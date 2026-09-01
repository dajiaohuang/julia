# This file is a part of Julia. License is MIT: https://julialang.org/license

# Date/DateTime Ranges

StepRange{<:Dates.DatePeriod,<:Real}(start, step, stop) =
    throw(ArgumentError("must specify step as a Period when constructing Dates ranges"))
Base.:(:)(a::T, b::T) where {T<:Date} = (:)(a, Day(1), b)

# Given a start and end date, how many steps/periods are in between
guess(a::DateTime, b::DateTime, c) = floor(Int64, (Int128(value(b)) - Int128(value(a))) / toms(c))
guess(a::Timestamp, b::Timestamp, c) = floor(Int64, (Int128(value(b)) - Int128(value(a))) / tons(c))
guess(a::Date, b::Date, c) = Int64(div(value(b - a), days(c)))
len(a::Time, b::Time, c) = Int64(div(value(b - a), tons(c)))
function len(a::Timestamp, b::Timestamp, c::FixedPeriod)
    n = div(abs(Int128(value(b)) - value(a)), abs(_timestamp_ns(c)))
    n < typemax(Int64) || throw(OverflowError("Timestamp range is too large"))
    return Int64(n)
end

function len(a::Timestamp, b::Timestamp, c::OtherPeriod)
    value(c) == typemin(Int64) && return Int64(0)
    lo, hi, st = min(a, b), max(a, b), abs(c)
    i = guess(a, b, c)
    local v
    while true
        try
            v = lo + st * i
            break
        catch err
            err isa OverflowError || rethrow()
            i == 0 && return Int64(0)
            i -= 1
        end
    end
    prev = v
    while v <= hi && prev <= v
        prev = v
        try
            v += st
        catch err
            err isa OverflowError || rethrow()
            return i
        end
        i += 1
    end
    return i - 1
end

function len(a, b, c)
    lo, hi, st = min(a, b), max(a, b), abs(c)
    i = guess(a, b, c)
    v = lo + st * i
    prev = v  # Ensure `v` does not overflow
    while v <= hi && prev <= v
        prev = v
        v += st
        i += 1
    end
    return i - 1
end
Base.length(r::StepRange{<:TimeType}) = isempty(r) ? Int64(0) : len(r.start, r.stop, r.step) + 1
Base.length(r::StepRange{Timestamp}) = isempty(r) ? Int64(0) : Base.checked_add(len(r.start, r.stop, r.step), Int64(1))
# Period ranges hook into Int64 overflow detection
Base.length(r::StepRange{<:Period}) = length(StepRange(value(r.start), value(r.step), value(r.stop)))
Base.checked_length(r::StepRange{<:Period}) = Base.checked_length(StepRange(value(r.start), value(r.step), value(r.stop)))

# Overload Base.steprange_last because `step::Period` may be a variable amount of time (e.g. for Month and Year)
function Base.steprange_last(start::T, step, stop) where T<:TimeType
    if isa(step, AbstractFloat)
        throw(ArgumentError("StepRange should not be used with floating point"))
    end
    z = zero(step)
    step == z && throw(ArgumentError("step cannot be zero"))

    if stop == start
        last = stop
    else
        if (step > z) != (stop > start)
            last = Base.steprange_last_empty(start, step, stop)
        else
            diff = stop - start
            if (diff > zero(diff)) != (stop > start)
                throw(OverflowError("Difference between stop and start overflowed"))
            end
            remain = stop - (start + step * len(start, stop, step))
            last = stop - remain
        end
    end
    return last
end

function Base.steprange_last(start::Timestamp, step, stop::Timestamp)
    isa(step, AbstractFloat) && throw(ArgumentError("StepRange should not be used with floating point"))
    z = zero(step)
    step == z && throw(ArgumentError("step cannot be zero"))

    if stop == start
        return stop
    elseif (step > z) != (stop > start)
        return Base.steprange_last_empty(start, step, stop)
    end

    n = len(start, stop, step)
    if step isa FixedPeriod
        return _timestamp_from_ns(Int128(value(start)) + _timestamp_ns(step) * n)
    end
    return start + step * n
end

function _timestamp_range_index(r::StepRange{Timestamp,<:FixedPeriod}, x::Timestamp)
    isempty(r) && return nothing
    lo, hi = minmax(first(r), last(r))
    lo <= x <= hi || return nothing
    q, rem = divrem(Int128(value(x)) - value(first(r)), _timestamp_ns(step(r)))
    iszero(rem) || return nothing
    i = q + 1
    return 1 <= i <= length(r) ? oftype(firstindex(r), i) : nothing
end

import Base.in
in(x::Timestamp, r::StepRange{Timestamp,<:FixedPeriod}) =
    _timestamp_range_index(r, x) !== nothing
function in(x::T, r::StepRange{T}) where T<:TimeType
    isempty(r) && return false
    lo, hi = minmax(first(r), last(r))
    lo <= x <= hi || return false
    n = len(first(r), x, step(r)) + 1
    n >= 1 && n <= length(r) && r[n] == x
end

function Base.findfirst(p::Union{Base.Fix2{typeof(isequal),Timestamp},
                                 Base.Fix2{typeof(==),Timestamp}},
                        r::StepRange{Timestamp,<:FixedPeriod})
    return _timestamp_range_index(r, p.x)
end

Base.iterate(r::StepRange{<:TimeType}) = length(r) <= 0 ? nothing : (r.start, (length(r), 1))
Base.iterate(r::StepRange{<:TimeType}, (l, i)) = l <= i ? nothing : (r.start + r.step * i, (l, i + 1))
Base.iterate(r::StepRange{Timestamp,<:FixedPeriod}) = length(r) <= 0 ? nothing : (r.start, (length(r), 1))
Base.iterate(r::StepRange{Timestamp,<:FixedPeriod}, (l, i)) =
    l <= i ? nothing : (Base.unsafe_getindex(r, i + 1), (l, i + 1))

function Base.unsafe_getindex(r::StepRange{Timestamp,<:FixedPeriod}, i::Integer)
    offset = _timestamp_ns(step(r)) * Int128(i - oneunit(i))
    return _timestamp_from_ns(Int128(value(first(r))) + offset)
end

function Base.getindex(r::StepRange{Timestamp,<:FixedPeriod}, s::AbstractRange{T}) where {T<:Integer}
    @inline
    @boundscheck checkbounds(r, s)

    if T === Bool
        st = step(s)
        nonempty = st > zero(st) ? last(s) : first(s)
        nonempty || return Timestamp[]
        start = xor(xor(first(s), nonempty), isempty(r)) ? last(r) : first(r)
        return range(start; step=step(r), length=1)
    end
    isempty(s) && return Timestamp[]

    start = Base.unsafe_getindex(r, first(s))
    stop = Base.unsafe_getindex(r, last(s))
    index_step = step(s)
    if typemin(Int64) <= index_step <= typemax(Int64)
        period_step = Int128(value(step(r))) * Int128(index_step)
        if typemin(Int64) <= period_step <= typemax(Int64)
            return range(start, stop; step=typeof(step(r))(Int64(period_step)))
        end
    end

    return [Base.unsafe_getindex(r, i) for i in s]
end

function Base._reverse(r::StepRange{Timestamp,<:FixedPeriod}, ::Colon)
    value(step(r)) == typemin(Int64) && return reverse!(collect(r))
    return (:)(last(r), -step(r), first(r))
end

+(x::Period, r::AbstractRange{<:TimeType}) = (x + first(r)):step(r):(x + last(r))
+(r::AbstractRange{<:TimeType}, x::Period) = x + r
-(r::AbstractRange{<:TimeType}, x::Period) = (first(r)-x):step(r):(last(r)-x)
*(x::Period, r::AbstractRange{<:Real}) = (x * first(r)):(x * step(r)):(x * last(r))
*(r::AbstractRange{<:Real}, x::Period) = x * r
/(r::AbstractRange{<:P}, x::P) where {P<:Period} = (first(r)/x):(step(r)/x):(last(r)/x)

# Combinations of types and periods for which the range step is regular
Base.RangeStepStyle(::Type{<:OrdinalRange{<:TimeType, <:FixedPeriod}}) =
    Base.RangeStepRegular()
