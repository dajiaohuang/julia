# This file is a part of Julia. License is MIT: https://julialang.org/license

# Instant arithmetic
(+)(x::Instant) = x
(-)(x::T, y::T) where {T<:Instant} = x.periods - y.periods

# TimeType arithmetic
(+)(x::TimeType) = x
(-)(x::T, y::T) where {T<:TimeType} = x.instant - y.instant
(-)(x::T, y::T) where {T<:AbstractDateTime} = x.instant - y.instant
(-)(x::Timestamp, y::Timestamp) = Nanosecond(Base.checked_sub(value(x), value(y)))
(-)(x::AbstractDateTime, y::AbstractDateTime) = -(promote(x, y)...)

# Date-Time arithmetic
"""
    dt::Date + t::Time -> DateTime

The addition of a `Date` with a `Time` produces a `DateTime`. The hour, minute, second, and millisecond parts of
the `Time` are used along with the year, month, and day of the `Date` to create the new `DateTime`.
Non-zero microseconds or nanoseconds in the `Time` type will result in an `InexactError` being thrown.
"""
(+)(dt::Date, t::Time) = DateTime(dt ,t)
(+)(t::Time, dt::Date) = DateTime(dt, t)

# TimeType-Year arithmetic
function (+)(dt::DateTime, y::Year)
    oy, m, d = yearmonthday(dt); ny = oy + value(y); ld = daysinmonth(ny, m)
    return DateTime(ny, m, d <= ld ? d : ld, hour(dt), minute(dt), second(dt), millisecond(dt))
end
function (+)(dt::Date,y::Year)
    oy, m, d = yearmonthday(dt); ny = oy + value(y); ld = daysinmonth(ny, m)
    return Date(ny, m, d <= ld ? d : ld)
end
function (-)(dt::DateTime,y::Year)
    oy, m, d = yearmonthday(dt); ny = oy - value(y); ld = daysinmonth(ny, m)
    return DateTime(ny, m, d <= ld ? d : ld, hour(dt), minute(dt), second(dt), millisecond(dt))
end
function (-)(dt::Date,y::Year)
    oy, m, d = yearmonthday(dt); ny = oy - value(y); ld = daysinmonth(ny, m)
    return Date(ny, m, d <= ld ? d : ld)
end

# TimeType-Month arithmetic
# monthwrap adds two months with wraparound behavior (i.e. 12 + 1 == 1)
monthwrap(m1, m2) = (v = mod1(m1 + m2, 12); return v < 0 ? 12 + v : v)
# yearwrap takes a starting year/month and a month to add and returns
# the resulting year with wraparound behavior (i.e. 2000-12 + 1 == 2001)
yearwrap(y, m1, m2) = y + fld(m1 + m2 - 1, 12)

function (+)(dt::DateTime, z::Month)
    y,m,d = yearmonthday(dt)
    ny = yearwrap(y, m, value(z))
    mm = monthwrap(m, value(z)); ld = daysinmonth(ny, mm)
    return DateTime(ny, mm, d <= ld ? d : ld, hour(dt), minute(dt), second(dt), millisecond(dt))
end

function (+)(dt::Date, z::Month)
    y,m,d = yearmonthday(dt)
    ny = yearwrap(y, m, value(z))
    mm = monthwrap(m, value(z)); ld = daysinmonth(ny, mm)
    return Date(ny, mm, d <= ld ? d : ld)
end
function (-)(dt::DateTime, z::Month)
    y,m,d = yearmonthday(dt)
    ny = yearwrap(y, m, -value(z))
    mm = monthwrap(m, -value(z)); ld = daysinmonth(ny, mm)
    return DateTime(ny, mm, d <= ld ? d : ld, hour(dt), minute(dt), second(dt), millisecond(dt))
end
function (-)(dt::Date, z::Month)
    y,m,d = yearmonthday(dt)
    ny = yearwrap(y, m, -value(z))
    mm = monthwrap(m, -value(z)); ld = daysinmonth(ny, mm)
    return Date(ny, mm, d <= ld ? d : ld)
end

(+)(x::Date, y::Quarter) = x + Month(y)
(-)(x::Date, y::Quarter) = x - Month(y)
(+)(x::DateTime, y::Quarter) = x + Month(y)
(-)(x::DateTime, y::Quarter) = x - Month(y)
(+)(x::Date, y::Week) = return Date(UTD(value(x) + 7 * value(y)))
(-)(x::Date, y::Week) = return Date(UTD(value(x) - 7 * value(y)))
(+)(x::Date, y::Day)  = return Date(UTD(value(x) + value(y)))
(-)(x::Date, y::Day)  = return Date(UTD(value(x) - value(y)))
(+)(x::DateTime, y::Period) = return DateTime(UTM(value(x) + toms(y)))
(-)(x::DateTime, y::Period) = return DateTime(UTM(value(x) - toms(y)))
(+)(x::Time, y::TimePeriod) = return Time(Nanosecond(value(x) + tons(y)))
(-)(x::Time, y::TimePeriod) = return Time(Nanosecond(value(x) - tons(y)))
# Widen period scaling before arithmetic so large period values cannot wrap.
_timestamp_ns(x::Nanosecond) = Int128(value(x))
_timestamp_ns(x::Microsecond) = Int128(value(x)) * 1000
_timestamp_ns(x::Millisecond) = Int128(value(x)) * 1000000
_timestamp_ns(x::Second) = Int128(value(x)) * 1000000000
_timestamp_ns(x::Minute) = Int128(value(x)) * 60000000000
_timestamp_ns(x::Hour) = Int128(value(x)) * 3600000000000
_timestamp_ns(x::Day) = Int128(value(x)) * NS_PER_DAY
_timestamp_ns(x::Week) = Int128(value(x)) * 7 * NS_PER_DAY
_timestamp_ns(x::Period) = Int128(tons(x))

function _timestamp_from_ns(ns::Int128)
    typemin(Int64) <= ns <= typemax(Int64) ||
        throw(OverflowError("Timestamp arithmetic overflow"))
    return Timestamp(UTN(Int64(ns)))
end

function _timestamp_add_fixed(x::Timestamp, v::Int64, scale::Int64)
    if cld(typemin(Int64), scale) <= v <= fld(typemax(Int64), scale)
        return Timestamp(UTN(Base.checked_add(value(x), v * scale)))
    end
    return _timestamp_from_ns(Int128(value(x)) + Int128(v) * scale)
end

function _timestamp_sub_fixed(x::Timestamp, v::Int64, scale::Int64)
    if cld(typemin(Int64), scale) <= v <= fld(typemax(Int64), scale)
        return Timestamp(UTN(Base.checked_sub(value(x), v * scale)))
    end
    return _timestamp_from_ns(Int128(value(x)) - Int128(v) * scale)
end

for (T, scale) in ((Nanosecond, Int64(1)), (Microsecond, Int64(1000)),
                   (Millisecond, Int64(1000000)), (Second, Int64(1000000000)),
                   (Minute, Int64(60000000000)), (Hour, Int64(3600000000000)),
                   (Day, NS_PER_DAY), (Week, 7NS_PER_DAY))
    @eval begin
        (+)(x::Timestamp, y::$T) = _timestamp_add_fixed(x, value(y), $scale)
        (-)(x::Timestamp, y::$T) = _timestamp_sub_fixed(x, value(y), $scale)
    end
end

function _timestamp_from_calendar(x::Timestamp, y::Int64, m::Int64, d::Int64)
    try
        return Timestamp(y, m, d, hour(x), minute(x), second(x),
                         millisecond(x), microsecond(x), nanosecond(x))
    catch err
        err isa ArgumentError || rethrow()
        throw(OverflowError("Timestamp arithmetic overflow"))
    end
end

function _timestamp_add_years(x::Timestamp, n::Int128)
    y = Int128(year(x)) + n
    typemin(Int64) <= y <= typemax(Int64) ||
        throw(OverflowError("Timestamp arithmetic overflow"))
    yy = Int64(y)
    m, d = monthday(x)
    return _timestamp_from_calendar(x, yy, m, min(d, daysinmonth(yy, m)))
end

function _timestamp_add_months(x::Timestamp, n::Int128)
    months = Int128(year(x)) * 12 + month(x) - 1 + n
    y, m = fldmod(months, 12)
    typemin(Int64) <= y <= typemax(Int64) ||
        throw(OverflowError("Timestamp arithmetic overflow"))
    yy, mm = Int64(y), Int64(m + 1)
    return _timestamp_from_calendar(x, yy, mm, min(day(x), daysinmonth(yy, mm)))
end

(+)(x::Timestamp, y::Year) = _timestamp_add_years(x, Int128(value(y)))
(-)(x::Timestamp, y::Year) = _timestamp_add_years(x, -Int128(value(y)))
(+)(x::Timestamp, y::Month) = _timestamp_add_months(x, Int128(value(y)))
(-)(x::Timestamp, y::Month) = _timestamp_add_months(x, -Int128(value(y)))
(+)(x::Timestamp, y::Quarter) = _timestamp_add_months(x, Int128(value(y)) * 3)
(-)(x::Timestamp, y::Quarter) = _timestamp_add_months(x, -Int128(value(y)) * 3)
# Unlike DateTime, Timestamp add/subtract throws `OverflowError` rather than
# wrapping: the ±292 year range makes overflow a realistic mistake to catch.
(+)(x::Timestamp, y::Period) = _timestamp_from_ns(Int128(value(x)) + _timestamp_ns(y))
(-)(x::Timestamp, y::Period) = _timestamp_from_ns(Int128(value(x)) - _timestamp_ns(y))
(+)(y::Period, x::TimeType) = x + y

# Missing support
(+)(x::AbstractTime, y::Missing) = missing
(+)(x::Missing, y::AbstractTime) = missing
(-)(x::AbstractTime, y::Missing) = missing
(-)(x::Missing, y::AbstractTime) = missing

# AbstractArray{TimeType}, AbstractArray{TimeType}
(-)(x::OrdinalRange{T}, y::OrdinalRange{T}) where {T<:TimeType} = Vector(x) - Vector(y)
(-)(x::AbstractRange{T}, y::AbstractRange{T}) where {T<:TimeType} = Vector(x) - Vector(y)

# Allow dates, times, and time zones to broadcast as unwrapped scalars
Base.Broadcast.broadcastable(x::AbstractTime) = Ref(x)
Base.Broadcast.broadcastable(x::TimeZone) = Ref(x)
