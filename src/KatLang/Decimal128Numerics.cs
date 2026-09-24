using System.Numerics;

namespace KatLang;

/// <summary>
/// Exact scaled-integer arithmetic over Decimal128 representations, shared by the
/// numeric paths that a chain of Decimal128 operations cannot deliver: the exact
/// <c>avg</c> mean (taken whenever the left-to-right sum was not exact, see
/// <see cref="TryExactDecimal128"/>) and the integer-exponent power (both correctly
/// rounded) and the truncating integer division <c>div</c>
/// (<see cref="IntegerDivide"/>, exact wherever the truncated quotient is representable).
/// It also hosts the inverse-trigonometric endpoint reformulation
/// (<see cref="Acos"/>/<see cref="Asin"/>), an approximate composition of Decimal128
/// primitives rather than a certified rounding.
/// Every finite Decimal128 is an integer coefficient times a power-of-ten quantum,
/// so an exact rational value can be rounded ONCE, under IEEE round-to-nearest with
/// ties-to-even, into a Decimal128 through <see cref="RoundRational"/>.
///
/// <para><b>Integer powers.</b> <see cref="TryIntegerPower(Decimal128, long, out Decimal128)"/> raises a finite
/// nonzero Decimal128 to an integral exponent whose magnitude fits a
/// <see cref="long"/> and returns a correctly rounded Decimal128 result or reports
/// that the precision cap prevented certification. The
/// contract it establishes, and how:</para>
/// <list type="bullet">
/// <item>The base is decomposed into its exact coefficient and quantum exponent;
/// trailing zeros of the coefficient move into the exponent (no information is lost,
/// and the preferred quantum of the written base is remembered separately). Squaring
/// and multiplying happen on exact <see cref="BigInteger"/> significands with a
/// separately tracked decimal exponent — never on rounded Decimal128
/// intermediates.</item>
/// <item>The computation stays EXACT until a product would exceed the working
/// precision. From that point every value is an enclosure [low, high] × 10^e whose
/// low end is truncated and whose high end is rounded up, so the true power always
/// lies inside. A result that never needed truncation is exact and is rounded with
/// the IEEE preferred-quantum rule; ties (such as <c>5 ^ 49</c>, a 35-digit exact
/// power ending in 5) are resolved on the exact value, to even.</item>
/// <item>An inexact result is CERTIFIED: both enclosure endpoints are rounded to
/// Decimal128 and the answer is accepted only when they agree, which (rounding being
/// monotone) proves the true value rounds the same way. Otherwise the working
/// precision doubles and the power is recomputed from the original exact inputs.
/// A negative exponent inverts the enclosure — [1/high, 1/low] — and rounds once at
/// the reciprocal, so no rounding of the positive power ever leaks into the
/// result.</item>
/// <item>Midpoints: every target rounding boundary, including zero/subnormal and
/// overflow boundaries, has at most 35 stripped digits and ends in 5. The normalized
/// input coefficient c is not divisible by ten, so no c^k acquires trailing zeros.
/// A positive power on a boundary therefore stays exact at every permitted precision
/// (at least 35). For a reciprocal to terminate, c must be 1, a pure power of 2, or
/// a pure power of 5. The c=1 chain is exact. For c=5^r the reciprocal's stripped
/// coefficient is 2^(r*n), which cannot end in 5, hence cannot be a midpoint. For
/// c=2^r it is 5^(r*n); at most 35 digits implies r*n &lt;= 50, so the positive
/// coefficient 2^(r*n) has at most 16 digits and the chain stays exact. Decimal
/// scaling changes none of these stripped-coefficient facts.</item>
/// <item>Convergence is separate from the cap: for a fixed input the finite
/// multiplication chain's outward truncation errors tend to zero as precision grows.
/// Multiplication is continuous, as is reciprocal inversion once the lower endpoint
/// is positive. A non-midpoint therefore eventually has both endpoints in its rounding
/// cell; exact midpoints are handled above. This proves eventual certification with
/// unbounded refinement, NOT certification within 4096 digits.</item>
/// <item>Resource policy: work per round is O(log|n|) multiplications of
/// working-precision integers; precision starts at 34 + digits(|n|) +
/// <see cref="InitialGuardDigits"/> and doubles per round up to
/// <see cref="MaxWorkingDigits"/>, so memory and time are bounded by the precision
/// actually needed for certification (never by |n| or by the digit count of the
/// full exact power). An outward carry can give an endpoint one extra digit;
/// multiplication temporaries have at most twice that size. The capped precision is
/// itself attempted before failure. No bound here proves that every input certifies
/// within the cap: when it does not, the method reports failure instead of an approximation;
/// the evaluator turns that into a structured error.</item>
/// </list>
/// </summary>
internal static class Decimal128Numerics
{
    private const double Log10Of2 = 0.30102999566398119521;

    /// <summary>Significant decimal digits of a Decimal128 coefficient (34), read from the type.</summary>
    internal static readonly int Precision = DigitCount(CoefficientOf(Decimal128.MaxValue, out _));

    /// <summary>The largest quantum exponent (6111), read from <see cref="Decimal128.MaxValue"/>'s quantum.</summary>
    internal static readonly int MaxQuantumExponent = Decimal128.ILogB(Decimal128.GetQuantum(Decimal128.MaxValue));

    /// <summary>The smallest (subnormal) quantum exponent (-6176), read from <see cref="Decimal128.Epsilon"/>'s quantum.</summary>
    internal static readonly int MinQuantumExponent = Decimal128.ILogB(Decimal128.GetQuantum(Decimal128.Epsilon));

    /// <summary>
    /// Working digits added to 34 + digits(|n|) for the first certification round. The
    /// initial allowance grows with exponent length to accommodate propagated
    /// truncation error. It is a performance heuristic, not an accuracy certificate
    /// or a probabilistic guarantee; endpoint rounding decides success.
    /// </summary>
    internal const int InitialGuardDigits = 8;

    /// <summary>The working-precision cap of the certification loop (see the class remarks).</summary>
    internal const int MaxWorkingDigits = 4096;

    /// <summary>Which of the three Decimal128 outcomes a rounded magnitude is.</summary>
    internal enum RoundedMagnitudeKind
    {
        Zero,
        Finite,
        Infinity,
    }

    /// <summary>
    /// A positive value rounded once into Decimal128 terms: a coefficient of at most
    /// <see cref="Precision"/> digits at an in-range quantum exponent, or one of the two
    /// range outcomes. RoundRational chooses a unique full-precision (or subnormal)
    /// representative, so record equality here certifies numerical equality. It does
    /// not establish a preferred quantum; the evaluator preserves compatible legacy
    /// reciprocal quanta separately, without changing the certified value.
    /// </summary>
    internal readonly record struct RoundedMagnitude(
        RoundedMagnitudeKind Kind,
        BigInteger Coefficient,
        int QuantumExponent)
    {
        public static readonly RoundedMagnitude Zero = new(RoundedMagnitudeKind.Zero, BigInteger.Zero, 0);
        public static readonly RoundedMagnitude Infinity = new(RoundedMagnitudeKind.Infinity, BigInteger.Zero, 0);

        /// <summary>Materializes the Decimal128 with the requested sign (a zero keeps its sign too).</summary>
        public Decimal128 ToDecimal128(bool negative)
        {
            switch (Kind)
            {
                case RoundedMagnitudeKind.Zero:
                    return negative ? Decimal128.NegativeZero : Decimal128.Zero;
                case RoundedMagnitudeKind.Infinity:
                    return negative ? Decimal128.NegativeInfinity : Decimal128.PositiveInfinity;
                default:
                    // The coefficient has at most Precision digits and the exponent is
                    // in range, so the conversion and the scaling are both exact.
                    var magnitude = Decimal128.ScaleB((Decimal128)(Int128)Coefficient, QuantumExponent);
                    return negative ? -magnitude : magnitude;
            }
        }
    }

    /// <summary>
    /// The exact integer coefficient of a finite non-negative Decimal128 together with
    /// its quantum exponent: <c>value == coefficient × 10^quantumExponent</c>. Dividing by
    /// the quantum is exact (it only moves the exponent), and a coefficient never exceeds
    /// <see cref="Int128"/>.
    /// </summary>
    internal static BigInteger CoefficientOf(Decimal128 finiteMagnitude, out int quantumExponent)
    {
        var quantum = Decimal128.GetQuantum(finiteMagnitude);
        quantumExponent = Decimal128.ILogB(quantum);
        return BigInteger.CreateChecked((Int128)(finiteMagnitude / quantum));
    }

    /// <summary>
    /// The quantum exponent <c>q</c> of a finite Decimal128 (its value is an integer
    /// coefficient times <c>10^q</c>), zeros included.
    /// </summary>
    internal static int QuantumExponent(Decimal128 finiteValue)
        => Decimal128.ILogB(Decimal128.GetQuantum(finiteValue));

    /// <summary>
    /// The exact value <c>scaledValue × 10^exponent</c> as a Decimal128 at the IEEE
    /// preferred quantum — <paramref name="preferredExponent"/> when the value fits there,
    /// else the nearest quantum at which it does (the quantum an exact IEEE sum carries) —
    /// or false when no Decimal128 represents the value exactly (more than
    /// <see cref="Precision"/> significant digits, or beyond the finite range). A zero is
    /// positive zero at the preferred quantum (clamped to the exponent range).
    /// </summary>
    internal static bool TryExactDecimal128(BigInteger scaledValue, int exponent, int preferredExponent, out Decimal128 value)
    {
        if (scaledValue.IsZero)
        {
            value = Decimal128.ScaleB(Decimal128.Zero, preferredExponent);
            return true;
        }

        var negative = scaledValue.Sign < 0;
        var coefficient = BigInteger.Abs(scaledValue);
        var coarsestExponent = exponent;
        var excessDigits = DigitCount(coefficient) - Precision;
        if (excessDigits > 0)
        {
            // Only trailing zeros may move into the exponent (one division, however long
            // the value): any other digit beyond Precision makes it unrepresentable.
            coefficient = BigInteger.DivRem(coefficient, BigInteger.Pow(10, excessDigits), out var dropped);
            if (!dropped.IsZero)
            {
                value = default;
                return false;
            }

            coarsestExponent += excessDigits;
        }

        while (true)
        {
            var shorter = BigInteger.DivRem(coefficient, 10, out var lastDigit);
            if (!lastDigit.IsZero)
                break;
            coefficient = shorter;
            coarsestExponent++;
        }

        // coefficient (no trailing zero, at most Precision digits) × 10^coarsestExponent:
        // every in-range quantum from the coefficient padded to Precision digits up to
        // coarsestExponent carries the value exactly, and the one nearest the preferred
        // quantum wins.
        var finest = Math.Max(coarsestExponent - (Precision - DigitCount(coefficient)), MinQuantumExponent);
        var coarsest = Math.Min(coarsestExponent, MaxQuantumExponent);
        if (finest > coarsest)
        {
            value = default;
            return false;
        }

        var quantum = Math.Clamp(preferredExponent, finest, coarsest);
        var coefficientAtQuantum = coefficient * BigInteger.Pow(10, coarsestExponent - quantum);
        var magnitude = Decimal128.ScaleB((Decimal128)(Int128)coefficientAtQuantum, quantum);
        value = negative ? -magnitude : magnitude;
        return true;
    }

    /// <summary>
    /// The number of decimal digits of a positive integer. The bit length bounds the
    /// answer to two candidates; exact comparisons against powers of ten settle it, so
    /// the floating-point estimate can never be off.
    /// </summary>
    internal static int DigitCount(BigInteger positive)
    {
        // 2^(bits-1) <= value < 2^bits, so floor((bits-1)·log10 2) + 1 <= digits <=
        // floor(bits·log10 2) + 1; the estimate below is the lower candidate up to
        // floating-point slack, and the two loops correct it exactly.
        var bits = positive.GetBitLength();
        var digits = (int)((bits - 1) * Log10Of2) + 1;
        while (positive >= BigInteger.Pow(10, digits))
            digits++;
        while (digits > 1 && positive < BigInteger.Pow(10, digits - 1))
            digits--;
        return digits;
    }

    /// <summary>
    /// Rounds the positive rational <c>numerator / denominator × 10^scale</c> ONCE into
    /// Decimal128 terms under round-to-nearest, ties-to-even: the coefficient is rounded
    /// at the quantum that keeps <see cref="Precision"/> significant digits, or at the
    /// subnormal floor <see cref="MinQuantumExponent"/> when the value is smaller (gradual
    /// underflow, possibly to zero), and a value at or beyond the overflow threshold
    /// rounds to infinity. The tie decision is taken on the exact remainder, so an
    /// exact midpoint resolves to even and nothing else can be mistaken for one. The
    /// rounding is monotone in the value, which is what makes two agreeing endpoints
    /// of an enclosure a certificate for everything between them.
    /// </summary>
    internal static RoundedMagnitude RoundRational(BigInteger numerator, BigInteger denominator, Int128 scale)
    {
        if (numerator.Sign <= 0 || denominator.Sign <= 0)
            throw new ArgumentOutOfRangeException(nameof(numerator), "RoundRational expects a positive numerator and denominator.");

        // 10^(dn-1) <= numerator < 10^dn and 10^(dd-1) <= denominator < 10^dd bound the
        // ratio to (10^(dn-dd-1), 10^(dn-dd+1)), so its scientific exponent is dn-dd or
        // dn-dd-1; one exact comparison decides which.
        var ratioExponent = DigitCount(numerator) - DigitCount(denominator);
        if (!RatioIsAtLeastPowerOfTen(numerator, denominator, ratioExponent))
            ratioExponent--;
        var scientificExponent = (Int128)ratioExponent + scale;

        // Range decisions on the scientific exponent alone: at least 10^6145 exceeds
        // MaxValue (34 nines at the largest quantum), and below 10^-6177 the value is
        // under a tenth of the smallest subnormal, so it rounds to zero. Everything in
        // between needs an in-range shift below, which is why the check comes first.
        if (scientificExponent > MaxQuantumExponent + Precision - 1)
            return RoundedMagnitude.Infinity;
        if (scientificExponent < MinQuantumExponent - 1)
            return RoundedMagnitude.Zero;

        var quantumExponent = (int)Int128.Max(scientificExponent - (Precision - 1), MinQuantumExponent);
        var shift = (int)(scale - quantumExponent);

        BigInteger quotient;
        BigInteger remainder;
        BigInteger roundingDenominator;
        if (shift >= 0)
        {
            roundingDenominator = denominator;
            quotient = BigInteger.DivRem(numerator * BigInteger.Pow(10, shift), roundingDenominator, out remainder);
        }
        else
        {
            roundingDenominator = denominator * BigInteger.Pow(10, -shift);
            quotient = BigInteger.DivRem(numerator, roundingDenominator, out remainder);
        }

        var doubledRemainder = remainder << 1;
        if (doubledRemainder > roundingDenominator
            || (doubledRemainder == roundingDenominator && !quotient.IsEven))
        {
            quotient++;
        }

        if (quotient.IsZero)
            return RoundedMagnitude.Zero;

        if (quotient == BigInteger.Pow(10, Precision))
        {
            // Rounding carried into a new digit: the cohort member with Precision digits
            // lives one quantum up (10^34 at q is 10^33 at q + 1).
            quotient = BigInteger.Pow(10, Precision - 1);
            quantumExponent++;
        }

        return quantumExponent > MaxQuantumExponent
            ? RoundedMagnitude.Infinity
            : new RoundedMagnitude(RoundedMagnitudeKind.Finite, quotient, quantumExponent);
    }

    private static bool RatioIsAtLeastPowerOfTen(BigInteger numerator, BigInteger denominator, int power)
        => power >= 0
            ? numerator >= denominator * BigInteger.Pow(10, power)
            : numerator * BigInteger.Pow(10, -power) >= denominator;

    // ── Integer powers ───────────────────────────────────────────────────────

    /// <summary>
    /// An enclosure of a positive value: <c>Low × 10^Exponent &lt;= value &lt;= High × 10^Exponent</c>.
    /// <see cref="IsExact"/> when the two ends coincide, which is the case exactly as long
    /// as no truncation has happened (dropping trailing zeros keeps it exact).
    /// </summary>
    private readonly record struct ScaledInterval(BigInteger Low, BigInteger High, Int128 Exponent)
    {
        public bool IsExact => Low == High;
    }

    /// <summary>
    /// Computes the correctly rounded Decimal128 value of <paramref name="value"/> raised to
    /// <paramref name="exponent"/> (see the class remarks for the contract). Preconditions:
    /// a finite nonzero base and a nonzero exponent above <see cref="long.MinValue"/>
    /// (the caller routes every other shape). Returns false only when certification
    /// could not be obtained within <see cref="MaxWorkingDigits"/>.
    /// </summary>
    internal static bool TryIntegerPower(Decimal128 value, long exponent, out Decimal128 result)
        => TryIntegerPower(value, exponent, Precision + DigitCount(UnsignedMagnitude(exponent)) + InitialGuardDigits, MaxWorkingDigits, out result);

    /// <summary>
    /// The certification loop with its policy knobs exposed for tests: the first round
    /// runs at <paramref name="initialWorkingDigits"/> significant digits (never below the
    /// digits a 34-digit result needs plus one guard digit, never above the cap), each
    /// further round doubles the precision, and <paramref name="maxWorkingDigits"/> caps it.
    /// </summary>
    internal static bool TryIntegerPower(
        Decimal128 value,
        long exponent,
        int initialWorkingDigits,
        int maxWorkingDigits,
        out Decimal128 result)
    {
        if (!Decimal128.IsFinite(value) || value == Decimal128.Zero)
            throw new ArgumentOutOfRangeException(nameof(value), "TryIntegerPower expects a finite nonzero base.");
        if (exponent == 0 || exponent == long.MinValue)
            throw new ArgumentOutOfRangeException(nameof(exponent), "TryIntegerPower expects a nonzero exponent above long.MinValue.");
        if (maxWorkingDigits < Precision + 1)
            throw new ArgumentOutOfRangeException(nameof(maxWorkingDigits), "The precision cap must allow at least 35 working digits.");

        var coefficient = CoefficientOf(Decimal128.Abs(value), out var quantumExponent);
        // Trailing zeros of the coefficient are not information: move them into the
        // exponent so the digit count measures significant digits only. The written
        // quantum stays the preferred quantum of the result (IEEE preferred exponent).
        Int128 strippedExponent = quantumExponent;
        while (true)
        {
            var shorter = BigInteger.DivRem(coefficient, 10, out var lastDigit);
            if (!lastDigit.IsZero)
                break;
            coefficient = shorter;
            strippedExponent++;
        }

        var reciprocal = exponent < 0;
        var magnitude = UnsignedMagnitude(exponent);
        var negative = Decimal128.IsNegative(value) && (magnitude & 1UL) == 1UL;
        var preferredExponent = (Int128)quantumExponent * (Int128)magnitude;

        var minimumWorkingDigits = Precision + 1;
        var workingDigits = Math.Clamp(initialWorkingDigits, minimumWorkingDigits, maxWorkingDigits);
        while (true)
        {
            var power = RaiseMagnitude(coefficient, strippedExponent, magnitude, workingDigits);
            if (TryRoundPower(power, preferredExponent, reciprocal, negative, out result))
                return true;
            if (workingDigits >= maxWorkingDigits)
                return false;
            workingDigits = (int)Math.Min(2L * workingDigits, maxWorkingDigits);
        }
    }

    private static ulong UnsignedMagnitude(long exponent)
        => exponent < 0 ? (ulong)(-(exponent + 1)) + 1UL : (ulong)exponent;

    /// <summary>
    /// Exponentiation by squaring on enclosures: O(log n) multiplications, each keeping
    /// at most <paramref name="workingDigits"/> digits plus one outward-carry digit.
    /// </summary>
    private static ScaledInterval RaiseMagnitude(BigInteger coefficient, Int128 exponent, ulong power, int workingDigits)
    {
        var result = new ScaledInterval(BigInteger.One, BigInteger.One, 0);
        var factor = new ScaledInterval(coefficient, coefficient, exponent);
        var remaining = power;
        while (true)
        {
            if ((remaining & 1UL) == 1UL)
                result = Multiply(result, factor, workingDigits);
            remaining >>= 1;
            if (remaining == 0)
                return result;
            factor = Multiply(factor, factor, workingDigits);
        }
    }

    /// <summary>
    /// Multiplies two enclosures exactly, then — only when the high end has more than
    /// <paramref name="workingDigits"/> digits — drops the excess digits, rounding the low
    /// end down and the high end up so the product's true value stays enclosed. Dropped
    /// digits that are all zero keep the enclosure exact.
    /// </summary>
    private static ScaledInterval Multiply(ScaledInterval a, ScaledInterval b, int workingDigits)
    {
        var low = a.Low * b.Low;
        var high = a.High * b.High;
        var exponent = a.Exponent + b.Exponent;

        var excessDigits = DigitCount(high) - workingDigits;
        if (excessDigits <= 0)
            return new ScaledInterval(low, high, exponent);

        var divisor = BigInteger.Pow(10, excessDigits);
        var truncatedLow = BigInteger.Divide(low, divisor);
        var truncatedHigh = BigInteger.DivRem(high, divisor, out var highRemainder);
        if (!highRemainder.IsZero)
            truncatedHigh++;
        return new ScaledInterval(truncatedLow, truncatedHigh, exponent + excessDigits);
    }

    /// <summary>
    /// Rounds a computed power (or its reciprocal) into the final Decimal128, or reports
    /// that the enclosure is too wide to certify the rounding at this precision.
    /// </summary>
    private static bool TryRoundPower(
        ScaledInterval power,
        Int128 preferredExponent,
        bool reciprocal,
        bool negative,
        out Decimal128 result)
    {
        if (power.IsExact)
        {
            result = reciprocal
                ? RoundExactReciprocal(power.Low, power.Exponent, negative)
                : RoundExact(power.Low, power.Exponent, preferredExponent, negative);
            return true;
        }

        if (power.Low.IsZero)
        {
            // The enclosure has lost its lower end entirely; only more precision helps.
            result = default;
            return false;
        }

        RoundedMagnitude low;
        RoundedMagnitude high;
        if (reciprocal)
        {
            // 1 / [low, high] × 10^e is [1/high, 1/low] × 10^-e: the reciprocal is taken
            // on the enclosure, so the rounding happens once, at the final result.
            low = RoundRational(BigInteger.One, power.High, -power.Exponent);
            high = RoundRational(BigInteger.One, power.Low, -power.Exponent);
        }
        else
        {
            low = RoundRational(power.Low, BigInteger.One, power.Exponent);
            high = RoundRational(power.High, BigInteger.One, power.Exponent);
        }

        if (low != high)
        {
            result = default;
            return false;
        }

        result = low.ToDecimal128(negative);
        return true;
    }

    /// <summary>
    /// The Decimal128 of the exact value <c>coefficient × 10^exponent</c>: rounded once
    /// (ties on the exact value, to even) when it needs more than <see cref="Precision"/>
    /// digits, and otherwise carried at the IEEE preferred quantum — the written
    /// <paramref name="preferredExponent"/> when the coefficient fits there, else the
    /// nearest quantum at which it does — with <see cref="Decimal128.ScaleB"/> applying
    /// the remaining range rules exactly as a Decimal128 multiplication would (padding
    /// toward the largest quantum, gradual underflow at the subnormal floor, overflow to
    /// infinity).
    /// </summary>
    private static Decimal128 RoundExact(BigInteger coefficient, Int128 exponent, Int128 preferredExponent, bool negative)
    {
        var digits = DigitCount(coefficient);
        if (digits > Precision)
            return RoundRational(coefficient, BigInteger.One, exponent).ToDecimal128(negative);

        var scientificExponent = exponent + digits - 1;
        if (scientificExponent > MaxQuantumExponent + Precision - 1)
            return RoundedMagnitude.Infinity.ToDecimal128(negative);
        if (scientificExponent < MinQuantumExponent - 1)
            return RoundedMagnitude.Zero.ToDecimal128(negative);

        // Any quantum in [minimumExponent, exponent] carries the value with an integer
        // coefficient of at most Precision digits; the preferred one wins when it is in
        // that range. Both bounds are within Precision of an in-range scientific
        // exponent, so the quantum is an int and ScaleB's clamping decides the rest.
        var minimumExponent = exponent - (Precision - digits);
        var quantum = Int128.Min(Int128.Max(preferredExponent, minimumExponent), exponent);
        var scaledCoefficient = coefficient * BigInteger.Pow(10, (int)(exponent - quantum));
        var magnitude = Decimal128.ScaleB((Decimal128)(Int128)scaledCoefficient, (int)quantum);
        return negative ? -magnitude : magnitude;
    }

    /// <summary>
    /// The Decimal128 of <c>1 / (coefficient × 10^exponent)</c> for an exact positive
    /// power. The reciprocal terminates exactly when the coefficient is 2^a·5^b; it is
    /// then <c>2^(s-a)·5^(s-b) × 10^(-exponent-s)</c> with <c>s = max(a, b)</c>, an exact value
    /// carried at its own canonical quantum (the IEEE division's preferred exponent,
    /// <c>0 - e(positive power)</c>, never lies below it, so the quotient's exact
    /// representation always lands there). Otherwise the reciprocal is rounded once from
    /// the exact rational.
    /// </summary>
    private static Decimal128 RoundExactReciprocal(BigInteger coefficient, Int128 exponent, bool negative)
    {
        if (TryFactorTwosAndFives(coefficient, out var twos, out var fives))
        {
            var shift = Math.Max(twos, fives);
            var reciprocalCoefficient = BigInteger.Pow(2, shift - twos) * BigInteger.Pow(5, shift - fives);
            var reciprocalExponent = -exponent - shift;
            return RoundExact(reciprocalCoefficient, reciprocalExponent, reciprocalExponent, negative);
        }

        return RoundRational(BigInteger.One, coefficient, -exponent).ToDecimal128(negative);
    }

    // ── Truncating integer division (`div`) ───────────────────────────────────

    /// <summary>
    /// <c>10^34</c>: the inclusive boundary of KatLang's exact consecutive-integer domain.
    /// Every integer with <c>|n| &lt;= 10^34</c> is a Decimal128 (at most 34 significant
    /// digits, or <c>1e34</c> itself); <c>10^34 + 1</c> is the first that is not. Sparse
    /// larger integers such as <c>1e40</c> stay representable, so this is the
    /// consecutive-integer boundary, not the largest representable integer.
    /// </summary>
    internal static readonly Decimal128 ConsecutiveIntegerBound = Decimal128.ScaleB(Decimal128.One, Precision);

    /// <summary>
    /// KatLang <c>div</c>: the EXACT quotient <c>dividend / divisor</c> rounded TOWARD ZERO to
    /// a Decimal128 integer (Lean: <c>Int.tdiv</c>). The result is the truncated
    /// mathematical quotient <c>t</c> whenever that integer is representable — throughout
    /// the consecutive-integer domain <c>|t| &lt;= 10^34</c> and for every representable
    /// sparse integer beyond it (<c>1e40 div 1e5</c> is exactly <c>1e35</c>) — and otherwise,
    /// when IEEE division remains finite,
    /// the largest-magnitude Decimal128 integer that does not exceed <c>|t|</c>: the
    /// truncated quotient's leading 34 significant digits (<c>1e40 div 7</c> is
    /// <c>1428571428571428571428571428571428e6</c>, never the rounded-up <c>…429e6</c> that
    /// <c>1e40 / 7</c> correctly rounds to). <c>div</c> is therefore a truncation at every
    /// finite magnitude, and <c>|(x div y) * y| &lt;= |x|</c> survives the product's own rounding
    /// for finite operands and nonzero divisor because rounding is monotone. The exact
    /// div/mod identity requires a representable truncated quotient; evaluating its
    /// recomposition in Decimal128 additionally requires exact multiplication and addition.
    /// Special values keep the operator's IEEE contract:
    /// NaN propagates, an IEEE quotient that overflows is a signed infinity like every
    /// other arithmetic overflow (never saturated to <see cref="Decimal128.MaxValue"/>), a
    /// finite dividend over an infinite divisor is a signed zero, and a zero result carries
    /// the quotient's sign (<c>-7 div 8</c> is <c>-0</c>). The evaluator has already rejected
    /// a zero-valued divisor as <c>divByZero</c>; the helper itself is total.
    ///
    /// <para><b>Why not <c>Truncate(x / y)</c>.</b> The IEEE quotient <c>r = RN(q)</c> is
    /// rounded to 34 significant digits BEFORE the truncation, and that rounding can land
    /// on an integer from below: <c>8999999999999999999999999999999999 / 3</c> is
    /// <c>2999…999.6…</c>, which rounds to <c>3e33</c>, so the old rule returned
    /// <c>3000000000000000000000000000000000</c> although the truncated quotient
    /// <c>2999999999999999999999999999999999</c> is representable and
    /// <c>8999… mod 3</c> is <c>2</c> — the truncated-division identity
    /// <c>x == y * (x div y) + (x mod y)</c> failed on exact operands. The defect is not
    /// confined to enormous quotients: <c>(13 * 3e32 - 1) div 3e32</c> rounded to
    /// <c>13.00000000000000000000000000000000</c> and returned <c>13</c> instead of <c>12</c>.
    /// The <c>%</c> remainder, by contrast, is exact for every pair of finite operands, so
    /// <c>div</c> and <c>mod</c> disagreed about the quotient.</para>
    ///
    /// <para><b>Lemma 1 — the fast path.</b> If <c>r</c> is finite and NOT an integer, then
    /// <c>Truncate(r) = t</c>. Every Decimal128 with <c>|v| &gt;= 10^34</c> is an integer (a
    /// 34-digit coefficient at exponent &gt;= 1), so <c>|r| &lt; 10^34</c>; rounding is monotone
    /// and <c>10^34</c> is representable, so <c>|q| &lt; 10^34</c> as well, and the integers
    /// <c>t</c> and <c>t ± 1</c> (toward and away from zero) are all representable. A
    /// nearest representable value to <c>q</c> can lie neither below <c>t</c> nor beyond
    /// <c>t ± 1</c> in magnitude — either would be farther from <c>q</c> than a representable
    /// integer is — so a non-integral <c>r</c> lies strictly between them and truncates to
    /// <c>t</c>, with the quotient's sign. This everyday case costs the division plus one
    /// <see cref="Decimal128.IsInteger"/>.</para>
    ///
    /// <para><b>Lemma 2 — the exact-division shortcut.</b> If <c>r</c> is an integer with
    /// <c>|r| &lt; 10^34</c> and <c>dividend % divisor</c> is zero, then <c>q</c> is an
    /// integer (the remainder is exact) below <c>10^34</c> (monotone rounding again), hence
    /// representable, hence <c>r = q = t</c>; <c>Truncate(r)</c> keeps that exact quotient at
    /// its established quantum. The bound is strict on purpose: at or above <c>10^34</c> a
    /// divisible <c>q</c> need not be representable, and <c>r</c> may have rounded up.</para>
    ///
    /// <para><b>Lemma 3 — the exact decision.</b> Any other integral <c>r</c> is an exact
    /// quotient that genuinely has 34 significant digits, a rounding that LANDED on an
    /// integer (from below — a crossing, <c>|r| = |t| + 1</c> — or from above, <c>r = t</c>),
    /// or a quotient at or beyond <c>10^34</c>. <see cref="TruncateQuotientTowardZero"/>
    /// decides every one of them from the operands' exact coefficients and quanta on
    /// <see cref="BigInteger"/>s of bounded size, never forming a power of ten
    /// proportional to the operands' exponent gap. Measured on the tested runtime the
    /// fast path is one division plus one predicate, and the exact decision costs about
    /// three divisions; the decision runs only for integral rounded quotients that the
    /// remainder shortcut cannot certify.</para>
    /// </summary>
    internal static Decimal128 IntegerDivide(Decimal128 dividend, Decimal128 divisor)
    {
        var quotient = dividend / divisor;

        // Keep the pre-G-3 Truncate operation on special outcomes, including its
        // re-quantization of a signed zero from a finite/infinite division.
        // (A zero divisor reaches here only when the caller skipped
        // its divByZero check, and then takes the same IEEE outcome.)
        if (!Decimal128.IsFinite(quotient) || !Decimal128.IsFinite(dividend) || !Decimal128.IsFinite(divisor))
            return Decimal128.Truncate(quotient);

        // |q| < 1 — a zero dividend, or a quotient that underflowed: the truncated
        // quotient is the signed zero IEEE already produced. Truncate re-quantizes
        // it to exponent 0 (an underflowed zero carries the subnormal quantum and
        // would otherwise display as 0.000…0 with 6176 places), as before G-3.
        if (quotient == Decimal128.Zero)
            return Decimal128.Truncate(quotient);

        // Lemma 1.
        if (!Decimal128.IsInteger(quotient))
            return Decimal128.Truncate(quotient);

        // Lemma 2.
        if (Decimal128.Abs(quotient) < ConsecutiveIntegerBound && dividend % divisor == Decimal128.Zero)
            return Decimal128.Truncate(quotient);

        // Lemma 3.
        var dividendCoefficient = CoefficientOf(Decimal128.Abs(dividend), out var dividendExponent);
        var divisorCoefficient = CoefficientOf(Decimal128.Abs(divisor), out var divisorExponent);
        return TruncateQuotientTowardZero(
            dividendCoefficient,
            divisorCoefficient,
            dividendExponent - divisorExponent,
            Decimal128.IsNegative(quotient),
            quotient);
    }

    /// <summary>
    /// The positive rational <c>numerator / denominator × 10^scale</c> rounded toward zero
    /// to a Decimal128 integer, for a quotient whose IEEE rounding
    /// <paramref name="roundedQuotient"/> is a finite nonzero integer. The scientific
    /// exponent <c>E</c> of the quotient comes from digit counts (as in
    /// <see cref="RoundRational"/>), and the truncation quantum is <c>10^k</c> with
    /// <c>k = max(E - 33, 0)</c>: <c>k = 0</c> keeps the whole integer part (below
    /// <c>10^34</c>, at most 34 digits, always representable) and <c>k &gt;= 1</c> keeps the
    /// leading 34 digits. The numerator shift <c>scale - k</c> then lies within
    /// <c>[-33, 67]</c> whatever the operands' quanta, so the work is bounded.
    /// </summary>
    private static Decimal128 TruncateQuotientTowardZero(
        BigInteger numerator,
        BigInteger denominator,
        int scale,
        bool negative,
        Decimal128 roundedQuotient)
    {
        var ratioExponent = DigitCount(numerator) - DigitCount(denominator);
        if (!RatioIsAtLeastPowerOfTen(numerator, denominator, ratioExponent))
            ratioExponent--;
        var scientificExponent = ratioExponent + scale;

        // |q| < 1 truncates to a signed zero. Unreachable for a nonzero integral
        // rounded quotient; kept so the function is total over its inputs.
        if (scientificExponent < 0)
            return negative ? Decimal128.NegativeZero : Decimal128.Zero;

        var truncationExponent = Math.Max(scientificExponent - (Precision - 1), 0);
        var shift = scale - truncationExponent;
        BigInteger remainder;
        var coefficient = shift >= 0
            ? BigInteger.DivRem(numerator * BigInteger.Pow(10, shift), denominator, out remainder)
            : BigInteger.DivRem(numerator, denominator * BigInteger.Pow(10, -shift), out remainder);

        // A zero remainder means the exact quotient is coefficient × 10^k — an integer
        // with at most 34 significant digits, which IEEE division already returned
        // exactly. Keep that result, and its established quantum, bit-for-bit.
        if (remainder.IsZero)
            return Decimal128.Truncate(roundedQuotient);

        // Inexact: materialize the truncated coefficient exactly. Below 10^34 it is
        // the whole truncated quotient at quantum 0; at or above, its leading 34
        // digits (10^33 <= coefficient < 10^34) at the exact quotient's truncation
        // exponent. The conversion and the scaling are both exact.
        var magnitude = (Decimal128)(Int128)coefficient;
        if (truncationExponent > 0)
            magnitude = Decimal128.ScaleB(magnitude, truncationExponent);
        return negative ? -magnitude : magnitude;
    }

    private static bool TryFactorTwosAndFives(BigInteger positive, out int twos, out int fives)
    {
        twos = (int)BigInteger.TrailingZeroCount(positive);
        var rest = positive >> twos;
        fives = 0;
        while (true)
        {
            var quotient = BigInteger.DivRem(rest, 5, out var remainder);
            if (!remainder.IsZero)
                break;
            rest = quotient;
            fives++;
        }

        return rest.IsOne;
    }

    // ── Inverse trigonometric endpoints ──────────────────────────────────────

    /// <summary>
    /// The magnitude above which <see cref="Acos"/> and <see cref="Asin"/> stop
    /// delegating to the platform functions: <c>1 - 1e-4</c>, i.e. <c>0.9999</c> exactly.
    /// This empirically chosen band limits the endpoint reformulation to inputs where
    /// the direct path starts losing accuracy. It is not an exact crossover for every
    /// function or input: some correctly rounded direct results change by one last-place
    /// digit inside the band. See the K6-R3 review in SEMANTIC-ALIGNMENT.md.
    /// </summary>
    internal static readonly Decimal128 InverseTrigEndpointBandStart =
        Decimal128.One - Decimal128.ScaleB(Decimal128.One, -4);

    /// <summary>
    /// Arc cosine: the platform <see cref="Decimal128.Acos"/> for <c>|x| &lt;= 0.9999</c> and
    /// for every non-finite or out-of-domain input, and <c>atan2(sqrt(1 - x²), x)</c> inside
    /// the endpoint band <c>0.9999 &lt; |x| &lt;= 1</c> (see <see cref="EndpointComplement"/>
    /// for the tested runtime). At the endpoints the numerical values agree with
    /// the platform: <c>Acos(1)</c> is <c>0</c> and <c>Acos(-1)</c> is <see cref="Decimal128.Pi"/>.
    /// </summary>
    internal static Decimal128 Acos(Decimal128 x)
        => IsInEndpointBand(x)
            ? Decimal128.Atan2(EndpointComplement(x), x)
            : Decimal128.Acos(x);

    /// <summary>
    /// Arc sine: the platform <see cref="Decimal128.Asin"/> outside the endpoint band and
    /// <c>atan2(x, sqrt(1 - x²))</c> inside it, with the same complement as <see cref="Acos"/>.
    /// <c>Asin(±1)</c> agrees with the existing Decimal128 ±π/2 value (a rounded
    /// constant, not mathematically exact π/2 or necessarily <c>Decimal128.Pi / 2</c>).
    /// </summary>
    internal static Decimal128 Asin(Decimal128 x)
        => IsInEndpointBand(x)
            ? Decimal128.Atan2(x, EndpointComplement(x))
            : Decimal128.Asin(x);

    /// <summary>
    /// <c>0.9999 &lt; |x| &lt;= 1</c>. NaN compares false on both sides and an infinity
    /// exceeds one, so every non-finite or out-of-domain input keeps the platform
    /// function's verdict (NaN) bit-for-bit.
    /// </summary>
    private static bool IsInEndpointBand(Decimal128 x)
    {
        var magnitude = Decimal128.Abs(x);
        return magnitude > InverseTrigEndpointBandStart && magnitude <= Decimal128.One;
    }

    /// <summary>
    /// <c>sqrt(1 - x²)</c> for <c>|x| &lt;= 1</c>, the quantity the inverse trigonometric
    /// functions are ill-conditioned in near ±1 (their derivative magnitude is <c>1 / sqrt(1 - x²)</c>).
    ///
    /// <para>The tested runtime is .NET 11.0.0-preview.7.26381.103. Its assembly
    /// metadata identifies dotnet/dotnet e2c1e00b3d0f96afb892fb261d5921565b400246,
    /// whose source manifest maps runtime to 253bde0a42aff6d8e99e039db1e710c5e1f5436a.
    /// In that pinned source, DecimalToDiyFp128 converts the input to a 128-bit binary
    /// significand before DiyFp128AsinAcos computes sqrt((1 - |x|) / 2).
    /// Conversion error is amplified relative to the small endpoint gap; the direct
    /// Acos(1 - 1e-30) result had about nine correct digits in the review.</para>
    ///
    /// <para>Decimal FusedMultiplyAdd retains the exact product and rounds 1 - x*x
    /// once, avoiding cancellation after a rounded product or binary input conversion.
    /// Sqrt and Atan2 still round separately: this is not a correctly rounded
    /// transcendental implementation. The deterministic review sweep (23,080 distinct
    /// signed inputs, including all gaps n*1e-34 for n=1..999) observed maxima of
    /// 1.52542 ulp for acos near +1, 0.50368 near -1, and 0.50228 for asin on either
    /// side. References used mpmath 1.3.0 at 100 digits, with selected results checked
    /// at 200 digits and by an independent 220-digit decimal series. These are sample
    /// measurements, not whole-domain bounds or a guarantee of preserving every
    /// previously correctly rounded result.</para>
    ///
    /// <para>At |x| = 1 the fused product is positive zero. Atan2(y, x) therefore
    /// selects the intended quadrants: acos(1) is +0, acos(-1) agrees with Decimal128.Pi,
    /// and asin(±1) agrees with the platform's existing rounded ±π/2 value.</para>
    /// </summary>
    private static Decimal128 EndpointComplement(Decimal128 x)
        => Decimal128.Sqrt(Decimal128.FusedMultiplyAdd(-x, x, Decimal128.One));

    // ── Logarithms and powers near 1 ─────────────────────────────────────────

    /// <summary>
    /// Natural logarithm with the accuracy of <c>ln(1 + ε)</c> near 1. The platform
    /// <see cref="Decimal128.Log(Decimal128)"/> loses roughly one significant digit per decade of
    /// closeness to 1 (cancellation: <c>Log(1 + 1e-33)</c> kept five correct digits of
    /// 34 in the tested runtime), which the tutorial's stated accuracy of the logarithm
    /// family does not allow. For <c>0.5 &lt;= x &lt;= 1.5</c> the difference <c>x - 1</c>
    /// is EXACT in Decimal128 (the two operands are within a factor of two of each other),
    /// so <see cref="Decimal128.LogP1"/> of that exact difference is the logarithm without
    /// the cancellation; it agrees with <see cref="Decimal128.Log(Decimal128)"/> to the last digit
    /// away from 1 and at the window's edges. Outside the window, and for every
    /// non-finite, zero, or negative input, the platform function's verdict is kept
    /// bit-for-bit. Like the inverse-trigonometric reformulation this is an accurate
    /// composition of platform primitives, not a certified rounding.
    /// </summary>
    internal static Decimal128 NaturalLog(Decimal128 x)
        => IsInLogOnePlusWindow(x)
            ? Decimal128.LogP1(x - Decimal128.One)
            : Decimal128.Log(x);

    /// <summary>
    /// Base-10 logarithm: <see cref="NaturalLog"/> over <c>ln 10</c> inside the near-1
    /// window (where <see cref="Decimal128.Log10"/> loses the same digits), the platform
    /// function elsewhere — so exact results away from 1, such as <c>Lg(1000) = 3</c>,
    /// keep their existing platform value.
    /// </summary>
    internal static Decimal128 Log10(Decimal128 x)
        => IsInLogOnePlusWindow(x)
            ? NaturalLog(x) / NaturalLogOfTen
            : Decimal128.Log10(x);

    /// <summary>
    /// Logarithm of <paramref name="value"/> in the given <paramref name="newBase"/>:
    /// the ratio of the two natural logarithms whenever either argument lies in the
    /// near-1 window, the platform <see cref="Decimal128.Log(Decimal128, Decimal128)"/>
    /// otherwise (its exact results such as <c>Log(100, 10) = 2</c> are unchanged). A
    /// DEGENERATE base or value — zero, negative, non-finite, or a base of exactly 1 —
    /// always keeps the platform verdict (NaN, an infinity, or zero by its rules), so that
    /// verdict never depends on whether the OTHER argument happens to lie in the window.
    /// </summary>
    internal static Decimal128 Log(Decimal128 value, Decimal128 newBase)
        => IsOrdinaryLogArgument(value) && IsOrdinaryLogArgument(newBase) && newBase != Decimal128.One
            && (IsInLogOnePlusWindow(value) || IsInLogOnePlusWindow(newBase))
            ? NaturalLog(value) / NaturalLog(newBase)
            : Decimal128.Log(value, newBase);

    /// <summary>Finite and strictly positive: an argument the reformulation may take.</summary>
    private static bool IsOrdinaryLogArgument(Decimal128 x)
        => Decimal128.IsFinite(x) && x > Decimal128.Zero;

    /// <summary>
    /// <see cref="Decimal128.Log(Decimal128)"/> of 10, computed once from the platform function
    /// (10 is far from 1, where that function is accurate to the last digit).
    /// </summary>
    private static readonly Decimal128 NaturalLogOfTen = Decimal128.Log((Decimal128)10);

    /// <summary>
    /// <c>0.5 &lt;= x &lt;= 1.5</c>: the window in which <c>x - 1</c> is an exact
    /// Decimal128 subtraction. NaN compares false on both sides, so non-finite inputs
    /// keep the platform verdict.
    /// </summary>
    private static bool IsInLogOnePlusWindow(Decimal128 x)
        => x >= LogOnePlusWindowLow && x <= LogOnePlusWindowHigh;

    private static readonly Decimal128 LogOnePlusWindowLow = Decimal128.Parse("0.5", System.Globalization.CultureInfo.InvariantCulture);
    private static readonly Decimal128 LogOnePlusWindowHigh = Decimal128.Parse("1.5", System.Globalization.CultureInfo.InvariantCulture);

    /// <summary>
    /// The band of base MAGNITUDES around 1 (<c>0.99 &lt;= |b| &lt;= 1.01</c>; the caller
    /// passes the magnitude) in which the DELEGATED power paths — a fractional exponent, an
    /// integral one beyond <see cref="long"/>, or a negative integral exponent whose positive
    /// power overflows — stop using the platform <see cref="Decimal128.Pow"/> and compute
    /// <c>exp(exponent · ln(base))</c> with the exponent product carried in EXACT
    /// arithmetic (<see cref="NearOnePower"/>). The platform power inherits the
    /// logarithm's near-1 cancellation, so <c>(1 + 1e-33) ^ 9223372036854775808</c> lost
    /// fourteen digits and came out SMALLER than the same base to the power
    /// <c>9223372036854775807</c> (the certified integer path), and its negative twin
    /// <c>(-0.9999999999999999999999999999999999) ^ 1e34</c> kept four digits until the band
    /// was applied to the magnitude (numeric audit #6, September 2026); away from 1 the
    /// platform power is at least as accurate and is kept unchanged.
    /// </summary>
    internal static bool IsInNearOnePowerBand(Decimal128 b)
        => b >= NearOnePowerBandLow && b <= NearOnePowerBandHigh;

    private static readonly Decimal128 NearOnePowerBandLow = Decimal128.Parse("0.99", System.Globalization.CultureInfo.InvariantCulture);
    private static readonly Decimal128 NearOnePowerBandHigh = Decimal128.Parse("1.01", System.Globalization.CultureInfo.InvariantCulture);

    /// <summary>
    /// Fixed-point scale of the logarithm and exponent product. Logarithm truncation
    /// is amplified by |exponent|: it is NOT an absolute 10^-80 product-error bound.
    /// In this band |base - 1| is either zero or at least 10^-34. A product within
    /// the 20,000 cutoff therefore has |exponent| below 2.1e38. Fewer than 41 log
    /// terms, each with less than two scale units of error, give a conservative
    /// product-error bound below 10^-39, still well below Decimal128 result precision.
    /// </summary>
    private const int NearOneProductScale = 80;

    /// <summary>
    /// <c>base ^ exponent</c> for a finite base in <see cref="IsInNearOnePowerBand"/> and a
    /// finite exponent, correct to about one unit in the last place: a power is
    /// ill-conditioned in its exponent product (a relative error <c>δ</c> in
    /// <c>t = exponent · ln(base)</c> becomes a relative error <c>|t| · δ</c> in
    /// <c>exp(t)</c>, so rounding <c>t</c> to 34 digits loses <c>log10 |t|</c> digits — 123
    /// ulp for <c>0.99 ^ 12345.5</c>, two thousand for <c>(1 + 1e-15) ^ 2^63</c>), so the
    /// product is never rounded to Decimal128: <c>ln(1 + ε)</c> is approximated by a fixed-point series
    /// (<c>ε = base − 1</c> is an exact Decimal128 difference in the band, and the series
    /// terms shrink a hundredfold each), multiplied by the exact exponent, and only then
    /// split as <c>t = n + f</c> with <c>n</c> an exact integer and <c>0 &lt;= f &lt; 1</c>.
    /// <c>exp(n) · exp(f)</c> is then evaluated in the same exact fixed-point arithmetic
    /// (the Taylor series for <c>exp(f)</c> and for <c>e</c>, binary powering for
    /// <c>e^n</c>) and rounded ONCE into Decimal128 terms by <see cref="RoundRational"/>.
    /// The fixed-point approximation is not an interval-certified rounding. A product
    /// past the exponential's range yields the IEEE infinity/zero of the true limit.
    /// </summary>
    internal static Decimal128 NearOnePower(Decimal128 b, Decimal128 exponent)
    {
        if (exponent == Decimal128.Zero || b == Decimal128.One)
            return Decimal128.One;

        // ε = b − 1 exactly (both operands share a quantum range in the band).
        var epsilon = b - Decimal128.One;
        var epsilonNegative = Decimal128.IsNegative(epsilon);
        var epsilonCoefficient = CoefficientOf(Decimal128.Abs(epsilon), out var epsilonQuantum);
        var scale = BigInteger.Pow(10, NearOneProductScale);

        // ln(1 + ε) = ε − ε²/2 + ε³/3 − … at the fixed-point scale (truncated terms; each
        // is at most a hundredth of the previous one, so the truncation error stays below
        // a few units of 10^-80). ε · 10^Scale is an exact integer because |ε| >= 10^-34.
        var epsilonScaled = epsilonCoefficient * BigInteger.Pow(10, NearOneProductScale + epsilonQuantum);
        if (epsilonNegative) epsilonScaled = -epsilonScaled;
        var epsilonDenominator = BigInteger.Pow(10, Math.Max(0, -epsilonQuantum));
        var epsilonNumerator = epsilonCoefficient * BigInteger.Pow(10, Math.Max(0, epsilonQuantum));
        var power = epsilonScaled;
        var logScaled = BigInteger.Zero;
        for (var n = 1; ; n++)
        {
            var term = power / n;
            if (term.IsZero) break;
            logScaled += (n % 2 == 1) ? term : -term;
            power = power * epsilonNumerator / epsilonDenominator;
            if (epsilonNegative) power = -power;
        }

        // t = exponent · ln(1 + ε), the exponent taken exactly (coefficient × 10^quantum).
        var exponentCoefficient = CoefficientOf(Decimal128.Abs(exponent), out var exponentQuantum);
        var productScaled = logScaled * exponentCoefficient;
        productScaled = exponentQuantum >= 0
            ? productScaled * BigInteger.Pow(10, exponentQuantum)
            : productScaled / BigInteger.Pow(10, -exponentQuantum);
        if (Decimal128.IsNegative(exponent)) productScaled = -productScaled;

        // Past the exponential's range the true value overflows or underflows: let the
        // platform exponential produce the IEEE limit from a rounded product (its sign and
        // magnitude are all that matter there).
        var integerPart = BigInteger.DivRem(productScaled, scale, out var fractionScaled);
        if (fractionScaled.Sign < 0)
        {
            integerPart -= 1;
            fractionScaled += scale;
        }
        if (BigInteger.Abs(integerPart) > 20_000)
            return Decimal128.Exp(exponent * NaturalLog(b));

        // exp(t) = exp(n) · exp(f) in exact fixed-point arithmetic, rounded ONCE into
        // Decimal128 terms. RoundRational rounds this approximation; it does not certify
        // the exact transcendental result. Overflow/underflow use the same rounding.
        var fractionExp = ExpFractionScaled(fractionScaled, scale);
        var wholeExp = ExpNaturalScaled((int)BigInteger.Abs(integerPart), scale);
        var (numerator, denominator) = integerPart.Sign >= 0
            ? (fractionExp * wholeExp, scale * scale)
            : (fractionExp * scale, scale * wholeExp);
        return RoundRational(numerator, denominator, 0).ToDecimal128(negative: false);
    }

    /// <summary><c>e^f · scale</c> for <c>0 &lt;= f &lt; 1</c> given as <c>f · scale</c>, by the Taylor series.</summary>
    private static BigInteger ExpFractionScaled(BigInteger fractionScaled, BigInteger scale)
    {
        var sum = scale;
        var term = scale;
        for (var k = 1; ; k++)
        {
            term = term * fractionScaled / scale / k;
            if (term.IsZero) break;
            sum += term;
        }
        return sum;
    }

    /// <summary>
    /// <c>e^n · scale</c> for a non-negative integer <c>n</c>: <c>e · scale</c> from the
    /// series, then binary powering on scaled integers (each product truncated back to the
    /// scale — a relative slack of 10^-80 per multiplication, amplified at most <c>n</c>-fold).
    /// </summary>
    private static BigInteger ExpNaturalScaled(int n, BigInteger scale)
    {
        var e = ExpFractionScaled(scale, scale); // e^1
        var result = scale;
        var basePower = e;
        for (var remaining = n; remaining > 0; remaining >>= 1)
        {
            if ((remaining & 1) == 1)
                result = result * basePower / scale;
            if (remaining > 1)
                basePower = basePower * basePower / scale;
        }
        return result;
    }
}
