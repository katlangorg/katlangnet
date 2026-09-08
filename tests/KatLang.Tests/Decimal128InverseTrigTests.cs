using System.Globalization;
using System.Numerics;
using System.Runtime.InteropServices;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// K6-R3 endpoint accuracy and routing. The original known answers were derived with
/// Perl Math::BigFloat 1.999837 at 90 digits; the review rechecked them with mpmath 1.3.0.
/// DeepEndpointCases uses exact decimal input strings and mpmath acos/asin at 200 digits,
/// cross-checked by a 220-digit decimal Taylor series with Chudnovsky π.
/// These external references do not use Decimal128 inverse trig or repeat its FMA formula.
/// The assertions compare exact integer-scaled reference intervals, not a parsed
/// 34-digit reference: ulp = 10^(floor(log10(abs(reference))) - 33).
/// No tolerance here is a universal accuracy or correct-rounding claim.
/// </summary>
public class Decimal128InverseTrigTests
{
    private static Decimal128 N(string text)
        => Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture);

    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static Decimal128 EvalSingle(string source)
    {
        var result = Evaluator.RunFlat(Program(source));
        if (result.IsError)
            Assert.Fail($"Expected `{source}` to succeed but got: {result.Error}");
        return Assert.Single(result.Value);
    }

    /// <summary>One unit in the last (34th) significant place of <paramref name="value"/>.</summary>
    private static Decimal128 UlpOf(Decimal128 value)
        => Decimal128.ScaleB(Decimal128.One, Decimal128.ILogB(value) - 33);

    private static (BigInteger Coefficient, int Exponent) ExactDecimal(string text)
    {
        var parts = text.Split(['e', 'E']);
        var exponent = parts.Length == 2 ? int.Parse(parts[1], CultureInfo.InvariantCulture) : 0;
        var dot = parts[0].IndexOf('.');
        if (dot >= 0)
            exponent -= parts[0].Length - dot - 1;
        return (BigInteger.Parse(parts[0].Replace(".", ""), CultureInfo.InvariantCulture), exponent);
    }

    private static void AssertWithinUlps(string reference, Decimal128 actual, int maxUlps)
        => AssertWithinUlps(reference, actual, maxUlps.ToString(CultureInfo.InvariantCulture));

    private static void AssertWithinUlps(string reference, Decimal128 actual, string maxUlps)
    {
        Assert.True(Decimal128.IsFinite(actual), $"Non-finite result for {reference}: {actual}");
        var (r, re) = ExactDecimal(reference);
        if (r.IsZero)
        {
            Assert.Equal(Decimal128.Zero, actual);
            return;
        }
        var (a, ae) = ExactDecimal(actual.ToString(CultureInfo.InvariantCulture));
        var (limit, le) = ExactDecimal(maxUlps);
        var ulpExponent = re + BigInteger.Abs(r).ToString(CultureInfo.InvariantCulture).Length - 34;
        var common = Math.Min(Math.Min(re, ae), ulpExponent + le);
        var distance = BigInteger.Abs(a * BigInteger.Pow(10, ae - common)
            - r * BigInteger.Pow(10, re - common));
        // One unit of the final supplied reference digit encloses truncation/rounding
        // uncertainty. Require the whole interval to fit, without Decimal128 rounding.
        var uncertainty = BigInteger.Pow(10, re - common);
        var allowed = limit * BigInteger.Pow(10, ulpExponent + le - common);
        Assert.True(distance + uncertainty <= allowed,
            $"{actual} exceeds {maxUlps} numerical ulp from {reference}.");
    }

    private static void AssertSameBits(Decimal128 expected, Decimal128 actual)
        => Assert.True(
            MemoryMarshal.AsBytes(MemoryMarshal.CreateReadOnlySpan(ref expected, 1))
                .SequenceEqual(MemoryMarshal.AsBytes(MemoryMarshal.CreateReadOnlySpan(ref actual, 1))),
            $"Representation differs: expected {expected}, got {actual}.");

    // ── Endpoint band: known answers ─────────────────────────────────────────

    // Both spellings appear because the endpoint routing lives behind the one
    // shared native wrapper; the catastrophic rows fail at 17da00a by 1e11..1e28 ulp.
    [Theory]
    // +1 side of acos (results are tiny: relative accuracy is what the platform lost)
    [InlineData("acos(1 - 1e-12)", "1.4142135623732128999318865086469358471334467e-6", 2)]
    [InlineData("acos(1 - 1e-20)", "1.4142135623730950488028672355116756577770093e-10", 2)]
    [InlineData("acos(1 - 1e-30)", "1.4142135623730950488016887242098159296998696e-15", 2)]
    [InlineData("Math.Acos(1 - 1e-30)", "1.4142135623730950488016887242098159296998696e-15", 2)]
    [InlineData("acos(1 - 1e-33)", "4.4721359549995793928183473374625528435592330e-17", 2)]
    // The first decade of the band, where the direct path begins losing accuracy.
    [InlineData("acos(0.99999)", "4.4721396817879271723396663048526822600177185e-3", 2)]
    [InlineData("acos(0.9999512345678901234567890123456789)", "9.8758117093829013029879032726239405441636291e-3", 2)]
    [InlineData("acos(0.9999991234567890123456789012345678)", "1.3240417962000678785959668004308952180934445e-3", 2)]
    [InlineData("acos(0.9999999999999999999987654321098765)", "4.9690399276389397915776534339960219802221331e-11", 2)]
    [InlineData("acos(0.9999999999999999999999999999999998)", "2.0000000000000000000000000000000000333333333e-17", 2)]
    [InlineData("acos(0.9999999999999999999999999999999999)", "1.4142135623730950488016887242096980903547849e-17", 2)]
    // -1 side of acos (results near π: the platform's absolute error showed as 22..29 digits)
    [InlineData("acos(-1 + 1e-12)", "3.1415912393762308652497434513929942372613223", 1)]
    [InlineData("acos(-1 + 1e-20)", "3.1415926534483718822253338783992161606460018", 1)]
    [InlineData("acos(-1 + 1e-30)", "3.1415926535897918242490810101844540825084452", 1)]
    [InlineData("Math.Acos(-1 + 1e-33)", "3.1415926535897931937412838332837089560136960", 1)]
    [InlineData("acos(-0.9999512345678901234567890123456789)", "3.1317168418804103371596554800068789436530058", 1)]
    [InlineData("acos(-0.9999991234567890123456789012345678)", "3.1402686117935931705840474164790719889790760", 1)]
    [InlineData("acos(-0.9999999999999999999987654321098765)", "3.1415926535401028391862539853637263498572092", 1)]
    [InlineData("acos(-0.9999999999999999999999999999999998)", "3.1415926535897932184626433832795028841971694", 1)]
    [InlineData("acos(-0.9999999999999999999999999999999999)", "3.1415926535897932243205077595485523961802822", 1)]
    // asin, both sides (results near ±π/2)
    [InlineData("asin(1 - 1e-12)", "1.5707949125813342460184217597532427951627376", 1)]
    [InlineData("asin(1 - 1e-20)", "1.5707963266534752629940121867594647185474171", 1)]
    [InlineData("asin(1 - 1e-30)", "1.5707963267948952050177593185447026404098605", 1)]
    [InlineData("Math.Asin(1 - 1e-30)", "1.5707963267948952050177593185447026404098605", 1)]
    [InlineData("asin(1 - 1e-33)", "1.5707963267948965745099621416439575139151113", 1)]
    [InlineData("asin(0.9999512345678901234567890123456789)", "1.5609205150855137179283337883671275015544211", 1)]
    [InlineData("asin(0.9999991234567890123456789012345678)", "1.5694722849986965513527257248393205468804913", 1)]
    [InlineData("asin(0.9999999999999999999987654321098765)", "1.5707963267452062199549322937239749077586245", 1)]
    [InlineData("asin(0.9999999999999999999999999999999998)", "1.5707963267948965992313216916397514420985847", 1)]
    [InlineData("asin(0.9999999999999999999999999999999999)", "1.5707963267948966050891860679088009540816975", 1)]
    [InlineData("asin(-1 + 1e-12)", "-1.5707949125813342460184217597532427951627376", 1)]
    [InlineData("asin(-1 + 1e-20)", "-1.5707963266534752629940121867594647185474171", 1)]
    [InlineData("asin(-1 + 1e-30)", "-1.5707963267948952050177593185447026404098605", 1)]
    [InlineData("Math.Asin(-1 + 1e-33)", "-1.5707963267948965745099621416439575139151113", 1)]
    [InlineData("asin(-0.99999)", "-1.5663241871131086920589820253348987598385670", 1)]
    [InlineData("asin(-0.9999991234567890123456789012345678)", "-1.5694722849986965513527257248393205468804913", 1)]
    [InlineData("asin(-0.9999999999999999999987654321098765)", "-1.5707963267452062199549322937239749077586245", 1)]
    [InlineData("asin(-0.9999999999999999999999999999999998)", "-1.5707963267948965992313216916397514420985847", 1)]
    [InlineData("asin(-0.9999999999999999999999999999999999)", "-1.5707963267948966050891860679088009540816975", 1)]
    public void EndpointBand_MatchesIndependentReference(string source, string reference, int maxUlps)
        => AssertWithinUlps(reference, EvalSingle(source), maxUlps);

    [Fact]
    public void Acos_OneMinus1e30_RecoversTheLostDigits()
    {
        // The audit's headline case: 17da00a returned 1.414213564615384992009383671093284e-15,
        // about 2.24e24 result ulp from the reference.
        AssertWithinUlps("1.4142135623730950488016887242098159296998696e-15", EvalSingle("acos(1 - 1e-30)"), maxUlps: 2);
        // And the mirrored -1 side / asin cases that carried the same 2.2e-24 absolute error.
        AssertWithinUlps("1.5707963267948952050177593185447026404098605", EvalSingle("asin(1 - 1e-30)"), maxUlps: 1);
        AssertWithinUlps("3.1415926535897918242490810101844540825084452", EvalSingle("acos(-1 + 1e-30)"), maxUlps: 1);
    }

    // Compact external goldens: enumerate the last nine interior values and retain
    // the deep sweep maximum, a near-halfway case, and a result exponent transition.
    [Theory]
    [InlineData("0.9999999999999999999999999999999991", "0.0000000000000000424264068711928514640506617262909455390706716007723019991000216115432954867", "3.14159265358979319603623651208665142014650767308416028190427299153551440719", "1.57079632679489657680491482044689997804792297339660737141680069538160620404")]
    [InlineData("0.9999999999999999999999999999999992", "0.0000000000000000400000000000000000000000000000000026666666666666666666666666666666671466667", "3.14159265358979319846264338327950288419716939937510315430827792564114973962", "1.57079632679489657923132169163975144209858469968755024382080562948724153648")]
    [InlineData("0.9999999999999999999999999999999993", "0.0000000000000000374165738677394138558374873231654952001936736959197443868908818578544546855", "3.1415926535897932010460695155400890283596820762096106207812708963880720194", "1.57079632679489658181474782390033758626109737652205771029379860023416381625")]
    [InlineData("0.9999999999999999999999999999999994", "0.0000000000000000346410161513775458705489268301174490709069126450849060885624810949112611078", "3.14159265358979320382162723190195701364824256925765675006803194722291031772", "1.57079632679489658459030554026220557154965786957010383958055965106900211458")]
    [InlineData("0.9999999999999999999999999999999995", "0.0000000000000000316227766016837933199889354443271866548112431300768899347806920415588150013", "3.14159265358979320683986678159570956420823395504791916616370146223092647151", "1.57079632679489658760854508995595812210964925536036625567622916607701826836")]
    [InlineData("0.9999999999999999999999999999999996", "0.0000000000000000282842712474619009760337744841939625142024790896023273313260775662801201352", "3.14159265358979321017837213581760190816339491518114330677246550270548907496", "1.57079632679489659094705044417785046606481021549359039628499320655158087182")]
    [InlineData("0.9999999999999999999999999999999997", "0.0000000000000000244948974278317809819728407470589145320319105023612258336479443489824931012", "3.14159265358979321396774595544772190222432865231619128894303408994659057264", "1.5707963267948965947364242638079704601257439526286383784555617937926823695")]
    [InlineData("0.9999999999999999999999999999999998", "0.0000000000000000200000000000000000000000000000000003333333333333333333333333333333333483333", "3.14159265358979321846264338327950288419716939937510548764161125897448307295", "1.57079632679489659923132169163975144209858469968755257715413896282057486981")]
    [InlineData("0.9999999999999999999999999999999999", "0.0000000000000000141421356237309504880168872420969809035478489515274014652408577307155006504", "3.14159265358979322432050775954855239618028215727812491742709564078041494105", "1.5707963267948966050891860679088009540816974575905720069396233446265067379")]
    [InlineData("0.9999999999999999999999999994547575", "0.0000000000000330224923347708569045678528361889047458891772365230302296130112470784225476", "3.14159265358976021597030861242259831634433321047035993179770806927758679327", "1.57079632679486359673898692078284687424574851078280702131023577312367859013")]
    [InlineData("0.9999999999999999999999999999999078", "0.000000000000000429418211071677769384193975620783742674401837393532812111351419749451151559", "3.14159265358979280904443231160173350000319377859136314657310719877500429493", "1.57079632679489618981311061996198205790460907890381023608563490262109609179")]
    [InlineData("0.9999999999999999995000000000000001", "0.000000000999999999999999900041666666666661654171354166666167289323614211247044993931", "3.14159265258979323846264348323783621753050774520375165430877730298420219504", "1.5707963257948966192313217915980847754319230455161987438213050068302939919")]
    [InlineData("0.9999999999999999994999999999999999", "0.00000000100000000000000010004166666666666167917135416666716729401111421124700332824", "3.14159265258979323846264328323783621753050772020375165430777729829670219504", "1.5707963257948966192313215915980847754319230205161987438203050021427939919")]
    public void DeepEndpointCases_MatchIndependentReferences(
        string input, string acosPositive, string acosNegative, string asinPositive)
    {
        AssertWithinUlps(acosPositive, EvalSingle($"acos({input})"), "1.6");
        AssertWithinUlps(acosNegative, EvalSingle($"Math.Acos(-{input})"), "0.51");
        AssertWithinUlps(asinPositive, EvalSingle($"Math.Asin({input})"), "0.51");
        AssertWithinUlps("-" + asinPositive, EvalSingle($"asin(-{input})"), "0.51");
    }

    [Fact]
    public void NearestInteriorInputs_AndTheirArithmeticSpellingsAreExact()
    {
        var positive = N("0.9999999999999999999999999999999999");
        var negative = -positive;
        AssertSameBits(positive, Decimal128.BitDecrement(Decimal128.One));
        AssertSameBits(negative, Decimal128.BitIncrement(-Decimal128.One));
        AssertSameBits(positive, EvalSingle("1 - 1e-34"));
        AssertSameBits(negative, EvalSingle("-1 + 1e-34"));
        Assert.Equal(N("1e-34"), Decimal128.One - positive);
        Assert.Equal(Decimal128.One, EvalSingle("1 - 1e-35"));
        Assert.Equal(-Decimal128.One, EvalSingle("-1 + 1e-35"));
        Assert.Equal(-34, Decimal128.ILogB(Decimal128.GetQuantum(positive)));
        // FMA rounds the exact complement once. Multiplying first discards x²'s
        // low digits: at a gap of 1e-20 it leaves 2e-20 instead of the exact complement.
        var x = N("0.99999999999999999999");
        var complement = Decimal128.FusedMultiplyAdd(-x, x, Decimal128.One);
        Assert.Equal(N("1.99999999999999999999e-20"), complement);
        Assert.NotEqual(Decimal128.One - x * x, complement);
    }

    [Fact]
    public void OutsideBand_AndEndpoints_PreserveRawRepresentations()
    {
        var boundary = N("0.9999");
        var nanBytes = MemoryMarshal.AsBytes(
            new[] { Decimal128.NaN }.AsSpan()).ToArray();
        nanBytes[0] = 37; // Nonzero payload, retained as an input to the direct path.
        var payloadNaN = MemoryMarshal.Read<Decimal128>(nanBytes);
        foreach (var x in new[] {
            N("0"), N("-0"), N("0e-100"), N("-0e+100"), N("0.50"), N("-0.500"),
            boundary, -boundary, Decimal128.BitDecrement(boundary), -Decimal128.BitDecrement(boundary),
            Decimal128.Epsilon, -Decimal128.Epsilon,
            Decimal128.One, -Decimal128.One, N("1.00"), N("-1.00"),
            Decimal128.BitIncrement(Decimal128.One), Decimal128.BitDecrement(-Decimal128.One),
            Decimal128.PositiveInfinity, Decimal128.NegativeInfinity,
            Decimal128.NaN, -Decimal128.NaN, payloadNaN, -payloadNaN })
        {
            AssertSameBits(Decimal128.Acos(x), Decimal128Numerics.Acos(x));
            AssertSameBits(Decimal128.Asin(x), Decimal128Numerics.Asin(x));
        }
    }

    [Theory]
    [InlineData("acos(0.9999000000000000000000000000000317)", "0.0141422534775128775962402258154145211877277810138768746193618123633544801175", "1.2")]
    [InlineData("acos(-0.9999201049463989999669472383812971)", "3.12895175825017441975460503782486149632945736451374747327237135722814282267", "0.51")]
    [InlineData("asin(0.9999000000000000000000000000000676)", "1.55665407331738374163508146582687549772053019120436234894648325528525877823", "0.51")]
    public void InBandRoundingTradeoffs_RemainSmall(string source, string reference, string maxUlps)
        => AssertWithinUlps(reference, EvalSingle(source), maxUlps);

    // ── Mid-domain controls: the platform path is preserved bit-for-bit ─────

    [Theory]
    [InlineData("acos(0.5)", "0.5", true, "1.0471975511965977461542144610931676280657231")]
    [InlineData("asin(0.5)", "0.5", false, "0.52359877559829887307710723054658381403286157")]
    [InlineData("acos(-0.5)", "-0.5", true, "2.0943951023931954923084289221863352561314463")]
    [InlineData("acos(0.9)", "0.9", true, "0.45102681179626243254464463579435182620342251")]
    [InlineData("asin(0.9)", "0.9", false, "1.1197695149986341866866770558453996158951622")]
    [InlineData("acos(-0.9)", "-0.9", true, "2.6905658417935308059179987474851510579937469")]
    [InlineData("acos(0.3)", "0.3", true, "1.2661036727794991112593187304122222751440247")]
    [InlineData("asin(-0.3)", "-0.3", false, "-0.30469265401539750797200296122752916695456003")]
    [InlineData("acos(0.7071067811865475244008443621048490)", "0.7071067811865475244008443621048490", true, "0.78539816339744830961566084581987577660644013")]
    [InlineData("asin(0.1234567890123456789012345678901234)", "0.1234567890123456789012345678901234", false, "0.12377257243915793136626255402941413340175449")]
    [InlineData("acos(0.99)", "0.99", true, "0.14153947332442721874578935697502701499398293")]
    [InlineData("acos(0)", "0", true, "1.5707963267948966192313216916397514420985847")]
    // The last inputs on the platform side of the band (|x| = 0.9999 is NOT in the band).
    [InlineData("acos(0.9999)", "0.9999", true, "1.4142253477512877596240225817656105724403066e-2")]
    [InlineData("asin(-0.9999)", "-0.9999", false, "-1.5566540733173837416350814658220953363741816")]
    [InlineData("acos(-0.9999)", "-0.9999", true, "3.1274504001122803608664031574618467784727663")]
    public void OutsideTheBand_PreservesThePlatformResultAndMatchesSelectedReferences(string source, string input, bool isAcos, string reference)
    {
        var value = EvalSingle(source);
        var x = N(input);
        AssertSameBits(Evaluator.CanonicalizeMathResult(
            isAcos ? Decimal128.Acos(x) : Decimal128.Asin(x)), value);
        // A one-ulp check is an accuracy check, not evidence of correct rounding.
        AssertWithinUlps(reference, value, maxUlps: 1);
    }

    [Fact]
    public void BandStart_IsOneMinusTenToTheMinusFour_AndBelowItTheHelperDelegates()
    {
        Assert.Equal(N("0.9999"), Decimal128Numerics.InverseTrigEndpointBandStart);
        Assert.Equal(Decimal128.One - N("1e-4"), Decimal128Numerics.InverseTrigEndpointBandStart);

        foreach (var text in new[] { "0", "-0", "0.5", "-0.5", "0.9", "-0.9", "0.99", "0.999", "0.9999", "-0.9999", "1e-30", "-1e-30" })
        {
            var x = N(text);
            AssertSameBits(Decimal128.Acos(x), Decimal128Numerics.Acos(x));
            AssertSameBits(Decimal128.Asin(x), Decimal128Numerics.Asin(x));
        }
    }

    // ── Exact endpoints, signed zero, quanta ──────────────────────────────────

    [Fact]
    public void ExactEndpoints_AgreeWithTheExistingRoundedConstants()
    {
        // Compatibility with rounded constants: π rounds up and π/2 rounds down.
        // Decimal128.Pi / 2 need not equal the existing inverse-trig π/2 value.
        var pi = N("3.141592653589793238462643383279503");
        var halfPi = N("1.570796326794896619231321691639751");
        Assert.Equal(Decimal128.Pi, pi);

        foreach (var one in new[] { "1", "1.0", "1.00" })
        {
            var acosOne = EvalSingle($"acos({one})");
            Assert.Equal(Decimal128.Zero, acosOne);
            Assert.False(Decimal128.IsNegative(acosOne), "acos(1) must be +0");
            Assert.Equal(pi, EvalSingle($"Math.Acos(-{one})"));
            Assert.Equal(halfPi, EvalSingle($"asin({one})"));
            Assert.Equal(-halfPi, EvalSingle($"Math.Asin(-{one})"));
        }

        // Signed zero: asin is odd (asin(-0) = -0); acos(±0) = π/2.
        var asinNegativeZero = EvalSingle("asin(-0)");
        Assert.Equal(Decimal128.Zero, asinNegativeZero);
        Assert.True(Decimal128.IsNegative(asinNegativeZero), "asin(-0) must be -0");
        Assert.False(Decimal128.IsNegative(EvalSingle("asin(0)")));
        Assert.Equal(halfPi, EvalSingle("acos(-0)"));
        Assert.Equal(halfPi, EvalSingle("acos(0)"));
    }

    [Theory]
    [InlineData("acos(2)")]
    [InlineData("asin(-2)")]
    [InlineData("acos(1.000000000000000000000000000000001)")] // the first value above the band
    [InlineData("asin(-1.000000000000000000000000000000001)")]
    [InlineData("Math.Acos(-1.000000000000000000000000000000001)")]
    [InlineData("acos(sqrt(-1))")]   // NaN
    [InlineData("asin(sqrt(-1))")]
    [InlineData("acos(exp(20000))")] // +Infinity
    [InlineData("asin(-exp(20000))")] // -Infinity
    [InlineData("Math.Asin(ln(0))")]  // -Infinity
    public void OutsideTheDomain_StaysNaN(string source)
        => Assert.True(Decimal128.IsNaN(EvalSingle(source)), $"{source} must be NaN");

    // ── Branch boundary: no cliff, no non-monotonic step ─────────────────────

    [Fact]
    public void BranchBoundary_IsMonotoneAndSmoothOnBothSidesForBothFunctions()
    {
        // The derivative 1 / sqrt(1 - x²) is 70.7124… at |x| = 0.9999, so consecutive
        // Decimal128 inputs (1e-34 apart) map to outputs 7.07124e-33 apart: 7 ulp for
        // results near π/2 or π and about 707 ulp for acos near +1.
        // This local sampled walk checks direction and step size; it does not
        // establish an error or monotonicity bound for unsampled inputs.
        // Walk 40 inputs on each side of the band start.
        var expectedStep = N("7.0712445951902e-33");
        var start = N("0.9998999999999999999999999999999960");

        foreach (var sign in new[] { 1, -1 })
        {
            foreach (var isAcos in new[] { true, false })
            {
                var magnitude = start;
                Decimal128? previous = null;
                for (var i = 0; i <= 80; i++)
                {
                    var input = sign < 0 ? -magnitude : magnitude;
                    var value = isAcos ? Decimal128Numerics.Acos(input) : Decimal128Numerics.Asin(input);
                    if (previous is { } previousValue)
                    {
                        var step = value - previousValue;
                        // Growing |x|: acos falls on the +1 side and rises on the -1 side; asin the opposite.
                        var expectedSign = isAcos ? -sign : sign;
                        Assert.True(
                            Decimal128.Sign(step) == expectedSign,
                            $"{(isAcos ? "acos" : "asin")}({input}) stepped the wrong way ({step}).");
                        var deviation = Decimal128.Abs(Decimal128.Abs(step) - expectedStep);
                        Assert.True(
                            deviation <= UlpOf(value) * 4,
                            $"{(isAcos ? "acos" : "asin")}({input}) stepped by {step}, expected {expectedStep} within 4 ulp.");
                    }

                    previous = value;
                    magnitude = Decimal128.BitIncrement(magnitude);
                }
            }
        }
    }

    [Theory]
    // At the band start (platform path) and one Decimal128 step on either side of it.
    [InlineData("acos(0.9999)", "1.4142253477512877596240225817656105724403066e-2")]
    [InlineData("acos(0.9999000000000000000000000000000001)", "1.4142253477512877596240225817649034479807876e-2")]
    [InlineData("acos(0.9998999999999999999999999999999999)", "1.4142253477512877596240225817663176968998256e-2")]
    [InlineData("asin(0.9999)", "1.5566540733173837416350814658220953363741816")]
    [InlineData("asin(0.9999000000000000000000000000000001)", "1.5566540733173837416350814658221024076187768")]
    [InlineData("asin(0.9998999999999999999999999999999999)", "1.5566540733173837416350814658220882651295864")]
    [InlineData("acos(-0.9999)", "3.1274504001122803608664031574618467784727663")]
    [InlineData("acos(-0.9999000000000000000000000000000001)", "3.1274504001122803608664031574618538497173615")]
    [InlineData("acos(-0.9998999999999999999999999999999999)", "3.1274504001122803608664031574618397072281711")]
    [InlineData("asin(-0.9999000000000000000000000000000001)", "-1.5566540733173837416350814658221024076187768")]
    public void BranchBoundary_MatchesTheReferenceOnBothSides(string source, string reference)
        => AssertWithinUlps(reference, EvalSingle(source), maxUlps: 2);

    // ── Dispatch parity ──────────────────────────────────────────────────────

    [Fact]
    public async Task EndpointBand_AgreesAcrossFlatCountedAndAsyncDispatch()
    {
        const string source =
            "CosInputs = [1 - 1e-30, -1 + 1e-33, 0.9999000000000000000000000000000001, 0.9999, 0.5]\n"
            + "SinInputs = [1 - 1e-30, -1 + 1e-33, -0.9999000000000000000000000000000001, 0.9999, -0.5]\n"
            + "CosInputs.map(acos)\nSinInputs.map(Math.Asin)";
        var program = Program(source);

        var flat = Evaluator.RunFlat(program);
        Assert.True(flat.IsOk, flat.IsError ? flat.Error.ToString() : null);
        Assert.Equal(10, flat.Value.Count);

        var counted = Evaluator.RunCounted(program);
        Assert.True(counted.IsOk);
        Assert.Equal(flat.Value, counted.Value.Value.ToHostAtoms());

        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var twin = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(program, cache));
        Assert.True(cache.AsyncAccesses > 0);
        Assert.Equal(0, cache.SyncAccesses);
        Assert.True(twin.IsOk);
        var twinAtoms = twin.Value.Value.ToHostAtoms();
        Assert.Equal(flat.Value.Count, twinAtoms.Count);
        for (var i = 0; i < flat.Value.Count; i++)
        {
            AssertSameBits(flat.Value[i], counted.Value.Value.ToHostAtoms()[i]);
            AssertSameBits(flat.Value[i], twinAtoms[i]);
        }

        var generic = EvaluatorTestSupport.Eval(source, enableLoopOptimization: false);
        var optimized = EvaluatorTestSupport.Eval(source, enableLoopOptimization: true);
        Assert.True(generic.IsOk);
        Assert.True(optimized.IsOk);
        Assert.Equal(flat.Value, generic.Value);
        Assert.Equal(flat.Value, optimized.Value);

        // The band results really are the reformulated ones (not the platform's).
        AssertWithinUlps("1.4142135623730950488016887242098159296998696e-15", flat.Value[0], maxUlps: 2);
        AssertWithinUlps("-1.5707963267948965745099621416439575139151113", flat.Value[6], maxUlps: 1);
    }
}
