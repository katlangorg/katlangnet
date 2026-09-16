using System.Text;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Order;

namespace KatLang.Benchmarks;

/// <summary>
/// Shared sources for the numeric-literal lexing benchmarks. The lexer scans a numeric
/// literal itself and then hands the selected text to <c>Decimal128</c> parsing; these
/// workloads measure that conversion step inside real <see cref="Lexer.Tokenize"/> runs.
/// Every single-literal source embeds the literal in an assignment row (<c>X = 123</c>)
/// because a literal that IS the whole source would be special-cased by
/// <c>string.Substring</c> (it returns the source instance) and hide the ordinary cost.
/// </summary>
internal static class LexerNumericLiteralScenarios
{
	internal const string RealisticSource = """
		# Physical constants (CODATA 2018) and a few derived quantities.
		SpeedOfLight = 299792458
		Planck = 6.62607015e-34
		ReducedPlanck = Planck / (2 * 3.14159265358979323846)
		Boltzmann = 1.380649e-23
		Avogadro = 6.02214076e23
		GasConstant = Boltzmann * Avogadro
		Gravitation = 6.67430e-11
		ElectronMass = 9.1093837015e-31
		ProtonMass = 1.67262192369e-27
		ElementaryCharge = 1.602176634e-19
		FineStructure = 0.0072973525693
		RydbergEnergy = 13.605693122994
		SolarMass = 1.98847e30
		EarthMass = 5.9722e24
		EarthRadius = 6371000
		AstronomicalUnit = 149597870700
		SecondsPerYear = 31557600
		PhotonEnergy(wavelength) = Planck * SpeedOfLight / wavelength
		KineticEnergy(mass, velocity) = 0.5 * mass * velocity ^ 2
		EscapeVelocity(mass, radius) = (2 * Gravitation * mass / radius) ^ 0.5
		OrbitalPeriod(radius, mass) = 2 * 3.14159265358979 * (radius ^ 3 / (Gravitation * mass)) ^ 0.5
		IdealGasPressure(moles, temperature, volume) = moles * GasConstant * temperature / volume
		Redshift(observed, emitted) = observed / emitted - 1
		PhotonEnergy(5.5e-7)
		KineticEnergy(1250, 27.78)
		EscapeVelocity(EarthMass, EarthRadius)
		OrbitalPeriod(AstronomicalUnit, SolarMass) / SecondsPerYear
		IdealGasPressure(2.5, 293.15, 0.0224)
		Redshift(656.46, 656.28)
		ElementaryCharge * 1e19 + FineStructure * 137.035999084
		ProtonMass / ElectronMass
		RydbergEnergy * 0.75 - 10.2
		""";

	/// <summary>
	/// The five literal shapes cycled through the generated sources: an integer, a
	/// fraction, an integer with an exponent, a leading-zero fraction, and a fraction
	/// with a signed exponent — the common forms a calculation program writes.
	/// </summary>
	private static string PlainLiteral(int i) => (i % 5) switch
	{
		0 => $"{i}",
		1 => $"{i}.{i % 100}",
		2 => $"{i}e{i % 10}",
		3 => $"0.{i}",
		_ => $"{i}.5e-{i % 5}",
	};

	/// <summary>The same shapes written with digit separators inside every digit run.</summary>
	private static string SeparatedLiteral(int i) => (i % 5) switch
	{
		0 => $"{i}_000",
		1 => $"{i}_000.{i % 100}_5",
		2 => $"1_{i}e1_{i % 10}",
		3 => $"0.0_0{i}",
		_ => $"{i}_5.2_5e-{i % 5}",
	};

	/// <summary>
	/// <paramref name="count"/> literals, ten per row separated by commas: a literal-dense
	/// root output where numeric conversion dominates the token stream.
	/// </summary>
	internal static string BuildDenseSource(int count, bool separated)
	{
		var source = new StringBuilder();
		for (var i = 0; i < count; i++)
		{
			source.Append(separated ? SeparatedLiteral(i + 1) : PlainLiteral(i + 1));
			source.Append(i % 10 == 9 ? '\n' : ',');
			if (i % 10 != 9)
				source.Append(' ');
		}

		return source.ToString();
	}

	internal static void AssertLexesCleanly(string source, int expectedNumberTokens)
	{
		var (tokens, diagnostics) = Lexer.Tokenize(source);
		if (diagnostics.Count != 0)
		{
			throw new InvalidOperationException(
				"Numeric-literal benchmark source produced lexer diagnostics: "
				+ string.Join("; ", diagnostics.Select(d => d.Message)));
		}

		var numberTokens = tokens.Count(t => t.Kind == TokenKind.Number);
		if (numberTokens != expectedNumberTokens)
		{
			throw new InvalidOperationException(
				$"Numeric-literal benchmark source expected {expectedNumberTokens} number tokens, found {numberTokens}.");
		}
	}

	internal static void AssertParsesCleanly(string source)
	{
		var result = Parser.Parse(source);
		if (result.HasErrors)
		{
			throw new InvalidOperationException(
				"Numeric-literal benchmark source failed to parse: "
				+ string.Join("; ", result.Diagnostics.Select(d => d.Message)));
		}
	}
}

/// <summary>
/// One numeric literal per <see cref="Lexer.Tokenize"/> call, embedded in an assignment
/// row: the cost of converting each representative literal shape to a value. The
/// overflow literal (<c>1e6145</c>) also exercises the diagnostic path; the 38-digit
/// literal rounds to Decimal128's 34 significant digits.
/// </summary>
[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.Declared)]
public class LexerSingleNumericLiteralBenchmarks
{
	private string source = string.Empty;

	[Params(
		"123",
		"123.456",
		"6.022e23",
		"1234567890123456789012345678901234",
		"12345678901234567890123456789012345678",
		"1e6145",
		"1_000_000")]
	public string Literal { get; set; } = string.Empty;

	[GlobalSetup]
	public void Setup()
	{
		source = "X = " + Literal;
		var (tokens, diagnostics) = Lexer.Tokenize(source);
		if (tokens.Count != 4 || tokens[2].Kind != TokenKind.Number || tokens[2].Length != Literal.Length)
			throw new InvalidOperationException($"Benchmark literal '{Literal}' did not lex as one number token.");
		var expectsOverflow = Literal == "1e6145";
		if ((diagnostics.Count != 0) != expectsOverflow)
			throw new InvalidOperationException($"Benchmark literal '{Literal}' produced an unexpected diagnostic set.");
	}

	[Benchmark]
	public IReadOnlyList<Token> TokenizeAssignment() => Lexer.Tokenize(source).Tokens;
}

/// <summary>
/// Literal-dense sources: a realistic constants-and-formulas program, a generated source
/// of 2,000 plain literals, and the same generated source with digit separators inside
/// every digit run (the separator path is measured separately because it strips the
/// separators before conversion). <c>Parse</c> measures the whole front end on the plain
/// generated source, so the lexer's share of a real parse is visible.
/// </summary>
[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.Declared)]
public class LexerNumericDenseSourceBenchmarks
{
	private const int DenseLiteralCount = 2000;

	private string denseSource = string.Empty;
	private string separatedDenseSource = string.Empty;

	[GlobalSetup]
	public void Setup()
	{
		LexerNumericLiteralScenarios.AssertLexesCleanly(LexerNumericLiteralScenarios.RealisticSource, expectedNumberTokens: 38);
		LexerNumericLiteralScenarios.AssertParsesCleanly(LexerNumericLiteralScenarios.RealisticSource);

		denseSource = LexerNumericLiteralScenarios.BuildDenseSource(DenseLiteralCount, separated: false);
		LexerNumericLiteralScenarios.AssertLexesCleanly(denseSource, DenseLiteralCount);
		LexerNumericLiteralScenarios.AssertParsesCleanly(denseSource);

		separatedDenseSource = LexerNumericLiteralScenarios.BuildDenseSource(DenseLiteralCount, separated: true);
		LexerNumericLiteralScenarios.AssertLexesCleanly(separatedDenseSource, DenseLiteralCount);
		LexerNumericLiteralScenarios.AssertParsesCleanly(separatedDenseSource);
	}

	[Benchmark]
	public IReadOnlyList<Token> TokenizeRealistic() => Lexer.Tokenize(LexerNumericLiteralScenarios.RealisticSource).Tokens;

	[Benchmark]
	public IReadOnlyList<Token> TokenizeDense() => Lexer.Tokenize(denseSource).Tokens;

	[Benchmark]
	public IReadOnlyList<Token> TokenizeSeparatedDense() => Lexer.Tokenize(separatedDenseSource).Tokens;

	[Benchmark]
	public ParseResult ParseDense() => Parser.Parse(denseSource);
}
