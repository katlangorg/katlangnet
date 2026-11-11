using System.Text;
using BenchmarkDotNet.Configs;
using BenchmarkDotNet.ConsoleArguments;
using BenchmarkDotNet.ConsoleArguments.ListBenchmarks;
using BenchmarkDotNet.Loggers;
using BenchmarkDotNet.Reports;
using BenchmarkDotNet.Running;

namespace KatLang.Benchmarks;

/// <summary>
/// Runs BenchmarkDotNet for the host and turns what it returns into the exit code decided by
/// <see cref="BenchmarkHostExit.Decide"/>. Everything BenchmarkDotNet-specific about that decision is here.
/// </summary>
internal static class BenchmarkHostRun
{
	public static int Run(string[] args)
	{
		var config = PinnedProjectToolchain.CreateConfig();
		var summaries = BenchmarkSwitcher.FromAssembly(typeof(Program).Assembly).Run(args, config).ToArray();

		// Only an invocation without summaries needs to know whether a run was asked for at all.
		var runRequested = summaries.Length > 0 || IsRunRequested(args, config);
		var exit = BenchmarkHostExit.Decide(runRequested, summaries.Select(Outcome).ToArray());
		if (exit.Message is not null)
		{
			// A failure reason goes to the error stream; the exit-0 warning stays on the output stream.
			var writer = exit.ExitCode == BenchmarkHostExit.Success ? Console.Out : Console.Error;
			writer.WriteLine($"KatLang.Benchmarks: {exit.Message} Exit code {exit.ExitCode}.");
		}

		return exit.ExitCode;
	}

	internal static BenchmarkSummaryOutcome Outcome(Summary summary)
		=> new(
			summary.Title,
			summary.BenchmarksCases.Length,
			summary.Reports.Count(IsSuccessful),
			summary.ValidationErrors.Count(error => error.IsCritical));

	// BenchmarkReport.Success covers generation, the build and every launch's exit code. The result statistics
	// are what the summary table prints: a report without a result measurement is an NA row whatever its flag.
	private static bool IsSuccessful(BenchmarkReport report)
		=> report.Success && report.ResultStatistics is not null;

	/// <summary>
	/// Whether the arguments ask BenchmarkDotNet to run benchmarks. <c>--help</c>, <c>--version</c>,
	/// <c>--info</c> and <c>--list</c> do not: for them <see cref="BenchmarkSwitcher"/> prints and returns no
	/// summary by design. It returns none for rejected arguments and an empty selection either, and those are
	/// requested runs that ran nothing.
	/// </summary>
	internal static bool IsRunRequested(string[] args, IConfig config)
	{
		// BenchmarkDotNet's own parse and validation (response files included), silenced: BenchmarkSwitcher
		// has already reported whatever it rejected.
		var (parsed, _, options) = ConfigParser.Parse(args, NullLogger.Instance, config);
		if (parsed)
		{
			return !options.PrintInformation && options.ListBenchmarkCaseMode == ListBenchmarkCaseMode.Disabled;
		}

		// A help or version request and a rejected argument both end unparsed; the parser's errors tell them
		// apart. Expand response files here too: the first parse consumed their contents, not the @path tokens.
		// The settings are those of BenchmarkDotNet's ConfigParser, without a help writer.
		if (!TryExpandResponseFiles(args, out var expandedArgs))
		{
			return true;
		}

		using var parser = new CommandLine.Parser(settings =>
		{
			settings.CaseInsensitiveEnumValues = true;
			settings.CaseSensitive = false;
			settings.EnableDashDash = true;
			settings.IgnoreUnknownArguments = false;
			settings.HelpWriter = null;
		});
		var informational = false;
		CommandLine.ParserResultExtensions.WithNotParsed(
			parser.ParseArguments<CommandLineOptions>(expandedArgs),
			errors => informational = IsHelpOrVersionRequest(errors.ToArray()));
		return !informational;
	}

	// ConfigParser's response-file reader is private. Keep this help-only fallback aligned with
	// BenchmarkDotNet 0.14.0's ExpandResponseFile/ConsumeTokens: one level, space delimiters, quoted tokens
	// and its backslash rules. The authoritative parse/validation above still decides every ordinary run.
	private static bool TryExpandResponseFiles(string[] args, out string[] expanded)
	{
		try
		{
			var tokens = new List<string>();
			foreach (var arg in args)
			{
				if (arg.StartsWith('@'))
				{
					foreach (var line in File.ReadLines(arg[1..]))
					{
						tokens.AddRange(ResponseLineTokens(line));
					}
				}
				else
				{
					tokens.Add(arg);
				}
			}

			expanded = tokens.ToArray();
			return true;
		}
		catch (Exception error) when (error is IOException or UnauthorizedAccessException or ArgumentException
			or NotSupportedException or FormatException)
		{
			expanded = [];
			return false;
		}
	}

	private static IEnumerable<string> ResponseLineTokens(string line)
	{
		var token = new StringBuilder();
		var quoted = false;
		for (var index = 0; index <= line.Length; index++)
		{
			if (index == line.Length || (line[index] == ' ' && !quoted))
			{
				if (token.Length > 0)
				{
					var value = token.ToString();
					// ConfigParser prefixes tokens containing spaces for CommandLineParser's quoting workaround.
					yield return value.Contains(' ') ? " " + value : value;
					token.Clear();
				}
			}
			else if (line[index] == '"')
			{
				quoted = !quoted;
			}
			else if (line[index] == '\\' && quoted)
			{
				if (index + 1 == line.Length)
				{
					throw new FormatException("Incomplete response-file escape.");
				}

				switch (line[index + 1])
				{
					case '"': quoted = false; index++; break;
					case '\\': token.Append('\\'); index++; break;
					default: token.Append(line[index]); break;
				}
			}
			else
			{
				token.Append(line[index]);
			}
		}
	}

	// The parser reports a help or version request only for the FIRST argument. A later `--help` is an unknown
	// option to it, yet it then prints the help text without an error, so that is a help request as well —
	// unless another error stands beside it, which BenchmarkDotNet reports as rejected arguments.
	private static bool IsHelpOrVersionRequest(IReadOnlyCollection<CommandLine.Error> errors)
		=> errors.Any(error =>
				error.Tag is CommandLine.ErrorType.HelpRequestedError or CommandLine.ErrorType.VersionRequestedError)
			|| (errors.Count > 0 && errors.All(error =>
				error is CommandLine.UnknownOptionError unknown
				&& string.Equals(unknown.Token, "help", StringComparison.OrdinalIgnoreCase)));
}
