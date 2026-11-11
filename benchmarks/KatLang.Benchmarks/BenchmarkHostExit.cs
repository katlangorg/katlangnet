namespace KatLang.Benchmarks;

/// <summary>
/// What one BenchmarkDotNet summary contributes to the benchmark host's exit code: plain counts, so the
/// decision in <see cref="BenchmarkHostExit.Decide"/> needs no BenchmarkDotNet type.
/// </summary>
/// <param name="Title">The summary's title, quoted in the printed reason.</param>
/// <param name="BenchmarkCases">The benchmark cases the summary reports on.</param>
/// <param name="SuccessfulReports">The cases whose report succeeded and holds a result (not an NA row).</param>
/// <param name="CriticalValidationErrors">BenchmarkDotNet's critical validation errors for this summary.</param>
internal readonly record struct BenchmarkSummaryOutcome(
	string Title,
	int BenchmarkCases,
	int SuccessfulReports,
	int CriticalValidationErrors);

/// <summary>
/// The benchmark host's exit code and the one-line reason it prints (<c>null</c>: nothing to say).
/// </summary>
/// <remarks>
/// BenchmarkDotNet returns summaries and never fails the process itself: a build failure, a benchmark that
/// throws or a rejected configuration ends as <c>NA</c> rows or as no summary at all. A run cited as
/// performance evidence must not exit 0 in that state, so the host decides the exit code here.
/// This file is shared as source with <c>tests/KatLang.Tests</c> (<c>BenchmarkHostExitTests</c>) and must stay
/// free of BenchmarkDotNet types.
/// </remarks>
internal readonly record struct BenchmarkHostExit(int ExitCode, string? Message)
{
	/// <summary>At least one benchmark case produced a successful report, or nothing was asked to run.</summary>
	public const int Success = 0;

	/// <summary>Benchmarks were selected, but none produced a successful report, or validation was critical.</summary>
	public const int NoSuccessfulBenchmark = 1;

	/// <summary>A run was requested and BenchmarkDotNet ran nothing: no selection, or rejected arguments.</summary>
	public const int NoBenchmarkRun = 2;

	/// <summary>
	/// Decides the exit code of one host invocation.
	/// </summary>
	/// <param name="runRequested">
	/// <c>false</c> for an informational invocation (<c>--help</c>, <c>--version</c>, <c>--info</c>,
	/// <c>--list</c>), which is expected to return no summary; <c>true</c> for everything else.
	/// </param>
	/// <param name="summaries">One entry per summary BenchmarkDotNet returned, in its order.</param>
	public static BenchmarkHostExit Decide(bool runRequested, IReadOnlyList<BenchmarkSummaryOutcome> summaries)
	{
		ArgumentNullException.ThrowIfNull(summaries);

		var criticalErrors = 0;
		var cases = 0;
		var successful = 0;
		string? firstCriticalTitle = null;
		foreach (var summary in summaries)
		{
			if (summary.CriticalValidationErrors > 0)
			{
				criticalErrors += summary.CriticalValidationErrors;
				firstCriticalTitle ??= summary.Title;
			}

			cases += summary.BenchmarkCases;
			successful += summary.SuccessfulReports;
		}

		// A critical validation error makes BenchmarkDotNet skip the whole run it belongs to, so it fails the
		// invocation even when another summary succeeded.
		if (criticalErrors > 0)
		{
			return new(
				NoSuccessfulBenchmark,
				$"BenchmarkDotNet reported {criticalErrors} critical validation error(s) (first in '{firstCriticalTitle}').");
		}

		if (summaries.Count == 0)
		{
			return runRequested
				? new(
					NoBenchmarkRun,
					"no benchmark was run (the filter or selection matched nothing, or BenchmarkDotNet rejected the arguments; see its output above).")
				: new(Success, null);
		}

		if (successful == 0)
		{
			return new(
				NoSuccessfulBenchmark,
				$"none of the {cases} benchmark case(s) produced a successful report (every result is NA).");
		}

		// Some cases failed beside successful ones: the exit code stays 0, but the run says so.
		return successful < cases
			? new(Success, $"warning: {cases - successful} of {cases} benchmark case(s) produced no successful report (NA).")
			: new(Success, null);
	}
}
