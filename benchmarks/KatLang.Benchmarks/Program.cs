namespace KatLang.Benchmarks;

public static class Program
{
	/// <summary>
	/// The benchmark host. The exit code is 0 for the diagnostic runners and for a BenchmarkDotNet run in
	/// which at least one benchmark case succeeded; see <see cref="BenchmarkHostExit"/> for the nonzero codes.
	/// </summary>
	public static int Main(string[] args)
	{
		if (BenchmarkCacheStatsDiagnosticRunner.TryRun(args))
		{
			return BenchmarkHostExit.Success;
		}

		if (BenchmarkLoopStatsDiagnosticRunner.TryRun(args))
		{
			return BenchmarkHostExit.Success;
		}

		if (BenchmarkSequenceStatsDiagnosticRunner.TryRun(args))
		{
			return BenchmarkHostExit.Success;
		}

		if (AsyncStackCapacityDiagnosticRunner.TryRun(args))
		{
			return BenchmarkHostExit.Success;
		}

		return BenchmarkHostRun.Run(args);
	}
}
