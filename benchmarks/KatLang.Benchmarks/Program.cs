using BenchmarkDotNet.Running;

namespace KatLang.Benchmarks;

public static class Program
{
	public static void Main(string[] args)
	{
		if (BenchmarkCacheStatsDiagnosticRunner.TryRun(args))
		{
			return;
		}

		if (BenchmarkLoopStatsDiagnosticRunner.TryRun(args))
		{
			return;
		}

		if (BenchmarkSequenceStatsDiagnosticRunner.TryRun(args))
		{
			return;
		}

		if (AsyncStackCapacityDiagnosticRunner.TryRun(args))
		{
			return;
		}

		BenchmarkSwitcher.FromAssembly(typeof(Program).Assembly).Run(args);
	}
}
