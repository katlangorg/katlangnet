using System.Text;
using KatLang.CLI;

try
{
    // KatLang results and diagnostics may contain non-ASCII text; make sure the
    // console can render it instead of mangling it to the default code page.
    Console.OutputEncoding = Encoding.UTF8;
}
catch (IOException)
{
    // No usable console attached — keep whatever encoding the host provides.
}

using var cancellation = new CancellationTokenSource();

ConsoleCancelEventHandler cancelHandler = (_, eventArgs) =>
{
    // Forward Ctrl+C into KatLang's existing source-processing and evaluation
    // cancellation tokens instead of terminating midway through host I/O.
    eventArgs.Cancel = true;
    cancellation.Cancel();
};

Console.CancelKeyPress += cancelHandler;
try
{
    return await CliApplication.RunAsync(
        args,
        Console.Out,
        Console.Error,
        cancellationToken: cancellation.Token);
}
finally
{
    Console.CancelKeyPress -= cancelHandler;
}
