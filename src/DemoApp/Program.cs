using KatLang;

var source = """
    doNotSin=Math.Sin
    doNotSin(1.23) #Remember Jesus
    """;

switch (await KatLangEngine.RunAsync(source, new RunOptions { DownloadCode = DownloadCode }))
{
    case RunResult.Success s:
        Console.WriteLine(s.ToDisplayString());
        break;

    case RunResult.NoProgramOutput n:
        Console.WriteLine(n.ToDisplayString());
        break;

    case RunResult.ParseFailure p:
        foreach (var error in p.Errors)
            Console.WriteLine(error);
        break;

    case RunResult.EvalFailure e:
        foreach (var error in e.Errors)
            Console.WriteLine(error);
        break;
}

static async ValueTask<string> DownloadCode(string url, CancellationToken cancellationToken)
{
    using var client = new HttpClient { Timeout = TimeSpan.FromSeconds(10) };
    return await client.GetStringAsync(url, cancellationToken);
}
