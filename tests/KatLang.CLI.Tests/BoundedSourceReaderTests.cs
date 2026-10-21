using System.Text;

namespace KatLang.CLI.Tests;

/// <summary>
/// SEC-04: the CLI's <c>run</c>/<c>check</c> file acquisition enforces KatLang's decoded
/// source-length ceiling WHILE reading, so an oversized, growing, endless, or nonseekable
/// input is refused after a bounded amount of input and is never accumulated whole. Most
/// cases use tiny limits; the real-ceiling cases drive the CLI itself.
/// </summary>
public sealed class BoundedSourceReaderTests
{
    private const int Success = 0;
    private const int Failure = 1;
    private const int Max = SourceProcessingLimits.MaxSupportedSourceLength;

    /// <summary>
    /// A generous bound on the input bytes one read can consume past the accepted text: a
    /// decoder byte buffer (at most 4,096 bytes; one refill) plus the bytes of one requested
    /// character chunk.
    /// Independent of the source's total size.
    /// </summary>
    private const int ReadAheadBytes = 4096 + 4 * BoundedSourceReader.ChunkCharacters;

    // ── T1: exact boundary ──────────────────────────────────────────────────

    [Theory]
    [InlineData(3)]
    [InlineData(4)]
    [InlineData(8)]
    [InlineData(0)]
    [InlineData(1)]
    public async Task Boundary_AcceptsUpToTheLimit_AndRefusesOneMore(int limit)
    {
        foreach (var length in new[] { 0, 1, limit - 1, limit }.Where(length => length >= 0 && length <= limit))
        {
            var text = new string('a', length);
            var read = await ReadBytesAsync(Encoding.UTF8.GetBytes(text), limit);

            Assert.False(read.ExceedsLimit, $"length {length} at limit {limit}");
            Assert.Equal(text, read.Source);
        }

        foreach (var length in new[] { limit + 1, limit + 2, limit * 1000 + 1, 100_000 })
        {
            var read = await ReadBytesAsync(Encoding.UTF8.GetBytes(new string('a', length)), limit);

            Assert.True(read.ExceedsLimit, $"length {length} at limit {limit}");
            Assert.Null(read.Source);
        }
    }

    [Fact]
    public async Task Boundary_HoldsAcrossChunkBoundaries()
    {
        // Limits around the chunk size: the last accepted character and the first refused one
        // fall in different chunks.
        foreach (var limit in new[] { BoundedSourceReader.ChunkCharacters - 1, BoundedSourceReader.ChunkCharacters, BoundedSourceReader.ChunkCharacters + 1, 3 * BoundedSourceReader.ChunkCharacters })
        {
            var exact = new string('x', limit);
            Assert.Equal(exact, (await ReadBytesAsync(Encoding.UTF8.GetBytes(exact), limit)).Source);
            Assert.True((await ReadBytesAsync(Encoding.UTF8.GetBytes(exact + "x"), limit)).ExceedsLimit);
        }
    }

    // ── T2 / T13: oversized input stops early, accumulation bounded ─────────

    [Fact]
    public async Task OversizedInput_StopsAfterABoundedPrefix()
    {
        const int limit = 8;
        var bytes = Encoding.UTF8.GetBytes(new string('a', 4 * 1024 * 1024));
        using var stream = new InstrumentedStream(bytes);

        var read = await BoundedSourceReader.ReadAsync(stream, limit, CancellationToken.None);

        Assert.True(read.ExceedsLimit);
        Assert.InRange(stream.BytesReturned, limit + 1, ReadAheadBytes);
        Assert.False(stream.ReachedEnd);
    }

    [Fact]
    public async Task OversizedInput_ConsumesInputProportionalToTheLimit_NotToTheSource()
    {
        // The same limit over sources 16x apart consumes the same bounded prefix: what is
        // read depends on the limit alone.
        const int limit = 64 * 1024;
        long? consumed = null;
        foreach (var size in new[] { 1, 16 })
        {
            using var stream = new InstrumentedStream(Encoding.UTF8.GetBytes(new string('a', size * 1024 * 1024)));

            var read = await BoundedSourceReader.ReadAsync(stream, limit, CancellationToken.None);

            Assert.True(read.ExceedsLimit);
            Assert.InRange(stream.BytesReturned, limit + 1, limit + ReadAheadBytes);
            consumed ??= stream.BytesReturned;
            Assert.Equal(consumed, stream.BytesReturned);
        }
    }

    [Fact]
    public async Task OversizedInput_AllocatesInProportionToTheLimit()
    {
        // A supplementary observation for T13 (the primary evidence is the consumed-byte
        // bound above): the instrumented stream completes every read synchronously, so the
        // whole read runs on this thread, and its allocation stays a small multiple of the
        // limit while the endless source is never exhausted.
        const int limit = 64 * 1024;
        using var warmup = InstrumentedStream.Endless((byte)'a');
        await BoundedSourceReader.ReadAsync(warmup, limit, CancellationToken.None);

        using var stream = InstrumentedStream.Endless((byte)'a');
        var before = GC.GetAllocatedBytesForCurrentThread();
        var read = await BoundedSourceReader.ReadAsync(stream, limit, CancellationToken.None);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.True(read.ExceedsLimit);
        Assert.InRange(allocated, 0, 8L * limit + 256 * 1024);
    }

    // ── T3: nonseekable stream ──────────────────────────────────────────────

    [Fact]
    public async Task NonseekableStream_IsReadWithoutLengthOrPosition()
    {
        // The stream throws from Length, Position, and Seek; the reader never asks.
        using var accepted = new InstrumentedStream(Encoding.UTF8.GetBytes("1 + 2\n"));
        Assert.False(accepted.CanSeek);
        Assert.Equal("1 + 2\n", (await BoundedSourceReader.ReadAsync(accepted, 6, CancellationToken.None)).Source);
        Assert.True(accepted.ReachedEnd);

        using var refused = new InstrumentedStream(Encoding.UTF8.GetBytes("1 + 2\n"));
        Assert.True((await BoundedSourceReader.ReadAsync(refused, 5, CancellationToken.None)).ExceedsLimit);
    }

    // ── T4: growing / endless input ─────────────────────────────────────────

    [Fact]
    public async Task EndlessInput_IsRefusedAfterBoundedReads()
    {
        const int limit = 1000;
        using var stream = InstrumentedStream.Endless((byte)'7');

        var read = await BoundedSourceReader.ReadAsync(stream, limit, CancellationToken.None);

        Assert.True(read.ExceedsLimit);
        Assert.InRange(stream.BytesReturned, limit + 1, limit + ReadAheadBytes);
    }

    [Fact]
    public async Task TricklingEndlessInput_IsRefusedAfterBoundedReads()
    {
        // One byte per read, like a slowly growing file or a pipe.
        const int limit = 50;
        using var stream = InstrumentedStream.Endless((byte)'7', maxBytesPerRead: 1);

        var read = await BoundedSourceReader.ReadAsync(stream, limit, CancellationToken.None);

        Assert.True(read.ExceedsLimit);
        Assert.Equal(limit + 1, stream.BytesReturned);
    }

    [Theory]
    [InlineData(4096)]
    [InlineData(4097)]
    [InlineData(8192)]
    public async Task OversizedInput_DoesNotRequestMoreDataAfterTheLimitIsProven(int limit)
    {
        // Full decoder buffers can make StreamReader.ReadAsync try to fill the whole
        // requested character chunk. A producer may stay open without sending more:
        // asking for another buffer after oversize is known would then block forever.
        using var stream = InstrumentedStream.Endless((byte)'a');
        stream.OnRead = _ =>
        {
            if (stream.BytesReturned > limit + 1024)
                throw new IOException("Read again after enough source was available to prove oversize.");
        };

        var read = await BoundedSourceReader.ReadAsync(stream, limit, CancellationToken.None);

        Assert.True(read.ExceedsLimit);
        Assert.Null(read.Source);
        Assert.InRange(stream.BytesReturned, limit + 1, limit + 1024);
    }

    // ── T5: UTF-16 code-unit counting ───────────────────────────────────────

    [Theory]
    [InlineData("abc", 3)]                  // ASCII: one byte, one code unit
    [InlineData("ééé", 3)]                  // two UTF-8 bytes, one code unit each
    [InlineData("€€", 2)]                   // three UTF-8 bytes, one code unit each
    [InlineData("\U0001F600", 2)]           // four UTF-8 bytes, a surrogate pair
    [InlineData("a\U0001F600b", 4)]
    public async Task Counting_IsInDecodedUtf16CodeUnits(string text, int codeUnits)
    {
        Assert.Equal(codeUnits, text.Length);
        foreach (var encoding in Encodings())
        {
            var bytes = WithPreamble(encoding, text);

            Assert.Equal(text, (await ReadBytesAsync(bytes, codeUnits)).Source);
            Assert.True((await ReadBytesAsync(bytes, codeUnits - 1)).ExceedsLimit, encoding.WebName);
        }
    }

    [Fact]
    public async Task ByteLength_IsNotTheLimit()
    {
        // 2,000 bytes of UTF-8 decode to 1,000 code units: accepted at a 1,000 limit.
        var text = new string('é', 1000);
        var bytes = Encoding.UTF8.GetBytes(text);
        Assert.Equal(2000, bytes.Length);

        Assert.Equal(text, (await ReadBytesAsync(bytes, 1000)).Source);
    }

    [Fact]
    public async Task ByteOrderMarks_AreNotCounted()
    {
        foreach (var encoding in Encodings())
        {
            var bytes = WithPreamble(encoding, "ab");
            Assert.True(bytes.Length > 2);

            Assert.Equal("ab", (await ReadBytesAsync(bytes, 2)).Source);
            Assert.True((await ReadBytesAsync(WithPreamble(encoding, "abc"), 2)).ExceedsLimit);
        }
    }

    // ── T6: text compatibility with File.ReadAllTextAsync ───────────────────

    public static TheoryData<string, byte[]> CompatibilityFixtures()
    {
        var data = new TheoryData<string, byte[]>
        {
            { "empty", [] },
            { "ascii LF", Encoding.ASCII.GetBytes("x = 1\ny = 2\nx + y\n") },
            { "CRLF", Encoding.ASCII.GetBytes("x = 1\r\ny = 2\r\nx + y\r\n") },
            { "lone CR and mixed", Encoding.ASCII.GetBytes("a\rb\r\nc\n\n\r") },
            { "no trailing newline, spaces", Encoding.ASCII.GetBytes("  1 + 2  \t") },
            { "utf8 no BOM", Encoding.UTF8.GetBytes("'π ≈ 3.14159'\n'naïve 😀'\n") },
            { "utf8 BOM only", Encoding.UTF8.GetPreamble() },
            { "utf8 double BOM", [.. Encoding.UTF8.GetPreamble(), .. Encoding.UTF8.GetPreamble(), (byte)'1'] },
            { "BOM character later", Encoding.UTF8.GetBytes("1﻿2") },
            { "invalid byte", [(byte)'a', 0xFF, (byte)'b'] },
            { "lone continuation", [(byte)'a', 0x80, 0x80, (byte)'b'] },
            { "overlong", [0xC0, 0x80, (byte)'z'] },
            { "encoded surrogate", [0xED, 0xA0, 0x80, (byte)'z'] },
            { "truncated sequence at end", [(byte)'a', 0xF0, 0x9F, 0x98] },
            { "utf16 BOM odd byte", [0xFF, 0xFE, (byte)'a', 0, (byte)'b'] },
            { "utf16 lone surrogate", [0xFF, 0xFE, 0x3D, 0xD8, (byte)'a', 0] },
        };

        foreach (var encoding in Encodings())
            data.Add($"{encoding.WebName} BOM", WithPreamble(encoding, "x = 'é😀'\r\nx\n"));

        // Multi-chunk content with multibyte and surrogate sequences crossing every boundary.
        var large = new StringBuilder();
        for (var i = 0; i < 6000; i++)
            large.Append(i % 7 == 0 ? "😀" : i % 5 == 0 ? "é" : i % 11 == 0 ? "\r\n" : "a");
        data.Add("large utf8", Encoding.UTF8.GetBytes(large.ToString()));
        data.Add("large utf16", WithPreamble(new UnicodeEncoding(bigEndian: false, byteOrderMark: true), large.ToString()));

        return data;
    }

    [Theory]
    [MemberData(nameof(CompatibilityFixtures))]
    public async Task AcceptedFile_IsTheStringReadAllTextAsyncReturns(string name, byte[] bytes)
    {
        var path = Path.Combine(Path.GetTempPath(), $"katlang-cli-bounded-{Guid.NewGuid():N}.kat");
        await File.WriteAllBytesAsync(path, bytes);
        try
        {
            var expected = await File.ReadAllTextAsync(path);

            var read = await BoundedSourceReader.ReadFileAsync(path, Max, CancellationToken.None);
            Assert.False(read.ExceedsLimit, name);
            Assert.Equal(expected, read.Source, StringComparer.Ordinal);

            // At exactly the decoded length too: the limit is the decoded length, so the
            // tightest accepting limit must still return the identical string.
            var tight = await BoundedSourceReader.ReadFileAsync(path, expected.Length, CancellationToken.None);
            Assert.Equal(expected, tight.Source, StringComparer.Ordinal);
            if (expected.Length > 0)
                Assert.True((await BoundedSourceReader.ReadFileAsync(path, expected.Length - 1, CancellationToken.None)).ExceedsLimit, name);

            // A stream that returns one byte per read splits every sequence across chunks. Its
            // reference is the unbounded StreamReader over the same trickle: StreamReader's
            // byte-order-mark detection needs two bytes in one read, so a BOM split this way
            // decodes differently from the file read above for EVERY StreamReader-based
            // reader — a property of the decoder, kept, not introduced, by the bound.
            using var trickle = new InstrumentedStream(bytes, maxBytesPerRead: 1);
            using var referenceTrickle = new InstrumentedStream(bytes, maxBytesPerRead: 1);
            using var reference = new StreamReader(referenceTrickle, Encoding.UTF8, detectEncodingFromByteOrderMarks: true);
            Assert.Equal(
                await reference.ReadToEndAsync(),
                (await BoundedSourceReader.ReadAsync(trickle, Max, CancellationToken.None)).Source,
                StringComparer.Ordinal);
        }
        finally
        {
            File.Delete(path);
        }
    }

    // ── T7 / T8: cancellation ───────────────────────────────────────────────

    [Fact]
    public async Task CancellationDuringReading_PropagatesAndStopsReading()
    {
        using var cancellation = new CancellationTokenSource();
        using var stream = InstrumentedStream.Endless((byte)'a', maxBytesPerRead: 16);
        stream.OnRead = reads =>
        {
            if (reads == 3)
                cancellation.Cancel();
        };

        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => BoundedSourceReader.ReadAsync(stream, Max, cancellation.Token));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        // Prompt: no read is issued after the one that observed cancellation.
        Assert.InRange(stream.ReadCalls, 3, 4);
        // The caller owns its stream; the reader neither disposes nor keeps it.
        Assert.False(stream.IsDisposed);
    }

    [Fact]
    public async Task AlreadyCancelledToken_ReadsNothing()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        using var stream = new InstrumentedStream(Encoding.UTF8.GetBytes("1"));

        await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => BoundedSourceReader.ReadAsync(stream, Max, cancellation.Token));

        Assert.Equal(0, stream.ReadCalls);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(9)]
    public async Task CancellationOnTheFinalRead_PropagatesBeforeReturningAnOutcome(int length)
    {
        using var cancellation = new CancellationTokenSource();
        using var stream = new InstrumentedStream(Encoding.UTF8.GetBytes(new string('a', length)));
        stream.OnRead = _ => cancellation.Cancel();

        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => BoundedSourceReader.ReadAsync(stream, 8, cancellation.Token));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(1, stream.ReadCalls);
        Assert.False(stream.IsDisposed);
    }

    [Fact]
    public async Task CancellationWhileAReadIsPending_PropagatesToTheStream()
    {
        using var cancellation = new CancellationTokenSource();
        using var stream = new PendingReadStream();
        var pending = BoundedSourceReader.ReadAsync(stream, 8, cancellation.Token);
        await stream.Entered.Task;
        Assert.False(pending.IsCompleted);

        cancellation.Cancel();
        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => pending);

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(cancellation.Token, stream.ObservedToken);
        Assert.False(stream.IsDisposed);
        stream.Dispose();
        Assert.True(stream.IsDisposed);
    }

    [Fact]
    public async Task AlreadyCancelledToken_DoesNotOpenTheFile()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        using var file = new TempSourceFile("1");

        await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => BoundedSourceReader.ReadFileAsync(file.Path, Max, cancellation.Token));

        // Unchanged CLI response: cancelled, not a file error.
        var output = new StringWriter();
        var error = new StringWriter();
        var exitCode = await CliApplication.RunAsync(["run", file.Path], output, error, cancellationToken: cancellation.Token);
        Assert.Equal(Failure, exitCode);
        Assert.Equal("", output.ToString());
        Assert.Equal("katlang: cancelled.", error.ToString().Trim());
        AssertNoOpenHandle(file.Path);
    }

    [Fact]
    public async Task FileHandle_IsReleasedAfterAcceptanceAndRefusal()
    {
        using var file = new TempSourceFile("12345");

        Assert.Equal("12345", (await BoundedSourceReader.ReadFileAsync(file.Path, 5, CancellationToken.None)).Source);
        AssertNoOpenHandle(file.Path);

        Assert.True((await BoundedSourceReader.ReadFileAsync(file.Path, 4, CancellationToken.None)).ExceedsLimit);
        AssertNoOpenHandle(file.Path);
    }

    // ── T9 / T10: both CLI file commands at the real ceiling ────────────────

    private static readonly string SourceLengthRefusal =
        $"Source length exceeds the maximum of {Max} UTF-16 code units.";

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task OversizedFile_IsRefusedAtTheRealCeiling_BeforeParsingOrLoading(string command)
    {
        // A load at the top would be the first thing the front end acts on. Max + 1 code
        // units, about 2 MiB.
        const string url = "https://katlang.org/demo/sec04.kat";
        var head = $"open '{url}'\nVal\n";
        using var file = new TempSourceFile(head + new string(' ', Max + 1 - head.Length));
        var downloader = new RecordingDownloader(new Dictionary<string, string> { [url] = "public Val = 1" });

        var result = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, command, file.Path, "--allow-loading");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(SourceLengthRefusal, result.TrimmedError);
        Assert.Empty(downloader.RequestedUrls);
    }

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task FileAtTheRealCeiling_IsAccepted(string command)
    {
        using var file = new TempSourceFile("1" + new string(' ', Max - 1));

        var result = await Cli.InvokeAsync(command, file.Path);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Error);
        Assert.Equal(command == "run" ? "1" : "", result.TrimmedOutput);
    }

    [Fact]
    public async Task MultibyteFileAtTheRealCeiling_IsAccepted_ThoughItsBytesExceedIt()
    {
        // Max code units in roughly 2 * Max UTF-8 bytes.
        var path = Path.Combine(Path.GetTempPath(), $"katlang-cli-bounded-{Guid.NewGuid():N}.kat");
        File.WriteAllText(path, "'" + new string('é', Max - 2) + "'", new UTF8Encoding(encoderShouldEmitUTF8Identifier: false));
        try
        {
            Assert.True(new FileInfo(path).Length > Max);

            var result = await Cli.InvokeAsync("check", path);

            Assert.Equal(Success, result.ExitCode);
            Assert.Equal("", result.Error);
        }
        finally
        {
            File.Delete(path);
        }
    }

    [Fact]
    public async Task Utf16FileOverTheRealCeiling_IsRefused()
    {
        var path = Path.Combine(Path.GetTempPath(), $"katlang-cli-bounded-{Guid.NewGuid():N}.kat");
        File.WriteAllText(path, "1" + new string(' ', Max), new UnicodeEncoding(bigEndian: true, byteOrderMark: true));
        try
        {
            var result = await Cli.InvokeAsync("run", path);

            Assert.Equal(Failure, result.ExitCode);
            Assert.Equal("", result.Output);
            Assert.Equal(SourceLengthRefusal, result.TrimmedError);
        }
        finally
        {
            File.Delete(path);
        }
    }

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task EndlessDevice_IsRefused(string command)
    {
        // A nonregular file with no meaningful length that never ends. Only Unix-like
        // systems expose one as a path the CLI can open.
        if (!File.Exists("/dev/zero"))
            return;

        var result = await Cli.InvokeAsync(command, "/dev/zero");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(SourceLengthRefusal, result.TrimmedError);
    }

    // ── T12: ordinary files are unchanged ───────────────────────────────────

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task EmptyFile_IsStillAccepted(string command)
    {
        using var file = new TempSourceFile("");

        var result = await Cli.InvokeAsync(command, file.Path);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal("", result.Error);
    }

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task InvalidFilePath_IsReportedInCliWords(string command)
    {
        var result = await Cli.InvokeAsync(command, "invalid\0path.kat");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal("katlang: cannot read file 'invalid\0path.kat': the path is not valid.", result.TrimmedError);
    }

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task MissingDirectory_IsReportedAsFileNotFound(string command)
    {
        var path = Path.Combine(TempSourceFile.MissingPath(), "source.kat");

        var result = await Cli.InvokeAsync(command, path);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal($"katlang: file not found: '{path}'.", result.TrimmedError);
    }

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task LockedFile_IsReportedAsAFileError(string command)
    {
        using var file = new TempSourceFile("1");
        using var locked = new FileStream(file.Path, FileMode.Open, FileAccess.ReadWrite, FileShare.None);

        var result = await Cli.InvokeAsync(command, file.Path);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.StartsWith($"katlang: cannot read file '{file.Path}': ", result.TrimmedError);
        Assert.DoesNotContain("unexpected error", result.TrimmedError);
    }

    [Fact]
    public void RefusalMessage_UsesTheFrontEndFamilyWithoutClaimingATotal()
    {
        Assert.Equal("Source length exceeds the maximum of 2097152 UTF-16 code units.", CliApplication.SourceLengthExceededMessage(Max));
        Assert.Equal("Source length exceeds the maximum of 1 UTF-16 code unit.", CliApplication.SourceLengthExceededMessage(1));
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    private static Task<BoundedSourceRead> ReadBytesAsync(byte[] bytes, int limit)
    {
        var stream = new InstrumentedStream(bytes);
        return BoundedSourceReader.ReadAsync(stream, limit, CancellationToken.None);
    }

    /// <summary>Every encoding StreamReader detects from a byte-order mark.</summary>
    private static IEnumerable<Encoding> Encodings() =>
    [
        new UTF8Encoding(encoderShouldEmitUTF8Identifier: true),
        new UnicodeEncoding(bigEndian: false, byteOrderMark: true),
        new UnicodeEncoding(bigEndian: true, byteOrderMark: true),
        new UTF32Encoding(bigEndian: false, byteOrderMark: true),
        new UTF32Encoding(bigEndian: true, byteOrderMark: true),
    ];

    private static byte[] WithPreamble(Encoding encoding, string text)
        => [.. encoding.GetPreamble(), .. encoding.GetBytes(text)];

    private static void AssertNoOpenHandle(string path)
    {
        // An exclusive open fails while any handle — including a read-sharing one — is open.
        using var exclusive = new FileStream(path, FileMode.Open, FileAccess.ReadWrite, FileShare.None);
    }

    /// <summary>
    /// A read-only, nonseekable stream that records what it hands out. Length, Position, and
    /// Seek throw, so a reader that consulted them would fail. Every read completes
    /// synchronously.
    /// </summary>
    private class InstrumentedStream : Stream
    {
        private readonly byte[]? _bytes;
        private readonly byte _fill;
        private readonly int _maxBytesPerRead;
        private int _offset;

        public InstrumentedStream(byte[] bytes, int maxBytesPerRead = int.MaxValue)
        {
            _bytes = bytes;
            _maxBytesPerRead = maxBytesPerRead;
        }

        private InstrumentedStream(byte fill, int maxBytesPerRead)
        {
            _fill = fill;
            _maxBytesPerRead = maxBytesPerRead;
        }

        public static InstrumentedStream Endless(byte fill, int maxBytesPerRead = int.MaxValue) => new(fill, maxBytesPerRead);

        public long BytesReturned { get; private set; }

        public int ReadCalls { get; private set; }

        public bool ReachedEnd { get; private set; }

        public bool IsDisposed { get; private set; }

        /// <summary>Called after each read with the number of reads so far.</summary>
        public Action<int>? OnRead { get; set; }

        public override bool CanRead => true;
        public override bool CanSeek => false;
        public override bool CanWrite => false;
        public override long Length => throw new NotSupportedException("Length must not be consulted.");

        public override long Position
        {
            get => throw new NotSupportedException("Position must not be consulted.");
            set => throw new NotSupportedException("Position must not be consulted.");
        }

        public override int Read(byte[] buffer, int offset, int count) => Read(buffer.AsSpan(offset, count));

        public override int Read(Span<byte> buffer)
        {
            ObjectDisposedException.ThrowIf(IsDisposed, this);
            ReadCalls++;

            var count = Math.Min(buffer.Length, _maxBytesPerRead);
            if (_bytes is not null)
            {
                count = Math.Min(count, _bytes.Length - _offset);
                _bytes.AsSpan(_offset, count).CopyTo(buffer);
                _offset += count;
                if (count == 0)
                    ReachedEnd = true;
            }
            else
            {
                buffer[..count].Fill(_fill);
            }

            BytesReturned += count;
            OnRead?.Invoke(ReadCalls);
            return count;
        }

        public override ValueTask<int> ReadAsync(Memory<byte> buffer, CancellationToken cancellationToken = default)
        {
            cancellationToken.ThrowIfCancellationRequested();
            return ValueTask.FromResult(Read(buffer.Span));
        }

        public override Task<int> ReadAsync(byte[] buffer, int offset, int count, CancellationToken cancellationToken)
            => ReadAsync(buffer.AsMemory(offset, count), cancellationToken).AsTask();

        public override void Flush() { }
        public override long Seek(long offset, SeekOrigin origin) => throw new NotSupportedException("Seek must not be consulted.");
        public override void SetLength(long value) => throw new NotSupportedException();
        public override void Write(byte[] buffer, int offset, int count) => throw new NotSupportedException();

        protected override void Dispose(bool disposing)
        {
            IsDisposed = true;
            base.Dispose(disposing);
        }
    }

    private sealed class PendingReadStream : InstrumentedStream
    {
        public PendingReadStream() : base([]) { }

        public TaskCompletionSource Entered { get; } = new(TaskCreationOptions.RunContinuationsAsynchronously);

        public CancellationToken ObservedToken { get; private set; }

        public override async ValueTask<int> ReadAsync(Memory<byte> buffer, CancellationToken cancellationToken = default)
        {
            ObservedToken = cancellationToken;
            Entered.SetResult();
            await Task.Delay(Timeout.InfiniteTimeSpan, cancellationToken);
            throw new InvalidOperationException("A pending read must terminate by cancellation.");
        }
    }
}
