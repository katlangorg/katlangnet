using System.Buffers;
using System.Text;

namespace KatLang.CLI;

/// <summary>
/// What one bounded source read produced: the complete decoded text, or the fact that the
/// text is longer than the limit. An oversized read carries no text and no total length —
/// the reader stops as soon as the limit is crossed, so it knows only that the source holds
/// MORE than the limit's code units.
/// </summary>
internal readonly record struct BoundedSourceRead(string? Source)
{
    public static BoundedSourceRead LimitExceeded => default;

    public bool ExceedsLimit => Source is null;
}

/// <summary>
/// The CLI's file acquisition for <c>run</c> and <c>check</c>: decodes a source file
/// incrementally and refuses it as soon as its decoded text exceeds a UTF-16 code-unit
/// limit, so an oversized, growing, or endless input is never accumulated in full.
///
/// <para>Decoding is exactly <see cref="File.ReadAllTextAsync(string, CancellationToken)"/>'s:
/// the same file-open options, a <see cref="StreamReader"/> over UTF-8 with byte-order-mark
/// detection (UTF-8, UTF-16 LE/BE, UTF-32 LE/BE), and replacement-character decoding of
/// malformed bytes. An accepted source is therefore the identical string. Nothing is
/// trusted from the stream itself — not its length, position, or seekability — so the
/// decoded count alone enforces the limit. KatLang's front end still applies its own
/// source-length limit to whatever text it is given; this is the CLI's earlier,
/// allocation-bounding check of the same ceiling.</para>
/// </summary>
internal static class BoundedSourceReader
{
    /// <summary>The file-stream buffer size <see cref="File.ReadAllTextAsync(string, CancellationToken)"/> uses.</summary>
    private const int ByteBufferSize = 4096;

    /// <summary>The largest number of decoded characters requested per read.</summary>
    internal const int ChunkCharacters = 4096;

    public static async Task<BoundedSourceRead> ReadFileAsync(
        string path,
        int maxUtf16CodeUnits,
        CancellationToken cancellationToken)
    {
        // The same argument validation, cancellation check, and open as File.ReadAllTextAsync,
        // in the same order, so file errors surface unchanged.
        ArgumentException.ThrowIfNullOrEmpty(path);
        cancellationToken.ThrowIfCancellationRequested();

        var stream = new FileStream(
            path,
            FileMode.Open,
            FileAccess.Read,
            FileShare.Read,
            ByteBufferSize,
            FileOptions.Asynchronous | FileOptions.SequentialScan);

        await using (stream.ConfigureAwait(false))
        {
            return await ReadAsync(stream, maxUtf16CodeUnits, cancellationToken).ConfigureAwait(false);
        }
    }

    /// <summary>
    /// Reads <paramref name="stream"/> to its end, or until its decoded text exceeds
    /// <paramref name="maxUtf16CodeUnits"/>. Memory is bounded by the limit: at most
    /// <paramref name="maxUtf16CodeUnits"/> characters are accumulated. Character reads
    /// request at most one code unit beyond the remaining allowance; the decoder may
    /// buffer a fixed amount of input ahead. The stream is left open for its owner.
    /// </summary>
    public static async Task<BoundedSourceRead> ReadAsync(
        Stream stream,
        int maxUtf16CodeUnits,
        CancellationToken cancellationToken)
    {
        ArgumentNullException.ThrowIfNull(stream);
        ArgumentOutOfRangeException.ThrowIfNegative(maxUtf16CodeUnits);
        cancellationToken.ThrowIfCancellationRequested();

        // StreamReader's default decoder buffer, as File.ReadAllTextAsync uses.
        using var reader = new StreamReader(
            stream,
            Encoding.UTF8,
            detectEncodingFromByteOrderMarks: true,
            bufferSize: -1,
            leaveOpen: true);

        // One more character than the limit is enough to prove a source oversized, so a
        // tiny limit never requests a whole chunk. The chunk buffer is pooled, as
        // File.ReadAllTextAsync pools its own.
        var chunkLength = maxUtf16CodeUnits < ChunkCharacters ? maxUtf16CodeUnits + 1 : ChunkCharacters;
        var buffer = ArrayPool<char>.Shared.Rent(chunkLength);
        try
        {
            var source = new StringBuilder();

            while (true)
            {
                cancellationToken.ThrowIfCancellationRequested();

                // StreamReader may wait to fill the requested character count. Ask only
                // for enough to prove oversize, so an open producer cannot delay refusal
                // by withholding the rest of a chunk after it has crossed the limit.
                var remaining = maxUtf16CodeUnits - source.Length;
                var requested = remaining < chunkLength ? remaining + 1 : chunkLength;
                var read = await reader.ReadAsync(buffer.AsMemory(0, requested), cancellationToken).ConfigureAwait(false);
                cancellationToken.ThrowIfCancellationRequested();
                if (read == 0)
                    return new BoundedSourceRead(source.ToString());

                if (read > remaining)
                    return BoundedSourceRead.LimitExceeded;

                source.Append(buffer, 0, read);
            }
        }
        finally
        {
            ArrayPool<char>.Shared.Return(buffer);
        }
    }
}
