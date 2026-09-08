using System.Net;
using System.Net.Sockets;
using System.Text;

namespace KatLang.CLI.Tests;

/// <summary>
/// One-request loopback HTTP endpoint. It keeps transport tests entirely offline
/// while exercising the downloader's real socket transport. A response is either
/// a fixed text (<see cref="Ok"/>, <see cref="Redirect"/>) or a script that
/// writes raw bytes itself — bodies that stall, trickle, or never end — and can
/// watch for the client to go away. Every wait inside a script observes the
/// fixture's shutdown, so disposal always completes.
/// </summary>
internal sealed class LoopbackHttpServer : IAsyncDisposable
{
    private readonly TcpListener _listener = new(IPAddress.Loopback, 0);
    private readonly CancellationTokenSource _shutdown = new();
    private readonly Func<Connection, Task> _respond;
    private readonly Task _serverTask;
    private readonly TaskCompletionSource _clientDisconnected = new(TaskCreationOptions.RunContinuationsAsynchronously);
    private int _requestCount;
    private long _bytesWritten;

    public LoopbackHttpServer(Func<string> response)
        : this(connection => connection.WriteAsync(Encoding.UTF8.GetBytes(response())))
    {
    }

    public LoopbackHttpServer(Func<Connection, Task> respond)
    {
        _respond = respond;
        _listener.Start();
        _serverTask = ServeOneAsync();
    }

    /// <summary>Requests accepted so far: 0 or 1.</summary>
    public int RequestCount => Volatile.Read(ref _requestCount);

    /// <summary>Bytes the script handed to the socket successfully.</summary>
    public long BytesWritten => Volatile.Read(ref _bytesWritten);

    /// <summary>Completes once the script observed the client closing the connection.</summary>
    public Task ClientDisconnected => _clientDisconnected.Task;

    public string Url(string host)
    {
        var endpoint = (IPEndPoint)_listener.LocalEndpoint;
        return $"http://{host}:{endpoint.Port}/module.kat";
    }

    public static string Ok(string content)
    {
        var length = Encoding.UTF8.GetByteCount(content);
        return $"HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: {length}\r\nConnection: close\r\n\r\n{content}";
    }

    public static string Redirect(string location)
        => $"HTTP/1.1 302 Found\r\nLocation: {location}\r\nContent-Length: 0\r\nConnection: close\r\n\r\n";

    /// <summary>A 200 response head with the given extra headers; the script writes the body itself.</summary>
    public static byte[] OkHead(params string[] headers)
        => Encoding.ASCII.GetBytes(
            "HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\n"
            + string.Concat(headers.Select(static header => header + "\r\n"))
            + "Connection: close\r\n\r\n");

    /// <summary>One chunk of a chunked transfer encoding.</summary>
    public static byte[] Chunk(ReadOnlySpan<byte> data)
        => [.. Encoding.ASCII.GetBytes($"{data.Length:x}\r\n"), .. data, (byte)'\r', (byte)'\n'];

    /// <summary>The terminating chunk of a chunked transfer encoding.</summary>
    public static byte[] LastChunk => "0\r\n\r\n"u8.ToArray();

    public async ValueTask DisposeAsync()
    {
        try
        {
            await _shutdown.CancelAsync();
            _listener.Stop();
            try
            {
                await _serverTask;
            }
            catch (OperationCanceledException ex) when (ex.CancellationToken == _shutdown.Token)
            {
                // Only this fixture's shutdown, including an unrequested listener.
            }
            catch (ClientDisconnectedException)
            {
                // A socket operation observed a known peer disconnect.
            }
        }
        finally
        {
            // Script failures must propagate, but must not skip resource cleanup.
            _listener.Stop();
            _shutdown.Dispose();
        }
    }

    private async Task ServeOneAsync()
    {
        using var client = await _listener.AcceptTcpClientAsync(_shutdown.Token);
        Interlocked.Increment(ref _requestCount);

        await using var stream = client.GetStream();
        var buffer = new byte[1024];
        var request = new StringBuilder();

        while (!request.ToString().Contains("\r\n\r\n", StringComparison.Ordinal))
        {
            int read;
            try
            {
                read = await stream.ReadAsync(buffer, _shutdown.Token);
            }
            catch (Exception ex) when (IsPeerDisconnect(ex))
            {
                _clientDisconnected.TrySetResult();
                return;
            }
            if (read == 0)
                return;

            request.Append(Encoding.ASCII.GetString(buffer, 0, read));
            if (request.Length > 16 * 1024)
                throw new InvalidOperationException("Loopback test request headers were unexpectedly large.");
        }

        await _respond(new Connection(this, stream));
    }

    private sealed class ClientDisconnectedException : IOException;

    // Classify only failures from actual socket operations, never arbitrary script errors.
    // Broken pipes on Unix map to Shutdown; resets/aborts vary by platform.
    private static bool IsPeerDisconnect(Exception ex)
        => (ex as SocketException ?? (ex as IOException)?.InnerException as SocketException)?.SocketErrorCode
            is SocketError.ConnectionReset or SocketError.ConnectionAborted
                or SocketError.NetworkReset or SocketError.Shutdown or SocketError.NotConnected;

    /// <summary>The accepted connection as a response script sees it.</summary>
    public sealed class Connection(LoopbackHttpServer server, NetworkStream stream)
    {
        /// <summary>Fixture shutdown; every wait in a script observes it.</summary>
        public CancellationToken Shutdown => server._shutdown.Token;

        /// <summary>Writes, throwing once the client has gone (the disconnect is recorded first).</summary>
        public async Task WriteAsync(ReadOnlyMemory<byte> bytes)
        {
            if (!await TryWriteAsync(bytes))
                throw new ClientDisconnectedException();
        }

        /// <summary>Writes; false once the client has gone. Never throws for a departed client.</summary>
        public async Task<bool> TryWriteAsync(ReadOnlyMemory<byte> bytes)
        {
            try
            {
                await stream.WriteAsync(bytes, Shutdown);
                Interlocked.Add(ref server._bytesWritten, bytes.Length);
                return true;
            }
            catch (Exception ex) when (IsPeerDisconnect(ex))
            {
                server._clientDisconnected.TrySetResult();
                return false;
            }
        }

        /// <summary>
        /// Blocks until the client closes its side. A GET carries no body, so the next
        /// read completes only when the client disconnects (or the fixture shuts down).
        /// </summary>
        public async Task WaitForClientToDisconnectAsync()
        {
            var buffer = new byte[64];
            try
            {
                while (await stream.ReadAsync(buffer, Shutdown) != 0)
                {
                }
            }
            catch (Exception ex) when (IsPeerDisconnect(ex))
            {
            }

            server._clientDisconnected.TrySetResult();
        }
    }
}
