using System.Net;
using System.Net.Sockets;

namespace KatLang.CLI;

/// <summary>
/// The CLI's address rule for everything it downloads: a program URL operand and, with
/// <c>--allow-loading</c>, every module. A download may reach only an address on the public
/// internet. The CLI runs inside AI agents, where a link can be pasted or injected by someone
/// else, and such a link must not reach the user's own machine or network: a local service, a
/// router, another host on the LAN, or a cloud metadata endpoint such as
/// <c>169.254.169.254</c>.
///
/// <para>The rule is about ADDRESSES, never names. <see cref="HttpSourceDownloader"/> resolves a
/// host name itself, judges every address the answer holds, and connects only to an address
/// this rule passed, so a name that resolves to a refused address is refused, and a second DNS
/// answer cannot swap the address between the check and the connection. An IP literal is
/// judged the same way, in whatever spelling the URL writes it.</para>
///
/// <para>Refused, for IPv4: <c>0.0.0.0/8</c> (unspecified, "this network"), <c>10.0.0.0/8</c>,
/// <c>172.16.0.0/12</c> and <c>192.168.0.0/16</c> (private, RFC 1918), <c>100.64.0.0/10</c>
/// (carrier-grade NAT), <c>127.0.0.0/8</c> (loopback), <c>169.254.0.0/16</c> (link-local),
/// <c>192.0.0.0/24</c> (protocol assignments), <c>192.88.99.0/24</c> (6to4 relays),
/// <c>198.18.0.0/15</c> (benchmarking), the documentation ranges <c>192.0.2.0/24</c>,
/// <c>198.51.100.0/24</c> and <c>203.0.113.0/24</c>, and everything from <c>224.0.0.0</c> up
/// (multicast, reserved, broadcast).</para>
///
/// <para>For IPv6 only global unicast space (<c>2000::/3</c>) is public, less the ranges inside
/// it that are not: <c>2001::/23</c> (protocol assignments, Teredo among them),
/// <c>2001:db8::/32</c> and <c>3fff::/20</c> (documentation). That refuses the unspecified
/// address, loopback (<c>::1</c>), unique-local (<c>fc00::/7</c>), link-local
/// (<c>fe80::/10</c>), site-local, the discard prefix and multicast. An address that carries an
/// IPv4 address is judged by that address: IPv4-mapped (<c>::ffff:a.b.c.d</c>), the NAT64
/// prefix <c>64:ff9b::/96</c> (so an IPv6-only network that reaches IPv4 hosts through NAT64
/// still works) and 6to4 (<c>2002::/16</c>). Any other address family is refused.</para>
/// </summary>
internal static class PublicAddress
{
    private static ReadOnlySpan<byte> Ipv4MappedPrefix => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xFF, 0xFF];

    private static ReadOnlySpan<byte> Nat64Prefix => [0x00, 0x64, 0xFF, 0x9B, 0, 0, 0, 0, 0, 0, 0, 0];

    /// <summary>Whether a download may connect to <paramref name="address"/>.</summary>
    public static bool IsPublic(IPAddress address)
    {
        ArgumentNullException.ThrowIfNull(address);

        Span<byte> bytes = stackalloc byte[16];
        if (!address.TryWriteBytes(bytes, out var length))
            return false;

        return address.AddressFamily switch
        {
            AddressFamily.InterNetwork when length == 4 => IsPublicV4(bytes[..4]),
            AddressFamily.InterNetworkV6 when length == 16 => IsPublicV6(bytes),
            _ => false,
        };
    }

    private static bool IsPublicV4(ReadOnlySpan<byte> a) => a[0] switch
    {
        0 or 10 or 127 => false,
        100 => (a[1] & 0xC0) != 0x40,
        169 => a[1] != 254,
        172 => (a[1] & 0xF0) != 0x10,
        192 => !(a[1] == 168 || (a[1] == 0 && a[2] is 0 or 2) || (a[1] == 88 && a[2] == 99)),
        198 => !((a[1] & 0xFE) == 18 || (a[1] == 51 && a[2] == 100)),
        203 => !(a[1] == 0 && a[2] == 113),
        >= 224 => false,
        _ => true,
    };

    private static bool IsPublicV6(ReadOnlySpan<byte> a)
    {
        if (a.StartsWith(Ipv4MappedPrefix) || a.StartsWith(Nat64Prefix))
            return IsPublicV4(a[12..]);

        // Global unicast only: this one test refuses ::, ::1, fc00::/7, fe80::/10, fec0::/10,
        // 100::/64, ff00::/8 and every other range outside 2000::/3.
        if ((a[0] & 0xE0) != 0x20)
            return false;

        if (a[0] == 0x20 && a[1] == 0x01)
        {
            // 2001::/23 (protocol assignments) and 2001:db8::/32 (documentation).
            if (a[2] <= 0x01 || (a[2] == 0x0D && a[3] == 0xB8))
                return false;
        }

        // 6to4: the IPv4 address it wraps decides.
        if (a[0] == 0x20 && a[1] == 0x02)
            return IsPublicV4(a.Slice(2, 4));

        // 3fff::/20 (documentation).
        return !(a[0] == 0x3F && a[1] == 0xFF && (a[2] & 0xF0) == 0);
    }
}
