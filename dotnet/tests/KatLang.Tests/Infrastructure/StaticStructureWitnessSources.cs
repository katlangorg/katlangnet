namespace KatLang.Tests;

// Exact source witnesses preserved from the approved B3 handoff; no dependency on ignored evidence at test time.
internal static class StaticStructureWitnessSources
{
    internal static readonly IReadOnlyDictionary<string, string> Cases = new Dictionary<string, string>
    {
        ["strata0-ambiguous"] = "open Back\nA = B\nB = {\n    public N = 5\n    A\n}\nBack = { public N = G.R }\nG = {\n    open A\n    public R = C\n    C = {\n        public X = Ref\n        N\n    }\n    0\n}\nF = {\n    open G.R\n    X\n}\nP = {\n    public Q = 42\n    F\n}\nRef = P\nOther = { public Q = 1 }\nH = {\n    open Ref, Other\n    Q + 0\n}\nH",
        ["strata0-get"] = "open Back\nA = B\nB = {\n    public N = 5\n    A\n}\nBack = { public N = G.R }\nG = {\n    open A\n    public R = C\n    C = {\n        public X = Ref\n        N\n    }\n    0\n}\nF = {\n    open G.R\n    X\n}\nP = {\n    public Q = 42\n    F\n}\nRef = P\nGet(z) = Ref.Q + 0\nGet(1)",
        ["A.3.1"] = "K(v) = 1000\nT(v) = 0\nU(v) = 0\nLib2 = { public y = 1 }\nLib3 = { public x = 10 }\nL = { public x = P.R }\nL3 = { public y = P.R2 }\nP = {\n    public R = C\n    C = {\n        open L\n        public T = Lib2\n        x\n    }\n    public R2 = C2\n    C2 = {\n        open L3\n        public U = Lib3\n        y\n    }\n    R.T.y + R2.U.x\n}\nP(K)",
        ["A.3.2"] = "L = { public m = P.R }\nL2 = { public n = { public m = 1 } }\nP = {\n    public R = C\n    C = {\n        open L\n        public n = 1\n        m\n    }\n    N = {\n        open L2\n        public S = n\n        0\n    }\n    R.n + N.S.m\n}\n5",
        ["A.3.3a"] = "Lib = { public a = 1 }\nLA = { public a = P.R3 }\nLB = { public a = P.R }\nP = {\n    open T\n    T = Cx\n    Cx = {\n        open L7\n        public y = Lib\n        b\n    }\n    L7 = { public b = T }\n    R2 = y\n    public R = C1\n    C1 = {\n        public b = 1\n        Cb\n    }\n    Cb = {\n        open L2\n        b\n    }\n    L2 = { public b = CaR }\n    CaR = {\n        open LB\n        a\n    }\n    public R3 = Cc\n    Cc = {\n        public c = 1\n        Ca3\n    }\n    Ca3 = {\n        open LA\n        a\n    }\n    R3.c + R.b + R2.a\n}\n5",
        ["A.3.3b"] = "K(v) = 1000\nX = { public e = { public e = 1 } }\nY = { public p = { public q = 1 } }\nLe = { public e = P.Rp }\nP = {\n    N = {\n        open X\n        public A = e\n        0\n    }\n    M = {\n        open Y\n        public B = p\n        0\n    }\n    public Rp = Cp\n    Cp = {\n        open Lp\n        public p = 1\n        q\n    }\n    Lp = { public q = Dp }\n    public Dp = {\n        open Le\n        e\n    }\n    N.A.e + M.B.q + Rp.p\n}\nP(K)",
    };
}
