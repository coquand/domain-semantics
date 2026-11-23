"""The bounded Ehrhard signature, with FA constructor names as term symbols."""

from dataclasses import dataclass


@dataclass(frozen=True)
class Operation:
    symbol: str
    telescope: tuple
    sort: tuple
    levels: tuple = ()
    bounds: tuple = ()


@dataclass(frozen=True)
class Equation:
    name: str
    telescope: tuple
    sort: tuple
    left: str
    right: str
    levels: tuple = ()
    bounds: tuple = ()


ctx = ("ctx",)


def sub(source, target):
    return "Sub", source, target


def ty(context):
    return "Ty", context


def tm(context, type_):
    return "Tm", context, type_


Q, T, D, G = ((name, ctx) for name in ("Q", "T", "D", "G"))
A = ("A", ty("G"))
B = ("B", ty("(fext G A)"))
S = ("s", sub("D", "G"))
DELTA = ("d", sub("T", "D"))
ARG = ("a", tm("G", "A"))
BODY = ("b", tm("(fext G A)", "B"))
FUNCTION = ("c", tm("G", "(fpi G A B)"))
CODE = ("a", tm("G", "(fuu n G)"))
LOWER_CODE = ("a", tm("G", "(fuu m G)"))
CODE_CONTEXT = "(fext G (fel n G a))"
CODE_BODY = ("b", tm(CODE_CONTEXT, f"(fuu n {CODE_CONTEXT})"))

SORTS = {
    "ctx": (),
    "Sub": (D, G),
    "Ty": (G,),
    "Tm": (G, A),
}

OPERATIONS = (
    Operation("fnil", (), ctx),
    Operation("fext", (G, A), ctx),
    Operation("fid", (G,), sub("G", "G")),
    Operation("fcomp", (T, D, G, S, DELTA), sub("T", "G")),
    Operation("feps", (G,), sub("G", "fnil")),
    Operation("fp", (G, A), sub("(fext G A)", "G")),
    Operation("flift", (D, G, A, S), sub("(fext D (ftsb D G A s))", "(fext G A)")),
    Operation("fsec", (G, A, ARG), sub("G", "(fext G A)")),
    Operation("ftsb", (D, G, A, S), ty("D")),
    Operation("fmsb", (D, G, A, ARG, S), tm("D", "(ftsb D G A s)")),
    Operation("fq", (G, A), tm("(fext G A)", "(ftsb (fext G A) G A (fp G A))")),
    Operation("fpi", (G, A, B), ty("G")),
    Operation("flam", (G, A, B, BODY), tm("G", "(fpi G A B)")),
    Operation("fapp", (G, A, B, FUNCTION, ARG), tm("G", "(ftsb G (fext G A) B (fsec G A a))")),
    Operation("fuu", (G,), ty("G"), ("n",), ("LeN n N",)),
    Operation("fel", (G, CODE), ty("G"), ("n",), ("LeN n N",)),
    Operation("fpic", (G, CODE, CODE_BODY), tm("G", "(fuu n G)"), ("n",), ("LeN n N",)),
    Operation("fuc", (G,), tm("G", "(fuu n G)"), ("m", "n"), ("LeN (suc m) n", "LeN n N")),
    Operation("flf", (G, ("a", tm("G", "(fuu m G)"))), tm("G", "(fuu n G)"),
              ("m", "n"), ("LeN (suc m) n", "LeN n N")),
)


EQUATIONS = (
    # Category and terminal
    Equation('fq-idl', (D, G, S), sub('D', 'G'),
        '(fcomp D G G (fid G) s)',
        's'),
    Equation('fq-idr', (D, G, S), sub('D', 'G'),
        '(fcomp D D G s (fid D))',
        's'),
    Equation('fq-assoc', (Q, T, D, G, S, DELTA, ('e', sub('Q', 'T'))), sub('Q', 'G'),
        '(fcomp Q T G (fcomp T D G s d) e)',
        '(fcomp Q D G s (fcomp Q T D d e))'),
    Equation('fq-eps', (G, ('s', sub('G', 'fnil'))), sub('G', 'fnil'),
        's',
        '(feps G)'),

    # Functoriality of the actions
    Equation('fe-sb-id', (G, A), ty('G'),
        '(ftsb G G A (fid G))',
        'A'),
    Equation('fe-sb-comp', (T, D, G, A, S, DELTA), ty('T'),
        '(ftsb T D (ftsb D G A s) d)',
        '(ftsb T G A (fcomp T D G s d))'),
    Equation('fm-sb-id', (G, A, ARG), tm('G', 'A'),
        '(fmsb G G A a (fid G))',
        'a'),
    Equation('fm-sb-comp', (T, D, G, A, ARG, S, DELTA), tm('T', '(ftsb T G A (fcomp T D G s d))'),
        '(fmsb T D (ftsb D G A s) (fmsb D G A a s) d)',
        '(fmsb T G A a (fcomp T D G s d))'),

    # Ehrhard's equations
    Equation('fq-lift-id', (G, A), sub('(fext G (ftsb G G A (fid G)))', '(fext G A)'),
        '(flift G G A (fid G))',
        '(fid (fext G A))'),
    Equation('fq-lift-comp', (T, D, G, A, S, DELTA), sub('(fext T (ftsb T G A (fcomp T D G s d)))', '(fext G A)'),
        '(flift T G A (fcomp T D G s d))',
        '(fcomp (fext T (ftsb T D (ftsb D G A s) d)) (fext D (ftsb D G A s)) (fext G A) '
        '(flift D G A s) (flift T D (ftsb D G A s) d))'),
    Equation('fq-p-lift', (D, G, A, S), sub('(fext D (ftsb D G A s))', 'G'),
        '(fcomp (fext D (ftsb D G A s)) (fext G A) G (fp G A) (flift D G A s))',
        '(fcomp (fext D (ftsb D G A s)) D G s (fp D (ftsb D G A s)))'),
    Equation('fq-p-sec', (G, A, ARG), sub('G', 'G'),
        '(fcomp G (fext G A) G (fp G A) (fsec G A a))',
        '(fid G)'),
    Equation('fq-sec-comp', (D, G, A, ARG, S), sub('D', '(fext G A)'),
        '(fcomp D G (fext G A) (fsec G A a) s)',
        '(fcomp D (fext D (ftsb D G A s)) (fext G A) (flift D G A s) (fsec D (ftsb D G '
        'A s) (fmsb D G A a s)))'),
    Equation('fq-lift-p-sec-q', (G, A), sub('(fext G A)', '(fext G A)'),
        '(fcomp (fext G A) (fext (fext G A) (ftsb (fext G A) G A (fp G A))) (fext G A) '
        '(flift (fext G A) G A (fp G A)) (fsec (fext G A) (ftsb (fext G A) G A (fp G A)) '
        '(fq G A)))',
        '(fid (fext G A))'),
    Equation('fm-q-lift', (D, G, A, S), tm('(fext D (ftsb D G A s))', '(ftsb (fext D (ftsb D G A s)) D (ftsb D G A s) (fp D (ftsb D G A s)))'),
        '(fmsb (fext D (ftsb D G A s)) (fext G A) (ftsb (fext G A) G A (fp G A)) (fq G '
        'A) (flift D G A s))',
        '(fq D (ftsb D G A s))'),
    Equation('fm-q-sec', (G, A, ARG), tm('G', 'A'),
        '(fmsb G (fext G A) (ftsb (fext G A) G A (fp G A)) (fq G A) (fsec G A a))',
        'a'),

    # Products
    Equation('fe-pi-sb', (D, G, A, B, S), ty('D'),
        '(ftsb D G (fpi G A B) s)',
        '(fpi D (ftsb D G A s) (ftsb (fext D (ftsb D G A s)) (fext G A) B (flift D G A '
        's)))'),
    Equation('fm-lam-sb', (D, G, A, B, BODY, S), tm('D', '(fpi D (ftsb D G A s) (ftsb (fext D (ftsb D G A s)) (fext G A) B (flift D G A s)))'),
        '(fmsb D G (fpi G A B) (flam G A B b) s)',
        '(flam D (ftsb D G A s) (ftsb (fext D (ftsb D G A s)) (fext G A) B (flift D G A '
        's)) (fmsb (fext D (ftsb D G A s)) (fext G A) B b (flift D G A s)))'),
    Equation('fm-app-sb', (D, G, A, B, FUNCTION, ARG, S), tm('D', '(ftsb D (fext D (ftsb D G A s)) (ftsb (fext D (ftsb D G A s)) (fext G A) B (flift D G A s)) (fsec D (ftsb D G A s) (fmsb D G A a s)))'),
        '(fmsb D G (ftsb G (fext G A) B (fsec G A a)) (fapp G A B c a) s)',
        '(fapp D (ftsb D G A s) (ftsb (fext D (ftsb D G A s)) (fext G A) B (flift D G A '
        's)) (fmsb D G (fpi G A B) c s) (fmsb D G A a s))'),
    Equation('fm-beta', (G, A, B, BODY, ARG), tm('G', '(ftsb G (fext G A) B (fsec G A a))'),
        '(fapp G A B (flam G A B b) a)',
        '(fmsb G (fext G A) B b (fsec G A a))'),
    Equation('fm-eta', (G, A, B, ('f', tm('G', '(fpi G A B)'))), tm('G', '(fpi G A B)'),
        'f',
        '(flam G A B (fapp (fext G A) (ftsb (fext G A) G A (fp G A)) (ftsb (fext (fext '
        'G A) (ftsb (fext G A) G A (fp G A))) (fext G A) B (flift (fext G A) G A (fp G '
        'A))) (fmsb (fext G A) G (fpi G A B) f (fp G A)) (fq G A)))'),

    # Universe naturality
    Equation('fe-uu-sb', (D, G, S), ty('D'),
        '(ftsb D G (fuu n G) s)',
        '(fuu n D)',
        ('n',), ('LeN n N',)),
    Equation('fe-el-sb', (D, G, CODE, S), ty('D'),
        '(ftsb D G (fel n G a) s)',
        '(fel n D (fmsb D G (fuu n G) a s))',
        ('n',), ('LeN n N',)),
    Equation('fm-pic-sb', (D, G, CODE, CODE_BODY, S), tm('D', '(fuu n D)'),
        '(fmsb D G (fuu n G) (fpic n G a b) s)',
        '(fpic n D (fmsb D G (fuu n G) a s) (fmsb (fext D (ftsb D G (fel n G a) s)) '
        '(fext G (fel n G a)) (fuu n (fext G (fel n G a))) b (flift D G (fel n G a) '
        's)))',
        ('n',), ('LeN n N',)),
    Equation('fm-uc-sb', (D, G, S), tm('D', '(fuu n D)'),
        '(fmsb D G (fuu n G) (fuc m n G) s)',
        '(fuc m n D)',
        ('m', 'n'), ('LeN (suc m) n', 'LeN n N')),
    Equation('fm-lf-sb', (D, G, LOWER_CODE, S), tm('D', '(fuu n D)'),
        '(fmsb D G (fuu n G) (flf m n G a) s)',
        '(flf m n D (fmsb D G (fuu m G) a s))',
        ('m', 'n'), ('LeN (suc m) n', 'LeN n N')),

    # Tarski and lift equations
    Equation('fe-el-pic', (G, CODE, CODE_BODY), ty('G'),
        '(fel n G (fpic n G a b))',
        '(fpi G (fel n G a) (fel n (fext G (fel n G a)) b))',
        ('n',), ('LeN n N',)),
    Equation('fe-el-uc', (G,), ty('G'),
        '(fel n G (fuc m n G))',
        '(fuu m G)',
        ('m', 'n'), ('LeN (suc m) n', 'LeN n N')),
    Equation('fe-el-lf', (G, LOWER_CODE), ty('G'),
        '(fel n G (flf m n G a))',
        '(fel m G a)',
        ('m', 'n'), ('LeN (suc m) n', 'LeN n N')),
    Equation('fm-lf-pic', (G, CODE, CODE_BODY), tm('G', '(fuu p G)'),
        '(flf n p G (fpic n G a b))',
        '(fpic p G (flf n p G a) (flf n p (fext G (fel n G a)) b))',
        ('n', 'p'), ('LeN (suc n) p', 'LeN p N')),
    Equation('fm-lf-uc', (G,), tm('G', '(fuu p G)'),
        '(flf n p G (fuc m n G))',
        '(fuc m p G)',
        ('m', 'n', 'p'), ('LeN (suc m) n', 'LeN (suc n) p', 'LeN p N')),
    Equation('fm-lf-lf', (G, LOWER_CODE), tm('G', '(fuu p G)'),
        '(flf n p G (flf m n G a))',
        '(flf m p G a)',
        ('m', 'n', 'p'), ('LeN (suc m) n', 'LeN (suc n) p', 'LeN p N')),
)
