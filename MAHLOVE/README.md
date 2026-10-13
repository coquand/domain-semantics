# MAHLOVE: Palmgren's paradox for a closed Mahlo universe

Palmgren observed that Setzer's Mahlo universe V becomes inconsistent once
it is made *closed*, that is, once it gets an elimination rule. This
directory derives that inconsistency inside the object theory. It takes the
annotated Russell Mahlo theory of `MAHLO/Typing`, adds V-elimination, and
derives a closed term of type

    Bot = Π X:V. X

Every small type in the theory is inhabited, so `Π X:V. X` plays the role
of falsum here.

Everything is `--safe --without-K --exact-split`, with no postulates and no
pragmas. To check it (about 1s):

```sh
agda MAHLOVE/Palmgren.agda
```

## Files

| File | Content |
|---|---|
| [`Basic`](Basic.agda) | the identity type, so that the directory builds on its own |
| [`Syntax`](Syntax.agda) | the raw syntax of `MAHLO/Syntax`, copied verbatim, plus one new former `VElim C cN cP cS cU t` |
| [`Typing`](Typing.agda) | the typing rules of `MAHLO/Typing`, copied verbatim, plus the V-elimination rules (marked NEW) |
| [`Palmgren`](Palmgren.agda) | the derivation `palmgren : HasType empty palm Bot` |

`MAHLO/Syntax` and `MAHLO/Typing` are frozen and are not changed here. Adding
a constructor to their `Expr` would break every development built on them.

## The rule

The cases bind their variables directly, as in Martin-Löf's original
elimination rules. Each computation rule is therefore a single substitution.

For a motive `x:V ⊢ C type`:

- `cN : C[N]`
- `A:V, B:A→V, iA:C[A], iB:Π y:A. C[B y] ⊢ cP : C[Π A B]`, and the same for Σ with `cS`
- `f:OpF, g:OpG f, if:Π a b. C[f a b], ig:Π a b c. C[g a b c] ⊢ cU : C[U(f,g)]`

From these, `velim(C; cN, cP, cS, cU; t) : C[t]` for every `t : V`. There
are computation rules `conv-VElim-Nat/Pi/Sigma/U`, and a congruence rule
`conv-VElim` in the eliminated term. A full congruence rule would only
strengthen the theory, so the inconsistency still holds with it.

## The derivation

Equality is Leibniz equality, `Leib x y = Π P:V→V. P x → P y`, since the
theory has no identity type.

- Let `f0 = λa b. a`, `g0 = λa b c. N`, and `w0 = U(f0, g0)`.
- `proj = velim(OpF; k, k, k, f)` satisfies `proj U(f,g) = f`. This gives
  injectivity of `U` in `f`.
- `PX = λy. velim(V; N, N, N, X; y)` sends U-codes to X and every other code
  to N. This gives no-confusion: from `e : Leib c w0`, where c is N, a Π code
  or a Σ code, the term `λX. e PX 0` has type Bot.
- The motive is `Q x = Leib x w0 → Bot`. In the U case:
  - transporting `e : Leib U(f,g) w0` along `h y = proj y w0 (λ_. w0)` gives
    `Leib (f w0 b0) w0`;
  - the induction hypothesis at `a = w0` turns this into Bot.

  This is where the paradox lies. The induction hypothesis for `U(f,g)`
  ranges over all `a : V`, including `U(f,g)` itself, and `f0 w0 b0 = w0`.
- Finally, `palm = velim(Q; qN, qP, qS, qU; w0) (refl w0) : Bot`.

Only `ty-VElim` and the computation rules are used, not the congruence rule.
The Π and Σ computation rules are stated at type `C[Π A B]`. The case's own
type is `C[Π A (λy. (λA.B) y)]`, which is β-equal to it under a binder.

## Relation to the models

The Mahlo universe cannot be an inductive definition: the constructor
`U(f,g)` takes `f : (a:V) → (El a → V) → V`, which mentions V in a negative
position. The models of `MAHLO` interpret V as a fixed point, not as a
well-founded generation, so they validate no V-elimination. This paradox
shows that they cannot.

This fits the reading that universes are explained by reflection, not by
induction. A metatheoretic version of the same argument, `ClosedMahlo -> Empty`
for any structure with an eliminator, is in `MAHLO/Palmgren.agda`.
