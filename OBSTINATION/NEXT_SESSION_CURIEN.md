# NEXT SESSION — Curien's machine, and the case split on `(past)`

**Source:** P.-L. Curien, *Sequential interactive behaviour of recursive program
schemes*, talk, Tallinn University of Technology, 19 December 2017 (`curien.pdf`
at the repository root, 56 slides). Slides 8–26 are Kahn–Plotkin cds and
Berry–Curien sequential algorithms; 27–39 interpret primitive recursive
*schemes*; 40–56 are a proof of Colson's ultimate obstinacy theorem in that
setting.

Read slides **37, 38, 49, 50** before anything else. They are the content.

---

## 1. What this is, relative to what we have

It is **David's setting made explicit**, not a third notion. `prinf.tex`'s
Remark 1 already records that David's trace is "in his own reading, a branch of
a Berry–Curien sequential algorithm"; this talk works directly with those
branches. A branch carries `valof c_{n.i}` — which cell of which argument was
read — so it is the labelled datum, and it is not our walk. Nothing in the talk
defines one from the other, and the remark stands unchanged.

The theorem is stated on slide 40: for a scheme `f` of arity `n`, every infinite
branch `q` of `[[f]]` has `{n | valof c_{n.i} occurs in q}` finite for every `i`
except a unique `i₀`. That is our clause (i), stated on the labelled branch.

**Scope, and do not overstate it:** the grammar of schemes (slide 27) has only
`rec(g,h)`. There is **no mutual recursion anywhere in the talk.** What can port
to a block is the machine and the criterion of §3 below, not a theorem.

## 2. The machine (slides 32–38)

An abstract machine for `f = rec(g,h)` whose states carry a **stack of frames**
`[Sᵐ(⊥), qʰ]`, one per pending recursive call, together with the ambient `y⃗`
and a marker for who has control (`?` = question, `!` = answer).

- push — "Recursive calls" (37): reaching `valof c_{?i}` in the current frame
  pushes a new frame, the depth argument decremented.
- pop — "Returns to the recursive calls" (38): an `output S` at depth `j < i`
  pops with `j+1`; an `output v` at depth `i` answers the pending `valof c_{?i}`.
- `S[← v]` (35) propagates an answer down the whole stack, with
  `Sⁿ(⊥)[← S] = Sⁿ⁺¹(⊥)` and `Sⁿ(⊥)[← 0] = Sⁿ(0)`.

Ours indexes unfoldings by the numeral depth; his by stack depth. Same dynamics.
His version is the one that generalises to a block most cheaply — a frame would
simply carry which component it belongs to, and the pop rule would dispatch on
that tag.

## 3. **The race — slides 49 and 50. This is the item to use.**

> `bʰ` is **i-OK** if `valof c_{?i}` occurs in `bʰ` and the number of `output`s
> in `bʰ` before it is `> i`.

- **i-OK up to `i`** ⟹ the machine reaches a stack of depth `i+1` (49).
- **not (i+1)-OK** ⟹ the machine reaches
  `[Sᵖ(⊥), rʰ valof c_{?i}][Sᵖ⁺¹(⊥), rʰ valof c_{?i}]` — *the same prefix of
  `bʰ` revisited* — "without contributing a new `valof c_{i.j}` to `b`, since it
  is the same part of `bʰ` which is revisited, and hence any such calls have
  thus been already made". From there it produces **stacks of unbounded depth in
  a loop** (50).

His own summary: *"there is a **race** between the `output`s and the
`valof c_{?i}`s of `bʰ` : enough `output`s must be issued ahead of the
`valof c_{?i}` to prevent such a loop of recursive calls."*

Two things follow for us.

1. The race is the **operational form of the verdict clause** of Definition 1 —
   enough successors must be produced, soon enough, relative to the demands. It
   is the same phenomenon `PhiOK` and `C_mut` measure arithmetically. (It is not
   literally either predicate; do not claim it is.)
2. The failing side is **IMG_0241's lemma**: while the machine loops it
   contributes no new demand on an argument — the value is frozen unless the
   demand is the recursion argument. See `project_img0241_terminal_clause`.

## 4. The route this suggests: split on `(past)`, do not discharge it

`TrMrecCalls.MFIXC.ON` takes three hypotheses, of which `(never)` and `(incomp)`
are the obstinate regime and

```agda
past : (i : Nat) (X : FTup) -> LeX (R.avT r p Tg L zero) X -> LeN (Nth i) (pos i X)
```

is the one flagged as not free — a step term stuck on a parameter never advances,
so never reaches the threshold `Nth i` at which its walk's label has settled.

**Curien never discharges his analogue. He cases on it**, and the failing branch
is a result, not a gap: not i-OK ⟹ loop ⟹ unbounded stack ⟹ **the index is the
recursion argument** (Cases 2(c), 2(d), slides 51–53).

The split is free for us: `pos i X` and `Nth i` are naturals and
`Prelude.LeN-dec : (m n : Nat) -> Dec (LeN m n)` decides `LeN`, so
`LeN-dec (Nth i) (pos i X)` is a constructive two-way case at every `X`. Nothing
has to be assumed to perform it — the work is entirely on the negative side.

So the shape to aim for is

```
      for each component i and each X on the cone:
        past  holds  ->  TrMrecCalls.CALLS.calls   (already proved)
        past  fails  ->  the demand is the depth coordinate
```

and the second disjunct is a shape we already have a name and a theorem for:
`BlkVerdD`'s fourth shape `Dep` (demand = the unfolding depth), with
`BlkIdxD.main` proving the block's index settles in the depth coordinate at
general `r` and `BlkIdxD2.qmain` at `r = 2`. His index trichotomy
`j` / `⋄` / `⋆` (a parameter, the recursion argument, the recursive call) is our
`Self` / `Cross` / `Dep` / parameter split, and the correspondence is close
enough to be worth checking case by case before writing any Agda.

**Concretely, the next step is to state and prove the negative branch**: from
`¬ LeN (Nth i) (pos i X)` on the cone, derive that the walk's demand is the
depth coordinate — i.e. that the trace is in `Dep`. Curien's argument for it is
the revisited-prefix loop of slide 50, whose ingredients we have separately:
a stall is permanent (`TrPrecStall`), and the depth sequence is the orbit of one
map (`TrMrecFix.MFIX.iter` conditionally, `TrMrecPsi.PFIX.psi-fix`
unconditionally).

## 5. Correspondence table

| Curien (talk) | here |
|---|---|
| branch of `[[f]]`, with `valof c_{n.i}` | David's labelled trace — **not** our walk |
| infinite branch, unique `i₀` (slide 40) | clause (i), `EvConstN` on `iv` |
| stack of frames `[Sᵐ(⊥), qʰ]` | the unfolding depth of the block trace |
| `S[← v]`, `Sⁿ(⊥)[← S] = Sⁿ⁺¹(⊥)` | `sucIt`, the depth shift of `TrMrecPsi` |
| i-OK: enough `output`s before `valof c_{?i}` | the verdict clause; `PhiOK`, `C_mut` |
| revisited prefix, no new argument call (50) | IMG_0241's terminal clause; stall is permanent |
| unbounded stack ⟹ index `⋄` (51–53) | `Dep`, `BlkIdxD.main` |
| index `j` = a parameter (2(a), 2(b)) | the parameter shapes; `BlkFunPar` |
| Case 3: `≤ n` branches of `h`, one of `g`, one infinite | the finite-box / pigeonhole step |
| `f ◦ ⟨g⃗⟩`: `q'` finite or infinite (42) | the two regimes of composition |

## 6. Caveats

- **Slides, and classical.** "the branch `bʰ` is infinite" and "let `i` be
  maximum such that `c_{?i}` occurs in `bʰ`" are exactly the decisions we must
  pay for constructively. This is the same tax as attained-versus-bounded
  suprema (`BlkAnswer.ANS.split`) and as `TrUOFail`. Expect the transcription,
  not the argument, to be the work.
- **No blocks.** See §1. The machine ports; the theorem does not come for free.
- `curien.pdf` is third-party and is not committed, like `david1.pdf` /
  `david2.pdf`.
