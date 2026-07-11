# Kahn–Plotkin sequentiality for the lazy naturals

**Remark (the point).** It is remarkable that the ultimate-obstination proof
uses only **stability** (Berry) of the elements of `PR`, and *not* the stronger
notion of **sequentiality** (Kahn–Plotkin). This note records how the
Kahn–Plotkin sequentiality condition specializes to the lazy-natural domain, so
that the two notions can be compared directly — and, in particular, so one can
ask whether the special inequality $p \le_s \mathrm{id}$ (a projection) forces
sequentiality even though stability alone does not.

---

Let

$$
N=\{\bot,S\bot,S^2\bot,\ldots\}\cup
\{0,S0,S^20,\ldots\}\cup\{S^\omega\}
$$

with the prefix order. For $x=(x_1,\ldots,x_n)\in N^n$, an **accessible input
cell** is precisely an $i$ such that

$$
x_i=S^{k_i}\bot
$$

for some $k_i$: the next question is whether the next constructor is $0$ or $S$.

Now let

$$
f:N^n\longrightarrow N
$$

be Scott-continuous. Suppose

$$
f(x)=S^m\bot.
$$

Thus the first $m$ output constructors are known to be $S$, and the **next output
cell** is unanswered.

Then the Kahn–Plotkin sequentiality condition specializes to:

$$
\boxed{
\begin{array}{l}
\text{Either no }y\geq x\text{ determines the next output cell},\\[2mm]
\text{or there is }i\text{ with }x_i=S^{k_i}\bot\text{ such that}\\[1mm]
\qquad
f(y)>S^m\bot\Longrightarrow y_i>S^{k_i}\bot
\qquad\text{for every }y\geq x.
\end{array}}
\tag{Seq}
$$

Here

$$
y_i>S^{k_i}\bot
$$

means that the next cell of argument $i$ has been answered, i.e. $y_i$ extends
either to

$$
S^{k_i}0
\quad\text{or}\quad
S^{k_i+1}\bot
$$

(and possibly further).

The index $i$, more precisely the cell $(i,k_i)$, is a **sequentiality index for
the requested output cell**.

So one can write the active case more compactly as

$$
\exists(i,k)\quad
x_i=S^k\bot
\quad\land\quad
\forall y\geq x,\;
\bigl(f(y)>f(x)\Rightarrow y_i>x_i\bigr),
\tag{1}
$$

provided $f(x)=S^m\bot$. Since the output is a chain-shaped data structure,
$f(y)>f(x)$ exactly means that the presently requested next output constructor
has been obtained.

## Example: predecessor

For

$$
\operatorname{pred}(\bot)=\bot,\qquad
\operatorname{pred}(0)=0,\qquad
\operatorname{pred}(Sx)=x,
$$

at input $S\bot$,

$$
\operatorname{pred}(S\bot)=\bot.
$$

To determine the first output cell, one must determine the next input cell:

$$
y\geq S\bot,\quad \operatorname{pred}(y)>\bot
\quad\Longrightarrow\quad
y>S\bot.
$$

So the cell at depth $1$ of the input is the sequentiality index.

## More generally, at a partial output

Suppose

$$
f(x)=S^m\bot.
$$

To produce the $(m+1)$-st output constructor, there must be some currently
unanswered input constructor whose answer is necessary for *every* way of
producing that output constructor:

$$
\exists i\quad
\forall y\geq x,\qquad
f(y)>S^m\bot \Longrightarrow y_i>x_i.
$$

This is exactly the generalization of the flat criterion

$$
f(y)\neq\bot\Longrightarrow y_i\neq\bot.
$$

For flat $\mathbb N_\bot$, every input has only one possible unanswered cell, so
$x_i=\bot$ and $y_i>x_i$ becomes simply $y_i\neq\bot$.

There is one important qualification: the first alternative should be phrased as

$$
\forall y\ge x,\quad f(y)=S^m\bot,
$$

i.e. the requested output cell is **never answered**. Thus the complete condition
is

$$
\boxed{
f(x)=S^m\bot\Longrightarrow
\left[
\begin{array}{l}
\forall y\ge x,\;f(y)=S^m\bot,\\
\text{or}\\
\exists i,\;x_i=S^k\bot\ \land
\forall y\ge x,\;
f(y)>S^m\bot\Rightarrow y_i>x_i.
\end{array}
\right].
}
\tag{KP-Nat}
$$

For the lazy natural-number concrete data structure, this is precisely the
specialization of the Kahn–Plotkin definition: the sequentiality index depends on
the **requested output cell**, which was their crucial refinement of the earlier
flat-domain notion. Berry and Curien explicitly emphasize this point. [1]

I think this formulation may be quite useful for the original question: for a
projection $p\leq_s\mathrm{id}$ on $N^n$, one can now ask directly whether
stability forces condition $(\mathrm{KP\text{-}Nat})$. The suspicion is that the
special inequality $p\leq_s\mathrm{id}$ may indeed force sequentiality, even
though stability alone does not.

---

[1] G. Berry, P.-L. Curien. "Sequential algorithms on concrete data structures."
<https://www.researchgate.net/profile/Gerard_Berry2/publication/222723389_Sequential_algorithms_on_concrete_data_structures/links/5ba40986299bf13e6040e1ac/Sequential-algorithms-on-concrete-data-structures.pdf>
