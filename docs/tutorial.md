# Naproche-ZF Tutorial


## Proof vernacular

Proof checking in Naproche-ZF relies on automated theorem provers like Vampire.
This means that reasoning can be quite loosely structured and many small details are taken care of automatically.
However, reasoning steps that require deep and complex reasoning may require more detailed proofs.

Within proofs, we distinguish between *global facts*, which are all preceding theorems that have been successfully proved, and *local assumptions*, which are the assumptions of the theorem statement (e.g. `Suppose ...`) or of individual proof steps (`Assume ...`) and *intermediate claims* that are established throughout the proof.

At the start of a proof, the *sufficiency* or *proof goal* corresponds to the conclusion of the theorem statement.
Some proof steps may change this sufficiency.

### Proof via intermediate claims

The simplest way to prove a statement is to make intermediate claims, relying on the proof automation to put everything together. Unless an explicit justification is given, all global facts are available to the proof automation.

In the following example, establishing the local fact that a restricted relation is a subset of itself, is enough detail for the proof automation to find the rest of the proof. As no explicit justification is given, all global facts can be used to establish that `$R$ is injective` and `$\restrl{R}{A}\subseteq R$` imply `$\restrl{R}{A}$ is injective`.

```tex
\begin{proposition}\label{restrl_injective}
    Suppose $R$ is injective.
    Then $\restrl{R}{A}$ is injective.
\end{proposition}
\begin{proof}
    $\restrl{R}{A}\subseteq R$.
\end{proof}
```

If explicit justification by reference given, then we the available global facts are restricted to only those explicitly listed. However, local assumptions and intermediate claims are always available. Explicitly justified proof steps are the best option in terms of stability and perfomance, since they minimize the search space for the proof automation.

```tex
\begin{proposition}\label{inters_of_family_of_equivalences_is_equivalence}
    Let $F$ be a family of relations.
    Suppose every element of $F$ is an equivalence.
    Then $\inters{F}$ is an equivalence.
\end{proposition}
\begin{proof}
    $\inters{F}$ is quasireflexive by \cref{quasireflexive,inters_destr,inters_iff_forall}.
    $\inters{F}$ is symmetric by \cref{symmetric,inters_iff_forall,inters_destr}.
    $\inters{F}$ is transitive by \cref{transitive,inters_iff_forall,inters_destr}.
\end{proof}
```

### Proof finishing steps

If no explicit proof-finishing step is given, the implicit last step is to establish the conclusion from everything that came before, including all global facts. Alternatively, we can again restrict to the number of global facts available with an explicit reference using the syntax `Follows by \cref{<labelname>}`.

```tex
\begin{proposition}\label{function_apply_default}
    Suppose $x\notin\dom{f}$.
    Then $f(x) = \emptyset$.
\end{proposition}
\begin{proof}
    $\img{f}{\{x\}} = \emptyset$ by \cref{setext,emptyset,img_singleton_iff,dom_intro}.
    Follows by \cref{apply,unions_emptyset}.
\end{proof}
```

There is also a built-in tactic that applies set extensionality, replacing a sufficiency of the form `A = B` with two sufficiencies `A\subseteq B` and `B\subseteq A`. This can be useful when you have to prove that two sets are equal.

```tex
\begin{proposition}\label{dom_circ_exact}
    Let $f, g$ be functions.
    Suppose $\ran{f} = \dom{g}$.
    $\dom{g\circ f} = \dom{f}$.
\end{proposition}
\begin{proof}
    Every element of $\dom{g\circ f}$ is an element of $\dom{f}$.
    Follows by set extensionality.
\end{proof}
```

### Assumption steps

If the suffiency is syntactically of the form `$\phi$ implies $\psi$` or similar, then we can locally assume `\phi` and are left with `\psi` as the sufficieny. Here is a simple artificial example.

```tex
\begin{proposition}\label{assumption_example}
    If $x\in y$ and $a\in b$, then $x\in y$.
\end{proposition}
\begin{proof}
    Assume $a\in b$. % Sufficiency is now "If $a\in b$, then $x\in y$."
    Assume $x\in y$. % Sufficiency is now "$x\in y$."
    Follows by assumption. % Finishing proof steps, which uses only local assumptions and intermediate claims (no global facts).
\end{proof}
```
