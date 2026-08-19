# Fiber–Aggregation Lean Prototype

This branch contains a conservative Lean model of the proposed **fiber–aggregation** language.
It is a model *inside* Lean's dependent type theory, not yet a replacement kernel or a proof that
the proposed foundation is stronger than ZFC.

## Reproducible verification

The project is pinned to Lean `v4.30.0` and mathlib `v4.30.0`. GitHub Actions runs:

```bash
lake exe cache get
lake build --wfail
```

The workflow also rejects `sorry` and `admit` in the project sources.

## Formalized core

- An aggregate is modeled by a Lean type.
- A fiber rule is modeled by a function.
- `Fiber f b := {a // f a = b}`.
- Aggregating all fibers reconstructs the domain:

  ```text
  (Σ b, Fiber f b) ≃ A
  ```

- Fibers compose by dependent aggregation:

  ```text
  Fiber (g ∘ f) c ≃ Σ y : Fiber g c, Fiber f y.1
  ```

- `All` is a dependent product; `Some` is a dependent sum; relative membership is a pullback fiber.
- Thin rules are exactly injective rules.
- A finite rule satisfies the exact fiber-cardinality decomposition

  ```text
  card A = ∑ b, card (Fiber f b).
  ```

## Verified consequences and applications

### Diagonal obstruction

A Lawvere-style theorem proves that a self-evaluation rule representing every observable profile
forces every observable endomorphism to have a fixed point. Boolean negation therefore rules out
complete Boolean-valued self-encoding. This is a conditional obstruction, not an unconditional
proof that every weak notion of a universal aggregate is impossible.

### Groups

- Stabilizers are fibers of orbit rules.
- Kernels are fibers over the unit.
- Fibers over points in one orbit are equivalent by translation.
- Orbit–stabilizer is recovered from fiber aggregation.

### Noether schema

For an abstract variational system, the Euler–Lagrange solution aggregate is the zero fiber of the
Euler–Lagrange rule. Once the first-variation identity is supplied as differential structure, its
restriction to the solution fiber yields conservation of the associated current.

### Linear and elliptic-type equations

- A nonempty solution fiber of an additive operator is equivalent to its kernel after choosing one
  solution.
- Injectivity gives uniqueness; bijectivity gives a determinate solution fiber.
- Bessel-potential operators are proved bijective, so every corresponding equation fiber is
  determinate.
- The standard Sobolev theorem that the Laplacian sends `H^s` to `H^(s-2)` is exposed in the same
  interface.

### Modular forms

- Slash invariance is represented as an equalizer fiber and proved equivalent to mathlib's bundled
  `SlashInvariantForm`.
- Odd-weight modular forms vanish when `-1` belongs to the group, so that aggregate is determinate.
- The q-expansion rule is proved injective under a positive strict-period hypothesis. Consequently,
  every q-expansion fiber is subsingleton, and every fiber over an actual modular form is
  determinate.

### Weierstrass and elliptic curves

- An affine Weierstrass equation is the zero fiber of its residual rule.
- Standard point negation is an involutive self-equivalence preserving every residual fiber.
- `1728 Δ = c₄³ - c₆²` is represented as an equalizer-fiber witness.
- The j-invariant rule on elliptic Weierstrass models is surjective over every field.
- Over a separably closed field, each j-fiber is a single orbit under admissible changes of
  Weierstrass variables. Thus equal visible j-invariant does not imply literal equality of models;
  it determines the model up to the specified symmetry rule.

## What this prototype does not prove

Bare fiber structure does not produce analytic estimates, coercivity, boundary regularity,
compactness, Hecke theory, Sturm bounds, or a full theory of meromorphic modular functions. Those
require additional algebraic, topological, smooth, measure-theoretic, and analytic structure.

Lean's ordinary equality is also proof-irrelevant, so this prototype is the set-level shadow of the
higher-identity theory discussed philosophically. A genuinely higher version would need explicit
groupoids, higher categories, or a homotopical/cubical foundation, together with syntax,
computation rules, universe policy, normalization, and semantic consistency results.
