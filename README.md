# gravitas

A verified parallel N-body core, written in [Bend 2](https://bend-lang.com).

The point is not the gravity. The point is that the parallel reduction is
**proved** to do the right thing, so it cannot quietly stop.

```
$ bend PROOF.bend
All terms check.
```

---

## What this is

`main.bend` holds the physics: 2^d bodies in a balanced binary tree, a
gravitational field reduced over that tree, and a parallel integrator.
Parallelism is written once, as a fork-join:

```python
a b = field(p, x, px, py, soft) field(p, y, px, py, soft)
```

No threads, no locks, no atomics, no `#pragma omp`. The scheduler deals the
forks across every core it can find.

`LAWS.bend` states, in Bend's own type system, the ten rules that reduction
and the integrator must obey. `PROOF.bend` proves them. `bend PROOF.bend` is a
gate: it fails while any law is open or false.

The split is deliberate:

| | |
|---|---|
| **The shape** — how many bodies, how much mass, how the forks combine | exact `Nat`, and **proved** |
| **The numerics** — the gravity itself | `F32`, and *not* provable (Bend is axiomatic about floating point) |

## Run it

```sh
export PATH="$HOME/.bend/bin:$PATH"   # after: curl -fsSL https://bend-lang.com/install.sh | sh

bend PROOF.bend                       # the gate: all 10 laws
bend sim.bend                         # interpreted (slow, single core)
bend sim.bend -o sim && ./sim         # native, real fork-join
./sim --threads 1                     # for the scaling comparison
```

1024 bodies, 100 steps of O(N²) gravity, on a 16-core machine:

| threads | ms | speedup |
|---|---|---|
| 1 | 3565 | 1.00x |
| 2 | 3492 | 1.02x |
| 4 | 2085 | 1.71x |
| 8 | 1416 | 2.52x |
| 16 | 995 | **3.58x** |

Not linear, and honestly not expected to be: the join at every one of the ten
fork levels costs something, and the leaves are only 1024 units of work.

## The gate, demonstrated

The interesting claim is that a *legal* change to the code — one that type-checks
perfectly — can still be rejected because it breaks a law.

**Sabotage:** make fusion keep only the first operand's mass.

```diff
-  +mt = Nat.add(m1, m2)
+  +mt = Nat.add(m1, 0n)
```

```
$ bend main.bend --check-only
All terms check.                     # the type system is perfectly happy

$ bend PROOF.bend
Error:
- expected : Nat.add(m1, 0n)
- observed : Nat.add(m1, m2)
Location: LAWS.zip_mass
195 |       G.Body{+m2, x2, y2, +vx2, +vy2} = y
196>|       {==}
    |       ^^^^
```

The same thing happens if the count reduction forgets a body
(`case 0n: 1n` → `case 0n: 0n`): `main.bend` still checks, and `zip_count`,
`step_count` and `count_pow2` all fail.

And a *dumber* sabotage never gets that far. Reusing a subtree in both halves
of a fork is caught by the type system before a proof is even consulted:

```
Error: - expected : xl
       - observed : xl (consumed more than once)
```

## The ten laws

`LAWS.bend` is the specification. A human writes it and does not touch it again.

| law | says |
|---|---|
| `count_pow2` | counting a system of depth d gives exactly 2^d bodies |
| `accels_count` | rewriting a body never changes how many bodies there are |
| `step_count` | a simulation step never adds or drops a body |
| `accels_mass` | rewriting a body never changes the mass of its subtree |
| `step_mass` | a simulation step never changes the total mass |
| `field_split` | the pull from a two-subtree system is the sum of the pulls from each |
| `comsum_split` | the same for the centre-of-mass reduction |
| `zip_count` | fusing two systems yields a system the same size as either input |
| `zip_mass` | fusion carries exactly the combined mass — neither invented nor lost |
| `zip_swap` | fusion does not depend on the order of its operands |

`zip_mass` is the one that earns the arithmetic. The left side groups the four
partial masses as `(xl+yl) + (xr+yr)`, because that is the order the parallel
fusion happens to visit them; the right side groups them as `(xl+xr) + (yl+yr)`,
because that is the order the two input systems arrive in. `add_regroup` is the
lemma that says the grouping is not the answer — the sum is. `PROOF.bend` builds
that lemma (and `add_zero`, `add_succ`, `add_comm`, `add_assoc`, `add_swap`)
from nothing first, because Base ships a proof of `U32.add_comm` but no `Nat`
algebra at all.

## The provability boundary

One invariant is **not** in `LAWS.bend`, and it is worth being precise about
why. The natural law would be "a step never changes the total mass", and it is
false as stated anyway — but it is also *unprovable* here, for a reason that is
a property of the checker rather than of the physics:

> The proof checker reduces a definition only when the scrutinee is in
> constructor form, and it cannot look inside a value held in a variable. The
> leaf of a system is a `Body` record, so its mass sits behind a projection of
> a value the prover cannot take apart. `count` escapes this because its leaf
> returns the literal `1n`; `mass` has no such escape.

So `sim.bend` checks mass conservation at runtime instead
(`check_mass` calls `IO.die`), and the report says so honestly rather than
claiming a proof it does not have. The real fix is architectural: carry the
masses in a parallel tree of bare `Nat`s so the aggregate never sits behind a
rebuilt record. That refactor is the obvious next step, and it is the honest
answer to "how would you make this fully verified".

The centre of mass drifting from `(0.233, 1.040)` to `(0.264, 1.094)` over 100
steps is likewise F32 rounding, not a bug: each body's field is summed in a
different order from every other body's, so the Newton's-third-law pairs do not
cancel exactly. It is reported, not proved — and it is a useful bug detector,
because it moves if a fork is ever wrong.

## Layout

```
main.bend    the physics: Body, Sys(d), count, mass, field, comsum, accels, step, zip
LAWS.bend    the specification: 10 laws, human-written
PROOF.bend   the proofs: Nat arithmetic from scratch, then one def per law
sim.bend     the driver: deterministic spawn, 100 steps, runtime invariant checks
bend         a wrapper that runs bend and strips the huge context dumps
```

## Use cases worth stealing this for

The pattern that generalises past gravity:

- **Anything with a parallel reduction and an invariant.** Sort, dedup, tree
  reduce, histogram, scan, physics. Write the law, get the proof.
- **Merging runs safely.** `zip` is the operation behind combining two
  simulations; `zip_mass` and `zip_swap` are what you want before trusting it.
- **A sandbox for AI-written code.** The intended use of `LAWS.bend` is as an
  ambiguity-free `AGENTS.md` backed by proof: state the rules, let an agent
  write the code, and the compiler refuses any edit that breaks a rule. You
  audit the laws once instead of the diff forever.
- **A spec that runs.** `LAWS.bend` is executable documentation. It cannot rot,
  because `bend PROOF.bend` is in the loop.

## Notes from writing it

Bend is new and the ergonomics are real friction. Things that cost time:

- Arithmetic operators only exist *inside* a type annotation: `(a + b : Nat)`,
  never a bare `a + b`.
- A `match` can only inspect a parameter or a pattern binder, never a computed
  value or a local `let`. Workaround: pass the Bool/vector as an argument to a
  helper and match on the parameter.
- `match b f:` on two values does **not** reduce in a proof; `match b:` does.
- A destructuring let (`(+xl, +xr) = t`) *does* fire on a variable, and is the
  only way to see through the leaves — which is why `zip_mass` opens by pulling
  the two leaves apart by hand.
- `def`s must be declared above their uses; types may be declared in any order.
- Base has `Nat.add`/`double`/`sub` but no `succ`, no `is_zero`, no `Nat`
  equality. It does have `Equal.sym`, which every induction here needs: a
  rewrite only ever replaces a right-hand side, and the goals run the other way.
