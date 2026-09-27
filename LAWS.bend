# gravitas -- LAWS.bend
#
# This file is the specification. It states, in Bend's own type system, every
# rule the parallel core must obey. A human writes this file and does not edit
# it again. PROOF.bend must discharge each law; `bend PROOF.bend` is the gate
# that refuses to pass while any of them is open or false.
#
# Every claim here is about exact arithmetic over the *shape* of the
# computation, which is why it is provable at all. The F32 gravity on top is
# not provable (Bend is axiomatic about floating point) and is not claimed.

import Base
import ./main.bend as G

# ---------------------------------------------------------------------------
# 1. The parallel count reduction agrees with the closed form
# ---------------------------------------------------------------------------

# LAW: counting a system of depth d gives exactly 2^d bodies.
#
# `count` is a fork-join reduction over the tree -- the kind of code that
# silently loses a subtree when someone refactors. This says it cannot.
law count_pow2:
  for +d: Nat
  for +t: G.Sys(d)
  {G.count(d, t) == G.pow2(d) : Nat}

# ---------------------------------------------------------------------------
# 2. The parallel step never adds or drops a body
# ---------------------------------------------------------------------------

# LAW: rewriting a body never changes how many bodies there are.
#
# Stated in full generality, because every body is updated under the pull of
# the *whole* system: the root the update reads and the leaf it rewrites are
# different values, and the proof has to keep them apart.
law accels_count:
  for +D: Nat
  for +d: Nat
  for +t: G.Sys(D)
  for +c: G.Sys(d)
  for +dt: F32
  for +soft: F32
  {G.count(d, G.accels(D, d, t, c, dt, soft)) == G.count(d, c) : Nat}

# LAW: a simulation step never changes how many bodies there are.
#
# This is the headline invariant of the step, and the one a refactor of the
# integrator is most likely to break.
law step_count:
  for +d: Nat
  for +t: G.Sys(d)
  for +dt: F32
  for +soft: F32
  {G.count(d, G.step(d, t, dt, soft)) == G.count(d, t) : Nat}

# LAW: rewriting a body never changes the mass of the subtree it lives in.
#
# The mass twin of accels_count, stated with the same root/leaf split.
law accels_mass:
  for +D: Nat
  for +d: Nat
  for +t: G.Sys(D)
  for +c: G.Sys(d)
  for +dt: F32
  for +soft: F32
  {G.mass(d, G.accels(D, d, t, c, dt, soft)) == G.mass(d, c) : Nat}

# LAW: a simulation step never changes the total mass.
#
# sim.bend prints this law's name next to the mass it reads back after the
# run, so the claim on screen is backed by a proof, not only by the runtime
# check.
law step_mass:
  for +d: Nat
  for +t: G.Sys(d)
  for +dt: F32
  for +soft: F32
  {G.mass(d, G.step(d, t, dt, soft)) == G.mass(d, t) : Nat}

# ---------------------------------------------------------------------------
# 3. The field reduction splits the way the tree says it does
# ---------------------------------------------------------------------------

# LAW: the pull on a probe from a two-subtree system is the sum of the pulls
# from each subtree.
#
# This is the linearity of the fork. It says parallelising the force
# reduction changed nothing about its answer, not merely that it ran faster.
# The F32 arithmetic inside is opaque, but its *shape* is fixed, which is
# what a wrong fork would change.
law field_split:
  for +d: Nat
  for +a: G.Sys(d)
  for +b: G.Sys(d)
  for +px: F32
  for +py: F32
  for +soft: F32
  {G.field(1n+d, (a, b), px, py, soft)
   == G.vadd(G.field(d, a, px, py, soft), G.field(d, b, px, py, soft))
   : G.V}

# LAW: the same for the centre-of-mass reduction, which the simulation reads
# back as a numerical check on the fork.
law comsum_split:
  for +d: Nat
  for +a: G.Sys(d)
  for +b: G.Sys(d)
  {G.comsum(1n+d, (a, b)) == G.mom_add(G.comsum(d, a), G.comsum(d, b))
   : G.Mom}

# ---------------------------------------------------------------------------
# 4. Fusing two systems
# ---------------------------------------------------------------------------

# LAW: fusing two systems pairwise yields a system of the same size as either
# input -- combining two runs never grows or shrinks the result.
law zip_count:
  for +d: Nat
  for +x: G.Sys(d)
  for +y: G.Sys(d)
  {G.count(d, G.zip(d, x, y)) == G.count(d, x) : Nat}

# LAW: fusing two systems gives a system carrying exactly their combined
# mass -- neither invented nor lost. This is the law that makes merging two
# N-body runs safe, and it is the one that needs the arithmetic lemmas of
# Part 1: a parallel reduction groups the same four partial sums differently
# at every fork, and this law is what makes those groupings interchangeable.
law zip_mass:
  for +d: Nat
  for +x: G.Sys(d)
  for +y: G.Sys(d)
  {G.mass(d, G.zip(d, x, y)) == Nat.add(G.mass(d, x), G.mass(d, y)) : Nat}

# LAW: fusion does not depend on the order of the operands.
law zip_swap:
  for +d: Nat
  for +x: G.Sys(d)
  for +y: G.Sys(d)
  {G.mass(d, G.zip(d, x, y)) == G.mass(d, G.zip(d, y, x)) : Nat}
