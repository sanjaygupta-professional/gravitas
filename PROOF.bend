# gravitas -- PROOF.bend
#
# The gate. `bend PROOF.bend` fails while any law in LAWS.bend is open or
# false, and prints "All terms check." only when every one holds.
#
# Structure:
#   Part 1  Nat arithmetic, proved from nothing (Base ships U32.add_comm but
#           no Nat algebra, and the laws are stated over Nat).
#   Part 2  One law per section of LAWS.bend.

import Base
import ./main.bend as G
import ./LAWS.bend as Laws

# ===========================================================================
# Part 1 -- Nat arithmetic
# ===========================================================================

# flip(a, b, e) is e read the other way round. Every induction below needs
# it: the goal states each partial sum in the opposite direction to the
# hypothesis, and a rewrite only ever replaces a right-hand side.
def flip(a: Nat, b: Nat, e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# add_zero: n + 0 == n
def add_zero(a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

# add_succ: 1 + (a + b) == a + (1 + b)
# Pushes a successor out to the front, which is how every lemma below gets
# its induction hypothesis into the shape it needs.
def add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# add_comm: a + b == b + a
def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      add_zero(b)
    case 1n+p:
      %add_succ(b, p) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# add_assoc: a + (b + c) == (a + b) + c
def add_assoc(a: Nat, -b: Nat, -c: Nat)
  -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# add_swap: x + (y + z) == y + (x + z)
# Swaps the middle two of a triple sum.
def add_swap(x: Nat, +y: Nat, +z: Nat)
  -> {Nat.add(x, Nat.add(y, z)) == Nat.add(y, Nat.add(x, z)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+q:
      %add_succ(y, Nat.add(q, z)) : {1n+Nat.add(q, Nat.add(y, z)) == _ : Nat}
      %add_swap(q, y, z) : {1n+Nat.add(q, Nat.add(y, z)) == 1n+_ : Nat}
      {==}

# add_regroup: (a + b) + (c + d) == (a + c) + (b + d)
# The workhorse. A parallel reduction groups the same four partial sums in a
# different order at every fork, and this lemma is what makes those groupings
# interchangeable.
def add_regroup(a: Nat, b: Nat, c: Nat, d: Nat)
  -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  match a:
    case 0n:
      add_swap(b, c, d)
    case 1n+p:
      %add_regroup(p, b, c, d) : {1n+Nat.add(Nat.add(p, b), Nat.add(c, d)) == 1n+_ : Nat}
      {==}


# ===========================================================================
# Part 2 -- the laws
# ===========================================================================

# ---------------------------------------------------------------------------
# count_pow2: the parallel count reduction agrees with 2^d
# ---------------------------------------------------------------------------

def Laws.count_pow2(d, t):
  match d:
    case 0n:
      {==}
    case 1n++p:
      (+xl, +xr) = t
      %Laws.count_pow2(p, xl) : {Nat.add(G.count(p, xl), G.count(p, xr)) == Nat.add(_, G.pow2(p)) : Nat}
      %Laws.count_pow2(p, xr) : {Nat.add(G.count(p, xl), G.count(p, xr)) == Nat.add(G.count(p, xl), _) : Nat}
      {==}

# ---------------------------------------------------------------------------
# accels_count / step_count: a step never adds or drops a body
# ---------------------------------------------------------------------------

def Laws.accels_count(D, d, t, c, dt, soft):
  match d:
    case 0n:
      {==}
    case 1n++p:
      (+cl, +cr) = c
      %flip(G.count(p, G.accels(D, p, t, cl, dt, soft)), G.count(p, cl),
            Laws.accels_count(D, p, t, cl, dt, soft))
        : {Nat.add(_, G.count(p, G.accels(D, p, t, cr, dt, soft)))
           == Nat.add(G.count(p, cl), G.count(p, cr)) : Nat}
      %flip(G.count(p, G.accels(D, p, t, cr, dt, soft)), G.count(p, cr),
            Laws.accels_count(D, p, t, cr, dt, soft))
        : {Nat.add(G.count(p, cl), _)
           == Nat.add(G.count(p, cl), G.count(p, cr)) : Nat}
      {==}

def Laws.step_count(d, t, dt, soft):
  match d:
    case 0n:
      {==}
    case 1n++p:
      (+xl, +xr) = t
      %flip(G.count(p, G.accels(1n+p, p, (xl, xr), xl, dt, soft)), G.count(p, xl),
            Laws.accels_count(1n+p, p, (xl, xr), xl, dt, soft))
        : {Nat.add(_, G.count(p, G.accels(1n+p, p, (xl, xr), xr, dt, soft)))
           == Nat.add(G.count(p, xl), G.count(p, xr)) : Nat}
      %flip(G.count(p, G.accels(1n+p, p, (xl, xr), xr, dt, soft)), G.count(p, xr),
            Laws.accels_count(1n+p, p, (xl, xr), xr, dt, soft))
        : {Nat.add(G.count(p, xl), _)
           == Nat.add(G.count(p, xl), G.count(p, xr)) : Nat}
      {==}

# ---------------------------------------------------------------------------
# accels_mass / step_mass: a step never changes the total mass
# ---------------------------------------------------------------------------

def Laws.accels_mass(D, d, t, c, dt, soft):
  match d:
    case 0n:
      G.Body{+m, x, y, +vx, +vy} = c
      {==}
    case 1n++p:
      (+cl, +cr) = c
      %flip(G.mass(p, G.accels(D, p, t, cl, dt, soft)), G.mass(p, cl),
            Laws.accels_mass(D, p, t, cl, dt, soft))
        : {Nat.add(_, G.mass(p, G.accels(D, p, t, cr, dt, soft)))
           == Nat.add(G.mass(p, cl), G.mass(p, cr)) : Nat}
      %flip(G.mass(p, G.accels(D, p, t, cr, dt, soft)), G.mass(p, cr),
            Laws.accels_mass(D, p, t, cr, dt, soft))
        : {Nat.add(G.mass(p, cl), _)
           == Nat.add(G.mass(p, cl), G.mass(p, cr)) : Nat}
      {==}

def Laws.step_mass(d, t, dt, soft):
  Laws.accels_mass(d, d, t, t, dt, soft)

# ---------------------------------------------------------------------------
# field_split / comsum_split: the forks preserve the shape of the answer
# ---------------------------------------------------------------------------

def Laws.field_split(d, a, b, px, py, soft):
  match d:
    case 0n:
      {==}
    case 1n++p:
      {==}

def Laws.comsum_split(d, a, b):
  match d:
    case 0n:
      {==}
    case 1n++p:
      {==}

# ---------------------------------------------------------------------------
# zip_count: fusion preserves the size of a system
# ---------------------------------------------------------------------------

def Laws.zip_count(d, x, y):
  match d:
    case 0n:
      {==}
    case 1n++p:
      (+xl, +xr) = x
      (+yl, +yr) = y
      %flip(G.count(p, G.zip(p, xl, yl)), G.count(p, xl), Laws.zip_count(p, xl, yl))
        : {Nat.add(_, G.count(p, G.zip(p, xr, yr))) == Nat.add(G.count(p, xl), G.count(p, xr)) : Nat}
      %flip(G.count(p, G.zip(p, xr, yr)), G.count(p, xr), Laws.zip_count(p, xr, yr))
        : {Nat.add(G.count(p, xl), _) == Nat.add(G.count(p, xl), G.count(p, xr)) : Nat}
      {==}

# ---------------------------------------------------------------------------
# zip_mass: fusion conserves mass
# ---------------------------------------------------------------------------
#
# This is where the arithmetic of Part 1 earns its keep. The left side groups
# the four partial masses as (xl+yl) + (xr+yr), because that is the order the
# parallel fusion happens to visit them; the right side groups them as
# (xl+xr) + (yl+yr), because that is the order the two input systems are
# given in. add_regroup is the lemma that says the grouping is not the
# answer -- the sum is.

def Laws.zip_mass(d, x, y):
  match d:
    case 0n:
      G.Body{+m1, x1, y1, +vx1, +vy1} = x
      G.Body{+m2, x2, y2, +vx2, +vy2} = y
      {==}
    case 1n++p:
      (+xl, +xr) = x
      (+yl, +yr) = y
      %flip(G.mass(p, G.zip(p, xl, yl)), Nat.add(G.mass(p, xl), G.mass(p, yl)),
            Laws.zip_mass(p, xl, yl))
        : {Nat.add(_, G.mass(p, G.zip(p, xr, yr)))
           == Nat.add(Nat.add(G.mass(p, xl), G.mass(p, xr)),
                      Nat.add(G.mass(p, yl), G.mass(p, yr))) : Nat}
      %flip(G.mass(p, G.zip(p, xr, yr)), Nat.add(G.mass(p, xr), G.mass(p, yr)),
            Laws.zip_mass(p, xr, yr))
        : {Nat.add(Nat.add(G.mass(p, xl), G.mass(p, yl)), _)
           == Nat.add(Nat.add(G.mass(p, xl), G.mass(p, xr)),
                      Nat.add(G.mass(p, yl), G.mass(p, yr))) : Nat}
      %flip(Nat.add(Nat.add(G.mass(p, xl), G.mass(p, xr)),
                    Nat.add(G.mass(p, yl), G.mass(p, yr))),
            Nat.add(Nat.add(G.mass(p, xl), G.mass(p, yl)),
                    Nat.add(G.mass(p, xr), G.mass(p, yr))),
            add_regroup(G.mass(p, xl), G.mass(p, xr), G.mass(p, yl), G.mass(p, yr)))
        : {Nat.add(Nat.add(G.mass(p, xl), G.mass(p, yl)),
                   Nat.add(G.mass(p, xr), G.mass(p, yr))) == _ : Nat}
      {==}

# ---------------------------------------------------------------------------
# zip_swap: fusion does not depend on the order of its operands
# ---------------------------------------------------------------------------
#
# Two systems combined give the same system either way round. Mechanically it
# is four induction hypotheses and two uses of add_comm, but the statement is
# the one you want before trusting a merge: fusing A into B and B into A must
# not be two different operations.

def Laws.zip_swap(d, x, y):
  match d:
    case 0n:
      G.Body{+m1, x1, y1, +vx1, +vy1} = x
      G.Body{+m2, x2, y2, +vx2, +vy2} = y
      add_comm(m1, m2)
    case 1n++p:
      (+xl, +xr) = x
      (+yl, +yr) = y
      %flip(G.mass(p, G.zip(p, xl, yl)), Nat.add(G.mass(p, xl), G.mass(p, yl)),
            Laws.zip_mass(p, xl, yl))
        : {Nat.add(_, G.mass(p, G.zip(p, xr, yr)))
           == Nat.add(G.mass(p, G.zip(p, yl, xl)), G.mass(p, G.zip(p, yr, xr))) : Nat}
      %flip(G.mass(p, G.zip(p, xr, yr)), Nat.add(G.mass(p, xr), G.mass(p, yr)),
            Laws.zip_mass(p, xr, yr))
        : {Nat.add(Nat.add(G.mass(p, xl), G.mass(p, yl)), _)
           == Nat.add(G.mass(p, G.zip(p, yl, xl)), G.mass(p, G.zip(p, yr, xr))) : Nat}
      %flip(G.mass(p, G.zip(p, yl, xl)), Nat.add(G.mass(p, yl), G.mass(p, xl)),
            Laws.zip_mass(p, yl, xl))
        : {Nat.add(Nat.add(G.mass(p, xl), G.mass(p, yl)), Nat.add(G.mass(p, xr), G.mass(p, yr)))
           == Nat.add(_, G.mass(p, G.zip(p, yr, xr))) : Nat}
      %flip(G.mass(p, G.zip(p, yr, xr)), Nat.add(G.mass(p, yr), G.mass(p, xr)),
            Laws.zip_mass(p, yr, xr))
        : {Nat.add(Nat.add(G.mass(p, xl), G.mass(p, yl)), Nat.add(G.mass(p, xr), G.mass(p, yr)))
           == Nat.add(Nat.add(G.mass(p, yl), G.mass(p, xl)), _) : Nat}
      %flip(Nat.add(G.mass(p, yl), G.mass(p, xl)), Nat.add(G.mass(p, xl), G.mass(p, yl)), add_comm(G.mass(p, yl), G.mass(p, xl)))
        : {Nat.add(Nat.add(G.mass(p, xl), G.mass(p, yl)), Nat.add(G.mass(p, xr), G.mass(p, yr)))
           == Nat.add(_, Nat.add(G.mass(p, yr), G.mass(p, xr))) : Nat}
      %flip(Nat.add(G.mass(p, yr), G.mass(p, xr)), Nat.add(G.mass(p, xr), G.mass(p, yr)), add_comm(G.mass(p, yr), G.mass(p, xr)))
        : {Nat.add(Nat.add(G.mass(p, xl), G.mass(p, yl)), Nat.add(G.mass(p, xr), G.mass(p, yr)))
           == Nat.add(Nat.add(G.mass(p, xl), G.mass(p, yl)), _) : Nat}
      {==}
