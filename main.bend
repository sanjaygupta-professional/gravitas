# gravitas -- a verified parallel n-body core.
#
# Split of responsibilities, and the point of the whole project:
#
#   The *shape* of the computation is exact Nat arithmetic, and LAWS.bend
#   states what that shape must preserve. PROOF.bend proves it. So the
#   compiler rules out a whole class of parallel-reduction bugs: dropped
#   bodies, double-counted bodies, fusion that invents mass, and a field
#   reduction that does not split.
#
#   The *numerics* are F32, and Bend is axiomatic about floating point, so
#   nothing there is provable. It is guarded instead by a runtime invariant
#   check that reads the proved laws back as an assertion (see check.bend).
#
# Parallelism is the fork-join `a b = f(x) g(y)`. It is not annotated as
# parallel anywhere else: no threads, no locks, no atomics.

import Base

# ---------------------------------------------------------------------------
# Data
# ---------------------------------------------------------------------------

# A body carries an *exact* Nat mass (so mass conservation is provable) and
# F32 kinematics (so gravity is fast).
type Body is Data:
  Body{m: Nat, x: F32, y: F32, vx: F32, vy: F32}

# A 2D vector, carried as a record so it can be matched and rebuilt.
type V is Data:
  V{x: F32, y: F32}

# 2^d bodies, held as a perfectly balanced binary tree. The tree *is* the
# parallel schedule: every fork is a node, every leaf is one body's work.
def Sys(d: Nat) -> Data:
  match d:
    case 0n:
      Body
    case 1n+p:
      Sigma<&2, &2, Sys(p), _ => Sys(p)>

# ---------------------------------------------------------------------------
# Accessors (Bend matches on parameters, never on computed values, so a
# record has to be taken apart inside a def that takes it as a parameter)
# ---------------------------------------------------------------------------

def mass_of(b: Body) -> Nat:
  match b:
    case Body{+m, x, y, vx, vy}:
      m

def pos_x(b: Body) -> F32:
  match b:
    case Body{m, x, y, vx, vy}:
      x

def pos_y(b: Body) -> F32:
  match b:
    case Body{m, x, y, vx, vy}:
      y

# ---------------------------------------------------------------------------
# Exact reductions -- the part LAWS.bend talks about
# ---------------------------------------------------------------------------

# pow2(d) = 2^d, by parallel doubling.
def pow2(+d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      a b = pow2(p) pow2(p)
      Nat.add(a, b)

# How many bodies: 2^d, counted by a parallel reduction over the tree.
def count(d: Nat, t: Sys(d)) -> Nat:
  match d:
    case 0n:
      1n
    case 1n++p:
      (x, y) = t
      a b = count(p, x) count(p, y)
      Nat.add(a, b)

# Total mass: the parallel reduction the conservation laws are about.
def mass(d: Nat, t: Sys(d)) -> Nat:
  match d:
    case 0n:
      # A destructuring let (not a match): this is the one form the proof
      # checker can fire on a value held in a variable, which is what makes
      # the conservation laws in LAWS.bend provable at all.
      Body{+m, x, y, vx, vy} = t
      m
    case 1n++p:
      (x, y) = t
      a b = mass(p, x) mass(p, y)
      Nat.add(a, b)

# ---------------------------------------------------------------------------
# Vector helpers
# ---------------------------------------------------------------------------

def vadd(a: V, b: V) -> V:
  match a b:
    case V{ax, ay} V{bx, by}:
      V{(ax + bx : F32), (ay + by : F32)}

# ---------------------------------------------------------------------------
# The field: total gravitational pull on a probe, reduced over the tree
# ---------------------------------------------------------------------------

# one_body(m, bx, by, px, py, soft) is the pull of a single body.
def one_body(+m: Nat, bx: F32, by: F32, px: F32, py: F32, soft: F32) -> V:
  +dx = (bx - px : F32)
  +dy = (by - py : F32)
  +r2 = ((dx * dx : F32) + (dy * dy : F32) + soft : F32)
  inv = (1.0 / r2 : F32)
  k = (inv / r2 : F32)
  +gm = (k * F32.from_nat(m) : F32)
  V{(gm * dx : F32), (gm * dy : F32)}

# field(d, t, px, py, soft) is the sum, over every body in t, of G*m*r/r^2.
# It is a pure parallel reduction: the two halves are independent, so this
# forks. LAWS.bend proves the fork is *correct*, not merely fast.
def field(d: Nat, +t: Sys(d), +px: F32, +py: F32, +soft: F32) -> V:
  match d:
    case 0n:
      one_body(mass_of(t), pos_x(t), pos_y(t), px, py, soft)
    case 1n++p:
      (x, y) = t
      a b = field(p, x, px, py, soft) field(p, y, px, py, soft)
      vadd(a, b)

# left(d, t) and right(d, t) are the two halves of a system. They exist so
# that LAWS.bend can *name* the two sub-reductions of a fork and state that
# the fork equals their combination.
def left(d: Nat, t: Sys(1n+d)) -> Sys(d):
  match t:
    case Tuple{x, y}:
      x

def right(d: Nat, t: Sys(1n+d)) -> Sys(d):
  match t:
    case Tuple{x, y}:
      y

# ---------------------------------------------------------------------------
# Centre of mass: an F32 reduction with the same shape as the Nat ones
# ---------------------------------------------------------------------------

# Mom is the first moment of a set of bodies: total mass and the two
# mass-weighted coordinate sums. comsum is the parallel reduction, and the
# simulation reads it back as a numerical check on the fork.
type Mom is Data:
  Mom{t: F32, mx: F32, my: F32}

def mom_of(b: Body) -> Mom:
  match b:
    case Body{+m, x, y, vx, vy}:
      +f = F32.from_nat(m)
      Mom{f, (f * x : F32), (f * y : F32)}

def mom_add(a: Mom, b: Mom) -> Mom:
  match a b:
    case Mom{at, ax, ay} Mom{bt, bx, by}:
      Mom{(at + bt : F32), (ax + bx : F32), (ay + by : F32)}

def comsum(d: Nat, +t: Sys(d)) -> Mom:
  match d:
    case 0n:
      mom_of(t)
    case 1n++p:
      (x, y) = t
      a b = comsum(p, x) comsum(p, y)
      mom_add(a, b)

# thin(s) reports a system carrying (almost) no mass.
def thin(s: Mom) -> Bool:
  match s:
    case Mom{t, mx, my}:
      F32.is_lt(t, 0.0001)

# divide(s, thin) turns a first moment into a position. The flag is passed
# as a parameter so the match inspects parameters, not computed values.
def divide(s: Mom, thin: Bool) -> V:
  match s thin:
    case Mom{t, mx, my} True{}:
      V{0.0, 0.0}
    case Mom{+t, mx, my} False{}:
      V{(mx / t : F32), (my / t : F32)}

# com2(d, t) divides the first moment by the total mass. Guarded against a
# near-zero total so the sim cannot produce a NaN.
def com2(+d: Nat, +t: Sys(d)) -> V:
  divide(comsum(d, t), thin(comsum(d, t)))

# com(d, t) is the centre of mass.
def com(+d: Nat, +t: Sys(d)) -> V:
  com2(d, t)


def vx_of(f: V) -> F32:
  match f:
    case V{x, y}:
      x

def vy_of(f: V) -> F32:
  match f:
    case V{x, y}:
      y

# kick(b, f, dt) is body b advanced by dt under the pull f. Only b is
# matched; f is read through vx_of/vy_of, so the new Body (and its mass) is
# visible even when f is an unevaluated field sum. That is what lets
# LAWS.accels_mass see that a step leaves every mass alone.
def kick(b: Body, +f: V, +dt: F32) -> Body:
  match b:
    case Body{m, x, y, +vx, +vy}:
      fx = vx_of(f)
      fy = vy_of(f)
      Body{m,
           (x + ((dt * vx : F32)) : F32),
           (y + ((dt * vy : F32)) : F32),
           (vx + ((dt * fx : F32)) : F32),
           (vy + ((dt * fy : F32)) : F32)}

# accels(D, d, root, cur, dt, soft) returns cur with every body advanced by
# dt under the pull of the *whole* system root. cur is the subtree being
# rewritten and shrinks; root is the full 2^D system, passed unchanged all
# the way down and kept reusable so every leaf sees all N bodies. D never
# changes and d shrinks first, so the termination checker is satisfied and
# every leaf does a full O(N) sweep. The two halves are independent, so the
# recursion forks and no thread or lock is ever named.
def accels(+D: Nat, d: Nat, +root: Sys(D), +cur: Sys(d),
           +dt: F32, +soft: F32) -> Sys(d):
  match d:
    case 0n:
      f = field(D, root, pos_x(cur), pos_y(cur), soft)
      kick(cur, f, dt)
    case 1n++p:
      (cl, cr) = cur
      a b = accels(D, p, root, cl, dt, soft) accels(D, p, root, cr, dt, soft)
      (a, b)

# step advances every body in parallel, leaving mass and count untouched.
def step(+d: Nat, +src: Sys(d), dt: F32, soft: F32) -> Sys(d):
  accels(d, d, src, src, dt, soft)

# ---------------------------------------------------------------------------
# Fusion: zip two systems into one, pairing bodies and adding their masses
# ---------------------------------------------------------------------------

# fuse(m1, x1, y1, vx1, vy1, m2, x2, y2, vx2, vy2) merges two bodies into
# one: mass summed exactly, kinematics at the centre of mass.
def fuse(+m1: Nat, x1: F32, y1: F32, vx1: F32, vy1: F32,
         +m2: Nat, x2: F32, y2: F32, vx2: F32, vy2: F32) -> Body:
  +mt = Nat.add(m1, m2)
  +mt_f = F32.from_nat(mt)
  +f1 = F32.from_nat(m1)
  +f2 = F32.from_nat(m2)
  Body{mt,
       (((x1 * f1 : F32) + ((x2 * f2 : F32))) / mt_f : F32),
       (((y1 * f1 : F32) + ((y2 * f2 : F32))) / mt_f : F32),
       (((vx1 * f1 : F32) + ((vx2 * f2 : F32))) / mt_f : F32),
       (((vy1 * f1 : F32) + ((vy2 * f2 : F32))) / mt_f : F32)}

# zip(p, x, y) has the shape of x, but every leaf holds the fusion of the
# matching leaves of x and y. This is the operation the "fusion conserves
# mass" laws are about: combining two systems must not create or destroy.
def zip(p: Nat, x: Sys(p), y: Sys(p)) -> Sys(p):
  match p:
    case 0n:
      # destructuring lets again, so the fusion law can see the leaf
      Body{+m1, x1, y1, vx1, vy1} = x
      Body{+m2, x2, y2, vx2, vy2} = y
      fuse(m1, x1, y1, vx1, vy1, m2, x2, y2, vx2, vy2)
    case 1n++p:
      (xl, xr) = x
      (yl, yr) = y
      a b = zip(p, xl, yl) zip(p, xr, yr)
      (a, b)
