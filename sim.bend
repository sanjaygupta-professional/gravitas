# gravitas -- the driver: build a system, run it, and read the proved laws
# back as a runtime assertion.
#
#   bend sim.bend                 # interpret (slow, no parallelism)
#   bend sim.bend -o sim && ./sim  # native: real fork-join across 16 cores
#   ./sim --threads 1             # the same run, single-threaded, for scaling

import Base
import ./main.bend as M

# ---------------------------------------------------------------------------
# A deterministic pseudo-random source, so a run is reproducible
# ---------------------------------------------------------------------------

# Numerical Recipes' LCG. Full period, so a seed reproduces a whole system.
def next(s: U32) -> U32:
  ((s * 1664525 : U32) + 1013904223 : U32)

# rand01(s) is uniform in [0, 1).
def rand01(s: U32) -> F32:
  (U32.to_f32(U32.shrn(s, 8n)) / 16777216.0 : F32)

# signed(s) is uniform in [-1, 1).
def signed(s: U32) -> F32:
  ((rand01(s) - 0.5 : F32) * 2.0 : F32)

# Base has Nat.add/double/sub but no succ or is_zero; we need both.
def succ(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      (1n + (1n + p) : Nat)

# same_nat(a, b) is Nat equality, which Base has no def for.
def same_nat2(diff: Nat) -> Bool:
  match diff:
    case 0n:
      True{}
    case 1n+p:
      False{}

def sub_nat(a: Nat, b: Nat) -> Nat:
  Nat.sub(a, b)

def same_nat(a: Nat, b: Nat) -> Bool:
  same_nat2(sub_nat(a, b))

def is_zero(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

# central(s, c) is the heavy mass at the origin that holds the cloud
# together; ring(s) is one light body of the cold cloud.
def central(c: Bool) -> M.Body:
  match c:
    case True{}:
      M.Body{1000n, 0.0, 0.0, 0.0, 0.0}
    case False{}:
      M.Body{0n, 0.0, 0.0, 0.0, 0.0}

def ring(s1: U32, s2: U32, s3: U32, +s4: U32) -> M.Body:
  m = U32.to_nat(U32.add(U32.and(s4, 15), 1))
  M.Body{m,
         (signed(s1) * 4.0 : F32),
         (signed(s2) * 4.0 : F32),
         (signed(s3) * 0.3 : F32),
         (signed(s4) * 0.3 : F32)}

# body_of(c, s): c says whether this is the heavy central mass.
def body_of(c: Bool, s: U32) -> M.Body:
  match c:
    case True{}:
      central(c)
    case False{}:
      +s1 = next(s)
      +s2 = next(s1)
      +s3 = next(s2)
      +s4 = next(s3)
      ring(s1, s2, s3, s4)

# body_at(i, s): body number i. Body 0 is the heavy mass; the rest are a
# cold cloud of light bodies.
def body_at(+i: Nat, s: U32) -> M.Body:
  body_of(is_zero(i), s)

# spawn(d, i, s) is 2^d bodies, indices 0 .. 2^d - 1, from seed s. The two
# halves read disjoint points of the same LCG stream, so each body is
# determined by its index alone and the spawn is a clean fork.
def spawn(d: Nat, +i: Nat, +s: U32) -> M.Sys(d):
  match d:
    case 0n:
      body_at(i, s)
    case 1n++p:
      a b = spawn(p, Nat.double(i), next(s)) spawn(p, succ(Nat.double(i)), next(next(s)))
      (a, b)

# ---------------------------------------------------------------------------
# Running the simulation
# ---------------------------------------------------------------------------

# run(d, t, fuel, dt, soft) takes `fuel` steps. A step needs a fuel argument
# to terminate in Bend's world (recursion must be provably finite), and this
# is exactly the "loop bounded by the outside world" case the guide names.
def run(fuel: Nat, +d: Nat, t: M.Sys(d), +dt: F32, +soft: F32) -> M.Sys(d):
  match fuel:
    case 0n:
      t
    case 1n+f:
      run(f, d, M.step(d, t, dt, soft), dt, soft)

# ---------------------------------------------------------------------------
# The runtime check: the proved laws, read back as an assertion
# ---------------------------------------------------------------------------

# Both of these are *consequences* of laws in LAWS.bend. The compiler has
# already ruled out a violation; this makes a violation loud anyway, which
# also covers the F32 half of the model that no proof reaches.
def check_count(before: Nat, after: Nat, same: Bool) -> IO(Unit):
  match same:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 3, "LAW BROKEN: step changed the body count: "
             ++ Nat.show(before) ++ " -> " ++ Nat.show(after))

def check_mass(before: Nat, after: Nat, same: Bool) -> IO(Unit):
  match same:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 4, "LAW BROKEN: step changed the total mass: "
             ++ Nat.show(before) ++ " -> " ++ Nat.show(after))

# fmt(m: Mom) prints the total mass carried by a first moment.
def fmt(s: M.Mom) -> String:
  match s:
    case M.Mom{t, mx, my}:
      "m=" ++ F32.show(t)

def com_str(v: M.V) -> String:
  match v:
    case M.V{x, y}:
      "(" ++ F32.show(x) ++ ", " ++ F32.show(y) ++ ")"

# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def steps_for(d: Nat, t: M.Sys(d), f: Nat, dt: F32, soft: F32) -> IO(M.Sys(d)):
  do IO<M.Sys(d)>:
    return run(f, d, t, dt, soft)

def main() -> IO(Unit):
  do IO<Unit>:
    DEPTH: Nat = 10n
    +STEPS: Nat = 100n
    DT: F32 = 0.004
    SOFT: F32 = 0.05
    th : U32 <- IO.thread_count()
    IO.print("gravitas -- 2^" ++ Nat.show(DEPTH) ++ " bodies, "
             ++ Nat.show(STEPS) ++ " steps, on " ++ U32.show(th) ++ " threads")
    IO.print("")

    +t0 : M.Sys(10n) = spawn(10n, 0n, 12345)
    +n0 : Nat = M.count(10n, t0)
    +w0 : Nat = M.mass(10n, t0)
    +c0 : M.V = M.com(10n, t0)
    IO.print("bodies   = " ++ Nat.show(n0))
    IO.print("mass     = " ++ Nat.show(w0))
    IO.print("com      = " ++ com_str(c0))

    t_start : Nat <- IO.now()
    +t1 : M.Sys(10n) <- steps_for(10n, t0, STEPS, DT, SOFT)
    t_end : Nat <- IO.now()
    +n1 : Nat = M.count(10n, t1)
    +w1 : Nat = M.mass(10n, t1)
    +c1 : M.V = M.com(10n, t1)

    check_count(n0, n1, same_nat(n0, n1))
    check_mass(w0, w1, same_nat(w0, w1))

    IO.print("")
    IO.print("after " ++ Nat.show(STEPS) ++ " steps:")
    IO.print("bodies   = " ++ Nat.show(n1) ++ "   (unchanged: law step_count)")
    IO.print("mass     = " ++ Nat.show(w1) ++ "   (unchanged: law step_mass)")
    IO.print("com      = " ++ com_str(c1))
    IO.print("elapsed  = " ++ Nat.show(Nat.sub(t_end, t_start)) ++ " ms for "
             ++ Nat.show(STEPS) ++ " steps of O(N^2) gravity")
    IO.print("")
    IO.print("All runtime invariants held.")
