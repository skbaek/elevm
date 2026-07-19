import Elevm.Basic

/-!
Step-1 U256 microbenchmark instrument.

Compile and run with `scripts/run-bench-u256.sh <label>`.  That wrapper uses
standalone `lean -c` followed by `leanc -O2`; this benchmark is not a Lake
target.  Timing a pure value that is only demanded after the second clock read
can produce a bogus near-zero result, so every result is forced through the
`@[noinline]` IO boundary below before the finish time is sampled.
-/

def sample : B256 :=
  (0x123456789abcdef0 : B64).toB256 <<< 128 ||| 0xfedcba9876543211

def drive (n : Nat) (seed : B256) (f : Nat → B256 → B256) : B256 :=
  go n seed where
  go : Nat → B256 → B256
    | 0, x => x
    | n + 1, x => go n (f n x)

@[noinline] def forceB256 (x : B256) : IO B256 := pure x

def bench (label : String) (iterations : Nat) (nonce : Nat)
    (f : Nat → B256 → B256) : IO Unit := do
  let seed := sample + nonce.toB256
  let start ← IO.monoNanosNow
  let sink ← forceB256 (drive iterations seed f)
  let finish ← IO.monoNanosNow
  IO.println s!"{label}\t{(finish - start) / iterations} ns/op\titerations={iterations}\tsink={sink.toHex}"

def main : IO Unit := do
  let nonce ← IO.monoNanosNow
  bench "add" 1000000 nonce (fun i x => x + sample + i.toB256)
  bench "and" 1000000 nonce (fun i x => (x &&& sample) ^^^ i.toB256)
  bench "lt" 1000000 nonce (fun i x => if x < sample then x + i.toB256 else x - i.toB256)
  bench "mul" 200000 nonce (fun i x => x * sample + i.toB256)
  bench "div-2^128" 20000 nonce (fun i x => x / ((1 : Nat).toB256 <<< 128) + sample + i.toB256)
  bench "div-3" 20000 nonce (fun i x => x / 3 + sample + i.toB256)
  bench "exp" 100 nonce (fun i x => B256.bexp x (i + 1).toB256)
