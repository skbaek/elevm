-- BLS12-381 field, curve, and EIP-2537 byte codecs.
--
-- Ported from py_ecc's non-optimized `bls12_381_curve` module (affine
-- coordinates; the generic curve law is already provided by EC.lean) and
-- EELS's `bls12_381/__init__.py` (byte-level codecs; gas semantics live in
-- Execution.lean). Mirrors the BN254 conventions already in EC.lean /
-- Execution.lean (BNF/BNP/B8L.toExStrBNP) rather than generalizing them.

import Elevm.EC

-- py_ecc.fields.field_properties.field_properties["bls12_381"]["field_modulus"];
-- equal to the pre-existing (unused) `bls12Prime` constant in EC.lean.
abbrev blsPrime : Nat := bls12Prime

-- py_ecc.bls12_381.bls12_381_curve.curve_order
abbrev blsCurveOrder : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

abbrev BLSF : Type := FinField blsPrime

-- Curve is y^2 = x^3 + 4 (py_ecc.bls12_381.bls12_381_curve.b)
abbrev BLSP : Type := EllipticCurve BLSF (0 : BLSF) (4 : BLSF)

-- GaloisField stores polynomial coefficients from highest degree to the
-- constant coefficient.  Thus [c1, c0] represents c0 + c1*u, while the
-- EIP-2537 codec exposes the py_ecc order c0 || c1.  The modulus is
-- u^2 + 1, matching py_ecc's FQ2_MODULUS_COEFFS = (1, 0).
abbrev BLSF2 : Type := GaloisField blsPrime [1, 0, 1]

def BLSF2.mk (c0 c1 : Nat) : BLSF2 :=
  ⟨trimZero [FinField.ofNat c1, FinField.ofNat c0]⟩

def blsB2 : BLSF2 := BLSF2.mk 4 4

abbrev BLSP2 : Type := EllipticCurve BLSF2 (0 : BLSF2) blsB2

-- def bytes_to_fq(data : Bytes) -> FQ:
def B8L.toExStrBLSF (data : B8L) : Except String BLSF := do
  if data.length ≠ 64 then
    .error "InvalidParameter : input should be 64 bytes long"
  let x := B8L.toNat data
  if x ≥ blsPrime then
    .error "InvalidParameter : invalid field element"
  pure (FinField.ofNat x)

-- def bytes_to_g1(data : Bytes) -> Point3D[FQ]:
def B8L.toExStrBLSP (data : B8L) (subgroupCheck : Bool := false) : Except String BLSP := do
  if data.length ≠ 128 then
    .error "InvalidParameter : input should be 128 bytes long"
  let x ← B8L.toExStrBLSF (data.take 64)
  let y ← B8L.toExStrBLSF (data.drop 64)
  let p ← (EllipticCurve.mk? x y).toExcept
    "InvalidParameter : point is not on curve"
  if subgroupCheck then
    if (p.mulBy blsCurveOrder) ≠ ⟨0, 0⟩ then
      .error "InvalidParameter : subgroup check failed"
  pure p

-- def g1_to_bytes(g1_point : Point3D[FQ]) -> Bytes:
def BLSP.toB8L (p : BLSP) : B8L :=
  p.x.val.toB8L.pack 64 ++ p.y.val.toB8L.pack 64

def B8L.toExStrBLSF2 (data : B8L) : Except String BLSF2 := do
  if data.length ≠ 128 then
    .error "InvalidParameter : input should be 128 bytes long"
  let c0 ← B8L.toExStrBLSF (data.take 64)
  let c1 ← B8L.toExStrBLSF (data.drop 64)
  pure ⟨trimZero [c1, c0]⟩

-- def bytes_to_g2(data : Bytes) -> Point3D[FQ2]:
def B8L.toExStrBLSP2 (data : B8L) (subgroupCheck : Bool := false) : Except String BLSP2 := do
  if data.length ≠ 256 then
    .error "InvalidParameter : input should be 256 bytes long"
  let x ← B8L.toExStrBLSF2 (data.take 128)
  let y ← B8L.toExStrBLSF2 (data.drop 128)
  let p ← (EllipticCurve.mk? x y).toExcept
    "InvalidParameter : point is not on curve"
  if subgroupCheck then
    if (p.mulBy blsCurveOrder) ≠ ⟨0, 0⟩ then
      .error "InvalidParameter : subgroup check failed"
  pure p

def BLSF2.toB8L (x : BLSF2) : B8L :=
  let cs := List.ekatD 2 x.val (0 : BLSF)
  let c1 := cs[0]!
  let c0 := cs[1]!
  c0.val.toB8L.pack 64 ++ c1.val.toB8L.pack 64

def BLSP2.toB8L (p : BLSP2) : B8L :=
  p.x.toB8L ++ p.y.toB8L

def decodeG1MsmPairs (data : B8L) : Except String (List (BLSP × Nat)) :=
  let rec aux (fuel : Nat) (acc : List (BLSP × Nat)) (bs : B8L) : Except String (List (BLSP × Nat)) :=
    match fuel with
    | 0 => .ok acc.reverse
    | fuel' + 1 =>
      if bs.isEmpty then .ok acc.reverse
      else if bs.length < 160 then
        .error "InvalidParameter : remaining bytes less than 160"
      else do
        let p ← B8L.toExStrBLSP (bs.take 128) true
        let s := B8L.toNat ((bs.drop 128).take 32)
        aux fuel' ((p, s) :: acc) (bs.drop 160)
  aux data.length [] data

def g1MsmSum (pairs : List (BLSP × Nat)) : BLSP :=
  let rec aux (acc : BLSP) : List (BLSP × Nat) → BLSP
    | [] => acc
    | (p, s) :: ps => aux (acc + p.mulBy s) ps
  aux ⟨0, 0⟩ pairs

def decodeG2MsmPairs (data : B8L) : Except String (List (BLSP2 × Nat)) :=
  let rec aux (fuel : Nat) (acc : List (BLSP2 × Nat)) (bs : B8L) : Except String (List (BLSP2 × Nat)) :=
    match fuel with
    | 0 => .ok acc.reverse
    | fuel' + 1 =>
      if bs.isEmpty then .ok acc.reverse
      else if bs.length < 288 then
        .error "InvalidParameter : remaining bytes less than 288"
      else do
        let p ← B8L.toExStrBLSP2 (bs.take 256) true
        let s := B8L.toNat ((bs.drop 256).take 32)
        aux fuel' ((p, s) :: acc) (bs.drop 288)
  aux data.length [] data

def g2MsmSum (pairs : List (BLSP2 × Nat)) : BLSP2 :=
  let rec aux (acc : BLSP2) : List (BLSP2 × Nat) → BLSP2
    | [] => acc
    | (p, s) :: ps => aux (acc + p.mulBy s) ps
  aux ⟨0, 0⟩ pairs

-- py_ecc.bls12_381.bls12_381_curve.G1
def blsG1GenX : Nat :=
  3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507
def blsG1GenY : Nat :=
  1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569

def blsG1Generator : BLSP := ⟨FinField.ofNat blsG1GenX, FinField.ofNat blsG1GenY⟩

-- py_ecc.bls12_381.bls12_381_curve.double(G1) (== add(G1, G1) == multiply(G1,
-- 2), confirmed against the local venv), pinned here as an independent
-- cross-check on EllipticCurve.add's p = q branch for BLSF.
def blsG1GenDoubleX : Nat :=
  838589206289216005799424730305866328161735431124665289961769162861615689790485775997575391185127590486775437397838
def blsG1GenDoubleY : Nat :=
  3450209970729243429733164009999191867485184320918914219895632678707687208996709678363578245114137957452475385814312

def blsG1GenDouble : BLSP := ⟨FinField.ofNat blsG1GenDoubleX, FinField.ofNat blsG1GenDoubleY⟩

#guard blsG1Generator.isOnCurve
#guard (B8L.toExStrBLSP (BLSP.toB8L blsG1Generator)).toOption = some blsG1Generator
#guard blsG1Generator.double = blsG1GenDouble
#guard (blsG1Generator + blsG1Generator) = blsG1GenDouble
#guard
  (B8L.toExStrBLSP (List.replicate 128 (0 : B8))).toOption = some (⟨0, 0⟩ : BLSP)
#guard BLSP.toB8L (⟨0, 0⟩ : BLSP) = List.replicate 128 (0 : B8)
#guard (blsG1Generator.mulBy blsCurveOrder) = ⟨0, 0⟩

-- py_ecc.bls12_381.bls12_381_curve.G2.  Its FQ2 coefficients are in the
-- c0, c1 order used by the EIP codec.
def blsG2GenX0 : Nat :=
  352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160
def blsG2GenX1 : Nat :=
  3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758
def blsG2GenY0 : Nat :=
  1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905
def blsG2GenY1 : Nat :=
  927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582

def blsG2Generator : BLSP2 :=
  ⟨BLSF2.mk blsG2GenX0 blsG2GenX1, BLSF2.mk blsG2GenY0 blsG2GenY1⟩

#guard blsG2Generator.isOnCurve
#guard (B8L.toExStrBLSP2 (BLSP2.toB8L blsG2Generator)).toOption = some blsG2Generator
#guard BLSP2.toB8L (⟨0, 0⟩ : BLSP2) = List.replicate 256 (0 : B8)
#guard (blsG2Generator.mulBy blsCurveOrder) = ⟨0, 0⟩

-- Pairing machinery, ported from py_ecc's non-optimized
-- `bls12_381_pairing` module.  The Fp12 tower type BLSF12 (modulus
-- w^12 - 2*w^6 + 2, py_ecc FQ12_MODULUS_COEFFS = (2, 0, 0, 0, 0, 0,
-- -2, 0, 0, 0, 0, 0)) and the curve BLSP12 over it already live in
-- EC.lean next to their BN254 counterparts.

-- py_ecc.bls12_381.bls12_381_pairing.ate_loop_count
def blsAteLoopCount : Nat := 15132376222941642752

-- py_ecc.bls12_381.bls12_381_pairing.log_ate_loop_count
def blsLogAteLoopCount : Nat := 62

-- def cast_point_to_fq12(pt: Point2D[FQ]) -> Point2D[FQ12]:
def BLSP.toBLSP12 : BLSP → BLSP12
  | ⟨x, y⟩ => ⟨⟨trimZero [x]⟩, ⟨trimZero [y]⟩⟩

-- def twist(pt: Point2D[FQP]) -> Point2D[FQ12]:
-- Unlike the BN254 twist in EC.lean (which multiplies by w^2 / w^3),
-- py_ecc's BLS12-381 twist divides the coordinates by w^2 / w^3.
def blsTwist (p : BLSP2) : BLSP12 :=
  let xs := List.ekatD 2 p.x.val (0 : BLSF)
  let ys := List.ekatD 2 p.y.val (0 : BLSF)
  let x1 := xs[0]!
  let x0 := xs[1]!
  let y1 := ys[0]!
  let y0 := ys[1]!
  -- Field isomorphism from Z[p] / u^2 + 1 to Z[p] / u^2 - 2*u + 2:
  -- xcoeffs = [_x.coeffs[0] - _x.coeffs[1], _x.coeffs[1]], embedded
  -- into FQ12 at degrees 0 and 6 (w^6 = u).
  let nx : BLSF12 := ⟨trimZero [x1, 0, 0, 0, 0, 0, x0 - x1]⟩
  let ny : BLSF12 := ⟨trimZero [y1, 0, 0, 0, 0, 0, y0 - y1]⟩
  let w : BLSF12 := ⟨[1, 0]⟩
  ⟨nx / (w ^ 2), ny / (w ^ 3)⟩

-- def linefunc(P1, P2, T) -> Field:
-- Duplicated from EC.lean's BN254 `linefunc` (numerator/denominator
-- form, avoiding per-line division) rather than generalizing it.
def blsLinefunc : BLSP12 → BLSP12 → BLSP12 → BLSP12
  | ⟨x1, y1⟩, ⟨x2, y2⟩, ⟨xt, yt⟩ =>
    let mNumerator : BLSF12 := y2 - y1
    let mDenominator : BLSF12 := x2 - x1
    if mDenominator ≠ 0
    then
      ⟨
        mNumerator * (xt - x1) - mDenominator * (yt - y1),
        mDenominator
      ⟩
    else
      if mNumerator = 0
      then
        let mNumerator := 3 * x1 * x1
        let mDenominator := 2 * y1
        ⟨
          mNumerator * (xt - x1) - mDenominator * (yt - y1),
          mDenominator
        ⟩
      else ⟨xt - x1, 1⟩

-- def miller_loop(Q: Point2D[FQ12], P: Point2D[FQ12]) -> FQ12:
-- Iterates the bits of ate_loop_count from bit log_ate_loop_count down
-- to bit 0; unlike the BN254 loop there are no negative pseudo-binary
-- digits and no Frobenius tail lines.
def blsMillerLoop (q p : BLSP12) (finalExp : Bool := true) : Option BLSF12 := do
  let mut r : BLSP12 := q
  let mut fNum : BLSF12 := 1
  let mut fDen : BLSF12 := 1
  -- for i in range(log_ate_loop_count, -1, -1):
  for i in (List.range (blsLogAteLoopCount + 1)).reverse do
    let ⟨_n, _d⟩ := blsLinefunc r r p
    fNum := fNum * fNum * _n
    fDen := fDen * fDen * _d
    r := r.double
    -- if ate_loop_count & (2**i):
    if blsAteLoopCount.testBit i then
      let ⟨_n, _d⟩ := blsLinefunc r q p
      fNum := fNum * _n
      fDen := fDen * _d
      r := r + q
  let f := fNum / fDen
  return (
    if finalExp
    then f ^ ((blsPrime ^ 12 - 1) / blsCurveOrder)
    else f
  )

-- def pairing(Q: Point2D[FQ2], P: Point2D[FQ]) -> FQ12:
def blsPairing (q : BLSP2) (p : BLSP) (finalExp : Bool := true) : Option BLSF12 := do
  guard q.isOnCurve
  guard p.isOnCurve
  if p = ⟨0, 0⟩ ∨ q = ⟨0, 0⟩ then
    return 1
  blsMillerLoop (blsTwist q) (p.toBLSP12) finalExp

-- py_ecc checks `is_on_curve(G12, b12)` for the twisted generator;
-- b12 = b = 4, so the G1 embedding must land on the same curve.
#guard (blsTwist blsG2Generator).isOnCurve
#guard (BLSP.toBLSP12 blsG1Generator).isOnCurve

-- Bilinearity sanity checks: e(2*G1gen, G2gen) = e(G1gen, 2*G2gen)
-- = e(G1gen + G1gen, G2gen) = e(G1gen, G2gen)^2 ≠ 1.  Each pairing is
-- bound once; the squared form and the final inequality also rule out
-- a degenerate implementation mapping everything to 1.
#guard
  let eg := blsPairing blsG2Generator blsG1Generator
  let e2g := blsPairing blsG2Generator (blsG1Generator.mulBy 2)
  let eg2 := blsPairing (blsG2Generator.mulBy 2) blsG1Generator
  let egg := blsPairing blsG2Generator (blsG1Generator + blsG1Generator)
  e2g = eg2 ∧ e2g = egg ∧ e2g = eg.map (fun f => f * f) ∧ eg ≠ some 1
