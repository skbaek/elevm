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

-- def bytes_to_fq(data : Bytes) -> FQ:
def B8L.toExStrBLSF (data : B8L) : Except String BLSF := do
  if data.length ≠ 64 then
    .error "InvalidParameter : input should be 64 bytes long"
  let x := B8L.toNat data
  if x ≥ blsPrime then
    .error "InvalidParameter : invalid field element"
  pure (FinField.ofNat x)

-- def bytes_to_g1(data : Bytes) -> Point3D[FQ]:
def B8L.toExStrBLSP (data : B8L) : Except String BLSP := do
  if data.length ≠ 128 then
    .error "InvalidParameter : input should be 128 bytes long"
  let x ← B8L.toExStrBLSF (data.take 64)
  let y ← B8L.toExStrBLSF (data.drop 64)
  (EllipticCurve.mk? x y).toExcept
    "InvalidParameter : point is not on curve"

-- def g1_to_bytes(g1_point : Point3D[FQ]) -> Bytes:
def BLSP.toB8L (p : BLSP) : B8L :=
  p.x.val.toB8L.pack 64 ++ p.y.val.toB8L.pack 64

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
