import SigGolfCandidate.Ref.Scheme
import SigGolfCandidate.Ref.Count
import SigGolfCandidate.Ref.Vectors

/-!
# Executable checks of the reference spec against `work/py/ref.py`

The vectors (`Vectors.lean`) are produced by `tools/ref_vectors.py` with a cheap *toy* oracle
(`toyHash`, implemented identically in Python). Each check also compares the number of calls and
an order-sensitive fingerprint `sum_i (i+1) * answer_i mod 2^256` of the whole query sequence,
so the query order is checked, not only the results. Tests only (`#guard`), not part of any proof.
-/

namespace SigGolfCandidate.Ref.Test
open SigGolf OracleComp OracleSpec SigGolfCandidate.Ref SigGolfCandidate.Ref.Vectors

/-- The toy oracle: `z = x mod (2^521-1)`, two squarings, low 256 bits. -/
def toyHash (q : Query) : BitVec 256 :=
  let M := 2 ^ 521 - 1
  let z := q.2.toNat % M
  let z := (z * z + 0x9E3779B97F4A7C15) % M
  let z := (z * z + (q.1 + 1)) % M
  BitVec.ofNat 256 z

/-- Answer with `toyHash`, counting calls and accumulating the fingerprint. -/
def logImpl : QueryImpl HashSpec (StateM (Nat × Nat)) := fun q => do
  let (n, fp) ← get
  let a := toyHash q
  set (n + 1, (fp + (n + 1) * a.toNat) % 2 ^ 256)
  pure a

/-- `(result, calls, fingerprint)` under the toy oracle. -/
def runToy {α : Type} (oa : OracleComp HashSpec α) : α × Nat × Nat :=
  let (a, n, fp) := (simulateQ logImpl oa).run (0, 0)
  (a, n, fp)

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def hex (s : String) : List Byte :=
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i =>
    byte (16 * hexDigit (cs.getD (2 * i) '0') + hexDigit (cs.getD (2 * i + 1) '0'))

def S := hex vSk
def m := hex vMsg

/-! The toy oracle through the organizer's `evalWithAnswerFn` agrees with `runToy`. -/
#guard evalWithAnswerFn toyHash (keygenRef (ofList 32 S)) ==
  ofList 16 (runToy (keygenList S)).1

/-! keygen -/
#guard runToy (keygenList S) == (hex vPk, vKeygenCalls, vKeygenFp)
#guard (runToy (countCalls (keygenRef (ofList 32 S)))).1.2 == 10815
#guard (runToy (countBlocks (keygenRef (ofList 32 S)))).1.2 == 11135

/-! one hypertree tree build with capture (`ref.build_tree`, lay 3, tau 5, e 17) -/
#guard runToy (buildTree S 3 5 5 17 vTreeX) ==
  ((hex vTreeRoot, vTreeVals.map hex, vTreePath.map hex), vTreeCalls, vTreeFp)

/-! one FORS tree of height 4 (tree 5, idx 2^33 + 12345, u = 11) -/
#guard runToy (buildFtsTree S 5 (2 ^ 33 + 12345) 4 11) ==
  ((hex vFtsSecret, vFtsPath.map hex, hex vFtsRoot), vFtsCalls, vFtsFp)

/-! digest search (sign step 1) -/
#guard runToy (searchDigest S m 0 aMax) == (some (hex vDigRho, vDigN), vDigCalls, vDigFp)

/-! counter search (layer 2, tau 7, e 3) and digit decoding -/
#guard runToy (searchCounter 2 7 3 (hex vEncM) 0 cMax) == (some (vEncC, vEncX), vEncC + 1, vEncFp)

def packDigits : Option (List Nat) → Nat
  | none => 0
  | some x => 1 + ((List.range x.length).map fun i => x.getD i 0 * 8 ^ i).sum

#guard vDecIn.map (fun v => packDigits (decodeDigits (hex v))) == vDecOut

/-! expand is `ref.to_witness`, and its inverse -/
def sig := hex vSig
def wit := hex vWit
#guard toWitness sig == wit
#guard fromWitness wit == sig
#guard toList (expandRef (ofList 7756 sig)) == wit
#guard toList (unexpandRef (ofList 7756 wit)) == sig

/-! verify: honest and corrupted witnesses -/
def ver (w : String) : Bool × Nat × Nat :=
  runToy (verifyRef (ofList 32 m) (ofList 16 (hex vPk)) (ofList 7756 (hex w)))

#guard ver vVerOkWit == (vVerOkRes, vVerOkCalls, vVerOkFp)
#guard vVerOkRes == true
#guard ver vVerChainWit == (vVerChainRes, vVerChainCalls, vVerChainFp)
#guard ver vVerSibWit == (vVerSibRes, vVerSibCalls, vVerSibFp)
#guard ver vVerCtrWit == (vVerCtrRes, vVerCtrCalls, vVerCtrFp)
#guard ver vVerRangeWit == (vVerRangeRes, vVerRangeCalls, vVerRangeFp)
#guard ver vVerRhoWit == (vVerRhoRes, vVerRhoCalls, vVerRhoFp)
#guard ver vVerForsWit == (vVerForsRes, vVerForsCalls, vVerForsFp)
#guard runToy (verifyRef (ofList 32 m) 0 (ofList 7756 wit)) == (vVerPkRes, vVerOkCalls, vVerPkFp)
#guard runToy (verifySigRef (ofList 32 m) (ofList 16 (hex vPk)) (ofList 7756 sig)) ==
  (true, vVerOkCalls, vVerOkFp)

#guard (runToy (countCalls (verifyRef (ofList 32 m) (ofList 16 (hex vPk)) (ofList 7756 wit)))).1 ==
  (true, vVerOkCalls)

/-! the full signature (121,400 queries; a few seconds) -/
#guard runToy (signRef (ofList 32 S) (ofList 32 m)) == (some (ofList 7756 sig), vSignCalls, vSignFp)

end SigGolfCandidate.Ref.Test
