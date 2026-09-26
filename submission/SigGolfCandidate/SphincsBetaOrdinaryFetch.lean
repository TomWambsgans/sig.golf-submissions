import SigGolfCandidate.SphincsBeta64Images
import SigGolfCandidate.SphincsMaskedImages
import SigGolfCandidate.SphincsImages

namespace SigGolfCandidate.KeygenOrdinaryFetch
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem whole :
    (SphincsMaskedImages.keygen.code.zipWith
      (fun old new => old == (0x73 : BitVec 32) || old == new)
      (Pc64KeygenImage.code.take 901)).all id = true := by decide

theorem keygen_word (i : Nat) (hi : i < 901) :
    SphincsMaskedImages.keygen.code[i]? = some (0x73 : BitVec 32) ∨
    SphincsMaskedImages.keygen.code[i]? = Pc64KeygenImage.code[i]? := by
  apply GenericWordTransport.pointwise (0x73 : BitVec 32) whole
  · rw [SphincsMaskedImages.keygen_code_length]
    exact hi
  · rw [Pc64KeygenImage.code_length]
    omega
  · exact hi

theorem keygen_ordinary_fetch (s : MachineState) (ins : Instruction)
    (fetched : fetch SphincsMaskedImages.keygen s = some ins)
    (ordinary : ins ≠ .base .ECALL) :
    fetch Pc64KeygenImage.image s = some ins := by
  apply GenericFetchTransport.ordinary_fetch SphincsMaskedImages.keygen
    Pc64KeygenImage.image s ins
  · intro i hi
    have hi' : i < 901 := by
      simpa only [SphincsMaskedImages.keygen_code_length] using hi
    simpa only [Pc64KeygenImage.image] using keygen_word i hi'
  · exact fetched
  · exact ordinary

#print axioms whole
#print axioms keygen_ordinary_fetch
end SigGolfCandidate.KeygenOrdinaryFetch

namespace SigGolfCandidate.SignOrdinaryFetch
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 262144
set_option maxHeartbeats 2000000

theorem whole :
    (SphincsMaskedImages.sign.code.zipWith
      (fun old new => old == (0x73 : BitVec 32) || old == new)
      (Pc64SignImage.code.take 10957)).all id = true := by decide

theorem sign_word (i : Nat) (hi : i < 10957) :
    SphincsMaskedImages.sign.code[i]? = some (0x73 : BitVec 32) ∨
    SphincsMaskedImages.sign.code[i]? = Pc64SignImage.code[i]? := by
  apply GenericWordTransport.pointwise (0x73 : BitVec 32) whole
  · rw [SphincsMaskedImages.sign_code_length]
    exact hi
  · rw [Pc64SignImage.code_length]
    omega
  · exact hi

theorem sign_ordinary_fetch (s : MachineState) (ins : Instruction)
    (fetched : fetch SphincsMaskedImages.sign s = some ins)
    (ordinary : ins ≠ .base .ECALL) :
    fetch Pc64SignImage.image s = some ins := by
  apply GenericFetchTransport.ordinary_fetch SphincsMaskedImages.sign
    Pc64SignImage.image s ins
  · intro i hi
    have hi' : i < 10957 := by
      simpa only [SphincsMaskedImages.sign_code_length] using hi
    simpa only [Pc64SignImage.image] using sign_word i hi'
  · exact fetched
  · exact ordinary

#print axioms whole
#print axioms sign_ordinary_fetch
end SigGolfCandidate.SignOrdinaryFetch

namespace SigGolfCandidate.UnitCycleLegacy
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000

def unitOrEcall (word : BitVec 32) : Bool :=
  match decodeInstruction word with
  | none => true
  | some instruction => instructionCycles instruction == 1

theorem unit_of_fetch (image : Image) (s : MachineState) (instruction : Instruction)
    (himage : image.code.all unitOrEcall = true)
    (fetched : fetch image s = some instruction) :
    instructionCycles instruction = 1 := by
  let i := (s.pc.toNat - 0x1000) / 4
  have guard : ¬ (s.pc.toNat < 0x1000 || s.pc.toNat % 4 != 0) := by
    by_contra h
    simp [fetch, h] at fetched
  have hf : (image.code[i]?).bind decodeInstruction = some instruction := by
    simpa [fetch, guard, i] using fetched
  cases hcode : image.code[i]? with
  | none => simp [hcode] at hf
  | some w =>
      have hi : i < image.code.length := (List.getElem?_eq_some_iff.mp hcode).1
      have hw : image.code[i] = w := by
        simpa [List.getElem?_eq_getElem hi] using hcode
      have hmem : w ∈ image.code := by simpa [hw] using List.getElem_mem hi
      have hunit : unitOrEcall w = true := (List.all_eq_true.mp himage) w hmem
      have hdecode : decodeInstruction w = some instruction := by simpa [hcode] using hf
      have hcycles : (instructionCycles instruction == 1) = true := by
        simpa only [unitOrEcall, hdecode] using hunit
      exact beq_iff_eq.mp hcycles

theorem keygen_all : SphincsMaskedImages.keygen.code.all unitOrEcall = true := by decide
theorem sign_all : SphincsMaskedImages.sign.code.all unitOrEcall = true := by decide
theorem expand_all : SphincsImages.expand.code.all unitOrEcall = true := by decide
theorem verify_all : SphincsImages.verify.code.all unitOrEcall = true := by decide

#print axioms keygen_all
#print axioms sign_all
#print axioms expand_all
#print axioms verify_all
#print axioms unit_of_fetch

end SigGolfCandidate.UnitCycleLegacy
