import SigGolfCandidate.SphincsBeta64Images
import SigGolfCandidate.SphincsMaskedImages

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
