import SigGolfCandidate.SphincsMaskedSignTagCheck
import SigGolfCandidate.SphincsMaskedMacRestoration

namespace SigGolfCandidate.SphincsMaskedSignTagFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedMacTrace SphincsMaskedMacDomain SphincsMaskedMacRestoration
open SphincsMaskedChainDomain SphincsMaskedSecretDomain SphincsCacheSecretDomains SphincsSecurity SphincsBridge
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The in-place MAC restores all five stored tag words. -/
theorem result_tag_word (hash : Hash) (p : Word) (s : MachineState)
    (i : Fin 5) :
    (result hash p s).getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val)) := by
  fin_cases i
  · simpa [MachineState.getWord32, alignToDword, byteOffset] using
      congrArg (fun w : Word => extractWord32 w 1)
        (result_low_frame hash p s 0x20048 (by decide))
  · simpa [MachineState.getWord32, alignToDword, byteOffset] using
      congrArg (fun w : Word => extractWord32 w 0)
        (result_low_frame hash p s 0x20050 (by decide))
  · simpa [MachineState.getWord32, alignToDword, byteOffset] using
      congrArg (fun w : Word => extractWord32 w 1)
        (result_low_frame hash p s 0x20050 (by decide))
  · simpa [MachineState.getWord32, alignToDword, byteOffset] using
      congrArg (fun w : Word => extractWord32 w 0)
        (result_low_frame hash p s 0x20058 (by decide))
  · simpa [MachineState.getWord32, alignToDword, byteOffset] using
      congrArg (fun w : Word => extractWord32 w 1)
        (result_low_frame hash p s 0x20058 (by decide))

/-- A canonical tag passes the five-lane signer MAC comparison. -/
theorem tag_equal_of_cache (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1144) (parameter : BitVec 160) (seed : MasterSeed)
    (par : Words20 s 0x74 parameter) (key : Words32 s seed)
    (tag : Words20 s 0x2004c
      (truncateHash (hash (toQuery (macInput parameter seed (ciphertext s))))))
    (i : Fin 5) :
    (result hash 0x1144 s).getWord32 (BitVec.ofNat 64 (0x84000 + 4 * i.val)) =
      (result hash 0x1144 s).getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val)) := by
  have h := (contract hash SphincsMaskedImages.sign 0x1144 sign_code s pc
    parameter seed par key).2.2.2 i
  rw [h, result_tag_word]
  exact (tag i).symm

/-- info: 'SigGolfCandidate.SphincsMaskedSignTagFrame.tag_equal_of_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tag_equal_of_cache

end SigGolfCandidate.SphincsMaskedSignTagFrame
