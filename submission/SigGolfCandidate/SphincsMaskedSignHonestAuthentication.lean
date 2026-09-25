import SigGolfCandidate.SphincsMaskedSignRootValue
import SigGolfCandidate.SphincsMaskedSignTagFrame
import SigGolfCandidate.SphincsMaskedSignParameterFrame
import SigGolfCandidate.SphincsMaskedKeygenPadding

namespace SigGolfCandidate.SphincsMaskedSignHonestAuthentication
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsSecurity SphincsBridge SphincsCacheSecretDomains
open SphincsMaskedChainDomain SphincsMaskedSecretDomain
open SphincsMaskedSignRootValue SphincsMaskedMaskSemantics
open SphincsMaskedKeygenRefinement
set_option maxRecDepth 16384
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

abbrev parameterState (hash : Hash) (seed : MasterSeed) (cache : SigGolf.Cache)
    (message : SigGolf.Message) : MachineState :=
  SphincsMaskedSignPrefix.afterHashState hash
    (SphincsMaskedSignPrefix.afterJumpState seed cache message) seed
abbrev checkedState (hash : Hash) (seed : MasterSeed) (cache : SigGolf.Cache)
    (message : SigGolf.Message) : MachineState :=
  SphincsMaskedSignParameterCheck.afterComparison (parameterState hash seed cache message)
abbrev macState (hash : Hash) (seed : MasterSeed) (cache : SigGolf.Cache)
    (message : SigGolf.Message) : MachineState :=
  SphincsMaskedMacTrace.result hash 0x1144 (checkedState hash seed cache message)
abbrev finalState (hash : Hash) (seed : MasterSeed) (cache : SigGolf.Cache)
    (message : SigGolf.Message) : MachineState :=
  SphincsMaskedSignTagCheck.afterComparison (macState hash seed cache message)

theorem firstHash_frame (s : MachineState) (a : Word) (low : a.toNat < 0x40000) :
    (SphincsMaskedSignPrefix.firstHashState s).getMem a = s.getMem a := by
  have ne (b : Word) (high : 0x40000 ≤ b.toNat) : a ≠ b := by
    intro eq; rw [eq] at low; omega
  simp [SphincsMaskedSignPrefix.firstHashState,
    SphincsMaskedKeygenPrefix.runSchedule,SphincsMaskedSignPrefix.prefixSchedule,
    SphincsMaskedKeygenPrefix.prefixSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,ne]

theorem afterHash_frame (hash : Hash) (s : MachineState) (seed : MasterSeed)
    (a : Word) (low : a.toNat < 0x40000) :
    (SphincsMaskedSignPrefix.afterHashState hash s seed).getMem a = s.getMem a := by
  have ne (b : Word) (high : 0x40000 ≤ b.toNat) : a ≠ b := by
    intro eq; rw [eq] at low; omega
  have dst := (SphincsMaskedSignPrefix.firstHash_registers s).2.2.1
  simp [SphincsMaskedSignPrefix.afterHashState,writeHash,dst,
    MachineState.writeWords,ne,firstHash_frame s a low]

/-- Parameter derivation leaves the whole loaded low memory intact. -/
theorem parameter_frame (hash : Hash) (seed : MasterSeed) (cache : SigGolf.Cache)
    (message : SigGolf.Message) (a : Word) (low : a.toNat < 0x40000) :
    (parameterState hash seed cache message).getMem a =
      (SphincsMaskedSignPrefix.entryState seed cache message).getMem a := by
  rw [parameterState,afterHash_frame _ _ _ _ low]
  simp only [SphincsMaskedSignPrefix.afterJumpState,execInstrBr,
    MachineState.getMem_setReg,MachineState.getMem_setPC]

theorem checked_frame (hash : Hash) (seed : MasterSeed) (cache : SigGolf.Cache)
    (message : SigGolf.Message) (a : Word) (low : a.toNat < 0x40000) :
    (checkedState hash seed cache message).getMem a =
      (SphincsMaskedSignPrefix.entryState seed cache message).getMem a := by
  rw [checkedState,SphincsMaskedSignParameterCheck.comparison_mem]
  exact parameter_frame hash seed cache message a low

theorem final_frame (hash : Hash) (seed : MasterSeed) (cache : SigGolf.Cache)
    (message : SigGolf.Message) (a : Word) (low : a.toNat < 0x40000) :
    (finalState hash seed cache message).getMem a =
      (SphincsMaskedSignPrefix.entryState seed cache message).getMem a := by
  rw [finalState,SphincsMaskedSignTagCheck.comparison_mem,
    macState,SphincsMaskedMacRestoration.result_low_frame _ _ _ a low]
  exact checked_frame hash seed cache message a low

/-- Reusable transport of decoded cache/key lanes across a low-memory frame. -/
theorem frame_word (before after : MachineState)
    (frame : ∀ a : Word, a.toNat < 0x40000 → after.getMem a = before.getMem a)
    (a : Nat) (low : a < 0x40000) :
    after.getWord32 (BitVec.ofNat 64 a) = before.getWord32 (BitVec.ofNat 64 a) := by
  simp only [MachineState.getWord32,frame _ (low_cell a low)]

theorem frame_words20 (before after : MachineState)
    (frame : ∀ a : Word, a.toNat < 0x40000 → after.getMem a = before.getMem a)
    (base : Nat) (low : base + 20 ≤ 0x40000) (value : Digest)
    (words : Words20 before base value) : Words20 after base value := by
  intro i
  rw [frame_word before after frame _ (by have := i.isLt; omega)]
  exact words i

theorem frame_words32 (before after : MachineState)
    (frame : ∀ a : Word, a.toNat < 0x40000 → after.getMem a = before.getMem a)
    (seed : MasterSeed) (words : Words32 before seed) : Words32 after seed := by
  intro i
  rw [frame_word before after frame _ (by have := i.isLt; omega)]
  exact words i

theorem checked_ciphertext (hash : Hash) (seed : MasterSeed) (cache : SigGolf.Cache)
    (message : SigGolf.Message) :
    SphincsMaskedMacDomain.ciphertext (checkedState hash seed cache message) =
      cacheCiphertext cache := by
  apply congrArg List.ofFn
  funext i
  apply congrArg UInt8.ofBitVec
  rw [MachineState.getByte,checked_frame _ _ _ _ _ (low_cell _ (by have := i.isLt; omega))]
  exact entry_cache_byte seed cache message i.val (by have := i.isLt; dsimp [CACHE_BYTES]; omega)

/-- The two concrete comparison premises follow from the generated cache's fields and tag. -/
theorem honest_checks (hash : Hash) (seed : MasterSeed) (cache : SigGolf.Cache)
    (message : SigGolf.Message) (sem : CacheSemantics hash seed cache) :
    (∀ i : Fin 5, (parameterState hash seed cache message).getWord32
      (BitVec.ofNat 64 (0x42000 + 4*i.val)) =
      (parameterState hash seed cache message).getWord32
      (BitVec.ofNat 64 (0x74 + 4*i.val))) ∧
    (∀ i : Fin 5, (macState hash seed cache message).getWord32
      (BitVec.ofNat 64 (0x84000 + 4*i.val)) =
      (macState hash seed cache message).getWord32
      (BitVec.ofNat 64 (0x2004c + 4*i.val))) := by
  obtain ⟨masked,par,key⟩ := entry_honest_cache hash seed cache message sem
  have pe : ∀ i : Fin 5, (parameterState hash seed cache message).getWord32
      (BitVec.ofNat 64 (0x42000 + 4*i.val)) =
      (parameterState hash seed cache message).getWord32
      (BitVec.ofNat 64 (0x74 + 4*i.val)) := by
    intro i
    rw [SphincsMaskedSignParameterCheck.afterHash_words32]
    rw [frame_word _ _ (parameter_frame hash seed cache message) (0x74 + 4*i.val) (by have := i.isLt; omega),par i]
    unfold parameter truncateHash
    exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm
  refine ⟨pe,?_⟩
  have pc : (parameterState hash seed cache message).pc = 0x10e8 := by
    simp [parameterState,SphincsMaskedSignPrefix.afterHashState,writeHash,
      SphincsMaskedSignPrefix.firstHash_pc,SphincsMaskedSignPrefix.afterJump_pc]
  have cpc := SphincsMaskedSignParameterCheck.comparison_pc _ pc pe
  have cpar := frame_words20 _ _ (checked_frame hash seed cache message) 0x74 (by decide) _ par
  have ckey := frame_words32 _ _ (checked_frame hash seed cache message) seed key
  apply SphincsMaskedSignTagFrame.tag_equal_of_cache hash _ cpc (parameter hash seed) seed cpar ckey
  rw [checked_ciphertext]
  apply frame_words20 _ _ (checked_frame hash seed cache message) 0x2004c (by decide)
  have tag := entry_cache_words20 seed cache message 131052 (by decide) (by decide)
  rw [sem.tag] at tag
  exact tag

/-- Exact authentication prefix for every cache carrying the keygen semantics.
    No random-oracle independence, query bound, or padding hypothesis is needed. -/
theorem honest_authenticated (hash : Hash) (seed : MasterSeed) (cache : SigGolf.Cache)
    (message : SigGolf.Message) (sem : CacheSemantics hash seed cache) :
    Trace hash SphincsMaskedImages.sign
      (SphincsMaskedSignPrefix.entryState seed cache message) 346 16752 2 2051
      (finalState hash seed cache message) ∧
    (finalState hash seed cache message).pc = 0x132c ∧
    Words20 (finalState hash seed cache message) 0x60
      (root hash seed ^^^ padValue hash (parameter hash seed) seed 4094) ∧
    Words20 (finalState hash seed cache message) 0x74 (parameter hash seed) ∧
    Words32 (finalState hash seed cache message) seed := by
  obtain ⟨pe,te⟩ := honest_checks hash seed cache message sem
  obtain ⟨masked,par,key⟩ := entry_honest_cache hash seed cache message sem
  have pc : (parameterState hash seed cache message).pc = 0x10e8 := by
    simp [parameterState,SphincsMaskedSignPrefix.afterHashState,writeHash,
      SphincsMaskedSignPrefix.firstHash_pc,SphincsMaskedSignPrefix.afterJump_pc]
  have cpc := SphincsMaskedSignParameterCheck.comparison_pc _ pc pe
  have mpc := (SphincsMaskedMacTrace.trace hash SphincsMaskedImages.sign 0x1144
    SphincsMaskedMacTrace.sign_code _ cpc).2
  refine ⟨SphincsMaskedSignTagCheck.loaded_authenticated_trace hash seed cache message pe te,
    SphincsMaskedSignTagCheck.comparison_pc _ mpc te,?_,?_,?_⟩
  · exact frame_words20 _ _ (final_frame hash seed cache message) 0x60 (by decide) _ masked
  · exact frame_words20 _ _ (final_frame hash seed cache message) 0x74 (by decide) _ par
  · exact frame_words32 _ _ (final_frame hash seed cache message) seed key

/-- Concrete organizer keygen output loads into a successful authentication prefix. -/
theorem generated_cache_authenticates (hash : Hash) (seed : MasterSeed)
    (message : SigGolf.Message) :
    ∃ (cache : SigGolf.Cache) (entry final : MachineState),
      SphincsSubmission.submission.runWith hash .keygen seed =
        ⟨some (publicKey hash seed,cache),true,92369576,860161,1007616⟩ ∧
      SphincsMaskedKeygenPadding.CacheZeroPadding cache ∧
      initialState SphincsSubmission.submission .sign (seed,cache,message) = some entry ∧
      Trace hash SphincsMaskedImages.sign entry 346 16752 2 2051 final ∧
      final.pc = 0x132c ∧
      Words20 final 0x60 (root hash seed ^^^ padValue hash (parameter hash seed) seed 4094) ∧
      Words20 final 0x74 (parameter hash seed) ∧ Words32 final seed := by
  obtain ⟨cache,run,sem,zero⟩ := SphincsMaskedKeygenPadding.keygen_runWith_canonical
    SphincsSubmission.submission hash seed rfl (SphincsSubmission.admissible.2 .keygen)
    rfl rfl rfl
  exact ⟨cache,SphincsMaskedSignPrefix.entryState seed cache message,
    finalState hash seed cache message,run,zero,
    SphincsMaskedSignPrefix.entry_loaded seed cache message,
    honest_authenticated hash seed cache message sem⟩

/-- info: 'SigGolfCandidate.SphincsMaskedSignHonestAuthentication.honest_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_checks

/-- info: 'SigGolfCandidate.SphincsMaskedSignHonestAuthentication.honest_authenticated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_authenticated

/-- info: 'SigGolfCandidate.SphincsMaskedSignHonestAuthentication.generated_cache_authenticates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms generated_cache_authenticates

end SigGolfCandidate.SphincsMaskedSignHonestAuthentication
