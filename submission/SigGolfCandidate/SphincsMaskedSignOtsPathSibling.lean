import SigGolfCandidate.SphincsMaskedSignOtsPathSetup

namespace SigGolfCandidate.SphincsMaskedSignOtsPathSibling
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SigGolfCandidate.SphincsMaskedSignOtsPath SigGolfCandidate.SphincsMaskedSignOtsPathSetup
open SphincsMaskedSignOtsParents SphincsMaskedSignOtsTree SphincsMaskedSignOtsShift
open SphincsVerifierCopy SphincsVerifierFtsRootCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem sibling_in_width (location : Fin 5) (level : Fin (Levels.height location))
    (bit : Nat) (small : bit < Levels.width location level.val) :
    bit ^^^ 1 < Levels.width location level.val := by
  have hn : 0 < Levels.height location-level.val := by omega
  have hpow : 1 < 2^(Levels.height location-level.val) := by
    obtain ⟨n,hn'⟩ : ∃ n,Levels.height location-level.val=n+1 :=
      ⟨Levels.height location-level.val-1,by omega⟩
    rw [hn',pow_succ]
    have hp : 0<2^n := pow_pos (by decide) n
    omega
  have hb : bit < 2^(Levels.height location-level.val) := by
    simpa [Levels.width,Nat.le_of_lt level.isLt] using small
  have result := Nat.xor_lt_two_pow hb hpow
  simpa [Levels.width,Nat.le_of_lt level.isLt] using result

theorem sibling_source (location : Fin 5) (level : Fin (Levels.height location))
    (bit : Nat) (small : bit < Levels.width location level.val) :
    let source := Levels.cacheBase location level.val + 20*(bit ^^^ 1)
    source % 4 = 0 ∧ 0x50000 ≤ source ∧ source + 20 ≤ 0x53000 := by
  have sibling := sibling_in_width location level bit small
  obtain ⟨baseEq,_,upper,aligned,_,above,_,_,_,twice,_,_⟩ := Levels.layout location level
  dsimp
  refine ⟨?_,by omega,?_⟩
  · omega
  · have within : Levels.cacheBase location level.val+20*(bit ^^^ 1)+20 ≤
        Levels.cacheBase location (level.val+1) := by
      calc
        _ = Levels.cacheBase location level.val+20*((bit ^^^ 1)+1) := by omega
        _ ≤ Levels.cacheBase location level.val+20*Levels.width location level.val := by omega
        _ = Levels.cacheBase location (level.val+1) := by omega
    omega

/-- The real fourteen-instruction address setup and ten-instruction copy write
one exact sibling digest to the signature, for arbitrary cached node bytes. -/
theorem copy_sibling (location : Fin 5) (s : MachineState)
    (level : Fin (Levels.height location)) (bit pointer : Nat)
    (pc : s.pc=0x1938+SphincsMaskedSignOtsParents.delta location)
    (ctrl : PathControls location s level.val bit pointer)
    (bitBound : bit < Levels.width location level.val)
    (pointerBound : pointer+20≤0x40000) (pointerAlign : pointer%4=0) :
    let source := Levels.cacheBase location level.val+20*(bit ^^^ 1)
    OrdinarySteps SphincsMaskedImages.sign s 24
      (copyRootState (setupState location s)) ∧
    ∀ i : Fin 5,
      (copyRootState (setupState location s)).getWord32 (BitVec.ofNat 64 (pointer+4*i.val)) =
        s.getWord32 (BitVec.ofNat 64 (source+4*i.val)) := by
  let source := Levels.cacheBase location level.val+20*(bit ^^^ 1)
  obtain ⟨sourceAlign,sourceAbove,sourceBound⟩ := sibling_source location level bit bitBound
  have regs := setup_regs location s level.val bit pointer ctrl
  have first := setup_block location s pc
  have second := copied_block location (setupState location s) source pointer
    (setup_pc location s pc) regs.1 regs.2 sourceAlign (by omega) pointerAlign pointerBound
  refine ⟨ordinary_trans _ _ _ _ 14 10 first second,?_⟩
  intro i
  rw [copied_word (setupState location s) source pointer regs.1 regs.2
    sourceAlign (by omega) pointerAlign pointerBound sourceAbove i]
  simp only [MachineState.getWord32]
  rw [setup_frame]

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathSibling.copy_sibling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copy_sibling

end SigGolfCandidate.SphincsMaskedSignOtsPathSibling
