import SigGolfCandidate.SphincsMaskedMacTrace
import SigGolfCandidate.SphincsMaskedSecretDomain
import SigGolfCandidate.SphincsCacheSecretDomains

namespace SigGolfCandidate.SphincsMaskedMacDomain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedMacTrace SphincsMaskedChainDomain SphincsMaskedSecretDomain
open SphincsVerifierFtsRootCopy SphincsVerifierFtsRootCopyBytes SphincsBridge SphincsSecurity
open SphincsCacheSecretDomains
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def lowWrites : List Word := List.ofFn fun i : Fin 9 => BitVec.ofNat 64 (0x18 + 8*i.val)
theorem lowWrites_eq : lowWrites = [0x18#64, 0x20#64, 0x28#64, 0x30#64, 0x38#64, 0x40#64, 0x48#64, 0x50#64, 0x58#64] := by rfl

def highWrites : List Word := [0x43000#64, 0x43008#64, 0x43010#64, 0x43018#64, 0x40000#64, 0x40008#64, 0x40010#64, 0x40018#64, 0x40020#64, 0x85000#64, 0x85008#64, 0x85010#64, 0x85018#64, 0x85020#64, 0x85028#64, 0x85030#64, 0x85038#64, 0x85040#64]
def prepareWrites : List Word := lowWrites ++ highWrites

theorem prepare_frame (p : Word) (s : MachineState) (a : Word) (outside : a ∉ prepareWrites) :
    (prepare p s).getMem a = s.getMem a := by
  have split : a ∉ lowWrites ∧ a ∉ highWrites := by
    simpa only [prepareWrites,List.mem_append,not_or] using outside
  obtain ⟨lo,hi⟩ := split
  simp only [lowWrites_eq,List.mem_cons,List.not_mem_nil,not_or] at lo
  simp only [highWrites,List.mem_cons,List.not_mem_nil,not_or] at hi
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := lo
  obtain ⟨h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26⟩ := hi
  simp [prepare,runSchedule,prepareSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26]

theorem prepare_cache_frame (p : Word) (s : MachineState) (a : Word)
    (lower : 0x60 ≤ a.toNat) (upper : a.toNat < 0x40000) :
    (prepare p s).getMem a = s.getMem a := by
  apply prepare_frame
  intro member
  have bounds : ∀ b ∈ prepareWrites, b.toNat < 0x60 ∨ 0x40000 ≤ b.toNat := by
    simp [prepareWrites,lowWrites_eq,highWrites]
  rcases bounds a member with low | high <;> omega

def queryWord (s : MachineState) (i : Fin 18) : BitVec 32 :=
  if i.val = 0 then 3841
  else if i.val < 5 then 0
  else if i.val < 10 then s.getWord32 (BitVec.ofNat 64 (0x74 + 4*(i.val-5)))
  else s.getWord32 (BitVec.ofNat 64 (0x20 + 4*(i.val-10)))

theorem prepare_words (p : Word) (s : MachineState) (i : Fin 18) :
    (prepare p s).getWord32 (BitVec.ofNat 64 (0x18 + 4*i.val)) = queryWord s i := by
  fin_cases i <;>
    simp [prepare,runSchedule,prepareSchedule,execInstrBr,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,queryWord,extractWord32]
  all_goals ext b hb;interval_cases b <;> simp [replaceWord32]

def macPrefix (parameter : BitVec 160) (seed : MasterSeed) : List Byte :=
  ((fieldBytes (tweakFields 15 0 0 0 0)) ++ bytesLE 20 parameter ++ bytesLE 32 seed).map UInt8.toBitVec

theorem macPrefix_length (parameter : BitVec 160) (seed : MasterSeed) : (macPrefix parameter seed).length = 72 := by
  simp [macPrefix,fieldBytes,tweakFields,bytesLE]

theorem macPrefix_byte (p : Word) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (par : Words20 s 0x74 parameter) (key : Words32 s seed) (i : Fin 72) :
    (prepare p s).getByte (BitVec.ofNat 64 (0x18+i.val)) =
      (macPrefix parameter seed)[i.val]'(by rw [macPrefix_length];exact i.isLt) := by
  have h := SphincsVerifierFtsGenericBytes.variableWord_byte (prepare p s)
    (0x18 + 4*(i.val/4)) (by omega) (by omega) 0 ⟨i.val%4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  rw [show 0x18+4*(i.val/4)+i.val%4 = 0x18+i.val by omega] at h
  rw [h,prepare_words p s ⟨i.val/4,by omega⟩]
  have p0 := par 0
  have p1 := par 1
  have p2 := par 2
  have p3 := par 3
  have p4 := par 4
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  have k3 := key 3
  have k4 := key 4
  have k5 := key 5
  have k6 := key 6
  have k7 := key 7
  norm_num at p0 p1 p2 p3 p4 k0 k1 k2 k3 k4 k5 k6 k7
  fin_cases i <;>
    simp [queryWord,p0,p1,p2,p3,p4,k0,k1,k2,k3,k4,k5,k6,k7,macPrefix,fieldBytes,tweakFields,bytesLE,protocolDomainSep]
  all_goals ext b hb;interval_cases b <;> simp

/-- The authenticated cache bytes are read directly from their original public-memory slots. -/
def ciphertext (s : MachineState) : HashInput :=
  List.ofFn fun i : Fin 131052 => UInt8.ofBitVec (s.getByte (BitVec.ofNat 64 (0x60+i.val)))

theorem prepare_payload (p : Word) (s : MachineState) (i : Fin 131052) :
    (prepare p s).getByte (BitVec.ofNat 64 (0x60+i.val)) = s.getByte (BitVec.ofNat 64 (0x60+i.val)) := by
  rw [getByte_word _ 0x60 i.val (by decide) (by omega),getByte_word _ 0x60 i.val (by decide) (by omega)]
  rw [prepare_cache_frame]
  all_goals simp only [wordAddress,BitVec.toNat_ofNat];rw [Nat.mod_eq_of_lt (by omega)];omega

theorem input_split (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed) :
    (macInput parameter seed (ciphertext s)).map UInt8.toBitVec =
      macPrefix parameter seed ++ (ciphertext s).map UInt8.toBitVec := by
  simp [macInput,macPrefix]

theorem query_eq (p : Word) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (par : Words20 s 0x74 parameter) (key : Words32 s seed) :
    hashInput (prepare p s) = toQuery (macInput parameter seed (ciphertext s)) := by
  apply Serialization.hashInput_of_list (prepare p s) 0x18 ((macInput parameter seed (ciphertext s)).map UInt8.toBitVec)
  · exact (prepare_registers p s).1
  · rw [input_split,List.length_append,macPrefix_length,List.length_map]
    simp only [ciphertext,List.length_ofFn,(prepare_registers p s).2.1];rfl
  · intro i hi
    simp only [input_split] at hi ⊢
    have bound : i < 131124 := by simpa only [List.length_append,macPrefix_length,List.length_map,ciphertext,List.length_ofFn] using hi
    by_cases h : i < 72
    · rw [List.getElem_append_left (by simpa only [macPrefix_length] using h)]
      exact macPrefix_byte p s parameter seed par key ⟨i,h⟩
    · rw [List.getElem_append_right (by simpa only [macPrefix_length] using Nat.le_of_not_gt h)]
      simp only [macPrefix_length]
      have address : 0x18+i = 0x60+(i-72) := by omega
      rw [address,prepare_payload p s ⟨i-72,by omega⟩]
      simp only [ciphertext,List.map_ofFn,List.getElem_ofFn,Function.comp_apply,UInt8.toBitVec_ofBitVec]

/-- info: 'SigGolfCandidate.SphincsMaskedMacDomain.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_eq

end SigGolfCandidate.SphincsMaskedMacDomain
