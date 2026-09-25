import SigGolfCandidate.Memory

namespace SigGolfCandidate.SphincsReadBufferBytes
open SigGolf RiscvZkvm.Rv64
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def encoded (s : MachineState) (base n : Nat) : Bytes n :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin (8*n) =>
    (s.getByte (BitVec.ofNat 64 (base+i.val/8))).getLsbD (i.val%8))).cast (by simp)

theorem encoded_byte (s : MachineState) (base n i : Nat) (bound : i<n) :
    (encoded s base n).extractLsb' (8*i) 8 = s.getByte (BitVec.ofNat 64 (base+i)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j h
  simp only [BitVec.getLsbD_extractLsb',show decide (j<8)=true by simp [h],Bool.true_and,
    encoded,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp;omega)]
  simp only [List.getElem_ofFn,Option.getD_some]
  rw [show (8*i+j)/8=i by omega,show (8*i+j)%8=j by omega]

theorem readBuffer_byte (s : MachineState) (base n i : Nat) (bound : i<n) :
    (readBuffer s base n).extractLsb' (8*i) 8 = s.getByte (BitVec.ofNat 64 (base+i)) := by
  have encode : readBuffer s base n=encoded s base n :=
    Memory.readBuffer_of_bytes s base n (encoded s base n) (fun j hj => (encoded_byte s base n j hj).symm)
  rw [encode,encoded_byte s base n i bound]

theorem readBuffer_slice_of_bytes (s : MachineState) (base n offset len : Nat)
    (value : Bytes len) (bound : offset+len≤n)
    (values : ∀ i, i<len → s.getByte (BitVec.ofNat 64 (base+offset+i)) = value.extractLsb' (8*i) 8) :
    (readBuffer s base n).extractLsb' (8*offset) (8*len) = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hb
  have hi : bit/8<len := by omega
  have h := (readBuffer_byte s base n (offset+bit/8) (by omega)).trans
    (by simpa [Nat.add_assoc] using values (bit/8) hi)
  have bits := congrArg (fun byte : Byte => byte.getLsbD (bit%8)) h
  have rem : bit%8<8 := Nat.mod_lt _ (by decide)
  simp only [BitVec.getLsbD_extractLsb',show decide (bit%8<8)=true by simp [rem],Bool.true_and] at bits
  rw [show 8*(offset+bit/8)+bit%8=8*offset+bit by omega,
    show 8*(bit/8)+bit%8=bit by omega] at bits
  simpa only [BitVec.getLsbD_extractLsb',show decide (bit<8*len)=true by simp [hb],Bool.true_and] using bits

/-- info: 'SigGolfCandidate.SphincsReadBufferBytes.readBuffer_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readBuffer_byte

/-- info: 'SigGolfCandidate.SphincsReadBufferBytes.readBuffer_slice_of_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readBuffer_slice_of_bytes

end SigGolfCandidate.SphincsReadBufferBytes
