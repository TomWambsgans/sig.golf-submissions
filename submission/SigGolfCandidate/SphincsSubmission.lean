import SigGolfCandidate.SphincsImages
import SigGolfCandidate.SphincsMaskedImages
import SigGolfCandidate.SphincsWire
import SigGolfCandidate.Execution

namespace SigGolfCandidate.SphincsSubmission
open SigGolf
set_option maxRecDepth 16384

def sizes : Sizes := ⟨SphincsWire.signatureBytes, SphincsWire.signatureBytes⟩
def layout : Layout := Riscv.standardLayout sizes

def submission : Submission where
  sizes := sizes
  layout := layout
  image
    | .keygen => SphincsMaskedImages.keygen
    | .sign => SphincsMaskedImages.sign
    | .expand => BetaExpand.translated
    | .verify => SphincsImages.verify

/-- Candidate value. No organizer certificate is claimed in this module. -/
def cycleBound : Nat := 1000000

theorem sizes_valid : sizes.Valid := by
  simp [Sizes.Valid, sizes, SphincsWire.signatureBytes_eq, MAX_WITNESS_BYTES]
theorem score_eq : submission.score cycleBound = 11324000000 := by decide

theorem keygen_byteSize : SphincsMaskedImages.keygen.byteSize = 3604 := by
  unfold Riscv.Image.byteSize
  rw [SphincsMaskedImages.keygen_code_length]
  rfl

theorem sign_byteSize : SphincsMaskedImages.sign.byteSize = 43828 := by
  unfold Riscv.Image.byteSize
  rw [SphincsMaskedImages.sign_code_length]
  rfl

theorem expand_byteSize : BetaExpand.translated.byteSize = 76 := by
  unfold Riscv.Image.byteSize
  rfl

theorem verify_byteSize : SphincsImages.verify.byteSize = 27816 := by
  unfold Riscv.Image.byteSize
  rw [SphincsImages.verify_code_length]
  rfl

private theorem layout_valid_of_data_empty (image : Riscv.Image)
    (empty : image.data = []) : Riscv.layoutValid layout sizes image := by
  simp [Riscv.layoutValid, Riscv.dataBase, empty, layout, sizes,
    SphincsWire.signatureBytes_eq, Riscv.layoutBuffers, Riscv.buffersDisjoint,
    Riscv.disjointBuffers, Riscv.standardLayout]
  norm_num [MEMORY_BYTES, CACHE_BYTES, Riscv.signatureBase, Riscv.witnessBase]

theorem admissible : submission.Admissible := by
  constructor
  · exact sizes_valid
  · intro phase
    cases phase <;> constructor
    · change SphincsMaskedImages.keygen.byteSize < MAX_IMAGE_BYTES
      rw [keygen_byteSize]
      decide
    · exact layout_valid_of_data_empty _ rfl
    · change SphincsMaskedImages.sign.byteSize < MAX_IMAGE_BYTES
      rw [sign_byteSize]
      decide
    · exact layout_valid_of_data_empty _ rfl
    · change BetaExpand.translated.byteSize < MAX_IMAGE_BYTES
      rw [expand_byteSize]
      decide
    · exact layout_valid_of_data_empty _ rfl
    · change SphincsImages.verify.byteSize < MAX_IMAGE_BYTES
      rw [verify_byteSize]
      decide
    · exact layout_valid_of_data_empty _ rfl

end SigGolfCandidate.SphincsSubmission
