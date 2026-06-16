import EndKan.Fubini.Slice

/-!
Lake-built smoke target for the slice iso bootstrap harness.
The full mutual-iso experiment lives in `scratch/SliceIsoMin.lean` (compile via `lake env lean scratch/SliceIsoMin.lean`).
-/

namespace Scratch.SliceIsoMin

#check @EndKan.Fubini.endSlice_cov_contr
#check @EndKan.Fubini.endSliceOpCovIso_comp_contr
#check @EndKan.Fubini.endSliceContrMap_hom_inv
#check @EndKan.Fubini.endSliceCov_hom_inv
#check @EndKan.Fubini.endSliceCov_inv_hom
#check @EndKan.Fubini.endSliceOpCovIso_isIso
#check @EndKan.Fubini.endSliceContrIsoFromData
#check @EndKan.Fubini.allEndSliceContrIsoOfData
#check @EndKan.Fubini.instEndSliceContrIsIso

end Scratch.SliceIsoMin
