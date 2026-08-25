  exact (cancel_epi (coendSliceMidToWedge F c d d' f)).mp h

@[reassoc (attr := simp)]
theorem coendSliceOpCovIso_sec [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    EndKan.Coend.ι F (c, d) =
      coendSliceOpCovIso F c d d' f ≫ EndKan.Coend.ι F (c, d') := by
  exact (coendSliceOpCovIso_post_ι F c d d' f).symm

theorem eqToHom_symm_post_coendι (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) (c : C)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    eqToHom (coendSlice_obj F d c).symm ≫ eqToHom (coendSlice_obj F d c) ≫
        EndKan.Coend.ι F (c, d) =
      EndKan.Coend.ι F (c, d) := by
  dsimp [eqToIso.inv, eqToIso.hom]
  exact (eqToIso (coendSlice_obj F d c)).inv_hom_id_assoc (EndKan.Coend.ι F (c, d))

@[reassoc (attr := simp)]
theorem coendSliceOpCovToSlice_post_ι [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    coendSliceOpCovToSlice F c f ≫ eqToHom (coendSlice_obj F d' c) ≫ EndKan.Coend.ι F (c, d') =
      eqToHom (coendSlice_obj F d c) ≫ EndKan.Coend.ι F (c, d) := by
  rw [coendSliceOpCovToSlice_eq_opCovIso F c f]
  refine (cancel_epi (eqToHom (coendSlice_obj F d c))).mp ?_
  rw [← Category.assoc, ← Category.assoc, ← coendSliceOpCovIso_post_ι F c d d' f]
  simp only [eqToIso.inv, eqToIso.hom, eqToHom_trans, eqToHom_refl, Category.id_comp,
    Category.comp_id, Category.assoc]

@[reassoc]
theorem coendSliceOpCovToSlice_post_ι_wedge [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    coendSliceOpCovToSlice F c f ≫ eqToHom (coendSlice_obj F d' c) ≫ EndKan.Coend.ι F (c, d') =
      eqToHom (coendSlice_obj F d c) ≫ EndKan.Coend.ι F (c, d) :=
  coendSliceOpCovToSlice_post_ι F c d d' f

end sliceIsoLemmas
