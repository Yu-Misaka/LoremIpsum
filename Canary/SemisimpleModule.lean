import Mathlib.RingTheory.SimpleModule.Basic

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {r : ℕ}
  -- each `N i` is a submodule of `M`
  (N : Fin r → Submodule R M)
  -- the intersection of `N i` is trivial
  (hN : ⨅ i, N i = ⊥)

open DirectSum

/-- defining `f` that takes `x` to `(x + N₁, ..., x + Nᵣ)` -/
def f : M →ₗ[R] (⨁ i, (M ⧸ (N i))) where
  -- every coordinate of the direct sum is `x + Nᵢ`
  toFun x := (mk (fun i ↦ M ⧸ N i) Finset.univ).toFun (fun i ↦ (⟦x⟧ : M ⧸ N i))
  -- proving that the map respect addition
  map_add' x y := by
    ext i
    simp
    convert_to (⟦x + y⟧ : M ⧸ N i) =
      @HAdd.hAdd (M ⧸ N i) (M ⧸ N i) (M ⧸ N i) instHAdd ⟦x⟧ ⟦y⟧
    · exact mk_apply_of_mem <| Finset.mem_univ i
    · congr <;> exact mk_apply_of_mem <| Finset.mem_univ i
    · rfl
  -- proving that the map respect scalar multiplication
  map_smul' c x := by
    ext i
    simp [smul_apply]
    convert_to (⟦c • x⟧ : M ⧸ N i) =
      @HSMul.hSMul R (M ⧸ N i) (M ⧸ N i) instHSMul c ⟦x⟧
    · exact mk_apply_of_mem <| Finset.mem_univ i
    · congr; exact mk_apply_of_mem <| Finset.mem_univ i
    · rfl

include hN in
/-- the kernel of `f` is trivial -/
lemma ker_f : LinearMap.ker (f N) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun m hm ↦ ?_
  -- given `m` in the kernel
  dsimp [f] at hm
  rw [DirectSum.ext_iff] at hm
  replace hm : ∀ i, (⟦m⟧ : M ⧸ N i) = (0 : M ⧸ N i) := by
    intro i
    convert hm i
    exact Eq.symm (mk_apply_of_mem <| Finset.mem_univ i)
  -- it must be in the intersection of `Nᵢ`
  have : m ∈ ⨅ i, N i :=
    (Submodule.mem_iInf N).2 fun i ↦
      (Submodule.Quotient.mk_eq_zero (N i)).mp (hm i)
  rwa [hN, Submodule.mem_bot] at this

include hN in
/-- `M` is semisimple iff for all `i`, `M ⧸ N i` is semisimple -/
lemma IsSemisimple_iff_quotient :
    IsSemisimpleModule R M ↔ ∀ i, IsSemisimpleModule R (M ⧸ (N i)) := by
  constructor
  · -- the quotient of semisimple module is semisimple
    exact fun _ _ ↦ IsSemisimpleModule.quotient
  · intro _
    -- the finite direct sum of semisimple module is semisimple
    let _ : IsSemisimpleModule R (⨁ i, (M ⧸ (N i))) :=
      instIsSemisimpleModuleDFinsupp fun i ↦ M ⧸ N i
    exact IsSemisimpleModule.congr <|
      (Submodule.quotEquivOfEqBot (LinearMap.ker (f N)) (ker_f N hN)).symm.trans
      (LinearMap.quotKerEquivRange (f N))
