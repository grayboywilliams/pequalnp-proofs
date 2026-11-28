import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53265 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275159 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.not, [3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [5, 6]⟩, ⟨.not, [7]⟩, ⟨.or, [8, 9]⟩], 10⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
