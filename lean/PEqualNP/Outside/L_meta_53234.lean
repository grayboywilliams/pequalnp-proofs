import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53234 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4297 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [0]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.not, [10]⟩], 11⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
