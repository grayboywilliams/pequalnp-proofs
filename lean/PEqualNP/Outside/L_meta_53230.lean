import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53230 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (924 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [4, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [6, 1]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [8, 6]⟩], 11⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
