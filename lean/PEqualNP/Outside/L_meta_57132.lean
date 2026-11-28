import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57132 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2182335 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.not, [5]⟩, ⟨.not, [7]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [6, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [9, 15]⟩, ⟨.or, [14, 16]⟩], 17⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
