import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57091 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181041 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [0, 8]⟩, ⟨.not, [8]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [7, 11]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [5, 14]⟩, ⟨.not, [15]⟩, ⟨.or, [12, 16]⟩], 17⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
