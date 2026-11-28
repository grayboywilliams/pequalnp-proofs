import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53237 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4500 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.not, [7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [5, 10]⟩], 11⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
