import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53221 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (203 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [1]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [6, 10]⟩], 11⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
