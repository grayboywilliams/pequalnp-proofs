import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53227 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (461 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.not, [7]⟩, ⟨.and, [6, 8]⟩], 9⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
