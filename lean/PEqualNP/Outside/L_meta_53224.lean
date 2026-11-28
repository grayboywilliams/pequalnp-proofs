import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53224 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (221 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 0]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩], 10⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
