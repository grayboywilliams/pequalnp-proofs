import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53225 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (222 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.not, [5]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [8, 9]⟩], 10⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
