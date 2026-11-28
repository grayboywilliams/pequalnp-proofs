import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53229 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (476 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.not, [5]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 10]⟩], 11⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
