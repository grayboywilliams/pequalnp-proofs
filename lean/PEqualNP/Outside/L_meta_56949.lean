import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_56949 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180539 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.not, [6]⟩, ⟨.and, [3, 7]⟩, ⟨.not, [7]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [12, 15]⟩, ⟨.not, [16]⟩], 17⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
