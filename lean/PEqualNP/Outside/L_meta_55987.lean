import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_55987
namespace Wide
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 256
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
lemma testBit_bin (d a b r : Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r := by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b : Nat) (ha : a < 2^256) (hb : b < 2^256) : bin d a b < 2^256 := by
  have h1 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x &&& y) < 2^256 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ||| y) < 2^256 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ^^^ y) < 2^256 := fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
lemma bin_bit0 (d a b : Nat) (ha : a.testBit 0 = false) (hb : b.testBit 0 = false) :
    (bin d a b).testBit 0 = false := by
  rw [testBit_bin]
  rcases d with _ | _ | _ | d <;> simp [ha, hb]
def Live (T : Nat) : Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U : Finset Nat) (a b d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩ := h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_sep {T k S} (h : Live T k S) {r s : Nat} (hd : T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩ := h
    obtain ⟨v, hv, hvd⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire := Bool × Nat
def swZero : SWire := (false, 0)
def swFlip (a : SWire) : SWire := (!a.1, a.2)
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def swMeet (a b : SWire) : SWire := (a.1 && b.1, bin (opIdx a.1 b.1) a.2 b.2)
def swJoin (a b : SWire) : SWire := swFlip (swMeet (swFlip a) (swFlip b))
def swRead (j : Nat) (a : SWire) : Bool := a.1 != a.2.testBit j
lemma swRead_zero (j : Nat) : swRead j swZero = false := by simp [swRead, swZero]
lemma swRead_flip (j : Nat) (a : SWire) : swRead j (swFlip a) = !(swRead j a) := by
  cases a with | mk s v => cases s <;> cases h : v.testBit j <;> simp [swRead, swFlip, h]
lemma swRead_meet (j : Nat) (a b : SWire) : swRead j (swMeet a b) = (swRead j a && swRead j b) := by
  obtain ⟨s, u⟩ := a; obtain ⟨t, v⟩ := b
  cases s <;> cases t <;> cases hu : u.testBit j <;> cases hv : v.testBit j <;>
    simp [swRead, swMeet, opIdx, testBit_bin, hu, hv]
lemma swRead_join (j : Nat) (a b : SWire) : swRead j (swJoin a b) = (swRead j a || swRead j b) := by
  simp only [swJoin, swRead_flip, swRead_meet]
  cases swRead j a <;> cases swRead j b <;> rfl
def swGate (w : List SWire) (g : Gate) : SWire :=
  let arg := fun i => w.getD i swZero
  match g.op, g.inputs with
  | .not, xs => swFlip (arg (xs.headD w.length))
  | .and, [] => swFlip swZero
  | .or, [] => swZero
  | .and, [i] | .or, [i] => arg i
  | .and, i :: j :: _ => swMeet (arg i) (arg j)
  | .or, i :: j :: _ => swJoin (arg i) (arg j)
  | _, _ => swZero
def swExec (gs : List Gate) (w : List SWire) : List SWire :=
  gs.foldl (fun w g => w ++ [swGate w g]) w
def isBin (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma get_simple (w : List SWire) (i : Nat) : simple w (w.getD i swZero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a, List.mem_of_getElem? eq, rfl⟩)
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
lemma swGate_priced (w : List SWire) (g : Gate) : priced w (isBin g) (swGate w g).2 := by
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | not => exact Or.inl (get_simple w _)
  | _ => exact Or.inl (Or.inl rfl)
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^256 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^256 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^256 ∧ (w.getD i swZero).2.testBit 0 = false := by
    simp only [List.getD_eq_getElem?_getD]
    cases eq : w[i]? with
    | none => exact hz
    | some a => exact hw a (List.mem_of_getElem? eq)
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | not => exact hg (xs.headD w.length)
  | _ => exact hz
lemma swExec_lt (gs : List Gate) (w : List SWire)
    (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hw u hu
    · rw [List.mem_singleton.mp hu]; exact swGate_lt w hw g
lemma swRead_get (j : Nat) (w : List SWire) (i : Nat) :
    (w.map (swRead j)).getD i false = swRead j (w.getD i swZero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [swRead_zero]
lemma swGate_read (w : List SWire) (g : Gate)
    (legal : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (j : Nat) :
    swRead j (swGate w g) = g.op.eval (g.inputs.map fun i => (w.map (swRead j)).getD i false) := by
  simp_rw [swRead_get]
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, hlen⟩ := legal
  rcases hop with rfl | rfl | rfl <;>
    rcases xs with _ | ⟨i, _ | ⟨k, _ | ⟨h, rest⟩⟩⟩ <;>
    simp_all [swGate, GateOp.eval, swRead_flip, swRead_meet, swRead_join, swRead_zero]
lemma swExec_read (j : Nat) (gs : List Gate) (w : List SWire)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (swExec gs w).map (swRead j) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (swRead j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (swExec gs (w ++ [swGate w g])).map (swRead j) = _
    rw [ih _ (fun v hv => legal v (List.mem_cons_of_mem _ hv))]
    simp [swGate_read w g (legal g List.mem_cons_self) j]
lemma pull_live {T k S w z p} (h : Live T k S) (op : priced w p z)
    (sub : ∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w := by
  by_cases needed : z ∈ S
  · by_cases avail : z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U := S.erase (bin d a b)
        have tail : Live T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase needed] using h
        have old (x : Nat) (hx : x ∈ U) : x ∈ reps w := by
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hx
          exact (by simpa using sub x mem : x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
lemma extract_live {T} (hT : T ≠ 0) (gs : List Gate) (w : List SWire)
    (found : T ∈ reps (swExec gs w)) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0, {T}, by simp, ⟨rfl, hT⟩, by simpa [swExec] using found⟩
  | cons g gs ih =>
    obtain ⟨k, S, lim, h, sub⟩ := ih (w ++ [swGate w g]) found
    have sub' : ∀ a ∈ S, a ∈ reps w ++ [(swGate w g).2] := by simpa [reps] using sub
    obtain ⟨l, V, cost, hl, raw⟩ := pull_live h (swGate_priced w g) sub'
    refine ⟨l, V, ?_, hl, raw⟩
    rw [List.countP_cons]
    cases e : isBin g <;> simp [e] at cost ⊢ <;> omega
def invW (a : Wire) : Wire := fun r => !(a r)
def comb2 (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d : Nat) (a b : Wire) : Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def wcost (a : Wire) : Nat := by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs : List Wire) : Nat := (xs.map wcost).sum
def Avail (pool : List Wire) (v : Wire) : Prop := v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs : List Wire) : Prop := ∀ a ∈ xs, Avail pool a
def Reach (roots : List Wire) : Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List Wire) (a b : Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run (goal : Wire) : Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire) (rest : List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a : Wire) : invW (invW a) = a := by funext r; simp [invW]
lemma invW_const {a : Wire} (h : Constant a) : Constant (invW a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
lemma wcost_inv (a : Wire) : wcost (invW a) = wcost a := by
  have h : Constant (invW a) ↔ Constant a := ⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc : Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank : List Wire} {a : Wire} (h : Avail bank a) : Avail bank (invW a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank : List Wire} {v : Wire} (w : Wire) (h : Avail bank v) : Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op : Bool) {a b : Wire} {bank : List Wire} (h : Constant a ∨ Constant b)
    (ha : Avail bank a) (hb : Avail bank b) : Avail bank (comb2 op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op : Bool) {a b : Wire} (ha : Constant a) (hb : Constant b) :
    Constant (comb2 op a b) := by
  obtain ⟨v, rfl⟩ := ha; obtain ⟨w, rfl⟩ := hb; cases op <;> exact ⟨_, rfl⟩
lemma extend_comb (roots : List Wire) {p bank a b} (d : Nat) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Avail bank a) (hb : Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b) := by
  have hprep : ∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b := by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩ := hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c : Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx : Constant x <;> by_cases hcy : Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx : ¬Constant x := fun h => c (Or.inl h)
    have hcy : ¬Constant y := fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a : Wire) (xs : List Wire) (k : Bool) : wmass xs ≤ wmass (kept k a xs) := by
  cases k <;> simp [kept, wmass]
lemma contraction {goal : Wire} (nc : ¬Constant goal) {s ws} (h : Run goal s ws)
    (roots : List Wire) {p bank} (hp : Reach roots p bank) (hs : Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s := by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem : goal ∈ ws := h.mem_iff.mp (by simp)
    have hlen : wmass ws = wcost goal := by
      have := (h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have hsa : Avail bank a := hs a (perm.mem_iff.mp (by simp))
    have hsb : Avail bank b := hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp hsa hsb
    have ht : Supply T (comb4 op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩ := ih tail hT ht
    have hm1 := wmass_kept a (kept kb b rest) ka
    have hm2 := wmass_kept b rest kb
    have hp_eq : wmass ws = wcost a + wcost b + wmass rest := by
      have := (perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons : wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)) := rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)
lemma restrict_run (f : Row → Row) {goal s ws} (h : Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have htail := ih tail
    have hk : ∀ (k : Bool) (x : Wire) (l : List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)) := by
      intro k x l; cases k <;> rfl
    have hc : restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b) := by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a : Nat) : Wire := fun r => a.testBit r.val
lemma obs_bin (d a b : Nat) : obs (bin d a b) = comb4 d (obs a) (obs b) := by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α : Type} (c : Bool) (x : α) (l : List α) (hl : l.Nodup) (hx : x ∉ l) :
    (kept c x l).Nodup := by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h : Live T k S) (v : List Nat) (nd : v.Nodup) (eqv : v.toFinset = S) :
    Run (obs T) k (v.map obs) := by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hp : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩ := h
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tl := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm : mid.Nodup := kept_nodup kb b rest hr br
    have am : a ∉ mid := by cases hkb : kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl : tl.Nodup := kept_nodup ka a mid bm am
    have htl : tl.toFinset = U := by
      have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha' : a ∈ U <;> by_cases hb' : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;>
        simp_all [ka, kb]
    have hf : bin d a b ∉ tl := fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog := ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk : ∀ (c : Bool) (x : Nat) (l : List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs) := by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f : Wire) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).toNat
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 256 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 256 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^256) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
  · simp only [hr, dite_true]
    cases op <;> cases ha0 : a 0 <;> cases hb0 : b 0 <;>
      cases har : a ⟨r, hr⟩ <;> cases hbr : b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank : List Wire} {v : Wire} (h : Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack := by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
set_option maxRecDepth 16000 in
lemma reach_to_live_sub {roots : List Wire} {p bank} (h : Reach roots p bank)
    {T k S} (run : Live T k S) (sub : ∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack := by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩ := h
    obtain ⟨d, hd, eq⟩ := normPack_comb2 op a b
    let w := prev.map (fun f => (false, normPack f))
    have hreps : reps w = prev.map normPack := by simp [w, reps, List.map_map, Function.comp_def]
    have hp : priced w true (normPack (comb2 op a b)) := by
      rw [eq]
      exact made_priced w d (false, normPack a) (false, normPack b) hd
        (by simpa [simple, hreps] using avail_normPack ha)
        (by simpa [simple, hreps] using avail_normPack hb)
    have hsub' : ∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)] := by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩ := pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩ := ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (255 ^^^ z)) ||| o) % 256, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma wmass_append (a b : List Wire) : wmass (a ++ b) = wmass a + wmass b := by simp [wmass]
lemma wmass_consts (xs : List Wire) (hc : ∀ x ∈ xs, Constant x) : wmass xs = xs.length := by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have := ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^256) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
    intro v hv
    obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo := prior q next hq (gc ▸ hav)
  have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
    simp only [front, List.map_append, wmass_append]
    let xs := (singles.toList.map obs).map (restrictW f)
    have hc : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen := wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have := hbound
  omega
def VAR (i : Nat) : Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | 7 => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | _ => 0
def ALL256 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def varsOf (m : Nat) : List Nat :=
  (List.range 8).filterMap fun i => if m.testBit i then some (VAR i) else none
def fixWord (z o w : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    let fr := ((r &&& (255 ^^^ z)) ||| o) % 256
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p : Nat → Bool) (l : List Nat) (r : Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra : r = a
      · subst hra; simp [hpa]
      · have h1 : (decide (a ≤ r) && (1 : Nat).testBit (r - a)) = false := by
          by_cases hle : a ≤ r
          · have hpos : r - a ≠ 0 := by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra : r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w : Nat) : fixWord z o w = renameW (fixRow z o) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 256
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 256) && decide (s < 256) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL256 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL256]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 256 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^256) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^256 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^256) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^256 ∧ a.testBit 0 = false := by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL256))
lemma lift_of {z o roots T other G essPairs L} (ok : liftCheck z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G := (fixWord_eq_renameW z o T).symm.trans heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [Bool.or_eq_true, beq_iff_eq, fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL256]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 256 r'.val |> fun e => by simpa [this] using e⟩
def evalInput (r : Row) : Fin 8 → Bool := fun i => r.val.testBit i.val
def packInput (x : Fin 8 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat + 128 * (x 7).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    have h6 := Bool.toNat_le (x 6); have h7 := Bool.toNat_le (x 7); omega⟩
lemma evalInput_packInput (x : Fin 8 → Bool) : evalInput (packInput x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (j : Fin 8),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat + 64 * b6.toNat + 128 * b7.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5, b6, b7].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) i
  fin_cases i <;> simpa [evalInput, packInput] using hi
lemma var_testBit (i : Fin 8) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 255 := by
  let seeds : List SWire := (varsOf 255).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 255).all (fun a => decide (a < 2^256) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^256 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi7 : i < 8 := by simpa using hi2
      have hv : (varsOf 255)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 255)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit ⟨i, hi7⟩ r
  have hev (r : Row) : swRead r.val out = T.testBit r.val := by
    have h1 := (swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0 : out.1 = false := by
    have h0 := hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2 : out.2 = T := by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · have h := hev ⟨r, hr⟩
      simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]
    exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma replace_of_lower (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 255) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : ∀ g ∈ wit, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (edgeFn : (Fin 8 → Bool) → Bool)
    (hEdgeT : ∀ r : Row, edgeFn (evalInput r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = T.testBit r.val)
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (spec : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x := by
  have hwEval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = edgeFn x := by
    intro x
    have hx := evalInput_packInput x
    rw [← hx]
    exact (hwEvalR (packInput x)).trans (hEdgeT (packInput x)).symm
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hlt : gates.countP isBin < gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full T hT0 hTlt hTb0 gates o legal (fun r => (spec (evalInput r)).trans (hEdgeT r))
    have hnd : S.toList.Nodup := Finset.nodup_toList S
    have hrun := live_to_run hlive S.toList hnd (by simp)
    have hsup : Supply ((varsOf 255).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 255).map obs)
        (show Reach ((varsOf 255).map obs) 0 ((varsOf 255).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    refine ⟨wit, wo, hwMono, by omega, hwEval⟩
  · refine ⟨gates, o, ?_, le_rfl, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim

end Wide
namespace Small
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 128
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def flipOp (d : Nat) : Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d
lemma bin_comm_flip (d : Nat) (hd : d < 4) (a b : Nat) : bin d a b = bin (flipOp d) b a := by
  interval_cases d <;> simp [bin, flipOp, Nat.and_comm, Nat.or_comm]
lemma flipOp_lt {d : Nat} (hd : d < 4) : flipOp d < 4 := by
  interval_cases d <;> decide
lemma testBit_bin (d a b r : Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r := by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b : Nat) (ha : a < 2^128) (hb : b < 2^128) : bin d a b < 2^128 := by
  have h1 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x &&& y) < 2^128 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ||| y) < 2^128 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ^^^ y) < 2^128 := fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
def Live (T : Nat) : Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U : Finset Nat) (a b d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩ := h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_size {T k S} (h : Live T k S) : S.card ≤ k + 1 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; simp
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, hf, tail⟩ := h
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have ht := ih tail
    rw [Finset.card_insert_of_notMem hu] at ht
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega
lemma live_sep {T k S} (h : Live T k S) {r s : Nat} (hd : T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩ := h
    obtain ⟨v, hv, hvd⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire := Bool × Nat
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
lemma pull_live {T k S w z p} (h : Live T k S) (op : priced w p z)
    (sub : ∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w := by
  by_cases needed : z ∈ S
  · by_cases avail : z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U := S.erase (bin d a b)
        have tail : Live T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase needed] using h
        have old (x : Nat) (hx : x ∈ U) : x ∈ reps w := by
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hx
          exact (by simpa using sub x mem : x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
def invW (a : Wire) : Wire := fun r => !(a r)
def comb2 (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d : Nat) (a b : Wire) : Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def wcost (a : Wire) : Nat := by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs : List Wire) : Nat := (xs.map wcost).sum
def Avail (pool : List Wire) (v : Wire) : Prop := v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs : List Wire) : Prop := ∀ a ∈ xs, Avail pool a
def Reach (roots : List Wire) : Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List Wire) (a b : Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run (goal : Wire) : Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire) (rest : List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a : Wire) : invW (invW a) = a := by funext r; simp [invW]
lemma invW_const {a : Wire} (h : Constant a) : Constant (invW a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
lemma wcost_inv (a : Wire) : wcost (invW a) = wcost a := by
  have h : Constant (invW a) ↔ Constant a := ⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc : Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank : List Wire} {a : Wire} (h : Avail bank a) : Avail bank (invW a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank : List Wire} {v : Wire} (w : Wire) (h : Avail bank v) : Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op : Bool) {a b : Wire} {bank : List Wire} (h : Constant a ∨ Constant b)
    (ha : Avail bank a) (hb : Avail bank b) : Avail bank (comb2 op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op : Bool) {a b : Wire} (ha : Constant a) (hb : Constant b) :
    Constant (comb2 op a b) := by
  obtain ⟨v, rfl⟩ := ha; obtain ⟨w, rfl⟩ := hb; cases op <;> exact ⟨_, rfl⟩
lemma extend_comb (roots : List Wire) {p bank a b} (d : Nat) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Avail bank a) (hb : Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b) := by
  have hprep : ∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b := by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩ := hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c : Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx : Constant x <;> by_cases hcy : Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx : ¬Constant x := fun h => c (Or.inl h)
    have hcy : ¬Constant y := fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a : Wire) (xs : List Wire) (k : Bool) : wmass xs ≤ wmass (kept k a xs) := by
  cases k <;> simp [kept, wmass]
lemma contraction {goal : Wire} (nc : ¬Constant goal) {s ws} (h : Run goal s ws)
    (roots : List Wire) {p bank} (hp : Reach roots p bank) (hs : Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s := by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem : goal ∈ ws := h.mem_iff.mp (by simp)
    have hlen : wmass ws = wcost goal := by
      have := (h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have hsa : Avail bank a := hs a (perm.mem_iff.mp (by simp))
    have hsb : Avail bank b := hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp hsa hsb
    have ht : Supply T (comb4 op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩ := ih tail hT ht
    have hm1 := wmass_kept a (kept kb b rest) ka
    have hm2 := wmass_kept b rest kb
    have hp_eq : wmass ws = wcost a + wcost b + wmass rest := by
      have := (perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons : wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)) := rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)
lemma restrict_run (f : Row → Row) {goal s ws} (h : Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have htail := ih tail
    have hk : ∀ (k : Bool) (x : Wire) (l : List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)) := by
      intro k x l; cases k <;> rfl
    have hc : restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b) := by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a : Nat) : Wire := fun r => a.testBit r.val
lemma obs_bin (d a b : Nat) : obs (bin d a b) = comb4 d (obs a) (obs b) := by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α : Type} (c : Bool) (x : α) (l : List α) (hl : l.Nodup) (hx : x ∉ l) :
    (kept c x l).Nodup := by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h : Live T k S) (v : List Nat) (nd : v.Nodup) (eqv : v.toFinset = S) :
    Run (obs T) k (v.map obs) := by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hp : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩ := h
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tl := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm : mid.Nodup := kept_nodup kb b rest hr br
    have am : a ∉ mid := by cases hkb : kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl : tl.Nodup := kept_nodup ka a mid bm am
    have htl : tl.toFinset = U := by
      have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha' : a ∈ U <;> by_cases hb' : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;>
        simp_all [ka, kb]
    have hf : bin d a b ∉ tl := fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog := ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk : ∀ (c : Bool) (x : Nat) (l : List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs) := by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f : Wire) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).toNat
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 128 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 128 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^128) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true]
    cases op <;> cases ha0 : a 0 <;> cases hb0 : b 0 <;>
      cases har : a ⟨r, hr⟩ <;> cases hbr : b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank : List Wire} {v : Wire} (h : Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack := by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
lemma reach_to_live_sub {roots : List Wire} {p bank} (h : Reach roots p bank)
    {T k S} (run : Live T k S) (sub : ∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack := by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩ := h
    obtain ⟨d, hd, eq⟩ := normPack_comb2 op a b
    let w := prev.map (fun f => (false, normPack f))
    have hreps : reps w = prev.map normPack := by simp [w, reps, List.map_map, Function.comp_def]
    have hp : priced w true (normPack (comb2 op a b)) := by
      rw [eq]
      exact made_priced w d (false, normPack a) (false, normPack b) hd
        (by simpa [simple, hreps] using avail_normPack ha)
        (by simpa [simple, hreps] using avail_normPack hb)
    have hsub' : ∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)] := by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩ := pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩ := ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Impossible (T : Nat) (cap : Nat) (S : Finset Nat) : Prop :=
  ∀ k ≤ cap, ¬Live T k S
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma lower_of_impossible {roots : List Nat} {T L : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (ess : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L + 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hnz : normPack (obs T) ≠ 0 := by rwa [hnormT]
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left hnz
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha'
    exact normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have heq : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    exact ⟨fun ha' => raw_required run roots a sub (ess a ha'), sub a⟩
  by_contra! small
  exact noRun k (by omega) (heq.symm ▸ run)
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def Slice (raw : List Nat) (T d : Nat) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Nat),
    (∀ r : Row, d.testBit (f r).val = true) ∧
    (∀ a ∈ raw, Avail (roots.map obs) (restrictW f (obs a))) ∧
    ¬Constant (restrictW f (obs T)) ∧
    ∀ p bank, Reach (roots.map obs) p bank → Avail bank (restrictW f (obs T)) → L ≤ p
def isConstM (d a : Nat) : Bool := (a &&& d == 0) || (a &&& d == d)
def availM (d : Nat) (pm : List Nat) (a : Nat) : Bool :=
  let m := a &&& d
  m == 0 || m == d || pm.contains m || pm.contains (d ^^^ m)
lemma masked_eq_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (b &&& d)) : restrictW f (obs a) = restrictW f (obs b) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_zero_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = 0) : restrictW f (obs a) = fun _ => false := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_one_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = d) : restrictW f (obs a) = fun _ => true := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_comp_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (d ^^^ (b &&& d))) : restrictW f (obs a) = invW (restrictW f (obs b)) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simp only [Nat.testBit_and, Nat.testBit_xor, dom r, Bool.and_true] at h
  simp only [restrictW, obs, invW, h]
  cases b.testBit (f r).val <;> rfl
def poolSupply (f : Row → Row) (bank : List Wire) (pool : List Nat) : Prop :=
  ∀ a ∈ pool, Avail bank (restrictW f (obs a))
lemma availM_sound {f : Row → Row} {d a : Nat} {bank : List Wire} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hs : poolSupply f bank pool)
    (ok : availM d (pool.map (· &&& d)) a = true) :
    Avail bank (restrictW f (obs a)) := by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq, List.mem_map] at ok
  rcases ok with ((h0 | h1) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero_obs dom h0⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one_obs dom h1⟩)
  · exact (masked_eq_obs dom he.symm) ▸ hs v hv
  · have hinv := avail_inv (hs v hv)
    have hcomp : restrictW f (obs a) = invW (restrictW f (obs v)) := by
      have hx : (a &&& d) = d ^^^ (v &&& d) := by
        have := congrArg (d ^^^ ·) he
        simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_self] using this.symm
      exact masked_comp_obs dom hx
    exact hcomp ▸ hinv
abbrev Choice := Nat × Nat × Nat
def choiceVal (c : Choice) : Nat := bin c.1 c.2.1 c.2.2
def choiceOK (d : Nat) (pm : List Nat) (c : Choice) : Bool :=
  decide (c.1 < 4) && availM d pm c.2.1 && availM d pm c.2.2
def makePool (d : Nat) (pool : List Nat) : List Choice → Option (List Nat)
  | [] => some pool
  | c :: cs => if choiceOK d (pool.map (· &&& d)) c then makePool d (choiceVal c :: pool) cs else none
lemma pay_choice {f : Row → Row} {d : Nat} {roots bank q} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d (pool.map (· &&& d)) c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  have ha := availM_sound dom hs valid.1.2
  have hb := availM_sound dom hs valid.2
  have hprep : ∃ op x y, comb4 c.1 (restrictW f (obs c.2.1)) (restrictW f (obs c.2.2)) = comb2 op x y ∧
      Avail bank x ∧ Avail bank y := by
    have hd := valid.1.1
    interval_cases c.1
    · exact ⟨false, _, _, rfl, ha, hb⟩
    · exact ⟨true, _, _, rfl, ha, hb⟩
    · exact ⟨false, _, _, rfl, ha, avail_inv hb⟩
    · exact ⟨false, _, _, rfl, avail_inv ha, hb⟩
  obtain ⟨op, x, y, eq, hx, hy⟩ := hprep
  refine ⟨comb2 op x y :: bank, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · have hcv : restrictW f (obs (choiceVal c)) = comb2 op x y := by
      rw [← eq]; funext r; simp only [choiceVal, restrictW, obs, testBit_bin, comb4, comb2, invW]
      rcases c.1 with _ | _ | _ | d' <;> rfl
    exact hcv ▸ Or.inl (by simp)
  · exact avail_cons _ (hs v hv)
lemma makePool_sound {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {res} (ok : makePool d pool cs = some res) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next res := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction
lemma count_constM {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (ws : List Nat) : ws.countP (isConstM d) ≤ wmass ((ws.map obs).map (restrictW f)) := by
  classical
  induction ws with
  | nil => simp [wmass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, wmass, List.sum_cons] at ih ⊢
    cases h : isConstM d a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih.trans (Nat.le_add_left _ _)
    · have hc : Constant (restrictW f (obs a)) := by
        simp only [isConstM, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h0 | h1
        · exact ⟨false, masked_zero_obs dom h0⟩
        · exact ⟨true, masked_one_obs dom h1⟩
      simp only [ite_true, wcost, hc]
      omega
structure BoundPool where
  dom : Nat
  lb : Nat
  paid : Nat
  wires : List Nat
  pm : List Nat
def ValidPool (_raw : List Nat) (T : Nat) (c : BoundPool) : Prop :=
  c.pm = c.wires.map (· &&& c.dom) ∧
  ∃ (f : Row → Row) (roots : List Nat) (bank : List Wire),
    (∀ r : Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw : List Nat) (cs : List Choice) (d lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map fun pool => ⟨d, lb, cs.length, pool, pool.map (· &&& d)⟩
lemma materialize_sound {raw T d L cs c} (sl : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩ := sl
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨rfl, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let z := choiceVal op
  let extra := !(availM c.dom c.pm z)
  decide (k + c.paid + extra.toNat < c.lb + (z :: rest).countP (isConstM c.dom)) &&
    rest.all (availM c.dom c.pm) && (!extra || choiceOK c.dom c.pm op)
lemma scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  obtain ⟨hpm, f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  intro t ht run
  have finish (n : Nat) (out : List Wire) (hr : Reach (roots.map obs) n out)
      (hsup : poolSupply f out (choiceVal op :: rest))
      (hle : n = c.paid + (!(availM c.dom c.pm (choiceVal op))).toNat) : False := by
    have hcov : Supply out (((choiceVal op :: rest).map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact hsup a ha
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction nc (restrict_run f (live_to_run run (choiceVal op :: rest) nd rfl)) (roots.map obs) hr hcov
    have hlo := lo q next hq hav
    have hcm := count_constM dom (choiceVal op :: rest)
    have hineq := cut.1.1
    omega
  cases hav : availM c.dom c.pm (choiceVal op) with
  | true =>
    apply finish c.paid bank hp _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact availM_sound dom hs (hpm ▸ hav)
    · exact availM_sound dom hs (hpm ▸ cut.1.2 a ha)
  | false =>
    have hok : choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true := by
      have h2 := cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      exact hpm ▸ h2
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt : poolSupply f out c.wires := fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (hpm ▸ cut.1.2 a ha)
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (127 ^^^ z)) ||| o) % 128, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 128
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 128 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^128) (hb : b < 2^128) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 128 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^128) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^128 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^128 := hS a (by simp)
    have hblt : b < 2^128 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^128 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^128 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^128 := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact hzlt; exact hUlt x hx
    have nr := ih tail htail_lt
    simp only [Finset.image_insert, renameW_bin] at nr ⊢
    refine ⟨U.image (renameW f), renameW f a, renameW f b, d, hd, rfl,
      fun hz => ha (renameW_inj f onto halt (by decide) (hz.trans (renameW_zero f).symm)),
      fun hz => hb (renameW_inj f onto hblt (by decide) (hz.trans (renameW_zero f).symm)),
      fun heq => hab (renameW_inj f onto halt hblt heq), ?_, nr⟩
    intro hm
    rw [← renameW_bin] at hm
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt halt heq]; simp)
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt hblt heq]; simp)
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
    exact fresh (by rw [renameW_inj f onto hzlt (hUlt x hx) heq.symm]; simp [hx])
lemma wmass_append (a b : List Wire) : wmass (a ++ b) = wmass a + wmass b := by simp [wmass]
lemma wmass_consts (xs : List Wire) (hc : ∀ x ∈ xs, Constant x) : wmass xs = xs.length := by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have := ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^128) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
    intro v hv
    obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo := prior q next hq (gc ▸ hav)
  have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
    simp only [front, List.map_append, wmass_append]
    let xs := (singles.toList.map obs).map (restrictW f)
    have hc : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen := wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have := hbound
  omega
def VAR (i : Nat) : Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000
  | _ => 0
def ALL128 : Nat := 0xffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 128, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL128 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 7) (hj : j < 7) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 7 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL128 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
  | true =>
    obtain ⟨heq, h10, h01⟩ := hr.1 hms
    rw [heq]
    by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
    · simp [hd, h10 hd, h01]
    · simp [hd, h01]
  | false =>
    rcases hr.2 hms with ⟨hd, h10, heq, h01⟩ | ⟨h10, h01, heq⟩
    · simp [hd, h10, heq, h01]
    · by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
      · simp [hd, h10 hd, h01, heq]
      · simp [hd, h01, heq]
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) : swapWord i j w < 2^128 := by
  have hi : i < 7 := by omega
  have h1 : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^128 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^128 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^128 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 7)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^128) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^128 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hr⟩, testBit_renameW _ _ (swapRow p.1 p.2 ⟨r, hr⟩), testBit_renameW _ _ ⟨r, hr⟩]
      rfl
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega)))]
lemma permRow_surj (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) :
    Function.Surjective (permRow swaps) := by
  induction swaps with
  | nil => intro r; exact ⟨r, rfl⟩
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro r
    obtain ⟨q, hq⟩ := ih hv.2 r
    refine ⟨swapRow p.1 p.2 q, ?_⟩
    change permRow ps (swapRow p.1 p.2 (swapRow p.1 p.2 q)) = r
    rw [swapRow_invol p.1 p.2 (by omega) hv.1.2, hq]
lemma permRow_rev_cancel (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) (r : Row) :
    permRow swaps.reverse (permRow swaps r) = r := by
  induction swaps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
        swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
      simp [permRow, List.reverse_cons, List.foldl_append]
    rw [h1, ih hv.2, swapRow_invol p.1 p.2 (by omega) hv.1.2]
lemma rotate_impossible {T n : Nat} {ws : List Nat} (hi : Impossible T n ws.toFinset)
    (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (hT : T < 2^128) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^128) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^128 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^128 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
  have run' := live_renameW run hr (permRow swaps.reverse) (permRow_surj swaps.reverse hvr)
  have hT' : renameW (permRow swaps.reverse) T = T := by
    conv_lhs => rw [← hfix]
    exact hinv_word T hT
  have hS' : (ws.map (permWord swaps)).toFinset.image (renameW (permRow swaps.reverse)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hinv_word x (hw x hx)]
    · intro ha
      exact ⟨permWord swaps a, ⟨a, ha, rfl⟩, hinv_word a (hw a ha)⟩
  rw [hT', hS'] at run'
  exact hi k hk run'
abbrev Decor := Nat × Nat × Nat
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1, bin d x.2.1 y.2.1, bin d x.2.2 y.2.2)
def dsep (x : Decor) : Nat := x.2.1 ^^^ x.2.2
def projBits (rows : List Nat) (w : Nat) : Nat :=
  rows.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0
lemma testBit_projBits (rows : List Nat) (w i : Nat) :
    (projBits rows w).testBit i = match rows[i]? with | none => false | some r => w.testBit r := by
  induction rows generalizing i with
  | nil => simp [projBits]
  | cons r rs ih =>
    simp only [projBits, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.not_le.mpr (by decide : 0 < 1)]
      cases w.testBit r <;> rfl
    | succ i =>
      simp only [List.getElem?_cons_succ, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
      have h0 : (if w.testBit r then (1 : Nat) else 0).testBit (i + 1) = false := by
        cases w.testBit r
        · simp
        · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ i + 1)))
      rw [h0, Bool.or_false]
      exact ih i
lemma projBits_bin (rows : List Nat) (d a b : Nat) :
    projBits rows (bin d a b) = bin d (projBits rows a) (projBits rows b) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_projBits, testBit_bin, testBit_projBits, testBit_projBits]
  cases rows[i]? with
  | none => rcases d with _ | _ | _ | d <;> rfl
  | some r => exact testBit_bin d a b r
def faithful (pos neg : List Nat) (x : Decor) : Prop :=
  x.2.1 = projBits pos x.1 ∧ x.2.2 = projBits neg x.1
lemma faithful_bin {pos neg x y} (d : Nat) (hx : faithful pos neg x) (hy : faithful pos neg y) :
    faithful pos neg (dbin d x y) :=
  ⟨by rw [dbin, hx.1, hy.1, projBits_bin], by rw [dbin, hx.2, hy.2, projBits_bin]⟩
def goodPairs (T : Nat) (pos neg : List Nat) : Prop :=
  pos.length = neg.length ∧ ∀ i < pos.length,
    T.testBit (pos.getD i 0) = true ∧ T.testBit (neg.getD i 0) = false
def fullMask (n : Nat) : Nat := (1 <<< n) - 1
abbrev Cov := Nat × Nat × Nat
def addCov (z : Nat) (c : Cov) : Cov :=
  (z ||| c.1, (z ^^^ (z &&& c.1)) ||| (c.2.1 ^^^ (c.2.1 &&& z)),
   (z &&& c.2.1) ||| (c.2.2 ^^^ (c.2.2 &&& z)))
def coverage (v : List Decor) : Cov := v.foldr (fun a c => addCov (dsep a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := c.1 ^^^ (c.1 &&& (c.2.1 &&& a))
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
lemma cov_one (c : Cov) (a : Nat) : takeOne (addCov a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOne, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
lemma cov_two (c : Cov) (a b : Nat) : takeTwo (addCov a (addCov b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwo, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma addCov_swap (c : Cov) (a b : Nat) : addCov a (addCov b c) = addCov b (addCov a c) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [addCov, Nat.testBit_or]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
      simp only [addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma cov_perm {l r : List Decor} (h : l.Perm r) : coverage l = coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (dsep a)) ih
  | swap _ _ _ => exact addCov_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
def delOne (ws : List Decor) (a : Decor) (k : Bool) : List Decor := if k then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) : List Decor := delOne (delOne ws a ka) b kb
def restCov (c : Cov) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOne c b) else if kb then takeOne c a else takeTwo c a b
lemma cov_delOne {ws : List Decor} (a : Decor) (ha : a ∈ ws) (k : Bool) :
    (coverage (delOne ws a k)).1 = if k then (coverage ws).1 else takeOne (coverage ws) (dsep a) := by
  cases k
  · change (coverage (ws.erase a)).1 = _
    rw [cov_perm (List.perm_cons_erase ha)]
    exact (cov_one _ _).symm
  · rfl
lemma cov_delTwo {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    (coverage (delTwo ws a b ka kb)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb := by
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
    have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hbm))
    change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm hp]
    exact (cov_two _ _ _).symm
  · exact cov_delOne a ha false
  · exact cov_delOne b hb false
  · rfl
lemma cov_testBit (ws : List Decor) (i : Nat) :
    (coverage ws).1.testBit i = true ↔ ∃ x ∈ ws, (dsep x).testBit i = true := by
  induction ws with
  | nil => simp [coverage]
  | cons a ws ih =>
    change (dsep a ||| (coverage ws).1).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp
lemma cov_required {T k pos neg} {ws : List Decor}
    (gp : goodPairs T pos neg) (hf : ∀ x ∈ ws, faithful pos neg x)
    (h : Live T k (ws.map Prod.fst).toFinset) :
    ((coverage ws).1 &&& fullMask pos.length) = fullMask pos.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  have hfm : (fullMask pos.length).testBit i = decide (i < pos.length) := by
    simp [fullMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · have ⟨hp, hn⟩ := gp.2 i hi
    have hsep : T.testBit (pos.getD i 0) ≠ T.testBit (neg.getD i 0) := by rw [hp, hn]; decide
    obtain ⟨v, hv, hvd⟩ := live_sep h hsep
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hfx := hf x hx
    have hpi : pos[i]? = some (pos.getD i 0) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hni : neg[i]? = some (neg.getD i 0) := by
      have hi' : i < neg.length := gp.1 ▸ hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    have hbit : (dsep x).testBit i = true := by
      simp only [dsep, Nat.testBit_xor, hfx.1, hfx.2, testBit_projBits, hpi, hni]
      have h12 : x.1.testBit (pos.getD i 0) ≠ x.1.testBit (neg.getD i 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        exact hvd
      cases h1 : x.1.testBit (pos.getD i 0) <;> cases h2 : x.1.testBit (neg.getD i 0)
      · exact absurd (h1.trans h2.symm) h12
      · rfl
      · rfl
      · exact absurd (h1.trans h2.symm) h12
    have hc := (cov_testBit ws i).mpr ⟨x, hx, hbit⟩
    simp [hfm, hi, hc]
  · simp [hfm, hi]
def insertNat (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertNat a bs
def sortNats : List Nat → List Nat
  | [] => []
  | a :: bs => insertNat a (sortNats bs)
lemma insertNat_perm (a : Nat) (l : List Nat) : (insertNat a l).Perm (a :: l) := by
  induction l with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp [insertNat, h]
    · exact by simpa [insertNat, h] using (List.Perm.cons b ih).trans (.swap a b bs)
lemma sortNats_perm (l : List Nat) : (sortNats l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertNat_perm a (sortNats bs)).trans (.cons a ih)
lemma sortNats_toFinset (l : List Nat) : (sortNats l).toFinset = l.toFinset := by
  ext x; simpa only [List.mem_toFinset] using (sortNats_perm l).mem_iff
def childTwo (ws : List Nat) (a b d : Nat) (ka kb : Bool) : List Nat :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
lemma erase_toFinset {l : List Nat} (nd : l.Nodup) (a : Nat) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [nd.mem_erase_iff]
lemma enum_step {T cap : Nat} {ws : List Nat} (nd : ws.Nodup) (out : T ∉ ws)
    (stepOK : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb : Bool,
      a ≠ b → bin d a b ≠ 0 → bin d a b ∉ ws → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  cases k with
  | zero =>
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  | succ k =>
    obtain ⟨U, a, b, d, hd, he, _, _, hab, hf, tail⟩ := h
    have am : a ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_self a _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    have fresh : bin d a b ∉ ws := fun hm => hf (he ▸ List.mem_toFinset.mpr hm)
    have hnz : bin d a b ≠ 0 := live_nonzero tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b from rfl, erase_toFinset (nd.erase _) b, erase_toFinset nd a]
    have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
      cases c <;> simp [kept]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kf, kf, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (nd.erase _).erase _
    have ar : a ∉ rest := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (nd.erase a).not_mem_erase
    have nk := kept_nodup kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have ndc : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr hm))),
        kept_nodup ka a _ nk ax⟩
    have eqc : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := live_size tail
    have hlen : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup ndc, eqc]; omega
    exact stepOK a am b bm d hd ka kb hab hnz fresh hlen k (by omega) (eqc.symm ▸ tail)
lemma delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k; exact List.erase_sublist; exact List.Sublist.refl _
lemma delTwo_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) : (delTwo ws a b ka kb).Sublist ws :=
  (delOne_sub _ _ _).trans (delOne_sub _ _ _)
lemma delTwo_len (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
  cases ka <;> cases kb <;> simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]
lemma unique_fst {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hn (eq ▸ List.mem_map_of_mem hb')).elim
    · exact (hn (eq.symm ▸ List.mem_map_of_mem ha')).elim
    · exact ih ht ha' hb'
lemma delTwo_map_toFinset {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  have wn : ws.Nodup := nd.of_map
  have dn : (delOne ws a ka).Nodup := wn.sublist (delOne_sub ws a ka)
  have m1 (l : List Decor) (hl : l.Nodup) (x y : Decor) (c : Bool) :
      y ∈ delOne l x c ↔ y ∈ l ∧ (y ≠ x ∨ c = true) := by
    cases c <;> simp [delOne, hl.mem_erase_iff, and_comm]
  have km (v : Nat) : v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
      v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
    simp only [delTwo, List.mem_map, m1 _ wn, m1 _ dn]
    constructor
    · rintro ⟨w, ⟨⟨hw, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, h1.imp (fun h e => h (unique_fst nd hw ha e)) id,
        h2.imp (fun h e => h (unique_fst nd hw hb e)) id⟩
    · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
      exact ⟨w, ⟨⟨hw, h1.imp (fun h e => h (congrArg Prod.fst e)) id⟩,
        h2.imp (fun h e => h (congrArg Prod.fst e)) id⟩, rfl⟩
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv := List.mem_map_of_mem (f := Prod.fst) hb
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (v : Nat) : v ∈ kept c x l ↔ (v = x ∧ c = true) ∨ v ∈ l := by
    cases c <;> simp [kept]
  ext v
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, km, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, dbin]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all
lemma childTwo_swap (v : List Nat) (nd : v.Nodup) (a b : Nat) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (y : Nat) : y ∈ kept c x l ↔ (y = x ∧ c = true) ∨ y ∈ l := by
    cases c <;> simp [kept]
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_comm_flip d hd a b]
  tauto
def varsOf (m : Nat) : List Nat :=
  (List.range 7).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    let fr := ((r &&& (127 ^^^ z)) ||| o) % 128
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p : Nat → Bool) (l : List Nat) (r : Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra : r = a
      · subst hra; simp [hpa]
      · have h1 : (decide (a ≤ r) && (1 : Nat).testBit (r - a)) = false := by
          by_cases hle : a ≤ r
          · have hpos : r - a ≠ 0 := by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra : r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w : Nat) : fixWord z o w = renameW (fixRow z o) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 128
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 128 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h127 : ((r.val &&& (127 ^^^ z)) ||| o) < 128 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (127 ^^^ z)) < 128 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 7) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (127 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h127
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 7
    · have h7 : (127 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 128) && decide (s < 128) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL128 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL128]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 128 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^128) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^128 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^128) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^128 ∧ a.testBit 0 = false := by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def carryOK (swaps : List (Nat × Nat)) (roots1 : List Nat) (T1 : Nat) (roots2 : List Nat) (T2 : Nat) : Bool :=
  swapsValid swaps && checkProper T1 && checkRoots roots1 && checkProper T2 &&
    (permWord swaps T1 == T2) && roots1.all (fun a => freeIn roots2 (permWord swaps a))
lemma carry_of {swaps roots1 T1 roots2 T2 L} (ok : carryOK swaps roots1 T1 roots2 T2 = true)
    (hL : Lower roots2 T2 L) : Lower roots1 T1 L := by
  simp only [carryOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hsv, hT1⟩, hR1⟩, hT2⟩, heq⟩, hcov⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT1
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hT2
  have hR1' := checkRoots_sound hR1
  have heq' : renameW (permRow swaps) T1 = T2 := (permWord_eq_renameW swaps hsv T1 p1b).symm.trans heq
  have hcov' : ∀ a ∈ roots1, Avail (roots2.map obs) (restrictW (permRow swaps) (obs a)) := fun a ha =>
    freeIn_sound (permWord_eq_renameW swaps hsv a (hR1' a ha).1 ▸ hcov a ha)
  simpa using lower_slice p1a p1b p1c hR1' p2a p2b p2c (permRow swaps) heq' hcov' ∅ (by simp) (by simp) L hL
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL128))
lemma lift_of {z o roots T other G essPairs L} (ok : liftCheck z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G := (fixWord_eq_renameW z o T).symm.trans heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [Bool.or_eq_true, beq_iff_eq, fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL128]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 128 r'.val |> fun e => by simpa [this] using e⟩
def goodPairsCheck (T : Nat) (pos neg : List Nat) : Bool :=
  (pos.length == neg.length) &&
    (List.range pos.length).all fun i => T.testBit (pos.getD i 0) && !(T.testBit (neg.getD i 0))
lemma goodPairs_of {T pos neg} (ok : goodPairsCheck T pos neg = true) : goodPairs T pos neg := by
  simp only [goodPairsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at ok
  exact ok
def autosCheck (T : Nat) (autos : List (List (Nat × Nat))) : Bool :=
  autos.all fun sw => swapsValid sw && (permWord sw T == T)
lemma autos_of {T autos} (ok : autosCheck T autos = true) :
    ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T := by
  simp only [autosCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at ok
  exact ok
def baseCheck (pos neg : List Nat) (base : List Decor) : Bool :=
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^128)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := by
  simp only [baseCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  intro x hx
  have h := ok x hx
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩
def forestRootCheck (roots : List Nat) (T : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    roots.all fun a => essPairs.any fun e => (e.1 == a) && checkEss1 T roots e.1 e.2.1 e.2.2
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat
lemma var_testBit (i : Fin 7) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
def sliceDirectCheck (z o zDead : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    decide (zDead < 128) && (((z ||| zDead) &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord (z ||| zDead) o T == qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord (z ||| zDead) o a))
lemma subcube_fixRow_sup (z o zDead : Nat) (hz : z < 128) (hd : zDead < 128) (ho : o < 128)
    (hzo : ((z ||| zDead) &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow (z ||| zDead) o r).val = true := by
  have hsub := subcube_fixRow (z ||| zDead) o (Nat.or_lt_two_pow (n := 7) hz hd) ho hzo r
  unfold subcube at hsub ⊢
  rw [testBit_foldr_bits] at hsub ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsub ⊢
  refine ⟨hsub.1, ?_, hsub.2.2⟩
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun x => x.testBit i) hsub.2.1
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
  cases hfa : (fixRow (z ||| zDead) o r).val.testBit i <;> cases hzb : z.testBit i <;> simp_all
lemma slice_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) qL := by
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz, ho⟩, _hzo0⟩, hd⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  refine ⟨fixRow (z ||| zDead) o, qRoots, subcube_fixRow_sup z o zDead hz hd ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW (z ||| zDead) o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW, heq]
  exact hPrior
inductive BT (α : Type) where
  | empty : BT α
  | leaf : α → BT α
  | node : BT α → BT α → BT α
def btGet {α : Type} (d : α) : BT α → Nat → α
  | .empty, _ => d
  | .leaf x, _ => x
  | .node l r, i => if i &&& 1 == 0 then btGet d l (i >>> 1) else btGet d r (i >>> 1)
def btSet {α : Type} : Nat → BT α → Nat → α → BT α
  | 0, _, _, v => .leaf v
  | d + 1, .empty, i, v =>
    if i &&& 1 == 0 then .node (btSet d .empty (i >>> 1) v) .empty
    else .node .empty (btSet d .empty (i >>> 1) v)
  | d + 1, .leaf x, i, v =>
    if i &&& 1 == 0 then .node (btSet d (.leaf x) (i >>> 1) v) .empty
    else .node .empty (btSet d (.leaf x) (i >>> 1) v)
  | d + 1, .node l r, i, v =>
    if i &&& 1 == 0 then .node (btSet d l (i >>> 1) v) r
    else .node l (btSet d r (i >>> 1) v)
def btUpdate {α : Type} (d0 : α) : Nat → BT α → Nat → (α → α) → BT α
  | 0, .leaf x, _, f => .leaf (f x)
  | 0, _, _, f => .leaf (f d0)
  | d + 1, .empty, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d .empty (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d .empty (i >>> 1) f)
  | d + 1, .leaf x, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d (.leaf x) (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d (.leaf x) (i >>> 1) f)
  | d + 1, .node l r, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d l (i >>> 1) f) r
    else .node l (btUpdate d0 d r (i >>> 1) f)
def btAll {α : Type} (P : α → Prop) : BT α → Prop
  | .empty => True
  | .leaf x => P x
  | .node l r => btAll P l ∧ btAll P r
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction t generalizing i with
  | empty => exact hd
  | leaf x => exact ht
  | node l r ihl ihr =>
    unfold btGet
    split
    · exact ihl ht.1 _
    · exact ihr ht.2 _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact hv
  | succ d ih =>
    cases t with
    | empty =>
      unfold btSet; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btSet; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btSet; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases t with
    | leaf x => exact hf x ht
    | empty => exact hf d0 hd0
    | node _ _ => exact hf d0 hd0
  | succ d ih =>
    cases t with
    | empty =>
      unfold btUpdate; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btUpdate; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btUpdate; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
def btOfList {α : Type} (depth : Nat) (l : List α) : BT α :=
  (l.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) (0, BT.empty)).2
lemma btAll_ofList {α : Type} {P : α → Prop} {depth : Nat} {l : List α}
    (h : ∀ x ∈ l, P x) : btAll P (btOfList depth l) := by
  unfold btOfList
  have hgo : ∀ (xs : List α) (acc : Nat × BT α),
      (∀ x ∈ xs, P x) → btAll P acc.2 →
      btAll P (xs.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) acc).2 := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc; exact hacc
    | cons x xs ih =>
      intro acc hx hacc
      exact ih (acc.1 + 1, btSet depth acc.2 acc.1 x)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        (btAll_set hacc (hx x (List.mem_cons_self ..)))
  exact hgo l (0, BT.empty) h trivial
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL128 ^^^ VAR i else if o.testBit i then VAR i else ALL128
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&& fastBitMask z o 6
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 7) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL128.testBit r.val = true := by
    simp only [ALL128]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 128 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · have hsub : (subcube z o).testBit r = ((r &&& z == 0) && (r &&& o == o)) := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and,
      fastBitMask_testBit z o 0 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 1 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 2 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 3 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 4 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 5 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 7) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 7, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 7
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 7
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 128 ≤ r := by omega
      have ha : ALL128 < 2^128 := by decide
      have hv : VAR i < 2^128 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^128; decide
      have hlt_m : fastBitMask z o i < 2^128 := by
        unfold fastBitMask; split
        · exact Nat.xor_lt_two_pow ha hv
        · split; exact hv; exact ha
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by decide : 0 < 2) hle))
    have hsub : (subcube z o).testBit r = false := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and, hlt_f]
    rfl
lemma slice_fast_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  have ok2 := ok
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1.1.1 ok2.1.1.1.1.1.1.1.2 ok2.1.1.1.1.1.1.2]
  exact slice_direct ok hPrior
def hashWs64 (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) &&& 63
def bucketContainsBT (bks : BT (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def closeChildBT (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (ws.map (permWord sw)))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContainsBT at hhit
    have hmem := List.contains_iff_mem.mp hhit
    have hb : ∀ xs ∈ btGet [] prevBks (hashWs64 (sortNats ((choiceVal op :: rest).map (permWord sw)))),
        Impossible T k xs.toFinset :=
      btAll_get hPrev (fun _ hx => (List.not_mem_nil hx).elim) _
    have himp := hb _ hmem
    rw [sortNats_toFinset] at himp
    have ⟨hsv, hfix⟩ := hAutos sw hsw
    have hvr : swapsValid sw.reverse = true := by simp only [swapsValid, List.all_reverse]; exact hsv
    have hinv_row_gen : ∀ (l : List (Nat × Nat)), swapsValid l = true →
        ∀ r : Row, permRow l.reverse (permRow l r) = r := by
      intro l hl
      induction l with
      | nil => intro r; rfl
      | cons p ps ih =>
        simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
        intro r
        have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
            swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
          simp [permRow, List.reverse_cons, List.foldl_append]
        rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
    have hinv_row2 : ∀ r : Row, permRow sw (permRow sw.reverse r) = r := by
      simpa using hinv_row_gen sw.reverse hvr
    have hinv_w : ∀ x : Nat, x < 2^128 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 128
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      rw [permWord_eq_renameW sw hsv x (hlt x hx)]
      exact renameW_lt _ x
    have hrot := rotate_impossible himp sw.reverse hvr hT hfixr hmap_lt
    have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
      exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
    rwa [hback] at hrot
abbrev FastPool := BoundPool × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else some (c, miss, vals.countP (isConstM c.dom))
def fastPoolCut (fp : FastPool) (k : Nat) (a b d : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let totC := fp.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && isConstM c.dom a then 1 else 0
    let dropB := if !kb && isConstM c.dom b then 1 else 0
    let z := bin d a b
    let cRest := totC - dropA - dropB + (if isConstM c.dom z then 1 else 0)
    let zIn := availM c.dom c.pm z
    let extra := if zIn then 0 else 1
    decide (k + c.paid + extra < c.lb + cRest) && (zIn || choiceOK c.dom c.pm (d, a, b))
lemma countP_erase {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {x : α} (hx : x ∈ l) :
    (l.erase x).countP p + (if p x then 1 else 0) = l.countP p := by
  have hp := List.perm_cons_erase hx
  have h1 := List.Perm.countP_eq p hp
  simp only [List.countP_cons] at h1
  omega
lemma countP_delTwo_fst (p : Nat → Bool) {ws : List Decor} {a b : Decor}
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map Prod.fst).countP p =
      (ws.map Prod.fst).countP p - (if !ka && p a.1 then 1 else 0) - (if !kb && p b.1 then 1 else 0) := by
  have hne : a ≠ b := fun e => hab (congrArg Prod.fst e)
  have hmap_erase : ∀ (l : List Decor) (x : Decor), (l.map Prod.fst).Nodup → x ∈ l →
      (l.erase x).map Prod.fst = (l.map Prod.fst).erase x.1 := by
    intro l x hnd hx
    induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne1 : y.1 ≠ x.1 := by
          intro eq; apply hnd.1; rw [eq]
          exact List.mem_map_of_mem ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx))
        have h1 : (y == x) = false := beq_false_of_ne hyx
        have h2 : (y.1 == x.1) = false := beq_false_of_ne hne1
        simp only [List.erase_cons, h1, h2, List.map_cons]
        exact congrArg (y.1 :: ·) (ih hnd.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx)))
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne hne.symm).mpr hb
    have hnd1 : ((ws.erase a).map Prod.fst).Nodup := ((List.erase_sublist).map Prod.fst).nodup nd
    change (((ws.erase a).erase b).map Prod.fst).countP p = _
    rw [hmap_erase _ b hnd1 hbm, hmap_erase ws a nd ha]
    have ha1 : a.1 ∈ ws.map Prod.fst := List.mem_map_of_mem ha
    have hb1 : b.1 ∈ (ws.map Prod.fst).erase a.1 := (List.mem_erase_of_ne hab.symm).mpr (List.mem_map_of_mem hb)
    have c1 := countP_erase p ha1
    have c2 := countP_erase p hb1
    cases hpa : p a.1 <;> cases hpb : p b.1 <;> simp [hpa, hpb] at c1 c2 ⊢ <;> omega
  · change ((ws.erase a).map Prod.fst).countP p = _
    rw [hmap_erase ws a nd ha]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) ha)
    cases hpa : p a.1 <;> simp [hpa] at c1 ⊢ <;> omega
  · change ((ws.erase b).map Prod.fst).countP p = _
    rw [hmap_erase ws b nd hb]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) hb)
    cases hpb : p b.1 <;> simp [hpb] at c1 ⊢ <;> omega
  · simp [delTwo, delOne]
lemma fastPoolCut_sound {raw T ws a b d ka kb k c fp}
    (hP : ValidPool raw T c) (hprep : prepPool (ws.map Prod.fst) c = some fp)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 d ka kb = true) :
    Impossible T k (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  unfold prepPool at hprep
  dsimp only at hprep
  split at hprep
  · simp at hprep
  · simp only [Option.some.injEq] at hprep
    subst hprep
    unfold fastPoolCut at hcut
    dsimp only at hcut
    split at hcut
    · simp at hcut
    · next hmiss =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_filter, Bool.not_eq_true'] at hmiss
      have hsub := (delTwo_sub ws a b ka kb).map Prod.fst
      have h_all_avail : ((delTwo ws a b ka kb).map Prod.fst).all (availM c.dom c.pm) = true := by
        rw [List.all_eq_true]; intro w hw
        by_contra hna
        have hnf : availM c.dom c.pm w = false := Bool.eq_false_iff.mpr hna
        have hmem_ws : w ∈ ws.map Prod.fst := hsub.subset hw
        have hm := hmiss w ⟨hmem_ws, hnf⟩
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
        have hne_ab : a ≠ b := fun e => hab (congrArg Prod.fst e)
        have hnot_in : ∀ (x : Decor) (kx : Bool), kx = false → x ∈ ws → x.1 ∉ (delTwo ws a b ka kb).map Prod.fst → True := fun _ _ _ _ _ => trivial
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            exact List.Nodup.not_mem_erase hnd_ws hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · have hu_eq : u = a := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa)
          exact hna' hka hu_eq
        · have hu_eq : u = b := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb)
          exact hnb' hkb hu_eq
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut
      simp only [choiceVal, h_all_avail, Bool.true_and, Bool.and_true, List.countP_cons,
        Bool.and_eq_true, decide_eq_true_eq] at hcut ⊢
      rw [hcnt]
      rcases hcut with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          cases hcz : isConstM c.dom (bin d a.1 b.1) <;>
          simp only [hz, hcz, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
            Bool.and_eq_true, Bool.false_eq_true, ite_true, ite_false] at h1 ⊢ <;> omega
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          simp only [hz, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or] at h2 ⊢ <;>
          exact h2
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
  go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^128) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (_hd : d < 4)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (hnz : bin d a.1 b.1 ≠ 0) (hfr : bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := (z :: rest).map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hfr_b : (ws.any (fun v => v.1 == z.1)) = false := by
    rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
    have hvz : v.1 = bin d a.1 b.1 := beq_iff_eq.mp heq
    exact hfr (hvz ▸ List.mem_map_of_mem hv)
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    have hdl := delTwo_len ws a b ka kb ha hb ne
    simp only [child, rest, List.length_map, List.length_cons]
    omega
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen : child.length ≤ cap := by omega
  have hcov := cov_required gp (ws := z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq : (coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z := by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b : (((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false := by
    simp [hcov]
  unfold evalMoveBT at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = false := Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw := raw) (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h : testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAllBT, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma nodeBT_sound {raw T pos neg ws fpools autos prevBks cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (checks : cap = 0 ∨ testAllBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0
    intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (x y : Decor) (d' : Nat) (hd' : d' < 4) (hx : x ∈ ws) (hy : y ∈ ws) (nxy : x.1 ≠ y.1)
      (k1 k2 : Bool) (hnz' : bin d' x.1 y.1 ≠ 0) (hfr' : bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht : testPairBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPairBT, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMoveBT_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAllBT_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
def buildWiresBT (depth : Nat) (base : List Decor) (steps : List (Nat × Nat × Nat)) : BT Decor :=
  let init := (base.length, btOfList depth base)
  (steps.foldl (fun p s =>
    let a := btGet (0, 0, 0) p.2 s.2.1
    let b := btGet (0, 0, 0) p.2 s.2.2
    (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 a b))) init).2
lemma buildWiresBT_faithful {depth pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128)
        (ss.foldl (fun p s => (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 (btGet (0, 0, 0) p.2 s.2.1) (btGet (0, 0, 0) p.2 s.2.2)))) acc).2 := by
    intro ss
    induction ss with
    | nil => intro acc hacc; exact hacc
    | cons s ss ih =>
      intro acc hacc
      have ha := btAll_get hacc hdef s.2.1
      have hb := btAll_get hacc hdef s.2.2
      exact ih _ (btAll_set hacc ⟨faithful_bin s.1 ha.1 hb.1, bin_lt s.1 _ _ ha.2 hb.2⟩)
  exact hgo steps (base.length, btOfList depth base) h0
def buildPoolsBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : List PoolSpec) : BT (Option BoundPool) :=
  btOfList pdepth (pspecs.map fun (slIdx, chIdxs) =>
    match btGet none slices slIdx with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
      materialize raw cs dom lb)
lemma buildPoolsBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))} {pspecs : List PoolSpec}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsBT pdepth W raw slices pspecs) := by
  apply btAll_ofList
  intro o ho c hc
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp ho
  dsimp only at hmat
  have hsl := btAll_get (d := none) hSlices (fun _ h => by simp at h) slIdx
  cases heq : btGet none slices slIdx with
  | none => rw [heq] at hmat; exact absurd (hmat.trans hc) (by simp)
  | some sl =>
    rw [heq] at hmat
    exact materialize_sound (hsl sl heq) (hmat.trans hc)
def checkNodeBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  let vals := ws.map Prod.fst
  let fpools := ns.2.1.filterMap fun pIdx =>
    match btGet none poolTable pIdx with
    | none => none
    | some c => prepPool vals c
  let nodeAutos := ns.2.2.map fun aIdx => btGet [] autosTable aIdx
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^128 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun fp hfp => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hfp
      cases heq : btGet none poolTable pIdx with
      | none => simp [heq] at hmat
      | some c =>
        simp only [heq] at hmat
        have hvc := btAll_get hPoolTable (fun _ h => by simp at h) pIdx c heq
        have hfp_eq : fp.1 = c := by
          unfold prepPool at hmat
          dsimp only at hmat
          split at hmat
          · simp at hmat
          · simp only [Option.some.injEq] at hmat; rw [← hmat]
        rw [hfp_eq]
        exact ⟨hvc, hmat⟩)
    (fun sw hsw => by
      obtain ⟨aIdx, _, rfl⟩ := List.mem_map.mp hsw
      exact btAll_get hAutos ⟨rfl, rfl⟩ aIdx)
    hPrev ok.2
def nodeValsBT (W : BT Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (btGet (0, 0, 0) W idx).1)
def buildBucketsBT (W : BT Decor) (nodes : List NodeSpec) : BT (List (List Nat)) :=
  nodes.foldl (fun acc ns =>
    let xs := nodeValsBT W ns
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := fun ns hns => by
    unfold nodeValsBT; rw [sortNats_toFinset]
    exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
lemma lower_of_forestBT {roots T cap} {topBks : BT (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : btAll (fun bk => ∀ xs ∈ bk, Impossible T cap xs.toFinset) topBks)
    (hRoot : bucketContainsBT topBks roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContainsBT at hRoot
    exact btAll_get hTop (fun _ h => (List.not_mem_nil h).elim) _ _ (List.contains_iff_mem.mp hRoot)
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def hashWs (nb : Nat) (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) % nb
def bucketContains (buckets : Array (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (buckets.getD (hashWs buckets.size s) []).contains s
def closeChild (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContains prevBuckets (ws.map (permWord sw)))
lemma closeChild_sound {raw T pools autos prevBuckets k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T k xs.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChild pools autos prevBuckets k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContains at hhit
    simp only [Array.getD, List.contains_eq_mem, decide_eq_true_eq] at hhit
    split at hhit
    next hlt_b =>
      have himp := hPrev _ hlt_b _ hhit
      rw [sortNats_toFinset] at himp
      have ⟨hsv, hfix⟩ := hAutos sw hsw
      have hvr : swapsValid sw.reverse = true := by simp only [swapsValid, List.all_reverse]; exact hsv
      have hinv_row_gen : ∀ (l : List (Nat × Nat)), swapsValid l = true →
          ∀ r : Row, permRow l.reverse (permRow l r) = r := by
        intro l hl
        induction l with
        | nil => intro r; rfl
        | cons p ps ih =>
          simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
          intro r
          have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
              swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
            simp [permRow, List.reverse_cons, List.foldl_append]
          rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
      have hinv_row2 : ∀ r : Row, permRow sw (permRow sw.reverse r) = r := by
        simpa using hinv_row_gen sw.reverse hvr
      have hinv_w : ∀ x : Nat, x < 2^128 → permWord sw.reverse (permWord sw x) = x := by
        intro x hx
        have h1 := permWord_eq_renameW sw hsv x hx
        have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
        rw [h2, h1]
        apply Nat.eq_of_testBit_eq; intro r
        by_cases hrr : r < 128
        · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
        · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
              Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
      have hfix_r : permWord sw.reverse T = T := by
        conv_lhs => rw [← hfix]
        exact hinv_w T hT
      have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [permWord_eq_renameW sw hsv x (hlt x hx)]
        exact renameW_lt _ x
      have hrot := rotate_impossible himp sw.reverse hvr hT hfix_r hmap_lt
      have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
        exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
      rwa [hback] at hrot
    next => simp at hhit
def evalMove (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild pools autos prevBuckets (cap - 1) rest (d, a.1, b.1)
def testPair (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMove cap n fmask ws cov pools autos prevBuckets d a b z
  go false false && go true false && go false true && go true true
def testAll (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPair cap n fmask ws cov pools autos prevBuckets a b)) &&
      testAll cap n fmask ws cov pools autos prevBuckets bs
lemma evalMove_sound {raw T pos neg ws pools autos prevBuckets cap a b d ka kb}
    (hT : T < 2^128)
    (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (hd : d < 4)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (hnz : (dbin d a b).1 ≠ 0) (hfr : (dbin d a b).1 ∉ ws.map Prod.fst)
    (test : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets
      d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => hfr ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      exact hlt w (sub.subset hw)
  have hfr_b : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
    exact hfr (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    change _ = (z.1 :: rest.map Prod.fst).length
    rw [List.length_cons, List.length_map, delTwo_len ws a b ka kb ha hb ne, Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen : child.length ≤ cap := by omega
  have hcov := cov_required gp (ws := z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq : (coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z := by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b : (((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false := by
    simp [hcov]
  unfold evalMove at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  exact closeChild_sound (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT hPools hAutos hPrev ndc hltc test k hk h
lemma testAll_pair {cap n fmask ws cov pools autos prevBuckets l}
    (h : testAll cap n fmask ws cov pools autos prevBuckets l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets a b d = true) ∨
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAll, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma node_sound {raw T pos neg ws pools autos prevBuckets cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (checks : cap = 0 ∨ testAll cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0; intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (x y : Decor) (d' : Nat) (hd' : d' < 4) (hx : x ∈ ws) (hy : y ∈ ws) (nxy : x.1 ≠ y.1)
      (k1 k2 : Bool) (hnz' : bin d' x.1 y.1 ≠ 0) (hfr' : bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht : testPair cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPair, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMove_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAll_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
lemma lower_of_forest {roots T cap} {topBuckets : Array (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : ∀ i (hi : i < topBuckets.size), ∀ xs ∈ topBuckets[i], Impossible T cap xs.toFinset)
    (hRoot : bucketContains topBuckets roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContains Array.getD at hRoot
    dsimp only at hRoot
    split at hRoot
    next hi => exact hTop _ hi _ (List.contains_iff_mem.mp hRoot)
    next => simp at hRoot
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def buildWires (base : List Decor) (steps : List (Nat × Nat × Nat)) : Array Decor :=
  steps.foldl (fun arr s =>
    let a := arr.getD s.2.1 (0, 0, 0)
    let b := arr.getD s.2.2 (0, 0, 0)
    arr.push (dbin s.1 a b)) base.toArray
lemma buildWires_faithful {pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    ∀ x ∈ (buildWires base steps).toList, faithful pos neg x ∧ x.1 < 2^128 := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hstep : ∀ (arr : Array Decor) (s : Nat × Nat × Nat),
      (∀ x ∈ arr.toList, faithful pos neg x ∧ x.1 < 2^128) →
      ∀ x ∈ (arr.push (dbin s.1 (arr.getD s.2.1 (0, 0, 0)) (arr.getD s.2.2 (0, 0, 0)))).toList,
        faithful pos neg x ∧ x.1 < 2^128 := by
    intro arr s harr x hx
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact harr x hx
    · have hget (i : Nat) : faithful pos neg (arr.getD i (0, 0, 0)) ∧ (arr.getD i (0, 0, 0)).1 < 2^128 := by
        unfold Array.getD
        split
        next hi => exact harr arr[i] (Array.getElem_mem_toList hi)
        next => exact hdef
      exact ⟨faithful_bin s.1 (hget s.2.1).1 (hget s.2.2).1, bin_lt s.1 _ _ (hget s.2.1).2 (hget s.2.2).2⟩
  unfold buildWires
  have hinit : ∀ x ∈ base.toArray.toList, faithful pos neg x ∧ x.1 < 2^128 := by simpa using hbase
  clear hbase
  generalize base.toArray = acc at hinit ⊢
  induction steps generalizing acc with
  | nil => exact hinit
  | cons s ss ih => exact ih _ (hstep acc s hinit)
lemma array_forall_of_list {α : Type} {P : α → Prop} {l : List α} (h : ∀ x ∈ l, P x) :
    ∀ i (hi : i < l.toArray.size), P l.toArray[i] :=
  fun i hi => h l.toArray[i] (Array.getElem_mem_toList hi)
def buildPools (W : Array Decor) (raw : List Nat) (slices : Array (Nat × Nat))
    (pspecs : List PoolSpec) : Array (Option BoundPool) :=
  (pspecs.map fun (slIdx, chIdxs) =>
    match slices[slIdx]? with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
      materialize raw cs dom lb).toArray
lemma buildPools_sound {W : Array Decor} {raw T} {slices : Array (Nat × Nat)} {pspecs : List PoolSpec}
    (hSlices : ∀ i (hi : i < slices.size), Slice raw T slices[i].1 slices[i].2) :
    ∀ i (hi : i < (buildPools W raw slices pspecs).size),
      ∀ c, (buildPools W raw slices pspecs)[i] = some c → ValidPool raw T c := by
  intro i hi c hc
  unfold buildPools at hi hc
  have hmem : some c ∈ pspecs.map (fun (slIdx, chIdxs) =>
      match slices[slIdx]? with
      | none => none
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
        materialize raw cs dom lb) := by
    rw [← hc]
    exact Array.getElem_mem_toList hi
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp hmem
  cases hget_sl : slices[slIdx]? with
  | none => simp [hget_sl] at hmat
  | some sl =>
    simp only [hget_sl] at hmat
    have ⟨hsi, hval⟩ := Array.getElem?_eq_some_iff.mp hget_sl
    exact materialize_sound (hval ▸ hSlices slIdx hsi) hmat
def checkNode (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  let vals := ws.map Prod.fst
  let pools := ns.2.1.filterMap fun pIdx => poolTable.getD pIdx none
  let nodeAutos := ns.2.2.filterMap fun aIdx => autosTable[aIdx]?
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAll k ws.length fmask ws (coverage ws) pools nodeAutos prevBuckets ws)
def checkNodes (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNode W T fmask poolTable autosTable prevBuckets k)
lemma checkNode_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (ok : checkNode W T (fullMask pos.length) poolTable autosTable prevBuckets k ns = true) :
    Impossible T k ((ns.1.map fun idx => (W.getD idx (0, 0, 0)).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (W.getD idx (0, 0, 0)) ∧ (W.getD idx (0, 0, 0)).1 < 2^128 := by
    unfold Array.getD; split
    next hi => exact hW W[idx] (Array.getElem_mem_toList hi)
    next => exact hdef
  unfold checkNode at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (W.getD idx (0, 0, 0)).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply node_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun c hc => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hc
      unfold Array.getD at hmat
      split at hmat
      next hi => exact hPoolTable pIdx hi c hmat
      next => simp at hmat)
    (fun sw hsw => by
      obtain ⟨aIdx, _, ha⟩ := List.mem_filterMap.mp hsw
      have ⟨hi, hval⟩ := Array.getElem?_eq_some_iff.mp ha
      exact hAutos sw (hval ▸ Array.getElem_mem_toList hi))
    hPrev ok.2
def nodeVals (W : Array Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (W.getD idx (0, 0, 0)).1)
def insertBucket (buckets : Array (List (List Nat))) (xs : List Nat) : Array (List (List Nat)) :=
  let idx := hashWs buckets.size xs
  if h : idx < buckets.size then
    let b := buckets[idx]
    if b.contains xs then buckets else buckets.set idx (xs :: b) h
  else buckets
def buildBuckets (nb : Nat) (W : Array Decor) (nodes : List NodeSpec) : Array (List (List Nat)) :=
  nodes.foldl (fun acc ns => insertBucket acc (nodeVals W ns)) (Array.replicate nb [])
lemma insertBucket_mem {bks : Array (List (List Nat))} {P : List Nat → Prop} {xs : List Nat}
    (hb : ∀ i (hi : i < bks.size), ∀ ys ∈ bks[i], P ys) (hxs : P xs) :
    ∀ i (hi : i < (insertBucket bks xs).size), ∀ ys ∈ (insertBucket bks xs)[i], P ys := by
  unfold insertBucket
  dsimp only
  split
  next hidx =>
    split
    · exact hb
    · intro i hi ys hys
      rw [Array.size_set] at hi
      rw [Array.getElem_set] at hys
      split at hys
      next =>
        rcases List.mem_cons.mp hys with rfl | hys'
        · exact hxs
        · exact hb _ hidx ys hys'
      next => exact hb i hi ys hys
  next => exact hb
lemma buildBuckets_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k nb}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (hNodes : checkNodes W T (fullMask pos.length) poolTable autosTable prevBuckets k nodes = true) :
    ∀ i (hi : i < (buildBuckets nb W nodes).size), ∀ xs ∈ (buildBuckets nb W nodes)[i], Impossible T k xs.toFinset := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeVals W ns).toFinset := fun ns hns => by
    unfold nodeVals
    rw [sortNats_toFinset]
    exact checkNode_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBuckets
  have hinit : ∀ i (hi : i < (Array.replicate nb ([] : List (List Nat))).size),
      ∀ xs ∈ (Array.replicate nb ([] : List (List Nat)))[i], Impossible T k xs.toFinset := by
    intro i hi xs hxs; simp at hxs
  generalize Array.replicate nb ([] : List (List Nat)) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    exact ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      (insertBucket acc (nodeVals W ns)) (insertBucket_mem hinit (hmem ns (List.mem_cons_self ..)))
lemma checkNodesBT_mem {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k nodes}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := by
  intro ns hns
  unfold nodeValsBT; rw [sortNats_toFinset]
  exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
lemma forall_append {α : Type} {P : α → Prop} {l1 l2 : List α}
    (h1 : ∀ x ∈ l1, P x) (h2 : ∀ x ∈ l2, P x) : ∀ x ∈ l1 ++ l2, P x := by
  intro x hx; rcases List.mem_append.mp hx with h | h; exact h1 x h; exact h2 x h
lemma buildBucketsBT_of_mem {W : BT Decor} {T k nodes}
    (hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
def buildPoolsSubBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : BT (Option PoolSpec)) (used : List Nat) : BT (Option BoundPool) :=
  used.foldl (fun acc pIdx =>
    match btGet none pspecs pIdx with
    | none => acc
    | some (slIdx, chIdxs) =>
      match btGet none slices slIdx with
      | none => acc
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
        btSet pdepth acc pIdx (materialize raw cs dom lb)) BT.empty
lemma buildPoolsSubBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))}
    {pspecs : BT (Option PoolSpec)} {used : List Nat}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsSubBT pdepth W raw slices pspecs used) := by
  unfold buildPoolsSubBT
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := trivial
  generalize (BT.empty : BT (Option BoundPool)) = acc at hinit ⊢
  induction used generalizing acc with
  | nil => exact hinit
  | cons pIdx rest ih =>
    apply ih
    dsimp only
    cases hps : btGet none pspecs pIdx with
    | none => simp only [hps]; exact hinit
    | some spec =>
      cases hsl : btGet none slices spec.1 with
      | none => simp only [hps, hsl]; exact hinit
      | some sl =>
        simp only [hps, hsl]
        apply btAll_set hinit
        intro c hc
        exact materialize_sound (btAll_get (d := none) hSlices (fun _ h => by simp at h) spec.1 sl hsl) hc

def dualRow (r : Row) : Row := ⟨(r.val ^^^ 127) % 128, Nat.mod_lt _ (by decide)⟩

lemma map_available (f : Row → Row) {b c : List Wire}
    (cover : ∀ w ∈ b, Avail c (restrictW f w)) {w : Wire} (hw : Avail b w) :
    Avail c (restrictW f w) := by
  rcases hw with hb | ⟨bit,rfl⟩ | hi
  · exact cover _ hb
  · exact Or.inr (Or.inl ⟨bit,rfl⟩)
  · have h : Avail c (invW (restrictW f w)) := cover _ hi
    simpa only [invW_inv] using avail_inv h

lemma map_reach (f : Row → Row) {R S : List Wire}
    (cover : ∀ w ∈ R, Avail S (restrictW f w)) {p b} (hr : Reach R p b) :
    ∃ c, Reach S p c ∧ ∀ w ∈ b, Avail c (restrictW f w) := by
  induction p generalizing b with
  | zero =>
    have hb : b = R := hr
    exact ⟨S,rfl,hb.symm ▸ cover⟩
  | succ p ih =>
    obtain ⟨op,b,a,d,prev,ha,hd,rfl⟩ := hr
    obtain ⟨c,hc,hmap⟩ := ih prev
    let w := comb2 op (restrictW f a) (restrictW f d)
    have eq : restrictW f (comb2 op a d) = w := by cases op <;> rfl
    refine ⟨w :: c,⟨op,c,_,_,hc,map_available f hmap ha,map_available f hmap hd,rfl⟩,?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl | hold
    · rw [eq]
      exact Or.inl List.mem_cons_self
    · exact avail_cons w (hmap t hold)

lemma dualLower {roots : List Nat} {T G L : Nat}
    (hvars : ∀ r : Row, roots.all (fun a => decide (obs a (dualRow r) = !(obs a r))) = true)
    (hgoal : ∀ r : Row, (!(obs T (dualRow r))) = obs G r)
    (prior : Lower roots G L) : Lower roots T L := by
  intro p bank hr hav
  have maps (w : Wire) (hw : w ∈ roots.map obs) : Avail (roots.map obs) (restrictW dualRow w) := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    have eq : restrictW dualRow (obs a) = invW (obs a) :=
      funext fun r => of_decide_eq_true (List.all_eq_true.mp (hvars r) a ha)
    rw [eq]
    exact avail_inv (Or.inl (List.mem_map.mpr ⟨a,ha,rfl⟩))
  obtain ⟨c,hc,hmap⟩ := map_reach dualRow maps hr
  have eq : invW (restrictW dualRow (obs T)) = obs G := funext hgoal
  exact prior p c hc (eq ▸ avail_inv (map_available dualRow hmap hav))

def identifyRow (z o i j : Nat) (r : Row) : Row :=
  let mask := if r.val.testBit i then 1 <<< j else 0
  ⟨((fixRow z o r).val &&& (127 ^^^ (1 <<< j)) ||| mask) % 128, Nat.mod_lt _ (by decide)⟩
lemma mappedSlice {f : Row → Row} {raw R : List Nat} {T G D L : Nat}
    (proper : checkProper G = true) (inDomain : ∀ r : Row, D.testBit (f r).val = true)
    (covered : raw.all (fun v => freeIn R (renameW f v)) = true)
    (mapped : renameW f T = G) (bound : Lower R G L) : Slice raw T D L := by
  have ⟨g0,glt,gb0⟩ := checkProper_sound proper
  refine ⟨f, R, inDomain, fun a ha => freeIn_sound (List.all_eq_true.mp covered a ha), ?_, ?_⟩
  · rw [← obs_renameW, mapped]
    exact obs_not_const g0 glt gb0
  · rw [← obs_renameW, mapped]
    exact bound


def wd4R : List Nat := varsOf 104
def wd4G : Nat := 0xffffffffff00ff00ff00ff0000000000
def wd4Pos : List Nat := [40,40,72,72,96,96]
def wd4Neg : List Nat := [32,8,64,8,64,32]
def wd4Mask : Nat := fullMask 6
def wd4Base : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,0xf,0xa),(0xffffffff00000000ffffffff00000000,0x33,0x21),(0xffffffffffffffff0000000000000000,0x3c,0x14)]
def wd4Steps : List (Nat × Nat × Nat) := []
def wd4W : BT Decor := buildWiresBT 2 wd4Base wd4Steps
def wd4AutoList : List (List (Nat × Nat)) := [[],[(3,5)],[(3,6)],[(5,6)],[(3,5),(5,6)],[(3,6),(5,6)]]
def wd4Autos : BT (List (Nat × Nat)) := btOfList 3 wd4AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd4Pairs : goodPairs wd4G wd4Pos wd4Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd4BaseOk : ∀ x ∈ wd4Base, faithful wd4Pos wd4Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd4WOk : btAll (fun x => faithful wd4Pos wd4Neg x ∧ x.1 < 2^128) wd4W := buildWiresBT_faithful wd4BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd4AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw wd4G = wd4G) wd4Autos := btAll_ofList (autos_of (by decide +kernel))
def wd4SliceList : List (Option (Nat × Nat)) := []
def wd4Slices : BT (Option (Nat × Nat)) := btOfList 1 wd4SliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd4SlicesOk : btAll (fun o => ∀ p, o = some p → Slice wd4R wd4G p.1 p.2) wd4Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice wd4R wd4G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
def wd4Empty : BT (List (List Nat)) := BT.empty
lemma wd4EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible wd4G (3 - 1) xs.toFinset) wd4Empty := trivial
def wd4Block3_0Specs : List PoolSpec := []
def wd4Block3_0Pools : BT (Option BoundPool) := buildPoolsBT 1 wd4W wd4R wd4Slices wd4Block3_0Specs
def wd4Block3_0 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd4Block3_0Ok : checkNodesBT wd4W wd4G wd4Mask wd4Block3_0Pools wd4Autos wd4Empty 3 wd4Block3_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd4Block3_0Mem : ∀ ns ∈ wd4Block3_0, Impossible wd4G 3 (nodeValsBT wd4W ns).toFinset := checkNodesBT_mem (by decide) wd4Pairs wd4WOk (buildPoolsBT_sound wd4SlicesOk) wd4AutosOk wd4EmptyOk wd4Block3_0Ok
def wd4Nodes3 : List NodeSpec := wd4Block3_0
def wd4Bucket3 : BT (List (List Nat)) := buildBucketsBT wd4W wd4Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd4Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd4G 3 xs.toFinset) wd4Bucket3 := buildBucketsBT_of_mem wd4Block3_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd4Bound : Lower wd4R wd4G 4 := lower_of_forestBT (essPairs := [(VAR 3,32,40),(VAR 5,8,40),(VAR 6,8,72)]) (by decide +kernel) wd4Bucket3Ok (by decide +kernel)
lemma wg5 : Lower (varsOf 104) 0xffffffffff00ff00ff00ff0000000000 4 := wd4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg6 : Lower (varsOf 42) 0xffccffcccc00cc00ffccffcccc00cc00 4 := carry_of (swaps := [(3, 5), (5, 6), (4, 6), (2, 4), (1, 2)]) (by decide +kernel) wg5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg7 : Lower (varsOf 74) 0xffccffccffccffcccc00cc00cc00cc00 4 := carry_of (swaps := [(3, 5), (4, 5), (2, 4), (1, 2)]) (by decide +kernel) wg5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg8 : Lower (varsOf 98) 0xffffffffcccccccccccccccc00000000 4 := carry_of (swaps := [(2, 3), (1, 2)]) (by decide +kernel) wg5
def wd3R : List Nat := varsOf 106
def wd3G : Nat := 0xffffffffffccffccffccffcccc00cc00
def wd3Pos : List Nat := [10,10,34,34,40,40,66,66,72,72,96,96]
def wd3Neg : List Nat := [8,2,32,2,32,8,64,2,64,8,64,32]
def wd3Mask : Nat := fullMask 12
def wd3Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x8a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x333,0x221),(0xffffffff00000000ffffffff00000000,0xc3c,0x814),(0xffffffffffffffff0000000000000000,0xfc0,0x540)]
def wd3Steps : List (Nat × Nat × Nat) := [(1,0,1),(1,4,2),(2,5,3),(2,4,2),(1,0,2),(1,1,2)]
def wd3W : BT Decor := buildWiresBT 4 wd3Base wd3Steps
def wd3AutoList : List (List (Nat × Nat)) := [[],[(1,3)],[(1,5)],[(1,6)],[(3,5)],[(3,6)],[(5,6)],[(1,3),(3,5)],[(1,3),(3,6)],[(1,3),(5,6)],[(1,5),(3,5)],[(1,5),(3,6)],[(1,5),(5,6)],[(1,6),(3,5)],[(1,6),(3,6)],[(1,6),(5,6)],[(3,5),(5,6)],[(3,6),(5,6)],[(1,3),(3,5),(5,6)],[(1,3),(3,6),(5,6)],[(1,5),(3,5),(3,6)],[(1,5),(5,6),(3,6)],[(1,6),(3,6),(3,5)],[(1,6),(5,6),(3,5)]]
def wd3Autos : BT (List (Nat × Nat)) := btOfList 5 wd3AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Pairs : goodPairs wd3G wd3Pos wd3Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3BaseOk : ∀ x ∈ wd3Base, faithful wd3Pos wd3Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3WOk : btAll (fun x => faithful wd3Pos wd3Neg x ∧ x.1 < 2^128) wd3W := buildWiresBT_faithful wd3BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw wd3G = wd3G) wd3Autos := btAll_ofList (autos_of (by decide +kernel))
def wd3SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 64 0,4),some (subcubeFast 32 0,4),some (subcubeFast 8 0,4),some (subcubeFast 2 0,4)]
def wd3Slices : BT (Option (Nat × Nat)) := btOfList 2 wd3SliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Slice0 : Slice wd3R wd3G (subcubeFast 64 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 42) (qGoal := 0xffccffcccc00cc00ffccffcccc00cc00) (by decide +kernel) wg6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Slice1 : Slice wd3R wd3G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 74) (qGoal := 0xffccffccffccffcccc00cc00cc00cc00) (by decide +kernel) wg7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Slice2 : Slice wd3R wd3G (subcubeFast 8 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 98) (qGoal := 0xffffffffcccccccccccccccc00000000) (by decide +kernel) wg8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Slice3 : Slice wd3R wd3G (subcubeFast 2 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 104) (qGoal := 0xffffffffff00ff00ff00ff0000000000) (by decide +kernel) wg5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3SlicesOk : btAll (fun o => ∀ p, o = some p → Slice wd3R wd3G p.1 p.2) wd3Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice wd3R wd3G p.1 p.2) (forall_cons (fun _ h => by cases h; exact wd3Slice0) (forall_cons (fun _ h => by cases h; exact wd3Slice1) (forall_cons (fun _ h => by cases h; exact wd3Slice2) (forall_cons (fun _ h => by cases h; exact wd3Slice3) (fun _ h => (List.not_mem_nil h).elim)))))
def wd3Empty : BT (List (List Nat)) := BT.empty
lemma wd3EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible wd3G (3 - 1) xs.toFinset) wd3Empty := trivial
def wd3Block3_0Specs : List PoolSpec := [(2,[]),(1,[])]
def wd3Block3_0Pools : BT (Option BoundPool) := buildPoolsBT 1 wd3W wd3R wd3Slices wd3Block3_0Specs
def wd3Block3_0 : List NodeSpec := [([6,0,1,2],[],[]),([9,8,4,3],[0,1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Block3_0Ok : checkNodesBT wd3W wd3G wd3Mask wd3Block3_0Pools wd3Autos wd3Empty 3 wd3Block3_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Block3_0Mem : ∀ ns ∈ wd3Block3_0, Impossible wd3G 3 (nodeValsBT wd3W ns).toFinset := checkNodesBT_mem (by decide) wd3Pairs wd3WOk (buildPoolsBT_sound wd3SlicesOk) wd3AutosOk wd3EmptyOk wd3Block3_0Ok
def wd3Nodes3 : List NodeSpec := wd3Block3_0
def wd3Bucket3 : BT (List (List Nat)) := buildBucketsBT wd3W wd3Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd3G 3 xs.toFinset) wd3Bucket3 := buildBucketsBT_of_mem wd3Block3_0Mem
def wd3Block4_0Specs : List PoolSpec := [(0,[]),(1,[]),(2,[])]
def wd3Block4_0Pools : BT (Option BoundPool) := buildPoolsBT 2 wd3W wd3R wd3Slices wd3Block4_0Specs
def wd3Block4_0 : List NodeSpec := [([5,0,1,2,3],[0],[0]),([7,0,1,2,3],[],[]),([8,4,1,2,3],[1,2],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Block4_0Ok : checkNodesBT wd3W wd3G wd3Mask wd3Block4_0Pools wd3Autos wd3Bucket3 4 wd3Block4_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Block4_0Mem : ∀ ns ∈ wd3Block4_0, Impossible wd3G 4 (nodeValsBT wd3W ns).toFinset := checkNodesBT_mem (by decide) wd3Pairs wd3WOk (buildPoolsBT_sound wd3SlicesOk) wd3AutosOk wd3Bucket3Ok wd3Block4_0Ok
def wd3Nodes4 : List NodeSpec := wd3Block4_0
def wd3Bucket4 : BT (List (List Nat)) := buildBucketsBT wd3W wd3Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd3G 4 xs.toFinset) wd3Bucket4 := buildBucketsBT_of_mem wd3Block4_0Mem
def wd3Block5_0Specs : List PoolSpec := [(2,[]),(3,[]),(1,[]),(0,[])]
def wd3Block5_0Pools : BT (Option BoundPool) := buildPoolsBT 2 wd3W wd3R wd3Slices wd3Block5_0Specs
def wd3Block5_0 : List NodeSpec := [([4,0,1,2,3],[0,1,2,3],[0,6,1,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Block5_0Ok : checkNodesBT wd3W wd3G wd3Mask wd3Block5_0Pools wd3Autos wd3Bucket4 5 wd3Block5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Block5_0Mem : ∀ ns ∈ wd3Block5_0, Impossible wd3G 5 (nodeValsBT wd3W ns).toFinset := checkNodesBT_mem (by decide) wd3Pairs wd3WOk (buildPoolsBT_sound wd3SlicesOk) wd3AutosOk wd3Bucket4Ok wd3Block5_0Ok
def wd3Nodes5 : List NodeSpec := wd3Block5_0
def wd3Bucket5 : BT (List (List Nat)) := buildBucketsBT wd3W wd3Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd3G 5 xs.toFinset) wd3Bucket5 := buildBucketsBT_of_mem wd3Block5_0Mem
def wd3Block6_0Specs : List PoolSpec := [(2,[]),(3,[]),(1,[]),(0,[])]
def wd3Block6_0Pools : BT (Option BoundPool) := buildPoolsBT 2 wd3W wd3R wd3Slices wd3Block6_0Specs
def wd3Block6_0 : List NodeSpec := [([0,1,2,3],[0,1,2,3],[0,2,3,4,5,11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Block6_0Ok : checkNodesBT wd3W wd3G wd3Mask wd3Block6_0Pools wd3Autos wd3Bucket5 6 wd3Block6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Block6_0Mem : ∀ ns ∈ wd3Block6_0, Impossible wd3G 6 (nodeValsBT wd3W ns).toFinset := checkNodesBT_mem (by decide) wd3Pairs wd3WOk (buildPoolsBT_sound wd3SlicesOk) wd3AutosOk wd3Bucket5Ok wd3Block6_0Ok
def wd3Nodes6 : List NodeSpec := wd3Block6_0
def wd3Bucket6 : BT (List (List Nat)) := buildBucketsBT wd3W wd3Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd3G 6 xs.toFinset) wd3Bucket6 := buildBucketsBT_of_mem wd3Block6_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd3Bound : Lower wd3R wd3G 7 := lower_of_forestBT (essPairs := [(VAR 1,8,10),(VAR 3,2,10),(VAR 5,2,34),(VAR 6,2,66)]) (by decide +kernel) wd3Bucket6Ok (by decide +kernel)
lemma wg9 : Lower (varsOf 106) 0xffffffffffccffccffccffcccc00cc00 7 := wd3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg10 : Lower (varsOf 110) 0xfffffffffffcfffcffccffcccc00cc00 8 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,64,68)]) (by decide +kernel) wg9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg11 : Lower (varsOf 93) 0xfffffffafffffffafafaa0a0fafaa0a0 8 := carry_of (swaps := [(0, 1), (2, 3), (4, 5)]) (by decide +kernel) wg10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg13 : Lower (varsOf 120) 0xffffffffffffff00ff00ff0000000000 5 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,64,80)]) (by decide +kernel) wg5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg14 : Lower (varsOf 92) 0xfffffff0fffffff0f0f00000f0f00000 5 := carry_of (swaps := [(3, 4), (4, 5), (2, 5)]) (by decide +kernel) wg13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg15 : Lower (varsOf 108) 0xfffffffffff0fff0ff00ff0000000000 5 := carry_of (swaps := [(2, 4)]) (by decide +kernel) wg13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg16 : Lower (varsOf 116) 0xfffffffffffff0f0f0f00000f0f00000 5 := carry_of (swaps := [(2, 3), (4, 5)]) (by decide +kernel) wg13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg17 : Lower (varsOf 84) 0xfffff0f0fffff0f0f0f00000f0f00000 4 := carry_of (swaps := [(2, 3), (4, 5)]) (by decide +kernel) wg5
def wd12R : List Nat := varsOf 124
def wd12G : Nat := 0xfffffffffffffff0fff0ff00f0f00000
def wd12Pos : List Nat := [20,20,28,28,40,40,44,44,52,52,56,56,68,68,72,72,76,80,80,88,96,96,100,112]
def wd12Neg : List Nat := [16,4,24,12,32,8,36,12,48,36,48,24,64,4,64,8,12,64,16,24,64,32,36,48]
def wd12Mask : Nat := fullMask 24
def wd12Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x4133cf,0x4122ca),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x9ccfc,0x988ac),(0xffff0000ffff0000ffff0000ffff0000,0x8e0f0f,0x8c0d05),(0xffffffff00000000ffffffff00000000,0xf00ff0,0xe00750),(0xffffffffffffffff0000000000000000,0xfff000,0x125000)]
def wd12Steps : List (Nat × Nat × Nat) := [(1,0,1),(0,5,4),(1,6,2),(1,0,4),(1,5,4),(2,9,2),(2,5,4),(3,5,4),(2,8,0),(2,8,1),(2,8,2),(1,13,1),(2,16,3)]
def wd12W : BT Decor := buildWiresBT 5 wd12Base wd12Steps
def wd12AutoList : List (List (Nat × Nat)) := [[],[(2,4)],[(3,5)],[(2,3),(4,5)],[(2,4),(3,5)],[(2,5),(3,4)],[(2,3),(3,4),(4,5)],[(2,5),(4,5),(3,4)]]
def wd12Autos : BT (List (Nat × Nat)) := btOfList 3 wd12AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Pairs : goodPairs wd12G wd12Pos wd12Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12BaseOk : ∀ x ∈ wd12Base, faithful wd12Pos wd12Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12WOk : btAll (fun x => faithful wd12Pos wd12Neg x ∧ x.1 < 2^128) wd12W := buildWiresBT_faithful wd12BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw wd12G = wd12G) wd12Autos := btAll_ofList (autos_of (by decide +kernel))
def wd12SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,5),some (subcubeFast 16 0,5),some (subcubeFast 8 0,5),some (subcubeFast 4 0,5),some (subcubeFast 40 0,4),some (subcubeFast 20 0,4)]
def wd12Slices : BT (Option (Nat × Nat)) := btOfList 3 wd12SliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Slice0 : Slice wd12R wd12G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 92) (qGoal := 0xfffffff0fffffff0f0f00000f0f00000) (by decide +kernel) wg14
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Slice1 : Slice wd12R wd12G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 108) (qGoal := 0xfffffffffff0fff0ff00ff0000000000) (by decide +kernel) wg15
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Slice2 : Slice wd12R wd12G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 116) (qGoal := 0xfffffffffffff0f0f0f00000f0f00000) (by decide +kernel) wg16
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Slice3 : Slice wd12R wd12G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 120) (qGoal := 0xffffffffffffff00ff00ff0000000000) (by decide +kernel) wg13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Slice4 : Slice wd12R wd12G (subcubeFast 40 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 84) (qGoal := 0xfffff0f0fffff0f0f0f00000f0f00000) (by decide +kernel) wg17
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Slice5 : Slice wd12R wd12G (subcubeFast 20 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 104) (qGoal := 0xffffffffff00ff00ff00ff0000000000) (by decide +kernel) wg5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12SlicesOk : btAll (fun o => ∀ p, o = some p → Slice wd12R wd12G p.1 p.2) wd12Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice wd12R wd12G p.1 p.2) (forall_cons (fun _ h => by cases h; exact wd12Slice0) (forall_cons (fun _ h => by cases h; exact wd12Slice1) (forall_cons (fun _ h => by cases h; exact wd12Slice2) (forall_cons (fun _ h => by cases h; exact wd12Slice3) (forall_cons (fun _ h => by cases h; exact wd12Slice4) (forall_cons (fun _ h => by cases h; exact wd12Slice5) (fun _ h => (List.not_mem_nil h).elim)))))))
def wd12Empty : BT (List (List Nat)) := BT.empty
lemma wd12EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible wd12G (3 - 1) xs.toFinset) wd12Empty := trivial
def wd12Block3_0Specs : List PoolSpec := []
def wd12Block3_0Pools : BT (Option BoundPool) := buildPoolsBT 1 wd12W wd12R wd12Slices wd12Block3_0Specs
def wd12Block3_0 : List NodeSpec := [([8,7,1,3],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Block3_0Ok : checkNodesBT wd12W wd12G wd12Mask wd12Block3_0Pools wd12Autos wd12Empty 3 wd12Block3_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Block3_0Mem : ∀ ns ∈ wd12Block3_0, Impossible wd12G 3 (nodeValsBT wd12W ns).toFinset := checkNodesBT_mem (by decide) wd12Pairs wd12WOk (buildPoolsBT_sound wd12SlicesOk) wd12AutosOk wd12EmptyOk wd12Block3_0Ok
def wd12Nodes3 : List NodeSpec := wd12Block3_0
def wd12Bucket3 : BT (List (List Nat)) := buildBucketsBT wd12W wd12Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd12G 3 xs.toFinset) wd12Bucket3 := buildBucketsBT_of_mem wd12Block3_0Mem
def wd12Block4_0Specs : List PoolSpec := []
def wd12Block4_0Pools : BT (Option BoundPool) := buildPoolsBT 1 wd12W wd12R wd12Slices wd12Block4_0Specs
def wd12Block4_0 : List NodeSpec := [([7,0,1,3,4],[],[0]),([8,6,1,2,3],[],[0]),([10,0,1,3,4],[],[]),([17,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Block4_0Ok : checkNodesBT wd12W wd12G wd12Mask wd12Block4_0Pools wd12Autos wd12Bucket3 4 wd12Block4_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Block4_0Mem : ∀ ns ∈ wd12Block4_0, Impossible wd12G 4 (nodeValsBT wd12W ns).toFinset := checkNodesBT_mem (by decide) wd12Pairs wd12WOk (buildPoolsBT_sound wd12SlicesOk) wd12AutosOk wd12Bucket3Ok wd12Block4_0Ok
def wd12Nodes4 : List NodeSpec := wd12Block4_0
def wd12Bucket4 : BT (List (List Nat)) := buildBucketsBT wd12W wd12Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd12G 4 xs.toFinset) wd12Bucket4 := buildBucketsBT_of_mem wd12Block4_0Mem
def wd12Block5_0Specs : List PoolSpec := [(2,[]),(3,[]),(1,[]),(0,[]),(5,[])]
def wd12Block5_0Pools : BT (Option BoundPool) := buildPoolsBT 3 wd12W wd12R wd12Slices wd12Block5_0Specs
def wd12Block5_0 : List NodeSpec := [([6,0,1,2,3,4],[0,1,2,3],[0,3]),([9,0,1,2,3,4],[2,3],[0,3]),([11,0,1,2,3,4],[],[]),([12,0,1,2,3,4],[],[]),([8,5,1,2,3,4],[0,4],[0]),([13,8,1,2,3,4],[4],[]),([14,0,1,2,3,4],[],[]),([15,0,1,3,4],[],[]),([15,8,0,1,3,4],[4],[]),([16,0,1,2,3,4],[3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Block5_0Ok : checkNodesBT wd12W wd12G wd12Mask wd12Block5_0Pools wd12Autos wd12Bucket4 5 wd12Block5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Block5_0Mem : ∀ ns ∈ wd12Block5_0, Impossible wd12G 5 (nodeValsBT wd12W ns).toFinset := checkNodesBT_mem (by decide) wd12Pairs wd12WOk (buildPoolsBT_sound wd12SlicesOk) wd12AutosOk wd12Bucket4Ok wd12Block5_0Ok
def wd12Nodes5 : List NodeSpec := wd12Block5_0
def wd12Bucket5 : BT (List (List Nat)) := buildBucketsBT wd12W wd12Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd12G 5 xs.toFinset) wd12Bucket5 := buildBucketsBT_of_mem wd12Block5_0Mem
def wd12Block6_0Specs : List PoolSpec := [(5,[]),(4,[]),(2,[]),(0,[])]
def wd12Block6_0Pools : BT (Option BoundPool) := buildPoolsBT 2 wd12W wd12R wd12Slices wd12Block6_0Specs
def wd12Block6_0 : List NodeSpec := [([5,0,1,2,3,4],[0,1],[0,3]),([8,0,1,2,3,4],[0,2,3],[0,2]),([13,0,1,2,3,4],[0,2,3],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Block6_0Ok : checkNodesBT wd12W wd12G wd12Mask wd12Block6_0Pools wd12Autos wd12Bucket5 6 wd12Block6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Block6_0Mem : ∀ ns ∈ wd12Block6_0, Impossible wd12G 6 (nodeValsBT wd12W ns).toFinset := checkNodesBT_mem (by decide) wd12Pairs wd12WOk (buildPoolsBT_sound wd12SlicesOk) wd12AutosOk wd12Bucket5Ok wd12Block6_0Ok
def wd12Nodes6 : List NodeSpec := wd12Block6_0
def wd12Bucket6 : BT (List (List Nat)) := buildBucketsBT wd12W wd12Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd12G 6 xs.toFinset) wd12Bucket6 := buildBucketsBT_of_mem wd12Block6_0Mem
def wd12Block7_0Specs : List PoolSpec := [(5,[]),(4,[])]
def wd12Block7_0Pools : BT (Option BoundPool) := buildPoolsBT 1 wd12W wd12R wd12Slices wd12Block7_0Specs
def wd12Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1],[0,1,5,3,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Block7_0Ok : checkNodesBT wd12W wd12G wd12Mask wd12Block7_0Pools wd12Autos wd12Bucket6 7 wd12Block7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Block7_0Mem : ∀ ns ∈ wd12Block7_0, Impossible wd12G 7 (nodeValsBT wd12W ns).toFinset := checkNodesBT_mem (by decide) wd12Pairs wd12WOk (buildPoolsBT_sound wd12SlicesOk) wd12AutosOk wd12Bucket6Ok wd12Block7_0Ok
def wd12Nodes7 : List NodeSpec := wd12Block7_0
def wd12Bucket7 : BT (List (List Nat)) := buildBucketsBT wd12W wd12Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd12G 7 xs.toFinset) wd12Bucket7 := buildBucketsBT_of_mem wd12Block7_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd12Bound : Lower wd12R wd12G 8 := lower_of_forestBT (essPairs := [(VAR 2,16,20),(VAR 3,32,40),(VAR 4,4,20),(VAR 5,8,40),(VAR 6,4,68)]) (by decide +kernel) wd12Bucket7Ok (by decide +kernel)
lemma wg18 : Lower (varsOf 124) 0xfffffffffffffff0fff0ff00f0f00000 8 := wd12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg19 : Lower (varsOf 109) 0xfffffffffffafffaffa0ffa0a0a0a0a0 8 := carry_of (swaps := [(2, 4), (1, 4), (0, 1)]) (by decide +kernel) wg18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg20 : Lower (varsOf 117) 0xfffffffffffffafafafaa0a0fafaa0a0 8 := carry_of (swaps := [(3, 4), (4, 5), (2, 5), (0, 1)]) (by decide +kernel) wg10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg21 : Lower (varsOf 121) 0xffffffffffffffaaffaaff00aaaa0000 8 := carry_of (swaps := [(1, 2), (0, 1)]) (by decide +kernel) wg18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg22 : Lower (varsOf 85) 0xfffffafafffffafafafaa0a0fafaa0a0 7 := carry_of (swaps := [(0, 1), (2, 3), (4, 5)]) (by decide +kernel) wg9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg23 : Lower (varsOf 106) 0xffffffffffffffffffccffcccc00cc00 5 := lift_of (z := 64) (o := 0) (essPairs := [(VAR 6,0,64)]) (by decide +kernel) wg6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg24 : Lower (varsOf 53) 0xfffffffffafaa0a0fffffffffafaa0a0 5 := carry_of (swaps := [(5, 6), (4, 6), (2, 3), (0, 1)]) (by decide +kernel) wg23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg25 : Lower (varsOf 61) 0xfffaffa0fafaa0a0fffaffa0fafaa0a0 6 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,32,40)]) (by decide +kernel) wg24
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg26 : Lower (varsOf 122) 0xffffffffffffffffffffffccffffcc00 6 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,0,16)]) (by decide +kernel) wg23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg27 : Lower (varsOf 93) 0xfffffffffffffffffffaffa0fffaffa0 6 := carry_of (swaps := [(3, 4), (4, 5), (2, 5), (0, 1)]) (by decide +kernel) wg26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg28 : Lower (varsOf 117) 0xfffffffffffffffffffffffffafaa0a0 6 := carry_of (swaps := [(0, 1), (2, 3), (4, 5)]) (by decide +kernel) wg26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg29 : Lower (varsOf 29) 0xfffaffa0fffaffa0fffaffa0fffaffa0 5 := carry_of (swaps := [(3, 6), (4, 6), (4, 5), (2, 5), (0, 1)]) (by decide +kernel) wg23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg30 : Lower (varsOf 77) 0xfffafffafffafffaa0a0a0a0a0a0a0a0 5 := carry_of (swaps := [(2, 5), (3, 4), (1, 4), (0, 1)]) (by decide +kernel) wg13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg31 : Lower (varsOf 101) 0xfffffffffafafafaa0a0a0a0a0a0a0a0 5 := carry_of (swaps := [(4, 5), (2, 4), (1, 3), (0, 1)]) (by decide +kernel) wg13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg32 : Lower (varsOf 85) 0xfffffffffffffffffafaa0a0fafaa0a0 5 := carry_of (swaps := [(0, 1), (2, 3), (4, 5)]) (by decide +kernel) wg23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg33 : Lower (varsOf 113) 0xffffffffffffaaaaaaaa0000aaaa0000 5 := carry_of (swaps := [(4, 5), (2, 3), (1, 2), (0, 1)]) (by decide +kernel) wg13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg34 : Lower (varsOf 21) 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0 4 := carry_of (swaps := [(4, 6), (2, 5), (1, 3), (0, 1)]) (by decide +kernel) wg5
def wd2R : List Nat := varsOf 125
def wd2G : Nat := 0xfffffffffffffffafffaffa0fafaa0a0
def wd2Pos : List Nat := [5,5,13,13,17,17,20,20,25,25,28,28,37,37,40,40,41,41,44,44,49,49,52,52,56,56,65,65,68,68,72,72,73,76,80,80,88,96,96,97,100,112]
def wd2Neg : List Nat := [4,1,12,9,16,1,16,4,24,9,24,12,36,33,32,8,33,9,36,12,48,33,48,36,48,24,64,1,64,4,64,8,9,12,64,16,24,64,32,33,36,48]
def wd2Mask : Nat := fullMask 42
def wd2Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x810c33333f,0x810823222a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x10230cc3ccf,0x102208c1885),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x13c30fcf0c,0x13820a8f0c),(0xffff0000ffff0000ffff0000ffff0000,0x21c03f00ff0,0x21803500550),(0xffffffff00000000ffffffff00000000,0x3e003fff000,0x3c001f57000),(0xffffffffffffffff0000000000000000,0x3fffc000000,0x2454000000)]
def wd2Steps : List (Nat × Nat × Nat) := [(1,0,1),(1,6,2),(2,7,3),(0,7,5),(1,9,3),(1,6,5),(1,0,5),(1,9,4),(1,2,5),(1,7,5),(2,15,0),(2,15,3),(2,15,4),(2,7,5),(3,7,5),(1,20,6),(1,20,0),(2,11,3),(1,1,5),(2,6,2),(1,25,4),(1,6,3),(1,27,5),(2,28,0),(2,28,1),(1,3,5),(2,14,4),(3,2,5),(1,33,27),(2,34,0),(1,33,0),(2,6,3),(1,37,5),(1,2,3),(3,3,5),(2,12,37),(2,12,3),(1,40,1),(0,39,5),(1,44,37),(1,44,0),(1,44,4),(3,39,5),(1,48,0),(2,14,3),(1,33,37),(1,40,0),(1,40,2),(2,53,4),(0,6,5),(1,55,2),(1,55,3),(2,12,55),(2,11,0),(1,59,3),(2,59,3),(1,1,3),(2,11,1),(0,11,3),(3,64,15),(2,11,2),(1,23,2),(2,67,4),(2,23,2),(2,23,1),(1,0,3),(3,33,11),(2,11,6),(1,23,6),(2,23,6),(2,6,5),(1,73,3),(1,73,0),(1,73,1),(1,73,2),(2,80,4),(0,0,1),(3,82,6),(1,82,3),(1,82,5),(1,33,62),(1,24,3),(1,33,71),(1,33,1),(1,63,3),(1,12,3),(1,12,2),(2,92,1),(2,92,4),(2,12,2),(2,91,6),(2,24,3),(1,44,6),(1,39,5),(2,99,6),(2,99,4),(2,39,5),(1,48,6),(2,14,6),(1,104,1),(2,21,3),(1,50,6),(2,21,0),(2,21,1),(0,21,3),(3,82,106),(3,33,6),(2,36,3),(1,33,3),(2,114,6),(1,96,0),(1,96,1),(2,31,2),(1,118,6),(1,118,0),(2,74,0),(2,74,1),(1,0,2),(2,123,1),(1,124,3),(1,125,5),(2,125,5),(2,31,1),(1,124,5),(2,129,3),(2,12,124),(2,31,124),(0,123,5),(1,133,1),(1,134,3),(2,135,0),(2,134,3),(0,12,134),(1,138,3),(2,12,134),(2,91,134),(1,133,4),(2,11,133),(1,93,3),(2,123,5),(3,123,5),(1,146,1),(2,147,3),(0,24,123),(1,1,2),(3,24,123),(2,14,1),(1,152,3),(2,12,0),(2,79,3),(1,63,2),(2,156,4),(2,63,2),(1,158,1),(1,70,1),(2,90,0),(2,159,3),(3,1,5),(1,163,3),(1,79,3),(2,165,1),(1,154,3),(1,154,2),(2,168,4),(0,1,3),(1,170,0),(1,170,5),(2,62,170),(2,1,3),(3,1,3),(2,14,0),(2,105,3),(1,109,3),(1,175,0)]
def wd2W : BT Decor := buildWiresBT 8 wd2Base wd2Steps
def wd2AutoList : List (List (Nat × Nat)) := [[],[(0,2)],[(0,4)],[(2,4)],[(3,5)],[(0,2),(2,4)],[(0,2),(3,5)],[(0,4),(2,4)],[(0,4),(3,5)],[(2,4),(3,5)],[(0,2),(2,4),(3,5)],[(0,4),(2,4),(3,5)]]
def wd2Autos : BT (List (Nat × Nat)) := btOfList 4 wd2AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Pairs : goodPairs wd2G wd2Pos wd2Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2BaseOk : ∀ x ∈ wd2Base, faithful wd2Pos wd2Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2WOk : btAll (fun x => faithful wd2Pos wd2Neg x ∧ x.1 < 2^128) wd2W := buildWiresBT_faithful wd2BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw wd2G = wd2G) wd2Autos := btAll_ofList (autos_of (by decide +kernel))
def wd2SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,8),some (subcubeFast 16 0,8),some (subcubeFast 8 0,8),some (subcubeFast 4 0,8),some (subcubeFast 1 0,8),some (subcubeFast 40 0,7),some (subcubeFast 64 0,6),some (subcubeFast 0 32,6),some (subcubeFast 0 8,6),some (subcubeFast 64 32,5),some (subcubeFast 48 0,5),some (subcubeFast 24 0,5),some (subcubeFast 64 8,5),some (subcubeFast 32 8,5),some (subcubeFast 12 0,5),some (subcubeFast 9 0,5),some (subcubeFast 96 0,4),some (subcubeFast 72 0,4),some (subcubeFast 104 0,4),some (subcubeFast 72 32,4),some (subcubeFast 41 0,4),some (subcubeFast 21 0,4)]
def wd2Slices : BT (Option (Nat × Nat)) := btOfList 5 wd2SliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice0 : Slice wd2R wd2G (subcubeFast 32 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 93) (qGoal := 0xfffffffafffffffafafaa0a0fafaa0a0) (by decide +kernel) wg11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice1 : Slice wd2R wd2G (subcubeFast 16 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 109) (qGoal := 0xfffffffffffafffaffa0ffa0a0a0a0a0) (by decide +kernel) wg19
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice2 : Slice wd2R wd2G (subcubeFast 8 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 117) (qGoal := 0xfffffffffffffafafafaa0a0fafaa0a0) (by decide +kernel) wg20
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice3 : Slice wd2R wd2G (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 121) (qGoal := 0xffffffffffffffaaffaaff00aaaa0000) (by decide +kernel) wg21
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice4 : Slice wd2R wd2G (subcubeFast 1 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 124) (qGoal := 0xfffffffffffffff0fff0ff00f0f00000) (by decide +kernel) wg18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice5 : Slice wd2R wd2G (subcubeFast 40 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 85) (qGoal := 0xfffffafafffffafafafaa0a0fafaa0a0) (by decide +kernel) wg22
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice6 : Slice wd2R wd2G (subcubeFast 64 0) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffaffa0fafaa0a0fffaffa0fafaa0a0) (by decide +kernel) wg25
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice7 : Slice wd2R wd2G (subcubeFast 0 32) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 93) (qGoal := 0xfffffffffffffffffffaffa0fffaffa0) (by decide +kernel) wg27
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice8 : Slice wd2R wd2G (subcubeFast 0 8) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 117) (qGoal := 0xfffffffffffffffffffffffffafaa0a0) (by decide +kernel) wg28
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice9 : Slice wd2R wd2G (subcubeFast 64 32) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 29) (qGoal := 0xfffaffa0fffaffa0fffaffa0fffaffa0) (by decide +kernel) wg29
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice10 : Slice wd2R wd2G (subcubeFast 48 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 77) (qGoal := 0xfffafffafffafffaa0a0a0a0a0a0a0a0) (by decide +kernel) wg30
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice11 : Slice wd2R wd2G (subcubeFast 24 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 101) (qGoal := 0xfffffffffafafafaa0a0a0a0a0a0a0a0) (by decide +kernel) wg31
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice12 : Slice wd2R wd2G (subcubeFast 64 8) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 53) (qGoal := 0xfffffffffafaa0a0fffffffffafaa0a0) (by decide +kernel) wg24
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice13 : Slice wd2R wd2G (subcubeFast 32 8) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 85) (qGoal := 0xfffffffffffffffffafaa0a0fafaa0a0) (by decide +kernel) wg32
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice14 : Slice wd2R wd2G (subcubeFast 12 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 113) (qGoal := 0xffffffffffffaaaaaaaa0000aaaa0000) (by decide +kernel) wg33
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice15 : Slice wd2R wd2G (subcubeFast 9 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 116) (qGoal := 0xfffffffffffff0f0f0f00000f0f00000) (by decide +kernel) wg16
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice16 : Slice wd2R wd2G (subcubeFast 96 0) 4 := slice_fast_direct (zDead := 8) (qRoots := varsOf 21) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) wg34
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice17 : Slice wd2R wd2G (subcubeFast 72 0) 4 := slice_fast_direct (zDead := 32) (qRoots := varsOf 21) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) wg34
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice18 : Slice wd2R wd2G (subcubeFast 104 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 21) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) wg34
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice19 : Slice wd2R wd2G (subcubeFast 72 32) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 21) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) wg34
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice20 : Slice wd2R wd2G (subcubeFast 41 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 84) (qGoal := 0xfffff0f0fffff0f0f0f00000f0f00000) (by decide +kernel) wg17
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Slice21 : Slice wd2R wd2G (subcubeFast 21 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 104) (qGoal := 0xffffffffff00ff00ff00ff0000000000) (by decide +kernel) wg5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2SlicesOk : btAll (fun o => ∀ p, o = some p → Slice wd2R wd2G p.1 p.2) wd2Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice wd2R wd2G p.1 p.2) (forall_cons (fun _ h => by cases h; exact wd2Slice0) (forall_cons (fun _ h => by cases h; exact wd2Slice1) (forall_cons (fun _ h => by cases h; exact wd2Slice2) (forall_cons (fun _ h => by cases h; exact wd2Slice3) (forall_cons (fun _ h => by cases h; exact wd2Slice4) (forall_cons (fun _ h => by cases h; exact wd2Slice5) (forall_cons (fun _ h => by cases h; exact wd2Slice6) (forall_cons (fun _ h => by cases h; exact wd2Slice7) (forall_cons (fun _ h => by cases h; exact wd2Slice8) (forall_cons (fun _ h => by cases h; exact wd2Slice9) (forall_cons (fun _ h => by cases h; exact wd2Slice10) (forall_cons (fun _ h => by cases h; exact wd2Slice11) (forall_cons (fun _ h => by cases h; exact wd2Slice12) (forall_cons (fun _ h => by cases h; exact wd2Slice13) (forall_cons (fun _ h => by cases h; exact wd2Slice14) (forall_cons (fun _ h => by cases h; exact wd2Slice15) (forall_cons (fun _ h => by cases h; exact wd2Slice16) (forall_cons (fun _ h => by cases h; exact wd2Slice17) (forall_cons (fun _ h => by cases h; exact wd2Slice18) (forall_cons (fun _ h => by cases h; exact wd2Slice19) (forall_cons (fun _ h => by cases h; exact wd2Slice20) (forall_cons (fun _ h => by cases h; exact wd2Slice21) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))
def wd2Empty : BT (List (List Nat)) := BT.empty
lemma wd2EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible wd2G (4 - 1) xs.toFinset) wd2Empty := trivial
def wd2Block4_0Specs : List PoolSpec := [(3,[(1,6,5),(1,6,2),(0,7,5),(1,9,3)])]
def wd2Block4_0Pools : BT (Option BoundPool) := buildPoolsBT 1 wd2W wd2R wd2Slices wd2Block4_0Specs
def wd2Block4_0 : List NodeSpec := [([14,47,37,0,1],[],[]),([83,81,2,3,5],[],[]),([84,81,6,2,5],[],[]),([85,81,6,2,3],[],[]),([111,6,2,4,5],[],[]),([83,106,2,4,5],[],[]),([85,106,6,2,4],[],[]),([128,12,125,2,4],[],[]),([139,12,134,2,4],[0],[]),([23,12,134,2,4],[],[]),([141,12,2,3,4],[],[]),([128,155,12,2,4],[],[]),([62,171,169,2,5],[],[]),([62,172,169,0,2],[],[]),([173,169,0,2,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block4_0Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block4_0Pools wd2Autos wd2Empty 4 wd2Block4_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block4_0Mem : ∀ ns ∈ wd2Block4_0, Impossible wd2G 4 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2EmptyOk wd2Block4_0Ok
def wd2Nodes4 : List NodeSpec := wd2Block4_0
def wd2Bucket4 : BT (List (List Nat)) := buildBucketsBT wd2W wd2Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd2G 4 xs.toFinset) wd2Bucket4 := buildBucketsBT_of_mem wd2Block4_0Mem
def wd2Block5_0Specs : List PoolSpec := [(3,[(1,6,5),(1,6,2),(0,7,5),(1,9,3)]),(3,[(1,2,5),(1,6,2),(0,7,5),(1,9,4)]),(6,[]),(21,[])]
def wd2Block5_0Pools : BT (Option BoundPool) := buildPoolsBT 2 wd2W wd2R wd2Slices wd2Block5_0Specs
def wd2Block5_0 : List NodeSpec := [([11,10,0,1,2,4],[0],[]),([12,10,6,1,2,4],[],[]),([14,13,6,0,1,3],[1],[]),([30,29,2,3,4,5],[],[]),([31,24,12,27,2,4],[2],[]),([35,1,2,3,4,5],[],[]),([24,41,12,2,3,4],[3],[]),([24,42,12,37,2,4],[],[]),([39,24,12,37,2,4],[],[]),([40,24,12,37,2,4],[],[]),([43,12,37,2,4],[],[]),([43,40,12,37,2,4],[],[]),([43,12,37,2,4,5],[],[]),([45,0,1,2,4,5],[],[]),([46,37,1,2,4,5],[],[]),([47,37,0,1,2,5],[],[0]),([14,44,37,0,1,4],[],[0]),([49,37,1,2,4,5],[],[]),([43,52,37,2,4,5],[3],[]),([54,37,0,1,2,5],[],[]),([62,61,11,2,4,5],[3],[]),([31,61,11,1,2,4],[3],[]),([31,63,59,2,3,4],[],[]),([40,63,59,2,3,4],[],[]),([64,63,59,2,4,5],[],[]),([23,63,59,2,4,5],[],[]),([31,62,59,11,2,4],[3],[]),([64,16,1,2,4,5],[],[]),([64,18,0,1,2,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block5_0Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block5_0Pools wd2Autos wd2Bucket4 5 wd2Block5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block5_0Mem : ∀ ns ∈ wd2Block5_0, Impossible wd2G 5 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket4Ok wd2Block5_0Ok
def wd2Block5_1Specs : List PoolSpec := [(21,[]),(14,[(2,14,4)]),(11,[(2,14,4)]),(4,[]),(15,[(2,92,4)]),(9,[]),(3,[(1,3,5),(1,2,3),(0,39,5),(1,44,6)]),(11,[]),(3,[(1,2,5),(1,2,3),(0,39,5),(1,44,4)]),(5,[(1,0,1),(1,6,5),(2,11,3)]),(6,[])]
def wd2Block5_1Pools : BT (Option BoundPool) := buildPoolsBT 4 wd2W wd2R wd2Slices wd2Block5_1Specs
def wd2Block5_1 : List NodeSpec := [([23,18,0,1,2,5],[],[]),([65,0,1,2,4,5],[],[]),([68,23,0,1,2,5],[],[]),([32,23,0,1,2,5],[],[]),([70,61,11,2,4,5],[0],[]),([70,61,6,2,4,5],[0],[]),([82,81,6,2,3,5],[],[0]),([32,62,71,6,2,5],[1,2],[]),([86,71,6,2,4,5],[3],[]),([31,61,24,6,2,4],[0],[]),([42,90,6,2,4,5],[0],[]),([31,42,63,6,2,4],[0],[]),([24,94,12,6,2,3],[4,5],[]),([24,96,12,2,3,4],[0],[]),([97,24,42,6,2,4],[],[]),([97,42,6,2,4,5],[0],[]),([31,24,42,6,2,4],[0],[]),([32,24,12,6,2,3],[1,5],[]),([43,31,12,6,2,4],[0],[]),([31,98,0,1,2,4],[6],[]),([31,46,6,1,2,4],[],[]),([14,47,6,0,1,3],[7,8],[0]),([106,14,0,1,4,5],[9],[]),([109,108,2,3,4,5],[],[]),([110,108,1,2,4,5],[],[]),([82,106,6,2,4,5],[],[0]),([117,116,2,3,4,5],[0],[]),([122,121,2,3,4,5],[],[]),([31,12,125,1,2,4],[10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block5_1Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block5_1Pools wd2Autos wd2Bucket4 5 wd2Block5_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block5_1Mem : ∀ ns ∈ wd2Block5_1, Impossible wd2G 5 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket4Ok wd2Block5_1Ok
def wd2Block5_2Specs : List PoolSpec := [(1,[(1,0,5),(1,0,2),(0,123,5),(1,133,1)]),(12,[]),(15,[]),(9,[]),(16,[]),(3,[(1,6,5),(1,6,2),(0,7,5)]),(4,[]),(3,[(3,2,5),(1,33,0),(2,36,3)])]
def wd2Block5_2Pools : BT (Option BoundPool) := buildPoolsBT 3 wd2W wd2R wd2Slices wd2Block5_2Specs
def wd2Block5_2 : List NodeSpec := [([128,125,0,2,4,5],[],[0]),([128,12,124,2,3,4],[],[0]),([136,134,2,3,4,5],[],[]),([12,135,134,2,3,4],[0],[]),([12,137,134,2,3,4],[0],[]),([138,12,134,2,3,4],[1,2,0,3,4,5],[0]),([11,12,134,2,3,4],[0,5],[0]),([140,12,134,2,3,4],[],[]),([91,12,134,2,3,4],[5,0],[0]),([42,12,134,2,3,4],[0],[]),([12,137,1,2,3,4],[0],[]),([140,12,1,2,3,4],[],[]),([63,12,134,2,3,4],[],[]),([143,12,1,2,3,4],[],[3]),([23,12,133,1,2,4],[],[0,3]),([31,155,12,1,2,4],[6],[0]),([128,79,12,2,3,4],[],[0]),([94,23,0,1,2,5],[],[]),([108,63,2,3,4,5],[],[]),([121,63,2,3,4,5],[],[2]),([31,160,63,0,2,4],[],[2]),([121,40,63,2,3,4],[],[2]),([171,169,1,2,3,5],[],[0]),([172,169,0,1,2,3],[],[0]),([62,170,169,0,2,5],[],[0]),([175,174,169,0,2,5],[],[0]),([175,178,0,2,4,5],[7],[]),([179,109,2,3,4,5],[],[]),([71,175,109,2,4,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block5_2Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block5_2Pools wd2Autos wd2Bucket4 5 wd2Block5_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block5_2Mem : ∀ ns ∈ wd2Block5_2, Impossible wd2G 5 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket4Ok wd2Block5_2Ok
def wd2Nodes5 : List NodeSpec := wd2Block5_0 ++ wd2Block5_1 ++ wd2Block5_2
def wd2Bucket5 : BT (List (List Nat)) := buildBucketsBT wd2W wd2Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd2G 5 xs.toFinset) wd2Bucket5 := buildBucketsBT_of_mem (forall_append (forall_append wd2Block5_0Mem wd2Block5_1Mem) wd2Block5_2Mem)
def wd2Block6_0Specs : List PoolSpec := [(6,[]),(3,[(1,6,2),(0,7,5),(1,9,3)]),(3,[(1,6,2),(0,7,5),(1,9,4)]),(3,[(1,6,5),(1,6,2),(0,7,5)]),(15,[]),(3,[(1,2,5),(1,6,2),(0,7,5)]),(3,[]),(3,[(1,6,2),(1,7,5),(2,15,3)]),(3,[(1,6,2),(1,7,5),(2,15,4)]),(8,[]),(2,[(1,0,1),(1,5,6)]),(21,[]),(14,[]),(12,[]),(9,[]),(2,[]),(17,[]),(5,[(1,0,1),(2,6,3)])]
def wd2Block6_0Pools : BT (Option BoundPool) := buildPoolsBT 5 wd2W wd2R wd2Slices wd2Block6_0Specs
def wd2Block6_0 : List NodeSpec := [([10,6,0,1,2,4,5],[0,1],[0,1]),([13,6,0,1,2,3,5],[2],[0]),([11,9,0,1,2,3,4],[3],[0]),([12,9,6,1,2,3,4],[0,4],[0]),([14,9,6,0,1,3,4],[5],[0]),([16,6,1,2,3,4,5],[6],[]),([17,6,0,1,2,4,5],[7],[]),([18,6,0,1,2,3,5],[8],[]),([11,19,0,1,2,3,4],[9],[]),([12,19,6,1,2,3,4],[0,4],[]),([21,0,1,2,3,4,5],[10],[]),([22,6,1,2,3,4,5],[6],[]),([23,7,0,1,2,4,5],[],[]),([24,12,7,6,2,3,4],[11,12,4],[]),([29,1,2,3,4,5],[],[]),([29,28,1,2,3,4,5],[11],[0,3]),([24,12,27,2,3,4],[11,13,14],[]),([24,12,27,2,3,4,5],[0,11],[0]),([32,27,0,1,2,3,5],[],[]),([34,0,1,2,3,4,5],[],[0,1,2]),([36,27,1,2,3,4,5],[0],[]),([23,38,0,1,2,4,5],[11],[]),([39,38,0,1,2,4,5],[15],[]),([40,38,0,1,2,4],[11],[]),([40,38,0,1,2,4,5],[11],[]),([41,12,1,2,3,4,5],[0],[0]),([42,12,37,1,2,4,5],[11],[0]),([24,12,37,2,3,4],[11,13,14],[0,6]),([24,12,37,2,3,4,5],[0,11],[0]),([39,12,37,1,2,4,5],[],[0]),([40,12,37,1,2,4],[11],[0]),([40,12,37,1,2,4,5],[11],[0]),([44,37,0,1,2,4,5],[11],[0,1]),([48,37,0,1,2,4,5],[],[0,1,2]),([14,39,37,0,1,4,5],[16,11,17],[0]),([50,37,0,1,2,4,5],[9],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_0Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block6_0Pools wd2Autos wd2Bucket5 6 wd2Block6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_0Mem : ∀ ns ∈ wd2Block6_0, Impossible wd2G 6 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket5Ok wd2Block6_0Ok
def wd2Block6_1Specs : List PoolSpec := [(21,[]),(12,[]),(9,[]),(8,[]),(10,[]),(11,[]),(0,[(1,0,1),(1,6,5),(2,11,3)]),(1,[]),(2,[(1,0,1),(1,6,5),(2,11,3)]),(2,[])]
def wd2Block6_1Pools : BT (Option BoundPool) := buildPoolsBT 4 wd2W wd2R wd2Slices wd2Block6_1Specs
def wd2Block6_1 : List NodeSpec := [([32,37,0,1,2,3,5],[],[]),([51,0,1,2,3,4,5],[],[2]),([36,37,1,2,3,4,5],[],[]),([23,40,0,1,2,4,5],[0],[]),([52,37,1,2,4,5],[0],[1]),([52,40,37,1,2,4,5],[0],[1]),([53,37,0,1,2,4,5],[],[0]),([12,57,1,2,4],[0,1,2],[]),([58,12,1,2,3,4],[0],[]),([60,11,1,2,3,4,5],[0],[]),([61,11,1,2,3,4,5],[0],[0]),([63,59,2,3,4,5],[],[0]),([63,59,11,2,3,4,5],[0],[0]),([64,59,11,1,2,4,5],[0],[0]),([23,59,11,1,2,4,5],[0],[0]),([62,59,11,2,3,4,5],[0],[0]),([31,59,11,1,2,3,4],[0],[0]),([40,59,11,1,2,3,4],[0],[0]),([16,11,1,2,3,4,5],[3],[0]),([17,11,0,1,2,4,5],[0],[]),([18,11,0,1,2,3,5],[],[0]),([64,15,0,1,2,4,5],[4],[0,1]),([23,15,0,1,2,4,5],[5,6],[0]),([64,66,0,1,2,4,5],[],[]),([23,66,0,1,2,4,5],[],[]),([23,11,0,1,2,4,5],[7],[]),([63,64,0,2,4,5],[0],[]),([29,11,1,2,3,4,5],[0],[3]),([67,23,0,1,2,4,5],[6,8],[0]),([69,23,0,1,2,4,5],[8],[]),([14,23,0,1,2,4,5],[6,8],[0]),([33,23,0,1,2,4,5],[8],[]),([61,23,11,1,2,4,5],[0],[0]),([40,23,11,0,1,2,4],[0],[]),([39,23,0,1,2,4,5],[9],[]),([31,23,0,1,2,4,5],[7],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_1Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block6_1Pools wd2Autos wd2Bucket5 6 wd2Block6_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_1Mem : ∀ ns ∈ wd2Block6_1, Impossible wd2G 6 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket5Ok wd2Block6_1Ok
def wd2Block6_2Specs : List PoolSpec := [(21,[]),(1,[]),(11,[]),(11,[(2,14,4)]),(14,[]),(5,[(1,1,3),(1,0,3),(1,0,1)]),(14,[(2,14,4)]),(3,[]),(15,[]),(9,[]),(3,[(1,6,2),(1,7,5),(2,15,4)]),(17,[]),(0,[(1,1,5),(1,0,5),(1,0,1)]),(12,[]),(2,[(1,1,5),(1,0,5),(1,0,1)])]
def wd2Block6_2Pools : BT (Option BoundPool) := buildPoolsBT 4 wd2W wd2R wd2Slices wd2Block6_2Specs
def wd2Block6_2 : List NodeSpec := [([71,23,11,1,2,4,5],[0],[1]),([31,23,11,0,1,2,4],[0],[0,1]),([62,71,11,2,4,5],[0],[0,1]),([31,71,11,1,2,4],[0],[0,1]),([31,71,11,1,2,4,5],[1],[]),([31,39,11,0,1,2,4],[2],[]),([32,11,0,1,2,3,5],[3],[0]),([72,0,1,2,3,4,5],[],[]),([40,31,11,0,1,2,4],[0],[]),([23,73,0,1,2,4,5],[],[]),([63,59,6,2,3,4,5],[0],[]),([23,59,6,1,2,4,5],[0],[]),([74,23,0,1,2,4,5],[],[]),([75,23,0,1,2,4,5],[0],[]),([61,23,6,1,2,4,5],[0],[0]),([32,76,0,1,2,3,5],[],[]),([79,78,6,2,3,4,5],[0],[]),([81,6,0,1,2,3,5],[],[0]),([24,12,73,6,2,3,4],[0],[]),([14,62,71,6,2,4,5],[4,5,2],[0]),([33,62,71,6,2,4,5],[0,4,2,5],[0,1,2]),([61,24,6,2,3,4,5],[0],[0,2]),([87,24,71,6,2,4,5],[0],[2]),([31,24,71,6,2,4],[0],[0,3]),([31,24,71,6,2,4,5],[0],[]),([32,71,6,1,2,3,5],[3,6],[0]),([88,6,1,2,3,4,5],[7],[1]),([89,71,6,2,3,4,5],[0],[0]),([90,12,6,2,3,4,5],[0],[0]),([91,63,6,2,3,4,5],[0],[5]),([42,63,6,2,3,4,5],[7],[0]),([31,63,12,6,2,3,4],[0],[0,1]),([40,63,12,6,2,3,4],[0],[]),([93,12,6,2,3,4,5],[7,8],[]),([94,12,6,1,2,3,5],[9,10],[0]),([24,92,12,6,2,3,4],[8,0,11,12,13,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_2Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block6_2Pools wd2Autos wd2Bucket5 6 wd2Block6_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_2Mem : ∀ ns ∈ wd2Block6_2, Impossible wd2G 6 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket5Ok wd2Block6_2Ok
def wd2Block6_3Specs : List PoolSpec := [(12,[]),(15,[]),(2,[(1,1,5),(1,0,5),(1,0,1)]),(21,[]),(3,[]),(6,[]),(17,[]),(0,[(1,1,5),(1,0,5),(1,0,1)]),(14,[]),(9,[]),(14,[(2,14,4)]),(1,[]),(3,[(1,2,3),(0,39,5),(1,44,6)]),(11,[]),(3,[(1,2,3),(0,39,5),(1,44,4)]),(3,[(1,2,5),(1,2,3),(0,39,5)]),(3,[(1,3,5),(1,2,3),(0,39,5)]),(3,[(1,2,3),(1,39,5),(2,99,6)]),(3,[(1,2,3),(1,39,5),(2,99,4)]),(5,[(1,0,1),(1,6,5)]),(5,[(1,0,5),(1,0,1)])]
def wd2Block6_3Pools : BT (Option BoundPool) := buildPoolsBT 5 wd2W wd2R wd2Slices wd2Block6_3Specs
def wd2Block6_3 : List NodeSpec := [([24,95,12,6,2,3,4],[0,1,2],[]),([96,12,1,2,3,4,5],[3],[0]),([30,12,6,2,3,4,5],[3],[]),([24,91,12,6,2,3,4],[3],[0,5]),([70,42,6,2,3,4,5],[4],[0,5]),([24,42,6,2,3,4],[3],[0,5]),([24,42,6,2,3,4,5],[3],[0]),([31,42,6,1,2,4,5],[3],[0]),([24,42,12,6,2,3,4],[3,5],[0,1,5]),([31,42,12,6,1,2,4],[3,5],[0,1]),([39,24,12,6,2,3,4],[0,3],[0]),([14,24,12,6,2,3,4],[6,7,8,0],[0]),([33,24,12,6,2,3,4],[5,8],[]),([31,24,12,6,2,3,4],[3],[0,1]),([40,24,12,6,2,3,4],[5,3],[0]),([31,39,12,6,1,2,4],[0,3],[]),([32,12,6,1,2,3,5],[9,10],[0]),([89,12,6,2,3,4,5],[5,2,8],[]),([96,31,12,1,2,3,4],[3,5],[7]),([87,31,12,6,2,3,4],[3],[1,7]),([40,31,12,6,1,2,4],[3,5],[0]),([43,12,6,2,3,4],[3,0,9],[0]),([43,40,12,6,2,3,4],[5],[0]),([43,12,6,2,3,4,5],[3,5],[0]),([98,0,1,2,3,4,5],[11,12],[0]),([46,6,1,2,3,4,5],[4,13],[0]),([47,6,0,1,2,3,5],[13,14],[0]),([14,44,6,0,1,3,4],[13,15],[0]),([31,44,6,0,1,2,4],[5,16],[0,1]),([100,0,1,2,3,4,5],[17],[]),([101,6,0,1,2,3,5],[18],[]),([103,0,1,2,3,4,5],[],[2]),([49,6,1,2,3,4,5],[4],[0]),([105,6,0,2,3,4,5],[4],[]),([21,14,0,1,3,4,5],[19],[0]),([36,14,6,1,3,4,5],[20],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_3Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block6_3Pools wd2Autos wd2Bucket5 6 wd2Block6_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_3Mem : ∀ ns ∈ wd2Block6_3, Impossible wd2G 6 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket5Ok wd2Block6_3Ok
def wd2Block6_4Specs : List PoolSpec := [(8,[]),(0,[]),(5,[(1,0,1),(1,6,5),(2,11,3)]),(1,[]),(2,[(1,0,1),(1,6,5),(2,11,3)]),(3,[]),(3,[(3,2,5),(1,33,0),(2,36,3)]),(14,[]),(6,[]),(2,[(1,1,5),(1,0,5),(1,0,1)]),(3,[(3,2,5),(1,33,3),(2,114,6)]),(21,[]),(11,[(2,14,4)]),(3,[(3,3,5),(1,40,2),(2,53,4)]),(20,[]),(15,[]),(12,[]),(1,[(1,0,2),(0,123,5),(1,133,1)])]
def wd2Block6_4Pools : BT (Option BoundPool) := buildPoolsBT 5 wd2W wd2R wd2Slices wd2Block6_4Specs
def wd2Block6_4 : List NodeSpec := [([107,0,1,2,3,4,5],[0],[]),([108,21,1,2,3,4,5],[1],[0]),([110,21,0,1,2,4,5],[],[0,1,2]),([106,0,1,2,4,5],[2],[0]),([106,21,0,1,2,4,5],[3],[]),([106,0,1,2,3,4,5],[],[]),([106,33,0,1,2,4,5],[4],[0]),([109,6,0,2,3,4,5],[5],[]),([106,6,0,1,2,4,5],[],[0]),([109,36,6,2,3,4,5],[5],[]),([113,6,1,2,3,4,5],[6],[]),([89,36,6,2,3,4,5],[7,8,9],[]),([115,0,1,2,3,4,5],[10],[]),([30,31,0,2,3,4,5],[11],[]),([116,96,1,2,3,4,5],[11],[0]),([87,91,6,2,3,4,5],[11],[]),([119,0,1,2,3,4,5],[3],[2]),([120,6,1,2,3,4,5],[5],[]),([74,31,0,1,2,4,5],[3],[]),([52,31,6,1,2,4,5],[11,8],[1]),([121,74,1,2,3,4,5],[11],[0]),([122,52,6,2,3,4,5],[5],[]),([43,52,6,2,3,4,5],[11,8],[0]),([54,6,0,1,2,3,5],[12,13],[0]),([126,0,1,2,3,4,5],[0],[]),([127,0,1,2,3,4,5],[],[]),([12,125,1,2,3,4,5],[8],[0]),([14,125,0,1,3,4,5],[14],[]),([31,125,0,1,2,4,5],[8],[0]),([130,0,1,2,3,4,5],[],[]),([131,12,1,2,3,4,5],[8],[]),([31,12,124,1,2,3,4],[15,16],[0]),([50,124,0,1,3,4,5],[],[]),([132,0,1,2,3,4,5],[5],[]),([128,124,0,2,3,4,5],[0],[0]),([135,134,0,2,3,4,5],[15,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_4Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block6_4Pools wd2Autos wd2Bucket5 6 wd2Block6_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_4Mem : ∀ ns ∈ wd2Block6_4, Impossible wd2G 6 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket5Ok wd2Block6_4Ok
def wd2Block6_5Specs : List PoolSpec := [(1,[(1,0,2),(0,123,5),(1,133,1)]),(9,[]),(12,[]),(1,[(1,0,5),(1,0,2),(0,123,5),(1,133,1)]),(3,[(1,6,5),(1,6,2),(0,7,5)]),(15,[]),(3,[(1,2,5),(1,6,2),(0,7,5),(1,9,4)]),(1,[(1,2,5),(1,0,2),(0,123,5),(1,133,4)]),(1,[(1,0,5),(1,0,2),(0,123,5)]),(1,[(1,0,5),(1,12,2),(2,92,1)]),(2,[(1,0,1),(1,6,5),(2,11,3)]),(6,[]),(21,[]),(4,[]),(0,[(1,0,1),(1,6,5),(2,11,3)]),(1,[(1,0,5),(1,12,2),(2,92,4)]),(8,[])]
def wd2Block6_5Pools : BT (Option BoundPool) := buildPoolsBT 5 wd2W wd2R wd2Slices wd2Block6_5Specs
def wd2Block6_5 : List NodeSpec := [([137,134,0,2,3,4,5],[0],[0]),([12,134,2,3,4],[1,2,3,4],[0]),([137,0,1,2,3,4,5],[0],[0]),([12,134,1,2,3,4],[4,1,2,3],[0,7]),([14,142,0,1,3],[2,1,5,6,7],[2]),([11,12,133,1,2,3,4],[8,4],[0,3]),([63,12,133,1,2,3,4],[4],[0,3]),([144,0,1,2,3,4,5],[9],[]),([148,0,1,2,3,4,5],[],[]),([23,12,123,1,2,4,5],[10],[0]),([24,63,12,123,2,3,4],[2],[]),([149,24,12,1,2,3,4],[2,5],[]),([97,12,123,1,2,3,4],[5],[3]),([153,123,0,1,3,4,5],[],[]),([155,12,1,2,3,4,5],[11],[0]),([63,79,12,2,3,4,5],[11],[]),([31,79,12,1,2,3,4],[12],[0,2]),([23,154,12,1,2,4,5],[12],[]),([24,63,154,12,2,3,4],[12,11],[]),([97,154,12,1,2,3,4],[12],[3]),([60,12,1,2,3,4,5],[13],[]),([63,59,12,2,3,4,5],[],[]),([31,59,12,1,2,3,4],[12],[0,3,7]),([40,59,12,1,2,3,4],[13],[0]),([64,59,12,1,2,4,5],[12],[0]),([23,59,12,1,2,4,5],[12],[0]),([61,23,12,1,2,4,5],[12],[]),([40,23,12,0,1,2,4],[12],[]),([92,23,0,1,2,4,5],[14],[0]),([95,23,0,1,2,4,5],[],[]),([31,23,12,0,1,2,4],[12],[3]),([94,11,0,1,2,3,5],[15],[0]),([31,42,11,0,1,2,4],[12],[1]),([157,63,0,1,2,3,5],[],[]),([159,63,0,2,3,4,5],[16],[0]),([160,63,0,2,3,4,5],[12],[0,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_5Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block6_5Pools wd2Autos wd2Bucket5 6 wd2Block6_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_5Mem : ∀ ns ∈ wd2Block6_5, Impossible wd2G 6 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket5Ok wd2Block6_5Ok
def wd2Block6_6Specs : List PoolSpec := [(1,[]),(0,[]),(21,[]),(6,[]),(3,[]),(3,[(1,6,5),(2,11,0)]),(17,[]),(20,[]),(3,[(1,6,2),(1,7,5),(2,15,4)]),(14,[(2,14,4)]),(4,[]),(13,[]),(9,[]),(5,[(1,0,5),(3,1,12)])]
def wd2Block6_6Pools : BT (Option BoundPool) := buildPoolsBT 4 wd2W wd2R wd2Slices wd2Block6_6Specs
def wd2Block6_6 : List NodeSpec := [([31,70,63,0,1,2,4],[0],[0,1]),([32,63,0,1,2,3,5],[],[]),([89,63,0,2,3,4,5],[1],[0]),([128,31,63,0,2,3,4],[2],[3]),([128,63,0,2,3,4,5],[2],[3]),([43,40,63,0,2,3,4],[],[0,2]),([43,63,0,2,3,4,5],[1],[0,2]),([24,73,63,12,2,3,4],[2],[]),([161,12,1,2,3,4,5],[3],[3,7]),([24,90,12,0,2,3,4],[4],[3,7]),([94,63,0,1,2,3,5],[],[]),([24,42,63,0,2,3,4],[4],[3]),([59,24,63,12,2,3,4],[5],[]),([43,63,12,0,2,3,4],[3],[]),([24,93,12,0,2,3,4],[4,6],[]),([24,94,12,0,1,2,3],[7,8],[0]),([162,0,1,2,3,4,5],[],[]),([108,12,1,2,3,4,5],[3],[0]),([32,24,12,0,1,2,3],[7,9],[0]),([161,164,12,1,2,3,4],[10,3],[]),([161,163,12,1,2,3,4],[10,4],[3,7]),([29,79,1,2,3,4,5],[],[]),([166,79,0,2,3,4,5],[3],[2]),([170,169,0,1,2,3,5],[11,7,12],[0]),([174,169,0,1,2,3,5],[],[0]),([177,0,1,2,3,4,5],[],[]),([109,14,0,1,3,4,5],[13],[]),([108,36,1,2,3,4,5],[1],[0]),([106,36,0,1,2,4,5],[],[]),([178,0,1,2,3,4,5],[],[0,1]),([175,109,0,2,3,4,5],[],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_6Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block6_6Pools wd2Autos wd2Bucket5 6 wd2Block6_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block6_6Mem : ∀ ns ∈ wd2Block6_6, Impossible wd2G 6 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket5Ok wd2Block6_6Ok
def wd2Nodes6 : List NodeSpec := wd2Block6_0 ++ wd2Block6_1 ++ wd2Block6_2 ++ wd2Block6_3 ++ wd2Block6_4 ++ wd2Block6_5 ++ wd2Block6_6
def wd2Bucket6 : BT (List (List Nat)) := buildBucketsBT wd2W wd2Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd2G 6 xs.toFinset) wd2Bucket6 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append wd2Block6_0Mem wd2Block6_1Mem) wd2Block6_2Mem) wd2Block6_3Mem) wd2Block6_4Mem) wd2Block6_5Mem) wd2Block6_6Mem)
def wd2Block7_0Specs : List PoolSpec := [(21,[]),(12,[]),(13,[]),(14,[]),(6,[]),(15,[]),(0,[(1,0,1)]),(3,[(1,6,2),(0,7,5)]),(17,[]),(3,[(1,6,2),(1,7,5)]),(3,[(1,6,2),(2,7,5)]),(3,[(1,6,2),(3,7,5)]),(8,[]),(3,[(1,6,5),(1,6,2)]),(5,[(1,0,1)]),(3,[(1,2,5),(1,6,2)]),(2,[]),(0,[]),(7,[]),(7,[(1,0,5)]),(5,[(1,0,1),(1,6,3)]),(9,[]),(5,[(1,0,1),(2,6,3)]),(4,[]),(3,[(1,6,5),(2,11,0)]),(1,[(1,1,5),(3,0,24)]),(2,[(1,0,1),(1,5,6)]),(0,[(1,0,1),(1,6,5)]),(11,[]),(10,[]),(5,[(1,0,1),(1,6,5),(2,11,3)]),(4,[(1,6,5),(2,11,3)]),(3,[(1,6,5),(2,11,3)]),(2,[(1,0,1),(1,6,5),(2,11,3)]),(0,[(1,0,1),(1,6,5),(2,11,3)])]
def wd2Block7_0Pools : BT (Option BoundPool) := buildPoolsBT 6 wd2W wd2R wd2Slices wd2Block7_0Specs
def wd2Block7_0 : List NodeSpec := [([8,0,1,2,3,4,5],[0,1,2],[]),([9,6,0,1,2,3,4,5],[0,3,4,5,6,7],[0,1]),([15,6,0,1,2,3,4,5],[8,0,6,9],[0,1]),([19,6,0,1,2,3,4,5],[0,3,1,5,10],[0,1]),([20,6,0,1,2,3,4,5],[11],[0,1]),([11,7,0,1,2,3,4,5],[3,12,0,13],[0]),([12,7,6,1,2,3,4,5],[0,3,5],[0]),([14,7,6,0,1,3,4,5],[0,14,3,5,15],[0]),([26,0,1,2,3,5],[0,1],[]),([28,0,1,2,3,4,5],[0,16,12,17,18],[0,1,2]),([12,27,1,2,3,4,5],[0,1,19],[0,3]),([14,27,0,1,2,3,4,5],[8,12,20],[0]),([33,27,0,1,2,3,4,5],[0,4,20],[0,1,2]),([38,0,1,2,3,4,5],[0,16,12,17,18],[0,2,4]),([12,37,1,2,3,4,5],[0,1,21],[0,4]),([39,37,0,1,2,4,5],[0,22],[0,1]),([14,37,0,1,2,3,4,5],[8,12,22,0],[0]),([33,37,0,1,2,3,4,5],[0,4,22],[0,1]),([40,37,0,1,2,4,5],[0],[0,6,2]),([56,0,1,3,4,5],[0,4,12],[]),([57,0,1,2,4,5],[0,21],[0,1]),([12,55,1,2,3,4],[0,1,21,23],[0]),([59,11,1,2,3,4,5],[0,24,25],[0]),([15,11,0,1,2,3,4,5],[26,0,27,12],[0,1]),([66,11,0,1,2,3,4,5],[26,12],[0]),([64,11,0,1,2,4,5],[0,28,29,25],[0,6,2]),([28,11,0,1,2,3,4,5],[0],[0,1,2]),([23,0,1,2,4,5],[0,30,31,32],[0,4]),([23,11,0,1,2,4,5],[0,31,32,33,34],[0,6]),([23,0,1,2,3,4,5],[0,33,34,12,18],[0,2,4]),([23,11,0,1,2,3,4,5],[0,31,32],[0,1,2]),([71,11,1,2,3,4,5],[0],[0,1]),([39,11,0,1,2,3,4,5],[28,12,0],[0]),([14,11,0,1,2,3,4,5],[26,12,27,28],[0]),([33,11,0,1,2,3,4,5],[28,26],[0]),([31,11,0,1,2,3,4],[0],[0,6]),([31,11,0,1,2,3,4,5],[0],[0,1]),([40,11,0,1,2,3,4],[0],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block7_0Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block7_0Pools wd2Autos wd2Bucket6 7 wd2Block7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block7_0Mem : ∀ ns ∈ wd2Block7_0, Impossible wd2G 7 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket6Ok wd2Block7_0Ok
def wd2Block7_1Specs : List PoolSpec := [(21,[]),(3,[(1,6,5),(2,11,0)]),(4,[(1,6,5)]),(8,[]),(2,[(1,0,1),(1,5,6)]),(3,[(1,6,5),(2,11,2)]),(3,[(1,6,5),(2,11,3)]),(2,[(1,0,1),(1,6,5),(2,11,3)]),(0,[(1,0,1),(1,6,5),(2,11,3)]),(4,[(1,6,5),(2,11,3)]),(5,[(1,0,1),(2,6,5)]),(12,[]),(9,[]),(17,[]),(0,[(1,0,1)]),(3,[(3,0,5),(1,2,59)]),(5,[(1,1,3),(1,0,3),(1,0,1)]),(3,[]),(4,[]),(11,[]),(5,[(1,0,3),(1,0,1)]),(14,[]),(3,[(1,6,5)]),(0,[(1,0,5),(1,0,1)]),(15,[]),(3,[(1,6,2),(1,7,5)]),(2,[(1,0,5),(1,0,1)]),(6,[]),(5,[(1,1,5),(1,0,5),(1,0,1)]),(2,[(1,1,5),(1,0,5),(1,0,1)]),(0,[(1,1,5),(1,0,5),(1,0,1)]),(3,[(1,2,3),(0,39,5)]),(3,[(1,2,3),(1,39,5)]),(3,[(1,2,3),(2,39,5)]),(3,[(1,2,3),(3,39,5)]),(18,[]),(5,[(1,0,1)]),(3,[(1,2,5),(1,2,3)])]
def wd2Block7_1Pools : BT (Option BoundPool) := buildPoolsBT 6 wd2W wd2R wd2Slices wd2Block7_1Specs
def wd2Block7_1 : List NodeSpec := [([40,11,0,1,2,3,4,5],[0],[0]),([73,11,0,1,2,3,4,5],[0,1],[0]),([59,6,1,2,3,4,5],[0,2],[]),([59,11,6,1,2,3,4,5],[0],[0]),([66,6,0,1,2,3,4,5],[3,4,5],[0]),([23,6,0,1,2,4,5],[0,6,7,8,9],[0,6]),([23,11,6,0,1,2,4,5],[0,6],[0,1]),([14,76,0,1,2,3,4,5],[10,3],[0]),([33,76,0,1,2,3,4,5],[4,10],[]),([77,0,1,2,3,4,5],[0,11,12],[]),([31,73,0,1,2,3,4],[0,11,12],[]),([78,73,6,1,2,3,4,5],[0],[0]),([80,6,0,1,2,3,4,5],[3,13,14,15],[0]),([12,73,6,1,2,3,4,5],[0,2],[0]),([62,71,6,2,4,5],[0,16,17,18],[0,8,3]),([24,71,6,2,3,4,5],[0],[0,3,2]),([14,71,6,1,2,3,4,5],[19,20,21],[0]),([33,71,6,1,2,3,4,5],[0,19,21,20],[0,3]),([63,12,6,2,3,4,5],[0,22],[0,1]),([92,12,6,1,2,3,4,5],[0,11,13,23,24,25,26],[0]),([95,12,6,1,2,3,4,5],[11,5,26],[0]),([91,12,6,1,2,3,4,5],[0],[0,1,5]),([42,6,1,2,3,4,5],[0,6],[0,5]),([42,12,6,1,2,3,4,5],[0,27,6],[0,1,5]),([24,12,6,2,3,4],[0,28,22,11,2,12],[0,6,1,4,3,7]),([24,12,6,2,3,4,5],[0,11,22,12,29,30],[0,6,3,7]),([39,12,6,1,2,3,4,5],[11,0],[0]),([14,12,6,1,2,3,4,5],[13,23,21,11,26],[0]),([33,12,6,1,2,3,4,5],[27,24,0,21,26],[0]),([31,12,6,1,2,3,4],[0,11,12],[0,7,3,4]),([31,12,6,1,2,3,4,5],[0,27],[0,7,3]),([40,12,6,1,2,3,4],[0,11,12],[0]),([40,12,6,1,2,3,4,5],[0,27],[0]),([44,6,0,1,2,3,4,5],[0,19,21,14,31],[0,1]),([99,6,0,1,2,3,4,5],[3,0,14,19,32],[0]),([102,6,0,1,2,3,4,5],[19,11,33],[]),([48,6,0,1,2,3,4,5],[0,27,19,34],[0,1]),([14,39,6,0,1,3,4,5],[0,3,19,35,36,37],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block7_1Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block7_1Pools wd2Autos wd2Bucket6 7 wd2Block7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block7_1Mem : ∀ ns ∈ wd2Block7_1, Impossible wd2G 7 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket6Ok wd2Block7_1Ok
def wd2Block7_2Specs : List PoolSpec := [(12,[]),(14,[]),(21,[]),(11,[]),(3,[(1,3,5),(1,2,3)]),(3,[(1,6,2),(1,7,5)]),(3,[(1,2,5),(2,14,6)]),(5,[(1,0,1)]),(6,[]),(3,[(3,2,5),(1,2,5)]),(17,[]),(8,[]),(3,[(1,2,5),(2,14,3)]),(3,[(1,2,5),(2,14,4)]),(13,[]),(15,[(2,92,4)]),(9,[]),(11,[(2,14,4)]),(4,[(1,2,5),(2,14,4)]),(5,[(1,0,1),(1,6,5)]),(3,[(3,2,5),(1,0,33)]),(4,[(3,2,5),(1,1,33)]),(2,[(1,0,1),(1,5,6)]),(3,[(1,6,2),(3,7,5)]),(5,[(1,0,1),(2,6,5)]),(5,[(1,0,5),(1,0,1)]),(15,[]),(4,[]),(2,[(1,0,5),(1,0,1)]),(3,[(3,2,5),(1,33,3)]),(1,[(1,1,5),(3,0,24)]),(2,[]),(0,[]),(7,[]),(3,[(1,3,5),(3,0,31)]),(3,[(1,3,5),(2,31,2)]),(3,[(3,3,5),(1,3,5)]),(0,[(1,0,1)]),(3,[(3,3,5),(1,40,2)]),(20,[]),(1,[]),(3,[(1,6,5),(1,6,2)]),(1,[(1,0,2),(0,123,5),(1,133,1)]),(3,[(1,6,2),(0,7,5)]),(3,[(1,6,2),(0,7,5),(1,9,4)]),(1,[(1,0,2),(0,123,5),(1,133,4)]),(3,[(1,6,5),(1,6,2),(0,7,5)]),(1,[(1,0,5),(1,0,2),(0,123,5)]),(4,[(3,2,5)]),(3,[(1,2,5),(1,6,2),(0,7,5)]),(1,[(1,2,5),(1,0,2),(0,123,5)]),(18,[]),(1,[(1,0,5),(1,12,2),(2,92,1)]),(2,[(1,0,5),(2,92,1)]),(3,[(1,6,2),(1,7,5),(2,15,4)]),(1,[(1,0,5),(1,12,2),(2,92,4)])]
def wd2Block7_2Pools : BT (Option BoundPool) := buildPoolsBT 6 wd2W wd2R wd2Slices wd2Block7_2Specs
def wd2Block7_2 : List NodeSpec := [([31,39,6,0,1,2,4,5],[0,1,2,3,4],[0,1]),([104,6,0,1,2,3,4,5],[5,6],[0]),([33,14,6,0,1,3,4,5],[7,8,9],[0,1]),([50,6,0,1,2,3,4,5],[10,2,11,3,12],[0]),([32,6,0,1,2,3,5],[13,14,15,16,17,18],[0,1]),([32,14,6,0,1,2,3,5],[10,11,7,13],[]),([21,0,1,2,3,4,5],[19,2,20,21],[0,1,3,7]),([21,33,0,1,2,3,4,5],[2,3,22],[0]),([21,6,0,1,2,3,4,5],[23,2,20],[0]),([112,33,0,1,2,3,4,5],[24],[0]),([36,6,1,2,3,4,5],[20,25,8,26],[0,1]),([36,33,6,1,2,3,4,5],[8,20,27,28],[0]),([114,6,0,1,2,3,4,5],[2,3,29],[0,1,2,3,7]),([28,31,0,1,2,3,4,5],[2,30],[0]),([96,0,1,2,3,4,5],[2,31,11,32,33,34],[0,1]),([96,31,0,1,2,3,4,5],[2,8,34],[3,7,0,1]),([91,31,6,1,2,3,4,5],[2],[0,1,3,7]),([118,6,0,1,2,3,4,5],[2,11,35],[0,1]),([40,31,6,0,1,2,4,5],[2,8,36],[0,1]),([74,0,1,2,3,4,5],[2,31,11,32,33],[0,1,2]),([74,40,0,1,2,3,4,5],[2],[0]),([52,6,1,2,3,4,5],[2,0,16],[0,1]),([52,40,6,1,2,3,4,5],[2,8],[0,1]),([53,6,0,1,2,3,4,5],[10,11,37,3,38],[0]),([125,0,1,2,3,4,5],[39,2,8],[0]),([129,0,1,2,3,4,5],[26,5,40,32,33,0],[0]),([12,124,1,2,3,4,5],[26,0,16,41],[0]),([39,124,0,1,3,4,5],[0,26,14,40],[]),([14,124,0,1,3,4,5],[39,0],[0]),([31,124,0,1,2,3,4,5],[26,0,1,40],[0]),([134,0,2,3,4,5],[16,26,42],[0]),([134,0,1,2,3,4,5],[16,26,42,43],[0,7]),([142,0,1,2,3,5],[26,8,33,44,45],[0,2]),([12,133,1,2,3,4],[16,0,46,47,48],[0,3,2]),([14,133,0,1,3,4],[16,11,26,49,50],[0,2]),([93,0,1,2,3,4,5],[0,5,51,52,33,53],[0,1,2]),([94,0,1,2,3,5],[16,39,18,11,54,55],[2]),([147,0,1,2,3,4,5],[16,23,11,40],[0,7,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block7_2Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block7_2Pools wd2Autos wd2Bucket6 7 wd2Block7_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block7_2Mem : ∀ ns ∈ wd2Block7_2, Impossible wd2G 7 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket6Ok wd2Block7_2Ok
def wd2Block7_3Specs : List PoolSpec := [(15,[]),(12,[]),(2,[(1,0,1),(1,5,6)]),(1,[(1,0,5),(1,0,2)]),(21,[]),(3,[(1,6,5),(1,6,2)]),(2,[(1,0,5),(2,92,1)]),(2,[(1,1,5),(1,0,5)]),(19,[]),(3,[(1,6,2),(1,7,5)]),(8,[]),(18,[]),(4,[]),(3,[(1,6,5),(2,11,0)]),(9,[]),(4,[(1,6,5)]),(1,[(1,0,5),(2,12,0)]),(1,[(1,0,5),(3,1,12)]),(4,[(1,6,5),(2,11,1)]),(4,[(1,6,5),(2,11,3)]),(3,[(1,6,5),(2,11,3)]),(2,[(1,0,1),(1,6,5),(2,11,3)]),(0,[(1,0,1),(1,6,5),(2,11,3)]),(0,[(1,0,1),(1,6,5)]),(1,[(1,0,5),(1,12,2)]),(14,[]),(1,[(1,0,5),(2,12,2)]),(0,[(1,0,5),(3,1,12)]),(2,[]),(0,[]),(7,[]),(6,[])]
def wd2Block7_3Pools : BT (Option BoundPool) := buildPoolsBT 5 wd2W wd2R wd2Slices wd2Block7_3Specs
def wd2Block7_3 : List NodeSpec := [([11,12,123,1,2,3,4,5],[0,1,2,3,4,5],[0]),([63,12,123,1,2,3,4,5],[0,1,6,5],[0]),([24,12,123,1,2,3,4],[1,7,5,0,8],[0,7,3]),([149,24,0,1,2,3,4,5],[1,0],[0]),([151,24,0,1,2,3,4,5],[1,9],[]),([97,123,0,1,2,3,4,5],[0,10,4],[0,3]),([31,24,123,0,1,2,3,4],[1,4],[2]),([152,123,0,1,3,4,5],[11,10,12],[0,3]),([79,12,1,2,3,4,5],[1,13,14,15],[0,7]),([11,154,12,1,2,3,4,5],[4,16,13],[0]),([63,154,12,1,2,3,4,5],[4,13],[0]),([24,154,12,1,2,3,4],[1,13,4,14],[0,7,3]),([59,12,1,2,3,4,5],[15,13,1,14,4],[0,3,7]),([59,11,12,1,2,3,4,5],[4,13],[0]),([63,11,12,0,2,3,4,5],[4,17,18],[0]),([64,11,12,0,1,2,4,5],[4,17],[0,1,7]),([23,12,0,1,2,4,5],[19,20,4,21,22],[0,4]),([23,11,12,0,1,2,4,5],[4,20,19],[0,1]),([23,12,0,1,2,3,4,5],[4,20,19],[0,3,5]),([92,11,0,1,2,3,4,5],[0,10,4,23,24],[0,1]),([95,11,0,1,2,3,4,5],[25,26],[0]),([91,11,0,1,2,3,4,5],[4],[1,2,5]),([42,11,0,1,2,3,4,5],[4,20],[0,1,3]),([31,11,12,0,1,2,3,4],[4],[0,1,2,3]),([40,11,12,0,1,2,3,4],[4],[0,1]),([156,63,0,1,2,3,4,5],[6,27,10],[0]),([158,63,0,1,2,3,4,5],[6,10],[0]),([90,0,1,2,3,4,5],[4,17,28,10,29,30],[1,2]),([90,63,0,1,2,3,4,5],[17],[1,2]),([70,63,0,1,2,3,4,5],[17],[0,1,2,3]),([14,63,0,1,2,3,4,5],[25,10,27,6],[0]),([33,63,0,1,2,3,4,5],[4,31,0,6],[0]),([31,63,0,1,2,3,4],[4,17],[0,5,1,3,10]),([31,63,0,1,2,3,4,5],[4,17],[2,1,3,5]),([40,63,0,1,2,3,4],[4],[0,1,5]),([40,63,0,1,2,3,4,5],[4],[0,1,5]),([73,63,12,1,2,3,4,5],[4,13],[0]),([90,12,0,1,2,3,4,5],[4,17],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block7_3Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block7_3Pools wd2Autos wd2Bucket6 7 wd2Block7_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block7_3Mem : ∀ ns ∈ wd2Block7_3, Impossible wd2G 7 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket6Ok wd2Block7_3Ok
def wd2Block7_4Specs : List PoolSpec := [(14,[]),(0,[(1,0,5),(3,1,12)]),(15,[]),(8,[]),(21,[]),(1,[(1,0,5),(3,1,12)]),(4,[(1,6,5),(2,11,1)]),(12,[]),(9,[]),(3,[(1,6,5)]),(6,[]),(17,[]),(3,[(1,6,2),(1,7,5)]),(4,[(1,2,5),(2,14,4)]),(3,[(1,6,2),(1,7,5),(2,15,4)]),(1,[(1,0,5),(1,12,2),(2,92,4)]),(18,[]),(0,[(1,1,5),(1,0,5)]),(2,[(1,1,5),(1,0,5)]),(2,[(1,0,1),(1,5,6)]),(1,[]),(0,[]),(7,[]),(3,[(1,6,2),(3,7,5)]),(3,[(1,6,5),(2,11,2)]),(14,[(2,14,4)]),(11,[(2,14,4)]),(2,[]),(20,[]),(3,[(1,2,5),(2,14,6)]),(4,[(3,2,5),(1,2,5)]),(5,[(1,0,5)]),(3,[(3,2,5),(1,0,33)]),(1,[(3,2,5),(1,33,0)]),(4,[(1,1,2),(2,5,7)]),(5,[(1,0,5),(3,1,12)]),(2,[(1,0,5),(2,92,1)])]
def wd2Block7_4Pools : BT (Option BoundPool) := buildPoolsBT 6 wd2W wd2R wd2Slices wd2Block7_4Specs
def wd2Block7_4 : List NodeSpec := [([92,63,0,1,2,3,4,5],[0,1,2,3],[0]),([95,63,0,1,2,3,4,5],[3,2,4],[0]),([42,63,0,1,2,3,4,5],[4,5],[0,3]),([24,63,12,0,2,3,4],[6,4,7,8],[0,3,4,7]),([24,63,12,0,2,3,4,5],[9,10,6],[0]),([31,63,12,0,1,2,3,4],[4,10,5],[2,3,0,1]),([40,63,12,0,1,2,3,4],[4,10],[0,1]),([93,12,0,1,2,3,4,5],[4,2,11,12,7],[0,1]),([94,12,0,1,2,3,5],[8,7,13,14,15],[0,3]),([24,92,12,0,1,2,3,4],[2,16,4,17,12,18,7],[0]),([159,0,1,2,3,4,5],[7,19,20,21,22,23,24],[0,7]),([159,12,0,1,2,3,4,5],[24,7,2,19],[0]),([24,95,12,0,1,2,3,4],[7,2,24,18],[0]),([14,24,12,0,1,2,3,4],[16,2,7,0,17],[0]),([33,24,12,0,1,2,3,4],[10,0,2],[0]),([31,24,12,0,1,2,3,4],[4],[0,2,3,1,5,7]),([40,24,12,0,1,2,3,4],[4,10],[0,1]),([164,12,0,1,2,3,4],[4,7,8],[3,0]),([164,163,12,0,1,2,3,4],[4,10],[3,0,7]),([164,12,0,1,2,3,4,5],[4,10],[3,0,7]),([32,12,0,1,2,3,5],[8,13,25,26,7],[0,3]),([89,12,0,1,2,3,4,5],[4,0,10,2,18],[0]),([165,79,0,1,2,3,4,5],[4],[0,2]),([155,0,1,2,3,4,5],[4,27,3,21,22],[0,2,5]),([155,79,0,1,2,3,4,5],[4,10],[2,5,7]),([40,79,0,1,2,3,4],[4,7,8],[]),([155,154,0,1,2,3,4,5],[4],[0,3,5]),([167,79,0,1,2,3,4,5],[4,10],[0,2,3]),([169,0,1,2,3,5],[8,28,13,3],[0,2,3]),([105,0,1,2,3,4,5],[16,29,20,3],[0,2,5]),([36,14,0,1,3,4,5],[8,3,30,31],[0,3]),([21,36,0,1,2,3,4,5],[32,33],[0,1]),([109,0,1,2,3,4,5],[34,35,20,32,10],[0,1,2,3]),([109,36,0,1,2,3,4,5],[32,10],[0,1]),([109,33,0,1,2,3,4,5],[32,2,36],[0,1]),([89,36,0,1,2,3,4,5],[0,2,18],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block7_4Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block7_4Pools wd2Autos wd2Bucket6 7 wd2Block7_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block7_4Mem : ∀ ns ∈ wd2Block7_4, Impossible wd2G 7 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket6Ok wd2Block7_4Ok
def wd2Nodes7 : List NodeSpec := wd2Block7_0 ++ wd2Block7_1 ++ wd2Block7_2 ++ wd2Block7_3 ++ wd2Block7_4
def wd2Bucket7 : BT (List (List Nat)) := buildBucketsBT wd2W wd2Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd2G 7 xs.toFinset) wd2Bucket7 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append wd2Block7_0Mem wd2Block7_1Mem) wd2Block7_2Mem) wd2Block7_3Mem) wd2Block7_4Mem)
def wd2Block8_0Specs : List PoolSpec := [(12,[]),(13,[]),(4,[(1,6,2)]),(3,[(1,6,2)]),(1,[]),(2,[(1,0,1)]),(21,[]),(5,[(1,0,1)]),(14,[]),(15,[]),(0,[]),(7,[]),(5,[(1,0,1),(1,6,3)]),(8,[]),(6,[]),(5,[(1,0,1),(2,6,3)]),(9,[]),(2,[]),(4,[]),(3,[]),(5,[(1,0,1),(1,6,5)]),(4,[(1,6,5)]),(3,[(1,6,5)]),(2,[(1,0,1),(1,5,6)]),(0,[(1,0,1),(1,6,5)]),(5,[(1,0,1),(2,6,5)]),(0,[(1,0,1)]),(17,[]),(16,[]),(3,[(3,0,5)]),(5,[(1,0,3),(1,0,1)]),(5,[(1,0,5),(1,0,1)]),(11,[]),(3,[(1,2,3)]),(4,[(1,2,5)]),(3,[(1,2,5)]),(18,[]),(4,[(3,2,5)]),(3,[(3,2,5)]),(10,[]),(3,[(1,3,5)]),(3,[(3,3,5)]),(20,[]),(3,[(1,6,2),(0,7,5)]),(1,[(1,0,2),(0,123,5)]),(3,[(1,6,2),(1,7,5)]),(2,[(1,0,5)]),(1,[(1,0,5),(1,12,2)]),(3,[(1,6,2),(2,7,5)]),(1,[(1,0,2),(2,123,5)]),(3,[(1,6,2),(3,7,5)]),(1,[(1,0,2),(3,123,5)]),(5,[(1,0,5)]),(3,[(1,6,5),(1,6,2)]),(1,[(1,0,5),(1,0,2)]),(5,[])]
def wd2Block8_0Pools : BT (Option BoundPool) := buildPoolsBT 6 wd2W wd2R wd2Slices wd2Block8_0Specs
def wd2Block8_0 : List NodeSpec := [([7,0,1,2,3,4,5],[0,1,2,3,4,5],[0]),([7,6,0,1,2,3,4,5],[6,7,8,9,0,3],[0,1]),([25,0,1,2,3,4,5],[6,0,10,11],[0]),([27,0,1,2,3,4,5],[6,12,13,11,14],[0,6,2]),([37,0,1,2,3,4,5],[6,15,13,11,14],[0,6]),([55,0,1,2,3,4,5],[6,16,17,18,19,13,4,10],[0,6]),([11,0,1,2,3,4,5],[6,20,21,22,13,11,4],[0,6]),([11,6,0,1,2,3,4,5],[6,23,24,22,14,21],[0,6]),([76,0,1,2,3,4,5],[6,25,13,11,22],[0,4]),([73,0,1,2,3,4,5],[0,6,16,22,21],[0]),([73,6,0,1,2,3,4,5],[6,22,8,26,21,0,27,16,28,29],[0,6]),([71,6,1,2,3,4,5],[6,30,4,19],[0,9]),([12,6,1,2,3,4,5],[6,22,31,0,16,18],[0,4,1,3]),([39,6,0,1,2,3,4,5],[6,7,0,32,33],[0,1]),([14,6,0,1,2,3,4,5],[7,34,35,36,6,13,32],[0,1]),([33,6,0,1,2,3,4,5],[7,37,38,14,6,32],[0,1]),([31,6,0,1,2,3,4,5],[6,8,26,0,32,4,16,39,40],[0,6,3,7,2]),([40,6,0,1,2,3,4,5],[6,0,8,26,32,4,16,39,41],[0,6]),([124,0,1,2,3,4,5],[42,6,0,3],[0]),([133,0,1,2,3,4,5],[9,16,43,4,18,17,19,10,44],[0,3,2]),([92,0,1,2,3,4,5],[1,0,34,45,46,47,10],[0,2,3]),([145,0,1,2,3,4,5],[42,0,48,49],[2]),([146,0,1,2,3,4,5],[16,13,37,50,51],[0,2,3]),([12,123,1,2,3,4,5],[0,52,53,54,18],[0,3,2]),([150,123,0,1,3,4,5],[0,55,6,19,18],[3,7])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block8_0Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block8_0Pools wd2Autos wd2Bucket7 8 wd2Block8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block8_0Mem : ∀ ns ∈ wd2Block8_0, Impossible wd2G 8 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket7Ok wd2Block8_0Ok
def wd2Block8_1Specs : List PoolSpec := [(12,[]),(4,[(1,6,5)]),(3,[(1,6,2)]),(19,[]),(2,[(1,1,5)]),(21,[]),(18,[]),(15,[]),(5,[]),(4,[(1,2,5)]),(3,[(1,2,5),(1,6,2)]),(1,[(1,2,5),(1,0,2)]),(9,[]),(4,[]),(3,[(1,6,5),(2,11,0)]),(1,[(1,0,5),(2,12,0)]),(3,[(1,6,5)]),(2,[(1,0,1),(1,5,6)]),(0,[(1,0,1),(1,6,5)]),(1,[(1,0,5)]),(5,[(1,0,5),(3,1,12)]),(4,[(3,1,5)]),(8,[]),(7,[]),(1,[(1,0,5),(3,1,12)]),(2,[(1,0,5),(2,92,1)]),(0,[(1,0,5),(3,1,12)]),(5,[(1,0,5)]),(1,[(1,0,5),(1,12,2)]),(3,[(1,6,2),(1,7,5)]),(13,[]),(4,[(3,2,5)]),(1,[(1,0,5),(2,12,2)]),(3,[(1,6,5),(2,11,2)]),(2,[(1,0,5)]),(5,[(1,1,5),(1,0,5)]),(2,[(1,1,5),(1,0,5)]),(0,[(1,1,5),(1,0,5)]),(14,[]),(11,[]),(3,[(3,0,5)]),(3,[(3,0,5),(1,2,59)]),(0,[]),(1,[(3,0,5),(1,2,154)]),(3,[(1,2,5),(2,14,6)]),(1,[(1,2,5),(2,14,0)]),(6,[]),(3,[(3,2,5),(1,2,5)]),(4,[(3,2,5),(1,2,5)]),(1,[(3,2,5),(1,2,5)]),(3,[(1,2,5),(2,14,4)]),(4,[(1,2,5),(2,14,4)]),(1,[(1,2,5),(2,14,4)]),(17,[]),(3,[(3,2,5),(1,0,33)]),(1,[(3,2,5),(1,33,0)])]
def wd2Block8_1Pools : BT (Option BoundPool) := buildPoolsBT 6 wd2W wd2R wd2Slices wd2Block8_1Specs
def wd2Block8_1 : List NodeSpec := [([24,123,0,1,2,3,4,5],[0,1,2,3,4,5,6,7],[0,7,3]),([14,123,0,1,3,4,5],[0,8,9,10,11],[0,3,2]),([154,12,1,2,3,4,5],[0,12,13,14,15],[0,3,2]),([11,12,0,1,2,3,4,5],[5,1,16,6,0,12,17,18,19],[0,4,7,1,3]),([63,0,1,2,3,4,5],[5,20,16,21,22,23,24],[0,4,1,2,3,5,10]),([63,12,0,1,2,3,4,5],[21,16,6,24,0,12,25,26],[0,4,3,1,2]),([92,12,0,1,2,3,4,5],[0,27,9,28,29,7,6,5],[0,3]),([95,0,1,2,3,4,5],[30,31,0,32,33],[0,2,3]),([95,12,0,1,2,3,4,5],[0,34,3,31,6,33,32],[0,3]),([24,12,0,1,2,3,4],[16,1,35,5],[0,1,3,7,4,6,2,8]),([24,12,0,1,2,3,4,5],[16,1,6,5,0,12,36,37],[0,6,3,7]),([163,12,0,1,2,3,4],[5,6,16,0,12,21],[3,0,1,2]),([163,12,0,1,2,3,4,5],[0,5,12,16,21],[3,0,1]),([14,12,0,1,2,3,4,5],[6,0,9,27,38,39],[0,3]),([33,12,0,1,2,3,4,5],[12,34,7,5,38,39,31],[0,3]),([79,0,1,2,3,4,5],[6,5,1,0,12,40],[0,5,7]),([79,154,0,1,2,3,4,5],[0,1,12,5,40],[0,7,5]),([168,0,1,2,3,4,5],[6,9,22,41,42,43],[0,2]),([163,154,0,1,2,3,4],[0,5,12,40,13,16],[3,7]),([176,0,1,2,3,4,5],[6,9,44,45],[0,1,2,3,5]),([33,14,0,1,3,4,5],[22,8,46,47,48,49],[0,2,1,3]),([32,0,1,2,3,5],[8,12,30,50,51,52],[0,2,1,3]),([32,14,0,1,2,3,5],[53,30,50,51,8,52],[0,2,3]),([36,0,1,2,3,4,5],[27,31,54,55,46],[0,3,1,2,5]),([36,33,0,1,2,3,4,5],[12,31,34,54,55],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block8_1Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block8_1Pools wd2Autos wd2Bucket7 8 wd2Block8_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block8_1Mem : ∀ ns ∈ wd2Block8_1, Impossible wd2G 8 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket7Ok wd2Block8_1Ok
def wd2Nodes8 : List NodeSpec := wd2Block8_0 ++ wd2Block8_1
def wd2Bucket8 : BT (List (List Nat)) := buildBucketsBT wd2W wd2Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd2G 8 xs.toFinset) wd2Bucket8 := buildBucketsBT_of_mem (forall_append wd2Block8_0Mem wd2Block8_1Mem)
def wd2Block9_0Specs : List PoolSpec := [(21,[]),(5,[(1,0,1)]),(3,[]),(4,[]),(1,[]),(5,[]),(12,[]),(3,[(1,6,2)]),(1,[(1,0,2)]),(15,[]),(5,[(1,0,5)]),(3,[(1,6,5)]),(1,[(1,0,5)]),(18,[]),(3,[(3,0,5)]),(1,[(3,0,5)]),(2,[]),(0,[]),(9,[]),(3,[(1,2,5)]),(4,[(1,2,5)]),(1,[(1,2,5)]),(8,[]),(6,[]),(4,[(3,2,5)]),(3,[(3,2,5)]),(1,[(3,2,5)])]
def wd2Block9_0Pools : BT (Option BoundPool) := buildPoolsBT 5 wd2W wd2R wd2Slices wd2Block9_0Specs
def wd2Block9_0 : List NodeSpec := [([6,0,1,2,3,4,5],[0,1,2,3,4],[0,6]),([123,0,1,2,3,4,5],[5,3,6,7,8,9],[0,3,2]),([12,0,1,2,3,4,5],[3,10,11,12],[0,9,1,2,5,6,10]),([154,0,1,2,3,4,5],[13,3,14,15,16,6,17,18],[0,9,1,5,2]),([14,0,1,2,3,4,5],[5,13,19,20,21,22],[0,2,1,3]),([33,0,1,2,3,4,5],[5,23,24,25,26],[0,2,1,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block9_0Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block9_0Pools wd2Autos wd2Bucket8 9 wd2Block9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block9_0Mem : ∀ ns ∈ wd2Block9_0, Impossible wd2G 9 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket8Ok wd2Block9_0Ok
def wd2Nodes9 : List NodeSpec := wd2Block9_0
def wd2Bucket9 : BT (List (List Nat)) := buildBucketsBT wd2W wd2Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd2G 9 xs.toFinset) wd2Bucket9 := buildBucketsBT_of_mem wd2Block9_0Mem
def wd2Block10_0Specs : List PoolSpec := [(5,[]),(3,[]),(4,[]),(1,[])]
def wd2Block10_0Pools : BT (Option BoundPool) := buildPoolsBT 2 wd2W wd2R wd2Slices wd2Block10_0Specs
def wd2Block10_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3],[0,8,1,5,4,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block10_0Ok : checkNodesBT wd2W wd2G wd2Mask wd2Block10_0Pools wd2Autos wd2Bucket9 10 wd2Block10_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Block10_0Mem : ∀ ns ∈ wd2Block10_0, Impossible wd2G 10 (nodeValsBT wd2W ns).toFinset := checkNodesBT_mem (by decide) wd2Pairs wd2WOk (buildPoolsBT_sound wd2SlicesOk) wd2AutosOk wd2Bucket9Ok wd2Block10_0Ok
def wd2Nodes10 : List NodeSpec := wd2Block10_0
def wd2Bucket10 : BT (List (List Nat)) := buildBucketsBT wd2W wd2Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd2G 10 xs.toFinset) wd2Bucket10 := buildBucketsBT_of_mem wd2Block10_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd2Bound : Lower wd2R wd2G 11 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 3,32,40),(VAR 4,1,17),(VAR 5,8,40),(VAR 6,1,65)]) (by decide +kernel) wd2Bucket10Ok (by decide +kernel)
lemma wg35 : Lower (varsOf 125) 0xfffffffffffffffafffaffa0fafaa0a0 11 := wd2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg36 : Lower (varsOf 111) 0xfffffffffffefffeffecffececa0eca0 11 := carry_of (swaps := [(2, 3), (2, 5), (4, 5), (1, 4), (0, 1)]) (by decide +kernel) wg35
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg39 : Lower (varsOf 58) 0xffccffcccccccc00ffccffcccccccc00 5 := carry_of (swaps := [(2, 6), (1, 2)]) (by decide +kernel) wg13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg40 : Lower (varsOf 58) 0xffffffccffffcc00ffffffccffffcc00 5 := carry_of (swaps := [(4, 6)]) (by decide +kernel) wg23
def wd41R : List Nat := varsOf 54
def wd41G : Nat := 0xfcfcccccfcfc0000fcfcccccfcfc0000
def wd41Pos : List Nat := [18,18,20,20,22,34,34,38,38,50,52,52]
def wd41Neg : List Nat := [16,2,16,4,6,32,2,36,6,48,48,36]
def wd41Mask : Nat := fullMask 12
def wd41Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x3f3,0x152),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xd9c,0x998),(0xffff0000ffff0000ffff0000ffff0000,0xe1f,0x605),(0xffffffff00000000ffffffff00000000,0xfe0,0xea0)]
def wd41Steps : List (Nat × Nat × Nat) := []
def wd41W : BT Decor := buildWiresBT 2 wd41Base wd41Steps
def wd41AutoList : List (List (Nat × Nat)) := [[],[(1,4),(2,5)]]
def wd41Autos : BT (List (Nat × Nat)) := btOfList 1 wd41AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd41Pairs : goodPairs wd41G wd41Pos wd41Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd41BaseOk : ∀ x ∈ wd41Base, faithful wd41Pos wd41Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd41WOk : btAll (fun x => faithful wd41Pos wd41Neg x ∧ x.1 < 2^128) wd41W := buildWiresBT_faithful wd41BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd41AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw wd41G = wd41G) wd41Autos := btAll_ofList (autos_of (by decide +kernel))
def wd41SliceList : List (Option (Nat × Nat)) := []
def wd41Slices : BT (Option (Nat × Nat)) := btOfList 1 wd41SliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd41SlicesOk : btAll (fun o => ∀ p, o = some p → Slice wd41R wd41G p.1 p.2) wd41Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice wd41R wd41G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
def wd41Empty : BT (List (List Nat)) := BT.empty
lemma wd41EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible wd41G (3 - 1) xs.toFinset) wd41Empty := trivial
def wd41Block3_0Specs : List PoolSpec := []
def wd41Block3_0Pools : BT (Option BoundPool) := buildPoolsBT 1 wd41W wd41R wd41Slices wd41Block3_0Specs
def wd41Block3_0 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd41Block3_0Ok : checkNodesBT wd41W wd41G wd41Mask wd41Block3_0Pools wd41Autos wd41Empty 3 wd41Block3_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd41Block3_0Mem : ∀ ns ∈ wd41Block3_0, Impossible wd41G 3 (nodeValsBT wd41W ns).toFinset := checkNodesBT_mem (by decide) wd41Pairs wd41WOk (buildPoolsBT_sound wd41SlicesOk) wd41AutosOk wd41EmptyOk wd41Block3_0Ok
def wd41Nodes3 : List NodeSpec := wd41Block3_0
def wd41Bucket3 : BT (List (List Nat)) := buildBucketsBT wd41W wd41Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd41Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd41G 3 xs.toFinset) wd41Bucket3 := buildBucketsBT_of_mem wd41Block3_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd41Bound : Lower wd41R wd41G 4 := lower_of_forestBT (essPairs := [(VAR 1,16,18),(VAR 2,16,20),(VAR 4,2,18),(VAR 5,2,34)]) (by decide +kernel) wd41Bucket3Ok (by decide +kernel)
lemma wg42 : Lower (varsOf 54) 0xfcfcccccfcfc0000fcfcccccfcfc0000 4 := wd41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg43 : Lower (varsOf 30) 0xfcfccc00fcfccc00fcfccc00fcfccc00 4 := carry_of (swaps := [(3, 5)]) (by decide +kernel) wg42
def wd38R : List Nat := varsOf 62
def wd38G : Nat := 0xfffcffccfcfccc00fffcffccfcfccc00
def wd38Pos : List Nat := [10,10,14,14,18,18,20,20,22,26,28,28,34,34,38,38,40,40,44,44,50,52,52,56,56]
def wd38Neg : List Nat := [8,2,12,6,16,2,16,4,6,24,24,12,32,2,36,6,32,8,36,12,48,48,36,48,24]
def wd38Mask : Nat := fullMask 25
def wd38Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x10f33f,0xa12a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x6ccdcc,0x4cc98c),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x18f0e0f,0x10a0e05),(0xffff0000ffff0000ffff0000ffff0000,0x1f00ff0,0x1b00650),(0xffffffff00000000ffffffff00000000,0x1fff000,0xf55000)]
def wd38Steps : List (Nat × Nat × Nat) := [(1,0,2),(2,5,4),(2,0,2),(1,2,4)]
def wd38W : BT Decor := buildWiresBT 4 wd38Base wd38Steps
def wd38AutoList : List (List (Nat × Nat)) := [[],[(3,5)]]
def wd38Autos : BT (List (Nat × Nat)) := btOfList 1 wd38AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Pairs : goodPairs wd38G wd38Pos wd38Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38BaseOk : ∀ x ∈ wd38Base, faithful wd38Pos wd38Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38WOk : btAll (fun x => faithful wd38Pos wd38Neg x ∧ x.1 < 2^128) wd38W := buildWiresBT_faithful wd38BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw wd38G = wd38G) wd38Autos := btAll_ofList (autos_of (by decide +kernel))
def wd38SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 32 0,4),some (subcubeFast 8 0,4),some (subcubeFast 20 0,4)]
def wd38Slices : BT (Option (Nat × Nat)) := btOfList 3 wd38SliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Slice0 : Slice wd38R wd38G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffccffcccccccc00ffccffcccccccc00) (by decide +kernel) wg39
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Slice1 : Slice wd38R wd38G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffffffccffffcc00ffffffccffffcc00) (by decide +kernel) wg40
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Slice2 : Slice wd38R wd38G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 30) (qGoal := 0xfcfccc00fcfccc00fcfccc00fcfccc00) (by decide +kernel) wg43
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Slice3 : Slice wd38R wd38G (subcubeFast 8 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 54) (qGoal := 0xfcfcccccfcfc0000fcfcccccfcfc0000) (by decide +kernel) wg42
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Slice4 : Slice wd38R wd38G (subcubeFast 20 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 42) (qGoal := 0xffccffcccc00cc00ffccffcccc00cc00) (by decide +kernel) wg6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38SlicesOk : btAll (fun o => ∀ p, o = some p → Slice wd38R wd38G p.1 p.2) wd38Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice wd38R wd38G p.1 p.2) (forall_cons (fun _ h => by cases h; exact wd38Slice0) (forall_cons (fun _ h => by cases h; exact wd38Slice1) (forall_cons (fun _ h => by cases h; exact wd38Slice2) (forall_cons (fun _ h => by cases h; exact wd38Slice3) (forall_cons (fun _ h => by cases h; exact wd38Slice4) (fun _ h => (List.not_mem_nil h).elim))))))
def wd38Empty : BT (List (List Nat)) := BT.empty
lemma wd38EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible wd38G (4 - 1) xs.toFinset) wd38Empty := trivial
def wd38Block4_0Specs : List PoolSpec := []
def wd38Block4_0Pools : BT (Option BoundPool) := buildPoolsBT 1 wd38W wd38R wd38Slices wd38Block4_0Specs
def wd38Block4_0 : List NodeSpec := [([6,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Block4_0Ok : checkNodesBT wd38W wd38G wd38Mask wd38Block4_0Pools wd38Autos wd38Empty 4 wd38Block4_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Block4_0Mem : ∀ ns ∈ wd38Block4_0, Impossible wd38G 4 (nodeValsBT wd38W ns).toFinset := checkNodesBT_mem (by decide) wd38Pairs wd38WOk (buildPoolsBT_sound wd38SlicesOk) wd38AutosOk wd38EmptyOk wd38Block4_0Ok
def wd38Nodes4 : List NodeSpec := wd38Block4_0
def wd38Bucket4 : BT (List (List Nat)) := buildBucketsBT wd38W wd38Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd38G 4 xs.toFinset) wd38Bucket4 := buildBucketsBT_of_mem wd38Block4_0Mem
def wd38Block5_0Specs : List PoolSpec := [(2,[]),(3,[]),(1,[]),(0,[])]
def wd38Block5_0Pools : BT (Option BoundPool) := buildPoolsBT 2 wd38W wd38R wd38Slices wd38Block5_0Specs
def wd38Block5_0 : List NodeSpec := [([5,0,1,2,3,4],[0,1],[0]),([7,0,1,2,3,4],[2,3,1],[]),([8,0,1,2,3,4],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Block5_0Ok : checkNodesBT wd38W wd38G wd38Mask wd38Block5_0Pools wd38Autos wd38Bucket4 5 wd38Block5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Block5_0Mem : ∀ ns ∈ wd38Block5_0, Impossible wd38G 5 (nodeValsBT wd38W ns).toFinset := checkNodesBT_mem (by decide) wd38Pairs wd38WOk (buildPoolsBT_sound wd38SlicesOk) wd38AutosOk wd38Bucket4Ok wd38Block5_0Ok
def wd38Nodes5 : List NodeSpec := wd38Block5_0
def wd38Bucket5 : BT (List (List Nat)) := buildBucketsBT wd38W wd38Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd38G 5 xs.toFinset) wd38Bucket5 := buildBucketsBT_of_mem wd38Block5_0Mem
def wd38Block6_0Specs : List PoolSpec := [(4,[]),(3,[]),(2,[]),(1,[])]
def wd38Block6_0Pools : BT (Option BoundPool) := buildPoolsBT 2 wd38W wd38R wd38Slices wd38Block6_0Specs
def wd38Block6_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Block6_0Ok : checkNodesBT wd38W wd38G wd38Mask wd38Block6_0Pools wd38Autos wd38Bucket5 6 wd38Block6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Block6_0Mem : ∀ ns ∈ wd38Block6_0, Impossible wd38G 6 (nodeValsBT wd38W ns).toFinset := checkNodesBT_mem (by decide) wd38Pairs wd38WOk (buildPoolsBT_sound wd38SlicesOk) wd38AutosOk wd38Bucket5Ok wd38Block6_0Ok
def wd38Nodes6 : List NodeSpec := wd38Block6_0
def wd38Bucket6 : BT (List (List Nat)) := buildBucketsBT wd38W wd38Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd38G 6 xs.toFinset) wd38Bucket6 := buildBucketsBT_of_mem wd38Block6_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd38Bound : Lower wd38R wd38G 7 := lower_of_forestBT (essPairs := [(VAR 1,8,10),(VAR 2,16,20),(VAR 3,2,10),(VAR 4,2,18),(VAR 5,2,34)]) (by decide +kernel) wd38Bucket6Ok (by decide +kernel)
lemma wg44 : Lower (varsOf 62) 0xfffcffccfcfccc00fffcffccfcfccc00 7 := wd38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg45 : Lower (varsOf 31) 0xfefeeca0fefeeca0fefeeca0fefeeca0 7 := carry_of (swaps := [(1, 4), (2, 3), (2, 5), (0, 5)]) (by decide +kernel) wg44
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg46 : Lower (varsOf 55) 0xfefeececfefea0a0fefeececfefea0a0 7 := carry_of (swaps := [(0, 3), (1, 4), (2, 5)]) (by decide +kernel) wg44
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg47 : Lower (varsOf 59) 0xffeeffcceeeecc00ffeeffcceeeecc00 7 := carry_of (swaps := [(0, 2)]) (by decide +kernel) wg44
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg48 : Lower (varsOf 31) 0xfffeffecfffeffecfffeffecfffeffec 6 := carry_of (swaps := [(3, 6), (2, 6), (1, 4), (4, 5), (0, 5)]) (by decide +kernel) wg26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg49 : Lower (varsOf 47) 0xffecffececa0eca0ffecffececa0eca0 6 := carry_of (swaps := [(2, 3), (2, 5), (4, 5), (1, 4), (0, 1)]) (by decide +kernel) wg25
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg50 : Lower (varsOf 55) 0xfffffffffefeececfffffffffefeecec 6 := carry_of (swaps := [(1, 4), (4, 5), (5, 6), (2, 6), (2, 3), (0, 3)]) (by decide +kernel) wg26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg51 : Lower (varsOf 59) 0xffffffeeffffeeaaffffffeeffffeeaa 6 := carry_of (swaps := [(4, 6), (2, 6), (0, 2)]) (by decide +kernel) wg26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg52 : Lower (varsOf 62) 0xfffffffcfffffcf0fffffffcfffffcf0 6 := carry_of (swaps := [(4, 6), (2, 6)]) (by decide +kernel) wg26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg53 : Lower (varsOf 43) 0xffeeffeeeeaaeeaaffeeffeeeeaaeeaa 5 := carry_of (swaps := [(4, 6), (2, 4), (0, 2)]) (by decide +kernel) wg23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg54 : Lower (varsOf 46) 0xfffcfffcfcf0fcf0fffcfffcfcf0fcf0 5 := carry_of (swaps := [(4, 6), (2, 4)]) (by decide +kernel) wg23
def wd37R : List Nat := varsOf 63
def wd37G : Nat := 0xfffeffecfefeeca0fffeffecfefeeca0
def wd37Pos : List Nat := [5,5,7,7,10,10,11,11,13,13,14,14,17,17,18,18,19,20,20,22,25,25,26,28,28,34,34,35,35,37,37,38,38,40,40,41,41,44,44,49,49,50,52,52,56,56]
def wd37Neg : List Nat := [4,1,6,3,8,2,9,3,12,9,12,6,16,1,16,2,3,16,4,6,24,9,24,24,12,32,2,33,3,36,33,36,6,32,8,33,9,36,12,48,33,48,48,36,48,24]
def wd37Mask : Nat := fullMask 46
def wd37Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x198783133cf,0x118582122ca),(0xcccccccccccccccccccccccccccccccc,0x2019e49ccfc,0x1140988ac),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc61e18e0f0f,0x861a10c0d05),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x307e01f00ff0,0x205401f00750),(0xffff0000ffff0000ffff0000ffff0000,0x3f8001fff000,0x368000d25000),(0xffffffff00000000ffffffff00000000,0x3ffffe000000,0x1faaea000000)]
def wd37Steps : List (Nat × Nat × Nat) := [(1,0,1),(3,0,1),(1,7,2),(1,0,2),(1,1,3),(2,10,5),(2,1,3),(1,3,5),(1,0,3),(1,0,4),(2,15,2),(3,0,4),(1,17,1),(1,12,17),(0,1,4),(1,20,0),(1,1,4),(2,22,20),(2,1,4),(3,1,4)]
def wd37W : BT Decor := buildWiresBT 5 wd37Base wd37Steps
def wd37AutoList : List (List (Nat × Nat)) := [[],[(0,2)],[(3,5)],[(0,2),(3,5)],[(0,3),(1,4),(2,5)],[(0,5),(1,4),(2,3)],[(0,3),(2,3),(2,5),(1,4)],[(0,5),(2,5),(2,3),(1,4)]]
def wd37Autos : BT (List (Nat × Nat)) := btOfList 3 wd37AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Pairs : goodPairs wd37G wd37Pos wd37Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37BaseOk : ∀ x ∈ wd37Base, faithful wd37Pos wd37Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37WOk : btAll (fun x => faithful wd37Pos wd37Neg x ∧ x.1 < 2^128) wd37W := buildWiresBT_faithful wd37BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw wd37G = wd37G) wd37Autos := btAll_ofList (autos_of (by decide +kernel))
def wd37SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,7),some (subcubeFast 8 0,7),some (subcubeFast 4 0,7),some (subcubeFast 1 0,7),some (subcubeFast 0 32,6),some (subcubeFast 16 0,6),some (subcubeFast 0 8,6),some (subcubeFast 0 4,6),some (subcubeFast 2 0,6),some (subcubeFast 0 1,6),some (subcubeFast 16 4,5),some (subcubeFast 2 32,5),some (subcubeFast 2 8,5),some (subcubeFast 5 0,5),some (subcubeFast 1 4,5),some (subcubeFast 16 1,5),some (subcubeFast 21 0,4)]
def wd37Slices : BT (Option (Nat × Nat)) := btOfList 5 wd37SliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice0 : Slice wd37R wd37G (subcubeFast 32 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfefeeca0fefeeca0fefeeca0fefeeca0) (by decide +kernel) wg45
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice1 : Slice wd37R wd37G (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefeececfefea0a0fefeececfefea0a0) (by decide +kernel) wg46
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice2 : Slice wd37R wd37G (subcubeFast 4 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeffcceeeecc00ffeeffcceeeecc00) (by decide +kernel) wg47
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice3 : Slice wd37R wd37G (subcubeFast 1 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffcffccfcfccc00fffcffccfcfccc00) (by decide +kernel) wg44
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice4 : Slice wd37R wd37G (subcubeFast 0 32) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfffeffecfffeffecfffeffecfffeffec) (by decide +kernel) wg48
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice5 : Slice wd37R wd37G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xffecffececa0eca0ffecffececa0eca0) (by decide +kernel) wg49
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice6 : Slice wd37R wd37G (subcubeFast 0 8) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfffffffffefeececfffffffffefeecec) (by decide +kernel) wg50
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice7 : Slice wd37R wd37G (subcubeFast 0 4) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffffffeeffffeeaaffffffeeffffeeaa) (by decide +kernel) wg51
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice8 : Slice wd37R wd37G (subcubeFast 2 0) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffaffa0fafaa0a0fffaffa0fafaa0a0) (by decide +kernel) wg25
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice9 : Slice wd37R wd37G (subcubeFast 0 1) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffffffcfffffcf0fffffffcfffffcf0) (by decide +kernel) wg52
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice10 : Slice wd37R wd37G (subcubeFast 16 4) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xffeeffeeeeaaeeaaffeeffeeeeaaeeaa) (by decide +kernel) wg53
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice11 : Slice wd37R wd37G (subcubeFast 2 32) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 29) (qGoal := 0xfffaffa0fffaffa0fffaffa0fffaffa0) (by decide +kernel) wg29
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice12 : Slice wd37R wd37G (subcubeFast 2 8) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 53) (qGoal := 0xfffffffffafaa0a0fffffffffafaa0a0) (by decide +kernel) wg24
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice13 : Slice wd37R wd37G (subcubeFast 5 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffccffcccccccc00ffccffcccccccc00) (by decide +kernel) wg39
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice14 : Slice wd37R wd37G (subcubeFast 1 4) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffffffccffffcc00ffffffccffffcc00) (by decide +kernel) wg40
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice15 : Slice wd37R wd37G (subcubeFast 16 1) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 46) (qGoal := 0xfffcfffcfcf0fcf0fffcfffcfcf0fcf0) (by decide +kernel) wg54
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Slice16 : Slice wd37R wd37G (subcubeFast 21 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 42) (qGoal := 0xffccffcccc00cc00ffccffcccc00cc00) (by decide +kernel) wg6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37SlicesOk : btAll (fun o => ∀ p, o = some p → Slice wd37R wd37G p.1 p.2) wd37Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice wd37R wd37G p.1 p.2) (forall_cons (fun _ h => by cases h; exact wd37Slice0) (forall_cons (fun _ h => by cases h; exact wd37Slice1) (forall_cons (fun _ h => by cases h; exact wd37Slice2) (forall_cons (fun _ h => by cases h; exact wd37Slice3) (forall_cons (fun _ h => by cases h; exact wd37Slice4) (forall_cons (fun _ h => by cases h; exact wd37Slice5) (forall_cons (fun _ h => by cases h; exact wd37Slice6) (forall_cons (fun _ h => by cases h; exact wd37Slice7) (forall_cons (fun _ h => by cases h; exact wd37Slice8) (forall_cons (fun _ h => by cases h; exact wd37Slice9) (forall_cons (fun _ h => by cases h; exact wd37Slice10) (forall_cons (fun _ h => by cases h; exact wd37Slice11) (forall_cons (fun _ h => by cases h; exact wd37Slice12) (forall_cons (fun _ h => by cases h; exact wd37Slice13) (forall_cons (fun _ h => by cases h; exact wd37Slice14) (forall_cons (fun _ h => by cases h; exact wd37Slice15) (forall_cons (fun _ h => by cases h; exact wd37Slice16) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))
def wd37Empty : BT (List (List Nat)) := BT.empty
lemma wd37EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible wd37G (5 - 1) xs.toFinset) wd37Empty := trivial
def wd37Block5_0Specs : List PoolSpec := []
def wd37Block5_0Pools : BT (Option BoundPool) := buildPoolsBT 1 wd37W wd37R wd37Slices wd37Block5_0Specs
def wd37Block5_0 : List NodeSpec := [([11,16,0,1,3,4],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Block5_0Ok : checkNodesBT wd37W wd37G wd37Mask wd37Block5_0Pools wd37Autos wd37Empty 5 wd37Block5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Block5_0Mem : ∀ ns ∈ wd37Block5_0, Impossible wd37G 5 (nodeValsBT wd37W ns).toFinset := checkNodesBT_mem (by decide) wd37Pairs wd37WOk (buildPoolsBT_sound wd37SlicesOk) wd37AutosOk wd37EmptyOk wd37Block5_0Ok
def wd37Nodes5 : List NodeSpec := wd37Block5_0
def wd37Bucket5 : BT (List (List Nat)) := buildBucketsBT wd37W wd37Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd37G 5 xs.toFinset) wd37Bucket5 := buildBucketsBT_of_mem wd37Block5_0Mem
def wd37Block6_0Specs : List PoolSpec := [(2,[(1,1,3),(2,10,5)]),(0,[(1,0,4),(2,15,2)]),(1,[(1,0,4),(2,15,2)]),(16,[]),(12,[]),(11,[])]
def wd37Block6_0Pools : BT (Option BoundPool) := buildPoolsBT 3 wd37W wd37R wd37Slices wd37Block6_0Specs
def wd37Block6_0 : List NodeSpec := [([11,9,0,1,2,3,4],[0],[]),([10,16,0,1,3,4,5],[1,2],[0]),([12,16,0,1,3,4,5],[2],[]),([19,0,1,2,3,4,5],[],[]),([23,0,2,3,5],[3,4,5],[]),([23,22,0,2,3,5],[3,4,5],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Block6_0Ok : checkNodesBT wd37W wd37G wd37Mask wd37Block6_0Pools wd37Autos wd37Bucket5 6 wd37Block6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Block6_0Mem : ∀ ns ∈ wd37Block6_0, Impossible wd37G 6 (nodeValsBT wd37W ns).toFinset := checkNodesBT_mem (by decide) wd37Pairs wd37WOk (buildPoolsBT_sound wd37SlicesOk) wd37AutosOk wd37Bucket5Ok wd37Block6_0Ok
def wd37Nodes6 : List NodeSpec := wd37Block6_0
def wd37Bucket6 : BT (List (List Nat)) := buildBucketsBT wd37W wd37Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd37G 6 xs.toFinset) wd37Bucket6 := buildBucketsBT_of_mem wd37Block6_0Mem
def wd37Block7_0Specs : List PoolSpec := [(15,[]),(11,[]),(7,[]),(13,[]),(0,[(1,0,2)]),(2,[(1,1,3)]),(1,[(1,0,2)]),(6,[]),(2,[(2,1,3)]),(2,[(1,3,5)]),(1,[(1,0,4),(2,15,2)]),(0,[(1,0,4),(2,15,2)]),(16,[]),(9,[]),(0,[(1,0,4)]),(3,[(1,1,3)]),(1,[(1,0,4)]),(3,[(2,1,3)]),(1,[]),(0,[]),(4,[]),(5,[]),(1,[(3,0,4)]),(12,[]),(10,[])]
def wd37Block7_0Pools : BT (Option BoundPool) := buildPoolsBT 5 wd37W wd37R wd37Slices wd37Block7_0Specs
def wd37Block7_0 : List NodeSpec := [([8,0,1,3,4,5],[0,1,2],[]),([10,9,0,1,2,3,4,5],[3,2,4,5,6],[0]),([12,9,0,1,2,3,4,5],[7,2,3,8,6],[]),([13,9,0,1,2,3,4,5],[3,2,9,4],[]),([16,0,1,3,4,5],[0,2,10,11],[0,2,4]),([10,15,0,1,2,3,4,5],[12,13,14,5,15,16],[0,4]),([12,15,0,1,2,3,4,5],[13,12,8,17,16],[0]),([18,0,1,2,3,4,5],[12,18,7,19,20],[]),([12,17,0,1,2,3,4,5],[21,7,17,22],[0]),([21,1,2,3,4,5],[23,21,13,1],[]),([22,20,0,2,3,5],[12,23,1],[0]),([22,0,1,2,3,4,5],[0,23,24,1],[]),([25,24,0,2,3,5],[24,23,1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Block7_0Ok : checkNodesBT wd37W wd37G wd37Mask wd37Block7_0Pools wd37Autos wd37Bucket6 7 wd37Block7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Block7_0Mem : ∀ ns ∈ wd37Block7_0, Impossible wd37G 7 (nodeValsBT wd37W ns).toFinset := checkNodesBT_mem (by decide) wd37Pairs wd37WOk (buildPoolsBT_sound wd37SlicesOk) wd37AutosOk wd37Bucket6Ok wd37Block7_0Ok
def wd37Nodes7 : List NodeSpec := wd37Block7_0
def wd37Bucket7 : BT (List (List Nat)) := buildBucketsBT wd37W wd37Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd37G 7 xs.toFinset) wd37Bucket7 := buildBucketsBT_of_mem wd37Block7_0Mem
def wd37Block8_0Specs : List PoolSpec := [(15,[]),(12,[]),(14,[]),(2,[(1,0,1)]),(11,[]),(0,[(1,0,1)]),(3,[]),(1,[]),(2,[]),(13,[]),(1,[(1,0,2)]),(0,[(1,0,2)]),(0,[]),(4,[]),(16,[]),(9,[]),(1,[(1,0,4)]),(0,[(1,0,4)]),(5,[]),(1,[(3,0,4)]),(0,[(3,0,4)]),(8,[]),(6,[]),(7,[]),(10,[]),(1,[(1,1,4)]),(0,[(1,1,4)])]
def wd37Block8_0Pools : BT (Option BoundPool) := buildPoolsBT 5 wd37W wd37R wd37Slices wd37Block8_0Specs
def wd37Block8_0 : List NodeSpec := [([6,0,1,2,3,4,5],[0,1,2,3,4,5,6,7],[]),([7,0,1,2,3,4,5],[0,1,4,8,2,6],[0]),([9,0,1,2,3,4,5],[0,9,10,11,8],[0,2]),([14,0,1,2,3,4,5],[1,0,2,9,6,12,13],[]),([15,0,1,2,3,4,5],[14,15,16,17,8,6],[0,2,4]),([17,0,1,2,3,4,5],[18,6,2,9,19,20,21,22,13,15],[4,2,6]),([20,0,1,2,3,4,5],[0,1,4,8,6,23,7,12],[0,1,4,5]),([22,0,1,2,3,4,5],[14,1,4,0,24,25,26],[0]),([24,0,1,2,3,4,5],[1,14,4,0,24],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Block8_0Ok : checkNodesBT wd37W wd37G wd37Mask wd37Block8_0Pools wd37Autos wd37Bucket7 8 wd37Block8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Block8_0Mem : ∀ ns ∈ wd37Block8_0, Impossible wd37G 8 (nodeValsBT wd37W ns).toFinset := checkNodesBT_mem (by decide) wd37Pairs wd37WOk (buildPoolsBT_sound wd37SlicesOk) wd37AutosOk wd37Bucket7Ok wd37Block8_0Ok
def wd37Nodes8 : List NodeSpec := wd37Block8_0
def wd37Bucket8 : BT (List (List Nat)) := buildBucketsBT wd37W wd37Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd37G 8 xs.toFinset) wd37Bucket8 := buildBucketsBT_of_mem wd37Block8_0Mem
def wd37Block9_0Specs : List PoolSpec := [(3,[]),(2,[]),(1,[]),(0,[])]
def wd37Block9_0Pools : BT (Option BoundPool) := buildPoolsBT 2 wd37W wd37R wd37Slices wd37Block9_0Specs
def wd37Block9_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3],[0,5,1,4,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Block9_0Ok : checkNodesBT wd37W wd37G wd37Mask wd37Block9_0Pools wd37Autos wd37Bucket8 9 wd37Block9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Block9_0Mem : ∀ ns ∈ wd37Block9_0, Impossible wd37G 9 (nodeValsBT wd37W ns).toFinset := checkNodesBT_mem (by decide) wd37Pairs wd37WOk (buildPoolsBT_sound wd37SlicesOk) wd37AutosOk wd37Bucket8Ok wd37Block9_0Ok
def wd37Nodes9 : List NodeSpec := wd37Block9_0
def wd37Bucket9 : BT (List (List Nat)) := buildBucketsBT wd37W wd37Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd37G 9 xs.toFinset) wd37Bucket9 := buildBucketsBT_of_mem wd37Block9_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd37Bound : Lower wd37R wd37G 10 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,2,34)]) (by decide +kernel) wd37Bucket9Ok (by decide +kernel)
lemma wg55 : Lower (varsOf 63) 0xfffeffecfefeeca0fffeffecfefeeca0 10 := wd37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg57 : Lower (varsOf 122) 0xffffffffffffffccffccffcccccccc00 8 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,2,18)]) (by decide +kernel) wg9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg59 : Lower (varsOf 114) 0xffffffffffffcccccccccccccccc0000 5 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,2,18)]) (by decide +kernel) wg8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg60 : Lower (varsOf 86) 0xfffffcfcfffffcfcfcfc0000fcfc0000 5 := carry_of (swaps := [(3, 5), (2, 3), (1, 4)]) (by decide +kernel) wg59
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg61 : Lower (varsOf 102) 0xfffffffffcfcfcfccccccccc00000000 5 := carry_of (swaps := [(1, 3), (2, 4)]) (by decide +kernel) wg13
def wd58R : List Nat := varsOf 118
def wd58G : Nat := 0xfffffffffffffcfcfcfcccccfcfc0000
def wd58Pos : List Nat := [18,18,20,20,22,34,34,38,38,50,52,52,66,66,68,68,70,80,80,96,96,100,112]
def wd58Neg : List Nat := [16,2,16,4,6,32,2,36,6,48,48,36,64,2,64,4,6,64,16,64,32,36,48]
def wd58Mask : Nat := fullMask 23
def wd58Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x133f3,0x12152),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x21cd9c,0x218998),(0xffff0000ffff0000ffff0000ffff0000,0x460e1f,0x440605),(0xffffffff00000000ffffffff00000000,0x780fe0,0x700ea0),(0xffffffffffffffff0000000000000000,0x7ff000,0xa5000)]
def wd58Steps : List (Nat × Nat × Nat) := []
def wd58W : BT Decor := buildWiresBT 3 wd58Base wd58Steps
def wd58AutoList : List (List (Nat × Nat)) := [[],[(1,4),(2,5)]]
def wd58Autos : BT (List (Nat × Nat)) := btOfList 1 wd58AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd58Pairs : goodPairs wd58G wd58Pos wd58Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd58BaseOk : ∀ x ∈ wd58Base, faithful wd58Pos wd58Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd58WOk : btAll (fun x => faithful wd58Pos wd58Neg x ∧ x.1 < 2^128) wd58W := buildWiresBT_faithful wd58BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd58AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw wd58G = wd58G) wd58Autos := btAll_ofList (autos_of (by decide +kernel))
def wd58SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,5),some (subcubeFast 16 0,5),some (subcubeFast 4 0,5),some (subcubeFast 2 0,5)]
def wd58Slices : BT (Option (Nat × Nat)) := btOfList 2 wd58SliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd58Slice0 : Slice wd58R wd58G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 86) (qGoal := 0xfffffcfcfffffcfcfcfc0000fcfc0000) (by decide +kernel) wg60
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd58Slice1 : Slice wd58R wd58G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 102) (qGoal := 0xfffffffffcfcfcfccccccccc00000000) (by decide +kernel) wg61
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd58Slice2 : Slice wd58R wd58G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 114) (qGoal := 0xffffffffffffcccccccccccccccc0000) (by decide +kernel) wg59
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd58Slice3 : Slice wd58R wd58G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 116) (qGoal := 0xfffffffffffff0f0f0f00000f0f00000) (by decide +kernel) wg16
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd58SlicesOk : btAll (fun o => ∀ p, o = some p → Slice wd58R wd58G p.1 p.2) wd58Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice wd58R wd58G p.1 p.2) (forall_cons (fun _ h => by cases h; exact wd58Slice0) (forall_cons (fun _ h => by cases h; exact wd58Slice1) (forall_cons (fun _ h => by cases h; exact wd58Slice2) (forall_cons (fun _ h => by cases h; exact wd58Slice3) (fun _ h => (List.not_mem_nil h).elim)))))
def wd58Empty : BT (List (List Nat)) := BT.empty
lemma wd58EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible wd58G (6 - 1) xs.toFinset) wd58Empty := trivial
def wd58Block6_0Specs : List PoolSpec := [(3,[]),(1,[]),(2,[]),(0,[])]
def wd58Block6_0Pools : BT (Option BoundPool) := buildPoolsBT 2 wd58W wd58R wd58Slices wd58Block6_0Specs
def wd58Block6_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd58Block6_0Ok : checkNodesBT wd58W wd58G wd58Mask wd58Block6_0Pools wd58Autos wd58Empty 6 wd58Block6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd58Block6_0Mem : ∀ ns ∈ wd58Block6_0, Impossible wd58G 6 (nodeValsBT wd58W ns).toFinset := checkNodesBT_mem (by decide) wd58Pairs wd58WOk (buildPoolsBT_sound wd58SlicesOk) wd58AutosOk wd58EmptyOk wd58Block6_0Ok
def wd58Nodes6 : List NodeSpec := wd58Block6_0
def wd58Bucket6 : BT (List (List Nat)) := buildBucketsBT wd58W wd58Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd58Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd58G 6 xs.toFinset) wd58Bucket6 := buildBucketsBT_of_mem wd58Block6_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd58Bound : Lower wd58R wd58G 7 := lower_of_forestBT (essPairs := [(VAR 1,16,18),(VAR 2,16,20),(VAR 4,2,18),(VAR 5,2,34),(VAR 6,2,66)]) (by decide +kernel) wd58Bucket6Ok (by decide +kernel)
lemma wg62 : Lower (varsOf 118) 0xfffffffffffffcfcfcfcccccfcfc0000 7 := wd58Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg63 : Lower (varsOf 94) 0xfffffffcfffffffcfcfccc00fcfccc00 7 := carry_of (swaps := [(3, 5)]) (by decide +kernel) wg62
def wd56R : List Nat := varsOf 126
def wd56G : Nat := 0xfffffffffffffffcfffcffccfcfccc00
def wd56Pos : List Nat := [10,10,14,14,18,18,20,20,22,26,28,28,34,34,38,38,40,40,44,44,50,52,52,56,56,66,66,68,68,70,72,72,76,80,80,88,96,96,100,112]
def wd56Neg : List Nat := [8,2,12,6,16,2,16,4,6,24,24,12,32,2,36,6,32,8,36,12,48,48,36,48,24,64,2,64,4,6,64,8,12,64,16,24,64,32,36,48]
def wd56Mask : Nat := fullMask 40
def wd56Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x2610f33f,0x2400a12a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x41386ccdcc,0x41304cc98c),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x9c18f0e0f,0x9810a0e05),(0xffff0000ffff0000ffff0000ffff0000,0x8e01f00ff0,0x8c01b00650),(0xffffffff00000000ffffffff00000000,0xf001fff000,0xe000f55000),(0xffffffffffffffff0000000000000000,0xfffe000000,0x124a000000)]
def wd56Steps : List (Nat × Nat × Nat) := [(1,2,4),(1,6,5),(1,2,5),(1,4,5),(2,8,4)]
def wd56W : BT Decor := buildWiresBT 4 wd56Base wd56Steps
def wd56AutoList : List (List (Nat × Nat)) := [[],[(3,5)]]
def wd56Autos : BT (List (Nat × Nat)) := btOfList 1 wd56AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Pairs : goodPairs wd56G wd56Pos wd56Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56BaseOk : ∀ x ∈ wd56Base, faithful wd56Pos wd56Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56WOk : btAll (fun x => faithful wd56Pos wd56Neg x ∧ x.1 < 2^128) wd56W := buildWiresBT_faithful wd56BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw wd56G = wd56G) wd56Autos := btAll_ofList (autos_of (by decide +kernel))
def wd56SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 16 0,8),some (subcubeFast 4 0,8),some (subcubeFast 2 0,8),some (subcubeFast 64 0,7),some (subcubeFast 32 0,7),some (subcubeFast 8 0,7),some (subcubeFast 0 4,6),some (subcubeFast 64 4,5),some (subcubeFast 96 0,4),some (subcubeFast 72 0,4),some (subcubeFast 42 0,4)]
def wd56Slices : BT (Option (Nat × Nat)) := btOfList 4 wd56SliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Slice0 : Slice wd56R wd56G (subcubeFast 16 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 110) (qGoal := 0xfffffffffffcfffcffccffcccc00cc00) (by decide +kernel) wg10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Slice1 : Slice wd56R wd56G (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 122) (qGoal := 0xffffffffffffffccffccffcccccccc00) (by decide +kernel) wg57
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Slice2 : Slice wd56R wd56G (subcubeFast 2 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 124) (qGoal := 0xfffffffffffffff0fff0ff00f0f00000) (by decide +kernel) wg18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Slice3 : Slice wd56R wd56G (subcubeFast 64 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffcffccfcfccc00fffcffccfcfccc00) (by decide +kernel) wg44
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Slice4 : Slice wd56R wd56G (subcubeFast 32 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 94) (qGoal := 0xfffffffcfffffffcfcfccc00fcfccc00) (by decide +kernel) wg63
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Slice5 : Slice wd56R wd56G (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 118) (qGoal := 0xfffffffffffffcfcfcfcccccfcfc0000) (by decide +kernel) wg62
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Slice6 : Slice wd56R wd56G (subcubeFast 0 4) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 122) (qGoal := 0xffffffffffffffffffffffccffffcc00) (by decide +kernel) wg26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Slice7 : Slice wd56R wd56G (subcubeFast 64 4) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffffffccffffcc00ffffffccffffcc00) (by decide +kernel) wg40
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Slice8 : Slice wd56R wd56G (subcubeFast 96 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 30) (qGoal := 0xfcfccc00fcfccc00fcfccc00fcfccc00) (by decide +kernel) wg43
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Slice9 : Slice wd56R wd56G (subcubeFast 72 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 54) (qGoal := 0xfcfcccccfcfc0000fcfcccccfcfc0000) (by decide +kernel) wg42
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Slice10 : Slice wd56R wd56G (subcubeFast 42 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 84) (qGoal := 0xfffff0f0fffff0f0f0f00000f0f00000) (by decide +kernel) wg17
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56SlicesOk : btAll (fun o => ∀ p, o = some p → Slice wd56R wd56G p.1 p.2) wd56Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice wd56R wd56G p.1 p.2) (forall_cons (fun _ h => by cases h; exact wd56Slice0) (forall_cons (fun _ h => by cases h; exact wd56Slice1) (forall_cons (fun _ h => by cases h; exact wd56Slice2) (forall_cons (fun _ h => by cases h; exact wd56Slice3) (forall_cons (fun _ h => by cases h; exact wd56Slice4) (forall_cons (fun _ h => by cases h; exact wd56Slice5) (forall_cons (fun _ h => by cases h; exact wd56Slice6) (forall_cons (fun _ h => by cases h; exact wd56Slice7) (forall_cons (fun _ h => by cases h; exact wd56Slice8) (forall_cons (fun _ h => by cases h; exact wd56Slice9) (forall_cons (fun _ h => by cases h; exact wd56Slice10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def wd56Empty : BT (List (List Nat)) := BT.empty
lemma wd56EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible wd56G (6 - 1) xs.toFinset) wd56Empty := trivial
def wd56Block6_0Specs : List PoolSpec := [(10,[]),(7,[]),(0,[(1,4,5),(1,2,5),(1,2,4)])]
def wd56Block6_0Pools : BT (Option BoundPool) := buildPoolsBT 2 wd56W wd56R wd56Slices wd56Block6_0Specs
def wd56Block6_0 : List NodeSpec := [([9,8,6,0,1,3],[0,1,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Block6_0Ok : checkNodesBT wd56W wd56G wd56Mask wd56Block6_0Pools wd56Autos wd56Empty 6 wd56Block6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Block6_0Mem : ∀ ns ∈ wd56Block6_0, Impossible wd56G 6 (nodeValsBT wd56W ns).toFinset := checkNodesBT_mem (by decide) wd56Pairs wd56WOk (buildPoolsBT_sound wd56SlicesOk) wd56AutosOk wd56EmptyOk wd56Block6_0Ok
def wd56Nodes6 : List NodeSpec := wd56Block6_0
def wd56Bucket6 : BT (List (List Nat)) := buildBucketsBT wd56W wd56Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd56G 6 xs.toFinset) wd56Bucket6 := buildBucketsBT_of_mem wd56Block6_0Mem
def wd56Block7_0Specs : List PoolSpec := [(10,[]),(0,[(1,2,4),(1,6,5)]),(1,[]),(6,[]),(8,[]),(9,[]),(6,[(1,2,5)]),(0,[(1,2,5),(1,2,4)]),(3,[(1,2,4)]),(0,[(1,2,5),(2,8,4)]),(7,[]),(0,[(1,4,5),(1,2,5)])]
def wd56Block7_0Pools : BT (Option BoundPool) := buildPoolsBT 4 wd56W wd56R wd56Slices wd56Block7_0Specs
def wd56Block7_0 : List NodeSpec := [([7,0,1,2,3,4,5],[0,1,2,3,4,5],[]),([8,6,0,1,3,4,5],[0,5,6,7,8],[0]),([7,8,0,1,2,3,4,5],[0,4,5],[]),([10,0,1,2,3,4,5],[0,5,9,2,3],[]),([9,8,0,1,2,3,4],[0,10,11,4,5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Block7_0Ok : checkNodesBT wd56W wd56G wd56Mask wd56Block7_0Pools wd56Autos wd56Bucket6 7 wd56Block7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Block7_0Mem : ∀ ns ∈ wd56Block7_0, Impossible wd56G 7 (nodeValsBT wd56W ns).toFinset := checkNodesBT_mem (by decide) wd56Pairs wd56WOk (buildPoolsBT_sound wd56SlicesOk) wd56AutosOk wd56Bucket6Ok wd56Block7_0Ok
def wd56Nodes7 : List NodeSpec := wd56Block7_0
def wd56Bucket7 : BT (List (List Nat)) := buildBucketsBT wd56W wd56Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd56G 7 xs.toFinset) wd56Bucket7 := buildBucketsBT_of_mem wd56Block7_0Mem
def wd56Block8_0Specs : List PoolSpec := [(10,[]),(1,[(1,2,4)]),(0,[(1,2,4)]),(4,[]),(3,[]),(7,[]),(0,[(1,2,5)]),(2,[(1,2,5)]),(1,[(1,2,5)]),(9,[]),(5,[])]
def wd56Block8_0Pools : BT (Option BoundPool) := buildPoolsBT 4 wd56W wd56R wd56Slices wd56Block8_0Specs
def wd56Block8_0 : List NodeSpec := [([6,0,1,2,3,4,5],[0,1,2,3,4],[0,1]),([8,0,1,2,3,4,5],[0,5,6,7,8,4,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Block8_0Ok : checkNodesBT wd56W wd56G wd56Mask wd56Block8_0Pools wd56Autos wd56Bucket7 8 wd56Block8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Block8_0Mem : ∀ ns ∈ wd56Block8_0, Impossible wd56G 8 (nodeValsBT wd56W ns).toFinset := checkNodesBT_mem (by decide) wd56Pairs wd56WOk (buildPoolsBT_sound wd56SlicesOk) wd56AutosOk wd56Bucket7Ok wd56Block8_0Ok
def wd56Nodes8 : List NodeSpec := wd56Block8_0
def wd56Bucket8 : BT (List (List Nat)) := buildBucketsBT wd56W wd56Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd56G 8 xs.toFinset) wd56Bucket8 := buildBucketsBT_of_mem wd56Block8_0Mem
def wd56Block9_0Specs : List PoolSpec := [(2,[]),(1,[]),(0,[]),(4,[]),(5,[]),(3,[])]
def wd56Block9_0Pools : BT (Option BoundPool) := buildPoolsBT 3 wd56W wd56R wd56Slices wd56Block9_0Specs
def wd56Block9_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Block9_0Ok : checkNodesBT wd56W wd56G wd56Mask wd56Block9_0Pools wd56Autos wd56Bucket8 9 wd56Block9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Block9_0Mem : ∀ ns ∈ wd56Block9_0, Impossible wd56G 9 (nodeValsBT wd56W ns).toFinset := checkNodesBT_mem (by decide) wd56Pairs wd56WOk (buildPoolsBT_sound wd56SlicesOk) wd56AutosOk wd56Bucket8Ok wd56Block9_0Ok
def wd56Nodes9 : List NodeSpec := wd56Block9_0
def wd56Bucket9 : BT (List (List Nat)) := buildBucketsBT wd56W wd56Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd56G 9 xs.toFinset) wd56Bucket9 := buildBucketsBT_of_mem wd56Block9_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd56Bound : Lower wd56R wd56G 10 := lower_of_forestBT (essPairs := [(VAR 1,8,10),(VAR 2,16,20),(VAR 3,2,10),(VAR 4,2,18),(VAR 5,2,34),(VAR 6,2,66)]) (by decide +kernel) wd56Bucket9Ok (by decide +kernel)
lemma wg64 : Lower (varsOf 126) 0xfffffffffffffffcfffcffccfcfccc00 10 := wd56Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg65 : Lower (varsOf 95) 0xfffffffefffffffefefeeca0fefeeca0 10 := carry_of (swaps := [(1, 4), (2, 3), (2, 5), (0, 5)]) (by decide +kernel) wg64
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg66 : Lower (varsOf 119) 0xfffffffffffffefefefeececfefea0a0 10 := carry_of (swaps := [(0, 3), (1, 4), (2, 5)]) (by decide +kernel) wg64
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg67 : Lower (varsOf 123) 0xffffffffffffffeeffeeffcceeeecc00 10 := carry_of (swaps := [(0, 2)]) (by decide +kernel) wg64
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg68 : Lower (varsOf 87) 0xfffffefefffffefefefea0a0fefea0a0 8 := carry_of (swaps := [(0, 3), (1, 4), (2, 5)]) (by decide +kernel) wg57
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg69 : Lower (varsOf 126) 0xfffffffffffffffffffffffcfffffcf0 7 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,0,4)]) (by decide +kernel) wg26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg70 : Lower (varsOf 95) 0xfffffffffffffffffffeffecfffeffec 7 := carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (0, 5)]) (by decide +kernel) wg69
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg71 : Lower (varsOf 119) 0xfffffffffffffffffffffffffefeecec 7 := carry_of (swaps := [(4, 5), (1, 2), (2, 3), (0, 3)]) (by decide +kernel) wg69
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg72 : Lower (varsOf 123) 0xffffffffffffffffffffffeeffffeeaa 7 := carry_of (swaps := [(0, 2)]) (by decide +kernel) wg69
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg73 : Lower (varsOf 91) 0xffffffeeffffffeeeeeecc00eeeecc00 7 := carry_of (swaps := [(0, 2), (3, 5)]) (by decide +kernel) wg62
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg74 : Lower (varsOf 115) 0xffffffffffffeeeeeeeecccceeee0000 7 := carry_of (swaps := [(0, 2)]) (by decide +kernel) wg62
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg75 : Lower (varsOf 87) 0xfffffffffffffffffefeececfefeecec 6 := carry_of (swaps := [(1, 4), (4, 5), (2, 5), (2, 3), (0, 3)]) (by decide +kernel) wg26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg76 : Lower (varsOf 110) 0xfffffffffffffffffffcfffcfcf0fcf0 6 := carry_of (swaps := [(2, 4)]) (by decide +kernel) wg26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg77 : Lower (varsOf 23) 0xfefeececfefeececfefeececfefeecec 5 := carry_of (swaps := [(1, 6), (4, 6), (4, 5), (2, 5), (2, 3), (0, 3)]) (by decide +kernel) wg23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wg78 : Lower (varsOf 82) 0xffffccccffffcccccccc0000cccc0000 4 := carry_of (swaps := [(4, 5), (2, 3), (1, 2)]) (by decide +kernel) wg5
def wd1R : List Nat := varsOf 127
def wd1G : Nat := 0xfffffffffffffffefffeffecfefeeca0
def wd1Pos : List Nat := [5,5,7,7,10,10,11,11,13,13,14,14,17,17,18,18,19,20,20,22,25,25,26,28,28,34,34,35,35,37,37,38,38,40,40,41,41,44,44,49,49,50,52,52,56,56,65,65,66,66,67,68,68,70,72,72,73,76,80,80,88,96,96,97,100,112]
def wd1Neg : List Nat := [4,1,6,3,8,2,9,3,12,9,12,6,16,1,16,2,3,16,4,6,24,9,24,24,12,32,2,33,3,36,33,36,6,32,8,33,9,36,12,48,33,48,48,36,48,24,64,1,64,2,3,64,4,6,64,8,9,12,64,16,24,64,32,33,36,48]
def wd1Mask : Nat := fullMask 66
def wd1Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x8104c198783133cf,0x81048118582122ca),(0xcccccccccccccccccccccccccccccccc,0x2702019e49ccfc,0x260001140988ac),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x102380c61e18e0f0f,0x102300861a10c0d05),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x13c0307e01f00ff0,0x1380205401f00750),(0xffff0000ffff0000ffff0000ffff0000,0x21c003f8001fff000,0x21800368000d25000),(0xffffffff00000000ffffffff00000000,0x3e0003ffffe000000,0x3c0001faaea000000),(0xffffffffffffffff0000000000000000,0x3ffffc00000000000,0x2449400000000000)]
def wd1Steps : List (Nat × Nat × Nat) := [(1,0,2),(1,7,3),(1,8,5),(2,8,5),(1,8,6),(2,8,6),(1,0,6),(1,2,6),(1,3,6),(1,7,6),(2,16,3),(1,3,5),(1,15,5),(2,15,5),(1,5,6),(1,0,3),(2,22,2),(1,23,5),(1,23,6),(1,22,6),(2,26,2),(1,0,5),(1,2,5),(2,22,6),(1,30,2),(1,2,3),(2,13,5),(2,13,2),(1,34,3),(2,26,5),(2,13,3),(1,37,2),(1,37,5)]
def wd1W : BT Decor := buildWiresBT 6 wd1Base wd1Steps
def wd1AutoList : List (List (Nat × Nat)) := [[],[(0,2)],[(3,5)],[(0,2),(3,5)],[(0,3),(1,4),(2,5)],[(0,5),(1,4),(2,3)],[(0,3),(2,3),(2,5),(1,4)],[(0,5),(2,5),(2,3),(1,4)]]
def wd1Autos : BT (List (Nat × Nat)) := btOfList 3 wd1AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Pairs : goodPairs wd1G wd1Pos wd1Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1BaseOk : ∀ x ∈ wd1Base, faithful wd1Pos wd1Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1WOk : btAll (fun x => faithful wd1Pos wd1Neg x ∧ x.1 < 2^128) wd1W := buildWiresBT_faithful wd1BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw wd1G = wd1G) wd1Autos := btAll_ofList (autos_of (by decide +kernel))
def wd1SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 16 0,11),some (subcubeFast 2 0,11),some (subcubeFast 64 0,10),some (subcubeFast 32 0,10),some (subcubeFast 8 0,10),some (subcubeFast 4 0,10),some (subcubeFast 1 0,10),some (subcubeFast 40 0,8),some (subcubeFast 5 0,8),some (subcubeFast 0 32,7),some (subcubeFast 0 8,7),some (subcubeFast 0 4,7),some (subcubeFast 0 1,7),some (subcubeFast 96 0,7),some (subcubeFast 72 0,7),some (subcubeFast 68 0,7),some (subcubeFast 36 0,7),some (subcubeFast 12 0,7),some (subcubeFast 65 0,7),some (subcubeFast 33 0,7),some (subcubeFast 9 0,7),some (subcubeFast 42 0,7),some (subcubeFast 21 0,7),some (subcubeFast 64 32,6),some (subcubeFast 64 8,6),some (subcubeFast 32 8,6),some (subcubeFast 64 4,6),some (subcubeFast 2 8,6),some (subcubeFast 16 1,6),some (subcubeFast 4 1,6),some (subcubeFast 72 32,5),some (subcubeFast 96 8,5),some (subcubeFast 80 4,5),some (subcubeFast 66 8,5),some (subcubeFast 69 0,5),some (subcubeFast 65 4,5),some (subcubeFast 68 1,5),some (subcubeFast 98 8,4),some (subcubeFast 45 0,4)]
def wd1Slices : BT (Option (Nat × Nat)) := btOfList 6 wd1SliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice0 : Slice wd1R wd1G (subcubeFast 16 0) 11 := slice_fast_direct (zDead := 0) (qRoots := varsOf 111) (qGoal := 0xfffffffffffefffeffecffececa0eca0) (by decide +kernel) wg36
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice1 : Slice wd1R wd1G (subcubeFast 2 0) 11 := slice_fast_direct (zDead := 0) (qRoots := varsOf 125) (qGoal := 0xfffffffffffffffafffaffa0fafaa0a0) (by decide +kernel) wg35
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice2 : Slice wd1R wd1G (subcubeFast 64 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 63) (qGoal := 0xfffeffecfefeeca0fffeffecfefeeca0) (by decide +kernel) wg55
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice3 : Slice wd1R wd1G (subcubeFast 32 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 95) (qGoal := 0xfffffffefffffffefefeeca0fefeeca0) (by decide +kernel) wg65
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice4 : Slice wd1R wd1G (subcubeFast 8 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 119) (qGoal := 0xfffffffffffffefefefeececfefea0a0) (by decide +kernel) wg66
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice5 : Slice wd1R wd1G (subcubeFast 4 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 123) (qGoal := 0xffffffffffffffeeffeeffcceeeecc00) (by decide +kernel) wg67
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice6 : Slice wd1R wd1G (subcubeFast 1 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 126) (qGoal := 0xfffffffffffffffcfffcffccfcfccc00) (by decide +kernel) wg64
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice7 : Slice wd1R wd1G (subcubeFast 40 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 87) (qGoal := 0xfffffefefffffefefefea0a0fefea0a0) (by decide +kernel) wg68
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice8 : Slice wd1R wd1G (subcubeFast 5 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 122) (qGoal := 0xffffffffffffffccffccffcccccccc00) (by decide +kernel) wg57
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice9 : Slice wd1R wd1G (subcubeFast 0 32) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 95) (qGoal := 0xfffffffffffffffffffeffecfffeffec) (by decide +kernel) wg70
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice10 : Slice wd1R wd1G (subcubeFast 0 8) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 119) (qGoal := 0xfffffffffffffffffffffffffefeecec) (by decide +kernel) wg71
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice11 : Slice wd1R wd1G (subcubeFast 0 4) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 123) (qGoal := 0xffffffffffffffffffffffeeffffeeaa) (by decide +kernel) wg72
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice12 : Slice wd1R wd1G (subcubeFast 0 1) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 126) (qGoal := 0xfffffffffffffffffffffffcfffffcf0) (by decide +kernel) wg69
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice13 : Slice wd1R wd1G (subcubeFast 96 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfefeeca0fefeeca0fefeeca0fefeeca0) (by decide +kernel) wg45
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice14 : Slice wd1R wd1G (subcubeFast 72 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefeececfefea0a0fefeececfefea0a0) (by decide +kernel) wg46
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice15 : Slice wd1R wd1G (subcubeFast 68 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeffcceeeecc00ffeeffcceeeecc00) (by decide +kernel) wg47
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice16 : Slice wd1R wd1G (subcubeFast 36 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 91) (qGoal := 0xffffffeeffffffeeeeeecc00eeeecc00) (by decide +kernel) wg73
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice17 : Slice wd1R wd1G (subcubeFast 12 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 115) (qGoal := 0xffffffffffffeeeeeeeecccceeee0000) (by decide +kernel) wg74
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice18 : Slice wd1R wd1G (subcubeFast 65 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffcffccfcfccc00fffcffccfcfccc00) (by decide +kernel) wg44
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice19 : Slice wd1R wd1G (subcubeFast 33 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 94) (qGoal := 0xfffffffcfffffffcfcfccc00fcfccc00) (by decide +kernel) wg63
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice20 : Slice wd1R wd1G (subcubeFast 9 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 118) (qGoal := 0xfffffffffffffcfcfcfcccccfcfc0000) (by decide +kernel) wg62
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice21 : Slice wd1R wd1G (subcubeFast 42 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 85) (qGoal := 0xfffffafafffffafafafaa0a0fafaa0a0) (by decide +kernel) wg22
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice22 : Slice wd1R wd1G (subcubeFast 21 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 106) (qGoal := 0xffffffffffccffccffccffcccc00cc00) (by decide +kernel) wg9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice23 : Slice wd1R wd1G (subcubeFast 64 32) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfffeffecfffeffecfffeffecfffeffec) (by decide +kernel) wg48
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice24 : Slice wd1R wd1G (subcubeFast 64 8) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfffffffffefeececfffffffffefeecec) (by decide +kernel) wg50
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice25 : Slice wd1R wd1G (subcubeFast 32 8) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 87) (qGoal := 0xfffffffffffffffffefeececfefeecec) (by decide +kernel) wg75
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice26 : Slice wd1R wd1G (subcubeFast 64 4) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffffffeeffffeeaaffffffeeffffeeaa) (by decide +kernel) wg51
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice27 : Slice wd1R wd1G (subcubeFast 2 8) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 117) (qGoal := 0xfffffffffffffffffffffffffafaa0a0) (by decide +kernel) wg28
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice28 : Slice wd1R wd1G (subcubeFast 16 1) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 110) (qGoal := 0xfffffffffffffffffffcfffcfcf0fcf0) (by decide +kernel) wg76
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice29 : Slice wd1R wd1G (subcubeFast 4 1) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 122) (qGoal := 0xffffffffffffffffffffffccffffcc00) (by decide +kernel) wg26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice30 : Slice wd1R wd1G (subcubeFast 72 32) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 23) (qGoal := 0xfefeececfefeececfefeececfefeecec) (by decide +kernel) wg77
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice31 : Slice wd1R wd1G (subcubeFast 96 8) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 23) (qGoal := 0xfefeececfefeececfefeececfefeecec) (by decide +kernel) wg77
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice32 : Slice wd1R wd1G (subcubeFast 80 4) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xffeeffeeeeaaeeaaffeeffeeeeaaeeaa) (by decide +kernel) wg53
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice33 : Slice wd1R wd1G (subcubeFast 66 8) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 53) (qGoal := 0xfffffffffafaa0a0fffffffffafaa0a0) (by decide +kernel) wg24
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice34 : Slice wd1R wd1G (subcubeFast 69 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffccffcccccccc00ffccffcccccccc00) (by decide +kernel) wg39
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice35 : Slice wd1R wd1G (subcubeFast 65 4) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffffffccffffcc00ffffffccffffcc00) (by decide +kernel) wg40
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice36 : Slice wd1R wd1G (subcubeFast 68 1) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffffffccffffcc00ffffffccffffcc00) (by decide +kernel) wg40
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice37 : Slice wd1R wd1G (subcubeFast 98 8) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 21) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) wg34
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Slice38 : Slice wd1R wd1G (subcubeFast 45 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 82) (qGoal := 0xffffccccffffcccccccc0000cccc0000) (by decide +kernel) wg78
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1SlicesOk : btAll (fun o => ∀ p, o = some p → Slice wd1R wd1G p.1 p.2) wd1Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice wd1R wd1G p.1 p.2) (forall_cons (fun _ h => by cases h; exact wd1Slice0) (forall_cons (fun _ h => by cases h; exact wd1Slice1) (forall_cons (fun _ h => by cases h; exact wd1Slice2) (forall_cons (fun _ h => by cases h; exact wd1Slice3) (forall_cons (fun _ h => by cases h; exact wd1Slice4) (forall_cons (fun _ h => by cases h; exact wd1Slice5) (forall_cons (fun _ h => by cases h; exact wd1Slice6) (forall_cons (fun _ h => by cases h; exact wd1Slice7) (forall_cons (fun _ h => by cases h; exact wd1Slice8) (forall_cons (fun _ h => by cases h; exact wd1Slice9) (forall_cons (fun _ h => by cases h; exact wd1Slice10) (forall_cons (fun _ h => by cases h; exact wd1Slice11) (forall_cons (fun _ h => by cases h; exact wd1Slice12) (forall_cons (fun _ h => by cases h; exact wd1Slice13) (forall_cons (fun _ h => by cases h; exact wd1Slice14) (forall_cons (fun _ h => by cases h; exact wd1Slice15) (forall_cons (fun _ h => by cases h; exact wd1Slice16) (forall_cons (fun _ h => by cases h; exact wd1Slice17) (forall_cons (fun _ h => by cases h; exact wd1Slice18) (forall_cons (fun _ h => by cases h; exact wd1Slice19) (forall_cons (fun _ h => by cases h; exact wd1Slice20) (forall_cons (fun _ h => by cases h; exact wd1Slice21) (forall_cons (fun _ h => by cases h; exact wd1Slice22) (forall_cons (fun _ h => by cases h; exact wd1Slice23) (forall_cons (fun _ h => by cases h; exact wd1Slice24) (forall_cons (fun _ h => by cases h; exact wd1Slice25) (forall_cons (fun _ h => by cases h; exact wd1Slice26) (forall_cons (fun _ h => by cases h; exact wd1Slice27) (forall_cons (fun _ h => by cases h; exact wd1Slice28) (forall_cons (fun _ h => by cases h; exact wd1Slice29) (forall_cons (fun _ h => by cases h; exact wd1Slice30) (forall_cons (fun _ h => by cases h; exact wd1Slice31) (forall_cons (fun _ h => by cases h; exact wd1Slice32) (forall_cons (fun _ h => by cases h; exact wd1Slice33) (forall_cons (fun _ h => by cases h; exact wd1Slice34) (forall_cons (fun _ h => by cases h; exact wd1Slice35) (forall_cons (fun _ h => by cases h; exact wd1Slice36) (forall_cons (fun _ h => by cases h; exact wd1Slice37) (forall_cons (fun _ h => by cases h; exact wd1Slice38) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))
def wd1Empty : BT (List (List Nat)) := BT.empty
lemma wd1EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible wd1G (8 - 1) xs.toFinset) wd1Empty := trivial
def wd1Block8_0Specs : List PoolSpec := [(33,[]),(22,[]),(11,[(1,0,6)]),(12,[(1,2,6)]),(2,[]),(23,[]),(21,[(1,2,6),(1,0,6),(1,0,2)]),(22,[(1,8,5)]),(15,[]),(18,[]),(3,[(1,2,6),(1,0,6),(1,0,2)]),(37,[]),(36,[]),(32,[]),(30,[]),(25,[]),(21,[]),(16,[]),(17,[]),(20,[]),(14,[])]
def wd1Block8_0Pools : BT (Option BoundPool) := buildPoolsBT 5 wd1W wd1R wd1Slices wd1Block8_0Specs
def wd1Block8_0 : List NodeSpec := [([14,13,8,1,3,4,5],[0,1,2,3,4,5],[]),([18,14,13,7,1,3,4,5],[6,7,5,8,2,9,3,10],[]),([21,15,23,0,1,2,4,5],[11,12,13],[]),([29,32,28,22,1,4,6],[14,15,16,17,18],[]),([21,15,28,22,1,2,4],[14,12,16,19,20],[]),([14,29,13,22,1,3,4,5],[11,14,1,8,9],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Block8_0Ok : checkNodesBT wd1W wd1G wd1Mask wd1Block8_0Pools wd1Autos wd1Empty 8 wd1Block8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Block8_0Mem : ∀ ns ∈ wd1Block8_0, Impossible wd1G 8 (nodeValsBT wd1W ns).toFinset := checkNodesBT_mem (by decide) wd1Pairs wd1WOk (buildPoolsBT_sound wd1SlicesOk) wd1AutosOk wd1EmptyOk wd1Block8_0Ok
def wd1Nodes8 : List NodeSpec := wd1Block8_0
def wd1Bucket8 : BT (List (List Nat)) := buildBucketsBT wd1W wd1Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd1G 8 xs.toFinset) wd1Bucket8 := buildBucketsBT_of_mem wd1Block8_0Mem
def wd1Block9_0Specs : List PoolSpec := [(23,[]),(22,[(1,8,5)]),(21,[(1,0,2)]),(22,[(2,8,5)]),(22,[(1,8,6)]),(27,[]),(24,[]),(3,[]),(9,[]),(33,[]),(22,[(2,8,6)]),(22,[]),(12,[]),(2,[]),(25,[]),(22,[(2,16,3)]),(21,[(1,0,2),(1,7,6)]),(2,[(1,0,2),(1,3,5)]),(34,[]),(15,[(1,3,5)]),(18,[(1,3,5)]),(3,[(1,0,2),(1,7,6)]),(1,[(1,2,6),(1,0,6),(1,0,2)]),(15,[]),(3,[(1,2,6),(1,0,6),(1,0,2)]),(4,[(1,2,6),(1,0,6),(1,0,2)]),(11,[(1,0,6)]),(18,[]),(12,[(1,2,6)]),(21,[(1,0,6),(1,0,2)]),(3,[(1,0,6),(1,0,2)]),(10,[]),(7,[(1,0,2)]),(14,[(1,0,2)]),(26,[]),(13,[(1,0,2)]),(5,[(1,3,6),(1,15,5)]),(22,[(1,3,6),(2,15,5)]),(5,[(1,3,6),(2,15,5)]),(22,[(1,5,6),(1,3,6)]),(31,[]),(30,[]),(5,[(1,5,6),(1,3,6)]),(21,[(2,22,2)]),(37,[]),(29,[]),(36,[]),(20,[]),(1,[(1,3,6),(1,0,3),(2,22,2)]),(32,[]),(16,[]),(21,[]),(19,[]),(14,[]),(22,[(2,13,5)]),(1,[(1,2,6),(1,0,6),(1,0,3)]),(28,[]),(35,[])]
def wd1Block9_0Pools : BT (Option BoundPool) := buildPoolsBT 6 wd1W wd1R wd1Slices wd1Block9_0Specs
def wd1Block9_0 : List NodeSpec := [([9,0,1,2,3,4,5,6],[0,1,2],[]),([10,0,1,2,3,4,5,6],[3,0,2],[]),([11,0,1,2,3,4,5,6],[4,5,6,7,8],[]),([12,0,1,2,3,4,5,6],[9,10,7,8],[]),([13,8,1,2,3,4,5,6],[9,11,12,13,0],[0]),([15,8,0,1,2,4,5,6],[6,4,5,14,13],[]),([17,0,1,2,3,4,5,6],[15,5,6,8,7],[]),([18,16,0,1,2,3,4,5,6],[16,1,17,18,12,19,20,21],[]),([14,13,7,1,3,4,5],[11,22,23,24,25,26,27,28],[0,2]),([18,13,7,1,2,3,4,5,6],[1,29,17,12,20,30],[0]),([19,15,7,0,1,2,3,4,5,6],[31,32,33,18,34,35,36],[]),([20,7,0,1,2,3,4,5,6],[37,2,33,12,38],[]),([21,15,7,0,1,2,3,4,5],[2,39,40,33,35,41,42],[4]),([24,0,1,2,3,4,5,6],[43,1,0],[]),([25,0,1,2,3,4,5,6],[4,44,34,45],[]),([13,23,1,2,3,4,5,6],[34,44,45,11,23],[]),([15,23,0,1,2,4,5,6],[46,44,4,47,48],[0]),([21,23,0,1,2,3,4,5,6],[44,46,49],[0]),([27,0,1,2,3,4,5,6],[49,45,44],[]),([28,26,1,2,3,4,5,6],[44,45,7,41],[]),([29,26,0,1,2,3,4,5,6],[44,4,41,50],[]),([31,0,1,2,3,4,5,6],[9,49,47,7,8],[]),([28,30,1,2,3,4,5,6],[44,46,47,41],[]),([32,28,22,1,2,4,5,6],[40,11,51,52],[0]),([15,28,22,1,2,4,5,6],[46,51,41,53,14],[0]),([33,22,1,2,3,4,5,6],[44,41,54],[]),([29,13,22,1,2,3,4,5,6],[44,41,11,27,12],[0]),([14,13,22,1,2,3,4,5],[46,11,55,9,53,23],[0,4]),([35,0,1,2,3,4,5,6],[4,5,27,7,8],[]),([36,13,0,1,2,3,4,5,6],[44,56,45,0],[]),([38,0,1,2,3,4,5,6],[18,49,44],[]),([39,0,1,2,3,4,5,6],[44,57,8,27,18],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Block9_0Ok : checkNodesBT wd1W wd1G wd1Mask wd1Block9_0Pools wd1Autos wd1Bucket8 9 wd1Block9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Block9_0Mem : ∀ ns ∈ wd1Block9_0, Impossible wd1G 9 (nodeValsBT wd1W ns).toFinset := checkNodesBT_mem (by decide) wd1Pairs wd1WOk (buildPoolsBT_sound wd1SlicesOk) wd1AutosOk wd1Bucket8Ok wd1Block9_0Ok
def wd1Nodes9 : List NodeSpec := wd1Block9_0
def wd1Bucket9 : BT (List (List Nat)) := buildBucketsBT wd1W wd1Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd1G 9 xs.toFinset) wd1Bucket9 := buildBucketsBT_of_mem wd1Block9_0Mem
def wd1Block10_0Specs : List PoolSpec := [(22,[]),(31,[]),(1,[(1,0,2),(1,7,3)]),(3,[]),(2,[]),(17,[]),(20,[]),(4,[(1,0,2)]),(1,[(1,0,2),(1,7,6)]),(34,[]),(3,[(1,0,2),(1,7,6)]),(4,[(1,0,2),(1,7,6)]),(12,[]),(2,[(1,0,2)]),(15,[]),(18,[]),(1,[(1,0,6),(1,0,2)]),(3,[(1,0,6),(1,0,2)]),(4,[(1,0,6),(1,0,2)]),(21,[(1,0,2)]),(22,[(1,8,5)]),(23,[]),(5,[(1,3,5)]),(22,[(1,8,6)]),(1,[(1,0,2),(1,3,6)]),(7,[(1,0,2)]),(14,[]),(10,[]),(14,[(1,0,2)]),(30,[]),(5,[(1,3,6)]),(24,[]),(27,[]),(25,[]),(1,[(1,0,3),(2,22,2)]),(21,[(2,22,2)]),(26,[]),(36,[]),(1,[(1,0,3),(1,22,6)]),(0,[(1,0,3),(1,22,6)]),(5,[]),(6,[(1,22,6)]),(4,[(1,22,6)]),(29,[]),(28,[]),(1,[(1,0,3),(2,22,6)]),(0,[(1,0,3),(2,22,6)]),(38,[]),(21,[]),(0,[(1,0,5),(1,0,3)]),(8,[]),(19,[]),(0,[(1,0,6),(1,0,3)]),(1,[(1,0,3),(1,0,6)]),(2,[(1,0,3)]),(16,[]),(1,[(1,0,3),(1,2,6)]),(1,[(1,0,6),(1,2,13)]),(3,[(1,0,6),(1,2,13)]),(4,[(1,0,6),(1,2,13)]),(1,[(1,0,6),(2,13,2)]),(3,[(1,0,6),(2,13,2)]),(4,[(1,0,6),(2,13,2)]),(1,[(1,0,6),(1,3,13)]),(1,[(1,0,6),(2,13,3)]),(0,[(1,0,6),(2,13,3)]),(35,[]),(1,[(1,2,6),(1,0,6)]),(3,[(1,2,6),(1,0,6)]),(4,[(1,2,6),(1,0,6)])]
def wd1Block10_0Pools : BT (Option BoundPool) := buildPoolsBT 7 wd1W wd1R wd1Slices wd1Block10_0Specs
def wd1Block10_0 : List NodeSpec := [([8,0,1,2,3,4,5,6],[0,1,2,3,4,5,6,7],[0,1]),([16,0,1,2,3,4,5,6],[0,8,9,10,11,12,13,14,15],[0,2]),([13,7,1,2,3,4,5,6],[0,16,15,13,12,17,18],[0,2]),([18,7,0,1,2,3,4,5,6],[19,20,14,21,22,7],[0,4,1,5]),([15,7,0,1,2,3,4,5,6],[23,24,13,25,26,27,28,29,30,7],[0,4]),([8,22,0,1,2,3,4,5,6],[31,0,32,33,5,6],[]),([23,0,1,2,3,4,5,6],[6,0,34,35,4,36],[0]),([26,0,1,2,3,4,5,6],[37,38,39,1,6,26,40,15,3,41,42],[0,4]),([26,22,0,1,2,3,4,5,6],[32,43,44,6,33,26,15,42],[]),([30,0,1,2,3,4,5,6],[6,45,46,1,47,40,3,42,37],[0,4]),([28,22,1,2,3,4,5,6],[48,37,49,50,51,6],[0,2]),([13,22,1,2,3,4,5,6],[1,52,6,53,15,54,37,42],[0,4,2]),([29,22,0,1,2,3,4,5,6],[47,48,0,55,6,26,14],[0,3,1,2,4,5]),([14,22,0,1,2,3,4,5,6],[37,0,56,6,31,26,14,51,55],[0,3,7,1,4]),([16,13,0,1,2,3,4,5,6],[9,0,12,57,58,14,15,59],[4]),([34,0,1,2,3,4,5,6],[0,15,60,61,62],[0,2,4]),([26,13,0,1,2,3,4,5,6],[43,15,44,63,26,31,51,6,54],[0]),([37,0,1,2,3,4,5,6],[15,64,65,33,26,40,54,3,66,9],[0,2]),([14,13,0,1,2,3,4,5],[0,67,66,14,43,15,68,69],[0,1,2,3,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Block10_0Ok : checkNodesBT wd1W wd1G wd1Mask wd1Block10_0Pools wd1Autos wd1Bucket9 10 wd1Block10_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Block10_0Mem : ∀ ns ∈ wd1Block10_0, Impossible wd1G 10 (nodeValsBT wd1W ns).toFinset := checkNodesBT_mem (by decide) wd1Pairs wd1WOk (buildPoolsBT_sound wd1SlicesOk) wd1AutosOk wd1Bucket9Ok wd1Block10_0Ok
def wd1Nodes10 : List NodeSpec := wd1Block10_0
def wd1Bucket10 : BT (List (List Nat)) := buildBucketsBT wd1W wd1Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd1G 10 xs.toFinset) wd1Bucket10 := buildBucketsBT_of_mem wd1Block10_0Mem
def wd1Block11_0Specs : List PoolSpec := [(22,[]),(1,[(1,0,2)]),(4,[(1,0,2)]),(3,[(1,0,2)]),(2,[(1,0,2)]),(5,[]),(4,[]),(1,[(1,0,3)]),(0,[(1,0,3)]),(8,[]),(3,[(1,0,3)]),(2,[(1,0,3)]),(6,[]),(20,[]),(0,[(1,0,6)]),(1,[(1,0,6)]),(2,[]),(4,[(1,22,6)]),(3,[(1,0,6)]),(18,[])]
def wd1Block11_0Pools : BT (Option BoundPool) := buildPoolsBT 5 wd1W wd1R wd1Slices wd1Block11_0Specs
def wd1Block11_0 : List NodeSpec := [([7,0,1,2,3,4,5,6],[0,1,2,3,4,5],[0,3]),([22,0,1,2,3,4,5,6],[6,7,8,9,10,11,12,13],[0,4]),([13,0,1,2,3,4,5,6],[12,14,15,16,9,17,18,19],[0,2,1,3,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Block11_0Ok : checkNodesBT wd1W wd1G wd1Mask wd1Block11_0Pools wd1Autos wd1Bucket10 11 wd1Block11_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Block11_0Mem : ∀ ns ∈ wd1Block11_0, Impossible wd1G 11 (nodeValsBT wd1W ns).toFinset := checkNodesBT_mem (by decide) wd1Pairs wd1WOk (buildPoolsBT_sound wd1SlicesOk) wd1AutosOk wd1Bucket10Ok wd1Block11_0Ok
def wd1Nodes11 : List NodeSpec := wd1Block11_0
def wd1Bucket11 : BT (List (List Nat)) := buildBucketsBT wd1W wd1Nodes11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Bucket11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd1G 11 xs.toFinset) wd1Bucket11 := buildBucketsBT_of_mem wd1Block11_0Mem
def wd1Block12_0Specs : List PoolSpec := [(1,[]),(0,[]),(5,[]),(6,[]),(4,[]),(3,[]),(2,[])]
def wd1Block12_0Pools : BT (Option BoundPool) := buildPoolsBT 3 wd1W wd1R wd1Slices wd1Block12_0Specs
def wd1Block12_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,3,4,5,6],[0,5,1,2,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Block12_0Ok : checkNodesBT wd1W wd1G wd1Mask wd1Block12_0Pools wd1Autos wd1Bucket11 12 wd1Block12_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Block12_0Mem : ∀ ns ∈ wd1Block12_0, Impossible wd1G 12 (nodeValsBT wd1W ns).toFinset := checkNodesBT_mem (by decide) wd1Pairs wd1WOk (buildPoolsBT_sound wd1SlicesOk) wd1AutosOk wd1Bucket11Ok wd1Block12_0Ok
def wd1Nodes12 : List NodeSpec := wd1Block12_0
def wd1Bucket12 : BT (List (List Nat)) := buildBucketsBT wd1W wd1Nodes12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Bucket12Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible wd1G 12 xs.toFinset) wd1Bucket12 := buildBucketsBT_of_mem wd1Block12_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma wd1Bound : Lower wd1R wd1G 13 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,2,34),(VAR 6,1,65)]) (by decide +kernel) wd1Bucket12Ok (by decide +kernel)
lemma wg79 : Lower (varsOf 127) 0xfffffffffffffffefffeffecfefeeca0 13 := wd1Bound
lemma rootNBound : Lower (varsOf 127) 0xfffffffffffffffefffeffecfefeeca0 13 := wg79
end Small
namespace Relate
def insertRow (r : Small.Row) : Wide.Row :=
  ⟨(0 + ((r.val / 1) % 2) * 1 + ((r.val / 2) % 2) * 2 + ((r.val / 4) % 2) * 8 + ((r.val / 8) % 2) * 16 + ((r.val / 16) % 2) * 32 + ((r.val / 32) % 2) * 64 + ((r.val / 64) % 2) * 128) % 256, Nat.mod_lt _ (by decide)⟩
def project (w : Wide.Wire) : Small.Wire := fun r => w (insertRow r)
lemma avail {b : List Wide.Wire} {v : Wide.Wire} (h : Wide.Avail b v) :
    Small.Avail (b.map project) (project v) := by
  rcases h with h | ⟨k, rfl⟩ | h
  · exact Or.inl (List.mem_map_of_mem h)
  · exact Or.inr (Or.inl ⟨k,rfl⟩)
  · exact Or.inr (Or.inr (List.mem_map_of_mem (f := project) h))
lemma reach {roots b : List Wide.Wire} {n : Nat} (h : Wide.Reach roots n b) :
    Small.Reach (roots.map project) n (b.map project) := by
  induction n generalizing b with
  | zero => change b = roots at h; rw [h]; rfl
  | succ n ih =>
    obtain ⟨op,bank,a,b,hr,ha,hb,rfl⟩ := h
    refine ⟨op, bank.map project, project a, project b, ih hr, avail ha, avail hb, ?_⟩
    cases op <;> rfl
lemma liftPins : Wide.Lower (Wide.varsOf 255) 0xffffffffffffffffffffffffffffffeefffffffefffffefcfffeffeefefcaa00 14 := by
  have bound : Wide.Lower (Wide.varsOf 251) 0xffffffffffffffffffffffffffffffeeffffffeeffffeeccffeeffeeeeccaa00 13 := by
    intro n bank hr ha
    have proots : (((Wide.varsOf 251).map Wide.obs).map project) = (Small.varsOf 127).map Small.obs := by
      change [_,_,_,_,_,_,_] = [_,_,_,_,_,_,_]
      repeat' apply congrArg₂ List.cons
      all_goals first | rfl | funext r; revert r; decide +kernel
    have target : project (Wide.obs 0xffffffffffffffffffffffffffffffeeffffffeeffffeeccffeeffeeeeccaa00) = Small.obs 0xfffffffffffffffefffeffecfefeeca0 := by funext r; revert r; decide +kernel
    have r := reach hr
    have a := avail ha
    rw [proots] at r
    rw [target] at a
    exact Small.rootNBound n _ r a
  exact Wide.lift_of (z := 4) (o := 0) (essPairs := [(Wide.VAR 2,16,20)]) (by decide +kernel) bound
end Relate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
def onWit : List Gate := [⟨.or, [0, 1]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [4, 6]⟩, ⟨.and, [10, 12]⟩, ⟨.and, [11, 15]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [21, 19]⟩]

theorem onWitBasis : ∀ g ∈ onWit,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [onWit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onWitCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨onWit, 22⟩ (List.ofFn x) = f x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onGraphCorrect : ∀ x : Fin 8 → Bool, f x = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

theorem onFinal :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfit _hone hev
  have hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y := fun y => (hev y).trans (onGraphCorrect y).symm
  have hrow : ∀ r : Wide.Row, f (Wide.evalInput r) = (0xffffffffffffffffffffffffffffffeefffffffefffffefcfffeffeefefcaa00 : Nat).testBit r.val := by decide +kernel
  have hw : ∀ r : Wide.Row, Circuit.eval ⟨onWit, 22⟩ (List.ofFn (Wide.evalInput r)) = (0xffffffffffffffffffffffffffffffeefffffffefffffefcfffeffeefefcaa00 : Nat).testBit r.val :=
    fun r => (onWitCorrect (Wide.evalInput r)).trans (hrow r)
  obtain ⟨gs, out, hg, hlen, hev⟩ := Wide.replace_of_lower (0xffffffffffffffffffffffffffffffeefffffffefffffefcfffeffeefefcaa00 : Nat) (by decide) (by decide) (by decide)
    14 Relate.liftPins onWit 22 (by decide) onWitBasis f hrow hw gates o hfit hf
  exact ⟨gs, out, hg, hlen, fun x => (hev x).trans (onGraphCorrect x)⟩
end PEqualNP.Outside.L_meta_55987

theorem PEqualNP.Outside.L_meta_55987 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_55987.onFinal
