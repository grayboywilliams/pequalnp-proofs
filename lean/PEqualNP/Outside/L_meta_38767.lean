import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38767

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808426 * 2 ^ 32 + 4236822664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x800424484b885855#64 ++ 0x2001091212e21615#64 ++ 0x640c7cf8fb88f8ff#64 ++ 0xd9031f3e3ee23e3f#64 : BitVec 256),
   (0x003191232403a3aa#64 ++ 0x400c6448c900e8ea#64 ++ 0xfc739327240fffff#64 ++ 0xbf1ce4c9c903ffff#64 : BitVec 256),
   (0x0582e2c5c5b0cd33#64 ++ 0x8160b8b1716c334c#64 ++ 0xef83e3c7c7f0cf33#64 ++ 0x7be0f8f1f1fc33cc#64 : BitVec 256),
   (0x0adc03f802dd0ec0#64 ++ 0x02b700fe00b743b0#64 ++ 0xfbfc03f807ff0fc2#64 ++ 0xfeff00fe01ffc3f0#64 : BitVec 256),
   (0x136ffc00076ef000#64 ++ 0x04dbff0001dbbc00#64 ++ 0xf3fffc0007fff001#64 ++ 0xfcffff0001fffc00#64 : BitVec 256),
   (0x03fb5bb6b0000000#64 ++ 0x00fed6edac000000#64 ++ 0xdffffffff8000003#64 ++ 0xf7fffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 7]⟩, ⟨.and, [11, 3]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00000001000103aa 0x40000000400040ea 0x0000000000000ffc 0x00000000000003ff

def z1 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xfc739327240fffff 0xbf1ce4c9c903ffff

def z2 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xdffffffff8000003 0xf7fffffffe000000

def z3 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef83e3c7c7f0cf33 0x7be0f8f1f1fc33cc

def z4 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfbfc03f807ff0fc2 0xfeff00fe01ffc3f0

def z5 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf3fffc0007fff001 0xfcffff0001fffc00

def z6 : W := mkw 0x800424484b885855 0x2001091212e21615 0x640c7cf8fb88f8ff 0xd9031f3e3ee23e3f

def z7 : W := mkw 0x0031112220032288 0x400c44488800c8a2 0x1070000000070000 0x041c00000001c000

def z8 : W := mkw 0x13ffffb6b76ef000 0x04ffffedaddbbc00 0xfffffffffffff003 0xfffffffffffffc00

def z9 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0x9bf3830700000000 0x26fce0c1c0000000

def z10 : W := mkw 0x800424484b885855 0x2001091212e21615 0x200000000388f8fc 0x0800000000e23e3f

def z11 : W := mkw 0x1804a44807fffec0 0x0601291201ffffb0 0x2000000007ffffc0 0x0800000001fffff0

def z12 : W := mkw 0x1123d8000422a000 0x0448f6000108a800 0x0003800000000000 0x0000e00000000000

def z13 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0x9ff3ff07f8000001 0x27fcffc1fe000000

def z14 : W := mkw 0x0000000000032288 0x400000000000c8a2 0x00000000000f30cc 0x000000000003cc33

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0xe800030004000f02 0x3a0000c0010003c0

def z16 : W := mkw 0x025c0120024d0280 0x00970048009340a0 0xfbfc032007ff0fc2 0xfeff00c801ffc3f0

def z17 : W := mkw 0x07ca6ad4d1b04c11 0x81f29ab5346c1304 0x038c6cd8dbf00000 0x40e31b3636fc0000

def z18 : W := mkw 0x009003b6b0000000 0x002400edac000000 0x0c0003fff8000002 0x030000fffe000000

def z19 : W := mkw 0x036b580000000000 0x00dad60000000000 0xd3fffc0000000001 0xf4ffff0000000000

def z20 : W := mkw 0x024c0000024c0000 0x0093000000930000 0xf3fc000007ff0000 0xfcff000001ffc000

def z21 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0x080003f800000fc2 0x020000fe000003f0

def z22 : W := mkw 0x05b3f3e7e5b3efbb 0xc16cfcf9f96cfbee 0xfff3f3e7e7ffffff 0xfffcfcf9f9ffffff

def z23 : W := mkw 0x8586e6cdcfb8dd77 0xa161b9b373ee375d 0xef8ffffffff8ffff 0xfbe3fffffffe3fff

def z24 : W := mkw 0x01235806b0000000 0x0048d601ac000000 0x0403fc07f8000001 0x0100ff01fe000000

def z25 : W := mkw 0x17ce6ec4c3fc5c11 0x85f39bb130ff1704 0x038c6cc0c3f00000 0x40e31b3030fc0000

def z26 : W := mkw 0x134eec00076cd000 0x04d3bb0001db3400 0xe38fec0007f0c001 0x78e3fb0001fc3000

def z27 : W := mkw 0x00100123200103aa 0x40040048c80040ea 0x0c00032720000ffe 0x030000c9c80003ff

def z28 : W := mkw 0x0102e0000520c000 0x0040b80001483000 0xe383e00007f0c001 0x78e0f80001fc3000

def z29 : W := mkw 0x0010012220000000 0x0004004888000000 0x0c00032720000002 0x030000c9c8000000

def z30 : W := mkw 0x87ffffffffb8dd77 0xa1ffffffffee375d 0xfffffffffff8ffff 0xfffffffffffe3fff

def z31 : W := mkw 0x07fbfbf7f5b0cd33 0x81fefefdfd6c334c 0xfffffffffff0cf33 0xfffffffffffc33cc

def z32 : W := mkw 0x009003b000000000 0x002400ec00000000 0x080003f800000002 0x020000fe00000000

def z33 : W := mkw 0x05a3f2c5c5b2ed33 0x8168fcb1716cbb4c 0xfff3f3c7c7ffff33 0xfffcfcf1f1ffffcc

def z34 : W := mkw 0x048082c5c4908d33 0x812020b17124234c 0xec0383c7c400cf33 0x3b00e0f1f10033cc

def z35 : W := mkw 0x0431b16365b3efbb 0xc10c6c58d96cfbee 0xfc73932727ffffff 0xbf1ce4c9c9ffffff

def z36 : W := mkw 0x00311123200103aa 0x400c4448c80040ea 0xdc73932720000fff 0xb71ce4c9c80003ff

def z37 : W := mkw 0x8a5c25784bcd5ad5 0x2297095e12f356b5 0x747c7cf8fb8ff8ff 0xdd1f1f3e3ee3fe3f

def z38 : W := mkw 0x0000204041804811 0x0000081010601204 0x640060c0c380c833 0x5900183030e0320c

def z39 : W := mkw 0x0d92e3fdc5b1cff3 0x8364b8ff716c73fc 0xef83e3ffc7f0cff3 0x7be0f8fff1fc33fc

def z40 : W := mkw 0x0010012220010288 0x40040048880040a2 0x00000020200000cc 0x0000000808000033

def z41 : W := mkw 0x03fb5bb6b0010280 0x00fed6edac0040a0 0xfffffffffc0f0fc3 0xffffffffff03c3f0

def z42 : W := mkw 0x0031112220032288 0x400c44488800c8a2 0xdc739327200f30cf 0xb71ce4c9c803cc33

def z43 : W := mkw 0x0031112220032288 0x400c44488800c8a2 0x74701020200ff8ff 0x9d1c04080803fe3f

def z44 : W := mkw 0x0a4c0018024c0040 0x0293000600930010 0x000c001800000000 0x0003000600000000

def z45 : W := mkw 0x0010012000010280 0x00040048000040a0 0xf8700320040f0fc2 0xbe1c00c80103c3f0

def z46 : W := mkw 0x1123fc000522f000 0x0448ff000148bc00 0x0003fc000000f001 0x0000ff0000003c00

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0x640010202008f8ff 0x9900040808023e3f

def z48 : W := mkw 0x8035b56b6f8bfbff 0x600d6d5adbe2feff 0xfc7fffffff8fffff 0xff1fffffffe3ffff

def z49 : W := mkw 0x800404080a081044 0x2001010202820411 0x000c1c38380830cc 0x8003070e0e020c33

def z50 : W := mkw 0x936ffc484feef855 0x24dbff1213fbbe15 0xf7fffcf8fffff8ff 0xfdffff3e3ffffe3f

def z51 : W := mkw 0x0bff5bfeb2dd0ec0 0x02ffd6ffacb743b0 0xffffffffffff0fc3 0xffffffffffffc3f0

def z52 : W := mkw 0x0edc03fdc2dd0ff3 0x83b700ff70b743fc 0xfffc03ffc7ff0ff2 0xffff00fff1ffc3fc

def z53 : W := mkw 0x0004040002081000 0x0001010000820400 0x000c1c0000083000 0x8003070000020c00

def z54 : W := mkw 0x936ffc080f6ef044 0x24dbff0203dbbc11 0xf3fffc383ffff0cd 0xfcffff0e0ffffc33

def z55 : W := mkw 0x1bfffff807fffec0 0x06fffffe01ffffb0 0xfbfffff807ffffc3 0xfefffffe01fffff0

def z56 : W := mkw 0x0000000000000000 0x0000000000000000 0x4400102020000003 0x9100040808000000

def z57 : W := mkw 0x800424484b885855 0x2001091212e21615 0x040c6cf8fb8008fe 0x41031b3e3ee0023f

def z58 : W := mkw 0x13ff7fb6b36c5000 0x04ffdfedacdb1400 0xdffffffffbf00003 0xf7fffffffefc0000

def z59 : W := mkw 0x0000000000000000 0x0000000000000000 0x440c7cf8f8000003 0xd1031f3e3e000000

def z60 : W := mkw 0x0182428480000000 0x006090a120000000 0xcf83e3c7c0000003 0x73e0f8f1f0000000

def z61 : W := mkw 0x0582c28584308522 0x8160b0a1610c2148 0x8b83830704700700 0x22e0e0c1c11c01c0

def z62 : W := mkw 0x8000240049005015 0x2000090012401405 0x04007c00f800f03d 0x01001f003e003c0f

def z63 : W := mkw 0x8adc27f84bdd5ed5 0x22b709fe12f757b5 0xfffc7ff8ffffffff 0xffff1ffe3fffffff

def z64 : W := mkw 0x1bde6ff803fd5ec0 0x06f79bfe00ff57b0 0xfbfc6ff807ff0fc2 0xfeff1bfe01ffc3f0

def z65 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xb8738307040ffffc 0x2e1ce0c1c103ffff

def z66 : W := mkw 0x176ffc05c76ef133 0x85dbff0171dbbc4c 0xf7fffc07c7fff031 0xfdffff01f1fffc0c

def z67 : W := mkw 0x0afd93fb26dfafea 0x42bf64fec9b7ebfa 0xffff93ff27ffffff 0xffffe4ffc9ffffff

def z68 : W := mkw 0x8404a4494fb8dd77 0xa101291253ee375d 0x640c7cf8fff8ffff 0xd9031f3e3ffe3fff

def z69 : W := mkw 0x0a7d193a324d02c0 0x029f464e8c9340b0 0x107c1c38380f00c0 0x841f070e0e03c030

def z70 : W := mkw 0x008002c000900c00 0x002000b000240300 0xeb8003c007f00f02 0x7ae000f001fc03c0

def z71 : W := mkw 0x0fdee3fdc7fdcff3 0x83f7b8ff71ff73fc 0xffffe3ffc7ffcff3 0xfffff8fff1fff3fc

def z72 : W := mkw 0x0c9003fdc0910ff3 0x832400ff702443fc 0x0c0003ffc0000ff2 0x030000fff00003fc

def z73 : W := mkw 0x05b3d3a7a433a7aa 0xc16cf4e9e90ce9ea 0xfff39327247fffff 0xbffce4c9c91fffff

def z74 : W := mkw 0x0000800104008122 0x0000200041002048 0xec0383070400cf33 0x3b00e0c1c10033cc

def z75 : W := mkw 0x127d1d22224f3288 0x449f47488893cca2 0x107c1c20200f30cc 0x841f07080803cc33

def z76 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef83f3e7e7f8ffff 0xfbe0fcf9f9fe3fff

def z77 : W := mkw 0x1025b400076ef000 0x04096d0001dbbc00 0xf073900007fff001 0xbc1ce40001fffc00

def z78 : W := mkw 0x002190000402a000 0x000864000100a800 0xf0739000040ff001 0xbc1ce4000103fc00

def z79 : W := mkw 0x01b3d3a7a403a3aa 0x406cf4e9e900e8ea 0xfff3f3e7e40fffff 0xfffcfcf9f903ffff

def z80 : W := mkw 0x08040008024d02c0 0x02010002009340b0 0x00000000000f00c0 0x000000000003c030

def z81 : W := mkw 0x0ad803b000550680 0x02b600ec001541a0 0x9bf0030004770700 0x26fc00c0011dc1c0

def z82 : W := mkw 0x0800004800910ec0 0x02000012002443b0 0x0000000000000fc0 0x00000000000003f0

def z83 : W := mkw 0x089403f802dd0ec0 0x022500fe00b743b0 0x280003f807ff0fc2 0x0a0000fe01ffc3f0

def z84 : W := mkw 0x9bfffff84ffffed5 0x26fffffe13ffffb5 0xfffffff8ffffffff 0xfffffffe3fffffff

def z85 : W := mkw 0x0582e2858530c522 0x8160b8a1614c3148 0xeb83e30707f0c701 0x7ae0f8c1c1fc31c0

def z86 : W := mkw 0x8000004848800855 0x2000001212200215 0x040000f8f80008fe 0x0100003e3e00023f

def z87 : W := mkw 0x009003e000910e80 0x002400f8002443a0 0xfbf003e007ff0fc2 0xfefc00f801ffc3f0

def z88 : W := mkw 0x036bf8000520c000 0x00dafe0001483000 0xf3fffc0007f0c001 0xfcffff0001fc3000

def z89 : W := mkw 0x0fdec3fd86fd8fe2 0x83f7b0ff61bf63f8 0xfbff83ff07ff0fc2 0xfeffe0ffc1ffc3f0

def z90 : W := mkw 0x0586e6c5c7b8dd33 0x8161b9b171ee374c 0xef8fffc7c7f8ff33 0xfbe3fff1f1fe3fcc

def z91 : W := mkw 0x0004240003085000 0x0001090000c21400 0x600c7c000388f001 0xd8031f0000e23c00

def z92 : W := mkw 0x8bff7ffefbdd5ed5 0x22ffdfffbef757b5 0xffffffffffffffff 0xffffffffffffffff

def z93 : W := mkw 0x8035b56b6f8bfbff 0x600d6d5adbe2feff 0xfc739327278fffff 0xbf1ce4c9c9e3ffff

def z94 : W := mkw 0x03ca4a9490000000 0x00f292a524000000 0xcf8fefdfd8000003 0x73e3fbf7f6000000

def z95 : W := mkw 0x137ffd23276ff3aa 0x44dfff48c9dbfcea 0xffffff2727ffffff 0xffffffc9c9ffffff

def z96 : W := mkw 0x134e6c00036c5000 0x04d39b0000db1400 0x038c6c0003f00000 0x40e31b0000fc0000

def z97 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0x9873830704070700 0x261ce0c1c101c1c0

def z98 : W := mkw 0x0bde43fc82dd0ec0 0x02f790ff20b743b0 0xffffe3ffc7ff0fc3 0xfffff8fff1ffc3f0

def z99 : W := mkw 0x02cc02c002dc0c00 0x00b300b000b70300 0xfbfc03c007ff0f02 0xfeff00f001ffc3c0

def z100 : W := mkw 0x03ca4a9490000000 0x00f292a524000000 0x038c6cd8d8000000 0x40e31b3636000000

def z101 : W := mkw 0x0400a04145b0cd33 0x81002810516c334c 0x2000000007f0cf30 0x0800000001fc33cc

def z102 : W := mkw 0x0000a0000520c000 0x0000280001483000 0x2000000007f0c000 0x0800000001fc3000

def z103 : W := mkw 0x136bd8000466a000 0x04daf6000119a800 0x93f3800004770000 0x24fce000011dc000

def z104 : W := mkw 0x0fde63fcc3fd4ed1 0x83f798ff30ff53b4 0xfbfc63f8c7ff0fc2 0xfeff18fe31ffc3f0

def z105 : W := mkw 0x0014016802890ac0 0x0005005a00a242b0 0xf87c03f8078f0fc2 0xfe1f00fe01e3c3f0

def z106 : W := mkw 0x02d803b000000000 0x00b600ec00000000 0x9bf0030000000000 0x26fc00c000000000

def z107 : W := mkw 0x124ca400076ef000 0x0493290001dbbc00 0xf3fc000007fff000 0xfcff000001fffc00

def z108 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xdff3932720000003 0xb7fce4c9c8000000

def z109 : W := mkw 0x01235806b0000000 0x0048d601ac000000 0x440ffcfff8000003 0xd103ff3ffe000000

def z110 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0x93ffec0007f70000 0x64fffb0001fdc000

def z111 : W := mkw 0x800404480a881844 0x2001011202a20611 0x600c1cf83b8838ce 0xd803073e0ee20e33

def z112 : W := mkw 0x002190032402a12a 0x40086400c900a84a 0xec0393072400ff3f 0x3b00e4c1c9003fcf

def z113 : W := mkw 0x01a35a86b0000000 0x0068d6a1ac000000 0xcf83ffc7f8000003 0x73e0fff1fe000000

def z114 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z115 : W := mkw 0x0a7d113a224f22c8 0x429f444e8893c8b2 0x107c1038200f30cc 0x841f040e0803cc33

def z116 : W := mkw 0x1127fc00076ef000 0x0449ff0001dbbc00 0x2003fc0007fff001 0x0800ff0001fffc00

def z117 : W := mkw 0x880424484bdd5ed5 0x2201091212f757b5 0x640c7cf8ffffffff 0xd9031f3e3fffffff

def z118 : W := mkw 0x0800000000550680 0x02000000001541a0 0x0000000004770700 0x00000000011dc1c0

def z119 : W := mkw 0x03fbfbb6b520c000 0x00fefeedad483000 0xfffffffffff0c003 0xfffffffffffc3000

def z120 : W := mkw 0x026d9000064ea000 0x009b64000193a800 0xf3ff900007fff001 0xfcffe40001fffc00

def z121 : W := mkw 0x800424484b885855 0x2001091212e21615 0x600c6cf8db8808c2 0xd8031b3e36e20230

def z122 : W := mkw 0x03fbdbb6b402a000 0x00fef6edad00a800 0xfffffffffc0ff003 0xffffffffff03fc00

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0700000040f0000 0xbc1c00000103c000

def z124 : W := mkw 0x137ffd32376ef000 0x04dfff4c8ddbbc00 0xf3fffc383ffff001 0xfcffff0e0ffffc00

def z125 : W := mkw 0x8586e6cdcfb8dd77 0xa161b9b373ee375d 0xef83e3c7c7f8ffff 0x7be0f8f1f1fe3fff

def z126 : W := mkw 0x034ee000076cc000 0x00d3b80001db3000 0xf3ffe00007ffc001 0xfcfff80001fff000

def z127 : W := mkw 0x00b193b7b403a3aa 0x402c64eded00e8ea 0xfc7393fffc0fffff 0xbf1ce4ffff03ffff

def z128 : W := mkw 0x1bffffb0077ff680 0x06ffffec01dffda0 0xfbffff0007fff701 0xfeffffc001fffdc0

def z129 : W := mkw 0x03fbdbb7b403a3aa 0x40fef6eded00e8ea 0xfffffffffc0fffff 0xffffffffff03ffff

def z130 : W := mkw 0x10042400036c5000 0x0401090000db1400 0x0000000003f00000 0x0000000000fc0000

def z131 : W := mkw 0x0d86e2cdc7fdcff3 0x8361b8b371ff73fc 0xef83e3c7c7ffcff3 0x7be0f8f1f1fff3fc

def z132 : W := mkw 0x0adc03feb2dd0ec0 0x02b700ffacb743b0 0xfffc03ffffff0fc2 0xffff00ffffffc3f0

def z133 : W := mkw 0x0004004802880840 0x0001001200a20210 0x600c00f8038808c2 0xd803003e00e20230

def z134 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0x9bff9f3f38000000 0xa6ffe7cfce000000

def z135 : W := mkw 0x0bfb5bb6b0550680 0x02fed6edac1541a0 0xdffffffffc770703 0xf7ffffffff1dc1c0

def z136 : W := mkw 0x8035356a6b885855 0x200d4d5a9ae21615 0xfc7ffffffb88f8ff 0xff1ffffffee23e3f

def z137 : W := mkw 0x0123f0000522e000 0x0048fc000148b800 0xf3f3f00007fff001 0xfcfcfc0001fffc00

def z138 : W := mkw 0x818666cccb885855 0x206199b332e21615 0xef8ffffffb88f8ff 0xfbe3fffffee23e3f

def z139 : W := mkw 0x136bfc000522f000 0x04daff000148bc00 0xd3fffc000000f001 0xf4ffff0000003c00

def z140 : W := mkw 0x0000200001004000 0x0000080000401000 0x600060000380c001 0x5800180000e03000

def z141 : W := mkw 0x0102e04045a0c811 0x0040b81011683204 0xe783e0c0c7f0c833 0x79e0f83031fc320c

def z142 : W := mkw 0x001081210403a3aa 0x400420484100e8ea 0xf8700320040ffffe 0xbe1c00c80103ffff

def z143 : W := mkw 0x8404a4494fb8dd77 0xa101291253ee375d 0x2000000007f8fffc 0x0800000001fe3fff

def z144 : W := mkw 0x0adc03f802dc0c40 0x02b700fe00b70310 0xdbfc03f803f00002 0xf6ff00fe00fc0000

def z145 : W := mkw 0x800424484b885855 0x2001091212e21615 0x040c7cd8fb80f03d 0x41031f363ee03c0f

def z146 : W := mkw 0x024c0000024c0000 0x0093000000930000 0x038c000003f00000 0x40e3000000fc0000

def z147 : W := mkw 0x000080010403a3aa 0x400020004100e8ea 0x20000000040ffffc 0x080000000103ffff

def z148 : W := mkw 0x0000800104008122 0x0000200041002048 0x8803830704000700 0x2200e0c1c10001c0

def z149 : W := mkw 0x0021100220022008 0x4008440088008802 0x000010002000300c 0x0000040008000c03

def z150 : W := mkw 0x037b592220000000 0x00ded64888000000 0xdfffff2720000003 0xf7ffffc9c8000000

def z151 : W := mkw 0x83ce6edcdb885855 0x20f39bb736e21615 0x038c6cd8db800000 0x40e31b3636e00000

def z152 : W := mkw 0x136fd800066ea000 0x04dbf600019ba800 0xf3ff800007ff0000 0xfcffe00001ffc000

def z153 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0x9ff383fff8000002 0x27fce0fffe000000

def z154 : W := mkw 0x0000800104008122 0x0000200041002048 0x040380070000c031 0x0100e001c000300c

def z155 : W := mkw 0x136ffc01076ef122 0x04dbff0041dbbc48 0xffffff0707ffff33 0xffffffc1c1ffffcc

def z156 : W := mkw 0x8000004848800855 0x2000001212200215 0x640010f8f808f8ff 0x9900043e3e023e3f

def z157 : W := mkw 0x02dc03b0024c0000 0x00b700ec00930000 0xfbfc03f807ff0002 0xfeff00fe01ffc000

def z158 : W := mkw 0x1adca7f807fffec0 0x06b729fe01ffffb0 0xfbfc03f807ffffc2 0xfeff00fe01fffff0

def z159 : W := mkw 0x8502e405cd20d137 0xa140b9017348344d 0x0403fc07f800f03d 0x0100ff01fe003c0f

def z160 : W := mkw 0x0248000000440000 0x0092000000110000 0x93f0000004770000 0x24fc0000011dc000

def z161 : W := mkw 0x800424484b885855 0x2001091212e21615 0x200c6cd8db88f8fc 0x48031b3636e23e3f

def z162 : W := mkw 0x126d1c00024e3000 0x049b470000938c00 0x107c1c00000f3000 0x841f07000003cc00

def z163 : W := mkw 0x800424484b885855 0x2001091212e21615 0x000c6cd8db800000 0x40031b3636e00000

def z164 : W := mkw 0x1106e400076ef000 0x0441b90001dbbc00 0xe383e00007fff001 0x78e0f80001fffc00

def z165 : W := mkw 0x0480028580100522 0x812000a160040148 0x0800030700000700 0x020000c1c00001c0

def z166 : W := mkw 0x01b35bb6b0000000 0x006cd6edac000000 0x0c03fffff8000003 0x0300fffffe000000

def z167 : W := mkw 0x83fb7fb6f9005015 0x20fedfedbe401405 0xdffffffff800f03f 0xf7fffffffe003c0f

def z168 : W := mkw 0x83ff7ffefb885855 0x20ffdfffbee21615 0xfffffffffb88f8ff 0xfffffffffee23e3f

def z169 : W := mkw 0x0182428480000000 0x006090a120000000 0x038060c0c0000000 0x40e0183030000000

def z170 : W := mkw 0x0502e005c520c133 0x8140b8017148304c 0x0403e007c000c031 0x0100f801f000300c

def z171 : W := mkw 0x0a5c0138024d02c0 0x0297004e009340b0 0x107c0038000f00c0 0x841f000e0003c030

def z172 : W := mkw 0x0000800004008000 0x0000200001002000 0xe00380000400c001 0x3800e00001003000

def z173 : W := mkw 0x134e6c00036c5000 0x04d39b0000db1400 0xf3fc6c0007ff0000 0xfcff1b0001ffc000

def z174 : W := mkw 0x002190032402a12a 0x40086400c900a84a 0x040390072000f03d 0x0100e401c8003c0f

def z175 : W := mkw 0x0acc02d802dc0c40 0x02b300b600b70310 0x038c00d803f00000 0x40e3003600fc0000

def z176 : W := mkw 0x0279193230000000 0x009e464c8c000000 0x107c1c3838000000 0x841f070e0e000000

def z177 : W := mkw 0x0ad803f800910ec0 0x02b600fe002443b0 0xdbfc03f800000fc2 0xf6ff00fe000003f0

def z178 : W := mkw 0x02d803b000010280 0x00b600ec000040a0 0xfbfc03f8040f0fc2 0xfeff00fe0103c3f0

def z179 : W := mkw 0x0000000000000000 0x0000000000000000 0x640c7cf8f808f8ff 0xd9031f3e3e023e3f

def z180 : W := mkw 0x049003e7e0910fbb 0xc12400f9f82443ee 0x0c0003e7e0000ffe 0x030000f9f80003ff

def z181 : W := mkw 0x05b3f3e7e5b3efbb 0xc16cfcf9f96cfbee 0xfff3e3c7c7f7cf33 0x7ffcf8f1f1fdf3cc

def z182 : W := mkw 0x0031912324008122 0x000c6448c9002048 0xfc7393272400cf33 0xbf1ce4c9c90033cc

def z183 : W := mkw 0x0592e3f7f5b0cd33 0x8164b8fdfd6c334c 0xef83e3fffff0cf33 0x7be0f8fffffc33cc

def z184 : W := mkw 0x800424484b885855 0x2001091212e21615 0x0000000003800000 0x0000000000e00000

def z185 : W := mkw 0x058262c4c1b04c11 0x816098b1306c1304 0x038060c0c3f00000 0x40e0183030fc0000

def z186 : W := mkw 0x0102400000000000 0x0040900000000000 0xc383e00000000001 0x70e0f80000000000

def z187 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xfc7ffffffc0fffff 0xff1fffffff03ffff

def z188 : W := mkw 0x0102c00004208000 0x0040b00001082000 0x8383800004700000 0x20e0e000011c0000

def z189 : W := mkw 0x0000800104008122 0x0000200041002048 0xec0393272408ffff 0xbb00e4c9c9023fff

def z190 : W := mkw 0x0004244043885811 0x0001091010e21604 0x640c7cc0c388f833 0xd9031f3030e23e0c

def z191 : W := mkw 0x17effe85877ef522 0x85fbffa161dfbd48 0xfbffff0707fff701 0xfeffffc1c1fffdc0

def z192 : W := mkw 0x0031112220032288 0x400c44488800c8a2 0x10701020200f30cc 0x841c04080803cc33

def z193 : W := mkw 0x0080028000000000 0x002000a000000000 0xcb8003c000000002 0x72e000f000000000

def z194 : W := mkw 0x0031112220000000 0x000c444888000000 0x9873830700000000 0x261ce0c1c0000000

def z195 : W := mkw 0x03da4bb6b0000000 0x00f692edac000000 0x0f8c6ffff8000002 0x43e31bfffe000000

def z196 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfffc7ff8ffff0fc3 0xffff1ffe3fffc3f0

def z197 : W := mkw 0x024c2400034c5000 0x0093090000d31400 0xf3fc7c0007fff001 0xfcff1f0001fffc00

def z198 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000000008f8fc 0x0800000000023e3f

def z199 : W := mkw 0x0010013230000000 0x0004004c8c000000 0x0000003838000000 0x0000000e0e000000

def z200 : W := mkw 0x880424484bdd5ed5 0x2201091212f757b5 0x2000000007fffffc 0x0800000001ffffff

def z201 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xbbf0030007ff0fc0 0x2efc00c001ffc3f0

def z202 : W := mkw 0x0adc27f803dd5ec0 0x02b709fe00f757b0 0xfbfc7ff807ffffc3 0xfeff1ffe01fffff0

def z203 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xf8739307040ff701 0xbe1ce4c1c103fdc0

def z204 : W := mkw 0x0031112220000000 0x000c444888000000 0xdc73932720000003 0xb71ce4c9c8000000

def z205 : W := mkw 0x8004a4494f88d977 0x2001291253e2365d 0xec0fffffff88ffff 0xfb03ffffffe23fff

def z206 : W := mkw 0x0592e3e7e5b1cfbb 0xc164b8f9f96c73ee 0xef83e3e7e7f0cfff 0x7be0f8f9f9fc33ff

def z207 : W := mkw 0x8adc07f80add1ec4 0x22b701fe02b747b1 0xfbfc1ff83fff3fce 0xfeff07fe0fffcff3

def z208 : W := mkw 0x03ff5bb6b24c0000 0x00ffd6edac930000 0xffffffffffff0003 0xffffffffffffc000

def z209 : W := mkw 0x8000244849805855 0x2000091212601615 0x04007cf8f800f8ff 0x01001f3e3e003e3f

def z210 : W := mkw 0x03fb5bb000000000 0x00fed6ec00000000 0xdbfffff800000003 0xf6fffffe00000000

def z211 : W := mkw 0x800424004b085015 0x2001090012c21405 0x640c7c00fb88f03d 0xd9031f003ee23c0f

def z212 : W := mkw 0x9127fc484faaf855 0x2449ff1213eabe15 0x640ffcf8fb88f8ff 0xd903ff3e3ee23e3f

def z213 : W := mkw 0x1004a401076ff3aa 0x4401290041dbfcea 0x2000000007fffffc 0x0800000001ffffff

def z214 : W := mkw 0x136bd8000466a000 0x04daf6000119a800 0xf3f39000047ff001 0xbcfce400011ffc00

def z215 : W := mkw 0x8adc03f84add0ed5 0x22b700fe12b743b5 0xfffc03f8ffff0ffe 0xffff00fe3fffc3ff

def z216 : W := mkw 0x0021100000000000 0x0008440000000000 0xd073900000000001 0xb41ce40000000000

def z217 : W := mkw 0x008082c104908d22 0x002020b041242348 0xef8383c707f0cf33 0x7be0e0f1c1fc33cc

def z218 : W := mkw 0x0004004802880840 0x0001001200a20210 0x000c00d803800000 0x4003003600e00000

def z219 : W := mkw 0x81277c4efb885855 0x2049df13bee21615 0x640ffcfffb88f8ff 0xd903ff3ffee23e3f

def z220 : W := mkw 0x0bff5bfeb2dc0c40 0x02ffd6ffacb70310 0xdffffffffbf00003 0xf7fffffffefc0000

def z221 : W := mkw 0x0248000000000000 0x0092000000000000 0xd3fc000000000000 0xf4ff000000000000

def z222 : W := mkw 0x1004a400076ef000 0x0401290001dbbc00 0x2000000007fff000 0x0800000001fffc00

def z223 : W := mkw 0x048002c5c0900d33 0x812000b17024034c 0x0c0003c7c0000f32 0x030000f1f00003cc

def z224 : W := mkw 0x0000004040800811 0x0000001010200204 0x040000c0c0000832 0x010000303000020c

def z225 : W := mkw 0x0031112220000000 0x000c444888000000 0x1070102020000000 0x841c040808000000

def z226 : W := mkw 0x17fffff7f7fefd33 0x85fffffdfdffbf4c 0xffffffffffffff33 0xffffffffffffffcc

def z227 : W := mkw 0x800424484b885855 0x2001091212e21615 0x600c00f80388f8fe 0xd803003e00e23e3f

def z228 : W := mkw 0x17effec5c7fefd33 0x85fbffb171ffbf4c 0xffffffc7c7ffff33 0xfffffff1f1ffffcc

def z229 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001020200830cc 0x8000040808020c33

def z230 : W := mkw 0x07fbdbb7b4308522 0x81fef6eded0c2148 0x9bf3830704700700 0x26fce0c1c11c01c0

def z231 : W := mkw 0x03fbdbb7b403a3aa 0x40fef6eded00e8ea 0xfff39327240fffff 0xbffce4c9c903ffff

def z232 : W := mkw 0x03da43b480000000 0x00f690ed20000000 0xdfffe3ffc0000003 0xf7fff8fff0000000

def z233 : W := mkw 0x002190032403a3aa 0x40086400c900e8ea 0x24039007240ffffd 0x0900e401c903ffff

def z234 : W := mkw 0x07dae3f5c5b0cd33 0x81f6b8fd716c334c 0xffffe3ffc7f0cf33 0xfffff8fff1fc33cc

def z235 : W := mkw 0x13ce6e94936c5000 0x04f39ba524db1400 0x038c6cd8dbf00000 0x40e31b3636fc0000

def z236 : W := mkw 0x1523fc05c522f133 0x8548ff017148bc4c 0x0403fc07c000f031 0x0100ff01f0003c0c

def z237 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c6cd8d8000000 0x40031b3636000000

def z238 : W := mkw 0x0502e005c520c133 0x8140b8017148304c 0xec03e307c400cf33 0x3b00f8c1f10033cc

def z239 : W := mkw 0x0004004802880840 0x0001001200a20210 0x640c10f82388f8ff 0xd903043e08e23e3f

def z240 : W := mkw 0x03fb5bb7b00103aa 0x40fed6edec0040ea 0xdffffffff8000fff 0xf7fffffffe0003ff

def z241 : W := mkw 0x809427fefb885855 0x202509ffbee21615 0x6c0c7ffffb88f8ff 0xdb031ffffee23e3f

def z242 : W := mkw 0x136f7c00036e7000 0x04dbdf0000db9c00 0x13fc7c0003ff3000 0xc4ff1f0000ffcc00

def z243 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf7fffc2027fff8ff 0xfdffff0809fffe3f

def z244 : W := mkw 0x1123fc000522f000 0x0448ff000148bc00 0xe383fc0007f0f001 0x78e0ff0001fc3c00

def z245 : W := mkw 0x048022c5c1904d33 0x812008b17064134c 0x6c0063c7c380cf33 0x5b0018f1f0e033cc

def z246 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xfffffffff808f8ff 0xfffffffffe023e3f

def z247 : W := mkw 0x0400004140900d33 0x810000105024034c 0x0000000000000f30 0x00000000000003cc

def z248 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xab83830707f0cf30 0x2ae0e0c1c1fc33cc

def z249 : W := mkw 0x0502e045c5a0c933 0x8140b8117168324c 0x6403e0c7c380c833 0x5900f831f0e0320c

def z250 : W := mkw 0x8582e2cdcdb0cd77 0xa160b8b3736c335d 0xef83e3fffff0cfff 0x7be0f8fffffc33ff

def z251 : W := mkw 0x036f5800024c0000 0x00dbd60000930000 0xf3fffc0007ff0001 0xfcffff0001ffc000

def z252 : W := mkw 0x93fffffeffeef855 0x24ffffffbffbbe15 0xfffffffffffff8ff 0xfffffffffffffe3f

def z253 : W := mkw 0x13ffffb6b76ef000 0x04ffffedaddbbc00 0xfbffff0707fff001 0xfeffffc1c1fffc00

def z254 : W := mkw 0x8000000048000015 0x2000000012000005 0x04000000f800003c 0x010000003e00000f

def z255 : W := mkw 0x0592e3e5c5b1cfb3 0x8164b8f9716c73ec 0xfff3e3e7c7ffcff3 0xfffcf8f9f1fff3fc

def z256 : W := mkw 0x0031112220000000 0x000c444888000000 0xdc7ffffff8000003 0xf71ffffffe000000

def z257 : W := mkw 0x0fdac3b5847587a2 0x83f6b0ed611d61e8 0x9bf3830704770700 0x26fce0c1c11dc1c0

def z258 : W := mkw 0x126d1c00024e3000 0x049b470000938c00 0xf3fc1c0007ff3000 0xfcff070001ffcc00

def z259 : W := mkw 0x0182428480000000 0x006090a120000000 0xcf8ffffff8000003 0xf3e3fffffe000000

def z260 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xdbffff0700000001 0xf6ffffc1c0000000

def z261 : W := mkw 0x0010012000010280 0x00040048000040a0 0x0800032000000fc2 0x020000c8000003f0

def z262 : W := mkw 0x008022c041904c11 0x002008b010641304 0xef8063c0c7f0cf33 0x7be018f031fc33cc

def z263 : W := mkw 0x0ad803f800d50ec0 0x02b600fe003543b0 0x9bf003f804770fc2 0x26fc00fe011dc3f0

def z264 : W := mkw 0x10211c0000023000 0x0408470000008c00 0x00001c0000003000 0x0000070000000c00

def z265 : W := mkw 0x0000200041004011 0x0000080010401004 0x04006000c000c031 0x010018003000300c

def z266 : W := mkw 0x126d9c00064eb000 0x049b67000193ac00 0xf07f9c00040ff001 0xbc1fe7000103fc00

def z267 : W := mkw 0x134a480000640000 0x04d2920000190000 0x0380000000700000 0x00e00000001c0000

def z268 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0x9bfc03d807f70700 0x66ff00f601fdc1c0

def z269 : W := mkw 0x089003feb0910ec0 0x022400ffac2443b0 0x0c0003fff8000fc2 0x030000fffe0003f0

def z270 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xdff3e3c7c0000003 0x77fcf8f1f0000000

def z271 : W := mkw 0x01335926b0000000 0x004cd649ac000000 0xdc73ff27f8000003 0xb71cffc9fe000000

def z272 : W := mkw 0x136ffc06b76ef000 0x04dbff01addbbc00 0xf7fffc07fffff001 0xfdffff01fffffc00

def z273 : W := mkw 0x9004a4484feef855 0x2401291213fbbe15 0x640c7cf8fffff8ff 0xd9031f3e3ffffe3f

def z274 : W := mkw 0x13effec007fefc00 0x04fbffb001ffbf00 0xfbffffc007ffff03 0xfefffff001ffffc0

def z275 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0x0c0393272000ffff 0x0300e4c9c8003fff

def z276 : W := mkw 0x8014256b6b895bff 0x6005095adae256ff 0x6c0c7ffffb88ffff 0xdb031ffffee23fff

def z277 : W := mkw 0x0582e285c520c133 0x8160b8a17148304c 0xcf83e3c7c000c033 0x73e0f8f1f000300c

def z278 : W := mkw 0x0bffdbffb6dfafea 0x42fff6ffedb7ebfa 0xffffffffffffffff 0xffffffffffffffff

def z279 : W := mkw 0x0804004802dd0ec0 0x0201001200b743b0 0x2000000007ff0fc0 0x0800000001ffc3f0

def z280 : W := mkw 0x889003f848910ed5 0x222400fe122443b5 0x0c0003f8f8000ffe 0x030000fe3e0003ff

def z281 : W := mkw 0x8025b4484f8af855 0x20096d1213e2be15 0xf47ffcf8ff8ff8ff 0xfd1fff3e3fe3fe3f

def z282 : W := mkw 0x009003b6b0000000 0x002400edac000000 0x0800030700000000 0x020000c1c0000000

def z283 : W := mkw 0x089003b000110680 0x022400ec000441a0 0x0800030000000700 0x020000c0000001c0

def z284 : W := mkw 0x137ffd20076ff280 0x04dfff4801dbfca0 0xfbffff2007ffffc3 0xfeffffc801fffff0

def z285 : W := mkw 0x937ffd6b6feffbff 0x64dfff5adbfbfeff 0xffffffffffffffff 0xffffffffffffffff

def z286 : W := mkw 0x0ad803f000d50e80 0x02b600fc003543a0 0xfbf003c007f70f02 0x7efc00f001fdc3c0

def z287 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc03830700000003 0x3300e0c1c0000000

def z288 : W := mkw 0x07fbfbf7f5b3efbb 0xc1fefefdfd6cfbee 0xffffffffffffffff 0xffffffffffffffff

def z289 : W := mkw 0x0000000000000000 0x0000000000000000 0x640000000000c833 0x190000000000320c

def z290 : W := mkw 0x0523f007e522e13b 0xc148fc01f948b84e 0x0403f007e000f03d 0x0100fc01f8003c0f

def z291 : W := mkw 0x0582e2c5c5b3efbb 0xc160b8b1716cfbee 0xef83e3c7c7ffffff 0x7be0f8f1f1ffffff

def z292 : W := mkw 0x03ca4a9490000000 0x00f292a524000000 0x0380000000000000 0x00e0000000000000

def z293 : W := mkw 0x0123d807b402a12a 0x4048f601ed00a84a 0x0403fc07f800f03d 0x0100ff01fe003c0f

def z294 : W := mkw 0x03fbdbb7b402a12a 0x40fef6eded00a84a 0xdffffffff800f03f 0xf7fffffffe003c0f

def z295 : W := mkw 0x1b6ffc4807fffec0 0x06dbff1201ffffb0 0xf3fffc0007ffffc1 0xfcffff0001fffff0

def z296 : W := mkw 0x800424484b885855 0x2001091212e21615 0x600c7c000388f8fd 0xd8031f0000e23e3f

def z297 : W := mkw 0x0279193230000000 0x009e464c8c000000 0x1070000000000000 0x041c000000000000

def z298 : W := mkw 0x1004a400076ef000 0x0401290001dbbc00 0x600c7c0007fff001 0xd8031f0001fffc00

def z299 : W := mkw 0x137ffd23276ff3aa 0x44dfff48c9dbfcea 0xfbffff0707fff701 0xfeffffc1c1fffdc0

def z300 : W := mkw 0x04000005c0000133 0x810000017000004c 0x04000007c0000030 0x01000001f000000c

def z301 : W := mkw 0x03eb5a8480000000 0x00fad6a120000000 0xdfffffc7c0000003 0xf7fffff1f0000000

def z302 : W := mkw 0x089003fb20910fea 0x422400fec82443fa 0x0c0003ff20000ffe 0x030000ffc80003ff

def z303 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef8ffffffff0cf33 0xfbe3fffffffc33cc

def z304 : W := mkw 0x0582c28584308522 0x8160b0a1610c2148 0xcf83e3c7c4700703 0x73e0f8f1f11c01c0

def z305 : W := mkw 0x0a7d913b264fa3ea 0x429f644ec993e8fa 0xfc7f933f240fffff 0xbf1fe4cfc903ffff

def z306 : W := mkw 0x0804004802dc0c40 0x0201001200b70310 0x0000000003f00000 0x0000000000fc0000

def z307 : W := mkw 0x124c0c00024c1000 0x0493030000930400 0x000c0c0000000000 0x0003030000000000

def z308 : W := mkw 0x0000204041804811 0x0000081010601204 0x000060c0c3800000 0x4000183030e00000

def z309 : W := mkw 0x0102e0010520c122 0x0040b80041483048 0xef83e30707f0cf33 0x7be0f8c1c1fc33cc

def z310 : W := mkw 0x00100123200103aa 0x40040048c80040ea 0x0800030700000700 0x020000c1c00001c0

def z311 : W := mkw 0x0123580000000000 0x0048d60000000000 0x0003fc0000000001 0x0000ff0000000000

def z312 : W := mkw 0x0bff5bf802dd0ec0 0x02ffd6fe00b743b0 0xfbfffff807ff0fc3 0xfefffffe01ffc3f0

def z313 : W := mkw 0x003191200403a280 0x000c64480100e8a0 0xf8739320040fffc3 0xbe1ce4c80103fff0

def z314 : W := mkw 0x0004004802880840 0x0001001200a20210 0x20000000038808c0 0x0800000000e20230

def z315 : W := mkw 0x889427f84b995ed5 0x222509fe12e657b5 0x6c0c7ff8fb88ffff 0xdb031ffe3ee23fff

def z316 : W := mkw 0x13ffffb0076ef000 0x04ffffec01dbbc00 0xfbfffff807fff003 0xfefffffe01fffc00

def z317 : W := mkw 0x0fce62dcc3fc4c51 0x83f398b730ff1314 0x038c60d8c3f00000 0x40e3183630fc0000

def z318 : W := mkw 0x8582e6c5cdb0dd37 0xa160b9b1736c374d 0xef83ffc7fff0ff3f 0x7be0fff1fffc3fcf

def z319 : W := mkw 0x0035b523270bf3aa 0x400d6d48c9c2fcea 0xfc7fff27278fffff 0xff1fffc9c9e3ffff

def z320 : W := mkw 0x02d803b000000000 0x00b600ec00000000 0xdbfc03f800000002 0xf6ff00fe00000000

def z321 : W := mkw 0x0182e2848520c000 0x0060b8a121483000 0xef83e3c7c7f0c003 0x7be0f8f1f1fc3000

def z322 : W := mkw 0x8035152a2a0b32cc 0x600d454a8a82ccb3 0x107c1c38380f30cc 0x841f070e0e03cc33

def z323 : W := mkw 0x0102400480000000 0x0040900120000000 0x0403e007c0000001 0x0100f801f0000000

def z324 : W := mkw 0x936ffc484feef855 0x24dbff1213fbbe15 0xf3fffc0007fff8fd 0xfcffff0001fffe3f

def z325 : W := mkw 0x0000204041804811 0x0000081010601204 0x640070e0e388f8ff 0xd9001c3838e23e3f

def z326 : W := mkw 0x03da4bb490000000 0x00f692ed24000000 0xdbfc6ff8d8000002 0xf6ff1bfe36000000

def z327 : W := mkw 0x00100123200103aa 0x40040048c80040ea 0x6c0013272008ffff 0x9b0004c9c8023fff

def z328 : W := mkw 0x034a480000000000 0x00d2920000000000 0x038c6c0000000000 0x40e31b0000000000

def z329 : W := mkw 0x1beffed807fefc40 0x06fbffb601ffbf10 0xf3fffcd807fff001 0xfcffff3601fffc00

def z330 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0x8b83e3c7c7f00700 0x62e0f8f1f1fc01c0

def z331 : W := mkw 0x0080028480000000 0x002000a120000000 0x0c0003c7c0000002 0x030000f1f0000000

def z332 : W := mkw 0x8000004848800855 0x2000001212200215 0x00000000000008fc 0x000000000000023f

def z333 : W := mkw 0x02d803b000000000 0x00b600ec00000000 0xdffc7ff8f8000003 0xf7ff1ffe3e000000

def z334 : W := mkw 0x9004a4484feef855 0x2401291213fbbe15 0x2000000007fff8fc 0x0800000001fffe3f

def z335 : W := mkw 0x137bd9232467a3aa 0x44def648c919e8ea 0x9bf3830704770700 0x26fce0c1c11dc1c0

def z336 : W := mkw 0x0269180000000000 0x009a460000000000 0x107c1c0000000000 0x841f070000000000

def z337 : W := mkw 0x0502e04145b0cd33 0x8140b810516c334c 0xe383e00007f0cf31 0x78e0f80001fc33cc

def z338 : W := mkw 0x0000004000800800 0x0000001000200200 0x600000c003800802 0x5800003000e00200

def z339 : W := mkw 0x126d3c00034e7000 0x049b4f0000d39c00 0x707c7c00038ff001 0xdc1f1f0000e3fc00

def z340 : W := mkw 0x8035356a6b8b7add 0x600d4d5a9ae2deb7 0x747c7cf8fb8ff8ff 0xdd1f1f3e3ee3fe3f

def z341 : W := mkw 0x048002c4c0900c11 0x812000b130240304 0x000000c0c0000000 0x0000003030000000

def z342 : W := mkw 0x8586e6cdcfb8dd77 0xa161b9b373ee375d 0xef8fefdfdff0cf33 0x7be3fbf7f7fc33cc

def z343 : W := mkw 0x0804004802dd0ec0 0x0201001200b743b0 0x600c00f807ff0fc2 0xd803003e01ffc3f0

def z344 : W := mkw 0x1b7ffd38076ff2c0 0x06dfff4e01dbfcb0 0xf3fffc3807fff0c1 0xfcffff0e01fffc30

def z345 : W := mkw 0x800404484a881855 0x2001011212a20615 0x040c1cf8f80838fe 0x8103073e3e020e3f

def z346 : W := mkw 0x0035916b268babea 0x400d645ac9a2eafa 0xfc7f93ff278fffff 0xff1fe4ffc9e3ffff

def z347 : W := mkw 0x0af993b32457a7aa 0x42be64ecc915e9ea 0xfff39327247fffff 0xbffce4c9c91fffff

def z348 : W := mkw 0x936ffc004f6ef015 0x24dbff0013dbbc05 0xf7fffc00fffff03d 0xfdffff003ffffc0f

def z349 : W := mkw 0x800424484b885855 0x2001091212e21615 0x440c7cf8fb800003 0xd1031f3e3ee00000

def z350 : W := mkw 0x0adc03b8025d06c0 0x02b700ee009741b0 0x9bfc0338047f07c0 0xa6ff00ce011fc1f0

def z351 : W := mkw 0x048002c5c0900d33 0x812000b17024034c 0xef8003c7c7f00f32 0x7be000f1f1fc03cc

def z352 : W := mkw 0x136f7c00036c5000 0x04dbdf0000db1400 0xd3fffc0003f00001 0xf4ffff0000fc0000

def z353 : W := mkw 0x934e6c484bec5855 0x24d39b1212fb1615 0x678c7cf8fbf8f8ff 0xd9e31f3e3efe3e3f

def z354 : W := mkw 0x03fbdbb7b4008122 0x00fef6eded002048 0xfffffffffc00cf33 0xffffffffff0033cc

def z355 : W := mkw 0x0814016802dd0ec0 0x0205005a00b743b0 0xf870032007ff0fc2 0xbe1c00c801ffc3f0

def z356 : W := mkw 0x1123fc000522f000 0x0448ff000148bc00 0xf073fc00040ff001 0xbc1cff000103fc00

def z357 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0xeb8003f807f00fc2 0x7ae000fe01fc03f0

def z358 : W := mkw 0x8acc26d84bdc5c55 0x22b309b612f71715 0x038c6cd8dbf00000 0x40e31b3636fc0000

def z359 : W := mkw 0x0004004802880840 0x0001001200a20210 0x640c7cf8fb8808c3 0xd9031f3e3ee20230

def z360 : W := mkw 0x1bfffffb27ffffea 0x46fffffec9fffffa 0xffffffff27ffffff 0xffffffffc9ffffff

def z361 : W := mkw 0x0a5c017802dd0ec0 0x0297005e00b743b0 0x307c003807ff0fc0 0x8c1f000e01ffc3f0

def z362 : W := mkw 0x0010012000010280 0x00040048000040a0 0x9870030004070700 0x261c00c00101c1c0

def z363 : W := mkw 0x0000000000010280 0x00000000000040a0 0x20000000040f0fc0 0x080000000103c3f0

def z364 : W := mkw 0x0248081010000000 0x0092020404000000 0x000c0c1818000000 0x0003030606000000

def z365 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf7fffcf8fffff003 0xfdffff3e3ffffc00

def z366 : W := mkw 0x024c004802cc0840 0x0093001200b30210 0xf3fc00f807ff08c2 0xfcff003e01ffc230

def z367 : W := mkw 0x0582c28584308522 0x8160b0a1610c2148 0xef8383070470cf33 0x3be0e0c1c11c33cc

def z368 : W := mkw 0x0004240003085000 0x0001090000c21400 0x640c7cf8fb88f003 0xd9031f3e3ee23c00

def z369 : W := mkw 0x0adc03b0025d0680 0x02b700ec009741a0 0xfbfc030007ff0700 0xfeff00c001ffc1c0

def z370 : W := mkw 0x800424484b885855 0x2001091212e21615 0x240000f8fb88f8fe 0x0900003e3ee23e3f

def z371 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xf8738327040f0fc2 0xbe1ce0c9c103c3f0

def z372 : W := mkw 0x0400a04145b3efbb 0xc1002810516cfbee 0x2000000007fffffc 0x0800000001ffffff

def z373 : W := mkw 0x858666cccbb85c55 0xa16199b332ee1715 0x038c6cd8dbf00000 0x40e31b3636fc0000

def z374 : W := mkw 0x0010012000010280 0x00040048000040a0 0xfc701320240fffff 0xbf1c04c80903ffff

def z375 : W := mkw 0x8031916b6c83abff 0x600c645adb20eaff 0xfc7393fffc0fffff 0xbf1ce4ffff03ffff

def z376 : W := mkw 0x0031112220010280 0x000c4448880040a0 0xfc739327240f0fc3 0xbf1ce4c9c903c3f0

def z377 : W := mkw 0x136f5c00024e3000 0x04dbd70000938c00 0xd3fffc00000f3001 0xf4ffff000003cc00

def z378 : W := mkw 0x0004244803885840 0x0001091200e21610 0x600c7cf80388f8c3 0xd8031f3e00e23e30

def z379 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0x0c03e3c7c000cf33 0x0300f8f1f00033cc

def z380 : W := mkw 0x0502e005c520c133 0x8140b8017148304c 0xe783e007c7f0c031 0x79e0f801f1fc300c

def z381 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0x9c73832724070ffe 0x271ce0c9c901c3ff

def z382 : W := mkw 0x002190000402a000 0x000864000100a800 0x000390000000f001 0x0000e40000003c00

def z383 : W := mkw 0x0acc02d802dc0c40 0x02b300b600b70310 0x638c00f803f808c2 0xd8e3003e00fe0230

def z384 : W := mkw 0x0102e0000520c000 0x0040b80001483000 0x0003e0000000c001 0x0000f80000003000

def z385 : W := mkw 0x1bfbdbb00477a680 0x06fef6ec011de9a0 0x9bf3830004770700 0x26fce0c0011dc1c0

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x040000f8f8000002 0x0100003e3e000000

def z387 : W := mkw 0x83ff5fbeba081044 0x20ffd7efae820411 0xdffffffff80830cf 0xf7fffffffe020c33

def z388 : W := mkw 0x83fb5bfef8800855 0x20fed6ffbe200215 0xdffffffff80008ff 0xf7fffffffe00023f

def z389 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0x13fc00f803ff00c0 0xc4ff003e00ffc030

def z390 : W := mkw 0x800404080a081044 0x2001010202820411 0x640c1c383808f8ff 0x9903070e0e023e3f

def z391 : W := mkw 0x11026c0001205000 0x04409b0000481400 0x00006c0000000000 0x00001b0000000000

def z392 : W := mkw 0x8021b4036d02f13f 0x60086d00db40bc4f 0x0403fc07f800f03d 0x0100ff01fe003c0f

def z393 : W := mkw 0x049003f7f0900d33 0x812400fdfc24034c 0x0c0003fff8000f32 0x030000fffe0003cc

def z394 : W := mkw 0x8000240049005015 0x2000090012401405 0x000000000000f03c 0x0000000000003c0f

def z395 : W := mkw 0x10040400024e3000 0x0401010000938c00 0x00000000000f3000 0x000000000003cc00

def z396 : W := mkw 0x809003fef8800855 0x202400ffbe200215 0x0c0003fff80008fe 0x030000fffe00023f

def z397 : W := mkw 0x0021180230000000 0x000846008c000000 0x00001c0038000000 0x000007000e000000

def z398 : W := mkw 0x07fb5bf7f0900d33 0x81fed6fdfc24034c 0xdffffffff8000f33 0xf7fffffffe0003cc

def z399 : W := mkw 0x827d1d3a3a081044 0x209f474e8e820411 0x107c1c38380830cc 0x841f070e0e020c33

def z400 : W := mkw 0x1ffffffdc7fffff3 0x87ffffff71fffffc 0xffffffffc7fffff3 0xfffffffff1fffffc

def z401 : W := mkw 0x0000004800800840 0x0000001200200210 0x000000f8000008c2 0x0000003e00000230

def z402 : W := mkw 0x02d803f000900c00 0x00b600fc00240300 0xfbfc03f807f00f02 0xfeff00fe01fc03c0

def z403 : W := mkw 0x0102480490000000 0x0040920124000000 0x00006c00d8000000 0x00001b0036000000

def z404 : W := mkw 0x088002d800900c40 0x022000b600240310 0x000000d800000000 0x0000003600000000

def z405 : W := mkw 0x800424484b885855 0x2001091212e21615 0x600c7cd8db88f001 0xd8031f3636e23c00

def z406 : W := mkw 0x0031112220000000 0x000c444888000000 0xfc7393272008f8ff 0xbf1ce4c9c8023e3f

def z407 : W := mkw 0x0004000002080000 0x0001000000820000 0x600c000003880000 0xd803000000e20000

def z408 : W := mkw 0x17ebfac5c5f6ed33 0x85fafeb1717dbb4c 0xfff3e3c7c7f7cf33 0x7ffcf8f1f1fdf3cc

def z409 : W := mkw 0x83ff7ffefb885855 0x20ffdfffbee21615 0xdffffffffb800003 0xf7fffffffee00000

def z410 : W := mkw 0x848426cdcb985d77 0xa12109b372e6175d 0x6c0c7ffffb88ffff 0xdb031ffffee23fff

def z411 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0x9c7393072407f73d 0x271ce4c1c901fdcf

def z412 : W := mkw 0x800424484b885855 0x2001091212e21615 0x000c7cf8fb8830cc 0xc0031f3e3ee20c33

def z413 : W := mkw 0x0582e2c4c5b0cc11 0x8160b8b1316c3304 0xe383e0c0c7f0c001 0x78e0f83031fc3000

def z414 : W := mkw 0x827d3d7a7b885855 0x209f4f5e9ee21615 0x747c7cf8fb88f8ff 0xdd1f1f3e3ee23e3f

def z415 : W := mkw 0x1afd1ff802df3ec0 0x06bf47fe00b7cfb0 0xfbfc1ff807ff3fc2 0xfeff07fe01ffcff0

def z416 : W := mkw 0x17ebda858476a522 0x85faf6a1611da948 0x9bf3830704770700 0x26fce0c1c11dc1c0

def z417 : W := mkw 0x00040000024c0000 0x0001000000930000 0x2000000007ff0000 0x0800000001ffc000

def z418 : W := mkw 0x97effecdcffefd77 0xa5fbffb373ffbf5d 0xffffffffffffffff 0xffffffffffffffff

def z419 : W := mkw 0x136bfc000566f000 0x04daff000159bc00 0x93f3fc000477f001 0x24fcff00011dfc00

def z420 : W := mkw 0x03eb5a96b0000000 0x00fad6a5ac000000 0x078ffcdff8000001 0x41e3ff37fe000000

def z421 : W := mkw 0x8010016b68810bff 0x6004005ada2042ff 0x0c0003fff8000ffe 0x030000fffe0003ff

def z422 : W := mkw 0x0182c28584008122 0x0060b0a161002048 0xef83e3c7c400cf33 0x7be0f8f1f10033cc

def z423 : W := mkw 0x800424484b885855 0x2001091212e21615 0x24007c00fb88f8fd 0x09001f003ee23e3f

def z424 : W := mkw 0x0fdae3f5c5f5cfb3 0x83f6b8fd717d73ec 0xfff3e3c7c7f7cf33 0x7ffcf8f1f1fdf3cc

def z425 : W := mkw 0x00100123200103aa 0x40040048c80040ea 0xfc700327240f0ffe 0xbf1c00c9c903c3ff

def z426 : W := mkw 0x0000000000000000 0x0000000000000000 0x600010000008f001 0x9800040000023c00

def z427 : W := mkw 0x03fb5bf6b0900c00 0x00fed6fdac240300 0xfffffffffff00f03 0xfffffffffffc03c0

def z428 : W := mkw 0x136ffc4807eef840 0x04dbff1201fbbe10 0xf3fffcf807fff8c3 0xfcffff3e01fffe30

def z429 : W := mkw 0x000080010402a12a 0x400020004100a84a 0x000000000000f03c 0x0000000000003c0f

def z430 : W := mkw 0x8000004848800855 0x2000001212200215 0x000000d8d8000000 0x0000003636000000

def z431 : W := mkw 0x018262c4c1804811 0x006098b130601204 0xef83e3c7c380c833 0x7be0f8f1f0e0320c

def z432 : W := mkw 0x002190032402a12a 0x40086400c900a84a 0x0003800700000000 0x0000e001c0000000

def z433 : W := mkw 0x13effe84876ef000 0x04fbffa121dbbc00 0xffffffc7c7fff003 0xfffffff1f1fffc00

def z434 : W := mkw 0x037bd9232403a3aa 0x40def648c900e8ea 0xffffff27240fffff 0xffffffc9c903ffff

def z435 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0x0b8c03f803f00fc2 0x42e300fe00fc03f0

def z436 : W := mkw 0x8004a4494f8bfbff 0x6001291253e2feff 0x20000000078ffffc 0x0800000001e3ffff

def z437 : W := mkw 0x03fbdbb7b403a3aa 0x40fef6eded00e8ea 0x9bf3830704070700 0x26fce0c1c101c1c0

def z438 : W := mkw 0x1404a44147fefd33 0x8501291051ffbf4c 0x2000000007ffff30 0x0800000001ffffcc

def z439 : W := mkw 0x07cee2c5c7fccd33 0x81f3b8b171ff334c 0xffffe3c7c7ffcf33 0xfffff8f1f1fff3cc

def z440 : W := mkw 0x05b3d3a7a433a7aa 0xc16cf4e9e90ce9ea 0x9bf3830704770700 0x26fce0c1c11dc1c0

def z441 : W := mkw 0x02dc03f802880840 0x00b700fe00a20210 0xfbfc03f8038808c2 0xfeff00fe00e20230

def z442 : W := mkw 0x009003b6b0000000 0x002400edac000000 0x4c0c7ffff8000003 0xd3031ffffe000000

def z443 : W := mkw 0x8000004848800855 0x2000001212200215 0x440c7cf8f80008ff 0xd1031f3e3e00023f

def z444 : W := mkw 0x002190032402a12a 0x40086400c900a84a 0x640390272008f8ff 0x9900e409c8023e3f

def z445 : W := mkw 0x05026004c1204011 0x8140980130481004 0x00006000c0000000 0x0000180030000000

def z446 : W := mkw 0x13fbdbb6b466a000 0x04fef6edad19a800 0x9bf3830704770000 0x26fce0c1c11dc000

def z447 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xb3f3800007fff000 0x2cfce00001fffc00

def z448 : W := mkw 0x8035952b2e0bb3ee 0x600d654acb82ecfb 0xfc7f9f3f3c0fffff 0xbf1fe7cfcf03ffff

def z449 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfffc13f827ffffff 0xffff04fe09ffffff

def z450 : W := mkw 0x0182428480000000 0x006090a120000000 0x8b83830700000000 0x22e0e0c1c0000000

def z451 : W := mkw 0x0080028000100400 0x002000a000040100 0x8b80030004700700 0x22e000c0011c01c0

def z452 : W := mkw 0x03ff7fb6b3085000 0x00ffdfedacc21400 0xfffffffffb88f003 0xfffffffffee23c00

def z453 : W := mkw 0x800424080b085044 0x2001090202c21411 0x600c7c383b88f0cd 0xd8031f0e0ee23c33

def z454 : W := mkw 0x002190032402a12a 0x40086400c900a84a 0xf4739007240ff03d 0xbd1ce401c903fc0f

def z455 : W := mkw 0x1123fc032522f12a 0x4448ff00c948bc4a 0x0403fc072000f03d 0x0100ff01c8003c0f

def z456 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0x9bffefdfd8000000 0x66fffbf7f6000000

def z457 : W := mkw 0x0279193230000000 0x009e464c8c000000 0x547c7cf8f8000003 0xd51f1f3e3e000000

def z458 : W := mkw 0x0025b400070af000 0x00096d0001c2bc00 0xf07ffc00078ff001 0xfc1fff0001e3fc00

def z459 : W := mkw 0x100080000466a000 0x040020000119a800 0x0000000004770000 0x00000000011dc000

def z460 : W := mkw 0x0582c2c5c4b08d33 0x8160b0b1712c234c 0x8f8383c7c4700f32 0x23e0e0f1f11c03cc

def z461 : W := mkw 0x136ffc03276ef12a 0x44dbff00c9dbbc4a 0xf7fffc0727fff03d 0xfdffff01c9fffc0f

def z462 : W := mkw 0x0ffffbfff7fdcff3 0x83fffefffdff73fc 0xffffffffffffcff3 0xfffffffffffff3fc

def z463 : W := mkw 0x08100138000102c0 0x0204004e000040b0 0x00000038000000c0 0x0000000e00000030

def z464 : W := mkw 0x027999333403a3aa 0x409e664ccd00e8ea 0xfc7f9f3f3c0fffff 0xbf1fe7cfcf03ffff

def z465 : W := mkw 0x036b580000000000 0x00dad60000000000 0x93f3800000000000 0x24fce00000000000

def z466 : W := mkw 0x0106e4000728d000 0x0041b90001ca3400 0xe38ffc0007f8f001 0xf8e3ff0001fe3c00

def z467 : W := mkw 0x0523f807f520c133 0x8148fe01fd48304c 0x0403fc07f800c031 0x0100ff01fe00300c

def z468 : W := mkw 0x0502e045c5b0cd33 0x8140b811716c334c 0x2403e007c7f0cf31 0x0900f801f1fc33cc

def z469 : W := mkw 0x00000006b0000000 0x00000001ac000000 0x04000007f8000000 0x01000001fe000000

def z470 : W := mkw 0x0acc02d802dc0c40 0x02b300b600b70310 0xf3fc00d807ff0000 0xfcff003601ffc000

def z471 : W := mkw 0x0400a0014520c133 0x810028005148304c 0x000000000000c030 0x000000000000300c

def z472 : W := mkw 0x0835916b26dfafea 0x420d645ac9b7ebfa 0xfc73932727ffffff 0xbf1ce4c9c9ffffff

def z473 : W := mkw 0x8000244049805815 0x2000091012601605 0x64007cc0fb80f83f 0x59001f303ee03e0f

def z474 : W := mkw 0x0bfb5bfeb0910ec0 0x02fed6ffac2443b0 0xdffffffff8000fc3 0xf7fffffffe0003f0

def z475 : W := mkw 0x136bf8000566e000 0x04dafe000159b800 0xf3f3e00007f7c001 0x7cfcf80001fdf000

def z476 : W := mkw 0x002190000402a000 0x000864000100a800 0x9073800004070000 0x241ce0000101c000

def z477 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c1c3838000000 0x8003070e0e000000

def z478 : W := mkw 0x8000040008001004 0x2000010002000401 0x00001c003800300c 0x000007000e000c03

def z479 : W := mkw 0x0000000000000000 0x0000000000000000 0x400c00f800000002 0xd003003e00000000

def z480 : W := mkw 0x8fdee7fdcffddff7 0xa3f7b9ff73ff77fd 0xffffffffffffffff 0xffffffffffffffff

def z481 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0x187c03f8000f0fc2 0x861f00fe0003c3f0

def z482 : W := mkw 0x1bce6ed803fc5c40 0x06f39bb600ff1710 0x038c6cd803f00000 0x40e31b3600fc0000

def z483 : W := mkw 0x058262c4c1b04c11 0x816098b1306c1304 0xeb8063c0c7f00f02 0x7ae018f031fc03c0

def z484 : W := mkw 0x13fbffb6b522f000 0x04feffedad48bc00 0xdffffffff800f003 0xf7fffffffe003c00

def z485 : W := mkw 0x136ffc01076ff3aa 0x44dbff0041dbfcea 0xf3fffc0007fffffd 0xfcffff0001ffffff

def z486 : W := mkw 0x8000240049005015 0x2000090012401405 0x00006c00d8000000 0x00001b0036000000

def z487 : W := mkw 0x0004240003085000 0x0001090000c21400 0x200000000388f000 0x0800000000e23c00

def z488 : W := mkw 0x0adc03fb22dd0fea 0x42b700fec8b743fa 0xfffc03ff27ff0ffe 0xffff00ffc9ffc3ff

def z489 : W := mkw 0x0a4c004802dd0ec0 0x0293001200b743b0 0xf3fc000007ff0fc0 0xfcff000001ffc3f0

def z490 : W := mkw 0x1269180000462000 0x049a460000118800 0x1070000000070000 0x041c00000001c000

def z491 : W := mkw 0x002190000402a000 0x000864000100a800 0xf4739020240ff8ff 0xbd1ce4080903fe3f

def z492 : W := mkw 0x127d1d32324e3000 0x049f474c8c938c00 0x107c1c38380f3000 0x841f070e0e03cc00

def z493 : W := mkw 0x0400800104308522 0x81002000410c2148 0x0000000004700700 0x00000000011c01c0

def z494 : W := mkw 0x0586e2cdc7b8cd73 0x8161b8b371ee335c 0xef8fe3ffc7f8cff3 0xfbe3f8fff1fe33fc

def z495 : W := mkw 0x0bff5bfeb2dd0ec0 0x02ffd6ffacb743b0 0xfbff83ff07ff0fc2 0xfeffe0ffc1ffc3f0

def z496 : W := mkw 0x024c0000024c0000 0x0093000000930000 0x107c0000000f0000 0x841f00000003c000

def z497 : W := mkw 0x9123fc004d22f015 0x2448ff001348bc05 0x0403fc00f800f03d 0x0100ff003e003c0f

def z498 : W := mkw 0x0adc83f906dfafea 0x42b720fe41b7ebfa 0xfbfc03f807fffffe 0xfeff00fe01ffffff

def z499 : W := mkw 0x07fb7bf6f1b04c11 0x81fedefdbc6c1304 0xdffffffffbf00003 0xf7fffffffefc0000

def z500 : W := mkw 0x0133d927b403a3aa 0x404cf649ed00e8ea 0xfc73ff27fc0fffff 0xbf1cffc9ff03ffff

def z501 : W := mkw 0x8000240049005015 0x2000090012401405 0x440c7cf8f800f03f 0xd1031f3e3e003c0f

def z502 : W := mkw 0x1035b523276ff3aa 0x440d6d48c9dbfcea 0xfc73932727ffffff 0xbf1ce4c9c9ffffff

def z503 : W := mkw 0x81237c06f9005015 0x2048df01be401405 0x0403fc07f800f03d 0x0100ff01fe003c0f

def z504 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xdbff83ff00000002 0xf6ffe0ffc0000000

def z505 : W := mkw 0x03fb5bb6b0032288 0x40fed6edac00c8a2 0xdffffffff80f30cf 0xf7fffffffe03cc33

def z506 : W := mkw 0x02f913b220000000 0x00be44ec88000000 0xdfff93ff20000003 0xf7ffe4ffc8000000

def z507 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0x30701020240ffffc 0x8c1c04080903ffff

def z508 : W := mkw 0x0480a2c145b0cd33 0x812028b0516c334c 0xeb8003c007f0cf32 0x7ae000f001fc33cc

def z509 : W := mkw 0x036bd8000402a000 0x00daf6000100a800 0xf3fffc00040ff001 0xfcffff000103fc00

def z510 : W := mkw 0x0afd93fb26dfafea 0x42bf64fec9b7ebfa 0xfbff83ff07ff0fc2 0xfeffe0ffc1ffc3f0

def z511 : W := mkw 0x836f7c484b885855 0x20dbdf1212e21615 0xf7fffcf8fb88f8ff 0xfdffff3e3ee23e3f

def z512 : W := mkw 0x83ffffffff8bfbff 0x60ffffffffe2feff 0xffffffffff8fffff 0xffffffffffe3ffff

def z513 : W := mkw 0x0400a04145b0cd33 0x81002810516c334c 0xec03830707f0cf33 0x3b00e0c1c1fc33cc

def z514 : W := mkw 0x0adc83f906dd8fe2 0x02b720fe41b763f8 0xffff83ff07ffcff3 0xffffe0ffc1fff3fc

def z515 : W := mkw 0x0edca3f947fdcff3 0x83b728fe51ff73fc 0xfbfc03f807ffcff2 0xfeff00fe01fff3fc

def z516 : W := mkw 0x0000204041804811 0x0000081010601204 0x200000000380c830 0x0800000000e0320c

def z517 : W := mkw 0x058262c4c1b04c11 0x816098b1306c1304 0xcf83e3c7c3f00003 0x73e0f8f1f0fc0000

def z518 : W := mkw 0x0acc02d802dc0c40 0x02b300b600b70310 0xeb8c03d807f00f02 0x7ae300f601fc03c0

def z519 : W := mkw 0x0a58013000450280 0x0296004c001140a0 0x1070000000070000 0x041c00000001c000

def z520 : W := mkw 0x0adc23f843dd4ed1 0x02b708fe10f753b4 0xfffc63f8c7ffcff3 0xffff18fe31fff3fc

def z521 : W := mkw 0x137ffd22276ef000 0x04dfff4889dbbc00 0xffffff2727fff003 0xffffffc9c9fffc00

def z522 : W := mkw 0x82dc27f84b885855 0x20b709fe12e21615 0xfffc7ff8fb88f8ff 0xffff1ffe3ee23e3f

def z523 : W := mkw 0x824c24484bcc5855 0x2093091212f31615 0xf7fc7cf8fffff8ff 0xfdff1f3e3ffffe3f

def z524 : W := mkw 0x036b5806b0000000 0x00dad601ac000000 0xd7fffc07f8000001 0xf5ffff01fe000000

def z525 : W := mkw 0x8004a4494f8bfbff 0x6001291253e2feff 0x640c7cf8ff8fffff 0xd9031f3e3fe3ffff

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x04007c00f8000001 0x01001f003e000000

def z527 : W := mkw 0x0582c2c584b08d22 0x8160b0b1612c2348 0xeb8383c707f00f02 0x7ae0e0f1c1fc03c0

def z528 : W := mkw 0x0004240003085000 0x0001090000c21400 0x000c6c0003800000 0x40031b0000e00000

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x440060c0c0000003 0x5100183030000000

def z530 : W := mkw 0x05a3fac7f5b0cd33 0x8168feb1fd6c334c 0xef83ffc7fff0cf33 0x7be0fff1fffc33cc

def z531 : W := mkw 0x088402c802dd0ec0 0x022100b200b743b0 0xeb8003c007ff0fc2 0x7ae000f001ffc3f0

def z532 : W := mkw 0x04b193e7e493afbb 0xc12c64f9f924ebee 0xfc7393e7e40fffff 0xbf1ce4f9f903ffff

def z533 : W := mkw 0x0a5c0138024d02c0 0x0297004e009340b0 0xf3fc003807ff00c0 0xfcff000e01ffc030

def z534 : W := mkw 0x848002cdc8900d77 0xa12000b37224035d 0x0c0003fff8000ffe 0x030000fffe0003ff

def z535 : W := mkw 0x08b193fb2493afea 0x422c64fec924ebfa 0xfc7393ff240fffff 0xbf1ce4ffc903ffff

def z536 : W := mkw 0x0400a04145b0cd33 0x81002810516c334c 0x640060c0c7f0cf33 0x5900183031fc33cc

def z537 : W := mkw 0x0004204843884851 0x0001081210e21214 0x640c60f8c388c8f3 0xd903183e30e2323c

def z538 : W := mkw 0x03ff5bfeb2880840 0x00ffd6ffaca20210 0xfffffffffb8808c3 0xfffffffffee20230

def z539 : W := mkw 0x018242c480900c00 0x006090b120240300 0xef83e3c7c7f00f03 0x7be0f8f1f1fc03c0

def z540 : W := mkw 0x01b353a6a0000000 0x006cd4e9a8000000 0xdff3f3e7e0000003 0xf7fcfcf9f8000000

def z541 : W := mkw 0x1bfffffeb7fffec0 0x06ffffffadffffb0 0xffffffffffffffc3 0xfffffffffffffff0

def z542 : W := mkw 0x0004240003085000 0x0001090000c21400 0x640c7c202388f8ff 0xd9031f0808e23e3f

def z543 : W := mkw 0x936ffc484feef855 0x24dbff1213fbbe15 0xf3fffcd8dffff001 0xfcffff3637fffc00

def z544 : W := mkw 0x8adc27f84bdd5ed5 0x22b709fe12f757b5 0xfbfc03f807fffffe 0xfeff00fe01ffffff

def z545 : W := mkw 0x0010012000000000 0x0004004800000000 0xd870032000000002 0xb61c00c800000000

def z546 : W := mkw 0x0400204041b04c11 0x81000810106c1304 0x0000000003f00000 0x0000000000fc0000

def z547 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xfc7383070407cf33 0x3f1ce0c1c101f3cc

def z548 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000020000808c2 0x9800000800020230

def z549 : W := mkw 0x0fcee2ddc7fccd73 0x83f3b8b771ff335c 0xef8fe3dfc7f0cf33 0x7be3f8f7f1fc33cc

def z550 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0xf87003f8040f0fc2 0xbe1c00fe0103c3f0

def z551 : W := mkw 0x0000204041804811 0x0000081010601204 0x640c7cf8fb80c833 0xd9031f3e3ee0320c

def z552 : W := mkw 0x8506e44dcfa8d977 0xa141b91373ea365d 0x640ffcfffb88f8ff 0xd903ff3ffee23e3f

def z553 : W := mkw 0x000080010403a3aa 0x400020004100e8ea 0x0000000004070700 0x000000000101c1c0

def z554 : W := mkw 0x0582428480300400 0x816090a1200c0100 0x0380000000700000 0x00e00000001c0000

def z555 : W := mkw 0x0afd1bfa32dd0ec0 0x02bf46fe8cb743b0 0xfbfc1ff83fff0fc2 0xfeff07fe0fffc3f0

def z556 : W := mkw 0x137ffd22276ff288 0x44dfff4889dbfca2 0xf3fffc2027fff0cd 0xfcffff0809fffc33

def z557 : W := mkw 0x001081232403a3aa 0x40042048c900e8ea 0x2c000327240ffffe 0x0b0000c9c903ffff

def z558 : W := mkw 0x03fb7bf6f1804811 0x00fedefdbc601204 0xfffffffffb80c833 0xfffffffffee0320c

def z559 : W := mkw 0x05a3f2c7e5b2ed3b 0xc168fcb1f96cbb4e 0xef83f3c7e7f0ff3f 0x7be0fcf1f9fc3fcf

def z560 : W := mkw 0x07ebfac5c5b0cd33 0x81fafeb1716c334c 0xffffffc7c7f0cf33 0xfffffff1f1fc33cc

def z561 : W := mkw 0x83ce6edcdb885855 0x20f39bb736e21615 0x678c7cf8fb88f8ff 0xd9e31f3e3ee23e3f

def z562 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000020200008fe 0x010000080800023f

def z563 : W := mkw 0x13fbdbb6b466a000 0x04fef6edad19a800 0xdffffffffc770003 0xf7ffffffff1dc000

def z564 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xdc73932724070703 0xb71ce4c9c901c1c0

def z565 : W := mkw 0x0000000000000000 0x0000000000000000 0xe380000007f00000 0x78e0000001fc0000

def z566 : W := mkw 0x808426c84b985c55 0x202109b212e61715 0xef8c7ff8fff8ffff 0xfbe31ffe3ffe3fff

def z567 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0x13fc7cf8f8000000 0xc4ff1f3e3e000000

def z568 : W := mkw 0x000080010403a3aa 0x400020004100e8ea 0x64001020240fffff 0x990004080903ffff

def z569 : W := mkw 0x019243b6b0000000 0x006490edac000000 0xcf83e3fff8000003 0x73e0f8fffe000000

def z570 : W := mkw 0x058262c5c1b04d33 0x816098b1706c134c 0x0f8063c7c3f00f32 0x43e018f1f0fc03cc

def z571 : W := mkw 0x00b113b6b0000000 0x002c44edac000000 0xdc7393fff8000003 0xb71ce4fffe000000

def z572 : W := mkw 0x01235806b0000000 0x0048d601ac000000 0x0003800700000000 0x0000e001c0000000

def z573 : W := mkw 0x037b593230000000 0x00ded64c8c000000 0xd3fffc3838000001 0xf4ffff0e0e000000

def z574 : W := mkw 0x0000004000900c00 0x0000001000240300 0x2000000007f00f00 0x0800000001fc03c0

def z575 : W := mkw 0x1127fc00072af000 0x0449ff0001cabc00 0x600ffc000388f001 0xd803ff0000e23c00

def z576 : W := mkw 0x02f91bb230000000 0x00be46ec8c000000 0xdbfc1ff838000002 0xf6ff07fe0e000000

def z577 : W := mkw 0x00311123200323aa 0x400c4448c800c8ea 0x1c701327200f3ffe 0x871c04c9c803cfff

def z578 : W := mkw 0x1a7d1d38024f32c0 0x069f474e0093ccb0 0x107c1c38000f30c0 0x841f070e0003cc30

def z579 : W := mkw 0x0bce4adc92dc0c40 0x02f392b724b70310 0x038c6cd8dbf00000 0x40e31b3636fc0000

def z580 : W := mkw 0x17effec4c7fefc11 0x85fbffb131ffbf04 0xf3fffcc0c7fff001 0xfcffff3031fffc00

def z581 : W := mkw 0x0afd93f806dfaec0 0x02bf64fe01b7ebb0 0xfbff93f807ffffc3 0xfeffe4fe01fffff0

def z582 : W := mkw 0x0031112220032288 0x400c44488800c8a2 0xf8701320240f3fce 0xbe1c04c80903cff3

def z583 : W := mkw 0x800424484b885855 0x2001091212e21615 0x640060c0c388f8ff 0x5900183030e23e3f

def z584 : W := mkw 0x00108121040183a2 0x00042048410060e8 0xfc738327040fcff3 0xbf1ce0c9c103f3fc

def z585 : W := mkw 0x934e6c484bec5855 0x24d39b1212fb1615 0x038c6cd8dbf00000 0x40e31b3636fc0000

def z586 : W := mkw 0x800424484b885855 0x2001091212e21615 0x640c6cd8db80c833 0x59031b3636e0320c

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x040010002000f03d 0x0100040008003c0f

def z588 : W := mkw 0x02d803b6b0000000 0x00b600edac000000 0xdffc03fff8000002 0xf7ff00fffe000000

def z589 : W := mkw 0x0021100220000000 0x0008440088000000 0x0403900720000001 0x0100e401c8000000

def z590 : W := mkw 0x0bfb5bb6b0550680 0x02fed6edac1541a0 0x9bf3830704770700 0x26fce0c1c11dc1c0

def z591 : W := mkw 0x800404080a081044 0x2001010202820411 0x00000000000830cc 0x0000000000020c33

def z592 : W := mkw 0x003191232402a12a 0x400c6448c900a84a 0xdc7393272000f03f 0xb71ce4c9c8003c0f

def z593 : W := mkw 0x0bde4bfc92dd0ec0 0x02f792ff24b743b0 0xfbfc6ff8dfff0fc2 0xfeff1bfe37ffc3f0

def z594 : W := mkw 0x800404080a081044 0x2001010202820411 0x000c0c1818000000 0x0003030606000000

def z595 : W := mkw 0x058262c4c1b04c11 0x816098b1306c1304 0x678060c0c3f0c833 0x59e0183030fc320c

def z596 : W := mkw 0x1123fc06b522f000 0x0448ff01ad48bc00 0x0403fc07f800f001 0x0100ff01fe003c00

def z597 : W := mkw 0x136bd8000466a000 0x04daf6000119a800 0xd3fffc0004770001 0xf4ffff00011dc000

def z598 : W := mkw 0x0c04a04947fdcff3 0x8301281251ff73fc 0x2000000007ffcff0 0x0800000001fff3fc

def z599 : W := mkw 0x03ca4a9490000000 0x00f292a524000000 0x478c7cf8f8000003 0xd1e31f3e3e000000

def z600 : W := mkw 0x176ffc4147fefd33 0x85dbff1051ffbf4c 0xf3fffc0007ffff31 0xfcffff0001ffffcc

def z601 : W := mkw 0x800424084b085055 0x2001090212c21415 0x040c7c38f808f0fd 0x81031f0e3e023c3f

def z602 : W := mkw 0x800424484b885855 0x2001091212e21615 0x640010202388f8ff 0x9900040808e23e3f

def z603 : W := mkw 0x801425684b895ad5 0x2005095a12e256b5 0xfc7c7ff8ff8fffff 0xff1f1ffe3fe3ffff

def z604 : W := mkw 0x0af993b32457a7aa 0x42be64ecc915e9ea 0x9bf3830704770700 0x26fce0c1c11dc1c0

def z605 : W := mkw 0x17ffffe7e7ffffbb 0xc5fffff9f9ffffee 0xffffffe7e7ffffff 0xfffffff9f9ffffff

def z606 : W := mkw 0x008002c000900c00 0x002000b000240300 0x038000c003f00000 0x40e0003000fc0000

def z607 : W := mkw 0x009003b7b00103aa 0x402400edec0040ea 0x0c0003fff8000ffe 0x030000fffe0003ff

def z608 : W := mkw 0x036b580000000000 0x00dad60000000000 0xd7fffcf8f8000003 0xf5ffff3e3e000000

def z609 : W := mkw 0x0010012000010280 0x00040048000040a0 0x10700020000f00c0 0x841c00080003c030

def z610 : W := mkw 0x127d9d23264fb3aa 0x449f6748c993ecea 0xfc7f9f27240fffff 0xbf1fe7c9c903ffff

def z611 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0x238060c0c7f0cf30 0x48e0183031fc33cc

def z612 : W := mkw 0x0004000802080040 0x0001000200820010 0x000c0038000800c0 0x8003000e00020030

def z613 : W := mkw 0x02c8029000000000 0x00b200a400000000 0x038c00d800000000 0x40e3003600000000

def z614 : W := mkw 0x0ffff3ffe7ffeffb 0xc3fffcfff9fffbfe 0xfffff3ffe7ffffff 0xfffffcfff9ffffff

def z615 : W := mkw 0x126dbc00076ef000 0x049b6f0001dbbc00 0x307c1c0007fff000 0x8c1f070001fffc00

def z616 : W := mkw 0x0000000000000000 0x0000000000000000 0x400c7c0000000001 0xd0031f0000000000

def z617 : W := mkw 0x8000204849804855 0x2000081212601215 0x640060f8fb80c8ff 0x5900183e3ee0323f

def z618 : W := mkw 0x0a5c0138024d02c0 0x0297004e009340b0 0xf87c0338040f0fc2 0xbe1f00ce0103c3f0

def z619 : W := mkw 0x07fbfbf7f5b0cd33 0x81fefefdfd6c334c 0xfff3e3c7c7f0cf33 0x7ffcf8f1f1fc33cc

def z620 : W := mkw 0x8000000808000044 0x2000000202000011 0x00000038380000cc 0x0000000e0e000033

def z621 : W := mkw 0x027d9123264fa3aa 0x409f6448c993e8ea 0xffff932727ffffff 0xffffe4c9c9ffffff

def z622 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0x038ffc0003f0f001 0x40e3ff0000fc3c00

def z623 : W := mkw 0x0480a2c5c5b0cd33 0x812028b1716c334c 0x2c0003c7c7f0cf32 0x0b0000f1f1fc33cc

def z624 : W := mkw 0x0bff5bbeb24d02c0 0x02ffd6efac9340b0 0xdffffffff80f00c3 0xf7fffffffe03c030

def z625 : W := mkw 0x000000032000012a 0x40000000c800004a 0x040000072000003c 0x01000001c800000f

def z626 : W := mkw 0x0533f127e523e3bb 0xc14cfc49f948f8ee 0xfc73f327e40fffff 0xbf1cfcc9f903ffff

def z627 : W := mkw 0x03fbdbb7b403a3aa 0x40fef6eded00e8ea 0xdffffffffc070703 0xf7ffffffff01c1c0

def z628 : W := mkw 0x07fbdbb7b4308522 0x81fef6eded0c2148 0xdffffffffc700703 0xf7ffffffff1c01c0

def z629 : W := mkw 0x0582e285c530c533 0x8160b8a1714c314c 0x8f83e307c470c731 0x23e0f8c1f11c31cc

def z630 : W := mkw 0x8afdb7fb6fdfffff 0x62bf6dfedbf7ffff 0xffffffffffffffff 0xffffffffffffffff

def z631 : W := mkw 0x0000800104008122 0x0000200041002048 0x200000000400cf30 0x08000000010033cc

def z632 : W := mkw 0x002190010402a122 0x000864004100a848 0xfc739307040fff33 0xbf1ce4c1c103ffcc

def z633 : W := mkw 0x136ffc4047eef811 0x04dbff1011fbbe04 0xf7fffcc0c7fff833 0xfdffff3031fffe0c

def z634 : W := mkw 0x000080000402a000 0x000020000100a800 0x20000000040ff000 0x080000000103fc00

def z635 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0x0783e0c7c3f0c031 0x41e0f831f0fc300c

def z636 : W := mkw 0x0182e2c005b0cc00 0x0060b8b0016c3300 0xeb83e3c007f0cf03 0x7ae0f8f001fc33c0

def z637 : W := mkw 0x8adc27f84bdd5ed5 0x22b709fe12f757b5 0xfbfc6ff8dfff0fc2 0xfeff1bfe37ffc3f0

def z638 : W := mkw 0x1000a4000522f000 0x040029000148bc00 0x000000000000f000 0x0000000000003c00

def z639 : W := mkw 0x002190010403a3aa 0x400864004100e8ea 0xf0739000040ffffd 0xbc1ce4000103ffff

def z640 : W := mkw 0x07fbfbb7f520c133 0x81fefeedfd48304c 0xdffffffff800c033 0xf7fffffffe00300c

def z641 : W := mkw 0x0133f1232523e3aa 0x404cfc48c948f8ea 0xfff3f32727ffffff 0xfffcfcc9c9ffffff

def z642 : W := mkw 0x0031b1636583ebbb 0x400c6c58d960faee 0xfc73f3e7e78fffff 0xff1cfcf9f9e3ffff

def z643 : W := mkw 0x0adc03b8024d02c0 0x02b700ee009340b0 0xdbfc03f8000f00c2 0xf6ff00fe0003c030

def z644 : W := mkw 0x0502c00584208122 0x8140b00161082048 0x0003800700000000 0x0000e001c0000000

def z645 : W := mkw 0x008002c000900c00 0x002000b000240300 0x080003c000000f02 0x020000f0000003c0

def z646 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0x98739327240f37cc 0xa61ce4c9c903cdf3

def z647 : W := mkw 0x926d1c080a4e3044 0x249b470202938c11 0x107c1c38380f30cc 0x841f070e0e03cc33

def z648 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0x14739027200ff0fd 0x851ce409c803fc3f

def z649 : W := mkw 0x136fdc00066eb000 0x04dbf700019bac00 0x93ff9c00047f3000 0xa4ffe700011fcc00

def z650 : W := mkw 0x003191222402a000 0x000c64488900a800 0xfc739327240ff003 0xbf1ce4c9c903fc00

def z651 : W := mkw 0x85b7f7efefbbffff 0xe16dfdfbfbeeffff 0xffffffffffffffff 0xffffffffffffffff

def z652 : W := mkw 0x0ac8029000540400 0x02b200a400150100 0x0380000000700000 0x00e00000001c0000

def z653 : W := mkw 0x03eb5a9490000000 0x00fad6a524000000 0xd3fffcd8d8000001 0xf4ffff3636000000

def z654 : W := mkw 0x003191222403a288 0x400c64488900e8a2 0xf0739020240ff0cd 0xbc1ce4080903fc33

def z655 : W := mkw 0x13ff5fb6b24e3000 0x04ffd7edac938c00 0xdffffffff80f3003 0xf7fffffffe03cc00

def z656 : W := mkw 0x0a5c017802cd0ac0 0x0297005e00b342b0 0x707c00f8038f08c2 0xdc1f003e00e3c230

def z657 : W := mkw 0x134eec00076ef000 0x04d3bb0001dbbc00 0x238c6c0007fff000 0x48e31b0001fffc00

def z658 : W := mkw 0x1586e6c5c7fefd33 0x8561b9b171ffbf4c 0xef83e3c7c7ffff33 0x7be0f8f1f1ffffcc

def z659 : W := mkw 0x037b5936b0000000 0x00ded64dac000000 0x147ffc3ff8000001 0x851fff0ffe000000

def z660 : W := mkw 0x800424484b885855 0x2001091212e21615 0x200c1c383b88f8fc 0x8803070e0ee23e3f

def z661 : W := mkw 0x058242c5c0900d33 0x816090b17024034c 0xcf83e3c7c0000f33 0x73e0f8f1f00003cc

def z662 : W := mkw 0x926d3c484bce7855 0x249b4f1212f39e15 0x747c7cf8fb8ff8ff 0xdd1f1f3e3ee3fe3f

def z663 : W := mkw 0x0021100000022000 0x0008440000008800 0x10701000000f3000 0x841c04000003cc00

def z664 : W := mkw 0x02f91bb6b0000000 0x00be46edac000000 0x1c7c1ffff8000002 0x871f07fffe000000

def z665 : W := mkw 0x15a3fec5c5b2fd33 0x8568ffb1716cbf4c 0xef83ffc7c7f0ff33 0x7be0fff1f1fc3fcc

def z666 : W := mkw 0x05b3f3e7e5b0cd33 0x816cfcf9f96c334c 0xfff3f3e7e7f0cf33 0xfffcfcf9f9fc33cc

def z667 : W := mkw 0x0279193230000000 0x009e464c8c000000 0xdc7f9f3f38000003 0xb71fe7cfce000000

def z668 : W := mkw 0x0ad803b000550680 0x02b600ec001541a0 0xdbfc03f804770702 0xf6ff00fe011dc1c0

def z669 : W := mkw 0x1bffdbf806ffaec0 0x06fff6fe01bfebb0 0xfbff83f807ff0fc2 0xfeffe0fe01ffc3f0

def z670 : W := mkw 0x1133fd232523f3aa 0x444cff48c948fcea 0xfc73ff27240fffff 0xbf1cffc9c903ffff

def z671 : W := mkw 0x17ceeec5c7fcdd33 0x85f3bbb171ff374c 0xef8fefc7c7f0cf33 0x7be3fbf1f1fc33cc

def z672 : W := mkw 0x0080029490000000 0x002000a524000000 0x000000d8d8000000 0x0000003636000000

def z673 : W := mkw 0x8031b5236d03f3bf 0x600c6d48db40fcef 0xfc73ff27fc0fffff 0xbf1cffc9ff03ffff

def z674 : W := mkw 0x0acc02d802dd0ec0 0x02b300b600b743b0 0x238c00d807ff0fc0 0x48e3003601ffc3f0

def z675 : W := mkw 0x0bdee3f807fdcec0 0x02f7b8fe01ff73b0 0xfbffe3f807ffcfc3 0xfefff8fe01fff3f0

def z676 : W := mkw 0x07caead5d5b0cd33 0x81f2bab5756c334c 0xef8fefdfdff0cf33 0x7be3fbf7f7fc33cc

def z677 : W := mkw 0x13effe94976ef000 0x04fbffa525dbbc00 0xf3fffcd8dffff001 0xfcffff3637fffc00

def z678 : W := mkw 0x8acc26d84bdc5c55 0x22b309b612f71715 0x678c7cf8fbf8f8ff 0xd9e31f3e3efe3e3f

def z679 : W := mkw 0x036f7c0003085000 0x00dbdf0000c21400 0xf3fffc000388f001 0xfcffff0000e23c00

def z680 : W := mkw 0x0804804906dfafea 0x4201201241b7ebfa 0x2000000007fffffc 0x0800000001ffffff

def z681 : W := mkw 0x0279193230032288 0x409e464c8c00c8a2 0x107c1c38380f30cc 0x841f070e0e03cc33

def z682 : W := mkw 0x0ad803b000550680 0x02b600ec001541a0 0xfbf00320047f0fc2 0xbefc00c8011fc3f0

def z683 : W := mkw 0x000080010403a3aa 0x400020004100e8ea 0xec038307040fffff 0x3b00e0c1c103ffff

def z684 : W := mkw 0x0000240001005000 0x0000090000401400 0x00007c000000f001 0x00001f0000003c00

def z685 : W := mkw 0x0102600001204000 0x0040980000481000 0x0380600003f00000 0x40e0180000fc0000

def z686 : W := mkw 0x8000240049005015 0x2000090012401405 0x64007c20f808f8ff 0x99001f083e023e3f

def z687 : W := mkw 0x008402c802980c40 0x002100b200a60310 0xeb8c03f807f80fc2 0xfae300fe01fe03f0

def z688 : W := mkw 0x800404080a081044 0x2001010202820411 0x440c7cf8f80830cf 0xd1031f3e3e020c33

def z689 : W := mkw 0x00b193e32493afaa 0x402c64f8c924ebea 0xfff393e727ffffff 0xfffce4f9c9ffffff

def z690 : W := mkw 0x8106e4484fa8d855 0x2041b91213ea3615 0xe78ffcf8fff8f8ff 0xf9e3ff3e3ffe3e3f

def z691 : W := mkw 0x089403f802990ec0 0x022500fe00a643b0 0x680c03f803880fc2 0xda0300fe00e203f0

def z692 : W := mkw 0x0afd13fa22df2ec8 0x42bf44fe88b7cbb2 0xfbfc13f827ff3fce 0xfeff04fe09ffcff3

def z693 : W := mkw 0x137bd9232467a3aa 0x44def648c919e8ea 0xfff39327247fffff 0xbffce4c9c91fffff

def z694 : W := mkw 0x0258013000000000 0x0096004c00000000 0x107c003800000000 0x841f000e00000000

def z695 : W := mkw 0x134e6c00036c5000 0x04d39b0000db1400 0x638c7c0003f8f001 0xd8e31f0000fe3c00

def z696 : W := mkw 0x00108123240183aa 0x40042048c90060ea 0xec0383272400cfff 0x3b00e0c9c90033ff

def z697 : W := mkw 0x858666cccbb85c55 0xa16199b332ee1715 0x678c7cf8fbf8f8ff 0xd9e31f3e3efe3e3f

def z698 : W := mkw 0x8025b44b6f8af97f 0x60096d12dbe2be5f 0x640ffcfffb88f8ff 0xd903ff3ffee23e3f

def z699 : W := mkw 0x13ffffb7b76ff3aa 0x44ffffededdbfcea 0xffffffffffffffff 0xffffffffffffffff

def z700 : W := mkw 0x02f993b32403a3aa 0x40be64ecc900e8ea 0xffff93ff240fffff 0xffffe4ffc903ffff

def z701 : W := mkw 0x0afd13fa22dd0ec0 0x02bf44fe88b743b0 0xffff93ff27ff0fc3 0xffffe4ffc9ffc3f0

def z702 : W := mkw 0x0000000100000122 0x0000000040000048 0x0c00030700000f32 0x030000c1c00003cc

def z703 : W := mkw 0x0000a0414580c933 0x000028105160324c 0xec03e3c7c780cf33 0x7b00f8f1f1e033cc

def z704 : W := mkw 0x800400484a880855 0x2001001212a20215 0x640c00f8fb8808fe 0xd903003e3ee2023f

def z705 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0x107ffc00000ff001 0x841fff000003fc00

def z706 : W := mkw 0x8a5c05380a4d12c4 0x2297014e029344b1 0x107c1c38380f30cc 0x841f070e0e03cc33

def z707 : W := mkw 0x136bf8000566e000 0x04dafe000159b800 0x93f3e00007f70000 0x64fcf80001fdc000

def z708 : W := mkw 0x0080a2c14590cd33 0x002028b05164334c 0xef83e3c7c7f0cf33 0x7be0f8f1f1fc33cc

def z709 : W := mkw 0x136bd8000466a000 0x04daf6000119a800 0xf3f3800007f70000 0x7cfce00001fdc000

def z710 : W := mkw 0x13fb5bb6b0462000 0x04fed6edac118800 0xdffffffff8070003 0xf7fffffffe01c000

def z711 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xffffff0707fff003 0xffffffc1c1fffc00

def z712 : W := mkw 0x0523f005c522e133 0x8148fc017148b84c 0x0403f007c000f031 0x0100fc01f0003c0c

def z713 : W := mkw 0x036f5800024c0000 0x00dbd60000930000 0xf3ff800007ff0000 0xfcffe00001ffc000

def z714 : W := mkw 0x024c0000024c0000 0x0093000000930000 0xfbfc030007ff0f02 0xfeff00c001ffc3c0

def z715 : W := mkw 0x024c0000024c0000 0x0093000000930000 0x93fc000007f70000 0x64ff000001fdc000

def z716 : W := mkw 0x02cc02c802dc0c40 0x00b300b200b70310 0xfbfc03f807ff0fc2 0xfeff00fe01ffc3f0

def z717 : W := mkw 0x8586c68d8e389566 0xa161b1a3638e2559 0x8b8f9f3f3c7837cc 0xa2e3e7cfcf1e0df3

def z718 : W := mkw 0x800424484b885855 0x2001091212e21615 0x040c7cf8f808f8ff 0x81031f3e3e023e3f

def z719 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0x080003d800000700 0x020000f6000001c0

def z720 : W := mkw 0x0d92e3fdc5b1cff3 0x8364b8ff716c73fc 0x0c03e3ffc000cff3 0x0300f8fff00033fc

def z721 : W := mkw 0x1123fc07b522f12a 0x4448ff01ed48bc4a 0x0403fc07f800f03d 0x0100ff01fe003c0f

def z722 : W := mkw 0x03fb5bb6b0022000 0x00fed6edac008800 0xdffffffff80f3003 0xf7fffffffe03cc00

def z723 : W := mkw 0x136bf8000566e000 0x04dafe000159b800 0xf3f3f00007fff001 0xfcfcfc0001fffc00

def z724 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xdffffffff80830cf 0xf7fffffffe020c33

def z725 : W := mkw 0x0031112220010280 0x000c4448880040a0 0xfc739327240fffff 0xbf1ce4c9c903ffff

def z726 : W := mkw 0x8ad827b049555695 0x22b609ec125555a5 0x9ff07f00fc77f73d 0x27fc1fc03f1dfdcf

def z727 : W := mkw 0x1523f805c522e133 0x8548fe017148b84c 0x0403e007c000c031 0x0100f801f000300c

def z728 : W := mkw 0x0127f400072af000 0x0049fd0001cabc00 0xf3fffc0007fff001 0xfcffff0001fffc00

def z729 : W := mkw 0x8582e6c5cdb0dd37 0xa160b9b1736c374d 0xef83efc7dff0cf33 0x7be0fbf1f7fc33cc

def z730 : W := mkw 0x9123fc036d22f13f 0x6448ff00db48bc4f 0x0403fc07f800f03d 0x0100ff01fe003c0f

def z731 : W := mkw 0x003191333403a3aa 0x400c644ccd00e8ea 0xfc73933f3c0fffff 0xbf1ce4cfcf03ffff

def z732 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0x0800030000000fc0 0x020000c0000003f0

def z733 : W := mkw 0x03fb5bb6b0100400 0x00fed6edac040100 0xdffffffffc700703 0xf7ffffffff1c01c0

def z734 : W := mkw 0x058242c5c0900d33 0x816090b17024034c 0xef83e3c7c7f00f33 0x7be0f8f1f1fc03cc

def z735 : W := mkw 0x024c0400024c1000 0x0093010000930400 0xf3fc1c0007ff3000 0xfcff070001ffcc00

def z736 : W := mkw 0x136ffc02276ef000 0x04dbff0089dbbc00 0xf7fffc0727fff001 0xfdffff01c9fffc00

def z737 : W := mkw 0x1127f400076ef000 0x0449fd0001dbbc00 0xf3f3f00007fff001 0xfcfcfc0001fffc00

def z738 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef83f3e7e7f0cf33 0xfbe0fcf9f9fc33cc

def z739 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xb3f3fc0007fff001 0x2cfcff0001fffc00

def z740 : W := mkw 0x8582e6c5cdb0dd37 0xa160b9b1736c374d 0xef83ffe7fff8ffff 0xfbe0fff9fffe3fff

def z741 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xeb83e30707f0cf31 0x7ae0f8c1c1fc33cc

def z742 : W := mkw 0x8c04a4494ffddff7 0xa301291253ff77fd 0x2000000007fffffc 0x0800000001ffffff

def z743 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef83f3c7e7f0ff3f 0x7be0fcf1f9fc3fcf

def z744 : W := mkw 0x134ee400076ef000 0x04d3b90001dbbc00 0xf3ffe00007fff001 0xfcfff80001fffc00

def z745 : W := mkw 0x936ffc004f6ef015 0x24dbff0013dbbc05 0xf7fffcf8fffff03f 0xfdffff3e3ffffc0f

def z746 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xdbfc03f807f70702 0xf6ff00fe01fdc1c0

def z747 : W := mkw 0x936ffc004f6ef015 0x24dbff0013dbbc05 0xf7fffc20fffff8ff 0xfdffff083ffffe3f

def z748 : W := mkw 0x0582e2858530c522 0x8160b8a1614c3148 0x8b83e30707f00700 0x62e0f8c1c1fc01c0

def z749 : W := mkw 0x0bfb5bb6b0110680 0x02fed6edac0441a0 0xdffffffff8000703 0xf7fffffffe0001c0

def z750 : W := mkw 0x8adc07f80add1ec4 0x22b701fe02b747b1 0xfffc7ff8ffff3fcf 0xffff1ffe3fffcff3

def z751 : W := mkw 0x8c9003fdc8910ff7 0xa32400ff722443fd 0x0c0003fff8000ffe 0x030000fffe0003ff

def z752 : W := mkw 0x0582eac5d5b0cd33 0x8160bab1756c334c 0xef83efc7dff0cf33 0x7be0fbf1f7fc33cc

def z753 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef83e3e7e7f0cfff 0x7be0f8f9f9fc33ff

def z754 : W := mkw 0x024c0000024d0280 0x00930000009340a0 0xf3fc000007ff0fc0 0xfcff000001ffc3f0

def z755 : W := mkw 0x0a4c0018024c0040 0x0293000600930010 0xf3fc001807ff0000 0xfcff000601ffc000

def z756 : W := mkw 0x0adc03feb2dd0ec0 0x02b700ffacb743b0 0xfffc7fffffff0fc3 0xffff1fffffffc3f0

def z757 : W := mkw 0x0679b97375b0cd33 0x819e6e5cdd6c334c 0x307c1c383ff0cf30 0x8c1f070e0ffc33cc

def z758 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xab83e3c7c7f0cf30 0x6ae0f8f1f1fc33cc

def z759 : W := mkw 0x049003f7f0910fbb 0xc12400fdfc2443ee 0x0c0003fff8000ffe 0x030000fffe0003ff

def z760 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0x8b83830707f00700 0x22e0e0c1c1fc01c0

def z761 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0x1c739327200fffff 0x871ce4c9c803ffff

def z762 : W := mkw 0x00b113b6b0000000 0x002c44edac000000 0xdc7ffffff8000003 0xf71ffffffe000000

def z763 : W := mkw 0x136ffc04976ef000 0x04dbff0125dbbc00 0xf3fffc00dffff001 0xfcffff0037fffc00

def z764 : W := mkw 0x0102e0010520c122 0x0040b80041483048 0xeb83e30707f0c701 0x7ae0f8c1c1fc31c0

def z765 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xf8739307040ffffd 0xbe1ce4c1c103ffff

def z766 : W := mkw 0x0bfbdbb7b457a7aa 0x42fef6eded15e9ea 0x9bf3830704770700 0x26fce0c1c11dc1c0

def z767 : W := mkw 0x0edc03fcc2dd0ed1 0x83b700ff30b743b4 0xfbfc03f8c7ff0fc2 0xfeff00fe31ffc3f0

def z768 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xfc7f9f3f3c0fffff 0xbf1fe7cfcf03ffff

def z769 : W := mkw 0x0adc07f802dd1ec0 0x02b701fe00b747b0 0xfbfc1ff807ff3fc2 0xfeff07fe01ffcff0

def z770 : W := mkw 0x8523f407ed22f13f 0xe148fd01fb48bc4f 0x0403fc07f800f03d 0x0100ff01fe003c0f

def z771 : W := mkw 0x03eb5a96b0000000 0x00fad6a5ac000000 0x478ffcfff8000003 0xd1e3ff3ffe000000

def z772 : W := mkw 0x136ffc03276ef12a 0x44dbff00c9dbbc4a 0xffffff0727ffff3f 0xffffffc1c9ffffcf

def z773 : W := mkw 0x136ffc01076ef122 0x04dbff0041dbbc48 0xf3fffc0007ffff31 0xfcffff0001ffffcc

def z774 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfbfc6ff8dfff0fc2 0xfeff1bfe37ffc3f0

def z775 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfffc03f807ffcff3 0xffff00fe01fff3fc

def z776 : W := mkw 0x0112e1232521c3aa 0x4044b848c94870ea 0xef83e32727f0cfff 0x7be0f8c9c9fc33ff

def z777 : W := mkw 0x800424484b985c55 0x2001091212e61715 0x640c7cf8fff8ffff 0xd9031f3e3ffe3fff

def z778 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf7fffc2027fff003 0xfdffff0809fffc00

def z779 : W := mkw 0x8035b56b6f8bfbff 0x600d6d5adbe2feff 0x987fefdfdf870700 0x661ffbf7f7e1c1c0

def z780 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0x93f3800007f70000 0x24fce00001fdc000

def z781 : W := mkw 0x127d1d22224f3288 0x449f47488893cca2 0x107c1c00000f3000 0x841f07000003cc00

def z782 : W := mkw 0x025c0120024d0280 0x00970048009340a0 0xfbfc030007ff0700 0xfeff00c001ffc1c0

def z783 : W := mkw 0x889003fef8910ed5 0x222400ffbe2443b5 0x0c0003fff8000ffe 0x030000fffe0003ff

def z784 : W := mkw 0x1123fc010522f12a 0x4448ff004148bc4a 0x0003fc000000f03d 0x0000ff0000003c0f

def z785 : W := mkw 0x024c0000024c0000 0x0093000000930000 0x13fc000003ff0000 0xc4ff000000ffc000

def z786 : W := mkw 0x889003f808910ec4 0x222400fe022443b1 0x080003f838000fce 0x020000fe0e0003f3

def z787 : W := mkw 0x0582e2c5c5b2ed3b 0xc160b8b1716cbb4e 0xef83e3c7c7f0ff3f 0x7be0f8f1f1fc3fcf

def z788 : W := mkw 0x03eb5a9490000000 0x00fad6a524000000 0xdfffffdfd8000003 0xf7fffff7f6000000

def z789 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf3ffec0007ff0000 0xfcfffb0001ffc000

def z790 : W := mkw 0x0d82e2ddc5b0cd73 0x8360b8b7716c335c 0xef83e3dfc7f0cf33 0x7be0f8f7f1fc33cc

def z791 : W := mkw 0x8035356a6b885855 0x200d4d5a9ae21615 0xfc7393272388f8ff 0xbf1ce4c9c8e23e3f

def z792 : W := mkw 0x0acc02d802dc0c40 0x02b300b600b70310 0xfbfc03d807ff0f02 0xfeff00f601ffc3c0

def z793 : W := mkw 0x1523fc058522f122 0x8548ff016148bc48 0x0003fc070000f001 0x0000ff01c0003c00

def z794 : W := mkw 0x03fb5bb6b0440000 0x00fed6edac110000 0xdffffffffc770003 0xf7ffffffff1dc000

def z795 : W := mkw 0x074ee005c76cc133 0x81d3b80171db304c 0xf7ffe007c7ffc031 0xfdfff801f1fff00c

def z796 : W := mkw 0x136bf8000566e000 0x04dafe000159b800 0xb3f3800007f7c000 0x2cfce00001fdf000

def z797 : W := mkw 0x136ff800076ee000 0x04dbfe0001dbb800 0xf3ffe00007ffc001 0xfcfff80001fff000

def z798 : W := mkw 0x889407f80a991ec4 0x222501fe02a647b1 0x080c1ff838083fce 0x820307fe0e020ff3

def z799 : W := mkw 0x800424084b085055 0x2001090212c21415 0x440c7cf8f808f0ff 0xd1031f3e3e023c3f

def z800 : W := mkw 0x0f5ee13dc76dc3f3 0x83d7b84f71db70fc 0x147fe03fc00fc0f1 0x851ff80ff003f03c

def z801 : W := mkw 0x800424484b885855 0x2001091212e21615 0x200c7cf8fb88f8fc 0xc8031f3e3ee23e3f

def z802 : W := mkw 0x024c0000024c0000 0x0093000000930000 0xf3fc002007ff08c2 0xfcff000801ffc230

def z803 : W := mkw 0x0102e04145a0c933 0x0040b8105168324c 0xef83e3c7c7f0cf33 0x7be0f8f1f1fc33cc

def z804 : W := mkw 0x0927584eb2dd0ec0 0x0249d613acb743b0 0x2403fc07ffff0fc1 0x0900ff01ffffc3f0

def z805 : W := mkw 0x02dc03b0024d0280 0x00b700ec009340a0 0xfbfc03f807ff0fc2 0xfeff00fe01ffc3f0

def z806 : W := mkw 0x0523f007e522e13b 0xc148fc01f948b84e 0x0403e007c000c031 0x0100f801f000300c

def z807 : W := mkw 0x136ffc01076ef122 0x04dbff0041dbbc48 0xffffff2727ffffff 0xffffffc9c9ffffff

def z808 : W := mkw 0x024c0000024c0000 0x0093000000930000 0xf3fc100007fff001 0xfcff040001fffc00

def z809 : W := mkw 0x1a7d1d3a324f32c0 0x069f474e8c93ccb0 0x107c1c38380f30c0 0x841f070e0e03cc30

def z810 : W := mkw 0x00108121040183a2 0x00042048410060e8 0xfc739327240fffff 0xbf1ce4c9c903ffff

def z811 : W := mkw 0x0182e2c105b0cd22 0x0060b8b0416c3348 0xef83e3c707f0cf33 0x7be0f8f1c1fc33cc

def z812 : W := mkw 0x024c2400034c5000 0x0093090000d31400 0xf3fc6c0007ff0000 0xfcff1b0001ffc000

def z813 : W := mkw 0x002190010403a3aa 0x400864004100e8ea 0xfc739307040fffff 0xbf1ce4c1c103ffff

def z814 : W := mkw 0x976ffc05cf6ef137 0xa5dbff0173dbbc4d 0xf7fffc07fffff03d 0xfdffff01fffffc0f

def z815 : W := mkw 0x8000244849805855 0x2000091212601615 0x440c7cf8f800f8ff 0xd1031f3e3e003e3f

def z816 : W := mkw 0x0248000000440000 0x0092000000110000 0xf3f0000007f70000 0x7cfc000001fdc000

def z817 : W := mkw 0x03caca959403a3aa 0x40f2b2a56500e8ea 0x238c6cd8dc0ffffc 0x48e31b363703ffff

def z818 : W := mkw 0x800424484b885855 0x2001091212e21615 0x040c7cf8fb88f0fd 0xc1031f3e3ee23c3f

def z819 : W := mkw 0x136ffc02276ef008 0x44dbff0089dbbc02 0xf3fffc0027fff00d 0xfcffff0009fffc03

def z820 : W := mkw 0x176ffc05c76ef133 0x85dbff0171dbbc4c 0xffffff07c7ffff33 0xffffffc1f1ffffcc

def z821 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfbfc7ff807ff0fc3 0xfeff1ffe01ffc3f0

def z822 : W := mkw 0x04a192c5c492ad33 0x812864b17124ab4c 0xfc7393c7c40fff33 0xbf1ce4f1f103ffcc

def z823 : W := mkw 0x03eb5a8480000000 0x00fad6a120000000 0xdffffffff8000003 0xf7fffffffe000000

def z824 : W := mkw 0x026d1000024e2000 0x009b440000938800 0xf3fc100007ff3000 0xfcff040001ffcc00

def z825 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0x0f83e3c7c3f0cf33 0x43e0f8f1f0fc33cc

def z826 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xb3ffec0007fff000 0x6cfffb0001fffc00

def z827 : W := mkw 0x0582c28584308522 0x8160b0a1610c2148 0xeb83830707f00700 0x7ae0e0c1c1fc01c0

def z828 : W := mkw 0x0adc0bf812dd0ec0 0x02b702fe04b743b0 0xfbfc0ff81fff0fc2 0xfeff03fe07ffc3f0

def z829 : W := mkw 0x0c9003fcc0910ed1 0x832400ff302443b4 0x080003f8c0000fc2 0x020000fe300003f0

def z830 : W := mkw 0x089403f802990ec0 0x022500fe00a643b0 0x080c03f800080fc2 0x820300fe000203f0

def z831 : W := mkw 0x026db400074ef000 0x009b6d0001d3bc00 0xf3fffc0007fff001 0xfcffff0001fffc00

def z832 : W := mkw 0x136f7c00036e7000 0x04dbdf0000db9c00 0x13fc6c0003f70000 0x44ff1b0000fdc000

def z833 : W := mkw 0x03da4bb6b0000000 0x00f692edac000000 0xcf8feffff8000003 0x73e3fbfffe000000

def z834 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xbc738327240ffffe 0x2f1ce0c9c903ffff

def z835 : W := mkw 0x889027f849915ed5 0x222409fe126457b5 0x0c007ff8f800ffff 0x03001ffe3e003fff

def z836 : W := mkw 0x124ca400076ef000 0x0493290001dbbc00 0xb3f0000007fff000 0x2cfc000001fffc00

def z837 : W := mkw 0x1094a7b6b76ef000 0x042529edaddbbc00 0x2c0003fffffff002 0x0b0000fffffffc00

def z838 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0x13fffc0003fff001 0xc4ffff0000fffc00

def z839 : W := mkw 0x124c0c00024c1000 0x0493030000930400 0xf3fc0c0007ff0000 0xfcff030001ffc000

def z840 : W := mkw 0x03fb5bb6b0032288 0x40fed6edac00c8a2 0xfffffffff80ff8ff 0xfffffffffe03fe3f

def z841 : W := mkw 0x05b373e6e1b36e99 0xc16cdcf9b86cdba6 0x13f070e0e3ff30cc 0xc4fc1c3838ffcc33

def z842 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf3fffc2027fff0cd 0xfcffff0809fffc33

def z843 : W := mkw 0x936ffc084f6ef055 0x24dbff0213dbbc15 0xf7fffc38fffff0fd 0xfdffff0e3ffffc3f

def z844 : W := mkw 0x136ffc06b76ef000 0x04dbff01addbbc00 0xf7fffcfffffff003 0xfdffff3ffffffc00

def z845 : W := mkw 0x136f7c00036e7000 0x04dbdf0000db9c00 0x73fc7c0003fff001 0xdcff1f0000fffc00

def z846 : W := mkw 0x1123fc000522f000 0x0448ff000148bc00 0xf3f3fc0007fff001 0xfcfcff0001fffc00

def z847 : W := mkw 0x8a7d153a2a4f32cc 0x629f454e8a93ccb3 0x107c1c38380f30cc 0x841f070e0e03cc33

def z848 : W := mkw 0x03fb5bb6b0010280 0x00fed6edac0040a0 0xdffffffff8000fc3 0xf7fffffffe0003f0

def z849 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfbf0032007ff0fc2 0xbefc00c801ffc3f0

def z850 : W := mkw 0x01335926b0000000 0x004cd649ac000000 0xdc7ffffff8000003 0xf71ffffffe000000

def z851 : W := mkw 0x136fd800066ea000 0x04dbf600019ba800 0x93ff800007f70000 0x64ffe00001fdc000

def z852 : W := mkw 0x024c0000024c0000 0x0093000000930000 0xf3fc00f807ff0002 0xfcff003e01ffc000

def z853 : W := mkw 0x176ffc04c76ef011 0x85dbff0131dbbc04 0xf3fffc00c7fff001 0xfcffff0031fffc00

def z854 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfbfc030007ff0fc0 0xfeff00c001ffc3f0

def z855 : W := mkw 0x8adc03f80add0ec4 0x22b700fe02b743b1 0xfbfc03f83fff0fce 0xfeff00fe0fffc3f3

def z856 : W := mkw 0x0502e005c520c133 0x8140b8017148304c 0xef83e307c7f0cf33 0x7be0f8c1f1fc33cc

def z857 : W := mkw 0x8000004848800855 0x2000001212200215 0x640c7cf8f808f8ff 0xd9031f3e3e023e3f

def z858 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xbbf003f807ff0fc2 0x2efc00fe01ffc3f0

def z859 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0x93fffc0007ff3000 0xe4ffff0001ffcc00

def z860 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xfff3e3c7c7ffcf33 0xfffcf8f1f1fff3cc

def z861 : W := mkw 0x8adc03f84add0ed5 0x22b700fe12b743b5 0xfffc7ff8ffff0fff 0xffff1ffe3fffc3ff

def z862 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xbbfc03d807ff0fc0 0x6eff00f601ffc3f0

def z863 : W := mkw 0x136fd800066ea000 0x04dbf600019ba800 0xb3f3800007ff0000 0x2cfce00001ffc000

def z864 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0x6c0013f82008ffff 0x9b0004fe08023fff

def z865 : W := mkw 0x8adc03f84add0ed5 0x22b700fe12b743b5 0xfbfc03f807ff0ffe 0xfeff00fe01ffc3ff

def z866 : W := mkw 0x134e6c00036c5000 0x04d39b0000db1400 0x13fc6c0003ff0000 0xc4ff1b0000ffc000

def z867 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfffc7ff8ffffffff 0xffff1ffe3fffffff

def z868 : W := mkw 0x136f7c00036e7000 0x04dbdf0000db9c00 0xf3fc7c0007ff3000 0xfcff1f0001ffcc00

def z869 : W := mkw 0x136fd800066ea000 0x04dbf600019ba800 0xf3ff900007fff001 0xfcffe40001fffc00

def z870 : W := mkw 0x09b35bfeb0910ec0 0x026cd6ffac2443b0 0x0c03fffff8000fc3 0x0300fffffe0003f0

def z871 : W := mkw 0x089003f000910e80 0x022400fc002443a0 0x080003c000000f02 0x020000f0000003c0

def z872 : W := mkw 0x840424484bb85c55 0xa101091212ee1715 0x640c7cf8fbf8f8ff 0xd9031f3e3efe3e3f

def z873 : W := mkw 0x0a5c017802dd0ec0 0x0297005e00b743b0 0xf3fc003807ff0fc0 0xfcff000e01ffc3f0

def z874 : W := mkw 0x13fbdbb7b467a3aa 0x44fef6eded19e8ea 0x9bf3830704770700 0x26fce0c1c11dc1c0

def z875 : W := mkw 0x034e4000024c0000 0x00d3900000930000 0xf3ffe00007ff0001 0xfcfff80001ffc000

def z876 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf7fffcc0c7fff003 0xfdffff3031fffc00

def z877 : W := mkw 0x0c9003f5c0910fb3 0x832400fd702443ec 0x0c0003c7c0000f32 0x030000f1f00003cc

def z878 : W := mkw 0x02c802c000d40c00 0x00b200b000350300 0xfbf003c007f70f02 0x7efc00f001fdc3c0

def z879 : W := mkw 0x800424484b885855 0x2001091212e21615 0xf47c7cf8ff8ff8ff 0xfd1f1f3e3fe3fe3f

def z880 : W := mkw 0x8804a4494fdfffff 0x6201291253f7ffff 0x2000000007fffffc 0x0800000001ffffff

def z881 : W := mkw 0x0582c2c584b08d22 0x8160b0b1612c2348 0xef83e3c7c7f00f03 0x7be0f8f1f1fc03c0

def z882 : W := mkw 0x002190000402a000 0x000864000100a800 0xf3f3900007fff001 0xfcfce40001fffc00

def z883 : W := mkw 0x024c0000024c0000 0x0093000000930000 0xb3f0000007ff0000 0x2cfc000001ffc000

def z884 : W := mkw 0x127d1d32324f3288 0x449f474c8c93cca2 0x107c1c38380f30cc 0x841f070e0e03cc33

def z885 : W := mkw 0x0bfb5bb6b0540400 0x02fed6edac150100 0xdffffffff8700003 0xf7fffffffe1c0000

def z886 : W := mkw 0x0182e2c485b0cc00 0x0060b8b1216c3300 0xef83e3c7c7f0cf03 0x7be0f8f1f1fc33c0

def z887 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0x9bfffffff8000000 0xe6fffffffe000000

def z888 : W := mkw 0x089003feb0910ec0 0x022400ffac2443b0 0x080003ff00000fc2 0x020000ffc00003f0

def z889 : W := mkw 0x009003e000910e80 0x002400f8002443a0 0xfbf003c007f70f02 0x7efc00f001fdc3c0

def z890 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0x9fffeffff8000002 0x67fffbfffe000000

def z891 : W := mkw 0x8bce6edcdbdc5c55 0x22f39bb736f71715 0x038c6cd8dbf00000 0x40e31b3636fc0000

def z892 : W := mkw 0x0adc03b8025d06c0 0x02b700ee009741b0 0xfbfc033807ff07c0 0xfeff00ce01ffc1f0

def z893 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xfff3932727ffffff 0xfffce4c9c9ffffff

def z894 : W := mkw 0x0bfb5bb6b0550680 0x02fed6edac1541a0 0xfffffffffc7f0fc3 0xffffffffff1fc3f0

def z895 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0x0c0003f8f8000fc2 0x030000fe3e0003f0

def z896 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0x93fffc0007f7f001 0x64ffff0001fdfc00

def z897 : W := mkw 0x03fb5bb6b0010280 0x00fed6edac0040a0 0xdffffffffc070703 0xf7ffffffff01c1c0

def z898 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xfc7393fffc0fffff 0xbf1ce4ffff03ffff

def z899 : W := mkw 0x134e4800026c0000 0x04d39200009b0000 0xf3fc000007ff0000 0xfcff000001ffc000

def z900 : W := mkw 0x0123f0000522e000 0x0048fc000148b800 0xf3f3e00007f7c001 0x7cfcf80001fdf000

def z901 : W := mkw 0x019243b6b0000000 0x006490edac000000 0xcf8ffffff8000003 0xf3e3fffffe000000

def z902 : W := mkw 0x0aed92db26dead6a 0x42bb64b6c9b7ab5a 0x078f90df23f0f03d 0x41e3e437c8fc3c0f

def z903 : W := mkw 0x83ff7ffefb885855 0x20ffdfffbee21615 0xbbf383070388f8fc 0x2efce0c1c0e23e3f

def z904 : W := mkw 0x136ffc08076ef040 0x04dbff0201dbbc10 0xf3fffc3807fff0c1 0xfcffff0e01fffc30

def z905 : W := mkw 0x936bd8484ce6a855 0x24daf6121339aa15 0x97f380f8fc7708fe 0x25fce03e3f1dc23f

def z906 : W := mkw 0x000080010403a3aa 0x400020004100e8ea 0x640c7cf8fc0fffff 0xd9031f3e3f03ffff

def z907 : W := mkw 0x900424484bec5855 0x2401091212fb1615 0x640c7cf8fbf8f8ff 0xd9031f3e3efe3e3f

def z908 : W := mkw 0x025c016802cd0ac0 0x0097005a00b342b0 0xfbfc03f807ff0fc2 0xfeff00fe01ffc3f0

def z909 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf7fffc00fffff001 0xfdffff003ffffc00

def z910 : W := mkw 0x01b35bb6b0000000 0x006cd6edac000000 0x4c0ffffff8000003 0xd303fffffe000000

def z911 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xfffffffffc0f0003 0xffffffffff03c000

def z912 : W := mkw 0x027d1122224f2288 0x409f44488893c8a2 0x107c1020200f30cc 0x841f04080803cc33

def z913 : W := mkw 0x0582c2c584b08d22 0x8160b0b1612c2348 0xab83830707f00f00 0x2ae0e0c1c1fc03c0

def z914 : W := mkw 0x8404a4494fb8dd77 0xa101291253ee375d 0x2000000007f0cf30 0x0800000001fc33cc

def z915 : W := mkw 0x034ec000066c8000 0x00d3b000019b2000 0xf3ff800007ff0000 0xfcffe00001ffc000

def z916 : W := mkw 0x03fb5bb6b0032288 0x40fed6edac00c8a2 0xfffffffffc0f3fcf 0xffffffffff03cff3

def z917 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0x9bf0030007f70700 0x26fc00c001fdc1c0

def z918 : W := mkw 0x1a7d1d3a224f32c8 0x469f474e8893ccb2 0x107c1c38200f30cc 0x841f070e0803cc33

def z919 : W := mkw 0x134e6c00036c5000 0x04d39b0000db1400 0x93fc6c0007f70000 0x64ff1b0001fdc000

def z920 : W := mkw 0x07fb5bb6b0300400 0x81fed6edac0c0100 0xdffffffff8700003 0xf7fffffffe1c0000

def z921 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf7fffcf8fffff8ff 0xfdffff3e3ffffe3f

def z922 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0x9fffffdff8000001 0x67fffff7fe000000

def z923 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0x1c7ffffff8000003 0x871ffffffe000000

def z924 : W := mkw 0x0123f0032522e12a 0x4048fc00c948b84a 0x0403f0072000f03d 0x0100fc01c8003c0f

def z925 : W := mkw 0x089003fa30910ec0 0x022400fe8c2443b0 0x080003f838000fc2 0x020000fe0e0003f0

def z926 : W := mkw 0x8adc07f84add1ed5 0x22b701fe12b747b5 0xfffc1ff8ffff3ffe 0xffff07fe3fffcfff

def z927 : W := mkw 0x0ad803b000550680 0x02b600ec001541a0 0xfbf0030007f70700 0x7efc00c001fdc1c0

def z928 : W := mkw 0x0c9003fff0910ff3 0x832400fffc2443fc 0x0c0003fff8000ff2 0x030000fffe0003fc

def z929 : W := mkw 0x0bfb5bb6b0450280 0x02fed6edac1140a0 0xdffffffff8070003 0xf7fffffffe01c000

def z930 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xb3ff9c0007fff000 0xacffe70001fffc00

def z931 : W := mkw 0x134e6c00036c5000 0x04d39b0000db1400 0xf3fc7c0007fff001 0xfcff1f0001fffc00

def z932 : W := mkw 0x0102e0000520c000 0x0040b80001483000 0xf3f3e00007ffc001 0xfcfcf80001fff000

def z933 : W := mkw 0x008082c104908d22 0x002020b041242348 0xeb8383c707f00f02 0x7ae0e0f1c1fc03c0

def z934 : W := mkw 0x0a7d193a324d02c0 0x029f464e8c9340b0 0x107c0038000f00c0 0x841f000e0003c030

def z935 : W := mkw 0x034ae0000564c000 0x00d2b80001593000 0xf3f3e00007f7c001 0x7cfcf80001fdf000

def z936 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xb8739327240ffffc 0xae1ce4c9c903ffff

def z937 : W := mkw 0x136f5c00024e3000 0x04dbd70000938c00 0xf3fffc0007ff3001 0xfcffff0001ffcc00

def z938 : W := mkw 0x889003fb68910fff 0x622400feda2443ff 0x0c0003fff8000ffe 0x030000fffe0003ff

def z939 : W := mkw 0x800424484b885855 0x2001091212e21615 0xec0ffffffb88f8ff 0xfb03fffffee23e3f

def z940 : W := mkw 0x126d9c00064eb000 0x049b67000193ac00 0xf3ff9c0007fff001 0xfcffe70001fffc00

def z941 : W := mkw 0x036ff000076ee000 0x00dbfc0001dbb800 0xf3fff00007fff001 0xfcfffc0001fffc00

def z942 : W := mkw 0x0004240003085000 0x0001090000c21400 0x640c7cf8fb88f8ff 0xd9031f3e3ee23e3f

def z943 : W := mkw 0x1582e6c5c5b2fd33 0x8560b9b1716cbf4c 0xef83e3c7c7f0ff33 0x7be0f8f1f1fc3fcc

def z944 : W := mkw 0x0279193230000000 0x009e464c8c000000 0xdc7ffffff8000003 0xf71ffffffe000000

def z945 : W := mkw 0x03ca4a9490000000 0x00f292a524000000 0x8b8fefdfd8000000 0x62e3fbf7f6000000

def z946 : W := mkw 0x0582e285c530c533 0x8160b8a1714c314c 0xef83e307c7f0c731 0x7be0f8c1f1fc31cc

def z947 : W := mkw 0x176ffc07f76ef133 0x85dbff01fddbbc4c 0xf7fffc07fffff031 0xfdffff01fffffc0c

def z948 : W := mkw 0x134eec00076ef000 0x04d3bb0001dbbc00 0xf3fc6c0007fff000 0xfcff1b0001fffc00

def z949 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0x9bfc03f807f70fc2 0x66ff00fe01fdc3f0

def z950 : W := mkw 0x089003fb20910fea 0x422400fec82443fa 0x080003ff00000fc2 0x020000ffc00003f0

def z951 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xbc739307240ffffd 0x2f1ce4c1c903ffff

def z952 : W := mkw 0x089403e802dd0ec0 0x022500fa00b743b0 0xfbf003e007ff0fc2 0xfefc00f801ffc3f0

def z953 : W := mkw 0x026d1800024c0000 0x009b460000930000 0xf3fc1c0007ff0000 0xfcff070001ffc000

def z954 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef83830707f0cf33 0x3be0e0c1c1fc33cc

def z955 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xfffffffff800c833 0xfffffffffe00320c

def z956 : W := mkw 0x0582e2858530c522 0x8160b8a1614c3148 0xef83e3c7c7f0c703 0x7be0f8f1f1fc31c0

def z957 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xeb83e3c7c7f00f02 0x7ae0f8f1f1fc03c0

def z958 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xfc73f3e7e40fffff 0xff1cfcf9f903ffff

def z959 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0xfbf003f807ff0fc2 0xfefc00fe01ffc3f0

def z960 : W := mkw 0x036b5806b0000000 0x00dad601ac000000 0xd7fffcfff8000003 0xf5ffff3ffe000000

def z961 : W := mkw 0x800424484bcc5855 0x2001091212f31615 0x640c7cf8fffff8ff 0xd9031f3e3ffffe3f

def z962 : W := mkw 0x0adc03f002dd0e80 0x02b700fc00b743a0 0xfbfc03c007ff0f02 0xfeff00f001ffc3c0

def z963 : W := mkw 0x16ed1ec5c2de3d33 0x85bb47b170b78f4c 0x1c7c1fc7c00f3f32 0x871f07f1f003cfcc

def z964 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xaf8383c7c7f0cf32 0x2be0e0f1f1fc33cc

def z965 : W := mkw 0x9523fc05cd22f137 0xa548ff017348bc4d 0x0403fc07f800f03d 0x0100ff01fe003c0f

def z966 : W := mkw 0x8582e2cdcdb0cd77 0xa160b8b3736c335d 0xef83e3dfdff0cf33 0x7be0f8f7f7fc33cc

def z967 : W := mkw 0x136ffc10176ef000 0x04dbff0405dbbc00 0xf3fffc181ffff001 0xfcffff0607fffc00

def z968 : W := mkw 0x03eb5a96b0000000 0x00fad6a5ac000000 0xd7fffcdff8000001 0xf5ffff37fe000000

def z969 : W := mkw 0x136ffc07b76ef12a 0x44dbff01eddbbc4a 0xf7fffc07fffff03d 0xfdffff01fffffc0f

def z970 : W := mkw 0x8582e6c5cdb0dd37 0xa160b9b1736c374d 0xef8ffffffff0ff3f 0xfbe3fffffffc3fcf

def z971 : W := mkw 0x089003fa20910ec0 0x022400fe882443b0 0x0c0003ff20000fc2 0x030000ffc80003f0

def z972 : W := mkw 0x03fb5bb6b0010280 0x00fed6edac0040a0 0xdffffffff80f00c3 0xf7fffffffe03c030

def z973 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xffff83ff07ff0fc3 0xffffe0ffc1ffc3f0

def z974 : W := mkw 0x936ffc036f6ef13f 0x64dbff00dbdbbc4f 0xf7fffc07fffff03d 0xfdffff01fffffc0f

def z975 : W := mkw 0x001081210403a3aa 0x400420484100e8ea 0xfc738327040fffff 0xbf1ce0c9c103ffff

def z976 : W := mkw 0x0adc03feb2dd0ec0 0x02b700ffacb743b0 0xfbfc03ff07ff0fc2 0xfeff00ffc1ffc3f0

def z977 : W := mkw 0x024c0000024c0000 0x0093000000930000 0xf7fc7cf8ffff0003 0xfdff1f3e3fffc000

def z978 : W := mkw 0x8582e2cdcdb0cd77 0xa160b8b3736c335d 0xef83f3fffff8ffff 0xfbe0fcfffffe3fff

def z979 : W := mkw 0x889003f848910ed5 0x222400fe122443b5 0x080003f800000ffe 0x020000fe000003ff

def z980 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xdffffffff80008ff 0xf7fffffffe00023f

def z981 : W := mkw 0x0182c2c584908d22 0x0060b0b161242348 0xef83e3c7c7f0cf33 0x7be0f8f1f1fc33cc

def z982 : W := mkw 0x03fb5bb6b0022008 0x40fed6edac008802 0xdffffffff800300f 0xf7fffffffe000c03

def z983 : W := mkw 0x089003fc90910ec0 0x022400ff242443b0 0x080003f8d8000fc2 0x020000fe360003f0

def z984 : W := mkw 0x01235806b0000000 0x0048d601ac000000 0x040ffcdff8000001 0x4103ff37fe000000

def z985 : W := mkw 0x8a7d1d3a3a4d12c4 0x229f474e8e9344b1 0x107c1c38380f30cc 0x841f070e0e03cc33

def z986 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xfc7fff27240fffff 0xff1fffc9c903ffff

def z987 : W := mkw 0x0010012000010280 0x00040048000040a0 0xfbf0032007ff0fc2 0xfefc00c801ffc3f0

def z988 : W := mkw 0x135e6d23236d53aa 0x44d79b48c8db54ea 0x0f8c6f2723f00ffe 0x43e31bc9c8fc03ff

def z989 : W := mkw 0x02d803f000910e80 0x00b600fc002443a0 0xfbfc03f807ff0fc2 0xfeff00fe01ffc3f0

def z990 : W := mkw 0x0adc03b0025d0680 0x02b700ec009741a0 0xfbfc03f807ff0702 0xfeff00fe01ffc1c0

def z991 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef8ffffffff8ffff 0xfbe3fffffffe3fff

def z992 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xfffffffffff00003 0xfffffffffffc0000

def z993 : W := mkw 0x0523f007e522e13b 0xc148fc01f948b84e 0xf7f3f007e7fff03d 0xfdfcfc01f9fffc0f

def z994 : W := mkw 0x0582e2cdc5b0cd73 0x8160b8b3716c335c 0xef83e3ffc7f0cff3 0x7be0f8fff1fc33fc

def z995 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfbfc03d807f70f02 0x7eff00f601fdc3c0

def z996 : W := mkw 0x008002c000900c00 0x002000b000240300 0xfbf003c007ff0f02 0xfefc00f001ffc3c0

def z997 : W := mkw 0x126dbc00076ef000 0x049b6f0001dbbc00 0xf3fc1c0007fff000 0xfcff070001fffc00

def z998 : W := mkw 0x124c0400024e3000 0x0493010000938c00 0xf3fc000007ff3000 0xfcff000001ffcc00

def z999 : W := mkw 0x036f7c00034c5000 0x00dbdf0000d31400 0xf3fffc0007fff001 0xfcffff0001fffc00

def z1000 : W := mkw 0x0502e04145b0cd33 0x8140b810516c334c 0xef83e30707f0cf33 0x7be0f8c1c1fc33cc

def z1001 : W := mkw 0x13fb5bb6b0640000 0x04fed6edac190000 0xdffffffff8700003 0xf7fffffffe1c0000

def z1002 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0x0f8ffffff8000003 0x43e3fffffe000000

def z1003 : W := mkw 0x0000800104008122 0x0000200041002048 0xef83830707f0cf33 0x7be0e0c1c1fc33cc

def z1004 : W := mkw 0x136ffc01076ef122 0x04dbff0041dbbc48 0xfbffff0707fff701 0xfeffffc1c1fffdc0

def z1005 : W := mkw 0x800424484b885855 0x2001091212e21615 0x040c7cf8fb80f8ff 0x41031f3e3ee03e3f

def z1006 : W := mkw 0x19b3fff805b3fec0 0x066cfffe016cffb0 0x0803fff80000ffc3 0x0200fffe00003ff0

def z1007 : W := mkw 0x036f5806b24c0000 0x00dbd601ac930000 0xf7fffc07ffff0001 0xfdffff01ffffc000

def z1008 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef8fffc7c7f0cf33 0xfbe3fff1f1fc33cc

def z1009 : W := mkw 0x036fd800064ea000 0x00dbf6000193a800 0xf3fffc0007fff001 0xfcffff0001fffc00

def z1010 : W := mkw 0x849003efe8910fff 0xe12400fbfa2443ff 0x0c0003fff8000ffe 0x030000fffe0003ff

def z1011 : W := mkw 0x0adc03fc82dd0ec0 0x02b700ff20b743b0 0xfffc03ffc7ff0fc2 0xffff00fff1ffc3f0

def z1012 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0x080c03f800000fc2 0x020300fe000003f0

def z1013 : W := mkw 0x136bf8000566e000 0x04dafe000159b800 0xf3fffc0007f7c001 0xfcffff0001fdf000

def z1014 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef83ffc7fff0cf33 0x7be0fff1fffc33cc

def z1015 : W := mkw 0x024c0000024c0000 0x0093000000930000 0xf3fc7c0007ff0001 0xfcff1f0001ffc000

def z1016 : W := mkw 0x0582e2c5c5b2ed33 0x8160b8b1716cbb4c 0xef83e3c7c7ffff33 0x7be0f8f1f1ffffcc

def z1017 : W := mkw 0x136ffc06b76ef000 0x04dbff01addbbc00 0xf3fffc0707fff001 0xfcffff01c1fffc00

def z1018 : W := mkw 0x026d9003264ea12a 0x409b6400c993a84a 0xf7ff900727fff03d 0xfdffe401c9fffc0f

def z1019 : W := mkw 0x0adc03fa32dd0ec0 0x02b700fe8cb743b0 0xfbfc03f83fff0fc2 0xfeff00fe0fffc3f0

def z1020 : W := mkw 0x0c9003ffe0910ffb 0xc32400fff82443fe 0x0c0003ffe0000ffe 0x030000fff80003ff

def z1021 : W := mkw 0x024c0000024c0000 0x0093000000930000 0xf7fc102027fff8ff 0xfdff040809fffe3f

def z1022 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xfffffffffc000f03 0xffffffffff0003c0

def z1023 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xdbffefffd8000002 0xf6fffbfff6000000

def z1024 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfbf003c007ff0fc2 0x7efc00f001ffc3f0

def z1025 : W := mkw 0x936ffc004f6ef015 0x24dbff0013dbbc05 0xf3fffc0007fff03d 0xfcffff0001fffc0f

def z1026 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xcf83e3c7c7f00703 0x73e0f8f1f1fc01c0

def z1027 : W := mkw 0x0000000000000000 0x0000000000000000 0xf3f0000007ff0000 0xfcfc000001ffc000

def z1028 : W := mkw 0x0adc03f842dd0ed1 0x02b700fe10b743b4 0xfffc03f8c7ff0ff2 0xffff00fe31ffc3fc

def z1029 : W := mkw 0x0182e2858520c122 0x0060b8a161483048 0xef83e3c7c7f0cf33 0x7be0f8f1f1fc33cc

def z1030 : W := mkw 0x0acc02c802dd0ec0 0x02b300b200b743b0 0xfbfc03c007ff0fc2 0xfeff00f001ffc3f0

def z1031 : W := mkw 0x018242c480900c00 0x006090b120240300 0xeb8383c707f00f02 0x7ae0e0f1c1fc03c0

def z1032 : W := mkw 0x8582e6cdcdb0dd77 0xa160b9b3736c375d 0xef83fffffff0ffff 0x7be0fffffffc3fff

def z1033 : W := mkw 0x03fb5bb6b0010280 0x00fed6edac0040a0 0xfffffffffc0fffff 0xffffffffff03ffff

def z1034 : W := mkw 0x0582e2d5d5b0cd33 0x8160b8b5756c334c 0xef83e3dfdff0cf33 0x7be0f8f7f7fc33cc

def z1035 : W := mkw 0x1582eec5c5b0dd33 0x8560bbb1716c374c 0xef83efc7c7f0cf33 0x7be0fbf1f1fc33cc

def z1036 : W := mkw 0x0021100220000000 0x0008440088000000 0x440ffcfff8000003 0xd103ff3ffe000000

def z1037 : W := mkw 0x03eb5a96b0000000 0x00fad6a5ac000000 0xcf8fffdff8000003 0x73e3fff7fe000000

def z1038 : W := mkw 0x0582c2c584b08d22 0x8160b0b1612c2348 0xef8383c707f0cf33 0x7be0e0f1c1fc33cc

def z1039 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf3f3900007fff001 0xbcfce40001fffc00

def z1040 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0x000000f8000000c0 0x0000003e00000030

def z1041 : W := mkw 0x0adc03b0025d0680 0x02b700ec009741a0 0xfbfc032007ff0fc2 0xfeff00c801ffc3f0

def z1042 : W := mkw 0x0a7d193a324f22c8 0x429f464e8c93c8b2 0x107c1c38380f30cc 0x841f070e0e03cc33

def z1043 : W := mkw 0x126d1800024e2000 0x049b460000938800 0xf3fc000007ff0000 0xfcff000001ffc000

def z1044 : W := mkw 0x02dc03e002dd0e80 0x00b700f800b743a0 0xfbfc03e007ff0fc2 0xfeff00f801ffc3f0

def z1045 : W := mkw 0x0a4c004802dd0ec0 0x0293001200b743b0 0xf3fc00f807ff0fc2 0xfcff003e01ffc3f0

def z1046 : W := mkw 0x176ffc07e76ef13b 0xc5dbff01f9dbbc4e 0xf7fffc07e7fff03d 0xfdffff01f9fffc0f

def z1047 : W := mkw 0x089003fc80910ec0 0x022400ff202443b0 0x0c0003ffc0000fc2 0x030000fff00003f0

def z1048 : W := mkw 0x1523fc07f522f133 0x8548ff01fd48bc4c 0x0403fc07f800f031 0x0100ff01fe003c0c

def z1049 : W := mkw 0x936ffc080f6ef044 0x24dbff0203dbbc11 0xf7fffcf8fffff0cf 0xfdffff3e3ffffc33

def z1050 : W := mkw 0x124ca400076ef000 0x0493290001dbbc00 0xf3fc7c0007fff001 0xfcff1f0001fffc00

def z1051 : W := mkw 0x800404080a081044 0x2001010202820411 0x640c7cf8f808f8ff 0xd9031f3e3e023e3f

def z1052 : W := mkw 0x089003f900910fea 0x422400fe402443fa 0x080003f800000ffe 0x020000fe000003ff

def z1053 : W := mkw 0x8004a4494f88d977 0x2001291253e2365d 0x200000000788fffc 0x0800000001e23fff

def z1054 : W := mkw 0x136ffc03276ef12a 0x44dbff00c9dbbc4a 0xf7fffc2727fff8ff 0xfdffff09c9fffe3f

def z1055 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0x4c0c7ff8f8000fc3 0xd3031ffe3e0003f0

def z1056 : W := mkw 0x8adc03fefadd0ed5 0x22b700ffbeb743b5 0xfffc03ffffff0ffe 0xffff00ffffffc3ff

def z1057 : W := mkw 0x089003f900910fe2 0x022400fe402443f8 0x0c0003ff00000ff2 0x030000ffc00003fc

def z1058 : W := mkw 0x034e6000036c4000 0x00d3980000db1000 0xf3fc600007ff0000 0xfcff180001ffc000

def z1059 : W := mkw 0x8adc03f84add0ed5 0x22b700fe12b743b5 0xfbfc03f8dfff0fc2 0xfeff00fe37ffc3f0

def z1060 : W := mkw 0x008002c000900c00 0x002000b000240300 0xef8383c707f00f03 0x7be0e0f1c1fc03c0

def z1061 : W := mkw 0x0480a2c145b0cd33 0x812028b0516c334c 0xef8383c707f0cf33 0x7be0e0f1c1fc33cc

def z1062 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0x0c0003f820000ffe 0x030000fe080003ff

def z1063 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef8fe3ffc7f0cf33 0xfbe3f8fff1fc33cc

def z1064 : W := mkw 0x8582e2c5cdb0cd37 0xa160b8b1736c334d 0xef83e3c7fff0cf3f 0x7be0f8f1fffc33cf

def z1065 : W := mkw 0x0a4c004802dd0ec0 0x0293001200b743b0 0xb3f0000007ff0fc0 0x2cfc000001ffc3f0

def z1066 : W := mkw 0x9004a4494feffbff 0x6401291253fbfeff 0x2000000007fffffc 0x0800000001ffffff

def z1067 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xdbffffdfd8000001 0xf6fffff7f6000000

def z1068 : W := mkw 0x97ce6ecccbfc5c55 0xa5f39bb332ff1715 0x038c6cd8dbf00000 0x40e31b3636fc0000

def z1069 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef83e3fffff0cf33 0x7be0f8fffffc33cc

def z1070 : W := mkw 0x058262c4c1b04c11 0x816098b1306c1304 0xef83e3c7c7f00f03 0x7be0f8f1f1fc03c0

def z1071 : W := mkw 0x009003e000910e80 0x002400f8002443a0 0x080003e000000fc2 0x020000f8000003f0

def z1072 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xdfffefdfd8000003 0x77fffbf7f6000000

def z1073 : W := mkw 0x08b193fb2493afea 0x422c64fec924ebfa 0x0c0393ff2000ffff 0x0300e4ffc8003fff

def z1074 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf3fffcf807fff003 0xfcffff3e01fffc00

def z1075 : W := mkw 0x089003f840910ed1 0x022400fe102443b4 0x0c0003f8c0000ff2 0x030000fe300003fc

def z1076 : W := mkw 0x936ffc080f6ef044 0x24dbff0203dbbc11 0xf3fffc181ffff001 0xfcffff0607fffc00

def z1077 : W := mkw 0x036ff800076cc000 0x00dbfe0001db3000 0xf3fffc0007ffc001 0xfcffff0001fff000

def z1078 : W := mkw 0x024c004002dc0c00 0x0093001000b70300 0xf3fc000007ff0f00 0xfcff000001ffc3c0

def z1079 : W := mkw 0x01a35a86b0000000 0x0068d6a1ac000000 0xcf8ffffff8000003 0xf3e3fffffe000000

def z1080 : W := mkw 0x024c0008024c0040 0x0093000200930010 0xf3fc003807ff00c0 0xfcff000e01ffc030

def z1081 : W := mkw 0x136ffc01076ef122 0x04dbff0041dbbc48 0xf7fffc0707fff031 0xfdffff01c1fffc0c

def z1082 : W := mkw 0x136fd800066ea000 0x04dbf600019ba800 0xf3fffc0007ff0001 0xfcffff0001ffc000

def z1083 : W := mkw 0x1123fc032522f12a 0x4448ff00c948bc4a 0x0003fc070000f001 0x0000ff01c0003c00

def z1084 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf3f3e00007fff001 0x7cfcf80001fffc00

def z1085 : W := mkw 0x0adc03fa22dd0ec0 0x02b700fe88b743b0 0xfffc03ff27ff0fc2 0xffff00ffc9ffc3f0

def z1086 : W := mkw 0x126d1c00024e3000 0x049b470000938c00 0x13fc1c0003ff3000 0xc4ff070000ffcc00

def z1087 : W := mkw 0x8582e2cdcdb0cd77 0xa160b8b3736c335d 0xef83e3c7c7f0cfff 0x7be0f8f1f1fc33ff

def z1088 : W := mkw 0x126d3c00034e7000 0x049b4f0000d39c00 0xf3fc7c0007fff001 0xfcff1f0001fffc00

def z1089 : W := mkw 0x136f7c00036e7000 0x04dbdf0000db9c00 0xd3fffc0003ff3001 0xf4ffff0000ffcc00

def z1090 : W := mkw 0x03ca4a9490000000 0x00f292a524000000 0xcf8ffffff8000003 0xf3e3fffffe000000

def z1091 : W := mkw 0x0c9003f940910ff3 0x832400fe502443fc 0x080003f800000ff2 0x020000fe000003fc

def z1092 : W := mkw 0x026d9000064ea000 0x009b64000193a800 0xf3ff800007ff0000 0xfcffe00001ffc000

def z1093 : W := mkw 0x800424484b885855 0x2001091212e21615 0xe78c7cf8fff8f8ff 0xf9e31f3e3ffe3e3f

def z1094 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xfc73ff27fc0fffff 0xbf1cffc9ff03ffff

def z1095 : W := mkw 0x024c8000064c8000 0x0093200001932000 0xf3ff800007ffc001 0xfcffe00001fff000

def z1096 : W := mkw 0x037b5936b0000000 0x00ded64dac000000 0x547ffcfff8000003 0xd51fff3ffe000000

def z1097 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf3fffc0007fff8fd 0xfcffff0001fffe3f

def z1098 : W := mkw 0x0adc03fc92dd0ec0 0x02b700ff24b743b0 0xfbfc03f8dfff0fc2 0xfeff00fe37ffc3f0

def z1099 : W := mkw 0x8adc03f84add0ed5 0x22b700fe12b743b5 0xfffc13f8ffffffff 0xffff04fe3fffffff

def z1100 : W := mkw 0x07fbdbb7b433a7aa 0xc1fef6eded0ce9ea 0x9bf3830704770700 0x26fce0c1c11dc1c0

def z1101 : W := mkw 0x824c04080a4c1044 0x2093010202930411 0xf3fc1c383fff30cc 0xfcff070e0fffcc33

def z1102 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf3fffc383ffff001 0xfcffff0e0ffffc00

def z1103 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0x33fc00f807ff0fc0 0xccff003e01ffc3f0

def z1104 : W := mkw 0x0adc03b0025d0680 0x02b700ec009741a0 0x9bfc030007f70700 0x66ff00c001fdc1c0

def z1105 : W := mkw 0x02dc03f002dc0c00 0x00b700fc00b70300 0xfbfc03f807ff0f02 0xfeff00fe01ffc3c0

def z1106 : W := mkw 0x003199233403a3aa 0x400c6648cd00e8ea 0xfc739f273c0fffff 0xbf1ce7c9cf03ffff

def z1107 : W := mkw 0x002190010402a122 0x000864004100a848 0xfc739327240fffff 0xbf1ce4c9c903ffff

def z1108 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf3ff800007fff000 0xfcffe00001fffc00

def z1109 : W := mkw 0x089003fa20910ec8 0x422400fe882443b2 0x080003f820000fce 0x020000fe080003f3

def z1110 : W := mkw 0x176ffc01476ef133 0x85dbff0051dbbc4c 0xf3fffc0007fff031 0xfcffff0001fffc0c

def z1111 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xfbffff0007ffff03 0xfeffffc001ffffc0

def z1112 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xdffffffff800f03f 0xf7fffffffe003c0f

def z1113 : W := mkw 0x824c24004b4c5015 0x2093090012d31405 0xf7fc7c00fffff03d 0xfdff1f003ffffc0f

def z1114 : W := mkw 0x0ad803f000d50e80 0x02b600fc003543a0 0xfbf003e007ff0fc2 0xfefc00f801ffc3f0

def z1115 : W := mkw 0x03da4bb490000000 0x00f692ed24000000 0xdfffefffd8000003 0xf7fffbfff6000000

def z1116 : W := mkw 0x036bf8000522e000 0x00dafe000148b800 0xf3fffc0007fff001 0xfcffff0001fffc00

def z1117 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xfffffffff80808c3 0xfffffffffe020230

def z1118 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfbfc13f807ffffc3 0xfeff04fe01fffff0

def z1119 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0x480c03f800000fc2 0xd20300fe000003f0

def z1120 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfbfc13f827ff3fce 0xfeff04fe09ffcff3

def z1121 : W := mkw 0x049003e5c0910fb3 0x812400f9702443ec 0x0c0003e7c0000ff2 0x030000f9f00003fc

def z1122 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0x8f83e3c7c7f00f32 0x63e0f8f1f1fc03cc

def z1123 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xaf83e307c7f0cf31 0x2be0f8c1f1fc33cc

def z1124 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xeb8383c707f0cf32 0x7ae0e0f1c1fc33cc

def z1125 : W := mkw 0x048082c5c4908d33 0x812020b17124234c 0xef8383c7c7f0cf33 0x7be0e0f1f1fc33cc

def z1126 : W := mkw 0x0582e2858530c522 0x8160b8a1614c3148 0xab83830707f0c700 0x2ae0e0c1c1fc31c0

def z1127 : W := mkw 0x0000204041804811 0x0000081010601204 0x640c7cf8fb88f8ff 0xd9031f3e3ee23e3f

def z1128 : W := mkw 0x034e4800024c0000 0x00d3920000930000 0xf3fc6c0007ff0000 0xfcff1b0001ffc000

def z1129 : W := mkw 0x936ffc080f6ef044 0x24dbff0203dbbc11 0xf7fffc383ffff8ff 0xfdffff0e0ffffe3f

def z1130 : W := mkw 0x8404a4494fa8d977 0xa101291253ea365d 0x200000000388f8fc 0x0800000000e23e3f

def z1131 : W := mkw 0x136ffc01076ef12a 0x44dbff0041dbbc4a 0xf3fffc0007fff03d 0xfcffff0001fffc0f

def z1132 : W := mkw 0x009403e802990ec0 0x002500fa00a643b0 0xfbfc03f807ff0fc2 0xfeff00fe01ffc3f0

def z1133 : W := mkw 0x089003ffb0910fea 0x422400ffec2443fa 0x0c0003fff8000ffe 0x030000fffe0003ff

def z1134 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0x9bfc03f807ff07c0 0xe6ff00fe01ffc1f0

def z1135 : W := mkw 0x024ca000076cc000 0x0093280001db3000 0xf3fc000007ffc000 0xfcff000001fff000

def z1136 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0x33fc7c0007fff000 0xccff1f0001fffc00

def z1137 : W := mkw 0x927d1d2a2a4f32cc 0x649f474a8a93ccb3 0x107c1c38380f30cc 0x841f070e0e03cc33

def z1138 : W := mkw 0x024c8001064c8122 0x0093200041932048 0xffff830707ffcf33 0xffffe0c1c1fff3cc

def z1139 : W := mkw 0x0582c2c584b08d22 0x8160b0b1612c2348 0x8b8383c707f00700 0x62e0e0f1c1fc01c0

def z1140 : W := mkw 0x0adc03b0025d0680 0x02b700ec009741a0 0xbbf0030007ff0700 0x2efc00c001ffc1c0

def z1141 : W := mkw 0x1123fc010522f122 0x0448ff004148bc48 0x0403fc070000f031 0x0100ff01c0003c0c

def z1142 : W := mkw 0x01b353a6a0000000 0x006cd4e9a8000000 0xdffffffff8000003 0xf7fffffffe000000

def z1143 : W := mkw 0x124c8000066ea000 0x04932000019ba800 0xf3fc000007ff0000 0xfcff000001ffc000

def z1144 : W := mkw 0x1b6ffc18076ef040 0x06dbff0601dbbc10 0xf3fffc1807fff001 0xfcffff0601fffc00

def z1145 : W := mkw 0x1523fc07e522f13b 0xc548ff01f948bc4e 0x0403fc07e000f03d 0x0100ff01f8003c0f

def z1146 : W := mkw 0x8fce66dccbfc5c55 0xa3f399b732ff1715 0x038c6cd8dbf00000 0x40e31b3636fc0000

def z1147 : W := mkw 0x0ad803f800d50ec0 0x02b600fe003543b0 0xfbf003f807f70fc2 0x7efc00fe01fdc3f0

def z1148 : W := mkw 0x02cc0280025c0400 0x00b300a000970100 0xfbfc030007ff0700 0xfeff00c001ffc1c0

def z1149 : W := mkw 0x936ffc000f6ef004 0x24dbff0003dbbc01 0xf3fffc003ffff00d 0xfcffff000ffffc03

def z1150 : W := mkw 0x136f7c00036c5000 0x04dbdf0000db1400 0xf3fffc0007ff0001 0xfcffff0001ffc000

def z1151 : W := mkw 0x8adc07f80add1ec4 0x22b701fe02b747b1 0xfbfc03f807ff3fce 0xfeff00fe01ffcff3

def z1152 : W := mkw 0x136bfc000566f000 0x04daff000159bc00 0xf3f3fc0007f7f001 0x7cfcff0001fdfc00

def z1153 : W := mkw 0x0004004802880840 0x0001001200a20210 0x640c7cf8fb88f8ff 0xd9031f3e3ee23e3f

def z1154 : W := mkw 0x0a5c0138024d02c0 0x0297004e009340b0 0xfbfc033807ff0fc2 0xfeff00ce01ffc3f0

def z1155 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf7fffc0027fff03d 0xfdffff0009fffc0f

def z1156 : W := mkw 0x8404a4494fbbffff 0xe101291253eeffff 0x2000000007fffffc 0x0800000001ffffff

def z1157 : W := mkw 0x03da43b480000000 0x00f690ed20000000 0xdffffffff8000003 0xf7fffffffe000000

def z1158 : W := mkw 0x0523f807f522e13b 0xc148fe01fd48b84e 0x0403fc07f800f03d 0x0100ff01fe003c0f

def z1159 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0x680003f800080fc2 0x9a0000fe000203f0

def z1160 : W := mkw 0x03eb5a96b0000000 0x00fad6a5ac000000 0x038fecdfd8000000 0x40e3fb37f6000000

def z1161 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf7fffc0007fff833 0xfdffff0001fffe0c

def z1162 : W := mkw 0x0a7d113a224d02c0 0x029f444e889340b0 0x107c1038200f00c0 0x841f040e0803c030

def z1163 : W := mkw 0x936ffc080f6ef044 0x24dbff0203dbbc11 0xf3fffc0007fff0cd 0xfcffff0001fffc33

def z1164 : W := mkw 0x034ee400076cd000 0x00d3b90001db3400 0xf3fffc0007fff001 0xfcffff0001fffc00

def z1165 : W := mkw 0x0ad803f000d50e80 0x02b600fc003543a0 0x9bf003c007f70700 0x66fc00f001fdc1c0

def z1166 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef83f3c7c7f8ff33 0xfbe0fcf1f1fe3fcc

def z1167 : W := mkw 0x0582e2858530c522 0x8160b8a1614c3148 0xef83e30707f0cf33 0x7be0f8c1c1fc33cc

def z1168 : W := mkw 0x889003f848910ed5 0x222400fe122443b5 0x080003f8d8000fc2 0x020000fe360003f0

def z1169 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xfc7f93ff240fffff 0xff1fe4ffc903ffff

def z1170 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf3fffcd8dffff001 0xfcffff3637fffc00

def z1171 : W := mkw 0x037b592220000000 0x00ded64888000000 0xdffffffff8000003 0xf7fffffffe000000

def z1172 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfffc03f827ff0ffe 0xffff00fe09ffc3ff

def z1173 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef8fefdfdff0cf33 0x7be3fbf7f7fc33cc

def z1174 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef83e3e7c7f8cff3 0xfbe0f8f9f1fe33fc

def z1175 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xf8738327040ffffe 0xbe1ce0c9c103ffff

def z1176 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0x17fffcfff8000001 0xc5ffff3ffe000000

def z1177 : W := mkw 0x1adc0ff802dd1ec0 0x06b703fe00b747b0 0xfbfc0ff807ff0fc2 0xfeff03fe01ffc3f0

def z1178 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfbfc1ff83fff0fc2 0xfeff07fe0fffc3f0

def z1179 : W := mkw 0x0582c2c5c4b08d33 0x8160b0b1712c234c 0xef8383c7c7f00f32 0x7be0e0f1f1fc03cc

def z1180 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xef83e3c7c7f8ffff 0x7be0f8f1f1fe3fff

def z1181 : W := mkw 0x049003e7e0910fbb 0xc12400f9f82443ee 0x0c0003c7c0000f32 0x030000f1f00003cc

def z1182 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfffc03f8ffff0fc2 0xffff00fe3fffc3f0

def z1183 : W := mkw 0x009003e320910faa 0x402400f8c82443ea 0x0c0003e720000ffe 0x030000f9c80003ff

def z1184 : W := mkw 0x0c9003fd80910fe2 0x832400ff602443f8 0x080003ff00000fc2 0x020000ffc00003f0

def z1185 : W := mkw 0x0582e2c585b0cd22 0x8160b8b1616c3348 0xeb83e3c707f0cf03 0x7ae0f8f1c1fc33c0

def z1186 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfbfc03d807ff0700 0xfeff00f601ffc1c0

def z1187 : W := mkw 0x05b3f3e7e5b3efbb 0xc16cfcf9f96cfbee 0x0c03f3e7e000ffff 0x0300fcf9f8003fff

def z1188 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0xeb83e3c7c7f0c701 0x7ae0f8f1f1fc31c0

def z1189 : W := mkw 0x0a4c0000025d0680 0x02930000009741a0 0xf3fc000007ff0700 0xfcff000001ffc1c0

def z1190 : W := mkw 0x8adc07f80add1ec4 0x22b701fe02b747b1 0xfbfc0ff81fff0fc2 0xfeff03fe07ffc3f0

def z1191 : W := mkw 0x136ffc04876ef000 0x04dbff0121dbbc00 0xf7fffc07c7fff001 0xfdffff01f1fffc00

def z1192 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xbbfc033807ff0fc0 0xaeff00ce01ffc3f0

def z1193 : W := mkw 0x003191232403a3aa 0x400c6448c900e8ea 0xfc738307040fffff 0x3f1ce0c1c103ffff

def z1194 : W := mkw 0x126db400076ef000 0x049b6d0001dbbc00 0xf3ff900007fff001 0xfcffe40001fffc00

def z1195 : W := mkw 0x089003f800910ec0 0x022400fe002443b0 0xe80003f804000fc2 0x3a0000fe010003f0

def z1196 : W := mkw 0x0a7d113a224f22c8 0x429f444e8893c8b2 0x107c0038000f00c0 0x841f000e0003c030

def z1197 : W := mkw 0x0a5c016802dd0ec0 0x0297005a00b743b0 0xfbfc032007ff0fc2 0xfeff00c801ffc3f0

def z1198 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfbfc03f807fffffe 0xfeff00fe01ffffff

def z1199 : W := mkw 0x0adc03fa22dd0ec8 0x42b700fe88b743b2 0xfbfc03f827ff0fce 0xfeff00fe09ffc3f3

def z1200 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf3ffec0007f7c001 0x7cfffb0001fdf000

def z1201 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfffc63f8c7ff0fc3 0xffff18fe31ffc3f0

def z1202 : W := mkw 0x1523fc014522f133 0x8548ff005148bc4c 0x0003fc000000f031 0x0000ff0000003c0c

def z1203 : W := mkw 0x026d1000024c0000 0x009b440000930000 0xf3ff900007ff0001 0xfcffe40001ffc000

def z1204 : W := mkw 0x058262c5c1b04d33 0x816098b1706c134c 0xcf83e3c7c3f00f33 0x73e0f8f1f0fc03cc

def z1205 : W := mkw 0x0acc02d802dd0ec0 0x02b300b600b743b0 0xf3fc00d807ff0fc0 0xfcff003601ffc3f0

def z1206 : W := mkw 0x8582e2cdcdb0cd77 0xa160b8b3736c335d 0xef8ffffffff0cfff 0xfbe3fffffffc33ff

def z1207 : W := mkw 0x0182428480000000 0x006090a120000000 0xcf8fefdfd8000003 0x73e3fbf7f6000000

def z1208 : W := mkw 0x024c2400034c5000 0x0093090000d31400 0xf3fc000007fff000 0xfcff000001fffc00

def z1209 : W := mkw 0x176ffc05876ef122 0x85dbff0161dbbc48 0xf3fffc0707fff001 0xfcffff01c1fffc00

def z1210 : W := mkw 0x03fb5bb6b0032288 0x40fed6edac00c8a2 0xdffffffff8070003 0xf7fffffffe01c000

def z1211 : W := mkw 0x03fb5bb6b0010288 0x40fed6edac0040a2 0xdffffffff80000cf 0xf7fffffffe000033

def z1212 : W := mkw 0x936ffc06ff6ef015 0x24dbff01bfdbbc05 0xf7fffc07fffff03d 0xfdffff01fffffc0f

def z1213 : W := mkw 0x8000240049005015 0x2000090012401405 0x640c7cf8f808f8ff 0xd9031f3e3e023e3f

def z1214 : W := mkw 0x936ffc004f6ef015 0x24dbff0013dbbc05 0xf3fffc00dffff001 0xfcffff0037fffc00

def z1215 : W := mkw 0x0adc03f802dd0ec0 0x02b700fe00b743b0 0xfffc13f827ff0fc3 0xffff04fe09ffc3f0

def z1216 : W := mkw 0x024c8000064ea000 0x009320000193a800 0xf3fc000007fff000 0xfcff000001fffc00

def z1217 : W := mkw 0x018262c4c1904c11 0x006098b130641304 0xef83e3c7c7f0cf33 0x7be0f8f1f1fc33cc

def z1218 : W := mkw 0x8582e6c5cdb0dd37 0xa160b9b1736c374d 0xef83e3c7c7f0ff3f 0x7be0f8f1f1fc3fcf

def z1219 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc0ffffff8000003 0xf303fffffe000000

def z1220 : W := mkw 0x0ad803f000d50e80 0x02b600fc003543a0 0xfbfc03f807f70f02 0xfeff00fe01fdc3c0

def z1221 : W := mkw 0x124c2400036c5000 0x0493090000db1400 0xf3fc000007ff0000 0xfcff000001ffc000

def z1222 : W := mkw 0x0582e2c5c5b0cd33 0x8160b8b1716c334c 0x8f83e3c7c7f0c731 0x63e0f8f1f1fc31cc

def z1223 : W := mkw 0x136ffc00476ef011 0x04dbff0011dbbc04 0xf7fffc00c7fff031 0xfdffff0031fffc0c

def z1224 : W := mkw 0x880424484bdc5c55 0x2201091212f71715 0x640c7cf8fbf8f8ff 0xd9031f3e3efe3e3f

def z1225 : W := mkw 0x8adc07f80add1ec4 0x22b701fe02b747b1 0xfffc1ff83fffffff 0xffff07fe0fffffff

def z1226 : W := mkw 0x136ffc02376ef000 0x04dbff008ddbbc00 0xf3fffc003ffff001 0xfcffff000ffffc00

def z1227 : W := mkw 0x024c2000034c4000 0x0093080000d31000 0xf3fc600007ffc001 0xfcff180001fff000

def z1228 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xd3fffc0007f70001 0xf4ffff0001fdc000

def z1229 : W := mkw 0x134eec00076cd000 0x04d3bb0001db3400 0xf3ffec0007ffc001 0xfcfffb0001fff000

def z1230 : W := mkw 0x136ffc00076ef000 0x04dbff0001dbbc00 0xf3fffc2007fff8c3 0xfcffff0801fffe30

def z1231 : W := mkw 0x0ad803f000d50e80 0x02b600fc003543a0 0xbbf0030007f70f00 0x2efc00c001fdc3c0

def z1232 : W := mkw 0x0102400480000000 0x0040900120000000 0x440ffcfff8000003 0xd103ff3ffe000000

def z1233 : W := mkw 0x9404a4494ffefd77 0xa501291253ffbf5d 0x2000000007fffffc 0x0800000001ffffff

def z1234 : W := mkw 0x089083f904918fe2 0x022420fe412463f8 0xec0383ff0400cff3 0x3b00e0ffc10033fc

def z1235 : W := mkw 0x02f913b220000000 0x00be44ec88000000 0xdffffffff8000003 0xf7fffffffe000000

def z1236 : W := mkw 0x8004a4494f8af97f 0x6001291253e2be5f 0x200000000388f8fc 0x0800000000e23e3f

def z1237 : W := mkw 0x03fb5bb6b0000000 0x00fed6edac000000 0xfffffffff808f003 0xfffffffffe023c00

def z1238 : W := mkw 0x0582e6c5c5b0dd33 0x8160b9b1716c374c 0xef83ffc7c7f0ff33 0x7be0fff1f1fc3fcc

def z1239 : W := mkw 0x800424484b885855 0x2001091212e21615 0xec0c7ff8ff88ffff 0xfb031ffe3fe23fff

def z1240 : W := mkw 0x136fdc00066eb000 0x04dbf700019bac00 0xf3ff9c0007ff3000 0xfcffe70001ffcc00

def z1241 : W := mkw 0x136ffc03276ef12a 0x44dbff00c9dbbc4a 0xf3fffc0707fff001 0xfcffff01c1fffc00

def z1242 : W := mkw 0x03ca4a9490000000 0x00f292a524000000 0x078fecdfd8000001 0x41e3fb37f6000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z8,z6]),(0,[z1,z9,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z11,z6]),(0,[z1,z2,z3,z4,z12,z5,z6]),(0,[z1,z13,z2,z3,z4,z5,z6])],[(0,[z14,z1,z2,z3,z4,z5,z6]),(0,[z15,z1,z2,z3,z4,z5,z6]),(0,[z1,z16,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z17,z4,z5,z6]),(0,[z1,z18,z19,z3,z4,z5,z6]),(0,[z1,z20,z20,z2,z3,z4,z6]),(1,[z1,z2,z3,z21,z4,z6])],[(0,[z1,z2,z22,z4,z5,z6,z23]),(0,[z1,z24,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z25,z6])],[(0,[z1,z2,z3,z4,z26,z5,z6]),(0,[z27,z1,z28,z2,z3,z4,z6])],[(0,[z29,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z30]),(0,[z1,z20,z2,z3,z31,z4,z6]),(0,[z1,z32,z2,z3,z21,z4,z6])],[(0,[z1,z2,z3,z33,z4,z5,z6]),(0,[z1,z2,z34,z3,z4,z5,z6]),(0,[z1,z2,z35,z3,z4,z5,z6]),(0,[z36,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z37]),(0,[z38,z1,z2,z3,z21,z4,z6]),(0,[z1,z2,z3,z4,z39,z5,z6])],[(0,[z40,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z41,z3,z4,z5,z6]),(0,[z42,z1,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z44,z4,z5,z6]),(0,[z45,z1,z2,z3,z46,z5,z6]),(0,[z47,z1,z2,z3,z4,z5,z48]),(0,[z47,z2,z3,z4,z5,z6,z48]),(0,[z1,z20,z2,z3,z4,z49,z6]),(0,[z1,z20,z2,z3,z4,z6,z50])]],
   [[(0,[z1,z3,z4,z51,z5,z10,z6]),(0,[z1,z2,z3,z4,z52,z5,z6]),(0,[z53,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z6,z54]),(0,[z1,z2,z3,z21,z4,z55,z6])],[(0,[z56,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z57,z6]),(0,[z1,z2,z3,z4,z5,z58,z6]),(0,[z59,z1,z60,z3,z4,z5,z6]),(0,[z1,z2,z61,z3,z21,z4,z6]),(0,[z1,z2,z3,z5,z62,z6,z63])],[(0,[z1,z2,z3,z4,z5,z64,z6]),(0,[z1,z2,z3,z21,z4,z8,z6]),(1,[z65,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z66,z6])],[(0,[z1,z2,z3,z4,z67,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z68]),(0,[z1,z2,z3,z69,z4,z5,z6]),(1,[z1,z70,z2,z71,z5,z6]),(0,[z1,z2,z3,z4,z72,z5,z6]),(0,[z1,z2,z3,z73,z4,z5,z6])],[(0,[z74,z1,z2,z3,z4,z5,z6]),(0,[z74,z1,z70,z2,z4,z5,z6]),(1,[z1,z2,z4,z75,z5,z6]),(0,[z1,z2,z3,z76,z4,z5,z6])],[(0,[z1,z2,z3,z4,z77,z5,z6]),(0,[z78,z1,z28,z2,z3,z4,z6]),(0,[z1,z79,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z80,z4,z5,z6]),(0,[z1,z2,z3,z81,z4,z5,z6])],[(0,[z1,z2,z3,z82,z4,z5,z6]),(0,[z1,z2,z3,z83,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z84]),(0,[z1,z2,z85,z4,z5,z86,z6])],[(1,[z1,z87,z2,z3,z5,z6]),(0,[z27,z78,z2,z3,z4,z5,z6]),(0,[z1,z88,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z89,z5,z6]),(0,[z1,z2,z3,z90,z4,z5,z6]),(0,[z91,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z3,z4,z5,z6,z92]),(0,[z1,z2,z3,z4,z5,z6,z93])],[(1,[z1,z94,z3,z4,z5,z6]),(0,[z78,z2,z3,z4,z5,z95,z6]),(0,[z1,z20,z2,z3,z4,z96,z6]),(0,[z47,z97,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z98,z5,z6]),(0,[z1,z99,z2,z3,z4,z5,z6])],[(0,[z1,z100,z101,z3,z4,z5,z6]),(0,[z102,z1,z2,z3,z4,z5,z6]),(0,[z1,z28,z20,z2,z3,z4,z6]),(0,[z91,z1,z2,z3,z4,z5,z50]),(0,[z1,z2,z3,z4,z103,z5,z86])],[(0,[z1,z2,z3,z4,z104,z5,z6]),(0,[z105,z1,z2,z3,z4,z5,z6]),(0,[z1,z106,z2,z3,z4,z5,z6])],[(1,[z1,z60,z31,z4,z5,z6]),(1,[z1,z2,z3,z4,z107,z6])],[(0,[z1,z108,z2,z3,z4,z5,z6]),(1,[z1,z109,z3,z4,z5,z6])],[(0,[z47,z1,z2,z3,z4,z110,z6]),(1,[z1,z70,z20,z2,z3,z6]),(0,[z1,z2,z3,z4,z5,z111,z6]),(0,[z112,z1,z2,z3,z4,z5,z6]),(0,[z1,z113,z2,z3,z4,z5,z6])],[(0,[z114,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z115,z4,z5,z6]),(0,[z1,z2,z3,z4,z116,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z117]),(0,[z1,z70,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z118,z4,z5,z6]),(0,[z1,z2,z119,z3,z4,z5,z6])],[(0,[z1,z120,z2,z3,z4,z67,z6]),(0,[z1,z2,z3,z4,z5,z121,z6]),(0,[z1,z2,z122,z3,z4,z5,z6]),(0,[z123,z1,z20,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z124,z6]),(0,[z1,z2,z3,z4,z5,z6,z125]),(0,[z1,z126,z2,z3,z4,z71,z6])],[(0,[z1,z127,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z128,z6]),(0,[z1,z2,z3,z4,z5,z86,z6])],[(0,[z97,z2,z129,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z130,z5,z6]),(0,[z47,z1,z9,z2,z3,z4,z5]),(0,[z1,z2,z3,z51,z5,z6,z63]),(0,[z1,z2,z3,z4,z131,z5,z6]),(1,[z1,z2,z3,z132,z5,z6]),(1,[z133,z1,z2,z3,z5,z63])],[(0,[z47,z1,z2,z3,z4,z5,z6]),(0,[z1,z134,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z135,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z136]),(1,[z1,z137,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z138]),(0,[z1,z2,z3,z4,z139,z5,z6]),(0,[z140,z1,z2,z3,z4,z5,z6]),(0,[z1,z141,z2,z3,z4,z5,z6])],[(0,[z142,z1,z2,z3,z4,z5,z6]),(0,[z1,z20,z9,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z143]),(0,[z1,z2,z3,z82,z21,z4,z6])]],
   [[(0,[z1,z2,z3,z144,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z145,z6]),(0,[z1,z146,z20,z2,z3,z4,z6])],[(0,[z59,z147,z1,z3,z4,z5,z6]),(0,[z148,z1,z2,z3,z4,z5,z6]),(0,[z1,z87,z2,z3,z4,z5,z6]),(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z1,z150,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z151]),(1,[z1,z2,z3,z4,z152,z6]),(0,[z1,z153,z2,z3,z4,z5,z6])],[(0,[z1,z2,z129,z3,z4,z5,z6]),(0,[z154,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z155,z6]),(0,[z1,z2,z3,z4,z5,z156,z6]),(0,[z1,z157,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z158,z6]),(0,[z1,z2,z3,z4,z5,z6,z159]),(0,[z1,z160,z20,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z161,z6]),(0,[z1,z2,z3,z4,z162,z96,z6]),(0,[z2,z3,z4,z5,z163,z6,z48]),(0,[z1,z2,z3,z4,z164,z5,z6]),(1,[z1,z19,z3,z4,z8,z6]),(0,[z1,z2,z165,z3,z4,z5,z6]),(0,[z1,z166,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z167])],[(0,[z1,z129,z3,z4,z5,z6,z168]),(0,[z1,z169,z2,z3,z4,z5,z6]),(1,[z1,z2,z170,z171,z5,z6])],[(0,[z172,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z67,z5,z6,z63]),(0,[z1,z2,z3,z4,z173,z5,z6]),(0,[z174,z1,z2,z3,z175,z5,z6]),(0,[z1,z70,z176,z2,z4,z5,z6]),(0,[z1,z2,z3,z177,z4,z5,z6]),(0,[z1,z70,z2,z4,z5,z6,z23]),(0,[z1,z2,z3,z21,z4,z86,z6])],[(0,[z1,z178,z2,z3,z4,z5,z6]),(1,[z179,z1,z2,z3,z4,z5]),(0,[z1,z2,z180,z3,z22,z4,z6]),(1,[z27,z2,z3,z4,z96,z6]),(0,[z1,z2,z3,z181,z4,z5,z6]),(0,[z182,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z183,z4,z5,z6]),(0,[z59,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z184,z6]),(0,[z147,z1,z100,z3,z4,z5,z6]),(0,[z2,z185,z3,z22,z4,z5,z6]),(0,[z1,z137,z2,z3,z22,z4,z6]),(0,[z1,z186,z2,z3,z4,z5,z6]),(0,[z1,z187,z2,z3,z4,z5,z6]),(0,[z1,z188,z2,z3,z4,z5,z6]),(0,[z189,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z60,z176,z3,z4,z5,z6]),(0,[z1,z70,z2,z3,z21,z4,z6]),(0,[z190,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z191,z6]),(0,[z1,z2,z3,z46,z5,z55,z6])],[(0,[z192,z1,z2,z4,z162,z5,z6]),(0,[z1,z2,z3,z4,z103,z95,z6]),(0,[z1,z193,z2,z3,z4,z5,z6]),(0,[z1,z19,z3,z4,z5,z8,z6])],[(0,[z194,z1,z2,z3,z4,z5,z6]),(0,[z192,z1,z28,z2,z4,z5,z6]),(0,[z1,z195,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z196,z5,z6]),(0,[z1,z20,z2,z3,z171,z4,z6]),(1,[z1,z197,z2,z3,z4,z6])],[(0,[z198,z1,z2,z3,z4,z5,z6]),(0,[z192,z1,z2,z22,z4,z5,z6]),(0,[z199,z1,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z170,z3,z5,z6]),(0,[z1,z2,z3,z21,z4,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z200])],[(0,[z174,z1,z2,z3,z4,z5,z6]),(0,[z45,z1,z20,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z110,z6]),(0,[z59,z1,z2,z3,z201,z5,z6]),(0,[z133,z1,z2,z3,z5,z6,z63]),(0,[z1,z2,z3,z4,z202,z5,z6]),(0,[z1,z2,z3,z4,z86,z6,z50]),(0,[z203,z1,z2,z3,z4,z5,z6])],[(0,[z204,z1,z2,z3,z21,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z205]),(0,[z1,z2,z3,z206,z4,z5,z6]),(1,[z1,z2,z3,z5,z6,z207]),(0,[z1,z2,z208,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z209,z6]),(0,[z1,z210,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z211,z6]),(0,[z1,z2,z3,z4,z5,z6,z212])],[(0,[z1,z2,z3,z4,z213,z5,z6]),(0,[z1,z2,z3,z4,z214,z5,z6]),(0,[z1,z2,z3,z5,z86,z6,z215])],[(0,[z216,z1,z2,z3,z4,z5,z6]),(1,[z1,z217,z2,z4,z5,z6]),(0,[z218,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z219]),(0,[z1,z9,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z220,z5,z6]),(0,[z97,z1,z2,z3,z4,z5,z163]),(0,[z1,z221,z2,z3,z4,z5,z6]),(0,[z1,z18,z2,z3,z4,z222,z6]),(0,[z1,z2,z223,z3,z4,z5,z6]),(0,[z224,z1,z2,z3,z4,z5,z6])],[(0,[z225,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z226,z6]),(0,[z1,z2,z3,z4,z5,z227,z6]),(0,[z1,z99,z2,z3,z5,z228,z6]),(0,[z38,z1,z2,z3,z4,z5,z49])],[(0,[z229,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z230,z4,z5,z6]),(0,[z1,z2,z231,z3,z4,z5,z6]),(0,[z1,z232,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z45,z1,z2,z3,z67,z5,z6]),(0,[z233,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z234,z4,z5,z6]),(0,[z1,z24,z2,z3,z51,z5,z6]),(0,[z1,z2,z3,z4,z5,z235,z6]),(0,[z1,z2,z3,z4,z5,z236,z6])],[(0,[z237,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z238,z3,z4,z5,z6]),(1,[z1,z20,z2,z3,z51,z6]),(0,[z1,z20,z2,z61,z3,z4,z6]),(1,[z1,z20,z2,z3,z6,z63])],[(0,[z239,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z240,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z51,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z241]),(1,[z1,z2,z223,z4,z162,z6]),(0,[z1,z2,z61,z3,z4,z5,z49]),(0,[z1,z20,z2,z3,z4,z55,z6])],[(1,[z1,z2,z3,z4,z242,z6]),(0,[z1,z2,z3,z4,z5,z243,z6]),(0,[z1,z176,z2,z101,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z244,z5,z6]),(0,[z1,z2,z245,z3,z4,z5,z6])],[(1,[z1,z246,z3,z4,z5,z6]),(0,[z1,z176,z2,z3,z4,z5,z6]),(0,[z1,z2,z247,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z4,z8,z6]),(0,[z59,z1,z2,z248,z4,z5,z6]),(0,[z38,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z211,z6]),(0,[z1,z2,z249,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z250])]],
   [[(0,[z1,z60,z100,z3,z4,z5,z6]),(0,[z1,z87,z2,z3,z22,z5,z6]),(0,[z174,z1,z2,z3,z4,z173,z6]),(0,[z174,z1,z2,z3,z46,z5,z6]),(0,[z1,z251,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z252]),(0,[z1,z2,z3,z4,z5,z253,z6]),(0,[z1,z2,z3,z4,z5,z254,z6])],[(0,[z192,z1,z2,z171,z4,z5,z6]),(0,[z1,z2,z3,z255,z4,z5,z6]),(0,[z256,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z201,z5,z6]),(0,[z1,z2,z3,z4,z257,z5,z6]),(0,[z1,z2,z3,z4,z258,z5,z6]),(0,[z1,z2,z4,z5,z49,z6,z23])],[(0,[z179,z1,z2,z3,z4,z5,z6]),(0,[z59,z1,z2,z3,z4,z5,z10]),(1,[z1,z259,z3,z4,z5,z6]),(0,[z133,z1,z2,z3,z4,z5,z62]),(0,[z1,z260,z2,z3,z4,z5,z6])],[(0,[z1,z100,z3,z4,z5,z6,z168]),(0,[z27,z1,z2,z3,z4,z95,z6]),(0,[z97,z1,z20,z2,z3,z4,z6]),(0,[z1,z2,z61,z3,z4,z5,z6]),(0,[z261,z1,z2,z3,z21,z4,z6]),(0,[z1,z262,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z263,z4,z5,z6])],[(0,[z1,z2,z3,z4,z264,z5,z6]),(0,[z265,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z266,z5,z6]),(0,[z1,z2,z3,z4,z267,z5,z6]),(0,[z47,z1,z2,z3,z268,z5,z6]),(0,[z1,z2,z101,z61,z4,z5,z6])],[(0,[z1,z129,z101,z3,z4,z5,z6]),(1,[z1,z176,z101,z4,z5,z6]),(0,[z1,z2,z3,z269,z4,z51,z6]),(0,[z1,z2,z4,z162,z5,z6,z23]),(0,[z1,z270,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z5,z55,z6])],[(1,[z1,z2,z3,z4,z173,z6]),(0,[z1,z271,z2,z3,z4,z5,z6]),(0,[z1,z24,z2,z3,z4,z272,z6]),(0,[z1,z2,z3,z4,z5,z6,z273]),(0,[z1,z2,z3,z4,z5,z274,z6]),(0,[z133,z1,z20,z2,z3,z4,z6]),(0,[z275,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z85,z4,z5,z6])]],
   [[(0,[z1,z2,z185,z61,z4,z5,z6]),(1,[z1,z251,z2,z3,z4,z6]),(0,[z59,z65,z2,z3,z4,z5,z6])],[(0,[z1,z24,z129,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z95,z228,z6]),(0,[z1,z2,z3,z4,z5,z6,z276]),(0,[z1,z2,z277,z3,z4,z5,z6]),(0,[z1,z2,z223,z3,z21,z4,z6]),(1,[z1,z20,z2,z3,z55,z6]),(0,[z1,z2,z85,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z278,z5,z6]),(1,[z1,z20,z2,z3,z279,z6]),(0,[z1,z2,z3,z4,z103,z8,z6]),(0,[z1,z2,z3,z5,z236,z228,z6]),(0,[z1,z2,z3,z4,z5,z6,z280])],[(0,[z1,z2,z3,z4,z5,z6,z281]),(0,[z1,z282,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z283,z21,z4,z6])],[(0,[z1,z2,z180,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z284,z6]),(0,[z1,z2,z3,z4,z5,z6,z285]),(1,[z1,z2,z248,z4,z5,z6]),(0,[z1,z2,z3,z286,z4,z5,z6])],[(0,[z287,z1,z2,z3,z4,z5,z6]),(1,[z204,z129,z3,z4,z5,z6]),(0,[z1,z2,z3,z288,z4,z5,z6]),(0,[z289,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z290,z3,z4,z5,z6]),(0,[z1,z137,z2,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z4,z95,z6]),(0,[z1,z20,z2,z3,z4,z222,z6]),(0,[z38,z1,z2,z4,z5,z6,z23]),(1,[z1,z2,z3,z286,z5,z6])],[(0,[z1,z2,z3,z4,z110,z5,z6]),(0,[z1,z18,z2,z3,z21,z4,z6]),(0,[z1,z2,z171,z4,z71,z5,z6]),(0,[z91,z1,z2,z3,z4,z5,z86])],[(0,[z1,z2,z3,z291,z4,z5,z6]),(0,[z1,z292,z2,z3,z4,z5,z6]),(0,[z1,z2,z223,z3,z4,z228,z6]),(0,[z1,z2,z3,z4,z49,z6,z54])]],
   [[(0,[z1,z293,z2,z3,z4,z5,z6]),(0,[z1,z2,z294,z3,z4,z5,z6]),(0,[z1,z60,z3,z4,z5,z10,z6]),(0,[z1,z176,z2,z3,z21,z4,z6]),(0,[z1,z2,z3,z4,z5,z295,z6]),(0,[z1,z2,z3,z4,z5,z296,z6])],[(1,[z174,z1,z20,z2,z3,z6]),(0,[z1,z297,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z298,z5,z6])],[(0,[z1,z2,z3,z4,z5,z299,z6]),(0,[z1,z2,z3,z4,z5,z272,z6]),(0,[z1,z2,z300,z3,z4,z5,z6]),(0,[z1,z301,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z62,z6])],[(1,[z1,z2,z3,z302,z4,z6]),(0,[z1,z2,z3,z303,z4,z5,z6]),(0,[z1,z2,z304,z3,z4,z5,z6]),(0,[z1,z2,z3,z305,z4,z5,z6])],[(0,[z1,z2,z3,z306,z4,z5,z6]),(0,[z1,z2,z3,z4,z307,z5,z6]),(0,[z192,z1,z20,z2,z3,z4,z6]),(0,[z308,z1,z2,z3,z4,z5,z6]),(0,[z1,z309,z2,z3,z4,z5,z6]),(0,[z310,z1,z2,z3,z4,z5,z6]),(0,[z1,z311,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z312,z5,z6])],[(1,[z97,z2,z3,z4,z5,z163]),(0,[z1,z60,z20,z2,z3,z4,z6]),(0,[z313,z1,z2,z3,z4,z5,z6])],[(0,[z59,z204,z1,z3,z4,z5,z6]),(0,[z314,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z315])],[(0,[z1,z2,z3,z4,z5,z316,z6]),(0,[z1,z2,z3,z4,z317,z5,z6]),(1,[z1,z2,z4,z5,z6,z318]),(0,[z1,z319,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z320,z2,z3,z21,z4,z6]),(0,[z1,z19,z2,z3,z4,z222,z6]),(0,[z1,z321,z2,z3,z4,z5,z6]),(0,[z1,z2,z170,z3,z21,z4,z6])],[(0,[z1,z20,z2,z3,z175,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z322]),(0,[z1,z323,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z324])],[(0,[z74,z1,z2,z3,z4,z242,z6]),(0,[z325,z1,z2,z3,z4,z5,z6]),(0,[z1,z326,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z4,z71,z6]),(0,[z1,z20,z2,z3,z4,z86,z6]),(0,[z327,z1,z2,z3,z4,z5,z6])],[(0,[z1,z328,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z329,z6]),(0,[z47,z1,z2,z330,z4,z5,z6]),(1,[z1,z2,z3,z268,z5,z6]),(0,[z1,z331,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z332,z6]),(0,[z1,z333,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z334])],[(0,[z2,z3,z4,z96,z5,z95,z6]),(0,[z1,z2,z170,z3,z171,z5,z6]),(0,[z1,z166,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z21,z4,z62,z6]),(0,[z1,z2,z4,z5,z86,z6,z250])],[(0,[z1,z2,z3,z4,z5,z335,z6]),(0,[z1,z336,z2,z3,z4,z5,z6]),(0,[z1,z20,z320,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z6,z50]),(0,[z1,z2,z337,z3,z4,z5,z6]),(0,[z338,z1,z2,z3,z4,z5,z6]),(0,[z1,z126,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z339,z5,z6])],[(0,[z1,z94,z2,z3,z4,z5,z6]),(0,[z45,z1,z2,z170,z3,z5,z6]),(0,[z59,z1,z24,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z340]),(0,[z1,z2,z341,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z342]),(0,[z1,z197,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z16,z2,z3,z5,z95,z6]),(0,[z1,z2,z3,z343,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z344,z6]),(0,[z1,z2,z3,z4,z5,z345,z6]),(0,[z1,z20,z2,z3,z4,z4,z6]),(0,[z1,z2,z3,z21,z4,z6,z315]),(0,[z1,z346,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z347,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z348])],[(0,[z1,z2,z3,z4,z5,z349,z6]),(1,[z1,z28,z2,z4,z228,z6]),(0,[z1,z2,z3,z350,z4,z5,z6]),(0,[z1,z2,z351,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z135,z5,z6])],[(0,[z1,z2,z3,z4,z352,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z353]),(0,[z1,z2,z170,z3,z71,z5,z6])],[(0,[z1,z2,z354,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z222,z5,z6]),(0,[z1,z2,z3,z21,z4,z222,z6]),(0,[z1,z9,z3,z4,z5,z10,z6])],[(0,[z1,z2,z3,z355,z4,z5,z6]),(0,[z1,z2,z3,z4,z356,z5,z6]),(0,[z1,z24,z2,z3,z21,z4,z6]),(0,[z1,z2,z3,z357,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z23]),(0,[z1,z2,z3,z81,z46,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z358])],[(0,[z74,z1,z2,z4,z162,z5,z6]),(0,[z1,z2,z3,z31,z21,z4,z6]),(0,[z359,z1,z2,z3,z4,z5,z6]),(0,[z91,z1,z2,z3,z4,z103,z6]),(0,[z1,z2,z3,z4,z103,z86,z6])],[(0,[z74,z1,z28,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z360,z6]),(1,[z1,z309,z2,z4,z5,z6]),(0,[z1,z2,z3,z361,z4,z5,z6])],[(0,[z204,z1,z2,z3,z4,z5,z6]),(0,[z74,z1,z2,z22,z4,z5,z6]),(0,[z362,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z21,z46,z6])]],
   [[(0,[z1,z20,z2,z185,z3,z4,z6]),(1,[z78,z2,z3,z4,z95,z6]),(0,[z1,z20,z2,z3,z4,z163,z6])],[(0,[z363,z1,z2,z3,z4,z5,z6]),(0,[z1,z364,z2,z3,z4,z5,z6]),(0,[z45,z1,z20,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z95,z6,z50]),(0,[z27,z1,z20,z2,z3,z4,z6]),(0,[z1,z18,z2,z3,z132,z5,z6]),(0,[z1,z2,z3,z4,z5,z365,z6]),(0,[z1,z221,z20,z2,z3,z4,z6]),(0,[z1,z366,z2,z3,z4,z5,z6])],[(0,[z1,z2,z367,z3,z4,z5,z6]),(0,[z1,z2,z69,z4,z51,z5,z6]),(0,[z368,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z10,z6,z168]),(0,[z1,z2,z3,z369,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z370,z6]),(0,[z371,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z372,z3,z4,z5,z6]),(0,[z1,z217,z2,z3,z4,z5,z6]),(0,[z47,z1,z246,z3,z4,z5,z6]),(0,[z1,z18,z3,z4,z222,z5,z6]),(1,[z1,z20,z2,z3,z4,z6]),(0,[z1,z20,z2,z3,z4,z209,z6])],[(0,[z1,z2,z4,z75,z5,z95,z6]),(0,[z1,z2,z3,z4,z5,z6,z373]),(0,[z374,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z375])],[(0,[z97,z2,z3,z4,z5,z163,z6]),(0,[z376,z1,z2,z3,z4,z5,z6]),(0,[z1,z19,z2,z3,z21,z4,z6]),(0,[z1,z70,z2,z3,z46,z5,z6]),(0,[z1,z2,z3,z21,z4,z6,z23])],[(0,[z1,z2,z3,z21,z175,z4,z6]),(0,[z1,z2,z3,z4,z377,z5,z6]),(0,[z378,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z174,z1,z70,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z71,z5,z6]),(0,[z1,z2,z3,z21,z4,z71,z6]),(0,[z1,z2,z379,z3,z4,z5,z6]),(0,[z1,z2,z380,z3,z4,z5,z6]),(0,[z1,z3,z81,z4,z135,z5,z6]),(0,[z381,z1,z2,z3,z4,z5,z6])],[(0,[z382,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z330,z4,z5,z6]),(0,[z1,z2,z3,z383,z4,z5,z6]),(0,[z1,z384,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z385,z6])],[(0,[z147,z204,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z75,z5,z6]),(0,[z1,z2,z330,z3,z4,z5,z6]),(0,[z1,z320,z2,z3,z51,z5,z6]),(0,[z386,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z387]),(0,[z1,z2,z3,z4,z5,z6,z388])],[(0,[z1,z2,z3,z389,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z390,z6]),(0,[z1,z2,z3,z4,z391,z5,z6]),(0,[z78,z1,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z392]),(0,[z1,z2,z393,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z394,z6])],[(0,[z1,z2,z3,z4,z5,z163,z6]),(0,[z1,z2,z3,z4,z395,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z396]),(0,[z1,z28,z2,z3,z21,z4,z6]),(0,[z1,z197,z2,z3,z4,z6,z63])],[(0,[z1,z100,z9,z3,z4,z5,z6]),(0,[z74,z1,z2,z171,z4,z5,z6]),(0,[z261,z1,z2,z3,z4,z5,z6]),(1,[z1,z120,z2,z3,z4,z6])],[(0,[z397,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z398,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z54])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z399]),(0,[z1,z2,z3,z4,z5,z400,z6]),(0,[z401,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z402,z2,z3,z4,z5,z6])],[(0,[z204,z2,z129,z3,z4,z5,z6]),(0,[z1,z403,z2,z3,z4,z5,z6]),(0,[z27,z1,z2,z3,z4,z96,z6]),(0,[z1,z2,z3,z404,z21,z4,z6]),(0,[z1,z2,z3,z21,z21,z4,z6])],[(0,[z1,z20,z2,z223,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z405,z6]),(0,[z1,z2,z246,z3,z4,z5,z6]),(0,[z406,z1,z2,z3,z4,z5,z6]),(0,[z407,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z408,z6])],[(0,[z1,z2,z3,z4,z5,z6,z409]),(0,[z1,z2,z3,z4,z5,z6,z410]),(0,[z411,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z412,z6]),(0,[z1,z2,z413,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z414]),(0,[z1,z20,z2,z3,z51,z5,z6]),(0,[z1,z2,z3,z4,z5,z415,z6]),(0,[z1,z2,z3,z283,z4,z5,z6]),(1,[z1,z2,z3,z4,z103,z86])],[(0,[z1,z2,z3,z21,z4,z163,z6]),(0,[z1,z2,z3,z4,z5,z416,z6])],[(0,[z417,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z418]),(0,[z1,z2,z3,z4,z419,z5,z6])]],
   [[(1,[z1,z420,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z421]),(0,[z1,z176,z2,z31,z4,z5,z6]),(0,[z1,z18,z2,z3,z4,z5,z6]),(0,[z1,z70,z2,z3,z5,z6,z63])],[(0,[z1,z422,z2,z3,z4,z5,z6]),(0,[z1,z2,z31,z4,z5,z6,z23]),(0,[z1,z2,z3,z279,z4,z5,z6]),(0,[z1,z2,z3,z4,z132,z5,z6]),(0,[z1,z70,z2,z170,z4,z5,z6]),(0,[z1,z2,z380,z3,z21,z4,z6])],[(0,[z1,z2,z3,z4,z5,z423,z6]),(0,[z1,z2,z3,z5,z49,z6,z207]),(0,[z1,z2,z3,z4,z424,z5,z6])],[(0,[z204,z1,z100,z3,z4,z5,z6]),(0,[z147,z1,z129,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z4,z96,z6]),(0,[z425,z1,z2,z3,z4,z5,z6])],[(0,[z426,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z61,z31,z4,z5,z6]),(0,[z1,z2,z427,z3,z4,z5,z6]),(0,[z1,z28,z2,z223,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z428,z6]),(0,[z1,z2,z3,z81,z4,z5,z62])],[(0,[z1,z20,z2,z3,z279,z4,z6]),(0,[z59,z1,z3,z4,z5,z6,z168]),(0,[z1,z2,z171,z4,z5,z6,z23])],[(0,[z429,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z430,z6]),(0,[z1,z431,z2,z3,z4,z5,z6]),(0,[z1,z2,z223,z3,z4,z103,z6])],[(0,[z432,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z433,z6]),(0,[z1,z434,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z369,z5,z6])]],
   [[(0,[z74,z1,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z175,z4,z5,z6]),(0,[z1,z2,z3,z435,z4,z5,z6]),(0,[z59,z187,z2,z3,z4,z5,z6]),(0,[z401,z1,z2,z3,z21,z4,z6])],[(0,[z2,z3,z175,z4,z67,z5,z6]),(0,[z256,z1,z3,z4,z5,z6,z48]),(1,[z1,z3,z4,z5,z6,z436]),(0,[z1,z2,z248,z3,z4,z5,z6]),(0,[z1,z2,z223,z4,z162,z5,z6]),(0,[z1,z20,z2,z3,z4,z62,z6])],[(0,[z1,z2,z437,z129,z3,z4,z5]),(0,[z1,z320,z2,z3,z4,z5,z6]),(0,[z1,z2,z170,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z438,z6]),(0,[z1,z2,z3,z439,z4,z5,z6])],[(0,[z1,z2,z3,z440,z4,z5,z6]),(0,[z97,z1,z9,z2,z3,z4,z5]),(0,[z1,z441,z2,z3,z4,z5,z6]),(0,[z91,z1,z20,z2,z3,z4,z6]),(0,[z1,z442,z2,z3,z4,z5,z6])],[(1,[z45,z1,z20,z2,z3,z6]),(0,[z1,z70,z2,z3,z81,z5,z6])],[(0,[z1,z2,z3,z4,z5,z443,z6]),(0,[z444,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z445,z3,z4,z5,z6]),(0,[z47,z1,z2,z3,z4,z5,z163]),(0,[z1,z2,z3,z4,z5,z446,z6]),(1,[z1,z2,z3,z4,z447,z6]),(0,[z1,z2,z3,z4,z5,z6,z448])],[(0,[z174,z1,z2,z170,z3,z5,z6]),(0,[z47,z1,z2,z3,z449,z5,z6]),(0,[z1,z450,z2,z3,z4,z5,z6]),(0,[z1,z451,z2,z3,z4,z5,z6]),(0,[z1,z2,z452,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z155,z6]),(0,[z1,z2,z3,z81,z67,z5,z6]),(1,[z1,z24,z3,z279,z5,z6]),(0,[z1,z2,z3,z4,z5,z453,z6]),(0,[z454,z1,z2,z3,z21,z4,z6])],[(1,[z1,z2,z3,z455,z5,z6]),(0,[z1,z456,z2,z3,z4,z5,z6]),(0,[z1,z457,z2,z3,z4,z5,z6]),(0,[z91,z1,z2,z3,z4,z6,z50])],[(0,[z458,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z279,z21,z4,z6]),(1,[z1,z2,z61,z4,z5,z49]),(0,[z1,z2,z3,z4,z5,z6,z207])],[(0,[z204,z1,z3,z4,z5,z10,z6]),(0,[z1,z320,z3,z4,z51,z5,z6]),(0,[z1,z2,z3,z4,z459,z5,z6]),(0,[z1,z70,z20,z2,z3,z4,z6]),(0,[z114,z1,z20,z2,z3,z4,z6]),(0,[z1,z2,z460,z3,z4,z5,z6])],[(0,[z1,z60,z129,z3,z4,z5,z6]),(0,[z174,z1,z2,z3,z4,z461,z6]),(0,[z1,z2,z3,z4,z462,z5,z6]),(0,[z1,z2,z61,z4,z162,z5,z6]),(0,[z1,z2,z3,z463,z21,z4,z6])],[(0,[z1,z464,z2,z3,z4,z5,z6]),(0,[z1,z465,z2,z3,z4,z5,z6]),(1,[z187,z2,z3,z4,z5,z6]),(0,[z1,z466,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z4,z5,z6])],[(0,[z1,z2,z61,z22,z4,z5,z6]),(0,[z1,z2,z467,z3,z4,z5,z6]),(0,[z1,z24,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z31,z4,z5,z6]),(0,[z1,z2,z468,z3,z4,z5,z6]),(0,[z469,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z204,z1,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z470,z4,z5,z6]),(0,[z59,z97,z1,z2,z3,z4,z5]),(0,[z1,z2,z471,z3,z4,z5,z6]),(0,[z1,z24,z320,z3,z4,z5,z6]),(0,[z1,z251,z2,z3,z4,z51,z6]),(0,[z1,z2,z3,z472,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z473,z6]),(0,[z1,z2,z3,z21,z4,z474,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z47,z1,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z475,z5,z6])],[(0,[z45,z1,z41,z3,z4,z5,z6]),(0,[z476,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z162,z5,z228,z6])],[(0,[z1,z129,z3,z4,z51,z5,z6]),(1,[z1,z2,z3,z4,z461,z6]),(0,[z477,z1,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z101,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z478,z6]),(0,[z1,z20,z2,z3,z4,z6,z23])],[(0,[z1,z2,z3,z302,z4,z67,z6]),(0,[z479,z1,z2,z3,z4,z5,z6]),(1,[z1,z18,z3,z4,z222,z6]),(0,[z1,z2,z3,z4,z5,z6,z480]),(0,[z1,z2,z3,z481,z4,z5,z6]),(0,[z38,z1,z2,z61,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z482,z6])],[(0,[z1,z2,z483,z3,z4,z5,z6]),(0,[z97,z1,z2,z3,z21,z4,z6]),(0,[z1,z2,z3,z4,z5,z484,z6])],[(0,[z1,z2,z3,z4,z5,z485,z6]),(0,[z147,z1,z2,z3,z21,z4,z6]),(0,[z1,z2,z3,z4,z5,z486,z6]),(0,[z487,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z488,z5,z6]),(0,[z59,z1,z101,z3,z4,z5,z6]),(1,[z1,z2,z3,z489,z5,z6]),(0,[z1,z2,z223,z3,z4,z162,z6]),(0,[z1,z2,z3,z4,z490,z5,z6])]],
   [[(0,[z1,z176,z2,z171,z4,z5,z6]),(0,[z1,z19,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z72,z6]),(0,[z1,z20,z2,z379,z3,z4,z6]),(0,[z1,z2,z3,z21,z81,z4,z6]),(0,[z1,z2,z3,z4,z6,z280,z63]),(0,[z491,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z4,z492,z5,z6]),(0,[z133,z1,z2,z3,z21,z4,z6])],[(0,[z1,z2,z493,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z107,z5,z6]),(0,[z59,z1,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z494,z4,z5,z6])],[(0,[z1,z2,z3,z4,z495,z5,z6]),(0,[z1,z496,z2,z3,z4,z5,z6])],[(0,[z147,z100,z2,z3,z4,z5,z6]),(1,[z1,z126,z2,z3,z4,z6]),(0,[z1,z2,z61,z171,z4,z5,z6]),(0,[z1,z2,z3,z4,z46,z5,z6]),(0,[z1,z2,z3,z4,z62,z6,z348]),(0,[z1,z2,z3,z4,z5,z6,z497])],[(0,[z1,z2,z3,z4,z498,z5,z6]),(0,[z1,z2,z3,z499,z4,z5,z6]),(1,[z1,z2,z3,z449,z5,z6]),(0,[z1,z500,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z501,z6])],[(0,[z1,z2,z3,z4,z502,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z503]),(0,[z1,z28,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z21,z4,z6]),(0,[z1,z504,z2,z3,z4,z5,z6])],[(0,[z1,z9,z129,z3,z4,z5,z6]),(0,[z1,z2,z290,z3,z22,z5,z6]),(0,[z192,z1,z505,z3,z4,z5,z6]),(0,[z1,z506,z2,z3,z4,z5,z6]),(0,[z507,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z508,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z162,z5,z6])]],
   [[(0,[z174,z1,z20,z2,z3,z4,z6])],[(0,[z1,z100,z2,z3,z4,z5,z6]),(0,[z1,z509,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z22,z4,z5,z6]),(0,[z1,z2,z3,z4,z510,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z511]),(0,[z1,z2,z3,z21,z4,z39,z6]),(1,[z1,z2,z3,z5,z6,z215])],[(0,[z1,z2,z3,z4,z5,z6,z512]),(0,[z1,z2,z513,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z514,z5,z6]),(0,[z1,z309,z2,z4,z5,z95,z6]),(0,[z1,z20,z176,z2,z3,z4,z6])],[(0,[z100,z2,z129,z3,z4,z5,z6]),(0,[z1,z2,z3,z404,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z5,z6])],[(0,[z192,z1,z2,z185,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z95,z6]),(0,[z1,z2,z3,z4,z515,z5,z6]),(0,[z516,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z66,z6])],[(0,[z1,z2,z517,z3,z4,z5,z6]),(0,[z1,z2,z3,z518,z4,z5,z6]),(0,[z123,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z10,z6])],[(0,[z192,z1,z2,z3,z21,z4,z6]),(0,[z45,z174,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z519,z4,z5,z6]),(0,[z1,z2,z3,z4,z520,z5,z6])],[(0,[z1,z2,z3,z4,z5,z521,z6]),(0,[z1,z2,z437,z3,z4,z5,z6]),(0,[z174,z1,z2,z3,z67,z5,z6]),(0,[z1,z2,z3,z268,z4,z5,z6]),(0,[z1,z60,z2,z3,z21,z4,z6]),(0,[z1,z320,z2,z3,z279,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z522]),(0,[z1,z3,z279,z4,z51,z5,z6]),(0,[z1,z20,z2,z3,z4,z6,z523])]],
   [[(0,[z1,z2,z3,z4,z96,z5,z6]),(0,[z1,z176,z101,z3,z4,z5,z6]),(0,[z417,z1,z20,z2,z3,z4,z6]),(0,[z1,z524,z2,z3,z21,z4,z6])],[(0,[z1,z2,z3,z4,z5,z6,z525]),(0,[z526,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z222,z103,z6]),(0,[z1,z28,z2,z3,z4,z103,z6]),(0,[z1,z2,z527,z4,z5,z62,z6])],[(0,[z1,z100,z3,z4,z51,z5,z6]),(1,[z192,z2,z185,z4,z5,z6]),(0,[z528,z1,z2,z3,z4,z5,z6]),(0,[z529,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z530,z4,z5,z6]),(1,[z1,z2,z3,z4,z258,z6]),(0,[z1,z2,z223,z3,z4,z6,z50])],[(0,[z1,z2,z3,z531,z4,z5,z6]),(0,[z1,z2,z101,z4,z5,z6,z23]),(0,[z1,z2,z3,z4,z447,z5,z6]),(0,[z1,z2,z532,z3,z4,z5,z6]),(0,[z1,z2,z3,z533,z4,z5,z6]),(0,[z38,z1,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z534])],[(0,[z1,z20,z2,z3,z4,z67,z6]),(0,[z1,z146,z2,z3,z4,z5,z6]),(1,[z1,z456,z3,z4,z5,z6]),(0,[z1,z101,z3,z31,z4,z5,z6]),(0,[z1,z2,z170,z3,z81,z5,z6]),(0,[z1,z28,z2,z4,z5,z6,z23]),(0,[z1,z2,z3,z21,z535,z4,z6]),(0,[z133,z1,z2,z3,z4,z5,z63])],[(1,[z1,z2,z69,z4,z5,z6]),(0,[z1,z2,z536,z3,z4,z5,z6]),(0,[z537,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z538,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z318])],[(0,[z1,z2,z185,z4,z5,z6,z23]),(0,[z1,z2,z3,z21,z4,z95,z6]),(1,[z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z101,z3,z21,z4,z6]),(0,[z1,z539,z2,z4,z51,z5,z6]),(0,[z1,z160,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z103,z6]),(0,[z1,z2,z3,z4,z152,z62,z6])],[(1,[z74,z2,z22,z4,z5,z6]),(0,[z1,z540,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z541,z6]),(0,[z1,z2,z3,z171,z4,z5,z6]),(0,[z1,z2,z3,z21,z46,z5,z6])]],
   [[(0,[z542,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z543]),(0,[z1,z2,z3,z4,z5,z6,z544]),(0,[z1,z2,z3,z4,z5,z228,z6])],[(0,[z545,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z546,z3,z4,z5,z6]),(0,[z1,z2,z185,z3,z21,z4,z6]),(0,[z45,z1,z2,z3,z175,z5,z6]),(0,[z97,z1,z2,z3,z4,z5,z48]),(0,[z1,z2,z3,z201,z4,z5,z6])],[(0,[z147,z2,z3,z4,z5,z6,z48]),(0,[z1,z20,z100,z2,z3,z4,z6]),(0,[z1,z100,z2,z3,z21,z4,z6]),(0,[z1,z20,z2,z3,z22,z4,z6]),(0,[z1,z2,z3,z22,z21,z4,z6]),(0,[z1,z24,z2,z3,z4,z107,z6]),(0,[z1,z20,z2,z3,z279,z5,z6]),(0,[z547,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z62,z6,z318])],[(0,[z548,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z549,z5,z6]),(0,[z1,z2,z3,z550,z4,z5,z6]),(0,[z1,z2,z3,z4,z96,z103,z6]),(0,[z551,z1,z2,z3,z4,z5,z6]),(0,[z1,z24,z2,z3,z279,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z552]),(0,[z275,z1,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z523])],[(0,[z553,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z180,z3,z4,z6]),(0,[z1,z2,z554,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z555,z5,z6])],[(0,[z1,z2,z3,z4,z5,z556,z6]),(1,[z256,z1,z3,z4,z5,z6]),(0,[z557,z1,z2,z3,z4,z5,z6]),(0,[z1,z28,z2,z3,z4,z228,z6]),(0,[z1,z2,z558,z3,z4,z5,z6])],[(0,[z1,z2,z3,z559,z4,z5,z6])],[(0,[z74,z192,z2,z3,z4,z5,z6]),(1,[z1,z505,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z48]),(0,[z1,z2,z3,z560,z4,z5,z6]),(0,[z1,z70,z2,z61,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z561]),(0,[z45,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z302,z4,z5,z6]),(0,[z562,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z6,z63]),(0,[z1,z2,z3,z4,z5,z563,z6])],[(1,[z1,z2,z115,z4,z5,z6]),(0,[z564,z1,z2,z3,z4,z5,z6]),(0,[z565,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z566])],[(0,[z1,z567,z2,z3,z4,z5,z6]),(0,[z47,z1,z2,z3,z4,z243,z6]),(0,[z568,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z228,z6]),(0,[z454,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z474,z5,z6])],[(0,[z27,z1,z2,z3,z21,z4,z6]),(0,[z1,z569,z2,z3,z4,z5,z6])],[(0,[z147,z97,z2,z3,z4,z5,z6]),(0,[z1,z2,z570,z3,z4,z5,z6]),(0,[z59,z1,z2,z3,z4,z447,z6]),(1,[z91,z1,z2,z3,z4,z50])],[(0,[z1,z571,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z436]),(0,[z1,z572,z2,z3,z4,z5,z6]),(0,[z1,z28,z2,z4,z5,z228,z6]),(0,[z1,z573,z2,z3,z4,z5,z6]),(0,[z1,z2,z61,z4,z5,z49,z6])],[(0,[z1,z420,z2,z3,z4,z5,z6]),(0,[z574,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z463,z4,z5,z6]),(0,[z1,z20,z2,z208,z3,z4,z6]),(0,[z1,z2,z3,z4,z575,z5,z6])],[(0,[z1,z2,z3,z4,z96,z228,z6]),(0,[z59,z47,z1,z2,z3,z4,z5]),(0,[z1,z576,z2,z3,z4,z5,z6]),(0,[z577,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z578,z6])]],
   [[(0,[z1,z2,z3,z4,z579,z5,z6]),(0,[z59,z1,z2,z3,z196,z5,z6]),(0,[z1,z70,z20,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z580,z6]),(0,[z1,z2,z3,z4,z581,z5,z6]),(0,[z1,z2,z3,z21,z4,z6,z48])],[(0,[z1,z2,z3,z21,z4,z67,z6]),(0,[z582,z1,z2,z3,z4,z5,z6]),(0,[z1,z28,z2,z3,z4,z162,z6]),(1,[z1,z99,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z583,z6]),(0,[z584,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z585])],[(1,[z147,z100,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z586,z6]),(0,[z587,z1,z2,z3,z4,z5,z6]),(0,[z1,z588,z2,z3,z4,z5,z6])],[(0,[z589,z1,z2,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z21,z4,z6]),(0,[z1,z2,z3,z4,z590,z5,z6]),(0,[z1,z20,z2,z3,z81,z4,z6])],[(0,[z1,z2,z3,z4,z5,z591,z6]),(0,[z592,z1,z2,z3,z4,z5,z6]),(1,[z59,z1,z3,z4,z5,z168]),(0,[z1,z2,z3,z4,z5,z6,z168]),(0,[z38,z1,z2,z3,z4,z5,z23])],[(0,[z1,z2,z3,z4,z593,z5,z6]),(0,[z1,z2,z3,z4,z5,z594,z6]),(0,[z97,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z595,z3,z4,z5,z6]),(0,[z1,z539,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z51,z46,z5,z6]),(0,[z1,z2,z3,z21,z4,z162,z6]),(0,[z1,z259,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z286,z5,z49,z6]),(0,[z1,z2,z3,z81,z5,z62,z6]),(1,[z1,z2,z527,z4,z5,z6])]],
   [[(0,[z147,z1,z2,z3,z4,z5,z6]),(0,[z27,z2,z3,z4,z96,z5,z6]),(0,[z1,z2,z3,z279,z46,z5,z6]),(0,[z1,z2,z3,z4,z596,z5,z6]),(0,[z1,z2,z3,z4,z475,z49,z6])],[(0,[z45,z1,z2,z3,z21,z4,z6]),(0,[z1,z2,z3,z4,z597,z5,z6]),(0,[z1,z2,z3,z4,z598,z5,z6])],[(1,[z1,z41,z3,z4,z5,z6]),(0,[z1,z599,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z600,z6]),(0,[z1,z2,z3,z4,z5,z601,z6]),(0,[z1,z2,z61,z3,z4,z5,z23])],[(0,[z1,z2,z3,z4,z5,z602,z6]),(0,[z1,z2,z3,z4,z5,z6,z603]),(0,[z1,z2,z3,z4,z604,z5,z6]),(0,[z133,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z605,z6]),(0,[z1,z606,z2,z3,z4,z5,z6]),(0,[z1,z496,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z21,z4,z46,z6]),(1,[z1,z2,z3,z81,z5,z62])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z607,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z196,z5,z6]),(0,[z1,z608,z2,z3,z4,z5,z6])],[(0,[z609,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z610,z5,z6])],[(0,[z1,z2,z611,z3,z4,z5,z6]),(0,[z204,z1,z129,z3,z4,z5,z6])]],
   [[(1,[z1,z16,z2,z3,z5,z6]),(1,[z1,z2,z3,z4,z243,z6]),(0,[z1,z2,z3,z21,z4,z6,z168]),(1,[z1,z9,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z72,z71,z6]),(0,[z612,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z49,z6]),(0,[z1,z3,z4,z5,z6,z143,z23]),(1,[z1,z20,z2,z3,z21,z6]),(0,[z1,z2,z3,z4,z5,z6,z50])],[(0,[z1,z613,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z614,z5,z6]),(0,[z1,z2,z3,z4,z615,z5,z6]),(0,[z1,z2,z170,z3,z46,z5,z6])],[(0,[z179,z1,z2,z129,z3,z4,z5]),(0,[z27,z1,z2,z223,z3,z4,z6]),(0,[z1,z20,z2,z3,z4,z10,z6]),(1,[z38,z1,z2,z4,z5,z23])],[(0,[z616,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z617,z6]),(0,[z1,z20,z2,z3,z21,z5,z6])],[(1,[z1,z2,z437,z3,z4,z5]),(0,[z1,z2,z3,z618,z4,z5,z6])],[(0,[z174,z1,z20,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z222,z6,z50]),(0,[z1,z2,z3,z619,z4,z5,z6]),(0,[z1,z28,z2,z3,z4,z6,z50])],[(1,[z1,z2,z3,z5,z236,z6]),(0,[z1,z2,z3,z4,z5,z620,z6])],[(1,[z45,z2,z3,z67,z5,z6]),(1,[z174,z2,z3,z175,z5,z6]),(0,[z1,z60,z2,z31,z4,z5,z6])]],
   [[(0,[z192,z1,z2,z3,z4,z5,z6]),(0,[z74,z1,z2,z185,z4,z5,z6]),(0,[z192,z1,z70,z2,z4,z5,z6]),(0,[z1,z60,z2,z101,z4,z5,z6]),(0,[z1,z621,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z46,z5,z6,z63])],[(0,[z1,z2,z3,z4,z622,z5,z6]),(0,[z47,z1,z456,z3,z4,z5,z6]),(0,[z1,z60,z2,z3,z4,z5,z6]),(0,[z1,z2,z623,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z624,z5,z6]),(1,[z1,z2,z4,z5,z6,z250])],[(0,[z74,z1,z2,z3,z21,z4,z6]),(0,[z625,z1,z2,z3,z4,z5,z6]),(1,[z1,z320,z3,z51,z5,z6]),(0,[z1,z2,z3,z279,z5,z6,z63]),(0,[z1,z2,z626,z3,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z49,z6]),(0,[z1,z524,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z6,z50])],[(0,[z1,z20,z2,z3,z4,z95,z6]),(0,[z47,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z627,z3,z4,z5,z6]),(0,[z1,z24,z3,z279,z4,z5,z6]),(0,[z65,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z628,z4,z5,z6]),(0,[z1,z20,z2,z3,z4,z103,z6]),(0,[z1,z2,z3,z4,z103,z5,z6])],[(0,[z78,z1,z2,z223,z3,z4,z6]),(0,[z1,z20,z19,z2,z3,z4,z6]),(0,[z1,z18,z2,z3,z489,z5,z6]),(0,[z59,z1,z2,z3,z4,z5,z168]),(0,[z1,z2,z629,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z6,z280])],[(0,[z1,z2,z3,z4,z5,z6,z630]),(0,[z91,z1,z2,z3,z21,z4,z6])],[(0,[z2,z129,z3,z4,z5,z6,z48]),(0,[z631,z1,z2,z3,z4,z5,z6]),(0,[z1,z217,z2,z4,z67,z5,z6]),(0,[z1,z2,z3,z4,z5,z10,z6]),(0,[z632,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z633,z6]),(0,[z1,z109,z3,z81,z4,z5,z6]),(0,[z1,z2,z3,z4,z103,z5,z50])],[(0,[z634,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z635,z3,z4,z5,z6]),(0,[z174,z2,z3,z175,z4,z5,z6]),(0,[z1,z2,z3,z4,z96,z6,z50]),(0,[z1,z18,z2,z3,z4,z8,z6]),(0,[z1,z636,z2,z3,z4,z5,z6])]],
   [[(0,[z74,z2,z3,z22,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z637]),(0,[z1,z2,z101,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z638,z5,z6]),(0,[z639,z1,z2,z3,z4,z5,z6]),(0,[z59,z1,z2,z303,z4,z5,z6]),(0,[z1,z2,z3,z640,z4,z5,z6]),(0,[z1,z641,z2,z3,z4,z5,z6]),(0,[z1,z642,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z175,z5,z6,z63]),(0,[z1,z2,z3,z643,z4,z5,z6]),(0,[z1,z2,z644,z3,z4,z5,z6]),(1,[z1,z20,z2,z3,z81,z6])],[(1,[z1,z539,z2,z4,z5,z6]),(0,[z1,z645,z2,z3,z4,z5,z6]),(0,[z646,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z647])],[(0,[z1,z2,z185,z3,z4,z5,z6]),(0,[z1,z2,z3,z455,z5,z95,z6]),(0,[z648,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z170,z171,z4,z5,z6]),(0,[z1,z2,z170,z3,z5,z6,z63]),(0,[z1,z2,z3,z4,z649,z5,z6]),(1,[z1,z3,z4,z5,z6,z143])],[(0,[z1,z2,z3,z21,z4,z96,z6]),(1,[z1,z2,z3,z4,z272,z6]),(0,[z650,z1,z2,z3,z4,z5,z6])],[(0,[z1,z20,z2,z3,z4,z51,z6]),(0,[z1,z9,z2,z3,z4,z5,z168]),(0,[z1,z20,z2,z3,z4,z6,z63]),(0,[z114,z1,z2,z3,z21,z4,z6])],[(0,[z1,z2,z3,z4,z5,z6,z651]),(0,[z1,z2,z3,z652,z4,z5,z6]),(0,[z1,z2,z3,z4,z455,z5,z6]),(0,[z1,z653,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z269,z4,z5,z6]),(0,[z1,z2,z3,z279,z81,z5,z6]),(0,[z654,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z655,z6]),(0,[z1,z2,z3,z656,z4,z5,z6])],[(0,[z1,z2,z3,z4,z657,z5,z6]),(0,[z1,z2,z3,z4,z5,z658,z6]),(0,[z1,z659,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z4,z228,z6]),(0,[z407,z1,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z535,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z660,z6]),(0,[z1,z2,z661,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z662])],[(0,[z663,z1,z2,z3,z4,z5,z6]),(0,[z1,z70,z2,z3,z171,z5,z6]),(0,[z1,z664,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z665,z6])],[(1,[z1,z2,z3,z269,z4,z6]),(0,[z565,z1,z20,z2,z3,z4,z6])],[(0,[z1,z2,z3,z666,z4,z5,z6]),(0,[z47,z1,z2,z3,z21,z4,z6])],[(0,[z1,z667,z2,z3,z4,z5,z6]),(0,[z59,z1,z3,z4,z51,z5,z6]),(0,[z1,z18,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z668,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z669,z6])],[(0,[z1,z24,z100,z3,z4,z5,z6]),(0,[z1,z2,z3,z175,z81,z5,z6]),(0,[z27,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z162,z95,z6]),(1,[z1,z2,z303,z4,z5,z6]),(1,[z1,z20,z2,z170,z3,z6]),(0,[z1,z2,z3,z4,z670,z5,z6]),(0,[z1,z2,z3,z369,z5,z86,z6])],[(0,[z192,z2,z185,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z671,z6]),(0,[z1,z20,z2,z3,z4,z6,z48]),(0,[z59,z1,z2,z3,z4,z365,z6]),(0,[z1,z70,z2,z4,z71,z5,z6]),(0,[z1,z20,z2,z3,z5,z6,z63]),(0,[z1,z2,z3,z81,z4,z5,z63])],[(0,[z1,z672,z2,z3,z4,z5,z6]),(0,[z1,z2,z115,z4,z67,z5,z6]),(0,[z1,z3,z4,z222,z5,z8,z6]),(0,[z1,z70,z2,z3,z71,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z673])]],
   [[(0,[z1,z2,z3,z674,z4,z5,z6]),(0,[z1,z2,z129,z3,z21,z4,z6]),(0,[z1,z2,z3,z4,z675,z5,z6]),(0,[z1,z2,z527,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z63])],[(0,[z1,z2,z3,z676,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z677,z6]),(0,[z1,z3,z4,z5,z6,z436,z48]),(0,[z59,z1,z9,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z6,z348])],[(0,[z1,z2,z505,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z678]),(0,[z1,z679,z2,z3,z4,z5,z6]),(0,[z1,z2,z170,z3,z4,z66,z6]),(0,[z1,z645,z2,z3,z21,z4,z6])],[(0,[z147,z1,z3,z4,z5,z10,z6]),(0,[z45,z1,z70,z2,z3,z5,z6]),(0,[z1,z2,z3,z680,z4,z5,z6]),(0,[z59,z1,z2,z3,z21,z4,z6]),(0,[z1,z20,z2,z3,z4,z162,z6])],[(0,[z1,z681,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z81,z51,z5,z6]),(0,[z133,z1,z2,z3,z81,z5,z6])],[(1,[z1,z2,z290,z3,z5,z6]),(0,[z45,z2,z3,z4,z67,z5,z6]),(0,[z1,z2,z3,z682,z4,z5,z6]),(0,[z683,z1,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z170,z3,z4,z6]),(1,[z1,z2,z3,z4,z475,z6]),(0,[z684,z1,z2,z3,z4,z5,z6])],[(0,[z1,z685,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z686,z6]),(0,[z78,z1,z2,z3,z4,z5,z6]),(0,[z1,z60,z2,z171,z4,z5,z6]),(0,[z1,z259,z3,z4,z5,z6,z23]),(0,[z1,z687,z2,z3,z4,z5,z6]),(0,[z1,z20,z621,z2,z3,z4,z6]),(0,[z1,z20,z2,z3,z439,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z688,z6]),(0,[z1,z689,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z690]),(0,[z1,z2,z3,z691,z4,z5,z6])],[(0,[z147,z1,z20,z2,z3,z4,z6]),(0,[z192,z1,z94,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z692,z5,z6]),(0,[z1,z2,z3,z4,z5,z461,z6]),(0,[z1,z60,z3,z31,z4,z5,z6]),(0,[z1,z2,z170,z3,z4,z258,z6]),(0,[z1,z20,z2,z3,z4,z46,z6]),(0,[z1,z2,z3,z4,z5,z693,z6])],[(0,[z1,z120,z2,z3,z4,z5,z6]),(0,[z174,z1,z2,z3,z21,z4,z6]),(0,[z1,z2,z3,z4,z449,z5,z6]),(0,[z1,z694,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z81,z5,z6])],[(0,[z1,z20,z2,z129,z3,z4,z6]),(0,[z74,z1,z2,z3,z4,z155,z6]),(0,[z1,z2,z3,z4,z242,z5,z6]),(0,[z1,z2,z3,z4,z695,z5,z6]),(0,[z1,z101,z3,z4,z5,z10,z6]),(0,[z1,z2,z3,z21,z4,z51,z6]),(0,[z1,z2,z3,z489,z4,z5,z6]),(1,[z1,z2,z3,z4,z365,z6]),(0,[z1,z28,z2,z61,z4,z5,z6]),(0,[z696,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z697]),(0,[z1,z2,z3,z4,z5,z6,z698]),(0,[z1,z70,z60,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z699,z6]),(0,[z45,z1,z420,z3,z4,z5,z6]),(1,[z47,z2,z3,z4,z5,z48]),(0,[z1,z700,z2,z3,z4,z5,z6]),(0,[z1,z24,z3,z4,z5,z10,z6]),(0,[z1,z20,z2,z3,z4,z6,z168]),(0,[z1,z9,z2,z3,z21,z4,z6]),(0,[z1,z2,z3,z21,z171,z4,z6]),(0,[z1,z109,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z152,z5,z6])],[(0,[z1,z2,z3,z4,z701,z5,z6]),(0,[z702,z1,z2,z3,z4,z5,z6]),(0,[z703,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z55,z6]),(0,[z1,z2,z3,z4,z5,z704,z6]),(0,[z1,z2,z3,z4,z5,z6,z215])],[(0,[z1,z19,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z705,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z59,z147,z97,z3,z4,z5]),(0,[z1,z2,z3,z4,z707,z6]),(0,[z45,z420,z3,z67,z5,z6]),(0,[z1,z2,z3,z132,z5,z6]),(0,[z1,z20,z2,z85,z4,z6]),(0,[z133,z1,z2,z3,z5,z63])],[(0,[z1,z137,z2,z4,z6,z23]),(0,[z1,z2,z302,z115,z4,z6]),(0,[z1,z708,z2,z4,z5,z6]),(0,[z47,z2,z3,z268,z5,z48]),(0,[z1,z320,z3,z51,z5,z6]),(0,[z1,z2,z3,z4,z709,z6]),(0,[z1,z70,z2,z424,z5,z6])],[(0,[z59,z1,z3,z4,z5,z136]),(0,[z1,z137,z2,z3,z4,z6]),(0,[z1,z3,z4,z5,z710,z6])],[(0,[z1,z2,z3,z4,z711,z6]),(0,[z625,z1,z20,z2,z3,z6]),(0,[z1,z2,z712,z3,z5,z6]),(0,[z1,z713,z2,z3,z4,z6]),(0,[z1,z70,z2,z257,z5,z6]),(0,[z1,z2,z3,z4,z6,z280])],[(0,[z1,z714,z2,z3,z5,z6]),(0,[z1,z137,z2,z61,z4,z6]),(0,[z40,z1,z28,z2,z4,z6]),(0,[z1,z715,z2,z3,z4,z6]),(0,[z1,z28,z2,z236,z228,z6]),(0,[z1,z716,z2,z3,z5,z6]),(1,[z1,z2,z4,z5,z717]),(0,[z1,z20,z2,z3,z4,z718])],[(0,[z1,z293,z20,z2,z3,z6]),(0,[z1,z2,z3,z719,z268,z6]),(0,[z1,z539,z20,z2,z51,z6]),(0,[z1,z2,z248,z196,z5,z6]),(0,[z1,z2,z3,z4,z720,z6]),(0,[z1,z2,z3,z4,z152,z6])],[(0,[z1,z2,z3,z721,z5,z6]),(0,[z1,z2,z3,z4,z155,z6]),(0,[z1,z94,z3,z21,z4,z6]),(0,[z1,z722,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z723,z6]),(0,[z1,z724,z3,z4,z5,z6]),(0,[z45,z20,z621,z2,z3,z6]),(0,[z1,z20,z2,z4,z75,z6]),(0,[z1,z20,z2,z3,z6,z637]),(0,[z725,z2,z3,z4,z5,z6]),(0,[z187,z2,z3,z4,z447,z6]),(0,[z1,z20,z2,z3,z357,z6]),(1,[z1,z2,z3,z5,z726]),(0,[z1,z2,z3,z5,z727,z6])]],
   [[(0,[z1,z70,z2,z255,z5,z6]),(0,[z45,z20,z2,z3,z67,z6])],[(0,[z1,z728,z2,z3,z4,z6]),(0,[z1,z2,z4,z5,z6,z729]),(0,[z1,z2,z3,z5,z6,z730]),(0,[z1,z456,z330,z4,z5,z6]),(0,[z1,z539,z2,z4,z5,z6]),(0,[z1,z60,z31,z21,z4,z6]),(0,[z731,z2,z3,z4,z5,z6]),(0,[z1,z157,z2,z3,z21,z6]),(0,[z1,z2,z3,z732,z4,z6]),(0,[z1,z733,z3,z4,z5,z6]),(0,[z1,z126,z2,z170,z3,z6]),(0,[z1,z28,z99,z2,z228,z6]),(0,[z1,z2,z3,z4,z453,z50]),(0,[z275,z146,z2,z3,z4,z6])],[(0,[z179,z1,z2,z3,z4,z5]),(0,[z45,z275,z20,z2,z3,z6]),(0,[z174,z2,z3,z175,z173,z6]),(0,[z1,z3,z4,z5,z6,z143]),(0,[z1,z2,z734,z4,z5,z6]),(0,[z1,z2,z171,z5,z6,z159]),(0,[z1,z735,z2,z3,z6,z207]),(0,[z1,z109,z3,z21,z4,z6])],[(0,[z1,z2,z3,z4,z736,z6]),(0,[z1,z2,z3,z4,z737,z6]),(0,[z542,z1,z2,z3,z4,z50]),(0,[z187,z2,z3,z196,z5,z6]),(0,[z1,z20,z2,z3,z286,z6]),(0,[z1,z496,z2,z379,z4,z6])],[(0,[z1,z2,z738,z4,z5,z6]),(0,[z179,z1,z60,z3,z4,z5]),(0,[z1,z2,z527,z5,z6,z63])],[(0,[z45,z1,z120,z2,z3,z6]),(0,[z1,z2,z3,z4,z739,z6])],[(0,[z1,z2,z4,z5,z6,z740]),(0,[z1,z2,z741,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z742]),(0,[z1,z197,z2,z3,z4,z6]),(0,[z1,z3,z135,z46,z5,z6])],[(0,[z1,z2,z743,z4,z5,z6]),(0,[z97,z246,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z744,z6]),(0,[z1,z2,z3,z4,z6,z745]),(0,[z1,z2,z3,z46,z6,z280])]],
   [[(0,[z376,z129,z3,z4,z5,z6]),(0,[z1,z2,z3,z746,z5,z6]),(0,[z1,z2,z3,z455,z461,z6]),(0,[z1,z2,z3,z4,z6,z747]),(0,[z1,z2,z3,z4,z110,z6]),(0,[z1,z2,z748,z4,z5,z6]),(0,[z1,z3,z4,z749,z5,z6])],[(0,[z45,z120,z2,z3,z67,z6]),(0,[z78,z641,z2,z3,z4,z6]),(0,[z1,z101,z4,z5,z6,z125]),(0,[z1,z2,z3,z5,z6,z750]),(0,[z1,z2,z3,z269,z4,z6]),(0,[z1,z2,z3,z4,z6,z751])],[(0,[z1,z2,z752,z4,z5,z6]),(0,[z1,z2,z753,z4,z5,z6])],[(0,[z1,z20,z2,z3,z674,z6]),(0,[z179,z1,z3,z4,z5,z168]),(0,[z1,z754,z2,z3,z5,z6]),(0,[z1,z217,z2,z4,z5,z6]),(0,[z1,z2,z3,z755,z4,z6]),(0,[z1,z2,z3,z4,z103,z156]),(0,[z1,z2,z61,z4,z5,z345]),(0,[z632,z1,z28,z2,z4,z6]),(0,[z1,z2,z3,z756,z5,z6])],[(0,[z1,z715,z2,z3,z268,z6]),(0,[z1,z2,z757,z4,z5,z6]),(0,[z1,z2,z303,z4,z5,z6]),(0,[z1,z645,z20,z2,z3,z6]),(0,[z1,z20,z2,z3,z675,z6])],[(0,[z1,z2,z758,z4,z5,z6]),(0,[z1,z2,z759,z3,z4,z6]),(0,[z179,z1,z2,z760,z4,z5]),(0,[z74,z20,z2,z22,z4,z6]),(0,[z1,z70,z197,z2,z3,z6]),(0,[z761,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z103,z86,z215])],[(0,[z45,z174,z20,z2,z3,z6]),(0,[z1,z762,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z763,z6]),(0,[z1,z2,z34,z4,z162,z6]),(0,[z47,z2,z330,z4,z5,z48]),(0,[z1,z764,z2,z4,z5,z6]),(0,[z765,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z766,z5]),(0,[z1,z2,z3,z767,z5,z6]),(0,[z768,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z51,z6]),(0,[z1,z2,z3,z258,z6,z63]),(0,[z1,z2,z3,z769,z5,z6]),(0,[z1,z20,z2,z3,z6,z63]),(0,[z1,z2,z527,z81,z5,z6])],[(0,[z1,z2,z3,z5,z6,z770]),(0,[z1,z771,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z772,z6])],[(0,[z1,z2,z3,z4,z773,z6]),(0,[z1,z2,z3,z774,z5,z6]),(0,[z1,z2,z3,z775,z5,z6]),(0,[z1,z776,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z777]),(0,[z1,z2,z303,z201,z5,z6]),(0,[z1,z2,z3,z4,z86,z315])],[(0,[z1,z2,z3,z4,z778,z6]),(0,[z97,z2,z3,z4,z5,z779]),(0,[z1,z259,z303,z4,z5,z6]),(0,[z1,z70,z2,z5,z6,z480])],[(0,[z179,z1,z2,z3,z4,z780]),(0,[z1,z2,z4,z781,z5,z6]),(0,[z1,z782,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z6,z783]),(0,[z1,z20,z2,z303,z4,z6])],[(0,[z1,z2,z3,z784,z5,z6]),(0,[z1,z785,z2,z3,z4,z6]),(0,[z1,z539,z251,z2,z4,z6]),(0,[z1,z24,z3,z279,z272,z6]),(0,[z1,z2,z4,z475,z6,z23]),(0,[z1,z2,z3,z6,z786,z207])],[(0,[z1,z2,z787,z4,z5,z6]),(0,[z1,z788,z3,z4,z5,z6]),(0,[z45,z689,z2,z3,z5,z6]),(0,[z1,z2,z170,z559,z5,z6]),(0,[z1,z2,z3,z4,z789,z6]),(0,[z1,z2,z3,z449,z243,z6]),(0,[z1,z60,z20,z31,z4,z6]),(0,[z1,z2,z21,z4,z790,z6])],[(0,[z1,z3,z4,z5,z6,z791]),(0,[z192,z1,z137,z2,z4,z6]),(0,[z1,z2,z3,z792,z5,z6]),(0,[z1,z20,z2,z3,z83,z6]),(0,[z1,z18,z3,z489,z222,z6]),(0,[z1,z2,z4,z5,z6,z717]),(0,[z1,z2,z3,z5,z793,z6]),(0,[z1,z794,z3,z4,z5,z6])]],
   [[(0,[z1,z20,z2,z3,z177,z6]),(0,[z1,z20,z2,z3,z795,z6])],[(0,[z1,z120,z2,z3,z6,z63]),(0,[z1,z2,z3,z4,z796,z6]),(0,[z59,z1,z539,z4,z5,z6]),(0,[z1,z2,z3,z4,z797,z6]),(0,[z1,z2,z3,z4,z6,z798]),(0,[z1,z2,z3,z5,z62,z726])],[(0,[z74,z2,z180,z22,z4,z6]),(0,[z1,z2,z3,z4,z5,z799]),(0,[z1,z442,z3,z4,z222,z6]),(0,[z1,z70,z2,z21,z71,z6]),(0,[z1,z2,z171,z800,z5,z6]),(0,[z1,z20,z2,z4,z6,z250])],[(0,[z1,z2,z3,z4,z5,z801]),(0,[z1,z2,z3,z4,z173,z6]),(0,[z1,z20,z2,z3,z6,z698]),(0,[z1,z802,z2,z3,z4,z6]),(0,[z1,z588,z3,z51,z5,z6]),(0,[z1,z20,z2,z3,z6,z566]),(0,[z1,z2,z170,z800,z5,z6])],[(0,[z1,z217,z2,z21,z4,z6]),(0,[z78,z16,z2,z3,z95,z6]),(0,[z1,z803,z2,z4,z5,z6]),(0,[z1,z2,z3,z804,z5,z6]),(0,[z1,z251,z2,z3,z4,z6])],[(0,[z1,z805,z2,z3,z5,z6]),(0,[z74,z689,z2,z4,z5,z6]),(0,[z1,z2,z806,z3,z5,z6]),(0,[z1,z2,z3,z489,z8,z6]),(1,[z1,z2,z800,z5,z6]),(0,[z38,z1,z20,z2,z4,z23]),(0,[z1,z2,z3,z4,z807,z6]),(0,[z1,z20,z2,z3,z6,z215])],[(0,[z1,z808,z2,z3,z449,z6]),(0,[z1,z320,z3,z804,z5,z6]),(0,[z1,z2,z4,z5,z809,z6]),(0,[z810,z2,z3,z4,z5,z6]),(0,[z1,z20,z794,z3,z4,z6])],[(0,[z239,z1,z2,z3,z5,z63]),(0,[z1,z811,z2,z4,z5,z6]),(0,[z246,z3,z4,z5,z6,z48]),(0,[z1,z2,z3,z4,z5,z779]),(0,[z1,z812,z2,z3,z4,z6]),(0,[z813,z2,z3,z4,z5,z6]),(0,[z584,z1,z70,z2,z5,z6]),(0,[z1,z2,z3,z4,z6,z814]),(0,[z1,z20,z2,z3,z4,z815]),(0,[z1,z20,z2,z3,z11,z6])]],
   [[(0,[z47,z246,z3,z4,z5,z48]),(0,[z1,z816,z2,z3,z4,z6])],[(0,[z1,z817,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z818]),(0,[z1,z2,z3,z286,z5,z6])],[(0,[z42,z129,z3,z4,z5,z6]),(0,[z1,z87,z2,z3,z21,z6]),(0,[z1,z2,z3,z4,z819,z6]),(0,[z1,z420,z3,z21,z4,z6]),(0,[z1,z2,z3,z4,z820,z6]),(0,[z1,z99,z2,z3,z96,z6]),(0,[z1,z2,z3,z821,z5,z6])],[(0,[z1,z217,z2,z302,z4,z6]),(0,[z1,z2,z822,z3,z4,z6]),(0,[z27,z1,z309,z2,z4,z6]),(0,[z187,z2,z303,z4,z5,z6]),(0,[z1,z823,z3,z4,z5,z6]),(0,[z1,z2,z4,z6,z318,z348]),(0,[z1,z2,z5,z6,z250,z215])],[(0,[z1,z681,z101,z4,z5,z6]),(0,[z45,z1,z217,z2,z5,z6]),(0,[z1,z246,z3,z21,z4,z6]),(0,[z1,z2,z3,z6,z280,z215])],[(0,[z147,z3,z4,z5,z6,z93]),(0,[z1,z824,z2,z3,z4,z6]),(0,[z174,z1,z20,z2,z3,z6]),(0,[z1,z2,z825,z4,z5,z6])],[(0,[z1,z2,z3,z4,z826,z6]),(0,[z1,z3,z279,z804,z5,z6]),(0,[z1,z99,z2,z223,z3,z6]),(0,[z1,z2,z827,z4,z5,z6])],[(0,[z204,z187,z3,z4,z5,z6]),(0,[z147,z599,z3,z4,z5,z6]),(0,[z1,z2,z3,z828,z5,z6]),(0,[z1,z2,z3,z4,z829,z6]),(0,[z1,z2,z3,z302,z4,z6]),(0,[z1,z2,z21,z115,z4,z6]),(0,[z1,z2,z455,z75,z5,z6]),(0,[z1,z20,z2,z3,z98,z6]),(0,[z1,z2,z3,z21,z489,z6]),(0,[z1,z259,z3,z21,z4,z6]),(0,[z1,z2,z3,z286,z475,z6]),(0,[z1,z2,z3,z830,z4,z6]),(0,[z1,z645,z2,z4,z39,z6])]],
   [[(0,[z1,z20,z41,z3,z5,z6]),(0,[z1,z831,z2,z3,z4,z6]),(0,[z1,z2,z3,z268,z110,z6]),(0,[z1,z2,z3,z4,z832,z6]),(0,[z1,z3,z81,z135,z5,z62])],[(0,[z65,z2,z3,z4,z5,z6]),(0,[z1,z833,z3,z4,z5,z6]),(0,[z327,z2,z3,z4,z96,z6]),(0,[z834,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z66,z6]),(0,[z1,z28,z99,z2,z3,z6]),(0,[z1,z2,z3,z6,z835,z63]),(0,[z1,z2,z3,z4,z836,z6])],[(0,[z59,z1,z246,z3,z4,z5]),(0,[z47,z256,z1,z3,z4,z5]),(0,[z1,z3,z4,z837,z8,z6]),(0,[z1,z20,z2,z527,z4,z6])],[(0,[z1,z2,z3,z4,z838,z6]),(0,[z1,z2,z290,z3,z839,z6]),(0,[z1,z176,z101,z21,z4,z6]),(0,[z1,z539,z2,z81,z5,z6]),(0,[z1,z2,z3,z489,z222,z6])],[(0,[z27,z1,z16,z2,z3,z6]),(0,[z97,z2,z231,z3,z4,z5]),(0,[z1,z3,z804,z51,z5,z6]),(0,[z1,z20,z2,z3,z81,z62]),(0,[z1,z2,z85,z21,z4,z6])],[(0,[z632,z2,z3,z4,z95,z6]),(0,[z59,z1,z20,z3,z51,z6]),(0,[z1,z840,z3,z4,z5,z6])],[(0,[z179,z1,z24,z3,z4,z5]),(0,[z1,z2,z841,z4,z5,z6]),(0,[z1,z87,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z842,z6]),(0,[z105,z1,z20,z2,z3,z6]),(0,[z1,z3,z757,z4,z5,z6]),(0,[z1,z2,z3,z4,z837,z6]),(0,[z1,z2,z3,z4,z6,z843]),(0,[z1,z2,z223,z4,z39,z6]),(0,[z123,z621,z2,z3,z4,z6]),(0,[z1,z109,z3,z4,z844,z6])],[(0,[z1,z2,z3,z4,z845,z6]),(0,[z1,z2,z3,z4,z846,z6]),(0,[z1,z2,z3,z268,z5,z6]),(0,[z1,z20,z176,z101,z4,z6]),(0,[z1,z2,z3,z21,z596,z6]),(0,[z65,z2,z3,z201,z5,z6]),(0,[z648,z1,z20,z2,z3,z6]),(0,[z1,z524,z3,z82,z4,z6])]],
   [[(0,[z1,z94,z3,z4,z5,z6]),(0,[z45,z1,z2,z3,z258,z6]),(0,[z1,z2,z4,z5,z6,z847]),(0,[z1,z2,z3,z21,z268,z6]),(0,[z1,z221,z208,z3,z4,z6]),(0,[z1,z848,z3,z21,z4,z6])],[(0,[z1,z2,z3,z849,z5,z6]),(0,[z1,z20,z2,z330,z4,z6]),(0,[z1,z20,z2,z3,z118,z6]),(0,[z187,z2,z3,z4,z365,z6]),(0,[z1,z2,z248,z21,z4,z6])],[(0,[z204,z129,z3,z21,z4,z6]),(0,[z1,z20,z2,z290,z3,z6]),(0,[z1,z850,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z851,z6]),(0,[z1,z2,z3,z21,z470,z6]),(0,[z1,z60,z757,z4,z5,z6]),(0,[z1,z852,z2,z3,z4,z6])],[(0,[z179,z2,z3,z4,z5,z48]),(0,[z1,z2,z3,z4,z853,z6]),(0,[z1,z60,z31,z4,z5,z6]),(0,[z1,z2,z3,z4,z107,z6]),(0,[z1,z2,z3,z854,z5,z6]),(0,[z1,z2,z3,z5,z6,z855]),(0,[z1,z2,z856,z21,z4,z6])],[(0,[z1,z2,z3,z4,z5,z857]),(0,[z1,z9,z3,z4,z5,z602]),(0,[z1,z109,z3,z4,z5,z6]),(0,[z1,z2,z3,z858,z5,z6]),(0,[z1,z20,z2,z3,z132,z6])],[(0,[z1,z2,z3,z4,z859,z6]),(0,[z1,z2,z860,z4,z5,z6]),(0,[z1,z456,z3,z449,z5,z6]),(0,[z1,z2,z3,z5,z6,z861]),(0,[z187,z9,z3,z4,z5,z6]),(0,[z1,z70,z20,z2,z3,z6])],[(0,[z1,z2,z3,z862,z5,z6]),(0,[z1,z2,z3,z4,z863,z6])],[(0,[z1,z2,z76,z449,z5,z6]),(0,[z1,z20,z2,z3,z449,z6]),(0,[z1,z2,z3,z864,z4,z6]),(0,[z1,z2,z3,z5,z6,z865]),(0,[z187,z2,z3,z21,z4,z6]),(0,[z1,z2,z3,z4,z866,z6]),(0,[z1,z2,z3,z21,z533,z6])]],
   [[(0,[z1,z20,z402,z2,z3,z6]),(0,[z1,z333,z3,z51,z5,z6]),(0,[z59,z1,z3,z4,z447,z168])],[(0,[z179,z1,z2,z3,z867,z5]),(0,[z59,z553,z1,z3,z4,z5]),(0,[z1,z2,z3,z4,z868,z6]),(0,[z1,z20,z505,z3,z4,z6]),(0,[z1,z2,z3,z4,z869,z6]),(0,[z1,z3,z201,z51,z5,z6]),(0,[z1,z20,z2,z3,z870,z6]),(0,[z1,z2,z3,z871,z4,z6])],[(0,[z179,z204,z129,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z872]),(0,[z1,z309,z2,z4,z5,z6]),(0,[z97,z2,z3,z21,z4,z163]),(0,[z1,z2,z3,z873,z5,z6]),(0,[z1,z101,z303,z4,z5,z6]),(0,[z1,z20,z3,z279,z51,z6]),(0,[z65,z2,z248,z4,z5,z6]),(0,[z1,z109,z3,z201,z5,z6]),(0,[z1,z20,z2,z3,z520,z6])],[(0,[z1,z2,z3,z4,z5,z874]),(0,[z1,z2,z61,z4,z5,z390]),(0,[z256,z97,z1,z3,z4,z5]),(0,[z1,z875,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z876,z6]),(0,[z1,z28,z2,z4,z408,z6]),(0,[z1,z2,z3,z4,z877,z6]),(0,[z1,z878,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z879]),(0,[z1,z3,z4,z5,z6,z880]),(0,[z574,z1,z20,z2,z3,z6]),(0,[z1,z3,z4,z135,z5,z6]),(0,[z1,z2,z881,z4,z5,z6]),(0,[z882,z1,z2,z3,z4,z6]),(0,[z1,z70,z20,z2,z170,z6])],[(0,[z59,z1,z3,z4,z5,z138]),(0,[z1,z20,z2,z69,z4,z6]),(0,[z1,z883,z2,z3,z4,z6]),(0,[z1,z20,z2,z3,z350,z6]),(0,[z1,z2,z3,z21,z369,z6])],[(0,[z1,z2,z4,z884,z5,z6]),(0,[z1,z87,z2,z180,z3,z6]),(0,[z1,z3,z4,z885,z5,z6]),(0,[z1,z2,z330,z4,z110,z6]),(1,[z2,z3,z4,z5,z779]),(0,[z1,z886,z2,z4,z5,z6]),(0,[z1,z28,z2,z4,z416,z6])],[(0,[z1,z887,z3,z4,z5,z6]),(0,[z192,z1,z87,z2,z5,z6]),(0,[z1,z70,z60,z20,z2,z6]),(0,[z1,z2,z3,z196,z447,z6]),(0,[z1,z2,z3,z888,z4,z6]),(0,[z1,z28,z2,z4,z6,z418]),(0,[z133,z1,z2,z3,z280,z63])]],
   [[(1,[z817,z3,z4,z5,z6]),(0,[z1,z889,z2,z3,z5,z6]),(0,[z1,z20,z2,z860,z4,z6])],[(0,[z432,z1,z20,z2,z3,z6]),(0,[z1,z890,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z158,z6]),(0,[z1,z2,z380,z4,z228,z6]),(0,[z1,z20,z2,z3,z6,z159]),(0,[z401,z1,z2,z3,z4,z315])],[(0,[z179,z1,z101,z3,z4,z5]),(0,[z47,z2,z3,z4,z5,z779]),(0,[z2,z3,z4,z5,z6,z891]),(0,[z1,z19,z3,z4,z8,z6]),(0,[z1,z2,z3,z892,z5,z6]),(0,[z893,z20,z2,z3,z4,z6])],[(0,[z74,z1,z87,z2,z5,z6]),(0,[z47,z2,z3,z449,z5,z48]),(0,[z1,z3,z4,z894,z5,z6]),(0,[z1,z2,z3,z895,z196,z6]),(0,[z1,z2,z170,z171,z5,z6])],[(0,[z2,z185,z841,z4,z5,z6]),(0,[z1,z2,z3,z4,z896,z6]),(0,[z1,z897,z3,z4,z5,z6]),(0,[z898,z2,z3,z4,z5,z6]),(0,[z1,z20,z99,z2,z3,z6]),(0,[z1,z2,z61,z4,z49,z54]),(0,[z1,z2,z3,z475,z6,z207]),(0,[z1,z2,z3,z4,z103,z209])],[(0,[z1,z2,z330,z4,z5,z6]),(0,[z27,z2,z3,z4,z96,z6]),(0,[z256,z1,z20,z3,z4,z6]),(0,[z1,z2,z3,z4,z899,z6]),(0,[z1,z900,z2,z3,z4,z6]),(0,[z1,z901,z3,z4,z5,z6]),(0,[z1,z2,z4,z103,z86,z250])],[(0,[z2,z3,z4,z902,z5,z6]),(0,[z1,z456,z76,z4,z5,z6]),(0,[z1,z2,z3,z21,z6,z207])],[(0,[z147,z256,z3,z4,z5,z6]),(0,[z1,z2,z3,z236,z66,z6])]],
   [[(0,[z1,z120,z2,z115,z4,z6]),(0,[z1,z20,z2,z471,z3,z6]),(0,[z1,z3,z4,z5,z10,z903]),(0,[z1,z2,z3,z4,z904,z6])],[(0,[z454,z1,z20,z2,z3,z6]),(0,[z1,z2,z3,z4,z5,z905])],[(0,[z906,z1,z3,z4,z5,z6]),(0,[z1,z16,z2,z75,z5,z6])],[(0,[z1,z2,z3,z4,z5,z907]),(0,[z429,z1,z20,z2,z3,z6]),(0,[z1,z309,z2,z21,z4,z6]),(0,[z1,z908,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z909,z6]),(0,[z1,z910,z20,z3,z4,z6])],[(0,[z74,z641,z2,z4,z5,z6]),(0,[z1,z24,z3,z804,z5,z6]),(0,[z1,z166,z3,z4,z222,z6]),(0,[z1,z2,z3,z5,z6,z207]),(0,[z1,z20,z911,z3,z4,z6]),(0,[z1,z912,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z844,z6])],[(1,[z2,z841,z4,z5,z6]),(0,[z192,z505,z185,z4,z5,z6]),(0,[z47,z20,z2,z3,z4,z48]),(0,[z1,z2,z913,z4,z5,z6]),(0,[z444,z1,z20,z2,z3,z6])],[(0,[z1,z3,z4,z5,z6,z914]),(0,[z59,z1,z3,z4,z5,z219]),(0,[z1,z915,z2,z3,z4,z6]),(0,[z1,z20,z2,z3,z669,z6]),(0,[z1,z109,z3,z4,z836,z6])],[(0,[z1,z2,z4,z162,z155,z6]),(0,[z1,z246,z3,z4,z110,z6]),(0,[z1,z916,z3,z4,z5,z6])]],
   [[(0,[z179,z1,z246,z3,z4,z5]),(0,[z179,z1,z2,z3,z917,z5]),(0,[z1,z28,z2,z4,z155,z6]),(0,[z1,z2,z4,z5,z918,z6]),(0,[z1,z539,z2,z46,z5,z6]),(0,[z1,z2,z3,z4,z919,z6])],[(0,[z1,z2,z3,z917,z5,z6]),(0,[z142,z100,z3,z4,z5,z6]),(0,[z1,z3,z920,z4,z5,z6]),(0,[z1,z309,z2,z4,z228,z6]),(0,[z1,z2,z3,z4,z103,z86])],[(0,[z179,z1,z2,z3,z4,z921]),(0,[z1,z922,z3,z4,z5,z6]),(1,[z1,z539,z20,z2,z6]),(0,[z1,z2,z3,z870,z51,z6]),(0,[z1,z923,z3,z4,z5,z6]),(0,[z1,z924,z2,z3,z5,z6]),(0,[z1,z20,z3,z81,z135,z6])],[(0,[z147,z817,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z618,z6]),(0,[z1,z2,z3,z925,z4,z6]),(0,[z1,z2,z61,z4,z5,z688]),(0,[z1,z20,z2,z3,z668,z6]),(0,[z1,z20,z2,z427,z3,z6]),(0,[z1,z2,z3,z5,z6,z926]),(0,[z1,z2,z3,z4,z905,z50])],[(0,[z1,z420,z3,z4,z5,z6]),(0,[z192,z2,z185,z21,z4,z6]),(0,[z1,z2,z223,z4,z162,z6]),(0,[z1,z2,z3,z927,z5,z6]),(0,[z1,z2,z3,z4,z103,z905])],[(0,[z1,z2,z3,z4,z242,z6]),(0,[z174,z2,z3,z21,z175,z6]),(0,[z1,z2,z3,z4,z928,z6]),(0,[z1,z3,z4,z929,z5,z6])],[(0,[z1,z246,z3,z4,z5,z6]),(0,[z174,z2,z3,z175,z461,z6]),(0,[z1,z2,z330,z21,z4,z6]),(0,[z1,z2,z3,z4,z930,z6]),(0,[z59,z1,z20,z3,z4,z168])],[(0,[z1,z2,z3,z4,z931,z6]),(0,[z1,z259,z31,z4,z5,z6])]],
   [[(0,[z154,z1,z20,z2,z3,z6]),(0,[z1,z932,z2,z3,z4,z6]),(0,[z78,z2,z4,z75,z95,z6]),(0,[z78,z621,z2,z3,z4,z6]),(0,[z1,z933,z2,z4,z5,z6]),(0,[z1,z259,z101,z4,z5,z6]),(0,[z1,z2,z3,z201,z5,z6]),(0,[z1,z2,z3,z279,z107,z6]),(0,[z1,z24,z3,z279,z21,z6]),(0,[z1,z2,z934,z4,z5,z6]),(0,[z1,z2,z3,z21,z6,z497]),(0,[z1,z935,z2,z3,z4,z6])],[(0,[z179,z1,z9,z3,z4,z5]),(0,[z936,z2,z3,z4,z5,z6]),(0,[z1,z259,z3,z4,z5,z6]),(0,[z1,z109,z3,z279,z5,z6]),(0,[z1,z18,z3,z132,z222,z6])],[(0,[z1,z3,z4,z5,z10,z525]),(0,[z1,z20,z2,z3,z104,z6]),(0,[z174,z2,z3,z670,z5,z6]),(0,[z1,z2,z3,z4,z937,z6])],[(0,[z1,z2,z3,z4,z6,z938]),(0,[z1,z20,z2,z3,z461,z6]),(0,[z1,z176,z757,z4,z5,z6]),(0,[z1,z70,z126,z2,z3,z6])],[(0,[z1,z2,z3,z4,z5,z939]),(0,[z74,z2,z290,z22,z5,z6]),(0,[z1,z2,z3,z4,z940,z6]),(0,[z1,z9,z246,z3,z4,z5]),(0,[z1,z20,z2,z170,z171,z6])],[(0,[z1,z3,z4,z5,z6,z436]),(0,[z1,z941,z2,z3,z4,z6]),(0,[z1,z176,z101,z4,z5,z6]),(0,[z1,z20,z2,z3,z269,z6]),(0,[z1,z3,z4,z222,z837,z6]),(0,[z1,z20,z2,z827,z4,z6])],[(0,[z59,z65,z3,z4,z5,z168]),(0,[z1,z20,z2,z3,z274,z6]),(0,[z1,z2,z85,z4,z5,z6]),(0,[z1,z2,z3,z5,z704,z63])],[(0,[z942,z1,z2,z3,z4,z5]),(0,[z1,z2,z4,z5,z943,z6]),(0,[z1,z20,z2,z3,z312,z6]),(0,[z1,z2,z303,z4,z447,z6]),(0,[z1,z20,z912,z2,z4,z6]),(0,[z1,z2,z3,z4,z5,z726])]],
   [[(0,[z1,z944,z3,z4,z5,z6]),(0,[z1,z60,z427,z4,z5,z6]),(0,[z1,z945,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z81,z523]),(0,[z1,z20,z2,z3,z55,z6]),(0,[z261,z2,z3,z535,z4,z6]),(0,[z1,z2,z946,z21,z4,z6])],[(0,[z1,z2,z3,z4,z947,z6]),(0,[z1,z20,z2,z3,z279,z6])],[(0,[z1,z2,z3,z4,z948,z6]),(0,[z1,z848,z3,z4,z5,z6]),(0,[z1,z2,z3,z949,z5,z6]),(0,[z2,z3,z4,z5,z6,z779]),(0,[z1,z539,z2,z5,z6,z63]),(0,[z1,z20,z2,z3,z196,z6])],[(0,[z1,z20,z2,z3,z284,z6]),(0,[z1,z2,z3,z950,z4,z6]),(0,[z1,z2,z248,z4,z5,z6]),(0,[z951,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z380,z3,z6]),(0,[z1,z2,z3,z81,z5,z209]),(0,[z1,z2,z3,z5,z726,z63])],[(0,[z204,z129,z3,z4,z5,z6]),(0,[z1,z2,z3,z952,z5,z6]),(0,[z1,z70,z2,z514,z5,z6]),(0,[z1,z953,z2,z3,z4,z6]),(0,[z1,z24,z3,z279,z5,z6]),(0,[z1,z524,z3,z4,z8,z6]),(0,[z1,z2,z380,z463,z4,z6])],[(0,[z1,z2,z954,z4,z5,z6]),(0,[z1,z539,z100,z4,z5,z6]),(0,[z1,z2,z3,z455,z5,z6]),(0,[z1,z2,z856,z4,z5,z6]),(0,[z1,z2,z330,z268,z5,z6]),(0,[z1,z20,z2,z3,z531,z6]),(0,[z454,z2,z3,z404,z4,z6])],[(0,[z1,z24,z3,z355,z5,z6]),(0,[z1,z955,z3,z4,z5,z6])],[(0,[z1,z3,z21,z4,z6,z436]),(0,[z1,z2,z3,z269,z46,z6]),(0,[z1,z20,z2,z3,z295,z6]),(0,[z1,z2,z956,z4,z5,z6]),(0,[z133,z1,z2,z3,z5,z726])]],
   [[(0,[z1,z2,z3,z4,z839,z6]),(0,[z1,z2,z957,z4,z5,z6]),(0,[z1,z456,z3,z4,z243,z6]),(0,[z1,z9,z627,z3,z4,z5]),(0,[z958,z2,z3,z4,z5,z6]),(0,[z1,z2,z269,z69,z4,z6]),(0,[z1,z2,z81,z5,z62,z318])],[(0,[z187,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z959,z5,z6]),(0,[z97,z187,z2,z3,z4,z5]),(0,[z1,z2,z248,z201,z5,z6]),(0,[z1,z20,z2,z300,z3,z6]),(0,[z1,z960,z3,z4,z5,z6]),(0,[z1,z2,z85,z4,z103,z6])],[(0,[z43,z2,z185,z4,z5,z6]),(0,[z1,z2,z76,z4,z243,z6]),(0,[z1,z808,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z961]),(0,[z59,z1,z3,z4,z365,z168]),(0,[z1,z2,z3,z81,z152,z6])],[(0,[z1,z20,z2,z437,z3,z4]),(0,[z1,z2,z3,z732,z201,z6]),(0,[z1,z2,z3,z962,z5,z6]),(0,[z1,z2,z223,z4,z963,z6]),(0,[z1,z3,z21,z4,z135,z6])],[(0,[z1,z309,z2,z4,z155,z6]),(0,[z1,z217,z2,z5,z6,z63]),(0,[z1,z20,z2,z3,z64,z6]),(0,[z97,z2,z3,z4,z5,z163]),(0,[z1,z20,z2,z3,z555,z6]),(0,[z1,z2,z964,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z965]),(0,[z1,z2,z61,z4,z475,z49])],[(0,[z1,z2,z4,z5,z6,z966]),(0,[z1,z457,z101,z4,z5,z6]),(0,[z1,z20,z2,z3,z4,z879]),(0,[z1,z20,z2,z3,z6,z315]),(0,[z1,z636,z20,z2,z3,z6])],[(0,[z1,z2,z3,z4,z967,z6]),(0,[z1,z968,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z318]),(0,[z1,z160,z2,z3,z4,z209])],[(0,[z1,z2,z3,z4,z969,z6]),(0,[z1,z2,z4,z5,z6,z970])]],
   [[(0,[z1,z2,z3,z971,z4,z6]),(0,[z1,z2,z3,z4,z921,z6]),(0,[z1,z972,z3,z4,z5,z6]),(0,[z1,z539,z20,z2,z4,z6]),(0,[z1,z18,z3,z4,z222,z6]),(0,[z582,z1,z20,z2,z3,z6]),(0,[z1,z20,z2,z3,z6,z84])],[(0,[z1,z2,z3,z973,z5,z6]),(0,[z174,z2,z3,z902,z5,z6]),(0,[z1,z2,z3,z81,z5,z686]),(0,[z1,z2,z3,z4,z6,z974]),(0,[z975,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z976,z5,z6]),(0,[z1,z2,z3,z196,z365,z6]),(0,[z1,z977,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z905])],[(0,[z1,z2,z4,z5,z6,z978]),(0,[z1,z2,z3,z449,z110,z6]),(0,[z187,z3,z4,z51,z5,z6]),(0,[z1,z20,z2,z3,z6,z92]),(0,[z1,z2,z3,z4,z6,z979]),(0,[z1,z2,z4,z162,z6,z534]),(0,[z1,z2,z61,z4,z475,z6])],[(0,[z1,z980,z3,z4,z5,z6]),(0,[z1,z2,z3,z489,z5,z6]),(0,[z1,z320,z69,z51,z5,z6]),(0,[z1,z20,z2,z3,z481,z6])],[(0,[z1,z981,z2,z4,z5,z6]),(0,[z1,z20,z100,z3,z51,z6]),(0,[z192,z2,z305,z4,z5,z6]),(0,[z1,z3,z668,z51,z5,z6]),(0,[z1,z20,z2,z3,z495,z6]),(0,[z1,z2,z3,z4,z72,z6])],[(0,[z74,z87,z2,z22,z5,z6]),(0,[z1,z982,z3,z4,z5,z6]),(0,[z1,z2,z3,z81,z62,z348])],[(0,[z1,z2,z3,z983,z4,z6]),(0,[z1,z246,z3,z268,z5,z6]),(0,[z47,z2,z3,z4,z243,z48]),(0,[z1,z2,z3,z5,z111,z63])],[(0,[z179,z97,z2,z3,z4,z5]),(0,[z1,z20,z2,z3,z581,z6]),(0,[z1,z20,z2,z3,z550,z6]),(0,[z1,z984,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z985]),(0,[z986,z2,z3,z4,z5,z6]),(0,[z1,z2,z170,z171,z258,z6]),(0,[z1,z2,z61,z21,z4,z49])]],
   [[(0,[z1,z217,z2,z81,z5,z6]),(0,[z1,z70,z20,z2,z71,z6]),(0,[z987,z1,z2,z3,z5,z6]),(0,[z1,z28,z2,z4,z228,z6]),(0,[z1,z2,z21,z4,z6,z318])],[(0,[z1,z2,z3,z449,z5,z6]),(0,[z2,z3,z175,z902,z5,z6]),(0,[z2,z3,z4,z96,z988,z6]),(0,[z1,z3,z4,z590,z5,z10]),(0,[z1,z20,z2,z3,z6,z117]),(0,[z1,z2,z223,z4,z6,z647])],[(0,[z1,z989,z2,z3,z5,z6]),(0,[z1,z217,z20,z2,z4,z6]),(0,[z1,z2,z3,z990,z5,z6]),(0,[z187,z2,z248,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z903]),(0,[z1,z2,z379,z4,z162,z6]),(0,[z1,z960,z3,z21,z4,z6])],[(0,[z179,z1,z2,z991,z4,z5]),(0,[z362,z1,z20,z2,z3,z6]),(0,[z2,z3,z4,z988,z5,z6]),(0,[z1,z539,z320,z51,z5,z6]),(0,[z1,z992,z3,z4,z5,z6]),(0,[z91,z1,z2,z3,z4,z523])],[(0,[z1,z2,z3,z867,z5,z6]),(0,[z1,z2,z993,z3,z4,z6]),(0,[z1,z2,z4,z162,z556,z6]),(0,[z45,z2,z115,z67,z5,z6]),(0,[z1,z2,z223,z206,z4,z6])],[(0,[z1,z101,z757,z4,z5,z6]),(0,[z1,z20,z2,z3,z128,z6]),(0,[z1,z2,z3,z5,z6,z215]),(0,[z1,z2,z994,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z905])],[(0,[z194,z129,z3,z4,z5,z6]),(0,[z1,z87,z137,z2,z3,z6]),(0,[z1,z2,z3,z995,z5,z6]),(0,[z1,z996,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z997,z6]),(0,[z1,z2,z3,z4,z998,z6]),(0,[z1,z999,z2,z3,z4,z6]),(0,[z1,z2,z3,z21,z46,z6])],[(0,[z1,z2,z437,z3,z21,z4]),(0,[z1,z2,z1000,z4,z5,z6]),(0,[z78,z2,z3,z4,z95,z6]),(0,[z1,z3,z4,z5,z1001,z6]),(0,[z1,z20,z2,z3,z361,z6]),(0,[z59,z1,z3,z196,z5,z168]),(0,[z1,z20,z2,z61,z4,z49]),(0,[z1,z20,z1002,z3,z4,z6]),(0,[z1003,z1,z2,z4,z5,z6]),(0,[z1,z968,z3,z21,z4,z6]),(0,[z1,z2,z527,z81,z5,z62])]],
   [[(0,[z1,z2,z3,z4,z1004,z6]),(0,[z1,z2,z3,z4,z5,z1005]),(0,[z1,z2,z3,z21,z488,z6]),(0,[z1,z3,z4,z837,z5,z6]),(0,[z1,z20,z2,z248,z4,z6]),(0,[z1,z2,z3,z4,z66,z6]),(0,[z1,z451,z20,z2,z3,z6]),(1,[z1,z2,z3,z1006,z6])],[(0,[z256,z187,z3,z4,z5,z6]),(0,[z1,z1007,z2,z3,z4,z6]),(0,[z1,z2,z1008,z4,z5,z6])],[(0,[z1,z1009,z2,z3,z4,z6]),(0,[z1,z2,z180,z290,z3,z6]),(0,[z1,z2,z3,z4,z6,z1010]),(0,[z1,z20,z2,z115,z4,z6]),(0,[z1,z2,z3,z1011,z5,z6])],[(0,[z1,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z1012,z4,z6]),(0,[z1,z2,z3,z902,z5,z6]),(0,[z1,z2,z3,z4,z1013,z6]),(0,[z1,z2,z1014,z4,z5,z6]),(0,[z1,z1015,z2,z3,z196,z6]),(0,[z1,z2,z4,z963,z228,z6]),(0,[z1,z2,z3,z6,z207,z54]),(0,[z1,z32,z3,z4,z474,z6])],[(0,[z817,z2,z3,z4,z5,z6]),(0,[z1,z2,z1016,z4,z5,z6]),(0,[z74,z137,z2,z22,z4,z6]),(0,[z1,z20,z2,z3,z455,z6]),(0,[z1,z2,z3,z4,z1017,z6])],[(0,[z1,z1018,z2,z3,z4,z6]),(0,[z47,z3,z4,z5,z436,z48]),(0,[z1,z2,z3,z1019,z5,z6])],[(0,[z192,z2,z185,z4,z5,z6]),(0,[z1,z2,z3,z4,z258,z6]),(0,[z1,z20,z3,z4,z6,z143])],[(0,[z1,z2,z3,z4,z780,z6]),(0,[z1,z2,z3,z4,z1020,z6]),(0,[z192,z20,z2,z185,z4,z6]),(0,[z174,z1,z120,z2,z3,z6]),(0,[z1,z1021,z2,z3,z4,z6]),(0,[z1,z3,z804,z4,z5,z6]),(0,[z1,z2,z369,z5,z6,z250])]],
   [[(0,[z1,z1022,z3,z4,z5,z6]),(0,[z1,z1023,z3,z4,z5,z6]),(0,[z1,z309,z2,z4,z103,z6]),(0,[z1,z2,z3,z1024,z5,z6]),(0,[z1,z2,z3,z4,z6,z1025]),(0,[z1,z24,z3,z279,z107,z6]),(0,[z1,z24,z3,z201,z5,z6]),(0,[z1,z2,z3,z4,z5,z718]),(0,[z1,z28,z2,z439,z4,z6]),(0,[z1,z20,z2,z3,z385,z6])],[(0,[z1,z2,z170,z21,z171,z6]),(0,[z1,z20,z2,z3,z1006,z6]),(0,[z1,z2,z3,z283,z369,z6])],[(0,[z406,z129,z3,z4,z5,z6]),(0,[z1,z2,z1026,z4,z5,z6]),(0,[z1027,z1,z87,z2,z3,z6]),(0,[z1,z20,z2,z3,z6,z392]),(0,[z1,z2,z3,z21,z201,z6]),(0,[z1,z2,z3,z1028,z5,z6])],[(0,[z1,z1029,z2,z4,z5,z6]),(0,[z1,z2,z4,z790,z5,z6]),(0,[z1,z2,z3,z1030,z5,z6]),(0,[z1,z2,z3,z82,z489,z6]),(0,[z1,z1031,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1032]),(0,[z1,z1033,z3,z4,z5,z6])],[(0,[z1,z2,z1034,z4,z5,z6]),(0,[z1,z120,z2,z3,z4,z6]),(0,[z1,z2,z4,z5,z1035,z6]),(0,[z1036,z1,z3,z4,z5,z6]),(0,[z1,z246,z330,z4,z5,z6]),(0,[z1,z20,z456,z3,z4,z6])],[(0,[z74,z1,z70,z20,z2,z6]),(0,[z1,z1037,z3,z4,z5,z6]),(0,[z149,z1,z70,z2,z5,z6]),(0,[z45,z41,z3,z67,z5,z6]),(0,[z1,z2,z1038,z4,z5,z6]),(0,[z1,z2,z3,z4,z963,z6]),(0,[z1,z20,z2,z3,z6,z200])],[(0,[z1,z2,z3,z4,z1039,z6]),(0,[z1,z2,z3,z1040,z4,z6]),(0,[z1,z2,z3,z1041,z5,z6]),(0,[z1,z2,z3,z21,z132,z6]),(0,[z1,z2,z994,z21,z4,z6])],[(0,[z187,z60,z3,z4,z5,z6]),(0,[z1,z539,z4,z5,z10,z6]),(0,[z1,z20,z2,z3,z640,z6]),(0,[z1,z197,z2,z170,z3,z6]),(0,[z1,z20,z2,z3,z691,z6])]],
   [[(0,[z1,z178,z3,z51,z5,z6]),(0,[z1,z2,z1042,z4,z5,z6]),(0,[z1,z2,z180,z3,z4,z6]),(0,[z1,z309,z2,z455,z5,z6]),(0,[z1,z2,z3,z4,z1043,z6]),(0,[z417,z1,z166,z3,z4,z6])],[(0,[z256,z1,z3,z4,z5,z6]),(1,[z1,z714,z2,z3,z6]),(0,[z1,z1044,z2,z3,z5,z6]),(0,[z1,z94,z171,z4,z5,z6]),(0,[z1,z2,z303,z4,z365,z6]),(0,[z1,z2,z3,z21,z52,z6])],[(0,[z1,z2,z991,z4,z5,z6]),(0,[z1,z2,z3,z1045,z5,z6]),(0,[z59,z187,z3,z4,z5,z168]),(0,[z1,z70,z2,z72,z71,z6]),(0,[z1,z2,z946,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1046,z6]),(0,[z1,z20,z2,z3,z518,z6]),(0,[z78,z1,z309,z2,z4,z6]),(0,[z27,z2,z3,z4,z988,z6]),(0,[z1,z20,z2,z3,z268,z6]),(0,[z1,z2,z3,z1047,z4,z6]),(0,[z1,z2,z3,z5,z1048,z6]),(0,[z1,z2,z3,z4,z6,z1049]),(0,[z1,z2,z3,z4,z1050,z6]),(0,[z1,z262,z20,z2,z3,z6])],[(0,[z179,z204,z1,z3,z4,z5]),(0,[z179,z1,z3,z4,z51,z5]),(0,[z1,z2,z3,z4,z5,z1051]),(0,[z1,z2,z3,z1052,z4,z6]),(0,[z1,z3,z4,z5,z6,z1053]),(0,[z45,z621,z2,z3,z5,z6]),(0,[z1,z2,z171,z555,z5,z6]),(0,[z1,z20,z2,z3,z415,z6]),(0,[z1,z2,z3,z4,z1054,z6])],[(0,[z47,z456,z3,z4,z5,z48]),(0,[z1,z2,z3,z1055,z4,z6]),(0,[z1,z2,z4,z5,z963,z6]),(0,[z1,z20,z2,z3,z236,z6]),(0,[z1,z20,z2,z3,z202,z6]),(0,[z1,z2,z85,z4,z6,z50])],[(0,[z1,z60,z676,z4,z5,z6]),(0,[z1,z911,z3,z4,z5,z6]),(0,[z1,z2,z3,z81,z5,z501]),(0,[z1,z2,z3,z5,z6,z1056])],[(0,[z1,z2,z3,z1057,z4,z6]),(0,[z1,z1058,z2,z3,z4,z6]),(0,[z1,z2,z3,z5,z6,z1059]),(0,[z47,z2,z76,z4,z5,z48]),(0,[z1,z20,z992,z3,z4,z6]),(0,[z1,z20,z2,z3,z6,z835]),(0,[z1,z910,z3,z4,z5,z6])]],
   [[(0,[z1,z1060,z2,z4,z5,z6]),(0,[z1,z2,z1061,z4,z5,z6]),(0,[z1,z2,z3,z1062,z449,z6]),(0,[z47,z187,z2,z3,z4,z5]),(0,[z1,z2,z1063,z4,z5,z6]),(0,[z1,z320,z3,z269,z51,z6]),(0,[z1,z2,z3,z4,z5,z717]),(0,[z1,z2,z4,z5,z6,z1064]),(0,[z1,z2,z3,z1065,z5,z6])],[(0,[z1,z2,z290,z3,z1046,z6]),(0,[z1,z3,z4,z5,z6,z1066]),(0,[z1,z1067,z3,z4,z5,z6]),(0,[z1,z456,z3,z21,z4,z6]),(0,[z1,z251,z2,z3,z81,z6]),(0,[z187,z24,z3,z4,z5,z6]),(0,[z761,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1068]),(0,[z1,z735,z2,z3,z4,z6])],[(0,[z74,z2,z841,z4,z5,z6]),(0,[z1,z70,z2,z3,z173,z6]),(0,[z1,z2,z1069,z4,z5,z6]),(0,[z1,z2,z3,z81,z5,z601])],[(0,[z1,z2,z760,z4,z5,z6]),(0,[z1,z2,z1070,z4,z5,z6]),(0,[z1,z1071,z87,z2,z3,z6]),(0,[z1,z1072,z3,z4,z5,z6]),(0,[z1,z2,z3,z1073,z4,z6]),(0,[z1,z2,z76,z21,z4,z6]),(0,[z1,z757,z31,z4,z5,z6]),(0,[z1,z2,z3,z4,z1074,z6]),(0,[z1,z20,z2,z277,z3,z6]),(0,[z1,z2,z4,z162,z963,z6]),(0,[z1,z2,z3,z1075,z4,z6]),(0,[z1,z20,z2,z3,z4,z961]),(0,[z1,z20,z923,z3,z4,z6])],[(0,[z74,z2,z22,z21,z4,z6]),(0,[z1,z2,z3,z4,z6,z1076]),(0,[z174,z1,z1018,z2,z3,z6]),(0,[z78,z1,z16,z2,z3,z6]),(0,[z47,z256,z3,z4,z5,z48]),(0,[z1,z1077,z2,z3,z4,z6]),(0,[z1,z1078,z2,z3,z5,z6]),(0,[z1,z1079,z3,z4,z5,z6]),(0,[z1,z28,z2,z4,z963,z6])],[(0,[z45,z2,z3,z21,z67,z6]),(0,[z97,z20,z2,z3,z4,z163]),(0,[z65,z20,z2,z3,z4,z6]),(0,[z1,z2,z4,z5,z473,z23])],[(1,[z1,z20,z41,z3,z6]),(0,[z1,z2,z3,z4,z988,z6]),(0,[z1,z70,z20,z176,z2,z6]),(0,[z1,z1080,z2,z3,z4,z6]),(0,[z1,z20,z2,z3,z81,z63]),(0,[z1,z2,z3,z369,z5,z6])],[(0,[z1,z2,z3,z4,z1081,z6]),(0,[z59,z1,z303,z4,z5,z168])]],
   [[(0,[z1,z16,z2,z3,z21,z6]),(0,[z1,z2,z3,z4,z1082,z6]),(0,[z1,z2,z3,z21,z286,z6]),(0,[z1,z816,z2,z3,z286,z6]),(0,[z1,z20,z2,z3,z263,z6]),(0,[z1,z20,z2,z3,z369,z6]),(0,[z1,z2,z85,z4,z103,z86])],[(0,[z45,z1,z20,z420,z3,z6]),(0,[z1,z309,z2,z4,z162,z6]),(0,[z1,z2,z3,z1083,z5,z6]),(0,[z1,z2,z3,z4,z1084,z6])],[(0,[z1,z2,z3,z1085,z5,z6]),(1,[z2,z3,z902,z5,z6]),(0,[z1,z20,z16,z2,z3,z6]),(0,[z1,z2,z3,z4,z1086,z6]),(0,[z256,z1,z3,z21,z4,z6]),(0,[z1,z2,z4,z5,z6,z1087]),(0,[z1,z2,z3,z795,z4,z6]),(0,[z1,z2,z3,z4,z1088,z6])],[(0,[z1,z2,z3,z4,z1089,z6]),(0,[z45,z1,z20,z2,z3,z6])],[(0,[z1,z505,z3,z21,z4,z6]),(0,[z1,z1090,z3,z4,z5,z6]),(0,[z45,z2,z3,z302,z67,z6]),(0,[z1,z2,z21,z4,z75,z6]),(0,[z1,z2,z3,z4,z1091,z6]),(0,[z1,z20,z2,z3,z6,z280])],[(0,[z1,z1092,z2,z3,z4,z6]),(0,[z1,z539,z20,z2,z5,z6]),(0,[z1,z2,z3,z4,z447,z6]),(0,[z1,z18,z3,z4,z474,z6]),(0,[z1,z2,z3,z4,z5,z1093]),(0,[z1,z20,z2,z3,z474,z6]),(0,[z1,z109,z20,z3,z4,z6]),(0,[z1,z2,z527,z4,z6,z348])],[(0,[z179,z147,z1,z3,z4,z5]),(0,[z1,z41,z3,z4,z5,z6]),(0,[z174,z1,z217,z2,z5,z6]),(0,[z1,z176,z4,z624,z5,z6]),(0,[z1094,z2,z3,z4,z5,z6]),(0,[z1,z2,z303,z196,z5,z6]),(0,[z1,z2,z3,z4,z211,z50])],[(0,[z1,z1095,z2,z3,z4,z6]),(0,[z192,z94,z185,z4,z5,z6]),(0,[z491,z2,z3,z4,z95,z6]),(0,[z47,z2,z3,z21,z4,z48]),(0,[z1,z2,z3,z895,z4,z6]),(0,[z1,z1096,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z1097,z6]),(0,[z1,z2,z3,z1098,z5,z6]),(0,[z45,z1,z20,z41,z3,z6]),(0,[z1,z2,z3,z5,z6,z1099]),(0,[z38,z1,z2,z4,z5,z717])],[(0,[z1,z539,z129,z4,z5,z6]),(0,[z1,z137,z2,z290,z3,z6]),(0,[z1,z309,z20,z2,z4,z6]),(0,[z1,z251,z2,z3,z6,z63]),(0,[z1,z2,z61,z4,z5,z49]),(0,[z1,z2,z3,z369,z103,z6])],[(0,[z97,z9,z129,z3,z4,z5]),(0,[z1,z2,z3,z1100,z4,z5]),(0,[z78,z309,z2,z4,z95,z6]),(0,[z1,z2,z3,z4,z6,z1101]),(0,[z1,z2,z85,z369,z5,z6])],[(0,[z1,z2,z3,z4,z1102,z6]),(0,[z1,z2,z3,z4,z5,z815]),(0,[z1,z2,z3,z201,z447,z6]),(0,[z1,z2,z3,z4,z6,z835])],[(0,[z1,z16,z2,z3,z5,z6]),(0,[z45,z2,z3,z902,z5,z6]),(0,[z1,z2,z3,z4,z243,z6]),(0,[z1,z2,z61,z5,z49,z207]),(0,[z1,z20,z2,z3,z21,z6])],[(0,[z1,z20,z2,z3,z682,z6]),(0,[z38,z1,z259,z4,z5,z23])],[(0,[z1,z2,z3,z1103,z5,z6]),(0,[z1,z2,z3,z1104,z5,z6]),(0,[z1,z1105,z2,z3,z5,z6]),(0,[z1106,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z590,z6]),(0,[z1,z70,z2,z439,z5,z6]),(0,[z1107,z2,z3,z4,z5,z6]),(0,[z38,z1,z2,z4,z5,z23])],[(0,[z45,z217,z2,z67,z5,z6]),(0,[z1,z2,z330,z449,z5,z6]),(0,[z1,z320,z3,z21,z51,z6]),(0,[z1,z2,z3,z4,z1108,z6])]],
   [[(0,[z1,z2,z437,z3,z4,z5]),(0,[z1,z2,z3,z1109,z4,z6]),(0,[z1,z20,z41,z3,z4,z6]),(0,[z1,z2,z3,z4,z1110,z6])],[(0,[z97,z2,z3,z4,z5,z349]),(0,[z1,z2,z3,z4,z1111,z6]),(0,[z1,z1112,z3,z4,z5,z6]),(1,[z1,z757,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z786]),(0,[z1,z20,z2,z249,z3,z6]),(0,[z1,z2,z3,z4,z6,z1113])],[(0,[z1,z20,z2,z3,z593,z6]),(0,[z1,z2,z3,z1114,z5,z6]),(0,[z1,z1115,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z461,z6]),(0,[z275,z2,z3,z4,z96,z6]),(0,[z187,z2,z3,z201,z5,z6]),(0,[z1,z2,z3,z5,z236,z6]),(0,[z38,z1,z4,z5,z143,z23])],[(0,[z1,z1116,z2,z3,z4,z6]),(0,[z45,z2,z3,z67,z5,z6]),(0,[z59,z1,z3,z21,z4,z168]),(0,[z1,z20,z2,z644,z3,z6]),(0,[z1,z687,z20,z2,z3,z6])],[(0,[z1,z20,z2,z3,z692,z6]),(0,[z1,z1117,z3,z4,z5,z6]),(0,[z2,z3,z902,z67,z5,z6]),(0,[z1,z309,z2,z4,z6,z50]),(0,[z27,z2,z532,z3,z4,z6]),(0,[z1,z20,z2,z3,z343,z6]),(0,[z1,z2,z170,z171,z66,z6]),(0,[z1,z2,z527,z21,z4,z6])],[(0,[z1,z70,z94,z4,z5,z6]),(0,[z1,z2,z3,z1118,z5,z6]),(0,[z59,z406,z1,z3,z4,z5]),(0,[z1,z2,z4,z5,z6,z250])],[(0,[z1,z20,z178,z2,z3,z6]),(0,[z1,z2,z248,z4,z447,z6]),(0,[z59,z1,z3,z4,z5,z903])],[(0,[z147,z187,z3,z4,z5,z6]),(0,[z1,z41,z3,z21,z4,z6]),(0,[z1,z16,z2,z3,z103,z6]),(0,[z1,z19,z3,z4,z837,z6])]],
   [[(0,[z1,z20,z129,z3,z51,z6]),(0,[z174,z20,z2,z3,z175,z6]),(0,[z1,z20,z2,z3,z435,z6]),(0,[z1,z539,z2,z269,z4,z6]),(0,[z1,z2,z3,z1119,z4,z6]),(0,[z1,z2,z4,z800,z5,z6])],[(0,[z507,z100,z3,z4,z5,z6]),(0,[z1,z2,z3,z1120,z5,z6]),(0,[z1,z20,z2,z41,z3,z6]),(0,[z1,z2,z1121,z3,z4,z6]),(0,[z1,z2,z170,z3,z173,z6]),(0,[z1,z2,z1122,z4,z5,z6]),(0,[z1,z2,z1123,z4,z5,z6]),(0,[z1,z2,z1124,z4,z5,z6]),(0,[z1,z166,z3,z279,z5,z6]),(0,[z1,z70,z2,z800,z5,z6]),(0,[z1,z2,z3,z800,z5,z6]),(0,[z1,z70,z20,z2,z6,z23]),(0,[z1,z70,z20,z2,z439,z6]),(0,[z1,z2,z3,z4,z103,z345]),(0,[z1,z2,z3,z871,z286,z6])],[(0,[z1,z2,z1125,z4,z5,z6]),(0,[z1,z2,z3,z269,z132,z6]),(0,[z1,z259,z171,z4,z5,z6]),(0,[z1,z2,z3,z21,z6,z215]),(0,[z133,z1,z197,z2,z3,z63])],[(0,[z1,z28,z2,z33,z4,z6]),(0,[z1,z2,z1126,z4,z5,z6]),(0,[z1,z126,z2,z3,z4,z6]),(0,[z1,z2,z61,z286,z5,z49])],[(0,[z1127,z1,z2,z3,z4,z5]),(0,[z1,z1128,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1129]),(0,[z1,z3,z4,z5,z10,z68]),(0,[z1,z2,z3,z21,z196,z6]),(0,[z1,z3,z4,z5,z6,z1130])],[(0,[z74,z2,z22,z4,z155,z6]),(1,[z2,z3,z4,z988,z6]),(0,[z1,z9,z3,z21,z4,z10]),(0,[z1,z20,z2,z3,z81,z6])],[(0,[z129,z3,z4,z5,z6,z136]),(0,[z256,z129,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1131,z6]),(0,[z1,z87,z2,z5,z6,z23]),(0,[z1,z1132,z2,z3,z5,z6]),(0,[z1,z2,z3,z46,z461,z6]),(0,[z1,z20,z2,z76,z4,z6]),(0,[z2,z3,z4,z5,z779,z48]),(0,[z2,z3,z4,z5,z163,z779]),(0,[z1,z2,z3,z4,z103,z443])],[(0,[z65,z2,z3,z4,z447,z6]),(0,[z38,z1,z2,z21,z4,z23]),(0,[z1,z2,z21,z4,z6,z250])]],
   [[(0,[z1,z2,z3,z1133,z4,z6]),(0,[z1,z2,z3,z1134,z5,z6]),(0,[z78,z2,z3,z4,z988,z6]),(0,[z1,z246,z3,z449,z5,z6]),(0,[z1,z1135,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z272,z6]),(0,[z376,z1,z20,z2,z3,z6]),(0,[z187,z3,z4,z5,z6,z168])],[(0,[z1,z2,z3,z4,z1136,z6]),(0,[z1,z20,z2,z294,z3,z6]),(0,[z1,z2,z4,z5,z6,z1137]),(1,[z1,z3,z804,z5,z6]),(1,[z1,z3,z4,z5,z903]),(0,[z1,z2,z61,z286,z5,z6])],[(0,[z261,z1,z20,z2,z3,z6]),(0,[z261,z1,z16,z2,z3,z6])],[(0,[z204,z817,z3,z4,z5,z6]),(0,[z1,z1138,z2,z3,z4,z6]),(0,[z1,z2,z1139,z4,z5,z6]),(0,[z1,z16,z2,z3,z228,z6]),(0,[z1,z2,z3,z1140,z5,z6]),(0,[z65,z2,z3,z196,z5,z6]),(0,[z1,z20,z2,z825,z4,z6])],[(0,[z204,z437,z129,z3,z4,z5]),(0,[z1,z2,z3,z1141,z155,z6]),(0,[z1,z1142,z3,z4,z5,z6]),(0,[z1,z456,z3,z4,z110,z6]),(0,[z1,z2,z3,z4,z1143,z6])],[(0,[z1,z2,z3,z4,z1144,z6]),(0,[z1,z2,z3,z5,z1145,z6]),(0,[z1,z2,z3,z870,z4,z6]),(0,[z2,z3,z4,z5,z6,z1146]),(0,[z1,z2,z3,z1147,z5,z6]),(0,[z1,z1148,z2,z3,z5,z6]),(1,[z1,z20,z3,z135,z6])],[(0,[z1,z2,z290,z3,z21,z6]),(0,[z1,z120,z2,z3,z81,z6]),(0,[z1,z2,z76,z4,z110,z6])],[(0,[z179,z1,z20,z2,z3,z4]),(0,[z1,z714,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1149]),(0,[z565,z1,z2,z439,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z1150,z6]),(0,[z1,z2,z3,z5,z6,z1151]),(0,[z1,z2,z3,z4,z1152,z6])],[(0,[z568,z100,z3,z4,z5,z6]),(0,[z2,z3,z4,z988,z95,z6]),(0,[z359,z1,z2,z3,z5,z63]),(0,[z1,z19,z208,z3,z4,z6]),(0,[z1,z20,z2,z170,z3,z6]),(0,[z1,z3,z21,z4,z6,z143]),(0,[z1,z20,z2,z3,z283,z6]),(0,[z1,z20,z3,z135,z5,z6]),(0,[z1,z2,z3,z21,z81,z62])],[(0,[z1153,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z1154,z5,z6]),(0,[z1,z2,z3,z4,z1155,z6]),(0,[z27,z2,z3,z535,z4,z6]),(0,[z1,z20,z2,z69,z51,z6]),(0,[z1,z2,z170,z3,z795,z6]),(0,[z1,z2,z170,z5,z665,z6]),(0,[z1,z259,z20,z3,z4,z6]),(0,[z374,z1,z20,z2,z3,z6])],[(0,[z1,z456,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1156]),(0,[z1,z70,z259,z4,z5,z6]),(0,[z1,z2,z3,z4,z86,z905])],[(0,[z192,z1,z70,z20,z2,z6]),(0,[z1,z2,z3,z268,z243,z6]),(0,[z1,z2,z69,z4,z5,z6]),(0,[z1,z20,z208,z3,z279,z6]),(0,[z1,z608,z3,z4,z8,z6]),(0,[z1,z1157,z3,z4,z5,z6]),(0,[z1,z2,z3,z81,z5,z726]),(0,[z1,z2,z85,z5,z6,z215])],[(0,[z204,z20,z129,z3,z4,z6]),(0,[z1,z2,z1158,z3,z5,z6]),(0,[z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z3,z1159,z4,z6]),(0,[z1,z20,z2,z3,z489,z6]),(0,[z368,z1,z2,z3,z4,z50]),(0,[z1,z2,z61,z4,z5,z601]),(0,[z313,z1,z20,z2,z3,z6]),(0,[z1,z1160,z3,z4,z5,z6]),(0,[z1,z109,z3,z81,z5,z62])],[(0,[z74,z2,z22,z4,z5,z6]),(0,[z1,z20,z2,z3,z541,z6]),(0,[z893,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z348])],[(0,[z1027,z1,z2,z3,z4,z6]),(0,[z1,z539,z2,z21,z4,z6]),(0,[z1,z20,z2,z3,z6,z544]),(0,[z1,z2,z3,z46,z66,z6]),(0,[z91,z1,z2,z3,z4,z905])]],
   [[(0,[z1,z2,z3,z4,z1161,z6]),(0,[z174,z2,z626,z3,z5,z6]),(0,[z1,z16,z2,z3,z162,z6])],[(0,[z1,z2,z1162,z4,z5,z6]),(0,[z179,z1,z2,z3,z21,z4]),(0,[z74,z2,z22,z4,z242,z6]),(0,[z1,z20,z246,z3,z4,z6]),(0,[z1,z246,z76,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z1163]),(0,[z1,z24,z20,z3,z279,z6]),(0,[z1,z70,z2,z89,z5,z6]),(0,[z1,z1164,z2,z3,z4,z6]),(0,[z1,z2,z286,z5,z6,z23])],[(0,[z1,z2,z290,z3,z5,z6]),(0,[z1,z2,z3,z1165,z5,z6]),(0,[z1,z2,z1166,z4,z5,z6]),(0,[z1,z2,z1167,z4,z5,z6]),(0,[z47,z2,z3,z4,z110,z48]),(0,[z1,z2,z3,z4,z6,z1168]),(0,[z1169,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z6,z552]),(0,[z1,z2,z3,z4,z475,z6]),(0,[z1,z2,z4,z152,z6,z318])],[(0,[z1,z2,z3,z4,z1170,z6]),(0,[z1,z1171,z3,z4,z5,z6]),(0,[z1,z2,z3,z1172,z5,z6]),(0,[z1,z70,z2,z98,z5,z6]),(1,[z1,z3,z4,z837,z6]),(0,[z1,z2,z4,z5,z717,z23]),(0,[z1,z20,z2,z4,z6,z318]),(0,[z1,z2,z3,z1006,z55,z6])],[(0,[z1,z2,z1173,z4,z5,z6]),(0,[z1,z2,z3,z21,z449,z6]),(0,[z1,z2,z3,z152,z6,z63]),(0,[z1,z2,z527,z4,z152,z6])],[(0,[z1,z2,z3,z1141,z5,z6]),(0,[z1,z87,z20,z2,z3,z6]),(0,[z1,z2,z1174,z4,z5,z6]),(0,[z78,z2,z3,z455,z95,z6]),(0,[z1175,z2,z3,z4,z5,z6]),(0,[z1,z99,z2,z3,z21,z6]),(0,[z1,z2,z3,z369,z6,z50])],[(0,[z1,z505,z3,z4,z5,z6]),(0,[z1,z1176,z3,z4,z5,z6]),(0,[z325,z1,z2,z4,z5,z23]),(0,[z1,z2,z3,z5,z1177,z6]),(0,[z1,z20,z1018,z2,z3,z6]),(0,[z1,z2,z3,z1178,z5,z6]),(0,[z1,z251,z2,z69,z4,z6]),(0,[z1,z197,z2,z3,z51,z6]),(0,[z592,z1,z20,z2,z3,z6]),(0,[z1,z20,z2,z3,z4,z1093])],[(0,[z1,z2,z3,z4,z365,z6]),(0,[z1,z18,z3,z4,z837,z6]),(0,[z1,z2,z4,z5,z49,z717]),(0,[z1,z2,z1179,z4,z5,z6])]],
   [[(0,[z1,z2,z1180,z4,z5,z6]),(0,[z74,z1,z137,z2,z4,z6]),(0,[z1,z2,z115,z4,z5,z6]),(0,[z1,z2,z1181,z3,z4,z6]),(0,[z1,z2,z3,z51,z107,z6])],[(0,[z1,z20,z2,z3,z355,z6]),(0,[z1,z2,z171,z692,z5,z6]),(0,[z192,z2,z841,z4,z5,z6]),(0,[z47,z2,z3,z4,z5,z48]),(0,[z1,z109,z3,z51,z5,z6]),(0,[z1,z2,z3,z1182,z5,z6]),(0,[z1,z2,z3,z4,z5,z903]),(0,[z1,z1183,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1184,z6]),(0,[z1,z3,z21,z4,z749,z6]),(0,[z1,z2,z3,z81,z152,z62])],[(0,[z374,z2,z3,z67,z5,z6]),(0,[z187,z101,z3,z4,z5,z6]),(0,[z1,z2,z303,z21,z4,z6])],[(0,[z2,z841,z22,z4,z5,z6]),(0,[z444,z2,z3,z175,z5,z6]),(0,[z1,z2,z1185,z4,z5,z6]),(0,[z91,z1,z2,z3,z4,z50])],[(0,[z15,z1,z20,z2,z3,z6]),(0,[z1,z217,z120,z2,z4,z6]),(0,[z1,z2,z3,z1186,z5,z6])],[(0,[z1,z2,z3,z21,z4,z6]),(0,[z1,z2,z3,z1187,z4,z6]),(0,[z187,z20,z2,z3,z4,z6]),(0,[z1,z2,z3,z201,z365,z6])],[(0,[z74,z1,z714,z2,z3,z6]),(0,[z1,z309,z16,z2,z5,z6]),(0,[z1,z2,z3,z21,z455,z6]),(0,[z1,z2,z1188,z4,z5,z6]),(0,[z1,z2,z3,z1189,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1190]),(0,[z1,z2,z3,z4,z1191,z6]),(0,[z1,z2,z3,z1192,z5,z6]),(0,[z551,z1,z2,z4,z5,z23]),(0,[z1193,z2,z3,z4,z5,z6]),(0,[z1,z109,z20,z3,z81,z6]),(0,[z1,z2,z3,z5,z6,z726])]],
   [[(0,[z1,z2,z3,z4,z1194,z6]),(0,[z1,z2,z3,z1195,z4,z6]),(0,[z1,z1071,z2,z3,z4,z6]),(0,[z1,z2,z1196,z4,z5,z6]),(0,[z1,z2,z170,z5,z6,z706]),(0,[z1,z2,z4,z5,z617,z23]),(0,[z1,z20,z2,z3,z135,z6]),(0,[z1,z2,z3,z4,z1006,z6]),(0,[z1,z2,z3,z369,z103,z86])],[(0,[z1,z20,z2,z3,z701,z6]),(0,[z1,z2,z3,z1197,z5,z6]),(0,[z1,z20,z3,z4,z6,z436]),(0,[z1,z99,z2,z3,z5,z6]),(0,[z1,z70,z126,z2,z71,z6])],[(0,[z1,z2,z3,z1198,z5,z6]),(0,[z1,z2,z3,z1199,z5,z6]),(0,[z1,z2,z3,z4,z1200,z6]),(0,[z1,z2,z330,z4,z243,z6]),(0,[z1,z2,z3,z1201,z5,z6]),(0,[z1,z2,z3,z5,z1202,z6]),(0,[z1,z2,z21,z69,z4,z6]),(0,[z1,z70,z20,z2,z379,z6]),(0,[z133,z1,z20,z2,z3,z63])],[(0,[z147,z100,z3,z4,z5,z6]),(0,[z1,z1203,z2,z3,z4,z6]),(0,[z1,z2,z1204,z4,z5,z6]),(0,[z1,z20,z420,z3,z4,z6]),(0,[z1,z16,z2,z3,z6,z50]),(0,[z1,z166,z20,z3,z279,z6]),(0,[z65,z2,z303,z4,z5,z6]),(0,[z1,z366,z2,z3,z21,z6]),(0,[z1,z2,z3,z21,z1006,z6])],[(0,[z1,z2,z3,z1205,z5,z6]),(0,[z1,z2,z3,z1062,z4,z6]),(0,[z1,z539,z20,z2,z3,z6]),(0,[z1,z197,z2,z3,z279,z6]),(0,[z1,z2,z4,z5,z6,z1206]),(0,[z1,z2,z3,z4,z6,z54])],[(0,[z1,z20,z2,z483,z3,z6]),(0,[z1,z1207,z3,z4,z5,z6]),(0,[z1,z20,z320,z3,z51,z6]),(0,[z59,z1,z3,z4,z5,z168]),(0,[z1,z1208,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1209,z6]),(0,[z1,z20,z3,z4,z135,z6])],[(0,[z1,z20,z94,z3,z4,z6]),(0,[z1,z1210,z3,z4,z5,z6]),(0,[z1,z2,z527,z4,z5,z6])],[(0,[z1,z1211,z3,z4,z5,z6]),(0,[z1,z1015,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1212]),(0,[z1,z70,z2,z71,z5,z6]),(0,[z1,z20,z2,z3,z81,z209])]],
   [[(0,[z1,z2,z3,z4,z5,z1213]),(0,[z1,z2,z4,z75,z5,z6]),(0,[z1,z20,z2,z635,z3,z6]),(0,[z1,z2,z3,z4,z6,z1214]),(0,[z1,z2,z248,z4,z365,z6]),(0,[z1,z9,z3,z4,z5,z903])],[(0,[z1,z2,z3,z1215,z5,z6]),(0,[z1,z1216,z2,z3,z4,z6]),(0,[z454,z2,z3,z4,z95,z6]),(0,[z1,z1217,z2,z4,z5,z6]),(0,[z1,z2,z3,z5,z1006,z6])],[(0,[z1,z20,z2,z3,z6,z603]),(0,[z1,z20,z3,z51,z10,z6]),(0,[z1,z2,z4,z5,z6,z1218]),(0,[z1,z883,z2,z3,z201,z6]),(0,[z1,z2,z800,z71,z5,z6])],[(0,[z1,z714,z2,z3,z155,z6]),(0,[z1219,z1,z3,z4,z5,z6]),(0,[z1,z456,z3,z268,z5,z6]),(0,[z1,z2,z3,z1220,z5,z6]),(0,[z59,z1,z3,z201,z5,z168]),(0,[z1,z2,z3,z81,z5,z62])],[(0,[z1,z2,z3,z4,z1221,z6]),(0,[z1,z2,z1222,z4,z5,z6]),(0,[z1,z99,z2,z3,z95,z6]),(0,[z696,z2,z3,z4,z96,z6]),(0,[z1,z2,z3,z196,z5,z6]),(0,[z1,z20,z2,z3,z6,z207]),(0,[z133,z1,z2,z3,z21,z63]),(0,[z1,z2,z3,z46,z1006,z6])],[(0,[z1,z87,z2,z61,z5,z6]),(0,[z1,z2,z76,z268,z5,z6]),(0,[z1,z2,z3,z719,z4,z6]),(0,[z1,z20,z2,z467,z3,z6]),(0,[z1,z20,z2,z3,z201,z6]),(0,[z1,z2,z3,z4,z1223,z6])],[(0,[z1,z2,z3,z4,z5,z1224]),(0,[z1,z20,z9,z3,z4,z10]),(0,[z1003,z1,z20,z2,z4,z6])],[(0,[z1,z60,z303,z4,z5,z6]),(0,[z1,z9,z3,z4,z5,z10]),(0,[z1,z2,z3,z21,z236,z6])]],
   [[(0,[z1,z2,z3,z5,z6,z1225]),(0,[z1,z2,z3,z4,z1226,z6]),(0,[z1,z28,z2,z4,z191,z6]),(0,[z1,z1227,z2,z3,z4,z6]),(0,[z1,z20,z2,z4,z6,z1032])],[(0,[z1,z2,z3,z4,z1228,z6]),(0,[z1,z2,z3,z4,z1229,z6]),(0,[z1,z2,z3,z4,z1230,z6]),(0,[z1,z2,z3,z1231,z5,z6]),(0,[z65,z2,z3,z4,z365,z6]),(0,[z1,z1232,z3,z4,z5,z6]),(1,[z1,z2,z4,z963,z6]),(0,[z1,z645,z99,z2,z3,z6]),(0,[z1,z3,z4,z5,z6,z1233])],[(0,[z179,z187,z2,z3,z4,z5]),(0,[z363,z1,z20,z2,z3,z6]),(0,[z2,z3,z841,z4,z5,z6]),(0,[z1,z2,z3,z1234,z4,z6]),(0,[z1,z1235,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1236]),(0,[z1,z1237,z3,z4,z5,z6]),(0,[z1,z2,z1238,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1239]),(0,[z1,z246,z3,z4,z243,z6]),(0,[z1,z2,z3,z81,z258,z6]),(0,[z1,z2,z3,z4,z1240,z6])],[(0,[z817,z129,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z903,z168]),(0,[z1,z20,z2,z3,z4,z1005]),(0,[z407,z1,z2,z3,z4,z523]),(0,[z1,z2,z3,z283,z4,z211])],[(0,[z100,z817,z3,z4,z5,z6]),(0,[z1,z41,z3,z46,z5,z6]),(0,[z1,z1002,z3,z4,z5,z6]),(0,[z174,z1,z2,z3,z258,z6]),(0,[z1,z70,z20,z2,z61,z6]),(0,[z1,z2,z61,z4,z5,z717])],[(0,[z189,z2,z22,z4,z5,z6]),(0,[z174,z2,z3,z175,z5,z6]),(0,[z1,z20,z2,z3,z82,z6]),(0,[z59,z1,z248,z4,z5,z168]),(0,[z1,z2,z3,z286,z6,z54])],[(0,[z192,z2,z4,z610,z5,z6]),(0,[z1,z2,z3,z4,z1241,z6]),(0,[z1,z320,z251,z3,z51,z6]),(0,[z65,z2,z3,z21,z4,z6]),(0,[z1,z1242,z3,z4,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 512) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 512).take 515) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1027).take 249) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1276)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [512, 515, 249] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 91).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 179).take 77).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [91, 88, 77] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_38767

theorem PEqualNP.Outside.L_meta_38767 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4236822664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4236822664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38767.solve