import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3308

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stepW x).getD C.output false := rfl

theorem getPush (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases hl : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hl, Nat.ne_of_lt hl]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    by_cases he : i = w.length
    · simp [he]
    · have hn : i - w.length ≠ 0 := by omega
      simp [he, List.getElem?_eq_none (by omega : w.length ≤ i), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp; omega : [b].length ≤ i - w.length)]

def AO (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem ao_of_mono (C : Circuit) (h : Monotone2 C) : ∀ g ∈ C.gates, AO g := by
  intro g hg
  obtain ⟨h1, h2⟩ := h g hg
  exact ⟨by simpa using h1, h2⟩

-- monotonicity of evaluation
theorem mono_fold (gs : List Gate) (hg : ∀ g ∈ gs, AO g) :
    ∀ a b : List Bool, a.length = b.length →
      (∀ i, a.getD i false = true → b.getD i false = true) →
      ∀ i, (gs.foldl stepW a).getD i false = true → (gs.foldl stepW b).getD i false = true := by
  induction gs with
  | nil => intro a b _ h; simpa using h
  | cons g gs ih =>
    intro a b hl h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (by simp [hg'])) _ _ (by simp [stepW, hl])
    intro i hi
    simp only [stepW, getPush] at hi ⊢
    rw [← hl]
    split_ifs at hi ⊢ with hk
    · rcases (hg g (by simp)).1 with hop | hop
      · rw [hop] at hi ⊢
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hi ⊢
        rintro _ ⟨j, hj, rfl⟩
        exact h j (hi _ ⟨j, hj, rfl⟩)
      · rw [hop] at hi ⊢
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hi ⊢
        obtain ⟨_, ⟨j, hj, rfl⟩, hv⟩ := hi
        exact ⟨_, ⟨j, hj, rfl⟩, h j hv⟩
    · exact h i hi

theorem circuit_mono (n : ℕ) (C : Circuit) (hC : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) (hx : circuitFun n C x = true) :
    circuitFun n C y = true := by
  unfold circuitFun at hx ⊢
  rw [eval_eq] at hx ⊢
  refine mono_fold C.gates (ao_of_mono C hC) _ _ (by simp) ?_ _ hx
  intro i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
  by_cases h : i < n
  · simp only [h, dite_true, Option.getD_some] at hi ⊢
    exact hxy _ hi
  · simp [h] at hi

-- the union find count
def orc (gs : List Gate) : ℕ := (gs.filter (fun g => g.op.eval [true, false])).length

theorem card_merge (s : Finset ℕ) (i j : ℕ) :
    s.card ≤ (s.image (fun x => if x = j then i else x)).card + 1 := by
  have h1 : (s.erase j).image (fun x => if x = j then i else x) = s.erase j := by
    ext y
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨x, ⟨hxj, hx⟩, rfl⟩
      simp [hxj, hx]
    · rintro ⟨hyj, hy⟩
      exact ⟨y, ⟨hyj, hy⟩, by simp [hyj]⟩
  have h2 : (s.erase j).image (fun x => if x = j then i else x) ⊆
      s.image (fun x => if x = j then i else x) :=
    Finset.image_subset_image (Finset.erase_subset _ _)
  have h3 := Finset.card_le_card h2
  rw [h1] at h3
  have h4 := Finset.pred_card_le_card_erase (s := s) (a := j)
  omega

def InvU {n : ℕ} (V : Finset (Fin n)) (wB : List Bool) (wv : Fin n → List Bool)
    (lab : Fin n → ℕ) : Prop :=
  (∀ v, (wv v).length = wB.length) ∧
  ∀ k, wB.getD k false = false → ∀ v ∈ V, ∀ w ∈ V,
    (wv v).getD k false = true → (wv w).getD k false = true → lab v = lab w

theorem uf_step {n : ℕ} (V : Finset (Fin n)) (g : Gate) (hg : AO g) (wB : List Bool)
    (wv : Fin n → List Bool) (lab : Fin n → ℕ) (h : InvU V wB wv lab) :
    ∃ lab', InvU V (stepW wB g) (fun v => stepW (wv v) g) lab' ∧
      (V.image lab).card ≤ (V.image lab').card + (if g.op.eval [true, false] then 1 else 0) := by
  obtain ⟨hlen, hinv⟩ := h
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only at hop hl
  have hlen' : ∀ v, (stepW (wv v) ⟨op, ins⟩).length = (stepW wB ⟨op, ins⟩).length := by
    intro v; simp [stepW, hlen v]
  -- old indices keep the invariant for any label map that is a function of lab
  have old : ∀ (φ : ℕ → ℕ) k, k ≠ wB.length → (stepW wB ⟨op, ins⟩).getD k false = false →
      ∀ v ∈ V, ∀ w ∈ V, (stepW (wv v) ⟨op, ins⟩).getD k false = true →
        (stepW (wv w) ⟨op, ins⟩).getD k false = true → φ (lab v) = φ (lab w) := by
    intro φ k hk h0 v hv w hw h1 h2
    simp only [stepW, getPush, hlen v, hlen w, if_neg hk] at h0 h1 h2
    rw [hinv k h0 v hv w hw h1 h2]
  rcases hop with rfl | rfl
  · -- AND gate
    refine ⟨lab, ⟨hlen', ?_⟩, by simp [GateOp.eval]⟩
    intro k h0 v hv w hw h1 h2
    by_cases hk : k = wB.length
    · subst hk
      simp only [stepW, getPush, hlen v, hlen w, ↓reduceIte, GateOp.eval] at h0 h1 h2
      rw [List.all_eq_false] at h0
      obtain ⟨_, hc, hcf⟩ := h0
      simp only [List.mem_map] at hc
      obtain ⟨c, hcin, rfl⟩ := hc
      simp only [List.all_eq_true, List.mem_map, id] at h1 h2
      have h1c := h1 _ ⟨c, hcin, rfl⟩
      have h2c := h2 _ ⟨c, hcin, rfl⟩
      exact hinv c (by simpa using hcf) v hv w hw h1c h2c
    · exact old id k hk h0 v hv w hw h1 h2
  · -- OR gate
    have hall : ∀ k, (stepW wB ⟨GateOp.or, ins⟩).getD k false = false → k = wB.length →
        ∀ c ∈ ins, wB.getD c false = false := by
      intro k h0 hk c hc
      subst hk
      simp only [stepW, getPush, ↓reduceIte, GateOp.eval, List.any_eq_false, List.mem_map,
        id] at h0
      have := h0 _ ⟨c, hc, rfl⟩
      simpa using this
    have hnew : ∀ v, (stepW (wv v) ⟨GateOp.or, ins⟩).getD wB.length false = true →
        ∃ c ∈ ins, (wv v).getD c false = true := by
      intro v h1
      simp only [stepW, getPush, hlen v, ↓reduceIte, GateOp.eval, List.any_eq_true,
        List.mem_map, id] at h1
      obtain ⟨_, ⟨c, hc, rfl⟩, hv⟩ := h1
      exact ⟨c, hc, hv⟩
    have hcount : (if GateOp.or.eval [true, false] then 1 else 0) = 1 := by
      simp [GateOp.eval]
    rw [hcount]
    -- does some v in V turn on input a, input b
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · refine ⟨lab, ⟨hlen', ?_⟩, by omega⟩
      intro k h0 v hv w hw h1 h2
      by_cases hk : k = wB.length
      · subst hk; obtain ⟨c, hc, _⟩ := hnew v h1; simp at hc
      · exact old id k hk h0 v hv w hw h1 h2
    · refine ⟨lab, ⟨hlen', ?_⟩, by omega⟩
      intro k h0 v hv w hw h1 h2
      by_cases hk : k = wB.length
      · have hb := hall k h0 hk
        subst hk
        obtain ⟨c1, hc1, h1'⟩ := hnew v h1
        obtain ⟨c2, hc2, h2'⟩ := hnew w h2
        simp at hc1 hc2
        subst hc1; subst hc2
        exact hinv _ (hb _ (by simp)) v hv w hw h1' h2'
      · exact old id k hk h0 v hv w hw h1 h2
    · by_cases hA : ∃ va ∈ V, (wv va).getD a false = true
      · by_cases hB : ∃ vb ∈ V, (wv vb).getD b false = true
        · obtain ⟨va, hva, hva'⟩ := hA
          obtain ⟨vb, hvb, hvb'⟩ := hB
          let φ : ℕ → ℕ := fun x => if x = lab vb then lab va else x
          refine ⟨fun v => φ (lab v), ⟨hlen', ?_⟩, ?_⟩
          · intro k h0 v hv w hw h1 h2
            by_cases hk : k = wB.length
            · have hb := hall k h0 hk
              subst hk
              have key : ∀ u ∈ V, (stepW (wv u) ⟨GateOp.or, [a, b]⟩).getD wB.length false = true →
                  φ (lab u) = lab va := by
                intro u hu hu1
                obtain ⟨c1, hc1, h1'⟩ := hnew u hu1
                simp at hc1
                rcases hc1 with rfl | rfl
                · have := hinv _ (hb _ (by simp)) u hu va hva h1' hva'
                  simp only [φ, this]
                  split_ifs with he
                  · rfl
                  · rfl
                · have := hinv _ (hb _ (by simp)) u hu vb hvb h1' hvb'
                  simp only [φ, this, if_pos rfl]
              show φ (lab v) = φ (lab w)
              rw [key v hv h1, key w hw h2]
            · exact old φ k hk h0 v hv w hw h1 h2
          · have := card_merge (V.image lab) (lab va) (lab vb)
            rw [Finset.image_image] at this
            exact this
        · refine ⟨lab, ⟨hlen', ?_⟩, by omega⟩
          intro k h0 v hv w hw h1 h2
          by_cases hk : k = wB.length
          · have hb := hall k h0 hk
            subst hk
            push_neg at hB
            obtain ⟨c1, hc1, h1'⟩ := hnew v h1
            obtain ⟨c2, hc2, h2'⟩ := hnew w h2
            simp at hc1 hc2
            rcases hc1 with rfl | rfl
            · rcases hc2 with rfl | rfl
              · exact hinv _ (hb _ (by simp)) v hv w hw h1' h2'
              · exact absurd h2' (hB w hw)
            · exact absurd h1' (hB v hv)
          · exact old id k hk h0 v hv w hw h1 h2
      · refine ⟨lab, ⟨hlen', ?_⟩, by omega⟩
        intro k h0 v hv w hw h1 h2
        by_cases hk : k = wB.length
        · have hb := hall k h0 hk
          subst hk
          push_neg at hA
          obtain ⟨c1, hc1, h1'⟩ := hnew v h1
          obtain ⟨c2, hc2, h2'⟩ := hnew w h2
          simp at hc1 hc2
          rcases hc1 with rfl | rfl
          · exact absurd h1' (hA v hv)
          · rcases hc2 with rfl | rfl
            · exact absurd h2' (hA w hw)
            · exact hinv _ (hb _ (by simp)) v hv w hw h1' h2'
        · exact old id k hk h0 v hv w hw h1 h2
    · simp at hl

theorem uf_fold {n : ℕ} (V : Finset (Fin n)) : ∀ (gs : List Gate), (∀ g ∈ gs, AO g) →
    ∀ (wB : List Bool) (wv : Fin n → List Bool) (lab : Fin n → ℕ), InvU V wB wv lab →
      ∃ lab', InvU V (gs.foldl stepW wB) (fun v => gs.foldl stepW (wv v)) lab' ∧
        (V.image lab).card ≤ (V.image lab').card + orc gs := by
  intro gs
  induction gs with
  | nil => intro _ wB wv lab h; exact ⟨lab, h, by simp [orc]⟩
  | cons g gs ih =>
    intro hg wB wv lab h
    obtain ⟨lab1, h1, c1⟩ := uf_step V g (hg g (by simp)) wB wv lab h
    obtain ⟨lab2, h2, c2⟩ := ih (fun g' hg' => hg g' (by simp [hg'])) _ _ lab1 h1
    refine ⟨lab2, h2, ?_⟩
    have e : orc (g :: gs) = orc gs + (if g.op.eval [true, false] then 1 else 0) := by
      unfold orc
      by_cases h : g.op.eval [true, false] = true <;> simp [List.filter_cons, h]
    rw [e]
    generalize (if g.op.eval [true, false] then 1 else 0) = t at c1
    omega

theorem or_count (n : ℕ) (C : Circuit) (hC : Monotone2 C) (B : Fin n → Bool)
    (V : Finset (Fin n)) (hV : ∀ v ∈ V, B v = false) (h0 : circuitFun n C B = false)
    (h1 : ∀ v ∈ V, circuitFun n C (Function.update B v true) = true) :
    V.card ≤ orc C.gates + 1 := by
  have hinit : InvU V (List.ofFn B) (fun v => List.ofFn (Function.update B v true))
      (fun v => v.val) := by
    refine ⟨by simp, ?_⟩
    intro k hk0 v hv w hw hv1 hw1
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hk0 hv1 hw1
    by_cases hk : k < n
    · simp only [hk, dite_true, Option.getD_some] at hk0 hv1 hw1
      have e1 : v = ⟨k, hk⟩ := by
        by_contra hne
        rw [Function.update_of_ne (Ne.symm hne)] at hv1
        rw [hk0] at hv1; exact absurd hv1 (by simp)
      have e2 : w = ⟨k, hk⟩ := by
        by_contra hne
        rw [Function.update_of_ne (Ne.symm hne)] at hw1
        rw [hk0] at hw1; exact absurd hw1 (by simp)
      rw [e1, e2]
    · simp [hk] at hv1
  obtain ⟨lab, ⟨_, hinv⟩, hc⟩ := uf_fold V C.gates (ao_of_mono C hC) _ _ _ hinit
  have hB : (C.gates.foldl stepW (List.ofFn B)).getD C.output false = false := by
    have := h0; unfold circuitFun at this; rw [eval_eq] at this; exact this
  have hall : ∀ v ∈ V, ∀ w ∈ V, lab v = lab w := by
    intro v hv w hw
    apply hinv C.output hB v hv w hw
    · have := h1 v hv; unfold circuitFun at this; rw [eval_eq] at this; exact this
    · have := h1 w hw; unfold circuitFun at this; rw [eval_eq] at this; exact this
  have hone : (V.image lab).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_image] at ha hb
    obtain ⟨v, hv, rfl⟩ := ha
    obtain ⟨w, hw, rfl⟩ := hb
    exact hall v hv w hw
  have hid : (V.image (fun v : Fin n => v.val)).card = V.card :=
    Finset.card_image_of_injective _ Fin.val_injective
  omega


section Plane

variable {N : ℕ} (R : Fin N → Fin N → Prop) [DecidableRel R]

def pts (l : Fin N) : Finset (Fin N) := Finset.univ.filter (fun p => R p l)

def lns (p : Fin N) : Finset (Fin N) := Finset.univ.filter (fun l => R p l)

theorem mem_pts (p l : Fin N) : p ∈ pts R l ↔ R p l := by simp [pts]

theorem mem_lns (p l : Fin N) : l ∈ lns R p ↔ R p l := by simp [lns]

end Plane

theorem lines_ge (q N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (hq : 1 ≤ q)
    (hN : N = q ^ 2 + q + 1) (hcard : ∀ l, Fintype.card { p : Fin N // R p l } = q + 1)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, R p l ∧ R p' l) (p : Fin N) :
    q + 1 ≤ (lns R p).card := by
  have hsub : Finset.univ.erase p ⊆ (lns R p).biUnion (fun l => (pts R l).erase p) := by
    intro p' hp'
    have hne : p' ≠ p := Finset.ne_of_mem_erase hp'
    obtain ⟨l, ⟨h1, h2⟩, _⟩ := huniq p p' (Ne.symm hne)
    simp only [Finset.mem_biUnion, Finset.mem_erase, mem_lns, mem_pts]
    exact ⟨l, h1, hne, h2⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := lns R p) (t := fun l => (pts R l).erase p)
  have h3 : ∀ l ∈ lns R p, ((pts R l).erase p).card = q := by
    intro l hl
    rw [Finset.card_erase_of_mem ((mem_pts R p l).mpr ((mem_lns R p l).mp hl))]
    have := hcard l
    rw [Fintype.card_subtype] at this
    simp only [pts]
    omega
  rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul] at h2
  rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin] at h1
  have h4 : q * (q + 1) ≤ q * (lns R p).card := by
    have : q * (q + 1) = N - 1 := by rw [hN]; ring_nf; omega
    rw [this, mul_comm]; omega
  exact Nat.le_of_mul_le_mul_left h4 (by omega)

theorem config (q N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (hq : 1 ≤ q)
    (hN : N = q ^ 2 + q + 1) (hcard : ∀ l, Fintype.card { p : Fin N // R p l } = q + 1)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, R p l ∧ R p' l) :
    ∃ LB PB : Finset (Fin N), LB.card = q ∧
      (∀ p ∈ PB, ∀ l ∈ LB, ¬ R p l) ∧
      q * q + 1 ≤ (LB.biUnion (pts R)).card ∧
      q * q + 1 ≤ (PB.biUnion (lns R)).card := by
  have hN0 : 0 < N := by omega
  let c : Fin N := ⟨0, hN0⟩
  have hLc := lines_ge q N R hq hN hcard huniq c
  obtain ⟨m, hm⟩ : (lns R c).Nonempty := Finset.card_pos.mp (by omega)
  have hcm : R c m := (mem_lns R c m).mp hm
  obtain ⟨LB, hLBsub, hLBcard⟩ :=
    Finset.exists_subset_card_eq (s := (lns R c).erase m) (n := q)
      (by rw [Finset.card_erase_of_mem hm]; omega)
  have hLB : ∀ l ∈ LB, R c l ∧ l ≠ m := by
    intro l hl
    have := hLBsub hl
    exact ⟨(mem_lns R c l).mp (Finset.mem_of_mem_erase this), Finset.ne_of_mem_erase this⟩
  let PB := (pts R m).erase c
  have hPB : ∀ p ∈ PB, R p m ∧ p ≠ c := by
    intro p hp
    exact ⟨(mem_pts R p m).mp (Finset.mem_of_mem_erase hp), Finset.ne_of_mem_erase hp⟩
  have hPBcard : PB.card = q := by
    rw [Finset.card_erase_of_mem ((mem_pts R c m).mpr hcm)]
    have := hcard m
    rw [Fintype.card_subtype] at this
    simp only [pts]
    omega
  have same : ∀ p p' l l' : Fin N, p ≠ p' → R p l → R p' l → R p l' → R p' l' → l = l' := by
    intro p p' l l' hne h1 h2 h3 h4
    exact (huniq p p' hne).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  have F1 : ∀ p ∈ PB, ∀ l ∈ LB, ¬ R p l := by
    intro p hp l hl hpl
    obtain ⟨hpm, hpc⟩ := hPB p hp
    obtain ⟨hcl, hlm⟩ := hLB l hl
    exact hlm (same p c l m hpc hpl hcl hpm hcm)
  refine ⟨LB, PB, hLBcard, F1, ?_, ?_⟩
  · -- points on the q concurrent lines
    let X := LB.biUnion (fun l => (pts R l).erase c)
    have hXcard : X.card = q * q := by
      rw [Finset.card_biUnion]
      · have h3 : ∀ l ∈ LB, ((pts R l).erase c).card = q := by
          intro l hl
          rw [Finset.card_erase_of_mem ((mem_pts R c l).mpr (hLB l hl).1)]
          have := hcard l
          rw [Fintype.card_subtype] at this
          simp only [pts]
          omega
        rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul, hLBcard]
      · intro l hl l' hl' hne
        rw [Function.onFun, Finset.disjoint_left]
        intro p hp hp'
        have hp1 := Finset.mem_erase.mp hp
        have hp2 := Finset.mem_erase.mp hp'
        exact hne (same p c l l' hp1.1 ((mem_pts R p l).mp hp1.2) (hLB l hl).1
          ((mem_pts R p l').mp hp2.2) (hLB l' hl').1)
    have hcX : c ∉ X := by
      simp only [X, Finset.mem_biUnion, Finset.mem_erase]
      rintro ⟨_, _, h, _⟩; exact h rfl
    have hsub : insert c X ⊆ LB.biUnion (pts R) := by
      intro p hp
      rw [Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · obtain ⟨l, hl⟩ : LB.Nonempty := Finset.card_pos.mp (by omega)
        exact Finset.mem_biUnion.mpr ⟨l, hl, (mem_pts R _ l).mpr (hLB l hl).1⟩
      · obtain ⟨l, hl, hpl⟩ := Finset.mem_biUnion.mp hp
        exact Finset.mem_biUnion.mpr ⟨l, hl, Finset.mem_of_mem_erase hpl⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hcX, hXcard] at this
    omega
  · -- lines through the q points of m other than c
    let Y := PB.biUnion (fun p => (lns R p).erase m)
    have hYcard : q * q ≤ Y.card := by
      rw [Finset.card_biUnion]
      · have h3 : ∀ p ∈ PB, q ≤ ((lns R p).erase m).card := by
          intro p hp
          rw [Finset.card_erase_of_mem ((mem_lns R p m).mpr (hPB p hp).1)]
          have := lines_ge q N R hq hN hcard huniq p
          omega
        have := Finset.sum_le_sum h3
        rw [Finset.sum_const, smul_eq_mul, hPBcard] at this
        exact this
      · intro p hp p' hp' hne
        rw [Function.onFun, Finset.disjoint_left]
        intro l hl hl'
        have hl1 := Finset.mem_erase.mp hl
        have hl2 := Finset.mem_erase.mp hl'
        exact hl1.1 (same p p' l m hne ((mem_lns R p l).mp hl1.2) ((mem_lns R p' l).mp hl2.2)
          (hPB p hp).1 (hPB p' hp').1)
    have hmY : m ∉ Y := by
      simp only [Y, Finset.mem_biUnion, Finset.mem_erase]
      rintro ⟨_, _, h, _⟩; exact h rfl
    have hsub : insert m Y ⊆ PB.biUnion (lns R) := by
      intro l hl
      rw [Finset.mem_insert] at hl
      rcases hl with rfl | hl
      · obtain ⟨p, hp⟩ : PB.Nonempty := Finset.card_pos.mp (by omega)
        exact Finset.mem_biUnion.mpr ⟨p, hp, (mem_lns R p _).mpr (hPB p hp).1⟩
      · obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
        exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_of_mem_erase hlp⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hmY] at this
    omega

end PEqualNP.Outside.L_meta_3308

theorem PEqualNP.Outside.L_meta_3308 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length := by
  intro q N R _ C hq hN hcard huniq hC hacc hsound
  obtain ⟨LB, PB, hLBc, F1, hU, hW⟩ :=
    PEqualNP.Outside.L_meta_3308.config q N R (by omega) hN hcard huniq
  let B : Fin (N + N) → Bool :=
    Fin.addCases (fun p => decide (p ∈ PB)) (fun l => decide (l ∈ LB))
  let V : Finset (Fin (N + N)) :=
    (LB.biUnion (PEqualNP.Outside.L_meta_3308.pts R)).image (Fin.castAdd N) ∪
      (PB.biUnion (PEqualNP.Outside.L_meta_3308.lns R)).image (Fin.natAdd N)
  have hBl : ∀ p, B (Fin.castAdd N p) = decide (p ∈ PB) := fun p => Fin.addCases_left p
  have hBr : ∀ l, B (Fin.natAdd N l) = decide (l ∈ LB) := fun l => Fin.addCases_right l
  have hne : ∀ p l : Fin N, Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro p l h
    have := congrArg Fin.val h
    simp at this
    omega
  have hV : ∀ v ∈ V, B v = false := by
    intro v hv
    simp only [V, Finset.mem_union, Finset.mem_image] at hv
    rcases hv with ⟨u, hu, rfl⟩ | ⟨w, hw, rfl⟩
    · rw [hBl]
      simp only [decide_eq_false_iff_not]
      intro hp
      obtain ⟨l, hl, hul⟩ := Finset.mem_biUnion.mp hu
      exact F1 u hp l hl ((PEqualNP.Outside.L_meta_3308.mem_pts R u l).mp hul)
    · rw [hBr]
      simp only [decide_eq_false_iff_not]
      intro hl
      obtain ⟨p, hp, hwp⟩ := Finset.mem_biUnion.mp hw
      exact F1 p hp w hl ((PEqualNP.Outside.L_meta_3308.mem_lns R p w).mp hwp)
  have h0 : PEqualNP.MetaComplexity.circuitFun (N + N) C B = false := by
    apply hsound
    · rw [Fintype.card_subtype]
      have e : (Finset.univ.filter fun l : Fin N => B (Fin.natAdd N l) = true) = LB := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hBr, decide_eq_true_eq]
      rw [e, hLBc]
    · rintro ⟨p, l, hpl, hp, hl⟩
      rw [hBl] at hp
      rw [hBr] at hl
      simp only [decide_eq_true_eq] at hp hl
      exact F1 p hp l hl hpl
  have h1 : ∀ v ∈ V, PEqualNP.MetaComplexity.circuitFun (N + N) C (Function.update B v true) = true := by
    intro v hv
    simp only [V, Finset.mem_union, Finset.mem_image] at hv
    rcases hv with ⟨u, hu, rfl⟩ | ⟨w, hw, rfl⟩
    · obtain ⟨l, hl, hul⟩ := Finset.mem_biUnion.mp hu
      refine PEqualNP.Outside.L_meta_3308.circuit_mono _ C hC _ _ ?_
        (hacc u l ((PEqualNP.Outside.L_meta_3308.mem_pts R u l).mp hul))
      intro z hz
      simp only [decide_eq_true_eq] at hz
      rcases hz with rfl | rfl
      · simp
      · rw [Function.update_of_ne (Ne.symm (hne u l)), hBr]
        simpa using hl
    · obtain ⟨p, hp, hwp⟩ := Finset.mem_biUnion.mp hw
      refine PEqualNP.Outside.L_meta_3308.circuit_mono _ C hC _ _ ?_
        (hacc p w ((PEqualNP.Outside.L_meta_3308.mem_lns R p w).mp hwp))
      intro z hz
      simp only [decide_eq_true_eq] at hz
      rcases hz with rfl | rfl
      · rw [Function.update_of_ne (hne p w), hBl]
        simpa using hp
      · simp
  have hcnt := PEqualNP.Outside.L_meta_3308.or_count (N + N) C hC B V hV h0 h1
  have hVcard : V.card = (LB.biUnion (PEqualNP.Outside.L_meta_3308.pts R)).card +
      (PB.biUnion (PEqualNP.Outside.L_meta_3308.lns R)).card := by
    rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (Fin.castAdd_injective N N),
      Finset.card_image_of_injective _ (Fin.natAdd_injective N N)]
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [Finset.mem_image] at hz1 hz2
    obtain ⟨p, _, rfl⟩ := hz1
    obtain ⟨l, _, h⟩ := hz2
    exact hne p l h.symm
  have horc : PEqualNP.Outside.L_meta_3308.orc C.gates =
      (List.filter (fun g => g.op.eval [Bool.true, Bool.false]) C.gates).length := rfl
  rw [← horc]
  have hsq : q ^ 2 = q * q := sq q
  omega
