import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3010

open PEqualNP.CircuitLowerBounds

def rl (π : Equiv.Perm (Fin 14)) (i : ℕ) : ℕ :=
  if h : i < 14 then ((π ⟨i, h⟩ : Fin 14) : ℕ) else i

theorem rl_lt (π : Equiv.Perm (Fin 14)) (i : ℕ) (h : i < 14) : rl π i < 14 := by
  unfold rl; rw [dif_pos h]; exact (π ⟨i, h⟩).isLt

theorem rl_ge (π : Equiv.Perm (Fin 14)) (i : ℕ) (h : 14 ≤ i) : rl π i = i := by
  unfold rl; rw [dif_neg (by omega)]

theorem rl_of_lt (π : Equiv.Perm (Fin 14)) (i : ℕ) (h : i < 14) :
    rl π i = ((π ⟨i, h⟩ : Fin 14) : ℕ) := by
  unfold rl; rw [dif_pos h]

theorem rl_mul (σ π : Equiv.Perm (Fin 14)) (i : ℕ) : rl σ (rl π i) = rl (σ * π) i := by
  by_cases h : i < 14
  · rw [rl_of_lt π i h, rl_of_lt σ _ (π ⟨i, h⟩).isLt, rl_of_lt (σ * π) i h]
    simp
  · rw [rl_ge π i (by omega), rl_ge σ i (by omega), rl_ge (σ * π) i (by omega)]

theorem rl_inj (π : Equiv.Perm (Fin 14)) (i j : ℕ) (h : rl π i = rl π j) : i = j := by
  by_cases hi : i < 14
  · by_cases hj : j < 14
    · rw [rl_of_lt π i hi, rl_of_lt π j hj] at h
      have := π.injective (Fin.ext h)
      simpa using this
    · have := rl_lt π i hi
      rw [h, rl_ge π j (by omega)] at this; omega
  · by_cases hj : j < 14
    · have := rl_lt π j hj
      rw [← h, rl_ge π i (by omega)] at this; omega
    · rwa [rl_ge π i (by omega), rl_ge π j (by omega)] at h

def relG (π : Equiv.Perm (Fin 14)) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rl π)⟩

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

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

theorem getD_ofFn (f : Fin 14 → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < 14 then f ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < 14
  · simp [h]
  · simp [h]

def Rel (π : Equiv.Perm (Fin 14)) (w v : List Bool) : Prop :=
  14 ≤ w.length ∧ w.length = v.length ∧ ∀ i, v.getD (rl π i) false = w.getD i false

theorem rel_step (π : Equiv.Perm (Fin 14)) (w v : List Bool) (g : Gate) (h : Rel π w v) :
    Rel π (stepW w g) (stepW v (relG π g)) := by
  obtain ⟨h14, hl, hr⟩ := h
  have hval : (relG π g).op.eval ((relG π g).inputs.map fun i => v.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [relG, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hr i
  refine ⟨by simp [stepW]; omega, by simp [stepW, hl], ?_⟩
  intro i
  simp only [stepW, hval, getPush]
  by_cases hi : i < 14
  · have h1 := rl_lt π i hi
    rw [if_neg (by omega), if_neg (by omega)]
    exact hr i
  · rw [rl_ge π i (by omega)]
    have := hr i
    rw [rl_ge π i (by omega)] at this
    by_cases he : i = w.length
    · rw [if_pos he, if_pos (by omega)]
    · rw [if_neg he, if_neg (by omega), this]

theorem rel_fold (π : Equiv.Perm (Fin 14)) (gs : List Gate) :
    ∀ (w v : List Bool), Rel π w v →
      Rel π (gs.foldl stepW w) ((gs.map (relG π)).foldl stepW v) := by
  induction gs with
  | nil => intro w v h; simpa using h
  | cons g gs ih =>
    intro w v h
    simp only [List.map_cons, List.foldl_cons]
    exact ih _ _ (rel_step π w v g h)

theorem rel_init (π : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool) :
    Rel π (List.ofFn fun i => x (π i)) (List.ofFn x) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases hi : i < 14
  · rw [getD_ofFn, getD_ofFn, dif_pos (rl_lt π i hi), dif_pos hi]
    congr 1
    exact Fin.ext (rl_of_lt π i hi)
  · rw [rl_ge π i (by omega), getD_ofFn, getD_ofFn, dif_neg hi, dif_neg hi]

theorem eval_comm (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (u v : Bool) :
    o.eval [u, v] = o.eval [v, u] := by
  rcases ho with ho | ho <;> subst ho <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

def key (a b c d : ℕ) : ℕ := (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

theorem key_swap1 (a b c d : ℕ) : key a b c d = key b a c d := by
  simp [key, min_comm, max_comm]

theorem key_swap2 (a b c d : ℕ) : key a b c d = key a b d c := by
  simp [key, min_comm, max_comm]

theorem key_minmax (f : Fin 14 → ℕ) (u v : Fin 14) (c d : ℕ) :
    key (f (min u v)) (f (max u v)) c d = key (f u) (f v) c d := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, key_swap1]

theorem key_minmax2 (g : ℕ → ℕ) (a b u v : ℕ) :
    key a b (g (min u v)) (g (max u v)) = key a b (g u) (g v) := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, key_swap2]

theorem key_mm (a b u v : ℕ) : key a b (min u v) (max u v) = key a b u v :=
  key_minmax2 (fun z => z) a b u v

theorem eval_minmax (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (f : Fin 14 → Bool)
    (u v : Fin 14) : o.eval [f (min u v), f (max u v)] = o.eval [f u, f v] := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, eval_comm o ho]

theorem eval_minmax2 (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (f : ℕ → Bool)
    (u v : ℕ) : o.eval [f (min u v), f (max u v)] = o.eval [f u, f v] := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, eval_comm o ho]

theorem act_eq (σ : Equiv.Perm (Fin 14)) (c : Fin 15) :
    (if (c : ℕ) < 14 then ((σ (Fin.ofNat 14 (c : ℕ)) : Fin 14) : ℕ) else 14) = rl σ c := by
  by_cases h : (c : ℕ) < 14
  · rw [if_pos h, rl_of_lt σ _ h]
    congr 2
    ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt h]
  · rw [if_neg h, rl_ge σ _ (by omega)]
    have := c.isLt
    omega

theorem act_eqN (σ : Equiv.Perm (Fin 14)) (c : ℕ) (hc : c < 15) :
    (if c < 14 then ((σ (Fin.ofNat 14 c) : Fin 14) : ℕ) else 14) = rl σ c := by
  by_cases h : c < 14
  · rw [if_pos h, rl_of_lt σ _ h]
    congr 2
    ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt h]
  · rw [if_neg h, rl_ge σ _ (by omega)]
    omega

end PEqualNP.Outside.L_meta_3010

theorem PEqualNP.Outside.L_meta_3010 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if ↑x10 < (14 : ℕ) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3010 in
  intro F C hAO hnd h2 h26 hcomp
  classical
  dsimp only
  obtain ⟨gs, out⟩ := C
  obtain ⟨hAnd, hBack, hLen⟩ := hAO
  simp only [Circuit.size] at h2 h26
  rcases gs with _ | ⟨g1, _ | ⟨g2, rest⟩⟩
  · simp at h2
  · simp at h2
  obtain ⟨o1, ins1⟩ := g1
  obtain ⟨o2, ins2⟩ := g2
  have hl1 : ins1.length = 2 := hLen ⟨o1, ins1⟩ (by simp)
  have hl2 : ins2.length = 2 := hLen ⟨o2, ins2⟩ (by simp)
  rcases ins1 with _ | ⟨p, _ | ⟨q, _ | ⟨_, _⟩⟩⟩ <;> try simp at hl1
  rcases ins2 with _ | ⟨r, _ | ⟨s, _ | ⟨_, _⟩⟩⟩ <;> try simp at hl2
  have hp : p < 14 := by
    have := hBack 0 (by simp) p (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt]); simpa using this
  have hq : q < 14 := by
    have := hBack 0 (by simp) q (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt]); simpa using this
  have hr : r < 15 := by
    have := hBack 1 (by simp) r (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt]); simpa using this
  have hs : s < 15 := by
    have := hBack 1 (by simp) s (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt]); simpa using this
  have hpq : p ≠ q := by have := hnd _ (by simp : (⟨o1, [p, q]⟩ : Gate) ∈ _); simpa using this
  have hrs : r ≠ s := by have := hnd _ (by simp : (⟨o2, [r, s]⟩ : Gate) ∈ _); simpa using this
  have ho1 : o1 = GateOp.and ∨ o1 = GateOp.or := hAnd ⟨o1, [p, q]⟩ (by simp)
  have ho2 : o2 = GateOp.and ∨ o2 = GateOp.or := hAnd ⟨o2, [r, s]⟩ (by simp)
  set P : Fin 14 := ⟨p, hp⟩ with hP
  set Q : Fin 14 := ⟨q, hq⟩ with hQ
  let S : Finset (Equiv.Perm (Fin 14)) :=
    Finset.univ.filter (fun σ => ∀ y : Fin 14 → Bool, F (y ∘ σ) = F y)
  let T : Equiv.Perm (Fin 14) → ℕ := fun σ => key (σ P) (σ Q) (rl σ r) (rl σ s)
  obtain ⟨π, hπS, hmin⟩ := S.exists_min_image T ⟨1, by simp [S]⟩
  have hπ : ∀ y : Fin 14 → Bool, F (y ∘ π) = F y := (Finset.mem_filter.mp hπS).2
  have hne : π P ≠ π Q := by
    intro h; apply hpq; have := π.injective h; simpa [P, Q] using congrArg Fin.val this
  have hrne : rl π r ≠ rl π s := fun h => hrs (rl_inj π r s h)
  have hr15 : rl π r < 15 := by
    by_cases h : r < 14
    · have := rl_lt π r h; omega
    · rw [rl_ge π r (by omega)]; omega
  have hs15 : rl π s < 15 := by
    by_cases h : s < 14
    · have := rl_lt π s h; omega
    · rw [rl_ge π s (by omega)]; omega
  refine ⟨min (π P) (π Q), max (π P) (π Q),
    ⟨min (rl π r) (rl π s), by omega⟩, ⟨max (rl π r) (rl π s), by omega⟩, o1, o2,
    ⟨rest.map (relG π), rl π out⟩, ?_, ?_, ho1, ho2, ?_, ?_, ?_, ?_⟩
  · rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  · show min (rl π r) (rl π s) < max (rl π r) (rl π s)
    omega
  · intro σ hσ
    rw [act_eqN σ _ (by omega : min (rl π r) (rl π s) < 15),
      act_eqN σ _ (by omega : max (rl π r) (rl π s) < 15)]
    change key ((min (π P) (π Q) : Fin 14) : ℕ) ((max (π P) (π Q) : Fin 14) : ℕ)
        (min (rl π r) (rl π s)) (max (rl π r) (rl π s)) ≤
      key ((σ (min (π P) (π Q)) : Fin 14) : ℕ) ((σ (max (π P) (π Q)) : Fin 14) : ℕ)
        (rl σ (min (rl π r) (rl π s))) (rl σ (max (rl π r) (rl π s)))
    rw [key_minmax (fun z => (z : ℕ)), key_minmax (fun z => ((σ z : Fin 14) : ℕ)),
      key_mm, key_minmax2 (rl σ)]
    have hm : σ * π ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      intro y
      have e : y ∘ ⇑(σ * π) = (y ∘ ⇑σ) ∘ ⇑π := by
        funext i; simp
      rw [e, hπ, hσ]
    have := hmin (σ * π) hm
    simp only [T] at this
    rw [← rl_mul, ← rl_mul] at this
    simpa using this
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    refine ⟨?_, ?_⟩
    · rcases hAnd g0 (by simp [hg0]) with h | h <;> simp [relG, h]
    · simp [relG, hLen g0 (by simp [hg0])]
  · simp only [Circuit.size, List.length_map]
    simp at h26
    omega
  · intro x
    have hR := (rel_fold π (⟨o1, [p, q]⟩ :: ⟨o2, [r, s]⟩ :: rest) _ _ (rel_init π x)).2.2 out
    have hC := hcomp (fun i => x (π i))
    have hF : F (fun i => x (π i)) = F x := hπ x
    simp only [Circuit.eval, wires_eq] at hC ⊢
    rw [← hF, ← hC, ← hR]
    simp only [List.map_cons, List.foldl_cons]
    congr 2
    have e1 : (List.ofFn x).getD (rl π p) false = x (π P) := by
      rw [getD_ofFn, dif_pos (rl_lt π p hp)]
      congr 1
      ext
      exact rl_of_lt π p hp
    have e2 : (List.ofFn x).getD (rl π q) false = x (π Q) := by
      rw [getD_ofFn, dif_pos (rl_lt π q hq)]
      congr 1
      ext
      exact rl_of_lt π q hq
    have hx1 : stepW (List.ofFn x) (relG π ⟨o1, [p, q]⟩) =
        List.ofFn x ++ [o1.eval [x (min (π P) (π Q)), x (max (π P) (π Q))]] := by
      rw [eval_minmax o1 ho1 x]
      simp only [stepW, relG, List.map_cons, List.map_nil, e1, e2]
    rw [hx1]
    rw [eval_minmax2 o2 ho2 (fun i => (List.ofFn x ++ [o1.eval [x (min (π P) (π Q)), x (max (π P) (π Q))]]).getD i false)]
    simp [stepW, relG]
