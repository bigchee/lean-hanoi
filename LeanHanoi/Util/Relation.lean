import Mathlib.Tactic
open List

namespace UtilRelation
theorem pairwise_append_transr {α : Type u} {R : α → α → Prop} [IsTrans α R] {l_1 l_2 : List α}
  (h_1 : Pairwise R l_1) (h_2 : Pairwise R l_2)
  (h_3 : ∃ x : α , (∀ y ∈ l_1, R y x) ∧ (∀ z ∈ l_2, R x z)) : Pairwise R (l_1 ++ l_2) := by
  induction l_1
  case nil => simp ; exact h_2
  case cons h tl ih =>
    rw [List.cons_append]
    apply List.pairwise_cons.mpr
    let ⟨h_11, h_12⟩   := List.pairwise_cons.mp h_1
    simp
    simp at h_3
    let ⟨x,⟨p_rhx, p_rax⟩ , p_rxz⟩ := h_3
    constructor
    · intros a' h_4
      apply Or.elim h_4
      · exact h_11 a'
      · intro h_a'_in_l2
        have := p_rxz a' h_a'_in_l2
        exact IsTrans.trans h x a' p_rhx this
    · exact ih h_12 ⟨x,p_rax, p_rxz⟩

theorem lt_remove_predsucc_ne_zero {m n : ℕ} (h : m < n.pred) : m + 1 < n := by
  cases n
  case zero => contradiction
  case succ n' =>
    rw [Nat.pred_succ] at h
    apply Nat.add_lt_add_iff_right.mpr
    exact h

theorem sub_one_lt_of_lt {m n : ℕ} (h : m+1 < n) : m < n := by
  have : (m+1) - 1 < n := Nat.sub_lt_of_lt h
  simp [Nat.add_sub_assoc (Nat.le_refl 1)] at this
  exact this

theorem predsucc_id (s : Nat) (hs : s ≥ 1): (s - 1) + 1 = s := by
  rw [Nat.add_comm,← Nat.add_sub_assoc,Nat.add_comm,Nat.add_sub_assoc]
  · rw [Nat.sub_self 1]
    simp
  · exact Nat.le_refl 1
  · exact hs

theorem not_lt_not_eq_implies_ge_nat {a b : Nat}
  (h1 : ¬ a < b.pred) (h2 : ¬ a = b.pred) : a ≥ b := by
  cases Nat.lt_or_ge a b.pred with
  | inl hlt => contradiction
  | inr hge =>
    cases Nat.lt_or_eq_of_le hge with
    | inl hlt2 =>
      by_cases hbpred : b = 0
      case pos =>
        rw [hbpred] at hlt2 ⊢
        dsimp [Nat.pred] at hlt2
        exact Nat.le_of_lt hlt2
      case neg =>
        let b_ge_one : b ≥ 1 := by
          have := Nat.pos_of_ne_zero hbpred
          exact Nat.add_one_le_of_lt this
        have := Nat.add_one_le_of_lt hlt2
        simp at this
        rw [predsucc_id b b_ge_one] at this
        exact this
    | inr heq => exact False.elim (h2 (Eq.symm heq))


theorem pred_lt_of_ne_zero (n : Nat) (h : n ≠ 0) : n.pred < n := by
  cases n with
  | zero => contradiction
  | succ k => exact Nat.lt_succ_self k

end UtilRelation
