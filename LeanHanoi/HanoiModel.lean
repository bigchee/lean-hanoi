import Mathlib.Tactic
import LeanHanoi.Util.List
open List

namespace Data
-- 状態の定義
structure State (n : ℕ) where
  a : List ℕ
  b : List ℕ
  c : List ℕ
  disk_valid : (a ++ b ++ c).Perm (List.range n)
  rod_valid : Sorted (· ≤ ·) a ∧ Sorted (· ≤ ·) b ∧ Sorted (· ≤ ·) c
  -- n : ℕ := a.length + b.length + c.length

structure SList (n : ℕ) where
  t : List (State n)

-- 遷移の定義

inductive Pos where
  | A
  | B
  | C

structure Move where
  s : Pos
  t : Pos
  valid : s ≠ t

def proj_ith_tower {n : ℕ} (q : State n) (i : Pos) : List ℕ  :=
  match (generalizing := true) i with
    | .A => q.a
    | .B => q.b
    | .C => q.c

def rest_tower (fromIdx : Pos) (toIdx : Pos) (_ : fromIdx ≠ toIdx)
  : {aIdx : Pos // fromIdx ≠ aIdx ∧ toIdx ≠ aIdx } :=
  match fromIdx, toIdx with
    | .A, .B | .B, .A => ⟨.C, by simp ⟩
    | .B, .C | .C, .B => ⟨.A, by simp ⟩
    | .A, .C | .C, .A => ⟨.B, by simp ⟩
end Data


namespace Rule
open Data

-- 遷移の正しさ
def valid_move {n : ℕ} (qFrom : State n) (qTo : State n) : Prop :=
  ∃ m : Move, ∃ h1 : proj_ith_tower qFrom m.s ≠ [], ∃ h2 : proj_ith_tower qTo m.t ≠ [],
      ((proj_ith_tower qFrom m.s).head h1 = (proj_ith_tower qTo m.t).head h2)

-- 状態列の正しさ
def valid_transition {n : ℕ} (l : SList n) : Prop := by
  by_cases  h : l.t = []
  case pos => exact False
  case neg =>
    let len := l.t.length
    have (m : ℕ) (h2 : m < len.pred) : Prop := by
      have : len.pred ≤ len := Nat.pred_le len
      have : m  < len := Nat.lt_of_lt_of_le h2 this
      have : Fin len := Fin.mk m this
      let q_mth : State n := l.t.get this
      have : m + 1 < len := by
        have : len.pred.succ = len := by
          apply Nat.succ_pred
          have := List.length_pos_of_ne_nil h
          exact Nat.ne_of_gt this
        rw [← this]
        have : m + 1 < len.pred.succ := Nat.succ_lt_succ h2
        exact this
      have : Fin len := Fin.mk (m+1) this
      let q_msucc_th : State n := l.t.get this
      exact valid_move q_mth q_msucc_th
    exact ∀ m : ℕ, (hm : m < len.pred) → this m hm

def is_gathered_ith {n : ℕ} (q : State n) (i : Pos): Prop :=
  let tower_i := proj_ith_tower q i
  tower_i = range n

def is_solution {n : ℕ} (i j : Pos) (ans : SList n) : Prop := by
  by_cases h : ans.t = []
  case pos => exact False
  case neg =>
    let head := List.head ans.t h
    let last := List.getLast ans.t h
    exact ((is_gathered_ith head i ∧ is_gathered_ith last j) ∧ valid_transition ans)

end Rule

namespace HanoiProperty
open Data
open UtilList

theorem is_nil_if_not_dest {n : ℕ} {q : State n} {k i : Pos}
  (h1 : proj_ith_tower q k = range n) (h2 : k ≠ i) : proj_ith_tower q i = [] := by
  have := q.disk_valid
  rw [← h1] at this
  match k, i with
    | .A, .B | .A, .C =>
      simp [proj_ith_tower] at *
      have := append_right_nil_of_append_eq_self_perm this
      simp at this
      (first | exact this.1 | exact this.2)
    | .B, .A | .B, .C =>
      simp [proj_ith_tower] at *
      -- swap13
      let htmp : (q.a ++ (q.b ++ q.c)).Perm (q.b ++ (q.a ++ q.c)):= append_perm_swap12
      have := Perm.trans (Perm.symm htmp) this
      have := append_right_nil_of_append_eq_self_perm this
      simp at this
      (first | exact this.1 | exact this.2)
    | .C, .A | .C, .B =>
      simp [proj_ith_tower] at *
      let htmp : (q.a ++ (q.b ++ q.c)).Perm (q.c ++ (q.b ++ q.a)) := by
        rw [← List.append_assoc]
        rw [← List.append_assoc]
        exact append_perm_swap13
      have := Perm.trans (Perm.symm htmp) this
      have := append_right_nil_of_append_eq_self_perm this
      simp at this
      (first | exact this.1 | exact this.2)

end HanoiProperty
