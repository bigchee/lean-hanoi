import Mathlib.Tactic
import LeanHanoi.HanoiModel
import LeanHanoi.Util.List

open Data Rule
open UtilList
open UtilRelation
open List

namespace DiskAddition

section Def

def add_disk_at_bottom {n : ℕ} (i : Pos) (m : ℕ) (q : State n) : State (n + m) := by
  let add_list := List.range' n m
  let h := r_perm_list (range n) (q.a ++ q.b ++ q.c)
                (Perm.symm q.disk_valid) n (range_n_le_n n)
  match i with
    | .A =>
      let new_a := q.a ++ add_list
      have := append_perm_swap13_left q.disk_valid
      have : (q.c ++ q.b ++ new_a).Perm (List.range (n + m))
         := append_range'_perm n m q.c q.b q.a this
      let new_disk_valid : (new_a ++ q.b ++ q.c).Perm (List.range (n + m))
        := append_perm_swap13_left this
      -- 以下はnew_rod_valid
      --  方針 q.a < n かつ n <= range' n m と, range' n m がsortedなことからいける
      let ⟨h_a,h_b,h_c⟩ := q.rod_valid
      let le_qa_n : ∀ y ∈ q.a, y ≤ n := by
        intro y h_y_in_qa
        have : y ∈ ((q.a ++ q.b) ++ q.c)
          := List.mem_append_left q.c <| List.mem_append_left q.b h_y_in_qa
        exact h y this
      have := add_greater_sorted n m q.a h_a le_qa_n
      exact State.mk new_a q.b q.c new_disk_valid ⟨this,h_b,h_c⟩
    | .B =>
      -- swap23で.Aと同じようにやる
      let new_b := q.b ++ add_list
      have := append_perm_swap23_left q.disk_valid
      have : (q.a ++ q.c ++ new_b).Perm (List.range (n + m))
         := append_range'_perm n m q.a q.c q.b this
      let new_disk_valid : (q.a ++ new_b ++ q.c).Perm (List.range (n + m))
        := append_perm_swap23_left this
      let ⟨h_a,h_b,h_c⟩ := q.rod_valid
      let le_qb_n : ∀ y ∈ q.b, y ≤ n := by
        intro y h_y_in_qb
        have : y ∈ ((q.a ++ q.b) ++ q.c)
          := List.mem_append_left q.c <| List.mem_append_right q.a h_y_in_qb
        exact h y this
      have := add_greater_sorted n m q.b h_b le_qb_n
      exact State.mk q.a new_b q.c new_disk_valid ⟨h_a,this,h_c⟩
    | .C =>
        let new_c := q.c ++ add_list
        let new_disk_valid : (q.a ++ q.b ++ new_c).Perm (List.range (n + m))
          := append_range'_perm n m q.a q.b q.c q.disk_valid
        let ⟨h_a,h_b,h_c⟩ := q.rod_valid
        let le_qc_n : ∀ y ∈ q.c, y ≤ n := by
          intro y h_y_in_qc
          have : y ∈ ((q.a ++ q.b) ++ q.c) := List.mem_append_right (q.a ++ q.b) h_y_in_qc
          exact h y this
        have := add_greater_sorted n m q.c h_c le_qc_n
        exact State.mk q.a q.b new_c new_disk_valid ⟨h_a,h_b,this⟩

def adab2SList {n : ℕ} (i : Pos) (m : ℕ) (q : SList n) : SList (n+m) := by
  have := List.map (add_disk_at_bottom i m) q.t
  exact SList.mk this

end Def


section ProjProperty
theorem proj_append_ith_tower {n m : ℕ} (i : Pos) (q : State n)
   : (proj_ith_tower (add_disk_at_bottom i m q) i) = proj_ith_tower q i ++ range' n m := by
  cases i
  repeat
    dsimp [proj_ith_tower]
    dsimp [add_disk_at_bottom]
    let ⟨h_a,h_b,h_c⟩ := q.rod_valid
    simp

theorem proj_notappend_ith_tower {n m : ℕ} (j i : Pos) (q : State n) (h : j ≠ i)
   : (proj_ith_tower (add_disk_at_bottom j m q) i) = proj_ith_tower q i := by
  cases i
  repeat
    cases j
    repeat
      (first
      | contradiction
      | dsimp [proj_ith_tower] ; dsimp [add_disk_at_bottom]
        let ⟨h_a,h_b,h_c⟩ := q.rod_valid ; simp
      | dsimp [proj_ith_tower]) -- Cの場合

end ProjProperty

section PreserveProperty

theorem adab2SList_preserve_length {n : ℕ} (i : Pos) (m : ℕ) (q : SList n)
  : (adab2SList i m q).t.length = q.t.length := by
  dsimp [adab2SList]
  have : (map (add_disk_at_bottom i m) q.t).length = q.t.length
    := List.length_map (add_disk_at_bottom i m)
  exact this

theorem adab2SList_preserve_ne_nil {n : ℕ} (i : Pos) (m : ℕ) (q : SList n) (h : q.t ≠ [])
  : (adab2SList i m q).t ≠ [] := by
  apply List.ne_nil_iff_length_pos.mpr
  let h := List.ne_nil_iff_length_pos.mp h
  rw [adab2SList_preserve_length i m q]
  exact h

theorem adab_preseve_projEq {n m : ℕ} (q1 q2 : State n) (pos1 pos2 i : Pos)
  (h1 : proj_ith_tower q1 pos1 ≠ []) (h2 : proj_ith_tower q2 pos2 ≠ [])
  (h3 : (proj_ith_tower q1 pos1).head h1 = (proj_ith_tower q2 pos2).head h2)
  -- (h4 : (proj_ith_tower (add_disk_at_bottom i m q1) pos1) ≠ [])
  -- (h5 : (proj_ith_tower (add_disk_at_bottom i m q2) pos2) ≠ [])
  : (proj_ith_tower (add_disk_at_bottom i m q1) pos1).head?
    = (proj_ith_tower (add_disk_at_bottom i m q2) pos2).head? := by
    cases i
    repeat'
      cases pos1
      repeat'
        cases pos2
        all_goals
          dsimp [proj_ith_tower] at h1 h2 h3 ⊢
          dsimp [add_disk_at_bottom]
          let ⟨h_a1,⟨h_b1,h_c1⟩⟩ := q1.rod_valid
          let ⟨h_a2,⟨h_b2,h_c2⟩⟩ := q2.rod_valid
          simp
          have := List.head?_eq_head h1
          simp [this]
          have := List.head?_eq_head h2
          simp [this]
          exact h3

theorem adab2SList_preserve_lt {m n k : ℕ} {l : SList n} {j : Pos} (h : m < l.t.length)
  : m < (adab2SList j k l).t.length := by
  rw [adab2SList_preserve_length j k l]
  exact h

theorem adab_preserve_proj_ne_nil {n m : ℕ} (pos1 pos2 : Pos) (q : State n)
  (h1 : proj_ith_tower q pos2 ≠ [])
  : proj_ith_tower (add_disk_at_bottom pos1 m q) pos2 ≠ [] := by
  by_cases hpos : pos1 = pos2
  case pos =>
    rw [← hpos] at h1 ⊢
    have : proj_ith_tower (add_disk_at_bottom pos1 m q) pos1 = proj_ith_tower q pos1 ++ range' n m
      := proj_append_ith_tower pos1 q
    rw [this]
    exact append_ne_nil_of_left_ne_nil h1 (range' n m)
  case neg =>
    -- dsimp [proj_ith_tower]
    have : proj_ith_tower (add_disk_at_bottom pos1 m q) pos2 = proj_ith_tower q pos2
      := proj_notappend_ith_tower pos1 pos2 q hpos
    rw [this]
    exact h1
    -- dsimp [add_disk_at_bottom]

lemma adab2SList_preserve_proj_ne_nil {m n k : ℕ} {l : SList n} {i j : Pos} (h1 : m < l.t.length)
  (h2 : ¬((proj_ith_tower (l.t.get ⟨m,h1⟩) i) = []))
  : ¬((proj_ith_tower ((adab2SList j k l).t.get ⟨m,adab2SList_preserve_lt h1⟩) i) = []) := by
  dsimp [adab2SList]
  have : (map (add_disk_at_bottom j k) l.t)[m]'(adab2SList_preserve_lt h1)
    = add_disk_at_bottom j k (l.t.get ⟨m, h1⟩) := get_map (add_disk_at_bottom j k) m h1
  -- have := get_map (add_disk_at_bottom j n) m h1
  rw [this]
  exact adab_preserve_proj_ne_nil j i (l.t.get ⟨m, h1⟩) h2

theorem adab2SList_preserve_move_valid {m n k : ℕ} {l : SList n} {j : Pos} (h1 : m+1 < l.t.length)
  (h2 : valid_move (l.t.get ⟨m,sub_one_lt_of_lt h1⟩)  (l.t.get ⟨m+1,h1⟩) )
  : valid_move ((adab2SList j k l).t.get ⟨m,sub_one_lt_of_lt (adab2SList_preserve_lt h1)⟩)
    ((adab2SList j k l).t.get ⟨m+1,adab2SList_preserve_lt h1⟩) := by
  dsimp [valid_move] at *
  let ⟨move,hm1,hm2,hm3⟩ := h2
  use move
  let h1' := sub_one_lt_of_lt h1
  use adab2SList_preserve_proj_ne_nil h1' hm1
  use adab2SList_preserve_proj_ne_nil h1 hm2
  dsimp [adab2SList]
  simp
  have := head_eq_of_head?_eq (proj_ith_tower (add_disk_at_bottom j k l.t[m]) move.s)
     (proj_ith_tower (add_disk_at_bottom j k l.t[m + 1]) move.t)
  let add_disk_ne_nil : proj_ith_tower (add_disk_at_bottom j k l.t[m]) move.s ≠ []
    := adab_preserve_proj_ne_nil j move.s l.t[m] hm1
  let add_disk_ne_nil2 : proj_ith_tower (add_disk_at_bottom j k l.t[m + 1]) move.t ≠ []
    := adab_preserve_proj_ne_nil j move.t l.t[m+1] hm2
  apply this add_disk_ne_nil add_disk_ne_nil2
  have : (proj_ith_tower (add_disk_at_bottom j k l.t[m]) move.s).head?
    = (proj_ith_tower (add_disk_at_bottom j k l.t[(m + 1)]) move.t).head?
    := adab_preseve_projEq l.t[m] l.t[m+1] move.s move.t j hm1 hm2 hm3
  exact this
end PreserveProperty


end DiskAddition
