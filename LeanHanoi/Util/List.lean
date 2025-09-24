import Mathlib.Tactic
import LeanHanoi.Util.Relation
open List
open UtilRelation

-- TODO : 外から使うやつをtheorem, 内部用をlemmaにする

namespace UtilList

section Append

lemma lt_append_left {α : Type} (l1 l2 : List α) (m : Nat) (h : m < l1.length)
   : m < (l1 ++ l2).length := by
  rw [List.length_append]
  have : l1.length ≤ l1.length + l2.length := by
    rw [Nat.add_comm]
    exact Nat.le_add_left l1.length l2.length
  apply Nat.lt_of_lt_of_le
  · exact h
  · exact this

-- これはList.getElem_append_left' で良かった
lemma get_append_left {α : Type} (l1 l2 : List α) (m : Nat) (h : m < l1.length) :
    (l1 ++ l2).get ⟨m, lt_append_left l1 l2 m h⟩ = l1.get ⟨m, h⟩ := by
  induction l1 generalizing m with
  | nil =>
    simp at h
  | cons x xs ih =>
    cases m with
    | zero =>
      dsimp [List.get]
    | succ m' =>
      simp [List.get]
      dsimp [List.length_append] at h
      repeat rw [Nat.add_one] at h
      have := Nat.lt_of_succ_lt_succ h
      have := ih m' this
      exact this
end Append

section Range

theorem add_one_range' {n m : ℕ} : range' n m ++ [n + m] = range' n (m + 1) := by
  induction m generalizing n
  case zero => simp
  case succ m' ih =>
    rw [Nat.add_one]
    dsimp [range']
    have : range' (n + 1) m' ++ [(n + 1) + m'] = range' (n+1) (m'+1):= ih
    rw [Nat.add_one m'] at this
    dsimp [range'] at this
    let h : n + 1 + m' = n + (m' + 1) := by
      rw [Nat.add_assoc]
      nth_rewrite 2 [Nat.add_comm]
      exact rfl
    rw [h] at this
    exact congr_arg (fun l => n :: l) this

theorem append_range_loop {n : ℕ} {l_1 l_2 : List ℕ}
  : (range.loop n l_1) ++ l_2 = range.loop n (l_1 ++ l_2) := by
  induction n generalizing l_1
  case zero => dsimp [range.loop]
  case succ n' ih =>
    rw [Nat.add_one]
    dsimp [range.loop]
    have : range.loop n' (n' :: l_1) ++ l_2 = range.loop n' ((n' :: l_1) ++ l_2) := ih
    rw [← List.cons_append]
    exact this

theorem add_range_range_add {n m : ℕ} : range (n + m) = (range n ++ range' n m) := by
    dsimp [range, range']
    induction m
    case zero => simp
    case succ m' ih =>
      rw [Nat.add_one,Nat.add_succ]
      dsimp [range.loop]
      rw [←add_one_range']
      have : range.loop (n + m') [n + m'] = range.loop (n + m') [] ++ [n + m'] := by
        apply Eq.symm
        exact append_range_loop
      rw [this,← List.append_assoc]
      apply congr_arg (fun l => l ++ [n + m'])
      exact ih

lemma add_range_1 {n: ℕ} : range (n + 1) = (range n ++ [n]) := by
  have : range (n + 1) = (range n ++ range' n 1) := add_range_range_add
  rw [this]
  dsimp [range']

lemma range_n_le_n (n : ℕ) : (∀ y ∈ range n, y ≤ n) := by
  dsimp [range]
  intro y h_y_in
  induction n
  case zero =>
    dsimp [range.loop] at h_y_in
    contradiction
  case succ n' ih =>
    rw [Nat.add_succ, range.loop] at h_y_in
    have : (range.loop n' []) ++ [n'] = range.loop n' [n'] := append_range_loop
    rw [← this] at h_y_in
    simp at h_y_in
    apply Or.elim h_y_in
    · intro h ; exact Nat.le_trans (ih h) (Nat.le_succ n')
    · intro h ; rw [h] ; exact Nat.le_succ n'

lemma range'_le_n (n m : ℕ) : ∀ y ∈ List.range' n m, n ≤ y := by
  intro y h_y_in
  simp at h_y_in
  exact h_y_in.left
end Range

section Perm

theorem append_range'_perm
  (n m : ℕ) (a b c : List ℕ) (disk_valid : (a ++ b ++ c).Perm (List.range n))
  : (a ++ b ++ (c ++ range' n m) ).Perm (List.range (n + m)) := by
    rw [add_range_range_add]
    apply List.Perm.symm
    have := List.Perm.symm  <| List.Perm.append_right (range' n m) disk_valid
    apply List.Perm.trans this
    rw [List.append_assoc]

theorem append_perm_swap13 {a b c : List ℕ}: (a ++ b ++ c).Perm (c ++ b ++ a) := by
      rw [List.append_assoc]
      have : (a ++ (b ++ c)).Perm ((b ++ c) ++ a):= List.perm_append_comm
      let h : ((b ++ c) ++ a).Perm ((c ++ b) ++ a) := List.Perm.append_right a List.perm_append_comm
      exact Perm.trans this h

theorem append_perm_swap13_left {a b c l : List ℕ} (h : (a ++ b ++ c).Perm l)
  : (c ++ b ++ a).Perm l := Perm.trans (Perm.symm append_perm_swap13) h

theorem append_perm_swap23 {a b c : List ℕ}: (a ++ b ++ c).Perm (a ++ c ++ b) := by
      simp [List.append_assoc]
      have : (a ++ (b ++ c)).Perm (a ++ (c ++ b)) := List.Perm.append_left a List.perm_append_comm
      exact this

theorem append_perm_swap23_left {a b c l : List ℕ} (h : (a ++ b ++ c).Perm l)
  : (a ++ c ++ b).Perm l := Perm.trans (Perm.symm append_perm_swap23) h

theorem append_perm_swap12 {a b c : List ℕ}: (a ++ (b ++ c)).Perm (b ++ (a ++ c)) := by
  rw [← List.append_assoc]
  rw [← List.append_assoc]
  exact List.Perm.append_right c List.perm_append_comm

lemma r_perm_list {α : Type u}
  {R : α → α → Prop} (l_1 l_2 : List α) (h_perm : l_1.Perm l_2) (x : α) (h_rl1 : ∀y ∈ l_1, R y x)
  : ∀y ∈ l_2, R y x := by
  intros y h_y_in_l2
  have := (List.Perm.mem_iff h_perm).mpr h_y_in_l2
  apply h_rl1
  exact this

end Perm

section Sorted
lemma range'_sorted (n m : ℕ) : Sorted (· ≤ ·) (List.range' n m) := by
  induction m generalizing n
  case zero => simp
  case succ m' ih =>
    dsimp [range']
    apply List.sorted_cons.mpr
    constructor
    · intro b h_b_in
      have := range'_le_n (n+1) m'
      exact Nat.le_trans (Nat.le_succ n) (this b h_b_in)
    · exact ih (n+1)

lemma add_greater_sorted (n m : ℕ) (l : List ℕ) (hl1 : Pairwise (· ≤ ·) l) (hl2 : ∀ y ∈ l, y ≤ n)
  : Pairwise (· ≤ ·) (l ++ (range' n m)) := by
  let le_n_addList : ∀ y ∈ range' n m, n ≤ y := range'_le_n n m
  have : Pairwise (· ≤ ·) (range' n m) := range'_sorted n m
  have : Pairwise (· ≤ ·) (l ++ (range' n m))
    := pairwise_append_transr hl1 this ⟨n,hl2, le_n_addList⟩
  exact this

lemma range_sorted (n : ℕ) : Sorted (· ≤ ·) (List.range n) := by
  induction n
  case zero => simp
  case succ n' ih =>
    dsimp [range, range.loop]
    dsimp [range, range.loop] at ih
    have : (((range.loop n' []) ++ [n']) = (range.loop n' ([] ++ [n']))) := append_range_loop
    simp at this
    rw [← this]
    let h_2 : Sorted (· ≤ ·) [n'] := by simp
    let h_3 : (∀ y ∈ (range.loop n' []), y ≤ n') ∧ (∀ z ∈ [n'], n' ≤ z) := by
      constructor
      · intro y hy ; exact range_n_le_n n' y hy
      · intro z hz ; simp at hz ; rw [hz]
    apply pairwise_append_transr
    · exact ih
    · exact h_2
    · exact ⟨n',h_3⟩
end Sorted

section Derive
theorem append_right_nil_of_append_eq_self {α : Type _} {l1 l2 : List α}
  (h : l1 ++ l2 = l1) : l2 = [] := by
  -- l2 = [] を示す（l1 に関する帰納）
  induction l1 with
  | nil =>
    simp at *
    exact h
  | cons x xs ih =>
    rw [List.cons_append] at h
    rw [List.cons_inj_right x] at h
    exact ih h

theorem append_right_nil_of_append_eq_self_perm {α : Type _} {l1 l2 : List α}
  (h : (l1 ++ l2).Perm l1) : l2 = [] := by
  -- l2 = [] を示す（l1 に関する帰納）
  induction l1 with
  | nil =>
    simp at *
    exact h
  | cons x xs ih =>
    rw [List.cons_append] at h
    have := List.Perm.cons_inv h
    exact ih this
end Derive

section Map

theorem head_map {α β : Type} (f : α → β) {l : List α}
  (fl_ne_nil : l.map f ≠ []) (l_ne_nil : l ≠ []) :
  (l.map f).head fl_ne_nil =
  f (l.head l_ne_nil) := by
  -- l が非空なので cons しかあり得ない
  cases l with
  | nil       => contradiction
  | cons a l' =>
    -- map f (a :: l') = f a :: l'.map f なので両辺とも f a となり定義的に等しい
    rfl
theorem tail_map {α β : Type} (f : α → β) {l : List α}
  (fl_ne_nil : l.map f ≠ []) (l_ne_nil : l ≠ []) :
  (l.map f).getLast fl_ne_nil =
  f (l.getLast l_ne_nil) := by
  -- l が非空なので cons しかあり得ない
  induction l
  case nil => contradiction
  case cons head tl ih =>
    induction tl
    case nil => simp
    case cons ht ttl _ =>
      dsimp [List.getLast]
      let tl_ne_nil : (ht :: ttl) ≠ [] := List.cons_ne_nil ht ttl
      let ftl_ne_nil : (map f (ht :: ttl)) ≠ [] := by
        dsimp [map]
        exact List.cons_ne_nil (f ht) (map f ttl)
      exact ih ftl_ne_nil tl_ne_nil

lemma map_length_eq {α β : Type} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l
  case nil => simp
  case cons h tl ih =>
    dsimp [List.map]
    exact congrArg (fun n => n + 1) ih

theorem get_map {α β : Type} (f : α → β) {l : List α}
(m : ℕ) (h : m < l.length) :
(l.map f).get ⟨m, by rw[← map_length_eq f l] at h; exact h⟩  = f (l.get ⟨m, h⟩) := by
  induction l generalizing m
  case nil => contradiction
  case cons he tl ih =>
    simp
    cases m
    case zero => simp
    case succ m' => simp

end Map

section Get
theorem head_eq_of_head?_eq {α : Type} (l1 l2 : List α)
    (h1 : l1 ≠ []) (h2 : l2 ≠ []) (h : l1.head? = l2.head?) :
    l1.head h1 = l2.head h2 := by
  let hl1 : l1.head? = some (l1.head h1) := List.head?_eq_head h1
  let hl2 : l2.head? = some (l2.head h2) := List.head?_eq_head h2
  rw [hl1, hl2] at h
  injection h


theorem get_eq_of_get?_eq {α : Type} {l1 l2 : List α} {n1 n2 : Nat}
    (h1 : n1 < l1.length) (h2 : n2 < l2.length) (h : l1[n1]? = l2[n2]?) :
    l1.get ⟨n1,h1⟩ = l2.get ⟨n2,h2⟩  := by
    let hl1 : l1[n1]? = some (l1.get ⟨n1,h1⟩) := by simp
    let hl2 : l2[n2]? = some (l2.get ⟨n2,h2⟩) := by simp
    rw [hl1,hl2] at h
    have := by injection h
    exact this
end Get


end UtilList
