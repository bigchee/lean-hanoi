import Mathlib.Tactic
import LeanHanoi.HanoiModel
import LeanHanoi.Util.List
import LeanHanoi.DiskAddition

open Data Rule HanoiProperty
open UtilList
open UtilRelation
open DiskAddition
open List

def make_state0 : State 0 := by
  let disk_valid : ([] ++ [] ++ []).Perm (range 0) := by simp
  exact State.mk [] [] [] disk_valid ⟨by simp,by simp, by simp⟩

def opt_play {n : ℕ} (i j : Pos) (h1 : i ≠ j) : SList n := by
  match n with
    | 0  => exact SList.mk [make_state0]
    | n'+ 1 =>
      let ⟨k, ⟨i_neq_k, j_neq_k⟩⟩ := rest_tower i j h1
      let prev : SList n' := opt_play i k i_neq_k
      let after : SList n'  := opt_play k j (Ne.symm j_neq_k)
      let adab_prev := adab2SList i 1 prev -- `[range n ,[],[]] -> [[n-1],range (n-1),[]]`
      let adab_after  := adab2SList j 1 after -- `[[],range (n-1),[n-1]] -> [[],[],range n]`
      exact SList.mk <| adab_prev.t ++ adab_after.t


theorem opt_play_is_minimum_ans {n : ℕ} (i j : Pos) (h1 : i ≠ j) :
    (List.length (opt_play i j h1 : SList n).t = 2^n) ∧ (is_solution i j (opt_play i j h1 : SList n)) := by
  induction n generalizing i j
  case zero =>
    dsimp [opt_play,is_solution]
    simp
    have : (i : Pos) →  (is_gathered_ith make_state0 i) := by
      intro i
      dsimp [is_gathered_ith, proj_ith_tower, make_state0]
      cases i ; repeat rfl
    constructor
    · constructor
      · exact this i
      · exact this j
    · dsimp [valid_transition]
      intros m hm
      have : m ≥ 0 := Nat.zero_le m
      have := Nat.not_lt_of_ge this
      apply absurd hm this
  case succ n' ih =>
    dsimp [is_solution,opt_play]
    let ⟨k, ⟨i_neq_k, j_neq_k⟩⟩ := rest_tower i j h1; simp
    set prev : SList n' := opt_play i k i_neq_k
    set after : SList n' := opt_play k j (Ne.symm j_neq_k)
    let adab_prev := adab2SList i 1 prev
    let adab_after := adab2SList j 1 after
    let ⟨h_prev_min, h_prev_sol⟩ := ih i k i_neq_k
    let ⟨h_after_min, h_after_sol⟩ := ih k j (Ne.symm j_neq_k)
    have : adab_prev = adab2SList i 1 prev := rfl ; simp [← this]
    have : adab_after = adab2SList j 1 after := rfl ; simp [← this]
    have : prev = opt_play i k i_neq_k:= rfl ; simp [← this] at *
    have : after = opt_play k j (Ne.symm j_neq_k) := rfl ; simp [← this] at *
    let lenadab_prev_eq_lenPrev : adab_prev.t.length = prev.t.length :=  adab2SList_preserve_length i 1 prev
    let lenadab_after_eq_lenAfter : adab_after.t.length = after.t.length := adab2SList_preserve_length j 1 after
    constructor
    · -- 状態列の長さが2^n
      rw [Eq.trans lenadab_prev_eq_lenPrev h_prev_min, Eq.trans lenadab_after_eq_lenAfter h_after_min]
      simp [Nat.pow_succ, ← Nat.two_mul, Nat.mul_comm]
    · dsimp [is_solution] at h_prev_sol h_after_sol
      simp at h_prev_sol h_after_sol
      let ⟨⟨prev_ne_nil,prev_gathered1,prev_gathered2⟩ ,prev_is_sol⟩ := h_prev_sol
      let adab_prev_ne_nil : adab_prev.t ≠ [] := adab2SList_preserve_ne_nil i 1 prev prev_ne_nil
      let ⟨⟨after_ne_nil,after_gathered1,after_gathered2⟩ ,after_is_sol⟩ := h_after_sol
      let adab_after_ne_nil : adab_after.t ≠ [] := adab2SList_preserve_ne_nil j 1 after after_ne_nil
      let a_not_nil : (adab_prev.t ++ adab_after.t) ≠ [] := List.append_ne_nil_of_left_ne_nil adab_prev_ne_nil adab_after.t
      constructor
      · use (λ _ => adab_after_ne_nil)
        let prev_append_gathered_lemma
      : ((proj_ith_tower (prev.t.head prev_ne_nil) i)) ++ [n']
        = proj_ith_tower (adab_prev.t.head adab_prev_ne_nil) i := by
          dsimp [adab_prev, adab2SList]
          rw [head_map (add_disk_at_bottom i 1) adab_prev_ne_nil prev_ne_nil]
          have : ((proj_ith_tower (add_disk_at_bottom i 1 (prev.t.head prev_ne_nil)) i)
                    = ((proj_ith_tower (prev.t.head prev_ne_nil) i) ++ (range' n' 1)))
            := proj_append_ith_tower i (prev.t.head prev_ne_nil)
          dsimp [range'] at this
          exact Eq.symm this
        let after_append_gathered_lemma
          : ((proj_ith_tower (after.t.getLast after_ne_nil) j)) ++ [n']
            = proj_ith_tower (adab_after.t.getLast adab_after_ne_nil) j := by
              dsimp [adab_after, adab2SList]
              rw [tail_map (add_disk_at_bottom j 1) adab_after_ne_nil after_ne_nil]
              have : ((proj_ith_tower (add_disk_at_bottom j 1 (after.t.getLast after_ne_nil)) j)
                        = ((proj_ith_tower (after.t.getLast after_ne_nil) j) ++ (range' n' 1)))
                := proj_append_ith_tower j (after.t.getLast after_ne_nil)
              dsimp [range'] at this
              exact Eq.symm this
        let headA_eq_headadab_prev : (adab_prev.t ++ adab_after.t).head a_not_nil = adab_prev.t.head adab_prev_ne_nil
          := List.head_append_of_ne_nil adab_prev_ne_nil
        let tailA_eq_tailadab_after : (adab_prev.t ++ adab_after.t).getLast a_not_nil = adab_after.t.getLast adab_after_ne_nil
          := List.getLast_append_right adab_after_ne_nil
        rw [headA_eq_headadab_prev, tailA_eq_tailadab_after]
        constructor
        · dsimp [is_gathered_ith]
          rw [← prev_append_gathered_lemma, prev_gathered1, add_range_1]
        · dsimp [is_gathered_ith]
          rw [← after_append_gathered_lemma, after_gathered2, add_range_1]
      · dsimp [valid_transition]
        split_ifs
        case pos => contradiction
        case neg =>
          intros m hm
          dsimp [valid_transition] at prev_is_sol after_is_sol
          simp [prev_ne_nil, after_ne_nil] at prev_is_sol after_is_sol
          by_cases hm_adab_prevpred : m < adab_prev.t.length.pred
          case pos =>
            let hm_adab_prev := Nat.lt_of_lt_pred hm_adab_prevpred
            have : m < prev.t.length - 1 := by
              rw [← lenadab_prev_eq_lenPrev]
              exact hm_adab_prevpred
            have := prev_is_sol m this
            dsimp [valid_move] at *
            let ⟨move,hm1,hm2,hm3⟩ := this
            use move
            have : proj_ith_tower (adab_prev.t ++ adab_after.t)[m] move.s = proj_ith_tower (adab_prev.t.get ⟨m,hm_adab_prev⟩) move.s := by
              have : (adab_prev.t ++ adab_after.t).get ⟨m,lt_append_left adab_prev.t adab_after.t m hm_adab_prev⟩ = (adab_prev.t ++ adab_after.t)[m] := List.get_eq_getElem
              rw [← this]
              have := get_append_left adab_prev.t adab_after.t m hm_adab_prev
              rw [this]
            rw [this]
            let hmsucc : m + 1 < adab_prev.t.length := lt_remove_predsucc_ne_zero hm_adab_prevpred
            have : proj_ith_tower (adab_prev.t ++ adab_after.t)[m+1] move.t = proj_ith_tower (adab_prev.t.get ⟨m+1,hmsucc⟩) move.t := by
              have : (adab_prev.t ++ adab_after.t).get ⟨m+1,lt_append_left adab_prev.t adab_after.t (m+1) hmsucc⟩ = (adab_prev.t ++ adab_after.t)[m+1] := List.get_eq_getElem
              rw [← this]
              have := get_append_left adab_prev.t adab_after.t (m+1) hmsucc
              rw [this]
            rw [this]
            -- proj_ith_tower prev.t[m] move.s ≠ [] → proj_ith_tower adab_prev.t[m] move.s ≠ 0 が必要moveとmを汎化したい
            let ne_nil_proj_prev2adab_prev (m : ℕ) (h : m < prev.t.length) (pos : Pos) (h2 : proj_ith_tower (prev.t.get ⟨m,h⟩) pos ≠ [])
              : proj_ith_tower (adab_prev.t.get ⟨m,by rw [← lenadab_prev_eq_lenPrev] at h ; exact h⟩) pos ≠ [] := by
                dsimp [adab_prev]
                by_cases hpos : pos = i
                · rw [hpos]
                  rw [hpos] at h2
                  dsimp [adab2SList]
                  have := get_map (add_disk_at_bottom i 1) m h
                  dsimp [List.get] at this h2
                  rw [this]
                  rw [proj_append_ith_tower i prev.t[m]]
                  exact List.append_ne_nil_of_left_ne_nil h2 (range' n' 1)
                · dsimp [adab2SList]
                  have := get_map (add_disk_at_bottom i 1) m h
                  dsimp [List.get] at this h2
                  rw [this]
                  rw [proj_notappend_ith_tower i pos prev.t[m]]
                  exact h2
                  exact fun heq => hpos (Eq.symm heq)
            let hm_ne_nil := ne_nil_proj_prev2adab_prev m (by rw [lenadab_prev_eq_lenPrev] at hm_adab_prev; exact hm_adab_prev) move.s hm1
            use hm_ne_nil
            let hmsucc_prev := by rw [lenadab_prev_eq_lenPrev] at hmsucc; exact hmsucc
            let hmsucc_ne_nil : prev.t[m + 1] = prev.t.get ⟨m+1,hmsucc_prev⟩ := by dsimp [List.get]
            let he1 := ne_nil_proj_prev2adab_prev (m+1) hmsucc_prev move.t (by rw [hmsucc_ne_nil] at hm2 ; exact hm2)
            use he1
            dsimp [adab_prev, adab2SList]
            let he2 := get_map (add_disk_at_bottom i 1) m (by rw [lenadab_prev_eq_lenPrev] at hm_adab_prev; exact hm_adab_prev)
            dsimp at he2
            simp
            let proj_head?_eq : (proj_ith_tower (add_disk_at_bottom i 1 prev.t[m]) move.s).head? = (proj_ith_tower (add_disk_at_bottom i 1 prev.t[m+1]) move.t).head?
              := adab_preseve_projEq prev.t[m] prev.t[m+1] move.s move.t i hm1 hm2 hm3

            have := head_eq_of_head?_eq (proj_ith_tower (add_disk_at_bottom i 1 prev.t[m]) move.s) (proj_ith_tower (add_disk_at_bottom i 1 prev.t[m + 1]) move.t)
            let add_disk_ne_nil : proj_ith_tower (add_disk_at_bottom i 1 prev.t[m]) move.s ≠ [] := by
              apply adab_preserve_proj_ne_nil i move.s prev.t[m]
              exact hm1
            let add_disk_ne_nil2 : proj_ith_tower (add_disk_at_bottom i 1 prev.t[m + 1]) move.t ≠ [] := adab_preserve_proj_ne_nil i move.t prev.t[m+1] hm2

            apply this add_disk_ne_nil add_disk_ne_nil2
            exact proj_head?_eq
          case neg =>
            let one_le_adab_prevlen : 1 ≤ adab_prev.t.length := by
                apply Nat.add_one_le_of_lt
                exact List.length_pos_of_ne_nil adab_prev_ne_nil
            by_cases hm_adab_prevlen : m = adab_prev.t.length.pred
            case pos =>
              dsimp [valid_move]
              let mid_move : Move := ⟨i,j,h1⟩
              use mid_move
              have : adab_prev.t.length.pred < adab_prev.t.length := by
                have : adab_prev.t.length ≠ 0 := by
                  apply ne_of_gt
                  exact List.length_pos_of_ne_nil adab_prev_ne_nil
                exact pred_lt_of_ne_zero adab_prev.t.length this
              let hm_lt_adab_prevlen : m < adab_prev.t.length := (by rw [hm_adab_prevlen] ; exact this)
              have : proj_ith_tower (adab_prev.t ++ adab_after.t)[m] mid_move.s = proj_ith_tower (adab_prev.t.get ⟨m,hm_lt_adab_prevlen⟩) mid_move.s := by
                have : (adab_prev.t ++ adab_after.t).get ⟨m,lt_append_left adab_prev.t adab_after.t m hm_lt_adab_prevlen⟩ = (adab_prev.t ++ adab_after.t)[m] := List.get_eq_getElem
                rw [← this]
                have := get_append_left adab_prev.t adab_after.t m hm_lt_adab_prevlen
                rw [this]
              rw [this]
              let zero_lt_adab_afterlen : 0 < adab_after.t.length := by
                apply List.length_pos_of_ne_nil
                exact adab_after_ne_nil
              let adab_prevlen_le_msucc : adab_prev.t.length ≤ m+1 := by
                rw [hm_adab_prevlen]
                simp
                rw [predsucc_id adab_prev.t.length one_le_adab_prevlen]
                -- rw [add_comm_sub]
              let pred_eq_minusone : adab_prev.t.length.pred = adab_prev.t.length - 1 := by simp
              have : proj_ith_tower (adab_prev.t ++ adab_after.t)[m+1] mid_move.t = proj_ith_tower (adab_after.t.get ⟨0,zero_lt_adab_afterlen⟩) mid_move.t := by
                have : (adab_prev.t ++ adab_after.t)[m+1]? = adab_after.t[(m+1) - adab_prev.t.length]? := List.getElem?_append_right adab_prevlen_le_msucc
                nth_rewrite 2 [hm_adab_prevlen] at this
                simp at this
                rw [predsucc_id adab_prev.t.length one_le_adab_prevlen] at this
                rw [Nat.sub_self adab_prev.t.length] at this
                let msucc_le_adab_prev2len : m + 1 < (adab_prev.t ++ adab_after.t).length := by
                  simp [hm_adab_prevlen]
                  rw [predsucc_id adab_prev.t.length one_le_adab_prevlen]
                  exact Nat.lt_add_of_pos_right zero_lt_adab_afterlen
                have := get_eq_of_get?_eq msucc_le_adab_prev2len zero_lt_adab_afterlen this
                rw [← this]
                simp
              rw [this]
              have : (proj_ith_tower (adab_prev.t.get ⟨m, hm_lt_adab_prevlen⟩) mid_move.s) = [n'] := by
                dsimp [adab_prev,adab2SList]
                have : m < prev.t.length := by
                  rw [hm_adab_prevlen,lenadab_prev_eq_lenPrev]
                  apply Nat.pred_lt
                  apply ne_of_gt
                  apply List.ne_nil_iff_length_pos.mp
                  exact prev_ne_nil
                have : (map (add_disk_at_bottom i 1) prev.t)[m] = add_disk_at_bottom i 1 (prev.t[m]) := get_map (add_disk_at_bottom i 1) m this
                rw [this]
                dsimp [mid_move]
                have : ((proj_ith_tower (add_disk_at_bottom i 1 prev.t[m]) i) = ((proj_ith_tower prev.t[m] i) ++ (range' n' 1))) := proj_append_ith_tower i prev.t[m]
                rw [this]
                dsimp [range']
                have : prev.t.getLast prev_ne_nil = prev.t[m] := by
                  have := List.getLast_eq_getElem prev_ne_nil
                  rw [pred_eq_minusone,lenadab_prev_eq_lenPrev] at hm_adab_prevlen
                  simp [← hm_adab_prevlen] at this
                  exact this
                rw [← this]
                have := prev_gathered2
                dsimp [is_gathered_ith] at this
                have := is_nil_if_not_dest this (Ne.symm i_neq_k)
                rw [this]
                simp
              rw [this]
              have : (proj_ith_tower (adab_after.t.get ⟨0, zero_lt_adab_afterlen⟩) mid_move.t) = [n'] := by
                dsimp [adab_after,adab2SList]
                have : (map (add_disk_at_bottom j 1) after.t)[0] = add_disk_at_bottom j 1 (after.t[0]) := get_map (add_disk_at_bottom j 1) 0 (List.length_pos_iff.mpr after_ne_nil)
                rw [this]
                dsimp [mid_move]
                have : ((proj_ith_tower (add_disk_at_bottom j 1 after.t[0]) j) = ((proj_ith_tower after.t[0] j) ++ (range' n' 1))) := proj_append_ith_tower j after.t[0]
                rw [this]
                have : after.t.head after_ne_nil = after.t[0] := List.head_eq_getElem after_ne_nil
                rw [← this]
                have := after_gathered1
                dsimp [is_gathered_ith] at this
                have := is_nil_if_not_dest this (Ne.symm j_neq_k)
                rw [this]
                simp
              rw [this]
              have :  ¬([n'] = []) := by simp
              use this
              use this
            case neg =>
              -- おもにList.getElem_append　を使う帰納ケースになる.
              let after_moves := h_after_sol.2
              simp [valid_transition] at after_moves
              let m_ge_adab_prevlen : m ≥ adab_prev.t.length := not_lt_not_eq_implies_ge_nat hm_adab_prevpred hm_adab_prevlen
              have := List.getElem_append (Nat.lt_of_lt_pred hm)
              let not_m_le_adab_prevlen := Nat.not_lt_of_le m_ge_adab_prevlen
              simp [not_m_le_adab_prevlen] at this
              rw [this]
              have : m+1 < (adab_prev.t ++ adab_after.t).length := by
                have := Nat.add_lt_add_right hm 1
                let htmp : (adab_prev.t ++ adab_after.t).length ≥ 1 := by
                  simp [List.length_append]
                  exact Nat.le_add_right_of_le one_le_adab_prevlen
                rw [predsucc_id (adab_prev.t ++ adab_after.t).length htmp] at this
                exact this
              -- (adab_prev.t ++ adab_after.t)[m+1] = adab_after.t[(m+1)-adab_prev.t.length]
              have := List.getElem_append this
              let not_msucc_le_adab_prevlen : ¬ (m+1 < adab_prev.t.length):= by
                apply Nat.not_lt_of_le
                apply (fun x => Nat.le_trans x (Nat.le_succ m))
                exact m_ge_adab_prevlen
              simp [not_msucc_le_adab_prevlen] at this
              rw [this]
              dsimp [adab_after]
              simp [Nat.sub_add_comm m_ge_adab_prevlen]
              let m_minus_adab_prevlen_succ_lt_afterlen : m - adab_prev.t.length + 1 < after.t.length := by
                rw [← lenadab_after_eq_lenAfter]
                rw [← Nat.sub_add_comm m_ge_adab_prevlen]
                rw [List.length_append] at hm
                have := Nat.add_lt_add_right hm 1
                rw [predsucc_id (adab_prev.t.length + adab_after.t.length) (Nat.le_add_right_of_le one_le_adab_prevlen)] at this
                let msucc_gt_adab_prevlen : adab_prev.t.length ≤ m + 1 := by
                  apply Nat.le_trans m_ge_adab_prevlen
                  exact Nat.le_succ m
                have := Nat.sub_lt_left_of_lt_add msucc_gt_adab_prevlen this
                exact this
              have : (m - adab_prev.t.length) + 1 < (adab2SList j 1 after).t.length
                := adab2SList_preserve_lt m_minus_adab_prevlen_succ_lt_afterlen
              have : valid_move ((adab2SList j 1 after).t[(m - adab_prev.t.length)]'(sub_one_lt_of_lt this))
                ((adab2SList j 1 after).t[((m - adab_prev.t.length) + 1)]'this)
                := adab2SList_preserve_move_valid m_minus_adab_prevlen_succ_lt_afterlen
              -- m -> m - adab_prev.t.length, l -> after
                  <| after_moves.2 (m - adab_prev.t.length)
                  <| Nat.lt_sub_of_add_lt m_minus_adab_prevlen_succ_lt_afterlen
              exact this
