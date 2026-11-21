(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Record FWX0 (s : deflate_state) : Prop := {
  fx0_insh : 0 <= ds_ins_h s < 65536;
  fx0_hw : ds_high_water s <= ds_window_size s }.

Section WF.
  Variables ws hs : Z.

  Lemma FWX0_same : forall s s', FWX0 s ->
    ds_ins_h s' = ds_ins_h s -> ds_high_water s' = ds_high_water s -> ds_window_size s' = ds_window_size s -> FWX0 s'.
  Proof.
    intros s s' X E7 E9 E10. destruct X. constructor.
    - rewrite E7. assumption.
    - rewrite E9, E10. assumption.
  Qed.

  Lemma FWX0_same' : forall s s', FWX0 s ->
    0 <= ds_ins_h s' < 65536 -> ds_high_water s' = ds_high_water s -> ds_window_size s' = ds_window_size s -> FWX0 s'.
  Proof.
    intros s s' X E7 E9 E10. destruct X. constructor.
    - exact E7.
    - rewrite E9, E10. assumption.
  Qed.

  Lemma FWX0_slide : forall s more, FWX0 s -> FWX0 (fw_slide s ws more).
  Proof.
    intros s more X.
    unfold fw_slide. cbv zeta. unfold slide_hash in *. dsred. destruct (Z.ltb_spec (ds_strstart s - ws) (ds_insert s));
      destruct X; constructor; dsred; assumption.
  Qed.

  Lemma FWX0_read_buf : forall s off n, FWX0 s -> FWX0 (fst (read_buf s (RB_window off) n)).
  Proof.
    intros s off n X.
    unfold read_buf. cbv beta iota zeta. dsred.
    set (len := if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)).
    destruct (Z.eqb_spec len 0) as [L0|L0]; [exact X|].
    destruct X.
    destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; constructor; dsred; assumption.
  Qed.

  Lemma FWX0_insert : forall n s str,
    ds_insert s = Z.of_nat n -> fw_wf ws hs s -> FWX0 s -> 0 <= str -> ds_insert s = ds_strstart s - str ->
    FWX0 (fill_window_insert (Z.to_nat (ds_insert s)) s str).
  Proof.
    induction n as [|n IH]; intros s str Hn HW X Hstr Hins.
    - rewrite Hn. change (Z.to_nat (Z.of_nat 0)) with 0%nat. cbn [fill_window_insert]. exact X.
    - rewrite (fill_window_insert_step (ds_insert s) s str) by lia.
      replace (ds_insert s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv zeta.
      pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_hsr _ _ _ HW) as Lhs. pose proof (wf_sl _ _ _ HW) as Vsl.
      pose proof (wf_hmask _ _ _ HW) as Vhm. pose proof (wf_ws _ _ _ HW) as Vws. pose proof (wf_wmask _ _ _ HW) as Vwm.
      pose proof (wf_pl _ _ _ HW) as Vpl. pose proof (wf_hl _ _ _ HW) as Vhl. pose proof (wf_hs _ _ _ HW) as Vhs.
      pose proof (wf_look _ _ _ HW) as Vlook.
      set (s3 := set_head (set_prev (set_ins_h s _) _) _).
      assert (Hh : 0 <= update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) <= ds_hash_mask s).
      { apply update_hash_range. rewrite Vhm. lia. }
      set (s4 := set_insert s3 (ds_insert s3 - 1)).
      assert (X4 : FWX0 s4).
      { subst s4 s3. constructor; dsred.
        - rewrite Vhm in Hh. lia.
        - exact (fx0_hw _ X). }
      assert (HW4 : fw_wf ws hs s4).
      { subst s4 s3. destruct HW; constructor; dsred; try assumption; try lia.
        - rewrite arr_len_set. assumption.
        - rewrite arr_len_set. assumption.
        - intros i Hi. rewrite arr_get_set. destruct (_ && _); [apply wf_hb; rewrite Vhm in Hh; lia | apply wf_pb; exact Hi].
        - intros i Hi. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply wf_hb; exact Hi]. }
      destruct (Z.ltb_spec (ds_lookahead s4 + ds_insert s4) MIN_MATCH) as [Sm|Bg]; [exact X4|].
      replace (Z.to_nat (ds_insert s - 1)) with (Z.to_nat (ds_insert s4)) by (subst s4 s3; dsred; reflexivity).
      apply (IH s4 (str + 1)); subst s4 s3; dsred; try assumption; lia.
  Qed.

  Lemma FWX0_fw_insert : forall s, fw_wf ws hs s -> FWX0 s -> FWX0 (fw_insert s).
  Proof.
    intros s HW X. unfold fw_insert.
    destruct (Z.leb_spec MIN_MATCH (ds_lookahead s + ds_insert s)) as [Big|Small]; [| exact X]. cbv zeta.
    pose proof (wf_ins _ _ _ HW) as Vins. pose proof (wf_hmask _ _ _ HW) as Vhm. pose proof (wf_hsr _ _ _ HW) as Lhs.
    set (s2 := set_ins_h (set_ins_h s _) _).
    assert (Hh : 0 <= ds_ins_h s2 < 65536).
    { subst s2. dsred.
      match goal with |- 0 <= update_hash ?t ?a ?b < 65536 =>
        pose proof (update_hash_range t a b ltac:(dsred; rewrite Vhm; lia)) as R end.
      revert R. dsred. rewrite Vhm. intros R. lia. }
    assert (X2 : FWX0 s2) by (apply (FWX0_same' s); [exact X | ..]; subst s2; dsred; try reflexivity; exact Hh).
    assert (HW2 : fw_wf ws hs s2) by (revert Hh; subst s2; dsred; intros Hh; destruct HW; constructor; dsred; try assumption; lia).
    replace (Z.to_nat (ds_insert s)) with (Z.to_nat (ds_insert s2)) by (subst s2; reflexivity).
    remember (Z.to_nat (ds_insert s2)) as n eqn:Hn.
    rewrite Hn. apply (FWX0_insert n s2 (ds_strstart s - ds_insert s)); subst s2; dsred; try assumption; try lia.
    revert Hn. dsred. intros Hn. rewrite Hn, Z2Nat.id by lia. reflexivity.
  Qed.

  Lemma FWX0_high : forall s, fw_wf ws hs s -> FWX0 s -> FWX0 (fill_window_high s).
  Proof.
    intros s HW X. pose proof (wf_sl _ _ _ HW) as Vsl. pose proof (wf_look _ _ _ HW) as Vlook. pose proof (wf_wsz _ _ _ HW) as Vwsz.
    pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_ins _ _ _ HW) as Vins.
    unfold fill_window_high, WIN_INIT, MAX_MATCH.
    destruct (Z.ltb_spec (ds_high_water s) (ds_window_size s)) as [C1|C1]; [| exact X]. cbv zeta.
    destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s)) as [C2|C2];
      [| destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s + 258)) as [C3|C3]; [| exact X]];
      destruct X; constructor; dsred; try assumption.
    - destruct (Z.ltb_spec 258 (ds_window_size s - (ds_strstart s + ds_lookahead s))); lia.
    - destruct (Z.ltb_spec (ds_window_size s - ds_high_water s) (ds_strstart s + ds_lookahead s + 258 - ds_high_water s)); lia.
  Qed.

  Lemma FWX0_body : forall s, fw_wf ws hs s -> FWX0 s -> ds_lookahead s < MIN_LOOKAHEAD ->
    FWX0 (fst (fill_window_body s ws)).
  Proof.
    intros s HW X Hlook. rewrite fill_window_body_eq.
    pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_sl _ _ _ HW) as Vsl. pose proof (wf_look _ _ _ HW) as Vlook.
    pose proof (wf_ws _ _ _ HW) as Vws. pose proof (wf_wsz _ _ _ HW) as Vwsz. pose proof (wf_ins _ _ _ HW) as Vins.
    unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *.
    assert (Hmore : fw_more s = 2 * ws - ds_lookahead s - ds_strstart s).
    { unfold fw_more. rewrite Vwsz. rewrite wrap32_id by lia. lia. }
    destruct (Z.leb_spec (ws + (ds_w_size s - (258 + 3 + 1))) (ds_strstart s)) as [Sl|Ns].
    - destruct (fw_slide_wf ws hs s (fw_more s) HW ltac:(lia) Hmore) as (HW1 & HC1 & HL1 & HS1).
      pose proof (FWX0_slide s (fw_more s) X) as X1.
      set (s1 := fw_slide s ws (fw_more s)) in *.
      assert (Hm1 : wrap32 (fw_more s + ws) = 3 * ws - ds_lookahead s - ds_strstart s) by (rewrite Hmore; rewrite wrap32_id by lia; lia).
      rewrite Hm1.
      destruct (Z.eqb_spec (cs_avail_in (ds_strm s1)) 0) as [A0|A0].
      + cbn [fst]. exact X1.
      + destruct (read_buf_wf ws hs s1 (ds_strstart s1 + ds_lookahead s1) (3 * ws - ds_lookahead s - ds_strstart s) HW1 eq_refl
                    ltac:(lia) ltac:(lia)) as (HW2 & HC2 & HL2 & HS2 & _ & _ & _ & _ & _ & Hn & Hpos & _).
        pose proof (FWX0_read_buf s1 (ds_strstart s1 + ds_lookahead s1) (3 * ws - ds_lookahead s - ds_strstart s) X1) as X2.
        destruct (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) (3 * ws - ds_lookahead s - ds_strstart s)) as [s2 n].
        cbn [fst snd] in *.
        assert (HW3 : fw_wf ws hs (set_lookahead s2 (ds_lookahead s2 + n))) by (destruct HW2; constructor; dsred; try assumption; lia).
        assert (X3 : FWX0 (set_lookahead s2 (ds_lookahead s2 + n))) by (apply (FWX0_same s2); [exact X2 | ..]; dsred; reflexivity).
        exact (FWX0_fw_insert _ HW3 X3).
    - destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [A0|A0].
      + cbn [fst]. exact X.
      + destruct (read_buf_wf ws hs s (ds_strstart s + ds_lookahead s) (fw_more s) HW eq_refl ltac:(lia) ltac:(lia))
          as (HW2 & HC2 & HL2 & HS2 & _ & _ & _ & _ & _ & Hn & Hpos & _).
        pose proof (FWX0_read_buf s (ds_strstart s + ds_lookahead s) (fw_more s) X) as X2.
        destruct (read_buf s (RB_window (ds_strstart s + ds_lookahead s)) (fw_more s)) as [s2 n].
        cbn [fst snd] in *.
        assert (HW3 : fw_wf ws hs (set_lookahead s2 (ds_lookahead s2 + n))) by (destruct HW2; constructor; dsred; try assumption; lia).
        assert (X3 : FWX0 (set_lookahead s2 (ds_lookahead s2 + n))) by (apply (FWX0_same s2); [exact X2 | ..]; dsred; reflexivity).
        exact (FWX0_fw_insert _ HW3 X3).
  Qed.

  Lemma FWX0_loop : forall n s, fw_wf ws hs s -> FWX0 s -> ds_lookahead s < MIN_LOOKAHEAD ->
    FWX0 (fill_window_loop (S n) s ws).
  Proof.
    induction n as [|n IH]; intros s HW X Hl.
    - rewrite fill_window_loop_step. pose proof (FWX0_body s HW X Hl) as B.
      destruct (fill_window_body s ws) as [s1 brk]. destruct brk; [exact B|].
      destruct (_ && _); cbn [fill_window_loop]; exact B.
    - rewrite fill_window_loop_step. pose proof (FWX0_body s HW X Hl) as B. pose proof (fill_window_body_wf ws hs s HW Hl) as C.
      destruct (fill_window_body s ws) as [s1 brk]. cbn [fst] in B. destruct C as (HW1 & _ & _).
      destruct brk; [exact B|].
      destruct (Z.ltb_spec (ds_lookahead s1) MIN_LOOKAHEAD) as [Lo|Hi]; cbn [andb].
      + destruct (negb (cs_avail_in (ds_strm s1) =? 0)); [| exact B].
        exact (IH s1 HW1 B Lo).
      + exact B.
  Qed.

  (* [comment removed for export] *)
  Lemma fill_window_FWX0 : forall s, fw_wf ws hs s -> FWX0 s -> ds_lookahead s < MIN_LOOKAHEAD ->
    FWX0 (fill_window s).
  Proof.
    intros s HW X Hl. pose proof (wf_ws _ _ _ HW) as Vws.
    unfold fill_window. rewrite Vws.
    pose proof (FWX0_loop 262 s HW X Hl) as X1.
    destruct (fill_window_loop_wf ws hs 263 s HW Hl) as (HW1 & _ & _).
    change (fill_window_loop 263 s ws) with (fill_window_loop (S 262) s ws) in HW1 |- *.
    exact (FWX0_high _ HW1 X1).
  Qed.
End WF.
