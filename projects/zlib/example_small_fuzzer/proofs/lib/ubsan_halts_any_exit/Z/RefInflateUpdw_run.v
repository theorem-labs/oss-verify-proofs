(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.

Module RefInflateInit_run.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition A5_4 : Z := 2779096485.
Definition A5_4s : Z := -1515870811.
Definition A5_8 : Z := 11936128518282651045.
Definition a5_vals : list Z :=
  [A5_8; A5_4; A5_4s; A5_4s; A5_4s; A5_4s; A5_4; A5_8; A5_8; A5_8; A5_4; A5_4; A5_4; A5_4; A5_8; A5_8; A5_4;
   A5_4; A5_4; A5_4; A5_8; A5_8; A5_4; A5_4; A5_4; A5_4; A5_4; A5_4; A5_8; A5_4s; A5_4s; A5_4].


Definition ir2_wrap (wb : Z) : Z := if wb <? 0 then 0 else Z.shiftr wb 4 + 5.
Definition ir2_wb (wb : Z) : Z := if wb <? 0 then - wb else if wb <? 48 then Z.land wb 15 else wb.

(* zlib 1.4: inflateInit2_ zmemzero's the state, so [init] (the allocator's bytes) is no longer read; inflateReset2
   sets reqwrap / reqbits beside wrap / wbits, and inflateReset restores wrap from reqwrap (the same value) *)
Definition s_pre (init : Z -> Z) (b : blk) (wb : Z) : inflate_state :=
  iset_wrap (iset_reqbits (iset_wbits (iset_reqwrap (iset_wrap (iset_mode (iset_window (iset_window_blk
    (is_of_oracle lay_ref (fun _ => 0) b) None) (arr_make 0 0)) HEAD)
               (ir2_wrap wb)) (ir2_wrap wb)) (ir2_wb wb)) (ir2_wb wb)) (ir2_wrap wb).
Definition z_pre (zc : ZCall) : zstrm := zs_set_msg MSG_NULL (zc_strm zc).

Section Model.

  Lemma ir2_bad_cases : forall wb,
    (ir2_bad wb = true)
    \/ (ir2_bad wb = false /\ -15 <= wb < 0 /\ wbits_valid (- wb) = true)
    \/ (ir2_bad wb = false /\ 0 <= wb <= 47 /\ wbits_valid (Z.land wb 15) = true).
  Proof.
    intros wb. destruct (ir2_bad wb) eqn:E; [left; reflexivity | right].
    unfold ir2_bad in E. apply Bool.orb_false_iff in E as [E1 E3]. apply Bool.orb_false_iff in E1 as [E1 E2].
    apply Bool.negb_false_iff in E3. apply Z.ltb_ge in E1. apply Z.ltb_ge in E2.
    destruct (Z.ltb_spec wb 0); [left | right]; (split; [reflexivity | split; [lia | exact E3]]).
  Qed.

  Lemma inflateInit2_m_eq : forall {St} (hooks : zhooks St) zc wb (g : St),
    inflateInit2_m ivar_ref hooks zc wb g =
    sbind (zalloc hooks 1 7176) (fun r =>
     match r with
     | None => sret (None, zret0 (z_pre zc) Z_MEM_ERROR)
     | Some (b, init) =>
         if ir2_bad wb then sbind (zfree hooks b) (fun _ => sret (None, zret0 (z_pre zc) Z_STREAM_ERROR))
         else sret (Some (ireset_s (s_pre init b wb)), zret0 (ireset_z (s_pre init b wb) (z_pre zc)) Z_OK)
     end) g.
  Proof.
    intros St hooks zc wb g.
    unfold inflateInit2_m. cbn [iv_lay ivar_ref]. unfold SIZEOF_inflate_state, z_pre.
    unfold sbind. f_equal. extensionality p. destruct p as [[[b init]|] g1]; cbn [fst snd]; [|reflexivity].
    unfold inflateReset2.
    replace (inflateStateCheck _) with false by reflexivity.
    unfold ir2_bad, s_pre, ir2_wrap, ir2_wb.
    destruct (Z.ltb_spec wb 0) as [Hneg|Hpos].
    - replace (47 <? wb) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (Z.ltb_spec wb (-15)) as [H15|H15]; cbn [orb]; [reflexivity|].
      unfold wbits_valid.
      destruct (Z.eqb_spec (- wb) 0) as [E0|E0]; [exfalso; lia|]. cbn [negb andb orb].
      replace (15 <? - wb) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (- wb <=? 15) with true by (symmetry; apply Z.leb_le; lia).
      destruct (Z.ltb_spec (- wb) 8) as [H8|H8]; destruct (Z.leb_spec 8 (- wb)) as [H8'|H8']; try (exfalso; lia); cbn [andb orb negb]; [reflexivity|].
      replace (is_window_blk _) with (@None blk) by reflexivity. unfold sbind at 1. cbn [sret mbind fst snd].
      rewrite inflateReset_same by reflexivity. replace (inflateStateCheck _) with false by reflexivity.
      rewrite inflateReset_eq by reflexivity. reflexivity.
    - replace (47 <? wb) with (negb (wb <? 48)) by (destruct (Z.ltb_spec 47 wb); destruct (Z.ltb_spec wb 48); try reflexivity; exfalso; lia).
      replace (wb <? -15) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (Z.ltb_spec wb 48) as [H48|H48]; cbn [negb orb].
      + unfold wbits_valid.
        pose proof (Z.land_nonneg wb 15) as HL0.
        assert (HL1 : Z.land wb 15 <= 15) by (rewrite land15_mod; pose proof (Z.mod_pos_bound wb (2 ^ 4) ltac:(lia)); lia).
        replace (15 <? Z.land wb 15) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (Z.land wb 15 <=? 15) with true by (symmetry; apply Z.leb_le; lia).
        destruct (Z.eqb_spec (Z.land wb 15) 0) as [E0|E0]; cbn [negb andb orb].
        * replace (is_window_blk _) with (@None blk) by reflexivity. unfold sbind at 1. cbn [sret mbind fst snd].
          rewrite inflateReset_same by reflexivity. replace (inflateStateCheck _) with false by reflexivity.
          rewrite inflateReset_eq by reflexivity. reflexivity.
        * destruct (Z.ltb_spec (Z.land wb 15) 8) as [H8|H8]; destruct (Z.leb_spec 8 (Z.land wb 15)) as [H8'|H8']; try (exfalso; lia); cbn [andb orb negb]; [reflexivity|].
          replace (is_window_blk _) with (@None blk) by reflexivity. unfold sbind at 1. cbn [sret mbind fst snd].
          rewrite inflateReset_same by reflexivity. replace (inflateStateCheck _) with false by reflexivity.
          rewrite inflateReset_eq by reflexivity. reflexivity.
      + destruct (Z.eqb_spec wb 0) as [E0|E0]; [exfalso; lia|]. cbn [negb andb].
        replace (15 <? wb) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Bool.orb_true_r. reflexivity.
  Qed.

  Lemma sfin_reach : forall (zc : ZCall) wb b init, ir2_bad wb = false -> ireach (ireset_s (s_pre init b wb)).
  Proof.
    intros zc wb b init Ebad.
    apply (IR_init zc wb (Some (b, init)) _ (zret0 (ireset_z (s_pre init b wb) (z_pre zc)) Z_OK)).
    unfold ipure. rewrite inflateInit2_m_eq. unfold sbind. cbn [zalloc hooks_pure mbind fst snd]. rewrite Ebad. reflexivity.
  Qed.

  Lemma sfin_witness : forall (zc : ZCall) wb b init, ir2_bad wb = false ->
    exists ch zr', ipure (ia_inflateInit2 inflate_model_ref hooks_pure zc wb) ch = Some (Some (ireset_s (s_pre init b wb)), zr').
  Proof.
    intros zc wb b init Ebad. exists (Some (b, init)). eexists.
    cbv beta iota delta [ia_inflateInit2 inflate_model_ref inflate_model_at].
    unfold ipure. rewrite inflateInit2_m_eq. unfold sbind. cbn [zalloc hooks_pure mbind fst snd]. rewrite Ebad. reflexivity.
  Qed.
End Model.

Lemma sfin_facts : forall init b wb,
  let s := ireset_s (s_pre init b wb) in
  is_mode s = HEAD /\ is_wrap s = ir2_wrap wb /\ is_window_blk s = None /\ is_wsize s = 0 /\ is_whave s = 0
  /\ is_wnext s = 0 /\ is_window s = arr_make 0 0 /\ is_self_blk s = b /\ is_wbits s = ir2_wb wb.
  (* 1.4 (zl14infl-r2): s_pre starts from a zeroed state (inflateInit2_'s memset), so the 1.3.1 conjuncts about the
     oracle's lens / work / codes / check bytes are dropped; this lemma has no users. *)
Proof. intros init b wb. cbv zeta. repeat split; reflexivity. Qed.

Lemma A5_u32 : forall o i, init_u32 (fun _ : Z => 165) o i = 2779096485.
Proof. intros. reflexivity. Qed.
Lemma A5_u16 : forall o i, init_u16 (fun _ : Z => 165) o i = 42405.
Proof. intros. reflexivity. Qed.
(* 1.4 (zl14infl-r2): s_pre reads the zero oracle, whatever [init] is *)
Lemma Z0_u32 : forall o i, init_u32 (fun _ : Z => 0) o i = 0.
Proof. intros. reflexivity. Qed.
Lemma Z0_u16 : forall o i, init_u16 (fun _ : Z => 0) o i = 0.
Proof. intros. reflexivity. Qed.
Lemma sfin_iwfx : forall b wb, iwfx (ireset_s (s_pre (fun _ : Z => 165) b wb)).
Proof.
  intros b wb. unfold iwfx.
  cbn [is_last is_havedict is_flags is_dmax is_total is_head is_bits is_hold is_length is_offset is_extra
       is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes
       is_sane is_back is_was ireset_s s_pre iset_back iset_sane iset_lencode iset_distcode iset_next iset_last iset_mode
       iset_dmax iset_flags iset_bits iset_hold iset_head iset_havedict iset_total iset_wnext iset_whave iset_wsize
       iset_wbits iset_wrap iset_window iset_window_blk iset_reqwrap iset_reqbits is_of_oracle lay_ref
       lay_length lay_offset lay_extra lay_lenbits lay_distbits lay_ncode lay_nlen lay_ndist lay_have lay_lens lay_work lay_codes lay_was].
  rewrite ?Z0_u32. unfold iarr_u16_of, iarr_u32_of. rewrite ?arr_len_init.
  repeat split; try lia; try (intros i Hi); rewrite ?arr_get_init; cbv beta; rewrite ?Z0_u16, ?Z0_u32; lia.
Qed.

Lemma spre_facts : forall init b wb,
  is_mode (s_pre init b wb) = HEAD /\ is_wrap (s_pre init b wb) = ir2_wrap wb.
Proof. intros. split; reflexivity. Qed.

Lemma iblocks_fin : forall init b wb, iblocks (ireset_s (s_pre init b wb)) = [(b, 7176)].  (* 1.4: sizeof(struct inflate_state) *)
Proof. intros. reflexivity. Qed.

Lemma land1_range : forall w, 0 <= Z.land w 1 <= 1.
Proof.
  intros w. assert (E : Z.land w 1 = w mod 2 ^ 1) by (rewrite <- Z.land_ones by lia; reflexivity). rewrite E.
  pose proof (Z.mod_pos_bound w (2 ^ 1) ltac:(lia)). lia.
Qed.

Lemma ir2_ranges : forall wb, ir2_bad wb = false -> 0 <= ir2_wrap wb < 8 /\ 0 <= ir2_wb wb <= 15 /\ -15 <= wb <= 47.
Proof.
  intros wb H. destruct (ir2_bad_cases wb) as [E|[(_ & Hr & _)|(_ & Hr & _)]]; [rewrite H in E; discriminate| |]; unfold ir2_wrap, ir2_wb.
  - rewrite (proj2 (Z.ltb_lt wb 0)) by lia. lia.
  - rewrite (proj2 (Z.ltb_ge wb 0)) by lia. rewrite (proj2 (Z.ltb_lt wb 48)) by lia.
    pose proof (Z.land_nonneg wb 15). assert (Z.land wb 15 <= 15) by (rewrite land15_mod; pose proof (Z.mod_pos_bound wb (2 ^ 4) ltac:(lia)); lia).
    assert (0 <= Z.shiftr wb 4 < 3) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.

Lemma ir2_wb_range : forall wb, ir2_bad wb = false -> (wb < 0 \/ Z.land wb 15 <> 0) -> 8 <= ir2_wb wb <= 15.
Proof.
  intros wb H Hnz. destruct (ir2_bad_cases wb) as [E|[(_ & Hr & Hv)|(_ & Hr & Hv)]]; [rewrite H in E; discriminate| |]; unfold ir2_wb; unfold wbits_valid in Hv.
  - rewrite (proj2 (Z.ltb_lt wb 0)) by lia.
    apply Bool.orb_true_iff in Hv as [Hv|Hv]; [apply Z.eqb_eq in Hv; lia|].
    apply andb_prop in Hv as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  - rewrite (proj2 (Z.ltb_ge wb 0)) by lia. rewrite (proj2 (Z.ltb_lt wb 48)) by lia.
    destruct Hnz as [?|Hnz]; [lia|].
    apply Bool.orb_true_iff in Hv as [Hv|Hv]; [apply Z.eqb_eq in Hv; lia|].
    apply andb_prop in Hv as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.


Section Calls.
End Calls.

Section Proofs.
End Proofs.
End RefInflateInit_run.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateUpdw_run.RefInflateInit_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma updw_core_keep : forall s src e c,
  let s' := updw_core s src e c in
  is_mode s' = is_mode s /\ is_wrap s' = is_wrap s /\ is_wbits s' = is_wbits s
  /\ is_window_blk s' = is_window_blk s /\ is_self_blk s' = is_self_blk s
  /\ is_lens s' = is_lens s /\ is_work s' = is_work s /\ is_codes s' = is_codes s /\ is_check s' = is_check s.
Proof.
  intros s src e c. cbv zeta. unfold updw_core, sA.
  destruct (is_wsize s =? 0);
  match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
  try (repeat split; reflexivity);
  match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
  try (repeat split; reflexivity);
  match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
  try (repeat split; reflexivity);
  match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
  repeat split; reflexivity.
Qed.

Definition uw_kept (st st' : inflate_state) : Prop :=
  is_flags st' = is_flags st /\ is_check st' = is_check st /\ is_total st' = is_total st
  /\ is_last st' = is_last st /\ is_bits st' = is_bits st /\ is_hold st' = is_hold st /\ iwfx st' = iwfx st.
Lemma updw_core_kept : forall s src e c, uw_kept s (updw_core s src e c).
Proof.
  intros s src e c. unfold uw_kept, updw_core, sA.
  destruct (is_wsize s =? 0);
  match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
  try (repeat split; reflexivity);
  match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
  try (repeat split; reflexivity);
  match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
  try (repeat split; reflexivity);
  match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
  repeat split; reflexivity.
Qed.
Lemma uw_kept_setwin : forall st s ob w, uw_kept st s -> uw_kept st (iset_window (iset_window_blk s ob) w).
Proof. intros st s ob w H. destruct s. exact H. Qed.

Lemma updw_core_iwfx : forall s src e c, iwfx (updw_core s src e c) = iwfx s.
Proof.
  intros s src e c. unfold updw_core, sA.
  destruct (is_wsize s =? 0);
  match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
  try reflexivity;
  match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
  try reflexivity;
  match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
  try reflexivity;
  match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
  reflexivity.
Qed.

Lemma updw_core_wfacts : forall s src e c,
  8 <= is_wbits s <= 15 -> arr_len (is_window s) = 2 ^ is_wbits s ->
  (is_wsize s = 0 \/ is_wsize s = arr_len (is_window s)) ->
  0 <= is_whave s < 2 ^ 32 -> 0 <= is_wnext s < 2 ^ 32 ->
  (is_wsize s <> 0 -> is_wnext s <= is_wsize s /\ is_whave s <= is_wsize s) ->
  (is_wsize s <> 0 -> is_whave s < is_wsize s -> is_wnext s = is_whave s) ->
  0 <= c < 2 ^ 32 ->
  let s' := updw_core s src e c in
  is_wsize s' = arr_len (is_window s) /\ 0 <= is_wnext s' <= arr_len (is_window s) /\ 0 <= is_whave s' <= arr_len (is_window s)
  /\ (is_whave s' < arr_len (is_window s) -> is_wnext s' = is_whave s')
  /\ arr_len (is_window s') = arr_len (is_window s).
Proof.
  intros s src e c Hwb HWN Hwsz Hwh Hwn Hwhn Hinv Hc. cbv zeta.
  assert (HWN0 : 256 <= arr_len (is_window s) <= 32768).
  { rewrite HWN. split; [change 256 with (2 ^ 8) | change 32768 with (2 ^ 15)]; apply Z.pow_le_mono_r; lia. }
  set (WN := arr_len (is_window s)) in *.
  assert (Hsh : shl32 1 (is_wbits s) = WN).
  { unfold shl32. rewrite Z.shiftl_1_l, <- HWN. apply wrap32_id. lia. }
  unfold updw_core.
  assert (SA : is_wsize (sA s) = WN /\ 0 <= is_wnext (sA s) <= WN /\ 0 <= is_whave (sA s) <= WN
               /\ (is_whave (sA s) < WN -> is_wnext (sA s) = is_whave (sA s))
               /\ is_window (sA s) = is_window s).
  { unfold sA. destruct (Z.eqb_spec (is_wsize s) 0) as [Hw0|Hw0].
    - cbn [is_wsize is_wnext is_whave is_window iset_whave iset_wnext iset_wsize]. rewrite Hsh. repeat split; try reflexivity; lia.
    - specialize (Hwhn Hw0). specialize (Hinv Hw0). destruct Hwsz as [?|Hws]; [contradiction|]. rewrite <- Hws. repeat split; try reflexivity; try lia. }
  set (s1 := sA s) in *. clearbody s1. destruct SA as (W1 & W2 & W3 & W4 & W5).
  destruct (Z.leb_spec (is_wsize s1) c) as [Hle|Hgt].
  - cbn [is_wsize is_wnext is_whave is_window iset_whave iset_wnext iset_window]. rewrite W1.
    rewrite arr_len_blit, W5. repeat split; lia.
  - rewrite W1 in Hgt |- *.
    assert (Hd0 : wrap32 (WN - is_wnext s1) = WN - is_wnext s1) by (apply wrap32_id; lia).
    rewrite Hd0.
    set (dist := if c <? WN - is_wnext s1 then c else WN - is_wnext s1).
    assert (Hdist : 0 <= dist <= c /\ dist <= WN - is_wnext s1 /\ (dist = c \/ dist = WN - is_wnext s1)).
    { subst dist. destruct (Z.ltb_spec c (WN - is_wnext s1)); lia. }
    clearbody dist.
    assert (Hcd : wrap32 (c - dist) = c - dist) by (apply wrap32_id; lia). rewrite Hcd.
    destruct (Z.eqb_spec (c - dist) 0) as [Hz|Hz]; cbn [negb].
    + assert (Hnd : wrap32 (is_wnext s1 + dist) = is_wnext s1 + dist) by (apply wrap32_id; lia).
      cbn [is_wnext is_wsize is_whave is_window iset_wnext iset_window iset_whave]. rewrite ?Hnd, ?W1.
      destruct (Z.eqb_spec (is_wnext s1 + dist) WN) as [Heq|Heq];
        cbn [is_whave is_wsize is_wnext is_window iset_wnext iset_window iset_whave]; rewrite ?W1;
        destruct (Z.ltb_spec (is_whave s1) WN) as [Hlt|Hlt];
        cbn [is_whave is_wsize is_wnext is_window iset_wnext iset_window iset_whave]; rewrite ?W1;
        rewrite ?arr_len_blit, ?W5.
      * specialize (W4 Hlt). rewrite (wrap32_id (is_whave s1 + dist)) by lia. repeat split; lia.
      * repeat split; lia.
      * specialize (W4 Hlt). rewrite (wrap32_id (is_whave s1 + dist)) by lia. repeat split; lia.
      * repeat split; lia.
    + cbn [is_whave is_wsize is_wnext is_window iset_wnext iset_window iset_whave].
      rewrite !arr_len_blit, W5. repeat split; lia.
Qed.


Section Proofs.

  Definition pc_updatewindow : Z := 0x18744.

  Lemma mul64_1 : forall x, 0 <= x < 2 ^ 64 -> mul64 x 1 = x.
  Proof.
    intros x Hx. unfold mul64, wrap64. rewrite Z.mul_1_r. change 18446744073709551615 with (Z.ones 64).
    rewrite Z.land_ones by lia. apply Z.mod_small. lia.
  Qed.

  Lemma shl32_wbits : forall w, 8 <= w <= 15 -> shl32 1 w = 2 ^ w.
  Proof.
    intros w Hw. unfold shl32. rewrite Z.shiftl_1_l. apply wrap32_id.
    split; [apply Z.pow_nonneg; lia|]. apply (Z.pow_lt_mono_r 2); lia.
  Qed.
End Proofs.
