(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflate_runA.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeA1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeS1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma MF_ext : forall m s s' h b,
  is_wrap s' = is_wrap s -> is_flags s' = is_flags s -> is_check s' = is_check s -> is_wbits s' = is_wbits s ->
  is_length s' = is_length s -> is_offset s' = is_offset s -> is_extra s' = is_extra s ->
  is_lencode s' = is_lencode s -> is_distcode s' = is_distcode s -> is_lenbits s' = is_lenbits s -> is_distbits s' = is_distbits s ->
  is_ncode s' = is_ncode s -> is_nlen s' = is_nlen s -> is_ndist s' = is_ndist s -> is_have s' = is_have s ->
  is_lens s' = is_lens s -> is_codes s' = is_codes s ->
  is_hold s' = h -> is_bits s' = b ->
  MF m s h b -> MF m s' h b.
Proof.
  intros m s s' h b E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 Eh Eb H.
  unfold MF, common, tables, lneed, cneed, code_at in *.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17.
  destruct (m =? MEM) eqn:EM.
  -
    revert H. repeat match goal with |- (if ?c then _ else _) -> _ => lazymatch c with MEM =? MEM => fail | _ => destruct c; [intros X; exact X|] end end.
    intros _. exact (conj Eh Eb).
  - revert H. repeat match goal with |- (if ?c then _ else _) -> (if ?c then _ else _) => destruct c; [intros X; exact X|] end.
    intros X; exact X.
Qed.

Ltac csplit := lazymatch goal with |- _ /\ _ => split; csplit | _ => idtac end.

Lemma MF_set_check : forall m s ck h b,
  (is_flags s = 0 -> adler_canon ck) -> (m = FLAGS -> adler_canon ck) -> MF m s h b -> MF m (iset_check s ck) h b.
Proof.
  intros m s ck h b Hc Hf. unfold MF, common, tables, lneed, cneed, code_at. sacc.
  destruct (Z.eqb_spec m FLAGS) as [->|NE].
  { cbn. intros [A B]. split; [exact A|exact (Hf eq_refl)]. }
  repeat match goal with |- (if ?c then _ else _) -> (if ?c then _ else _) => destruct c end;
    first [ intros X; exact X
          | intros X; decompose [and] X; csplit; first [assumption | exact Hc] ].
Qed.

Lemma CORE_updw : forall s src end_ copy, CORE s ->
  is_window_blk s <> None -> 0 <= copy ->
  CORE (updw_core s src end_ copy).
Proof.
  intros s src end_ copy HC Hb Hcopy.
  pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
  destruct (C2 Hb) as [WL WB].
  unfold updw_core, sA.
  pose proof (wrap32_range (Z.shiftl 1 (is_wbits s))) as VR. unfold shl32 in *.
  set (V := wrap32 (Z.shiftl 1 (is_wbits s))) in *.

  set (s1 := if is_wsize s =? 0 then iset_whave (iset_wnext (iset_wsize s V) 0) 0 else s).
  assert (H1 : is_wsize s1 = V /\ 0 <= is_whave s1 <= V /\ 0 <= is_wnext s1 /\ (V <> 0 -> is_wnext s1 < V) /\ (is_whave s1 < V -> is_wnext s1 = is_whave s1)
               /\ is_window_blk s1 = is_window_blk s /\ arr_len (is_window s1) = V /\ is_wbits s1 = is_wbits s /\ is_wrap s1 = is_wrap s
               /\ arr_len (is_lens s1) = 320 /\ arr_len (is_work s1) = 288 /\ arr_len (is_codes s1) = 1444 /\ is_sane s1 = 1 /\ 0 <= is_length s1 < 2 ^ 32).
  { subst s1. destruct (Z.eqb_spec (is_wsize s) 0) as [Z0|Z0]; sacc.
    - repeat split; try assumption; try lia.
    - pose proof (C3 Z0). pose proof (C7 Z0). pose proof (C8 Z0). repeat split; try assumption; try lia. }
  clearbody s1. destruct H1 as (W1 & W2 & W3 & W4 & W5 & B1 & L1 & WB1 & WR1 & A1 & A2 & A3 & S1 & LL1).
  Ltac norm1 W1 B1 L1 WB1 WR1 A1 A2 A3 S1 V := unfold shl32; rewrite ?arr_len_blit, ?W1, ?B1, ?L1, ?WB1, ?WR1, ?A1, ?A2, ?A3, ?S1; fold V.
  destruct (Z.leb_spec (is_wsize s1) copy) as [LE|GT]; unfold CORE; sacc; norm1 W1 B1 L1 WB1 WR1 A1 A2 A3 S1 V.
  - repeat split; first [ lia | reflexivity | (intros X; exfalso; exact (Hb X)) | (intros X; exfalso; exact (WB X))
            | (intros _; split; [first [lia | assumption | reflexivity] | exact WB]) | (intros; lia) | (pose proof W5; intros; lia) ].
  - rewrite (wrap32_id (V - is_wnext s1)) by lia.
    set (dist := if copy <? V - is_wnext s1 then copy else V - is_wnext s1).
    assert (Hd : 0 <= dist <= copy /\ dist <= V - is_wnext s1) by (subst dist; destruct (Z.ltb_spec copy (V - is_wnext s1)); lia).
    rewrite (wrap32_id (copy - dist)) by lia.
    destruct (Z.eqb_spec (copy - dist) 0) as [CD|CD]; cbn [negb]; sacc; norm1 W1 B1 L1 WB1 WR1 A1 A2 A3 S1 V.
    + rewrite (wrap32_id (is_wnext s1 + dist)) by lia.
      destruct (Z.eqb_spec (is_wnext s1 + dist) V) as [EV|EV]; sacc; norm1 W1 B1 L1 WB1 WR1 A1 A2 A3 S1 V;
        (destruct (Z.ltb_spec (is_whave s1) V) as [WH|WH]; sacc; norm1 W1 B1 L1 WB1 WR1 A1 A2 A3 S1 V);
        rewrite ?(wrap32_id (is_whave s1 + dist)) by lia; repeat split; first [ lia | reflexivity | (intros X; exfalso; exact (Hb X)) | (intros X; exfalso; exact (WB X))
            | (intros _; split; [first [lia | assumption | reflexivity] | exact WB]) | (intros; lia) | (pose proof W5; intros; lia) ].
    + repeat split; first [ lia | reflexivity | (intros X; exfalso; exact (Hb X)) | (intros X; exfalso; exact (WB X))
            | (intros _; split; [first [lia | assumption | reflexivity] | exact WB]) | (intros; lia) | (pose proof W5; intros; lia) ].
Qed.

Lemma updw_core_fields : forall s src end_ copy,
  let s' := updw_core s src end_ copy in
  is_mode s' = is_mode s /\ is_wrap s' = is_wrap s /\ is_flags s' = is_flags s /\ is_check s' = is_check s /\ is_wbits s' = is_wbits s
  /\ is_length s' = is_length s /\ is_offset s' = is_offset s /\ is_extra s' = is_extra s
  /\ is_lencode s' = is_lencode s /\ is_distcode s' = is_distcode s /\ is_lenbits s' = is_lenbits s /\ is_distbits s' = is_distbits s
  /\ is_ncode s' = is_ncode s /\ is_nlen s' = is_nlen s /\ is_ndist s' = is_ndist s /\ is_have s' = is_have s
  /\ is_lens s' = is_lens s /\ is_codes s' = is_codes s /\ is_hold s' = is_hold s /\ is_bits s' = is_bits s /\ is_total s' = is_total s
  /\ is_window_blk s' = is_window_blk s /\ is_last s' = is_last s.
Proof.
  intros s src end_ copy. cbv zeta. unfold updw_core, sA.
  destruct (is_wsize s =? 0); sacc;
  match goal with |- context [if ?c then _ else _] => destruct c end; sacc; try (csplit; reflexivity);
  match goal with |- context [if ?c then _ else _] => destruct c end; sacc; try (csplit; reflexivity);
  match goal with |- context [if ?c then _ else _] => destruct c end; sacc; try (csplit; reflexivity);
  match goal with |- context [if ?c then _ else _] => destruct c end; sacc; try (csplit; reflexivity).
Qed.

Lemma arr_get_of_list_byte : forall l i, bytes_ok l -> 0 <= arr_get (arr_of_list l) i < 256.
Proof.
  intros l i Hb. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  destruct ((0 <=? i) && (i <? 0 + zlength l) && arr_inb (arr_make (zlength l) 0) i) eqn:C.
  - unfold bytes_ok in Hb. rewrite Forall_forall in Hb.
    apply andb_prop in C as [C _]. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
    apply Hb. apply nth_In. unfold zlength in C2. lia.
  - unfold arr_make. rewrite arr_get_init. lia.
Qed.

Ltac munf := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY,
  TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *.
Ltac mode_lit E := first [ apply Z.eqb_eq in E | apply Bool.orb_true_iff in E; destruct E as [E|E]; mode_lit E ].

Lemma MF_mode_range : forall m s h b, MF m s h b -> HEAD <= m <= MEM.
Proof.
  intros m s h b HM. unfold MF in HM. revert HM.
  repeat match goal with |- (if ?c then _ else _) -> _ =>
    let E := fresh "E" in destruct c eqn:E;
    [ mode_lit E; revert E; clear; intros; munf; lia |] end.
  intros X. destruct X.
Qed.

Lemma INV_check : forall st, INV st -> inflateStateCheck st = false.
Proof.
  intros st (_ & _ & HM). apply MF_mode_range in HM. unfold inflateStateCheck.
  destruct (Z.ltb_spec (is_mode st) HEAD) as [L|L]; [munf; lia|].
  destruct (Z.ltb_spec SYNC (is_mode st)) as [G|G]; [munf; lia|reflexivity].
Qed.

Lemma lv_fin_INV : forall flush m s2 c2 r,
  CORE s2 -> HB (ir_hold r) (ir_bits r) -> is_hold s2 = ir_hold r -> is_bits s2 = ir_bits r -> is_mode s2 = m ->
  MF m s2 (ir_hold r) (ir_bits r) ->
  (m = FLAGS -> wrap32 (ir_out r - ic_avail_out c2) = 0) ->
  INV (fst (lv_fin flush s2 c2 r)).
Proof.
  intros flush m s2 c2 r HC HBr Eh Eb Em HM Hfl.
  unfold lv_fin. cbv zeta.
  set (out := wrap32 (ir_out r - ic_avail_out c2)) in *.
  match goal with |- INV (fst (let '(a, b) := (if ?cnd then _ else _) in _)) => destruct cnd eqn:C end; cbn [fst].
  - unfold INV. sacc. rewrite Em, Eh, Eb. split; [core_keep HC; apply CORE_length; exact HC|]. split; [exact HBr|].
    apply MF_set_check.
    + sacc. intros F0. unfold UPDATE_CHECK_bytes. sacc. rewrite F0. cbn [Z.eqb negb]. unfold iadler32_upd. apply adler32_model_canon.
    + intros EM. exfalso. rewrite (Hfl EM) in C. rewrite Z.eqb_refl, Bool.andb_false_r in C. discriminate C.
    + apply (MF_ext _ s2); first [sacc; reflexivity | sacc; assumption | exact HM].
  - unfold INV. sacc. rewrite Em, Eh, Eb. split; [core_keep HC; apply CORE_length; exact HC|]. split; [exact HBr|].
    apply (MF_ext _ s2); first [sacc; reflexivity | sacc; assumption | exact HM].
Qed.

Lemma CORE_fresh_window : forall s b g,
  CORE s -> is_window_blk s = None -> is_wbits s <> 0 ->
  CORE (iset_window (iset_window_blk s (Some b)) (iarr_u8_of g 0 (shl32 1 (is_wbits s)))).
Proof.
  intros s b g HC EB WB.
  pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
  pose proof (C1 EB) as Z0.
  unfold CORE. sacc. unfold iarr_u8_of. rewrite arr_len_init. rewrite Z0.
  split; [intros X; discriminate X|]. split; [intros _; split; [reflexivity|exact WB]|].
  split; [intros X; exfalso; exact (X eq_refl)|]. split; [exact C4|]. split; [exact C5|].
  split; [intros _; exact (C6 Z0)|]. split; [intros X; exfalso; exact (X eq_refl)|]. split; [intros X; exfalso; exact (X eq_refl)|].
  split; [intros X; exfalso; exact (WB X)|]. exact (conj C10 (conj C11 (conj C12 (conj C13 C14)))).
Qed.

Lemma inf_leave_INV : forall flush s c r ch s' zr ch',
  WINV (mkW s c r) -> inf_leave hooks_pure flush (mkW s c r) ch = MRet ((s', zr), ch') -> INV s'.
Proof.
  intros flush s c r ch s' zr ch' HW.
  unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (HC & HR & HMF & HWF & HWB).
  pose proof HR as (RN & RH & RNH & RP & RL & RPL & HBr & RIN & RNI & RNO).
  pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & _).
  rewrite (inf_leave_eq hooks_pure). unfold sbind.

  assert (HCR : CORE (s_rest s r)) by (unfold s_rest; core_keep HC; apply CORE_length; exact HC).
  assert (HMR : MF (is_mode s) (s_rest s r) (ir_hold r) (ir_bits r)).
  { apply (MF_ext _ s); unfold s_rest; first [sacc; reflexivity | exact HMF]. }
  assert (HFL : is_mode s = FLAGS -> wrap32 (ir_out r - ic_avail_out (c_rest c r)) = 0).
  { intros EM. unfold c_rest. sacc. rewrite EM in HWF. revert HWF. mred. intros [E1 E2]. rewrite E1, <- RPL, E2. replace (0 + ir_left r - ir_left r) with 0 by lia. reflexivity. }

  assert (TAIL : forall s2 g, CORE s2 -> is_hold s2 = ir_hold r -> is_bits s2 = ir_bits r -> is_mode s2 = is_mode s ->
            MF (is_mode s) s2 (ir_hold r) (ir_bits r) ->
            sret (lv_fin flush s2 (c_rest c r) r) g = MRet ((s', zr), ch') -> INV s').
  { intros s2 g HC2 Eh Eb Em HM2 E. unfold sret in E.
    apply (f_equal (fun mm => match mm with MRet p => fst (fst p) | _ => s' end)) in E. cbn [fst] in E.
    rewrite <- E. exact (lv_fin_INV flush (is_mode s) s2 (c_rest c r) r HC2 HBr Eh Eb Em HM2 HFL). }
  destruct (lv_cond flush (s_rest s r) (c_rest c r) r) eqn:LC.
  -
    assert (WB : is_wbits s <> 0).
    { intros W. destruct (C9 W) as [N _]. pose proof (C1 N) as Z0. pose proof (HWB W) as P0.
      assert (NLD : is_mode s <> LENGTH /\ is_mode s <> DONE).
      { split; intros E; rewrite E in HMF; revert HMF; mred; intros [X _]; exact (X W). }
      unfold WF in HWF.
      revert LC. unfold lv_cond, s_rest, c_rest. sacc. rewrite Z0, Z.eqb_refl. change (negb true) with false. rewrite Bool.orb_false_l.
      destruct (Z.eqb_spec (is_mode s) BAD) as [EB'|NB].
      - rewrite EB' in *. replace (BAD <? BAD) with false by reflexivity. rewrite Bool.andb_false_r. cbn [andb]. intros X; discriminate X.
      - assert (EO : ir_out r = ir_left r).
        { destruct NLD as [N1 N2]. rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2) in HWF. cbn [orb] in HWF.
          destruct ((is_mode s =? HEAD) || (is_mode s =? FLAGS)); [destruct HWF as [E1 _]|rename HWF into E1]; rewrite E1, <- RPL, P0; lia. }
        rewrite EO. replace (ir_left r - ir_left r) with 0 by lia. change (wrap32 0 =? 0) with true. cbn [negb andb]. intros X; discriminate X. }
    rewrite updatewindow_pure. cbn [mbind fst snd].
    unfold uw_pure. replace (is_window_blk (s_rest s r)) with (is_window_blk s) by reflexivity.
    pose proof (wrap32_range (ir_out r - ic_avail_out (c_rest c r))) as CP.
    destruct (is_window_blk s) as [b|] eqn:EB.
    + apply TAIL.
      * apply CORE_updw; [exact HCR | unfold s_rest; sacc; rewrite EB; intros X; discriminate X | lia].
      * rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (updw_core_fields _ _ _ _)))))))))))))))))))). reflexivity.
      * rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (updw_core_fields _ _ _ _))))))))))))))))))))). reflexivity.
      * rewrite (proj1 (updw_core_fields _ _ _ _)). reflexivity.
      * pose proof (updw_core_fields (s_rest s r) (ic_outbuf (c_rest c r)) (ic_next_out (c_rest c r)) (wrap32 (ir_out r - ic_avail_out (c_rest c r)))) as F.
        cbv zeta in F. decompose [and] F.
        apply (MF_ext _ (s_rest s r)); first [assumption | exact HMR | idtac].
        all: match goal with H : ?f (updw_core ?ba _ _ _) = ?f ?ba |- ?f _ = _ => rewrite H; reflexivity end.
    + destruct ch as [[b g]|].
      * set (s1 := iset_window (iset_window_blk (s_rest s r) (Some b)) (iarr_u8_of g 0 (shl32 1 (is_wbits (s_rest s r))))).
        assert (HC1 : CORE s1) by (subst s1; apply CORE_fresh_window; [exact HCR | exact EB | exact WB]).
        assert (HM1 : MF (is_mode s) s1 (ir_hold r) (ir_bits r)).
        { apply (MF_ext _ s); subst s1; unfold s_rest; first [sacc; reflexivity | exact HMF]. }
        apply TAIL.
        -- apply CORE_updw; [exact HC1 | subst s1; sacc; intros X; discriminate X | lia].
        -- rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (updw_core_fields _ _ _ _)))))))))))))))))))). reflexivity.
        -- rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (updw_core_fields _ _ _ _))))))))))))))))))))). reflexivity.
        -- rewrite (proj1 (updw_core_fields _ _ _ _)). reflexivity.
        -- pose proof (updw_core_fields s1 (ic_outbuf (c_rest c r)) (ic_next_out (c_rest c r)) (wrap32 (ir_out r - ic_avail_out (c_rest c r)))) as F.
           cbv zeta in F. decompose [and] F.
           apply (MF_ext _ s1); first [assumption | exact HM1 | idtac].
           all: first [ match goal with H : ?f (updw_core ?ba _ _ _) = ?f ?ba |- ?f _ = _ => rewrite H; reflexivity end | subst s1; sacc; reflexivity ].
      *
        unfold sret. intros E.
        apply (f_equal (fun mm => match mm with MRet p => fst (fst p) | _ => s' end)) in E. cbn [fst] in E.
        rewrite <- E. unfold lv_mem. cbn [fst]. rewrite lv_pre_shape. cbv zeta. cbn [fst].
        match goal with |- context [if ?bb then _ else _] => destruct bb end;
          (unfold INV, s_rest; sacc; split; [core_keep HC; apply CORE_length; exact HC|]; split; [exact HBr|]; mred; split; reflexivity).
  -
    cbn [sret mbind fst snd]. intros E. apply (TAIL (s_rest s r) ch); first [exact HCR | reflexivity | exact HMR | exact E].
Qed.
