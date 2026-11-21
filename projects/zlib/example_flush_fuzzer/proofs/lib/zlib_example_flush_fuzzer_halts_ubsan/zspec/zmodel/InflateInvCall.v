(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb ModelRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab InflateInvKit InflateInvApi InflateInvLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition UR (s : inflate_state) : Prop :=
  SRNGq s
  /\ (0 <= is_bits s < 64 /\ 0 <= is_hold s < 2 ^ is_bits s)
  /\ match is_window_blk s with
     | Some _ => arr_len (is_window s) = 2 ^ is_wbits s /\ (is_wsize s = 0 \/ is_wsize s = 2 ^ is_wbits s)
     | None => arr_len (is_window s) = 0 /\ is_wsize s = 0
     end.

Definition UI (s : inflate_state) : Prop := UR s /\ sinv s /\ binv_saved s /\ cks s.

Definition zcall_ok (zc : ZCall) : Prop :=
  Forall (fun b => 0 <= b < 256) (zc_input zc) /\ zlength (zc_input zc) < 2 ^ 32
  /\ 0 <= zc_avail_out zc < 2 ^ 32
  /\ 0 <= zs_total_in (zc_strm zc) < 2 ^ 64 /\ 0 <= zs_total_out (zc_strm zc) < 2 ^ 64
  /\ 0 <= zs_adler (zc_strm zc) < 2 ^ 64 /\ - 2 ^ 31 <= zs_data_type (zc_strm zc) < 2 ^ 31.

Definition zret_ok (z : ZRet) : Prop :=
  0 <= zr_consumed z
  /\ 0 <= zs_total_in (zr_strm z) < 2 ^ 64 /\ 0 <= zs_total_out (zr_strm z) < 2 ^ 64
  /\ 0 <= zs_adler (zr_strm z) < 2 ^ 64 /\ - 2 ^ 31 <= zs_data_type (zr_strm z) < 2 ^ 31.

Definition XPOST (NI NO WN TOT0 : Z) (w : iw) : Prop :=
  LRNGq NI NO WN TOT0 w /\ sinv (w_s w) /\ binv w /\ cks (w_s w).

Definition UIleaf {St : Type} (p : inflate_state * ZRet) (_ : St) : Prop := UI (fst p) /\ zret_ok (snd p).

Definition leave_ui_stmt : Prop :=
  forall (St : Type) (hooks : zhooks St) (flush NI NO WN TOT0 : Z) (w : iw),
    0 <= NI < 2 ^ 32 -> 0 <= NO < 2 ^ 32 -> XPOST NI NO WN TOT0 w ->
    sall (fun _ => True) UIleaf (inf_leave hooks flush w).


Lemma arr_get_of_list_In : forall l i, 0 <= i < zlength l -> In (arr_get (arr_of_list l) i) l.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  unfold arr_inb, arr_make. rewrite arr_len_init.
  replace ((0 <=? i) && (i <? 0 + zlength l) && ((0 <=? i) && (i <? zlength l))) with true
    by (symmetry; rewrite !andb_true_iff; rewrite !Z.leb_le, !Z.ltb_lt; lia).
  rewrite Z.sub_0_r. apply nth_In. unfold zlength in Hi. lia.
Qed.

Lemma Forall_arr_of_list : forall (P : Z -> Prop) l, Forall P l -> forall i, 0 <= i < zlength l -> P (arr_get (arr_of_list l) i).
Proof. intros P l H i Hi. apply (proj1 (Forall_forall P l) H). apply arr_get_of_list_In. exact Hi. Qed.


Lemma s_entryM_fields : forall st,
  is_hold (s_entryM st) = is_hold st /\ is_bits (s_entryM st) = is_bits st /\ is_window (s_entryM st) = is_window st
  /\ is_window_blk (s_entryM st) = is_window_blk st /\ is_wbits (s_entryM st) = is_wbits st /\ is_wsize (s_entryM st) = is_wsize st.
Proof. intros st. unfold s_entryM. destruct (is_mode st =? TYPE); [destruct st|]; cbn; repeat split; reflexivity. Qed.

Lemma SRNGq_entryM : forall st, SRNGq st -> SRNGq (s_entryM st).
Proof.
  intros st H. unfold s_entryM. destruct (is_mode st =? TYPE); [| exact H].
  destruct st; unfold SRNGq in *; cbn -[Z.pow Z.le Z.lt arr_get arr_len ARRB] in *.
  destruct H as (Hm & Hrest). split; [unfold HEAD, TYPEDO, SYNC; lia | exact Hrest].
Qed.


Lemma zcall_NI : forall zc, zcall_ok zc -> 0 <= zlength (zc_input zc) < 2 ^ 32.
Proof. intros zc (_ & H & _). unfold zlength in *. lia. Qed.
Lemma zcall_NO : forall zc, zcall_ok zc -> 0 <= zc_avail_out zc < 2 ^ 32.
Proof. intros zc (_ & _ & H & _). exact H. Qed.

Section Call.
  Variables (st : inflate_state) (zc : ZCall).
  Let c := icall_of_zcall zc.
  Let NI := zlength (zc_input zc).
  Let NO := zc_avail_out zc.
  Let WN := arr_len (is_window st).
  Let TOT0 := zs_total_out (zc_strm zc).

  Lemma LRNGq_entry : UR st -> zcall_ok zc -> LRNGq NI NO WN TOT0 (W1M st c).
  Proof.
    intros (SR & (Hb & Hh) & WS) (Zb & Zl & Zo & Zti & Zto & Zad & Zdt).
    pose proof (s_entryM_fields st) as (Eh & Eb & Ew & Ewb & Ewbits & Ews).
    apply LRNGq_mk.
    - apply SRNGq_entryM. exact SR.
    - unfold CINV. subst c. unfold icall_of_zcall, W1M.
      cbn [w_c ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg].
      rewrite arr_len_of_list, arr_len_make. subst NI NO. unfold zlength in *.
      repeat match goal with |- _ /\ _ => split end; try lia.
      + intros i Hi. apply (Forall_arr_of_list _ _ Zb). unfold zlength. exact Hi.
      + intros i Hi. rewrite arr_get_make. lia.
    - unfold RINV. subst c. unfold icall_of_zcall, W1M.
      cbn [w_r ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
      rewrite Eh, Eb. subst NI NO. unfold zlength in *. repeat match goal with |- _ /\ _ => split end; lia.
    - unfold WINV, W1M. cbn [w_s]. rewrite Ew, Ewb, Ewbits, Ews. subst WN. split; [reflexivity|].
      assert (Hwb : 8 <= is_wbits st <= 15) by (destruct SR as (_ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
      assert (Hp : 256 <= 2 ^ is_wbits st) by (change 256 with (2 ^ 8); apply Z.pow_le_mono_r; lia).
      destruct (is_window_blk st) as [b|]; destruct WS as [L S].
      + split; [right; exact L|]. split; [| destruct S as [S|S]; [left; exact S | right; rewrite S, L; reflexivity]].
        split; [intros X; exfalso; lia | intros X; discriminate X].
      + rewrite L. split; [left; reflexivity|]. split; [split; [reflexivity | reflexivity] | left; exact S].
    - unfold CROSS. subst c TOT0. unfold icall_of_zcall, W1M. cbn [w_c w_r ic_total_out ir_out ir_left ir_put ic_avail_out ic_next_out].
      rewrite Z.sub_diag, !Z.add_0_r. reflexivity.
  Qed.

  Theorem ui_entry : UI st -> zcall_ok zc -> pinv NI NO WN TOT0 (W1M st c).
  Proof.
    intros (R & SI & BS & CK) ZC.
    apply (pinv_entry NI NO WN TOT0 (zcall_NI zc ZC) (zcall_NO zc ZC) st c (LRNGq_entry R ZC) SI BS CK).
    subst c. reflexivity.
  Qed.
End Call.


Lemma UR_of_exit : forall NI NO WN TOT0 s c r,
  LRNGq NI NO WN TOT0 (mkW s c r) -> is_hold s = ir_hold r -> is_bits s = ir_bits r -> UR s.
Proof.
  intros NI NO WN TOT0 s c r LR Eh Eb. apply LRNGq_iff in LR. destruct LR as (SR & CI & RI & WI & CR).
  split; [exact SR|]. split.
  - rewrite Eh, Eb. destruct RI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rb & Rh). split; [exact Rb | exact Rh].
  - destruct WI as (L & P & N & S). rewrite L.
    destruct (is_window_blk s) as [b|].
    + assert (WN <> 0) by (intros X; pose proof (proj1 N X) as Y; discriminate Y).
      destruct P as [P|P]; [exfalso; exact (H P)|]. split; [exact P | rewrite <- P; exact S].
    + assert (WN = 0) by (apply (proj2 N); reflexivity). rewrite H in S. split; [exact H | destruct S as [S|S]; exact S].
Qed.

Lemma zret_ok_of_CINV : forall NI NO c rc, CINV NI NO c -> zret_ok (zret_of_icall c rc).
Proof.
  intros NI NO c rc CI. unfold zret_ok, zret_of_icall, zstrm_of_icall. cbn.
  destruct CI as (_ & _ & Cni & _ & _ & _ & _ & _ & _ & _ & Cti & Cto & Cad & Cdt). repeat split; lia.
Qed.

Theorem ret_ui : forall NI NO WN TOT0 w rc,
  XPOST NI NO WN TOT0 w -> is_hold (w_s w) = ir_hold (w_r w) -> is_bits (w_s w) = ir_bits (w_r w) ->
  UI (w_s w) /\ zret_ok (zret_of_icall (w_c w) rc).
Proof.
  intros NI NO WN TOT0 [s c r] rc (LR & SI & BI & CK) Eh Eb. cbn [w_s w_c w_r] in *. split.
  - split; [exact (UR_of_exit NI NO WN TOT0 s c r LR Eh Eb)|]. split; [exact SI|]. split; [| exact CK].
    exact (binv_saved_of_binv s c r BI Eh Eb).
  - apply (zret_ok_of_CINV NI NO). exact (LRNGq_C NI NO WN TOT0 s c r LR).
Qed.


Section Inflate.
  Hypothesis LEAVE : leave_ui_stmt.

End Inflate.
