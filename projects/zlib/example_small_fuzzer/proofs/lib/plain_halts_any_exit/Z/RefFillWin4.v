(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemFill.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefAdler_run.

Module RefFillWin1.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemFill.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefAdler_run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable S : Z.
Variable sp : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.

Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).

Definition LF : franges :=
  [(sp - 176, 176); (S + 128, 4); (S + 152, 8); (S + 172, 12); (S + 5932, 4); (S + 5944, 8);
   (W, 2 * ws); (PV, 2 * ws); (HD, 2 * hs); (strm, 24); (strm + 96, 8)].

Definition fr_layout : list (Z * nat) :=
  [(8, 8%nat); (16, 8%nat); (24, 8%nat); (32, 8%nat); (40, 8%nat); (48, 8%nat);
   (56, 8%nat); (64, 8%nat); (72, 8%nat); (80, 8%nat); (88, 8%nat)].

Definition CSTL (s : deflate_state) : Prop :=
  arr_len (ds_window s) = 2 * ws /\ arr_len (ds_prev s) = ws /\ arr_len (ds_head s) = hs
  /\ cs_input (ds_strm s) = cs_input (ds_strm ds) /\ ds_wrap s = ds_wrap ds
  /\ ds_w_size s = ws /\ ds_hash_size s = hs.


Lemma fr_layout_within : layout_within fr_layout 96 = true.
Proof. vm_compute. reflexivity. Qed.

Definition shv (m : Z) : Z := if m <? ws then 0 else m - ws.
Definition LB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 63); (36%nat, 2 ^ 63);
   (37%nat, 2 ^ 63); (38%nat, 2 ^ 63); (39%nat, 32769); (40%nat, 65537)].

Local Ltac open_lregs H :=
  let H' := fresh "HL'" in pose proof H as H';
  destruct H' as (P20 & P2 & P8 & P9 & P18 & P19 & P21 & P22).


Definition moreof (s : deflate_state) : Z := 2 * ws - ds_strstart s - ds_lookahead s.


Lemma CSTL_set_window : forall s w', CSTL s -> arr_len w' = 2 * ws -> CSTL (set_window s w').
Proof. intros s w' HK Hl. unfold CSTL in *. dsred. rewrite Hl. tauto. Qed.


Definition slide_fields (s1 : deflate_state) : deflate_state :=
  let s2 := set_match_start s1 (wrap32 (ds_match_start s1 - ws)) in
  let s3 := set_strstart s2 (ds_strstart s1 - ws) in
  let s4 := set_block_start s3 (ds_block_start s1 - ws) in
  if ds_strstart s1 - ws <? ds_insert s1 then set_insert s4 (ds_strstart s1 - ws) else s4.

Local Ltac in_LF := unfold LF; repeat first [ apply sub_franges_here; cbn; lia | apply sub_franges_later ].

Local Ltac cstl := intros; unfold CSTL in *; dsred; assumption.
Lemma CSTL_match_start : forall s v, CSTL s -> CSTL (set_match_start s v). Proof. cstl. Qed.
Lemma CSTL_strstart : forall s v, CSTL s -> CSTL (set_strstart s v). Proof. cstl. Qed.
Lemma CSTL_lookahead : forall s v, CSTL s -> CSTL (set_lookahead s v). Proof. cstl. Qed.
Lemma CSTL_block_start : forall s v, CSTL s -> CSTL (set_block_start s v). Proof. cstl. Qed.
Lemma CSTL_ins_h : forall s v, CSTL s -> CSTL (set_ins_h s v). Proof. cstl. Qed.
Lemma CSTL_insert : forall s v, CSTL s -> CSTL (set_insert s v). Proof. cstl. Qed.
Lemma CSTL_high_water : forall s v, CSTL s -> CSTL (set_high_water s v). Proof. cstl. Qed.

Lemma CSTL_set_head : forall s h', CSTL s -> arr_len h' = hs -> CSTL (set_head s h').
Proof. intros s h' HK Hl. unfold CSTL in *. dsred. rewrite Hl. tauto. Qed.
Lemma CSTL_set_prev : forall s pv', CSTL s -> arr_len pv' = ws -> CSTL (set_prev s pv').
Proof. intros s pv' HK Hl. unfold CSTL in *. dsred. rewrite Hl. tauto. Qed.

End Walk.
End RefFillWin1.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFillWin4.RefFillWin1.

Module RefFillWin2.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemFill.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefAdler_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFillWin4.RefFillWin1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable S : Z.
Variable sp : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.

Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation CSTL := (RefFillWin1.CSTL ds).
Local Notation LF := (RefFillWin1.LF S sp p ds).
Local Notation moreof := (RefFillWin1.moreof ds).
Local Notation CSTL_match_start := (RefFillWin1.CSTL_match_start ds).
Local Notation CSTL_strstart := (RefFillWin1.CSTL_strstart ds).
Local Notation CSTL_lookahead := (RefFillWin1.CSTL_lookahead ds).
Local Notation CSTL_block_start := (RefFillWin1.CSTL_block_start ds).
Local Notation CSTL_ins_h := (RefFillWin1.CSTL_ins_h ds).
Local Notation CSTL_insert := (RefFillWin1.CSTL_insert ds).
Local Notation CSTL_high_water := (RefFillWin1.CSTL_high_water ds).
Local Notation CSTL_set_window := (RefFillWin1.CSTL_set_window ds).
Local Notation CSTL_set_head := (RefFillWin1.CSTL_set_head ds).
Local Notation CSTL_set_prev := (RefFillWin1.CSTL_set_prev ds).
Local Ltac open_lregs H :=
  let H' := fresh "HL'" in pose proof H as H';
  destruct H' as (P20 & P2 & P8 & P9 & P18 & P19 & P21 & P22).
Local Ltac open_cstl HK :=
  pose proof HK as (Kwl & Kpl & Khl & Kin & Kwr & Kws & Khs);
  pose proof (f_equal (@arr_len Z) Kin) as KIL; cbn beta in KIL.
Local Ltac in_LF := unfold RefFillWin1.LF; repeat first [ apply sub_franges_here; cbn; lia | apply sub_franges_later ].
Definition ck_ra (wrap : Z) : Z := if wrap =? 1 then 0x13614 else 0x1362c.

End Walk.
End RefFillWin2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFillWin4.RefFillWin2.

Module RefFillWin3.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemFill.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefAdler_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFillWin4.RefFillWin1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFillWin4.RefFillWin2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable S : Z.
Variable sp : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.

Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation CSTL := (RefFillWin1.CSTL ds).
Local Notation LF := (RefFillWin1.LF S sp p ds).
Local Notation moreof := (RefFillWin1.moreof ds).
Local Notation CSTL_match_start := (RefFillWin1.CSTL_match_start ds).
Local Notation CSTL_strstart := (RefFillWin1.CSTL_strstart ds).
Local Notation CSTL_lookahead := (RefFillWin1.CSTL_lookahead ds).
Local Notation CSTL_block_start := (RefFillWin1.CSTL_block_start ds).
Local Notation CSTL_ins_h := (RefFillWin1.CSTL_ins_h ds).
Local Notation CSTL_insert := (RefFillWin1.CSTL_insert ds).
Local Notation CSTL_high_water := (RefFillWin1.CSTL_high_water ds).
Local Notation CSTL_set_window := (RefFillWin1.CSTL_set_window ds).
Local Notation CSTL_set_head := (RefFillWin1.CSTL_set_head ds).
Local Notation CSTL_set_prev := (RefFillWin1.CSTL_set_prev ds).
Local Ltac open_lregs H :=
  let H' := fresh "HL'" in pose proof H as H';
  destruct H' as (P20 & P2 & P8 & P9 & P18 & P19 & P21 & P22).
Local Ltac open_cstl HK :=
  pose proof HK as (Kwl & Kpl & Khl & Kin & Kwr & Kws & Khs);
  pose proof (f_equal (@arr_len Z) Kin) as KIL; cbn beta in KIL.
Local Ltac in_LF := unfold RefFillWin1.LF; repeat first [ apply sub_franges_here; cbn; lia | apply sub_franges_later ].


Definition ILINV (s : deflate_state) (str : Z) : Prop :=
  0 <= ds_hash_shift s < 32 /\ ds_hash_mask s = hs - 1 /\ ds_w_mask s = ws - 1
  /\ 0 <= str /\ ds_insert s = ds_strstart s - str /\ 0 <= ds_insert s
  /\ 0 <= ds_ins_h s < 2 ^ 32 /\ 0 <= ds_lookahead s
  /\ ds_strstart s + ds_lookahead s <= 2 * ws
  /\ (forall i, 0 <= i < 2 * ws -> 0 <= arr_get (ds_window s) i < 256)
  /\ (forall i, 0 <= i < ws -> 0 <= arr_get (ds_prev s) i < 65536)
  /\ (forall i, 0 <= i < hs -> 0 <= arr_get (ds_head s) i < 65536).

Definition il_next (s : deflate_state) (str : Z) : deflate_state :=
  let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + 2)) in
  let s1 := set_ins_h s h in
  let s2 := set_prev s1 (arr_set (ds_prev s1) (Z.land str (ds_w_mask s1)) (arr_get (ds_head s1) h)) in
  let s3 := set_head s2 (arr_set (ds_head s2) h (wrap16 str)) in
  set_insert s3 (ds_insert s3 - 1).

End Walk.
End RefFillWin3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFillWin4.RefFillWin3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable S : Z.
Variable sp : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.

Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation CSTL := (RefFillWin1.CSTL ds).
Local Notation LF := (RefFillWin1.LF S sp p ds).
Local Notation moreof := (RefFillWin1.moreof ds).
Local Notation CSTL_match_start := (RefFillWin1.CSTL_match_start ds).
Local Notation CSTL_strstart := (RefFillWin1.CSTL_strstart ds).
Local Notation CSTL_lookahead := (RefFillWin1.CSTL_lookahead ds).
Local Notation CSTL_block_start := (RefFillWin1.CSTL_block_start ds).
Local Notation CSTL_ins_h := (RefFillWin1.CSTL_ins_h ds).
Local Notation CSTL_insert := (RefFillWin1.CSTL_insert ds).
Local Notation CSTL_high_water := (RefFillWin1.CSTL_high_water ds).
Local Notation CSTL_set_window := (RefFillWin1.CSTL_set_window ds).
Local Notation CSTL_set_head := (RefFillWin1.CSTL_set_head ds).
Local Notation CSTL_set_prev := (RefFillWin1.CSTL_set_prev ds).
Local Notation ILINV := (RefFillWin3.ILINV ds).
Local Ltac open_lregs H :=
  let H' := fresh "HL'" in pose proof H as H';
  destruct H' as (P20 & P2 & P8 & P9 & P18 & P19 & P21 & P22).
Local Ltac open_cstl HK :=
  pose proof HK as (Kwl & Kpl & Khl & Kin & Kwr & Kws & Khs);
  pose proof (f_equal (@arr_len Z) Kin) as KIL; cbn beta in KIL.
Local Ltac in_LF := unfold RefFillWin1.LF; repeat first [ apply sub_franges_here; cbn; lia | apply sub_franges_later ].


Lemma fill_window_high_wf : forall s, fw_wf ws hs s -> fw_wf ws hs (fill_window_high s).
Proof.
  intros s HW. pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_sl _ _ _ HW) as Vsl. pose proof (wf_look _ _ _ HW) as Vlook.
  pose proof (wf_wsz _ _ _ HW) as Vwsz. pose proof (wf_ins _ _ _ HW) as Vins. pose proof (wf_hw _ _ _ HW) as Vhw.
  unfold fill_window_high, WIN_INIT, MAX_MATCH. rewrite Vwsz. pose proof HW as HW'.
  destruct (Z.ltb_spec (ds_high_water s) (2 * ws)); [|exact HW]. cbv zeta.
  destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s)).
  - destruct HW; constructor; dsred; try assumption.
    + rewrite arr_len_fill. assumption.
    + destruct (Z.ltb_spec 258 (2 * ws - (ds_strstart s + ds_lookahead s))); lia.
    + intros i Hi. rewrite arr_get_fill. destruct (_ && _); [lia | match goal with Hb : forall j, _ -> 0 <= arr_get (ds_window s) j < 256 |- _ => apply Hb; exact Hi end].
  - destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s + 258)); [|exact HW].
    destruct HW; constructor; dsred; try assumption.
    + rewrite arr_len_fill. assumption.
    + destruct (Z.ltb_spec (2 * ws - ds_high_water s) (ds_strstart s + ds_lookahead s + 258 - ds_high_water s)); lia.
    + intros i Hi. rewrite arr_get_fill. destruct (_ && _); [lia | match goal with Hb : forall j, _ -> 0 <= arr_get (ds_window s) j < 256 |- _ => apply Hb; exact Hi end].
Qed.

End Walk.
