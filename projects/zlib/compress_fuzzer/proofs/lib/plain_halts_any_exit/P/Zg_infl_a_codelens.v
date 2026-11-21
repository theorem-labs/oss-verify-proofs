(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_iface Z_infl_c_defs Z_infl_c_pure Z_infl_c_tab Z_infl_a_dist1 Z_infl_a_dist Zg_infl_t_iface Zg_infl_c_kit Zg_infl_a_lenlens1 Zg_infl_a_lenlens Zg_infl_a_codelens1 Zg_infl_a_codelens2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate Inftrees ItableModel InffastMem RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_LENLENS1 RefInflateA_CODELENS1 RefInflateA_CODELENS11 RefInflateSafeA5 RefInflateSafeOK RefInflateSafeOK2 RefInflateSafeOK3 RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.

Definition PC_CL_C1 : Z := 0x1dbf0.
Definition PC_CL_RET1 : Z := 0x1dc20.
Definition PC_CL_C2 : Z := 0x1de30.
Definition PC_CL_RET2 : Z := 0x1de64.

Local Ltac close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; unfold iframe_cells; inorm; close_cells FRM | exact STK
  | first [exact ZS | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS]
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma cl_x256 : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_CL_X q ms -> sc12 q = wz (is_nlen s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) -> ix_ok X -> PATG X (mkW s c r) ->
  arr_len (is_lens s) = 320 -> ty16 (is_lens s) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
    if arr_get (is_lens s) 256 =? 0
    then exists x8, ILOOP X (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_code_missing_end_of_block) r) PC_DISPATCH x8 (wz BAD) ms'
    else exists q', ILOOPg X (mkW s c r) PC_CL_C1 q' ms' /\ sc12 q' = wz (is_nlen s) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E12 E26 XO HP LL TY RPUT.
  iarm_openg HL. subst x12 x26.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_X.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  pose proof (TY 256) as R256.
  pose proof Gl as Gl'. unfold ilens, u16arr in Gl'. ld16 Gl' (is_lens s) 320 (il_As (ix_L X) + 168) 256 ltac:(lia). clear Gl'.
  zs. br_cases K.
  - replace (arr_get (is_lens s) 256 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    do 3 zs. do 3 zs. do 3 zs. itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  - replace (arr_get (is_lens s) 256 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. |]| cbn [sc12 sc26]; split; reflexivity].
    close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma cl_after2 : forall X s4 c r k ms ret,
  ILOOPk X (mkW s4 c r) PC_CL_RET2 k ms -> k10 k = wz (ret mod 2 ^ 64) -> k27 k = wz 6 -> (ret = 0 \/ ret = 1 \/ ret = -1) -> ix_ok X ->
  0 <= ix_flush X <= 4 ->
  (is_window_blk s4 <> None -> ix_hasw X = true) -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 ->
  arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
    if negb (ret =? 0)
    then exists x8, ILOOP X (mkW (iset_mode s4 BAD) (icset_msg c MSG_invalid_distances_set) (irset_ret r ret)) PC_DISPATCH x8 (wz BAD) ms'
    else exists x8 x12, ILOOP X (mkW (iset_mode s4 LEN_) c (irset_ret r ret)) PC_LEN_ x8 x12 ms') ms.
Proof.
  intros X s4 c r [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms ret HL E10 E27 RRET XO RF Pwin Pin Pin1 Pout RPUT.
  iarm_openk HL. subst x10 x27.
  ix_open XO. unfold PC_CL_RET2.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  assert (RM : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  do 2 zs. br_cases K.
  -
    assert (R0 : ret = 0) by (destruct RRET as [R|[R|R]]; rewrite R in K; [exact R| |]; exfalso; revert K; vm_compute; discriminate).
    clear RRET K RM. subst ret. cbn [Z.eqb negb].
    do 9 zs. br_false. itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
    close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  -
    assert (R1 : (ret =? 0) = false) by (apply Z.eqb_neq; intros R; rewrite R in K; apply K; reflexivity). rewrite R1. cbn [negb].
    clear RRET K.
    do 2 zs. do 5 zs. do 5 zs. do 2 zs. itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Section CLcalls.
Variable flush : Z.
Hypothesis ITABLE : inflate_table_stmt.

Lemma cl_call2 : forall X s3 c r k ms ret tbl nxt db wk,
  ILOOPk X (mkW s3 c r) PC_CL_C2 k ms -> ix_ok X -> 0 <= ix_flush X <= 4 ->
  (is_window_blk s3 <> None -> ix_hasw X = true) -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 ->
  arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  inflate_table DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = (ret, tbl, nxt, db, wk) ->
  it_safe DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = true ->
  ATY s3 -> (forall i, 0 <= i < is_ndist s3 -> arr_get (is_lens s3) (is_nlen s3 + i) <= 15) ->
  257 <= is_nlen s3 <= 286 -> 1 <= is_ndist s3 <= 30 -> 0 <= is_next s3 <= 1444 -> iarrs s3 ->
  evt psegs (fun ms' =>
    if negb (ret =? 0)
    then exists x8, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl nxt db wk) BAD) (icset_msg c MSG_invalid_distances_set) (irset_ret r ret)) PC_DISPATCH x8 (wz BAD) ms'
    else exists x8 x12, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl nxt db wk) LEN_) c (irset_ret r ret)) PC_LEN_ x8 x12 ms') ms.
Proof.
  intros X s3 c r [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms ret tbl nxt db wk HL XO RF Pwin Pin Pin1 Pout RPUT EIT SAFE HA HL15 Rnl Rnd Rnx HARR.
  iarm_openk HL.
  ix_open XO. unfold PC_CL_C2.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  rd_sub GA 148%nat 0%nat 4%nat. do 13 zs. itr_groups MUf WMf. clear MUf WMf.
  set (spre := iset_distbits (iset_distcode s3 (CDyn (is_next s3))) 6).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
  assert (ST' : IST m1 (ix_L X) spre);
  [ subst spre; constructor; inorm;
    [ unfold isA, isA_cells; inorm; unfold cp_addr at 2; close_cells GA | exact GT | exact Gl | exact Gw | exact Gc | exact Gwin
    | unfold iarrs in *; inorm; exact HARR | exact LAY ]
  | clear GA GT Gl Gw Gc Gwin ] end.
  pose proof (inflate_table_ret _ _ _ _ _ _ _ _ _ _ _ _ _ EIT) as RRET.
  eapply evt_cut.
  { eapply (ITABLE (ix_L X) spre DISTS true (is_nlen s3) (is_ndist s3) (ix_lo X));
      [ exact ST' | eassumption | rewrite unsigned_lit by lia; exact STK | rewrite unsigned_lit by lia; unfold Z_ITABLE_STACK; lia | lia
      | intros NE; subst spre; cbn in NE; pose proof (xo_win _ XO (Pwin NE)); lia
      | lia | lia | lia | subst spre; cbn; lia | subst spre; cbn; lia
      | subst spre; cbn [it_bits_get is_lens is_codes is_next is_work is_distbits iset_distcode iset_distbits]; exact SAFE
      | exact HA
      | subst spre; cbn [is_lens is_nlen iset_distcode iset_distbits]; exact HL15
      | exact I
      | reflexivity | f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STKc & EA0 & STc).
  rewrite unsigned_lit in MUc, STKc by lia.
  assert (ER : it_result DISTS true (is_nlen s3) (is_ndist s3) spre = (ret, cl_tab2 s3 tbl nxt db wk)).
  { unfold it_result. subst spre. cbn [it_bits_get it_bits_set is_lens is_codes is_next is_work is_distbits iset_distcode iset_distbits].
    rewrite EIT.
    unfold cl_tab2, it_bits_set. cbv [iset_work iset_distbits iset_next iset_distcode iset_codes
      is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk
      is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next
      is_lens is_work is_codes is_sane is_back is_was is_self_blk]. reflexivity. }
  rewrite ER in EA0, STc. cbn [fst snd] in EA0, STc. subst a0'. clear ER ST' spre.
  lazymatch type of WMc with wmono _ ?ma _ => itr_groups MUc WMc; transport_after_call psegs ma m' MUc WMc end. clear MUc WMc MI HARR LAY.
  replace (ret_pc (wz 122468)) with (wz 122468) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply (cl_after2 X (cl_tab2 s3 tbl nxt db wk) c r _ _ ret); [ | | | exact RRET | exact XO | exact RF | exact Pwin | exact Pin | exact Pin1 | exact Pout | exact RPUT].
  { eapply ILOOPk_intro; ired; [ireg .. |].
    apply IMEM_intro; [ exists jf; exact FRM | exact STKc | exact ZS | exact STc | exact IN | exact OUT | exact MIc | exact MU | exact WM ]. }
  all: reflexivity.
Qed.

Lemma cl_after1 : forall X s3 c r k ms ret ret2 tbl2 nxt2 db wk2,
  ILOOPk X (mkW s3 c r) PC_CL_RET1 k ms -> k10 k = wz (ret mod 2 ^ 64) -> (ret = 0 \/ ret = 1 \/ ret = -1) -> ix_ok X -> 0 <= ix_flush X <= 4 ->
  (is_window_blk s3 <> None -> ix_hasw X = true) -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 ->
  arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  (ret = 0 -> inflate_table DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = (ret2, tbl2, nxt2, db, wk2)) ->
  (ret = 0 -> it_safe DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = true) ->
  (ret = 0 -> ATY s3) -> (ret = 0 -> forall i, 0 <= i < is_ndist s3 -> arr_get (is_lens s3) (is_nlen s3 + i) <= 15) ->
  257 <= is_nlen s3 <= 286 -> 1 <= is_ndist s3 <= 30 -> (ret = 0 -> 0 <= is_next s3 <= 1444) ->
  evt psegs (fun ms' =>
    if negb (ret =? 0)
    then exists x8, ILOOP X (mkW (iset_mode s3 BAD) (icset_msg c MSG_invalid_literal_lengths_set) (irset_ret r ret)) PC_DISPATCH x8 (wz BAD) ms'
    else if negb (ret2 =? 0)
    then exists x8, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl2 nxt2 db wk2) BAD) (icset_msg c MSG_invalid_distances_set) (irset_ret r ret2)) PC_DISPATCH x8 (wz BAD) ms'
    else exists x8 x12, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl2 nxt2 db wk2) LEN_) c (irset_ret r ret2)) PC_LEN_ x8 x12 ms') ms.
Proof.
  intros X s3 c r [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms ret ret2 tbl2 nxt2 db wk2 HL E10 RRET XO RF Pwin Pin Pin1 Pout RPUT
         EIT2 SAFE2 HA3 HL15 Rnl Rnd Rnx.
  pose proof HL as HL0. iarm_openk HL. subst x10.
  ix_open XO. unfold PC_CL_RET1.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  assert (RM : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  zs. br_cases K.
  -
    assert (R0 : ret = 0) by (destruct RRET as [R|[R|R]]; rewrite R in K; [exact R| |]; exfalso; revert K; vm_compute; discriminate).
    clear RRET K RM. subst ret. cbn [Z.eqb negb].
    eapply (cl_call2 X s3 c r _ _ ret2 tbl2 nxt2 db wk2); [| exact XO | exact RF | exact Pwin | exact Pin | exact Pin1 | exact Pout | exact RPUT
      | exact (EIT2 eq_refl) | exact (SAFE2 eq_refl) | exact (HA3 eq_refl) | exact (HL15 eq_refl) | exact Rnl | exact Rnd | exact (Rnx eq_refl) | exact ARRS ].
    eapply ILOOPk_intro; ired; [ireg .. |].
    close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  -
    assert (R1 : (ret =? 0) = false) by (apply Z.eqb_neq; intros R; rewrite R in K; apply K; reflexivity). rewrite R1. cbn [negb].
    clear RRET K.
    do 4 zs. do 5 zs. do 5 zs. do 2 zs. itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma cl_call1 : forall X s c r q ms ret tbl nxt lb wk ret2 tbl2 nxt2 db wk2,
  let s3 := cl_tab1 s tbl nxt lb wk in
  ILOOPg X (mkW s c r) PC_CL_C1 q ms -> sc12 q = wz (is_nlen s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> 0 <= ix_flush X <= 4 -> PATG X (mkW s c r) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  inflate_table LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s) = (ret, tbl, nxt, lb, wk) ->
  it_safe LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s) = true ->
  ATY s -> (forall i, 0 <= i < is_nlen s -> arr_get (is_lens s) (0 + i) <= 15) ->
  257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 ->
  (ret = 0 -> inflate_table DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = (ret2, tbl2, nxt2, db, wk2)) ->
  (ret = 0 -> it_safe DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = true) ->
  (ret = 0 -> ATY s3) -> (ret = 0 -> forall i, 0 <= i < is_ndist s3 -> arr_get (is_lens s3) (is_nlen s3 + i) <= 15) ->
  (ret = 0 -> 0 <= is_next s3 <= 1444) ->
  evt psegs (fun ms' =>
    if negb (ret =? 0)
    then exists x8, ILOOP X (mkW (iset_mode s3 BAD) (icset_msg c MSG_invalid_literal_lengths_set) (irset_ret r ret)) PC_DISPATCH x8 (wz BAD) ms'
    else if negb (ret2 =? 0)
    then exists x8, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl2 nxt2 db wk2) BAD) (icset_msg c MSG_invalid_distances_set) (irset_ret r ret2)) PC_DISPATCH x8 (wz BAD) ms'
    else exists x8 x12, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl2 nxt2 db wk2) LEN_) c (irset_ret r ret2)) PC_LEN_ x8 x12 ms') ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms ret tbl nxt lb wk ret2 tbl2 nxt2 db wk2 s3 HL E12 E26 XO RF HP RPUT
         EIT SAFE HA HL15 Rnl Rnd EIT2 SAFE2 HA3 HL15' Rnx.
  iarm_openg HL. subst x12 x26.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_C1.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  do 12 zs. itr_groups MUf WMf. clear MUf WMf.
  set (spre := iset_lencode (iset_next (iset_lenbits s 9) 0) (CDyn 0)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
  assert (ST' : IST m1 (ix_L X) spre);
  [ subst spre; constructor; inorm;
    [ unfold isA, isA_cells; inorm; unfold cp_addr at 1; close_cells GA | exact GT | exact Gl | exact Gw | exact Gc | exact Gwin
    | unfold iarrs in *; inorm; exact ARRS | exact LAY ]
  | clear GA GT Gl Gw Gc Gwin ] end.
  pose proof (inflate_table_ret _ _ _ _ _ _ _ _ _ _ _ _ _ EIT) as RRET.
  eapply evt_cut.
  { eapply (ITABLE (ix_L X) spre LENS false 0 (is_nlen s) (ix_lo X));
      [ exact ST' | eassumption | rewrite unsigned_lit by lia; exact STK | rewrite unsigned_lit by lia; unfold Z_ITABLE_STACK; lia | lia
      | intros NE; subst spre; cbn in NE; pose proof (xo_win _ XO (Pwin NE)); lia
      | lia | lia | lia | subst spre; cbn; lia | subst spre; cbn; lia
      | subst spre; cbn [it_bits_get is_lens is_codes is_next is_work is_lenbits iset_lencode iset_next iset_lenbits]; exact SAFE
      | exact HA
      | subst spre; cbn [is_lens iset_lencode iset_next iset_lenbits]; exact HL15
      | cbn [it_codes_ok]; lia
      | reflexivity | f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STKc & EA0 & STc).
  rewrite unsigned_lit in MUc, STKc by lia.
  assert (ER : it_result LENS false 0 (is_nlen s) spre = (ret, s3)).
  { unfold it_result. subst spre s3. cbn [it_bits_get it_bits_set is_lens is_codes is_next is_work is_lenbits iset_lencode iset_next iset_lenbits].
    rewrite EIT.
    unfold cl_tab1, it_bits_set. cbv [iset_work iset_lenbits iset_next iset_lencode iset_codes
      is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk
      is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next
      is_lens is_work is_codes is_sane is_back is_was is_self_blk]. reflexivity. }
  rewrite ER in EA0, STc. cbn [fst snd] in EA0, STc. subst a0'. clear ER ST' spre.
  lazymatch type of WMc with wmono _ ?ma _ => itr_groups MUc WMc; transport_after_call psegs ma m' MUc WMc end. clear MUc WMc MI ARRS LAY.
  replace (ret_pc (wz 121888)) with (wz 121888) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (Pwin3 : is_window_blk s3 <> None -> ix_hasw X = true) by exact Pwin.
  eapply (cl_after1 X s3 c r _ _ ret ret2 tbl2 nxt2 db wk2);
    [ | | exact RRET | exact XO | exact RF | exact Pwin3 | exact Pin | exact Pin1 | exact Pout | exact RPUT
    | exact EIT2 | exact SAFE2 | exact HA3 | exact HL15' | exact Rnl | exact Rnd | exact Rnx ].
  { eapply ILOOPk_intro; ired; [ireg .. |].
    apply IMEM_intro; [ exists jf; exact FRM | exact STKc | exact ZS | exact STc | exact IN | exact OUT | exact MIc | exact MU | exact WM ]. }
  reflexivity.
Qed.
End CLcalls.

Lemma irset_ret_twice : forall r a b, irset_ret (irset_ret r a) b = irset_ret r b.
Proof. intros [n h p l ho b' i o rt] a b. reflexivity. Qed.

Section CLcore.
Variable flush : Z.
Hypothesis ITABLE : inflate_table_stmt.
Hypothesis RF : 0 <= flush <= 4.
Hypothesis LEN__CORE : len__core_stmt.

Lemma codelens_core : codelens_core_stmt flush.
Proof.
  intros X [s c r] q ms EF HL E13 E26 XO HW HA HP HM. cbn [w_s w_c w_r] in *.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (RFX : 0 <= ix_flush X <= 4) by (rewrite EF; exact RF).
  rewrite arm_CODELENS_eq.
  pose proof (codelens_facts s c r HW HA HM) as (HCL & Hlt & F).
  pose proof (WINV_codelens_okb s c r HW HA HM) as OKB. unfold codelens_okb in OKB. cbn [w_s w_c w_r] in OKB.
  apply andb_prop in OKB. destruct OKB as [_ OKB].
  pose proof (codelens_next_WINV flush s c r HW HA HM) as NXW. unfold codelens_next in NXW.
  eapply evt_cut; [exact (cl_while X s c r q ms HL E13 E26 XO HW HA HP HM)|]. intros ms1 H1.
  destruct (codelens_while 321 (mkW s c r)) as [[] [s1 c1 r1] | w' | rc w']; cbn [CLPOST w_s w_r] in H1.
  2:{ apply evt_done. cbn [IPOST wof]. exact H1. }
  2:{ destruct H1. }
  destruct (Z.eqb_spec (is_mode s1) BAD) as [EB|NB].
  { destruct H1 as [H1 HP1]. apply evt_done. split; [cbn [IPOST w_s]; rewrite EB; exact H1| exact HP1]. }
  destruct F as [EB|(-> & HCL1 & Hh1 & Hb1 & HA1)]; [contradiction|].
  destruct H1 as [(q1 & HL1 & E12' & E13' & E26') HP1].
  pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & Hbx1 & Hnl1 & Hnd1 & Hh1' & HLs1 & HT1 & HWF1 & HWB1).
  assert (LL1 : arr_len (is_lens s1) = 320) by (destruct HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  pose proof HR1 as (Rn1 & Rh1 & Rnh1 & Rp1 & Rl1 & Rpl1 & _).
  pose proof HP1 as (_ & _ & _ & Pfl1 & _ & _ & _ & _ & _ & _ & Pisr1 & _). cbn [w_s w_c w_r] in Pfl1, Pisr1.
  assert (Pf1 : is_flags s1 = 0) by (destruct Pfl1 as [Pf|(Pf & [E'|E'] & _)]; [exact Pf| |]; rewrite E1 in E'; discriminate E').
  assert (RPUT1 : 0 <= ir_put r1 <= Z.of_nat (length (ix_rest0 X))) by (rewrite <- Pout; lia).
  pose proof HA1 as (TY1 & TYw1 & TYc1).
  unfold cl_post_ok in OKB. unfold cl_post.
  eapply evt_cut; [exact (cl_x256 X s1 c r1 q1 ms1 HL1 E12' E26' XO HP1 LL1 TY1 RPUT1)|]. intros ms2 H2.
  revert OKB NXW H2. destruct (Z.eqb_spec (arr_get (is_lens s1) 256) 0) as [Z0|NZ]; intros OKB NXW H2.
  {
    apply evt_done. split; [cbn [IPOST w_s]; exact H2|]. cbn [wof].
    eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| try reflexivity ..]. exact Pisr1. }
  destruct H2 as (q2 & HL2 & E12'' & E26'').
  revert OKB NXW. destruct (inflate_table LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)) as [[[[ret tbl] nxt] lb] wk] eqn:EIT1.
  cbv zeta. intros OKB NXW.
  apply andb_prop in OKB. destruct OKB as [OKB REST]. apply andb_prop in OKB. destruct OKB as [L15 SAFE1].
  apply andb_prop in REST. destruct REST as [LPO1 REST].
  pose proof (lens15b_sound _ _ _ L15 ltac:(lia) ltac:(lia)) as HL15. rewrite Z.sub_0_r in HL15.
  destruct (ll_post_ok_sound _ _ _ _ LPO1) as (Ltbl & Lwk & Rnxt & Rlb & Ttbl & Twk).
  pose proof (inflate_table_typed LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1) TYc1 TYw1) as TT. rewrite EIT1 in TT. destruct TT as [TT1 TT2].
  set (s3 := cl_tab1 s1 tbl nxt lb wk) in *.
  assert (HA3 : ATY s3) by (split; [exact TY1| split; [exact TT2| exact TT1]]).
  revert REST NXW. destruct (inflate_table DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3)) as [[[[ret2 tbl2] nxt2] db] wk2] eqn:EIT2.
  intros REST NXW.
  assert (C2 : ret = 0 -> (forall i, 0 <= i < is_ndist s3 -> arr_get (is_lens s3) (is_nlen s3 + i) <= 15)
                         /\ it_safe DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = true).
  { intros R0. rewrite R0 in REST. cbn [Z.eqb] in REST. apply andb_prop in REST. destruct REST as [REST _]. apply andb_prop in REST. destruct REST as [L15' SAFE2].
    split; [|exact SAFE2]. pose proof (lens15b_sound _ _ _ L15' ltac:(cbn; lia) ltac:(cbn; lia)) as H. intros i Hi. apply H. lia. }
  eapply evt_cut.
  { exact (cl_call1 ITABLE X s1 c r1 q2 ms2 ret tbl nxt lb wk ret2 tbl2 nxt2 db wk2 HL2 E12'' E26'' XO RFX HP1 RPUT1 EIT1 SAFE1 HA1 HL15 Hnl1 Hnd1
             (fun _ => EIT2) (fun R0 => proj2 (C2 R0)) (fun _ => HA3) (fun R0 => proj1 (C2 R0)) (fun _ => Rnxt)). }
  intros ms3 H3. cbv zeta in H3. fold s3 in H3.
  revert H3 NXW. destruct (Z.eqb_spec ret 0) as [R0|R1]; cbn [negb]; intros H3 NXW.
  2:{
      apply evt_done. split; [cbn [IPOST w_s]; exact H3|]. cbn [wof]. subst s3. unfold cl_tab1.
      eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| try reflexivity ..]. exact Pisr1. }
  rewrite irset_ret_twice. rewrite irset_ret_twice in NXW.
  revert H3 NXW. destruct (Z.eqb_spec ret2 0) as [R0'|R1']; cbn [negb]; intros H3 NXW.
  2:{
      apply evt_done. split; [cbn [IPOST w_s]; exact H3|]. cbn [wof]. subst s3. unfold cl_tab1, cl_tab2.
      eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| try reflexivity ..]. exact Pisr1. }
  replace (flush =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia).
  replace (flush =? Z_TREES) with false in NXW by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia).
  destruct H3 as (x8' & x12' & HL3).
  destruct (NXW _ eq_refl) as [HW2 HM2].
  refine (LEN__CORE X _ x8' x12' ms3 HL3 XO HW2 _ HM2).
  subst s3. unfold cl_tab1, cl_tab2.
  eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold LEN_, FLAGS, HCRC; lia| try reflexivity ..]. exact Pisr1.
Qed.

Lemma arm_CODELENS_of : arm_stmtg flush CODELENS PC_CODELENS (arm_CODELENS ivar_ref flush).
Proof.
  intros X [s c r] x12 ms EF HL XO HW HA HP HM.
  assert (H0 : evt psegs (fun ms' => exists q, ILOOPg X (mkW s c r) PC_CODELENS_E q ms' /\ sc13 q = wz (is_have s) /\ sc26 q = wz (il_NI (ix_L X) + ir_next r)) ms).
  { pose proof HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in HMF, HM. rewrite HM in HMF. unfold MF in HMF. cbn in HMF.
    destruct HMF as (_ & _ & Hnl & Hnd & Hh & _).
    destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM).
    pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s w_c w_r] in *.
    unfold PC_CODELENS. do 2 zs.
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]| cbn [sc13 sc26]; split; reflexivity]. }
  eapply evt_cut; [exact H0|]. intros ms1 (q1 & H1 & E13 & E26).
  exact (codelens_core X (mkW s c r) q1 ms1 EF H1 E13 E26 XO HW HA HP HM).
Qed.
End CLcore.
