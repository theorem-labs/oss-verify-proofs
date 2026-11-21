(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Zh_kit Z_infl_iface Z_itab_kit Z_itab_defs Z_itab_pure Z_itab_ldefs Z_itab_trip Z_itab_exit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_itab_lx.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees ItableModel ItableModel2 RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].


Lemma itab_loop : forall k X root max st q ms,
  ITL X root max PC_IT_TRIP q (t_count st) (t_work st) (t_tbl st) ms -> TREGS X st q -> LINV X root st ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> 1 <= root <= 15 -> 1 <= max <= 15 ->
  it_loop_ok k (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) 288 320 1444 st = true ->
  it_lx k (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) st ->
  tx_call X = it_fin (tx_table X) root (tx_bits X) (it_loop_n (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) (Z.of_nat k) st) ->
  evt psegs (itab_post X) ms.
Proof.
  induction k as [|k IH]; intros X root max st q ms HL HR HI XO IST0 Rroot Rmax OK LX CALL; [discriminate OK|].
  set (x := itm_ctx _ _ _ _ _ _) in *.
  rewrite it_loop_ok_S in OK. apply andb_prop in OK as [TOK OK].
  rewrite it_lx_S in LX. destruct LX as [[LX0 LC0] LX].
  rewrite it_loop_n_step in CALL by lia. replace (Z.of_nat (S k) - 1) with (Z.of_nat k) in CALL by lia.
  eapply evt_cut.
  { eapply itab_trip; [exact HL| exact HR| exact HI| exact XO| exact IST0| exact Rroot| exact Rmax| exact TOK| | exact LX0| exact LC0].
    intros st' ES. fold x in ES. rewrite ES in OK. destruct k as [|k']; [discriminate OK|]. rewrite it_loop_ok_S in OK. apply andb_prop in OK as [TOK' _]. exact TOK'. }
  cbv beta. intros ms1 TP. fold x in TP.
  pose proof (trip_ok_basic x _ _ _ st TOK) as (Bsym & Blen & Bdrop & Bcurr & Bhuff & Bnext & Bused & Bmin).
  pose proof (trip_ok_fill x _ _ _ st TOK) as Bfill. rewrite !Z.shiftl_1_l in Bfill.
  destruct (it_step x st) as [st'|st'|st'].
  -
    destruct TP as (q' & HL' & HR' & HI'). eapply IH; [exact HL'| exact HR'| exact HI'| exact XO| exact IST0| exact Rroot| exact Rmax| exact OK| exact LX| exact CALL].
  -
    destruct TP as (q' & HL' & HR' & HI' & Rh & Rb & Ru & Rn). destruct q' as [x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31].
    destruct HR' as (E8 & E9 & E24 & E30). cbn [l8 l9 l24 l30] in E8, E9, E24, E30.
    destruct HI' as (_ & _ & _ & Rtab & _ & _ & TYT & LT & _ & LW).
    cbn [it_fin] in CALL.
    eapply itab_done; [exact HL'| exact E8| exact E9| exact E24| exact E30| exact XO| exact IST0| exact Rroot| lia| lia| lia| lia| lia| | exact LW| exact LT| exact TYT| exact CALL].
    intros NE. revert OK. replace (t_huff st' =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [negb]. intros OK.
    apply andb_prop in OK as [_ OK]. apply Z.ltb_lt in OK. exact OK.
  -
    destruct TP as (q' & HL' & E16 & HI'). destruct HI' as (_ & _ & _ & _ & _ & _ & _ & LT & _ & LW).
    cbn [it_fin] in CALL.
    eapply itab_fail_exit; [exact HL'| exact E16| exact XO| exact IST0| exact LW| exact LT| exact CALL].
Qed.
