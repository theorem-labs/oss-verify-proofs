(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I3_base Fz_I3_kit Fz_I3_fxi Fz_W3_iface Fz_T_ekit Fz_M_malloc Fz_M_zalloc Fz_M_free.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock Fz_W1_defs Fz_W1_new Fz_W1_free Fz_W2_rep Fz_W2_exd Fz_W5_env.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation wz := (Z_to_bv 64) (only parsing).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


(* [comment removed for export] *)
Lemma le4_m1 : le4 (Z_to_bv 64 (-1)) = le4 (Z_to_bv 64 4294967295).
Proof.
  unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned (Z_to_bv 64 (-1))) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned (Z_to_bv 64 4294967295)) 32) by (cbn; lia). rewrite !Z_to_bv_unsigned. reflexivity.
Qed.
Lemma w1c_numw_fix : forall (m : mem) A (w1 flw rrw padw ptr : word),
  rw_cells usegs m A [C8 w1; C4 flw; C4 rrw; C4 (Z_to_bv 64 (-1)); C4 padw; C8 ptr] ->
  rw_cells usegs m A [C8 w1; C4 flw; C4 rrw; C4 (Z_to_bv 64 4294967295); C4 padw; C8 ptr].
Proof.
  intros m A w1 flw rrw padw ptr H. eapply th_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes app]; rewrite le4_m1; reflexivity| reflexivity| cbn; tauto].
Qed.

(* [comment removed for export] *)
Definition mcreate (meth : Z) : Z := if Z.eqb meth M_SECMEM then 0x183d24 else 0x183a2c.
Lemma meth_create : forall m meth, cimg m -> mem_inv usegs m -> (meth = M_MEM \/ meth = M_SECMEM) -> rw_cells usegs m (meth + 72) [C8 (wz (mcreate meth))].
Proof.
  intros m meth CIMG MI [-> | ->]; unfold M_MEM, M_SECMEM, mcreate; cbn [Z.eqb Pos.eqb].
  - cimg_cell CIMG m (0x2d3fc8 + 72) [C8 (wz 0x183a2c)] H. exact H.
  - cimg_cell CIMG m (0x2d4038 + 72) [C8 (wz 0x183d24)] H. exact H.
Qed.
Lemma mcreate_cases : forall meth, (meth = M_MEM \/ meth = M_SECMEM) -> (mcreate meth = 0x183a2c /\ msec meth = 0) \/ (mcreate meth = 0x183d24 /\ msec meth = 1).
Proof. intros meth [-> | ->]; unfold mcreate, msec, M_MEM, M_SECMEM; cbn; [left | right]; split; reflexivity. Qed.
Lemma mem_new_meth : crypto_zalloc_stmt -> forall meth, (meth = M_MEM \/ meth = M_SECMEM) -> W1_mem_new_stmt (mcreate meth) (msec meth).
Proof.
  intros CZ meth METH. destruct (mcreate_cases meth METH) as [[-> ->]|[-> ->]]; [exact (W1_mem_new_spec CZ)| exact (W1_secmem_new_spec CZ)].
Qed.

(* [comment removed for export] *)
Theorem bio_new_mem_proof : crypto_malloc_stmt -> bio_new_mem_stmt libenv.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM. pose proof (crypto_zalloc_spec CM) as CZ. unfold bio_new_mem_stmt. intros until B. intros Hf ROOM CST SLO ENV INCL -> METH.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  pose proof (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST)) as ND.
  destruct (libenv_exd_cells _ _ _ ENV) as (kd & LK & pk & INKL & _ & _ & HKD & _ & _ & _ & _ & _ & _ & _ & LK0 & LKAL & _ & _).
  assert (INK : In (pk, LK, 40) LBall) by (exact (INCL _ INKL)).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INK) as (_ & _ & _ & KCL & KIMG).
  assert (TPV : bv_unsigned tp = RATP) by (rewrite TP; apply unsigned_lit; unfold RATP; lia). unfold RATP in TPV.
  unfold BNEW_STACK, FZ_BIO_NEW, GLOBALS_TOP, ceil_window in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. th_frame 16%nat [8; 8]%nat ST.
  do 4 ths. ths. ths. ths. ths. ths. th_release FR (bv_unsigned sp). ths.
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  do 13 ths. ths.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma end.
  lazymatch goal with H : stk usegs ma lo _ |- _ => rename H into STa end. lazymatch goal with H : mem_inv usegs ma |- _ => rename H into MIa end.
  lazymatch goal with H : rw_cells usegs ma (bv_unsigned sp + -48) _ |- _ => rename H into FRa0 end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ tp lo B (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | clear - SLO LO; lia| exact SPB| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; clear - SPB; lia].
    - apply Forall_cons; [apply cwin_stack; clear - SLO LO; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SLO GLO; lia. }
  assert (FRa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| clear - SLO LO; lia|]. apply Forall_cons; [apply cseg_ok_stack; clear - SLO LO; lia| apply Forall_nil]. }
  pose proof (w_bounds 128 ltac:(lia)) as W128. destruct (wA_small 128 ltac:(unfold TIER_A_MAX; lia)) as (WA & WB & WC).
  eapply climpl_seq.
  { eapply CZ with (n := 128) (lo := lo) (B := B); [clear - Hf; lia| rewrite WA, WB, WC; clear - ROOM; unfold croom in *; lia| lia| exact CSTa| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; clear - SLO; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (pbi & BI & -> & -> & -> & RNG1 & BLK1)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia).
  rewrite WA, WB, WC in GR1.
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRa0 ltac:(clear - RSP; lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & SPB1 & ST1 & LO1 & _ & MI1 & _) & LXS1 & _ & CIMG1 & GLO1).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG1 as (BI0 & BI16 & _ & BICL & BIIMG).
  (* [comment removed for export] *)
  change (Z.to_nat 128) with 128%nat in BLK1.
  apply (th_cells_congr usegs m1 BI _ ([C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ++ [C4 z64; C4 z64; C4 z64; C4 z64; C4 z64; C4 z64; C8 z64]
                                        ++ [C8 z64; C8 z64; C4 z64; C4 z64; C8 z64; C8 z64] ++ [C8 z64; C8 z64])) in BLK1; [| reflexivity | reflexivity | cbn [cells_wf cell_wf app]; repeat split; exact I].
  apply (proj1 (rw_cells_app usegs m1 _ _ _)) in BLK1. destruct BLK1 as [HEAD BLK1].
  apply (proj1 (rw_cells_app usegs m1 _ _ _)) in BLK1. destruct BLK1 as [W1C BLK1].
  apply (proj1 (rw_cells_app usegs m1 _ _ _)) in BLK1. destruct BLK1 as [TAIL EXD].
  cbn [cells_size csize Nat.add app] in W1C, TAIL, EXD. change (Z.of_nat 40) with 40 in W1C, TAIL, EXD. change (Z.of_nat 32) with 32 in TAIL, EXD. change (Z.of_nat 40) with 40 in EXD.
  replace (BI + 40 + 32) with (BI + 72) in TAIL by lia. replace (BI + 40 + 32 + 40) with (BI + 112) in EXD by lia.
  (* [comment removed for export] *)
  assert (ENV1 : libenv m1 LBL E).
  { eapply libenv_agree; [exact ENV|]. eapply agree_on_trans.
    - eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|]. intros a Ha; cbv beta; cbn [outside].
      destruct (libenv_fp_where LBL a Ha) as [(X1 & X2 & X3)|(b & Hb & Hr)]; [clear - X1 SLO GLO; lia|].
      destruct b as [[q A] n]. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (INCL _ Hb)) as (_ & _ & _ & BCL & _). cbn [blk_addr blk_size fst snd] in Hr. clear - Hr BCL LO SLO; lia.
    - eapply agree_on_mono; [exact CFR1|]. intros a Ha.
      destruct (libenv_fp_where LBL a Ha) as [(X1 & X2 & X3)|(b & Hb & Hr)]; [right; right; split; [exact X1|]; split; [exact X2|]; split; [exact X3| cbn; intros X9; exact X9]|].
      right; left. exists b. split; [exact (INCL _ Hb)|]. split; [intros X0; exact X0| exact Hr]. }
  destruct (libenv_exd_cells _ _ _ ENV1) as (kd' & LK' & pk' & INKL' & XI & XK & HKD' & XO1 & XR1 & XO2 & XR2 & XTS & XT & XG & LK0' & LKAL' & XM & XIP).
  assert (INK1 : In (pk', LK', 40) ((pbi, BI, 128) :: LBall)) by (right; exact (INCL _ INKL')).
  assert (INBI1 : In (pbi, BI, 128) ((pbi, BI, 128) :: LBall)) by (left; reflexivity).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 INK1) as (_ & _ & _ & KCL' & KIMG').
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INBI1 INK1 ltac:(intros EQ; exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (INCL _ INKL') (eq_sym EQ)))) as APIK.
  pose proof (meth_create m1 meth CIMG1 MI1 METH) as MCR. pose proof METH as METH'. unfold M_MEM, M_SECMEM in METH.
  unfold DC_S, DC_GLOBAL_LOCK, DC_IP12 in XI, XK, XO1, XR1, XO2, XR2, XG, XIP. unfold TSD_MAIN, RATP in XTS, XT. change (3344744 + -88) with 3344656 in XTS.
  change (3333808 + 4) with 3333812 in XK. change (3333808 + 8) with 3333816 in XO1. change (3333808 + 12) with 3333820 in XR1.
  change (3333808 + 16) with 3333824 in XO2. change (3333808 + 20) with 3333828 in XR2.
  unfold mutex_cells in XM. set (Pk := 3480784 + 8 * kd') in *.
  pose proof (munch_refl [(bv_unsigned sp - 48 - 304, bv_unsigned sp); (BI, BI + 128)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  assert (BI8 : BI mod 8 = 0) by (clear - BI16; Z.div_mod_to_equations; lia).
  assert (METH8 : meth mod 8 = 0) by (clear - METH; destruct METH as [-> | ->]; reflexivity).
  cprefix. ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. clear - K1 BI0 BICL CEIL_RANGE__; lia. }
  ths. ths. ths. ubs_if. ths. ths. ths. ths.
  do 8 ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    lazymatch goal with MUh : munch _ m1 mc, WMh : wmono usegs m1 mc |- _ =>
      assert (LXSc : lx_statics mc)
        by (eapply lx_statics_agree; [exact (agree_on_of_munch _ _ _ MUh WMh)| | exact LXS1];
            intros a Ha; cbv beta; cbn [outside]; unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in Ha; clear - Ha GLO SLO RSP BIIMG BI0; lia) end end.
  pose proof T_newex_proof as X. unfold T_newex_stmt, NEWEX_STACK, DC_IP12, DC_GLOBAL_LOCK, DC_S, GLOBALS_TOP, mutex_cells in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 3480784 kd' LK' (BI + 112) (Z_to_bv 64 0) (Z_to_bv 64 0)).
  all: try first [reflexivity | eassumption | rewrite TPV; eassumption | clear - TPV HKD' BI0 BI8 BICL BIIMG KCL' KIMG' APIK LO SLO GLO RSP; lia].
  clear X. cbv beta delta [mkR].
  ths. th_if_lit.
  ths. ubs_if.
  ths. ths. ubs_if.
  ths.
  ths. if_cases K2; zify_cond K2. { exfalso. destruct (mcreate_cases meth METH') as [[EC _]|[EC _]]; rewrite EC in K2; cbv in K2; discriminate K2. }
  ths. ths.
  replace (ret_pc (Z_to_bv 64 (mcreate meth))) with (Z_to_bv 64 (mcreate meth))
    by (symmetry; apply ret_pc_even; destruct (mcreate_cases meth METH') as [[EC _]|[EC _]]; rewrite EC; first [reflexivity | lia]).
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mb end.
  lazymatch goal with H : stk usegs mb lo _ |- _ => rename H into STb end. lazymatch goal with H : mem_inv usegs mb |- _ => rename H into MIb end.
  lazymatch goal with H : munch _ m1 mb |- _ => rename H into MUb end. lazymatch goal with H : wmono usegs m1 mb |- _ => rename H into WMb end.
  lazymatch goal with H : rw_cells usegs mb (bv_unsigned sp + -48) _ |- _ => rename H into FRb0 end.
  lazymatch goal with H : rw_cells usegs mb (BI + 112) _ |- _ => rename H into EXDb end.
  lazymatch goal with H : rw_cells usegs mb LK' _ |- _ => rename H into XMb end.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (CSTb : cstate st1 ((pbi, BI, 128) :: LBall) LB ((pbi, 128) :: L) mb (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m1 mb _ _ tp lo B (bv_unsigned sp)); [exact CST1| exact MUb| exact WMb| exact MIb| | clear - SLO LO; lia| exact SPB| | rewrite unsigned_lit by lia; exact STb| exact SPB1].
    - apply Forall_cons; [apply cwin_stack; clear - SLO LO; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pbi, BI, 128)); [exact INBI1| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SLO GLO BIIMG BI0; lia. }
  assert (FRb : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st1 ((pbi, BI, 128) :: LBall) ((pbi, 128) :: L) mb).
  { eapply cframe_seg; [eapply cframe_call; [exact FRa| exact FRM1| clear - RSP; lia| intros a X; exact X| intros q _ X; exact X]| exact MUb| exact WMb| exact HP1| clear - SLO LO; lia|].
    apply Forall_cons; [apply cseg_ok_stack; clear - SLO LO; lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (pbi, BI, 128)); [exact INBI1| exact (cfresh_new _ _ _ _ _ _ (proj1 (proj2 FRa)) ND1)| cbn; lia| cbn; lia]. }
  lazymatch goal with H : rw_cells usegs mb (BI + 40) _ |- _ => rename H into W1Cb end.
  (* [comment removed for export] *)
  change ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
    with ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1)] ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in W1Cb.
  apply (proj1 (rw_cells_app usegs mb _ _ _)) in W1Cb. destruct W1Cb as [ISb W1Cb].
  apply (proj1 (t_cells_halves usegs mb (BI + 40) 0 1 ltac:(lia) ltac:(lia))) in ISb. change (0 + 2 ^ 32 * 1) with 4294967296 in ISb.
  pose proof (proj2 (rw_cells_app usegs mb (BI + 40) _ _) (conj ISb W1Cb)) as W1Cj. clear ISb W1Cb. cbn [app] in W1Cj.
  change ([C8 (Z_to_bv 64 4294967296); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
    with (bio_w1_cells (Z_to_bv 64 4294967296) 0 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) in W1Cj. rename W1Cj into W1Cb.
  lazymatch goal with H : rw_cells usegs mb BI _ |- _ => rename H into HEADb end.
  lazymatch goal with H : rw_cells usegs mb (BI + 72) _ |- _ => rename H into TAILb end.
  assert (TLb : rw_cells usegs mb (BI + 72) ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])).
  { apply (proj2 (rw_cells_app usegs mb (BI + 72) _ _)). split; [exact TAILb|]. cbn [cells_size csize Nat.add]. replace (BI + 72 + Z.of_nat 40) with (BI + 112) by lia. exact EXDb. }
  clear TAILb EXDb.
  destruct (wA_small 16 ltac:(unfold TIER_A_MAX; lia)) as (A16 & B16 & C16). destruct (wA_small 32 ltac:(unfold TIER_A_MAX; lia)) as (A32 & B32 & C32).
  eapply climpl_seq.
  { eapply (mem_new_meth CZ meth METH') with (pbi := pbi) (BI := BI) (nbi := 128) (fl := 0);
      [ clear - FU1 Hf; lia
      | rewrite A16, B16, C16, A32, B32, C32; eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GR1)| clear; lia| clear; lia| clear; lia]
      | exact CSTb
      | rewrite unsigned_lit by lia; unfold MEM_INIT_STACK, BUF_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; clear - SLO; lia
      | reflexivity| exact INBI1| lia| exact W1Cb| apply fl_ok_0| exact HEADb| reflexivity| exact TLb| cbn; lia]. }
  intros f2 L2 st2 ms2 (v2 & mn & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (prp & RP & pbm & BM & pbb & BB & -> & -> & -> & RNGR & RNGM & RNGB & W1C2 & BBC & BMC & RPC & HEAD2 & TL2)).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. repeat (rewrite unsigned_lit in FRM2 by lia).
  rewrite A16, B16, C16, A32, B32, C32 in GR2.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FRb0 ltac:(clear - RSP; lia)) as FR2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & SPB2 & ST2 & LO2 & _ & MI2 & _) & LXS2 & _ & CIMG2 & GLO2). rewrite unsigned_lit in ST2 by lia.
  pose proof (meth_create mn meth CIMG2 MI2 METH') as MCR2.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z mn) as MU2. pose proof (wmono_refl usegs mn) as WM2.
  (* [comment removed for export] *)
  cprefix. ths. th_if_lit.
  ths. ths. if_cases K3; zify_cond K3; [| exfalso; destruct (mcreate_cases meth METH') as [[EC _]|[EC _]]; rewrite EC in K3; cbv in K3; discriminate K3].
  ths. do 6 ths. th_release FR2 (bv_unsigned sp). ths. chere.
  lazymatch goal with H : stk usegs mn lo (bv_unsigned sp) |- _ => rename H into STf end.
  apply climpl_done.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 NDL2].
  exists (Z_to_bv 64 BI), mn, ((prp, RP, 32) :: (pbm, BM, 32) :: (pbb, BB, 16) :: (pbi, BI, 128) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|].
  split; [clear - FU1 FU2 Hf; lia|].
  split; [pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) as GR; clear - GR; unfold cgrow in *; lia|].
  split. { eapply (cstate_seg [] _ _ _ _ mn mn _ sp tp lo B (bv_unsigned sp)); [exact CST2| apply munch_refl| apply wmono_refl| exact MI2| apply Forall_nil| clear - SLO LO; lia| exact SPB| cbn; exact I| exact STf| exact SPB]. }
  split. { eapply cframe_call; [exact FRb| exact FRM2| clear - RSP; lia| intros a X; exact X|].
    intros q Hq _ EQ. subst q. destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [NDB1' NDL1']. cbn [map blk_id fst] in NDB1', NDL1'.
    inversion NDB1'; inversion NDL1'; subst. destruct Hq as [Hq|Hq]; contradiction. }
  assert (ENVb : libenv mb LBL E).
  { eapply libenv_agree; [exact ENV1|]. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MUb WMb)|]. intros a Ha; cbv beta; cbn [outside].
    destruct (libenv_fp_where LBL a Ha) as [(X1 & X2 & X3)|(b & Hb & Hr)]; [clear - X1 SLO GLO BIIMG BI0; lia|].
    destruct b as [[q A] n]. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (INCL _ Hb)) as (_ & _ & _ & BCL & _). cbn [blk_addr blk_size fst snd] in Hr.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INBI1 (or_intror (INCL _ Hb)) ltac:(intros EQ; exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (INCL _ Hb) (eq_sym EQ)))) as AP.
    clear - Hr BCL LO SLO AP; lia. }
  assert (ENVn : libenv mn LBL E).
  { eapply libenv_agree; [exact ENVb|]. eapply agree_on_mono; [exact CFR2|]. intros a Ha.
    destruct (libenv_fp_where LBL a Ha) as [(X1 & X2 & X3)|(b & Hb & Hr)]; [right; right; split; [exact X1|]; split; [exact X2|]; split; [exact X3| cbn; intros X9; exact X9]|].
    right; left. exists b. split; [right; exact (INCL _ Hb)|]. split; [| exact Hr]. destruct b as [[q A] n]. cbn [blk_id fst]. intros EQ.
    exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (INCL _ Hb) (eq_sym EQ)). }
  split; [exact ENVn|].
  exists (MBK pbi pbb pbm prp None), BI, BB, BM, RP. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  exists BM. exists BB, RP, (Z.lor 0 4096), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0).
  split; [split; do 3 right; left; reflexivity|].
  split. { cbn [mbio_blocks k_bi k_bb k_bm k_rp k_d app]. cbn [map blk_id fst] in ND2.
    change (prp :: pbm :: pbb :: pbi :: map blk_id LBall) with ([prp; pbm; pbb; pbi] ++ map blk_id LBall) in ND2.
    apply NoDup_app_remove_r in ND2. apply NoDup_rev in ND2. cbn [rev app] in ND2. exact ND2. }
  split; [exact METH'|].
  split; [exact HEAD2|].
  split; [unfold bio_w1_cells in W1C2 |- *; exact (w1c_numw_fix _ _ _ _ _ _ _ W1C2)|].
  split; [unfold fl_ok; change (Z.lor 0 4096) with 4096; split; [lia| reflexivity]|].
  split; [cbn [app] in TL2; exact TL2|].
  exists (Z_to_bv 64 0). cbn [k_bb k_bm k_rp k_d].
  split; [split; [do 2 right; left; reflexivity| do 2 right; left; reflexivity]|].
  split; [exact BBC|].
  split; [split; [right; left; reflexivity| right; left; reflexivity]|].
  split; [split; [left; reflexivity| left; reflexivity]|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [reflexivity|]. unfold bufmem_cells in BMC, RPC. split; [exact BMC| exact RPC].
Qed.

End WithCeiling0.
