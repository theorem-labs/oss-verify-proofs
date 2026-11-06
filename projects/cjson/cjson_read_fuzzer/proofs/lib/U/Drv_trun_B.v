(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_pad Exit F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_heap_instR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_heap_instR.CJ_heap_inst0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_heap_instR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_heap_instR.CJ_heap_inst.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_fuzz CJ_fuzz_top.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_heap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_heap.KB_drv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Drv_base Drv_heap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_open.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_open.Drv_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Drv_trun_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
  Hypothesis Hr : realloc_scps_stmt LHEAPd.
  Hypothesis Hrn : rrealloc_null_stmt.
  Hypothesis SO_EMIT1 : so_emit_first_stmt.
  Hypothesis SO_EMIT2 : so_emit_again_stmt.
  Variables (sp gp tp : word) (fs : Fs) (lo SPB : Z) (tid : word)
            (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 ra0 : word) (ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 : word)
            (A cap D plen owned : Z) (pay : list byte).
  Hypothesis TP : tp = wz PTP.
  Hypothesis LO : lo + 2^22 <= bv_unsigned sp + 80.
  Hypothesis GT : alloc_ceiling <= lo.
  Hypothesis SPH : bv_unsigned sp + 128 <= 0x800000000000.
  Hypothesis SPBE : SPB = bv_unsigned sp + 128.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
  Hypothesis TID : 0 < bv_unsigned tid < 2^22.
  Hypothesis PLEN : 0 <= plen < 2^26.
  Hypothesis OWN : owned = 0 \/ (owned = D /\ D <> A).

  Notation TITER := (titer sp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 A cap D plen owned pay).
  Notation TRET := (trun_ret sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap).
  Notation LST pc Fv fcv mm rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 cnt x28 x29 x30 x31 :=
    (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp x5 x6 x7 (Z_to_bv 64 plen) (Z_to_bv 64 D) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 owned) x19 (Z_to_bv 64 PINITFLAG) (Z_to_bv 64 cnt) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 x28 x29 x30 x31)
        Fv (Z_to_bv 64 pc) fcv None mm (seg_rom usegs)) (only parsing).

  (* [comment removed for export] *)
  Lemma trun_ctrl : forall (n : nat) LB so fc m mo (F : bvmap 5 word) (T : TSet) rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    TITER LB so fc m mo -> (1 <= n <= 4)%nat ->
    (n = 1%nat -> realizes usegs (mkCfg (LST 0x1352c F fc m rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-1)) 0 x28 x29 x30 x31) mo) T) ->
    ((2 <= n)%nat -> realizes usegs (mkCfg (LST 0x134f4 F fc m rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-1)) (Z.of_nat n - 1) x28 x29 x30 x31) mo) T) ->
    realizes usegs (mkCfg (LST 0x13518 F fc m rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0) (Z.of_nat n) x28 x29 x30 x31) mo) T.
  Proof.
    intros until x31. intros IT Hn K1 K2.
    pose proof (lhd_mok _ _ _ _ (proj1 IT)) as MOK'.
    eapply rz_step_evt; [exact MOK'|].
    step. step. replace (negb (bv_ltu (Z_to_bv 64 (-1)) (Z_to_bv 64 (-2)))) with true by (vm_compute; reflexivity). cbv iota.
    step.
    rewrite (unsigned_lit (Z.of_nat n)) by lia. rewrite swrap32_small by lia.
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - apply evt_done. replace (Z.of_nat n + -1) with (Z.of_nat n - 1) by lia. apply K2. lia.
    - apply evt_done. replace (Z.of_nat n + -1) with 0 by lia. apply K1. lia.
  Qed.

  Lemma in_cb_remove_ne : forall (b : cblock) X LB, In b LB -> fst b <> X -> In b (cb_remove X LB).
  Proof.
    intros [B n] X LB. induction LB as [|[B' n'] LB IH]; intros Hin Hne; [destruct Hin|].
    cbn. cbn in Hne. destruct Hin as [E|Hin].
    - injection E as -> ->. destruct (Z.eqb_spec B X); [exfalso; exact (Hne e)|]. left. reflexivity.
    - destruct (Z.eqb_spec B' X); [exact Hin|]. right. apply IH; [exact Hin| exact Hne].
  Qed.

  (* [comment removed for export] *)
  Lemma trun_tail : forall LB so fc m mo (F : bvmap 5 word) (T : TSet) (cnt : Z) rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    TITER LB so fc m mo ->
    (forall ms' mo', TRET 0 so ms' mo' -> realizes usegs (mkCfg ms' mo') T) ->
    realizes usegs (mkCfg (LST 0x1352c F fc m rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-1)) cnt x28 x29 x30 x31) mo) T.
  Proof.
    intros until x31. intros IT K.
    destruct IT as (HL & INA & IND & PAY & CJ & [e ER] & MI & ST & [u TFR] & MFR & DS & INC & SEF & SOF & DM & FRM).
    pose proof DM as [MOK' MFDS HFS].
    pose proof GT as GT'. try rewrite <- alloc_ceiling_eq in GT'.
    eapply rz_step_evt; [exact MOK'|].
    do 2 step. apply evt_done.
    destruct (Z.eq_dec owned 0) as [OW | NZ].
    - (* [comment removed for export] *)
      rewrite OW.
      eapply rz_step_evt; [exact MOK'|].
      eapply evt_cut. { eapply (lhd_free_null); reflexivity. }
      intros ms' ->.
      replace (ret_pc (Z_to_bv 64 0x13534)) with (Z_to_bv 64 0x13534) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold PERRNO in ER. unfold wz in TFR.
      do 14 step.
      replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
      apply evt_done. apply K.
      unfold trun_ret.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, F, fc, m, e, LB.
      split; [reflexivity|]. split; [exact FRM|]. split; [exact MI|]. split.
      { pose proof (stk_release usegs m lo _ _ ST TFR ltac:(lia)) as ST2. cbn [cells_size csize Nat.add] in ST2.
        replace (bv_unsigned sp - 80 + Z.of_nat 80) with (bv_unsigned sp) in ST2 by lia. exact ST2. }
      split; [exact ER|]. split; [exact HL|]. split; [exact INA|]. split; [exact MFR|]. split; [exact DS|]. split; [exact SEF|]. split; [exact SOF| exact DM].
    - (* [comment removed for export] *)
      destruct OWN as [H0 | [OW DNA]]; [exfalso; exact (NZ H0)|].
      rewrite OW. assert (INDL : In (D, plen) LB) by (destruct IND as [H|H]; [exfalso; exact (NZ H)| exact H]).
      unfold PERRNO in ER. unfold wz in TFR.
      eapply (scps_realizes usegs).
      { eapply (lhd_free) with (lo := lo) (SPB := SPB) (LB := LB) (A := D) (n := plen) (errv := e);
          first [exact HL| exact INDL| exact ER| exact MI| exact TP| reflexivity
                | rewrite ?unsigned_lit by lia; first [exact ST| rewrite ?alloc_ceiling_eq; unfold CJ_iface.RMALLOC_STACK; lia] ]. }
      intros ms' mo' PO VO.
      destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MI' & ST' & ER' & PR & HL').
      rewrite ?unsigned_lit in ST' by lia. rewrite ?unsigned_lit in PR by lia.
      replace (ret_pc (Z_to_bv 64 0x13534)) with (Z_to_bv 64 0x13534) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (lhd_mok _ _ _ _ HL') as MOK2.
      assert (TFR' : rw_cells usegs m' (bv_unsigned sp - 80) [CB 8 u; C8 s7; C8 s6; C8 ms5; C8 ms4; C8 ms3; C8 ms2; C8 ms1; C8 ms0; C8 (Z_to_bv 64 0x132e0)]).
      { eapply cj_pres_rw_cells; [exact PR| exact TFR| left; cbn; lia]. }
      eapply rz_step_evt; [exact MOK2|].
      do 14 step.
      replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
      apply evt_done. apply K.
      unfold trun_ret.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, F, fc, m', e, (cb_remove D LB).
      split; [reflexivity|]. split; [exact FRM|]. split; [exact MI'|]. split.
      { pose proof (stk_release usegs m' lo _ _ ST' TFR' ltac:(lia)) as ST2. cbn [cells_size csize Nat.add] in ST2.
        replace (bv_unsigned sp - 80 + Z.of_nat 80) with (bv_unsigned sp) in ST2 by lia. exact ST2. }
      split; [exact ER'|]. split; [exact HL'|]. split; [apply in_cb_remove_ne; [exact INA| cbn; intros E; apply DNA; symmetry; exact E]|].
      split. { eapply cj_pres_rw_cells; [exact PR| exact MFR| left; cbn; lia]. }
      split. { eapply DSTAT_cj_pres; [exact DS| exact PR]. }
      split. { eapply stderr_wfile0_cj_pres; [exact SEF| exact PR]. }
      split. { eapply stdout_file_cj_pres; [exact SOF| exact PR]. }
      eapply DMOD_vm_only; [exact DM| exact VO| exact MOK2].
  Qed.

  (* [comment removed for export] *)
  Lemma titer_emit : forall LB so so' fc fc' m m' mo,
    TITER LB so fc m mo ->
    munch [(lo, bv_unsigned sp - 80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' ->
    wmono usegs m m' -> mem_inv usegs m' -> frm0 fc' -> stk usegs m' lo (bv_unsigned sp - 80) -> stdout_file m' so' ->
    TITER LB so' fc' m' mo.
  Proof.
    intros LB so so' fc fc' m m' mo IT MU WM MI' FRM' ST' SOF'.
    destruct IT as (HL & INA & IND & PAY & CJ & [e ER] & MI & ST & [u TFR] & MFR & DS & INC & SEF & SOF & DM & FRM).
    pose proof GT as GT'. try rewrite <- alloc_ceiling_eq in GT'.
    split.
    { eapply lhd_frame_ext; [exact HL| exact MU| exact WM|]. solve_Forall ltac:(drv_write_ok_tac). }
    split; [exact INA|]. split; [exact IND|]. split.
    { destruct PAY as [H|(H1 & H2 & H3)]; [left; exact H| right]. split; [exact H1|]. split; [| exact H3].
      pose proof (lhd_block_range _ _ _ _ _ _ HL H1) as (R1 & R2 & R3 & R4 & R5). try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
      xport H2 MU WM H2'. exact H2'. }
    split. { xport CJ MU WM CJ'. exact CJ'. }
    split. { unfold PERRNO in ER. xport ER MU WM ER'. exists e. exact ER'. }
    split; [exact MI'|]. split; [exact ST'|].
    split. { xport TFR MU WM TFR'. exists u. exact TFR'. }
    split. { xport MFR MU WM MFR'. exact MFR'. }
    split. { xport DS MU WM DS'. exact DS'. }
    split. { unfold PINCB in *. xport INC MU WM INC'. exact INC'. }
    split. { xport SEF MU WM SEF'. exact SEF'. }
    split; [exact SOF'|]. split; [exact DM| exact FRM'].
  Qed.

  (* [comment removed for export] *)
  Lemma trun_emit2 : forall (j : nat) LB fc m mo (F : bvmap 5 word) (K : TSet) (cnt : Z) x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    TITER LB (so_after j) fc m mo -> (j <= 3)%nat -> K [] ->
    (forall fc' m' (F' : bvmap 5 word) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
        TITER LB (so_after (S j)) fc' m' mo ->
        realizes usegs (mkCfg (LST 0x13518 F' fc' m' (Z_to_bv 64 0x13518) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 0) cnt y28 y29 y30 y31) mo) K) ->
    realizes usegs (mkCfg (LST 0x135c4 F fc m (Z_to_bv 64 0x13518) x5 x6 x7 x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0) cnt x28 x29 x30 x31) mo) K.
  Proof.
    intros until x31. intros IT Hj HK K2.
    pose proof IT as (HL & INA & IND & PAY & CJ & [e ER] & MI & ST & [u TFR] & MFR & DS & INC & SEF & SOF & DM & FRM).
    pose proof DM as [MOK' MFDS HFS]. destruct (DMOD_chan _ _ _ DM ltac:(left; reflexivity)) as [CH1 CH2].
    pose proof (lhd_ssp0 _ _ _ _ HL) as SSP.
    pose proof (lines_length j) as LL. pose proof (lines_bytes j) as LBY.
    apply rz_drop_nil; [exact HK|].
    unfold so_after in SOF.
    eapply (SO_EMIT2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo lo ssp_guard_val (lines j) K);
      first [exact MOK'| exact CH1| exact SOF| exact LBY| exact SSP| exact MI| exact FRM| exact HK
            | rewrite ?unsigned_lit by lia; first [exact ST| reflexivity| unfold STDOUT_BUFSIZ, EMITD_DEPTH, GLOBALS_TOP in *; lia] | idtac].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' MU WM MI' FRM' FA ST' SOF' SSP'.
    rewrite ?unsigned_lit in MU by lia. rewrite ?unsigned_lit in ST' by lia.
    replace (ret_pc (Z_to_bv 64 0x13518)) with (Z_to_bv 64 0x13518) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply K2. rewrite lines_S in SOF'. eapply titer_emit; [exact IT| exact MU| exact WM| exact MI'| exact FRM'| exact ST'| exact SOF'].
  Qed.

  (* [comment removed for export] *)
  Lemma trun_emit1 : forall LB fc m mo (F : bvmap 5 word) (K : TSet) (cnt : Z) x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    TITER LB stdout_init fc m mo -> K [] ->
    (forall fc' m' (F' : bvmap 5 word) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
        TITER LB (so_after 0) fc' m' mo ->
        realizes usegs (mkCfg (LST 0x13518 F' fc' m' (Z_to_bv 64 0x13518) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 0) cnt y28 y29 y30 y31) mo) K) ->
    realizes usegs (mkCfg (LST 0x135c4 F fc m (Z_to_bv 64 0x13518) x5 x6 x7 x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0) cnt x28 x29 x30 x31) mo)
             (t_emit (W 1 emit_line) K).
  Proof.
    intros until x31. intros IT HK K2.
    pose proof IT as (HL & INA & IND & PAY & CJ & [e ER] & MI & ST & [u TFR] & MFR & DS & INC & SEF & SOF & DM & FRM).
    pose proof DM as [MOK' MFDS HFS]. destruct (DMOD_chan _ _ _ DM ltac:(left; reflexivity)) as [CH1 CH2].
    pose proof (lhd_ssp0 _ _ _ _ HL) as SSP.
    eapply (SO_EMIT1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo lo ssp_guard_val K);
      first [exact MOK'| exact CH1| exact SOF| exact SSP| exact MI| exact FRM| exact HK
            | rewrite ?unsigned_lit by lia; first [exact ST| reflexivity| unfold EMITD_DEPTH, GLOBALS_TOP in *; lia] | idtac].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' MU WM MI' FRM' FA ST' SOF' SSP'.
    rewrite ?unsigned_lit in MU by lia. rewrite ?unsigned_lit in ST' by lia.
    replace (ret_pc (Z_to_bv 64 0x13518)) with (Z_to_bv 64 0x13518) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply K2. change emit_after_first with (so_after 0) in SOF'.
    eapply titer_emit; [exact IT| exact MU| exact WM| exact MI'| exact FRM'| exact ST'| exact SOF'].
  Qed.

  (* [comment removed for export] *)
  Lemma trun_again : forall (n j : nat) LB fc m mo (F : bvmap 5 word) (KT : TSet) rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
    TITER LB (so_after j) fc m mo -> (1 <= n)%nat -> (j + n <= 4)%nat -> KT [] ->
    (forall ms' mo', TRET 0 (so_after (j + n)) ms' mo' -> realizes usegs (mkCfg ms' mo') KT) ->
    realizes usegs (mkCfg (LST 0x134f4 F fc m rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z.of_nat n) x28 x29 x30 x31) mo) KT.
  Proof.
    induction n as [|n IH]; intros until x31; intros IT Hn Hjn HK KF; [exfalso; lia|].
    eapply (trun_call Hr Hrn sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap D plen owned pay TP LO GT SPH SPBE SPAL PLEN);
      [exact IT|].
    intros LB' fc' m' mo' F' y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 IT'.
    eapply trun_emit2; [exact IT'| lia| exact HK|].
    intros fc2 m2 F2 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 IT2.
    eapply trun_ctrl; [exact IT2| lia| |].
    - intros Hn1. eapply trun_tail; [exact IT2|]. intros msx mox HR. apply KF. replace (j + S n)%nat with (S j) by lia. exact HR.
    - intros Hn2. replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
      eapply IH; [exact IT2| lia| lia| exact HK|]. intros msx mox HR. apply KF. replace (j + S n)%nat with (S j + n)%nat by lia. exact HR.
  Qed.

  (* [comment removed for export] *)
  Lemma trun_rounds : forall (c : nat) LB fc m mo (F : bvmap 5 word) (KT : TSet) rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
    TITER LB stdout_init fc m mo -> (1 <= c <= 4)%nat -> KT [] ->
    (forall ms' mo', TRET 0 (so_after (c - 1)) ms' mo' -> realizes usegs (mkCfg ms' mo') KT) ->
    realizes usegs (mkCfg (LST 0x134f4 F fc m rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z.of_nat c) x28 x29 x30 x31) mo)
             (t_emit (W 1 emit_line) KT).
  Proof.
    intros until x31; intros IT Hc HK KF.
    eapply (trun_call Hr Hrn sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap D plen owned pay TP LO GT SPH SPBE SPAL PLEN);
      [exact IT|].
    intros LB' fc' m' mo' F' y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 IT'.
    eapply trun_emit1; [exact IT'| exact HK|].
    intros fc2 m2 F2 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 IT2.
    eapply trun_ctrl; [exact IT2| lia| |].
    - intros Hc1. eapply trun_tail; [exact IT2|]. intros msx mox HR. apply KF. replace (c - 1)%nat with 0%nat by lia. exact HR.
    - intros Hc2. replace (Z.of_nat c - 1) with (Z.of_nat (c - 1)) by lia.
      eapply trun_again; [exact IT2| lia| lia| exact HK|]. intros msx mox HR. apply KF. replace (c - 1)%nat with (0 + (c - 1))%nat by lia. exact HR.
  Qed.
End S.


End CeilWrap.
