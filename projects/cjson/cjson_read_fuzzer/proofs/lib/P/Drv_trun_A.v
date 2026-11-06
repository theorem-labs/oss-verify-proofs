(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_pad Exit Printf_model F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RRealloc_iface CJ_heap_inst0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_heap_instR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_heap_instR.CJ_heap_inst.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_fuzz CJ_fuzz_top.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_heap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_heap.KB_drv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Drv_base Drv_heap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_hdr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_hdr.Drv_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_emit_app' : forall o1 o2 K, t_eq (t_emit (o1 ++ o2) K) (t_emit o1 (t_emit o2 K)).
Proof.
  intros o1 o2 K tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HK)].
    + destruct (is_prefix_app_split o1 o2 tr Hp) as [Hp1 | (b' & -> & Hp2)]; [left; exact Hp1|].
      right. exists b'. split; [reflexivity|]. left. exact Hp2.
    + right. exists (o2 ++ tr'). split; [rewrite app_assoc; reflexivity|]. right. exists tr'. auto.
  - intros [Hp | (tr' & -> & [Hp2 | (tr'' & -> & HK)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. clear K. revert o2 tr' Hp2. induction o1 as [|x o1 IH]; intros o2 tr' Hp2; cbn; [exact Hp2|]. split; [reflexivity| apply IH; exact Hp2].
    + right. exists tr''. split; [rewrite app_assoc; reflexivity| exact HK].
Qed.

(* [comment removed for export] *)
Lemma lines_S : forall j, lines j ++ [48; 10] = lines (S j).
Proof.
  intros j. unfold lines. induction j as [|j IH]; [reflexivity|]. cbn [repeat concat]. rewrite <- app_assoc, IH. reflexivity.
Qed.

Lemma lines_length : forall j, zlength (lines j) = 2 * Z.of_nat j.
Proof. intros j. unfold lines, zlength. induction j as [|j IH]; [reflexivity|]. cbn [repeat concat app length]. lia. Qed.

Lemma lines_bytes : forall j, Forall (fun c => 0 <= c < 256) (lines j).
Proof.
  intros j. unfold lines. induction j as [|j IH]; [constructor|]. cbn [repeat concat app].
  constructor; [lia|]. constructor; [lia|]. exact IH.
Qed.

(* [comment removed for export] *)
Lemma swrap32_small : forall z, -2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32 `div` 2) with 2147483648. lia.
Qed.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
      change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.

Section S.
  Hypothesis Hr : realloc_scps_stmt LHEAPd.
  Hypothesis Hrn : rrealloc_null_stmt.
  Hypothesis SO_EMIT1 : so_emit_first_stmt.
  Hypothesis SO_EMIT2 : so_emit_again_stmt.

  (* [comment removed for export] *)
  Definition HI : cj_heap_iface := PHI Hr Hrn.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Definition titer (LB : list cblock) (so : stdout_st) (fc : bv 32) (m : word -> option byte) (mo : Model) : Prop :=
    LHEAPd SPB LB m mo /\ In (A, cap) LB /\ (owned = 0 \/ In (D, plen) LB)
    /\ (plen <= 4 \/ (In (D, plen) LB /\ bytes_at psegs m D pay /\ Z.of_nat (length pay) = plen))
    /\ CJST m /\ (exists e, rw_cells psegs m PERRNO [C4 e]) /\ mem_inv psegs m /\ stk psegs m lo (bv_unsigned sp - 80)
    /\ (exists uj, rw_cells psegs m (bv_unsigned sp - 80) [CB 8 uj; C8 s7; C8 s6; C8 ms5; C8 ms4; C8 ms3; C8 ms2; C8 ms1; C8 ms0; C8 (wz 0x122c0)])
    /\ rw_cells psegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)
    /\ DSTAT true tid m /\ rw_cells psegs m PINCB [C1 (Z_to_bv 8 0)] /\ stderr_wfile0 m /\ stdout_file m so /\ DMOD fs FDS0 mo /\ frm0 fc.

  Notation TRET := (trun_ret sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap).

  (* [comment removed for export] *)
  Notation LST pc Fv fcv mm rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 cnt x28 x29 x30 x31 :=
    (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp x5 x6 x7 (Z_to_bv 64 plen) (Z_to_bv 64 D) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 owned) x19 (Z_to_bv 64 PINITFLAG) (Z_to_bv 64 cnt) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 x28 x29 x30 x31)
        Fv (Z_to_bv 64 pc) fcv None mm (seg_rom psegs)) (only parsing).

  (* [comment removed for export] *)
  Lemma DSTAT_incb_cycle : forall ph LB SP m m0 m' m1,
    DSTAT ph tid m -> munch [(PINCB, PINCB + 1)] m m0 -> wmono psegs m m0 -> dpres LB SP m0 m' ->
    munch [(PINCB, PINCB + 1)] m' m1 -> wmono psegs m' m1 -> rw_cells psegs m1 PINCB [C1 (Z_to_bv 8 0)] -> DSTAT ph tid m1.
  Proof.
    intros ph LB SP m m0 m' m1 DD MU1 WM1 PR MU3 WM3 INC1. unfold DSTAT, ATEX, PDSO, PINCB, PATEX, PCXAFIN in *.
    destruct DD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ exact INC1
               | lazymatch type of MU1 with munch _ ?mm _ => match goal with |- rw_cells _ _ ?A ?cs => match goal with Dm : rw_cells _ mm A cs |- _ =>
                   let Da := fresh in let Db := fresh in
                   pose proof (rw_cells_transport _ _ _ _ _ _ Dm MU1 WM1 ltac:(cbn; lia)) as Da;
                   pose proof (rw_cells_magree _ _ _ _ _ PR Da ltac:(cbn [cells_size atex_cells csize Nat.add]; intros; apply (dstat_doc_addr LB SP); unfold dstat_addr; lia)) as Db;
                   exact (rw_cells_transport _ _ _ _ _ _ Db MU3 WM3 ltac:(cbn; lia))
                 end end end ].
  Qed.


  (* [comment removed for export] *)
  Lemma trun_call : forall LB so fc m mo (F : bvmap 5 word) (cnt : Z) (T : TSet) rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
    titer LB so fc m mo ->
    (forall LB' fc' m' mo' (F' : bvmap 5 word) y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
        titer LB' so fc' m' mo' ->
        realizes psegs (mkCfg (LST 0x125a4 F' fc' m' (Z_to_bv 64 0x124f8) y5 y6 y7 (Z_to_bv 64 0) (Z_to_bv 64 0) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 0) cnt y28 y29 y30 y31) mo') T) ->
    realizes psegs (mkCfg (LST 0x124d4 F fc m rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 cnt x28 x29 x30 x31) mo) T.
  Proof.
    intros until x31. intros IT K.
    destruct IT as (HL & INA & IND & PAY & CJ & [e ER] & MI & ST & [u TFR] & MFR & DS & INC & SEF & SOF & DM & FRM).
    pose proof DM as [MOK' MFDS HFS].
    pose proof (munch_refl [(PINCB, PINCB + 1)] m) as MU1. pose proof (wmono_refl psegs m) as WM1. unfold PINCB in MU1, INC. unfold PINITFLAG. unfold PERRNO in ER.
    eapply rz_step_evt; [exact MOK'|].
    step. step. fix_lit_store. (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof GT as GT0. try rewrite <- alloc_ceiling_eq in GT0.
    lazymatch type of MU1 with munch _ _ ?m1 =>
      assert (HL0 : LHEAPd SPB LB m1 mo) by (eapply lhd_frame_ext; [exact HL| exact MU1| exact WM1| solve_Forall ltac:(drv_write_ok_tac)]);
      assert (PAY0 : plen <= 4 \/ (In (D, plen) LB /\ bytes_at psegs m1 D pay /\ Z.of_nat (length pay) = plen))
        by (destruct PAY as [Hp|(Hp1 & Hp2 & Hp3)]; [left; exact Hp| right];
            pose proof (lhd_block_range _ _ _ _ _ _ HL Hp1) as (R1 & R2 & R3 & R4 & R5); try rewrite alloc_ceiling_eq in R4; unfold PIMG_LO, PIMG_HI in R5;
            xport Hp2 MU1 WM1 Hp4; split; [exact Hp1| split; [exact Hp4| exact Hp3]])
    end.
    xport CJ MU1 WM1 CJ0. xport SEF MU1 WM1 SEF0. xport SOF MU1 WM1 SOF0.
    do 3 step. apply evt_done.
    eapply (scps_realizes psegs).
    { eapply (fuzz_spec_closed HI) with (lo := lo) (data := pay) (LB := LB) (SPB := SPB) (errv := e);
        first [ exact HL0 | exact PAY0 | exact PLEN | exact CJ0 | exact ER | exact MI | exact FRM | exact TP | reflexivity
              | rewrite ?unsigned_lit by lia; first [exact ST | rewrite ?alloc_ceiling_eq; unfold FUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK; lia ] ]. }
    intros ms' mo' PO VO.
    destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & F' & fc' & m' & e' & LB' & LX
                    & -> & -> & FRM' & _ & MI' & ST' & CJ' & ER' & HL' & HP & PR & PAY').
    rewrite ?unsigned_lit in ST' by lia. rewrite ?unsigned_lit in PR by lia.
    replace (ret_pc (Z_to_bv 64 0x124e8)) with (Z_to_bv 64 0x124e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (lhd_mok _ _ _ _ HL') as MOK2.
    assert (INL : forall b, In b LB -> In b LB').
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; left; exact Hb]. }
    pose proof GT as GT'. try rewrite <- alloc_ceiling_eq in GT'.
    (* [comment removed for export] *)
    unfold PERRNO in ER'.
    lazymatch type of MU1 with munch _ _ ?m0 =>
      assert (INC2 : rw_cells psegs m' 210820 [C1 (Z_to_bv 8 1)])
        by (eapply rw_cells_magree; [exact PR| match goal with H : rw_cells psegs m0 210820 _ |- _ => exact H end
                                    | intros a Ha; apply (dstat_doc_addr LB (bv_unsigned sp - 80)); unfold dstat_addr; cbn in Ha; lia]);
      assert (TFR2 : rw_cells psegs m' (bv_unsigned sp - 80) [CB 8 u; C8 s7; C8 s6; C8 ms5; C8 ms4; C8 ms3; C8 ms2; C8 ms1; C8 ms0; C8 (wz 0x122c0)])
        by (eapply dpres_rw_cells_stack; [exact PR| match goal with H : rw_cells psegs m0 (bv_unsigned sp - 80) _ |- _ => exact H end| lia| lia]);
      assert (MFR2 : rw_cells psegs m' (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0))
        by (eapply dpres_rw_cells_stack; [exact PR| match goal with H : rw_cells psegs m0 (bv_unsigned sp) _ |- _ => exact H end| lia| lia])
    end.
    pose proof (stderr_wfile0_dpres _ _ _ _ SEF0 PR) as SEF2. pose proof (stdout_file_dpres _ _ _ _ _ SOF0 PR) as SOF2.
    unfold wz in TFR2.
    (* [comment removed for export] *)
    pose proof (munch_refl [(PINCB, PINCB + 1)] m') as MU3. pose proof (wmono_refl psegs m') as WM3. unfold PINCB in MU3.
    eapply rz_step_evt; [exact MOK2|]. unfold wz. step. step. fix_lit_store.
    lazymatch type of MU3 with munch _ _ ?m1 =>
      assert (HL3 : LHEAPd SPB LB' m1 mo') by (eapply lhd_frame_ext; [exact HL'| exact MU3| exact WM3| solve_Forall ltac:(drv_write_ok_tac)]);
      assert (PAY3 : plen <= 4 \/ (In (D, plen) LB' /\ bytes_at psegs m1 D pay /\ Z.of_nat (length pay) = plen))
        by (destruct PAY' as [Hq|Hq]; [left; exact Hq|]; destruct PAY as [Hp|(Hp1 & Hp2 & Hp3)]; [left; exact Hp| right];
            pose proof (lhd_block_range _ _ _ _ _ _ HL Hp1) as (R1 & R2 & R3 & R4 & R5); try rewrite alloc_ceiling_eq in R4; unfold PIMG_LO, PIMG_HI in R5;
            xport Hq MU3 WM3 Hq4; split; [apply INL; exact Hp1| split; [exact Hq4| exact Hp3]]);
      assert (DS3 : DSTAT true tid m1)
        by (eapply (DSTAT_incb_cycle true LB (bv_unsigned sp - 80)); [exact DS| exact MU1| exact WM1| exact PR| exact MU3| exact WM3
                                                                 | unfold PINCB; match goal with H : rw_cells psegs m1 210820 _ |- _ => exact H end])
    end.
    xport CJ' MU3 WM3 CJ3. xport SEF2 MU3 WM3 SEF3. xport SOF2 MU3 WM3 SOF3.
    step. step. apply evt_done.
    eapply K. split; [exact HL3|]. split; [apply INL; exact INA|]. split.
    { destruct IND as [Hi|Hi]; [left; exact Hi| right; apply INL; exact Hi]. }
    split; [exact PAY3|].
    split; [exact CJ3|]. split; [exists e'; exact ER'|]. split; [exact MI'|]. split; [exact ST'|].
    split; [exists u; exact TFR2|]. split; [exact MFR2|]. split; [exact DS3|]. split; [unfold PINCB; exact INC2|].
    split; [exact SEF3|]. split; [exact SOF3|].
    split. { eapply DMOD_vm_only; [exact DM| exact VO| exact MOK2]. }
    exact FRM'.
  Qed.
End S.


End CeilWrap.
