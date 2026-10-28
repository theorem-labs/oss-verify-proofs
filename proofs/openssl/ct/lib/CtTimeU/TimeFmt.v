(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem Bytes.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG PrintfModel PrintfModelX ApFmt CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx Printf_apfmt Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_pop_arg F_printf_iface F_vsnprintf Printf_sn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_snprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnFmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeFmtPure.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_C17 : Z := 0x132b1.      (* [comment removed for export] *)

Local Ltac rom_lit A :=
  intros m MI;
  lazymatch goal with |- bytes_at _ _ _ ?bs =>
    let bs' := eval cbv in bs in
    change bs with bs';
    apply (ro_cells_bytes m A (length bs') bs');
    apply (ro_cells_image ctusegs m A bs' MI); [vm_compute; reflexivity| unfold A; lia| unfold A; cbn; lia]
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma fmt_C17_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C17 (zb FMT_C17). Proof. rom_lit A_C17. Qed.
End WithCeiling0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma sng_C17 : forall m lo q D (a3 a4 a5 a6 a7 st0 : word) (t : tm6),
  mem_inv ctusegs m -> STATIC_SPLIT <= lo -> tm_valid t ->
  bv_unsigned a3 mod 2^32 = t_year t -> bv_unsigned a4 mod 2^32 = t_mon t -> bv_unsigned a5 mod 2^32 = t_mday t ->
  bv_unsigned a6 mod 2^32 = t_hour t -> bv_unsigned a7 mod 2^32 = t_min t -> bv_unsigned st0 mod 2^32 = t_sec t ->
  sng_call_ok m lo q D 20 A_C17 FMT_C17 [a3; a4; a5; a6; a7; st0]
    [PA_i (t_year t); PA_i (t_mon t); PA_i (t_mday t); PA_i (t_hour t); PA_i (t_min t); PA_i (t_sec t)] (gen15 t).
Proof.
  intros until t. intros MI SL TV A3 A4 A5 A6 A7 S0. pose proof TV as (Y & MO & MD & HH & MI' & SS).
  pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
  destruct (printf_piecesx_C17 (t_year t) (t_mon t) (t_mday t) (t_hour t) (t_min t) (t_sec t)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (ps & P & CC).
  pose proof (printf_piecesx_count _ _ _ _ P) as L. rewrite (ct_gentime_gen15 t TV) in CC.
  split; [apply fmt_C17_at; exact MI|]. split; [exact fmt_bytes_C17|]. split; [exact pass1x_ok_C17|].
  split; [unfold A_C17, STATIC_SPLIT; change (zlength FMT_C17) with 26; lia|].
  split.
  { intros m' MU'. cbn [args_ok arg_ok].
    rewrite A3, A4, A5, A6, A7, S0. rewrite !(Z.mod_small _ (2^32)) by lia. repeat split; lia. }
  assert (MDL : printf_modelx OUT_sn OUTFP_sn FMT_C17
            [PA_i (t_year t); PA_i (t_mon t); PA_i (t_mday t); PA_i (t_hour t); PA_i (t_min t); PA_i (t_sec t)] []
          = ITree.Ret (ITree.Exc.Ok (zlength (gen15 t), gen15 t))).
  { rewrite <- CC. rewrite L. apply (printf_modelx_sn _ _ _ _ P). rewrite L. unfold SN_CAP. lia. }
  split; [exact MDL|].
  split; [apply fp_callsx_nog; repeat constructor|].
  rewrite gen15_length. lia.
Qed.

End WithCeiling1.
