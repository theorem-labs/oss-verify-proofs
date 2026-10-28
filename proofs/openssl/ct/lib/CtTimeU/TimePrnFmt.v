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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_bio_push W_bio_write W_bio_printf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnFmt W_bio_printfx8.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeFmtPure TimeToTmDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition A_C16 : Z := 0x21840.
Definition A_MON : Z := 0x41980.

Definition mon_str (k : Z) : list Z :=
  nth (Z.to_nat k) [[74;97;110]; [70;101;98]; [77;97;114]; [65;112;114]; [77;97;121]; [74;117;110];
                    [74;117;108]; [65;117;103]; [83;101;112]; [79;99;116]; [78;111;118]; [68;101;99]] [].
(* [comment removed for export] *)
Definition mon_slack (k : Z) : list byte := if Z.even k then zb (mon_str (k + 1)) ++ [Z_to_bv 8 0] else [].

Lemma mon_str_len : forall k, 0 <= k <= 11 -> zlength (mon_str k) = 3 /\ Forall (fun c => 0 < c < 256) (mon_str k).
Proof.
  intros k Hk. assert (H : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; (split; [reflexivity| cbv; repeat constructor]).
Qed.

Local Ltac rom_lit A :=
  intros m MI;
  lazymatch goal with |- bytes_at _ _ _ ?bs =>
    let bs' := eval cbv in bs in
    change bs with bs';
    apply (ro_cells_bytes m A (length bs') bs');
    apply (ro_cells_image ctusegs m A bs' MI); [vm_compute; reflexivity| unfold A; lia| unfold A; cbn; lia]
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma fmt_C16_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C16 (zb FMT_C16). Proof. rom_lit A_C16. Qed.

Lemma mon_at : forall m k, mem_inv ctusegs m -> 0 <= k <= 11 ->
  bytes_at ctusegs m (4 * k + A_MON) (zb (mon_str k) ++ Z_to_bv 8 0 :: mon_slack k).
Proof.
  intros m k MI Hk. assert (H : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]];
  lazymatch goal with |- bytes_at _ _ ?a ?bs =>
    let bs' := eval cbv in bs in change bs with bs'; let av := eval cbv in a in change a with av;
    apply (ro_cells_bytes m av (length bs') bs');
    apply (ro_cells_image ctusegs m av bs' MI); [vm_compute; reflexivity| lia| cbn; lia]
  end.
Qed.

Lemma mon_slack_ok : forall k, 0 <= k <= 11 -> (- (4 * k + A_MON + 3 + 1)) mod 8 <= zlength (mon_slack k) /\ zlength (mon_slack k) <= 4.
Proof.
  intros k Hk. assert (H : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; (cbv; split; discriminate).
Qed.

(* [comment removed for export] *)
Lemma pcokx_C16 : forall m lo q (t : tm6) (ms F3 : Z) (a2 a3 a4 a5 a6 a7 st0 st1 : word),
  mem_inv ctusegs m -> STATIC_SPLIT <= lo -> tm_valid t -> 0 <= ms < 1000 ->
  a2 = Z_to_bv 64 (4 * (t_mon t - 1) + A_MON) ->
  bv_unsigned a3 mod 2^32 = t_mday t -> bv_unsigned a4 mod 2^32 = t_hour t -> bv_unsigned a5 mod 2^32 = t_min t -> bv_unsigned a6 mod 2^32 = t_sec t ->
  bv_unsigned a7 mod 2^32 = 3 -> st0 = Z_to_bv 64 F3 -> bv_unsigned st1 mod 2^32 = t_year t ->
  bytes_at ctusegs m F3 (zb (dec3 ms)) -> 232 <= F3 -> F3 + 3 <= lo -> F3 + 3 <= 2^63 ->
  exists o, zlength o = 24 + zdigits (t_year t) /\
    printf_call_okx m lo q A_C16 FMT_C16 [a2; a3; a4; a5; a6; a7; st0; st1]
      [PA_s (mon_str (t_mon t - 1)); PA_i (t_mday t); PA_i (t_hour t); PA_i (t_min t); PA_i (t_sec t); PA_i 3; PA_s (dec3 ms); PA_i (t_year t)] o.
Proof.
  intros until st1. intros MI SL TV MSR -> A3 A4 A5 A6 A7 -> S1 HF F0 FLO F63.
  pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS). pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
  destruct (mon_str_len (t_mon t - 1) ltac:(lia)) as [ML MR]. pose proof (mon_slack_ok (t_mon t - 1) ltac:(lia)) as [SK1 SK2].
  pose proof (dec3_bytes ms ltac:(lia)) as DR. assert (DL : zlength (dec3 ms) = 3) by reflexivity.
  destruct (printf_piecesx_C16 (mon_str (t_mon t - 1)) (t_mday t) (t_hour t) (t_min t) (t_sec t) (dec3 ms) (t_year t)
              ML ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite DL; lia) ltac:(lia)) as (ps & P).
  pose proof (printf_piecesx_count _ _ _ _ P) as L. pose proof (zdigits_le4 (t_year t) ltac:(lia)) as ZD. pose proof (zdigits_range (t_year t) ltac:(lia)) as ZR.
  exists (concat ps). split; [exact L|].
  split; [apply fmt_C16_at; exact MI|]. split; [exact fmt_bytes_C16|]. split; [exact pass1x_ok_C16|].
  split; [unfold A_C16, STATIC_SPLIT; change (zlength FMT_C16) with 34; lia|].
  split.
  { intros m' MU'. rewrite arg_covs_C16. unfold A_MON, STATIC_SPLIT in *. cbn [args_okx arg_okx arg_ok hd_cov tl].
    rewrite !unsigned_lit by lia. rewrite A3, A4, A5, A6, A7, S1. rewrite !(Z.mod_small _ (2^32)) by lia.
    split.
    { left. exists (mon_slack (t_mon t - 1)). split.
      { eapply bytes_at_transport; [apply mon_at; [exact MI| lia]| exact MU'|]. cbn [disjoint_from]. unfold zb. rewrite length_app, length_map. cbn [length].
        unfold zlength in *. split; [lia| exact I]. }
      split; [exact MR|]. rewrite ML. unfold zlength in *. lia. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split.
    { right. rewrite DL. split; [lia|]. split.
      { eapply bytes_at_transport; [exact HF| exact MU'|]. cbn [disjoint_from]. unfold zb. rewrite length_map. change (Z.of_nat (length (dec3 ms))) with 3. split; [lia| exact I]. }
      split; [exact DR|]. lia. }
    split; [lia| exact I]. }
  assert (MD : printf_modelx OUT_sn OUTFP_sn FMT_C16
            [PA_s (mon_str (t_mon t - 1)); PA_i (t_mday t); PA_i (t_hour t); PA_i (t_min t); PA_i (t_sec t); PA_i 3; PA_s (dec3 ms); PA_i (t_year t)] []
          = ITree.Ret (ITree.Exc.Ok (zlength (concat ps), concat ps))).
  { rewrite L at 1. apply (printf_modelx_sn _ _ _ _ P). rewrite L. unfold SN_CAP. lia. }
  split; [exact MD|].
  split; [apply fp_callsx_C16| unfold zlength in L; lia].
Qed.

End WithCeiling0.
