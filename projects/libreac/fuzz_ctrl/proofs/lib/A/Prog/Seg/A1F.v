(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names and addresses changed; 1348 of its 1450 lines of code are new or changed and 1100 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/A1.v; 137 of its 344 lines of code are new or changed and 1243 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/A1.v blob 458ad3d18e8a at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives A1.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of A1.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) form of the segment runs of Seg/A1.v (prologue 0x80edc-0x80f50 of LLVMFuzzerTestOneInput):
   a1_store_evt and a1_tail_evt are re-stepped with lib.Lib StepF as ExecF.evtF under a universally quantified
   footprint RNG, with the same binders, the same premises in the same order, the same post-state predicate, and
   one ExecF.rng premise per region the run reads or writes (instruction fetch is not an access). A1.v is
   unchanged.
   Run lemmas of A1.v (segment-runs-A.tsv row S_A1): a1_store_evt:97, a1_tail_evt:197, a1_req_evt:785,
   sl_run_lib:861. Two of the four get no _F:
   - a1_req_evt (:785) is the class-6 frame request at 0x80f50 on the callee contract Sm6.stack_malloc_6
     (A1.v:832, lib/A/Tk/AW/Sm6.v). __asan_stack_malloc_6 has no _F contract on the base or on a Theorem Labs lane's
     working branch 28b0af0a5b2, so that run stays plain: blocked, __asan_stack_malloc_6 has no _F.
   - sl_run_lib (:861) is not a machine run: it concludes SR, and its Exec.evt appears only as a premise. Its _F
     counterpart is the kit bridge (ProgBridge.fevt_of_evtF + YA0nR.SRr_fevt), not a re-stepped run. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Sm6.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_fsfree.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import A1.
(* Last but YK11: StepF's step / if_false / finish (evtF goals) shadow the evt engine's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11.getr (the register read A1.v's statements use) as the default. *)
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
(* BRIDGE (a Theorem Labs lane 08:56Z rule, statement case): the three _F statements below name the UL engine's Frame.mkR,
   in full path, not lib.Lib's: Seg/A1Fs.v:380-390 pins each of their types by constr_eq to a statement naming it. *)

Section S.
Context {fx : FPState}.

(* A1.v's stw, with the after-store goal matched as an ExecF.evtF: one `sd` of the prologue, whose store is inside
   the 416-byte window the carried wr_at covers. The script of each run is otherwise A1.v's, unchanged. *)
Ltac stw addr :=
  let HS := fresh "HS" in
  lazymatch goal with
  | HW : wr_at rsegs ?m ?base ?n |- _ =>
      assert (HS : store_ok rsegs m (wa addr) 8 = true)
        by (replace addr with (base + (addr - base)) by lia;
            apply (wr_at_store_ok rsegs m base n (addr - base) 8%nat HW); lia);
      step; clear HS;
      lazymatch goal with
      | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m2 ?c ?bs) _) =>
          apply (wr_at_write rsegs m2 base n c bs) in HW
      end
  end.

(* ---- a1_store_evt (A1.v:97), 0x80edc-0x80f14: sp = S - 416, `sd zero,0(sp)` and the 13 callee-saved registers
   at sp + 312 .. sp + 408. Every access is a write inside the slot stack window [S - 1048576, S) that the run's
   own `stk` premise names, so that window is the one rng premise. ---- *)
Lemma a1_store_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte) (S : Z),
  HIGHMEM_BEG <= S - 1048576 -> S < APPMEM_END ->
  stk rsegs mem (S - 1048576) S ->
  ExecF.rng RNG (S - 1048576) 1048576 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists mem',
       ms = MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 (S - 416)) gp tp t0 t1
         t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               fp_regs (Z_to_bv 64 0x80f18) fp_csr None mem' (seg_rom rsegs) /\
       munch [(S - 416, S)] mem mem' /\ wmono rsegs mem mem' /\
       stk rsegs mem' (S - 1048576) S /\
       bytes_at rsegs mem' (S - 104)
         (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
          le8 s1 ++ le8 s0 ++ le8 ra0))
    (MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1
      a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80edc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mem S
    HS1 HS2 HST RSTK.
  unfold HIGHMEM_BEG, APPMEM_END in HS1, HS2.
  assert (HW : wr_at rsegs mem (S - 416) 416).
  { destruct HST as (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (S - 416 + i) ltac:(lia))). }
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR.
  step.
  stw (S - 416).
  stw (S - 8).
  stw (S - 16).
  stw (S - 24).
  stw (S - 32).
  stw (S - 40).
  stw (S - 48).
  stw (S - 56).
  stw (S - 64).
  stw (S - 72).
  stw (S - 80).
  stw (S - 88).
  stw (S - 96).
  stw (S - 104).
  apply ExecF.evtF_done. eexists. split; [reflexivity|].
  split.
  { repeat (apply munch_write; [ | lia | rewrite ?length_le8; lia | cbn [inside]; left; rewrite ?length_le8; lia ]).
    apply munch_refl. }
  split.
  { repeat apply wmono_write. apply wmono_refl. }
  split.
  { repeat (apply stk_write; [ | lia | rewrite ?length_le8; lia ]). exact HST. }
  apply (proj2 (bytes_at_app rsegs _ (S - 104) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 104 + Z.of_nat 8) with (S - 96) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 96) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 96 + Z.of_nat 8) with (S - 88) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 88) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 88 + Z.of_nat 8) with (S - 80) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 80) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 80 + Z.of_nat 8) with (S - 72) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 72) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 72 + Z.of_nat 8) with (S - 64) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 64) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 64 + Z.of_nat 8) with (S - 56) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 56) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 56 + Z.of_nat 8) with (S - 48) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 48) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 48 + Z.of_nat 8) with (S - 40) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 40) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 40 + Z.of_nat 8) with (S - 32) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 32) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 32 + Z.of_nat 8) with (S - 24) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 24) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 24 + Z.of_nat 8) with (S - 16) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 16) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 16 + Z.of_nat 8) with (S - 8) by (cbn; lia).
  ba_one.
Qed.

(* ---- a1_tail_evt (A1.v:197), 0x80f18-0x80f4c: the two GOT loads (GOT_UAR -> UAR, GOT_CELL_K -> CELL_K), the
   switch word at UAR and the shadow offset at CELL_K. No memory is written, so the four cells its own bytes_at
   premises name are the whole footprint. ---- *)
Lemma a1_tail_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte) (S A : Z),
  HIGHMEM_BEG <= S - 1048576 -> S < APPMEM_END -> A = (S - 416) / 32 * 32 ->
  bytes_at rsegs mem GOT_UAR (le8 (wa UAR)) ->
  bytes_at rsegs mem GOT_CELL_K (le8 (wa CELL_K)) ->
  bytes_at rsegs mem UAR (le4 (wa 1)) ->
  bytes_at rsegs mem CELL_K (le8 (wa ASAN_K)) ->
  ExecF.rng RNG GOT_UAR 8 -> ExecF.rng RNG GOT_CELL_K 8 ->
  ExecF.rng RNG UAR 4 -> ExecF.rng RNG CELL_K 8 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists a1' a2',
       ms = MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 A) gp tp t0 t1 t2
         (Z_to_bv 64 S) (Z_to_bv 64 A)
                          (Z_to_bv 64 3136) a1' a2' a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 a0 a1 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
               fp_regs (Z_to_bv 64 0x80f50) fp_csr None mem (seg_rom rsegs))
    (MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 (S - 416)) gp tp t0 t1 t2 s0
      s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80f18) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mem S A
    HS1 HS2 HA HG1 HG2 HU HK RG1a RG2a RUa RKa.
  unfold HIGHMEM_BEG, APPMEM_END in HS1, HS2.
  pose proof (rd8 mem _ _ HG1 ltac:(apply length_le8)) as RG1.
  pose proof (rd8 mem _ _ HG2 ltac:(apply length_le8)) as RG2.
  pose proof (rd4 mem _ _ HU ltac:(apply length_le4)) as RU.
  pose proof (rd8 mem _ _ HK ltac:(apply length_le8)) as RK.
  unfold GOT_UAR, GOT_CELL_K, UAR, CELL_K in RG1, RG2, RU, RK.
  (* The same unfold on the footprint premises: StepF's access solver matches a literal access address against a
     [rng] hypothesis whose lo and len are literals, so the four cell names are numerals here too. *)
  unfold GOT_UAR, GOT_CELL_K, UAR, CELL_K in RG1a, RG2a, RUa, RKa.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR.
  step. step.
  replace (S - 416 + 416) with S by lia.
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (S - 416)) by lia.
  rewrite (land_align32 (S - 416)) by lia.
  rewrite <- HA.
  step. step. step. step. step. step. step. step. step.
  assert (E1 : sx32 (Z_to_bv 64 1) = Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
  step. rewrite E1. if_false.
  step. step.
  apply ExecF.evtF_done. eexists. eexists. reflexivity.
Qed.

(* ---- A1.a1_store_evt / A1.a1_tail_evt re-derived from the twins at ExecF.RNG_all. Each is the check that the
   _F statement is the old one plus the footprint premises, nothing weaker. ---- *)

Lemma a1_store_evt_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte) (S : Z),
  HIGHMEM_BEG <= S - 1048576 -> S < APPMEM_END ->
  stk rsegs mem (S - 1048576) S ->
  evt rsegs
    (fun ms => exists mem',
       ms = MS (Frame.mkR ra0 (Z_to_bv 64 (S - 416)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               fp_regs (Z_to_bv 64 0x80f18) fp_csr None mem' (seg_rom rsegs) /\
       munch [(S - 416, S)] mem mem' /\ wmono rsegs mem mem' /\
       stk rsegs mem' (S - 1048576) S /\
       bytes_at rsegs mem' (S - 104)
         (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
          le8 s1 ++ le8 s0 ++ le8 ra0))
    (MS (Frame.mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80edc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mem S
    HS1 HS2 HST.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (a1_store_evt_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mem S); try assumption.
  apply ExecF.rng_all; unfold HIGHMEM_BEG, APPMEM_END in *; lia.
Qed.

Lemma a1_tail_evt_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte) (S A : Z),
  HIGHMEM_BEG <= S - 1048576 -> S < APPMEM_END -> A = (S - 416) / 32 * 32 ->
  bytes_at rsegs mem GOT_UAR (le8 (wa UAR)) ->
  bytes_at rsegs mem GOT_CELL_K (le8 (wa CELL_K)) ->
  bytes_at rsegs mem UAR (le4 (wa 1)) ->
  bytes_at rsegs mem CELL_K (le8 (wa ASAN_K)) ->
  evt rsegs
    (fun ms => exists a1' a2',
       ms = MS (Frame.mkR ra0 (Z_to_bv 64 A) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 A)
                          (Z_to_bv 64 3136) a1' a2' a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 a0 a1 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
               fp_regs (Z_to_bv 64 0x80f50) fp_csr None mem (seg_rom rsegs))
    (MS (Frame.mkR ra0 (Z_to_bv 64 (S - 416)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80f18) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mem S A
    HS1 HS2 HA HG1 HG2 HU HK.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (a1_tail_evt_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mem S A); try assumption;
    apply ExecF.rng_all; unfold GOT_UAR, GOT_CELL_K, UAR, CELL_K; lia.
Qed.

(* ---- SPLIT STRETCH (spec (a working note, not in this delivery), a Theorem Labs lane 00:45Z) for a1_req_evt (A1.v:793): the class-6 frame request
   at 0x80f50 `jal __asan_stack_malloc_6`, whose callee has no _F of record. The pre stretch is the one jal
   instruction, ending at the callee entry state (pc = ASAN_STACK_MALLOC_6, ra = the return pc 0x80f54), as
   Seg/R15.v rfree_evt ends. The jal makes no data access, so no rng premise is appended. There is NO post
   stretch: the source run ends at the callee's own post (asan_stack_malloc_post is stated at the return pc
   0x80f54), so zero instructions run after the return; see the report and the A1F.rng.tsv callee_split row. ---- *)
Lemma a1_req_evt_pre_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp0 t0 t1 t2 s0v s1v a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte) (A lo FS : Z) (h : word) (flags : list byte)
         (DT TS C T DB : word) (k : Z),
  bv_unsigned tp0 = AC.as_tp AC.ASYMS ->
  0 <= A < 2 ^ 64 ->
  ro_agree rsegs mem ->
  asan_cells mem -> shadow_rw mem ->
  asan_tls_cells mem (AC.as_tp AC.ASYMS) DT TS C T DB k ->
  bytes_at rsegs mem (AC.as_tp AC.ASYMS) (le8 (Z_to_bv 64 FS)) ->
  fs_place mem FS -> 0x5fe000 <= FS -> FS + FS_SIZE <= 2 ^ 64 ->
  bytes_at rsegs mem (FS + 88) (le8 (Z_to_bv 64 20)) ->
  bytes_at rsegs mem (FS + 96) [Z_to_bv 8 0] ->
  bytes_at rsegs mem (fs_hint FS 6) (le8 h) ->
  bytes_at rsegs mem (fs_flag FS 6 0) flags -> Z.of_nat (length flags) = fs_M 6 ->
  Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
  stk rsegs mem lo A -> 0x5fe000 <= lo -> lo + ASAN_STACK_MALLOC_K <= A ->
  FS + FS_SIZE <= A - ASAN_STACK_MALLOC_K ->
  (forall a, A - ASAN_STACK_MALLOC_K <= a < A -> app_mem a) ->
  disjoint_from [(AC.as_tp AC.ASYMS - 88, AC.as_tp AC.ASYMS - 80);
                 (AC.as_tp AC.ASYMS - 8, AC.as_tp AC.ASYMS + 16);
                 (bv_unsigned DT + 8, bv_unsigned DT + 16);
                 (bv_unsigned TS + 8 * k, bv_unsigned TS + 8 * k + 8);
                 (bv_unsigned C + 152, bv_unsigned C + 160);
                 (bv_unsigned T + 48, bv_unsigned T + 64);
                 (bv_unsigned DB + 24, bv_unsigned DB + 32)] (A - ASAN_STACK_MALLOC_K) ASAN_STACK_MALLOC_K ->
  ExecF.evtF rsegs RNG
    (fun ms => ms = MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR (Z_to_bv 64 0x80f54)
      (Z_to_bv 64 A) gp tp0 t0 t1 t2 s0v s1v (Z_to_bv 64 3136)
                          a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6)
                 fp_regs (Z_to_bv 64 ASAN_STACK_MALLOC_6) fp_csr None mem (seg_rom rsegs))
    (MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 A) gp tp0 t0 t1 t2 s0v s1v
      (Z_to_bv 64 3136) a1v a2v a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80f50) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp0 t0 t1 t2 s0v s1v a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6
    mem A lo FS h flags DT TS C T DB k
    HTP HAr HRO HAC HSW HTLS HFSw HFSp HFSlo HFShi H88 H96 Hh Hfl Hfll Hfl01 HST HLOlo HLOK HROOM HAPP HDJ.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR.
  step.
  apply ExecF.evtF_done. reflexivity.
Qed.

(* A1.a1_req_evt from the pre stretch at RNG_all and the callee's own proved contract Sm6.stack_malloc_6, which
   the source applies (A1.v:832). Everything after the jal is the source script, unchanged. *)
Lemma a1_req_evt_of_pre_post :
  forall (ra0 gp tp0 t0 t1 t2 s0v s1v a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte) (A lo FS : Z) (h : word) (flags : list byte)
         (DT TS C T DB : word) (k : Z),
  bv_unsigned tp0 = AC.as_tp AC.ASYMS ->
  0 <= A < 2 ^ 64 ->
  ro_agree rsegs mem ->
  asan_cells mem -> shadow_rw mem ->
  asan_tls_cells mem (AC.as_tp AC.ASYMS) DT TS C T DB k ->
  bytes_at rsegs mem (AC.as_tp AC.ASYMS) (le8 (Z_to_bv 64 FS)) ->
  fs_place mem FS -> 0x5fe000 <= FS -> FS + FS_SIZE <= 2 ^ 64 ->
  bytes_at rsegs mem (FS + 88) (le8 (Z_to_bv 64 20)) ->
  bytes_at rsegs mem (FS + 96) [Z_to_bv 8 0] ->
  bytes_at rsegs mem (fs_hint FS 6) (le8 h) ->
  bytes_at rsegs mem (fs_flag FS 6 0) flags -> Z.of_nat (length flags) = fs_M 6 ->
  Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
  stk rsegs mem lo A -> 0x5fe000 <= lo -> lo + ASAN_STACK_MALLOC_K <= A ->
  FS + FS_SIZE <= A - ASAN_STACK_MALLOC_K ->
  (forall a, A - ASAN_STACK_MALLOC_K <= a < A -> app_mem a) ->
  disjoint_from [(AC.as_tp AC.ASYMS - 88, AC.as_tp AC.ASYMS - 80);
                 (AC.as_tp AC.ASYMS - 8, AC.as_tp AC.ASYMS + 16);
                 (bv_unsigned DT + 8, bv_unsigned DT + 16);
                 (bv_unsigned TS + 8 * k, bv_unsigned TS + 8 * k + 8);
                 (bv_unsigned C + 152, bv_unsigned C + 160);
                 (bv_unsigned T + 48, bv_unsigned T + 64);
                 (bv_unsigned DB + 24, bv_unsigned DB + 32)] (A - ASAN_STACK_MALLOC_K) ASAN_STACK_MALLOC_K ->
  evt rsegs
    (fun ms => exists s0,
       asan_stack_malloc_post 6 ASAN_STACK_MALLOC_K (Z_to_bv 64 0x80f54) (Z_to_bv 64 A) gp tp0 s0v s1v
         s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 fp_regs fp_csr 3136 FS h flags lo (normalize rsegs mem) s0 /\
       ms_rel rsegs ms s0 /\ ro_same rsegs mem (ms_mem ms))
    (MS (Frame.mkR ra0 (Z_to_bv 64 A) gp tp0 t0 t1 t2 s0v s1v (Z_to_bv 64 3136) a1v a2v a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80f50) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 gp tp0 t0 t1 t2 s0v s1v a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6
    mem A lo FS h flags DT TS C T DB k
    HTP HAr HRO HAC HSW HTLS HFSw HFSp HFSlo HFShi H88 H96 Hh Hfl Hfll Hfl01 HST HLOlo HLOK HROOM HAPP HDJ.
  eapply evt_cut.
  { apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    apply (a1_req_evt_pre_F ExecF.RNG_all ra0 gp tp0 t0 t1 t2 s0v s1v a1v a2v a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6 mem A lo FS h flags DT TS C T DB k);
      assumption. }
  intros ms' ->.
  pose proof (mem_rel_normalize rsegs mem HRO) as REL.
  assert (HC : evt rsegs
      (asan_stack_malloc_post 6 ASAN_STACK_MALLOC_K (Z_to_bv 64 0x80f54) (Z_to_bv 64 A) gp tp0 s0v s1v
         s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 fp_regs fp_csr (bv_unsigned (Z_to_bv 64 3136)) FS h flags lo
         (normalize rsegs mem))
      (MS (Frame.mkR (Z_to_bv 64 0x80f54) (Z_to_bv 64 A) gp tp0 t0 t1 t2 s0v s1v (Z_to_bv 64 3136)
                     a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6)
          fp_regs (Z_to_bv 64 ASAN_STACK_MALLOC_6) fp_csr None (normalize rsegs mem) (seg_rom rsegs))).
  { apply (Sm6.stack_malloc_6 (Z_to_bv 64 0x80f54) (Z_to_bv 64 A) gp tp0 t0 t1 t2 s0v s1v (Z_to_bv 64 3136)
             a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6 fp_regs fp_csr
             (normalize rsegs mem) lo FS h DT TS C T DB k flags).
    all: rewrite ?(MState.unsigned_lit 3136), ?(MState.unsigned_lit A), ?HTP by lia.
    - unfold fs_B. cbn. lia.
    - reflexivity.
    - exact (asan_cells_rel mem _ REL HAC).
    - exact (shadow_rw_rel mem _ REL HSW).
    - apply mem_inv_normalize.
    - exact (asan_tls_cells_rel mem _ _ _ _ _ _ _ _ REL HTLS).
    - intros Hc. lia.
    - apply (ba_rel1 mem _ _ _ REL); exact HFSw.
    - exact (fs_place_rel mem _ FS REL HFSlo HFShi HFSp).
    - apply (ba_rel1 mem _ _ _ REL); exact H88.
    - apply (ba_rel1 mem _ _ _ REL); exact H96.
    - apply (ba_rel1 mem _ _ _ REL); exact Hh.
    - apply (ba_rel1 mem _ _ _ REL); exact Hfl.
    - exact Hfll.
    - exact Hfl01.
    - exact (stk_rel_hi mem _ lo A REL HLOlo ltac:(lia) HST).
    - exact HLOK.
    - exact HROOM.
    - exact HAPP.
    - exact HDJ. }
  rewrite (MState.unsigned_lit 3136 ltac:(lia)) in HC.
  exact (evt_normalize rsegs _ _ fp_regs _ fp_csr None mem (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC).
Qed.

(* The pins: each _of_F states A1.v's text term for term (constr_eq: syntactic, not up to conversion). *)
Lemma a1_store_evt_of_F_verbatim : True.
Proof.
  let A := type of A1.a1_store_evt in let B := type of a1_store_evt_of_F in constr_eq A B; exact I.
Qed.

Lemma a1_tail_evt_of_F_verbatim : True.
Proof.
  let A := type of A1.a1_tail_evt in let B := type of a1_tail_evt_of_F in constr_eq A B; exact I.
Qed.

Lemma a1_req_evt_of_pre_post_verbatim : True.
Proof.
  let A := type of A1.a1_req_evt in let B := type of a1_req_evt_of_pre_post in constr_eq A B; exact I.
Qed.

End S.
