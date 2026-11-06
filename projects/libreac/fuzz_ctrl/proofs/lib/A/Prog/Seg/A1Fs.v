(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names and addresses changed; 1348 of its 1450 lines of code are new or changed and 1100 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/A1.v; 179 of its 338 lines of code are new or changed and 1291 lines of the source are left out. *)
(* lib/A/Prog/Seg/A1Fs.v -- NARROWED footprint (_Fs) forms of the prologue runs of Seg/A1F.v (0x80edc-0x80f50 of
   LLVMFuzzerTestOneInput, fuzz_ctrl image A, libreac v1.9.0), each with a proved PIN that re-derives a Theorem Labs lane's
   _F lemma from it, and the one composite run the stage glue lib/A/ACtlG/A1.v lifts.  Written by a Theorem Labs
   lane under a Theorem Labs lane's narrowing rule (any split / run of a Theorem Labs lane's may be narrowed by the stage's
   glue owner in its own new file, with a proved pin back to a Theorem Labs lane's lemma; relayed by a Theorem Labs lane, 2026-10-29).
   rule 24: no function proved (segment runs of a walk).

   WHY NARROWED (measured on the glue base 46eb24cd4b3)
   - a1_store_evt_F (A1F.v:68) states `stk rsegs mem (S - 1048576) S` and `rng RNG (S - 1048576) 1048576`: the
     source's slot stack window of 1 MiB.  The walk's journal gives presence and visibility only for the LLVMF
     window [c_sp - LLVMF_STK, c_sp), LLVMF_STK = 32768 (A/ACfn.v:25, YCbq.v ajournal), and the run writes only
     [S - 416, S).  a1_store_evt_Fs takes the window's low end lo as a binder (0 <= lo, lo + 416 <= S) and the
     footprint of the 14 stores, rng (S - 416) 416.  Its script is A1F.v's, unchanged.
   - a1_tail_evt_F (A1F.v:148) states `S < APPMEM_END`; the core's pre gives only S <= APPMEM_END (afn_pre's
     astk_ok, sp0 <= ly_stk_hi <= kHighMemEnd = APPMEM_END; a Theorem Labs lane's ruling, batch 4: PREFC / FRAC / FRAHC
     state c_sp <= APPMEM_END).  a1_tail_evt_Fs takes S <= APPMEM_END; its script is A1F.v's, unchanged.
   - a1_req_evt_pre_F (A1F.v:255) is ONE jal and carries the source run's whole premise list (TLS cells, fake-stack
     place, ...), none of which the jal reads.  a1_jal_Fs states the jal alone, for any sp and a0.
   PINS: a1_store_evt_F_of_Fs, a1_tail_evt_F_of_Fs, a1_req_evt_pre_F_of_Fs state A1F's three lemmas; the
   *_verbatim checks below assert by constr_eq that each pin's type IS the A1F lemma's type, term for term.

   COMPOSITE: a1_pro_Fs = store ; tail ; jal, from 0x80edc (sp = S) to the callee entry ASAN_STACK_MALLOC_6 with
   ra = 0x80f54, sp = A = (S - 416) / 32 * 32, s0 = S, s1 = A, a0 = 3136, s7 / s8 = the entry a0 / a1, s10 = ASAN_K;
   memory: munch [(S - 416, S)], wmono, the window kept present, and the 13 saved registers at [S - 104, S).  The
   four runtime cells are read on the entry memory (the stores do not touch them: they lie below 0x5fe000).

   Imports: A1F.v's block, verbatim (a run file of the Seg family; the glue that Requires this file Requires it
   QUALIFIED).  BUILD STATE: see lib/A/ACtlG/A1.v's header. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require A1F.
(* Last but YK11: StepF's step / if_false / finish (evtF goals) shadow the evt engine's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11.getr (the register read A1.v's statements use) as the default. *)
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.

Section S.
Context {fx : FPState}.

(* A1F.v:51-63's stw, verbatim (an Ltac of A1F's Section S, which does not survive its End): one `sd` of the
   prologue, whose store is inside the 416-byte window the carried wr_at covers. *)
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

(* ---- a1_store_evt (A1.v:97), narrowed: the slot window [lo, S) instead of [S - 1048576, S), the footprint of the
   14 stores [S - 416, S) instead of the whole window, S <= APPMEM_END.  Script: A1F.v:91-142, with its stw. ---- *)
Lemma a1_store_evt_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte) (S lo : Z),
  0 <= lo -> lo + 416 <= S -> S <= APPMEM_END ->
  stk rsegs mem lo S ->
  ExecF.rng RNG (S - 416) 416 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists mem',
       ms = MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 (S - 416)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               fp_regs (Z_to_bv 64 0x80f18) fp_csr None mem' (seg_rom rsegs) /\
       munch [(S - 416, S)] mem mem' /\ wmono rsegs mem mem' /\
       stk rsegs mem' lo S /\
       bytes_at rsegs mem' (S - 104)
         (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
          le8 s1 ++ le8 s0 ++ le8 ra0))
    (MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80edc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mem S lo
    Hlo HlS HS2 HST RSTK.
  unfold APPMEM_END in HS2.
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

(* ---- a1_tail_evt (A1.v:197), narrowed: S <= APPMEM_END instead of S < APPMEM_END.  Script: A1F.v:169-190. ---- *)
Lemma a1_tail_evt_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte) (S A : Z),
  HIGHMEM_BEG <= S - 1048576 -> S <= APPMEM_END -> A = (S - 416) / 32 * 32 ->
  bytes_at rsegs mem GOT_UAR (le8 (wa UAR)) ->
  bytes_at rsegs mem GOT_CELL_K (le8 (wa CELL_K)) ->
  bytes_at rsegs mem UAR (le4 (wa 1)) ->
  bytes_at rsegs mem CELL_K (le8 (wa ASAN_K)) ->
  ExecF.rng RNG GOT_UAR 8 -> ExecF.rng RNG GOT_CELL_K 8 ->
  ExecF.rng RNG UAR 4 -> ExecF.rng RNG CELL_K 8 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists a1' a2',
       ms = MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 A) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 A)
                          (Z_to_bv 64 3136) a1' a2' a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 a0 a1 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
               fp_regs (Z_to_bv 64 0x80f50) fp_csr None mem (seg_rom rsegs))
    (MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 (S - 416)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
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

(* ---- the jal at 0x80f50 (A1F.v:255-296's one step), for any sp and a0: it reads no memory. ---- *)
Lemma a1_jal_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp0 t0 t1 t2 s0v s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte),
  ExecF.evtF rsegs RNG
    (fun ms => ms = MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR (Z_to_bv 64 0x80f54) sp gp tp0 t0 t1 t2 s0v s1v a0v
                          a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6)
                 fp_regs (Z_to_bv 64 ASAN_STACK_MALLOC_6) fp_csr None mem (seg_rom rsegs))
    (MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 sp gp tp0 t0 t1 t2 s0v s1v a0v a1v a2v a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80f50) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp0 t0 t1 t2 s0v s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6
    mem.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR.
  step.
  apply ExecF.evtF_done. reflexivity.
Qed.

(* ---- the composite the glue lifts: 0x80edc -> ASAN_STACK_MALLOC_6 (ra = 0x80f54). ---- *)
Lemma a1_pro_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte) (S lo : Z),
  HIGHMEM_BEG <= S - 1048576 -> S <= APPMEM_END -> 0 <= lo -> lo + 416 <= S ->
  stk rsegs mem lo S ->
  bytes_at rsegs mem GOT_UAR (le8 (wa UAR)) ->
  bytes_at rsegs mem GOT_CELL_K (le8 (wa CELL_K)) ->
  bytes_at rsegs mem UAR (le4 (wa 1)) ->
  bytes_at rsegs mem CELL_K (le8 (wa ASAN_K)) ->
  ExecF.rng RNG (S - 416) 416 ->
  ExecF.rng RNG GOT_UAR 8 -> ExecF.rng RNG GOT_CELL_K 8 ->
  ExecF.rng RNG UAR 4 -> ExecF.rng RNG CELL_K 8 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists mem' a1' a2',
       ms = MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR (Z_to_bv 64 0x80f54) (Z_to_bv 64 ((S - 416) / 32 * 32)) gp tp t0 t1 t2 (Z_to_bv 64 S)
                          (Z_to_bv 64 ((S - 416) / 32 * 32)) (Z_to_bv 64 3136) a1' a2' a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 a0 a1 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
               fp_regs (Z_to_bv 64 ASAN_STACK_MALLOC_6) fp_csr None mem' (seg_rom rsegs) /\
       munch [(S - 416, S)] mem mem' /\ wmono rsegs mem mem' /\
       stk rsegs mem' lo S /\
       bytes_at rsegs mem' (S - 104)
         (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
          le8 s1 ++ le8 s0 ++ le8 ra0))
    (MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80edc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mem S lo
    HS1 HS2 Hlo HlS HST HG1 HG2 HU HK RST RG1 RG2 RU RK.
  eapply ExecF.evtF_cut.
  { exact (a1_store_evt_Fs RNG ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 mem S lo Hlo HlS HS2 HST RST). }
  intros ms (mem' & -> & MU & WM & HST' & HSV).
  (* the four cells lie below the image top, the stores at or above S - 416 > 0x5fe000 *)
  assert (Hdj : forall a n, 0 <= a -> a + n <= 0x5fe000 -> disjoint_from [(S - 416, S)] a n).
  { intros a n H0 H1. unfold HIGHMEM_BEG in HS1. cbn [disjoint_from]. split; [left; lia | exact I]. }
  assert (HG1' : bytes_at rsegs mem' GOT_UAR (le8 (wa UAR))).
  { apply (bytes_at_transport rsegs [(S - 416, S)] mem mem' _ _ HG1 MU). apply Hdj;
      rewrite ?length_le8; unfold GOT_UAR; cbn; lia. }
  assert (HG2' : bytes_at rsegs mem' GOT_CELL_K (le8 (wa CELL_K))).
  { apply (bytes_at_transport rsegs [(S - 416, S)] mem mem' _ _ HG2 MU). apply Hdj;
      rewrite ?length_le8; unfold GOT_CELL_K; cbn; lia. }
  assert (HU' : bytes_at rsegs mem' UAR (le4 (wa 1))).
  { apply (bytes_at_transport rsegs [(S - 416, S)] mem mem' _ _ HU MU). apply Hdj;
      rewrite ?length_le4; unfold UAR; cbn; lia. }
  assert (HK' : bytes_at rsegs mem' CELL_K (le8 (wa ASAN_K))).
  { apply (bytes_at_transport rsegs [(S - 416, S)] mem mem' _ _ HK MU). apply Hdj;
      rewrite ?length_le8; unfold CELL_K; cbn; lia. }
  eapply ExecF.evtF_cut.
  { exact (a1_tail_evt_Fs RNG ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 mem' S ((S - 416) / 32 * 32) HS1 HS2 eq_refl HG1' HG2' HU' HK' RG1 RG2 RU RK). }
  intros ms (a1' & a2' & ->).
  eapply ExecF.evtF_cut.
  { exact (a1_jal_Fs RNG ra0 (Z_to_bv 64 ((S - 416) / 32 * 32)) gp tp t0 t1 t2 (Z_to_bv 64 S)
             (Z_to_bv 64 ((S - 416) / 32 * 32)) (Z_to_bv 64 3136) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 a0 a1 s9
             (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6 mem'). }
  intros ms ->.
  apply ExecF.evtF_done. exists mem', a1', a2'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact HST' | exact HSV].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   THE PINS: A1F's three lemmas, re-derived from the narrowed ones (statements copied from A1F.v; the _verbatim
   checks assert that each is A1F's own type, term for term). *)
Lemma a1_store_evt_F_of_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte) (S : Z),
  HIGHMEM_BEG <= S - 1048576 -> S < APPMEM_END ->
  stk rsegs mem (S - 1048576) S ->
  ExecF.rng RNG (S - 1048576) 1048576 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists mem',
       ms = MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 (S - 416)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               fp_regs (Z_to_bv 64 0x80f18) fp_csr None mem' (seg_rom rsegs) /\
       munch [(S - 416, S)] mem mem' /\ wmono rsegs mem mem' /\
       stk rsegs mem' (S - 1048576) S /\
       bytes_at rsegs mem' (S - 104)
         (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
          le8 s1 ++ le8 s0 ++ le8 ra0))
    (MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80edc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mem S
    HS1 HS2 HST RSTK.
  apply (a1_store_evt_Fs RNG ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 mem S (S - 1048576)); [unfold HIGHMEM_BEG in HS1; lia | lia | lia | exact HST |].
  apply (ExecF.rng_sub RNG (S - 1048576) 1048576); [exact RSTK | lia | lia].
Qed.

Lemma a1_tail_evt_F_of_Fs :
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
       ms = MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 A) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 A)
                          (Z_to_bv 64 3136) a1' a2' a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 a0 a1 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
               fp_regs (Z_to_bv 64 0x80f50) fp_csr None mem (seg_rom rsegs))
    (MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 (S - 416)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80f18) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mem S A
    HS1 HS2.
  apply (a1_tail_evt_Fs RNG ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 mem S A HS1 ltac:(lia)).
Qed.

Lemma a1_req_evt_pre_F_of_Fs :
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
    (fun ms => ms = MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR (Z_to_bv 64 0x80f54) (Z_to_bv 64 A) gp tp0 t0 t1 t2 s0v s1v (Z_to_bv 64 3136)
                          a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6)
                 fp_regs (Z_to_bv 64 ASAN_STACK_MALLOC_6) fp_csr None mem (seg_rom rsegs))
    (MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra0 (Z_to_bv 64 A) gp tp0 t0 t1 t2 s0v s1v (Z_to_bv 64 3136) a1v a2v a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80f50) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp0 t0 t1 t2 s0v s1v a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6
    mem A lo FS h flags DT TS C T DB k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  exact (a1_jal_Fs RNG ra0 (Z_to_bv 64 A) gp tp0 t0 t1 t2 s0v s1v (Z_to_bv 64 3136) a1v a2v a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6 mem).
Qed.

Lemma a1_store_evt_F_of_Fs_verbatim : True.
Proof.
  let A := type of A1F.a1_store_evt_F in let B := type of a1_store_evt_F_of_Fs in constr_eq A B; exact I.
Qed.

Lemma a1_tail_evt_F_of_Fs_verbatim : True.
Proof.
  let A := type of A1F.a1_tail_evt_F in let B := type of a1_tail_evt_F_of_Fs in constr_eq A B; exact I.
Qed.

Lemma a1_req_evt_pre_F_of_Fs_verbatim : True.
Proof.
  let A := type of A1F.a1_req_evt_pre_F in let B := type of a1_req_evt_pre_F_of_Fs in constr_eq A B; exact I.
Qed.

End S.
