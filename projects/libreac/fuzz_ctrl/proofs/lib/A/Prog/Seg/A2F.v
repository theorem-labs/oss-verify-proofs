(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 358 of its 400 lines of code are new or changed and 354 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/A2.v; 91 of its 142 lines of code are new or changed and 349 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/A2.v 283929a6248b (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives A2.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of A2.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) form of the two segment runs of Seg/A2.v (0x80f54-0x80f88 of LLVMFuzzerTestOneInput, the two
   arms after the class-6 frame request): a2_real_evt and a2_side_evt re-stepped with lib.Lib StepF as ExecF.evtF
   under a universally quantified footprint RNG, with the same binders, the same premises in the same order, the
   same post-state predicate, and one ExecF.rng premise per region the run reads or writes (instruction fetch is
   not an access). A2.v is unchanged apart from comment text.
   Run lemmas of A2.v (segment-runs-A.tsv row S_A2): a2_real_evt:184, a2_side_evt:221. Both are re-run here.
   a2_real_evt's one access is the probe store `sd zero,0(sp)` at 0x80f7c, the region its own ULMem.wr_at premise
   names; a2_side_evt touches no memory, so it gets no rng premise. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import A2.
(* Last but YK11: StepF's step / if_false / finish (evtF goals) shadow the UL engine's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11.getr (the register read A2.v's statements use) as the default. *)
Import YK11.
Open Scope Z_scope.

Module UE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.
Module LEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
(* A2.v's statements are the UL engine's: UL Exec.evt over UL MState.MS, with UL Mem's le8 (checked by Locate in
   this file's import context, where StepF's Require Export rebinds the bare names to lib.Lib's). StepF steps
   lib.Lib's MS, and the two MS are the same record by delta (A3.v:90 ms_ul_lib). So the twins state LMS.MS and
   the corollaries state A2.v's own constants, UE.evt and the UL engine's MState.MS / Mem.le8 (written in full
   path), which the pins check. *)
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
(* The core copy an _F statement names (a Theorem Labs lane 08:56Z rule): LMem (lib.Lib's Mem), LPE (lib.Lib's PropExec).
   BRIDGE: the premises `getr regs 2` / `getr regs 10` of a2_real_evt_F and `getr regs 10` of a2_side_evt_F keep
   A2.v's copy (lib.A.Reusable.YK11), in full path: each proof rewrites them into A2.mkR_of_expand's register map
   (`rewrite Hr2, Hr10`), which names that copy; with lib.Lib's getr the rewrite finds no subterm. *)
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.

(* ---- Engine glue, as A3.v:77-88 proves it for the same two modules: lib.Lib's mstep and the UL engine's mstep
   are the same relation (both `ms_svc_pending ms = None /\ RiscvSemantics.step rsegs ms = MachineOk ms'`), so a
   lib.Lib run is a UL run. ExecF.evtF_evt lands in lib.Lib Exec.evt; A2.v's runs are UL Exec.evt, so each
   corollary goes through a2F_evtF_evt. ---- *)
Section Glue.
Context {fx : FPState}.

Lemma a2F_msteps_ul : forall s s', LEx.msteps rsegs s s' -> UE.msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply UE.msteps_refl|].
  eapply UE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma a2F_evtF_evt : forall RNG (Q : machine_state -> Prop) ms,
  ExecF.evtF rsegs RNG Q ms -> UE.evt rsegs Q ms.
Proof.
  intros RNG Q ms H. destruct (ExecF.evtF_evt rsegs RNG Q ms H) as (ms' & Hs & HQ).
  exists ms'. split; [exact (a2F_msteps_ul _ _ Hs) | exact HQ].
Qed.

End Glue.

Section S.
Context {fx : FPState}.

(* ---- a2_real_evt (A2.v:184), the real-stack arm 0x80f54-0x80f88 (a0 = 0). The one access is the probe store at
   0x80f7c into [A - 4096, A - 4088), the region the run's own ULMem.wr_at premise names. ---- *)
Lemma a2_real_evt_F : forall (RNG : ExecF.footprint) regs mem A,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2 = Z_to_bv 64 A ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 10 = Z_to_bv 64 0 ->
  0x5fe000 <= A - 4096 -> A < 2 ^ 63 -> A mod 32 = 0 ->
  LMem.wr_at rsegs mem (A - 4096) 8 ->
  ExecF.rng RNG (A - 4096) 8 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LMS.MS R fp_regs pc' fp_csr None mem' (LPE.seg_rom rsegs) /\
     pc' = Z_to_bv 64 0x80f88 /\ mem' = write_to_mem mem (LMem.wa (A - 4096)) (le8 (Z_to_bv 64 0)) /\
     LPE.getr R 2 = Z_to_bv 64 (A - 3136) /\ LPE.getr R 22 = Z_to_bv 64 (A - 3136) /\ LPE.getr R 21 = Z_to_bv 64 0 /\
     LPE.getr R 3 = LPE.getr regs 3 /\ LPE.getr R 4 = LPE.getr regs 4 /\ LPE.getr R 8 = LPE.getr regs 8 /\
     LPE.getr R 9 = LPE.getr regs 9 /\ LPE.getr R 23 = LPE.getr regs 23 /\ LPE.getr R 24 = LPE.getr regs 24 /\
     LPE.getr R 26 = LPE.getr regs 26)
    (LMS.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x80f54) fp_csr None mem (LPE.seg_rom rsegs)).
Proof.
  intros RNG regs mem A Hr2 Hr10 HA1 HA2 HAm Hwr RPR.
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_store_ok rsegs mem (A - 4096) 8 0 8 Hwr
    ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS.
  rewrite mkR_of_expand. rewrite Hr2, Hr10.
  (* StepF's simp_regs reads the explicit 31-slot map, where the UL engine's unfolds mkR itself (Seg/A1F.v does
     the same unfold before its first step). *)
  unfold Frame.mkR.
  (* 0x80f54 mv s5,a0 ; j ; mv s6,s5 ; bnez s5 (s5 = 0, not taken) *)
  step. step. step. step. if_false.
  (* 0x80f68 addi ; addi ; andi s6,a0,-32 = A - 3136 *)
  step. step. step.
  rewrite ?(MState.unsigned_lit (A + -3136)) by lia.
  rewrite (land_align32 (A + -3136)) by lia.
  replace ((A + -3136) / 32 * 32) with (A - 3136) by (Z.div_mod_to_equations; lia).
  (* 0x80f74 lui a0,0x1 ; 0x80f78 sub sp,sp,a0 = A - 4096 *)
  step. step.
  rewrite ?(MState.unsigned_lit A) by lia.
  (* 0x80f7c sd zero,0(sp) ; 0x80f80 blt s6,sp (A - 3136 < A - 4096 is false) *)
  step. step.
  assert (HL : bv_lts (Z_to_bv 64 (A - 3136)) (Z_to_bv 64 (A - 4096)) = false)
    by (unfold bv_lts; rewrite !signed_lit by lia; apply Z.ltb_ge; lia).
  rewrite HL. cbv_concl_iota.
  (* 0x80f84 mv sp,s6 *)
  step.
  finish.
  all: simp_regs; reflexivity.
Qed.

(* ---- a2_side_evt (A2.v:221), the side-stack arm 0x80f54-0x80f88 (a0 = r <> 0): mv s5,a0 ; j ; mv s6,s5 ;
   bnez s5 (taken). Register-only, no memory access, so no rng premise. ---- *)
Lemma a2_side_evt_F : forall (RNG : ExecF.footprint) regs mem r,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 10 = Z_to_bv 64 r ->
  bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 0) = false ->
  ExecF.evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LMS.MS R fp_regs pc' fp_csr None mem' (LPE.seg_rom rsegs) /\
     pc' = Z_to_bv 64 0x80f88 /\ mem' = mem /\ LPE.getr R 22 = Z_to_bv 64 r /\ LPE.getr R 21 = Z_to_bv 64 r /\
     LPE.getr R 2 = LPE.getr regs 2 /\ LPE.getr R 3 = LPE.getr regs 3 /\ LPE.getr R 4 = LPE.getr regs 4 /\
     LPE.getr R 8 = LPE.getr regs 8 /\ LPE.getr R 9 = LPE.getr regs 9 /\ LPE.getr R 23 = LPE.getr regs 23 /\
     LPE.getr R 24 = LPE.getr regs 24 /\ LPE.getr R 26 = LPE.getr regs 26)
    (LMS.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x80f54) fp_csr None mem (LPE.seg_rom rsegs)).
Proof.
  intros RNG regs mem r Hr10 E.
  rewrite mkR_of_expand. rewrite Hr10.
  unfold Frame.mkR.
  step. step. step. step.
  rewrite E. cbn [negb]. cbv_concl_iota.
  finish.
  all: simp_regs; reflexivity.
Qed.

(* ---- A2.a2_real_evt / A2.a2_side_evt re-derived from the twins at ExecF.RNG_all. ---- *)

Lemma a2_real_evt_of_F : forall regs mem A,
  getr regs 2 = Z_to_bv 64 A -> getr regs 10 = Z_to_bv 64 0 ->
  0x5fe000 <= A - 4096 -> A < 2 ^ 63 -> A mod 32 = 0 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at rsegs mem (A - 4096) 8 ->
  UE.evt rsegs (fun ms => exists R pc' mem',
     ms = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS R fp_regs pc' fp_csr None mem'
       (seg_rom rsegs) /\
     pc' = Z_to_bv 64 0x80f88 /\
     mem' = write_to_mem mem (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa (A - 4096))
     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.le8 (Z_to_bv 64 0)) /\
     getr R 2 = Z_to_bv 64 (A - 3136) /\ getr R 22 = Z_to_bv 64 (A - 3136) /\ getr R 21 = Z_to_bv 64 0 /\
     getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\
     getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS (Regs6ss.mkR_of regs) fp_regs
       (Z_to_bv 64 0x80f54) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem A Hr2 Hr10 HA1 HA2 HAm Hwr.
  apply (a2F_evtF_evt ExecF.RNG_all).
  (* A2.v's MS and lib.Lib's are the same record by delta (A3.v:90 ms_ul_lib); the twin states the latter. *)
  change OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS with LMS.MS.
  apply (a2_real_evt_F ExecF.RNG_all regs mem A); try assumption.
  apply ExecF.rng_all; lia.
Qed.

Lemma a2_side_evt_of_F : forall regs mem r,
  getr regs 10 = Z_to_bv 64 r -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 0) = false ->
  UE.evt rsegs (fun ms => exists R pc' mem',
     ms = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS R fp_regs pc' fp_csr None mem'
       (seg_rom rsegs) /\
     pc' = Z_to_bv 64 0x80f88 /\ mem' = mem /\ getr R 22 = Z_to_bv 64 r /\ getr R 21 = Z_to_bv 64 r /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
     getr R 9 = getr regs 9 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS (Regs6ss.mkR_of regs) fp_regs
       (Z_to_bv 64 0x80f54) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem r Hr10 E.
  apply (a2F_evtF_evt ExecF.RNG_all).
  change OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS with LMS.MS.
  apply (a2_side_evt_F ExecF.RNG_all regs mem r); assumption.
Qed.

(* The pins: each _of_F states A2.v's text term for term (constr_eq: syntactic, not up to conversion). *)
Lemma a2_real_evt_of_F_verbatim : True.
Proof.
  let A := type of A2.a2_real_evt in let B := type of a2_real_evt_of_F in constr_eq A B; exact I.
Qed.

Lemma a2_side_evt_of_F_verbatim : True.
Proof.
  let A := type of A2.a2_side_evt in let B := type of a2_side_evt_of_F in constr_eq A B; exact I.
Qed.

End S.
