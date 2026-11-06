(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: satisfiability witnesses for the hypotheses image B's ARx SEG_EXIT
   (lib/B/W_LLVMFuzzerTestOneInput_exit_x.v) exports and the AR text did not have, at TWO instances where cut_x's
   HP0 (`ARx ly S Hp W mem md -> Hp = []`) ALSO holds, so each instance satisfies the Section as a whole:
   (1) Section ar0, ARx := W_journal_x.v's ARi0 = AR /\ Hp = [] (a Theorem Labs lane's HP0 ruling), PST := []:
     HP0 (ARi0_hp0), HPST, BLKN / BLKM (AR's al_blocks, MALLOC_MAX = 2 ^ 28), WFL (WFx := Wf (as_universe B),
     AR's am_wf) and SFREE (the kit's W_frame_x.v:1008 SFREE_AR, from model_laws).
   (2) Section cf, the consumer's own instance: ARx := ARcf segs B /\ Hp = [] (bint-fp2 9dbe30ddcba
     lib/B/W_LLVMFuzzerTestOneInput_top_x.v:93 ARX), PST := [], at ANY cf parameters (generic in {ci} {cp}):
     HP0 (proj2), HPST, BLKN / BLKM (YG0dcf.v alc_blocks + YG08cf.v:68 cf_malloc_max_bound), WFL (WFx := Wf_cf,
     YGcallcf.v:116 ARx_wf_law_cf_x) and SFREE (YG05cf.v:109 stack_free_ok_cf).  Its one premise LCF : AR_laws_cf
     segs B is the laws record, proved for fuzz_reply's image B as bint-fp2's Reusable/YG0lawscf.v:26 AR_laws_ok_cf.
   (A first version of this file witnessed at ARi = AR with Hp ignored, where HP0 is false; the fresh review of
   2026-10-29 found that, and this file now uses only instances where HP0 holds.)
   The hypotheses the conversion carries over unchanged (XR_HGM, XRF_ERRNO, HG_SL, GWR, XRF_ROM_OUT, AZS_s) are
   witnessed at B's concrete global set in lib/B/W_bx_inst.v, which this lane proved for the AR segment; their ARx
   texts are the same propositions, none of which mentions AR. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_shadow_pin W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_frame_x W_contract_x W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_bx_defs.
(* RelocB's sink-instance guard, after every Import of YE2k: no sink class is a hint after it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.

Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG0ncf YG0dcf YG05cf YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcallcf.

Section ar0.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis ML : model_laws (as_universe B).
Local Notation ARi0 := (W_journal_x.ARi0 segs B).

Lemma bxi_HP0_ar0 : forall ly S Hp (W : world segs) mem md, ARi0 ly S Hp W mem md -> Hp = [].
Proof. exact (W_journal_x.ARi0_hp0 segs B). Qed.
Lemma bxi_HPST_x : forall a, in_img segs a -> ~ Exists (in_zr a) (@nil (Z * Z)).
Proof. intros a _ HE. inversion HE. Qed.
Lemma bxi_BLKN_ar0 : forall ly S Hp (W : world segs) mem md p n,
  ARi0 ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Proof.
  intros ly S Hp W mem md p n (HAR & _) Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn). lia.
Qed.
Lemma bxi_BLKM_ar0 : forall ly S Hp (W : world segs) mem md p n,
  ARi0 ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> n < 2 ^ 30.
Proof.
  intros ly S Hp W mem md p n (HAR & _) Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  change MALLOC_MAX with 268435456 in Hn. lia.
Qed.
Lemma bxi_WFL_ar0 : ARx_wf_law segs ARi0 (Wf (as_universe B)).
Proof. intros ly S Hp W mem md (HAR & _). exact (am_wf _ _ _ _ (proj1 HAR)). Qed.
Lemma bxi_SFREE_ar0 : forall s cid pos, Wf (as_universe B) s -> In (cid, pos) (frames s) ->
  exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Proof. intros s cid pos HWF Hin. exact (W_frame_x.SFREE_AR _ ML s cid pos HWF Hin). Qed.
End ar0.

Section cf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
(* the cf laws record at image B: bint-fp2 9dbe30ddcba Reusable/YG0lawscf.v:26 AR_laws_ok_cf proves it *)
Hypothesis LCF : AR_laws_cf segs B.
(* the consumer's ARX (bint-fp2 lib/B/W_LLVMFuzzerTestOneInput_top_x.v:93), generic in the cf parameters *)
Local Notation ARX := (fun ly S Hp (W : world segs) mem md => ARcf segs B ly S Hp W mem md /\ Hp = []).

Lemma bxi_HP0_cf : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md -> Hp = [].
Proof. intros ly S Hp W mem md H. exact (proj2 H). Qed.
Lemma bxi_BLK_cf : forall ly S Hp (W : world segs) mem md p n,
  ARX ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n < 2 ^ 30.
Proof.
  intros ly S Hp W mem md p n H Hin.
  destruct (alc_blocks _ _ LCF ly S Hp W mem md p n (proj1 H) Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof cf_malloc_max_bound as Hb. lia.
Qed.
Lemma bxi_BLKN_cf : forall ly S Hp (W : world segs) mem md p n,
  ARX ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Proof. intros ly S Hp W mem md p n H Hin. exact (proj1 (bxi_BLK_cf ly S Hp W mem md p n H Hin)). Qed.
Lemma bxi_BLKM_cf : forall ly S Hp (W : world segs) mem md p n,
  ARX ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> n < 2 ^ 30.
Proof. intros ly S Hp W mem md p n H Hin. exact (proj2 (bxi_BLK_cf ly S Hp W mem md p n H Hin)). Qed.
Lemma bxi_WFL_cf : ARx_wf_law segs ARX (Wf_cf (as_universe B)).
Proof. intros ly S Hp W mem md H. exact (ARx_wf_law_cf_x segs B ly S Hp W mem md (proj1 H)). Qed.
Lemma bxi_SFREE_cf : forall s cid pos, Wf_cf (as_universe B) s -> In (cid, pos) (frames s) ->
  exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Proof. intros s cid pos HWF Hin. exact (proj2 (stack_free_ok_cf _ s cid pos HWF Hin)). Qed.
End cf.
