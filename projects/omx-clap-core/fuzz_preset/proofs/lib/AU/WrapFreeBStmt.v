(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset, the free interceptor walk of image B (asan-ubsan, stripped pin
   d663f82d7f48, unstripped twin c90d4fa54d43; relocated from pin f8f98a95bc52) over the second allocator instance ARcf: the
   statements the walk proves, the two fields of the primed keep record wrap_free_walk_keep_cf_rh
   (lib/Reusable/YGcfMallocComposeKeep.v:398-423), generic over segs, B, atpD, ARX and K:
   - wf_call_stmt: field wfrk_call (YGcfMallocComposeKeep.v:399-407) verbatim: the call segment's frame is ikeep_mn_cf
     (:57-62), ikeep_cf with the memnorm keep. The stack room Deallocate's entry asks (free_dpre_cf's ly_bot ly < spZ
     regsD, dealloc_pre (lib/Reusable/DeallocG.v), below the interceptor's frame of 2128) is acall_pre_cf's own conjunct
     ly_bot ly + ACALL_PREFIX < spZ regs (YG0dcf.v:225, ACALL_PREFIX := 4096, YG0d.v:21), so the field takes no premise more.
   - wf_ret_stmt: field wfrk_ret (YGcfMallocComposeKeep.v:408-422) verbatim: Deallocate's post is the primed
     YGcfRehidePost.dealloc_post_raw_rh (YGcfRehidePost.v:395), the memnorm keep right after RGtop.rwin.
   - wf_call_of_record / wf_ret_of_record / wf_record_of: the text checks, by conversion, both ways.
   No image constant here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DeallocG RGtop YGcfRmodel YAkMemnorm YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfMallocComposeKeep.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section J.
Variable segs : list Segment.
Variable B : asyms.

Section F.
Variable atpD : Z.
(* YGcfMallocComposeKeep.v:399-407 verbatim (field wfrk_call). *)
Definition wf_call_stmt (ARX : ARXh_t segs) (K : Kfree_t segs) : Prop :=
forall ly S Hp W regs mem md p n ch,
  fentry_cf segs B ly S Hp W regs mem md p n ch -> rpreD_free_cf B (finit_cf S) n ->
  SRr segs W (cfg_at segs (pc_wrap_free (as_code B)) regs mem md)
  (fun W1 c1 => exists inst so bp regsD memD mdD,
    c1 = cfg_at segs cf_pc_deallocate regsD memD mdD /\
    free_dpre_cf segs B atpD ARX Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf B ly regs ch) /\
    same_io md mdD /\ RGtop.rin regs (spZ regsD) DeallocG.DFSTACK_G /\
    ikeep_mn_cf segs B ly S regs W mem W1 memD /\ errno_kept_cf B mem memD /\
    K ly S Hp W regs mem md p n ch W1 regsD memD mdD).

(* YGcfMallocComposeKeep.v:408-422 verbatim (field wfrk_ret). *)
Definition wf_ret_stmt (ARX : ARXh_t segs) (K : Kfree_t segs) : Prop :=
forall ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2,
  fentry_cf segs B ly S Hp W regs mem md p n ch ->
  K ly S Hp W regs mem md p n ch W1 regsD memD mdD ->
  free_dpre_cf segs B atpD ARX Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf B ly regs ch) ->
  YGcfRehidePost.dealloc_post_raw_rh segs B (ARX Hp) (aowned B) inst ly (finit_cf S) W1 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  qtight S2 ->
  (exists trc, apath (free_cf p (ftr_cf B ly regs ch) (finit_cf S)) trc (tt, S2) /\ gflag trc = true) ->
  SRr segs W2 (cfg_at segs (raZ regsD) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep segs B regs W2 mem2 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    (YAkMemnorm.memnorm segs mem2 -> YAkMemnorm.memnorm segs mem') /\
    errno_kept_cf B mem2 mem').

(* The text checks: each field of the Record is its statement here, and the two statements build the Record, all by
   conversion. *)
Lemma wf_call_of_record : forall (ARX : ARXh_t segs) (K : Kfree_t segs),
wrap_free_walk_keep_cf_rh segs B atpD ARX K -> wf_call_stmt ARX K.
Proof. intros ARX K R. exact (wfrk_call segs B atpD ARX K R). Qed.
Lemma wf_ret_of_record : forall (ARX : ARXh_t segs) (K : Kfree_t segs),
wrap_free_walk_keep_cf_rh segs B atpD ARX K -> wf_ret_stmt ARX K.
Proof. intros ARX K R. exact (wfrk_ret segs B atpD ARX K R). Qed.
Lemma wf_record_of : forall (ARX : ARXh_t segs) (K : Kfree_t segs),
wf_call_stmt ARX K -> wf_ret_stmt ARX K -> wrap_free_walk_keep_cf_rh segs B atpD ARX K.
Proof. intros ARX K WC WR. exact (Build_wrap_free_walk_keep_cf_rh segs B atpD ARX K WC WR). Qed.
End F.
End J.
End G.
