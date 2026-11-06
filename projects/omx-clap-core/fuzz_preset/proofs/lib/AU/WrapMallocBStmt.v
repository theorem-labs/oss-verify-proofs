(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset, the malloc interceptor walk of image B (asan-ubsan, stripped pin
   d663f82d7f48, unstripped twin c90d4fa54d43; relocated from pin f8f98a95bc52) over the second allocator instance ARcf: the
   statements the walk proves, the two fields of the keep record wrap_malloc_walk_keep_cf
   (lib/Reusable/YGcfMallocComposeKeep.v:74-102), whose fields are the plain record's (YGcfMallocCompose.v:172-200) with
   the memnorm keep in each segment's post.
   - wmk_call_stmt: field wmk_call (YGcfMallocComposeKeep.v:75-83) verbatim. Its frame is ikeep_mn_cf
     (YGcfMallocComposeKeep.v:57-62: ikeep_cf's two conjuncts, then the memnorm keep). No premise is added: the stack
     room malloc_apre_cf asks at Allocate's entry (ly_bot ly < spZ regsA, AllocG.v:75, the image's sp there being the
     caller's less 2144) comes from acall_pre_cf's conjunct ly_bot ly + ACALL_PREFIX < spZ regs (YG0dcf.v:225,
     ACALL_PREFIX := 4096, YG0d.v:21).
   - wmk_ret_stmt: field wmk_ret (YGcfMallocComposeKeep.v:84-101) verbatim, the memnorm keep right after RGtop.rwin.
   - wmk_call_of_record / wmk_ret_of_record: the text checks, the record's two fields are the two statements by
     conversion.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require AllocG RGtop YGcfRmodel YAkMemnorm.
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

Section M.
Variables (nmax al atp acf : Z).
(* YGcfMallocComposeKeep.v:75-83 verbatim (field wmk_call). *)
Definition wmk_call_stmt (ARX : ARXh_t segs) (K : Kmalloc_t segs) : Prop :=
forall ly S Hp W regs mem md n ch,
  mentry_cf segs B ly S Hp W regs mem md n ch -> YGcfRmodel.rpre_cfr B S n -> 0 <= n < nmax ->
  SRr segs W (cfg_at segs (pc_wrap_malloc (as_code B)) regs mem md)
  (fun W1 c1 => exists inst so bp regsA memA mdA,
    c1 = cfg_at segs cf_pc_allocate regsA memA mdA /\
    malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly S W1 regsA memA mdA n (mtr_cf B ly regs ch) /\
    same_io md mdA /\ RGtop.rin regs (spZ regsA) AllocG.AFSTACK_G /\
    ikeep_mn_cf segs B ly S regs W mem W1 memA /\ errno_kept_cf B mem memA /\
    K ly S Hp W regs mem md n ch W1 regsA memA mdA).

(* YGcfMallocComposeKeep.v:84-101 verbatim (field wmk_ret). *)
Definition wmk_ret_stmt (ARX : ARXh_t segs) (K : Kmalloc_t segs) : Prop :=
forall ly S Hp W regs mem md n ch W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2,
  mentry_cf segs B ly S Hp W regs mem md n ch ->
  K ly S Hp W regs mem md n ch W1 regsA memA mdA ->
  malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly S W1 regsA memA mdA n (mtr_cf B ly regs ch) ->
  malloc_apost_cf segs B ARX Hp inst ly S W1 regsA memA mdA
    (fun a => q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 (sptr_addr B ly2 q) -> qtight S2 ->
  (exists trc, apath (malloc_cf n (mtr_cf B ly regs ch) S) trc (q, S2) /\ gflag trc = true) ->
  (q = PNull -> val_mem segs (mrestrict (w_H W2) mem2) (as_oom_byte B) 1 1) ->
  SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    getr regs' 10 = w64 (sptr_addr B ly2 q) /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep segs B regs W2 mem2 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    (YAkMemnorm.memnorm segs mem2 -> YAkMemnorm.memnorm segs mem') /\
    (q <> PNull -> errno_kept_cf B mem2 mem') /\
    (q = PNull -> rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1)).

(* The text checks: the keep record's fields are the two statements (by conversion). *)
Lemma wmk_call_of_record : forall (ARX : ARXh_t segs) (K : Kmalloc_t segs),
wrap_malloc_walk_keep_cf segs B nmax al atp acf ARX K -> wmk_call_stmt ARX K.
Proof. intros ARX K R. exact (wmk_call segs B nmax al atp acf ARX K R). Qed.
Lemma wmk_ret_of_record : forall (ARX : ARXh_t segs) (K : Kmalloc_t segs),
wrap_malloc_walk_keep_cf segs B nmax al atp acf ARX K -> wmk_ret_stmt ARX K.
Proof. intros ARX K R. exact (wmk_ret segs B nmax al atp acf ARX K R). Qed.
End M.
End J.
End G.
