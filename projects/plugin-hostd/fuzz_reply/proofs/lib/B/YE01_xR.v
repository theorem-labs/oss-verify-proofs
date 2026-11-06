(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/YE01_x.v, with its module paths changed; 13 of its 86 lines of code are new or changed and 23 lines of the source are left out. *)
(* lib/B/YE01_x.v's two journal lemmas at a world relation R, for lib/B: asink_none_kept_xR (YE01_x.v:64) and
   ameta_inv_kept_xR (YE01_x.v:95), with the helper aenv_kept_xR (YE01_x.v:54).  Each is its YE01_x text with the
   journal `ajournal_x segs B PST ARx` -> `ajournal_xR segs B PST ARx R` and nothing else changed; R is a Section
   variable after the sink symbols K and none of its laws is needed.  The proofs read only the journal's conjuncts
   that do not mention R (YCbqG.v ajournal_xR: only its world conjunct reads R), so each proof is its YE01_x proof
   at the R journal.  lib/B/YE01_x.v is NOT edited; ameta_ptr_of_ARx (no journal) is cited from it.
   USED BY: lib/B/W_LLVMFuzzerTestOneInput_exit_x.v (the R twin of the spine's lx_end_state_x).
   proves no function (kind: route-R twins of kit journal lemmas). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01_x.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section JR.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws segs B K.
Variable R : world segs -> world segs -> Prop.
Local Notation AJR := (ajournal_xR segs B PST ARx R).
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* YE01_x.v:54 aenv_kept_x *)
Lemma aenv_kept_xR : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a,
AJR STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> aenv_addr K a -> ~ Exists (in_zr a) PST ->
fp_spares FP a -> mbyte segs (rd W' mem') a = mbyte segs (rd W mem) a.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a HJ Ha HPa Hsp.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (ail_env _ _ _ AIL a Ha) as (Hi & Hns & He). apply mbyte_kept_of_aview. exact (F3 a Hi Hns He HPa Hsp).
Qed.

(* YE01_x.v:64 asink_none_kept_x *)
Lemma asink_none_kept_xR : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
AJR STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
(forall a, aenv_addr K a -> ~ Exists (in_zr a) PST) ->
~ YI16.sink_open_fp FP ->
asink_none segs K (rd W mem) md -> asink_none segs K (rd W' mem') md'.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ HPST Hcl (Henv & Hhead & Hn).
pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed FP md md' Hcl Hos) as (Efd & Efsys & Eproc & Eio).
assert (FR : forall a, aenv_addr K a -> mbyte segs (rd W' mem') a = mbyte segs (rd W mem) a).
{ intros a Ha. eapply aenv_kept_xR; [exact HJ | exact Ha | exact (HPST a Ha) | apply fp_spares_closed; exact Hcl]. }
split; [exact (astdio_env_frame segs K _ _ FR Henv)|]. split.
- eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply FR. unfold aenv_addr, ak_ofl_head in *. cbn in Hx. lia.
- unfold m_fds in *. rewrite Efd. exact Hn.
Qed.

(* YE01_x.v:95 ameta_inv_kept_x *)
Lemma ameta_inv_kept_xR : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k M,
AJR STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
(forall a, ak_meta_mem K <= a < ak_meta_mem K + 8 -> ~ Exists (in_zr a) PST) ->
ameta_inv segs K ly (rd W mem) M -> ameta_inv segs K ly' (rd W' mem') M.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k M HJ HPST (HX & Himg & Hp0 & Hm & H0 & H47 & Hal & HZ).
pose proof HJ as (HAR' & Hly & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
assert (HX' : In (M, AMETA_SIZE) (ly_extra ly')) by (rewrite Eextra; exact HX).
split; [exact HX'|]. split; [exact Himg|]. split; [exact (ameta_ptr_of_ARx segs B ARx LAWS K AIL _ _ _ _ _ _ HAR')|]. split.
- eapply val_mem_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply mbyte_kept_of_aview.
destruct (ail_meta _ _ _ AIL x ltac:(lia)) as (Hi & Hns & He & Hlt).
apply (F3 x Hi Hns He (HPST x ltac:(lia))). apply fp_spares_below. exact Hlt.
- split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
intros a Ha. rewrite <- (HZ a Ha). apply mbyte_kept_of_aview. apply F5.
+ apply Exists_exists. exists (M, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
+ intros He. pose proof (ail_errno_img _ _ _ AIL a He) as Hi.
destruct (alx_extra _ _ _ LAWS ly' S' Hp' W' mem' md' a HAR'
ltac:(apply Exists_exists; exists (M, AMETA_SIZE); split; [exact HX' | unfold in_zr; cbn [fst snd]; lia])) as (_ & _ & _ & _ & Hni & _).
exact (Hni Hi).
Qed.
End JR.
End d.
