(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twins of two journal lemmas of lib/Reusable/YE01.v (a Theorem Labs lane's route (b)):
   asink_none_kept (YE01.v:83) and ameta_inv_kept (YE01.v:149), with the two helpers their proofs use, aenv_kept
   (YE01.v:55) and ameta_ptr_of_AR (YE01.v:137).  YE01.v is NOT edited: this file sits beside it.
   - Each twin NAME_x is stated over a Section relation `ARx` with its laws `LAWS : AR_laws_x segs B ARx hl`, the journal
     YCbqG.ajournal_x (written AJ below; the ghost set Hp after S and Hp' after S') and its placement parameter PST.
     The proofs are YE01.v's, with AR's invariant fields replaced by AR_laws_x's: am_const (the const cells held) by
     alx_const_cells, AR_extra_law_ok by alx_extra.
   - The AR-free names of YE01.v (asink_img_laws, ameta_inv, mbyte_kept_of_aview) and YE00.v / YCbq.v (asink_none,
     astdio_env_frame, aos_step_closed, fp_spares_closed, fp_spares_below) are cited, not copied.
   One difference of statement, forced by PST: YCbqG.ajournal_x's image clause keeps only bytes outside PST, so each
   twin that reads it takes the bytes it reads there outside PST (aenv_kept_x / asink_none_kept_x: the stdio
   environment's bytes; ameta_inv_kept_x: the 8 bytes at ak_meta_mem).  At an instance with PST = [] the premise
   holds trivially. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section J.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws segs B K.
Local Notation AJ := (ajournal_x segs B PST ARx).
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* YE01.v:55 aenv_kept *)
Lemma aenv_kept_x : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a,
AJ STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> aenv_addr K a -> ~ Exists (in_zr a) PST ->
fp_spares FP a -> mbyte segs (rd W' mem') a = mbyte segs (rd W mem) a.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a HJ Ha HPa Hsp.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (ail_env _ _ _ AIL a Ha) as (Hi & Hns & He). apply mbyte_kept_of_aview. exact (F3 a Hi Hns He HPa Hsp).
Qed.

(* YE01.v:83 asink_none_kept *)
Lemma asink_none_kept_x : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
AJ STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
(forall a, aenv_addr K a -> ~ Exists (in_zr a) PST) ->
~ YI16.sink_open_fp FP ->
asink_none segs K (rd W mem) md -> asink_none segs K (rd W' mem') md'.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ HPST Hcl (Henv & Hhead & Hn).
pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed FP md md' Hcl Hos) as (Efd & Efsys & Eproc & Eio).
assert (FR : forall a, aenv_addr K a -> mbyte segs (rd W' mem') a = mbyte segs (rd W mem) a).
{ intros a Ha. eapply aenv_kept_x; [exact HJ | exact Ha | exact (HPST a Ha) | apply fp_spares_closed; exact Hcl]. }
split; [exact (astdio_env_frame segs K _ _ FR Henv)|]. split.
- eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply FR. unfold aenv_addr, ak_ofl_head in *. cbn in Hx. lia.
- unfold m_fds in *. rewrite Efd. exact Hn.
Qed.

(* YE01.v:137 ameta_ptr_of_AR: AR's am_const is AR_laws_x's alx_const_cells *)
Lemma ameta_ptr_of_ARx : forall ly S Hp W mem md,
ARx ly S Hp W mem md -> val_mem segs (rd W mem) (ak_meta_ptr K) 8 (ak_meta_mem K).
Proof.
intros ly S Hp W mem md HAR k Hk.
pose proof (alx_const_cells _ _ _ LAWS ly S Hp W mem md HAR) as HC.
pose proof (proj1 (Forall_forall _ _) HC _ (ail_meta_ptr _ _ _ AIL ly)) as Hc. unfold z8, c8, cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
specialize (Hc k Hk). unfold aview in Hc.
destruct (mbyte segs (mrestrict (w_H W) mem) (ak_meta_ptr K + Z.of_nat k)) as [b|] eqn:E; [|discriminate Hc]. cbn in Hc.
injection Hc as Hc. f_equal. apply bv_eq. rewrite Hc, Z_to_bv_unsigned. symmetry.
change (YO0f.le_byte (ak_meta_mem K) 8 k) with (YG0f.le_byte (ak_meta_mem K) 8 k). unfold YG0f.le_byte.
unfold bv_wrap. change (bv_modulus 8) with 256%Z. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.

(* YE01.v:149 ameta_inv_kept: AR_extra_law_ok is AR_laws_x's alx_extra *)
Lemma ameta_inv_kept_x : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k M,
AJ STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
(forall a, ak_meta_mem K <= a < ak_meta_mem K + 8 -> ~ Exists (in_zr a) PST) ->
ameta_inv segs K ly (rd W mem) M -> ameta_inv segs K ly' (rd W' mem') M.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k M HJ HPST (HX & Himg & Hp0 & Hm & H0 & H47 & Hal & HZ).
pose proof HJ as (HAR' & Hly & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
assert (HX' : In (M, AMETA_SIZE) (ly_extra ly')) by (rewrite Eextra; exact HX).
split; [exact HX'|]. split; [exact Himg|]. split; [exact (ameta_ptr_of_ARx _ _ _ _ _ _ HAR')|]. split.
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
End J.
End d.
