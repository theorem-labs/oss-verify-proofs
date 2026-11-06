(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g YQ0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF3w YF7z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma st_ok_ecall_full_shape {imgk : img} : forall (H : word -> bool) E ss ms,
st_ok_ecall tfxsegs E ss (restrict H ms) -> ss_resv ss = None ->
ms = pend_at (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom tfxsegs).
Proof.
intros H E ss ms HS Hrv. destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & _).
destruct ms as [regs fregs pcv pend resv fcsr mem rom]; cbn in *.
rewrite Hrv in Hresv. cbn in Hresv. unfold pend_at. cbn.
rewrite Hpend. specialize (Hregs 17%bv). cbn in Hregs. rewrite <- Hregs. (subst; cbv beta). img_refl.
Qed.
Lemma st_node_cont {imgk : img} : forall (H : word -> bool) (E : env) ss ms (e : sv) (v pc' : Z) (mem' : word -> option byte),
st_ok_ecall tfxsegs E ss (restrict H ms) -> ss_resv ss = None ->
sv_denot E e = Z_to_bv 64 v -> no_cdata (ss_mem ss) = true ->
Forall (region_kept tfxsegs E (mrestrict H (ms_mem ms)) (mrestrict H mem')) (ss_mem ss) ->
st_ok tfxsegs E (setpc (pin ss 10%bv e) pc')
(restrict H (mkst (regupd (ms_regs ms) 10%bv (Z_to_bv 64 v)) (Z_to_bv 64 pc') mem' (seg_rom tfxsegs))).
Proof.
intros H E ss ms e v pc' mem' HS Hrv He Hnc Hk.
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG).
unfold st_ok, setpc, pin. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
rewrite restrict_mkst_fx. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst].
split; [img_refl|]. split; [img_refl|]. split; [img_refl|]. split; [img_try (rewrite Hrv; img_refl)|].
split; [img_refl|]. split; [img_refl|]. split; [|img_try (split; [|img_exact HG])].
- pose proof (regs_ok_set E (ss_regs ss) (ms_regs (restrict H ms)) 10%bv (Z_to_bv 64 v) e Hregs He) as R. cbn in R.
destruct ms; cbn in *. img_exact R.
- img_apply (mem_ok_kept tfxsegs E (mrestrict H (ms_mem ms))); [| img_try (img_exact Hnc) | img_try (img_exact Hk)].
destruct ms; cbn in *. img_exact Hmem.
Qed.
End a.
