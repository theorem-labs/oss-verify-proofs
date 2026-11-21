(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFk7.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFk7.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFhz_w AFk8_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma st_ok_ecall_full_shape : forall (H : word -> bool) E ss ms,
st_ok_ecall tfibsegs E ss (restrict H ms) -> ss_resv ss = None ->
ms = pend_at (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom tfibsegs).
Proof.
intros H E ss ms HS Hrv. destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & _).
destruct ms as [regs fregs pcv pend resv fcsr mem rom]; cbn in *.
rewrite Hrv in Hresv. cbn in Hresv. unfold pend_at. cbn.
rewrite Hpend. specialize (Hregs 17%bv). cbn in Hregs. rewrite <- Hregs. subst. reflexivity.
Qed.
Lemma st_node_cont : forall (H : word -> bool) (E : env) ss ms (e : sv) (v pc' : Z) (mem' : word -> option byte),
st_ok_ecall tfibsegs E ss (restrict H ms) -> ss_resv ss = None ->
sv_denot E e = Z_to_bv 64 v -> no_cdata (ss_mem ss) = true ->
Forall (region_kept tfibsegs E (mrestrict H (ms_mem ms)) (mrestrict H mem')) (ss_mem ss) ->
st_ok tfibsegs E (setpc (pin ss 10%bv e) pc')
(restrict H (mkst (regupd (ms_regs ms) 10%bv (Z_to_bv 64 v)) (Z_to_bv 64 pc') mem' (seg_rom tfibsegs))).
Proof.
intros H E ss ms e v pc' mem' HS Hrv He Hnc Hk.
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG).
unfold st_ok, setpc, pin. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
rewrite restrict_mkst_fx. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [rewrite Hrv; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [|split; [|exact HG]].
- pose proof (regs_ok_set E (ss_regs ss) (ms_regs (restrict H ms)) 10%bv (Z_to_bv 64 v) e Hregs He) as R. cbn in R.
destruct ms; cbn in *. exact R.
- apply (mem_ok_kept tfibsegs E (mrestrict H (ms_mem ms))); [| exact Hnc | exact Hk].
destruct ms; cbn in *. exact Hmem.
Qed.
End a.
