(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFk7.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AFk7.v (donor image sha256 43654a025fd0), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/AFk7.v at 9f8c843f0e03 (image sha256 614cffc0864c), with its module paths changed and its addresses moved to reac-pw/fuzz_headamp's ASan build (image sha256 f3e0669d2819) by alreloc a5c53bb2bed4; comments kept as the source has them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_headamp/lib/A/AFk7.v at b0cad0df5623 (image sha256 f3e0669d2819), with its module names changed (A.Axyz -> AU.Yxyz) and its addresses moved to reac-pw/fuzz_headamp's ASan+UBSan build (image sha256 53edda9bdeeb) by derive_y.py b7b132fb12a7; the Modified-by lines above describe how lib/A/AFk7.v was made and quote its ASan-build values. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.

From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n.

From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import YB1v YF0x YFhz YFk8.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
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
