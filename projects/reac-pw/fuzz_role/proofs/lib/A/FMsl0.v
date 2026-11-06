(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: cgif_file_fuzzer lib/A/AE6y.v's walk of the wrapper's shadow check (with AE7e.v's entry registers), restated for the strlen wrapper of libreac/fuzz_disco: a0 = n - 1 and s1 = 1 at RC_ENTRY, the size test is decided by the engine, the code table adds the wrapper body, and the common-flags pointer and the strlen flag are read-only cells; module paths. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Rt/StrlenChk.v, with its module paths and addresses changed; 24 of its 76 lines of code are new or changed and 2444 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from port-fm's cgif_file_fuzzer-coordinate copy (origin/cold/port-fm-rtscan f8664b31b9c, proofs/cgif/cgif_file_fuzzer/lib/A/FMsl0.v) to fuzz_identity.asan by an address map recorded by the porting lane; module paths, the record class TfibSyms (unchanged), YA0m import dropped; tbl_sl_probe's trampoline word 0x0980006f (cgif: j +0x98) is 0x0900006f here (j +0x90, read from the image at 0x4218c). *)
(* Modified by Theorem Labs, 2026-10-29: for r-identity's acceptance (cold/h-rw-ide-6-wrapacc), the record class is TfibSyms, not IdentTfibSyms (DECISIONS-LIVE 05:31Z: TfibSyms in both A and B, no --rename), and the core modules are Required by full path at the applied A core's names (lib/A/A*.v, lib/Reusable/YA0m, YE08, YE21). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/FMsl0.v at origin/ossv/recipes 7cbe5270d908 (donor image sha256 c954b804786c); module paths changed and addresses moved to reac-pw/fuzz_role's ASan build (fuzz_role.asan sha256 614cffc0864c) by port_core.py 1e42da8952ec, cross-checked numeral by numeral with alreloc a5c53bb2bed4 (ledger provenance/reloc/A-Rt-Strlen.tsv); hand: tbl_sl_probe's trampoline word 0x0900006f is 0x08c0006f here (j +0x8c, read from fuzz_role.asan at 0x41ac8). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.

From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.

Require Import
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.AB1v
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.AE34
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.AF0l
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.AF0m
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.AF0x
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.AB1w
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.AE20
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.AE2y.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable.YE08
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable.YE21.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The strlen interceptor body 0x4221c..0x424b0 (165 instructions) is outside AE34's icpt_ranges:
   that table stops at the trampolines (0x4218c, 38) and resumes at the strnlen interceptor
   (0x424b0, 165).  tbl_sl is tbl_icpt plus that one range. *)
Definition sl_ranges : list (Z * nat) := [(0x41b54, 165%nat)].
Definition tbl_sl : ctable := Eval vm_compute in build_ranges sl_ranges tbl_icpt.
Lemma tbl_sl_eq : tbl_sl = build_ranges sl_ranges tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_sl). Qed.
Lemma tbl_sl_ok : table_ok tfibsegs tbl_sl.
Proof.
rewrite tbl_sl_eq. apply build_ranges_ok; [| exact tbl_icpt_ok].
unfold sl_ranges. repeat constructor; cbn; discriminate.
Qed.
(* the strlen trampoline, the first and the last instruction word of the interceptor body *)
Lemma tbl_sl_probe :
clookup tbl_sl 0x41ac8 = Some 0x08c0006f /\
clookup tbl_sl 0x41b54 = Some 0x81010113 /\
clookup tbl_sl 0x41de4 = Some 0xe29ff06f /\
clookup tbl_sl 0x41de8 = Some 0x81010113.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma sl_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl_sl FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_sl tbl_sl_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma sl_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfibsegs tbl_sl FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_sl tbl_sl_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
End f.
