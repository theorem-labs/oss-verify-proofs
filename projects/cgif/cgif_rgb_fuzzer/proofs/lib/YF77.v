(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0j YQ0c YQ0b YQ03 YQ0i YQ09 YQ04 YQ0e YQ0f YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03 YF04.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfxtbl_rr {imgk : img} : ctable := ltac:(img_eval_sel (fun imgk : img => (build_table tfxsegs (0x53504 + D_2c4) 118%nat (build_table tfxsegs (0x322a4 + D_150) 131%nat tfxtbl_rtA)))).
Lemma tfxtbl_rr_eq {imgk : img} : tfxtbl_rr = build_table tfxsegs (0x53504 + D_2c4) 118%nat (build_table tfxsegs (0x322a4 + D_150) 131%nat tfxtbl_rtA).
Proof. img_case; lazymatch goal with |- ?l_ = _ => vm_cast_no_check (@eq_refl _ l_) end. Qed.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma tfxtbl_rr_ok {imgk : img} : table_ok tfxsegs tfxtbl_rr.
Proof. img_destruct imgk. all: rewrite tfxtbl_rr_eq. all: img_apply build_table_ok; [img_try ((img_case; cbv); discriminate)|]. all: img_apply build_table_ok; [img_try ((img_case; cbv); discriminate) | img_try (img_exact tfxtbl_rtA_ok)]. Qed.
End a.
