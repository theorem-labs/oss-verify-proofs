(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 15 of its 31 lines of code are new or changed and 1012 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
tx_put_c TxRet Ledger GIInit strlen_c tx_line_c tx_string_c tx_value_c TvAsm.
Local Open Scope Z_scope.

Section KB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRB : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis AX : YL01.AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis HG : globals_free B API omx_G.
Hypothesis SLK : block_slack_present B API.
Variable F : ResForm.

Theorem tx_value_holds : tx_put_contract B API F -> tx_line_contract B API F -> tx_string_contract B API F ->
  strlen_contract -> tx_value_contract B API F.
Proof.
  intros TXP TXL TXS STR. apply tv_for_all. intros tv.
  exact (tv_all B API SEGS ERRB AX CTX F HG SLK TXP TXL TXS STR (S (depth tv)) tv (Nat.lt_succ_diag_r _)).
Qed.

End KB.