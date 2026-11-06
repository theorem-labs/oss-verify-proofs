(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module names changed; 605 of its 653 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_chain.v, with its module paths, module names and addresses changed; 27 of its 67 lines of code are new or changed and 613 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0 AllocSlots.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM06 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecAnsB.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecSeq RecStep RecGlue RecAnsB RecTail RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import xmalloc_c record_c arg_s_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require sprintf_c snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import SupChainUA SupChainUB SupChainUF sup_chain_c.
Import ListNotations.
Open Scope Z_scope.

Section Main.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GRD : ms_guard B = 0x54730.
Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis FREE : forall fx0 : YK11.FPState, free_contract (fx := fx0) B API.
Hypothesis ARGS : forall fx0 : YK11.FPState, @arg_s_contract fx0 rc B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis ANS : forall fx0 : YK11.FPState, @answer_contract fx0 rc B API.
Hypothesis XM : xmalloc_contract B API.
Hypothesis REC : record_contract B API.
Hypothesis SNP : snprintf_c.snprintf_contract.
Hypothesis SPR : sprintf_c.sprintf_contract.

Theorem sup_chain_holds : sup_chain_contract B API.
Proof using SEGS ERRNO_LOW GFACT GOWN RIMG AX CTX SLACK GOTG GRD FREE_PC FREE ARGS RSO ANS XM REC SNP SPR.
  unfold sup_chain_contract.
  intros L A regs mem md id pids ids R O b PRE GA HID GP GN HN HF HP0 HP4 BS HPS BH NRA GS GR RA FRM F18 RES ROOM.
  rewrite SEGS in BS, BH, GS, GR, RA, F18.
  assert (H : SR rsegs (mkCfg (mkst regs (Z_to_bv 64 SUP_CHAIN) mem (seg_rom rsegs)) md)
                (scu_ret B API L A regs mem md id ids R O b)).
  { apply (scu_front B API SEGS ERRNO_LOW AX GFACT GOWN GOTG GRD XM REC SNP SPR ARGS L A regs mem md id pids ids R O b
             _ PRE GA HID GP GN HN HF HP0 HP4 BS HPS BH NRA GR RA FRM F18 RES ROOM).
    intros fx' R' m' mc Lc Ac mdc Oc lp b1 FK SI BX BP MU WM RA' E2 E3 E4 E19 INI BLE EQB FR0 FR1.
    exact (scu_back B API SEGS ERRNO_LOW GFACT GOWN RIMG AX CTX SLACK GOTG GRD FREE_PC FREE ARGS RSO ANS
             L A regs mem md id ids R O b fx' R' m' Lc Ac mdc Oc lp b1 PRE HN HF GS GR ROOM FK SI BX E2 E3 E4 E19 INI
             BLE EQB FR0 FR1). }
  rewrite <- SEGS in H. exact H.
Qed.

End Main.
