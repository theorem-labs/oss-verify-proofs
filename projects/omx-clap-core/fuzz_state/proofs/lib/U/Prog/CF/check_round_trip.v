(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, module names, addresses and numbers changed; 583 of its 659 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/past_nul.v, with its module paths and module names changed; 715 of its 794 lines of code are new or changed and 580 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/check_as_written.v, with its module paths, module names, addresses and numbers changed; 1718 of its 1788 lines of code are new or changed and 724 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/check_no_overread.v, with its module paths, module names and numbers changed; 1320 of its 1479 lines of code are new or changed and 1629 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/check_round_trip_calls.v; 224 of its 413 lines of code are new or changed and 1290 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/check_round_trip_sd5.v; 136 of its 208 lines of code are new or changed and 341 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/check_round_trip_top.v; 6 of its 61 lines of code are new or changed and 153 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YL01 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger LedgerFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import HState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import HStateRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import fuzz_free_c fuzz_malloc_c preset_base64_encode_c preset_base64_decode_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import pj_string_c pj_set_c pj_free_c pj_parse_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterApp WriterAppFacts WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import put_c put_string_c indent_c write_value_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import check_round_trip_runs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import check_round_trip_c check_round_trip_glue check_round_trip_calls check_round_trip_stages_a check_round_trip_stages_b check_round_trip_st8 check_round_trip_stdefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require HsKindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require check_reject_clean_starved past_nul fuzz_free check_no_overread.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpecFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c pj_get_c pj_get_str_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require check_round_trip_st8 check_round_trip_top check_round_trip_chain.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.

Theorem check_round_trip_holds : forall (rc : lib.Reusable.YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16c7c -> ms_free B = 0x16b3c -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> lib.U.Reusable.YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = U.Prog.strtod_c.STRTOD_TP -> errno_addr B = U.Prog.strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = U.Prog.strtod_c.STRTOD_GOT_GUARD -> ms_guard B = U.Prog.strtod_c.STRTOD_GUARD ->
  strlen_contract /\ strcmp_contract /\ bcmp_contract /\ pj_object_contract /\ pj_get_contract /\
  pj_get_str_contract /\
  (forall fx' : lib.Reusable.YK11.FPState, malloc_contract (fx := fx') B API) /\
  (forall fx' : lib.Reusable.YK11.FPState, free_contract (fx := fx') B API) /\
  (forall fx' : lib.Reusable.YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) /\
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) /\
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) /\
  (forall fx' : lib.Reusable.YK11.FPState, pj_string_contract (fx := fx') B API sb_form) /\
  (forall fx' : lib.Reusable.YK11.FPState, pj_set_contract (fx := fx') B API sb_form) /\
  (forall fx' : lib.Reusable.YK11.FPState, pj_free_contract (fx := fx') B API sb_form) /\
  (forall fx' : lib.Reusable.YK11.FPState, pj_write_contract_sb (fx := fx') B API) /\
  (forall fx' : lib.Reusable.YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  check_round_trip_st8.St8 -> forall fx : lib.Reusable.YK11.FPState, check_round_trip_contract (fx := fx) B API.
Proof.
  intros rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD CS H8.
  exact (check_round_trip_top.check_round_trip_top rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD CS
           (check_round_trip_chain.st_chain H8)).
Qed.
