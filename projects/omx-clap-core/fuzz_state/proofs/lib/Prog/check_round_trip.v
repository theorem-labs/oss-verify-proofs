(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 976 of its 1075 lines of code are new or changed and 647 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_reject_clean_starved.v, with its module names and numbers changed; 714 of its 791 lines of code are new or changed and 998 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_as_written.v, with its module paths, module names, addresses and numbers changed; 1718 of its 1786 lines of code are new or changed and 723 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_no_overread.v, with its module paths, module names and numbers changed; 1312 of its 1471 lines of code are new or changed and 1627 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_calls.v; 223 of its 404 lines of code are new or changed and 1290 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_sd5.v; 138 of its 202 lines of code are new or changed and 340 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_top.v; 9 of its 57 lines of code are new or changed and 154 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YL01 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger LedgerFacts KindBGlue HState HStateRoom
  ReaderRes WriterSpec fuzz_free_c fuzz_malloc_c preset_base64_encode_c preset_base64_decode_c
  PjStruct pj_string_c pj_set_c pj_free_c pj_parse_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterApp WriterAppFacts WriterValue
  put_c put_string_c indent_c write_value_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import check_round_trip_c check_round_trip_glue
  check_round_trip_runs check_round_trip_calls check_round_trip_stages_a check_round_trip_stages_b
  check_round_trip_st8 check_round_trip_stdefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB WriterSpecFacts fuzz_free
  check_no_overread.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c
  pj_get_c pj_get_str_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require check_round_trip_st8 check_round_trip_top
  check_round_trip_chain.
Import ListNotations.
Local Open Scope Z_scope.

(* check_round_trip (plain): the top (crt_r0, check_round_trip_top) and the stages st7..st0 (check_round_trip_chain);
   the one open premise is St8, the stage the other stage file proves (st8 : St8). *)
Theorem check_round_trip_holds : forall (rc : YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16594 -> ms_free B = 0x16454 -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = strtod_c.STRTOD_TP -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = strtod_c.STRTOD_GOT_GUARD -> ms_guard B = strtod_c.STRTOD_GUARD ->
  strlen_contract /\ strcmp_contract /\ bcmp_contract /\ pj_object_contract /\ pj_get_contract /\
  pj_get_str_contract /\
  (forall fx' : YK11.FPState, malloc_contract (fx := fx') B API) /\
  (forall fx' : YK11.FPState, free_contract (fx := fx') B API) /\
  (forall fx' : YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) /\
  (forall fx' : YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) /\
  (forall fx' : YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) /\
  (forall fx' : YK11.FPState, pj_string_contract (fx := fx') B API sb_form) /\
  (forall fx' : YK11.FPState, pj_set_contract (fx := fx') B API sb_form) /\
  (forall fx' : YK11.FPState, pj_free_contract (fx := fx') B API sb_form) /\
  (forall fx' : YK11.FPState, pj_write_contract_sb (fx := fx') B API) /\
  (forall fx' : YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  check_round_trip_st8.St8 -> forall fx : YK11.FPState, check_round_trip_contract (fx := fx) B API.
Proof.
  intros rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD CS H8.
  exact (check_round_trip_top.check_round_trip_top rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD CS
           (check_round_trip_chain.st_chain H8)).
Qed.
