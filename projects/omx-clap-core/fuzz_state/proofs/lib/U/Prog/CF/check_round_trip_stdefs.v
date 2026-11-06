(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 976 of its 1075 lines of code are new or changed and 647 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_reject_clean_starved.v, with its module names and numbers changed; 714 of its 791 lines of code are new or changed and 998 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_as_written.v, with its module paths, module names, addresses and numbers changed; 1718 of its 1786 lines of code are new or changed and 723 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_no_overread.v, with its module paths, module names and numbers changed; 1312 of its 1471 lines of code are new or changed and 1627 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_calls.v; 223 of its 404 lines of code are new or changed and 1290 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_sd5.v, with its module paths and numbers changed; 327 of its 355 lines of code are new or changed and 376 lines of the source are left out. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import check_round_trip_c check_round_trip_glue check_round_trip_calls check_round_trip_stages_a check_round_trip_st8.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require HsKindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require check_reject_clean_starved past_nul.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c pj_get_c pj_get_str_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.


Definition St7 : Prop :=
  forall (rc : lib.Reusable.YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16c7c -> ms_free B = 0x16b3c -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> lib.U.Reusable.YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = U.Prog.strtod_c.STRTOD_TP -> errno_addr B = U.Prog.strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = U.Prog.strtod_c.STRTOD_GOT_GUARD -> ms_guard B = U.Prog.strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : lib.Reusable.YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : lib.Reusable.YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Dv bs b kb,
  CR B API L A regs mem md Lam peak cnt bnd X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 59 <= cnt + CRT_ALLOCS -> (151 <= Nc)%nat ->
  Permutation X (Dd ++ Dv ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 192) (JObj [(CRT_FORMAT, JStr CRT_FMT2)]) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 80) (JStr CRT_STATE) Dv ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13d54 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 352 + 192) ->
  getr regsc 11 = Z_to_bv 64 0x102ba -> getr regsc 12 = Z_to_bv 64 (spZ regs - 352 + 80) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_SET) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

Definition St6 : Prop :=
  forall (rc : lib.Reusable.YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16c7c -> ms_free B = 0x16b3c -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> lib.U.Reusable.YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = U.Prog.strtod_c.STRTOD_TP -> errno_addr B = U.Prog.strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = U.Prog.strtod_c.STRTOD_GOT_GUARD -> ms_guard B = U.Prog.strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : lib.Reusable.YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : lib.Reusable.YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd bs b kb,
  CR B API L A regs mem md Lam peak cnt bnd X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 60 <= cnt + CRT_ALLOCS -> (152 <= Nc)%nat ->
  Permutation X (Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 192) (JObj [(CRT_FORMAT, JStr CRT_FMT2)]) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13d3c -> getr regsc 10 = Z_to_bv 64 (spZ regs - 352 + 80) ->
  getr regsc 11 = Z_to_bv 64 0x102f8 ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_STRING) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

Definition St5 : Prop :=
  forall (rc : lib.Reusable.YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16c7c -> ms_free B = 0x16b3c -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> lib.U.Reusable.YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = U.Prog.strtod_c.STRTOD_TP -> errno_addr B = U.Prog.strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = U.Prog.strtod_c.STRTOD_GOT_GUARD -> ms_guard B = U.Prog.strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : lib.Reusable.YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : lib.Reusable.YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dv bs b kb,
  CR B API L A regs mem md Lam peak cnt bnd X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 63 <= cnt + CRT_ALLOCS -> (155 <= Nc)%nat ->
  Permutation X (Dv ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 192) (JObj []) [] ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 80) (JStr CRT_FMT2) Dv ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13d28 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 352 + 192) ->
  getr regsc 11 = Z_to_bv 64 0x1036e -> getr regsc 12 = Z_to_bv 64 (spZ regs - 352 + 80) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_SET) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

Definition St4 : Prop :=
  forall (rc : lib.Reusable.YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16c7c -> ms_free B = 0x16b3c -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> lib.U.Reusable.YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = U.Prog.strtod_c.STRTOD_TP -> errno_addr B = U.Prog.strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = U.Prog.strtod_c.STRTOD_GOT_GUARD -> ms_guard B = U.Prog.strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : lib.Reusable.YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : lib.Reusable.YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 bs b kb,
  CR B API L A regs mem md Lam peak cnt bnd [(b1, k1); (q, kq)] [(same, sn); (want, wn)]
    Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 64 <= cnt + CRT_ALLOCS -> (156 <= Nc)%nat ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 192) (JObj []) [] ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13d10 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 352 + 80) ->
  getr regsc 11 = Z_to_bv 64 0x1037a ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_STRING) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

Definition St3 : Prop :=
  forall (rc : lib.Reusable.YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16c7c -> ms_free B = 0x16b3c -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> lib.U.Reusable.YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = U.Prog.strtod_c.STRTOD_TP -> errno_addr B = U.Prog.strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = U.Prog.strtod_c.STRTOD_GOT_GUARD -> ms_guard B = U.Prog.strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : lib.Reusable.YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : lib.Reusable.YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq bs b kb,
  CR B API L A regs mem md Lam peak cnt bnd [(q, kq)] [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 65 <= cnt + CRT_ALLOCS -> (157 <= Nc)%nat ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13cc4 -> getr regsc 10 = Z_to_bv 64 q ->
  getr regsc 11 = Z_to_bv 64 (spZ regs - 352 + 8) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same ->
  0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PRESET_BASE64_DECODE) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

Definition St2 : Prop :=
  forall (rc : lib.Reusable.YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16c7c -> ms_free B = 0x16b3c -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> lib.U.Reusable.YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = U.Prog.strtod_c.STRTOD_TP -> errno_addr B = U.Prog.strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = U.Prog.strtod_c.STRTOD_GOT_GUARD -> ms_guard B = U.Prog.strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : lib.Reusable.YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : lib.Reusable.YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall Lc Ac regsc memc mdc Lamc peakc cntc Nc want wn q kq bs b kb t tb,
  CR B API L A regs mem md Lam peak cnt bnd [(q, kq)] [(want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 66 <= cnt + CRT_ALLOCS -> (158 <= Nc)%nat ->
  wn = (Z.of_nat (length bs) + 2) / 3 * 4 + 1 ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  Mem.bytes_at rsegs memc t (tb ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) tb -> Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
  (exists pt kt, In (pt, kt) (blocks L A) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
  b64_dec (zs tb) = Some bs ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13a34 -> getr regsc 10 = Z_to_bv 64 (Z.of_nat (length tb) + 1) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 t -> getr regsc 22 = Z_to_bv 64 ((Z.of_nat (length bs) + 2) / 3 * 4) ->
  getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 0x16c7c) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

Definition St1 : Prop :=
  forall (rc : lib.Reusable.YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16c7c -> ms_free B = 0x16b3c -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> lib.U.Reusable.YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = U.Prog.strtod_c.STRTOD_TP -> errno_addr B = U.Prog.strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = U.Prog.strtod_c.STRTOD_GOT_GUARD -> ms_guard B = U.Prog.strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : lib.Reusable.YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : lib.Reusable.YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall Lc Ac regsc memc mdc Lamc peakc cntc Nc q kq bs b kb t tb slack,
  CR B API L A regs mem md Lam peak cnt bnd [(q, kq)] [] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 67 <= cnt + CRT_ALLOCS -> (159 <= Nc)%nat ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  Mem.bytes_at rsegs memc t (tb ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) tb ->
  (- (t + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
  (exists pt kt, In (pt, kt) (blocks L A) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
  b64_dec (zs tb) = Some bs ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13a20 ->
  getr regsc 10 = Z_to_bv 64 ((Z.of_nat (length bs) + 2) / 3 * 4 + 1) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 t -> getr regsc 22 = Z_to_bv 64 ((Z.of_nat (length bs) + 2) / 3 * 4) ->
  getr regsc 8 = Z_to_bv 64 q ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 0x16c7c) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

Definition St0 : Prop :=
  forall (rc : lib.Reusable.YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16c7c -> ms_free B = 0x16b3c -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> lib.U.Reusable.YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = U.Prog.strtod_c.STRTOD_TP -> errno_addr B = U.Prog.strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = U.Prog.strtod_c.STRTOD_GOT_GUARD -> ms_guard B = U.Prog.strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : lib.Reusable.YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : lib.Reusable.YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : lib.Reusable.YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall Lc Ac regsc memc mdc Lamc peakc cntc Nc bs b kb t tb slack,
  CR B API L A regs mem md Lam peak cnt bnd [] [] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 68 <= cnt + CRT_ALLOCS -> (160 <= Nc)%nat ->
  bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  Mem.bytes_at rsegs memc t (tb ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) tb ->
  (- (t + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
  (exists pt kt, In (pt, kt) (blocks L A) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
  b64_dec (zs tb) = Some bs ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x139fc -> getr regsc 10 = Z_to_bv 64 b ->
  getr regsc 11 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 t ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PRESET_BASE64_ENCODE) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).
