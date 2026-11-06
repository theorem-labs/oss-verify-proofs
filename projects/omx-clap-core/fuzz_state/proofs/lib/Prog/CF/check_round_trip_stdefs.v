(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, module names, addresses and numbers changed; 556 of its 631 lines of code are new or changed and 671 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/past_nul.v, with its module names changed; 711 of its 786 lines of code are new or changed and 556 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_as_written.v, with its module names, addresses and numbers changed; 1716 of its 1784 lines of code are new or changed and 718 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_no_overread.v, with its module paths, module names and numbers changed; 1316 of its 1472 lines of code are new or changed and 1628 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_round_trip_calls.v; 223 of its 404 lines of code are new or changed and 1291 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_round_trip_sd5.v; 310 of its 346 lines of code are new or changed and 368 lines of the source are left out. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger LedgerFacts HState ReaderRes WriterSpec PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import KindBGlue HStateRoom fuzz_free_c fuzz_malloc_c preset_base64_encode_c preset_base64_decode_c pj_string_c pj_set_c pj_free_c pj_parse_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterApp WriterAppFacts WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import put_c put_string_c indent_c write_value_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import check_round_trip_runs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import check_round_trip_c check_round_trip_glue check_round_trip_calls check_round_trip_stages_a check_round_trip_st8.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c pj_get_c pj_get_str_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF ReaderResCF.

(* check_round_trip (check_4, plain, 0x138ac): the statements of stages 7 to 0, in the form of St8
   (check_round_trip_st8.v). St_i is the state at the entry of the callee of call c_i, the end state of the stretch
   crt_r_i of check_round_trip_runs.v, down to the post; st_i : St_(i+1) -> St_i runs the wrapper of c_i
   (check_round_trip_calls.v), then crt_r_(i+1), then St_(i+1).
   The leading arguments are those of St8: Section ST of check_round_trip_stages_a.v, then fx0, fx and the two
   hypotheses of Section F2 of check_round_trip_stages_b.v. The frame: v at sp+80, state at sp+136, doc at sp+192,
   n at sp+8 (sp = spZ regs - 336). Registers: s0 = x8 (text q), s1 = x9 (want), s2 = x18 (same), s3 = x19 (len),
   s4 = x20 (body b), s5 = x21 (input t before c3, back b1 after it), s6 = x22.
   The allocation count: c0..c3 and the pj_string calls one each, the pj_set calls at most three each; St_i keeps
   room for the 68 - u_i of CRT_ALLOCS and the 160 - u_i of CRT_OPS the calls from c_i on use, where u_i is what
   c0..c_(i-1) used (u_7 = 9, u_6 = 8, u_5 = 5, u_4 = 4, u_3 = 3, u_2 = 2, u_1 = 1, u_0 = 0). *)

(* Stage 7, at the entry of c7 = pj_set(&doc, "carries", &v) with ra = 0x13bf4.
   Against St8: v (Dv, from c6) holds the string CRT_STATE and X holds its blocks; the doc has its first member. *)
Definition St7 : Prop :=
  forall (rc : YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16594 -> ms_free B = 0x16454 -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = strtod_c.STRTOD_TP -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = strtod_c.STRTOD_GOT_GUARD -> ms_guard B = strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Dv bs b kb,
  CR B API L A regs mem md Lam peak cnt bnd X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 59 <= cnt + CRT_ALLOCS -> (151 <= Nc)%nat ->
  Permutation X (Dd ++ Dv ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj [(CRT_FORMAT, JStr CRT_FMT2)]) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 80) (JStr CRT_STATE) Dv ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13bf4 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 192) ->
  getr regsc 11 = Z_to_bv 64 0x102ba -> getr regsc 12 = Z_to_bv 64 (spZ regs - 336 + 80) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_SET) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

(* Stage 6, at the entry of c6 = pj_string(&v, PRESET_CARRIES_STATE) (0x102f8) with ra = 0x13bdc.
   Against St7: no fact on v (pj_string writes it); X is the doc's blocks and the two decoder blocks. *)
Definition St6 : Prop :=
  forall (rc : YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16594 -> ms_free B = 0x16454 -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = strtod_c.STRTOD_TP -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = strtod_c.STRTOD_GOT_GUARD -> ms_guard B = strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd bs b kb,
  CR B API L A regs mem md Lam peak cnt bnd X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 60 <= cnt + CRT_ALLOCS -> (152 <= Nc)%nat ->
  Permutation X (Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj [(CRT_FORMAT, JStr CRT_FMT2)]) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13bdc -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 80) ->
  getr regsc 11 = Z_to_bv 64 0x102f8 ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_STRING) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

(* Stage 5, at the entry of c5 = pj_set(&doc, "format", &v) (0x1036e) with ra = 0x13bc8.
   Against St6: the doc is the empty object pj_object made (no blocks); v (Dv, from c4) holds CRT_FMT2. *)
Definition St5 : Prop :=
  forall (rc : YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16594 -> ms_free B = 0x16454 -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = strtod_c.STRTOD_TP -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = strtod_c.STRTOD_GOT_GUARD -> ms_guard B = strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dv bs b kb,
  CR B API L A regs mem md Lam peak cnt bnd X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 63 <= cnt + CRT_ALLOCS -> (155 <= Nc)%nat ->
  Permutation X (Dv ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj []) [] ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 80) (JStr CRT_FMT2) Dv ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13bc8 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 192) ->
  getr regsc 11 = Z_to_bv 64 0x1036e -> getr regsc 12 = Z_to_bv 64 (spZ regs - 336 + 80) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_SET) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

(* Stage 4, at the entry of c4 = pj_string(&v, PRESET_FORMAT_STATE) (0x1037a) with ra = 0x13bb0, after the
   comparison of back with the body and pj_object(&doc), pj_object(&state) (crt_r4).
   Against St5: no fact on v; X is exactly the decoder's block (b1, from c3) and the encoder's text (q, from c0). *)
Definition St4 : Prop :=
  forall (rc : YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16594 -> ms_free B = 0x16454 -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = strtod_c.STRTOD_TP -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = strtod_c.STRTOD_GOT_GUARD -> ms_guard B = strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 bs b kb,
  CR B API L A regs mem md Lam peak cnt bnd [(b1, k1); (q, kq)] [(same, sn); (want, wn)]
    Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 64 <= cnt + CRT_ALLOCS -> (156 <= Nc)%nat ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj []) [] ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13bb0 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 80) ->
  getr regsc 11 = Z_to_bv 64 0x1037a ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_STRING) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

(* Stage 3, at the entry of c3 = preset_base64_decode(text, &n) with ra = 0x13b64, after expected_text, the
   length check of text, canonical(input, same) and the two strcmp (crt_r3).
   Against St4: no doc or state yet (crt_r4 makes them); X is the text only; s5 is free (crt_r3 uses it). *)
Definition St3 : Prop :=
  forall (rc : YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16594 -> ms_free B = 0x16454 -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = strtod_c.STRTOD_TP -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = strtod_c.STRTOD_GOT_GUARD -> ms_guard B = strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq bs b kb,
  CR B API L A regs mem md Lam peak cnt bnd [(q, kq)] [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 65 <= cnt + CRT_ALLOCS -> (157 <= Nc)%nat ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13b64 -> getr regsc 10 = Z_to_bv 64 q ->
  getr regsc 11 = Z_to_bv 64 (spZ regs - 336 + 8) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same ->
  0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PRESET_BASE64_DECODE) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

(* Stage 2, at the entry of c2 = malloc(strlen(input) + 1) with ra = 0x1392c.
   Against St3: no same yet; want has the size (len + 2) / 3 * 4 + 1 expected_text writes; the input t (in a block
   of the caller) holds tb, whose decoding is the body, for canonical(input, same); s5 = t and s6 = the encoding's
   length, which crt_r3 reads. *)
Definition St2 : Prop :=
  forall (rc : YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16594 -> ms_free B = 0x16454 -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = strtod_c.STRTOD_TP -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = strtod_c.STRTOD_GOT_GUARD -> ms_guard B = strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall Lc Ac regsc memc mdc Lamc peakc cntc Nc want wn q kq bs b kb t tb,
  CR B API L A regs mem md Lam peak cnt bnd [(q, kq)] [(want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 66 <= cnt + CRT_ALLOCS -> (158 <= Nc)%nat ->
  wn = (Z.of_nat (length bs) + 2) / 3 * 4 + 1 ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  Mem.bytes_at rsegs memc t (tb ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) tb -> Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
  (exists pt kt, In (pt, kt) (blocks L A) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
  b64_dec (zs tb) = Some bs ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x1392c -> getr regsc 10 = Z_to_bv 64 (Z.of_nat (length tb) + 1) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 t -> getr regsc 22 = Z_to_bv 64 ((Z.of_nat (length bs) + 2) / 3 * 4) ->
  getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 0x16594) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

(* Stage 1, at the entry of c1 = malloc((len + 2) / 3 * 4 + 1) with ra = 0x13918.
   Against St2: no want yet; t's string comes with the slack and alignment strlen(input) (crt_r2) reads. *)
Definition St1 : Prop :=
  forall (rc : YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16594 -> ms_free B = 0x16454 -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = strtod_c.STRTOD_TP -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = strtod_c.STRTOD_GOT_GUARD -> ms_guard B = strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall Lc Ac regsc memc mdc Lamc peakc cntc Nc q kq bs b kb t tb slack,
  CR B API L A regs mem md Lam peak cnt bnd [(q, kq)] [] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 67 <= cnt + CRT_ALLOCS -> (159 <= Nc)%nat ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  Mem.bytes_at rsegs memc t (tb ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) tb ->
  (- (t + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
  (exists pt kt, In (pt, kt) (blocks L A) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
  b64_dec (zs tb) = Some bs ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13918 ->
  getr regsc 10 = Z_to_bv 64 ((Z.of_nat (length bs) + 2) / 3 * 4 + 1) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 t -> getr regsc 22 = Z_to_bv 64 ((Z.of_nat (length bs) + 2) / 3 * 4) ->
  getr regsc 8 = Z_to_bv 64 q ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 0x16594) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).

(* Stage 0, at the entry of c0 = preset_base64_encode(body, len) with ra = 0x138f4, right after the prologue
   (crt_r0): a0 = body, a1 = len, s3 = len, s4 = body, s5 = input. The facts are those of
   check_round_trip_contract for the input (t, tb, slack) and the body (b, bs), with bytes_ok bs and the length
   bound of bs from its decoding, and CR with nothing held.
   Against St1: no text yet (X = []); s0 and s6 are not yet set. *)
Definition St0 : Prop :=
  forall (rc : YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16594 -> ms_free B = 0x16454 -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = strtod_c.STRTOD_TP -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = strtod_c.STRTOD_GOT_GUARD -> ms_guard B = strtod_c.STRTOD_GUARD ->
  strlen_contract -> strcmp_contract -> bcmp_contract -> pj_object_contract -> pj_get_contract ->
  pj_get_str_contract ->
  (forall fx' : YK11.FPState, malloc_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, free_contract (fx := fx') B API) ->
  (forall fx' : YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_string_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_set_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_free_contract (fx := fx') B API sb_form) ->
  (forall fx' : YK11.FPState, pj_write_contract_sb (fx := fx') B API) ->
  (forall fx' : YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  forall (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  call_pre_k B (aa_MR API) CRT_STK L A regs mem md ->
  forall (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound),
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt + CRT_ALLOCS < 2 ^ 63 -> spZ regs <= 2 ^ 47 ->
  strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK ->
  forall (fx0 fx : YK11.FPState), fregs_kept fx0 fx -> frm_zero (@fp_csr fx) ->
  forall Lc Ac regsc memc mdc Lamc peakc cntc Nc bs b kb t tb slack,
  CR B API L A regs mem md Lam peak cnt bnd [] [] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 68 <= cnt + CRT_ALLOCS -> (160 <= Nc)%nat ->
  bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  Mem.bytes_at rsegs memc t (tb ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) tb ->
  (- (t + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
  (exists pt kt, In (pt, kt) (blocks L A) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
  b64_dec (zs tb) = Some bs ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x138f4 -> getr regsc 10 = Z_to_bv 64 b ->
  getr regsc 11 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 t ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PRESET_BASE64_ENCODE) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).
