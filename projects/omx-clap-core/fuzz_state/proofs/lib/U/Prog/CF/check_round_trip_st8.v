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
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/check_round_trip_stdefs.v, with its addresses and numbers changed; 26 of its 98 lines of code are new or changed and 283 lines of the source are left out. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import check_round_trip_c check_round_trip_glue check_round_trip_calls check_round_trip_stages_a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require HsKindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require check_reject_clean_starved past_nul.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c pj_get_c pj_get_str_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.


Definition CRT_FORMAT : list Z := [102; 111; 114; 109; 97; 116].
Definition CRT_CARRIES : list Z := [99; 97; 114; 114; 105; 101; 115].
Definition CRT_FMT2 : list Z :=
  [111; 114; 103; 46; 111; 112; 101; 110; 109; 105; 120; 101; 114; 46; 112; 114; 101; 115; 101; 116; 47; 50].

Lemma crt_cb_format : forall m, mem_inv rsegs m -> pj_cbytes rsegs m 0x1036e CRT_FORMAT.
Proof.
  intros m MI. apply crt_lit; [exact MI | unfold CRT_FORMAT; repeat constructor; lia | lia | cbn; lia |].
  intros i Hi. cbn [length CRT_FORMAT app] in Hi.
  do 7 (destruct i as [|i]; [split; vm_compute; reflexivity|]). lia.
Qed.

Lemma crt_cb_carries : forall m, mem_inv rsegs m -> pj_cbytes rsegs m 0x102ba CRT_CARRIES.
Proof.
  intros m MI. apply crt_lit; [exact MI | unfold CRT_CARRIES; repeat constructor; lia | lia | cbn; lia |].
  intros i Hi. cbn [length CRT_CARRIES app] in Hi.
  do 8 (destruct i as [|i]; [split; vm_compute; reflexivity|]). lia.
Qed.

Lemma crt_cb_fmt2 : forall m, mem_inv rsegs m -> pj_cbytes rsegs m 0x1037a CRT_FMT2.
Proof.
  intros m MI. apply crt_lit; [exact MI | unfold CRT_FMT2; repeat constructor; lia | lia | cbn; lia |].
  intros i Hi. cbn [length CRT_FMT2 app] in Hi.
  do 23 (destruct i as [|i]; [split; vm_compute; reflexivity|]). lia.
Qed.

Definition crt_doc8 : list (list Z * jv) := [(CRT_FORMAT, JStr CRT_FMT2); (CRT_CARRIES, JStr CRT_STATE)].

Definition St8 : Prop :=
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
  cntc + 56 <= cnt + CRT_ALLOCS -> (148 <= Nc)%nat ->
  Permutation X (Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 192) (JObj crt_doc8) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13d68 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 352 + 80) ->
  getr regsc 11 = Z_to_bv 64 0x103c5 ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_STRING) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).
