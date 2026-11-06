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
  check_round_trip_runs check_round_trip_calls check_round_trip_stages_a.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c
  pj_get_c pj_get_str_c.

(* check_round_trip (check_4, plain, 0x138ac): the statement of stage 8, the interface between the stages from c8 to
   the end and the stages from the function's entry to c8. *)

(* The literals of c4..c7: pj_string(&v, PRESET_FORMAT_STATE) (0x1037a), pj_set(&doc, "format", &v) (0x1036e),
   pj_string(&v, PRESET_CARRIES_STATE) (0x102f8, CRT_STATE), pj_set(&doc, "carries", &v) (0x102ba). *)
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

(* The document's members after c7: pj_set(&doc, "format", ...) then pj_set(&doc, "carries", ...). *)
Definition crt_doc8 : list (list Z * jv) := [(CRT_FORMAT, JStr CRT_FMT2); (CRT_CARRIES, JStr CRT_STATE)].

(* Stage 8, at the entry of c8 = pj_string(&v, PRESET_ENCODING_BASE64) with ra = 0x13c08, down to the post.
   The arguments before X are the variables and hypotheses of Section ST of check_round_trip_stages_a.v, in the order
   of its PFX, then the FP state fx and the two hypotheses of its Section F (F2 of check_round_trip_stages_b.v).
   The frame: back at sp+24, v at sp+80, state at sp+136, doc at sp+192 (sp = spZ regs - 336).
   X: the doc's blocks Dd, back (b1, from c3) and text (q, from c0); P: same and want (c2, c1).
   Before c8 the function used 12 allocations (c0..c3 one each, c4 and c6 one each, c5 and c7 at most three each)
   and 12 of the CRT_OPS = 160 operations of the bound. *)
Definition St8 : Prop :=
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
  cntc + 56 <= cnt + CRT_ALLOCS -> (148 <= Nc)%nat ->
  Permutation X (Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj crt_doc8) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13c08 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 80) ->
  getr regsc 11 = Z_to_bv 64 0x103c5 ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_STRING) memc (seg_rom (ms_segs B))) mdc)
    (crt_post B API L A regs mem md Lam peak cnt bnd fx0).
