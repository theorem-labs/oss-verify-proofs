From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 FrameAPI SlotPack KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger GIInit LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require fuzz_alloc_live_c fuzz_alloc_peak_c fuzz_alloc_peak_reset_c fuzz_alloc_count_c fuzz_alloc_fail_c strlen_c strcmp_c bcmp_c memcpy_c memset_c memchr_c memcmp_c memcpy_same_c strtod_c snprintf_c snprintf_stk_c put_utf8_c hex4_c literal_c skip_ws_c pj_get_c pj_get_str_c ex_hex4_c ex_string_c ex_word_c ex_ws_c ex_value_c same_c check_reject_clean_c check_bounded_alloc_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require fuzz_malloc_c fuzz_free_c fuzz_realloc_c fuzz_strdup_c pj_parse_c pj_free_c pj_string_c pj_set_c grow_c parse_string_c parse_value_c parse_items_c put_c indent_c put_string_c write_value_c pj_write_c tx_put_c tx_line_c tx_string_c tx_value_c check_as_written_c check_no_overread_c check_reject_clean_starved_c round_trip_text_c check_round_trip_c PjWriteNeed PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require bcmp check_bounded_alloc check_reject_clean ex_hex4 ex_word ex_ws fuzz_alloc_count fuzz_alloc_fail fuzz_alloc_live fuzz_alloc_peak fuzz_alloc_peak_reset hex4 literal memchr memcmp memcpy memcpy_same memset pj_get pj_get_str put_utf8 same skip_ws snprintf strcmp strlen strtod.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require PjWriteAdapt ReaderLink check_as_written check_no_overread check_reject_clean_starved check_round_trip ex_string ex_value fuzz_free fuzz_malloc fuzz_realloc fuzz_strdup indent pj_write put put_string round_trip_text tx_line tx_put tx_string tx_value write_value.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require
  fuzz_alloc_ran_out_c fuzz_alloc_ran_out_reset_c fuzz_alloc_ran_out fuzz_alloc_ran_out_reset
  fuzz_alloc_most_c fuzz_alloc_most read_members_c read_members.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require parse_noting_c parse_noting.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocAgCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Local Open Scope Z_scope.

(* Second build, cut-free (SR is SRcf, CF/SRCF.v): every callee contract of the entry at F := pack_ag_form
   (lib/U/AllocAgCf.v), bottom-up from the slot givens and the cut-free allocator contracts MALR FREER REALR
   REALNR. *)
Section LinkU.
Context {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil} {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SYMS : slot_syms B.
Hypothesis GLOB : slot_globals B.
Hypothesis FA : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis MALR : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @malloc_contract_r fx' rc B API pack_ag_form.
Hypothesis FREER : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @free_contract_r fx' rc B API pack_ag_form.
Hypothesis REALR : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @realloc_contract_r fx' rc B API pack_ag_form 0x19bfc.
Hypothesis REALNR : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @realloc_null_contract_r fx' rc B API pack_ag_form 0x19bfc.

Lemma lu_segs : ms_segs B = rsegs.
Proof. exact (proj1 SYMS). Qed.

(* the #102 ubsan allocator entries, as the contract's slot_syms states them (default_malloc 0x18390, free 0x18250,
   realloc 0x19bfc in the twin 27566683952ebd54's symtab) *)
Lemma lu_malloc_at : ms_malloc B = 0x18390.
Proof. destruct SYMS as (_ & H & _). exact H. Qed.

Lemma lu_free_at : ms_free B = 0x18250.
Proof. destruct SYMS as (_ & _ & H & _). exact H. Qed.

Lemma lu_realloc_at : ms_realloc B = Some 0x19bfc.
Proof. destruct SYMS as (_ & _ & _ & H & _). exact H. Qed.

Lemma lu_errno : errno_addr B + 4 <= alloc_ceiling.
Proof.
  destruct SYMS as (_ & _ & _ & _ & _ & _ & Htp & Heo). unfold errno_addr. rewrite Htp, Heo.
  pose proof (@alloc_ceiling_value rc) as H. lia.
Qed.

Lemma lu_ax : AllocExtra B (aa_MR API).
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lu_ctx : ctx_owned B API.
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lu_slack : block_slack_present B API.
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lu_errno_unowned : errno_unowned B API.
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lu_frame_own : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lu_frame_G : forall a, in_globals frame_G a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros a (lo & len & Hin & Hr).
  assert (H : slot_apart B a).
  { apply GLOB. exists lo, len. split; [|exact Hr].
    unfold slot_G, frame_G in *. exact Hin. }
  exact H.
Qed.

Lemma lu_globals : globals_free B API omx_G.
Proof. exact (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.fuzz_malloc.omx_globals_free fx rc B API lu_segs lu_ax lu_frame_own lu_frame_G). Qed.

Lemma lu_malloc_r : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @malloc_contract_r fx' rc B API pack_ag_form.
Proof. exact MALR. Qed.

Lemma lu_free_r : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @free_contract_r fx' rc B API pack_ag_form.
Proof. exact FREER. Qed.

Lemma lu_realloc_r : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @realloc_contract_r fx' rc B API pack_ag_form 0x19bfc.
Proof. exact REALR. Qed.

Lemma lu_realloc_null_r : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @realloc_null_contract_r fx' rc B API pack_ag_form 0x19bfc.
Proof. exact REALNR. Qed.

Lemma lu_strlen : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strlen_c.strlen_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strlen.strlen_holds. Qed.
Lemma lu_strcmp : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strcmp_c.strcmp_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strcmp.strcmp_holds. Qed.
Lemma lu_bcmp : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.bcmp_c.bcmp_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.bcmp.bcmp_holds. Qed.
Lemma lu_memcpy : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.memcpy_c.memcpy_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.memcpy.memcpy_holds. Qed.
Lemma lu_memset : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.memset_c.memset_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.memset.memset_holds. Qed.
Lemma lu_memchr : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.memchr_c.memchr_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.memchr.memchr_holds. Qed.
Lemma lu_memcmp : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.memcmp_c.memcmp_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.memcmp.memcmp_holds. Qed.
Lemma lu_memcpy_same : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.memcpy_same_c.memcpy_same_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.memcpy_same.memcpy_same_holds. Qed.
Lemma lu_strtod : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.strtod_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod.strtod_holds. Qed.
Lemma lu_snprintf : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.snprintf_c.snprintf_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.snprintf.snprintf_holds. Qed.
Lemma lu_snprintf_stk : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.snprintf_stk_c.snprintf_stk_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.snprintf.snprintf_stk_holds. Qed.
Lemma lu_put_utf8 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.put_utf8_c.put_utf8_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.put_utf8.put_utf8_holds. Qed.
Lemma lu_hex4 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.hex4_c.hex4_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.hex4.hex4_holds. Qed.
Lemma lu_literal : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.literal_c.literal_contract.
Proof. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.literal.literal_holds lu_strlen lu_bcmp). Qed.
Lemma lu_skip_ws : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.skip_ws_c.skip_ws_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.skip_ws.skip_ws_holds. Qed.

Lemma lu_alloc_live : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_live_c.fuzz_alloc_live_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_live.fuzz_alloc_live_holds. Qed.
Lemma lu_alloc_peak : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_peak_c.fuzz_alloc_peak_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_peak.fuzz_alloc_peak_holds. Qed.
Lemma lu_alloc_peak_reset : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_peak_reset_c.fuzz_alloc_peak_reset_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_peak_reset.fuzz_alloc_peak_reset_holds. Qed.
Lemma lu_alloc_count : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_count_c.fuzz_alloc_count_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_count.fuzz_alloc_count_holds. Qed.
Lemma lu_alloc_fail : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_fail_c.fuzz_alloc_fail_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_fail.fuzz_alloc_fail_holds. Qed.

Lemma lu_fuzz_malloc : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.fuzz_malloc_c.fuzz_malloc_contract fx' rc B API pack_ag_form.
Proof.
  intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.fuzz_malloc.fuzz_malloc_holds B API pack_ag_form lu_segs lu_malloc_at lu_errno lu_globals (lu_malloc_r fx')).
Qed.

Lemma lu_fuzz_free : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.fuzz_free_c.fuzz_free_contract fx' rc B API pack_ag_form.
Proof.
  intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.fuzz_free.fuzz_free_holds B API pack_ag_form lu_segs lu_free_at lu_frame_G lu_ax lu_frame_own (lu_free_r fx')).
Qed.

Lemma lu_fuzz_realloc : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.fuzz_realloc_c.fuzz_realloc_contract fx' rc B API pack_ag_form.
Proof.
  intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.fuzz_realloc.fuzz_realloc_holds B API lu_segs lu_errno lu_globals pack_ag_form (lu_realloc_r fx') (lu_fuzz_malloc fx')).
Qed.

Lemma lu_fuzz_strdup : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.fuzz_strdup_c.fuzz_strdup_contract fx' rc B API pack_ag_form.
Proof.
  intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.fuzz_strdup.fuzz_strdup_holds B API pack_ag_form lu_segs lu_errno lu_strlen lu_memcpy (lu_fuzz_malloc fx')).
Qed.

Lemma lu_reader : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState,
  @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_parse_c.pj_parse_contract fx' rc B API pack_ag_form /\ @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_free_c.pj_free_contract fx' rc B API pack_ag_form /\
  @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_string_c.pj_string_contract fx' rc B API pack_ag_form /\ @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_set_c.pj_set_contract fx' rc B API pack_ag_form /\
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.pj_get_c.pj_get_contract /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.pj_get_str_c.pj_get_str_contract /\
  @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.grow_c.grow_contract fx' rc B API pack_ag_form /\ @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.parse_string_c.parse_string_contract fx' rc B API pack_ag_form /\
  (forall d, (d <= MAXD)%nat ->
     @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.parse_value_c.parse_value_contract fx' rc B API pack_ag_form d /\ @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.parse_items_c.parse_items_contract fx' rc B API pack_ag_form d).
Proof.
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.ReaderLink.reader_link B API pack_ag_form lu_ax lu_ctx lu_errno_unowned lu_fuzz_malloc lu_fuzz_free lu_fuzz_realloc
    lu_fuzz_strdup lu_memset lu_memcpy lu_strtod lu_strcmp lu_literal lu_put_utf8 lu_hex4 lu_skip_ws).
Qed.

Lemma lu_pj_parse : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_parse_c.pj_parse_contract fx' rc B API pack_ag_form.
Proof. intros fx'. exact (proj1 (lu_reader fx')). Qed.
Lemma lu_pj_free : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_free_c.pj_free_contract fx' rc B API pack_ag_form.
Proof. intros fx'. exact (proj1 (proj2 (lu_reader fx'))). Qed.
Lemma lu_pj_string : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_string_c.pj_string_contract fx' rc B API pack_ag_form.
Proof. intros fx'. destruct (lu_reader fx') as (_ & _ & H & _). exact H. Qed.
Lemma lu_pj_set : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_set_c.pj_set_contract fx' rc B API pack_ag_form.
Proof. intros fx'. destruct (lu_reader fx') as (_ & _ & _ & H & _). exact H. Qed.
Lemma lu_pj_get : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.pj_get_c.pj_get_contract.
Proof. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.pj_get.pj_get_holds lu_strcmp). Qed.
Lemma lu_pj_get_str : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.pj_get_str_c.pj_get_str_contract.
Proof. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.pj_get_str.pj_get_str_holds lu_pj_get). Qed.
Lemma lu_grow : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.grow_c.grow_contract fx' rc B API pack_ag_form.
Proof. intros fx'. destruct (lu_reader fx') as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma lu_parse_string : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.parse_string_c.parse_string_contract fx' rc B API pack_ag_form.
Proof. intros fx'. destruct (lu_reader fx') as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lu_put : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.put_c.put_contract fx' rc B API pack_ag_form.
Proof. intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.put.put_holds B API pack_ag_form (lu_fuzz_realloc fx') lu_memcpy). Qed.

Lemma lu_indent : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.indent_c.indent_contract fx' rc B API pack_ag_form.
Proof. intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.indent.indent_holds B API pack_ag_form lu_segs lu_ax lu_ctx (lu_put fx')). Qed.

Lemma lu_put_string : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.put_string_c.put_string_contract fx' rc B API pack_ag_form.
Proof. intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.put_string.put_string_holds B API pack_ag_form lu_ax lu_ctx lu_put lu_snprintf lu_strlen). Qed.

Lemma lu_write_value : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.write_value_c.write_value_contract fx' rc B API pack_ag_form.
Proof.
  intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.write_value.write_value_holds B API pack_ag_form lu_ax lu_ctx lu_put lu_indent lu_put_string lu_strlen lu_slack).
Qed.

Lemma lu_pj_write : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.pj_write_contract fx' rc B API pack_ag_form.
Proof.
  intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write.pj_write_holds B API pack_ag_form lu_segs lu_ax lu_ctx (lu_write_value fx') lu_put lu_fuzz_free).
Qed.

Lemma lu_tx_put : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.tx_put_c.tx_put_contract fx' rc B API pack_ag_form.
Proof.
  intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.tx_put.tx_put_holds B API pack_ag_form lu_segs lu_errno lu_malloc_at (lu_realloc_r fx') (lu_realloc_null_r fx') lu_memcpy).
Qed.

Lemma lu_tx_line : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.tx_line_c.tx_line_contract fx' rc B API pack_ag_form.
Proof. intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.tx_line.tx_line_holds B API lu_segs lu_errno lu_ax lu_ctx pack_ag_form (lu_tx_put fx')). Qed.

Lemma lu_tx_string : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.tx_string_c.tx_string_contract fx' rc B API pack_ag_form.
Proof. intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.tx_string.tx_string_holds B API lu_segs lu_errno lu_ax lu_ctx lu_globals pack_ag_form (lu_tx_put fx')). Qed.

Lemma lu_tx_value : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.tx_value_c.tx_value_contract fx' rc B API pack_ag_form.
Proof.
  intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.tx_value.tx_value_holds B API lu_segs lu_errno lu_ax lu_ctx lu_globals lu_slack pack_ag_form
    (lu_tx_put fx') (lu_tx_line fx') (lu_tx_string fx') lu_strlen).
Qed.

Lemma lu_ex_hex4 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.ex_hex4_c.ex_hex4_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.ex_hex4.ex_hex4_holds. Qed.
Lemma lu_ex_string : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.ex_string_c.ex_string_contract.
Proof. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.ex_string.ex_string_holds lu_ex_hex4). Qed.
Lemma lu_ex_word : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.ex_word_c.ex_word_contract.
Proof. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.ex_word.ex_word_holds lu_strlen lu_bcmp). Qed.
Lemma lu_ex_ws : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.ex_ws_c.ex_ws_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.ex_ws.ex_ws_holds. Qed.
Lemma lu_ex_value : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.ex_value_c.ex_value_contract.
Proof. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.ex_value.ex_value_holds lu_ex_string lu_ex_word lu_strcmp lu_bcmp lu_memcpy lu_strtod lu_ex_ws). Qed.
Lemma lu_same : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.same_c.same_contract.
Proof. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.same.same_holds lu_strcmp lu_bcmp). Qed.
Lemma lu_check_reject_clean : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.check_reject_clean_c.check_reject_clean_contract.
Proof. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.check_reject_clean.check_reject_clean_holds lu_alloc_live lu_bcmp). Qed.
Lemma lu_check_bounded_alloc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.check_bounded_alloc_c.check_bounded_alloc_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.check_bounded_alloc.check_bounded_alloc_holds. Qed.

Lemma lu_alloc_ran_out_reset : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_ran_out_reset_c.fuzz_alloc_ran_out_reset_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_ran_out_reset.fuzz_alloc_ran_out_reset_holds. Qed.
Lemma lu_alloc_ran_out : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_ran_out.fuzz_alloc_ran_out_holds. Qed.
Lemma lu_alloc_most : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_most_c.fuzz_alloc_most_contract.
Proof. exact OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.fuzz_alloc_most.fuzz_alloc_most_holds. Qed.

Lemma lu_check_as_written : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.check_as_written_c.check_as_written_contract fx' rc B API pack_ag_form.
Proof.
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.check_as_written.check_as_written_holds B API pack_ag_form lu_malloc_at lu_free_at lu_ax lu_errno_unowned
    lu_malloc_r lu_free_r lu_ex_value lu_ex_ws lu_globals lu_alloc_ran_out).
Qed.
Lemma lu_read_members : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.read_members_c.read_members_contract.
Proof. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.read_members.read_members_holds lu_pj_get lu_pj_get_str). Qed.

Lemma lu_parse_noting : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.parse_noting_c.parse_noting_contract fx' rc B API pack_ag_form.
Proof.
  intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.parse_noting.parse_noting_holds B API pack_ag_form lu_globals
    lu_alloc_live lu_alloc_ran_out_reset (lu_pj_parse fx') lu_alloc_ran_out).
Qed.

Lemma lu_check_no_overread : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.check_no_overread_c.check_no_overread_contract fx' rc B API pack_ag_form.
Proof.
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.check_no_overread.check_no_overread_holds B API pack_ag_form lu_malloc_at lu_free_at lu_ax lu_globals
    lu_malloc_r lu_free_r lu_memcpy lu_memset lu_parse_noting lu_pj_free lu_same).
Qed.

Lemma lu_not_owned_hi : forall L A mem md a, aa_MR API L A mem md -> alloc_ceiling <= a -> ~ owned B L A a.
Proof. intros L A mem md a M Ha O. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M O). lia. Qed.

Lemma lu_pj_write_need : forall KW : Z,
  (forall t, (PjTree.depth t <= 32)%nat -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.PJW_K t <= KW) ->
  forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState,
    @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.PjWriteNeed.pj_write_need fx' rc B API pack_ag_form KW.
Proof.
  intros KW HK fx'. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.PjWriteNeed.pj_write_need.
  intros L A regs mem md b v pretty t D Lam peak cnt fail SEG GG GD PRE INIT RO FRM R10 R11 HPR LG OFF PN PW DIN DEP
    D32 WL RFOK RM.
  pose proof (HK t D32) as Kt.
  pose proof lu_errno as HE. pose proof (@alloc_ceiling_value rc) as HCV.
  unfold call_pre_t, call_pre_k in PRE.
  destruct PRE as ((HM & HWF & HB & Hra & Hal & Hceil & Hsp & HWs & Htp & HWe & Haux) & HTS).
  assert (PRE' : call_pre_t B API (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.PJW_K t) L A regs mem md).
  { unfold call_pre_t, call_pre_k.
    refine (conj (conj HM (conj HWF (conj HB (conj Hra (conj Hal (conj _ (conj Hsp (conj _ (conj Htp (conj HWe Haux))))))))))
      HTS); [lia | intros a Ha; apply HWs; lia]. }
  assert (OFF' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.put_c.off_errno B
                   (spZ regs - OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.PJW_K t)
                   (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.PJW_K t))
    by (unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.put_c.off_errno in *; lia).
  pose proof (lu_pj_write fx' L A regs mem md b v pretty t D Lam peak cnt fail SEG GG GD PRE' INIT RO FRM R10 R11 HPR LG
    OFF' PN PW DIN DEP WL RFOK RM) as SRC.
  eapply SR_mono; [exact SRC|].
  intros c' RET. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.pj_write_ret in RET |- *.
  cbv zeta in RET |- *.
  destruct RET as (fx2 & L' & A' & regs' & mem' & md' & Lam' & peak' & b' & E1 & E2 & E3 & E4 & HM' & E6 & E7 & E8 & E9 &
    E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & FR & WW & RES).
  exists fx2, L', A', regs', mem', md', Lam', peak', b'.
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact HM'|].
  split; [exact E6|]. split; [exact E7|]. split; [exact E8|]. split; [exact E9|]. split; [exact E10|].
  split; [exact E11|]. split; [exact E12|]. split; [exact E13|]. split; [exact E14|]. split; [exact E15|].
  split; [exact E16|]. split; [exact E17|]. split; [exact E18|].
  split.
  { intros a H1 H2 H3 H4 H5 H6. apply FR; try assumption. lia. }
  split; [|exact RES].
  intros a Ha Hw.
  destruct (Z_lt_le_dec a (spZ regs - OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.PJW_K t))
    as [Hlo|Hhi].
  - destruct Ha as [Ha|Ha]; [|exact (WW a (or_intror Ha) Hw)].
    assert (Hc : alloc_ceiling <= a) by lia.
    refine (proj1 (proj2 (FR a _ _ _ _ _ _)) Hw).
    + left; lia.
    + exact (lu_not_owned_hi L A mem md a HM Hc).
    + exact (lu_not_owned_hi L' A' mem' md' a HM' Hc).
    + lia.
    + intros He. hnf in He. lia.
    + intros Hs. hnf in Hs. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hs. lia.
  - apply WW; [|exact Hw]. destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha].
Qed.

Definition LU_KW : Z := 12768.

Lemma lu_pjw_kw : forall t, (PjTree.depth t <= 32)%nat ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.PJW_K t <= LU_KW.
Proof.
  intros t Hd. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.PJW_K,
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.write_value_c.WV_K, LU_KW.
  assert (H0 : 0 <= Z.of_nat (PjTree.depth t) <= 32) by lia.
  assert (C : 0 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.write_value_c.WV_FR /\
              OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.PJW_FR +
                Z.max (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.write_value_c.WV_FR * 33 +
                       OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.write_value_c.WV_KMAX)
                      (Z.max OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.put_c.PUT_K ALLOC_STACK)
                <= 12768 /\ 0 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.PJW_FR /\
              0 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.write_value_c.WV_KMAX)
    by (vm_compute; repeat split; discriminate).
  destruct C as (C1 & C2 & C3 & C4).
  assert (M : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.write_value_c.WV_FR * (Z.of_nat (PjTree.depth t) + 1)
              <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.write_value_c.WV_FR * 33) by nia.
  lia.
Qed.

Lemma lu_check_reject_clean_starved_kw : forall KW : Z,
  (forall t, (PjTree.depth t <= 32)%nat -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.PJW_K t <= KW) ->
  forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.check_reject_clean_starved_c.check_reject_clean_starved_contract fx' rc B API pack_ag_form KW.
Proof.
  intros KW HK fx'.
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.check_reject_clean_starved.check_reject_clean_starved_holds B API KW pack_ag_form lu_ax lu_globals
    lu_alloc_live lu_alloc_count lu_alloc_fail lu_check_reject_clean lu_pj_parse (lu_pj_write_need KW HK) lu_fuzz_free).
Qed.

Lemma lu_check_reject_clean_starved : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState,
  @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.check_reject_clean_starved_c.check_reject_clean_starved_contract fx' rc B API pack_ag_form LU_KW.
Proof. exact (lu_check_reject_clean_starved_kw LU_KW lu_pjw_kw). Qed.

Lemma lu_round_trip_text : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.round_trip_text_c.round_trip_text_contract fx' rc B API pack_ag_form.
Proof.
  intros fx'.
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.round_trip_text.round_trip_text_holds_w B API pack_ag_form lu_segs FA lu_free_at lu_free_r lu_pj_write
    lu_tx_put lu_tx_value lu_strcmp lu_strlen lu_same lu_memcpy lu_parse_noting lu_alloc_ran_out lu_fuzz_free lu_pj_free).
Qed.

Lemma lu_pj_write_hyp : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.PjWriteHyp.pj_write_hyp fx' rc B API pack_ag_form OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.PJW_K.
Proof. intros fx'. exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.PjWriteAdapt.pj_write_adapt B API pack_ag_form lu_ax lu_pj_write). Qed.

Lemma lu_check_round_trip : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.check_round_trip_c.check_round_trip_contract fx' rc B API pack_ag_form.
Proof.
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.check_round_trip.check_round_trip_holds B API pack_ag_form lu_ax lu_globals lu_round_trip_text lu_pj_string lu_pj_set
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.pj_write_c.PJW_K OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.round_trip_text.rtt_pjw_k lu_pj_write_hyp lu_parse_noting lu_fuzz_free lu_pj_free
    lu_strlen lu_strcmp lu_same lu_memset lu_alloc_ran_out).
Qed.

End LinkU.
