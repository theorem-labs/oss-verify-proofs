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
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require LinkU34 EntrySR EntrySRHolds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocAgCf34.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.

(* Copy of CF/LinkUEntry.v at F := pack_ag34_form (the 2^34 law). The ubsan entry link: entry_sr_holds of the U entry composition at F := pack_ag34_form, KW := CF.LinkU34.LU_KW, over the
   callee lemmas of CF.LinkU34.v. Open hypotheses as in LinkU: PI and PV (the reader's parse_items and parse_value steps). *)
Section LinkUEntry34.
Context {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil} {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SYMS : slot_syms B.
Hypothesis GLOB : slot_globals B.
Hypothesis FA : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis MALR : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @malloc_contract_r fx' rc B API pack_ag34_form.
Hypothesis FREER : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @free_contract_r fx' rc B API pack_ag34_form.
Hypothesis REALR : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @realloc_contract_r fx' rc B API pack_ag34_form 0x19bfc.
Hypothesis REALNR : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @realloc_null_contract_r fx' rc B API pack_ag34_form 0x19bfc.
Context {SH : sink_head} {SK : sink_syms}.

Lemma lu_kw0 : 0 <= CF.LinkU34.LU_KW /\ 112 + CF.check_reject_clean_starved_c.CRCS_K CF.LinkU34.LU_KW <= SLOT_K.
Proof. vm_compute. repeat split; discriminate. Qed.

Lemma lu_kw1 : 0 <= CF.LinkU34.LU_KW <= ReaderRes.PJ_PARSE_K.
Proof. vm_compute. repeat split; discriminate. Qed.

Lemma lu_entry_sr : forall ra empty stk, @CF.EntrySR.entry_sr_contract fx rc B API SH SK pack_ag34_form ra empty stk.
Proof.
  intros ra empty stk.
  eapply CF.EntrySRHolds.entry_sr_holds.
  all: first [ exact lu_kw0 | exact lu_kw1
             | eapply CF.LinkU34.lu_segs; eassumption | exact FA
             | eapply CF.LinkU34.lu_check_no_overread; eassumption | eapply CF.LinkU34.lu_parse_noting; eassumption
             | eapply CF.LinkU34.lu_check_as_written; eassumption
             | eapply CF.LinkU34.lu_check_reject_clean_starved; eassumption
             | eapply CF.LinkU34.lu_check_round_trip; eassumption | eapply CF.LinkU34.lu_pj_free; eassumption
             | eapply CF.LinkU34.lu_alloc_live | eapply CF.LinkU34.lu_alloc_count | eapply CF.LinkU34.lu_alloc_peak
             | eapply CF.LinkU34.lu_alloc_peak_reset | eapply CF.LinkU34.lu_check_bounded_alloc
             | eapply CF.LinkU34.lu_check_reject_clean | eapply CF.LinkU34.lu_alloc_ran_out
             | eapply CF.LinkU34.lu_alloc_ran_out_reset | eapply CF.LinkU34.lu_alloc_most
             | eapply CF.LinkU34.lu_read_members ].
Qed.

End LinkUEntry34.
