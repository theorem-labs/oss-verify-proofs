From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YL0g YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes parse_noting_c pj_free_c check_no_overread_c check_as_written_c check_reject_clean_starved_c check_round_trip_c check_reject_clean_c check_bounded_alloc_c fuzz_alloc_live_c fuzz_alloc_count_c fuzz_alloc_peak_c fuzz_alloc_peak_reset_c fuzz_alloc_ran_out_c fuzz_alloc_ran_out_reset_c fuzz_alloc_most_c read_members_c EntrySR EntStg EntStgCno EntStgRej EntStgPjp EntStgCaw EntStgD EntStgCrt EntStgCrs1 EntStgPjf EntSQ_Cnt SlotSizesEsq LLVMFuzzerTestOneInput_c.
Local Open Scope Z_scope.

(* The ubsan entry's link on the #102 pin: entry_sr_contract (EntrySR) from the eight stages of
   LLVMFuzzerTestOneInput (EntStg; sub-row E1), each over its callee's contract. The callees of the #102 entry
   (fuzz_preset.c new:800-836): fuzz_alloc_ran_out_reset and fuzz_alloc_most (entry_sr_of_cno, over RwEnt's
   EntBig.ent_start), check_no_overread, fuzz_alloc_live / count / peak_reset (stg_cno_holds), parse_noting,
   check_bounded_alloc, fuzz_alloc_peak and fuzz_alloc_ran_out of out_of_memory() (stg_pjp_holds), check_as_written,
   check_reject_clean and read_members (stg_caw_holds, over stg_d_to_crt), check_reject_clean_starved (stg_crs0_holds,
   stg_crs1_holds), check_round_trip (stg_crt_holds), pj_free (stg_pjf_holds). *)
Section H.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Variable KW : Z.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis HKW0 : 0 <= KW /\ 112 + CRCS_K KW <= SLOT_K.
Hypothesis HKW1 : 0 <= KW <= PJ_PARSE_K.
Hypothesis CNO : forall fx' : YK11.FPState, @check_no_overread_contract fx' rc B API F.
Hypothesis PN : forall fx' : YK11.FPState, @parse_noting_contract fx' rc B API F.
Hypothesis CAW : forall fx' : YK11.FPState, @check_as_written_contract fx' rc B API F.
Hypothesis CRS : forall fx' : YK11.FPState, @check_reject_clean_starved_contract fx' rc B API F KW.
Hypothesis CRT : forall fx' : YK11.FPState, @check_round_trip_contract fx' rc B API F.
Hypothesis PJF : forall fx' : YK11.FPState, @pj_free_contract fx' rc B API F.
Hypothesis HLIVE : fuzz_alloc_live_contract.
Hypothesis HCOUNT : fuzz_alloc_count_contract.
Hypothesis HPEAK : fuzz_alloc_peak_contract.
Hypothesis HRESET : fuzz_alloc_peak_reset_contract.
Hypothesis HCBA : check_bounded_alloc_contract.
Hypothesis HCRC : check_reject_clean_contract.
Hypothesis HRM : read_members_contract.
Hypothesis HRO : fuzz_alloc_ran_out_contract.
Hypothesis HRST : fuzz_alloc_ran_out_reset_contract.
Hypothesis HMOST : fuzz_alloc_most_contract.

Theorem entry_sr_holds : forall ra empty stk, entry_sr_contract (fx := fx) B API F ra empty stk.
Proof.
  assert (S7 : stg_pjf_st (fx := fx) B API F)
    by (eapply stg_pjf_holds; eauto using esq_wl1_holds, esq_wl2_holds).
  assert (S6 : stg_crs1_st (fx := fx) B API F)
    by (eapply stg_crs1_holds; eauto using esq_wl1_holds, esq_wl2_holds).
  assert (S5 : stg_crt_st (fx := fx) B API F)
    by (eapply stg_crt_holds; eauto using esq_wl1_holds, esq_wl2_holds, esq_esz_holds).
  assert (S4 : stg_crs0_st (fx := fx) B API F) by (eapply stg_crs0_holds; eauto).
  assert (S3 : stg_caw_st (fx := fx) B API F) by (eapply stg_caw_holds; eauto).
  assert (S2 : stg_pjp_st (fx := fx) B API F) by (eapply stg_pjp_holds; eauto).
  assert (S1 : stg_cno_st (fx := fx) B API F) by (eapply stg_cno_holds; eauto).
  intros ra empty stk. eapply entry_sr_of_cno; eauto.
Qed.

End H.
