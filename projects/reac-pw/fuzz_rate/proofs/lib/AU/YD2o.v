(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v and AD2p.v at
   c8557374ad2e. This file is knock's closing assembly of lib/A/KnockClose.v's parts (rule 24: no function proved; kind:
   assembly): it instantiates KnockClose's asan Section at closed parts, so fuzz_knock's two ASan statements rest on no
   Section hypothesis. cgif's AD2o keeps three program-walk hypotheses that its AD2p discharges; knock's program contract
   (lib/A/APgLib.v knock_lib_x_all) takes none, so the closing is one file and there is no AD2p. *)
(* Modified by Theorem Labs, 2026-10: taken for reac-pw/fuzz_qdisc image A from proofs/libreac/fuzz_knock/lib/A/AD2o.v at
   origin/ossv/recipes 6ebe35ba632: it instantiates lib/A/QdiscClose.v's asan Section; the program contract is
   lib/A/QPgLib.v's (qdisc_lib_contract_x_all_tfib over qdisc_lib_x_all, in the roles of APgLib's knock_* ); the
   allocator parts are lib/A/QdiscAllocClose.v's; names knock_* -> qdisc_*, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_qdisc/lib/A/AD2o.v at 56ce9edaafc, for reac-pw/fuzz_role image A: it
   instantiates lib/A/RoleClose.v's asan Section (its trace tables from ACej / ACejTfib); the driver is the relocated
   core's float-state-slot driver (libreac/fuzz_grant's lib/A/AD1p.v tfib_drv_main at P := a zero rounding mode, as
   fuzz_grant's lib/A/AD1q.v:107-142 tfib_srealizesXF and libreac/fuzz_boxreg's lib/A/Prog/BoxCore.v apply it), since
   fuzz_role's entry function changes the float registers; the program contract is lib/A/RPgLib.v's
   (role_lib_contract_x_all_tfib over role_lib_x_all, whose free / malloc premises the adapter feeds, as
   libreac/fuzz_ctrl's lib/A/ACtlAll.v:110-111 feeds its walk top's); the allocator parts are lib/A/RoleAllocClose.v's;
   names qdisc_* -> role_*, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/AD2o.v at fa745625e7df, for reac-pw/fuzz_rate image A: it
   instantiates lib/A/RateClose.v's asan Section; the program contract is lib/A/RtPgLib.v's (rate_lib_contract_x_all_tfib
   over rate_lib_x_all; fuzz_rate's entry function also changes the float registers and allocates three blocks); the
   allocator parts are lib/A/RateAllocClose.v's; names role_* -> rate_*, module paths changed; in the second
   Modified-by line above, a space now stands between `knock_*` and `)`, so that the comment does not end there. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_rate Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require AgreeRate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0o YG00 YG01 YG0f YG0d YC5d YCbp YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require YB1v YB01 YB12 YB1n YCej YCejTfib YD2l YD2m YD1k YD1o YD1l YD1j YD1p YCfn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgLibB RtPgLinkB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require YRateAllocClose.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RateAsanTop RateClose.
Local Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance RateAsanTop.rate_shape.

Local Notation segs := YB1v.tfibsegs.
Local Notation B := YD2l.TfibB.
Local Notation HB := YD2l.TfibB_syms.
Local Notation LAWS := (YG0q.AR_laws_ok YB1v.tfibsegs YD2l.TfibB).
Local Notation XL0 := RtPgLibB.XL0_B.
Local Notation RO_LO := RtPgLibB.RO_LO_B.
Local Notation RO_HI := RtPgLibB.RO_HI_B.

Lemma rate_driver_TfibB_U : forall rc : YM05.RunCeil,
  (forall fx : YK11.FPState, @amalloc_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B))) ->
  universe_ok (as_universe B) ->
  (forall t, In t YCejTfib.Tfib_drv_traces -> In t (as_universe B)) ->
  RateClose.drv_mainU YB01.HS_tfib YB12.TFIB rc.
Proof.
  intros rc AM AF AI _ _.
  exact (@YD1p.tfib_drv_main rc RateAsanTop.rate_shape (fun fx : YK11.FPState => frm_zero (@fp_csr fx)) fp_frm_zero_fx0
    B HB (AM YK11.fx0) (fun fx _ => AF fx) (AI YK11.fx0) (YD2m.tfib_ARDCHK B HB)
    ameter_triv XL0 XL0 RO_LO RO_HI (fun _ _ => I) (fun a H => or_intror H)
    (fun fx Hz => YCfn.tfib_lib_contract_xP_of_xf (fx := fx) B ameter_triv XL0 XL0 RO_LO RO_HI Hz
      (RtPgLibB.rate_lib_contract_x_all_tfib_B B ameter_triv XL0 XL0 RO_LO RO_HI
        (RtPgLinkB.rate_lib_x_all_B rc RateAsanTop.rate_shape (fun _ _ _ => eq_refl) AF AM) fx))
    YD1k.xst YD1k.tfib_xst_frame
    (fun fx _ => YD1o.tfib_printf_first (fx := fx) B HB LAWS HB)
    (fun fx _ => YD1o.tfib_printf_next (fx := fx) B HB LAWS HB)
    YD1k.est YD1k.tfib_est_img YD1k.tfib_est_frame
    (YD1k.tfib_fwrite_site B HB LAWS)
    (YD1k.tfib_refused_site B HB LAWS HB)
    (YD1l.tfib_fprintf_open_site B HB LAWS HB)
    (YD1l.tfib_fprintf_rderr_site B HB LAWS HB)
    (YD1l.tfib_fprintf_usage_site B HB LAWS HB)
    (fun fx _ => YD1j.tfib_exit_site (fx := fx) B HB LAWS)).
Qed.

Theorem ASAN_UBSAN_T_closed : RateAsanTop.ASAN_UBSAN_T.
Proof.
  exact (RateClose.ASAN_UBSAN_T_of_parts YB01.HS_tfib YB12.TFIB YB1n.tfib_startup_T1 B
    YRateAllocClose.rate_amalloc_closed_U YRateAllocClose.rate_afree_closed_U YRateAllocClose.rate_aicpy_closed_U
    YCej.Tfib_universe YCej.Tfib_universe_ok eq_refl YCejTfib.Tfib_drv_traces YCejTfib.Tfib_universe_drv
    rate_driver_TfibB_U).
Qed.
Theorem rate_asan_ubsan_halts_closed : Statements.asan_ubsan_halts.
Proof. exact (RateAsanTop.asan_ubsan_halts_of_asan_side ASAN_UBSAN_T_closed). Qed.

Theorem rate_asan_ubsan_agrees_closed : Statements.asan_ubsan_agrees.
Proof. exact (RateAsanTop.asan_ubsan_agrees_of_asan_side AgreeRate.plain_slot_ag ASAN_UBSAN_T_closed). Qed.
