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
(* fuzz_rate's two image-A ASan statements from lib/A/RateClose.v's parts, with no hypothesis left. The agreement
   statement takes the plain build's entry-function slot at the agreement shape from lib/AgreeRate.v plain_slot_ag (of
   exactly the type RateAsanTop.PLAIN_SLOT_AG). The entry function's program contract RtPgLib.rate_lib_x_all_stmt is
   lib/A/RtPgLink.v's rate_lib_x_all (the image-A walks of LLVMFuzzerTestOneInput and its callees) at its one Section
   hypothesis, check_csv's contract (0x838e0, class-2 frame, closed_list 0x21520) at every float state, which
   lib/A/RtPgCcsvClose.v rate_ccsv_tfib proves at TfibB. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_rate Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require AgreeRate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0o YG00 YG01 YG0f YG0d YC5d YCbp YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require AB1v AB01 AB12 AB1n ACej ACejTfib AD2l AD2m AD1k AD1o AD1l AD1j AD1p ACfn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgLib RtPgLink RtPgCcsvClose.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RateAllocClose RateAsanTop RateClose.
Local Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance RateAsanTop.rate_shape.

Local Notation segs := AB1v.tfibsegs.
Local Notation B := AD2l.TfibB.
Local Notation HB := AD2l.TfibB_syms.
Local Notation LAWS := (YG0q.AR_laws_ok AB1v.tfibsegs AD2l.TfibB).
Local Notation XL0 := RtPgLib.XL0.
Local Notation RO_LO := RtPgLib.RO_LO.
Local Notation RO_HI := RtPgLib.RO_HI.

(* The entry function's program contract (lib/A/RtPgLib.v), from the walks (lib/A/RtPgLink.v) and check_csv's
   contract (lib/A/RtPgCcsvClose.v). *)
Lemma rate_lib_x_all : RtPgLib.rate_lib_x_all_stmt.
Proof. exact (RtPgLink.rate_lib_x_all RtPgCcsvClose.rate_ccsv_tfib). Qed.

(* RateClose's H_DRIVER at B := AD2l.TfibB, from the core's driver main AD1p.tfib_drv_main at the float-state invariant
   P := a zero rounding mode (P0: YK0o.fp_frm_zero_fx0). The adapter bridges two differences. (1) H_DRIVER hands over
   the three allocator parts for every FPState; the driver takes malloc and memcpy at YK11.fx0 and free at every
   float state with P (it frees after LLVMFuzzerTestOneInput returns, at that call's float state). (2) The driver takes
   its other parts, which H_DRIVER leaves inside itself; they are supplied here: TfibSyms (AD2l.TfibB_syms), the read
   check (AD2m.tfib_ARDCHK), the program contract LIBC (RtPgLib.rate_lib_x_all at ameter_triv / XL0 / RO_LO..RO_HI and
   the free / malloc facts H_DRIVER receives, through RtPgLib.rate_lib_contract_x_all_tfib to ACfn's exists-fx' slot and
   ACfn.tfib_lib_contract_xP_of_xf; its LEAF holds by eq_refl at rate_shape), MT_FREE (ameter_triv's mo_ok is True),
   RO_IN (RO_LO..RO_HI is in_ro_tfa's second disjunct) and the stdio sites (AD1k, AD1o, AD1l, AD1j; the printf and exit
   sites at every float state). H_DRIVER's two trace premises are not used: AD2l.TfibB_syms carries them. *)
Lemma rate_driver_TfibB : forall rc : YM05.RunCeil,
  (forall fx : YK11.FPState, @amalloc_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B))) ->
  universe_ok (as_universe B) ->
  (forall t, In t ACejTfib.Tfib_drv_traces -> In t (as_universe B)) ->
  RateClose.drv_mainA AB01.HS_tfib AB12.TFIB rc.
Proof.
  intros rc AM AF AI _ _.
  exact (@AD1p.tfib_drv_main rc RateAsanTop.rate_shape (fun fx : YK11.FPState => frm_zero (@fp_csr fx)) fp_frm_zero_fx0
    B HB (AM YK11.fx0) (fun fx _ => AF fx) (AI YK11.fx0) (AD2m.tfib_ARDCHK B HB)
    ameter_triv XL0 XL0 RO_LO RO_HI (fun _ _ => I) (fun a H => or_intror H)
    (fun fx Hz => ACfn.tfib_lib_contract_xP_of_xf (fx := fx) B ameter_triv XL0 XL0 RO_LO RO_HI Hz
      (RtPgLib.rate_lib_contract_x_all_tfib B ameter_triv XL0 XL0 RO_LO RO_HI
        (rate_lib_x_all rc RateAsanTop.rate_shape (fun _ _ _ => eq_refl) AF AM) fx))
    AD1k.xst AD1k.tfib_xst_frame
    (fun fx _ => AD1o.tfib_printf_first (fx := fx) B HB LAWS HB)
    (fun fx _ => AD1o.tfib_printf_next (fx := fx) B HB LAWS HB)
    AD1k.est AD1k.tfib_est_img AD1k.tfib_est_frame
    (AD1k.tfib_fwrite_site B HB LAWS)
    (AD1k.tfib_refused_site B HB LAWS HB)
    (AD1l.tfib_fprintf_open_site B HB LAWS HB)
    (AD1l.tfib_fprintf_rderr_site B HB LAWS HB)
    (AD1l.tfib_fprintf_usage_site B HB LAWS HB)
    (fun fx _ => AD1j.tfib_exit_site (fx := fx) B HB LAWS)).
Qed.

(* RateClose's asan Section at its parts: HS_TBL / TFIB_TBL / H_STARTUP from the start-up certificate (AB01.HS_tfib,
   AB12.TFIB, AB1n.tfib_startup_T1), B := AD2l.TfibB, the allocator parts from lib/A/RateAllocClose.v, the trace tables
   from ACej / ACejTfib with H_TRACES_B by reflexivity, and H_DRIVER from rate_driver_TfibB. *)
Theorem ASAN_T_closed : RateAsanTop.ASAN_T.
Proof.
  exact (RateClose.ASAN_T_of_parts AB01.HS_tfib AB12.TFIB AB1n.tfib_startup_T1 B
    RateAllocClose.rate_amalloc_closed RateAllocClose.rate_afree_closed RateAllocClose.rate_aicpy_closed
    ACej.Tfib_universe ACej.Tfib_universe_ok eq_refl ACejTfib.Tfib_drv_traces ACejTfib.Tfib_universe_drv
    rate_driver_TfibB).
Qed.
Theorem rate_asan_halts_closed : Statements.asan_halts.
Proof. exact (RateAsanTop.asan_halts_of_asan_side ASAN_T_closed). Qed.

(* The plain build's entry-function slot at the agreement shape: lib/AgreeRate.v plain_slot_ag, of exactly the type
   RateAsanTop.PLAIN_SLOT_AG (the Check in lib/A/AuditRateClose.v). *)
Theorem rate_asan_agrees_closed : Statements.asan_agrees.
Proof. exact (RateAsanTop.asan_agrees_of_asan_side AgreeRate.plain_slot_ag ASAN_T_closed). Qed.
