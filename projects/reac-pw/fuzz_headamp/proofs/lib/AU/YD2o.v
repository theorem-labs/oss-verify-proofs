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
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/AD2o.v at fa745625e7d, for reac-pw/fuzz_headamp image A:
   it instantiates lib/A/HeadampClose.v's asan Section; the program contract is lib/A/HPgLib.v's
   (headamp_lib_contract_x_all_tfib over headamp_lib_x_all_stmt, the same premises in the same order as role's: the
   one-leaf law, then free, then malloc; the entry function's four blocks add none); the plain slot is
   lib/A/HeadampPlainSlot.v's (lib/AgreeHead.v plain_slot_ag_of_evts at the plain walks); names role_* -> headamp_*,
   RPgLib -> HPgLib, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/AD2o.v at 7d1244d171b, the asan-ubsan twin for image B
   (fuzz_headamp.asan-ubsan), in the form of proofs/libreac/fuzz_knock/lib/AU/YD2o.v (origin/ossv/recipes 4b6f0df50aa7):
   it instantiates lib/A/HeadampClose.v's asan_ubsan Section; image A's core modules move to their lib/AU twins
   (AB1v, AB01, AB12, AB1n, ACej, ACejTfib, AD2l, AD2m, AD1k, AD1o, AD1l, AD1j, AD1p, ACfn -> YB1v, YB01, YB12, YB1n,
   YCej, YCejTfib, YD2l, YD2m, YD1k, YD1o, YD1l, YD1j, YD1p, YCfn, the same identifiers), the program contract is
   lib/AU/HPgLibU.v's (the names of lib/A/HPgLib.v), the allocator parts lib/AU/YHeadampAllocClose.v's; ASAN_T ->
   ASAN_UBSAN_T, drv_mainA -> drv_mainU, headamp_*_asan_* -> headamp_*_asan_ubsan_*, the driver adapter gets the
   suffix _U, module paths changed. *)
(* fuzz_headamp's two image-B ASan statements (asan_ubsan_halts, asan_ubsan_agrees) from lib/A/HeadampClose.v's
   asan_ubsan parts; the agreement statement's plain side is lib/A/HeadampPlainSlot.v headamp_plain_slot_ag_closed
   (HeadampAsanTop.PLAIN_SLOT_AG), the same plain slot as image A's.
   The entry function's program contract is lib/AU/HPgTopI.v headamp_lib_x_all (the image-B walks of
   LLVMFuzzerTestOneInput and its callees, of type lib/AU/HPgLibU.v headamp_lib_x_all_stmt), with no hypothesis, so the
   two statements here rest on no premise. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_headamp Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0o YG00 YG01 YG0f YG0d YC5d YCbp YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require YB1v YB01 YB12 YB1n YCej YCejTfib YD2l YD2m YD1k YD1o YD1l YD1j YD1p YCfn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgLibU HPgTopI YHeadampAllocClose.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HeadampAsanTop HeadampClose HeadampPlainSlot.
Local Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance HeadampAsanTop.headamp_shape.

Local Notation segs := YB1v.tfibsegs.
Local Notation B := YD2l.TfibB.
Local Notation HB := YD2l.TfibB_syms.
Local Notation LAWS := (YG0q.AR_laws_ok YB1v.tfibsegs YD2l.TfibB).
Local Notation XL0 := HPgLibU.XL0.
Local Notation RO_LO := HPgLibU.RO_LO.
Local Notation RO_HI := HPgLibU.RO_HI.

(* The entry function's program contract at image B (lib/AU/HPgTopI.v), named with its full path: lib/A/HPgTopI.v is
   image A's file of the same short name. *)
Local Notation headamp_lib_x_all := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.HPgTopI.headamp_lib_x_all.

(* HeadampClose's H_DRIVER_U at B_U := YD2l.TfibB, from image B's core driver main YD1p.tfib_drv_main at the float-state
   invariant P := a zero rounding mode (P0: YK0o.fp_frm_zero_fx0). The adapter bridges two differences. (1) H_DRIVER_U
   hands over the three allocator parts for every FPState; the driver takes malloc and memcpy at YK11.fx0 and free at
   every float state with P (it frees after LLVMFuzzerTestOneInput returns, at that call's float state). (2) The driver
   takes its other parts, which H_DRIVER_U leaves inside itself; they are supplied here: TfibSyms (YD2l.TfibB_syms),
   the read check (YD2m.tfib_ARDCHK), the program contract LIBC (headamp_lib_x_all at ameter_triv / XL0 /
   RO_LO..RO_HI and the free / malloc facts H_DRIVER_U receives, through HPgLibU.headamp_lib_contract_x_all_tfib to
   YCfn's exists-fx' slot and YCfn.tfib_lib_contract_xP_of_xf; its LEAF holds by eq_refl at headamp_shape), MT_FREE
   (ameter_triv's mo_ok is True), RO_IN (RO_LO..RO_HI is in_ro_tfa's second disjunct) and the stdio sites (YD1k,
   YD1o, YD1l, YD1j; the printf and exit sites at every float state). H_DRIVER_U's two trace premises are not used:
   YD2l.TfibB_syms carries them. *)
Lemma headamp_driver_TfibB_U : forall rc : YM05.RunCeil,
  (forall fx : YK11.FPState, @amalloc_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B))) ->
  universe_ok (as_universe B) ->
  (forall t, In t YCejTfib.Tfib_drv_traces -> In t (as_universe B)) ->
  HeadampClose.drv_mainU YB01.HS_tfib YB12.TFIB rc.
Proof.
  intros rc AM AF AI _ _.
  exact (@YD1p.tfib_drv_main rc HeadampAsanTop.headamp_shape (fun fx : YK11.FPState => frm_zero (@fp_csr fx)) fp_frm_zero_fx0
    B HB (AM YK11.fx0) (fun fx _ => AF fx) (AI YK11.fx0) (YD2m.tfib_ARDCHK B HB)
    ameter_triv XL0 XL0 RO_LO RO_HI (fun _ _ => I) (fun a H => or_intror H)
    (fun fx Hz => YCfn.tfib_lib_contract_xP_of_xf (fx := fx) B ameter_triv XL0 XL0 RO_LO RO_HI Hz
      (HPgLibU.headamp_lib_contract_x_all_tfib B ameter_triv XL0 XL0 RO_LO RO_HI
        (headamp_lib_x_all rc HeadampAsanTop.headamp_shape (fun _ _ _ => eq_refl) AF AM) fx))
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

(* HeadampClose's asan_ubsan Section at its parts, in the order of knock's lib/AU/YD2o.v:55-57 with its eq_refl replaced
   by the five trace arguments: HS_TBL_U / TFIB_TBL_U / H_STARTUP_U from image B's start-up certificate (YB01.HS_tfib,
   YB12.TFIB, YB1n.tfib_startup_T1), B_U := YD2l.TfibB, the allocator parts from lib/AU/YHeadampAllocClose.v, the
   trace tables from YCej / YCejTfib with H_TRACES_B_U by reflexivity, and H_DRIVER_U from headamp_driver_TfibB_U. *)
Theorem ASAN_UBSAN_T_closed : HeadampAsanTop.ASAN_UBSAN_T.
Proof.
  exact (HeadampClose.ASAN_UBSAN_T_of_parts YB01.HS_tfib YB12.TFIB YB1n.tfib_startup_T1 B
    YHeadampAllocClose.headamp_amalloc_closed_U YHeadampAllocClose.headamp_afree_closed_U YHeadampAllocClose.headamp_aicpy_closed_U
    YCej.Tfib_universe YCej.Tfib_universe_ok eq_refl YCejTfib.Tfib_drv_traces YCejTfib.Tfib_universe_drv
    headamp_driver_TfibB_U).
Qed.
Theorem headamp_asan_ubsan_halts_closed : Statements.asan_ubsan_halts.
Proof. exact (HeadampAsanTop.asan_ubsan_halts_of_asan_side ASAN_UBSAN_T_closed). Qed.

(* The agreement statement: the plain build's entry-function slot at the agreement shape is lib/A/HeadampPlainSlot.v
   headamp_plain_slot_ag_closed, of type HeadampAsanTop.PLAIN_SLOT_AG. *)
Theorem headamp_asan_ubsan_agrees_closed : Statements.asan_ubsan_agrees.
Proof.
  exact (HeadampAsanTop.asan_ubsan_agrees_of_asan_side HeadampPlainSlot.headamp_plain_slot_ag_closed ASAN_UBSAN_T_closed).
Qed.
