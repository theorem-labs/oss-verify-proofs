(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the image-B twin of lib/A/AD2o.v of this library (whose Modified-by lines trace it
   to proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v), in the form of libreac/fuzz_knock's lib/AU/YD2o.v at
   origin/ossv/recipes: module names A.Axyz -> AU.Yxyz, the program contract lib/AU/RPgLibX.v role_lib_x_all (closed,
   so image A's role_lib_x_all_closed step has no twin), the allocator parts lib/AU/YRoleAllocClose.v, RoleClose's
   Section asan_ubsan in place of Section asan, names role_* -> role_*_U / role_asan_ubsan_*. *)
(* fuzz_role's two image-B (asan-ubsan) statements from lib/A/RoleClose.v's parts, with no hypothesis: the entry
   function's program contract is lib/AU/RPgLibX.v role_lib_x_all (the image-B walks of LLVMFuzzerTestOneInput 0x80020
   and its callees, of type lib/AU/RPgLib.v role_lib_x_all_stmt), which leaves no Section hypothesis; its premises are
   the shape equation (role_shape_leaf) and the free / malloc facts H_DRIVER_U hands over. The agreement statement's
   plain side is lib/AgreeRole.v plain_slot_ag (RoleAsanTop.PLAIN_SLOT_AG). rule 24: proves no function (kind:
   assembly). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_role Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require AgreeRole.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0o YG00 YG01 YG0f YG0d YC5d YCbp YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YG0q YK15 YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require YB1v YB01 YB12 YB1n YCej YCejTfib YD2l YD2m YD1k YD1o YD1l YD1j YD1p YCfn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgLib RPgLibX YRoleAllocClose.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RoleAsanTop RoleClose.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance RoleAsanTop.role_shape.

Local Notation segs := YB1v.tfibsegs.
Local Notation B := YD2l.TfibB.
Local Notation HB := YD2l.TfibB_syms.
Local Notation LAWS := (YG0q.AR_laws_ok YB1v.tfibsegs YD2l.TfibB).
Local Notation XL0 := AU.RPgLib.XL0.
Local Notation RO_LO := AU.RPgLib.RO_LO.
Local Notation RO_HI := AU.RPgLib.RO_HI.

(* The shape equation: at RoleAsanTop.role_shape (ag_shape checksum_shape) the entry function's continuation is
   applied to the leaf with return 0, the file system unchanged and no output; it is the LEAF premise of
   AU.RPgLib.role_lib_x_all_stmt, and holds by reflexivity (image A's AD2o passes it as fun _ _ _ => eq_refl). *)
Lemma role_shape_leaf : forall pl fs (K : YO09.lleaf -> YK15.TSet),
  @YO09.LIBK RoleAsanTop.role_shape pl fs K = K (YO09.LL 0 fs []).
Proof. intros pl fs K. reflexivity. Qed.

(* RoleClose's H_DRIVER_U at B_U := YD2l.TfibB, from image B's driver main YD1p.tfib_drv_main at the float-state
   invariant P := a zero rounding mode (P0: YK0o.fp_frm_zero_fx0), the twin of AD2o.role_driver_TfibB. The adapter
   bridges the same two differences. (1) H_DRIVER_U hands over the three allocator parts for every FPState; the driver
   takes malloc and memcpy at YK11.fx0 and free at every float state with P. (2) The driver takes its other parts,
   which H_DRIVER_U leaves inside itself; they are supplied here: TfibSyms (YD2l.TfibB_syms), the read check
   (YD2m.tfib_ARDCHK), the program contract LIBC (AU.RPgLibX.role_lib_x_all at role_shape_leaf and the free / malloc
   facts H_DRIVER_U receives, through AU.RPgLib.role_lib_contract_x_all_tfib to YCfn's exists-fx' slot and
   YCfn.tfib_lib_contract_xP_of_xf, at ameter_triv / XL0 / RO_LO..RO_HI = 0x9a3c0..0x9b7c8), MT_FREE (ameter_triv's
   mo_ok is True), RO_IN (RO_LO..RO_HI is lib/AU/YCeg.v in_ro_tfa's second disjunct) and the stdio sites (YD1k, YD1o,
   YD1l, YD1j; the printf and exit sites at every float state). H_DRIVER_U's two trace premises are not used:
   YD2l.TfibB_syms carries them. *)
Lemma role_driver_TfibB_U : forall rc : YM05.RunCeil,
  (forall fx : YK11.FPState, @amalloc_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B))) ->
  universe_ok (as_universe B) ->
  (forall t, In t YCejTfib.Tfib_drv_traces -> In t (as_universe B)) ->
  RoleClose.drv_mainU YB01.HS_tfib YB12.TFIB rc.
Proof.
  intros rc AM AF AI _ _.
  exact (@YD1p.tfib_drv_main rc RoleAsanTop.role_shape (fun fx : YK11.FPState => frm_zero (@fp_csr fx)) fp_frm_zero_fx0
    B HB (AM YK11.fx0) (fun fx _ => AF fx) (AI YK11.fx0) (YD2m.tfib_ARDCHK B HB)
    ameter_triv XL0 XL0 RO_LO RO_HI (fun _ _ => I) (fun a H => or_intror H)
    (fun fx Hz => YCfn.tfib_lib_contract_xP_of_xf (fx := fx) B ameter_triv XL0 XL0 RO_LO RO_HI Hz
      (AU.RPgLib.role_lib_contract_x_all_tfib B ameter_triv XL0 XL0 RO_LO RO_HI
        (AU.RPgLibX.role_lib_x_all rc RoleAsanTop.role_shape role_shape_leaf AF AM) fx))
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

(* RoleClose's asan_ubsan Section at its parts, every argument in order: HS_TBL_U / TFIB_TBL_U / H_STARTUP_U from
   image B's start-up certificate (YB01.HS_tfib, YB12.TFIB, YB1n.tfib_startup_T1), B_U := YD2l.TfibB, the allocator
   parts from lib/AU/YRoleAllocClose.v, the trace tables from YCej / YCejTfib with H_TRACES_B_U by reflexivity, and
   H_DRIVER_U from role_driver_TfibB_U. *)
Theorem ASAN_UBSAN_T_closed : RoleAsanTop.ASAN_UBSAN_T.
Proof.
  exact (RoleClose.ASAN_UBSAN_T_of_parts YB01.HS_tfib YB12.TFIB YB1n.tfib_startup_T1 B
    YRoleAllocClose.role_amalloc_closed_U YRoleAllocClose.role_afree_closed_U YRoleAllocClose.role_aicpy_closed_U
    YCej.Tfib_universe YCej.Tfib_universe_ok eq_refl YCejTfib.Tfib_drv_traces YCejTfib.Tfib_universe_drv
    role_driver_TfibB_U).
Qed.
Theorem role_asan_ubsan_halts_closed : Statements.asan_ubsan_halts.
Proof. exact (RoleAsanTop.asan_ubsan_halts_of_asan_side ASAN_UBSAN_T_closed). Qed.

(* The agreement statement: the plain build's entry-function slot at the agreement shape is lib/AgreeRole.v
   plain_slot_ag, of type RoleAsanTop.PLAIN_SLOT_AG. *)
Theorem role_asan_ubsan_agrees_closed : Statements.asan_ubsan_agrees.
Proof. exact (RoleAsanTop.asan_ubsan_agrees_of_asan_side AgreeRole.plain_slot_ag ASAN_UBSAN_T_closed). Qed.
