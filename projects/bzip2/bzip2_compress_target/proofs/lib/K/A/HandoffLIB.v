(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require HandoffKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require HandoffImage HandoffCLX RT_state RT_rep RT_init.
Module TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import HandoffKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffImage.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffCLX.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_init.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hl_fx : PropExec.FPState := PropExec.fx0.

(* [comment removed for export] *)
Definition hs_lib_ok (ch : acs) : bool :=
  (hs_rw_cells ch CRC_A [CB 1024 CRC_BYTES] && hs_rw_cells ch INCS_A [CB 56 INCS_BYTES] && hs_rw_cells ch RNUMS_A [CB 2048 RNUMS_BYTES])%bool.

Section Lib.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.

(* [comment removed for export] *)
Theorem hs_lib_gen : forall A' : list (Z * Z),
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_lib_ok ch = true -> LIB_A (mH FULL model A').
Proof.
  intros A' HA' HT. unfold hs_lib_ok in HT. apply andb_prop in HT as [HT H2]. apply andb_prop in HT as [H0 H1]. split; [|split].
  - exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H0).
  - exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H1).
  - exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H2).
Qed.

(* [comment removed for export] *)
Theorem hs_lib : hs_lib_ok ch = true -> LIB_A (mH FULL model (rtA_allow (sigma0 A E ch model))).
Proof. intros HT. exact (hs_lib_gen (rtA_allow (sigma0 A E ch model)) (ri_allow A E ch model) HT). Qed.

End Lib.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import HandoffKit HandoffImage HandoffCLX RT_state RT_rep RT_init.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hl_fx : PropExec.FPState := PropExec.fx0.

(* [comment removed for export] *)
Definition hs_lib_ok (ch : acs) : bool :=
  (hs_rw_cells ch CRC_A [CB 1024 CRC_BYTES] && hs_rw_cells ch RNUMS_A [CB 2048 RNUMS_BYTES])%bool.

Section Lib.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.

(* [comment removed for export] *)
Theorem hs_lib_gen : forall A' : list (Z * Z),
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_lib_ok ch = true -> LIB_A (mH FULL model A').
Proof.
  intros A' HA' HT. unfold hs_lib_ok in HT.  apply andb_prop in HT as [H0 H1]. split.
  - exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H0).
  - exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H1).
Qed.

(* [comment removed for export] *)
Theorem hs_lib : hs_lib_ok ch = true -> LIB_A (mH FULL model (rtA_allow (sigma0 A E ch model))).
Proof. intros HT. exact (hs_lib_gen (rtA_allow (sigma0 A E ch model)) (ri_allow A E ch model) HT). Qed.

End Lib.
