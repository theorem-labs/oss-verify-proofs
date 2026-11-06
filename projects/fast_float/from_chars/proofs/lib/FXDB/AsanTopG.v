(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open Namei.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg RealizesAbort AsanAcct FxLin FxCore FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhKCAThm.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhKCBThm.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhAll.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhKCAThm.AsanPhKCA OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhKCBThm.AsanPhKCB OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhAll.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyCertThm.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyIfOk AsanBodyCertThm AsanTopF.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyCertThm.AsanBodyTThm OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyIfOk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyCertThm OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTopF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section TopG.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hfs : sc_fs cfg = true.
(* [comment removed for export] *)
Hypothesis Hharn : AsanBodyIfOk.harn_hyps cfg.

#[using="Hoff Hfs Hharn"] Theorem hleaves : forall (path0 : path) (data0 : list byte) (fs0 : Fs.Fs) (argv0 : list byte),
  path_eqb path0 [] = false -> path_has_slash path0 = false -> path_is_dirref path0 = false -> (length path0 < path_max)%nat ->
  Forall (fun b => b <> Z_to_bv 8 0) path0 -> 6 <= Z.of_nat (length data0) <= PHI ->
  Forall (AsanPhAll.cont_okR cfg path0 data0 fs0 argv0) CONTSCA /\ Forall (AsanPhAll.cont_okR cfg path0 data0 fs0 argv0) CONTSCB.
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hharn : LiaFast.U) => LiaFast.u0).
  intros path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL.
  pose proof (AsanBodyCertThm.body_conts cfg Hoff Hfs Hharn path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL) as HB.
  pose proof (OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyCertThm.AsanBodyTThm.leaf_cont cfg Hoff Hfs path0 data0 fs0 argv0 Hp1 Hp2 Hp3 Hp4 Hp5 HFL HB) as HLf.
  assert (HN : forall k j c, nth_error LEAVES_T k = Some (j, c) -> AsanPhAll.cont_okR cfg path0 data0 fs0 argv0 c).
  { intros k j c Hk. exact (HLf (j, c) (nth_error_In LEAVES_T k Hk)). }
  split; unfold CONTSCA, CONTSCB.
  - repeat apply Forall_cons; try apply Forall_nil.
    + exact (HN 0%nat _ _ eq_refl). + exact (HN 10%nat _ _ eq_refl). + exact (HN 1%nat _ _ eq_refl). + exact (HN 11%nat _ _ eq_refl).
    + exact (HN 2%nat _ _ eq_refl). + exact (HN 12%nat _ _ eq_refl). + exact (HN 3%nat _ _ eq_refl). + exact (HN 13%nat _ _ eq_refl).
    + exact (HN 4%nat _ _ eq_refl). + exact (HN 14%nat _ _ eq_refl).
  - repeat apply Forall_cons; try apply Forall_nil.
    + exact (HN 5%nat _ _ eq_refl). + exact (HN 15%nat _ _ eq_refl). + exact (HN 6%nat _ _ eq_refl). + exact (HN 16%nat _ _ eq_refl).
    + exact (HN 7%nat _ _ eq_refl). + exact (HN 17%nat _ _ eq_refl). + exact (HN 8%nat _ _ eq_refl). + exact (HN 18%nat _ _ eq_refl).
    + exact (HN 9%nat _ _ eq_refl). + exact (HN 19%nat _ _ eq_refl).
Qed.
End TopG.
(* [comment removed for export] *)
