(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxStep FxSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxQRNode FxMchr FxMNode FxRunPost FxSNodes AsanSNodes AsanQSites.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanQcsNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanQcsNode AsanQSSites.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQRNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxRunPost OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsNode.AsanRpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQSSites.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive pnode : Type :=
| PQC (j : nat)      (* [comment removed for export] *)
| PMC (j : nat)      (* [comment removed for export] *)
| PRP                (* [comment removed for export] *)
| PQR (j : nat)      (* [comment removed for export] *)
| PQS (j : nat).     (* [comment removed for export] *)

Section P.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable img : tree Z.
Variable qsites : list qsite.
Variable mcsites : list Z.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.
Hypothesis Himg : img_ok ASEGSN img.
Hypothesis Hqs : Forall (qsite_ok ASEGSN) qsites.
Hypothesis Hms : Forall (msite_ok ASEGSN) mcsites.

Definition ppostA (p : pnode) (S : sst) (M : smodel) : option sst :=
  match p with
  | PQC j => match nth_error qsites j with
             | Some q => if qc_chk img q S M then Some (qc_post q S) else None
             | None => None
             end
  | PMC j => match nth_error mcsites j with
             | Some pcw => if mc_chk img pcw S then Some (mc_post S) else None
             | None => None
             end
  | PRP => if rp_chk img S M then Some (rp_post S) else None
  | PQR j => match nth_error qsites j with
             | Some q => if qcr_chk img q S M then Some (qc_post q S) else None
             | None => None
             end
  | PQS j => match nth_error QSSITES_P j with
             | Some s => if qcs_chk img s S M then Some (qcs_post s S) else None
             | None => None
             end
  end.

#[using="Hwx Himg Hqs Hms"] Theorem pnodeA_ok : forall p, pnode_ok ASEGSN cfg LIMIT ppostA p.
Proof. LiaFast.lf_pins (fun (Hwx Himg Hqs Hms : LiaFast.U) => LiaFast.u0).
  intros p S M S' Hp model0 mem0 E ms model T Hd Hk.
  destruct p as [j|j| |j|j]; cbn [ppostA] in Hp.
  - destruct (nth_error qsites j) as [q|] eqn:Hq; [|discriminate].
    destruct (qc_chk img q S M) eqn:Hc; [|discriminate]. injection Hp as <-.
    rewrite Forall_forall in Hqs.
    exact (den_qc ASEGSN cfg LIMIT model0 mem0 img Hwx Himg q S M E ms model T (Hqs q (nth_error_In _ _ Hq)) Hc Hd Hk).
  - destruct (nth_error mcsites j) as [pcw|] eqn:Hq; [|discriminate].
    destruct (mc_chk img pcw S) eqn:Hc; [|discriminate]. injection Hp as <-.
    rewrite Forall_forall in Hms.
    exact (den_mc ASEGSN cfg LIMIT model0 mem0 img Hwx Himg pcw S M E ms model T (Hms pcw (nth_error_In _ _ Hq)) Hc Hd Hk).
  - destruct (rp_chk img S M) eqn:Hc; [|discriminate]. injection Hp as <-.
    exact (den_rp cfg LIMIT model0 mem0 img Hwx Himg S M E ms model T Hc Hd Hk).
  - destruct (nth_error qsites j) as [q|] eqn:Hq; [|discriminate].
    destruct (qcr_chk img q S M) eqn:Hc; [|discriminate]. injection Hp as <-.
    rewrite Forall_forall in Hqs.
    exact (den_qcr ASEGSN cfg LIMIT model0 mem0 img Hwx Himg q S M E ms model T (Hqs q (nth_error_In _ _ Hq)) Hc Hd Hk).
  - destruct (nth_error QSSITES_P j) as [s|] eqn:Hq; [|discriminate].
    destruct (qcs_chk img s S M) eqn:Hc; [|discriminate]. injection Hp as <-.
    pose proof QSSITES_P_ok as Hss. rewrite Forall_forall in Hss.
    exact (den_qcs cfg LIMIT model0 mem0 img Hwx Himg s S M E ms model T (Hss s (nth_error_In _ _ Hq)) Hc Hd Hk).
Qed.
End P.

(* [comment removed for export] *)
Definition QSITES_P : list qsite := [QS_PRINTF; QS_MEMCHR; QS_STRNLEN; QS_MEMCPY_S; QS_MEMCPY_D].
Definition MCSITES_P : list Z := [MC_PCW].
Lemma QSITES_P_ok : Forall (qsite_ok ASEGSN) QSITES_P.
Proof.
  unfold QSITES_P. apply Forall_cons; [exact QS_PRINTF_ok|]. apply Forall_cons; [exact QS_MEMCHR_ok|]. apply Forall_cons; [exact QS_STRNLEN_ok|].
  apply Forall_cons; [exact QS_MEMCPY_S_ok|]. apply Forall_cons; [exact QS_MEMCPY_D_ok|]. apply Forall_nil.
Qed.
Lemma MCSITES_P_ok : Forall (msite_ok ASEGSN) MCSITES_P.
Proof. unfold MCSITES_P. apply Forall_cons; [exact MC_SITE_ok | apply Forall_nil]. Qed.
