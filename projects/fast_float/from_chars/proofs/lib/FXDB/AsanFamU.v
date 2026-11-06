(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxSubst FxEnt FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxWvC FxChMain FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcFam AcDepDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMchr FxMNode FxSNodes AsanSNodes AsanPNodes FxSFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanSFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanSFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxChFamI.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanSFam3.AsanCpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanSFam3 OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib.FxKeep OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxChFamI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma HA_keep : forall segs LIMIT model0 E S M M' ms model a m0 m0', DEN segs LIMIT model0 m0' E S M' ms model ->
  keep_ok model M M' m0 m0' -> HA E M a m0 -> HA E M' a m0'.
Proof.
  intros segs LIMIT model0 E S M M' ms model a m0 m0' Hd (Hm & Ho & Hsn & Hzr) H.
  destruct (a_on a) eqn:Hon; [|intros Hc; congruence].
  pose proof (H Hon) as Hon'. destruct Hon' as [_ _ _ _ (k1 & Hg1) (k2 & Hg2)].
  pose proof (dn_gtop _ _ _ _ _ _ _ _ _ Hd) as Hgt. rewrite Forall_forall in Hgt.
  pose proof (alloc_top_lo _ (proj1 (dn_spok _ _ _ _ _ _ _ _ _ Hd))) as Tlo.
  apply (HA_ext E M M' a m0 m0' Hm Ho Hzr); [| |exact H].
  - intros x Hx Hdw. apply Hsn. split; [lia|].
    pose proof (Hgt _ (Hm _ Hg1)) as T1. pose proof (Hgt _ (Hm _ Hg2)) as T2. cbn [fst snd] in T1, T2.
    unfold gsz in T1, T2. cbn [fst snd] in T1, T2. rewrite uE_lc in T1, T2 by lia.
    unfold downed, dD1, dB1 in *. lia.
  - (* [comment removed for export] *)
    intros Hne x Hx. apply Hsn.
    destruct (pri_cases E M a m0 (H Hon) Hne x Hx) as [(g & Hg & _ & Hin & _ & _) | [(_ & Hsh & _) | Hgq]].
    + pose proof (Hgt _ (Hm _ Hg)) as T1. pose proof (bv_unsigned_in_range _ (lden E (fst (fst g)))) as Rg. unfold uE in *. lia.
    + unfold in_shadow, SH_LO, SH_HI in Hsh. apply andb_prop in Hsh as [S1 S2]. apply Z.leb_le in S1. apply Z.ltb_lt in S2. lia.
    + (* [comment removed for export] *) lia.
Qed.

Section U.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.
Hypothesis Hsegb : segs_below_b ASEGSN 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGSN).
Hypothesis Hreswf : ivs_wf (segments_reserved ASEGSN).
Variable sarg : nat -> list byte.
Variable islx : Z.
Variable nsites : list nsite.
Hypothesis His : isl_ok ASEGSN islx.
Hypothesis Hns : Forall (nsite_ok ASEGSN) nsites.
Variable img : tree Z.
Variable qsites : list qsite.
Variable mcsites : list Z.
Hypothesis Himg : img_ok ASEGSN img.
Hypothesis Hqs : Forall (qsite_ok ASEGSN) qsites.
Hypothesis Hms : Forall (msite_ok ASEGSN) mcsites.

Definition apostS : snode + pnode -> sst -> smodel -> sfam -> option (sst * smodel * sfam) :=
  apostP (hpost3 islx nsites) (ppostA img qsites mcsites).
Definition apostU2 : anode + (snode + pnode) -> sst -> smodel -> ast * sfam -> option (sst * smodel * (ast * sfam)) :=
  apostI (apost_alloc LIMIT) anil3 apostS.

#[using="Hwx His Hns"] Lemma hnode3_okS : forall nk, anode_okS ASEGSN cfg LIMIT (hpost3 islx nsites) awf3 (HA3 sarg) nk.
Proof. LiaFast.lf_pins (fun (Hwx His Hns : LiaFast.U) => LiaFast.u0). intros nk. exact (hnode3_ok cfg LIMIT sarg islx nsites Hwx His Hns nk). Qed.

#[using="Hwx Hsegb Hoff Hrespos Hreswf His Hns Himg Hqs Hms"] Theorem anodeU_ok : forall nk, anode_ok ASEGSN cfg LIMIT apostU2 (awfX awf awf3) (HAsum HA (HA3 sarg)) nk.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf His Hns Himg Hqs Hms : LiaFast.U) => LiaFast.u0).
  apply (anodeI_ok ASEGSN cfg LIMIT (apost_alloc LIMIT) awf HA apostS anil3 awf3 (HA3 sarg)).
  - exact (HA3_nil sarg).
  - exact HA_agree.
  - intros model0 E S M M' ms model a m0 m0' Hd Hk H. exact (HA_keep ASEGSN LIMIT model0 E S M M' ms model a m0 m0' Hd Hk H).
  - exact (alloc_anode_ok cfg LIMIT Hwx Hsegb Hoff Hrespos Hreswf).
  - apply (anodeP_okS ASEGSN cfg LIMIT (hpost3 islx nsites) awf3 (HA3 sarg) (ppostA img qsites mcsites)).
    + exact (HA3_agree sarg).
    + exact hnode3_okS.
    + exact (pnodeA_ok cfg LIMIT img qsites mcsites Hwx Himg Hqs Hms).
Qed.
End U.
(* [comment removed for export] *)
