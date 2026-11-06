(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarve AcAst AcHA AcPri AcMALp AcMALlib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition LVP_KEY : positive := 42%positive.
Definition apost_psr (i : nat) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let l := nth i (a_pri a) lc0 in
  if lwf (s_next S) l then Some (with_reg S LVP_KEY l, M, a) else None.

Lemma rkey_ne_big : forall (r : reg) (k : positive), (32 < k)%positive -> rkey r <> k.
Proof.
  intros r k Hk. destruct (decide (r = 0%bv)) as [->|Hr].
  - change (rkey 0%bv) with xH. lia.
  - destruct (rkey_succ r Hr) as (j & Hj & Ej). rewrite Ej. intros Hc.
    assert (X : Pos.to_nat (Pos.of_succ_nat j) = Pos.to_nat k) by (rewrite Hc; reflexivity).
    rewrite SuccNat2Pos.id_succ in X. lia.
Qed.

Section Psr.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.

(* [comment removed for export] *)
#[using="Type"] Theorem den_psr : forall mem0 E S M ms model k l, (32 < k)%positive ->
  DEN ASEGS LIMIT model0 mem0 E S M ms model -> DEN ASEGS LIMIT model0 mem0 E (with_reg S k l) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 E S M ms model k l Hk Hd.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; cbn [with_reg s_rgs s_next]; try assumption.
  intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_reg s_pc s_regs s_rgs s_facts s_resv].
  refine (conj A1 (conj A2 (conj A3 (conj _ (conj A5 (conj A6 (conj A7 A8))))))).
  intros r. rewrite (A4 r). rewrite rget_rset_other by (apply rkey_ne_big; exact Hk). reflexivity.
Qed.

#[using="Type"] Theorem npsr_node : forall i S M a S' M' a', apost_psr i S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_psr in H. cbv zeta in H.
  destruct (lwf (s_next S) (nth i (a_pri a) lc0)); [|discriminate]. injection H as <- <- <-.
  apply (Hk E mem0 ms model); [apply agree_refl | intros p Hp w Hw; reflexivity | | exact HHA].
  apply den_psr; [unfold LVP_KEY; lia | exact Hd].
Qed.
End Psr.
