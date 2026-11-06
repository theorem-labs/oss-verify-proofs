(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr Frame TacX Bytes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXRep AXRep2 AXRep_fields.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import N8Kit N8Kit2 N8Kit3 X8Kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac join_frameA LOW HIGH base :=
  lazymatch type of LOW with rw_cells _ ?mx _ ?cs1 =>
  lazymatch type of HIGH with rw_cells _ _ ?ah ?cs2 =>
    let J := fresh "FRJ" in
    assert (J : rw_cells bsegs mx base (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app bsegs mx base cs1 cs2)); split; [exact LOW | cbn [cells_size csize Nat.add];
            lazymatch goal with |- rw_cells _ _ ?a _ => replace a with ah by lia end; exact HIGH]);
    clear LOW HIGH; cbn [app] in J; rename J into LOW
  end end.

Ltac split_frameA FR cs1 cs2 LOW HIGH :=
  lazymatch type of FR with rw_cells _ ?mx ?base _ =>
    apply (proj1 (rw_cells_app bsegs mx base cs1 cs2)) in FR;
    destruct FR as [LOW HIGH]; cbn [cells_size csize Nat.add] in HIGH;
    repeat match type of HIGH with
    | rw_cells _ _ (Z.add (Z.add ?b ?c) (Z.of_nat ?k)) _ =>
        let v := eval vm_compute in (c + Z.of_nat k)%Z in
        replace (Z.add (Z.add b c) (Z.of_nat k)) with (Z.add b v) in HIGH by lia
    | rw_cells _ _ (Z.add ?b (Z.of_nat ?k)) _ =>
        let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in HIGH
    end
  end.

(* [comment removed for export] *)
Ltac shchk_brv_ge V1 V2 :=
  lazymatch type of V1 with 0 <= ?v < 8 =>
    let KV := fresh "KV" in let K2 := fresh "K2" in
    step; if_cases KV; zify_cond KV; rewrite ?(unsigned_lit v) in KV by (clear - V1; lia);
    [ (* [comment removed for export] *)
      zstep; first [ step; if_cases K2 | zstep; step; if_cases K2 ]; zify_cond K2;
      [ exfalso; revert K2; rewrite ?Z.add_0_r;
        first [ rewrite land7_mod8 by lia | idtac ];
        rewrite !bv_signed_small by (rewrite unsigned_lit; Z.div_mod_to_equations; lia);
        rewrite !unsigned_lit by (Z.div_mod_to_equations; lia); clear - V1 V2 KV; intros K2; lia
      | clear KV K2; step ]
    | clear KV ]
  end.

(* [comment removed for export] *)
Ltac shchk_ld1 RD :=
  step; clear RD;
  try replace (zxb (b8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity);
  try replace (sxb (b8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).

Section K.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma accessible_transport_awin : forall W m m' a n,
    accessible m a n -> munch W m m' -> Forall awin W -> accessible m' a n.
  Proof.
    intros W m m' a n AC MU FW. eapply accessible_transport; [exact AC| exact MU|].
    destruct AC as (A0 & A1 & _). intros x Hx. apply awin_outside_sh; [exact FW| lia].
  Qed.

  Lemma awin_wins_hi_stack : forall l h, aceil <= l -> awin (l, h).
  Proof. exact awin_stack. Qed.

  Lemma ACONST_transport_awin : forall W m m', ACONST m -> munch W m m' -> wmono bsegs m m' -> Forall awin W -> ACONST m'.
  Proof.
    intros W m m' AC MU WM FW. eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros iv (K & _ & _). exact K.
  Qed.

  (* [comment removed for export] *)
  Definition aside0 (m : mem) (ACC : list (Z * Z)) : Prop :=
    ACONST m /\ Forall (fun o : Z * Z => accessible m (fst o) (snd o)) ACC.

  Lemma aside0_transport : forall W m m' ACC,
    aside0 m ACC -> munch W m m' -> wmono bsegs m m' -> Forall awin W -> aside0 m' ACC.
  Proof.
    intros W m m' ACC (AC & FA) MU WM FW. split.
    - eapply ACONST_transport_awin; eauto.
    - eapply Forall_impl; [| exact FA]. intros [o n] K. cbn [fst snd] in *. eapply accessible_transport_awin; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma ANSAcc_transport_awin : forall W m m' ns, ANSAcc m ns -> munch W m m' -> Forall awin W -> ANSAcc m' ns.
  Proof.
    intros W m m' ns NA MU FW a nd L. destruct (NA a nd L) as (AL & AP & AC). split; [exact AL|]. split; [exact AP|].
    eapply accessible_transport_awin; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma stackW_awin : forall SP W, stackW SP W -> Forall awin W.
  Proof. intros SP W F. eapply Forall_impl; [| exact F]. intros [l h] [K _]. cbn [fst snd] in K. apply awin_stack. exact K. Qed.

  (* [comment removed for export] *)
  Lemma fwin_of_awin : forall Fa em l h, awin (l, h) -> AIMG_TOP <= l ->
    (h <= Fa \/ Fa + 48 <= l) -> (forall e d, em !! e = Some d -> h <= e \/ e + esize d <= l) -> fwin Fa em (l, h).
  Proof.
    intros Fa em l h (_ & _ & K) HL HS HE. split; [| split; [exact HS| exact HE]]. cbn [fst snd] in *.
    destruct K as [K|K]; [left; lia| right; exact K].
  Qed.
End K.
