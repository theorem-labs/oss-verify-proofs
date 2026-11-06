(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.

Module FxBlobLib.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma blob_sh_top : forall E M model BL w, blob_ok E M model BL -> blob_sh BL w -> w < SH_OFF + alloc_top (m_vmmaps model) / 8.
Proof.
  intros E M model BL w (Hbe & _) (p & Hp & Hs). rewrite Forall_forall in Hbe. destruct (Hbe p Hp) as (_ & _ & _ & _ & Ht).
  unfold SHz in Hs. assert ((bv_unsigned (fst p) + bv_unsigned (snd p)) / 8 <= alloc_top (m_vmmaps model) / 8) by (apply Z.div_le_mono; lia).
  lia.
Qed.
(* [comment removed for export] *)
End FxBlobLib.

Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode.FxBlobLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition existsb_cf {A : Type} (c f : A -> bool) (l : list A) : bool :=
  if existsb_lz (fun x => if c x then f x else false) l then true else existsb_lz (fun x => if c x then false else f x) l.
Lemma existsb_cf_eq : forall {A : Type} (c f : A -> bool) (l : list A), existsb_cf c f l = List.existsb f l.
Proof.
  intros A c f l. unfold existsb_cf. rewrite !existsb_lz_eq. induction l as [|x r IH]; [reflexivity|]. cbn [List.existsb].
  destruct (c x), (f x); cbn [orb]; try reflexivity; try exact IH.
  destruct (List.existsb (fun x0 => if c x0 then f x0 else false) r); reflexivity.
Qed.
Definition cand_t (a b : lin) : bool := match l_t a, l_t b with [], [] => true | ta, tb => shares ta tb end.

(* [comment removed for export] *)
Definition HSHB : Z := 0x2008fff7000.
(* [comment removed for export] *)
Definition hshb_g (g : lin * lin * gkind) : bool :=
  (lin_eqb (fst (fst g)) (lconst HSHB) && match gsz_c g with Some z => Z.eqb z (SH_HI - HSHB) | None => false end)%bool.
Lemma hshb_g_sound : forall E g, hshb_g g = true -> fst (fst g) = lconst HSHB /\ gsz E g = SH_HI - HSHB.
Proof.
  intros E g H. unfold hshb_g in H. apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1. split; [exact H1|].
  destruct (gsz_c g) as [z|] eqn:Hz; [|discriminate]. apply Z.eqb_eq in H2. subst z. exact (gsz_const E g _ Hz).
Qed.

(* [comment removed for export] *)
Record qsite : Type := QS { qs_pc0 : Z; qs_rP : reg; qs_rA : reg; qs_rB : reg; qs_rY : reg; qs_rZ : reg; qs_rW : reg;
                            qs_ord : bool; qs_bim : bv 13; qs_beq : bool }.

Definition qsite_ok (segs : list Segment) (q : qsite) : Prop :=
  let '(QS pc0 rP rA rB rY rZ rW ord bim beq) := q in
  (rP <> 0%bv /\ rA <> 0%bv /\ rY <> 0%bv /\ rZ <> 0%bv /\ rW <> 0%bv) /\
  (rA <> rP /\ rY <> rP /\ rY <> rA /\ rZ <> rP /\ rZ <> rA /\ rZ <> rY /\ rW <> rP /\ rW <> rA /\ rW <> rY /\ rW <> rZ) /\
  (rB <> rP /\ rB <> rA /\ rB <> rY) /\
  qins segs pc0 0 (Load SZ8 true rY rP (Z_to_bv 12 0)) /\
  qins segs pc0 1 (if ord then ShiftImm ALU_SRL rP rB (Z_to_bv 6 3) else OpImm ALU_ADD rA rA (Z_to_bv 12 (-1))) /\
  qins segs pc0 2 (if ord then OpImm ALU_ADD rA rA (Z_to_bv 12 (-1)) else ShiftImm ALU_SRL rP rB (Z_to_bv 6 3)) /\
  qins segs pc0 3 (ShiftImm ALU_SRL rZ rA (Z_to_bv 6 3)) /\ qins segs pc0 4 (Op ALU_ADD rP rY rP) /\
  qins segs pc0 5 (Op ALU_ADD rY rY rZ) /\ qins segs pc0 6 (OpImm ALU_AND rZ rP (Z_to_bv 12 (-8))) /\
  qins segs pc0 7 (OpImm ALU_AND rW rY (Z_to_bv 12 (-8))) /\ qins segs pc0 8 (Load SZ8 true rZ rZ (Z_to_bv 12 0)) /\
  qins segs pc0 9 (Load SZ8 true rW rW (Z_to_bv 12 0)) /\ qins segs pc0 10 (Op ALU_OR rZ rW rZ) /\
  qins segs pc0 11 (Branch (if beq then BC_EQ else BC_NE) rZ (Z_to_bv 5 0) bim).

(* [comment removed for export] *)
Definition qs_ok (q : qsite) : Z := bv_unsigned (qok2 (qs_pc0 q) (qs_bim q) (qs_beq q)).

(* [comment removed for export] *)
Definition qc_rg4_ref (fs : list fact) (gs : list (lin * lin * gkind)) (R : region) : bool :=
  let rb := irange fs (rg_base R) in
  if Z.leb SH_HI (fst rb) then true else
  let sz := snd (irange fs (rg_size R)) in
  if Z.leb (snd rb + sz) HSHB then true else
  if sep_pgrant_acc fs gs (length gs) O R then true else
  existsb (fun g => (negb (is_mark g) && negb (match is_const (fst (fst g)) with Some z => Z.eqb z HSHB | None => false end) &&
                     Z.leb 1 sz && contained_b fs (rg_base R) sz (fst (fst g)) (gsz_lo fs g))%bool) gs.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pg_test (fs : list fact) (sz : Z) (R : region) (j : nat) (ig : nat * (lin * lin * gkind)) : bool :=
  negb (is_mark (snd ig)) &&& negb (Nat.eqb (fst ig) j) &&& Z.leb 1 sz &&&
  match srl_lin fs 3 (fst (fst (snd ig))) with
  | Some pb => contained_b fs (rg_base R) sz (laddc pb SH_OFF) (gsz_lo fs (snd ig) / 8)
  | None => false
  end.
Lemma pg_test_unf : forall fs sz R j i g,
  pg_test fs sz R j (i, g) = (negb (is_mark g) &&& negb (Nat.eqb i j) &&& Z.leb 1 sz &&&
                              match srl_lin fs 3 (fst (fst g)) with
                              | Some pb => contained_b fs (rg_base R) sz (laddc pb SH_OFF) (gsz_lo fs g / 8)
                              | None => false
                              end).
Proof. reflexivity. Qed.
Lemma sep_pgrant_acc_ex : forall fs gs j i R,
  sep_pgrant_acc fs gs j i R = List.existsb (pg_test fs (snd (irange fs (rg_size R))) R j) (List.combine (List.seq i (length gs)) gs).
Proof.
  intros fs gs j. induction gs as [|g r IH]; intros i R; [reflexivity|].
  cbn [sep_pgrant_acc length List.seq List.combine List.existsb]. rewrite IH, pg_test_unf.
  match goal with |- (if ?t then true else _) = _ => destruct t; reflexivity end.
Qed.
Definition sep_pgrant_cf (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (sz : Z) (R : region) : bool :=
  existsb_cf (fun ig => cand_t (rg_base R) (fst (fst (snd ig)))) (pg_test fs sz R j) (List.combine (List.seq O (length gs)) gs).
Lemma sep_pgrant_cf_eq : forall fs gs j R, sep_pgrant_cf fs gs j (snd (irange fs (rg_size R))) R = sep_pgrant_acc fs gs j O R.
Proof. intros fs gs j R. unfold sep_pgrant_cf. rewrite existsb_cf_eq, sep_pgrant_acc_ex. reflexivity. Qed.
Definition qc_hint_sh (R : region) : bool := Z.leb SH_LO (l_c (rg_base R)) &&& Z.ltb (l_c (rg_base R)) SH_HI.
Definition qc_rg4 (fs : list fact) (gs : list (lin * lin * gkind)) (R : region) : bool :=
  let rb := irange fs (rg_base R) in
  if Z.leb SH_HI (fst rb) then true else
  let sz := snd (irange fs (rg_size R)) in
  if Z.leb (snd rb + sz) HSHB then true else
  if qc_hint_sh R then
    (if sep_pgrant_cf fs gs (length gs) sz R then true else
     existsb_cf (fun g => cand_t (rg_base R) (fst (fst g)))
                (fun g => (negb (is_mark g) && negb (match is_const (fst (fst g)) with Some z => Z.eqb z HSHB | None => false end) &&
                           Z.leb 1 sz) &&& contained_b fs (rg_base R) sz (fst (fst g)) (gsz_lo fs g)) gs)
  else
    (if existsb_cf (fun g => cand_t (rg_base R) (fst (fst g)))
                (fun g => (negb (is_mark g) && negb (match is_const (fst (fst g)) with Some z => Z.eqb z HSHB | None => false end) &&
                           Z.leb 1 sz) &&& contained_b fs (rg_base R) sz (fst (fst g)) (gsz_lo fs g)) gs then true else
     sep_pgrant_cf fs gs (length gs) sz R).
Lemma qc_rg4_eq : forall fs gs R, qc_rg4 fs gs R = qc_rg4_ref fs gs R.
Proof.
  intros fs gs R. unfold qc_rg4, qc_rg4_ref. cbv zeta. rewrite sep_pgrant_cf_eq.
  set (sz := snd (irange fs (rg_size R))).
  assert (K : existsb_cf (fun g => cand_t (rg_base R) (fst (fst g)))
                (fun g => (negb (is_mark g) && negb (match is_const (fst (fst g)) with Some z => Z.eqb z HSHB | None => false end) &&
                                    Z.leb 1 sz) &&& contained_b fs (rg_base R) sz (fst (fst g)) (gsz_lo fs g)) gs =
              existsb (fun g => (negb (is_mark g) && negb (match is_const (fst (fst g)) with Some z => Z.eqb z HSHB | None => false end) &&
                                 Z.leb 1 sz && contained_b fs (rg_base R) sz (fst (fst g)) (gsz_lo fs g))%bool) gs).
  { rewrite existsb_cf_eq. reflexivity. }
  rewrite K.
  destruct (Z.leb SH_HI (fst (irange fs (rg_base R)))); [reflexivity|].
  destruct (Z.leb (snd (irange fs (rg_base R)) + sz) HSHB); [reflexivity|].
  destruct (qc_hint_sh R); destruct (sep_pgrant_acc fs gs (length gs) O R);
    match goal with |- context [if ?y then true else _] => destruct y; reflexivity | |- _ => reflexivity end.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qc_rgz (R : region) : bool :=
  match rg_kind R with RZ => range_zero (rg_cont R) 0 two64 | _ => false end.
(* [comment removed for export] *)
Definition qc_rg (fs : list fact) (gs : list (lin * lin * gkind)) (R : region) : bool := if qc_rgz R then true else qc_rg4 fs gs R.
(* [comment removed for export] *)
Definition qc_own (fs : list fact) (p : lin * lin) : bool :=
  let rb := irange fs (fst p) in (Z.leb (snd rb + snd (irange fs (snd p))) HSHB || Z.leb SH_HI (fst rb))%bool.
(* [comment removed for export] *)
Definition qc_own2 (fs : list fact) (gs : list (lin * lin * gkind)) (p : lin * lin) : bool :=
  if qc_own fs p then true else
  match is_const (snd p) with
  | Some sz => existsb (fun g => (negb (is_mark g) && negb (match is_const (fst (fst g)) with Some z => Z.eqb z HSHB | None => false end) &&
                                  Z.leb 1 sz && contained_b fs (fst p) sz (fst (fst g)) (gsz_lo fs g))%bool) gs
  | None => false
  end.

(* [comment removed for export] *)
Definition qc_own3 (fs : list fact) (sp : lin) (p : lin * lin) : bool :=
  let '(dlo, dhi) := irange fs (lsub (laddc sp (8 * SH_OFF)) (lscale 8 (ladd (fst p) (snd p)))) in
  (Z.leb 8388608 dlo && Z.leb dhi (2 ^ 62) && Z.ltb (snd (irange fs (fst p)) + snd (irange fs (snd p))) (2 ^ 60))%bool.
Definition qc_ownx_ref (fs : list fact) (gs : list (lin * lin * gkind)) (sp : lin) (p : lin * lin) : bool :=
  if qc_own2 fs gs p then true else qc_own3 fs sp p.
(* [comment removed for export] *)
Definition qc_own2s (fs : list fact) (gs : list (lin * lin * gkind)) (p : lin * lin) : bool :=
  match is_const (snd p) with
  | Some sz => existsb_cf (fun g => cand_t (fst p) (fst (fst g)))
                 (fun g => (negb (is_mark g) && negb (match is_const (fst (fst g)) with Some z => Z.eqb z HSHB | None => false end) &&
                                     Z.leb 1 sz) &&& contained_b fs (fst p) sz (fst (fst g)) (gsz_lo fs g)) gs
  | None => false
  end.
Definition qc_ownx (fs : list fact) (gs : list (lin * lin * gkind)) (sp : lin) (p : lin * lin) : bool :=
  if qc_own fs p then true else if qc_own3 fs sp p then true else qc_own2s fs gs p.
Lemma qc_ownx_eq : forall fs gs sp p, qc_ownx fs gs sp p = qc_ownx_ref fs gs sp p.
Proof.
  intros fs gs sp p. unfold qc_ownx, qc_ownx_ref, qc_own2, qc_own2s.
  assert (K : match is_const (snd p) with
              | Some sz => existsb_cf (fun g => cand_t (fst p) (fst (fst g)))
                             (fun g => (negb (is_mark g) && negb (match is_const (fst (fst g)) with Some z => Z.eqb z HSHB | None => false end) &&
                                                 Z.leb 1 sz) &&& contained_b fs (fst p) sz (fst (fst g)) (gsz_lo fs g)) gs
              | None => false end =
              match is_const (snd p) with
              | Some sz => existsb (fun g => (negb (is_mark g) && negb (match is_const (fst (fst g)) with Some z => Z.eqb z HSHB | None => false end) &&
                                              Z.leb 1 sz && contained_b fs (fst p) sz (fst (fst g)) (gsz_lo fs g))%bool) gs
              | None => false end).
  { destruct (is_const (snd p)) as [sz|]; [|reflexivity]. rewrite existsb_cf_eq. reflexivity. }
  rewrite K. destruct (qc_own fs p), (qc_own3 fs sp p); try reflexivity;
    match goal with |- ?x = (if ?y then true else _) => destruct y; reflexivity end.
Qed.

(* [comment removed for export] *)
Definition qc_allow (fs : list fact) (sp : lin) (p : lin * Z) : bool :=
  let '(dlo, dhi) := irange fs (lsub (laddc sp (8 * SH_OFF)) (lscale 8 (fst p))) in
  (Z.leb (2 ^ 20 + 64) dlo && Z.leb dhi (2 ^ 40) && Z.leb (dhi / 8 + 2 ^ 19 + 4096) (snd p) && Z.ltb (snd (irange fs (fst p))) (2 ^ 61))%bool.
(* [comment removed for export] *)
Definition qc_allowL (fs : list fact) (sp : lin) (p : lin * Z) : bool :=
  let '(dlo, dhi) := irange fs (lsub (laddc sp (8 * SH_OFF)) (lscale 8 (fst p))) in
  if (Z.leb (2 ^ 20 + 64) dlo && Z.leb dhi (2 ^ 40) && Z.leb (dhi / 8 + 2 ^ 19 + 4096) (snd p))%bool then Z.ltb (snd (irange fs (fst p))) (2 ^ 61) else false.
Lemma qc_allowL_eq : forall fs sp p, qc_allowL fs sp p = qc_allow fs sp p.
Proof.
  intros fs sp p. unfold qc_allowL, qc_allow. destruct (irange fs (lsub (laddc sp (8 * SH_OFF)) (lscale 8 (fst p)))) as [dlo dhi].
  destruct (Z.leb (2 ^ 20 + 64) dlo && Z.leb dhi (2 ^ 40) && Z.leb (dhi / 8 + 2 ^ 19 + 4096) (snd p))%bool; reflexivity.
Qed.
Definition qc_allow_scan (fs : list fact) (sp : lin) (al : list (lin * Z)) : bool := existsb_cf (fun p => cand_t sp (fst p)) (qc_allowL fs sp) al.
Lemma qc_allow_scan_eq : forall fs sp al, qc_allow_scan fs sp al = List.existsb (qc_allow fs sp) al.
Proof.
  intros fs sp al. unfold qc_allow_scan. rewrite existsb_cf_eq. induction al as [|p r IH]; [reflexivity|]. cbn [List.existsb]. rewrite IH, qc_allowL_eq. reflexivity.
Qed.

Definition qc_chk (img : tree Z) (q : qsite) (S : sst) (M : smodel) : bool :=
  let fs := s_facts S in let rgs := s_rgs S in
  let b := rget (s_regs S) (rkey (qs_rB q)) in
  match s_resv S, is_const (rget (s_regs S) (rkey (qs_rP q))) with
  | RNone, Some P =>
      let '(nlo, nhi) := irange fs (lsub (rget (s_regs S) (rkey (qs_rA q))) b) in
      let '(blo, bhi) := irange fs b in let '(dlo, dhi) := irange fs (lsub b (sm_sp M)) in
      if (Z.eqb (s_pc S) (qs_pc0 q) && Z.leb 1 nlo && Z.leb nhi 64 && lwf (s_next S) b &&
       match load_at img fs rgs (lconst P) SZ8 false with Some (Some sl) => lin_eqb sl (lconst SH_OFF) | _ => false end &&
       Z.leb SH_HI blo && Z.ltb (bhi + nhi) two64 && Z.leb (snd (irange fs (rget (s_regs S) (rkey (qs_rA q))))) 0x800000000000 &&
       ((Z.leb 0 dlo && Z.leb dhi (2 ^ 22)) || (Z.leb (two64 - 2 ^ 20) dlo && Z.ltb dhi two64)) &&
       existsb (fun z => (Z.eqb (fst z) HSHB && Z.eqb (snd z) SH_HI)%bool) (sm_zr M) &&
       existsb hshb_g (sm_maps M))%bool
      then (qc_allow_scan fs (sm_sp M) (sm_allow M) && forallb (qc_ownx fs (sm_maps M) (sm_sp M)) (sm_own M) && forallb (qc_rg fs (sm_maps M)) rgs)%bool
      else false
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition qc_post (q : qsite) (S : sst) : sst :=
  SST (qs_ok q)
      (rset (rset (rset (rset (rset (s_regs S) (rkey (qs_rP q)) (lvar (s_next S))) (rkey (qs_rY q)) (lvar (Pos.succ (s_next S))))
                        (rkey (qs_rA q)) (laddc (rget (s_regs S) (rkey (qs_rA q))) (-1))) (rkey (qs_rZ q)) (lconst 0)) (rkey (qs_rW q)) (lconst 0))
      (s_rgs S) (s_facts S) (Pos.succ (Pos.succ (s_next S))) (s_resv S).

(* [comment removed for export] *)
Section QSep.
Variable E : valu.
Variable fs : list fact.
Variable gs : list (lin * lin * gkind).
Variable model : Model.
Variable BL : list (word * word).
Hypothesis HF : Forall (fact_ok E) fs.
Hypothesis Hmaps : vm_maps (m_vmmaps model) = lden_maps E BL gs.
Hypothesis Hpd : pdisj (vm_maps (m_vmmaps model)).
Hypothesis Hgsh : Forall (gshape_ok E) gs.
Hypothesis Hgtop : Forall (fun g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model)) gs.

#[using="Type"] Lemma u_laddc_small : forall l c, 0 <= c -> uE E l + c < two64 -> uE E (laddc l c) = uE E l + c.
Proof. LiaFast.lf_pins LiaFast.u0. intros l c Hc H. unfold uE. rewrite lden_laddc. rewrite fg64'; [reflexivity|]. pose proof (uE_range E l). unfold uE in *. lia. Qed.

#[using="BL HF Hmaps Hpd Hgsh Hgtop"] Theorem qc_rg_sound : forall R (k : lin * lin * gkind) x,
  qc_rg4 fs gs R = true -> 0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 ->
  In k gs -> fst (fst k) = lconst HSHB -> gsz E k = SH_HI - HSHB ->
  HSHB <= x < SH_HI -> SH_OFF + alloc_top (m_vmmaps model) / 8 + 8 <= x ->
  ~ (uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R).
Proof. LiaFast.lf_pins (fun (BL HF Hmaps Hpd Hgsh Hgtop : LiaFast.U) => LiaFast.u0).
  intros R k x H Hrs Hrw Hk Hkb Hks Hx Hxa Hin. rewrite qc_rg4_eq in H. unfold qc_rg4_ref in H. cbv zeta in H.
  pose proof (irange_sound E fs (rg_base R) HF) as Rb. fold (uE E (rg_base R)) in Rb.
  pose proof (irange_sound E fs (rg_size R) HF) as Rs. unfold rsz in Rs. fold (rsz E R) in Rs.
  set (lo := fst (irange fs (rg_base R))) in *. set (hi := snd (irange fs (rg_base R))) in *.
  set (sz := snd (irange fs (rg_size R))) in *.
  revert H. destruct (Z.leb SH_HI lo) eqn:Ha; intros H; [|cbv iota in H].
  { (* [comment removed for export] *) apply Z.leb_le in Ha. unfold SH_HI in *. lia. }
  revert H. destruct (Z.leb (hi + sz) HSHB) eqn:Hb; intros H; [|cbv iota in H].
  { (* [comment removed for export] *) apply Z.leb_le in Hb. lia. }
  revert H. destruct (sep_pgrant_acc fs gs (length gs) O R) eqn:Hcc; intros H; [|cbv iota in H].
  - (* [comment removed for export] *)
    destruct (sep_pgrant_acc_spec fs gs (length gs) O R Hcc) as (i' & g & pb & _ & _ & Hn & Hs & Hs1 & Hc & _). rewrite Nat.sub_0_r in Hn.
    rewrite Forall_forall in Hgsh, Hgtop. pose proof (Hgsh g (nth_error_In _ _ Hn)) as (G1 & G2 & G3 & G4 & G5).
    pose proof (Hgtop g (nth_error_In _ _ Hn)) as Gt.
    pose proof (srl_lin_sound E fs 3 (fst (fst g)) pb HF ltac:(lia) Hs) as Hpb. fold (uE E pb) (uE E (fst (fst g))) in Hpb.
    rewrite Z.shiftr_div_pow2 in Hpb by lia. change (2 ^ 3) with 8 in Hpb.
    assert (Hpbs : uE E (laddc pb SH_OFF) = uE E pb + SH_OFF) by (apply u_laddc_small; [unfold SH_OFF; lia | rewrite Hpb; unfold SH_OFF, two64 in *; lia]).
    pose proof (gsz_bounds E fs g HF) as Gb. pose proof (gsz_lo_nonneg fs g) as Gb0.
    assert (Gdv : gsz_lo fs g / 8 <= gsz E g / 8) by (apply Z.div_le_mono; lia).
    destruct (contained_sound E fs (rg_base R) sz (laddc pb SH_OFF) (gsz_lo fs g / 8) HF Hc ltac:(lia)
                ltac:(rewrite Hpbs, Hpb; assert (gsz E g / 8 <= gsz E g) by (apply Z.div_le_upper_bound; lia); unfold SH_OFF, two64 in *; lia))
      as [C1 C2].
    rewrite Hpbs, Hpb in C2.
    assert (Hdv : uE E (fst (fst g)) / 8 + gsz E g / 8 <= alloc_top (m_vmmaps model) / 8).
    { assert (E1 : uE E (fst (fst g)) = 8 * (uE E (fst (fst g)) / 8)) by (pose proof (Z.div_mod (uE E (fst (fst g))) 4096 ltac:(lia)); pose proof (Z.div_mod (uE E (fst (fst g))) 8 ltac:(lia)); lia).
      assert (E2 : gsz E g = 8 * (gsz E g / 8)) by (pose proof (Z.div_mod (gsz E g) 4096 ltac:(lia)); pose proof (Z.div_mod (gsz E g) 8 ltac:(lia)); lia).
      apply Z.div_le_mono with (c := 8) in Gt; [|lia]. rewrite E1, E2 in Gt.
      replace (8 * (uE E (fst (fst g)) / 8) + 8 * (gsz E g / 8)) with ((uE E (fst (fst g)) / 8 + gsz E g / 8) * 8) in Gt by ring.
      rewrite Z.div_mul in Gt by lia. exact Gt. }
    lia.
  - (* [comment removed for export] *)
    apply existsb_exists in H as (g & Hg & Hc). apply andb_prop in Hc as [Hc Hcn]. apply andb_prop in Hc as [Hneq Hsz1]. apply andb_prop in Hneq as [Hgm Hneq]. apply negb_true_iff in Hgm.
    apply Z.leb_le in Hsz1.
    rewrite Forall_forall in Hgsh. pose proof (Hgsh g Hg) as Gg. pose proof (Hgsh k Hk) as Gk.
    pose proof (gsz_bounds E fs g HF) as Gb. pose proof (gsz_lo_nonneg fs g) as Gb0.
    destruct (contained_sound E fs (rg_base R) sz (fst (fst g)) (gsz_lo fs g) HF Hcn ltac:(lia)
                ltac:(destruct Gg as (_ & _ & _ & G4 & _); unfold two64; lia)) as [C1 C2].
    destruct (In_nth_error _ _ Hg) as (i & Hi). destruct (In_nth_error _ _ Hk) as (i' & Hi').
    destruct (Nat.eq_dec i i') as [->|Hne].
    + rewrite Hi in Hi'. injection Hi' as <-. rewrite Hkb in Hneq. cbn in Hneq. unfold HSHB in Hneq. discriminate.
    + assert (Hd : iv_disj (gden E g) (gden E k)).
      { rewrite Hmaps in Hpd. apply (pdisj_lden_nth E BL gs i i' g k Hpd Hi Hi' Hne Hgm). unfold is_mark. rewrite Hkb. reflexivity. }
      unfold iv_disj in Hd. rewrite !gden_uB, !gden_uS in Hd by assumption.
      rewrite Hkb, Hks in Hd. unfold uE in Hd. rewrite lden_lconst, fg64' in Hd by (unfold HSHB, two64; lia).
      fold (uE E (fst (fst g))) in Hd. unfold SH_HI, HSHB in *. lia.
Qed.

#[using="model BL HF Hmaps Hpd Hgsh"] Theorem qc_own2_sound : forall p (k : lin * lin * gkind) x,
  qc_own2 fs gs p = true -> In k gs -> fst (fst k) = lconst HSHB -> gsz E k = SH_HI - HSHB ->
  HSHB <= x < SH_HI -> ~ (uE E (fst p) <= x < uE E (fst p) + uE E (snd p)).
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hpd Hgsh : LiaFast.U) => LiaFast.u0).
  intros p k x H Hk Hkb Hks Hx Hin. unfold qc_own2 in H.
  destruct (qc_own fs p) eqn:Ho.
  - unfold qc_own in Ho. cbv zeta in Ho.
    pose proof (irange_sound E fs (fst p) HF) as R1. pose proof (irange_sound E fs (snd p) HF) as R2.
    fold (uE E (fst p)) in R1. fold (uE E (snd p)) in R2.
    apply orb_prop in Ho as [Ho|Ho]; apply Z.leb_le in Ho; unfold HSHB, SH_HI in *; lia.
  - destruct (is_const (snd p)) as [sz|] eqn:Hsz; [|discriminate].
    destruct (is_const_sound E _ sz Hsz) as [Hv Hr].
    assert (Hu : uE E (snd p) = sz) by (unfold uE; rewrite Hv; apply fg64'; exact Hr).
    rewrite Hu in Hin.
    apply existsb_exists in H as (g & Hg & Hc). apply andb_prop in Hc as [Hc Hcn]. apply andb_prop in Hc as [Hneq Hsz1]. apply andb_prop in Hneq as [Hgm Hneq]. apply negb_true_iff in Hgm.
    apply Z.leb_le in Hsz1.
    rewrite Forall_forall in Hgsh. pose proof (Hgsh g Hg) as Gg. pose proof (Hgsh k Hk) as Gk.
    pose proof (gsz_bounds E fs g HF) as Gb. pose proof (gsz_lo_nonneg fs g) as Gb0.
    destruct (contained_sound E fs (fst p) sz (fst (fst g)) (gsz_lo fs g) HF Hcn ltac:(lia)
                ltac:(destruct Gg as (_ & _ & _ & G4 & _); unfold two64; lia)) as [C1 C2].
    destruct (In_nth_error _ _ Hg) as (i & Hi). destruct (In_nth_error _ _ Hk) as (i' & Hi').
    destruct (Nat.eq_dec i i') as [->|Hne].
    + rewrite Hi in Hi'. injection Hi' as <-. rewrite Hkb in Hneq. cbn in Hneq. unfold HSHB in Hneq. discriminate.
    + assert (Hd : iv_disj (gden E g) (gden E k)).
      { rewrite Hmaps in Hpd. apply (pdisj_lden_nth E BL gs i i' g k Hpd Hi Hi' Hne Hgm). unfold is_mark. rewrite Hkb. reflexivity. }
      unfold iv_disj in Hd. rewrite !gden_uB, !gden_uS in Hd by assumption.
      rewrite Hkb, Hks in Hd. unfold uE in Hd. rewrite lden_lconst, fg64' in Hd by (unfold HSHB, two64; lia).
      fold (uE E (fst (fst g))) in Hd. unfold SH_HI, HSHB in *. lia.
Qed.

(* [comment removed for export] *)
#[using="HF"] Theorem qc_own3_sound : forall sp p x,
  qc_own3 fs sp p = true -> uE E sp <= 2 ^ 47 -> SH_OFF + (uE E sp - 8388608) / 8 + 8 <= x ->
  ~ (uE E (fst p) <= x < uE E (fst p) + uE E (snd p)).
Proof. LiaFast.lf_pins (fun (HF : LiaFast.U) => LiaFast.u0).
  intros sp p x H Hsp47 Hx Hin. unfold qc_own3 in H.
  destruct (irange fs (lsub (laddc sp (8 * SH_OFF)) (lscale 8 (ladd (fst p) (snd p))))) as [dlo dhi] eqn:Hdd.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. apply Z.ltb_lt in H3.
  pose proof (irange_sound E fs (fst p) HF) as R1. pose proof (irange_sound E fs (snd p) HF) as R2.
  fold (uE E (fst p)) in R1. fold (uE E (snd p)) in R2.
  pose proof (irange_sound E fs (lsub (laddc sp (8 * SH_OFF)) (lscale 8 (ladd (fst p) (snd p)))) HF) as Rdd. rewrite Hdd in Rdd. cbn [fst snd] in Rdd.
  fold (uE E (lsub (laddc sp (8 * SH_OFF)) (lscale 8 (ladd (fst p) (snd p))))) in Rdd.
  pose proof (uE_range E (fst p)) as B1. pose proof (uE_range E (snd p)) as B2. pose proof (uE_range E sp) as B3.
  assert (He : uE E (ladd (fst p) (snd p)) = uE E (fst p) + uE E (snd p)).
  { unfold uE. rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    apply Z.mod_small. fold (uE E (fst p)) (uE E (snd p)). unfold two64 in *. lia. }
  assert (Hsl : uE E (lscale 8 (ladd (fst p) (snd p))) = 8 * (uE E (fst p) + uE E (snd p))).
  { unfold uE at 1. rewrite lden_lscale. fold (uE E (ladd (fst p) (snd p))). rewrite He. apply fg64'. unfold two64 in *. lia. }
  assert (Hsa : uE E (laddc sp (8 * SH_OFF)) = uE E sp + 8 * SH_OFF) by (apply u_laddc_small; unfold SH_OFF, two64 in *; lia).
  destruct (small_diff E (laddc sp (8 * SH_OFF)) (lscale 8 (ladd (fst p) (snd p))) dlo dhi Rdd) as [[Hl Hd]|[Hl Hd]]; rewrite Hsl, Hsa in Hd, Hl.
  - pose proof (Z.div_mod (uE E sp - 8388608) 8 ltac:(lia)) as Ed. pose proof (Z.mod_pos_bound (uE E sp - 8388608) 8 ltac:(lia)) as Em.
    unfold SH_OFF in *. set (q := (uE E sp - 8388608) / 8) in *. set (m := (uE E sp - 8388608) mod 8) in *.
    set (D := uE E (lsub (laddc sp (8 * 2147450880)) (lscale 8 (ladd (fst p) (snd p))))) in *. clearbody q m D. clear - Hd Rdd H1 Hin Hx Ed Em. lia.
  - unfold two64, SH_OFF in *. set (D := uE E (lsub (laddc sp (8 * 2147450880)) (lscale 8 (ladd (fst p) (snd p))))) in *. clearbody D.
    clear - Hd Rdd H2 H3 R1 R2 B1 B2 B3 Hl Hsp47. lia.
Qed.
End QSep.

(* [comment removed for export] *)
Lemma u_small : forall z, 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply fg64'. exact Hz. Qed.

Lemma land_m8 : forall x, 0 <= x < two64 -> Z.land x (bv_wrap 64 (-8)) = 8 * (x / 8).
Proof.
  intros x Hx. change (bv_wrap 64 (-8)) with (Z.lnot (Z.ones 3) mod 2 ^ 64).
  replace (Z.lnot (Z.ones 3) mod 2 ^ 64) with (Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity.
  assert (H1 : Z.land x (Z.ldiff (Z.ones 64) (Z.ones 3)) = Z.ldiff (Z.land x (Z.ones 64)) (Z.ones 3)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x i), (Z.testbit (Z.ones 64) i), (Z.testbit (Z.ones 3) i); reflexivity. }
  rewrite H1. rewrite Z.land_ones by lia. rewrite Z.mod_small by (unfold two64 in Hx; lia).
  rewrite ldiff_ones_sub by lia. change (2 ^ 3) with 8. pose proof (Z.div_mod x 8 ltac:(lia)). lia.
Qed.

Section Words.
Variables (b : word) (n : Z).
Hypothesis Hb : SH_HI <= bv_unsigned b.
Hypothesis Hbn : bv_unsigned b + n <= 0x800000000000.
Hypothesis Hn : 1 <= n <= 64.
Let sh := Z_to_bv 64 SH_OFF.
Let Hb0 : 0x10007fff8000 <= bv_unsigned b. Proof. exact Hb. Qed.

#[using="n Hb Hbn Hn Hb0"] Lemma qX_u : bv_unsigned (qX sh b) = SH_OFF + bv_unsigned b / 8.
Proof. LiaFast.lf_pins (fun (n Hb Hbn Hn Hb0 : LiaFast.U) => LiaFast.u0).
  unfold qX, v_add, v_srli. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (u_small (bv_unsigned b / 8)) by (assert (bv_unsigned b / 8 <= bv_unsigned b) by (apply Z.div_le_upper_bound; lia); unfold two64, SH_HI in *; lia).
  unfold sh. rewrite (u_small SH_OFF) by (unfold SH_OFF, two64; lia).
  apply u_small. assert (bv_unsigned b / 8 <= bv_unsigned b) by (apply Z.div_le_upper_bound; lia). unfold SH_OFF, two64 in *. lia.
Qed.
#[using="Hb Hbn Hn Hb0"] Lemma qlast_u : bv_unsigned (qlast b n) = bv_unsigned b + n - 1.
Proof. LiaFast.lf_pins (fun (Hb Hbn Hn Hb0 : LiaFast.U) => LiaFast.u0).
  unfold qlast, v_addi, v_add. rewrite (u_small n) by (unfold two64; lia).
  rewrite (u_small (bv_unsigned b + n)) by (unfold two64; lia). apply u_small. unfold two64, SH_HI in *. lia.
Qed.
#[using="Hb Hbn Hn Hb0"] Lemma qY_u : bv_unsigned (qY sh b n) = SH_OFF + (bv_unsigned b + n - 1) / 8.
Proof. LiaFast.lf_pins (fun (Hb Hbn Hn Hb0 : LiaFast.U) => LiaFast.u0).
  unfold qY, v_add, v_srli. rewrite qlast_u. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (H0 : 0 <= (bv_unsigned b + n - 1) / 8 <= bv_unsigned b + n - 1) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite (u_small ((bv_unsigned b + n - 1) / 8)) by (unfold two64 in *; lia).
  unfold sh. rewrite (u_small SH_OFF) by (unfold SH_OFF, two64; lia). apply u_small. unfold SH_OFF, two64 in *. lia.
Qed.
#[using="n Hb Hbn Hn Hb0"] Lemma qw1_u : bv_unsigned (qw1 sh b) = 8 * ((SH_OFF + bv_unsigned b / 8) / 8).
Proof. LiaFast.lf_pins (fun (n Hb Hbn Hn Hb0 : LiaFast.U) => LiaFast.u0).
  unfold qw1, v_andi. rewrite qX_u. rewrite land_m8.
  - apply u_small. split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; [apply Z.add_nonneg_nonneg; [unfold SH_OFF; lia | apply Z.div_pos; lia] | lia]]|].
    assert (8 * ((SH_OFF + bv_unsigned b / 8) / 8) <= SH_OFF + bv_unsigned b / 8) by (apply Z.mul_div_le; lia).
    assert (bv_unsigned b / 8 <= bv_unsigned b) by (apply Z.div_le_upper_bound; lia). unfold SH_OFF, two64 in *. lia.
  - split; [apply Z.add_nonneg_nonneg; [unfold SH_OFF; lia | apply Z.div_pos; lia]|].
    assert (bv_unsigned b / 8 <= bv_unsigned b) by (apply Z.div_le_upper_bound; lia). unfold SH_OFF, two64 in *. lia.
Qed.
#[using="Hb Hbn Hn Hb0"] Lemma qw2_u : bv_unsigned (qw2 sh b n) = 8 * ((SH_OFF + (bv_unsigned b + n - 1) / 8) / 8).
Proof. LiaFast.lf_pins (fun (Hb Hbn Hn Hb0 : LiaFast.U) => LiaFast.u0).
  unfold qw2, v_andi. rewrite qY_u.
  assert (H0 : 0 <= (bv_unsigned b + n - 1) / 8 <= bv_unsigned b + n - 1) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite land_m8 by (unfold SH_OFF, two64 in *; lia).
  apply u_small. split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; [unfold SH_OFF; lia | lia]]|].
  assert (8 * ((SH_OFF + (bv_unsigned b + n - 1) / 8) / 8) <= SH_OFF + (bv_unsigned b + n - 1) / 8) by (apply Z.mul_div_le; lia).
  unfold SH_OFF, two64 in *. lia.
Qed.
(* [comment removed for export] *)
#[using="Hb Hbn Hn Hb0"] Lemma qw_geo : forall w, (w = qw1 sh b \/ w = qw2 sh b n) ->
  HSHB <= bv_unsigned w /\ bv_unsigned w + 8 <= SH_HI /\ SH_OFF + bv_unsigned b / 8 - 7 <= bv_unsigned w /\
  bv_unsigned w <= SH_OFF + (bv_unsigned b + 63) / 8.
Proof. LiaFast.lf_pins (fun (Hb Hbn Hn Hb0 : LiaFast.U) => LiaFast.u0).
  intros w [->| ->].
  - rewrite qw1_u. set (y := SH_OFF + bv_unsigned b / 8).
    pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)).
    assert (Hy1 : HSHB <= y) by (unfold y, HSHB, SH_OFF; assert (SH_HI / 8 <= bv_unsigned b / 8) by (apply Z.div_le_mono; lia); unfold SH_HI in *; lia).
    assert (Hy2 : y <= SH_OFF + (0x800000000000 - 1) / 8) by (unfold y; assert (bv_unsigned b / 8 <= (0x800000000000 - 1) / 8) by (apply Z.div_le_mono; lia); lia).
    assert (Hy3 : bv_unsigned b / 8 <= (bv_unsigned b + 63) / 8) by (apply Z.div_le_mono; lia).
    unfold HSHB, SH_HI, SH_OFF in *. lia.
  - rewrite qw2_u. set (y := SH_OFF + (bv_unsigned b + n - 1) / 8).
    pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)).
    assert (Hy1 : HSHB <= y) by (unfold y, HSHB, SH_OFF; assert (SH_HI / 8 <= (bv_unsigned b + n - 1) / 8) by (apply Z.div_le_mono; lia); unfold SH_HI in *; lia).
    assert (Hy2 : y <= SH_OFF + (0x800000000000 - 1) / 8) by (unfold y; assert ((bv_unsigned b + n - 1) / 8 <= (0x800000000000 - 1) / 8) by (apply Z.div_le_mono; lia); lia).
    assert (Hy3 : bv_unsigned b / 8 <= (bv_unsigned b + n - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (Hy4 : (bv_unsigned b + n - 1) / 8 <= (bv_unsigned b + 63) / 8) by (apply Z.div_le_mono; lia).
    unfold HSHB, SH_HI, SH_OFF in *. lia.
Qed.
End Words.

(* [comment removed for export] *)
Lemma rdn_zeros8 : forall segs m (w : word), bv_unsigned w + 8 < two64 ->
  (forall i, 0 <= i < 8 -> rd1 segs m (Z_to_bv 64 (bv_unsigned w + i)) = Some (Z_to_bv 8 0)) -> rdn segs m w 8 = Some zeros8.
Proof.
  intros segs m w Hw H.
  assert (Hs : forall k a, (k <= 8)%nat -> bv_unsigned a + Z.of_nat k < two64 ->
            (forall i, 0 <= i < Z.of_nat k -> rd1 segs m (Z_to_bv 64 (bv_unsigned a + i)) = Some (Z_to_bv 8 0)) ->
            rdn segs m a k = Some (List.repeat (Z_to_bv 8 0) k)).
  { induction k as [|k IH]; intros a Hk Ha Hall; [reflexivity|]. cbn [rdn List.repeat].
    assert (H0 : rd1 segs m a = Some (Z_to_bv 8 0)) by (rewrite <- (Hall 0 ltac:(lia)); rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    unfold rd1 in H0. rewrite H0. rewrite (IH (a + 1)%bv ltac:(lia)); [reflexivity| |].
    - rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1. unfold bv_wrap. change (bv_modulus 64) with two64.
      rewrite Z.mod_small by (pose proof (bv_unsigned_in_range _ a); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with two64 in *; lia). lia.
    - intros i Hi. rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1. unfold bv_wrap. change (bv_modulus 64) with two64.
      rewrite Z.mod_small by (pose proof (bv_unsigned_in_range _ a); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with two64 in *; lia).
      replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (i + 1)) by lia. apply Hall. lia. }
  exact (Hs 8%nat w ltac:(lia) ltac:(lia) H).
Qed.

(* [comment removed for export] *)
Lemma ld8_val : forall bs v, length bs = 8%nat -> ld_word SZ8 false bs = v -> bytes_le_to_Z bs = bv_unsigned v.
Proof.
  intros bs v Hl <-. unfold ld_word, le_bytes_to_word. cbn. rewrite bv_extract_unsigned.
  pose proof (bytes_le_to_Z_bound bs) as Bb. pose proof (bytes_le_to_Z_nonneg bs) as B0. rewrite Hl in Bb.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite (Z.mod_small (bytes_le_to_Z bs)) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Bb; lia).
  rewrite Z.shiftr_0_r. symmetry. apply Z.mod_small. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Bb. lia.
Qed.

Lemma page_allowedb_in : forall A a pg, In a A -> page_allowedb [a] pg = true -> page_allowedb A pg = true.
Proof.
  intros A a pg Ha H. unfold page_allowedb in *. cbn [existsb] in H. rewrite orb_false_r in H.
  apply existsb_exists. exists a. split; assumption.
Qed.

Lemma lsub_const_add : forall E a b n, lden E (lsub a b) = Z_to_bv 64 n -> lden E a = v_add (lden E b) (Z_to_bv 64 n).
Proof.
  intros E a b n H. rewrite lden_lsub in H. apply (f_equal bv_unsigned) in H. rewrite bv_sub_unsigned, Z_to_bv_unsigned in H.
  unfold bv_wrap in H. apply bv_eq. unfold v_add. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite <- H. rewrite Zplus_mod_idemp_r.
  replace (bv_unsigned (lden E b) + (bv_unsigned (lden E a) - bv_unsigned (lden E b))) with (bv_unsigned (lden E a)) by ring.
  symmetry. apply Z.mod_small. exact (bv_unsigned_in_range _ (lden E a)).
Qed.

(* [comment removed for export] *)
Section Node.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma qc_rgz_zero : forall E (mm : word -> option byte) (R : region) x,
  rg_kind R = RZ -> range_zero (rg_cont R) 0 two64 = true ->
  0 <= rsz E R -> bv_unsigned (lden E (rg_base R)) + rsz E R <= two64 ->
  (forall i, 0 <= i < rsz E R ->
     match rg_kind R with
     | RW => rd1 segs mm (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None /\ wview segs mm (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None
     | RO => mm (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) = None /\ seg_rom segs (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None
     | RZ => (rd1 segs mm (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None /\ wview segs mm (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None) /\
             (tget (okey i) (rg_cont R) = None -> rd1 segs mm (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) = Some (Z_to_bv 8 0))
     | RI => (rd1 segs mm (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None /\ wview segs mm (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None) /\
             (tget (okey i) (rg_cont R) = None -> rd1 segs mm (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) = seg_rom segs (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)))
     | RT => rd1 segs mm (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None
     end) ->
  (forall p v, tget p (rg_cont R) = Some v -> Zpos p - 1 < rsz E R /\ rd1 segs mm (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + (Zpos p - 1))) = Some (bden E v)) ->
  uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R ->
  rd1 segs mm (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E mm R x HkR Hz Hrs0 Hrw Hpts Hcont Hx. unfold uE in Hx. set (A := bv_unsigned (lden E (rg_base R))) in *.
  specialize (Hpts (x - A) ltac:(lia)). rewrite HkR in Hpts. destruct Hpts as (_ & Hzz).
  replace (A + (x - A)) with x in Hzz by lia.
  destruct (tget (okey (x - A)) (rg_cont R)) as [v|] eqn:Ht; [|exact (Hzz eq_refl)].
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as RA. fold A in RA.
  assert (Hv : v = BK 0) by (apply (range_zero_spec _ 0 two64 _ v Hz Ht); rewrite okey_pos by lia; unfold two64 in *; lia).
  destruct (Hcont _ _ Ht) as (_ & Hrd). rewrite okey_pos in Hrd by lia. replace (A + (x - A)) with x in Hrd by lia.
  rewrite Hrd, Hv. reflexivity.
Qed.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Himg : img_ok segs img.

#[using="Hwx Himg"] Theorem den_qc : forall q S M E ms model T,
  qsite_ok segs q -> qc_chk img q S M = true -> DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' (qc_post q S) M ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Himg : LiaFast.U) => LiaFast.u0).
  intros q S M E ms model T Hq Hck Hd Hk.
  destruct q as [pc0 rP rA rB rY rZ rW ord bim beq].
  pose proof Hq as Hq0. cbn [qsite_ok] in Hq0.
  destruct Hq0 as (Hnz & Hd1 & Hd2 & I0 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11).
  unfold qc_chk in Hck. cbn [qs_rB qs_rA qs_rP qs_pc0] in Hck.
  set (fs := s_facts S) in *. set (b := rget (s_regs S) (rkey rB)) in *.
  destruct (s_resv S) eqn:Hrv; try discriminate.
  destruct (is_const (rget (s_regs S) (rkey rP))) as [P|] eqn:HP; [|discriminate].
  destruct (irange fs (lsub (rget (s_regs S) (rkey rA)) b)) as [nlo nhi] eqn:Hnr.
  destruct (irange fs b) as [blo bhi] eqn:Hbr. destruct (irange fs (lsub b (sm_sp M))) as [dlo dhi] eqn:Hdr.
  destruct (load_at img fs (s_rgs S) (lconst P) SZ8 false) as [[sl|]|] eqn:HlP;
    [|rewrite ?andb_false_r, ?andb_false_l in Hck; discriminate | rewrite ?andb_false_r, ?andb_false_l in Hck; discriminate].
  match type of Hck with ((if ?c then ?x else false) = true) =>
    assert (Hck2 : (c && x)%bool = true) by (destruct c; [exact Hck | discriminate Hck]) end.
  clear Hck. apply andb_prop in Hck2 as [Hck Hxx]. apply andb_prop in Hxx as [Hxx Hsep]. apply andb_prop in Hxx as [Hal Hoq].
  rewrite qc_allow_scan_eq in Hal.
  repeat match type of Hck with ((_ && _)%bool = true) => apply andb_prop in Hck as [Hck ?Hc] end.
  rename Hck into Hpc0.
  repeat match goal with
         | Hx : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx
         | Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx
         | Hx : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx
         end.
  subst sl.
  match goal with Hx : existsb hshb_g (sm_maps M) = true |- _ => rename Hx into Hhs end.
  match goal with Hx : existsb (fun z => (Z.eqb (fst z) HSHB && _)%bool) (sm_zr M) = true |- _ => rename Hx into Hzre end.
  match goal with Hx : lwf (s_next S) b = true |- _ => rename Hx into Hwb end.
  (* [comment removed for export] *)
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  set (bw := lden E b).
  assert (HB : getr (ms_regs ms) rB = bw) by exact (HR rB).
  set (n := bv_unsigned (lden E (lsub (rget (s_regs S) (rkey rA)) b))).
  assert (HnE : lden E (lsub (rget (s_regs S) (rkey rA)) b) = Z_to_bv 64 n) by (unfold n; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Hn64 : 0 <= n < two64) by (unfold n; apply uE_range).
  pose proof (irange_sound E fs (lsub (rget (s_regs S) (rkey rA)) b) HF) as Rn. rewrite Hnr in Rn. cbn [fst snd] in Rn. fold n in Rn.
  assert (HA : getr (ms_regs ms) rA = v_add bw (Z_to_bv 64 n)) by (rewrite (HR rA); exact (lsub_const_add E _ b n HnE)).
  assert (HPr : getr (ms_regs ms) rP = Z_to_bv 64 P) by (rewrite (HR rP); exact (proj1 (is_const_sound E _ P HP))).
  pose proof (irange_sound E fs b HF) as Rb. rewrite Hbr in Rb. cbn [fst snd] in Rb. fold bw in Rb.
  pose proof (irange_sound E fs (lsub b (sm_sp M)) HF) as Rd. rewrite Hdr in Rd. cbn [fst snd] in Rd. fold (uE E (lsub b (sm_sp M))) in Rd.
  (* [comment removed for export] *)
  assert (Hb2 : bv_unsigned bw + n <= 0x800000000000).
  { pose proof (irange_sound E fs (rget (s_regs S) (rkey rA)) HF) as RA.
    assert (HvA : bv_unsigned (lden E (rget (s_regs S) (rkey rA))) = bv_unsigned bw + n).
    { rewrite <- (HR rA), HA. unfold v_add. rewrite u_small; [rewrite (u_small n) by (unfold two64 in *; lia); reflexivity|].
      rewrite (u_small n) by (unfold two64 in *; lia). pose proof (bv_unsigned_in_range _ bw) as Rbw. unfold bv_modulus in Rbw.
      change (2 ^ Z.of_N 64) with two64 in Rbw. unfold two64 in *. lia. }
    rewrite HvA in RA. lia. }
  match goal with Hx : ((Z.leb 0 dlo && Z.leb dhi (2 ^ 22)) || (Z.leb (two64 - 2 ^ 20) dlo && Z.ltb dhi two64))%bool = true |- _ => rename Hx into Hdw end.
  assert (Hbsp : bv_unsigned (vm_init_sp (m_vmmaps model)) - 2 ^ 20 <= bv_unsigned bw /\ bv_unsigned bw <= bv_unsigned (vm_init_sp (m_vmmaps model)) + 2 ^ 22).
  { rewrite Hsp. fold (uE E (sm_sp M)). change (bv_unsigned bw) with (uE E b) in Hb2 |- *.
    pose proof (uE_range E b). pose proof (uE_range E (sm_sp M)). destruct Hspok as [_ Hsh]. rewrite Hsp in Hsh. unfold sp_window_hi in Hsh.
    fold (uE E (sm_sp M)) in Hsh.
    apply orb_prop in Hdw as [Hdw|Hdw]; apply andb_prop in Hdw as [D1 D2]; [apply Z.leb_le in D1, D2 | apply Z.leb_le in D1; apply Z.ltb_lt in D2];
      destruct (small_diff E b (sm_sp M) dlo dhi Rd) as [[Hl He]|[Hl He]]; unfold two64 in *; lia. }
  (* [comment removed for export] *)
  destruct (load_at_sound segs E img fs (s_rgs S) _ SZ8 false _ (ms_mem (restrict H ms)) Himg HG HF HlP) as (bsP & HrP & HvP).
  specialize (HvP _ eq_refl). rewrite ov_rdn in HrP. cbn [nbytes] in HrP.
  assert (HlbP : length bsP = 8%nat) by exact (rdn_length _ _ _ _ _ HrP).
  set (Pw := Z_to_bv 64 P).
  set (sh := Z_to_bv 64 SH_OFF).
  assert (HPv : bytes_le_to_Z bsP = bv_unsigned sh) by (apply ld8_val; [exact HlbP | rewrite <- HvP, lden_lconst; reflexivity]).
  rewrite lden_lconst in HrP. fold Pw in HrP.
  (* [comment removed for export] *)
  assert (Hb1 : SH_HI <= bv_unsigned bw) by (unfold SH_HI in *; lia).
  assert (Hn1 : 1 <= n <= 64) by lia.
  pose proof (alloc_top_lo _ (proj1 Hspok)) as Hatl.
  assert (Hat : alloc_top (m_vmmaps model) = bv_unsigned (vm_init_sp (m_vmmaps model)) - 8388608) by reflexivity.
  destruct (proj1 (existsb_exists _ _) Hhs) as (k & Hkin & Hkc). destruct (hshb_g_sound E k Hkc) as [Hkb Hks].
  assert (Hzero : forall w, (w = qw1 sh bw \/ w = qw2 sh bw n) -> forall i, 0 <= i < 8 ->
            rd1 segs (mrestrict H (ms_mem ms)) (Z_to_bv 64 (bv_unsigned w + i)) = Some (Z_to_bv 8 0)).
  { intros w Hw i Hi. destruct (qw_geo bw n Hb1 Hb2 Hn1 w Hw) as (G1 & G2 & G3 & G4).
    set (x := bv_unsigned w + i).
    assert (Hx64 : bv_unsigned (Z_to_bv 64 x) = x) by (apply u_small; unfold x, HSHB, SH_HI, two64 in *; lia).
    (* [comment removed for export] *)
    assert (Hvis : H (Z_to_bv 64 x) = false).
    { apply existsb_exists in Hal as (p & Hp & Hpa). unfold qc_allow in Hpa.
      destruct (irange fs (lsub (laddc (sm_sp M) (8 * SH_OFF)) (lscale 8 (fst p)))) as [d1 d2] eqn:Hdd.
      repeat match type of Hpa with ((_ && _)%bool = true) => apply andb_prop in Hpa as [Hpa ?Hq] end.
      repeat match goal with
             | Hx' : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx'
             | Hx' : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx'
             end.
      pose proof (irange_sound E fs (lsub (laddc (sm_sp M) (8 * SH_OFF)) (lscale 8 (fst p))) HF) as Rdd. rewrite Hdd in Rdd. cbn [fst snd] in Rdd.
      fold (uE E (lsub (laddc (sm_sp M) (8 * SH_OFF)) (lscale 8 (fst p)))) in Rdd.
      pose proof (irange_sound E fs (fst p) HF) as Rl. fold (uE E (fst p)) in Rl.
      destruct Hspok as [_ Hsh]. unfold sp_window_hi in Hsh. rewrite Hsp in Hsh, Hbsp. fold (uE E (sm_sp M)) in Hsh, Hbsp.
      assert (Hsl : uE E (lscale 8 (fst p)) = 8 * uE E (fst p)).
      { unfold uE at 1. rewrite lden_lscale. fold (uE E (fst p)). apply u_small. pose proof (uE_range E (fst p)). unfold two64 in *. lia. }
      assert (Hsa : uE E (laddc (sm_sp M) (8 * SH_OFF)) = uE E (sm_sp M) + 8 * SH_OFF) by (apply u_laddc_small; unfold SH_OFF, two64 in *; lia).
      destruct (small_diff E (laddc (sm_sp M) (8 * SH_OFF)) (lscale 8 (fst p)) d1 d2 Rdd) as [[Hl He]|[Hl He]];
        rewrite Hsl, Hsa in He, Hl; [|rewrite Hat, Hsp in Hatl; fold (uE E (sm_sp M)) in Hatl; unfold two64, SH_OFF in *; lia].
      unfold H, Hof. apply mkH_allowed. unfold allowA. apply (page_allowedb_in _ (allow1 E p)); [apply in_map; exact Hp|].
      apply allow1_covers; [unfold x, HSHB, SH_HI, two64 in *; lia|].
      change (bv_unsigned bw) with (uE E b) in *.
      pose proof (Z.div_mod (uE E (sm_sp M)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (uE E (sm_sp M)) 8 ltac:(lia)).
      pose proof (Z.div_mod (uE E b) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (uE E b) 8 ltac:(lia)).
      pose proof (Z.div_mod (uE E b + 63) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (uE E b + 63) 8 ltac:(lia)).
      pose proof (Z.div_mod d2 8 ltac:(lia)). pose proof (Z.mod_pos_bound d2 8 ltac:(lia)).
      unfold x, SH_OFF in *. lia. }
    destruct (existsb (fun R => (qc_rgz R && (Z.leb (uE E (rg_base R)) x && Z.ltb x (uE E (rg_base R) + rsz E R)))%bool) (s_rgs S)) eqn:Hez.
    { (* [comment removed for export] *)
      apply existsb_exists in Hez as (R & HRin & HRc). apply andb_prop in HRc as [Hz HRc]. apply andb_prop in HRc as [C1 C2].
      apply Z.leb_le in C1. apply Z.ltb_lt in C2.
      unfold qc_rgz in Hz. destruct (rg_kind R) eqn:HkR; try discriminate.
      rewrite Forall_forall in HG. destruct (HG R HRin) as (Hrs0 & Hrw & Hpts & Hcont).
      exact (qc_rgz_zero E _ R x HkR Hz Hrs0 Hrw Hpts Hcont ltac:(lia)). }
    assert (Hxat : SH_OFF + alloc_top (m_vmmaps model) / 8 + 8 <= x).
    { change (bv_unsigned bw) with (uE E b) in *; pose proof (Z.div_mod (uE E b) 8 ltac:(lia));
      pose proof (Z.mod_pos_bound (uE E b) 8 ltac:(lia));
      pose proof (Z.div_mod (alloc_top (m_vmmaps model)) 8 ltac:(lia));
      pose proof (Z.mod_pos_bound (alloc_top (m_vmmaps model)) 8 ltac:(lia)); unfold x in *; lia. }
    (* [comment removed for export] *)
    assert (Hout : outside E (s_rgs S) (Z_to_bv 64 x)).
    { unfold outside. rewrite Forall_forall. intros R HRin. rewrite Hx64.
      rewrite forallb_forall in Hsep. pose proof (Hsep R HRin) as HqR0. unfold qc_rg in HqR0.
      rewrite Forall_forall in HG. destruct (HG R HRin) as (Hrs0 & Hrw & _).
      destruct (qc_rg4 fs (sm_maps M) R) eqn:HqR.
      2:{ rewrite ?HqR in HqR0. assert (HqR0' : qc_rgz R = true) by (destruct (qc_rgz R); [reflexivity | discriminate HqR0]).
          clear HqR0. rename HqR0' into HqR0. destruct (Z_lt_le_dec x (uE E (rg_base R))) as [Hl|Hl]; [left; unfold uE in Hl; exact Hl|].
          destruct (Z_lt_le_dec x (uE E (rg_base R) + rsz E R)) as [Hl2|Hl2]; [|right; unfold uE in Hl2; exact Hl2].
          exfalso. assert (Hc : (qc_rgz R && (Z.leb (uE E (rg_base R)) x && Z.ltb x (uE E (rg_base R) + rsz E R)))%bool = true).
          { rewrite HqR0. cbn [andb]. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
          rewrite (proj2 (existsb_exists _ _) (ex_intro _ R (conj HRin Hc))) in Hez. discriminate. }
      assert (Hnot := qc_rg_sound E fs (sm_maps M) model _ HF Hmaps Hpd Hgsh Hgtop R k x HqR Hrs0 ltac:(unfold uE; lia) Hkin Hkb Hks
                        ltac:(unfold x, HSHB, SH_HI in *; lia) Hxat).
      unfold uE in Hnot. lia. }
    (* [comment removed for export] *)
    assert (Hinzr : in_zr (sm_zr M) x = true).
    { apply existsb_exists in Hzre as (z & Hz & Hzc). apply andb_prop in Hzc as [Hz1 Hz2]. apply Z.eqb_eq in Hz1, Hz2.
      unfold in_zr. apply existsb_exists. exists z. split; [exact Hz|]. rewrite Hz1, Hz2.
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; unfold x, HSHB, SH_HI in *; lia. }
    assert (Hno : ~ own_pt E M x).
    { intros (p & Hp & Hpx). rewrite forallb_forall in Hoq. pose proof (Hoq p Hp) as Hqo. rewrite qc_ownx_eq in Hqo. unfold qc_ownx_ref in Hqo.
      destruct (qc_own2 fs (sm_maps M) p) eqn:Hq2.
      - exact (qc_own2_sound E fs (sm_maps M) model _ HF Hmaps Hpd Hgsh p k x Hq2 Hkin Hkb Hks ltac:(unfold x, HSHB, SH_HI in *; lia) Hpx).
      - apply (qc_own3_sound E fs HF (sm_sp M) p x Hqo); [| |exact Hpx].
        + destruct Hspok as [_ Hsh]. unfold sp_window_hi in Hsh. rewrite Hsp in Hsh. fold (uE E (sm_sp M)) in Hsh. lia.
        + rewrite Hat, Hsp in Hxat. fold (uE E (sm_sp M)) in Hxat. exact Hxat. }
    unfold rd1, mrestrict. rewrite Hvis. rewrite (Hzr x Hinzr Hout Hno (fun Hb => ltac:(pose proof (blob_sh_top _ _ _ _ _ Hblob Hb); lia))). reflexivity. }
  (* [comment removed for export] *)
  pose proof (qw_geo bw n Hb1 Hb2 Hn1 (qw1 sh bw) (or_introl eq_refl)) as (W1a & W1b & _).
  pose proof (qw_geo bw n Hb1 Hb2 Hn1 (qw2 sh bw n) (or_intror eq_refl)) as (W2a & W2b & _).
  assert (HZ1 : rdn segs (mrestrict H (ms_mem ms)) (qw1 sh bw) 8 = Some zeros8)
    by (apply rdn_zeros8; [unfold SH_HI, two64 in *; lia | exact (Hzero _ (or_introl eq_refl))]).
  assert (HZ2 : rdn segs (mrestrict H (ms_mem ms)) (qw2 sh bw n) 8 = Some zeros8)
    by (apply rdn_zeros8; [unfold SH_HI, two64 in *; lia | exact (Hzero _ (or_intror eq_refl))]).
  destruct (@qc2_isteps (mkFP (ms_fregs ms) (ms_fcsr ms)) segs pc0 rP rA rB rY rZ rW ord bim beq Hnz Hd1 Hd2
              I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11
              (ms_regs ms) (mrestrict H (ms_mem ms)) (ms_rom ms) bw n Pw sh bsP HB HPr HA HrP HPv HZ1 HZ2)
    as (regs' & Hst & Rp & Ry & Ra & Rz & Rw & Rothers).
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (qpc pc0 0) (mrestrict H (ms_mem ms)) (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. rewrite Hpc0 in Hpc. cbn [qs_pc0] in Hpc. subst pcv.
    unfold restrict, mkst, qpc. cbn [ms_regs ms_fregs ms_fcsr ms_mem ms_rom fp_regs fp_csr ms_pc_val ms_svc_pending ms_resv].
    replace (pc0 + 4 * 0) with pc0 by lia. reflexivity. }
  (* [comment removed for export] *)
  set (x1 := s_next S). set (x2 := Pos.succ (s_next S)).
  set (E1 := upd (upd E x1 (qX sh bw)) x2 (qY sh bw n)).
  assert (Ha1 : agree (s_next S) E E1).
  { intros y Hy. unfold E1, upd. destruct (Pos.eqb_spec y x2); [unfold x2 in *; lia|]. destruct (Pos.eqb_spec y x1); [unfold x1 in *; lia|]. reflexivity. }
  assert (HE1a : E1 x1 = qX sh bw) by (unfold E1, upd; destruct (Pos.eqb_spec x1 x2); [unfold x1, x2 in *; lia|]; rewrite Pos.eqb_refl; reflexivity).
  assert (HE1b : E1 x2 = qY sh bw n) by (unfold E1, upd; rewrite Pos.eqb_refl; reflexivity).
  set (S1 := bump S (Pos.succ x2)).
  assert (Hnx : (s_next S <= s_next S1)%positive) by (unfold S1, bump, x2; cbn [s_next]; lia).
  assert (Hx1 : (x1 < s_next S1)%positive) by (unfold S1, bump, x1, x2; cbn [s_next]; lia).
  assert (Hx2 : (x2 < s_next S1)%positive) by (unfold S1, bump, x2; cbn [s_next]; lia).
  assert (HdS1 : DEN segs LIMIT model0 mem0 E1 S1 M ms model) by (apply den_bump; [exact (den_agree segs LIMIT model0 mem0 E E1 S M ms model Hd Ha1) | unfold x2; lia]).
  assert (HH1 : Hof E1 M model = H) by (unfold Hof, H; rewrite (allowA_agree (s_next S) E E1 M Hwf Ha1); reflexivity).
  set (qq := QS pc0 rP rA rB rY rZ rW ord bim beq).
  assert (Hpost : sden segs E1 (qc_post qq S) (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (qok2 pc0 bim beq) (mrestrict H (ms_mem ms)) (ms_rom ms))).
  { destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HdS1)) as (_ & _ & _ & _ & _ & _ & _ & _).
    pose proof (sden_regs segs E1 S1 (restrict H ms) (s_regs (qc_post qq S)) regs' (qs_ok qq) ltac:(rewrite <- HH1; exact (dn_sden _ _ _ _ _ _ _ _ _ HdS1))) as X.
    assert (Hqk : Z_to_bv 64 (qs_ok qq) = qok2 pc0 bim beq) by (unfold qs_ok; cbn [qs_pc0 qs_bim qs_beq]; apply Z_to_bv_bv_unsigned).
    rewrite Hqk in X. cbn [restrict ms_fregs ms_fcsr ms_resv ms_mem ms_rom] in X. rewrite Hrsv in X.
    unfold qc_post at 1. cbn [qs_ok]. fold qq. unfold mkst. cbn [fp_regs fp_csr]. apply X.
    intros E' Ha' HR'.
    assert (HbE' : lden E' b = bw) by (unfold bw; apply (lden_agree_wf (s_next S) E E' b Hwb); exact (agree_trans _ E E1 E' Ha1 (agree_mono _ _ E1 E' Hnx Ha'))).
    assert (HE'1 : E' x1 = qX sh bw) by (rewrite <- HE1a; symmetry; apply Ha'; exact Hx1).
    assert (HE'2 : E' x2 = qY sh bw n) by (rewrite <- HE1b; symmetry; apply Ha'; exact Hx2).
    destruct Hnz as (NP & NA & NY & NZ & NW).
    destruct Hd1 as (DAP & DYP & DYA & DZP & DZA & DZY & DWP & DWA & DWY & DWZ).
    set (r5 := regupd (regupd (regupd (regupd (regupd (ms_regs ms) rP (qX sh bw)) rY (qY sh bw n)) rA (qlast bw n)) rZ (Z_to_bv 64 0)) rW (Z_to_bv 64 0)).
    assert (HR5 : regs_ok E' (s_regs (qc_post qq S)) r5).
    { unfold qc_post, qq. cbn [s_regs qs_rB qs_rP qs_rY qs_rA qs_rZ qs_rW]. fold b.
      unfold r5.
      assert (R0 : forall E0 R regs (rd : reg) l v, rd <> 0%bv -> regs_ok E0 R regs -> lden E0 l = v ->
                     regs_ok E0 (rset R (rkey rd) l) (regupd regs rd v)).
      { intros E0 R regs rd l v Hne HR0 Hv. pose proof (regs_ok_upd E0 R regs rd l v HR0 Hv) as X0.
        rewrite (PropExec.bv_eqb_neq rd 0%bv Hne) in X0. exact X0. }
      apply R0; [exact NW| |]; [apply R0; [exact NZ| |]; [apply R0; [exact NA| |]; [apply R0; [exact NY| |]; [apply R0; [exact NP| |]|]|]|]|].
      - exact HR'.
      - rewrite lden_lvar. exact HE'1.
      - rewrite lden_lvar. exact HE'2.
      - assert (HRA : lden E' (rget (s_regs S) (rkey rA)) = v_add bw (Z_to_bv 64 n)) by (rewrite <- HA; symmetry; exact (HR' rA)).
        rewrite lden_laddc, HRA. unfold qlast, v_addi. reflexivity.
      - rewrite lden_lconst. reflexivity.
      - rewrite lden_lconst. reflexivity. }
    intros r. rewrite <- (HR5 r). unfold r5.
    destruct (decide (r = rW)) as [->|NrW]; [rewrite getr_same by exact NW; exact Rw|]. rewrite getr_other by exact NrW.
    destruct (decide (r = rZ)) as [->|NrZ]; [rewrite getr_same by exact NZ; exact Rz|]. rewrite getr_other by exact NrZ.
    destruct (decide (r = rA)) as [->|NrA]; [rewrite getr_same by exact NA; exact Ra|]. rewrite getr_other by exact NrA.
    destruct (decide (r = rY)) as [->|NrY]; [rewrite getr_same by exact NY; exact Ry|]. rewrite getr_other by exact NrY.
    destruct (decide (r = rP)) as [->|NrP]; [rewrite getr_same by exact NP; exact Rp|]. rewrite getr_other by exact NrP.
    exact (Rothers r NrP NrA NrY NrZ NrW). }
  apply (den_isteps segs cfg LIMIT model0 mem0 Hwx E1 S1 M ms model T (qc_post qq S)
           (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (qok2 pc0 bim beq) (mrestrict H (ms_mem ms)) (ms_rom ms)) E1 HdS1).
  - rewrite HH1, Hmsr. exact Hst.
  - exact Hpost.
  - apply agree_refl.
  - unfold qc_post, S1, bump, x2. cbn [s_next]. apply Pos.le_refl.
  - intros y _. rewrite HH1. reflexivity.
  - reflexivity.
  - intros E2 ms2 model2 HD2 Ha2. apply (Hk E2 ms2 model2); [|exact HD2].
    exact (agree_trans _ E E1 E2 Ha1 (agree_mono _ _ E1 E2 Hnx Ha2)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_shzero : forall S M E ms model x,
  DEN segs LIMIT model0 mem0 E S M ms model ->
  existsb (fun z => (Z.eqb (fst z) HSHB && Z.eqb (snd z) SH_HI)%bool) (sm_zr M) = true ->
  existsb hshb_g (sm_maps M) = true ->
  existsb (qc_allow (s_facts S) (sm_sp M)) (sm_allow M) = true ->
  forallb (qc_own2 (s_facts S) (sm_maps M)) (sm_own M) = true ->
  forallb (qc_rg (s_facts S) (sm_maps M)) (s_rgs S) = true ->
  SH_OFF + (uE E (sm_sp M) - 2 ^ 20) / 8 - 8 <= x -> x <= SH_OFF + (uE E (sm_sp M) + 2 ^ 22 + 128) / 8 -> x < SH_HI ->
  rd1 segs (mrestrict (Hof E M model) (ms_mem ms)) (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M E ms model x Hd Hzre Hhs Hal Hoq Hsep HX1 HX2 HX3.
  set (fs := s_facts S) in *.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  pose proof (alloc_top_lo _ (proj1 Hspok)) as Hatl.
  assert (Hat : alloc_top (m_vmmaps model) = bv_unsigned (vm_init_sp (m_vmmaps model)) - 8388608) by reflexivity.
  pose proof (uE_range E (sm_sp M)) as Rsp.
  destruct Hspok as [Hspo Hsh]. unfold sp_window_hi in Hsh. rewrite Hsp in Hsh, Hat. fold (uE E (sm_sp M)) in Hsh, Hat.
  rewrite Hat in Hatl.
  destruct (proj1 (existsb_exists _ _) Hhs) as (k & Hkin & Hkc). destruct (hshb_g_sound E k Hkc) as [Hkb Hks].
  pose proof (Z.div_mod (uE E (sm_sp M)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (uE E (sm_sp M)) 8 ltac:(lia)).
  assert (HxB : HSHB <= x < SH_HI).
  { assert (A1 : (uE E (sm_sp M) - 2 ^ 20) / 8 = uE E (sm_sp M) / 8 - 2 ^ 17).
    { replace (uE E (sm_sp M) - 2 ^ 20) with (uE E (sm_sp M) + (- 2 ^ 17) * 8) by lia. rewrite Z.div_add by lia. lia. }
    assert (A2 : (uE E (sm_sp M) + 2 ^ 22 + 128) / 8 = uE E (sm_sp M) / 8 + 2 ^ 19 + 16).
    { replace (uE E (sm_sp M) + 2 ^ 22 + 128) with (uE E (sm_sp M) + (2 ^ 19 + 16) * 8) by lia. rewrite Z.div_add by lia. lia. }
    rewrite A1 in HX1. rewrite A2 in HX2. unfold HSHB, SH_HI, SH_OFF in *. lia. }
  assert (Hx64 : bv_unsigned (Z_to_bv 64 x) = x) by (apply u_small; unfold HSHB, SH_HI, two64 in *; lia).
  (* [comment removed for export] *)
  assert (Hvis : H (Z_to_bv 64 x) = false).
  { apply existsb_exists in Hal as (p & Hp & Hpa). unfold qc_allow in Hpa.
    destruct (irange fs (lsub (laddc (sm_sp M) (8 * SH_OFF)) (lscale 8 (fst p)))) as [d1 d2] eqn:Hdd.
    repeat match type of Hpa with ((_ && _)%bool = true) => apply andb_prop in Hpa as [Hpa ?Hq] end.
    repeat match goal with
           | Hx' : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx'
           | Hx' : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx'
           end.
    pose proof (irange_sound E fs (lsub (laddc (sm_sp M) (8 * SH_OFF)) (lscale 8 (fst p))) HF) as Rdd. rewrite Hdd in Rdd. cbn [fst snd] in Rdd.
    fold (uE E (lsub (laddc (sm_sp M) (8 * SH_OFF)) (lscale 8 (fst p)))) in Rdd.
    pose proof (irange_sound E fs (fst p) HF) as Rl. fold (uE E (fst p)) in Rl.
    assert (Hsl : uE E (lscale 8 (fst p)) = 8 * uE E (fst p)).
    { unfold uE at 1. rewrite lden_lscale. fold (uE E (fst p)). apply u_small. pose proof (uE_range E (fst p)). unfold two64 in *. lia. }
    assert (Hsa : uE E (laddc (sm_sp M) (8 * SH_OFF)) = uE E (sm_sp M) + 8 * SH_OFF) by (apply u_laddc_small; unfold SH_OFF, two64 in *; lia).
    destruct (small_diff E (laddc (sm_sp M) (8 * SH_OFF)) (lscale 8 (fst p)) d1 d2 Rdd) as [[Hl He]|[Hl He]];
      rewrite Hsl, Hsa in He, Hl; [|unfold two64, SH_OFF in *; lia].
    unfold H, Hof. apply mkH_allowed. unfold allowA. apply (page_allowedb_in _ (allow1 E p)); [apply in_map; exact Hp|].
    apply allow1_covers; [unfold HSHB, SH_HI, two64 in *; lia|].
    pose proof (Z.div_mod d2 8 ltac:(lia)). pose proof (Z.mod_pos_bound d2 8 ltac:(lia)).
    assert (A1 : (uE E (sm_sp M) - 2 ^ 20) / 8 = uE E (sm_sp M) / 8 - 2 ^ 17).
    { replace (uE E (sm_sp M) - 2 ^ 20) with (uE E (sm_sp M) + (- 2 ^ 17) * 8) by lia. rewrite Z.div_add by lia. lia. }
    assert (A2 : (uE E (sm_sp M) + 2 ^ 22 + 128) / 8 = uE E (sm_sp M) / 8 + 2 ^ 19 + 16).
    { replace (uE E (sm_sp M) + 2 ^ 22 + 128) with (uE E (sm_sp M) + (2 ^ 19 + 16) * 8) by lia. rewrite Z.div_add by lia. lia. }
    rewrite A1 in HX1. rewrite A2 in HX2. unfold SH_OFF in *. lia. }
  destruct (existsb (fun R => (qc_rgz R && (Z.leb (uE E (rg_base R)) x && Z.ltb x (uE E (rg_base R) + rsz E R)))%bool) (s_rgs S)) eqn:Hez.
  { apply existsb_exists in Hez as (R & HRin & HRc). apply andb_prop in HRc as [Hz HRc]. apply andb_prop in HRc as [C1 C2].
    apply Z.leb_le in C1. apply Z.ltb_lt in C2.
    unfold qc_rgz in Hz. destruct (rg_kind R) eqn:HkR; try discriminate.
    rewrite Forall_forall in HG. destruct (HG R HRin) as (Hrs0 & Hrw & Hpts & Hcont).
    exact (qc_rgz_zero E _ R x HkR Hz Hrs0 Hrw Hpts Hcont ltac:(lia)). }
  assert (Hxat : SH_OFF + alloc_top (m_vmmaps model) / 8 + 8 <= x).
  { rewrite Hat; pose proof (Z.div_mod (uE E (sm_sp M) - 8388608) 8 ltac:(lia));
    pose proof (Z.mod_pos_bound (uE E (sm_sp M) - 8388608) 8 ltac:(lia));
    assert (A1 : (uE E (sm_sp M) - 2 ^ 20) / 8 = uE E (sm_sp M) / 8 - 2 ^ 17)
      by (replace (uE E (sm_sp M) - 2 ^ 20) with (uE E (sm_sp M) + (- 2 ^ 17) * 8) by lia; rewrite Z.div_add by lia; lia);
    rewrite A1 in HX1; lia. }
  assert (Hout : outside E (s_rgs S) (Z_to_bv 64 x)).
  { unfold outside. rewrite Forall_forall. intros R HRin. rewrite Hx64.
    rewrite forallb_forall in Hsep. pose proof (Hsep R HRin) as HqR0. unfold qc_rg in HqR0.
    rewrite Forall_forall in HG. destruct (HG R HRin) as (Hrs0 & Hrw & _).
    destruct (qc_rg4 fs (sm_maps M) R) eqn:HqR.
    2:{ rewrite ?HqR in HqR0. assert (HqR0' : qc_rgz R = true) by (destruct (qc_rgz R); [reflexivity | discriminate HqR0]).
        clear HqR0. rename HqR0' into HqR0. destruct (Z_lt_le_dec x (uE E (rg_base R))) as [Hl|Hl]; [left; unfold uE in Hl; exact Hl|].
        destruct (Z_lt_le_dec x (uE E (rg_base R) + rsz E R)) as [Hl2|Hl2]; [|right; unfold uE in Hl2; exact Hl2].
        exfalso. assert (Hc : (qc_rgz R && (Z.leb (uE E (rg_base R)) x && Z.ltb x (uE E (rg_base R) + rsz E R)))%bool = true).
        { rewrite HqR0. cbn [andb]. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
        rewrite (proj2 (existsb_exists _ _) (ex_intro _ R (conj HRin Hc))) in Hez. discriminate. }
    assert (Hnot := qc_rg_sound E fs (sm_maps M) model _ HF Hmaps Hpd Hgsh Hgtop R k x HqR Hrs0 ltac:(unfold uE; lia) Hkin Hkb Hks
                      HxB Hxat).
    unfold uE in Hnot. lia. }
  assert (Hinzr : in_zr (sm_zr M) x = true).
  { apply existsb_exists in Hzre as (z & Hz & Hzc). apply andb_prop in Hzc as [Hz1 Hz2]. apply Z.eqb_eq in Hz1, Hz2.
    unfold in_zr. apply existsb_exists. exists z. split; [exact Hz|]. rewrite Hz1, Hz2.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Hno : ~ own_pt E M x).
  { intros (p & Hp & Hpx). rewrite forallb_forall in Hoq. pose proof (Hoq p Hp) as Hqo.
    exact (qc_own2_sound E fs (sm_maps M) model _ HF Hmaps Hpd Hgsh p k x Hqo Hkin Hkb Hks HxB Hpx). }
  unfold rd1, mrestrict. rewrite Hvis. rewrite (Hzr x Hinzr Hout Hno (fun Hb => ltac:(pose proof (blob_sh_top _ _ _ _ _ Hblob Hb); lia))). reflexivity.
Qed.
End Node.
(* [comment removed for export] *)
