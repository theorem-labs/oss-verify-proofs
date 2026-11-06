(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRn FxLazy.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ditem : Type := (int * int * int * rkind)%type.

Definition redress (rg : region) (clo chi : int) (k : rkind) : region :=
  RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg) (rg_pages rg) clo chi k.

Definition dress_mem (M : itrie region) (x : ditem) : itrie region :=
  let '(t, clo, chi, k) := x in
  match iget t M with
  | Some rg => iset t (redress rg clo chi k) M
  | None => M
  end.

Definition dress (F : fstate) (bs : list ditem) : fstate :=
  FS (f_pc F) (f_regs F) (fold_left dress_mem bs (f_mem F)) (f_resv F).

(* [comment removed for export] *)
Definition same_pg (M M' : itrie region) : Prop :=
  forall t, match iget t M, iget t M' with
            | Some rg, Some rg' =>
                rg_lo rg' = rg_lo rg /\ rg_len rg' = rg_len rg /\ rg_dflt rg' = rg_dflt rg
                /\ rg_pages rg' = rg_pages rg
            | None, None => True
            | _, _ => False
            end.

Lemma same_pg_refl M : same_pg M M.
Proof. intros t. destruct (iget t M); [repeat split; reflexivity | exact I]. Qed.

Lemma same_pg_trans M1 M2 M3 : same_pg M1 M2 -> same_pg M2 M3 -> same_pg M1 M3.
Proof.
  intros H12 H23 t. specialize (H12 t). specialize (H23 t).
  destruct (iget t M1), (iget t M2), (iget t M3); try contradiction; try exact I.
  destruct H12 as (A1 & A2 & A3 & A4), H23 as (B1 & B2 & B3 & B4). repeat split; congruence.
Qed.

Lemma same_pg_sym M1 M2 : same_pg M1 M2 -> same_pg M2 M1.
Proof.
  intros H t. specialize (H t). destruct (iget t M1), (iget t M2); try contradiction; try exact I.
  destruct H as (A1 & A2 & A3 & A4). repeat split; congruence.
Qed.

Lemma dress_mem_same M x : same_pg M (dress_mem M x).
Proof.
  destruct x as [[[t clo] chi] k]. unfold dress_mem. destruct (iget t M) as [rg|] eqn:Hg; [|apply same_pg_refl].
  intros t'. rewrite iget_iset. destruct (t' =? t)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. subst t'. rewrite Hg. cbn. repeat split; reflexivity.
  - destruct (iget t' M); [repeat split; reflexivity | exact I].
Qed.

Lemma dress_same : forall bs M, same_pg M (fold_left dress_mem bs M).
Proof.
  induction bs as [|x bs IH]; intros M; cbn [fold_left]; [apply same_pg_refl|].
  eapply same_pg_trans; [apply dress_mem_same | apply IH].
Qed.

Section Claims.
Variable IM : fimage.
Variable rho : int -> word.

Lemma page_at_same rg rg' t pn :
  rg_lo rg' = rg_lo rg -> rg_len rg' = rg_len rg -> rg_dflt rg' = rg_dflt rg -> rg_pages rg' = rg_pages rg ->
  page_at IM rg' t pn = page_at IM rg t pn.
Proof.
  intros E1 E2 E3 E4. unfold page_at, page_in_region. rewrite E1, E2, E3, E4. reflexivity.
Qed.

Lemma same_pg_get M M' t rg' : same_pg M M' -> iget t M' = Some rg' ->
  exists rg, iget t M = Some rg /\ rg_len rg' = rg_len rg /\ forall pn, page_at IM rg' t pn = page_at IM rg t pn.
Proof.
  intros H Hg. specialize (H t). rewrite Hg in H. destruct (iget t M) as [rg|]; [|contradiction].
  destruct H as (A1 & A2 & A3 & A4). exists rg. split; [reflexivity|]. split; [exact A2|].
  intros pn. apply page_at_same; assumption.
Qed.

Lemma claimed_wr_same M M' x : same_pg M M' -> claimed_wr IM rho M' x -> claimed_wr IM rho M x.
Proof.
  intros H (t & rg' & pn & p & j & Hg & Hpn & Hp & Hw & Hj & Hjl & Ex).
  destruct (same_pg_get M M' t rg' H Hg) as (rg & Hg0 & Elen & Epa).
  exists t, rg, pn, p, j. rewrite <- Epa, <- Elen. repeat split; try assumption; lia.
Qed.

Lemma LZ_same lazy A M M' : same_pg M M' -> LZ IM rho lazy A M -> LZ IM rho lazy A M'.
Proof.
  intros H HL t rg' pn p x Hg Hpn Hp Hx Hxl Hlz.
  destruct (same_pg_get M M' t rg' H Hg) as (rg & Hg0 & Elen & Epa).
  rewrite Epa in Hp. rewrite Elen in Hxl. exact (HL t rg pn p x Hg0 Hpn Hp Hx Hxl Hlz).
Qed.
End Claims.

(* [comment removed for export] *)
Section Dress.
Variable segs : list Segment.
Variable IM : fimage.

Definition ditem_ok (rho : int -> word) (x : ditem) : Prop :=
  let '(t, clo, chi, k) := x in
  to_Z clo <= bv_unsigned (rho t) <= to_Z chi /\ rkind_ok rho t k.

Lemma mem_ok_redress rho M m t rg clo chi k :
  mem_ok segs IM rho M m -> iget t M = Some rg ->
  to_Z clo <= bv_unsigned (rho t) <= to_Z chi -> rkind_ok rho t k ->
  mem_ok segs IM rho (iset t (redress rg clo chi k) M) m.
Proof.
  intros [Hmem Hsep] Hg Hb Hk. split.
  - intros t1 rg1 H1. rewrite iget_iset in H1. destruct (t1 =? t)%uint63 eqn:E.
    + apply Uint63.eqb_spec in E. subst t1. injection H1 as <-.
      destruct (Hmem t rg Hg) as [Hreg Hpages]. split.
      * destruct Hreg as (A1 & A2 & A3 & A4 & A5 & _ & _). unfold region_ok, redress.
        cbn [rg_lo rg_len rg_align rg_clo rg_chi rg_kind].
        split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
        split; [exact Hb | exact Hk].
      * intros pn p Hpn Hp.
        rewrite (page_at_same IM rg (redress rg clo chi k) t pn eq_refl eq_refl eq_refl eq_refl) in Hp.
        exact (Hpages pn p Hpn Hp).
    + exact (Hmem t1 rg1 H1).
  - intros t1 t2 rg1 rg2 Hne H1 H2. rewrite iget_iset in H1, H2.
    destruct (t1 =? t)%uint63 eqn:E1; destruct (t2 =? t)%uint63 eqn:E2.
    + apply Uint63.eqb_spec in E1, E2. congruence.
    + injection H1 as <-. apply Uint63.eqb_spec in E1. subst t1. exact (Hsep t t2 rg rg2 Hne Hg H2).
    + injection H2 as <-. apply Uint63.eqb_spec in E2. subst t2. exact (Hsep t1 t rg1 rg Hne H1 Hg).
    + exact (Hsep t1 t2 rg1 rg2 Hne H1 H2).
Qed.

Lemma mem_ok_dress rho m : forall bs M,
  mem_ok segs IM rho M m -> Forall (ditem_ok rho) bs -> mem_ok segs IM rho (fold_left dress_mem bs M) m.
Proof.
  induction bs as [|x bs IH]; intros M HM Hbs; cbn [fold_left]; [exact HM|].
  inversion Hbs as [|x0 bs0 Hx Hr]; subst. apply IH; [|exact Hr].
  destruct x as [[[t clo] chi] k]. unfold dress_mem. destruct (iget t M) as [rg|] eqn:Hg; [|exact HM].
  destruct Hx as [Hb Hk]. exact (mem_ok_redress rho M m t rg clo chi k HM Hg Hb Hk).
Qed.

Lemma R_dress rho F ms bs :
  R segs IM rho F ms -> Forall (ditem_ok rho) bs -> R segs IM rho (dress F bs) ms.
Proof.
  intros [P1 P2 P3 P4 P5] Hbs. constructor; cbn [dress f_pc f_regs f_mem f_resv]; try assumption.
  exact (mem_ok_dress rho (ms_mem ms) bs (f_mem F) P5 Hbs).
Qed.

(* [comment removed for export] *)
Definition ditem_lt (n : int) (x : ditem) : Prop :=
  let '(t, _, _, k) := x in
  to_Z t < to_Z n /\ match k with RK_plain => True | RK_shadow p => to_Z p < to_Z n end.

Lemma ditem_ok_agree n rho rho' x :
  agree n rho rho' -> ditem_lt n x -> ditem_ok rho x -> ditem_ok rho' x.
Proof.
  intros [_ Hag]. destruct x as [[[t clo] chi] k]. cbn [ditem_lt ditem_ok]. intros [Ht Hk] [Hb Hko].
  rewrite (Hag t Ht). split; [exact Hb|].
  destruct k as [|p]; [exact I|]. cbn [rkind_ok] in *. rewrite (Hag t Ht), (Hag p Hk). exact Hko.
Qed.

Theorem Rn_dress n rho F ms bs :
  Rn segs IM n rho F ms -> Forall (ditem_lt n) bs -> Forall (ditem_ok rho) bs ->
  Rn segs IM n rho (dress F bs) ms.
Proof.
  intros HRn Hlt Hok rho' Hag. apply R_dress; [exact (HRn rho' Hag)|].
  apply Forall_forall. intros x Hx.
  exact (ditem_ok_agree n rho rho' x Hag (proj1 (Forall_forall _ _) Hlt x Hx) (proj1 (Forall_forall _ _) Hok x Hx)).
Qed.

End Dress.
