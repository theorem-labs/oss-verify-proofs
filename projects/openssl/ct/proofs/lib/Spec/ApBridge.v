(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import RelSpec.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Malloc Driver Prog MI_Cnt MI_Inv LB_Inv LibProg LibSafe LibOps.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim BnModel BnTree BgState
  ApBase ApState ApLogic ApErr ApCnf ApInv ApFmt ApParse ApPrim ApObj ApObjTab ApBn ApParse2 ApSpecs ApParseSpec ApBnSpec ApOwner.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition sys_to (o : ApBase.sysop) : LibProg.sysop :=
  match o with
  | ApBase.SyGetuid => LibProg.SyGetuid
  | ApBase.SyGeteuid => LibProg.SyGeteuid
  | ApBase.SyGetgid => LibProg.SyGetgid
  | ApBase.SyGetegid => LibProg.SyGetegid
  | ApBase.SyOpenCnf => LibProg.SyOpenCnf
  end.

Fixpoint ap_embed {A} (t : aprog bptr A) : lprog A :=
  match t with
  | ARet a => LRet a
  | AUnr => LUnr
  | AMalloc n k => LMalloc n (fun r => ap_embed (k r))
  | AFree p k => LFree p (ap_embed k)
  | ARealloc p n k => LRealloc p n (fun r => ap_embed (k r))
  | AReallocS p n k => LReallocS p n (fun r => ap_embed (k r))
  | ASys o k => LSys (sys_to o) (fun r => ap_embed (k r))
  | AReallocI p n k => LReallocI p n (fun r => ap_embed (k r))       (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Definition shrink_crit (m n : Z) : Prop := 0 <= n < m /\ m < MMAP_THRESHOLD /\ size_to_class n + 1 < size_to_class m.
Definition shrink_crit_b (m n : Z) : bool := (0 <=? n) && (n <? m) && (m <? MMAP_THRESHOLD) && (size_to_class n + 1 <? size_to_class m).
Lemma shrink_crit_b_ok m n : shrink_crit_b m n = true -> shrink_crit m n.
Proof.
  unfold shrink_crit_b, shrink_crit. intros H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3. apply Z.ltb_lt in H4. lia.
Qed.

(* [comment removed for export] *)
Definition ap_spre (o : ApBase.sysop) : Prop := sys_pre (sys_to o).
Lemma ap_spre_all : cnf_arm_present -> forall o, ap_spre o.
Proof. intros H o. destruct o; cbn; first [exact I| exact H]. Qed.

(* [comment removed for export] *)
Lemma fresh_of_slot_fresh (p : bptr) (X : list (bptr * Z)) : ~ In (fst p) (slotsX X) -> ~ In p (map fst X).
Proof.
  intros H Hin. apply H. unfold slotsX. apply in_map_iff in Hin. destruct Hin as ([q n] & E & Hin). cbn in E. subst q.
  apply in_map_iff. exists (p, n). split; [reflexivity|exact Hin].
Qed.

Lemma ap_embed_lwf : forall (ok : list (bptr * Z) -> Z -> Prop) {A} (t : aprog bptr A) X Q,
  awp ok realloc_crit shrink_crit inplace_crit ap_spre t X Q -> lwf ok (ap_embed t) X Q.
Proof.
  intros ok A t. induction t as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros X Q H; cbn [awp ap_embed lwf] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & Hok & HN & Hk). split; [exact Hn|]. split; [exact Hok|]. split; [rewrite HN; reflexivity|].
    intros q Hq. apply IH. apply Hk. apply fresh_of_slot_fresh. exact Hq.
  - destruct H as (m & X' & HP & Hk). exists m, X'. split; [exact HP|]. apply IH. exact Hk.
  - destruct H as (m & X' & HP & Hn & Hc & Hok & HN & Hk). exists m, X'. split; [exact HP|]. split; [exact Hn|]. split; [exact Hc|].
    split; [exact Hok|]. split; [rewrite HN; reflexivity|]. intros q Hq. apply IH. apply Hk. apply fresh_of_slot_fresh. exact Hq.
  - destruct H as (m & X' & HP & Hn & (C1 & C2 & C3) & Hok & HN & Hk). exists m, X'. split; [exact HP|]. split; [lia|]. split; [exact C2|]. split; [exact C3|].
    split; [exact Hok|]. split; [rewrite HN; reflexivity|]. intros q Hq. apply IH. apply Hk. apply fresh_of_slot_fresh. exact Hq.
  - destruct H as [Hs H]. split; [exact Hs|]. intros r _. apply IH. apply H.
  - (* [comment removed for export] *)
    destruct H as (m & X' & HP & Hn & (C1 & C2 & C3) & Hok & HN & Hk). exists m, X'. split; [exact HP|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    split; [exact Hok|]. split; [rewrite HN; reflexivity|]. intros q Hq. apply IH. apply Hk.
    destruct Hq as [Hq|Hq]; [left; exact Hq| right; apply fresh_of_slot_fresh; exact Hq].
Qed.

Lemma ap_embed_lleaves : forall {A} (t : aprog bptr A) (phi : A -> Prop), aleaves t phi -> lleaves (ap_embed t) phi.
Proof.
  intros A t phi. induction t as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros H; cbn [aleaves ap_embed lleaves] in *; auto.
Qed.

(* [comment removed for export] *)
Lemma rc_grow_46 : forall m, 0 <= m <= 46 -> realloc_crit m 1024.
Proof.
  intros m Hm. apply realloc_crit_b_ok.
  assert (H : forallb (fun m => realloc_crit_b m 1024) (zrange 0 47) = true) by (vm_compute; reflexivity).
  exact (forallb_zrange _ 0 47 m H ltac:(lia) ltac:(lia)).
Qed.

Lemma rc_shrink_46 : forall n, 1 <= n <= 46 -> shrink_crit 1024 n.
Proof.
  intros n Hn. apply shrink_crit_b_ok.
  assert (H : forallb (fun n => shrink_crit_b 1024 n) (zrange 1 46) = true) by (vm_compute; reflexivity).
  exact (forallb_zrange _ 1 46 n H ltac:(lia) ltac:(lia)).
Qed.

(* [comment removed for export] *)
Lemma okAp_same X n : ApLogic.okAp AP_NB AP_TOT X n <-> LibOps.okAp AP_NB AP_TOT X n.
Proof. unfold ApLogic.okAp, LibOps.okAp, zlength, zlen, bnonneg, bsum, MI_Inv.zsum. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ap_lib_one (ls : ap_ls bptr) (d : list Z) : lprog (ap_ls bptr * Z) := ap_embed (ap_one ls d).

(* [comment removed for export] *)
Theorem ap_H_one : cnf_arm_present -> forall ls d X, ap_linv ls X -> zlength d <= MAX_INPUT ->
  lwf (LibOps.okAp AP_NB AP_TOT) (ap_lib_one ls d) X (fun r X' => ap_linv (fst r) X').
Proof.
  intros HC ls d X HL Hd. unfold ap_lib_one.
  apply (lwf_ok_mono (ApLogic.okAp AP_NB AP_TOT)); [intros X' n H; apply okAp_same; exact H|].
  apply ap_embed_lwf.
  apply (ap_one_awp realloc_crit shrink_crit inplace_crit ap_spre rc_grow_46 rc_shrink_46 (ap_spre_all HC)); [exact HL|]. unfold AP_MAX_INPUT. unfold MAX_INPUT in Hd. exact Hd.
Qed.

Theorem ap_H_rc : forall ls d, lleaves (ap_lib_one ls d) (fun r => snd r = 0).
Proof. intros ls d. unfold ap_lib_one. apply ap_embed_lleaves. apply ap_one_leaves. Qed.

Theorem ap_linv_init_bptr : ap_linv (ptr:=bptr) ap_ls0 [].
Proof. apply ap_linv_init. Qed.
