(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Driver Prog
  MI_Arith MI_Inv MI_Cnt LB_Tables LB_Inv LB_Sum LB_Raw LB_StmtA LibProg LibSafe LibOps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Definition CT_NBT : Z := 45000.          (* [comment removed for export] *)
Definition CT_SMB : Z := 3145728.        (* [comment removed for export] *)
Definition CT_NB63 : Z := 4.             (* [comment removed for export] *)
Definition CT_BIGB : Z := 167772160.     (* [comment removed for export] *)
Definition CT_NSEC : Z := 6.             (* [comment removed for export] *)
Definition CT_MAXREQ : Z := 100663296.   (* [comment removed for export] *)
Definition ASAN_SEC_MIN : Z := 64513.

Definition smsz (n : Z) : Z := if n <? MMAP_THRESHOLD then n else 0.
Definition smsum (X : list (bptr * Z)) : Z := zsum (map (fun xb => smsz (snd xb)) X).
Definition nsecX (X : list (bptr * Z)) : Z := zcount (fun xb => ASAN_SEC_MIN <=? snd xb) X.

Definition okCt (X : list (bptr * Z)) (n : Z) : Prop :=
  0 <= n /\ Forall (fun xb => 0 <= snd xb) X
  /\ zlen X + 1 <= CT_NBT
  /\ smsum X + smsz n <= CT_SMB
  /\ n63X X + (if MMAP_THRESHOLD <=? n then 1 else 0) <= CT_NB63
  /\ R63X X + bigb n <= CT_BIGB
  /\ nsecX X + (if ASAN_SEC_MIN <=? n then 1 else 0) <= CT_NSEC
  /\ n <= CT_MAXREQ.

(* [comment removed for export] *)
Definition cmin (c : Z) : Z := if c <=? 0 then 0 else UNIT * size_class (c - 1) - IB + 1.
Definition cmin_f (k : Z) : bool := let c := stc_k k in (c <=? 0) || (size_class (c - 1) <=? k).
Lemma cmin_f_true : forallb cmin_f (zrange 0 8191) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cmin_le n : 0 <= n < MMAP_THRESHOLD -> cmin (size_to_class n) <= n.
Proof.
  intros Hn. rewrite size_to_class_k. rewrite Z.shiftr_div_pow2 by lia. unfold IB, UNIT, MMAP_THRESHOLD in *.
  set (k := (n + 4 - 1) / 2 ^ 4).
  assert (Hk : 0 <= k < 8191) by (subst k; change (2 ^ 4) with 16; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (Hk2 : 16 * k <= n + 3) by (subst k; change (2 ^ 4) with 16; pose proof (Z.mul_div_le (n + 4 - 1) 16 ltac:(lia)); lia).
  pose proof (forallb_zrange cmin_f 0 8191 k cmin_f_true ltac:(lia) ltac:(lia)) as H. unfold cmin_f in H. cbn zeta in H.
  unfold cmin. apply orb_true_iff in H. destruct H as [H|H]; [rewrite H; lia|]. apply Z.leb_le in H.
  destruct (stc_k k <=? 0); [lia|]. unfold UNIT, IB. nia.
Qed.
Lemma cmin_nonneg c : 0 <= c < 48 -> 0 <= cmin c.
Proof. intros Hc. unfold cmin. destruct (Z.leb_spec c 0); [lia|]. pose proof (size_class_bound (c - 1) ltac:(lia)). unfold UNIT, IB. lia. Qed.

(* [comment removed for export] *)
Definition NBC (c : Z) : Z := if cmin c <=? 0 then CT_NBT else Z.min CT_NBT (CT_SMB / cmin c).

Lemma smsum_cons p n X : smsum ((p, n) :: X) = smsz n + smsum X.
Proof. unfold smsum. cbn [map snd]. rewrite zsum_cons. reflexivity. Qed.
Lemma smsum_app X Y : smsum (X ++ Y) = smsum X + smsum Y.
Proof. unfold smsum. rewrite map_app. apply zsum_app. Qed.
Lemma smsz_nonneg n : 0 <= n -> 0 <= smsz n.
Proof. intros. unfold smsz. destruct (n <? MMAP_THRESHOLD); lia. Qed.
Lemma smsum_nonneg X : Forall (fun xb => 0 <= snd xb) X -> 0 <= smsum X.
Proof. induction X as [|[p n] X IH]; intros HF; [reflexivity|]. rewrite smsum_cons. inversion HF; subst. cbn [snd] in *. pose proof (smsz_nonneg n H1). specialize (IH H2). lia. Qed.
Lemma nsecX_cons p n X : nsecX ((p, n) :: X) = (if ASAN_SEC_MIN <=? n then 1 else 0) + nsecX X.
Proof. unfold nsecX. rewrite zcount_cons. reflexivity. Qed.
Lemma nsecX_app X Y : nsecX (X ++ Y) = nsecX X + nsecX Y.
Proof. unfold nsecX. apply zcount_app. Qed.
Lemma LRX_cons' p n X c : LRX ((p, n) :: X) c = (if negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? c) then 1 else 0) + LRX X c.
Proof. unfold LRX. rewrite zcount_cons. reflexivity. Qed.

(* [comment removed for export] *)
Lemma LRX_smsum X c : 0 <= c < 48 -> Forall (fun xb => 0 <= snd xb) X -> cmin c * LRX X c <= smsum X.
Proof.
  intros Hc. induction X as [|[p n] X IH]; intros HF.
  - unfold LRX, smsum, zcount, zlen, zsum. cbn. lia.
  - inversion HF as [|x l Hn HX]; subst. cbn [snd] in Hn. specialize (IH HX). rewrite LRX_cons', smsum_cons.
    pose proof (smsz_nonneg n Hn). pose proof (cmin_nonneg c Hc).
    destruct (Z.leb_spec MMAP_THRESHOLD n) as [B|B]; cbn [negb andb]; [lia|].
    destruct (Z.eqb_spec (size_to_class n) c) as [E|NE]; [| lia].
    pose proof (cmin_le n ltac:(lia)) as CM. rewrite E in CM. unfold smsz. replace (n <? MMAP_THRESHOLD) with true by (symmetry; apply Z.ltb_lt; lia). nia.
Qed.

Lemma okCt_LRX X n c : 0 <= c < 48 -> okCt X n -> n < MMAP_THRESHOLD -> size_to_class n = c -> LRX X c + 1 <= NBC c.
Proof.
  intros Hc (Hn & HF & HL & HS & _) Hsm Ecl. unfold NBC.
  pose proof (LRX_le_zlen X c) as L1. pose proof (LRX_smsum X c Hc HF) as L2. pose proof (cmin_nonneg c Hc) as C0.
  assert (Hsz : smsz n = n) by (unfold smsz; replace (n <? MMAP_THRESHOLD) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity). rewrite Hsz in HS.
  pose proof (cmin_le n ltac:(lia)) as CM. rewrite Ecl in CM.
  destruct (Z.leb_spec (cmin c) 0) as [Z0|P0]; [lia|].
  apply Z.min_glb; [lia|].
  (* [comment removed for export] *)
  apply Z.div_le_lower_bound; [lia|]. nia.
Qed.

Section CapsCt.
Variable P : Z -> Z.
Variable T : list Z.

Definition capsCt_ok : Prop :=
  (forall c, 0 <= c < 48 -> LRs T c + NBC c + 5 <= P c) /\ n63s T + CT_NB63 + 5 <= P 63
  /\ PHI P + R63s T + CT_BIGB + 5 * DRV_BIG <= LBUDGET.

Definition capsCt_ok_b : bool :=
  forallb (fun c => LRs T c + NBC c + 5 <=? P c) (zrange 0 48)
  && (n63s T + CT_NB63 + 5 <=? P 63)
  && (PHI P + R63s T + CT_BIGB + 5 * DRV_BIG <=? LBUDGET).

Lemma capsCt_ok_b_ok : capsCt_ok_b = true -> capsCt_ok.
Proof.
  unfold capsCt_ok_b, capsCt_ok. intros H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H2, H3.
  split; [| split; assumption].
  intros c Hc. pose proof (forallb_zrange _ 0 48 c H1 ltac:(lia) ltac:(lia)) as Hf. cbn beta in Hf. apply Z.leb_le in Hf. exact Hf.
Qed.

Hypothesis HC : capsCt_ok.

Lemma NBC_nonneg c : 0 <= c < 48 -> 0 <= NBC c.
Proof. intros Hc. unfold NBC, CT_NBT, CT_SMB. destruct (Z.leb_spec (cmin c) 0); [lia|]. apply Z.min_glb; [lia| apply Z.div_pos; lia]. Qed.

Lemma capsT_of_capsCt : capsT_ok P T.
Proof.
  destruct HC as (C1 & C2 & C3). unfold CT_NB63, CT_BIGB in *.
  split; [|split]; [intros c Hc; specialize (C1 c Hc); pose proof (NBC_nonneg c Hc); lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma okCt_LRX_le X n c : 0 <= c < 48 -> okCt X n -> LRX X c <= NBC c.
Proof.
  intros Hc (Hn & HF & HL & HS & _). unfold NBC.
  pose proof (LRX_le_zlen X c) as L1. pose proof (LRX_smsum X c Hc HF) as L2. pose proof (cmin_nonneg c Hc) as C0. pose proof (smsz_nonneg n Hn).
  destruct (Z.leb_spec (cmin c) 0) as [Z0|P0]; [lia|].
  apply Z.min_glb; [lia|]. apply Z.div_le_lower_bound; [lia|]. nia.
Qed.

Lemma okCt_bridge : ok_bridge P T okCt.
Proof.
  intros D Li X n HD SD HS _ HOK. pose proof HOK as (Hn & HF & HL & HSM & H63 & HB & _). rewrite app_assoc.
  set (q0 := (((0%N, 0), 0) : bptr)).
  apply (libfit_lib P (X ++ Li) D q0 n); [|exact HD| exact SD| exact Hn].
  apply (libfit_perm P (((q0, n) :: X) ++ Li)); [apply Permutation_refl|].
  destruct HC as (C1 & C2 & C3).
  split; [|split].
  - intros c Hc. rewrite LRX_app, (LRX_sizes Li). pose proof (subms_LRs _ _ c HS). specialize (C1 c Hc).
    rewrite LRX_cons'. cbn [snd].
    destruct (Z.leb_spec MMAP_THRESHOLD n) as [B|B]; cbn [negb andb].
    + pose proof (okCt_LRX_le X n c Hc HOK). lia.
    + destruct (Z.eqb_spec (size_to_class n) c) as [E|NE].
      * pose proof (okCt_LRX X n c Hc HOK ltac:(lia) E). lia.
      * pose proof (okCt_LRX_le X n c Hc HOK). lia.
  - rewrite n63X_app, (n63X_sizes Li). pose proof (subms_n63s _ _ HS). unfold n63X at 1. rewrite zcount_cons. fold (n63X X). cbn [snd].
    unfold CT_NB63 in *. destruct (MMAP_THRESHOLD <=? n); lia.
  - rewrite R63X_app, (R63X_sizes Li), R63X_cons. pose proof (subms_R63s _ _ HS). unfold CT_BIGB in *. lia.
Qed.
End CapsCt.
