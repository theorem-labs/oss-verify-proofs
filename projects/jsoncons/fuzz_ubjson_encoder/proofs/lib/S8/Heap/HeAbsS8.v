(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import KInvS8 MI_InvS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Kit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import MI_ListS8 MI_ExtS8 MI_Ext2S8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import DecodeS8.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMABS.
Context {RUNp : RunP}.

Definition INVC (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) : Prop :=
  inv_R X st L /\ inv_A st /\ inv_M X st LS /\ inv_L st LS /\ inv_G X st LS /\ inv_S X st BL.

Lemma INVC_of X st L BL LS : INVL X st L BL LS -> INVC X st L BL LS.
Proof. intros (A & B & C & D & E & F & _). exact (conj A (conj B (conj C (conj D (conj E F))))). Qed.

Lemma INVC_strip X st L BL LS : INVL X st L BL LS -> INVC X (strip st) L BL LS.
Proof.
  intros (A & B & C & D & E & F & _).
  split; [destruct A; constructor; match goal with H : _ |- _ => exact H end|].
  split; [destruct B; constructor; match goal with H : _ |- _ => exact H end|].
  split; [apply (inv_M_ext X st (strip st) LS); [reflexivity| reflexivity| exact C]|].
  split; [apply (inv_L_ext st (strip st) LS); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact D]|].
  split.
  - destruct E as [E1 E2 E3 E4 E5]; constructor; try (match goal with H : _ |- _ => exact H end).
    intros m b ai H. apply (group_ok_ext X st (strip st) LS m b ai); [reflexivity| reflexivity| auto| exact (E1 m b ai H)].
  - apply (inv_S_ext X st (strip st) BL); [reflexivity| reflexivity| reflexivity| exact F].
Qed.

Lemma linked_det st a : forall t1 t2 x, linked st (x :: t1 ++ [a]) -> linked st (x :: t2 ++ [a]) ->
  ~ In a t1 -> ~ In a t2 -> t1 = t2.
Proof.
  induction t1 as [|y t1 IH]; intros t2 x H1 H2 N1 N2; destruct t2 as [|y' t2].
  - reflexivity.
  - cbn [app linked] in H1, H2. destruct H1 as [E1 _]. destruct H2 as [E2 _]. rewrite E1 in E2. injection E2 as ->.
    exfalso. apply N2. left. reflexivity.
  - cbn [app linked] in H1, H2. destruct H1 as [E1 _]. destruct H2 as [E2 _]. rewrite E1 in E2. injection E2 as ->.
    exfalso. apply N1. left. reflexivity.
  - cbn [app] in H1, H2. cbn [linked] in H1, H2. destruct H1 as (E1 & _ & H1). destruct H2 as (E2 & _ & H2).
    rewrite E1 in E2. injection E2 as <-. f_equal. apply (IH t2 y); [exact H1| exact H2| |].
    + intros Hin. apply N1. right. exact Hin.
    + intros Hin. apply N2. right. exact Hin.
Qed.

Lemma dll_det st l1 l2 : NoDup l1 -> NoDup l2 -> dll st l1 -> dll st l2 -> head_of l1 = head_of l2 -> l1 = l2.
Proof.
  intros N1 N2 D1 D2 H. destruct l1 as [|a t1]; destruct l2 as [|b t2]; cbn in H; try discriminate; [reflexivity|].
  injection H as <-. cbn [dll] in D1, D2. f_equal.
  apply (linked_det st a t1 t2 a); [exact D1| exact D2| |].
  - intros Hin. apply NoDup_cons in N1 as [Na _]. apply Na. apply list_elem_of_In. exact Hin.
  - intros Hin. apply NoDup_cons in N2 as [Na _]. apply Na. apply list_elem_of_In. exact Hin.
Qed.

Lemma lists_det st LS1 LS2 : inv_L st LS1 -> inv_L st LS2 -> forall h, LS1 h = LS2 h.
Proof.
  intros I1 I2 h. apply (dll_det st); [exact (il_nodup _ _ I1 h)| exact (il_nodup _ _ I2 h)| exact (il_dll _ _ I1 h)| exact (il_dll _ _ I2 h)|].
  rewrite <- (il_head _ _ I1 h), <- (il_head _ _ I2 h). reflexivity.
Qed.

Definition fmask (r : meta) : Z := Z.lor (m_avail r) (m_freed r).

Definition gempty (st : mstate) (m : aptr) : Prop := fmask (MR st m) = mask_upto (m_last_idx (MR st m)).

Record EINV (st : mstate) : Prop := mkEINV {
  e_uniq : forall b1 m1 b2 m2, hosts st b1 m1 -> hosts st b2 m2 -> gempty st m1 -> gempty st m2 ->
      m_sizeclass (MR st m1) = m_sizeclass (MR st m2) -> b1 = b2;
  e_top : forall b m, hosts st b m -> gempty st m -> m_maplen (MR st m) <> 0 /\ 7 <= m_sizeclass (MR st m) <= 38
}.

Definition L63 (st : mstate) (SZ : list (aptr * Z)) : Prop :=
  forall c n m i, In (c, n) SZ -> s_slots st !! c = Some (m, i) -> m_sizeclass (MR st m) = 63 ->
    exists r, s_regions st !! fst c = Some r /\ r_kind r = RKGroup /\ r_len r = n + IB + UNIT.

Definition NLK (st : mstate) : Prop :=
  forall m, s_metas st !! m <> None -> m_mem (MR st m) <> None \/ m_next (MR st m) <> None.

Definition nmeta (st : mstate) : Z := Z.of_nat (size (s_metas st)).
Definition ngrp (st : mstate) : Z := Z.of_nat (size (s_groups st)).
Definition nareas (st : mstate) : Z := Z.of_nat (size (s_areas st)).
Definition carved (st : mstate) : Z := NSLOTS * nareas st - c_avail_meta_count (s_ctx st).

Definition zsum (l : list Z) : Z := fold_right Z.add 0 l.

Definition wreg (r : region) : Z :=
  match r_kind r with RKGroup => mmap_len (r_len r) | RKMeta => r_len r | RKBrk => 2 * r_len r end.
Definition brk_dead_w (st : mstate) : Z := match c_brk (s_ctx st) with BrkDead => 2 * PGSZ | _ => 0 end.
Definition Phi (st : mstate) : Z := zsum (map (fun kr : N * region => wreg (snd kr)) (map_to_list (s_regions st))) + brk_dead_w st.

Definition is_greg (kr : N * region) : bool := match r_kind (snd kr) with RKGroup => true | _ => false end.
Definition ngreg (st : mstate) : Z := Z.of_nat (length (List.filter is_greg (map_to_list (s_regions st)))).
Definition Psi (st : mstate) : Z := ngreg st + 4 * nareas st.

Lemma zsum_app l1 l2 : zsum (l1 ++ l2) = zsum l1 + zsum l2.
Proof. unfold zsum. induction l1 as [|x l1 IH]; cbn [app fold_right]; lia. Qed.

Lemma zsum_perm l1 l2 : Permutation l1 l2 -> zsum l1 = zsum l2.
Proof. unfold zsum. induction 1 as [|x l1 l2 P IH|x y l|l1 l2 l3 P1 IH1 P2 IH2]; cbn [fold_right]; [reflexivity| rewrite IH; reflexivity| lia| congruence]. Qed.

End HMABS.
