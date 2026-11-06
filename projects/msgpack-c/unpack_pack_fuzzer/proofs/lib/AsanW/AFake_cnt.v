(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr Tac InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase ALayout FsKit AFake_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma first_false_nat : forall (P : Z -> bool) (n : nat),
  (exists t, 0 <= t < Z.of_nat n /\ P t = false) ->
  exists j, 0 <= j < Z.of_nat n /\ P j = false /\ forall t, 0 <= t < j -> P t = true.
Proof.
  intros P n. induction n as [|n IH]; intros (t & Ht & Pt); [lia|].
  destruct (Z.eq_dec t (Z.of_nat n)) as [E|NE].
  -
    destruct (forallb (fun k => P (Z.of_nat k)) (seq 0 n)) eqn:ALL.
    + exists (Z.of_nat n). split; [lia|]. split; [subst t; exact Pt|]. intros u Hu.
      rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat u) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in ALL by lia. exact ALL.
    + assert (EX : exists u, 0 <= u < Z.of_nat n /\ P u = false).
      { apply Bool.not_true_iff_false in ALL. destruct (existsb (fun k => negb (P (Z.of_nat k))) (seq 0 n)) eqn:EXB.
        - apply existsb_exists in EXB as (k & Hk & Pk). apply in_seq in Hk. exists (Z.of_nat k). split; [lia|]. apply negb_true_iff in Pk. exact Pk.
        - exfalso. apply ALL. apply forallb_forall. intros k Hk. rewrite <- negb_false_iff.
          destruct (negb (P (Z.of_nat k))) eqn:Q; [|reflexivity]. exfalso.
          assert (X : existsb (fun k => negb (P (Z.of_nat k))) (seq 0 n) = true) by (apply existsb_exists; exists k; split; assumption). congruence. }
      destruct (IH EX) as (j & Hj & Pj & MIN). exists j. split; [lia|]. split; [exact Pj| exact MIN].
  - destruct (IH ltac:(exists t; split; [lia| exact Pt])) as (j & Hj & Pj & MIN). exists j. split; [lia|]. split; [exact Pj| exact MIN].
Qed.

Lemma first_false : forall (P : Z -> bool) (N : Z), 0 <= N ->
  (exists t, 0 <= t < N /\ P t = false) ->
  exists j, 0 <= j < N /\ P j = false /\ forall t, 0 <= t < j -> P t = true.
Proof. intros P N HN EX. rewrite <- (Z2Nat.id N HN) in EX |- *. exact (first_false_nat P (Z.to_nat N) EX). Qed.

Lemma inj_incl_length : forall {A : Type} (f : Z -> A) (l : list A) (N : Z), 0 <= N ->
  (forall t1 t2, 0 <= t1 < N -> 0 <= t2 < N -> f t1 = f t2 -> t1 = t2) ->
  (forall t, 0 <= t < N -> In (f t) l) -> N <= Z.of_nat (length l).
Proof.
  intros A f l N HN INJ INC.
  set (im := map (fun k => f (Z.of_nat k)) (seq 0 (Z.to_nat N))).
  assert (ND : List.NoDup im).
  { subst im. apply Finite.Injective_map_NoDup_in; [| apply seq_NoDup].
    intros k1 k2 H1 H2 E. apply in_seq in H1, H2. apply Nat2Z.inj. apply INJ; [lia| lia| exact E]. }
  assert (IC : incl im l).
  { subst im. intros x Hx. apply in_map_iff in Hx as (k & <- & Hk). apply in_seq in Hk. apply INC. lia. }
  pose proof (NoDup_incl_length ND IC) as LE. subst im. rewrite length_map, length_seq in LE. lia.
Qed.

Lemma probe_inj : forall N h t1 t2, 0 < N -> 0 <= t1 < N -> 0 <= t2 < N -> (h + t1) mod N = (h + t2) mod N -> t1 = t2.
Proof.
  intros N h t1 t2 HN H1 H2 E.
  assert (D : (t1 - t2) mod N = 0).
  { replace (t1 - t2) with ((h + t1) - (h + t2)) by lia. rewrite Zminus_mod, E, Z.sub_diag. apply Z.mod_0_l. lia. }
  apply Z.mod_divide in D; [|lia]. destruct D as [q Hq]. assert (q = 0) by nia. lia.
Qed.

Lemma first_free_pos : forall (busy : Z -> bool) (blk : Z -> ablock) (LBc : list ablock) (N h : Z),
  0 < N -> List.NoDup LBc ->
  (forall p1 p2, 0 <= p1 < N -> 0 <= p2 < N -> blk p1 = blk p2 -> p1 = p2) ->
  (forall p, 0 <= p < N -> busy p = true -> In (blk p) LBc) ->
  Z.of_nat (length LBc) < N ->
  exists j, 0 <= j < N /\ busy ((h + j) mod N) = false /\ forall t, 0 <= t < j -> busy ((h + t) mod N) = true.
Proof.
  intros busy blk LBc N h HN ND INJ BUSY CNT.
  apply (first_false (fun t => busy ((h + t) mod N)) N ltac:(lia)).
  destruct (forallb (fun k => busy ((h + Z.of_nat k) mod N)) (seq 0 (Z.to_nat N))) eqn:ALL.
  - exfalso. rewrite forallb_forall in ALL.
    pose proof (inj_incl_length (fun t => blk ((h + t) mod N)) LBc N ltac:(lia)) as LE. cbv beta in LE.
    assert (N <= Z.of_nat (length LBc)); [| lia]. apply LE.
    + intros t1 t2 H1 H2 E. apply INJ in E; [| apply Z.mod_pos_bound; lia| apply Z.mod_pos_bound; lia]. exact (probe_inj N h t1 t2 HN H1 H2 E).
    + intros t Ht. apply BUSY; [apply Z.mod_pos_bound; lia|]. specialize (ALL (Z.to_nat t) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in ALL by lia. exact ALL.
  - apply Bool.not_true_iff_false in ALL.
    destruct (existsb (fun k => negb (busy ((h + Z.of_nat k) mod N))) (seq 0 (Z.to_nat N))) eqn:EXB.
    + apply existsb_exists in EXB as (k & Hk & Pk). apply in_seq in Hk. exists (Z.of_nat k). split; [lia|]. apply negb_true_iff in Pk. exact Pk.
    + exfalso. apply ALL. apply forallb_forall. intros k Hk.
      destruct (busy ((h + Z.of_nat k) mod N)) eqn:Q; [reflexivity|]. exfalso.
      assert (X : existsb (fun k => negb (busy ((h + Z.of_nat k) mod N))) (seq 0 (Z.to_nat N)) = true)
        by (apply existsb_exists; exists k; split; [exact Hk| rewrite Q; reflexivity]). congruence.
Qed.

Definition isfk (c : Z) (b : ablock) : bool := match ab_kind b with ABFake c' => c' =? c | _ => false end.
Definition fk_count (c : Z) (LB : list ablock) : nat := length (List.filter (isfk c) LB).

Lemma fk_count_cons_other : forall c b LB, isfk c b = false -> fk_count c (b :: LB) = fk_count c LB.
Proof. intros c b LB H. unfold fk_count. change (List.filter (isfk c) (b :: LB)) with (if isfk c b then b :: List.filter (isfk c) LB else List.filter (isfk c) LB). rewrite H. reflexivity. Qed.
Lemma fk_count_filter_le : forall c (f : ablock -> bool) LB, (fk_count c (List.filter f LB) <= fk_count c LB)%nat.
Proof.
  intros c f LB. unfold fk_count. induction LB as [|b LB IH]; [cbn; lia|].
  change (List.filter f (b :: LB)) with (if f b then b :: List.filter f LB else List.filter f LB).
  change (List.filter (isfk c) (b :: LB)) with (if isfk c b then b :: List.filter (isfk c) LB else List.filter (isfk c) LB).
  destruct (f b).
  - change (List.filter (isfk c) (b :: List.filter f LB)) with (if isfk c b then b :: List.filter (isfk c) (List.filter f LB) else List.filter (isfk c) (List.filter f LB)).
    destruct (isfk c b); cbn [length]; lia.
  - destruct (isfk c b); cbn [length]; lia.
Qed.
Lemma isfk_FKB : forall c F n, isfk c (FKB c F n) = true.
Proof. intros. unfold isfk. cbn. apply Z.eqb_refl. Qed.

Section CANSEC1. Context {rc : runConstT}.
Lemma rw_cells_at_eq : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
Lemma fk_frame_inj : forall L c p1 p2, 0 <= c -> fk_frame L c p1 = fk_frame L c p2 -> p1 = p2.
Proof. intros L c p1 p2 Hc E. unfold fk_frame in E. pose proof (fk_fsize_pos c Hc). nia. Qed.
End CANSEC1.

Section CANSEC2. Context {rc : runConstT} {gb : GcBit}.
Definition fbusy (L : alayout) (m : amem) (c pos : Z) : bool :=
  match m (wa (fk_flag L c pos)) with Some b => negb (bv_unsigned b =? 0) | None => true end.

Lemma afake_flag_cell : forall L LB m c pos, AFAKE L LB m -> 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
  exists b, rw_cells asegs m (fk_flag L c pos) [C1 b] /\ m (wa (fk_flag L c pos)) = Some b.
Proof.
  intros L LB m c pos (G & _ & _ & _ & _ & DC1 & _) Hc Hp. destruct G as (G1 & G2 & G3 & _).
  pose proof (ablk_lin _ _ G2) as (GL1 & _ & _ & _). unfold AIMG_HI, FAKESZ in *.
  pose proof (fk_flag_range L c pos Hc Hp) as FR.
  pose proof (dc_sub m (al_fake L + 4096) (11571200 - 4096) (fk_flag L c pos) 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D.
  destruct (c1_of_dc m _ D) as [b Hb]. exists b. split; [exact Hb|]. apply (rw_C1_high m _ b Hb). lia.
Qed.

Lemma afake_first_free : forall L LB m c h,
  AFAKE L LB m -> List.NoDup LB -> 0 <= c < FK_NCLS ->
  Z.of_nat (fk_count c LB) < fk_nframes c ->
  exists j, 0 <= j < fk_nframes c
    /\ (forall t, 0 <= t < j -> exists b, rw_cells asegs m (fk_flag L c ((h + t) mod fk_nframes c)) [C1 b] /\ bv_unsigned b <> 0)
    /\ rw_cells asegs m (fk_flag L c ((h + j) mod fk_nframes c)) [C1 (Z_to_bv 8 0)]
    /\ ~ In (FKB c (fk_frame L c ((h + j) mod fk_nframes c)) (fk_fsize c)) LB.
Proof.
  intros L LB m c h AF ND Hc CNT. pose proof AF as (_ & _ & _ & _ & _ & _ & _ & FL & LV & _).
  assert (NP : 0 < fk_nframes c) by (apply fk_nframes_pos; unfold FK_NCLS in Hc; lia).
  destruct (first_free_pos (fbusy L m c) (fun p => FKB c (fk_frame L c p) (fk_fsize c)) (List.filter (isfk c) LB) (fk_nframes c) h NP) as (j & Hj & FREE & BUSY).
  - apply NoDup_filter. exact ND.
  - intros p1 p2 _ _ E. injection E as E. exact (fk_frame_inj L c p1 p2 ltac:(lia) E).
  - intros p Hp B. apply filter_In. split; [| apply isfk_FKB].
    destruct (afake_flag_cell L LB m c p AF Hc Hp) as (b & _ & Mb). unfold fbusy in B. rewrite Mb in B.
    apply (FL c p b Hc Hp Mb). intros ->. rewrite bv_unsigned_Z_to_bv_0 in B || cbn in B. discriminate B.
  - exact CNT.
  - exists j. split; [exact Hj|].
    assert (PJ : forall t, 0 <= (h + t) mod fk_nframes c < fk_nframes c) by (intros t; apply Z.mod_pos_bound; exact NP).
    split; [| split].
    + intros t Ht. destruct (afake_flag_cell L LB m c _ AF Hc (PJ t)) as (b & Cb & Mb). exists b. split; [exact Cb|].
      specialize (BUSY t Ht). unfold fbusy in BUSY. rewrite Mb in BUSY. apply negb_true_iff in BUSY. apply Z.eqb_neq in BUSY. exact BUSY.
    + destruct (afake_flag_cell L LB m c _ AF Hc (PJ j)) as (b & Cb & Mb). unfold fbusy in FREE. rewrite Mb in FREE.
      apply negb_false_iff in FREE. apply Z.eqb_eq in FREE. assert (b = Z_to_bv 8 0) as <- by (apply bv_eq; rewrite FREE; reflexivity). exact Cb.
    + intros Hin. destruct (LV c _ _ Hin) as (_ & _ & pos' & Hp' & HF' & B1). apply (fk_frame_inj L c _ _ ltac:(lia)) in HF'. subst pos'.
      unfold fbusy in FREE. rewrite B1 in FREE. cbn in FREE. discriminate FREE.
Qed.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import ABase.TwinB ALayout.TwinB FsKit.TwinB AFake_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma first_false_nat : forall (P : Z -> bool) (n : nat),
  (exists t, 0 <= t < Z.of_nat n /\ P t = false) ->
  exists j, 0 <= j < Z.of_nat n /\ P j = false /\ forall t, 0 <= t < j -> P t = true.
Proof.
  intros P n. induction n as [|n IH]; intros (t & Ht & Pt); [lia|].
  destruct (Z.eq_dec t (Z.of_nat n)) as [E|NE].
  -
    destruct (forallb (fun k => P (Z.of_nat k)) (seq 0 n)) eqn:ALL.
    + exists (Z.of_nat n). split; [lia|]. split; [subst t; exact Pt|]. intros u Hu.
      rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat u) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in ALL by lia. exact ALL.
    + assert (EX : exists u, 0 <= u < Z.of_nat n /\ P u = false).
      { apply Bool.not_true_iff_false in ALL. destruct (existsb (fun k => negb (P (Z.of_nat k))) (seq 0 n)) eqn:EXB.
        - apply existsb_exists in EXB as (k & Hk & Pk). apply in_seq in Hk. exists (Z.of_nat k). split; [lia|]. apply negb_true_iff in Pk. exact Pk.
        - exfalso. apply ALL. apply forallb_forall. intros k Hk. rewrite <- negb_false_iff.
          destruct (negb (P (Z.of_nat k))) eqn:Q; [|reflexivity]. exfalso.
          assert (X : existsb (fun k => negb (P (Z.of_nat k))) (seq 0 n) = true) by (apply existsb_exists; exists k; split; assumption). congruence. }
      destruct (IH EX) as (j & Hj & Pj & MIN). exists j. split; [lia|]. split; [exact Pj| exact MIN].
  - destruct (IH ltac:(exists t; split; [lia| exact Pt])) as (j & Hj & Pj & MIN). exists j. split; [lia|]. split; [exact Pj| exact MIN].
Qed.

Lemma first_false : forall (P : Z -> bool) (N : Z), 0 <= N ->
  (exists t, 0 <= t < N /\ P t = false) ->
  exists j, 0 <= j < N /\ P j = false /\ forall t, 0 <= t < j -> P t = true.
Proof. intros P N HN EX. rewrite <- (Z2Nat.id N HN) in EX |- *. exact (first_false_nat P (Z.to_nat N) EX). Qed.

Lemma inj_incl_length : forall {A : Type} (f : Z -> A) (l : list A) (N : Z), 0 <= N ->
  (forall t1 t2, 0 <= t1 < N -> 0 <= t2 < N -> f t1 = f t2 -> t1 = t2) ->
  (forall t, 0 <= t < N -> In (f t) l) -> N <= Z.of_nat (length l).
Proof.
  intros A f l N HN INJ INC.
  set (im := map (fun k => f (Z.of_nat k)) (seq 0 (Z.to_nat N))).
  assert (ND : List.NoDup im).
  { subst im. apply Finite.Injective_map_NoDup_in; [| apply seq_NoDup].
    intros k1 k2 H1 H2 E. apply in_seq in H1, H2. apply Nat2Z.inj. apply INJ; [lia| lia| exact E]. }
  assert (IC : incl im l).
  { subst im. intros x Hx. apply in_map_iff in Hx as (k & <- & Hk). apply in_seq in Hk. apply INC. lia. }
  pose proof (NoDup_incl_length ND IC) as LE. subst im. rewrite length_map, length_seq in LE. lia.
Qed.

Lemma probe_inj : forall N h t1 t2, 0 < N -> 0 <= t1 < N -> 0 <= t2 < N -> (h + t1) mod N = (h + t2) mod N -> t1 = t2.
Proof.
  intros N h t1 t2 HN H1 H2 E.
  assert (D : (t1 - t2) mod N = 0).
  { replace (t1 - t2) with ((h + t1) - (h + t2)) by lia. rewrite Zminus_mod, E, Z.sub_diag. apply Z.mod_0_l. lia. }
  apply Z.mod_divide in D; [|lia]. destruct D as [q Hq]. assert (q = 0) by nia. lia.
Qed.

Lemma first_free_pos : forall (busy : Z -> bool) (blk : Z -> ablock) (LBc : list ablock) (N h : Z),
  0 < N -> List.NoDup LBc ->
  (forall p1 p2, 0 <= p1 < N -> 0 <= p2 < N -> blk p1 = blk p2 -> p1 = p2) ->
  (forall p, 0 <= p < N -> busy p = true -> In (blk p) LBc) ->
  Z.of_nat (length LBc) < N ->
  exists j, 0 <= j < N /\ busy ((h + j) mod N) = false /\ forall t, 0 <= t < j -> busy ((h + t) mod N) = true.
Proof.
  intros busy blk LBc N h HN ND INJ BUSY CNT.
  apply (first_false (fun t => busy ((h + t) mod N)) N ltac:(lia)).
  destruct (forallb (fun k => busy ((h + Z.of_nat k) mod N)) (seq 0 (Z.to_nat N))) eqn:ALL.
  - exfalso. rewrite forallb_forall in ALL.
    pose proof (inj_incl_length (fun t => blk ((h + t) mod N)) LBc N ltac:(lia)) as LE. cbv beta in LE.
    assert (N <= Z.of_nat (length LBc)); [| lia]. apply LE.
    + intros t1 t2 H1 H2 E. apply INJ in E; [| apply Z.mod_pos_bound; lia| apply Z.mod_pos_bound; lia]. exact (probe_inj N h t1 t2 HN H1 H2 E).
    + intros t Ht. apply BUSY; [apply Z.mod_pos_bound; lia|]. specialize (ALL (Z.to_nat t) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in ALL by lia. exact ALL.
  - apply Bool.not_true_iff_false in ALL.
    destruct (existsb (fun k => negb (busy ((h + Z.of_nat k) mod N))) (seq 0 (Z.to_nat N))) eqn:EXB.
    + apply existsb_exists in EXB as (k & Hk & Pk). apply in_seq in Hk. exists (Z.of_nat k). split; [lia|]. apply negb_true_iff in Pk. exact Pk.
    + exfalso. apply ALL. apply forallb_forall. intros k Hk.
      destruct (busy ((h + Z.of_nat k) mod N)) eqn:Q; [reflexivity|]. exfalso.
      assert (X : existsb (fun k => negb (busy ((h + Z.of_nat k) mod N))) (seq 0 (Z.to_nat N)) = true)
        by (apply existsb_exists; exists k; split; [exact Hk| rewrite Q; reflexivity]). congruence.
Qed.

Definition isfk (c : Z) (b : ablock) : bool := match ab_kind b with ABFake c' => c' =? c | _ => false end.
Definition fk_count (c : Z) (LB : list ablock) : nat := length (List.filter (isfk c) LB).

Lemma fk_count_cons_other : forall c b LB, isfk c b = false -> fk_count c (b :: LB) = fk_count c LB.
Proof. intros c b LB H. unfold fk_count. change (List.filter (isfk c) (b :: LB)) with (if isfk c b then b :: List.filter (isfk c) LB else List.filter (isfk c) LB). rewrite H. reflexivity. Qed.
Lemma fk_count_filter_le : forall c (f : ablock -> bool) LB, (fk_count c (List.filter f LB) <= fk_count c LB)%nat.
Proof.
  intros c f LB. unfold fk_count. induction LB as [|b LB IH]; [cbn; lia|].
  change (List.filter f (b :: LB)) with (if f b then b :: List.filter f LB else List.filter f LB).
  change (List.filter (isfk c) (b :: LB)) with (if isfk c b then b :: List.filter (isfk c) LB else List.filter (isfk c) LB).
  destruct (f b).
  - change (List.filter (isfk c) (b :: List.filter f LB)) with (if isfk c b then b :: List.filter (isfk c) (List.filter f LB) else List.filter (isfk c) (List.filter f LB)).
    destruct (isfk c b); cbn [length]; lia.
  - destruct (isfk c b); cbn [length]; lia.
Qed.
Lemma isfk_FKB : forall c F n, isfk c (FKB c F n) = true.
Proof. intros. unfold isfk. cbn. apply Z.eqb_refl. Qed.

Section CANSEC1. Context {rc : runConstT}.
Lemma rw_cells_at_eq : forall m A A' cs, rw_cells bsegs m A cs -> A = A' -> rw_cells bsegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
Lemma fk_frame_inj : forall L c p1 p2, 0 <= c -> fk_frame L c p1 = fk_frame L c p2 -> p1 = p2.
Proof. intros L c p1 p2 Hc E. unfold fk_frame in E. pose proof (fk_fsize_pos c Hc). nia. Qed.
End CANSEC1.

Section CANSEC2. Context {rc : runConstT} {gb : GcBit}.
Definition fbusy (L : alayout) (m : amem) (c pos : Z) : bool :=
  match m (wa (fk_flag L c pos)) with Some b => negb (bv_unsigned b =? 0) | None => true end.

Lemma afake_flag_cell : forall L LB m c pos, AFAKE L LB m -> 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
  exists b, rw_cells bsegs m (fk_flag L c pos) [C1 b] /\ m (wa (fk_flag L c pos)) = Some b.
Proof.
  intros L LB m c pos (G & _ & _ & _ & _ & DC1 & _) Hc Hp. destruct G as (G1 & G2 & G3 & _).
  pose proof (ablk_lin _ _ G2) as (GL1 & _ & _ & _). unfold AIMG_HI, FAKESZ in *.
  pose proof (fk_flag_range L c pos Hc Hp) as FR.
  pose proof (dc_sub m (al_fake L + 4096) (11571200 - 4096) (fk_flag L c pos) 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D.
  destruct (c1_of_dc m _ D) as [b Hb]. exists b. split; [exact Hb|]. apply (rw_C1_high m _ b Hb). lia.
Qed.

Lemma afake_first_free : forall L LB m c h,
  AFAKE L LB m -> List.NoDup LB -> 0 <= c < FK_NCLS ->
  Z.of_nat (fk_count c LB) < fk_nframes c ->
  exists j, 0 <= j < fk_nframes c
    /\ (forall t, 0 <= t < j -> exists b, rw_cells bsegs m (fk_flag L c ((h + t) mod fk_nframes c)) [C1 b] /\ bv_unsigned b <> 0)
    /\ rw_cells bsegs m (fk_flag L c ((h + j) mod fk_nframes c)) [C1 (Z_to_bv 8 0)]
    /\ ~ In (FKB c (fk_frame L c ((h + j) mod fk_nframes c)) (fk_fsize c)) LB.
Proof.
  intros L LB m c h AF ND Hc CNT. pose proof AF as (_ & _ & _ & _ & _ & _ & _ & FL & LV & _).
  assert (NP : 0 < fk_nframes c) by (apply fk_nframes_pos; unfold FK_NCLS in Hc; lia).
  destruct (first_free_pos (fbusy L m c) (fun p => FKB c (fk_frame L c p) (fk_fsize c)) (List.filter (isfk c) LB) (fk_nframes c) h NP) as (j & Hj & FREE & BUSY).
  - apply NoDup_filter. exact ND.
  - intros p1 p2 _ _ E. injection E as E. exact (fk_frame_inj L c p1 p2 ltac:(lia) E).
  - intros p Hp B. apply filter_In. split; [| apply isfk_FKB].
    destruct (afake_flag_cell L LB m c p AF Hc Hp) as (b & _ & Mb). unfold fbusy in B. rewrite Mb in B.
    apply (FL c p b Hc Hp Mb). intros ->. rewrite bv_unsigned_Z_to_bv_0 in B || cbn in B. discriminate B.
  - exact CNT.
  - exists j. split; [exact Hj|].
    assert (PJ : forall t, 0 <= (h + t) mod fk_nframes c < fk_nframes c) by (intros t; apply Z.mod_pos_bound; exact NP).
    split; [| split].
    + intros t Ht. destruct (afake_flag_cell L LB m c _ AF Hc (PJ t)) as (b & Cb & Mb). exists b. split; [exact Cb|].
      specialize (BUSY t Ht). unfold fbusy in BUSY. rewrite Mb in BUSY. apply negb_true_iff in BUSY. apply Z.eqb_neq in BUSY. exact BUSY.
    + destruct (afake_flag_cell L LB m c _ AF Hc (PJ j)) as (b & Cb & Mb). unfold fbusy in FREE. rewrite Mb in FREE.
      apply negb_false_iff in FREE. apply Z.eqb_eq in FREE. assert (b = Z_to_bv 8 0) as <- by (apply bv_eq; rewrite FREE; reflexivity). exact Cb.
    + intros Hin. destruct (LV c _ _ Hin) as (_ & _ & pos' & Hp' & HF' & B1). apply (fk_frame_inj L c _ _ ltac:(lia)) in HF'. subst pos'.
      unfold fbusy in FREE. rewrite B1 in FREE. cbn in FREE. discriminate FREE.
Qed.
End CANSEC2.
End TwinB.
