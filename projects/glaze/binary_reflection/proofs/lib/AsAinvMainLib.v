(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

Section MainLib.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable ISP : expr.
  Variable FS0 : Fs.Fs.
  (* [comment removed for export] *)
  Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (u a) = false -> find_segment SEGS (u a) 1 = None.
  Hypothesis HULL_ok : APS.hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> sp_window_lo <= u a /\ u (edenot E ISP) <= u a.

  Variables (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis CS : APS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model.
  #[local] Notation Mr := (APS.Mr A argH E cs model FULL).
  #[local] Notation hid := (APS.hid A argH E cs model).

  Lemma KN : know_ok SEGS E Mr (kn cs).
  Proof. exact (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ CS). Qed.
  Lemma kn_fact : forall K, In K (kn cs) -> kentry_ok SEGS E Mr K.
  Proof. intros K HK. pose proof KN as H. unfold know_ok in H. rewrite Forall_forall in H. exact (H K HK). Qed.

  Lemma HOFF : H_off_segments SEGS hid.
  Proof. exact (APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH ISP argH_high E cs model). Qed.

  (* [comment removed for export] *)
  Lemma rdn_full : forall (a : word) w bs, rdn SEGS Mr a w = Some bs -> rdn SEGS FULL a w = Some bs.
  Proof.
    intros a w. revert a. induction w as [|w IH]; intros a bs Hr; [exact Hr|].
    cbn [rdn] in Hr |- *.
    assert (BYTE : forall b, (match Mr a with Some b => Some b | None => seg_rom SEGS a end) = Some b ->
                             (match FULL a with Some b => Some b | None => seg_rom SEGS a end) = Some b).
    { intros b Hb. unfold APS.Mr, mrestrict in Hb. destruct (hid a) eqn:Hh; [| exact Hb].
      exfalso. unfold seg_rom in Hb. rewrite (memory_read1_hidden SEGS hid HOFF a Hh) in Hb. discriminate Hb. }
    destruct (match Mr a with Some b => Some b | None => seg_rom SEGS a end) as [b|] eqn:Hb; [| discriminate Hr].
    rewrite (BYTE b eq_refl).
    destruct (rdn SEGS Mr (a + 1)%bv w) as [rest|] eqn:Hr2; [| discriminate Hr].
    rewrite (IH _ _ Hr2). exact Hr.
  Qed.

  (* [comment removed for export] *)
  Lemma Mr_some : forall (a : word) b, Mr a = Some b -> FULL a = Some b.
  Proof. intros a b H. unfold APS.Mr, mrestrict in H. destruct (hid a); [discriminate H | exact H]. Qed.

  (* [comment removed for export] *)
  Lemma kword_cellZ : forall b o w v, In (KWord (SA b o) w v) (kn cs) ->
    flat E (SA b o) (Z.of_nat w) /\ cellN SEGS FULL (estart E (SA b o)) w (u (edenot E v)).
  Proof.
    intros b o w v HK. destruct (kn_fact _ HK) as (Hw & Hf & Hr). split; [exact Hf|].
    unfold cellN. rewrite <- (flat_u E (SA b o) (Z.of_nat w) Hf). rewrite !Z_to_bv_bv_unsigned.
    exact (rdn_full _ _ _ Hr).
  Qed.
  (* [comment removed for export] *)
  Lemma kword_cellZ_lit : forall b o w z, In (KWord (SA b o) w (ELit z)) (kn cs) -> 0 <= z < 2 ^ 64 ->
    cellN SEGS FULL (estart E (SA b o)) w z.
  Proof.
    intros b o w z HK Hz. destruct (kword_cellZ b o w (ELit z) HK) as [_ C]. cbn [edenot] in C. rewrite u64_lit in C by exact Hz. exact C.
  Qed.

  (* [comment removed for export] *)
  Lemma kzero_bytes : forall b o n, In (KZero (SA b o) (ELit n)) (kn cs) -> 0 <= n < 2 ^ 64 ->
    flat E (SA b o) n /\ forall i, 0 <= i < n -> FULL (Z_to_bv 64 (estart E (SA b o) + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros b o n HK Hn. destruct (kn_fact _ HK) as (Hf & Hz). unfold elenZ in Hf, Hz. cbn [edenot] in Hf, Hz. rewrite u64_lit in Hf, Hz by exact Hn.
    split; [exact Hf|]. intros i Hi. exact (Mr_some _ _ (Hz i Hi)).
  Qed.
  Lemma kzero_fillZ : forall b o n, In (KZero (SA b o) (ELit n)) (kn cs) -> 0 <= n < 2 ^ 64 ->
    fillZ SEGS FULL (estart E (SA b o)) (estart E (SA b o) + n) 0
    /\ (forall i, estart E (SA b o) <= i < estart E (SA b o) + n -> FULL (Z_to_bv 64 i) <> None).
  Proof.
    intros b o n HK Hn. destruct (kzero_bytes b o n HK Hn) as [Hf Hz]. split.
    - intros i Hi. unfold byteZ, cellN. cbn [rdn]. replace i with (estart E (SA b o) + (i - estart E (SA b o))) by lia.
      rewrite (Hz (i - estart E (SA b o))) by lia. reflexivity.
    - intros i Hi. replace i with (estart E (SA b o) + (i - estart E (SA b o))) by lia. rewrite (Hz (i - estart E (SA b o))) by lia. discriminate.
  Qed.
  Lemma kfill_fillZ : forall b o n c, In (KFill (SA b o) (ELit n) c) (kn cs) -> 0 <= n < 2 ^ 64 -> 0 <= c < 256 ->
    fillZ SEGS FULL (estart E (SA b o)) (estart E (SA b o) + n) c.
  Proof.
    intros b o n c HK Hn Hc. destruct (kn_fact _ HK) as (Hf & Hz). unfold elenZ in Hf, Hz. cbn [edenot] in Hf, Hz. rewrite u64_lit in Hf, Hz by exact Hn.
    intros i Hi. unfold byteZ, cellN. cbn [rdn]. replace i with (estart E (SA b o) + (i - estart E (SA b o))) by lia.
    rewrite (Mr_some _ _ (Hz (i - estart E (SA b o)) ltac:(lia))). unfold word_to_le_bytes. cbn [Z_to_le_bytes]. rewrite u64_lit by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma kimg_none : forall lo hi, In (KImg lo hi) (kn cs) ->
    forall i, lo <= i < hi -> APS.in_hull A i = true -> FULL (Z_to_bv 64 i) = None.
  Proof.
    intros lo hi HK i Hi Hin. destruct (kn_fact _ HK) as (H0 & H1 & Hn). specialize (Hn i Hi).
    unfold APS.Mr, mrestrict in Hn.
    pose proof (APS.hid_hull A HULL_ok argH ISP argH_high E cs model (Z_to_bv 64 i)) as X. rewrite u64_lit in X by lia.
    rewrite (X Hin) in Hn. exact Hn.
  Qed.
  (* [comment removed for export] *)
  Lemma cellZ_rom : forall a n v, (forall i, a <= i < a + Z.of_nat n -> FULL (Z_to_bv 64 i) = None) ->
    rdn SEGS (fun _ => None) (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
    cellZ SEGS FULL a n v.
  Proof.
    intros a n v Hnone Hrom H0 H1. unfold cellZ, cellN. rewrite <- Hrom. apply rdn_ext; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia. pose proof (u64_range x) as Rx.
    replace x with (Z_to_bv 64 (u x)) by (apply bv_eq; rewrite u64_lit by lia; reflexivity). exact (Hnone (u x) ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma krange_bounds : forall e lo hi, In (KRange e lo hi) (kn cs) -> lo <= u (edenot E e) <= hi.
  Proof. intros e lo hi HK. destruct (kn_fact _ HK) as [H1 H2]. lia. Qed.
  Lemma kalign_mod : forall e m, In (KAlign e m) (kn cs) -> u (edenot E e) mod m = 0.
  Proof. intros e m HK. destruct (kn_fact _ HK) as [_ H]. exact H. Qed.
  Lemma kdisj_apart : forall a1 n1 a2 n2, In (KDisj a1 n1 a2 n2) (kn cs) ->
    estart E a1 + elenZ E n1 <= estart E a2 \/ estart E a2 + elenZ E n2 <= estart E a1.
  Proof. intros a1 n1 a2 n2 HK. exact (kn_fact _ HK). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mapped_defined : forall lo hi,
    (forall i, lo <= i < hi -> APS.in_ivs i (vm_maps (m_vmmaps model)) = true /\ APS.in_ivs i (vm_noaccess (m_vmmaps model)) = false) ->
    0 <= lo -> hi <= 2 ^ 64 -> writableZ SEGS FULL lo hi.
  Proof.
    intros lo hi H H0 H1 i Hi. destruct (H i Hi) as [M N].
    assert (D : FULL (Z_to_bv 64 i) <> None).
    { apply (APS.co_mdef _ _ _ _ _ _ _ _ _ _ _ _ CS (Z_to_bv 64 i)); rewrite u64_lit by lia; assumption. }
    split; [exact D | apply store_ok1_some; exact D].
  Qed.
  Lemma defined_writableZ : forall lo hi, (forall i, lo <= i < hi -> FULL (Z_to_bv 64 i) <> None) -> writableZ SEGS FULL lo hi.
  Proof. intros lo hi H i Hi. split; [exact (H i Hi) | apply store_ok1_some; exact (H i Hi)]. Qed.
  (* [comment removed for export] *)
  Lemma rdn_offimg_defined : forall M (a : word) n bs, rdn SEGS M a n = Some bs -> u a + Z.of_nat n <= 2 ^ 64 ->
    (forall x : word, u a <= u x < u a + Z.of_nat n -> APS.in_hull A (u x) = false) ->
    forall x : word, u a <= u x < u a + Z.of_nat n -> M x <> None.
  Proof.
    intros M a n. revert a. induction n as [|n IH]; intros a bs Hr Hn Hoff x Hx; [lia|].
    cbn [rdn] in Hr.
    destruct (Z.eq_dec (u x) (u a)) as [Ex|NE].
    - assert (x = a) by (apply bv_eq; exact Ex). subst x. destruct (M a) as [b|] eqn:Ma; [discriminate|].
      exfalso. unfold seg_rom, memory_read in Hr. change (Z.of_N 1) with 1 in Hr. rewrite (SEGS_in_hull a (Hoff a ltac:(lia))) in Hr. discriminate Hr.
    - destruct (match M a with Some b => Some b | None => seg_rom SEGS a end) as [b|]; [| discriminate Hr].
      destruct (rdn SEGS M (a + 1)%bv n) as [rest|] eqn:Hr2; [| discriminate Hr].
      pose proof (u64_range x) as Rx. pose proof (u64_range a) as Ra.
      assert (Hu1 : u (a + 1)%bv = u a + 1) by (apply u_add1; lia).
      apply (IH (a + 1)%bv rest Hr2); [rewrite Hu1; lia | intros y Hy; apply Hoff; rewrite Hu1 in Hy; lia | rewrite Hu1; lia].
  Qed.
  Lemma kword_defined : forall b o w v, In (KWord (SA b o) w v) (kn cs) ->
    (forall i, estart E (SA b o) <= i < estart E (SA b o) + Z.of_nat w -> APS.in_hull A i = false) ->
    forall i, estart E (SA b o) <= i < estart E (SA b o) + Z.of_nat w -> FULL (Z_to_bv 64 i) <> None.
  Proof.
    intros b o w v HK Hoff i Hi. destruct (kword_cellZ b o w v HK) as [Hf C]. unfold cellN in C.
    pose proof Hf as (F1 & F2 & F3 & F4).
    pose proof (rdn_offimg_defined FULL (Z_to_bv 64 (estart E (SA b o))) w _ C) as D. rewrite u64_lit in D by lia.
    specialize (D ltac:(lia) ltac:(intros x Hx; apply Hoff; exact Hx) (Z_to_bv 64 i)). rewrite u64_lit in D by lia. exact (D Hi).
  Qed.
End MainLib.

(* [comment removed for export] *)
Arguments KN {SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model} CS.
Arguments kn_fact {SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model} CS K _.
Arguments HOFF {SEGS A argH ISP} SEGS_in_hull HULL_ok argH_high E cs model a _.
Arguments rdn_full {SEGS A argH ISP} SEGS_in_hull HULL_ok argH_high E cs FULL model a w bs _.
Arguments Mr_some {A argH E cs FULL model} a b _.
Arguments kword_cellZ {SEGS A LIMIT SINV argH ISP FS0} SEGS_in_hull HULL_ok argH_high {E cs R FULL model} CS b o w v _.
Arguments kword_cellZ_lit {SEGS A LIMIT SINV argH ISP FS0} SEGS_in_hull HULL_ok argH_high {E cs R FULL model} CS b o w z _ _.
Arguments kzero_bytes {SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model} CS b o n _ _.
Arguments kzero_fillZ {SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model} CS b o n _ _.
Arguments kfill_fillZ {SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model} CS b o n c _ _ _ i _.
Arguments kimg_none {SEGS A LIMIT SINV argH ISP FS0} HULL_ok argH_high {E cs R FULL model} CS lo hi _ i _ _.
Arguments cellZ_rom {SEGS FULL} a n v _ _ _ _.
Arguments krange_bounds {SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model} CS e lo hi _.
Arguments kalign_mod {SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model} CS e m _.
Arguments kdisj_apart {SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model} CS a1 n1 a2 n2 _.
Arguments mapped_defined {SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model} CS lo hi _ _ _ i _.
Arguments defined_writableZ {SEGS FULL} lo hi _ i _.
Arguments rdn_offimg_defined {SEGS A} SEGS_in_hull M a n bs _ _ _ x _.
Arguments kword_defined {SEGS A LIMIT SINV argH ISP FS0} SEGS_in_hull HULL_ok argH_high {E cs R FULL model} CS b o w v _ _ i _.

(* [comment removed for export] *)
Lemma kbase_lmin : AsAinvDefs3.KBASE + AsAinvDefs3.ROOMSLACK <= StoreOk.RunLim.LMIN.
Proof.
  eapply Z.le_trans; [| exact AsAinvDefs3.budget_closed].
  vm_compute. intros H; discriminate H.
Qed.
