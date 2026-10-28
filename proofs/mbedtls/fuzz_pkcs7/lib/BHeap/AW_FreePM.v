(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Sorting.Permutation.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX AModelC24 APop AW_FreeP AW_FreeK AW_FreeG AW_FreeR AW_FreeRM.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_FreePM () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_region"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.wf_chunks'"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_user"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_n"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeG.ext_hi"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "Corelib.Numbers.BinNums.Z"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.flat_map"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_elems"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AH"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cache"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.quar_ab"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_ab"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.QC"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_bytes"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.DP"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.hgeom"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pc_chunks"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.carved"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk_at"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeG.ext_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.WFR"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kBatchClass"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_addr"; "ARUN_1.PutN.putN_cache"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

#[using="Type"] Lemma chunk_eq_dec : forall k1 k2 : chunk, {k1 = k2} + {k1 <> k2}.
Proof.
  intros [a1 n1 p1 c1 s1] [a2 n2 p2 c2 s2].
  destruct (Z.eq_dec a1 a2); [| right; congruence]. destruct (Z.eq_dec n1 n2); [| right; congruence]. destruct (Bool.bool_dec p1 p2); [| right; congruence].
  destruct (Z.eq_dec c1 c2); [| right; congruence]. destruct (Z.eq_dec s1 s2); [| right; congruence]. left. subst. reflexivity.
Qed.

#[using="Type"] Lemma fold_add_base : forall (l : list Z) a, fold_right Z.add a l = fold_right Z.add 0 l + a.
Proof. induction l as [|x l IH]; intros a; cbn; [lia|]. rewrite (IH a), (IH 0). lia. Qed.

(* [comment removed for export] *)
Definition quar (k : chunk) : chunk := CK (ck_ab k) (ck_n k) (ck_prim k) (ck_cls k) CHUNK_QUARANTINE.

#[using="Type"] Lemma quar_ab_In : forall ab ks k', In k' (quar_ab ab ks) <-> exists k0, In k0 ks /\ k' = (if ck_ab k0 =? ab then quar k0 else k0).
Proof.
  intros ab ks k'. unfold quar_ab, quar. rewrite in_map_iff. split.
  - (intros dd_H; ddestruct dd_H as (k0 & E & H)). exists k0. split; [exact H| symmetry; exact E].
  - (intros dd_H; ddestruct dd_H as (k0 & H & ->)). exists k0. split; [reflexivity| exact H].
Qed.

#[using="Type"] Lemma quar_ab_map_ab : forall ab ks, map ck_ab (quar_ab ab ks) = map ck_ab ks.
Proof. intros ab ks. unfold quar_ab. rewrite map_map. apply map_ext. intros k0. destruct (ck_ab k0 =? ab); reflexivity. Qed.


#[using="Type"] Lemma find_map_inv : forall {A} (f : A -> A) (p : A -> bool) l, (forall x, p (f x) = p x) -> find p (map f l) = option_map f (find p l).
Proof. intros A f p l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite H. destruct (p x); [reflexivity| exact IH]. Qed.

#[using="Type"] Lemma find_hdr_quar_ab : forall ab ks e,
  find (fun k0 => ck_hdr k0 =? e) (quar_ab ab ks) = option_map (fun k0 => if ck_ab k0 =? ab then quar k0 else k0) (find (fun k0 => ck_hdr k0 =? e) ks).
Proof. intros ab ks e. unfold quar_ab. apply find_map_inv. intros x. destruct (ck_ab x =? ab); reflexivity. Qed.

#[using="Type"] Lemma used_size_quar_ab : forall ab ks e,
  match find (fun k0 => ck_hdr k0 =? e) (quar_ab ab ks) with Some k0 => used_size (ck_n k0) | None => 0 end
  = match find (fun k0 => ck_hdr k0 =? e) ks with Some k0 => used_size (ck_n k0) | None => 0 end.
Proof. intros ab ks e. rewrite find_hdr_quar_ab. destruct (find _ ks) as [k0|]; [cbn; destruct (ck_ab k0 =? ab); reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma user_round_le_ext : ltac2:(CDefT.buildp (gd_tbl_AW_FreePM ()) "Ph,$0.Pk,$1.P,(2.VhAR,(3.R2.))P,(4.R3.)P,(5.VhAR,R4.)P,(6.$1.R4.(7.R5.))(8.(9.(:.R5.)(;.+8.(<.(9.(=.(>.R5.))+7.)+8.)))(?.R5.))")
(* [comment removed for export] *).
Proof.
  (intros h k WL WR dd_H; ddestruct dd_H as (WKF & _ & _); intros Hk). pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (WN & WST & WP & WX).
  unfold AW_FreeG.ext_hi, ck_end, ck_user, ck_rz, nfix. pose proof (rz_size_bound' (ck_n k)) as RZ.
  destruct (ck_prim k) eqn:PK.
  - ddestruct WX as (ECLS & C30 & _). rewrite ECLS. destruct (Z.eq_dec (ck_n k) 0) as [E0|NZ].
    + rewrite E0 in *. pose proof (user_end_prim 0 ltac:(lia) ltac:(symmetry; exact WP)) as [U _]. change ((Z.max 0 1 + 7) / 8) with 1. cbn [pclass] in U |- *. lia.
    + pose proof (user_end_prim8 (ck_n k) ltac:(lia) ltac:(symmetry; exact WP)) as U. replace (Z.max (ck_n k) 1) with (ck_n k) by lia. lia.
  - unfold ck_map_beg, ck_map_size, sec_map_size, needed2. rewrite <- WP. unfold needed.
    pose proof (round_up_spec (rounded (ck_n k) + rz_size (ck_n k) + rz_size (ck_n k)) 4096 ltac:(lia)) as [R1 _].
    unfold rounded in *. pose proof (round_up_spec (Z.max (ck_n k) 8) 8 ltac:(lia)) as [[R2 R2'] R3].
    pose proof (Z.div_mod (Z.max (ck_n k) 1 + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max (ck_n k) 1 + 7) 8 ltac:(lia)).
    pose proof (Z.div_mod (round_up (Z.max (ck_n k) 8) 8) 8 ltac:(lia)). rewrite R3, Z.add_0_r in H1. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma elems_owner_unique : ltac2:(CDefT.buildp (gd_tbl_AW_FreePM ()) "PL,(10.$11.)Pb,$11.Pb2,$11.Pe,$12.P,(13.$12.(14.$11.$12.$15.R4.))P,(6.$11.R4.R5.)P,(6.$11.R4.R6.)P,(6.$12.R4.(15.R6.))P,(6.$12.R5.(15.R6.))(16.$11.R8.R7.)")
(* [comment removed for export] *).
Proof.
  induction L as [|x L IH]; intros b b2 e ND Hb Hb2 He He2; [destruct Hb|]. cbn in ND.
  pose proof (NoDup_app_remove_r _ _ ND) as NDx. pose proof (NoDup_app_remove_l _ _ ND) as NDL.
  destruct Hb as [<-|Hb], Hb2 as [<-|Hb2]; [reflexivity| | | exact (IH b b2 e NDL Hb Hb2 He He2)].
  - exfalso. apply (NoDup_app_l_r _ _ e ND He). apply in_flat_map. exists b2. auto.
  - exfalso. apply (NoDup_app_l_r _ _ e ND He2). apply in_flat_map. exists b. auto.
Qed.

#[using="Type"] Lemma NoDup_insert_mid : forall (l1 l2 : list Z) x, NoDup (l1 ++ l2) -> ~ In x (l1 ++ l2) -> NoDup (l1 ++ x :: l2).
Proof.
  intros l1 l2 x ND NI. apply (Permutation_NoDup (Permutation_middle l1 l2 x)). constructor; [exact NI| exact ND].
Qed.

#[using="Type"] Lemma snoc_case : forall {A} (l : list A), l = [] \/ exists l' x, l = l' ++ [x].
Proof.
  intros A l. induction l as [|a l IH] using rev_ind; [left; reflexivity|]. right. dexists l, a. reflexivity.
Qed.

Section PutP.
  Variables (h : ahst) (k : chunk) (tq0 : list batch) (lb : batch) (N' tf' : Z) (nb' bl' : list Z).
  Let nx := nfix (ck_n k).
  Let lb' := BA (b_addr lb) (b_elems lb ++ [ck_hdr k]) (b_size lb + nx).
  Definition h_putP : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreePM ()) "(17.(3.Vh,)(18.Vh,)(19.Vh,)(1:.Vh,)(1;.(1<.Vk,)(7.Vh,))(1=.(1>.$11.Vtq0,(1?.$11.Vlb',(20.$11.)))(9.(21.(22.Vh,))Vnx,))(23.Vh,)(24.Vh,)(25.VN',Vnb',Vtf',Vbl',)$26.(27.Vh,)(28.Vh,)(29.Vh,)(2:.Vh,))")
(* [comment removed for export] *).   (* [comment removed for export] *)
  Let h' := h_putP.

  Hypothesis WF : awf' h.
  Hypothesis GEO : hgeom h.
  Hypothesis Hk : In k (h_chunks h).
  Hypothesis STA : ck_st k = CHUNK_ALLOCATED.
  Hypothesis HB : q_batches (h_tq h) = tq0 ++ [lb].
  Hypothesis ROOM : (length (b_elems lb) < 1021)%nat.
  (* [comment removed for export] *)
  Hypothesis DN : d_n (h_dep h) <= N' <= d_n (h_dep h) + 1.
  Hypothesis DTF : s_total (h_dep h) <= tf'.
  Hypothesis DLN : Z.of_nat (length nb') = N' / 65536 + 1.
  Hypothesis DWN : Forall (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb'.
  Hypothesis DLB : Z.of_nat (length bl') = (tf' + 2^20 - 1) / 2^20.
  Hypothesis DWB : Forall (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl'.
  Hypothesis DLNB : Z.of_nat (length nb') <= 32768.
  Hypothesis DLBB : Z.of_nat (length bl') <= 4096.

  #[using="hAR WF Hk"] Lemma putP_chunks_In : forall k', In k' (h_chunks h') <-> k' = quar k \/ (In k' (h_chunks h) /\ k' <> k).
  Proof.
    intros k'. dpose WF as (_ & _ & _ & (_ & ND & _) & _). cbn [h_chunks h' h_putP]. rewrite quar_ab_In. split.
    - (intros dd_H; ddestruct dd_H as (k0 & H0 & ->)). destruct (Z.eqb_spec (ck_ab k0) (ck_ab k)) as [E|NE].
      + left. rewrite (NoDup_map_inj ck_ab _ _ _ ND H0 Hk E). reflexivity.
      + right. split; [exact H0|]. intros ->. exact (NE eq_refl).
    - intros [->|[H0 NE]].
      + exists k. rewrite Z.eqb_refl. split; [exact Hk| reflexivity].
      + exists k'. split; [exact H0|]. destruct (Z.eqb_spec (ck_ab k') (ck_ab k)) as [E|_]; [| reflexivity].
        exfalso. exact (NE (NoDup_map_inj ck_ab _ _ _ ND H0 Hk E)).
  Qed.

  (* [comment removed for export] *)
  #[using="hAR WF GEO Hk STA"] Lemma hdr_fresh : forall b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) -> ~ In (ck_hdr k) (b_elems b).
  Proof.
    intros b Hb Hin. dpose WF as ([WL _] & _ & WR & WK & WQ & _). dpose WQ as ((T1 & _) & (G1 & _) & _).
    assert (WBb : wf_batch h b).
    { apply in_app_iff in Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) T1 b Hb)| exact (proj1 (Forall_forall _ _) G1 b Hb)]. }
    ddestruct WBb as (_ & _ & B3 & _). destruct (proj1 (Forall_forall _ _) B3 _ Hin) as (k2 & Hk2 & S2 & E2).
    pose proof (hdr_unique h k2 k WL WR WK GEO Hk2 Hk E2) as ->. rewrite STA in S2. discriminate S2.
  Qed.

  #[using="hAR WF Hk STA"] Lemma wf_batch_kept : forall b, wf_batch h b -> wf_batch h' b.
  Proof.
    (intros b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4)). dpose WF as (_ & _ & _ & (_ & ND & _) & _). split; [exact B1|]. split; [| split].
    - cbn [h_chunks h' h_putP]. rewrite B2. f_equal. f_equal. apply map_ext_in. intros e He. symmetry. apply used_size_quar_ab.
    - apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) B3 e He) as (k2 & Hk2 & S2 & E2). destruct (chunk_eq_dec k2 k) as [->|NE].
      + rewrite STA in S2. discriminate S2.
      + exists k2. split; [apply (proj2 (putP_chunks_In k2)); right; exact (conj Hk2 NE)| exact (conj S2 E2)].
    - unfold carved in *. cbn [h_reg h_L h' h_putP]. exact B4.
  Qed.

  #[using="Type"] Lemma chunk_set_putP : forall c, chunk_set h' c = chunk_set h c.
  Proof.
    clear. intros c. unfold chunk_set. cbn [h_chunks h_L h' h_putP]. unfold quar_ab. induction (h_chunks h) as [|x l IH]; [reflexivity|]. cbn [map].
    destruct (ck_ab x =? ck_ab k); cbn [List.filter ck_prim ck_cls quar]; destruct (ck_prim x && (ck_cls x =? c)); cbn [map ck_ab]; rewrite IH; reflexivity.
  Qed.
  #[using="HB"] Lemma batch_set_putP : forall c, batch_set h' c = batch_set h c.
  Proof. intros c. unfold batch_set. cbn [h_tq h_gq h_L h' h_putP q_batches]. destruct (c =? kBatchClass); [| reflexivity]. rewrite HB, !map_app. reflexivity. Qed.
  #[using="HB"] Lemma owned_putP : forall c, owned h' c = owned h c.
  Proof. intros c. unfold owned. rewrite chunk_set_putP, batch_set_putP. reflexivity. Qed.

  #[using="hAR WF GEO Hk STA"] Lemma blocks_putP : blocks h' = lb_remove (ck_user k) (blocks h).
  Proof.
    dpose WF as ([WL _] & _ & WR & WK & _). dpose WK as (_ & ND & _).
    unfold blocks, live. cbn [h_chunks h' h_putP]. unfold quar_ab.
    set (qa := fun k0 => if ck_ab k0 =? ck_ab k then quar k0 else k0). set (f := fun k0 : chunk => (ck_user k0, ck_n k0)). set (al := fun k0 => ck_st k0 =? CHUNK_ALLOCATED).
    assert (QID : forall l, (forall y, In y l -> ck_ab y <> ck_ab k) -> map qa l = l).
    { induction l as [|y l IH]; intros H; [reflexivity|]. cbn [map]. rewrite (IH ltac:(intros z Hz; apply H; right; exact Hz)).
      subst qa. cbn beta. destruct (Z.eqb_spec (ck_ab y) (ck_ab k)) as [E|NE]; [exfalso; exact (H y ltac:(left; reflexivity) E)| reflexivity]. }
    assert (GEN : forall l, incl l (h_chunks h) -> NoDup (map ck_ab l) -> In k l ->
              map f (List.filter al (map qa l)) = lb_remove (ck_user k) (map f (List.filter al l))).
    { induction l as [|x l IH]; intros INC NDl Hkl; [destruct Hkl|]. cbn [map List.filter]. cbn in NDl. inversion NDl as [|? ? NI ND']; subst.
      assert (INC' : incl l (h_chunks h)) by (intros z Hz; apply INC; right; exact Hz).
      destruct (chunk_eq_dec x k) as [->|NX].
      - replace (qa k) with (quar k) by (subst qa; cbn beta; rewrite Z.eqb_refl; reflexivity).
        replace (al (quar k)) with false by reflexivity. replace (al k) with true by (subst al; cbn beta; rewrite STA; reflexivity).
        cbn [map lb_remove fst f]. rewrite Z.eqb_refl. rewrite QID; [reflexivity|]. intros y Hy E. apply NI. rewrite <- E. apply in_map. exact Hy.
      - destruct Hkl as [E|Hkl]; [exfalso; exact (NX E)|].
        replace (qa x) with x by (subst qa; cbn beta; destruct (Z.eqb_spec (ck_ab x) (ck_ab k)) as [E|_]; [exfalso; apply NI; rewrite E; apply in_map; exact Hkl| reflexivity]).
        destruct (al x); cbn [map lb_remove fst f]; [| exact (IH INC' ND' Hkl)].
        destruct (Z.eqb_spec (ck_user x) (ck_user k)) as [EU|NU].
        + exfalso. apply NX. apply (hdr_unique h x k WL WR WK GEO (INC x ltac:(left; reflexivity)) Hk). unfold ck_hdr. rewrite EU. reflexivity.
        + f_equal. exact (IH INC' ND' Hkl). }
    exact (GEN (h_chunks h) (incl_refl _) ND Hk).
  Qed.

  #[using="WF GEO Hk STA HB ROOM DN DTF DLN DWN DLB DWB DLNB DLBB"] Theorem WFC_putP : WFC h' (q_bytes (h_tq h) + nx) kQuarantineMax.
  Proof.
    dpose WF as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG). dpose WK as (WKF & ND & WKSEC). pose proof WL as [WL0 _].
    dpose WQ as ((T1 & T2 & T3) & WGQ & NDA & UQ). rewrite HB in T1, T2, NDA. apply Forall_app in T1 as [T1a T1b]. inversion T1b as [|? ? WLB _]; subst.
    pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (WN & _ & WP & WXk).
    assert (ENX : nx = nfix (ck_n k)) by reflexivity. assert (NX1 : 1 <= nx) by (rewrite ENX; unfold nfix; lia).
    (* [comment removed for export] *)
    assert (NDE : NoDup (flat_map b_elems ((tq0 ++ [lb']) ++ q_batches (h_gq h)))).
    { dpose WX as (_ & X2 & _). rewrite HB in X2. rewrite <- app_assoc in X2 |- *. rewrite !flat_map_app in X2 |- *. cbn [flat_map b_elems lb'] in X2 |- *.
      rewrite app_nil_r in X2 |- *. rewrite <- app_assoc. cbn [app]. rewrite (app_assoc (flat_map b_elems tq0)).
      replace (flat_map b_elems tq0 ++ (b_elems lb ++ ck_hdr k :: flat_map b_elems (q_batches (h_gq h))))
        with ((flat_map b_elems tq0 ++ b_elems lb) ++ ck_hdr k :: flat_map b_elems (q_batches (h_gq h))) by (rewrite <- app_assoc; reflexivity).
      apply NoDup_insert_mid; [rewrite <- app_assoc; exact X2|].
      intros IN. rewrite <- app_assoc in IN. apply in_app_iff in IN as [IN|[IN|IN]%in_app_iff].
      - apply in_flat_map in IN as (b & Hb & He). apply (hdr_fresh b); [rewrite HB; apply in_app_iff; left; apply in_app_iff; left; exact Hb| exact He].
      - apply (hdr_fresh lb); [rewrite HB; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity| exact IN].
      - apply in_flat_map in IN as (b & Hb & He). apply (hdr_fresh b); [rewrite HB; apply in_app_iff; right; exact Hb| exact He]. }
    split; [exact WL|].
    split; [exact WC|].
    split. { intros c Hc. pose proof (WR c Hc) as X. cbn zeta in X |- *. rewrite owned_putP. exact X. }
    split. { (* [comment removed for export] *)
      split; [| split].
      - apply Forall_forall. intros k' Hk'. apply putP_chunks_In in Hk' as [->|[Hk' _]].
        + unfold wf_chunk', quar. cbn [ck_n ck_st ck_prim ck_cls ck_ab ck_map_beg ck_map_size h_sec h_L h' h_putP carved h_reg].
          split; [exact WN|]. split; [right; reflexivity|]. split; [exact WP|]. unfold ck_map_beg, ck_map_size in WXk. exact WXk.
        + pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as X. unfold wf_chunk' in *. cbn [h_sec h_L h' h_putP carved h_reg]. exact X.
      - cbn [h_chunks h' h_putP]. rewrite quar_ab_map_ab. exact ND.
      - cbn [h_sec h_chunks h' h_putP]. intros i sh Hi. ddestruct (WKSEC i sh Hi) as (k2 & Hk2 & P2 & MB & MS).
        destruct (chunk_eq_dec k2 k) as [->|NE].
        + exists (quar k). split; [apply (proj2 (putP_chunks_In _)); left; reflexivity|]. cbn. unfold ck_map_beg, ck_map_size in *. cbn. exact (conj P2 (conj MB MS)).
        + exists k2. split; [apply (proj2 (putP_chunks_In _)); right; exact (conj Hk2 NE)| exact (conj P2 (conj MB MS))]. }
    split. { (* [comment removed for export] *)
      split; [| split; [| split]].
      - (* [comment removed for export] *)
        cbn [h_tq h' h_putP q_batches q_bytes]. split; [| split].
        + apply Forall_app. split; [apply Forall_forall; intros b Hb; apply wf_batch_kept; exact (proj1 (Forall_forall _ _) T1a b Hb)|].
          constructor; [| constructor]. ddestruct WLB as (B1 & B2 & B3 & B4). split; [| split; [| split]].
          * unfold b_count in *. cbn [b_elems lb']. rewrite length_app. cbn [length]. unfold kBatchCap in *. clear - B1 ROOM. lia.
          * cbn [b_size b_elems lb'].
            assert (FK : find (fun k0 => ck_hdr k0 =? ck_hdr k) (h_chunks h') = Some (quar k)).
            { cbn [h_chunks h' h_putP]. rewrite find_hdr_quar_ab.
              destruct (find (fun k0 => ck_hdr k0 =? ck_hdr k) (h_chunks h)) as [k2|] eqn:FD.
              -- apply find_some in FD as [Hk2 E2]. apply Z.eqb_eq in E2. pose proof (hdr_unique h k2 k WL0 WR WK GEO Hk2 Hk E2) as ->. cbn. rewrite Z.eqb_refl. reflexivity.
              -- exfalso. pose proof (find_none _ _ FD k Hk) as X. cbn beta in X. rewrite Z.eqb_refl in X. discriminate X. }
            dpose (wf_batch_kept lb (conj B1 (conj B2 (conj B3 B4)))) as (_ & B2' & _). cbn [b_size b_elems] in B2'.
            unfold used_size in *. rewrite map_app, sum_app. cbn [map]. rewrite FK. cbn [ck_n quar]. set (S1 := sum (map _ (b_elems lb))) in *.
            cbn [sum fold_right]. rewrite ENX. clear - B2'. lia.
          * cbn [b_elems lb']. apply Forall_app. split.
            -- apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) B3 e He) as (k2 & Hk2 & S2 & E2). destruct (chunk_eq_dec k2 k) as [->|NE]; [rewrite STA in S2; discriminate S2|].
               exists k2. split; [apply (proj2 (putP_chunks_In _)); right; exact (conj Hk2 NE)| exact (conj S2 E2)].
            -- constructor; [| constructor]. exists (quar k). split; [apply (proj2 (putP_chunks_In _)); left; reflexivity| split; reflexivity].
          * unfold carved in *. cbn [b_addr lb' h_reg h_L h' h_putP]. exact B4.
        + cbn [q_batches q_bytes]. unfold sum in *. rewrite map_app, fold_right_app. cbn [map fold_right b_size lb']. rewrite T2, map_app, fold_right_app. cbn [map fold_right]. rewrite (fold_add_base (map b_size tq0) (b_size lb + 0)), (fold_add_base (map b_size tq0) (b_size lb + nx + 0)). clear. lia.
        + cbn [q_batches q_bytes]. pose proof T3. lia.
      - (* [comment removed for export] *)
        cbn [h_gq h' h_putP]. ddestruct WGQ as (G1 & G2 & G3). split; [| exact (conj G2 G3)]. apply Forall_forall. intros b Hb. apply wf_batch_kept. exact (proj1 (Forall_forall _ _) G1 b Hb).
      - cbn [h_tq h_gq h' h_putP q_batches]. rewrite !map_app in NDA |- *. cbn [map b_addr lb'] in NDA |- *. exact NDA.
      - (* [comment removed for export] *)
        cbn [h_tq h_gq h' h_putP q_batches]. intros k' Hk' S'.
        assert (EX : exists b, In b ((tq0 ++ [lb']) ++ q_batches (h_gq h)) /\ In (ck_hdr k') (b_elems b)).
        { apply putP_chunks_In in Hk' as [->|[Hk' NE]].
          - exists lb'. split; [apply in_app_iff; left; apply in_app_iff; right; left; reflexivity| cbn [b_elems lb']; apply in_app_iff; right; left; reflexivity].
          - ddestruct (UQ k' Hk' S') as (b & [Hb Hin] & _). rewrite HB in Hb. rewrite <- app_assoc in Hb. apply in_app_iff in Hb as [Hb|[<-|Hb]].
            + exists b. split; [rewrite <- app_assoc; apply in_app_iff; left; exact Hb| exact Hin].
            + exists lb'. split; [rewrite <- app_assoc; apply in_app_iff; right; left; reflexivity| cbn [b_elems lb']; apply in_app_iff; left; exact Hin].
            + exists b. split; [rewrite <- app_assoc; apply in_app_iff; right; right; exact Hb| exact Hin]. }
        ddestruct EX as (b & Hb & Hin). exists b. split; [exact (conj Hb Hin)|]. intros b2 [Hb2 Hin2]. exact (elems_owner_unique _ b b2 (ck_hdr k') NDE Hb Hb2 Hin Hin2). }
    split; [exact WS|].
    split. { (* [comment removed for export] *)
      ddestruct WD as (N1 & _ & _ & T0 & _). unfold wf_depot'. cbn [h_dep h' h_putP d_n d_nb s_total d_bl]. unfold kDepotNodesL2 in *.
      repeat split; try assumption; lia. }
    split; [exact WB|].
    split; [exact WBIG|].
    split. { (* [comment removed for export] *)
      ddestruct WX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9). split; [exact X1|].
      split; [| split; [exact X3| split; [exact X4| split; [exact X5| split; [exact X6| split; [exact X7| split; [exact X8|]]]]]]].
      - cbn [h_tq h_gq h' h_putP q_batches]. exact NDE.
      - (* [comment removed for export] *)
        rewrite !blocks_blk_of. cbn [h_chunks h' h_putP]. unfold quar_ab. eapply Z.le_trans; [apply cnt24_blk_map| exact X9].
        intros k0 ST. destruct (ck_ab k0 =? ck_ab k); [cbn [ck_st] in ST; cbv in ST; discriminate ST| reflexivity]. }
    exact WG.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma kview_putP : kview_eq (hdep h nb' bl') h'.
  Proof. clear. unfold kview_eq, hdep, set_dep. cbn. repeat split; reflexivity. Qed.

                  End PutP.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma cache_code_slot : forall c q kq, 1 <= c <= 31 -> 16 * q = kq * class_size c -> q = kq * (class_size c / 16).
Proof.
  intros c q kq Hc E. pose proof (class_size_mod16 c Hc) as M. pose proof (Z.div_mod (class_size c) 16 ltac:(lia)) as D. rewrite M, Z.add_0_r in D.
  rewrite D in E. lia.
Qed.

#[using="Type"] Lemma cache_vs_chunk : ltac2:(CDefT.buildp (gd_tbl_AW_FreePM ()) "Ph,$0.Pc,$12.Pq,$12.Pkq,$12.Pk',$1.P,(2.VhAR,(3.R5.))P,(4.R6.)P,(5.VhAR,R7.)P,(2;.R8.)P,(2<.(8.+1.R8.)(8.R8.+1>.))P,(6.$12.R8.(2=.(19.R:.R9.)))P,(2<.(8.=R8.)(2>.R8.(2?.R;.R:.)))P,(16.$12.(;.+10.R:.)(;.R9.(30.R;.)))P,(6.$1.R9.(7.R=.))(31.(8.(?.R:.)(32.(3.R>.)R=.R;.))(8.(9.(32.(3.R>.)R=.R;.)(30.R=.))(33.R:.)))")
(* [comment removed for export] *).
Proof.
  intros h c q kq k' WL WR WK GEO Hc Hq Hkq EQ Hk'.
  pose proof (WR c ltac:(unfold kNumClasses; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU & AUCS & _ & MULIM & _ & _ & _ & _ & _ & NDO & _).
  destruct (slot_le h c kq WR ltac:(lia) Hkq) as [S1 S2]. pose proof (class_size_range c ltac:(lia)) as CSR.
  pose proof (cache_code_slot c q kq ltac:(lia) EQ) as EQ'.
  ddestruct (chunk_ext' h k' WL WR WK Hk') as (_ & F1 & F2 & F3 & F4 & _ & _ & [(P' & C' & RL' & RH' & i' & Hi' & EL' & EH')|(P' & i' & Ni' & EL' & EH')]).
  - destruct (Z.eq_dec (ck_cls k') c) as [EC|NC].
    + rewrite EC in RL', RH', Hi', EL', EH'. rewrite EL', EH'.
      assert (NEI : i' <> kq).
      { intros ->. apply (owned_cache_not_chunk h c q NDO); [unfold cache_set; exact Hq|].
        replace q with (compact (h_L h) c (ck_ab k')); [exact (in_chunk_set h c k' Hk' P' EC)|].
        unfold ext_lo in EL'. rewrite P' in EL'. rewrite EL', compact_chunk_at by (apply class_size_mod16; lia). lia. }
      unfold chunk_at. destruct (proj1 (Z.lt_gt_cases i' kq) NEI) as [LT|GT].
      * left. pose proof (Z.mul_le_mono_nonneg_r (i' + 1) kq (class_size c) ltac:(lia) ltac:(lia)). lia.
      * right. pose proof (Z.mul_le_mono_nonneg_r (kq + 1) i' (class_size c) ltac:(lia) ltac:(lia)). lia.
    + pose proof (user_vs_user h c (ck_cls k') WR ltac:(lia) ltac:(lia) ltac:(congruence)) as UU.
      pose proof (WR (ck_cls k') ltac:(unfold kNumClasses; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _). lia.
  - pose proof (z_sec_hull h GEO i' _ Ni') as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y.
    destruct (user_in_hull h c (chunk_at (h_L h) c kq) WL WR ltac:(lia) ltac:(lia)) as (HU1 & _).
    destruct (user_in_hull h c (chunk_at (h_L h) c kq + class_size c - 1) WL WR ltac:(lia) ltac:(lia)) as (HU2 & _). lia.
Qed.

#[using="Type"] Lemma cache_vs_batch : ltac2:(CDefT.buildp (gd_tbl_AW_FreePM ()) "Ph,$0.Pq,$12.Pkq,$12.Pb,$11.P,(34.VhAR,R4.)P,(6.$12.R4.(2=.(19.R5.$35.)))P,(2<.(8.=R4.)(2>.R4.(2?.R6.$35.)))P,(16.$12.(;.+10.R6.)(;.R5.+2000.))P,(6.$11.R5.(1>.$11.(36.(22.R8.))(36.(23.R8.))))(31.(8.(9.(37.R6.)+2000.)(32.(3.R9.)$35.R7.))(8.(9.(32.(3.R9.)$35.R7.)+2000.)(37.R6.)))")
(* [comment removed for export] *).
Proof.
  intros h q kq b WF Hq Hkq EQ Hb. dpose WF as (_ & _ & WR & _).
  pose proof (WR kBatchClass ltac:(unfold kBatchClass, kNumClasses; lia)) as X. cbn zeta in X. ddestruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDO & _).
  ddestruct (batch_slot h b WF Hb) as (i & Hi & EB). rewrite EB.
  assert (NEI : i <> kq).
  { intros ->. unfold owned in NDO. apply NoDup_app_remove_l in NDO. apply (NoDup_app_l_r _ _ q NDO); [unfold cache_set; exact Hq|].
    apply in_app_iff. right. unfold batch_set. rewrite Z.eqb_refl. apply in_map_iff. exists b. split; [| exact Hb].
    rewrite EB, compact_chunk_at by (unfold kBatchClass; reflexivity). unfold kBatchClass in *. change (class_size 24) with 8192 in *. change (8192 / 16) with 512. lia. }
  unfold chunk_at. unfold kBatchClass in *. change (class_size 24) with 8192 in *. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section PutN.
  Variables (h : ahst) (k : chunk) (q kq : Z) (N' tf' : Z) (nb' bl' : list Z).
  Let nx := nfix (ck_n k).
  Let p24 := h_cache h kBatchClass.
  Let baddr := chunk_at (h_L h) kBatchClass kq.
  Let nb0 := BA baddr [ck_hdr k] (nx + 8192).
  Definition putN_cache (j : Z) : pcl := if j =? kBatchClass then PC (pc_max p24) (pc_csize p24) (removelast (pc_chunks p24)) else h_cache h j.
  Definition h_putN : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreePM ()) "(17.(3.Vh,)(18.Vh,)$38.(1:.Vh,)(1;.(1<.Vk,)(7.Vh,))(1=.(1>.$11.(36.(22.Vh,))(1?.$11.Vnb0,(20.$11.)))(9.(21.(22.Vh,))(9.Vnx,+2000.)))(23.Vh,)(24.Vh,)(25.VN',Vnb',Vtf',Vbl',)$26.(27.Vh,)(28.Vh,)(29.Vh,)(2:.Vh,))")
(* [comment removed for export] *).
  Let h' := h_putN.

  Hypothesis WF : awf' h.
  Hypothesis GEO : hgeom h.
  Hypothesis Hk : In k (h_chunks h).
  Hypothesis STA : ck_st k = CHUNK_ALLOCATED.
  Hypothesis NE : pc_chunks p24 <> [].
  Hypothesis HQ : q = nth (length (pc_chunks p24) - 1) (pc_chunks p24) 0.
  Hypothesis HKQ : 0 <= kq < carved h kBatchClass /\ 16 * q = kq * 8192.
  Hypothesis DN : d_n (h_dep h) <= N' <= d_n (h_dep h) + 1.
  Hypothesis DTF : s_total (h_dep h) <= tf'.
  Hypothesis DLN : Z.of_nat (length nb') = N' / 65536 + 1.
  Hypothesis DWN : Forall (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb'.
  Hypothesis DLB : Z.of_nat (length bl') = (tf' + 2^20 - 1) / 2^20.
  Hypothesis DWB : Forall (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl'.
  Hypothesis DLNB : Z.of_nat (length nb') <= 32768.
  Hypothesis DLBB : Z.of_nat (length bl') <= 4096.

  #[using="NE HQ"] Lemma pop24_split : pc_chunks p24 = removelast (pc_chunks p24) ++ [q].
  Proof. rewrite HQ, <- last_nth by exact NE. apply app_removelast_last. exact NE. Qed.

  #[using="hAR k N' tf' nb' bl' nx HKQ"] Lemma compact_baddr : compact (h_L h) kBatchClass baddr = q.
  Proof.
    unfold baddr. rewrite compact_chunk_at by (unfold kBatchClass; reflexivity). destruct HKQ as [_ E]. unfold kBatchClass in *.
    change (class_size 24) with 8192 in *. change (8192 / 16) with 512. lia.
  Qed.

  #[using="hAR WF Hk"] Lemma putN_chunks_In : forall k', In k' (h_chunks h') <-> k' = quar k \/ (In k' (h_chunks h) /\ k' <> k).
  Proof.
    intros k'. dpose WF as (_ & _ & _ & (_ & ND & _) & _). cbn [h_chunks h' h_putN]. rewrite quar_ab_In. split.
    - (intros dd_H; ddestruct dd_H as (k0 & H0 & ->)). destruct (Z.eqb_spec (ck_ab k0) (ck_ab k)) as [E|NEQ].
      + left. rewrite (NoDup_map_inj ck_ab _ _ _ ND H0 Hk E). reflexivity.
      + right. split; [exact H0|]. intros ->. exact (NEQ eq_refl).
    - intros [->|[H0 NEQ]].
      + exists k. rewrite Z.eqb_refl. split; [exact Hk| reflexivity].
      + exists k'. split; [exact H0|]. destruct (Z.eqb_spec (ck_ab k') (ck_ab k)) as [E|_]; [| reflexivity].
        exfalso. exact (NEQ (NoDup_map_inj ck_ab _ _ _ ND H0 Hk E)).
  Qed.

  #[using="hAR WF GEO Hk STA"] Lemma hdr_freshN : forall b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) -> ~ In (ck_hdr k) (b_elems b).
  Proof.
    intros b Hb Hin. dpose WF as ([WL _] & _ & WR & WK & WQ & _). dpose WQ as ((T1 & _) & (G1 & _) & _).
    assert (WBb : wf_batch h b).
    { apply in_app_iff in Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) T1 b Hb)| exact (proj1 (Forall_forall _ _) G1 b Hb)]. }
    ddestruct WBb as (_ & _ & B3 & _). destruct (proj1 (Forall_forall _ _) B3 _ Hin) as (k2 & Hk2 & S2 & E2).
    pose proof (hdr_unique h k2 k WL WR WK GEO Hk2 Hk E2) as ->. rewrite STA in S2. discriminate S2.
  Qed.

  #[using="hAR WF Hk STA"] Lemma wf_batch_keptN : forall b, wf_batch h b -> wf_batch h' b.
  Proof.
    (intros b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4)). dpose WF as (_ & _ & _ & (_ & ND & _) & _). split; [exact B1|]. split; [| split].
    - cbn [h_chunks h' h_putN]. rewrite B2. f_equal. f_equal. apply map_ext_in. intros e He. symmetry. apply used_size_quar_ab.
    - apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) B3 e He) as (k2 & Hk2 & S2 & E2). destruct (chunk_eq_dec k2 k) as [->|NEQ].
      + rewrite STA in S2. discriminate S2.
      + exists k2. split; [apply (proj2 (putN_chunks_In k2)); right; exact (conj Hk2 NEQ)| exact (conj S2 E2)].
    - unfold carved in *. cbn [h_reg h_L h' h_putN]. exact B4.
  Qed.

  #[using="Type"] Lemma chunk_set_putN : forall c, chunk_set h' c = chunk_set h c.
  Proof.
    clear. intros c. unfold chunk_set. cbn [h_chunks h_L h' h_putN]. unfold quar_ab. induction (h_chunks h) as [|x l IH]; [reflexivity|]. cbn [map].
    destruct (ck_ab x =? ck_ab k); cbn [List.filter ck_prim ck_cls quar]; destruct (ck_prim x && (ck_cls x =? c)); cbn [map ck_ab]; rewrite IH; reflexivity.
  Qed.
  #[using="Type"] Lemma cache_set_putN : forall c, cache_set h' c = (if c =? kBatchClass then removelast (pc_chunks p24) else cache_set h c).
  Proof. clear. intros c. unfold cache_set. cbn [h_cache h' h_putN]. unfold putN_cache. destruct (c =? kBatchClass); reflexivity. Qed.
  #[using="hAR HKQ"] Lemma batch_set_putN : forall c, Permutation (batch_set h' c) (if c =? kBatchClass then batch_set h c ++ [q] else batch_set h c).
  Proof.
    intros c. unfold batch_set. cbn [h_tq h_gq h_L h' h_putN q_batches]. destruct (Z.eqb_spec c kBatchClass) as [->|NEQ]; [| apply Permutation_refl].
    rewrite !map_app. cbn [map b_addr nb0]. rewrite compact_baddr, <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
  Qed.
  (* [comment removed for export] *)
  #[using="hAR q NE HQ HKQ"] Lemma owned_putN : forall c, Permutation (owned h' c) (owned h c).
  Proof.
    intros c. destruct (Z.eqb_spec c kBatchClass) as [Ec|NEQ].
    - subst c. unfold owned. rewrite chunk_set_putN, cache_set_putN, Z.eqb_refl. change (fa_set h' kBatchClass) with (fa_set h kBatchClass).
      pose proof (batch_set_putN kBatchClass) as PB. rewrite Z.eqb_refl in PB.
      unfold cache_set. fold p24. rewrite pop24_split at 2.
      transitivity (fa_set h kBatchClass ++ removelast (pc_chunks p24) ++ chunk_set h kBatchClass ++ (batch_set h kBatchClass ++ [q])); [do 3 apply Permutation_app_head; exact PB|].
      rewrite <- !app_assoc. do 2 apply Permutation_app_head. rewrite (app_assoc (chunk_set h kBatchClass)). cbn [app].
      apply Permutation_sym. apply Permutation_cons_append.
    - unfold owned. rewrite chunk_set_putN, cache_set_putN. replace (c =? kBatchClass) with false by (symmetry; apply Z.eqb_neq; exact NEQ).
      change (fa_set h' c) with (fa_set h c). pose proof (batch_set_putN c) as PB. replace (c =? kBatchClass) with false in PB by (symmetry; apply Z.eqb_neq; exact NEQ).
      do 3 apply Permutation_app_head. exact PB.
  Qed.

  #[using="hAR q WF GEO Hk STA HQ HKQ"] Lemma blocks_putN : blocks h' = lb_remove (ck_user k) (blocks h).
  Proof.
    dpose WF as ([WL _] & _ & WR & WK & _). dpose WK as (_ & ND & _).
    unfold blocks, live. cbn [h_chunks h' h_putN]. unfold quar_ab.
    set (qa := fun k0 => if ck_ab k0 =? ck_ab k then quar k0 else k0). set (f := fun k0 : chunk => (ck_user k0, ck_n k0)). set (al := fun k0 => ck_st k0 =? CHUNK_ALLOCATED).
    assert (QID : forall l, (forall y, In y l -> ck_ab y <> ck_ab k) -> map qa l = l).
    { induction l as [|y l IH]; intros H; [reflexivity|]. cbn [map]. rewrite (IH ltac:(intros z Hz; apply H; right; exact Hz)).
      subst qa. cbn beta. destruct (Z.eqb_spec (ck_ab y) (ck_ab k)) as [E|NEQ]; [exfalso; exact (H y ltac:(left; reflexivity) E)| reflexivity]. }
    assert (GEN : forall l, incl l (h_chunks h) -> NoDup (map ck_ab l) -> In k l ->
              map f (List.filter al (map qa l)) = lb_remove (ck_user k) (map f (List.filter al l))).
    { induction l as [|x l IH]; intros INC NDl Hkl; [destruct Hkl|]. cbn [map List.filter]. cbn in NDl. inversion NDl as [|? ? NI ND']; subst.
      assert (INC' : incl l (h_chunks h)) by (intros z Hz; apply INC; right; exact Hz).
      destruct (chunk_eq_dec x k) as [->|NX].
      - replace (qa k) with (quar k) by (subst qa; cbn beta; rewrite Z.eqb_refl; reflexivity).
        replace (al (quar k)) with false by reflexivity. replace (al k) with true by (subst al; cbn beta; rewrite STA; reflexivity).
        cbn [map lb_remove fst f]. rewrite Z.eqb_refl. rewrite QID; [reflexivity|]. intros y Hy E. apply NI. rewrite <- E. apply in_map. exact Hy.
      - destruct Hkl as [E|Hkl]; [exfalso; exact (NX E)|].
        replace (qa x) with x by (subst qa; cbn beta; destruct (Z.eqb_spec (ck_ab x) (ck_ab k)) as [E|_]; [exfalso; apply NI; rewrite E; apply in_map; exact Hkl| reflexivity]).
        destruct (al x); cbn [map lb_remove fst f]; [| exact (IH INC' ND' Hkl)].
        destruct (Z.eqb_spec (ck_user x) (ck_user k)) as [EU|NU].
        + exfalso. apply NX. apply (hdr_unique h x k WL WR WK GEO (INC x ltac:(left; reflexivity)) Hk). unfold ck_hdr. rewrite EU. reflexivity.
        + f_equal. exact (IH INC' ND' Hkl). }
    exact (GEN (h_chunks h) (incl_refl _) ND Hk).
  Qed.

  (* [comment removed for export] *)
  #[using="hAR k q N' tf' nb' bl' nx p24 WF NE HQ HKQ"] Lemma baddr_fresh : forall b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) -> b_addr b <> baddr.
  Proof.
    intros b Hb E. dpose WF as (_ & _ & WR & _). pose proof (WR kBatchClass ltac:(unfold kBatchClass, kNumClasses; lia)) as X. cbn zeta in X.
    ddestruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDO & _). unfold owned in NDO.
    apply NoDup_app_remove_l in NDO. apply (NoDup_app_l_r _ _ q NDO).
    - unfold cache_set. fold p24. rewrite pop24_split. apply in_app_iff. right. left. reflexivity.
    - apply in_app_iff. right. unfold batch_set. rewrite Z.eqb_refl. apply in_map_iff. exists b. rewrite E. split; [exact compact_baddr| exact Hb].
  Qed.

  #[using="q WF GEO Hk STA NE HQ HKQ DN DTF DLN DWN DLB DWB DLNB DLBB"] Theorem WFC_putN : WFC h' (q_bytes (h_tq h) + (nx + 8192)) kQuarantineMax.
  Proof.
    dpose WF as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG). dpose WK as (WKF & ND & WKSEC). pose proof WL as [WL0 _].
    dpose WQ as ((T1 & T2 & T3) & WGQ & NDA & UQ).
    pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (WN & _ & WP & WXk).
    assert (ENX : nx = nfix (ck_n k)) by reflexivity. assert (NX1 : 1 <= nx) by (rewrite ENX; unfold nfix; lia).
    assert (LEN : length (pc_chunks p24) = (length (removelast (pc_chunks p24)) + 1)%nat).
    { rewrite pop24_split at 1. rewrite length_app. cbn [length]. reflexivity. }
    assert (NDE : NoDup (flat_map b_elems ((q_batches (h_tq h) ++ [nb0]) ++ q_batches (h_gq h)))).
    { dpose WX as (_ & X2 & _). rewrite <- app_assoc. rewrite !flat_map_app in X2. rewrite !flat_map_app. cbn [flat_map b_elems nb0]. rewrite app_nil_r.
      change (flat_map b_elems (q_batches (h_tq h)) ++ [ck_hdr k] ++ flat_map b_elems (q_batches (h_gq h)))
        with (flat_map b_elems (q_batches (h_tq h)) ++ ck_hdr k :: flat_map b_elems (q_batches (h_gq h))).
      apply NoDup_insert_mid; [exact X2|].
      intros IN. apply in_app_iff in IN as [IN|IN]; apply in_flat_map in IN as (b & Hb & He); apply (hdr_freshN b); try exact He; apply in_app_iff; [left| right]; exact Hb. }
    assert (NDB : NoDup (map b_addr ((q_batches (h_tq h) ++ [nb0]) ++ q_batches (h_gq h)))).
    { rewrite <- app_assoc, !map_app. cbn [map b_addr nb0]. change (map b_addr (q_batches (h_tq h)) ++ [baddr] ++ map b_addr (q_batches (h_gq h)))
        with (map b_addr (q_batches (h_tq h)) ++ baddr :: map b_addr (q_batches (h_gq h))).
      rewrite map_app in NDA. apply NoDup_insert_mid; [exact NDA|]. rewrite <- map_app. intros IN. apply in_map_iff in IN as (b & E & Hb). exact (baddr_fresh b Hb E). }
    split; [exact WL|].
    split. { (* [comment removed for export] *)
      intros c' Hc'. pose proof (WC c' Hc') as X. cbn zeta in X |- *. cbn [h_cache h_cinit h' h_putN]. unfold putN_cache.
      change (carved h' c') with (carved h c').
      destruct (Z.eqb_spec c' kBatchClass) as [->|NEQ]; [| exact X].
      fold p24 in X |- *. cbn [pc_max pc_csize pc_chunks]. ddestruct X as (X1 & X2 & X3 & X4 & X5).
      unfold pc_count in *. cbn [pc_chunks].
      split; [exact X1|]. split; [unfold kBatchClass; intros; lia|]. split; [lia|]. split; [lia|].
      rewrite pop24_split in X5. apply Forall_app in X5 as [X5 _]. exact X5. }
    split. { (* [comment removed for export] *)
      intros c Hc. pose proof (WR c Hc) as X. cbn zeta in X |- *. change (h_reg h' c) with (h_reg h c). change (carved h' c) with (carved h c).
      ddestruct X as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11). pose proof (owned_putN c) as PM.
      split; [exact R0|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact R6|].
      split; [exact R7|]. split; [exact R8|]. split; [exact R9|].
      split; [exact (Permutation_NoDup (Permutation_sym PM) R10)|].
      intros k0. rewrite (R11 k0). split; intros IN; [eapply Permutation_in; [apply Permutation_sym; exact PM| exact IN]| eapply Permutation_in; [exact PM| exact IN]]. }
    split. { (* [comment removed for export] *)
      split; [| split].
      - apply Forall_forall. intros k' Hk'. apply putN_chunks_In in Hk' as [->|[Hk' _]].
        + unfold wf_chunk', quar. cbn [ck_n ck_st ck_prim ck_cls ck_ab ck_map_beg ck_map_size h_sec h_L h' h_putN carved h_reg].
          split; [exact WN|]. split; [right; reflexivity|]. split; [exact WP|]. unfold ck_map_beg, ck_map_size in WXk. exact WXk.
        + pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as X. unfold wf_chunk' in *. cbn [h_sec h_L h' h_putN carved h_reg]. exact X.
      - cbn [h_chunks h' h_putN]. rewrite quar_ab_map_ab. exact ND.
      - cbn [h_sec h_chunks h' h_putN]. intros i sh Hi. ddestruct (WKSEC i sh Hi) as (k2 & Hk2 & P2 & MB & MS).
        destruct (chunk_eq_dec k2 k) as [->|NEQ].
        + exists (quar k). split; [apply (proj2 (putN_chunks_In _)); left; reflexivity|]. cbn. unfold ck_map_beg, ck_map_size in *. cbn. exact (conj P2 (conj MB MS)).
        + exists k2. split; [apply (proj2 (putN_chunks_In _)); right; exact (conj Hk2 NEQ)| exact (conj P2 (conj MB MS))]. }
    split. { (* [comment removed for export] *)
      split; [| split; [| split]].
      - cbn [h_tq h' h_putN q_batches q_bytes]. split; [| split].
        + apply Forall_app. split; [apply Forall_forall; intros b Hb; apply wf_batch_keptN; exact (proj1 (Forall_forall _ _) T1 b Hb)|].
          constructor; [| constructor]. split; [| split; [| split]].
          * unfold b_count, kBatchCap. cbn [b_elems nb0 length]. lia.
          * cbn [b_size b_elems nb0].
            assert (FK : find (fun k0 => ck_hdr k0 =? ck_hdr k) (h_chunks h') = Some (quar k)).
            { cbn [h_chunks h' h_putN]. rewrite find_hdr_quar_ab.
              destruct (find (fun k0 => ck_hdr k0 =? ck_hdr k) (h_chunks h)) as [k2|] eqn:FD.
              -- apply find_some in FD as [Hk2 E2]. apply Z.eqb_eq in E2. pose proof (hdr_unique h k2 k WL0 WR WK GEO Hk2 Hk E2) as ->. cbn. rewrite Z.eqb_refl. reflexivity.
              -- exfalso. pose proof (find_none _ _ FD k Hk) as X. cbn beta in X. rewrite Z.eqb_refl in X. discriminate X. }
            unfold used_size, kBatchSize. cbn [map]. rewrite FK. cbn [ck_n quar sum fold_right]. rewrite ENX. lia.
          * cbn [b_elems nb0]. constructor; [| constructor]. exists (quar k). split; [apply (proj2 (putN_chunks_In _)); left; reflexivity| split; reflexivity].
          * unfold carved in *. cbn [b_addr nb0 h_reg h_L h' h_putN]. exists kq. exact (conj (proj1 HKQ) eq_refl).
        + cbn [q_batches q_bytes]. unfold sum in *. rewrite map_app, fold_right_app. cbn [map fold_right b_size nb0]. rewrite T2.
          rewrite (fold_add_base (map b_size (q_batches (h_tq h))) (nx + 8192 + 0)). lia.
        + cbn [q_batches q_bytes]. pose proof T3. lia.
      - cbn [h_gq h' h_putN]. ddestruct WGQ as (G1 & G2 & G3). split; [| exact (conj G2 G3)]. apply Forall_forall. intros b Hb. apply wf_batch_keptN. exact (proj1 (Forall_forall _ _) G1 b Hb).
      - cbn [h_tq h_gq h' h_putN q_batches]. exact NDB.
      - cbn [h_tq h_gq h' h_putN q_batches]. intros k' Hk' S'.
        assert (EX : exists b, In b ((q_batches (h_tq h) ++ [nb0]) ++ q_batches (h_gq h)) /\ In (ck_hdr k') (b_elems b)).
        { apply putN_chunks_In in Hk' as [->|[Hk' NEQ]].
          - exists nb0. split; [apply in_app_iff; left; apply in_app_iff; right; left; reflexivity| cbn [b_elems nb0]; left; reflexivity].
          - ddestruct (UQ k' Hk' S') as (b & [Hb Hin] & _). apply in_app_iff in Hb as [Hb|Hb].
            + exists b. split; [apply in_app_iff; left; apply in_app_iff; left; exact Hb| exact Hin].
            + exists b. split; [apply in_app_iff; right; exact Hb| exact Hin]. }
        ddestruct EX as (b & Hb & Hin). exists b. split; [exact (conj Hb Hin)|]. intros b2 [Hb2 Hin2]. exact (elems_owner_unique _ b b2 (ck_hdr k') NDE Hb Hb2 Hin Hin2). }
    split; [exact WS|].
    split. { ddestruct WD as (N1 & _ & _ & T0 & _). unfold wf_depot'. cbn [h_dep h' h_putN d_n d_nb s_total d_bl]. unfold kDepotNodesL2 in *.
             repeat split; try assumption; lia. }
    split; [exact WB|].
    split; [exact WBIG|].
    split. { (* [comment removed for export] *)
      ddestruct WX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9). split; [exact X1|].
      split; [| split; [exact X3| split; [exact X4| split; [exact X5| split; [exact X6| split; [exact X7| split; [exact X8|]]]]]]].
      - cbn [h_tq h_gq h' h_putN q_batches]. exact NDE.
      - (* [comment removed for export] *)
        rewrite !blocks_blk_of. cbn [h_chunks h' h_putN]. unfold quar_ab. eapply Z.le_trans; [apply cnt24_blk_map| exact X9].
        intros k0 ST. destruct (ck_ab k0 =? ck_ab k); [cbn [ck_st] in ST; cbv in ST; discriminate ST| reflexivity]. }
    exact WG.
  Qed.

  #[using="Type"] Lemma kview_putN : kview_eq (hdep h nb' bl') h'.
  Proof. clear. unfold kview_eq, hdep, set_dep. cbn. repeat split; reflexivity. Qed.
  End PutN.
End ARUN_1.
