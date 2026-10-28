(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX APop.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Ltac2 gd_tbl_AModelC24 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.incl"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.sum"; "Corelib.Lists.ListDef.map"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "Corelib.Init.Datatypes.bool"; "ARUN_1.c24p"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.win24"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_n"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_hdr"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_ab"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.carved"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kBatchClass"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_batch"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_size"; "ARUN_1.wq"; "Stdlib.Lists.List.flat_map"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_elems"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.Lists.List.filter"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.blocks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineCache"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineMax"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.fa_set"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.cache_set"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.CMAX24"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_st"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "ARUN_1.blk_of"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zallb (P : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with O => true | S k => P lo && zallb P (lo + 1) k end.
#[using="Type"] Lemma zallb_spec : forall P n lo, zallb P lo n = true -> forall x, lo <= x < lo + Z.of_nat n -> P x = true.
Proof.
  induction n as [|n IH]; intros lo H x Hx; [lia|].
  cbn [zallb] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec x lo) as [->|]; [exact H1|]. apply (IH (lo + 1) H2). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma class_of_24_tbl : forall j, 3 <= j <= 8192 -> (class_of (8 * j) =? 24) = ((768 <? j) && (j <=? 1024)).
Proof.
  intros j Hj.
  pose proof (zallb_spec (fun j => Bool.eqb (class_of (8 * j) =? 24) ((768 <? j) && (j <=? 1024))) (Z.to_nat 8190) 3 ltac:(vm_compute; reflexivity) j ltac:(lia)) as X.
  cbn beta in X. apply Bool.eqb_prop in X. exact X.
Qed.


#[using="Type"] Lemma rz_size_ranges : ltac2:(CDefT.buildp (gd_tbl_AModelC24 ()) "Pn,$0.(1.P,(2.R1.+?81.)(3.(4.R2.)+80.)(1.P,(1.(3.+?81.R1.)(2.R1.+3?01.))(5.$0.(4.R2.)+100.)P,(3.+3?01.R1.)(3.+200.(4.R2.))))")
(* [comment removed for export] *).
Proof.
  intros n. unfold rz_size, rz_log.
  destruct (Z.ltb_spec n 49); [repeat split; intros; lia|]. destruct (Z.ltb_spec n 97); [repeat split; intros; lia|].
  destruct (Z.ltb_spec n 449); [repeat split; intros; lia|]. destruct (Z.ltb_spec n 0xf81); [repeat split; intros; lia|].
  destruct (Z.ltb_spec n 0x3f01); [repeat split; intros; lia|]. destruct (Z.ltb_spec n 0x7e01); [repeat split; intros; lia|].
  destruct (Z.ltb_spec n 0xfc01); repeat split; intros; lia.
Qed.

#[using="Type"] Lemma needed_mul8 : forall n, 0 <= n -> exists j, needed n = 8 * j /\ 3 <= j.
Proof.
  intros n Hn. unfold needed, rounded, round_up.
  pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as M.
  destruct (rz_size_cases n) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E;
    [exists ((Z.max n 8 + 8 - 1) / 8 + 2)| exists ((Z.max n 8 + 8 - 1) / 8 + 4)| exists ((Z.max n 8 + 8 - 1) / 8 + 8)| exists ((Z.max n 8 + 8 - 1) / 8 + 16)
    | exists ((Z.max n 8 + 8 - 1) / 8 + 32)| exists ((Z.max n 8 + 8 - 1) / 8 + 64)| exists ((Z.max n 8 + 8 - 1) / 8 + 128)| exists ((Z.max n 8 + 8 - 1) / 8 + 256)]; lia.
Qed.

#[using="Type"] Lemma rz_window : forall n, 5889 <= n <= 7936 -> rz_size n = 256.
Proof. intros n Hn. apply (proj1 (proj2 (rz_size_ranges n))). lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma win24_primary : forall n, win24 n = true -> from_primary n = true /\ pclass n = kBatchClass.
Proof.
  intros n W. unfold win24 in W. apply andb_prop in W as [W1 W2]. apply Z.leb_le in W1, W2.
  pose proof (rz_window n (conj W1 W2)) as RZ.
  assert (ND : exists j, needed n = 8 * j /\ 768 < j <= 1024).
  { unfold needed, rounded, round_up. rewrite RZ. rewrite Z.max_l by lia.
    pose proof (Z.div_mod (n + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 8 - 1) 8 ltac:(lia)).
    exists ((n + 8 - 1) / 8 + 32). split; lia. }
  ddestruct ND as (j & EJ & HJ). split.
  - unfold from_primary, kMaxSize. apply Z.leb_le. lia.
  - unfold pclass, kBatchClass. rewrite EJ. apply Z.eqb_eq. rewrite (class_of_24_tbl j ltac:(lia)).
    apply andb_true_intro. split; [apply Z.ltb_lt| apply Z.leb_le]; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pclass_24_win : forall n, 0 <= n -> from_primary n = true -> pclass n = kBatchClass -> win24 n = true.
Proof.
  intros n Hn FP PC. unfold from_primary, kMaxSize in FP. apply Z.leb_le in FP.
  ddestruct (needed_mul8 n Hn) as (j & EJ & J3).
  unfold pclass, kBatchClass in PC. rewrite EJ in PC. apply Z.eqb_eq in PC. rewrite (class_of_24_tbl j ltac:(lia)) in PC.
  apply andb_prop in PC as [P1 P2]. apply Z.ltb_lt in P1. apply Z.leb_le in P2.
  (* [comment removed for export] *)
  unfold needed, rounded, round_up in EJ.
  pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as M.
  ddestruct (rz_size_ranges n) as (R1 & R2 & R3).
  destruct (Z_lt_le_dec n 3969) as [A|A]; [pose proof (R1 A); exfalso; lia|].
  destruct (Z_lt_le_dec n 16129) as [B|B]; [| pose proof (R3 B); exfalso; lia].
  rewrite (R2 (conj A B)) in EJ. unfold win24. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma secondary_not_win : forall n, from_primary n = false -> win24 n = false.
Proof.
  intros n FP. destruct (win24 n) eqn:W; [| reflexivity]. destruct (win24_primary n W) as [FP' _]. rewrite FP in FP'. discriminate FP'.
Qed.
#[using="Type"] Lemma secondary_big : forall n, 0 <= n -> from_primary n = false -> 7936 < n.
Proof.
  intros n Hn FP. unfold from_primary, kMaxSize in FP. apply Z.leb_gt in FP. unfold needed, rounded, round_up in FP.
  pose proof (rz_size_bound' n) as RZ. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as M. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma filter_length_impl : forall {A} (p q : A -> bool) (l : list A),
  (forall x, In x l -> p x = true -> q x = true) -> (length (filter p l) <= length (filter q l))%nat.
Proof.
  intros A p q l. induction l as [|a l IH]; intros H; cbn [filter]; [lia|].
  specialize (IH ltac:(intros x Hx; apply H; right; exact Hx)).
  destruct (p a) eqn:Pa; [rewrite (H a (or_introl eq_refl) Pa); cbn [length]; lia|]. destruct (q a); cbn [length]; lia.
Qed.

#[using="Type"] Lemma NoDup_map_filter : forall {A B} (f : A -> B) (p : A -> bool) (l : list A), NoDup (map f l) -> NoDup (map f (filter p l)).
Proof.
  intros A B f p l. induction l as [|a l IH]; intros ND; cbn [filter map]; [constructor|].
  cbn [map] in ND. inversion ND as [|? ? NI ND']; subst. specialize (IH ND').
  destruct (p a); [| exact IH]. cbn [map]. constructor; [| exact IH].
  intros X. apply NI. apply in_map_iff in X. ddestruct X as (x & E & Hx). apply filter_In in Hx. apply in_map_iff. exists x. split; [exact E| exact (proj1 Hx)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sum_incl_le : ltac2:(CDefT.buildp (gd_tbl_AModelC24 ()) "Pw,P,$0.$0.Pl1,(6.$0.)Pl2,(6.$0.)P,(7.$0.R2.)P,(8.$0.R3.R2.)P,Pe,$0.(3.=A1.R6.R1.)(3.(9.(:.$0.$0.R6.R5.))(9.(:.$0.$0.R6.R4.)))")
(* [comment removed for export] *).
Proof.
  intros w l1. induction l1 as [|a l1 IH]; intros l2 ND HI W0.
  - clear ND HI. unfold sum. cbn [map fold_right]. induction l2 as [|b l2 IH2]; cbn [map fold_right]; [lia|]. pose proof (W0 b). lia.
  - inversion ND as [|? ? NI ND']; subst.
    ddestruct (in_split a l2 (HI a (or_introl eq_refl))) as (l2a & l2b & ->).
    assert (HI' : incl l1 (l2a ++ l2b)).
    { intros x Hx. pose proof (HI x (or_intror Hx)) as X. apply in_app_iff in X. apply in_app_iff.
      destruct X as [X|[X|X]]; [left; exact X| exfalso; apply NI; rewrite X; exact Hx| right; exact X]. }
    specialize (IH (l2a ++ l2b) ND' HI' W0). cbn [map sum fold_right] in *. unfold sum in *. rewrite !map_app, !fold_right_app in *. cbn [map fold_right] in *.
    assert (G : forall (l : list Z) (z : Z), fold_right Z.add z l = fold_right Z.add 0 l + z) by (induction l as [|x l IHl]; intros z; cbn; [lia| rewrite IHl; lia]).
    rewrite (G (map w l2a) (w a + fold_right Z.add 0 (map w l2b))). rewrite (G (map w l2a) (fold_right Z.add 0 (map w l2b))) in IH. lia.
Qed.

#[using="Type"] Lemma sum_ge_count : ltac2:(CDefT.buildp (gd_tbl_AModelC24 ()) "Pw,P,$0.$0.Pl,(6.$0.)Pm,$0.P,Pe,$0.P,(;.$0.R1.R3.)(3.R3.A1.R5.R2.)(3.(<.R2.(=.(>.$0.R3.)))(9.(:.$0.$0.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros w l m H. induction l as [|a l IH]; cbn [map length]; [unfold sum; cbn; lia|].
  specialize (IH ltac:(intros e He; apply H; right; exact He)). pose proof (H a (or_introl eq_refl)).
  unfold sum in *. cbn [fold_right]. lia.
Qed.

#[using="Type"] Lemma sum_app' : forall l1 l2, sum (l1 ++ l2) = sum l1 + sum l2.
Proof. intros l1 l2. unfold sum. induction l1 as [|a l1 IH]; cbn; [lia| rewrite IH; lia]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma codes_le_length : ltac2:(CDefT.buildp (gd_tbl_AModelC24 ()) "Pf,P,$0.$0.Pn,$0.Pl,(6.$0.)P,(3.=R2.)P,Pi,$0.Pj,$0.P,(1.(3.=R2.)(2.R2.R5.))P,(1.(3.=R2.)(2.R2.R6.))P,(5.$0.A1.R8.R4.A1.R8.R3.)(5.$0.R5.R4.)P,Pk,$0.P,(1.(3.=R1.)(2.R1.R5.))(;.$0.A1.R7.R2.R5.)(3.R5.(=.(>.$0.R4.)))")
(* [comment removed for export] *).
Proof.
  intros f n l N0 INJ HIN.
  set (cs := map (fun i => f (Z.of_nat i)) (seq 0 (Z.to_nat n))).
  assert (ND : NoDup cs).
  { unfold cs. apply Finite.Injective_map_NoDup_in; [| apply seq_NoDup].
    intros i j Hi Hj E. apply in_seq in Hi, Hj. apply Nat2Z.inj. apply INJ; [lia| lia| exact E]. }
  assert (HI : incl cs l).
  { intros x Hx. unfold cs in Hx. apply in_map_iff in Hx. ddestruct Hx as (i & <- & Hi). apply in_seq in Hi. apply HIN. lia. }
  pose proof (NoDup_incl_length ND HI) as LE. unfold cs in LE. rewrite length_map, length_seq in LE. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition c24p (k : chunk) : bool := ck_prim k && (ck_cls k =? kBatchClass).
Definition wq (h : ahst) (e : Z) : Z :=
  match find (fun k => ck_hdr k =? e) (h_chunks h) with Some k => used_size (ck_n k) | None => 0 end.

Section Count.
  Variable h : ahst.
  Hypothesis AWF : awf' h.
  Let batches := q_batches (h_tq h) ++ q_batches (h_gq h).

  #[using="Type"] Lemma wq_nonneg : forall e, 0 <= wq h e.
  Proof. intros e. unfold wq. destruct (find _ _); [unfold used_size, nfix; lia| lia]. Qed.

  #[using="AWF"] Lemma chunk_wf : forall k, In k (h_chunks h) -> wf_chunk' h k.
  Proof. intros k Hk. dpose AWF as (_ & _ & _ & (WKF & _) & _). exact (proj1 (Forall_forall _ _) WKF k Hk). Qed.

  (* [comment removed for export] *)
  #[using="hAR AWF"] Lemma c24_chunk : ltac2:(CDefT.buildp (gd_tbl_AModelC24 ()) "Pk,$?.P,(;.$?.R1.(10.Vh,))P,(5.$11.(12.R2.)$13.)(1.(5.$11.(14.(15.R3.))$13.)(1.(5.$0.(16.R3.)(17.(18.R3.)+?0.))(19.$0.Li,$0.(1.(1.(3.=R1.)(2.R1.(1:.Vh,$1;.)))(5.$0.(18.R4.)(17.(1<.(1=.Vh,)$1;.)(<.R1.+2000.)))))))")
(* [comment removed for export] *).
  Proof.
    intros k Hk C. unfold c24p in C. apply andb_prop in C as [PK CK]. apply Z.eqb_eq in CK.
    ddestruct (chunk_wf k Hk) as (N0 & _ & FPK & W4). rewrite PK in W4, FPK. ddestruct W4 as (CLS & _ & i & Hi & EAB). rewrite CK in *.
    assert (W : win24 (ck_n k) = true) by (apply pclass_24_win; [lia| symmetry; exact FPK| symmetry; exact CLS]).
    split; [exact W|]. unfold win24 in W. apply andb_prop in W as [W1 W2]. apply Z.leb_le in W1, W2.
    split; [unfold ck_hdr, ck_user, ck_rz, kChunkHeaderSize; rewrite (rz_window _ (conj W1 W2)); lia|].
    exists i. split; [exact Hi|]. rewrite EAB. unfold chunk_at. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="hAR AWF"] Lemma wq_c24 : forall k, In k (h_chunks h) -> c24p k = true -> 5889 <= wq h (ck_hdr k).
  Proof.
    intros k Hk C. unfold wq. destruct (find (fun k0 => ck_hdr k0 =? ck_hdr k) (h_chunks h)) as [k'|] eqn:F.
    2:{ exfalso. pose proof (find_none _ _ F k Hk) as X. cbv beta in X. rewrite Z.eqb_refl in X. discriminate X. }
    apply find_some in F. destruct F as [Hk' EH]. apply Z.eqb_eq in EH.
    ddestruct (c24_chunk k Hk C) as (_ & HD & i & Hi & EAB).
    ddestruct (chunk_wf k' Hk') as (N0' & _ & FPK' & W4'). unfold used_size, nfix.
    revert FPK' W4'. destruct (ck_prim k'); intros FPK' W4'.
    - ddestruct W4' as (CLS' & C30' & i' & Hi' & EAB').
      (* [comment removed for export] *)
      dpose AWF as (_ & _ & WR & _).
      pose proof (WR kBatchClass ltac:(unfold kNumClasses, kBatchClass; lia)) as R24. cbn zeta in R24. ddestruct R24 as (_ & AU24 & AUC24 & _ & ML24 & _).
      pose proof (WR (ck_cls k') ltac:(unfold kNumClasses; lia)) as Rc. cbn zeta in Rc. ddestruct Rc as (_ & AUc & AUCc & _ & MLc & _).
      pose proof (class_size_pos (ck_cls k') ltac:(lia)) as CSP. pose proof (rz_size_bound' (ck_n k')) as RZ'.
      assert (CS24 : class_size kBatchClass = 8192) by reflexivity. rewrite CS24 in AUC24.
      assert (B1 : 0 <= i' * class_size (ck_cls k') /\ i' * class_size (ck_cls k') + class_size (ck_cls k') <= r_alloc_user (h_reg h (ck_cls k'))) by (rewrite AUCc; nia).
      assert (B2 : 0 <= i * 8192 /\ i * 8192 + 8192 <= r_alloc_user (h_reg h kBatchClass)) by (rewrite AUC24; lia).
      unfold ck_hdr, ck_user, ck_rz, kChunkHeaderSize in EH, HD. rewrite EAB', EAB in EH. unfold chunk_at, region_beg, kRegionSize, kUserLimit, kBatchClass in *.
      assert (ECLS : ck_cls k' = 24) by lia.
      assert (W : win24 (ck_n k') = true) by (apply pclass_24_win; [lia| symmetry; exact FPK'| rewrite <- CLS'; exact ECLS]).
      unfold win24 in W. apply andb_prop in W as [W1 _]. apply Z.leb_le in W1. lia.
    - pose proof (secondary_big (ck_n k') ltac:(lia) ltac:(symmetry; exact FPK')). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma batches_bytes : ltac2:(CDefT.buildp (gd_tbl_AModelC24 ()) "Pbs,(6.$1>.)P,(1?.$1>.(20.Vh,)R1.)(5.$0.(9.(:.$1>.$0.$21.R2.))(17.(<.+2000.(=.(>.$1>.R2.)))(9.(:.$0.$0.(22.Vh,)(23.$1>.$0.$24.R2.)))))")
(* [comment removed for export] *).
  Proof.
    induction bs as [|b bs IH]; intros F; [reflexivity|]. inversion F as [|? ? WB F']; subst. specialize (IH F').
    ddestruct WB as (_ & BS & _). cbn [map flat_map length]. rewrite map_app, sum_app'.
    unfold kBatchSize in BS. unfold wq in *. unfold sum in *. cbn [fold_right]. rewrite BS, IH. lia.
  Qed.

  #[using="hAR AWF"] Lemma quar_bytes_le : sum (map b_size batches) <= kQuarantineCache + kQuarantineMax.
  Proof.
    dpose AWF as (_ & _ & _ & _ & ((T1 & T2 & T3) & (G1 & G2 & G3) & _) & _).
    unfold batches. rewrite map_app, sum_app'. rewrite <- T2, <- G2. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="hAR AWF"] Theorem c24_count : ltac2:(CDefT.buildp (gd_tbl_AModelC24 ()) "(3.(17.(<.+1701.(25.(=.(>.$?.(26.$?.$12.(10.Vh,))))(27.(28.Vh,))))(<.+2000.(=.(>.$1>.Vbatches,))))(17.$29.$2:.))")
(* [comment removed for export] *).
  Proof.
    dpose AWF as (_ & _ & _ & (WKF & WKND & _) & ((T1 & _) & (G1 & _) & _ & UQ) & _ & _ & _ & _ & WX & _).
    ddestruct WX as (_ & NDE & _).
    set (QK := filter (fun k => c24p k && (ck_st k =? CHUNK_QUARANTINE)) (h_chunks h)).
    set (LK := filter (fun k => c24p k && (ck_st k =? CHUNK_ALLOCATED)) (h_chunks h)).
    (* [comment removed for export] *)
    assert (SPLIT : (length (filter c24p (h_chunks h)) <= length LK + length QK)%nat).
    { unfold LK, QK. revert WKF. generalize (h_chunks h) as ks. induction ks as [|k ks IH]; intros WKF'; cbn [filter]; [lia|].
      inversion WKF' as [|? ? WK WKF'']; subst. specialize (IH WKF''). ddestruct WK as (_ & ST & _).
      destruct (c24p k); cbn [andb]; [| exact IH].
      destruct ST as [ST | ST]; rewrite ST;
        [change (CHUNK_ALLOCATED =? CHUNK_ALLOCATED) with true; change (CHUNK_ALLOCATED =? CHUNK_QUARANTINE) with false
        | change (CHUNK_QUARANTINE =? CHUNK_ALLOCATED) with false; change (CHUNK_QUARANTINE =? CHUNK_QUARANTINE) with true]; cbn [length]; lia. }
    (* [comment removed for export] *)
    assert (LIVE : Z.of_nat (length LK) <= cnt24 (blocks h)).
    { unfold cnt24, blocks, live. set (f := fun k => (ck_user k, ck_n k)).
      assert (E : forall l, filter (fun b : Z * Z => win24 (snd b)) (map f l) = map f (filter (fun k => win24 (ck_n k)) l))
        by (induction l as [|a l IHl]; cbn [filter map]; [reflexivity| unfold f at 1; cbn [snd]; destruct (win24 (ck_n a)); cbn [map]; rewrite IHl; reflexivity]).
      rewrite E, length_map. apply Nat2Z.inj_le. unfold LK.
      eapply Nat.le_trans; [apply (filter_length_impl (fun k => c24p k && (ck_st k =? CHUNK_ALLOCATED)) (fun k => (ck_st k =? CHUNK_ALLOCATED) && win24 (ck_n k)) (h_chunks h))|].
      { intros k Hk P. apply andb_prop in P as [P1 P2]. rewrite P2. destruct (c24_chunk k Hk P1) as (W & _). rewrite W. reflexivity. }
      generalize (h_chunks h) as ks. induction ks as [|k ks IH]; cbn [filter]; [lia|].
      destruct (ck_st k =? CHUNK_ALLOCATED); cbn [andb filter]; [destruct (win24 (ck_n k)); cbn [length]; lia| exact IH]. }
    (* [comment removed for export] *)
    set (EQ := map ck_hdr QK).
    assert (NDQ : NoDup EQ).
    { assert (EE : EQ = map (fun k => ck_ab k + 240) QK).
      { unfold EQ, QK. apply map_ext_in. intros k Hk. apply filter_In in Hk. destruct Hk as [Hk P]. apply andb_prop in P as [P _]. exact (proj1 (proj2 (c24_chunk k Hk P))). }
      rewrite EE. replace (map (fun k => ck_ab k + 240) QK) with (map (fun a => a + 240) (map ck_ab QK)) by (rewrite map_map; reflexivity).
      apply Finite.Injective_map_NoDup; [intros a b E; lia|]. unfold QK. apply NoDup_map_filter. exact WKND. }
    assert (INQ : incl EQ (flat_map b_elems batches)).
    { intros e He. unfold EQ in He. apply in_map_iff in He. ddestruct He as (k & <- & Hk). unfold QK in Hk. apply filter_In in Hk. destruct Hk as [Hk P].
      apply andb_prop in P as [_ ST]. apply Z.eqb_eq in ST. ddestruct (UQ k Hk ST) as (b & (Hb & Hin) & _). apply in_flat_map. exists b. split; [exact Hb| exact Hin]. }
    assert (WGE : 5889 * Z.of_nat (length EQ) <= sum (map (wq h) EQ)).
    { apply sum_ge_count. intros e He. unfold EQ in He. apply in_map_iff in He. ddestruct He as (k & <- & Hk). unfold QK in Hk. apply filter_In in Hk. destruct Hk as [Hk P].
      apply andb_prop in P as [P _]. exact (wq_c24 k Hk P). }
    pose proof (sum_incl_le (wq h) EQ (flat_map b_elems batches) NDQ INQ wq_nonneg) as SLE.
    assert (FB : Forall (wf_batch h) batches) by (unfold batches; apply Forall_app; split; assumption).
    pose proof (batches_bytes batches FB) as BB. pose proof quar_bytes_le as QB.
    assert (LQ : length EQ = length QK) by (unfold EQ; apply length_map). rewrite LQ in WGE. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="hAR AWF"] Lemma carved24_le_owned : carved h kBatchClass <= Z.of_nat (length (owned h kBatchClass)).
  Proof.
    dpose AWF as (_ & _ & WR & _). pose proof (WR kBatchClass ltac:(unfold kNumClasses, kBatchClass; lia)) as R. cbn zeta in R.
    ddestruct R as (_ & AU & AUC & _ & _ & _ & _ & _ & _ & _ & _ & PART).
    assert (CS24 : class_size kBatchClass = 8192) by reflexivity. rewrite CS24 in *.
    assert (C0 : 0 <= carved h kBatchClass) by (unfold carved; rewrite CS24; apply Z.div_pos; lia).
    apply (codes_le_length (fun k => k * 8192 / 16) (carved h kBatchClass) _ C0).
    - intros i j Hi Hj E. replace (i * 8192 / 16) with (i * 512) in E by (replace (i * 8192) with (i * 512 * 16) by lia; rewrite Z.div_mul by lia; reflexivity).
      replace (j * 8192 / 16) with (j * 512) in E by (replace (j * 8192) with (j * 512 * 16) by lia; rewrite Z.div_mul by lia; reflexivity). lia.
    - intros k Hk. exact (proj1 (PART k) Hk).
  Qed.

  (* [comment removed for export] *)
  #[using="hAR AWF batches"] Theorem carve24_bound : ltac2:(CDefT.buildp (gd_tbl_AModelC24 ()) "Pnw,$0.P,(5.(6.$0.)(2;.Vh,$1;.)(2<.$0.))P,(5.(6.$0.)(2=.Vh,$1;.)(2<.$0.))P,(1.(3.=R3.)(3.R3.+40.))P,(3.(27.(28.Vh,))$2>.)(3.(17.(1:.Vh,$1;.)R5.)$2?.)")
(* [comment removed for export] *).
  Proof.
    intros nw FA0 CA0 NW C24. pose proof carved24_le_owned as LE. pose proof c24_count as CNT.
    unfold owned in LE. rewrite FA0, CA0 in LE. cbn [app] in LE. rewrite length_app in LE.
    unfold chunk_set, batch_set in LE. rewrite Z.eqb_refl, !length_map in LE. fold batches in LE.
    change (fun k : chunk => ck_prim k && (ck_cls k =? kBatchClass)) with c24p in LE.
    unfold kQuarantineCache, kQuarantineMax in CNT. unfold CMAX24, C24MAX in *. lia.
  Qed.
End Count.

(* [comment removed for export] *)
#[using="Type"] Theorem noexh24 : forall h, awf' h -> r_mapped_user (h_reg h kBatchClass) + kUserMapSize <= kUserLimit.
Proof.
  intros h AWF. dpose AWF as (_ & _ & WR & _ & _ & _ & _ & _ & _ & WX & _).
  ddestruct WX as (_ & _ & _ & _ & _ & _ & _ & X8 & _).
  pose proof (WR kBatchClass ltac:(unfold kNumClasses, kBatchClass; lia)) as R. cbn zeta in R. ddestruct R as (_ & AU & AUC & _ & _ & GAP & _).
  specialize (GAP ltac:(unfold kBatchClass; lia)). assert (CS24 : class_size kBatchClass = 8192) by reflexivity. rewrite CS24 in AUC.
  unfold kUserMapSize, kUserLimit, CMAX24 in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition blk_of (ks : list chunk) : list (Z * Z) := map (fun k => (ck_user k, ck_n k)) (filter (fun k => ck_st k =? CHUNK_ALLOCATED) ks).
#[using="Type"] Lemma blocks_blk_of : forall h, blocks h = blk_of (h_chunks h). Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cnt24_blk_filter : forall (p : chunk -> bool) ks, cnt24 (blk_of (filter p ks)) <= cnt24 (blk_of ks).
Proof.
  intros p ks. unfold blk_of. induction ks as [|k ks IH]; cbn [filter]; [lia|].
  destruct (p k); cbn [filter]; destruct (ck_st k =? CHUNK_ALLOCATED); cbn [map]; rewrite ?cnt24_cons; cbn [snd]; try destruct (win24 (ck_n k)); lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma cnt24_blk_map : ltac2:(CDefT.buildp (gd_tbl_AModelC24 ()) "Pg,P,$?.$?.Pks,(6.$?.)P,Pk,$?.P,(5.$0.(30.A1.R3.R1.)$31.)(5.$?.A1.R4.R2.R2.)(3.(27.(32.(:.$?.$?.R3.R2.)))(27.(32.R2.)))")
(* [comment removed for export] *).
Proof.
  intros g ks G. unfold blk_of. induction ks as [|k ks IH]; cbn [map filter]; [lia|].
  destruct (ck_st (g k) =? CHUNK_ALLOCATED) eqn:SG.
  - apply Z.eqb_eq in SG. pose proof (G k SG) as EK. rewrite EK in *. rewrite SG. change (CHUNK_ALLOCATED =? CHUNK_ALLOCATED) with true. cbn [map]. rewrite !cnt24_cons. lia.
  - destruct (ck_st k =? CHUNK_ALLOCATED); cbn [map]; rewrite ?cnt24_cons; cbn [snd]; try destruct (win24 (ck_n k)); lia.
Qed.

End ARUN_1.
