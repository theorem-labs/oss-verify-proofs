(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsKSys4.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition room_test (n : Z) : bool := if n <=? 16 then Z.eqb (class_of (needed n)) 1 else (csize (class_of (needed n)) <=? 4 * n).
Lemma room_check : zforallb room_test 1 (Z.to_nat 64512) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma class_small : forall n, 1 <= n <= 16 -> blk_class n = 1.
Proof.
  intros n Hn. pose proof (zforallb_spec room_test (Z.to_nat 64512) 1 room_check n) as C. rewrite Z2Nat.id in C by lia. specialize (C ltac:(lia)).
  unfold room_test in C. destruct (Z.leb_spec n 16); [| lia]. apply Z.eqb_eq in C. exact C.
Qed.
Lemma csize_le_4n : forall n, 17 <= n -> is_primary n = true -> csize (blk_class n) <= 4 * n.
Proof.
  intros n Hn HP. apply (is_primary_iff n ltac:(lia)) in HP.
  pose proof (zforallb_spec room_test (Z.to_nat 64512) 1 room_check n) as C. rewrite Z2Nat.id in C by lia. specialize (C ltac:(lia)).
  unfold room_test in C. destruct (Z.leb_spec n 16); [lia|]. apply Z.leb_le in C. exact C.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wsum {A} (w : A -> Z) (l : list A) : Z := fold_right (fun x acc => w x + acc) 0 l.
Lemma wsum_app : forall {A} (w : A -> Z) l1 l2, wsum w (l1 ++ l2) = wsum w l1 + wsum w l2.
Proof. intros A w l1 l2. induction l1 as [|x t IH]; (lazymatch goal with |- ?G => let G' := eval cbn [wsum fold_right app] in G in change_no_check G' end); [reflexivity|]. fold (wsum w (t ++ l2)) (wsum w t). rewrite IH. lia. Qed.
Lemma wsum_le : forall {A} (w w' : A -> Z) l, (forall x, In x l -> w x <= w' x) -> wsum w l <= wsum w' l.
Proof.
  intros A w w' l H. induction l as [|x t IH]; (lazymatch goal with |- ?G => let G' := eval cbn [wsum fold_right] in G in change_no_check G' end); [lia|]. fold (wsum w t) (wsum w' t).
  pose proof (H x (or_introl eq_refl)). assert (wsum w t <= wsum w' t) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.
Lemma wsum_const : forall {A} (k : Z) (l : list A), wsum (fun _ => k) l = k * Z.of_nat (length l).
Proof. intros A k l. induction l as [|x t IH]; (lazymatch goal with |- ?G => let G' := eval cbn [wsum fold_right length] in G in change_no_check G' end); [symmetry; apply Z.mul_0_r|]. fold (wsum (fun _ : A => k) t). rewrite IH, Nat2Z.inj_succ. ring. Qed.
Lemma wsum_filter_len : forall {A} (f : A -> bool) (k : Z) (l : list A), k * Z.of_nat (length (List.filter f l)) = wsum (fun x => if f x then k else 0) l.
Proof.
  intros A f k l. induction l as [|x t IH]; (lazymatch goal with |- ?G => let G' := eval cbn [wsum fold_right List.filter length] in G in change_no_check G' end); [apply Z.mul_0_r|].
  fold (wsum (fun x0 : A => if f x0 then k else 0) t).
  destruct (f x); (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite ?Nat2Z.inj_succ; rewrite <- IH; ring.
Qed.

(* [comment removed for export] *)
Lemma items_sum_q : forall q, wsum (fun it : Z * Z => snd it) (flat_map ba_items q) + BATCHSZ * Z.of_nat (length q) = q_bytes q.
Proof.
  induction q as [|b t IH]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [flat_map length q_bytes fold_right] in G in change_no_check G' end). fold (q_bytes t). rewrite wsum_app.
  (lazymatch goal with |- ?G => let G' := eval unfold ba_bytes in G in change_no_check G' end). fold (wsum (fun it : Z * Z => snd it) (ba_items b)). lia.
Qed.
Lemma items_len_q : forall q, (forall b, In b q -> Z.of_nat (length (ba_items b)) <= BATCHCAP) ->
  Z.of_nat (length (flat_map ba_items q)) <= BATCHCAP * Z.of_nat (length q).
Proof.
  induction q as [|b t IH]; intros H; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [flat_map length] in G in change_no_check G' end). rewrite length_app, Nat2Z.inj_add.
  pose proof (H b (or_introl eq_refl)). assert (Z.of_nat (length (flat_map ba_items t)) <= BATCHCAP * Z.of_nat (length t)) by (apply IH; intros b0 Hb0; apply H; right; exact Hb0). lia.
Qed.

Lemma filter_len_le : forall {A} (f : A -> bool) (l : list A), (length (List.filter f l) <= length l)%nat.
Proof. intros A f l. induction l as [|x t IH]; (lazymatch goal with |- ?G => let G' := eval cbn [List.filter length] in G in change_no_check G' end); [lia|]. destruct (f x); (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Room.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Variables (st : ast) (Lc FF : list (Z * Z)).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  Variable c : Z.
  Hypothesis Hc : 1 <= c <= 30.

  Definition fl (pn : Z * Z) : bool := is_primary (snd pn) && Z.eqb (blk_class (snd pn)) c.
  Definition ncarved : Z := r_alloc_user (a_reg st c) / csize c.
  Definition CL : list Z := map (fun j => chunk_addr SBEG c (Z.of_nat j)) (seq 0 (Z.to_nat ncarved)).
  Definition owners : list Z :=
    map (fun pn => prim_alloc_beg (fst pn) (snd pn)) (List.filter fl Lc)
    ++ map (fun mn => prim_alloc_beg (fst mn + 16) (snd mn)) (List.filter fl (quar st))
    ++ map (chunk_of_compact SBEG c) (a_cache st c)
    ++ map (chunk_of_compact SBEG c) (r_free (a_reg st c))
    ++ (if Z.eqb c BATCHCLASS then map ba_addr (a_tq st ++ a_gq st) else []).

  Lemma alloc_eq : r_alloc_user (a_reg st c) = ncarved * csize c /\ 0 <= ncarved.
  Proof.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((Y1 & _) & _ & _ & Y4 & _). pose proof (csize_pos c Hc) as ((S1 & _) & _).
    (lazymatch goal with |- ?G => let G' := eval unfold ncarved in G in change_no_check G' end). split; [| apply Z.div_pos; lia]. rewrite Z.mul_comm. apply Z.div_exact; [lia | exact Y4].
  Qed.

  Lemma CL_nodup : List.NoDup CL.
  Proof.
    (lazymatch goal with |- ?G => let G' := eval unfold CL in G in change_no_check G' end). apply Finite.Injective_map_NoDup; [| apply seq_NoDup].
    intros j j' E. apply (AsAinvOpsP3.chunk_addr_inj bt c _ _ Hc) in E. lia.
  Qed.

  Lemma CL_owned : incl CL owners.
  Proof.
    intros a Ha. unfold CL in Ha. apply in_map_iff in Ha. destruct Ha as (j & <- & Hj). apply in_seq in Hj.
    destruct alloc_eq as [AE N0]. pose proof (csize_pos c Hc) as ((S1 & _) & _).
    assert (CV : carved bt st c (chunk_addr SBEG c (Z.of_nat j))).
    { exists (Z.of_nat j). split; [lia|]. split; [| reflexivity]. rewrite AE. assert (Z.of_nat j + 1 <= ncarved) by lia. nia. }
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & _). destruct PART as (P1 & _).
    apply (P1 _) in CV. (lazymatch goal with |- ?G => let G' := eval unfold owners in G in change_no_check G' end). rewrite !in_app_iff.
    destruct CV as [(p & n & Hin & HP & HC & HA) | [(m & n & Hin & HP & HC & HA) | [(k & Hk & E) | [(k & Hk & E) | [E24 (b & Hb & E)]]]]].
    - left. apply in_map_iff. exists (p, n). split; [exact HA|]. apply filter_In. split; [exact Hin|]. (lazymatch goal with |- ?G => let G' := eval unfold fl in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end). rewrite HP, HC, Z.eqb_refl. reflexivity.
    - right; left. apply in_map_iff. exists (m, n). split; [exact HA|]. apply filter_In. split; [exact Hin|]. (lazymatch goal with |- ?G => let G' := eval unfold fl in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end). rewrite HP, HC, Z.eqb_refl. reflexivity.
    - right; right; left. apply in_map_iff. exists k. split; [symmetry; exact E | exact Hk].
    - right; right; right; left. apply in_map_iff. exists k. split; [symmetry; exact E | exact Hk].
    - right; right; right; right. destruct (Z.eqb_spec c BATCHCLASS) as [_ | NE]; [| exfalso; exact (NE E24)]. apply in_map_iff. exists b. split; [exact E | exact Hb].
  Qed.

  Lemma ncarved_le : ncarved <= Z.of_nat (length (List.filter fl Lc)) + Z.of_nat (length (List.filter fl (quar st)))
                               + Z.of_nat (length (a_cache st c)) + Z.of_nat (length (r_free (a_reg st c)))
                               + (if Z.eqb c BATCHCLASS then Z.of_nat (length (a_tq st ++ a_gq st)) else 0).
  Proof.
    pose proof (NoDup_incl_length CL_nodup CL_owned) as LE. unfold CL, owners in LE. rewrite !length_app, !length_map, length_seq in LE.
    destruct alloc_eq as [_ N0]. destruct (Z.eqb c BATCHCLASS); [rewrite length_map in LE | cbn [length] in LE]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma quar_weight : csize c * Z.of_nat (length (List.filter fl (quar st))) <= 4 * (qt + qg).
  Proof.
    pose proof W as (_ & _ & (Q1 & Q2 & Q3 & Q4 & _) & _).
    pose proof (items_sum_q (a_tq st ++ a_gq st)) as IS. rewrite AsAinvOpsPf3d.q_bytes_app in IS. fold (quar st) in IS.
    assert (NN : forall x, In x (quar st) -> 1 <= snd x) by (intros [m n] Hx; destruct (quar_item bt st Lc FF W m n Hx) as (N1 & _); (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end); lia).
    assert (S0 : 0 <= wsum (fun it : Z * Z => snd it) (quar st)).
    { clear -NN. induction (quar st) as [|x t IH]; (lazymatch goal with |- ?G => let G' := eval cbn [wsum fold_right] in G in change_no_check G' end); [lia|]. fold (wsum (fun it : Z * Z => snd it) t).
      pose proof (NN x (or_introl eq_refl)). assert (0 <= wsum (fun it : Z * Z => snd it) t) by (apply IH; intros y Hy; apply NN; right; exact Hy). lia. }
    rewrite wsum_filter_len. destruct (Z.eq_dec c 1) as [-> | NE1].
    - (* [comment removed for export] *)
      assert (LQ : Z.of_nat (length (quar st)) <= BATCHCAP * Z.of_nat (length (a_tq st ++ a_gq st))).
      { apply items_len_q. intros b Hb. destruct (batch_facts bt st Lc FF W b Hb) as (_ & BL & _). lia. }
      eapply Z.le_trans; [apply (wsum_le _ (fun _ => csize 1)); intros x _; destruct (fl x); [lia | change (csize 1) with 32; lia]|].
      rewrite wsum_const. change (csize 1) with 32. unfold BATCHCAP, BATCHSZ in *. lia.
    - (* [comment removed for export] *)
      eapply Z.le_trans; [apply (wsum_le _ (fun x => 4 * snd x))|].
      + intros [m n] Hx. (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end). pose proof (NN _ Hx) as N1. cbn [snd] in N1. (lazymatch goal with |- ?G => let G' := eval unfold fl in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end).
        destruct (is_primary n) eqn:HP; (lazymatch goal with |- ?G => let G' := eval cbn [andb] in G in change_no_check G' end); [| lia]. destruct (Z.eqb_spec (blk_class n) c) as [EC | _]; [| lia].
        destruct (Z_le_dec n 16) as [L16 | G16]; [exfalso; apply NE1; rewrite <- EC; apply class_small; lia|].
        rewrite <- EC. apply csize_le_4n; [lia | exact HP].
      + assert (E4 : wsum (fun x : Z * Z => 4 * snd x) (quar st) = 4 * wsum (fun it : Z * Z => snd it) (quar st)).
        { clear. induction (quar st) as [|x t IH]; (lazymatch goal with |- ?G => let G' := eval cbn [wsum fold_right] in G in change_no_check G' end); [lia|]. fold (wsum (fun x0 : Z * Z => 4 * snd x0) t) (wsum (fun it : Z * Z => snd it) t). lia. }
        rewrite E4. unfold BATCHSZ in *. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem alloc_bound : r_alloc_user (a_reg st c)
    <= 65536 * LMAX + 5 * (qt + qg) + csize c * (Z.of_nat (length (a_cache st c)) + Z.of_nat (length (r_free (a_reg st c)))).
  Proof.
    destruct alloc_eq as [AE N0]. pose proof (csize_pos c Hc) as ((S1 & S2) & _). pose proof ncarved_le as NL. pose proof quar_weight as QW.
    pose proof W as (_ & _ & (Q1 & Q2 & Q3 & Q4 & _) & _ & _ & _ & _ & _ & _ & (_ & GC & _) & _).
    pose proof (filter_len_le fl Lc) as FLc.
    assert (BW : csize c * (if Z.eqb c BATCHCLASS then Z.of_nat (length (a_tq st ++ a_gq st)) else 0) <= qt + qg).
    { destruct (Z.eqb_spec c BATCHCLASS) as [-> | _]; [| lia]. change (csize BATCHCLASS) with 8192.
      pose proof (items_sum_q (a_tq st ++ a_gq st)) as IS. rewrite AsAinvOpsPf3d.q_bytes_app in IS.
      assert (S0 : 0 <= wsum (fun it : Z * Z => snd it) (flat_map ba_items (a_tq st ++ a_gq st))).
      { fold (quar st). assert (NN : forall x, In x (quar st) -> 1 <= snd x) by (intros [m n] Hx; destruct (quar_item bt st Lc FF W m n Hx) as (N1 & _); (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end); lia).
        clear -NN. induction (quar st) as [|x t IH]; (lazymatch goal with |- ?G => let G' := eval cbn [wsum fold_right] in G in change_no_check G' end); [lia|]. fold (wsum (fun it : Z * Z => snd it) t).
        pose proof (NN x (or_introl eq_refl)). assert (0 <= wsum (fun it : Z * Z => snd it) t) by (apply IH; intros y Hy; apply NN; right; exact Hy). lia. }
      unfold BATCHSZ in *. lia. }
    rewrite AE. set (a1 := Z.of_nat (length (List.filter fl Lc))) in *. set (a2 := Z.of_nat (length (List.filter fl (quar st)))) in *.
    set (a3 := Z.of_nat (length (a_cache st c))) in *. set (a4 := Z.of_nat (length (r_free (a_reg st c)))) in *.
    set (a5 := if Z.eqb c BATCHCLASS then Z.of_nat (length (a_tq st ++ a_gq st)) else 0) in *.
    assert (A1 : csize c * a1 <= 65536 * LMAX) by (unfold a1, LMAX in *; nia).
    assert (A0 : 0 <= a1 /\ 0 <= a2 /\ 0 <= a3 /\ 0 <= a4) by ((lazymatch goal with |- ?G => let G' := eval unfold a1, a2, a3, a4 in G in change_no_check G' end); lia).
    nia.
  Qed.
End Room.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RoomThms.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  (* [comment removed for export] *)
  Theorem carve_room : forall st Lc FF c (qt qg : Z), WFq bt st Lc FF qt qg -> 1 <= c <= 30 ->
    a_cache st c = [] -> Z.of_nat (length (r_free (a_reg st c))) < cache_hint c -> qt + qg <= 2 ^ 28 + 2 ^ 21 ->
    r_alloc_user (a_reg st c) + carve_n (a_reg st c) c * csize c <= AMAX.
  Proof.
    intros st Lc FF c qt qg W Hc HC HF HQ.
    pose proof (alloc_bound bt st Lc FF W c Hc) as AB. rewrite HC in AB. cbn [length] in AB.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((Y1 & TI & _) & _). pose proof (csize_pos c Hc) as ((S1 & S2) & _).
    pose proof (AsAinvEntry3.AsAinvHole3.hint_size_le c Hc) as HS.
    assert (CN : carve_n (a_reg st c) c * csize c <= r_mapped_user (a_reg st c) - r_alloc_user (a_reg st c)).
    { (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
    assert (FW : csize c * Z.of_nat (length (r_free (a_reg st c))) <= 65536) by nia.
    unfold AMAX, LMAX, KUSERMAP in *. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem usermap_room : forall st Lc FF c (qt qg : Z), WFq bt st Lc FF qt qg -> 1 <= c <= 30 ->
    r_mapped_user (a_reg st c) - r_alloc_user (a_reg st c) < csize c ->
    r_mapped_user (a_reg st c) + KUSERMAP + KUSERMAP <= KREGION_EXHAUST.
  Proof.
    intros st Lc FF c qt qg W Hc TI. pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((Y1 & _ & YA) & _).
    pose proof (csize_pos c Hc) as ((S1 & S2) & _). unfold AMAX, KUSERMAP, KREGION_EXHAUST in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fa_count_le : forall st Lc FF c (qt qg : Z), WFq bt st Lc FF qt qg -> 1 <= c <= 30 ->
    Z.of_nat (length (r_free (a_reg st c))) * csize c <= r_alloc_user (a_reg st c).
  Proof.
    intros st Lc FF c qt qg W Hc. destruct (alloc_eq bt st Lc FF W c Hc) as [AE N0]. pose proof (csize_pos c Hc) as ((S1 & S2) & _).
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & Y9 & PART & _). destruct PART as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10).
    assert (ND : List.NoDup (map (chunk_of_compact SBEG c) (r_free (a_reg st c)))).
    { apply Finite.Injective_map_NoDup; [| exact P10]. intros k k' E. apply (f_equal (compact_of SBEG c)) in E. rewrite !(AsAinvOpsPf3b.compact_roundtrip_k bt) in E. exact E. }
    assert (IN : incl (map (chunk_of_compact SBEG c) (r_free (a_reg st c))) (CL bt st c)).
    { intros a Ha. apply in_map_iff in Ha. destruct Ha as (k & <- & Hk). destruct (Y9 k Hk) as (_ & (j & Hj & Hle & Ea)).
      (lazymatch goal with |- ?G => let G' := eval unfold CL in G in change_no_check G' end). apply in_map_iff. exists (Z.to_nat j). split; [rewrite Z2Nat.id by lia; symmetry; exact Ea|]. apply in_seq.
      rewrite AE in Hle. assert (j < ncarved st c) by nia. lia. }
    pose proof (NoDup_incl_length ND IN) as LE. unfold CL in LE. rewrite !length_map, length_seq in LE. rewrite AE. nia.
  Qed.

  (* [comment removed for export] *)
  Theorem famap_room : forall st Lc FF c (qt qg : Z), WFq bt st Lc FF qt qg -> 1 <= c <= 30 ->
    r_mapped_fa (a_reg st c) < 4 * (Z.of_nat (length (r_free (a_reg st c))) + carve_n (a_reg st c) c) ->
    r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29.
  Proof.
    intros st Lc FF c qt qg W Hc TEST. pose proof (fa_count_le st Lc FF c qt qg W Hc) as FC.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((Y1 & _) & _ & Y3 & _). pose proof (csize_pos c Hc) as ((S1 & S2) & _).
    assert (CN : carve_n (a_reg st c) c * csize c <= r_mapped_user (a_reg st c) - r_alloc_user (a_reg st c)).
    { (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
    assert (TOT : (Z.of_nat (length (r_free (a_reg st c))) + carve_n (a_reg st c) c) * 32 <= r_mapped_user (a_reg st c)) by nia.
    unfold KFAMAP, KUSERMAP, KREGION_EXHAUST in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma famap_fa_le : forall fa q mu cs, 0 < cs -> 0 <= q -> fa < 4 * q -> q * cs <= mu -> fa <= 4 * (mu / cs).
  Proof.
    intros fa q mu cs CS Q T M.
    assert (q <= mu / cs) by (apply Z.div_le_lower_bound; [lia | rewrite Z.mul_comm; exact M]).
    lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fa_q_pop : forall st Lc FF c (qt qg : Z), WFq bt st Lc FF qt qg -> 1 <= c <= 30 ->
    (Z.of_nat (length (r_free (a_reg st c))) + carve_n (a_reg st c) c) * csize c <= r_mapped_user (a_reg st c).
  Proof.
    intros st Lc FF c qt qg W Hc. pose proof (fa_count_le st Lc FF c qt qg W Hc) as FC.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((Y1 & _) & _). pose proof (csize_pos c Hc) as ((S1 & S2) & _).
    assert (CN : carve_n (a_reg st c) c * csize c <= r_mapped_user (a_reg st c) - r_alloc_user (a_reg st c)).
    { (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
    nia.
  Qed.
  (* [comment removed for export] *)
  Lemma fa_q_drain : forall st Lc FF c (qt qg : Z) (m : Z), WFq bt st Lc FF qt qg -> 1 <= c <= 30 ->
    m <= Z.of_nat (length (a_cache st c)) ->
    (Z.of_nat (length (r_free (a_reg st c))) + m) * csize c <= r_mapped_user (a_reg st c).
  Proof.
    intros st Lc FF c qt qg m W Hc Hm. destruct (alloc_eq bt st Lc FF W c Hc) as [AE N0]. pose proof (csize_pos c Hc) as ((S1 & S2) & _).
    pose proof W as ((WR1 & _) & WC & _). destruct (WR1 c Hc) as ((Y1 & _) & _ & _ & _ & _ & _ & _ & _ & Y9 & PART & _).
    destruct PART as (_ & _ & _ & _ & _ & _ & P7 & _ & P9 & P10). destruct (WC c Hc) as (_ & _ & C3).
    set (L := map (chunk_of_compact SBEG c) (a_cache st c ++ r_free (a_reg st c))).
    assert (INJ : forall k k', chunk_of_compact SBEG c k = chunk_of_compact SBEG c k' -> k = k').
    { intros k k' E. apply (f_equal (compact_of SBEG c)) in E. rewrite !(AsAinvOpsPf3b.compact_roundtrip_k bt) in E. exact E. }
    assert (ND : List.NoDup L).
    { (lazymatch goal with |- ?G => let G' := eval unfold L in G in change_no_check G' end). apply Finite.Injective_map_NoDup; [exact INJ|]. apply NoDup_app; [exact P9 | exact P10 |].
      intros k Hk Hk'. apply (P7 (chunk_of_compact SBEG c k)). split; [exists k; split; [exact Hk | reflexivity] | exists k; split; [exact Hk' | reflexivity]]. }
    assert (IN : incl L (CL bt st c)).
    { intros a Ha. unfold L in Ha. apply in_map_iff in Ha. destruct Ha as (k & <- & Hk). apply in_app_iff in Hk.
      assert (CV : carved bt st c (chunk_of_compact SBEG c k)) by (destruct Hk as [Hk|Hk]; [exact (proj2 (C3 k Hk)) | exact (proj2 (Y9 k Hk))]).
      destruct CV as (j & Hj & Hle & Ea).
      (lazymatch goal with |- ?G => let G' := eval unfold CL in G in change_no_check G' end). apply in_map_iff. exists (Z.to_nat j). split; [rewrite Z2Nat.id by lia; symmetry; exact Ea|]. apply in_seq.
      rewrite AE in Hle. assert (j < ncarved st c) by nia. lia. }
    pose proof (NoDup_incl_length ND IN) as LE. unfold CL, L in LE. rewrite !length_map, length_seq, length_app in LE. rewrite AE in Y1. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma mu_room_charged : forall st Lc FF (st' : ast), WF bt st Lc FF -> a_reg st' = a_reg st -> a_kact st' = a_kact st + EVT -> mu_room st'.
  Proof.
    intros st Lc FF st' W ER EK. pose proof W as (_ & _ & _ & _ & _ & _ & _ & (M1 & _ & _ & M4 & _) & _).
    (lazymatch goal with |- ?G => let G' := eval unfold mu_room in G in change_no_check G' end). rewrite (sum_mu_ext st st') by (intros c Hc; rewrite ER; reflexivity). rewrite EK.
    replace ((a_kact st + EVT) / EVT) with (a_kact st / EVT + 1)
      by (rewrite <- (Z.div_add (a_kact st) 1 EVT ltac:((lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia)); f_equal; lia).
    unfold KUSERMAP in *. lia.
  Qed.
End RoomThms.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Grant.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Lemma free_apart_maps0 : forall st mdl (a : word) (n : Z), rep_ledger bt st mdl -> 0 <= n < 2 ^ 64 ->
    region_free (vm_reserved (m_vmmaps mdl) ++ vm_maps (m_vmmaps mdl)) a (Z_to_bv 64 n) = true ->
    forall b n0, In (b, n0) (bt_maps0 bt) -> bv_unsigned a + n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned n0 <= bv_unsigned a.
  Proof.
    intros st mdl a n RL Hn RF b n0 Hin. pose proof (AsAinvEntry3.AsKSys4.maps0_in_vm_maps bt st mdl (b, n0) RL Hin) as HV.
    pose proof (region_free_In _ a (Z_to_bv 64 n) b n0 RF ltac:(apply in_app_iff; right; exact HV)) as D.
    rewrite Z_to_bv_unsigned in D. unfold bv_wrap, bv_modulus in D. change (2 ^ Z.of_N 64) with (2 ^ 64) in D. rewrite Z.mod_small in D by lia. exact D.
  Qed.
  (* [comment removed for export] *)
  Lemma grant_apart_maps0 : forall st mdl hint (a : word) (n : Z), rep_ledger bt st mdl -> 0 <= n < 2 ^ 64 -> grant_ok hint mdl a n = true ->
    forall b n0, In (b, n0) (bt_maps0 bt) -> bv_unsigned a + n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned n0 <= bv_unsigned a.
  Proof.
    intros st mdl hint a n RL Hn G. unfold grant_ok in G. apply andb_prop in G. destruct G as [G _]. apply andb_prop in G. destruct G as [_ RF].
    exact (free_apart_maps0 st mdl a n RL Hn RF).
  Qed.

End Grant.
