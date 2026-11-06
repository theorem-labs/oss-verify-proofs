(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp.AsDepotImg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section Bud2.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.

  Definition in_rangesb (L : list (Z * Z)) (z : Z) : bool := existsb (fun r => (fst r <=? z) && (z <? snd r)) L.
  Definition HF (st : ast) : word -> bool :=
    fun w => (U w <? CEIL) && negb ((AIMGLO <=? U w) && (U w <? AIMGHI)) && negb (in_rangesb (all_ranges bt st) (U w)).
  Definition HD2 (Hd : word -> bool) (st : ast) : word -> bool := fun w => Hd w || HF st w.

  Lemma hf_off : forall st (w : word), (CEIL <= U w \/ (AIMGLO <= U w /\ U w < AIMGHI)) -> HF st w = false.
  Proof using.
    intros st w [H | [H1 H2]]; (lazymatch goal with |- ?G => let G' := eval unfold HF in G in change_no_check G' end).
    - rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
    - rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2). (lazymatch goal with |- ?G => let G' := eval cbn [andb negb] in G in change_no_check G' end). rewrite andb_false_r. reflexivity.
  Qed.

  Lemma hf_fresh : forall st a n (w : word), (forall lo hi, In (lo, hi) (all_ranges bt st) -> a + n <= lo \/ hi <= a) -> a + n <= CEIL -> AIMGHI <= a ->
    a <= U w < a + n -> HF st w = true.
  Proof using.
    intros st a n w AP HC HI Hw. (lazymatch goal with |- ?G => let G' := eval unfold HF in G in change_no_check G' end). rewrite (proj2 (Z.ltb_lt _ _)) by lia.
    replace (U w <? AIMGHI) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. (lazymatch goal with |- ?G => let G' := eval cbn [negb andb] in G in change_no_check G' end).
    destruct (in_rangesb (all_ranges bt st) (U w)) eqn:E; [| reflexivity]. exfalso.
    unfold in_rangesb in E. apply existsb_exists in E as ([lo hi] & Hin & T). cbn [fst snd] in T. apply andb_prop in T as [T1 T2].
    apply Z.leb_le in T1. apply Z.ltb_lt in T2. destruct (AP lo hi Hin); lia.
  Qed.
  Lemma hd2_off : forall Hd st (w : word), Hd w = false -> (CEIL <= U w \/ (AIMGLO <= U w /\ U w < AIMGHI)) -> HD2 Hd st w = false.
  Proof using. intros Hd st w H1 H2. (lazymatch goal with |- ?G => let G' := eval unfold HD2 in G in change_no_check G' end). rewrite H1, (hf_off st w H2). reflexivity. Qed.

  Lemma hoff_hd2 : forall Hd st, H_off_segments ASEGS Hd -> H_off_segments ASEGS (HD2 Hd st).
  Proof using.
    intros Hd st HO a Ha. unfold HD2 in Ha. apply orb_true_iff in Ha as [Ha | Ha]; [exact (HO a Ha)|].
    unfold HF in Ha. apply andb_prop in Ha as [Ha _]. apply andb_prop in Ha as [_ Ha]. apply negb_true_iff in Ha.
    apply asanF_segs_off. pose proof (u64_range a). apply andb_false_iff in Ha as [Ha | Ha]; [apply Z.leb_gt in Ha; left; lia | apply Z.ltb_ge in Ha; right; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma lazy_cover_hd2_cons : forall Hd st (lazy : list (word * word)) A (a n : word),
    lazy_cover Hd lazy A -> U a mod 4096 = 0 -> U n mod 4096 = 0 ->
    (forall w : word, U a <= U w < U a + U n -> HF st w = true) ->
    lazy_cover (HD2 Hd st) ((a, n) :: lazy) A.
  Proof using.
    intros Hd st lazy A a n LC AA NA FR w Hp Hh. unfold HD2 in Hh. apply orb_false_iff in Hh as [Hh1 Hh2].
    rewrite AsKSys6.AsanNodesMmLib.page_in_ranges_cons in Hp. cbn [fst snd] in Hp. apply orb_true_iff in Hp as [Hp | Hp]; [| exact (LC w Hp Hh1)].
    exfalso. apply andb_prop in Hp as [P1 P2]. apply Z.leb_le in P1. apply Z.leb_le in P2. unfold page_size in P2.
    pose proof (AsKSys6.AsanNodesMmLib.page_base_facts w) as (B1 & B2 & _).
    rewrite (FR w ltac:(lia)) in Hh2. discriminate Hh2.
  Qed.
  Lemma lazy_cover_hd2 : forall Hd st lazy A, lazy_cover Hd lazy A -> lazy_cover (HD2 Hd st) lazy A.
  Proof using. intros Hd st lazy A LC w Hp Hh. unfold HD2 in Hh. apply orb_false_iff in Hh as [Hh1 _]. exact (LC w Hp Hh1). Qed.

  (* [comment removed for export] *)
  Theorem depot_grow_budget : forall st Lc FF M0 mdl (qt qg kn ks : Z),
    Rep bt st Lc FF M0 mdl -> WFq bt st Lc FF qt qg -> qt + qg <= 2 ^ 28 + 2 ^ 21 -> a_kact st <= KCAP -> 0 <= kn <= 1 -> 0 <= ks <= 1 ->
    eager_used mdl + 2 ^ 20 * kn + 2 ^ 23 * ks + A_bytes (a_aa st) <= vm_limit (m_vmmaps mdl).
  Proof using.
    intros st Lc FF M0 mdl qt qg kn ks R W HQ KC Hkn Hks.
    (* [comment removed for export] *)
    pose proof (budget_room bt st Lc FF qt qg W HQ KC) as BR.
    destruct (ledger_R bt st Lc FF M0 mdl R) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LIM & _).
    destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & BUD & _) & _).
    unfold ROOMSLACK in BR. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma A_bytes_snoc : forall A lo hi, A_bytes (A ++ [(lo, hi)]) = A_bytes A + (hi - lo).
  Proof using. induction A as [|iv t IH]; intros lo hi; (lazymatch goal with |- ?G => let G' := eval cbn [app A_bytes fst snd] in G in change_no_check G' end); [lia | rewrite IH; lia]. Qed.
  Lemma A_wf_snoc : forall A lo hi, A_wf A -> lo <= hi -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> A_wf (A ++ [(lo, hi)]).
  Proof using. intros A lo hi W H1 H2 H3. unfold A_wf in *. apply Forall_app. split; [exact W|]. constructor; [| constructor]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end). auto. Qed.
  Lemma page_allowedb_app_l : forall A B p, page_allowedb A p = true -> page_allowedb (A ++ B) p = true.
  Proof using. intros A B p H. unfold page_allowedb in *. rewrite existsb_app, H. reflexivity. Qed.
  Lemma MInv_snoc : forall A B m, MInv A m -> eager_used m + A_bytes (A ++ B) <= vm_limit (m_vmmaps m) -> MInv (A ++ B) m.
  Proof using. intros A B m [N1 N2 N3 N4 N5] BUD. constructor; try assumption. intros p Hp. apply page_allowedb_app_l. exact (N3 p Hp). Qed.
  Lemma lazy_cover_snoc : forall Hd lazy A B, lazy_cover Hd lazy A -> lazy_cover Hd lazy (A ++ B).
  Proof using. intros Hd lazy A B LC w Hp Hh. apply page_allowedb_app_l. exact (LC w Hp Hh). Qed.
  (* [comment removed for export] *)
  Lemma grant_nr_facts_x : forall st Lc FF M0 mdl mdlm (qt qg : Z) (hint a : word) (nn : option Z) (h : option Z),
    WFq bt st Lc FF qt qg -> Rep bt st Lc FF M0 mdl -> boot_geom bt ->
    vm_reserved (m_vmmaps mdlm) = vm_reserved (m_vmmaps mdl) ->
    vm_maps (m_vmmaps mdlm) = List.map (fun p => (Z_to_bv 64 p, Z_to_bv 64 (2 ^ 20))) (blk_opt nn) ++ vm_maps (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdlm) = vm_init_sp (m_vmmaps mdl) ->
    (forall p, nn = Some p -> 0 <= p /\ p + 2 ^ 20 < 2 ^ 64) ->
    holes_le h st ->
    grant_ok_nr hint mdlm a (2 ^ 23) = true ->
    dyn_ok (bt_ia bt) (U a) (U a + 2 ^ 23) /\ U a mod PG = 0
    /\ (forall lo hi, In (lo, hi) (all_ranges bt st) -> U a + 2 ^ 23 <= lo \/ hi <= U a)
    /\ (forall p, nn = Some p -> p + 2 ^ 20 <= U a \/ U a + 2 ^ 23 <= p)
    /\ (forall b0 n0, In (b0, n0) (bt_maps0 bt) -> U a + 2 ^ 23 <= U b0 \/ U b0 + U n0 <= U a).
  Proof using.
    intros st Lc FF M0 mdl mdlm qt qg hint a nn h W R BG ER EM ES NNR HOLE G.
    apply grant_ok_nr_unpack in G. destruct G as (G1 & G2 & G3 & G4). unfold page_size in G1.
    assert (TOP : U a + 2 ^ 23 <= alloc_top (m_vmmaps mdl)) by (unfold alloc_top in *; rewrite <- ES; exact G3).
    rewrite ER, EM in G4. rewrite !RefNodes.region_free_app in G4. apply andb_prop in G4 as [F1 F23]. apply andb_prop in F23 as [F2 F3].
    assert (FREE : region_free (vm_reserved (m_vmmaps mdl) ++ vm_maps (m_vmmaps mdl)) a (Z_to_bv 64 (2 ^ 23)) = true)
      by (rewrite RefNodes.region_free_app, F1, F3; reflexivity).
    assert (NZ : 0 < 2 ^ 23) by lia. assert (NAL : 2 ^ 23 mod 4096 = 0) by reflexivity.
    destruct (g_lits bt st Lc FF M0 mdl R a (2 ^ 23) G1 G2 NZ NAL TOP) as (_ & UN & _).
    assert (SZ19 : 2 ^ 19 < 2 ^ 23) by lia.
    split; [exact (grant_dyn_ok bt st Lc FF M0 mdl R BG a (2 ^ 23) G1 G2 NZ NAL TOP FREE)|].
    split; [exact G1|].
    split; [intros lo hi Hin; exact (grant_apart_all bt st Lc FF M0 mdl W R BG a (2 ^ 23) G1 G2 NZ NAL TOP FREE h (or_intror (conj SZ19 HOLE)) lo hi Hin)|].
    split.
    - intros p E. subst nn. cbn [blk_opt List.map] in F2. destruct (NNR p eq_refl) as [P0 P1].
      pose proof (RefNodes.region_free_In _ a _ (Z_to_bv 64 p) (Z_to_bv 64 (2 ^ 20)) F2 (or_introl eq_refl)) as AP.
      rewrite UN in AP. rewrite !Spec4.AgentLib.u64_lit in AP by lia. lia.
    - intros b0 n0 Hin.
      assert (Hin' : In (b0, n0) (vm_maps (m_vmmaps mdl))).
      { destruct (ledger_R bt st Lc FF M0 mdl R) as ((F6 & PM & _) & _). apply (Permutation.Permutation_in _ (Permutation.Permutation_sym PM)).
        apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
      pose proof (RefNodes.region_free_In _ a _ b0 n0 F3 Hin') as AP. rewrite UN in AP. exact AP.
  Qed.
End Bud2.

(* [comment removed for export] *)
Lemma ss_len : Z.of_nat 65552 = 65552.
Proof. vm_compute. reflexivity. Qed.
Lemma ss_store_ok : forall {fx : FPState} (m : word -> option byte) (x : word) (n : nat), 0x1d9448 <= U x -> U x + Z.of_nat n <= 0x1d9448 + 65552 -> store_ok ASEGS m x n = true.
Proof.
  intros fx m x n H1 H2. apply (rwseg_store_ok ASEGS _ (Z_to_bv 64 0x1d9448) m x n ss_img_ok).
  - rewrite ss_len. change (U (Z_to_bv 64 0x1d9448)) with 0x1d9448. lia.
  - change (U (Z_to_bv 64 0x1d9448)) with 0x1d9448. exact H1.
  - rewrite ss_len. change (U (Z_to_bv 64 0x1d9448)) with 0x1d9448. exact H2.
Qed.

(* [comment removed for export] *)
Lemma sev_mmap_model_nr : forall (a n : word) (m : Model), same_except_vm m (mmap_model_noreserve a n m).
Proof. intros a n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma le8_word2 : forall bs, length bs = 8%nat -> word_to_le_bytes 8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof. intros bs Hl. apply AsAinvHoleP3.AsanPlanSoundSums.APSX.word_to_le_bytes_of_bytes_n; [exact Hl | auto]. Qed.

(* [comment removed for export] *)
Lemma mrestrict_clean_mem : forall {fx : FPState} (H : word -> bool) (full : word -> option byte) (r : bvmap 5 word) (pc : word) (m rom : word -> option byte),
  hclean H (@mkst fx r pc m rom) -> mrestrict H (munrestrict H full m) = m.
Proof.
  intros fx H full r pc m rom HC. rewrite mrestrict_munrestrict. apply functional_extensionality. intro a. (lazymatch goal with |- ?G => let G' := eval unfold mrestrict in G in change_no_check G' end).
  destruct (H a) eqn:E; [symmetry; exact (HC a E) | reflexivity].
Qed.
