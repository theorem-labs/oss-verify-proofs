(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanCtrlProps AsanEmbed AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanTotal AsanFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ABase AProto ATsafeCore ATsafeEv ATsafeAlloc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import EdDefs.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.

Definition NLK0 : Z := EAGER0 + CBM + 2^37 + 2^32.

Definition CRED0 : Z := 3 * 2^34.
Definition C_EXH : Z := 2^20.

Definition Abase_of (SB PA : Z) : alw :=
  fun p => exists z', (shad SB <= z' < shad (SB + K_SPACE_SIZE) \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) /\ p = page_base_of z'.

Definition c24_ok (n : Z) : bool := implb (class_id (needed_size n) =? K_BATCH_CLASS) ((5881 <=? n) && (n <=? 7936)).
Lemma c24_ok_range : forallb c24_ok (zseq 0 (Z.to_nat 64513)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma c24_range : forall n, 0 <= n <= 64512 -> class_id (needed_size n) = K_BATCH_CLASS -> 5881 <= n <= 7936.
Proof.
  intros n Hn Hc. pose proof (forallb_zseq c24_ok 0 (Z.to_nat 64513) c24_ok_range n ltac:(rewrite Z2Nat.id; lia)) as H.
  unfold c24_ok in H. rewrite Hc, Z.eqb_refl in H. cbn [implb] in H. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma NLK0_nonneg : 0 <= NLK0. Proof. vm_compute. discriminate. Qed.

Section OpsM.
Variable NMAX : nat.
Local Notation NMAXZ := (Z.of_nat NMAX).
Hypothesis HLIM : NLK0 + NMAXZ * 4096 <= LIMIT.
Variable RESV : list (Z * Z).

Variable AFIX : alw.
Definition Abase_x (SB PA : Z) : alw := fun p => Abase_of SB PA p \/ AFIX p.
Local Notation INV := (AsanInv.INV RESV ATOP).
Local Notation TS := (TS NMAX).

Definition ACCTc (v : Z) (RNG : footprint) (A : alw) (st : astate) (mo : Model) : Prop :=
  INV [] [] st mo /\ a_qloc_bytes st <= Q_CACHE /\ a_qglob_bytes st <= Q_MAX
  /\ RNG = fp_ok (m_vm_lazy mo) A
  /\ 0 <= v <= CRED0
  /\ 110 * secbytes (live_chunks st) + C_EXH * emb_sz st <= 110 * (CRED0 - v)
  /\ exists k, alw_le (Abase_x (a_space_beg st) (a_ptr_array st)) A /\ (forall p, COVP mo p -> A p) /\ abud A k /\ 0 <= k
               /\ 1024 * (k + GP st) + v <= 1024 * NMAXZ.

Lemma ACCTc_weaken : forall v v' RNG A st mo, ACCTc v RNG A st mo -> 0 <= v' <= v -> ACCTc v' RNG A st mo.
Proof.
  intros v v' RNG A st mo (HI & Q1 & Q2 & ER & Hv & HC & k & HAB & HCV & HBU & Hk & HP) Hv'.
  split; [exact HI|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact ER|]. split; [lia|]. split; [lia|].
  exists k. split; [exact HAB|]. split; [exact HCV|]. split; [exact HBU|]. split; [exact Hk| lia].
Qed.

Lemma MOK_of_AMI : forall ch st mo, AMI RESV ATOP ch st mo -> MOK mo.
Proof.
  intros ch st mo HM. pose proof (AMI_ivs_wf _ _ _ HM) as W. destruct HM as (M1 & M2 & _ & _ & _ & M6 & _ & _ & M9 & [_ M10] & _).
  split; [exact M1|]. split; [exact M2|]. split; [exact W|]. split; [exact (proj1 M9)| split; [exact M6| exact M10]].
Qed.

Lemma chunk_cls_ok_wf : forall ch, chunk_wf ATOP ch -> chunk_cls_ok ch.
Proof.
  intros [c n|mb ms n] H; cbn in *; [| exact I]. destruct H as [Hn Hc].
  pose proof (prim_cls_facts c n Hn Hc) as (C1 & _). lia.
Qed.

Lemma LW_of_AINV : forall st, AINV ATOP [] [] st -> LW (a_space_beg st) (a_ptr_array st) st.
Proof.
  intros st HA. pose proof HA as (HC & HW & _ & _ & _ & _ & (j & Hj & Hres) & _ & _ & _ & _ & _ & _ & HE).
  split; [reflexivity|]. split; [reflexivity|]. split; [unfold K_CHUNKS_BLOCK in Hres; lia|]. split; [unfold K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *; lia|].
  split; [| split].
  - intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in X. cbv zeta in X. unfold cls_lw. lia.
  - unfold emb_ok in HE. unfold emb_lw, emb_cap, emb_sz. destruct (a_emb st) as [[d cap] sz]. cbn [fst snd].
    destruct HE as [[-> ->]|(E1 & E2 & _ & _ & E5 & _)]; [unfold EMB_MAX; cbn; lia| unfold EMB_INIT in E1; lia].
  - unfold QOK. eapply Forall_impl; [| exact HW]. intros ch Hch. apply chunk_cls_ok_wf. exact Hch.
Qed.

Lemma CHX_bound : forall st, AINV ATOP [] [] st -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> zsum2 (CHX [] [] st) <= 2^37.
Proof.
  intros st HA Q1 Q2.
  destruct (CH_bounds [] [] st HA) as [_ X]; [| unfold zlen; cbn; lia| cbn; lia|].
  { unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA as (_ & _ & _ & Hb1 & Hb2 & _). unfold Q_CACHE, Q_MAX in *. lia. }
  rewrite zsum2_CHX. pose proof (emb_ent_zsum2 _ _ _ HA) as EZ. unfold EMB_MAX in EZ. lia.
Qed.

Lemma KI_entry : forall v RNG A st mo extra,
  ACCTc v RNG A st mo -> 0 <= extra <= 2^32 ->
  exists k, KI (Abase_x (a_space_beg st) (a_ptr_array st)) NLK0 (PHI st + extra) A k mo
            /\ 1024 * (k + GP st) + v <= 1024 * NMAXZ /\ LW (a_space_beg st) (a_ptr_array st) st.
Proof.
  intros v RNG A st mo extra (HI & Q1 & Q2 & ER & Hv & HC & k & HAB & HCV & HBU & Hk & HP) Hex. pose proof HI as [HA HM].
  exists k. assert (HL : LW (a_space_beg st) (a_ptr_array st) st) by (apply LW_of_AINV; exact HA).
  split; [| split; [exact HP| exact HL]].
  pose proof (PHI_nonneg _ _ _ HL). pose proof (commit_bytes_LW _ _ _ HL).
  pose proof (AMI_nonlazy_bound _ _ _ HM (CHX_wf _ _ _ HA)). pose proof (CHX_bound st HA Q1 Q2).
  split; [eapply MOK_of_AMI; exact HM|]. split; [lia|]. split; [unfold PHI, NLK0 in *; lia|].
  split; [exact HAB|]. split; [exact HCV|]. split; [exact HBU| exact Hk].
Qed.

Lemma INV_SB_PA : forall st mo, INV [] [] st mo ->
  (0 <= a_space_beg st /\ a_space_beg st + K_SPACE_SIZE <= ATOP) /\ (0 <= a_ptr_array st /\ a_ptr_array st + K_PTRARR_RESERVE <= ATOP).
Proof.
  intros st mo HI. destruct (INV_prim _ _ _ _ HI) as (pb0 & _ & P1 & P2 & P3 & P4). destruct (INV_ptr _ _ _ _ HI) as (_ & Q1 & _).
  destruct HI as [HA _]. destruct (AINV_geom _ _ _ HA) as (_ & G2 & _ & G4).
  unfold K_SPACE_SIZE, K_PTRARR_RESERVE, PTR_SZ, PRIM_SZ in *. lia.
Qed.

Lemma pcost_sec : forall n, 64512 < n <= 2^40 -> 1024 * pcost (sec_map_size n) <= n.
Proof.
  intros n Hn. pose proof (sec_map_size_bounds n Hn) as SBn. unfold pcost.
  set (s := sec_map_size n) in *.
  pose proof (Z.div_le_mono s (n + 12296) 4096 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono s (n + 12296) 32768 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_mod (n + 12296) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 4096 ltac:(lia)).
  pose proof (Z.div_mod (n + 12296) 32768 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 32768 ltac:(lia)).
  lia.
Qed.

Lemma secbytes_perm : forall l l', Permutation l l' -> secbytes l = secbytes l'.
Proof. intros l l' HP. induction HP as [| [c n|mb ms n] l l' _ IH | [c n|mb ms n] [c' n'|mb' ms' n'] l | l l' l'' _ IH1 _ IH2]; cbn [secbytes]; lia. Qed.

Definition malloc_leaf (v n : Z) (st : astate) (mo0 : Model) (RNG0 : footprint) : postT (astate * option AsanCtrl.aptr) :=
  fun r RNG' A' mo' =>
    vmh mo0 mo' /\ fp_le RNG0 RNG' /\
    (is_primary n = false -> cls_keep K_BATCH_CLASS st (fst r)) /\
    match snd r with
    | Some p => p = a_next st /\ (a_live st) !! p = None
                /\ (exists ch, a_live (fst r) = <[p := ch]> (a_live st) /\ chunk_size ch = n)
                /\ ACCTc (v - (if is_primary n then 0 else n)) RNG' A' (fst r) mo'
    | None => a_live (fst r) = a_live st /\ a_next (fst r) = a_next st /\ ACCTc (v - C_EXH) RNG' A' (fst r) mo'
    end.

Theorem U_malloc_g : forall (NN : Prop) v RNG A st mo n,
  ACCTc v RNG A st mo -> 1 <= n <= AREQMAX -> (is_primary n = false -> n <= v) -> C_EXH <= v ->
  size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX ->
  (is_primary n = true -> class_id (needed_size n) <> K_BATCH_CLASS ->
     K_FREEARR_OFF < c_mapped_user (get_cls st (class_id (needed_size n))) + K_USER_MAP -> NN) ->
  (is_primary n = false -> vm_gap_available (m_vmmaps mo) (sec_map_size n) = false -> NN) ->
  TS RNG A (aembed ATOP (amalloc ATOP RESV st n)) mo (fun r RNG' A' mo' => malloc_leaf v n st mo RNG r RNG' A' mo' /\ (snd r = None -> NN)).
Proof.
  intros NN v RNG A st mo n HACC Hn Hnv Hcv H24 HNN1 HNN2. unfold AREQMAX in Hn.
  pose proof HACC as (HI & Q1 & Q2 & ER & Hv & HC & _). pose proof HI as [HA HM].
  pose proof (secs_bounds (ATOP:=ATOP) (live_chunks st)) as SBD.
  assert (HWl : Forall (chunk_wf ATOP) (live_chunks st)).
  { destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HW _]. exact HW. }
  destruct (SBD HWl) as (S1 & _ & S3).
  assert (E0 : 0 <= emb_sz st) by (pose proof (LW_emb _ _ _ (LW_of_AINV st HA)) as (_ & _ & X); exact X).
  assert (HEMB : emb_sz st + 110 <= EMB_MAX - 4096) by (unfold C_EXH, CRED0, EMB_MAX in *; lia).
  assert (HLB : forall mb ms, live_budget_list (mkch n mb ms :: live_chunks st)).
  { intros mb ms. assert (S24 : size_of_class K_BATCH_CLASS = 8192) by reflexivity. rewrite S24 in *.
    pose proof (cntP_nonneg K_BATCH_CLASS (live_chunks st)) as CN0.
    unfold live_budget_list, mkch. rewrite S24. destruct (is_primary n) eqn:EP.
    - rewrite cntP_cons. change (secs (CPrim (class_id (needed_size n)) n :: live_chunks st)) with (secs (live_chunks st)). cbn [secbytes]. split; [| split].
      + destruct (is_prim_of K_BATCH_CLASS (CPrim (class_id (needed_size n)) n)); unfold L24MAX in *; lia.
      + unfold SMAX, CRED0, C_EXH in *. lia.
      + unfold LSBYTES, CRED0, C_EXH in *. lia.
    - specialize (Hnv eq_refl). rewrite cntP_cons. cbn [is_prim_of]. change (secs (CSec mb ms n :: live_chunks st)) with ((mb, ms) :: secs (live_chunks st)).
      rewrite zlen_cons. cbn [secbytes]. split; [| split].
      + unfold L24MAX in *. lia.
      + pose proof (not_primary_large n ltac:(lia) EP). unfold SMAX, CRED0, C_EXH in *. lia.
      + unfold LSBYTES, CRED0, C_EXH in *. lia. }
  pose proof (amalloc_core_g (RESV:=RESV) (ATOP:=ATOP) NN st mo n HI Q1 Q2 ltac:(lia) HLB HEMB HNN1 HNN2) as HTOT.
  set (SB := a_space_beg st) in *. set (PA := a_ptr_array st) in *.
  set (gx := if is_primary n then 0 else pcost (sec_map_size n)).
  set (bx := if is_primary n then EXB else sec_map_size n).
  assert (Hbx : 0 <= bx <= 2^32).
  { unfold bx. destruct (is_primary n) eqn:EP; [unfold EXB, EMB_MAX; lia|].
    pose proof (not_primary_large n ltac:(lia) EP). pose proof (sec_map_size_bounds n ltac:(lia)). lia. }
  destruct (KI_entry v RNG A st mo bx HACC Hbx) as (k & HK & HP & HL).
  pose proof (evq_amalloc SB PA RESV st n HL ltac:(lia) HEMB) as HEV. fold gx bx in HEV.
  destruct (INV_SB_PA st mo HI) as [HSB HPA].
  assert (Hgx : 0 <= gx).
  { unfold gx. destruct (is_primary n) eqn:EP; [lia|]. pose proof (not_primary_large n ltac:(lia) EP). pose proof (sec_map_size_bounds n ltac:(lia)). apply pcost_nonneg. lia. }
  pose proof (GP_nonneg st (LW_emb _ _ _ HL)) as G0.
  assert (CHG : 0 <= (if is_primary n then 0 else n) <= v /\ 1024 * gx <= (if is_primary n then 0 else n)).
  { unfold gx. destruct (is_primary n) eqn:EP; [lia|]. specialize (Hnv eq_refl). split; [lia|]. apply pcost_sec. pose proof (not_primary_large n ltac:(lia) EP). lia. }
  pose proof (TS_aembed NMAX SB PA (Abase_x SB PA) NLK0 HLIM
                ltac:(intros z' Hz'; left; exists z'; split; [exact Hz'| reflexivity])
                (amalloc ATOP RESV st n) (RPm SB PA n) (fun r mo' => malloc_post st n r mo' /\ (snd r = None -> NN)) (GP st + gx) (PHI st + bx) A k (k + (GP st + gx)) mo RNG mo
                HTOT HEV HK (vmh_refl mo) ltac:(rewrite ER; apply fp_le_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as HTS.
  rewrite ER. eapply TS_mono; [exact HTS|].
  intros r RNG' A' mo' _ (b' & k' & gp' & HRP & [HPOST HNN] & HK' & Hgp' & Hkg & HH & HFL & ERN).
  destruct HRP as [HL' HGP']. destruct HK' as (_ & _ & _ & HAB' & HCV' & HBU' & Hk').
  pose proof HL' as (ESB & EPA & _).
  split; [| exact HNN].
  split; [exact HH|]. split; [rewrite <- ER; exact HFL|].
  destruct HPOST as [(ch & Esnd & HI' & ELIVE & ENONE & ESZ & B1 & B2 & B3 & B4 & EEMB & CK)|(Esnd & HI' & ELIVE & ENEXT & B1 & B2 & B3 & B4 & EEMB & CK)]; rewrite Esnd in *.
  -
    split; [exact CK|].
    split; [reflexivity|]. split; [exact ENONE|]. split; [exists ch; split; [exact ELIVE| exact ESZ]|].
    assert (ESB' : secbytes (live_chunks (fst r)) <= secbytes (live_chunks st) + (if is_primary n then 0 else n)).
    { assert (PL : Permutation (live_chunks (fst r)) (ch :: live_chunks st)).
      { pose proof (live_chunks_insert st (a_next st) ch ENONE) as X. unfold live_chunks in X |- *. cbn [a_live set_live] in X. rewrite ELIVE. exact X. }
      rewrite (secbytes_perm _ _ PL).
      assert (Hwf : chunk_wf ATOP ch).
      { destruct HI' as [HA' _]. destruct HA' as (_ & HW' & _). unfold all_chunks in HW'. cbn [app] in HW'. apply Forall_app in HW' as [HW' _].
        eapply (proj1 (Forall_forall _ _) HW'). eapply Permutation_in; [apply Permutation_sym; exact PL| left; reflexivity]. }
      destruct ch as [c0 n0|mb0 ms0 n0]; cbn [secbytes chunk_size] in *; [destruct (is_primary n); lia|].
      subst n0. cbn in Hwf. rewrite (large_not_primary n) by lia. lia. }
    assert (EES : emb_sz (fst r) = emb_sz st) by (unfold emb_sz; rewrite EEMB; reflexivity).
    assert (EGP : GP (fst r) = GP st) by (unfold GP, emb_cap; rewrite EEMB; reflexivity).
    split; [exact HI'|]. split; [lia|]. split; [lia|]. split; [exact ERN|]. split; [lia|]. split; [lia|].
    exists k'. rewrite ESB, EPA. split; [exact HAB'|]. split; [exact HCV'|]. split; [exact HBU'|]. split; [exact Hk'|]. lia.
  -
    split; [exact CK|].
    split; [exact ELIVE|]. split; [exact ENEXT|].
    assert (ESB' : secbytes (live_chunks (fst r)) = secbytes (live_chunks st)) by (unfold live_chunks; rewrite ELIVE; reflexivity).
    split; [exact HI'|]. split; [lia|]. split; [lia|]. split; [exact ERN|]. split; [unfold C_EXH in *; lia|]. split; [unfold C_EXH in *; lia|].
    exists k'. rewrite ESB, EPA. split; [exact HAB'|]. split; [exact HCV'|]. split; [exact HBU'|]. split; [exact Hk'|].
    assert (0 <= (if is_primary n then 0 else pcost (sec_map_size n))) by (fold gx; exact Hgx). unfold C_EXH. lia.
Qed.

Theorem U_malloc : forall v RNG A st mo n,
  ACCTc v RNG A st mo -> 1 <= n <= AREQMAX -> (is_primary n = false -> n <= v) -> C_EXH <= v ->
  size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX ->
  TS RNG A (aembed ATOP (amalloc ATOP RESV st n)) mo (malloc_leaf v n st mo RNG).
Proof.
  intros v RNG A st mo n HACC Hn Hnv Hcv H24.
  eapply TS_mono; [apply (U_malloc_g True v RNG A st mo n HACC Hn Hnv Hcv H24); intros; exact I|].
  intros r RNG' A' mo' _ [H _]. exact H.
Qed.

Theorem U_malloc_nn_prim : forall v RNG A st mo n,
  ACCTc v RNG A st mo -> 1 <= n <= 64512 -> C_EXH <= v ->
  size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX ->
  (forall c, 1 <= c <= 31 -> c <> K_BATCH_CLASS -> c_mapped_user (get_cls st c) = 0) ->
  TS RNG A (aembed ATOP (amalloc ATOP RESV st n)) mo (fun r RNG' A' mo' => malloc_leaf v n st mo RNG r RNG' A' mo' /\ snd r <> None).
Proof.
  intros v RNG A st mo n HACC Hn Hcv H24 HPR.
  assert (HP : is_primary n = true) by (rewrite is_primary_iff by lia; apply Z.leb_le; lia).
  eapply TS_mono; [apply (U_malloc_g False v RNG A st mo n HACC ltac:(unfold AREQMAX; lia) ltac:(intros X; rewrite HP in X; discriminate X) Hcv H24)|].
  - intros _ N24 HEX. pose proof (primary_class_facts n ltac:(lia) HP) as F. cbv zeta in F. destruct F as (F1 & _).
    rewrite (HPR (class_id (needed_size n)) ltac:(lia) N24) in HEX. unfold K_FREEARR_OFF, K_USER_MAP in HEX. lia.
  - intros X. rewrite HP in X. discriminate X.
  - intros r RNG' A' mo' _ [H HN]. split; [exact H|]. intros E. exact (HN E).
Qed.
Theorem U_malloc_nn_sec : forall v RNG A st mo n,
  ACCTc v RNG A st mo -> 64512 < n <= 2^28 -> n <= v -> CRED0 - 2^30 <= v ->
  size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX ->
  TS RNG A (aembed ATOP (amalloc ATOP RESV st n)) mo (fun r RNG' A' mo' => malloc_leaf v n st mo RNG r RNG' A' mo' /\ snd r <> None).
Proof.
  intros v RNG A st mo n HACC Hn Hnv Hcv H24.
  pose proof HACC as (HI & Q1 & Q2 & ER & Hv & HC & _). pose proof HI as [HA HM].
  assert (HP : is_primary n = false) by (apply large_not_primary; lia).
  assert (E0 : 0 <= emb_sz st) by (pose proof (LW_emb _ _ _ (LW_of_AINV st HA)) as (_ & _ & X); exact X).
  assert (HLB : secbytes (live_chunks st) <= 2^30) by (unfold C_EXH, CRED0 in *; nia).
  eapply TS_mono; [apply (U_malloc_g False v RNG A st mo n HACC ltac:(unfold AREQMAX; lia) ltac:(intros _; exact Hnv) ltac:(unfold C_EXH, CRED0 in *; lia) H24)|].
  - intros X. rewrite HP in X. discriminate X.
  - intros _ NG. rewrite (INV_gap_sec (RESV:=RESV) (ATOP:=ATOP) st mo n HI ltac:(lia) HLB Q1 Q2 (CHX_bound st HA Q1 Q2)) in NG. discriminate NG.
  - intros r RNG' A' mo' _ [H HN]. split; [exact H|]. intros E. exact (HN E).
Qed.

Theorem U_aligned16 : forall v RNG A st mo n,
  ACCTc v RNG A st mo -> 16 <= n <= ALIGNED_NMAX -> n mod 16 = 0 -> C_EXH <= v ->
  TS RNG A (aembed ATOP (aaligned16x ATOP RESV st n)) mo (malloc_leaf v n st mo RNG).
Proof.
  intros v RNG A st mo n HACC Hn Hm Hcv.
  pose proof HACC as (HI & Q1 & Q2 & ER & Hv & HC & _). pose proof HI as [HA HM].
  pose proof (al16_facts n Hn Hm) as F. cbv zeta in F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EP).
  assert (E0 : 0 <= emb_sz st) by (pose proof (LW_emb _ _ _ (LW_of_AINV st HA)) as (_ & _ & X); exact X).
  pose proof (secs_bounds (ATOP:=ATOP) (live_chunks st)) as SBD.
  assert (HWl : Forall (chunk_wf ATOP) (live_chunks st)).
  { destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HW _]. exact HW. }
  destruct (SBD HWl) as (S1 & _ & S3).
  assert (HEMB : emb_sz st + 110 <= EMB_MAX - 4096) by (unfold C_EXH, CRED0, EMB_MAX in *; lia).
  pose proof (aaligned16x_core (RESV:=RESV) (ATOP:=ATOP) st mo n HI Q1 Q2 Hn Hm HEMB) as HTOT.
  set (SB := a_space_beg st) in *. set (PA := a_ptr_array st) in *.
  assert (Hbx : 0 <= EXB <= 2^32) by (unfold EXB, EMB_MAX; lia).
  destruct (KI_entry v RNG A st mo EXB HACC Hbx) as (k & HK & HP & HL).
  pose proof (evq_aaligned16x SB PA RESV st n HL Hn Hm HEMB) as HEV.
  destruct (INV_SB_PA st mo HI) as [HSB HPA].
  pose proof (GP_nonneg st (LW_emb _ _ _ HL)) as G0.
  pose proof (TS_aembed NMAX SB PA (Abase_x SB PA) NLK0 HLIM
                ltac:(intros z' Hz'; left; exists z'; split; [exact Hz'| reflexivity])
                (aaligned16x ATOP RESV st n) (RPm SB PA n) (malloc_post st n) (GP st + 0) (PHI st + EXB) A k (k + (GP st + 0)) mo RNG mo
                HTOT HEV HK (vmh_refl mo) ltac:(rewrite ER; apply fp_le_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as HTS.
  rewrite ER. eapply TS_mono; [exact HTS|].
  intros r RNG' A' mo' _ (b' & k' & gp' & HRP & HPOST & HK' & Hgp' & Hkg & HH & HFL & ERN).
  destruct HRP as [HL' HGP']. destruct HK' as (_ & _ & _ & HAB' & HCV' & HBU' & Hk').
  pose proof HL' as (ESB & EPA & _).
  split; [exact HH|]. split; [rewrite <- ER; exact HFL|]. rewrite EP in *.
  destruct HPOST as [(ch & Esnd & HI' & ELIVE & ENONE & ESZ & B1 & B2 & B3 & B4 & EEMB & CK)|(Esnd & HI' & ELIVE & ENEXT & B1 & B2 & B3 & B4 & EEMB & CK)]; rewrite Esnd in *.
  -
    split; [intros X; discriminate X|].
    split; [reflexivity|]. split; [exact ENONE|]. split; [exists ch; split; [exact ELIVE| exact ESZ]|].
    assert (ESB' : secbytes (live_chunks (fst r)) <= secbytes (live_chunks st)).
    { assert (PL : Permutation (live_chunks (fst r)) (ch :: live_chunks st)).
      { pose proof (live_chunks_insert st (a_next st) ch ENONE) as X. unfold live_chunks in X |- *. cbn [a_live set_live] in X. rewrite ELIVE. exact X. }
      rewrite (secbytes_perm _ _ PL).
      assert (Hwf : chunk_wf ATOP ch).
      { destruct HI' as [HA' _]. destruct HA' as (_ & HW' & _). unfold all_chunks in HW'. cbn [app] in HW'. apply Forall_app in HW' as [HW' _].
        eapply (proj1 (Forall_forall _ _) HW'). eapply Permutation_in; [apply Permutation_sym; exact PL| left; reflexivity]. }
      destruct ch as [c0 n0|mb0 ms0 n0]; cbn [secbytes chunk_size] in *; [lia|].
      subst n0. cbn in Hwf. unfold ALIGNED_NMAX in Hn. lia. }
    assert (EES : emb_sz (fst r) = emb_sz st) by (unfold emb_sz; rewrite EEMB; reflexivity).
    assert (EGP : GP (fst r) = GP st) by (unfold GP, emb_cap; rewrite EEMB; reflexivity).
    split; [exact HI'|]. split; [lia|]. split; [lia|]. split; [exact ERN|]. split; [lia|]. split; [lia|].
    exists k'. rewrite ESB, EPA. split; [exact HAB'|]. split; [exact HCV'|]. split; [exact HBU'|]. split; [exact Hk'|]. lia.
  -
    split; [intros X; discriminate X|].
    split; [exact ELIVE|]. split; [exact ENEXT|].
    assert (ESB' : secbytes (live_chunks (fst r)) = secbytes (live_chunks st)) by (unfold live_chunks; rewrite ELIVE; reflexivity).
    split; [exact HI'|]. split; [lia|]. split; [lia|]. split; [exact ERN|]. split; [unfold C_EXH in *; lia|]. split; [unfold C_EXH in *; lia|].
    exists k'. rewrite ESB, EPA. split; [exact HAB'|]. split; [exact HCV'|]. split; [exact HBU'|]. split; [exact Hk'|].
    unfold C_EXH. lia.
Qed.

Definition free_leaf (v : Z) (id : AsanCtrl.aptr) (st : astate) (mo0 : Model) (RNG0 : footprint) : postT astate :=
  fun st' RNG' A' mo' =>
    vmh mo0 mo' /\ fp_le RNG0 RNG' /\ a_live st' = delete id (a_live st) /\ a_next st' = a_next st
    /\ cls_keep K_BATCH_CLASS st st'
    /\ ACCTc v RNG' A' st' mo'.

Theorem U_free : forall v RNG A st mo id ch,
  ACCTc v RNG A st mo -> (a_live st) !! id = Some ch ->
  TS RNG A (aembed ATOP (afree st (Some id))) mo (free_leaf v id st mo RNG).
Proof.
  intros v RNG A st mo id ch HACC Hl.
  pose proof HACC as (HI & Q1 & Q2 & ER & Hv & HC & _). pose proof HI as [HA HM].
  pose proof (afree_core (RESV:=RESV) (ATOP:=ATOP) st mo id ch HI Q1 Q2 Hl) as HTOT.
  set (SB := a_space_beg st) in *. set (PA := a_ptr_array st) in *.
  destruct (KI_entry v RNG A st mo 0 HACC ltac:(lia)) as (k & HK & HP & HL).
  pose proof (evq_afree SB PA st id HL) as HEV.
  destruct (INV_SB_PA st mo HI) as [HSB HPA].
  pose proof (GP_nonneg st (LW_emb _ _ _ HL)) as G0.
  pose proof (TS_aembed NMAX SB PA (Abase_x SB PA) NLK0 HLIM
                ltac:(intros z' Hz'; left; exists z'; split; [exact Hz'| reflexivity])
                (afree st (Some id)) (RPst SB PA) (free_post st id) (GP st + 0) (PHI st + 0) A k (k + (GP st + 0)) mo RNG mo
                HTOT HEV HK (vmh_refl mo) ltac:(rewrite ER; apply fp_le_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as HTS.
  rewrite ER. eapply TS_mono; [exact HTS|].
  intros st' RNG' A' mo' _ (b' & k' & gp' & HRP & HPOST & HK' & Hgp' & Hkg & HH & HFL & ERN).
  destruct HRP as [HL' HGP']. destruct HK' as (_ & _ & _ & HAB' & HCV' & HBU' & Hk').
  pose proof HL' as (ESB & EPA & _).
  destruct HPOST as (HI' & ELIVE & ENEXT & B1 & B2 & EEMB & CK).
  split; [exact HH|]. split; [rewrite <- ER; exact HFL|]. split; [exact ELIVE|]. split; [exact ENEXT|]. split; [exact CK|].
  assert (ESB' : secbytes (live_chunks st') <= secbytes (live_chunks st)).
  { assert (PL : Permutation (live_chunks st) (ch :: live_chunks st')).
    { pose proof (live_chunks_delete st id ch Hl) as X. unfold live_chunks in X |- *. cbn [a_live set_live] in X. rewrite ELIVE. exact X. }
    rewrite (secbytes_perm _ _ PL).
    assert (HW' : Forall (chunk_wf ATOP) (live_chunks st')).
    { destruct HI' as [HA' _]. destruct HA' as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HW _]. exact HW. }
    assert (Hch : chunk_wf ATOP ch).
    { destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HW _].
      eapply (proj1 (Forall_forall _ _) HW). eapply Permutation_in; [apply Permutation_sym; exact PL| left; reflexivity]. }
    destruct ch as [c0 n0|mb0 ms0 n0]; cbn [secbytes]; [lia|]. cbn in Hch. lia. }
  assert (EES : emb_sz st' = emb_sz st) by (unfold emb_sz; rewrite EEMB; reflexivity).
  split; [exact HI'|]. split; [exact B1|]. split; [exact B2|]. split; [exact ERN|]. split; [lia|]. split; [lia|].
  exists k'. rewrite ESB, EPA. split; [exact HAB'|]. split; [exact HCV'|]. split; [exact HBU'|]. split; [exact Hk'|]. lia.
Qed.

Definition arealloc_m (st : astate) (p : AsanCtrl.aptr) (n : Z) : AM (astate * option AsanCtrl.aptr) :=
  sbind (amalloc ATOP RESV st n) (fun r =>
    match snd r with
    | Some q => sbind (afree (fst r) (Some p)) (fun st2 => aret (st2, Some q))
    | None => aret r
    end).

Definition realloc_leaf (v n : Z) (p : AsanCtrl.aptr) (st : astate) (mo0 : Model) (RNG0 : footprint) : postT (astate * option AsanCtrl.aptr) :=
  fun r RNG' A' mo' =>
    vmh mo0 mo' /\ fp_le RNG0 RNG' /\
    match snd r with
    | Some q => q = a_next st /\ (a_live st) !! q = None
                /\ (exists ch, a_live (fst r) = delete p (<[q := ch]> (a_live st)) /\ chunk_size ch = n)
                /\ ACCTc (v - (if is_primary n then 0 else n)) RNG' A' (fst r) mo'
    | None => a_live (fst r) = a_live st /\ ACCTc (v - C_EXH) RNG' A' (fst r) mo'
    end.

Theorem U_realloc : forall v RNG A st mo p chp n,
  ACCTc v RNG A st mo -> (a_live st) !! p = Some chp -> 1 <= n <= AREQMAX -> (is_primary n = false -> n <= v) -> C_EXH <= v ->
  size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX ->
  TS RNG A (aembed ATOP (arealloc_m st p n)) mo (realloc_leaf v n p st mo RNG).
Proof.
  intros v RNG A st mo p chp n HACC Hp Hn Hnv Hcv H24. unfold arealloc_m.
  eapply TS_sbind; [exact (U_malloc v RNG A st mo n HACC Hn Hnv Hcv H24)|].
  intros [st1 res] RNG1 A1 mo1 ACC1 (HH1 & FL1 & CK1 & LEAF). cbn [fst snd] in LEAF |- *. destruct res as [q|].
  - destruct LEAF as (-> & FRESH & (ch & ELIVE & ESZ) & HC1).
    assert (Hp1 : (a_live st1) !! p = Some chp).
    { rewrite ELIVE. rewrite lookup_insert_ne; [exact Hp|]. intros <-. rewrite FRESH in Hp. discriminate. }
    eapply TS_sbind; [exact (U_free _ RNG1 A1 st1 mo1 p chp HC1 Hp1)|].
    intros st2 RNG2 A2 mo2 ACC2 (HH2 & FL2 & ELIVE2 & _ & _ & HC2). unfold aret. rewrite aembed_ret. apply TS_ret_ok; [exact ACC2|].
    split; [exact (vmh_trans _ _ _ HH1 HH2)|]. split; [exact (fp_le_trans _ _ _ FL1 FL2)|]. cbn [fst snd].
    split; [reflexivity|]. split; [exact FRESH|]. split; [exists ch; split; [rewrite ELIVE2, ELIVE; reflexivity| exact ESZ]| exact HC2].
  - destruct LEAF as (ELIVE & _ & HC1). unfold aret. rewrite aembed_ret. apply TS_ret_ok; [exact ACC1|].
    split; [exact HH1|]. split; [exact FL1|]. cbn [fst snd]. split; [exact ELIVE| exact HC1].
Qed.

End OpsM.
End CANSEC1.

Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ModelX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.MmXfer OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.BackingAlgebra.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrlProps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanInv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanBudget OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanTotalCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanNodeSem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanTotal OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanFree.
Import ABase.TwinB AProto.TwinB ATsafeCore.TwinB ATsafeEv.TwinB ATsafeAlloc.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.

Definition NLK0 : Z := EAGER0 + CBM + 2^37 + 2^32.

Definition CRED0 : Z := 3 * 2^34.
Definition C_EXH : Z := 2^20.

Definition Abase_of (SB PA : Z) : alw :=
  fun p => exists z', (shad SB <= z' < shad (SB + K_SPACE_SIZE) \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) /\ p = page_base_of z'.

Definition c24_ok (n : Z) : bool := implb (class_id (needed_size n) =? K_BATCH_CLASS) ((5881 <=? n) && (n <=? 7936)).
Lemma c24_ok_range : forallb c24_ok (zseq 0 (Z.to_nat 64513)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma c24_range : forall n, 0 <= n <= 64512 -> class_id (needed_size n) = K_BATCH_CLASS -> 5881 <= n <= 7936.
Proof.
  intros n Hn Hc. pose proof (forallb_zseq c24_ok 0 (Z.to_nat 64513) c24_ok_range n ltac:(rewrite Z2Nat.id; lia)) as H.
  unfold c24_ok in H. rewrite Hc, Z.eqb_refl in H. cbn [implb] in H. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma NLK0_nonneg : 0 <= NLK0. Proof. vm_compute. discriminate. Qed.

Section OpsM.
Variable NMAX : nat.
Local Notation NMAXZ := (Z.of_nat NMAX).
Hypothesis HLIM : NLK0 + NMAXZ * 4096 <= LIMIT.
Variable RESV : list (Z * Z).

Variable AFIX : alw.
Definition Abase_x (SB PA : Z) : alw := fun p => Abase_of SB PA p \/ AFIX p.
Local Notation INV := (AsanInv.INV RESV ATOP).
Local Notation TS := (TS NMAX).

Definition ACCTc (v : Z) (RNG : footprint) (A : alw) (st : astate) (mo : Model) : Prop :=
  INV [] [] st mo /\ a_qloc_bytes st <= Q_CACHE /\ a_qglob_bytes st <= Q_MAX
  /\ RNG = fp_ok (m_vm_lazy mo) A
  /\ 0 <= v <= CRED0
  /\ 110 * secbytes (live_chunks st) + C_EXH * emb_sz st <= 110 * (CRED0 - v)
  /\ exists k, alw_le (Abase_x (a_space_beg st) (a_ptr_array st)) A /\ (forall p, COVP mo p -> A p) /\ abud A k /\ 0 <= k
               /\ 1024 * (k + GP st) + v <= 1024 * NMAXZ.

Lemma ACCTc_weaken : forall v v' RNG A st mo, ACCTc v RNG A st mo -> 0 <= v' <= v -> ACCTc v' RNG A st mo.
Proof.
  intros v v' RNG A st mo (HI & Q1 & Q2 & ER & Hv & HC & k & HAB & HCV & HBU & Hk & HP) Hv'.
  split; [exact HI|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact ER|]. split; [lia|]. split; [lia|].
  exists k. split; [exact HAB|]. split; [exact HCV|]. split; [exact HBU|]. split; [exact Hk| lia].
Qed.

Lemma MOK_of_AMI : forall ch st mo, AMI RESV ATOP ch st mo -> MOK mo.
Proof.
  intros ch st mo HM. pose proof (AMI_ivs_wf _ _ _ HM) as W. destruct HM as (M1 & M2 & _ & _ & _ & M6 & _ & _ & M9 & [_ M10] & _).
  split; [exact M1|]. split; [exact M2|]. split; [exact W|]. split; [exact (proj1 M9)| split; [exact M6| exact M10]].
Qed.

Lemma chunk_cls_ok_wf : forall ch, chunk_wf ATOP ch -> chunk_cls_ok ch.
Proof.
  intros [c n|mb ms n] H; cbn in *; [| exact I]. destruct H as [Hn Hc].
  pose proof (prim_cls_facts c n Hn Hc) as (C1 & _). lia.
Qed.

Lemma LW_of_AINV : forall st, AINV ATOP [] [] st -> LW (a_space_beg st) (a_ptr_array st) st.
Proof.
  intros st HA. pose proof HA as (HC & HW & _ & _ & _ & _ & (j & Hj & Hres) & _ & _ & _ & _ & _ & _ & HE).
  split; [reflexivity|]. split; [reflexivity|]. split; [unfold K_CHUNKS_BLOCK in Hres; lia|]. split; [unfold K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *; lia|].
  split; [| split].
  - intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in X. cbv zeta in X. unfold cls_lw. lia.
  - unfold emb_ok in HE. unfold emb_lw, emb_cap, emb_sz. destruct (a_emb st) as [[d cap] sz]. cbn [fst snd].
    destruct HE as [[-> ->]|(E1 & E2 & _ & _ & E5 & _)]; [unfold EMB_MAX; cbn; lia| unfold EMB_INIT in E1; lia].
  - unfold QOK. eapply Forall_impl; [| exact HW]. intros ch Hch. apply chunk_cls_ok_wf. exact Hch.
Qed.

Lemma CHX_bound : forall st, AINV ATOP [] [] st -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> zsum2 (CHX [] [] st) <= 2^37.
Proof.
  intros st HA Q1 Q2.
  destruct (CH_bounds [] [] st HA) as [_ X]; [| unfold zlen; cbn; lia| cbn; lia|].
  { unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA as (_ & _ & _ & Hb1 & Hb2 & _). unfold Q_CACHE, Q_MAX in *. lia. }
  rewrite zsum2_CHX. pose proof (emb_ent_zsum2 _ _ _ HA) as EZ. unfold EMB_MAX in EZ. lia.
Qed.

Lemma KI_entry : forall v RNG A st mo extra,
  ACCTc v RNG A st mo -> 0 <= extra <= 2^32 ->
  exists k, KI (Abase_x (a_space_beg st) (a_ptr_array st)) NLK0 (PHI st + extra) A k mo
            /\ 1024 * (k + GP st) + v <= 1024 * NMAXZ /\ LW (a_space_beg st) (a_ptr_array st) st.
Proof.
  intros v RNG A st mo extra (HI & Q1 & Q2 & ER & Hv & HC & k & HAB & HCV & HBU & Hk & HP) Hex. pose proof HI as [HA HM].
  exists k. assert (HL : LW (a_space_beg st) (a_ptr_array st) st) by (apply LW_of_AINV; exact HA).
  split; [| split; [exact HP| exact HL]].
  pose proof (PHI_nonneg _ _ _ HL). pose proof (commit_bytes_LW _ _ _ HL).
  pose proof (AMI_nonlazy_bound _ _ _ HM (CHX_wf _ _ _ HA)). pose proof (CHX_bound st HA Q1 Q2).
  split; [eapply MOK_of_AMI; exact HM|]. split; [lia|]. split; [unfold PHI, NLK0 in *; lia|].
  split; [exact HAB|]. split; [exact HCV|]. split; [exact HBU| exact Hk].
Qed.

Lemma INV_SB_PA : forall st mo, INV [] [] st mo ->
  (0 <= a_space_beg st /\ a_space_beg st + K_SPACE_SIZE <= ATOP) /\ (0 <= a_ptr_array st /\ a_ptr_array st + K_PTRARR_RESERVE <= ATOP).
Proof.
  intros st mo HI. destruct (INV_prim _ _ _ _ HI) as (pb0 & _ & P1 & P2 & P3 & P4). destruct (INV_ptr _ _ _ _ HI) as (_ & Q1 & _).
  destruct HI as [HA _]. destruct (AINV_geom _ _ _ HA) as (_ & G2 & _ & G4).
  unfold K_SPACE_SIZE, K_PTRARR_RESERVE, PTR_SZ, PRIM_SZ in *. lia.
Qed.

Lemma pcost_sec : forall n, 64512 < n <= 2^40 -> 1024 * pcost (sec_map_size n) <= n.
Proof.
  intros n Hn. pose proof (sec_map_size_bounds n Hn) as SBn. unfold pcost.
  set (s := sec_map_size n) in *.
  pose proof (Z.div_le_mono s (n + 12296) 4096 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono s (n + 12296) 32768 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_mod (n + 12296) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 4096 ltac:(lia)).
  pose proof (Z.div_mod (n + 12296) 32768 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 32768 ltac:(lia)).
  lia.
Qed.

Lemma secbytes_perm : forall l l', Permutation l l' -> secbytes l = secbytes l'.
Proof. intros l l' HP. induction HP as [| [c n|mb ms n] l l' _ IH | [c n|mb ms n] [c' n'|mb' ms' n'] l | l l' l'' _ IH1 _ IH2]; cbn [secbytes]; lia. Qed.

Definition malloc_leaf (v n : Z) (st : astate) (mo0 : Model) (RNG0 : footprint) : postT (astate * option AsanCtrl.aptr) :=
  fun r RNG' A' mo' =>
    vmh mo0 mo' /\ fp_le RNG0 RNG' /\
    (is_primary n = false -> cls_keep K_BATCH_CLASS st (fst r)) /\
    match snd r with
    | Some p => p = a_next st /\ (a_live st) !! p = None
                /\ (exists ch, a_live (fst r) = <[p := ch]> (a_live st) /\ chunk_size ch = n)
                /\ ACCTc (v - (if is_primary n then 0 else n)) RNG' A' (fst r) mo'
    | None => a_live (fst r) = a_live st /\ a_next (fst r) = a_next st /\ ACCTc (v - C_EXH) RNG' A' (fst r) mo'
    end.

Theorem U_malloc_g : forall (NN : Prop) v RNG A st mo n,
  ACCTc v RNG A st mo -> 1 <= n <= AREQMAX -> (is_primary n = false -> n <= v) -> C_EXH <= v ->
  size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX ->
  (is_primary n = true -> class_id (needed_size n) <> K_BATCH_CLASS ->
     K_FREEARR_OFF < c_mapped_user (get_cls st (class_id (needed_size n))) + K_USER_MAP -> NN) ->
  (is_primary n = false -> vm_gap_available (m_vmmaps mo) (sec_map_size n) = false -> NN) ->
  TS RNG A (aembed ATOP (amalloc ATOP RESV st n)) mo (fun r RNG' A' mo' => malloc_leaf v n st mo RNG r RNG' A' mo' /\ (snd r = None -> NN)).
Proof.
  intros NN v RNG A st mo n HACC Hn Hnv Hcv H24 HNN1 HNN2. unfold AREQMAX in Hn.
  pose proof HACC as (HI & Q1 & Q2 & ER & Hv & HC & _). pose proof HI as [HA HM].
  pose proof (secs_bounds (ATOP:=ATOP) (live_chunks st)) as SBD.
  assert (HWl : Forall (chunk_wf ATOP) (live_chunks st)).
  { destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HW _]. exact HW. }
  destruct (SBD HWl) as (S1 & _ & S3).
  assert (E0 : 0 <= emb_sz st) by (pose proof (LW_emb _ _ _ (LW_of_AINV st HA)) as (_ & _ & X); exact X).
  assert (HEMB : emb_sz st + 110 <= EMB_MAX - 4096) by (unfold C_EXH, CRED0, EMB_MAX in *; lia).
  assert (HLB : forall mb ms, live_budget_list (mkch n mb ms :: live_chunks st)).
  { intros mb ms. assert (S24 : size_of_class K_BATCH_CLASS = 8192) by reflexivity. rewrite S24 in *.
    pose proof (cntP_nonneg K_BATCH_CLASS (live_chunks st)) as CN0.
    unfold live_budget_list, mkch. rewrite S24. destruct (is_primary n) eqn:EP.
    - rewrite cntP_cons. change (secs (CPrim (class_id (needed_size n)) n :: live_chunks st)) with (secs (live_chunks st)). cbn [secbytes]. split; [| split].
      + destruct (is_prim_of K_BATCH_CLASS (CPrim (class_id (needed_size n)) n)); unfold L24MAX in *; lia.
      + unfold SMAX, CRED0, C_EXH in *. lia.
      + unfold LSBYTES, CRED0, C_EXH in *. lia.
    - specialize (Hnv eq_refl). rewrite cntP_cons. cbn [is_prim_of]. change (secs (CSec mb ms n :: live_chunks st)) with ((mb, ms) :: secs (live_chunks st)).
      rewrite zlen_cons. cbn [secbytes]. split; [| split].
      + unfold L24MAX in *. lia.
      + pose proof (not_primary_large n ltac:(lia) EP). unfold SMAX, CRED0, C_EXH in *. lia.
      + unfold LSBYTES, CRED0, C_EXH in *. lia. }
  pose proof (amalloc_core_g (RESV:=RESV) (ATOP:=ATOP) NN st mo n HI Q1 Q2 ltac:(lia) HLB HEMB HNN1 HNN2) as HTOT.
  set (SB := a_space_beg st) in *. set (PA := a_ptr_array st) in *.
  set (gx := if is_primary n then 0 else pcost (sec_map_size n)).
  set (bx := if is_primary n then EXB else sec_map_size n).
  assert (Hbx : 0 <= bx <= 2^32).
  { unfold bx. destruct (is_primary n) eqn:EP; [unfold EXB, EMB_MAX; lia|].
    pose proof (not_primary_large n ltac:(lia) EP). pose proof (sec_map_size_bounds n ltac:(lia)). lia. }
  destruct (KI_entry v RNG A st mo bx HACC Hbx) as (k & HK & HP & HL).
  pose proof (evq_amalloc SB PA RESV st n HL ltac:(lia) HEMB) as HEV. fold gx bx in HEV.
  destruct (INV_SB_PA st mo HI) as [HSB HPA].
  assert (Hgx : 0 <= gx).
  { unfold gx. destruct (is_primary n) eqn:EP; [lia|]. pose proof (not_primary_large n ltac:(lia) EP). pose proof (sec_map_size_bounds n ltac:(lia)). apply pcost_nonneg. lia. }
  pose proof (GP_nonneg st (LW_emb _ _ _ HL)) as G0.
  assert (CHG : 0 <= (if is_primary n then 0 else n) <= v /\ 1024 * gx <= (if is_primary n then 0 else n)).
  { unfold gx. destruct (is_primary n) eqn:EP; [lia|]. specialize (Hnv eq_refl). split; [lia|]. apply pcost_sec. pose proof (not_primary_large n ltac:(lia) EP). lia. }
  pose proof (TS_aembed NMAX SB PA (Abase_x SB PA) NLK0 HLIM
                ltac:(intros z' Hz'; left; exists z'; split; [exact Hz'| reflexivity])
                (amalloc ATOP RESV st n) (RPm SB PA n) (fun r mo' => malloc_post st n r mo' /\ (snd r = None -> NN)) (GP st + gx) (PHI st + bx) A k (k + (GP st + gx)) mo RNG mo
                HTOT HEV HK (vmh_refl mo) ltac:(rewrite ER; apply fp_le_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as HTS.
  rewrite ER. eapply TS_mono; [exact HTS|].
  intros r RNG' A' mo' _ (b' & k' & gp' & HRP & [HPOST HNN] & HK' & Hgp' & Hkg & HH & HFL & ERN).
  destruct HRP as [HL' HGP']. destruct HK' as (_ & _ & _ & HAB' & HCV' & HBU' & Hk').
  pose proof HL' as (ESB & EPA & _).
  split; [| exact HNN].
  split; [exact HH|]. split; [rewrite <- ER; exact HFL|].
  destruct HPOST as [(ch & Esnd & HI' & ELIVE & ENONE & ESZ & B1 & B2 & B3 & B4 & EEMB & CK)|(Esnd & HI' & ELIVE & ENEXT & B1 & B2 & B3 & B4 & EEMB & CK)]; rewrite Esnd in *.
  -
    split; [exact CK|].
    split; [reflexivity|]. split; [exact ENONE|]. split; [exists ch; split; [exact ELIVE| exact ESZ]|].
    assert (ESB' : secbytes (live_chunks (fst r)) <= secbytes (live_chunks st) + (if is_primary n then 0 else n)).
    { assert (PL : Permutation (live_chunks (fst r)) (ch :: live_chunks st)).
      { pose proof (live_chunks_insert st (a_next st) ch ENONE) as X. unfold live_chunks in X |- *. cbn [a_live set_live] in X. rewrite ELIVE. exact X. }
      rewrite (secbytes_perm _ _ PL).
      assert (Hwf : chunk_wf ATOP ch).
      { destruct HI' as [HA' _]. destruct HA' as (_ & HW' & _). unfold all_chunks in HW'. cbn [app] in HW'. apply Forall_app in HW' as [HW' _].
        eapply (proj1 (Forall_forall _ _) HW'). eapply Permutation_in; [apply Permutation_sym; exact PL| left; reflexivity]. }
      destruct ch as [c0 n0|mb0 ms0 n0]; cbn [secbytes chunk_size] in *; [destruct (is_primary n); lia|].
      subst n0. cbn in Hwf. rewrite (large_not_primary n) by lia. lia. }
    assert (EES : emb_sz (fst r) = emb_sz st) by (unfold emb_sz; rewrite EEMB; reflexivity).
    assert (EGP : GP (fst r) = GP st) by (unfold GP, emb_cap; rewrite EEMB; reflexivity).
    split; [exact HI'|]. split; [lia|]. split; [lia|]. split; [exact ERN|]. split; [lia|]. split; [lia|].
    exists k'. rewrite ESB, EPA. split; [exact HAB'|]. split; [exact HCV'|]. split; [exact HBU'|]. split; [exact Hk'|]. lia.
  -
    split; [exact CK|].
    split; [exact ELIVE|]. split; [exact ENEXT|].
    assert (ESB' : secbytes (live_chunks (fst r)) = secbytes (live_chunks st)) by (unfold live_chunks; rewrite ELIVE; reflexivity).
    split; [exact HI'|]. split; [lia|]. split; [lia|]. split; [exact ERN|]. split; [unfold C_EXH in *; lia|]. split; [unfold C_EXH in *; lia|].
    exists k'. rewrite ESB, EPA. split; [exact HAB'|]. split; [exact HCV'|]. split; [exact HBU'|]. split; [exact Hk'|].
    assert (0 <= (if is_primary n then 0 else pcost (sec_map_size n))) by (fold gx; exact Hgx). unfold C_EXH. lia.
Qed.

Theorem U_malloc : forall v RNG A st mo n,
  ACCTc v RNG A st mo -> 1 <= n <= AREQMAX -> (is_primary n = false -> n <= v) -> C_EXH <= v ->
  size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX ->
  TS RNG A (aembed ATOP (amalloc ATOP RESV st n)) mo (malloc_leaf v n st mo RNG).
Proof.
  intros v RNG A st mo n HACC Hn Hnv Hcv H24.
  eapply TS_mono; [apply (U_malloc_g True v RNG A st mo n HACC Hn Hnv Hcv H24); intros; exact I|].
  intros r RNG' A' mo' _ [H _]. exact H.
Qed.

Theorem U_malloc_nn_prim : forall v RNG A st mo n,
  ACCTc v RNG A st mo -> 1 <= n <= 64512 -> C_EXH <= v ->
  size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX ->
  (forall c, 1 <= c <= 31 -> c <> K_BATCH_CLASS -> c_mapped_user (get_cls st c) = 0) ->
  TS RNG A (aembed ATOP (amalloc ATOP RESV st n)) mo (fun r RNG' A' mo' => malloc_leaf v n st mo RNG r RNG' A' mo' /\ snd r <> None).
Proof.
  intros v RNG A st mo n HACC Hn Hcv H24 HPR.
  assert (HP : is_primary n = true) by (rewrite is_primary_iff by lia; apply Z.leb_le; lia).
  eapply TS_mono; [apply (U_malloc_g False v RNG A st mo n HACC ltac:(unfold AREQMAX; lia) ltac:(intros X; rewrite HP in X; discriminate X) Hcv H24)|].
  - intros _ N24 HEX. pose proof (primary_class_facts n ltac:(lia) HP) as F. cbv zeta in F. destruct F as (F1 & _).
    rewrite (HPR (class_id (needed_size n)) ltac:(lia) N24) in HEX. unfold K_FREEARR_OFF, K_USER_MAP in HEX. lia.
  - intros X. rewrite HP in X. discriminate X.
  - intros r RNG' A' mo' _ [H HN]. split; [exact H|]. intros E. exact (HN E).
Qed.
Theorem U_malloc_nn_sec : forall v RNG A st mo n,
  ACCTc v RNG A st mo -> 64512 < n <= 2^28 -> n <= v -> CRED0 - 2^30 <= v ->
  size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX ->
  TS RNG A (aembed ATOP (amalloc ATOP RESV st n)) mo (fun r RNG' A' mo' => malloc_leaf v n st mo RNG r RNG' A' mo' /\ snd r <> None).
Proof.
  intros v RNG A st mo n HACC Hn Hnv Hcv H24.
  pose proof HACC as (HI & Q1 & Q2 & ER & Hv & HC & _). pose proof HI as [HA HM].
  assert (HP : is_primary n = false) by (apply large_not_primary; lia).
  assert (E0 : 0 <= emb_sz st) by (pose proof (LW_emb _ _ _ (LW_of_AINV st HA)) as (_ & _ & X); exact X).
  assert (HLB : secbytes (live_chunks st) <= 2^30) by (unfold C_EXH, CRED0 in *; nia).
  eapply TS_mono; [apply (U_malloc_g False v RNG A st mo n HACC ltac:(unfold AREQMAX; lia) ltac:(intros _; exact Hnv) ltac:(unfold C_EXH, CRED0 in *; lia) H24)|].
  - intros X. rewrite HP in X. discriminate X.
  - intros _ NG. rewrite (INV_gap_sec (RESV:=RESV) (ATOP:=ATOP) st mo n HI ltac:(lia) HLB Q1 Q2 (CHX_bound st HA Q1 Q2)) in NG. discriminate NG.
  - intros r RNG' A' mo' _ [H HN]. split; [exact H|]. intros E. exact (HN E).
Qed.

Theorem U_aligned16 : forall v RNG A st mo n,
  ACCTc v RNG A st mo -> 16 <= n <= ALIGNED_NMAX -> n mod 16 = 0 -> C_EXH <= v ->
  TS RNG A (aembed ATOP (aaligned16x ATOP RESV st n)) mo (malloc_leaf v n st mo RNG).
Proof.
  intros v RNG A st mo n HACC Hn Hm Hcv.
  pose proof HACC as (HI & Q1 & Q2 & ER & Hv & HC & _). pose proof HI as [HA HM].
  pose proof (al16_facts n Hn Hm) as F. cbv zeta in F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EP).
  assert (E0 : 0 <= emb_sz st) by (pose proof (LW_emb _ _ _ (LW_of_AINV st HA)) as (_ & _ & X); exact X).
  pose proof (secs_bounds (ATOP:=ATOP) (live_chunks st)) as SBD.
  assert (HWl : Forall (chunk_wf ATOP) (live_chunks st)).
  { destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HW _]. exact HW. }
  destruct (SBD HWl) as (S1 & _ & S3).
  assert (HEMB : emb_sz st + 110 <= EMB_MAX - 4096) by (unfold C_EXH, CRED0, EMB_MAX in *; lia).
  pose proof (aaligned16x_core (RESV:=RESV) (ATOP:=ATOP) st mo n HI Q1 Q2 Hn Hm HEMB) as HTOT.
  set (SB := a_space_beg st) in *. set (PA := a_ptr_array st) in *.
  assert (Hbx : 0 <= EXB <= 2^32) by (unfold EXB, EMB_MAX; lia).
  destruct (KI_entry v RNG A st mo EXB HACC Hbx) as (k & HK & HP & HL).
  pose proof (evq_aaligned16x SB PA RESV st n HL Hn Hm HEMB) as HEV.
  destruct (INV_SB_PA st mo HI) as [HSB HPA].
  pose proof (GP_nonneg st (LW_emb _ _ _ HL)) as G0.
  pose proof (TS_aembed NMAX SB PA (Abase_x SB PA) NLK0 HLIM
                ltac:(intros z' Hz'; left; exists z'; split; [exact Hz'| reflexivity])
                (aaligned16x ATOP RESV st n) (RPm SB PA n) (malloc_post st n) (GP st + 0) (PHI st + EXB) A k (k + (GP st + 0)) mo RNG mo
                HTOT HEV HK (vmh_refl mo) ltac:(rewrite ER; apply fp_le_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as HTS.
  rewrite ER. eapply TS_mono; [exact HTS|].
  intros r RNG' A' mo' _ (b' & k' & gp' & HRP & HPOST & HK' & Hgp' & Hkg & HH & HFL & ERN).
  destruct HRP as [HL' HGP']. destruct HK' as (_ & _ & _ & HAB' & HCV' & HBU' & Hk').
  pose proof HL' as (ESB & EPA & _).
  split; [exact HH|]. split; [rewrite <- ER; exact HFL|]. rewrite EP in *.
  destruct HPOST as [(ch & Esnd & HI' & ELIVE & ENONE & ESZ & B1 & B2 & B3 & B4 & EEMB & CK)|(Esnd & HI' & ELIVE & ENEXT & B1 & B2 & B3 & B4 & EEMB & CK)]; rewrite Esnd in *.
  -
    split; [intros X; discriminate X|].
    split; [reflexivity|]. split; [exact ENONE|]. split; [exists ch; split; [exact ELIVE| exact ESZ]|].
    assert (ESB' : secbytes (live_chunks (fst r)) <= secbytes (live_chunks st)).
    { assert (PL : Permutation (live_chunks (fst r)) (ch :: live_chunks st)).
      { pose proof (live_chunks_insert st (a_next st) ch ENONE) as X. unfold live_chunks in X |- *. cbn [a_live set_live] in X. rewrite ELIVE. exact X. }
      rewrite (secbytes_perm _ _ PL).
      assert (Hwf : chunk_wf ATOP ch).
      { destruct HI' as [HA' _]. destruct HA' as (_ & HW' & _). unfold all_chunks in HW'. cbn [app] in HW'. apply Forall_app in HW' as [HW' _].
        eapply (proj1 (Forall_forall _ _) HW'). eapply Permutation_in; [apply Permutation_sym; exact PL| left; reflexivity]. }
      destruct ch as [c0 n0|mb0 ms0 n0]; cbn [secbytes chunk_size] in *; [lia|].
      subst n0. cbn in Hwf. unfold ALIGNED_NMAX in Hn. lia. }
    assert (EES : emb_sz (fst r) = emb_sz st) by (unfold emb_sz; rewrite EEMB; reflexivity).
    assert (EGP : GP (fst r) = GP st) by (unfold GP, emb_cap; rewrite EEMB; reflexivity).
    split; [exact HI'|]. split; [lia|]. split; [lia|]. split; [exact ERN|]. split; [lia|]. split; [lia|].
    exists k'. rewrite ESB, EPA. split; [exact HAB'|]. split; [exact HCV'|]. split; [exact HBU'|]. split; [exact Hk'|]. lia.
  -
    split; [intros X; discriminate X|].
    split; [exact ELIVE|]. split; [exact ENEXT|].
    assert (ESB' : secbytes (live_chunks (fst r)) = secbytes (live_chunks st)) by (unfold live_chunks; rewrite ELIVE; reflexivity).
    split; [exact HI'|]. split; [lia|]. split; [lia|]. split; [exact ERN|]. split; [unfold C_EXH in *; lia|]. split; [unfold C_EXH in *; lia|].
    exists k'. rewrite ESB, EPA. split; [exact HAB'|]. split; [exact HCV'|]. split; [exact HBU'|]. split; [exact Hk'|].
    unfold C_EXH. lia.
Qed.

Definition free_leaf (v : Z) (id : AsanCtrl.aptr) (st : astate) (mo0 : Model) (RNG0 : footprint) : postT astate :=
  fun st' RNG' A' mo' =>
    vmh mo0 mo' /\ fp_le RNG0 RNG' /\ a_live st' = delete id (a_live st) /\ a_next st' = a_next st
    /\ cls_keep K_BATCH_CLASS st st'
    /\ ACCTc v RNG' A' st' mo'.

Theorem U_free : forall v RNG A st mo id ch,
  ACCTc v RNG A st mo -> (a_live st) !! id = Some ch ->
  TS RNG A (aembed ATOP (afree st (Some id))) mo (free_leaf v id st mo RNG).
Proof.
  intros v RNG A st mo id ch HACC Hl.
  pose proof HACC as (HI & Q1 & Q2 & ER & Hv & HC & _). pose proof HI as [HA HM].
  pose proof (afree_core (RESV:=RESV) (ATOP:=ATOP) st mo id ch HI Q1 Q2 Hl) as HTOT.
  set (SB := a_space_beg st) in *. set (PA := a_ptr_array st) in *.
  destruct (KI_entry v RNG A st mo 0 HACC ltac:(lia)) as (k & HK & HP & HL).
  pose proof (evq_afree SB PA st id HL) as HEV.
  destruct (INV_SB_PA st mo HI) as [HSB HPA].
  pose proof (GP_nonneg st (LW_emb _ _ _ HL)) as G0.
  pose proof (TS_aembed NMAX SB PA (Abase_x SB PA) NLK0 HLIM
                ltac:(intros z' Hz'; left; exists z'; split; [exact Hz'| reflexivity])
                (afree st (Some id)) (RPst SB PA) (free_post st id) (GP st + 0) (PHI st + 0) A k (k + (GP st + 0)) mo RNG mo
                HTOT HEV HK (vmh_refl mo) ltac:(rewrite ER; apply fp_le_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as HTS.
  rewrite ER. eapply TS_mono; [exact HTS|].
  intros st' RNG' A' mo' _ (b' & k' & gp' & HRP & HPOST & HK' & Hgp' & Hkg & HH & HFL & ERN).
  destruct HRP as [HL' HGP']. destruct HK' as (_ & _ & _ & HAB' & HCV' & HBU' & Hk').
  pose proof HL' as (ESB & EPA & _).
  destruct HPOST as (HI' & ELIVE & ENEXT & B1 & B2 & EEMB & CK).
  split; [exact HH|]. split; [rewrite <- ER; exact HFL|]. split; [exact ELIVE|]. split; [exact ENEXT|]. split; [exact CK|].
  assert (ESB' : secbytes (live_chunks st') <= secbytes (live_chunks st)).
  { assert (PL : Permutation (live_chunks st) (ch :: live_chunks st')).
    { pose proof (live_chunks_delete st id ch Hl) as X. unfold live_chunks in X |- *. cbn [a_live set_live] in X. rewrite ELIVE. exact X. }
    rewrite (secbytes_perm _ _ PL).
    assert (HW' : Forall (chunk_wf ATOP) (live_chunks st')).
    { destruct HI' as [HA' _]. destruct HA' as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HW _]. exact HW. }
    assert (Hch : chunk_wf ATOP ch).
    { destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HW _].
      eapply (proj1 (Forall_forall _ _) HW). eapply Permutation_in; [apply Permutation_sym; exact PL| left; reflexivity]. }
    destruct ch as [c0 n0|mb0 ms0 n0]; cbn [secbytes]; [lia|]. cbn in Hch. lia. }
  assert (EES : emb_sz st' = emb_sz st) by (unfold emb_sz; rewrite EEMB; reflexivity).
  split; [exact HI'|]. split; [exact B1|]. split; [exact B2|]. split; [exact ERN|]. split; [lia|]. split; [lia|].
  exists k'. rewrite ESB, EPA. split; [exact HAB'|]. split; [exact HCV'|]. split; [exact HBU'|]. split; [exact Hk'|]. lia.
Qed.

Definition arealloc_m (st : astate) (p : AsanCtrl.aptr) (n : Z) : AM (astate * option AsanCtrl.aptr) :=
  sbind (amalloc ATOP RESV st n) (fun r =>
    match snd r with
    | Some q => sbind (afree (fst r) (Some p)) (fun st2 => aret (st2, Some q))
    | None => aret r
    end).

Definition realloc_leaf (v n : Z) (p : AsanCtrl.aptr) (st : astate) (mo0 : Model) (RNG0 : footprint) : postT (astate * option AsanCtrl.aptr) :=
  fun r RNG' A' mo' =>
    vmh mo0 mo' /\ fp_le RNG0 RNG' /\
    match snd r with
    | Some q => q = a_next st /\ (a_live st) !! q = None
                /\ (exists ch, a_live (fst r) = delete p (<[q := ch]> (a_live st)) /\ chunk_size ch = n)
                /\ ACCTc (v - (if is_primary n then 0 else n)) RNG' A' (fst r) mo'
    | None => a_live (fst r) = a_live st /\ ACCTc (v - C_EXH) RNG' A' (fst r) mo'
    end.

Theorem U_realloc : forall v RNG A st mo p chp n,
  ACCTc v RNG A st mo -> (a_live st) !! p = Some chp -> 1 <= n <= AREQMAX -> (is_primary n = false -> n <= v) -> C_EXH <= v ->
  size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX ->
  TS RNG A (aembed ATOP (arealloc_m st p n)) mo (realloc_leaf v n p st mo RNG).
Proof.
  intros v RNG A st mo p chp n HACC Hp Hn Hnv Hcv H24. unfold arealloc_m.
  eapply TS_sbind; [exact (U_malloc v RNG A st mo n HACC Hn Hnv Hcv H24)|].
  intros [st1 res] RNG1 A1 mo1 ACC1 (HH1 & FL1 & CK1 & LEAF). cbn [fst snd] in LEAF |- *. destruct res as [q|].
  - destruct LEAF as (-> & FRESH & (ch & ELIVE & ESZ) & HC1).
    assert (Hp1 : (a_live st1) !! p = Some chp).
    { rewrite ELIVE. rewrite lookup_insert_ne; [exact Hp|]. intros <-. rewrite FRESH in Hp. discriminate. }
    eapply TS_sbind; [exact (U_free _ RNG1 A1 st1 mo1 p chp HC1 Hp1)|].
    intros st2 RNG2 A2 mo2 ACC2 (HH2 & FL2 & ELIVE2 & _ & _ & HC2). unfold aret. rewrite aembed_ret. apply TS_ret_ok; [exact ACC2|].
    split; [exact (vmh_trans _ _ _ HH1 HH2)|]. split; [exact (fp_le_trans _ _ _ FL1 FL2)|]. cbn [fst snd].
    split; [reflexivity|]. split; [exact FRESH|]. split; [exists ch; split; [rewrite ELIVE2, ELIVE; reflexivity| exact ESZ]| exact HC2].
  - destruct LEAF as (ELIVE & _ & HC1). unfold aret. rewrite aembed_ret. apply TS_ret_ok; [exact ACC1|].
    split; [exact HH1|]. split; [exact FL1|]. cbn [fst snd]. split; [exact ELIVE| exact HC1].
Qed.

End OpsM.
End CANSEC1.
End TwinB.
