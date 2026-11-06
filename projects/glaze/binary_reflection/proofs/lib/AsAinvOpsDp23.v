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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)

Section Dp2.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Ztac := try ceil; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.
  Ltac uilia := unfold DEPOT_NIDS, DEPOT_MAP1 in *; unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.

  (* [comment removed for export] *)
  Definition nn_idx (st : ast) : Z := Z.of_nat (length (dp_nodeblocks (a_dep st))) + 1.


  Definition foot_depot_ins (st st' : ast) (b : Z) (nn : option Z) (a : Z) : Prop :=
    (DEPOT_TAB bt + 4 * b <= a < DEPOT_TAB bt + 4 * b + 4)
    \/ (DEPOT_NIDS bt <= a < DEPOT_NIDS bt + 16)
    \/ (nn <> None /\ DEPOT_MAP1 bt + 8 * nn_idx st <= a < DEPOT_MAP1 bt + 8 * nn_idx st + 8)
    \/ (SSOBJ bt <= a < SSOBJ bt + 16 + 16 * 2 ^ 12)
    \/ (node_addr bt (a_dep st') (dp_nids (a_dep st) + 1) <= a < node_addr bt (a_dep st') (dp_nids (a_dep st) + 1) + 16)
    \/ (exists q, In q (store_blocks bt (a_dep st')) /\ q <= a < q + 2 ^ 23)
    \/ (exists p, nn = Some p /\ p <= a < p + 2 ^ 20)
    \/ CEIL <= a.

  Definition OPS_REP_depot_insert : Prop := forall st Lc FF M M' mdl mdl' b h s2 sid fr' std' nn ns,
    let st' := op_depot_insert st b h s2 sid fr' std' nn ns in
    let d := a_dep st in let id := dp_nids d + 1 in
    WF bt st Lc FF -> WF bt st' Lc FF -> Rep bt st Lc FF M mdl ->
    0 <= b < 2 ^ 20 ->
    (forall p, nn = Some p -> dyn_ok (bt_ia bt) p (p + 2 ^ 20) /\ p mod PG = 0 /\
        forall lo hi, In (lo, hi) (all_ranges bt st) -> p + 2 ^ 20 <= lo \/ hi <= p) ->
    (forall p, ns = Some p -> dyn_ok (bt_ia bt) p (p + 2 ^ 23) /\ p mod PG = 0 /\
        forall lo hi, In (lo, hi) (all_ranges bt st) -> p + 2 ^ 23 <= lo \/ hi <= p) ->
    (forall p q, nn = Some p -> ns = Some q -> p + 2 ^ 20 <= q \/ q + 2 ^ 23 <= p) ->
    agrees_off (foot_depot_ins st st' b nn) M M' ->
    (* [comment removed for export] *)
    cellZ SG M' (DEPOT_TAB bt + 4 * b) 4 id -> cellZ SG M' (DEPOT_NIDS bt) 4 id -> byteZ SG M' (DEPOT_NIDS bt + 8) 0 ->
    cellZ SG M' (node_addr bt (a_dep st') id) 8 h -> cellZ SG M' (node_addr bt (a_dep st') id + 8) 4 s2 -> cellZ SG M' (node_addr bt (a_dep st') id + 12) 4 sid ->
    (forall p, nn = Some p -> cellZ SG M' (DEPOT_MAP1 bt + 8 * nn_idx st) 8 p /\ writableZ SG M' p (p + 2 ^ 20)) ->
    cellZ SG M' (SSOBJ bt) 8 fr' ->
    (forall i, 0 <= i < 2 ^ 12 ->
        cellZ SG M' (SSOBJ bt + 16 + 16 * i) 8 (nth (Z.to_nat i) (store_blocks bt (a_dep st')) 0)
        /\ cellZ SG M' (SSOBJ bt + 24 + 16 * i) 4 (std' i) /\ byteZ SG M' (SSOBJ bt + 28 + 16 * i) 0) ->
    (forall q, ns = Some q -> writableZ SG M' q (q + 2 ^ 23)) ->
    (* [comment removed for export] *)
    Permutation (vm_maps (m_vmmaps mdl'))
                (List.map (fun p => (Z_to_bv 64 p, Z_to_bv 64 (2 ^ 20))) (blk_opt nn) ++ List.map (fun q => (Z_to_bv 64 q, Z_to_bv 64 (2 ^ 23))) (blk_opt ns) ++ vm_maps (m_vmmaps mdl)) ->
    vm_noaccess (m_vmmaps mdl') = vm_noaccess (m_vmmaps mdl) ->
    (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a \/ (exists q, ns = Some q /\ q <= a < q + 2 ^ 23)) ->
    Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0
                                   /\ 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= bv_unsigned (fst iv)))
           (m_vm_lazy mdl') ->
    vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) -> vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl) ->
    vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) -> vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) ->
    vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) ->
    MInv (a_aa st ++ store_aa ns) mdl' -> eager_used mdl' <= eager_used mdl + 2 ^ 20 * Z.of_nat (length (blk_opt nn)) ->
    Rep bt st' Lc FF M' mdl'.

  (* [comment removed for export] *)
  Lemma node_blocks_ins : forall st b h s2 sid fr' std' nn ns,
    node_blocks bt (a_dep (op_depot_insert st b h s2 sid fr' std' nn ns)) = node_blocks bt (a_dep st) ++ blk_opt nn.
  Proof using. intros. reflexivity. Qed.
  Lemma store_blocks_ins : forall st b h s2 sid fr' std' nn ns,
    store_blocks bt (a_dep (op_depot_insert st b h s2 sid fr' std' nn ns)) = store_blocks bt (a_dep st) ++ blk_opt ns.
  Proof using. intros. reflexivity. Qed.
  Lemma in_blk_opt : forall (o : option Z) x, In x (blk_opt o) <-> o = Some x.
  Proof using. intros [y|] x; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); split; try am_tauto; [intros [->|[]]; reflexivity | intros E; injection E as ->; left; reflexivity | intros E; discriminate E]. Qed.
  Lemma nth_app_old : forall (l l' : list Z) k, (k < length l)%nat -> nth k (l ++ l') 0 = nth k l 0.
  Proof using. intros l l' k Hk. apply app_nth1. exact Hk. Qed.

  Lemma nth_split_Z : forall (L : list Z) j, (j < length L)%nat -> L = firstn j L ++ nth j L 0 :: skipn (S j) L.
  Proof using.
    induction L as [|x t IH]; intros j Hj; [cbn in Hj; lia|].
    destruct j as [|j0]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [firstn skipn nth app] in G in change_no_check G' end). f_equal. apply IH. cbn in Hj. lia.
  Qed.
  Lemma nth_firstn_Z : forall (L : list Z) j j', (j' < j)%nat -> nth j' (firstn j L) 0 = nth j' L 0.
  Proof using.
    induction L as [|x t IH]; intros j j' Hj; [rewrite firstn_nil; reflexivity|].
    destruct j as [|j0]; [lia|]. destruct j' as [|j0']; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [firstn nth] in G in change_no_check G' end). apply IH. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dyn_nodes_disj : forall st Lc FF, WF bt st Lc FF -> forall j' j, (j' < j < length (dp_nodeblocks (a_dep st)))%nat ->
    let q' := nth j' (dp_nodeblocks (a_dep st)) 0 in let q := nth j (dp_nodeblocks (a_dep st)) 0 in
    q' + 2 ^ 20 <= q \/ q + 2 ^ 20 <= q'.
  Proof using.
    intros st Lc FF W j' j Hj. cbn zeta. set (L := dp_nodeblocks (a_dep st)) in *.
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & PWs & _) & _).
    set (fn := fun b : Z => (b, b + 2 ^ 20)).
    assert (EL : L = firstn j L ++ nth j L 0 :: skipn (S j) L) by (apply nth_split_Z; lia).
    assert (E : all_ranges bt st = (bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st) ++ List.map fn (firstn j L))
                                   ++ fn (nth j L 0) :: (List.map fn (skipn (S j) L) ++ List.map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). fold L. fold fn. rewrite EL at 1. rewrite map_app. (lazymatch goal with |- ?G => let G' := eval cbn [List.map] in G in change_no_check G' end). rewrite <- !app_assoc. reflexivity. }
    assert (IN' : In (fn (nth j' L 0)) ((bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st) ++ List.map fn (firstn j L))
                                        ++ (List.map fn (skipn (S j) L) ++ List.map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st))))).
    { apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. apply in_map.
      rewrite <- (nth_firstn_Z L j j') by lia. apply nth_In. rewrite length_firstn. lia. }
    pose proof (PWs _ _ _ _ _ _ E IN') as D. cbn [fst snd] in D. lia.
  Qed.

  Lemma node_blocks_disj : forall st Lc FF, WF bt st Lc FF -> forall k' k, (k' < k < length (node_blocks bt (a_dep st)))%nat ->
    let q' := nth k' (node_blocks bt (a_dep st)) 0 in let q := nth k (node_blocks bt (a_dep st)) 0 in
    q' + 2 ^ 20 <= q \/ q + 2 ^ 20 <= q'.
  Proof using.
    intros st Lc FF W k' k Hk. cbn zeta. unfold node_blocks in *. cbn [length] in Hk.
    destruct k as [|k0]; [lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [nth] in G in change_no_check G' end).
    destruct k' as [|k0'].
    - (lazymatch goal with |- ?G => let G' := eval cbn [nth] in G in change_no_check G' end). pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & INN & _) & _).
      assert (Hq : In (nth k0 (dp_nodeblocks (a_dep st)) 0) (dp_nodeblocks (a_dep st))) by (apply nth_In; lia).
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INN (node_dyn st _ Hq)) as D. hnf in D. cbn in D. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [nth] in G in change_no_check G' end). apply (dyn_nodes_disj st Lc FF W k0' k0). lia.
  Qed.

  Lemma perm_ins2 : forall {A} (N S X C D E : list A), Permutation (N ++ S ++ X ++ (C ++ D ++ E)) (X ++ (C ++ (D ++ N) ++ (E ++ S))).
  Proof using.
    intros A N S X C D E.
    eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- !app_assoc.
    eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- !app_assoc.
    do 3 apply Permutation_app_head. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  Qed.

  Theorem OPS_REP_depot_insert_pf : OPS_REP_depot_insert.
  Proof using.
    intros st Lc FF M M' mdl mdl' b h s2 sid fr' std' nn ns. cbn zeta.
    intros W W' R Hb NNF NSF NNS AGR CT CN CM CH CL CS CNN CF CBI CNS PM NA LZ FL' E1 E2 E3 E4 E6 E5 MI EAG.
    pose proof (ptrarr_vs_store0 bt st Lc FF W) as SEP8.   (* [comment removed for export] *)
    set (st' := op_depot_insert st b h s2 sid fr' std' nn ns) in *.
    set (id := dp_nids (a_dep st) + 1) in *.
    pose proof W as ((WR1 & WR2) & WC & WQ & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM' & (RNG & PW' & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (bt_ok_W bt st Lc FF W) as (I1 & I2 & PR & QI1 & QI2 & QI3 & QI4 & QI5 & QI6 & CC & U1 & U2 & U3 & U4 & DC & DT & DR & DJI).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & YC).
    pose proof (agrees_DEFK _ _ _ AGR) as DEF. pose proof (agrees_at' _ _ _ AGR) as AGF.
    (* [comment removed for export] *)
    assert (DIH : ia_img_lo IA <= DEPOT_TAB bt /\ DEPOT_TAB bt + 0x400010 + 8 * 2 ^ 15 <= ia_img_hi IA).
    { destruct QI2 as (plo & phi & Hin & Hx1 & Hx2). destruct (PR plo phi (or_introl Hin)) as [Ga Gb]. (lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB in G in change_no_check G' end). clear -Hx1 Hx2 Ga Gb. lia. }
    assert (SIH : ia_img_lo IA <= SSOBJ bt /\ SSOBJ bt + 16 + 16 * 2 ^ 12 <= ia_img_hi IA).
    { destruct QI3 as (plo & phi & Hin & Hx1 & Hx2). destruct (PR plo phi (or_introl Hin)) as [Ga Gb]. (lazymatch goal with |- ?G => let G' := eval unfold SSOBJ in G in change_no_check G' end). clear -Hx1 Hx2 Ga Gb. lia. }
    (* [comment removed for export] *)
    assert (NID0 : 0 <= dp_nids (a_dep st)).
    { destruct WD as (_ & _ & _ & D4 & _). pose proof (D4 0 ltac:(lia)). lia. }
    assert (HID' : 1 <= id <= dp_nids (a_dep st')) by (subst id st'; (lazymatch goal with |- ?G => let G' := eval cbn [a_dep op_depot_insert dp_nids] in G in change_no_check G' end); lia).
    destruct (node_addr_range bt st' Lc FF W' id HID') as (NIn' & NA1 & NA2 & NA3). pose proof (node_addr_block bt st' id HID') as [NB1 NB2].
    set (na := node_addr bt (a_dep st') id) in *. set (nb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st')) 0) in *.
    assert (NBcase : In nb (node_blocks bt (a_dep st)) \/ nn = Some nb).
    { subst nb st'. rewrite node_blocks_ins in NIn'. apply in_app_iff in NIn'. destruct NIn' as [X|X]; [left; exact X | right; apply in_blk_opt; exact X]. }
    (* [comment removed for export] *)
    assert (NNIDX : nn <> None -> 0 <= nn_idx st < 2 ^ 15 /\ nn_idx st = id / 2 ^ 16).
    { intros NNe. pose proof W' as (_ & _ & _ & _ & _ & _ & (_ & _ & D3' & _ & _ & D6' & _) & _).
      subst st'. cbn [a_dep op_depot_insert dp_nids dp_nodeblocks] in D3', D6'. fold id in D3', D6'. rewrite length_app, Nat2Z.inj_add in D6'.
      destruct nn as [p|]; [| exfalso; exact (NNe eq_refl)]. cbn [blk_opt length Z.of_nat Pos.of_succ_nat] in D6'. (lazymatch goal with |- ?G => let G' := eval unfold nn_idx in G in change_no_check G' end).
      assert (E : Z.of_nat (length (dp_nodeblocks (a_dep st))) + 1 = id / 2 ^ 16) by lia.
      split; [| exact E]. rewrite E. clear -D3' HID'. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    assert (AGZ : forall i, 0 <= i < 2 ^ 64 ->
              ~ (DEPOT_TAB bt <= i < DEPOT_TAB bt + 0x400010 + 8 * 2 ^ 15) -> ~ (SSOBJ bt <= i < SSOBJ bt + 16 + 16 * 2 ^ 12) ->
              (forall q, In q (node_blocks bt (a_dep st)) -> ~ (q <= i < q + 2 ^ 20)) ->
              (forall q, In q (store_blocks bt (a_dep st)) -> ~ (q <= i < q + 2 ^ 23)) ->
              (forall p, nn = Some p -> ~ (p <= i < p + 2 ^ 20)) -> (forall q, ns = Some q -> ~ (q <= i < q + 2 ^ 23)) ->
              i < CEIL -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hr N1 N2 N3 N4 N5 N6 N7. apply AGF; [| exact Hr]. intros Hf. unfold foot_depot_ins in Hf. fold st' in Hf. fold id in Hf. fold na in Hf.
      destruct Hf as [Hf|[Hf|[[NNe Hf]|[Hf|[Hf|[(q & Hq & Hf)|[(p & Hp & Hf)|Hf]]]]]]].
      3: pose proof (NNIDX NNe) as [NNI _].
      - apply N1. clear -Hf Hb. unfold DEPOT_NIDS, DEPOT_MAP1 in *. lia.
      - apply N1. clear -Hf. unfold DEPOT_NIDS, DEPOT_MAP1 in *. lia.
      - apply N1. clear -Hf NNI. unfold DEPOT_NIDS, DEPOT_MAP1 in *. lia.
      - exact (N2 Hf).
      - destruct NBcase as [X|X]; [apply (N3 nb X) | apply (N5 nb X)]; clear -Hf NB1 NB2; lia.
      - subst st'. rewrite store_blocks_ins in Hq. apply in_app_iff in Hq. destruct Hq as [X|X]; [exact (N4 q X Hf) | apply in_blk_opt in X; exact (N6 q X Hf)].
      - exact (N5 p Hp Hf).
      - lia. }
    (* [comment removed for export] *)
    assert (NBR : forall q, In q (node_blocks bt (a_dep st)) -> In (q, q + 2 ^ 20) (all_ranges bt st)).
    { intros q [<- | Hq]; [exact (all_ranges_fixed bt st _ INN) | exact (all_ranges_dyn bt st _ (node_dyn st q Hq))]. }
    assert (SBR : forall q, In q (store_blocks bt (a_dep st)) -> In (q, q + 2 ^ 23) (all_ranges bt st)).
    { intros q [<- | Hq]; [exact (all_ranges_fixed bt st _ INS) | exact (all_ranges_dyn bt st _ (store_dyn st q Hq))]. }
    (* [comment removed for export] *)
    assert (RNGfree : forall lo hi, In (lo, hi) (all_ranges bt st) ->
              (forall q, In q (node_blocks bt (a_dep st)) -> hi <= q \/ q + 2 ^ 20 <= lo) ->
              (forall q, In q (store_blocks bt (a_dep st)) -> hi <= q \/ q + 2 ^ 23 <= lo) ->
              forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hin VN VS i Hi Hr. destruct (RNG lo hi Hin) as ((A1 & A2 & A3 & A4 & A5) & _).
      apply AGZ; [exact Hr | clear -Hi A4 DIH; lia | clear -Hi A4 SIH; lia | | | | | clear -Hi A3; lia].
      - intros q Hq. pose proof (VN q Hq). lia.
      - intros q Hq. pose proof (VS q Hq). lia.
      - intros p0 Hp. destruct (NNF p0 Hp) as (_ & _ & DJ). pose proof (DJ lo hi Hin). lia.
      - intros q0 Hq. destruct (NSF q0 Hq) as (_ & _ & DJ). pose proof (DJ lo hi Hin). lia. }
    (* [comment removed for export] *)
    assert (IMGfree : forall i, ia_img_lo IA <= i < ia_img_hi IA ->
              ~ (DEPOT_TAB bt <= i < DEPOT_TAB bt + 0x400010 + 8 * 2 ^ 15) -> ~ (SSOBJ bt <= i < SSOBJ bt + 16 + 16 * 2 ^ 12) ->
              M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi N1 N2.
      apply AGZ; [clear -Hi I1 I2; ulia | exact N1 | exact N2 | | | | | clear -Hi I2; ulia].
      - intros q Hq. destruct (RNG _ _ (NBR q Hq)) as ((_ & _ & _ & A4 & _) & _). clear -Hi A4. lia.
      - intros q Hq. destruct (RNG _ _ (SBR q Hq)) as ((_ & _ & _ & A4 & _) & _). clear -Hi A4. lia.
      - intros p0 Hp. destruct (NNF p0 Hp) as ((_ & _ & _ & A4 & _) & _). clear -Hi A4. lia.
      - intros q0 Hq. destruct (NSF q0 Hq) as ((_ & _ & _ & A4 & _) & _). clear -Hi A4. lia. }
    (* [comment removed for export] *)
    assert (BANDfree : forall i, AS_LO <= i < AS_HEAPLO -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi.
      apply AGZ; [clear -Hi; ulia | clear -Hi DIH I2; lia | clear -Hi SIH I2; lia | | | | | clear -Hi; ulia].
      - intros q Hq. destruct (RNG _ _ (NBR q Hq)) as ((_ & _ & _ & _ & A5) & _). clear -Hi A5. lia.
      - intros q Hq. destruct (RNG _ _ (SBR q Hq)) as ((_ & _ & _ & _ & A5) & _). clear -Hi A5. lia.
      - intros p0 Hp. destruct (NNF p0 Hp) as ((_ & _ & _ & _ & A5) & _). clear -Hi A5. lia.
      - intros q0 Hq. destruct (NSF q0 Hq) as ((_ & _ & _ & _ & A5) & _). clear -Hi A5. lia. }
    (* [comment removed for export] *)
    assert (FIXfree : forall lo hi, In (lo, hi) (bt_fixed bt) ->
              (hi <= bt_nodes0 bt \/ bt_nodes0 bt + 2 ^ 20 <= lo) -> (hi <= bt_store0 bt \/ bt_store0 bt + 2 ^ 23 <= lo) ->
              forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hin VN VS. apply (RNGfree lo hi (all_ranges_fixed bt st _ Hin)).
      - intros q [<- | Hq]; [exact VN|]. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hin (node_dyn st q Hq)) as D. hnf in D. cbn in D. lia.
      - intros q [<- | Hq]; [exact VS|]. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hin (store_dyn st q Hq)) as D. hnf in D. cbn in D. lia. }
    (* [comment removed for export] *)
    assert (SECfree : forall sc, In sc (a_sec st) -> forall i, sc_map sc <= i < sc_map sc + sc_mapsz sc -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros sc Hs. apply (RNGfree _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))).
      - intros q [<- | Hq]; [pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INN (sec_dyn st sc Hs)) as D; hnf in D; cbn in D; lia|].
        pose proof (sec_vs_node bt st Lc FF W sc q Hs Hq). lia.
      - intros q [<- | Hq]; [pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INS (sec_dyn st sc Hs)) as D; hnf in D; cbn in D; lia|].
        pose proof (sec_vs_store bt st Lc FF W sc q Hs Hq). lia. }
    (* [comment removed for export] *)
    pose proof (fixed_sep bt st Lc FF W _ _ _ _ IN6 INN ltac:(destruct (space_facts bt st Lc FF W) as (_ & _ & SP7 & SP8 & _); intros E; injection E; clear -SP7 SP8; unfold KSPACE, PG in *; lia)) as V6N.
    pose proof (fixed_sep bt st Lc FF W _ _ _ _ IN6 INS ltac:(destruct (space_facts bt st Lc FF W) as (_ & _ & SP7 & SP8 & _); intros E; injection E; clear -SP7 SP8; unfold KSPACE, PG in *; lia)) as V6S.
    pose proof (fixed_sep bt st Lc FF W _ _ _ _ IN8 INN ltac:(clear; intros E; injection E; lia)) as V8N.
    pose proof (fixed_sep bt st Lc FF W _ _ _ _ INT INN ltac:(clear; intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)) as VTN.
    pose proof (fixed_sep bt st Lc FF W _ _ _ _ INT INS ltac:(clear; intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)) as VTS.
    pose proof (fixed_sep bt st Lc FF W _ _ _ _ INFS INN ltac:(clear; intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end); lia)) as VFN.
    pose proof (fixed_sep bt st Lc FF W _ _ _ _ INFS INS ltac:(clear; intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end); lia)) as VFS.
    pose proof (fixed_sep bt st Lc FF W _ _ _ _ INC INN ltac:(clear; intros E; injection E; lia)) as VCN.
    pose proof (fixed_sep bt st Lc FF W _ _ _ _ INC INS ltac:(clear; intros E; injection E; lia)) as VCS.
    assert (V8S : bt_ptrarr bt + 2 ^ 23 <= bt_store0 bt \/ bt_store0 bt + 2 ^ 23 <= bt_ptrarr bt) by (clear -SEP8; lia).
    box V6N. box V6S. box V8N. box V8S. box VTN. box VTS. box VFN. box VFS. box VCN. box VCS. box SEP8.
    (* [comment removed for export] *)
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by (clear -SP7 SPH; lia). box SP4. box SP5.
    assert (SPCfree : forall i, SBEG <= i < SBEG + KSPACE + PG -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply (FIXfree _ _ IN6); [exact V6N | exact V6S | clear -Hi SP7 SP8; lia | clear -Hi X14 X15; ulia]. }
    assert (HDRfree : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros p' n' i Hown Hfh Hr.
      destruct (hdr_zone bt st Lc FF W p' n' i Hown Hfh) as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')]; [apply SPCfree; clear -Z1 Z2 Z3 Z4 N1'; ulia|].
      destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). apply (SECfree sc' Hs'); [rewrite Eu', En' in *; clear -Z1 A5 A6 N1'; ulia | exact Hr]. }
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    (* [comment removed for export] *)
    pose proof (img_pw bt st Lc FF W) as PWI. unfold img_ranges in PWI. cbn [AsAinvDefs3.PW seps fst snd] in PWI.
    destruct PWI as ((S01 & S02 & _) & (DSsep & S12 & S13 & S14 & S15 & S16 & _) & (S22 & S23 & S24 & S25 & S26 & _) & _). box DSsep.
    assert (IMGR : forall i,
              (ia_instance IA + 112 <= i < ia_instance IA + 985)
              \/ (ia_ialloc_flag IA <= i < ia_ialloc_flag IA + 8) \/ (ia_ialloc_inst IA <= i < ia_ialloc_inst IA + IASZ)
              \/ (bt_tls_fs bt <= i < bt_tls_fs bt + 16) \/ (ia_rtc_sb IA <= i < ia_rtc_sb IA + 8) \/ (ia_rtc_uar IA <= i < ia_rtc_uar IA + 4) ->
              M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hr.
      assert (HI : ia_img_lo IA <= i < ia_img_hi IA).
      { destruct QI1 as (plo1 & phi1 & Hin1 & Hx1 & Hx2). destruct (PR plo1 phi1 (or_introl Hin1)) as [Ga Gb].
        destruct QI4 as (plo4 & phi4 & Hin4 & Hz1 & Hz2). destruct (PR plo4 phi4 (or_introl Hin4)) as [Ge Gf].
        destruct QI5 as (plo5 & phi5 & Hin5 & Hw1 & Hw2). destruct (PR plo5 phi5 (or_introl Hin5)) as [Gg Gh].
        destruct QI6 as (plo6 & phi6 & Hin6 & Hv1 & Hv2). destruct (PR plo6 phi6 (or_introl Hin6)) as [Gi Gj].
        clear -Hr Hx1 Hx2 Hz1 Hz2 Hw1 Hw2 Hv1 Hv2 Ga Gb Ge Gf Gg Gh Gi Gj U1 U2 U3 U4. unfold IASZ in *. dsj; lia. }
      apply IMGfree; [exact HI | |]; (lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB, SSOBJ in G in change_no_check G' end); intros X.
      - destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]; [clear -Hr X S01 | clear -Hr X S12 | clear -Hr X S13 | clear -Hr X S14 | clear -Hr X S15 | clear -Hr X S16]; unfold IASZ in *; lia.
      - destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]; [clear -Hr X S02 | clear -Hr X S22 | clear -Hr X S23 | clear -Hr X S24 | clear -Hr X S25 | clear -Hr X S26]; unfold IASZ in *; lia. }
    clear S01 S02 S12 S13 S14 S15 S16 S22 S23 S24 S25 S26.
    (* [comment removed for export] *)
    assert (CONSTfree : forall c i, In c (bt_consts bt) -> fst (fst c) <= i < fst (fst c) + Z.of_nat (snd (fst c)) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros c i Hc Hi. rewrite Forall_forall in DC. pose proof (DC c Hc i Hi) as ND. unfold img_dyn in ND.
      apply IMGfree; [exact (proj1 (img_kinds bt st Lc FF W i ltac:(left; exists c; split; [exact Hc | exact Hi]))) | |]; (lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB, SSOBJ in G in change_no_check G' end); intros X; apply ND.
      - right; right; right; right; left. exact X.
      - right; right; right; right; right; left. exact X. }
    try ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Y2, Y4, Y6, Y8, Y10, Y12, Y14, Y16.
    assert (IBH : ia_img_lo IA <= ia_instance IA + 112 /\ ia_instance IA + 985 <= ia_img_hi IA).
    { destruct QI1 as (plo & phi & Hin & Hx1 & Hx2). destruct (PR plo phi (or_introl Hin)) as [Ga Gb]. clear -Hx1 Hx2 Ga Gb. lia. }
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact R1 | exact YC |]. intros c0 i Hc0 Hi. exact (CONSTfree c0 i Hc0 Hi). }
    (* [comment removed for export] *)
    split. { change (rep_instance bt st' M') with (rep_instance bt st M').
             eapply rep_instance_frame; [exact DEF | exact R2 | clear -IBH I1; uilia | clear -IBH I2; uilia | clear -X12; uilia | clear -X12 X13 S3; uilia | exact S1 |].
             intros i Hi Hr. unfold instance_cells, IB in Hi.
             destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
             - apply (FIXfree _ _ IN8); [exact V8N | exact V8S | clear -IN S1 S3; lia | exact Hr].
             - apply IMGR. left. clear -Hi NI. lia. }
    (* [comment removed for export] *)
    split. { change (rep_thread bt st' M') with (rep_thread bt st M').
             eapply rep_thread_frame; [exact DEF | exact R3 | clear -X1; uilia | clear -X2; uilia | clear -X3; uilia | clear -X4; uilia | exact (cache_len bt st Lc FF W) |].
             intros i Hi Hr. unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in Hi.
             destruct Hi as [Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|Hi]]]]]]].
             1-6: apply (FIXfree _ _ INT); [exact VTN | exact VTS | clear -Hi; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia | exact Hr].
             all: apply (FIXfree _ _ INC); [exact VCN | exact VCS | clear -Hi; lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. destruct (R4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
             destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
             change (a_reg st' c0) with (a_reg st c0).
             eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | uilia | uilia | uilia | uilia | uilia |].
             intros i Hi Hr. unfold foot_region in Hi. apply SPCfree. clear -Hi Q1 Q2 Q5 Q6 Q7 Q8 Q9 Q10. uilia. }
    (* [comment removed for export] *)
    assert (BR : forall b0, In b0 (a_tq st ++ a_gq st) -> 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP).
    { intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 Hb0) as (_ & BL1 & BL2 & BL3). clear -BL1 BL2 BL3 X14 X15. uilia. }
    assert (BA : forall b0 i, In b0 (a_tq st ++ a_gq st) -> foot_batch b0 i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros b0 i Hb0 Hi Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b0 Hb0) as (CVb & BLb & BL2 & BL3). apply SPCfree. clear -Hi BLb BL2 BL3. uilia. }
    split. { change (a_tq st') with (a_tq st). eapply rep_batches_frame; [exact DEF | exact R5 | intros b0 Hb0; apply BR; apply in_app_iff; left; exact Hb0 |].
             intros b0 i Hb0 Hi Hr. apply (BA b0 i); [apply in_app_iff; left; exact Hb0 | exact Hi | exact Hr]. }
    split. { change (a_gq st') with (a_gq st). eapply rep_batches_frame; [exact DEF | exact R6 | intros b0 Hb0; apply BR; apply in_app_iff; right; exact Hb0 |].
             intros b0 i Hb0 Hi Hr. apply (BA b0 i); [apply in_app_iff; right; exact Hb0 | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st' M') with (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact R7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear -A1 A2 A5 A6 A7. ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply (SECfree sc Hs); [| exact Hr]. pose proof (rz_range (sc_n sc)). clear -Hi A5 A6 A7 H. ulia. }
    (* [comment removed for export] *)
    split. { change (quar st') with (quar st). destruct R8 as [HL HQ]. split.
             - intros p0 n0 Hin. destruct (live_range bt st Lc FF W p0 n0 Hin) as (A1 & A2 & A3 & A4). pose proof (rz_range n0).
               eapply rep_hdr_frame; [exact DEF | exact (HL p0 n0 Hin) | uilia | uilia |].
               intros i Hi Hr. apply (HDRfree p0 n0 i); [left; exact Hin | exact Hi | exact Hr].
             - intros m n0 Hin. destruct (HQ m n0 Hin) as [Hh HWq]. destruct (quar_item_range bt st Lc FF W m n0 Hin) as (A1 & A2 & A3). pose proof (rz_range n0).
               split; [| frW DEF HWq].
               eapply rep_hdr_frame; [exact DEF | exact Hh | uilia | uilia |].
               intros i Hi Hr. apply (HDRfree (m + 16) n0 i); [right; replace (m + 16 - 16) with m by lia; exact Hin | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    assert (AGD : forall i, DEPOT_TAB bt <= i < DEPOT_TAB bt + 0x400010 + 8 * 2 ^ 15 ->
              ~ (DEPOT_TAB bt + 4 * b <= i < DEPOT_TAB bt + 4 * b + 4) -> ~ (DEPOT_NIDS bt <= i < DEPOT_NIDS bt + 16) ->
              ~ (nn <> None /\ DEPOT_MAP1 bt + 8 * nn_idx st <= i < DEPOT_MAP1 bt + 8 * nn_idx st + 8) ->
              M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi N1 N2 N3. apply AGF; [| clear -Hi DIH I1 I2; ulia]. intros Hf. unfold foot_depot_ins in Hf. fold st' in Hf. fold id in Hf. fold na in Hf.
      destruct Hf as [Hf|[Hf|[Hf|[Hf|[Hf|[(q & Hq & Hf)|[(p & Hp & Hf)|Hf]]]]]]].
      - exact (N1 Hf).
      - exact (N2 Hf).
      - exact (N3 Hf).
      - clear -Hf Hi DSsep. unfold DEPOT_TAB, SSOBJ, boxed in *. lia.
      - destruct NBcase as [X|X].
        + destruct (RNG _ _ (NBR nb X)) as ((_ & _ & _ & A4 & _) & _). clear -Hf Hi NB1 NB2 A4 DIH. lia.
        + destruct (NNF nb X) as ((_ & _ & _ & A4 & _) & _). clear -Hf Hi NB1 NB2 A4 DIH. lia.
      - subst st'. rewrite store_blocks_ins in Hq. apply in_app_iff in Hq. destruct Hq as [X|X].
        + destruct (RNG _ _ (SBR q X)) as ((_ & _ & _ & A4 & _) & _). clear -Hf Hi A4 DIH. lia.
        + apply in_blk_opt in X. destruct (NSF q X) as ((_ & _ & _ & A4 & _) & _). clear -Hf Hi A4 DIH. lia.
      - destruct (NNF p Hp) as ((_ & _ & _ & A4 & _) & _). clear -Hf Hi A4 DIH. lia.
      - clear -Hf Hi DIH I2. ulia. }
    (* [comment removed for export] *)
    pose proof WD as (WD1 & WD2 & WD3 & WD4 & WD5 & WD6 & WDrest).
    assert (LNB : length (node_blocks bt (a_dep st)) = S (length (dp_nodeblocks (a_dep st)))) by reflexivity.
    assert (KOLD : forall id', 1 <= id' <= dp_nids (a_dep st) -> (Z.to_nat (id' / 2 ^ 16) < length (node_blocks bt (a_dep st)))%nat).
    { intros id' Hid'. rewrite LNB. assert (0 <= id' / 2 ^ 16 <= dp_nids (a_dep st) / 2 ^ 16) by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]). lia. }
    assert (NAOLD : forall id', 1 <= id' <= dp_nids (a_dep st) -> node_addr bt (a_dep st') id' = node_addr bt (a_dep st) id').
    { intros id' Hid'. (lazymatch goal with |- ?G => let G' := eval unfold node_addr in G in change_no_check G' end). subst st'. rewrite node_blocks_ins. rewrite (nth_app_old _ _ _ (KOLD id' Hid')). reflexivity. }
    assert (NODESEP : forall id', 1 <= id' <= dp_nids (a_dep st) -> node_addr bt (a_dep st) id' + 16 <= na \/ na + 16 <= node_addr bt (a_dep st) id').
    { intros id' Hid'. pose proof (KOLD id' Hid') as K'. pose proof (node_addr_block bt st id' Hid') as [OB1 OB2].
      destruct (node_addr_range bt st Lc FF W id' Hid') as (OIn & _).
      set (q' := nth (Z.to_nat (id' / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *.
      assert (Q0 : 0 <= id' / 2 ^ 16 <= id / 2 ^ 16) by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]).
      destruct (Z.eq_dec (id' / 2 ^ 16) (id / 2 ^ 16)) as [EQ | NEQ].
      - (* [comment removed for export] *)
        assert (Enb : nb = q'). { subst nb q' st'. rewrite node_blocks_ins, <- EQ. apply nth_app_old. exact K'. }
        subst na. unfold node_addr in *. fold nb. rewrite Enb. fold q'. clear -EQ Hid' HID'. subst id. Z.div_mod_to_equations. lia.
      - destruct (lt_dec (Z.to_nat (id / 2 ^ 16)) (length (node_blocks bt (a_dep st)))) as [LT | GE].
        + (* [comment removed for export] *)
          assert (Enb : nb = nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) by (subst nb st'; rewrite node_blocks_ins; apply nth_app_old; exact LT).
          pose proof (node_blocks_disj st Lc FF W (Z.to_nat (id' / 2 ^ 16)) (Z.to_nat (id / 2 ^ 16)) ltac:(lia)) as D. cbn zeta in D. fold q' in D. rewrite <- Enb in D.
          clear -D OB1 OB2 NB1 NB2. lia.
        + (* [comment removed for export] *)
          destruct NBcase as [X | X].
          * exfalso. (* [comment removed for export] *)
            assert (Enb0 : nb = nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st) ++ blk_opt nn) 0) by reflexivity.
            rewrite app_nth2 in Enb0 by lia.
            destruct (blk_opt nn) as [|p r] eqn:EB.
            -- rewrite nth_overflow in Enb0 by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). rewrite Enb0 in X. pose proof (node_blocks_range bt st Lc FF W 0 X). lia.
            -- assert (Ep : nn = Some p) by (apply in_blk_opt; rewrite EB; left; reflexivity).
               assert (r = []) by (destruct nn; cbn in EB; [injection EB as _ <-; reflexivity | discriminate EB]). subst r.
               destruct (Z.to_nat (id / 2 ^ 16) - length (node_blocks bt (a_dep st)))%nat as [|r0] eqn:Er.
               ++ change (nth 0 [p] 0) with p in Enb0. rewrite Enb0 in X. destruct (NNF p Ep) as (_ & _ & DJ). pose proof (DJ _ _ (NBR p X)). lia.
               ++ assert (E0 : nth (S r0) [p] 0 = 0) by (destruct r0; reflexivity). rewrite E0 in Enb0. rewrite Enb0 in X.
                  pose proof (node_blocks_range bt st Lc FF W 0 X). lia.
          * destruct (NNF nb X) as (_ & _ & DJ). pose proof (DJ _ _ (NBR q' OIn)) as DQ. clear -DQ OB1 OB2 NB1 NB2. lia. }
    (* [comment removed for export] *)
    assert (NBSB : forall q q2, In q (node_blocks bt (a_dep st)) -> In q2 (store_blocks bt (a_dep st)) -> q + 2 ^ 20 <= q2 \/ q2 + 2 ^ 23 <= q).
    { intros q q2 [<- | Hq] [<- | Hq2].
      - pose proof (fixed_sep bt st Lc FF W _ _ _ _ INN INS ltac:(clear; intros E; injection E; lia)) as D. clear -D. lia.
      - pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INN (store_dyn st q2 Hq2)) as D. hnf in D. cbn in D. clear -D. lia.
      - pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INS (node_dyn st q Hq)) as D. hnf in D. cbn in D. clear -D. lia.
      - pose proof (ar_disj_app bt st Lc FF W _ _ (q, q + 2 ^ 20) (q2, q2 + 2 ^ 23) (all_ranges_old3 bt st)
                      ltac:(apply in_app_iff; right; apply in_app_iff; right; exact (in_map (fun b0 : Z => (b0, b0 + 2 ^ 20)) _ q Hq)) ltac:(exact (in_map (fun b0 : Z => (b0, b0 + 2 ^ 23)) _ q2 Hq2))) as D.
        hnf in D. cbn in D. clear -D. lia. }
    assert (OLDNBfree : forall q, In q (node_blocks bt (a_dep st)) -> forall j, q <= j < q + 2 ^ 20 -> ~ (na <= j < na + 16) -> M' (Z_to_bv 64 j) = M (Z_to_bv 64 j)).
    { intros q Hq j Hj NN. destruct (RNG _ _ (NBR q Hq)) as ((A1 & A2 & A3 & A4 & A5) & _).
      apply AGF; [| clear -Hj A1 A3; ulia]. intros Hf. unfold foot_depot_ins in Hf. fold st' in Hf. fold id in Hf. fold na in Hf.
      destruct Hf as [Hf|[Hf|[[NNe Hf]|[Hf|[Hf|[(q2 & Hq2 & Hf)|[(p & Hp & Hf)|Hf]]]]]]].
      - clear -Hf Hj A4 DIH Hb. unfold DEPOT_NIDS, DEPOT_MAP1 in *. lia.
      - clear -Hf Hj A4 DIH. unfold DEPOT_NIDS, DEPOT_MAP1 in *. lia.
      - pose proof (NNIDX NNe) as [NNI _]. clear -Hf Hj A4 DIH NNI. unfold DEPOT_NIDS, DEPOT_MAP1 in *. lia.
      - clear -Hf Hj A4 SIH. lia.
      - exact (NN Hf).
      - subst st'. rewrite store_blocks_ins in Hq2. apply in_app_iff in Hq2. destruct Hq2 as [X|X].
        + pose proof (NBSB q q2 Hq X) as D. clear -D Hf Hj. lia.
        + apply in_blk_opt in X. destruct (NSF q2 X) as (_ & _ & DJ). pose proof (DJ _ _ (NBR q Hq)) as D. clear -D Hf Hj. lia.
      - destruct (NNF p Hp) as (_ & _ & DJ). pose proof (DJ _ _ (NBR q Hq)) as D. clear -D Hf Hj. lia.
      - clear -Hf Hj A3. lia. }
    split. { destruct R9 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9). (lazymatch goal with |- ?G => let G' := eval unfold rep_depot in G in change_no_check G' end).
             change (dp_nids (a_dep st')) with id. change (dp_frames (a_dep st')) with fr'. change (dp_stored (a_dep st')) with std'.
             split. { intros i Hi. change (dp_tab (a_dep st') i) with (fupdZ (dp_tab (a_dep st)) b id i). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end).
                      destruct (Z.eqb_spec i b) as [-> | NE]; [exact CT|]. pose proof (D1 i Hi) as C.
                      eapply (cellZ_frame _ _ _ _ _ _ C); [clear -Hi DIH I1; uilia | clear -Hi DIH I2; uilia |]. intros j Hj. cbn [Z.of_nat Pos.of_succ_nat] in Hj.
                      apply AGD; [clear -Hj Hi; lia | clear -Hj Hi NE; lia | clear -Hj Hi; unfold DEPOT_NIDS in *; lia | clear -Hj Hi; unfold DEPOT_MAP1, nn_idx in *; lia]. }
             split; [exact CN|]. split; [exact CM|].
             split. { intros i Hi. subst st'. rewrite node_blocks_ins. pose proof (D4 i Hi) as C.
                      destruct (Z.eq_dec i (nn_idx st)) as [Ei | Ni].
                      - destruct (blk_opt nn) as [|p r] eqn:EB.
                        + rewrite app_nil_r. eapply (cellZ_frame _ _ _ _ _ _ C); [clear -Hi DIH I1; uilia | clear -Hi DIH I2; uilia |]. intros j Hj. cbn [Z.of_nat Pos.of_succ_nat] in Hj.
                          apply AGD; [clear -Hj Hi; unfold DEPOT_MAP1 in *; lia | clear -Hj Hi Hb; unfold DEPOT_MAP1 in *; lia | clear -Hj Hi; unfold DEPOT_MAP1, DEPOT_NIDS in *; lia |].
                          intros [NNe _]. apply NNe. destruct nn; [discriminate EB | reflexivity].
                        + assert (Ep : nn = Some p) by (apply in_blk_opt; rewrite EB; left; reflexivity).
                          assert (r = []) by (destruct nn; cbn in EB; [injection EB as _ <-; reflexivity | discriminate EB]). subst r.
                          destruct (CNN p Ep) as [Cp _]. rewrite Ei.
                          replace (nth (Z.to_nat (nn_idx st)) (node_blocks bt (a_dep st) ++ [p]) 0) with p; [exact Cp|].
                          (lazymatch goal with |- ?G => let G' := eval unfold nn_idx in G in change_no_check G' end). replace (Z.to_nat (Z.of_nat (length (dp_nodeblocks (a_dep st))) + 1)) with (length (node_blocks bt (a_dep st))) by (rewrite LNB; lia).
                          symmetry. apply nth_middle.
                      - replace (nth (Z.to_nat i) (node_blocks bt (a_dep st) ++ blk_opt nn) 0) with (nth (Z.to_nat i) (node_blocks bt (a_dep st)) 0).
                        + eapply (cellZ_frame _ _ _ _ _ _ C); [clear -Hi DIH I1; uilia | clear -Hi DIH I2; uilia |]. intros j Hj. cbn [Z.of_nat Pos.of_succ_nat] in Hj.
                          apply AGD; [clear -Hj Hi; unfold DEPOT_MAP1 in *; lia | clear -Hj Hi Hb; unfold DEPOT_MAP1 in *; lia | clear -Hj Hi; unfold DEPOT_MAP1, DEPOT_NIDS in *; lia |].
                          intros [_ X]. clear -X Hj Ni. lia.
                        + destruct (lt_dec (Z.to_nat i) (length (node_blocks bt (a_dep st)))) as [LT | GE]; [symmetry; apply nth_app_old; exact LT|].
                          rewrite (nth_overflow (node_blocks bt (a_dep st))) by lia. symmetry. apply nth_overflow. rewrite length_app.
                          assert (length (blk_opt nn) <= 1)%nat by (destruct nn; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
                          unfold nn_idx in Ni. rewrite LNB in *. lia. }
             split. { intros id' Hid'. destruct (Z.eq_dec id' id) as [-> | NE].
                      - change (dp_hash (a_dep st') id) with (fupdZ (dp_hash (a_dep st)) id h id). change (dp_link (a_dep st') id) with (fupdZ (dp_link (a_dep st)) id s2 id).
                        change (dp_store (a_dep st') id) with (fupdZ (dp_store (a_dep st)) id sid id). rewrite !fupdZ_same. exact (conj CH (conj CL CS)).
                      - assert (Hold : 1 <= id' <= dp_nids (a_dep st)) by (subst id; lia).
                        change (dp_hash (a_dep st') id') with (fupdZ (dp_hash (a_dep st)) id h id'). change (dp_link (a_dep st') id') with (fupdZ (dp_link (a_dep st)) id s2 id').
                        change (dp_store (a_dep st') id') with (fupdZ (dp_store (a_dep st)) id sid id'). rewrite !fupdZ_other by exact NE.
                        rewrite (NAOLD id' Hold). destruct (D5 id' Hold) as (C1 & C2 & C3).
                        destruct (node_addr_range bt st Lc FF W id' Hold) as (OIn & O1 & O2 & _). pose proof (node_addr_block bt st id' Hold) as [OB1 OB2].
                        pose proof (NODESEP id' Hold) as NS'.
                        assert (AGn : forall j, node_addr bt (a_dep st) id' <= j < node_addr bt (a_dep st) id' + 16 -> M' (Z_to_bv 64 j) = M (Z_to_bv 64 j)).
                        { intros j Hj. apply (OLDNBfree _ OIn); [clear -Hj OB1 OB2; lia | clear -Hj NS'; lia]. }
                        split; [eapply (cellZ_frame _ _ _ _ _ _ C1); [clear -O1; lia | clear -O2; ulia | intros j Hj; apply AGn; cbn [Z.of_nat Pos.of_succ_nat] in Hj; lia]|].
                        split; [eapply (cellZ_frame _ _ _ _ _ _ C2); [clear -O1; lia | clear -O2; ulia | intros j Hj; apply AGn; cbn [Z.of_nat Pos.of_succ_nat] in Hj; lia]|].
                        eapply (cellZ_frame _ _ _ _ _ _ C3); [clear -O1; lia | clear -O2; ulia | intros j Hj; apply AGn; cbn [Z.of_nat Pos.of_succ_nat] in Hj; lia]. }
             split. { intros q Hq. subst st'. rewrite node_blocks_ins in Hq. apply in_app_iff in Hq. destruct Hq as [X|X]; [frW DEF (D6 q X)|].
                      apply in_blk_opt in X. exact (proj2 (CNN q X)). }
             split; [exact CF|].
             split; [exact CBI|].
             intros q Hq. subst st'. rewrite store_blocks_ins in Hq. apply in_app_iff in Hq. destruct Hq as [X|X]; [frW DEF (D9 q X)|].
             apply in_blk_opt in X. exact (CNS q X). }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st' FF M') with (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2].
             pose proof (fixed_sep bt st Lc FF W _ _ _ _ (dtls_member bt st Lc FF W) INN ltac:(clear; intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)) as VDN.
             pose proof (fixed_sep bt st Lc FF W _ _ _ _ (dtls_member bt st Lc FF W) INS ltac:(clear; intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)) as VDS.
             eapply rep_fake_frame; [exact DEF | exact R10 | clear -X5; uilia | clear -X6; uilia | clear -Y11; uilia | clear -Y12; uilia | clear -DT1; uilia | clear -DT2; uilia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). clear -A1 A2 A3 A4 X5 X6. uilia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply (FIXfree _ _ INFS); [exact VFN | exact VFS | clear -Hi; uilia | exact Hr].
               + apply IMGR. right; right; right; left. exact Hi.
               + apply (FIXfree _ _ (dtls_member bt st Lc FF W)); [exact VDN | exact VDS | clear -Hi; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia | exact Hr].
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXfree _ _ INFS); [exact VFN | exact VFS | clear -Hi A1 A2 A4; uilia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st' M') with (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact R11 | clear -Y7; uilia | clear -Y8; uilia | clear -Y9; uilia | clear -Y10; uilia |].
             intros i Hi Hr. unfold ialloc_cells, IA_FLAG, IA_INST in Hi.
             apply IMGR. clear -Hi. (lazymatch goal with |- ?G => let G' := eval unfold IASZ in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    split. { change (rep_shadow bt st' Lc M') with (rep_shadow bt st Lc M').
             eapply rep_shadow_frame; [exact DEF | exact R12 | | | |].
             - intros c0 Hc0. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). clear -Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 X14 X15. ulia.
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear -A1 A2 A3 A4 A5 A6 A7. try ceil; unfold PG, AS_HEAPLO, NMAX in *. Ztac.
             - intros c0 i Hc0 Hi Hr. apply BANDfree. exact (AsAinvZone3b.AsAinvZone3.shreg_in_band bt st Lc FF W c0 i Hc0 ltac:(unfold foot_shreg in Hi; clear -Hi; am_tauto)).
             - intros sc i Hs Hi Hr. apply BANDfree. unfold foot_shsec in Hi. exact (AsAinvZone3b.AsAinvZone3.shsec_in_band bt st Lc FF W sc i Hs (proj1 Hi)). }
    (* [comment removed for export] *)
    split. { destruct R13 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12). (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end).
             assert (HOL : forall a, holes bt st' a <-> holes bt st a) by (intros a; (lazymatch goal with |- ?G => let G' := eval unfold holes in G in change_no_check G' end); change (a_reg st') with (a_reg st); am_tauto).
             assert (COM : forall a, committed bt st' a <-> committed bt st a) by (intros a; (lazymatch goal with |- ?G => let G' := eval unfold committed in G in change_no_check G' end); change (a_reg st') with (a_reg st); change (a_nres st') with (a_nres st); am_tauto).
             split. { destruct L1 as (F6l & PF & FOK & FPW & FH). exists F6l.
                      split. { eapply Permutation_trans; [exact PM|].
                               eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_head; exact PF|].
                               (lazymatch goal with |- ?G => let G' := eval unfold dyn_maps in G in change_no_check G' end). change (a_sec st') with (a_sec st).
                               change (dp_nodeblocks (a_dep st')) with (dp_nodeblocks (a_dep st) ++ blk_opt nn). change (dp_storeblocks (a_dep st')) with (dp_storeblocks (a_dep st) ++ blk_opt ns).
                               rewrite !map_app. rewrite (app_assoc F6l (bt_maps0 bt)). rewrite (app_assoc F6l (bt_maps0 bt) (_ ++ (_ ++ _) ++ _)). apply perm_ins2. }
                      split; [exact FOK|]. split; [exact FPW|]. intros a Ha. rewrite (HOL a). exact (FH a Ha). }
             split. { intros a. rewrite NA, (L2 a), (COM a), (HOL a). am_tauto. }
             split. { intros a. rewrite (LZ a), (L3 a), (COM a), (HOL a). change (dp_storeblocks (a_dep st')) with (dp_storeblocks (a_dep st) ++ blk_opt ns).
                      split.
                      - intros [[X | (q & Hq & Ra)] | (q & Hq & Ra)]; [left; exact X | right; exists q; split; [apply in_app_iff; left; exact Hq | exact Ra] |
                                                                         right; exists q; split; [apply in_app_iff; right; apply in_blk_opt; exact Hq | exact Ra]].
                      - intros [X | (q & Hq & Ra)]; [left; left; exact X|]. apply in_app_iff in Hq. destruct Hq as [Hq | Hq];
                          [left; right; exists q; exact (conj Hq Ra) | right; exists q; split; [apply in_blk_opt; exact Hq | exact Ra]]. }
             split; [exact FL'|]. unfold alloc_top in L10 |- *. rewrite E1, E2, E3, E4, E6, E5, NA. repeat (split; [assumption|]). exact L12. }
    (* [comment removed for export] *)
    split. { destruct R14 as (Bu1 & Bu2 & Bu3 & Bu4 & Bu5 & Bu6 & Bu7 & Bu8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
             change (a_aa st') with (a_aa st ++ store_aa ns). change (a_reg st') with (a_reg st). change (a_sec st') with (a_sec st).
             change (a_shsec st') with (a_shsec st). change (a_nres st') with (a_nres st).
             change (dp_storeblocks (a_dep st')) with (dp_storeblocks (a_dep st) ++ blk_opt ns).
             split. { unfold A_wf in *. apply Forall_app. split; [exact Bu1|]. (lazymatch goal with |- ?G => let G' := eval unfold store_aa in G in change_no_check G' end). apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as (q & <- & Hq).
                      apply in_blk_opt in Hq. destruct (NSF q Hq) as (_ & QM & _). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). unfold page_size, PG in *. clear -QM. repeat split; [lia | exact QM |]. Z.div_mod_to_equations. lia. }
             split; [exact MI|].
             split; [intros lo hi Hin; apply range_allowed_app; exact (Bu3 lo hi Hin)|].
             split; [intros p0 n0 Hin; apply range_allowed_app; exact (Bu4 p0 n0 Hin)|].
             split; [intros c0 Hc0; destruct (Bu5 c0 Hc0) as [Ba Bb]; split; apply range_allowed_app; assumption|].
             split; [intros sc Hs; apply range_allowed_app; exact (Bu6 sc Hs)|].
             split. { intros q [<- | Hq]; [apply range_allowed_app; apply Bu7; left; reflexivity|]. apply in_app_iff in Hq. destruct Hq as [Hq | Hq].
                      - apply range_allowed_app. apply Bu7. right. exact Hq.
                      - apply in_blk_opt in Hq. destruct (NSF q Hq) as ((Q1 & Q2 & Q3 & _) & QM & _).
                        assert (Esa : store_aa ns = [(q, q + 2 ^ 23)]) by (rewrite Hq; reflexivity). rewrite Esa.
                        apply AsAinvHoleU3.range_allowed_last; [exact QM | unfold PG in *; clear -QM; Z.div_mod_to_equations; lia | clear -Q1; lia | clear -Q3; ulia]. }
             change (prim_charge st') with (prim_charge st). change (sec_charge st') with (sec_charge st).
             (lazymatch goal with |- ?G => let G' := eval unfold depot_charge in G in change_no_check G' end). change (dp_nodeblocks (a_dep st')) with (dp_nodeblocks (a_dep st) ++ blk_opt nn). change (dp_storeblocks (a_dep st')) with (dp_storeblocks (a_dep st) ++ blk_opt ns).
             rewrite A_bytes_app, !length_app, !Nat2Z.inj_add. unfold depot_charge in Bu8.
             assert (ESA : A_bytes (store_aa ns) = 2 ^ 23 * Z.of_nat (length (blk_opt ns))) by (destruct ns; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
             rewrite ESA. destruct Bu8 as [Bu8 Bu9]. split; [clear -Bu8 EAG; lia|].
             (* [comment removed for export] *)
             intros s0 Hs0. apply in_app_iff. left. exact (Bu9 s0 Hs0). }
    (* [comment removed for export] *)
    split. { intros p0 n0 Hin. destruct (R15 p0 n0 Hin) as [W1 W2]. split; [frW DEF W1 | frW DEF W2]. }
    split. { intros f' k' Hin'. frW DEF (R16 f' k' Hin'). }
    split. { eapply (cellZ_frame _ _ _ _ _ _ R17); [clear -Y13; uilia | clear -Y14; uilia |]. intros i Hi. apply IMGR. right; right; right; right; left. exact Hi. }
    split. { eapply (cellZ_frame _ _ _ _ _ _ R18); [clear -Y15; uilia | clear -Y16; uilia |]. intros i Hi. apply IMGR. right; right; right; right; right. exact Hi. }
    exact (rep_last_keep bt _ _ M M' DEF R19 (fun H => H)).
  Qed.
End Dp2.
