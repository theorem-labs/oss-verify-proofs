(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMallocI AMalmys ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ABudget ACover AFreeT AFreeB6 ANodijx APgGeo AFreeX1 AFreeX2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeGD0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeWD.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeX1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeX2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeGD0.AFreeX4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeWD.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AFreeGD0 AFreeKH.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize, kSecondaryHeaderSize, kMaxPrimaryUser in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section KChainG.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (p n0 : Z) (i : nat).
  Hypothesis G : kgeo p n0.

  #[warnings="-notation-for-abbreviation"] Local Notation h := (p - 6144).
  #[warnings="-notation-for-abbreviation"] Local Notation msz := (map_size n0).
  #[warnings="-notation-for-abbreviation"] Local Notation pbeg := (a8_pbeg (p - 6144)).
  #[warnings="-notation-for-abbreviation"] Local Notation pend := (a8_pend (p - 6144) (map_size n0)).
  #[warnings="-notation-for-abbreviation"] Local Notation len := (a8_pend (p - 6144) (map_size n0) - a8_pbeg (p - 6144)).
  #[warnings="-notation-for-abbreviation"] Local Notation H0p := (AFreeX2.H0p A p n0 i).
  #[warnings="-notation-for-abbreviation"] Local Notation H1 := (AFreeX2.H1 A p n0 i).
  #[warnings="-notation-for-abbreviation"] Local Notation H2 := (AFreeX2.H2 A p n0 i).


  (* [comment removed for export] *)
  Variables (mv0' mv1' mv2' : mem).
  Hypothesis CL0 : forall x, hidc H0p x = true -> mv0' x = None.
  Hypothesis CL1 : forall x, hidc H1 x = true -> mv1' x = None.
  Hypothesis CL2 : forall x, hidc H2 x = true -> mv2' x = None.

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation rm1 := (AFreeGD0.rm1 A m p n0 i mv0').
  #[warnings="-notation-for-abbreviation"] Local Notation rm2 := (AFreeGD0.rm2 A m p n0 i mv0').
  #[warnings="-notation-for-abbreviation"] Local Notation mv1 := (AFreeGD0.mv1 A m p n0 i mv0').
  #[warnings="-notation-for-abbreviation"] Local Notation rm3 := (AFreeGD0.rm3 A m p n0 i mv0' mv1').
  #[warnings="-notation-for-abbreviation"] Local Notation rm4 := (AFreeGD0.rm4 A m p n0 i mv0' mv1').
  #[warnings="-notation-for-abbreviation"] Local Notation mv2 := (AFreeGD0.mv2 A m p n0 i mv0' mv1').
  #[warnings="-notation-for-abbreviation"] Local Notation rm5 := (AFreeGD0.rm5 A m p n0 i mv0' mv1' mv2').

  Lemma klenU : bv_unsigned (wz pbeg) = pbeg /\ bv_unsigned (wz len) = len /\ bv_unsigned (wz h) = h /\ bv_unsigned (wz msz) = msz /\
               0 < len /\ pbeg + len = pend /\ 0 < pbeg /\ pend <= kHighMemBeg /\ 0x60a000 <= h /\ h + msz <= alloc_ceiling /\ 0 < msz.
  Proof.
    (first [ pose proof ((klen_facts0 p n0 G)) as dR_1; dand14 dR_1 as F1 F2 F3 F4 F5 F6 U1 U2 U3 U4 H5 HHI MP _ | pose proof (klen_facts0 p n0 G) as (F1 & F2 & F3 & F4 & F5 & F6 & U1 & U2 & U3 & U4 & H5 & HHI & MP & _) ]).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.

  Lemma krm2_spec : forall x, rm2 x = if in_range pbeg len x then Some (Z_to_bv 8 0) else rm1 x.
  Proof.
    intros x. (first [ pose proof (klenU) as dR_2; dand9 dR_2 as U1 U2 _ _ F1 F2 F3 F4 _ | pose proof klenU as (U1 & U2 & _ & _ & F1 & F2 & F3 & F4 & _) ]). pose proof alloc_ceiling_val as CE. unfold AFreeGD0.rm2.
    apply (apply_zeros_spec rm1 pbeg len x); clear -F1 F2 F3 F4 CE; kung_all; lia.
  Qed.
  Lemma krm4_spec : forall x, rm4 x = if in_range h msz x then None else rm3 x.
  Proof.
    intros x. (first [ pose proof (klenU) as dR_3; dand11 dR_3 as _ _ U3 U4 _ _ _ _ H5 HHI MP | pose proof klenU as (_ & _ & U3 & U4 & _ & _ & _ & _ & H5 & HHI & MP) ]). pose proof alloc_ceiling_val as CE. unfold AFreeGD0.rm4.
    apply (apply_unmaps_spec rm3 h msz x); clear -H5 HHI MP CE; lia.
  Qed.

  Lemma kin_range_iff : forall a n x, in_range a n x = true <-> a <= bv_unsigned x < a + n.
  Proof. intros a n x. unfold in_range. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
  Lemma kin_range_false : forall a n x, in_range a n x = false <-> ~ (a <= bv_unsigned x < a + n).
  Proof. intros a n x. rewrite <- kin_range_iff. destruct (in_range a n x); split; congruence. Qed.

  (* [comment removed for export] *)
  Lemma kT01 : munch [(pbeg, pend)] mv0' mv1.
  Proof.
    intros x Hx. cbn [outside] in Hx. destruct Hx as [Hx _]. (first [ pose proof (klenU) as dR_4; dand7 dR_4 as _ _ _ _ F1 F2 _ | pose proof klenU as (_ & _ & _ & _ & F1 & F2 & _) ]).
    unfold AFreeGD0.mv1, mrestrict. destruct (hidc H1 x) eqn:E1.
    - (* [comment removed for export] *)
      symmetry. destruct (hidc H0p x) eqn:E0; [exact (CL0 x E0)|]. exfalso.
      unfold hidc in E0, E1. apply Bool.negb_false_iff in E0. apply Bool.negb_true_iff in E1.
      pose proof (kvis_H1 A p n0 i G (bv_unsigned x) E0 ltac:(lia)). congruence.
    - rewrite krm2_spec. destruct (in_range pbeg len x) eqn:R; [apply kin_range_iff in R; exfalso; lia|].
      unfold AFreeGD0.rm1, munrestrict. unfold hidc in E1 |- *. apply Bool.negb_false_iff in E1.
      rewrite (kvis_H1_H0p A p n0 i G (bv_unsigned x) E1). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma kT12 : munch [(h, h + msz)] mv1' mv2.
  Proof.
    intros x Hx. cbn [outside] in Hx. destruct Hx as [Hx _].
    unfold AFreeGD0.mv2, mrestrict. destruct (hidc H2 x) eqn:E2.
    - symmetry. destruct (hidc H1 x) eqn:E1; [exact (CL1 x E1)|]. exfalso.
      unfold hidc in E1, E2. apply Bool.negb_false_iff in E1. apply Bool.negb_true_iff in E2.
      pose proof (vis_H2 A p n0 i (bv_unsigned x) E1 ltac:(lia)). congruence.
    - rewrite krm4_spec. destruct (in_range h msz x) eqn:R; [apply kin_range_iff in R; exfalso; lia|].
      unfold AFreeGD0.rm3, munrestrict. unfold hidc in E2 |- *. apply Bool.negb_false_iff in E2.
      rewrite (vis_H2_H1 A p n0 i (bv_unsigned x) E2). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma khop01 : forall a, 0 <= a < 2^64 -> ~ (pbeg <= a < pend) -> mv1 (wz a) = mv0' (wz a).
  Proof. intros a Ha N. apply kT01. rewrite unsigned_lit by exact Ha. cbn [outside]. split; [exact N| exact I]. Qed.
  Lemma khop12 : forall a, 0 <= a < 2^64 -> ~ (h <= a < h + msz) -> mv2 (wz a) = mv1' (wz a).
  Proof. intros a Ha N. apply kT12. rewrite unsigned_lit by exact Ha. cbn [outside]. split; [exact N| exact I]. Qed.

  (* [comment removed for export] *)
  Lemma kmv1_mid : forall a, pbeg <= a < pend -> hidc H1 (wz a) = false -> mv1 (wz a) = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha V1. (first [ pose proof (klenU) as dR_5; dand9 dR_5 as _ _ _ _ F1 F2 F3 F4 _ | pose proof klenU as (_ & _ & _ & _ & F1 & F2 & F3 & F4 & _) ]). pose proof alloc_ceiling_val as CE.
    unfold AFreeGD0.mv1, mrestrict. rewrite V1. rewrite krm2_spec.
    destruct (in_range pbeg len (wz a)) eqn:R; [reflexivity|]. apply kin_range_false in R. rewrite unsigned_lit in R by (clear -Ha F2 F3 F4 CE; kung_all; lia).
    exfalso. clear -R Ha F2. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma kvis_edges : forall a, (sh h <= a < pbeg \/ pend <= a < sh h + msz / 8) -> in_hullb H2 a = true.
  Proof.
    intros a Ha. unfold AFreeX2.H2. cbn [in_hullb existsb]. unfold AFreeX2.e1, AFreeX2.e2, in_ivb. cbn [fst snd].
    destruct Ha as [Ha|Ha]; [apply Bool.orb_true_iff; left| apply Bool.orb_true_iff; right; apply Bool.orb_true_iff; left]; apply andb_true_iff; rewrite Z.leb_le, Z.ltb_lt; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kmv1_clean : forall x, hidc H1 x = true -> mv1 x = None.
  Proof. intros x E. unfold AFreeGD0.mv1, mrestrict. rewrite E. reflexivity. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma krm5_view : mrestrict (hidc H2) rm5 = mv2'.
  Proof. unfold AFreeGD0.rm5. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact CL2. Qed.

  (* [comment removed for export] *)
  Lemma kmv2_none_map : forall a, h <= a < h + msz -> mv2 (wz a) = None.
  Proof.
    intros a Ha. (first [ pose proof (klenU) as dR_6; dand11 dR_6 as _ _ _ _ _ _ _ _ H5 HHI _ | pose proof klenU as (_ & _ & _ & _ & _ & _ & _ & _ & H5 & HHI & _) ]). pose proof alloc_ceiling_val as CE.
    unfold AFreeGD0.mv2, mrestrict. destruct (hidc H2 (wz a)); [reflexivity|]. rewrite krm4_spec.
    destruct (in_range h msz (wz a)) eqn:R; [reflexivity|]. apply kin_range_false in R. rewrite unsigned_lit in R by lia. exfalso. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kT01_NN : forall x, ~ (pbeg <= bv_unsigned x < pend) -> mv0' x <> None -> mv1 x <> None.
  Proof. intros x Hx NN. rewrite (kT01 x ltac:(cbn [outside]; split; [exact Hx| exact I])). exact NN. Qed.
  Lemma kT12_NN : forall x, ~ (h <= bv_unsigned x < h + msz) -> mv1' x <> None -> mv2 x <> None.
  Proof. intros x Hx NN. rewrite (kT12 x ltac:(cbn [outside]; split; [exact Hx| exact I])). exact NN. Qed.

  (* [comment removed for export] *)
  Lemma kMI1 : mem_inv rsegs mv0' -> mem_inv rsegs mv1.
  Proof.
    intros MI x b E. unfold AFreeGD0.mv1, mrestrict in E. destruct (hidc H1 x) eqn:E1; [discriminate|].
    rewrite krm2_spec in E. destruct (in_range pbeg len x) eqn:R.
    - apply kin_range_iff in R. (first [ pose proof (klenU) as dR_7; dand9 dR_7 as _ _ _ _ F1 F2 F3 F4 _ | pose proof klenU as (_ & _ & _ & _ & F1 & F2 & F3 & F4 & _) ]). pose proof (ka8_geo p n0 G) as (G1 & _).
      (first [ pose proof ((proj2 G)) as dR_8; dand4 dR_8 as _ _ _ SD | pose proof (proj2 G) as (_ & _ & _ & SD) ]).
      apply pa_ro_addr_false. clear -R F2 G1 SD. kung_all. lia.
    - unfold AFreeGD0.rm1, munrestrict, hidc in E. unfold hidc in E1. apply Bool.negb_false_iff in E1.
      rewrite (kvis_H1_H0p A p n0 i G (bv_unsigned x) E1) in E. exact (MI x b E).
  Qed.
  Lemma kMI2 : mem_inv rsegs mv1' -> mem_inv rsegs mv2.
  Proof.
    intros MI x b E. unfold AFreeGD0.mv2, mrestrict in E. destruct (hidc H2 x) eqn:E2; [discriminate|].
    rewrite krm4_spec in E. destruct (in_range h msz x) eqn:R; [discriminate|].
    unfold AFreeGD0.rm3, munrestrict, hidc in E. unfold hidc in E2. apply Bool.negb_false_iff in E2.
    rewrite (vis_H2_H1 A p n0 i (bv_unsigned x) E2) in E. exact (MI x b E).
  Qed.

  (* [comment removed for export] *)
  Lemma krm5_mid : forall a, pbeg <= a < pend -> in_hullb H2 a = false -> rm5 (wz a) = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha V2. (first [ pose proof (klenU) as dR_9; dand11 dR_9 as _ _ _ _ F1 F2 F3 F4 H5 HHI MP | pose proof klenU as (_ & _ & _ & _ & F1 & F2 & F3 & F4 & H5 & HHI & MP) ]). pose proof alloc_ceiling_val as CE.
    pose proof (ka8_geo p n0 G) as (G1 & _). (first [ pose proof ((proj2 G)) as dR_10; dand4 dR_10 as _ _ _ SD | pose proof (proj2 G) as (_ & _ & _ & SD) ]).
    assert (U : bv_unsigned (wz a) = a) by (apply unsigned_lit; clear -Ha F2 F3 F4; kung_all; lia).
    assert (V1 : in_hullb H1 a = false).
    { destruct (in_hullb H1 a) eqn:E; [| reflexivity]. rewrite (vis_H2 A p n0 i a E) in V2; [discriminate|]. clear -Ha F2 F4 G1 SD H5 HHI CE. kung_all. lia. }
    unfold AFreeGD0.rm5, munrestrict, hidc. rewrite U, V2. cbn [negb]. rewrite krm4_spec.
    destruct (in_range h msz (wz a)) eqn:R; [apply kin_range_iff in R; rewrite U in R; exfalso; clear -R Ha F2 F4 G1 SD H5 HHI CE; kung_all; lia|].
    unfold AFreeGD0.rm3, munrestrict, hidc. rewrite U, V1. cbn [negb]. rewrite krm2_spec.
    destruct (in_range pbeg len (wz a)) eqn:R2; [reflexivity|]. apply kin_range_false in R2. rewrite U in R2. exfalso. clear -R2 Ha F2. lia.
  Qed.
  Lemma krm5_hid : forall a, 0 <= a < 2^64 -> in_hullb H0p a = false -> ~ (h <= a < h + msz) -> rm5 (wz a) = m (wz a).
  Proof.
    intros a Ha V0 NM. (first [ pose proof (klenU) as dR_11; dand9 dR_11 as _ _ _ _ F1 F2 F3 F4 _ | pose proof klenU as (_ & _ & _ & _ & F1 & F2 & F3 & F4 & _) ]).
    assert (U : bv_unsigned (wz a) = a) by (apply unsigned_lit; exact Ha).
    assert (V1 : in_hullb H1 a = false).
    { destruct (in_hullb H1 a) eqn:E; [| reflexivity]. rewrite (kvis_H1_H0p A p n0 i G a E) in V0. discriminate. }
    assert (V2 : in_hullb H2 a = false).
    { destruct (in_hullb H2 a) eqn:E; [| reflexivity]. rewrite (vis_H2_H1 A p n0 i a E) in V1. discriminate. }
    unfold AFreeGD0.rm5, munrestrict, hidc. rewrite U, V2. cbn [negb]. rewrite krm4_spec.
    destruct (in_range h msz (wz a)) eqn:R; [apply kin_range_iff in R; rewrite U in R; exfalso; exact (NM R)|].
    unfold AFreeGD0.rm3, munrestrict, hidc. rewrite U, V1. cbn [negb]. rewrite krm2_spec.
    destruct (in_range pbeg len (wz a)) eqn:R2.
    - (* [comment removed for export] *) exfalso. apply kin_range_iff in R2. rewrite U in R2.
      (first [ pose proof ((ka8_geo p n0 G)) as dR_12; dand7 dR_12 as G1 G2 G3 G4 G5 G6 _ | pose proof (ka8_geo p n0 G) as (G1 & G2 & G3 & G4 & G5 & G6 & _) ]).
      unfold AFreeX2.H0p in V0. cbn [in_hullb existsb] in V0. apply Bool.orb_false_iff in V0 as [_ V0]. apply Bool.orb_false_iff in V0 as [V0 _].
      unfold in_ivb in V0. cbn [fst snd] in V0. apply Bool.andb_false_iff in V0. rewrite Z.leb_gt, Z.ltb_ge in V0. clear -V0 R2 F2 G1 G6. lia.
    - unfold AFreeGD0.rm1, munrestrict, hidc. rewrite U, V0. reflexivity.
  Qed.
  Lemma krm5_vis : forall x, hidc H2 x = false -> rm5 x = mv2' x.
  Proof. intros x E. unfold AFreeGD0.rm5, munrestrict. rewrite E. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma kvis_same : forall x, ~ (sh h <= x < sh h + msz / 8) -> ~ (h <= x < h + msz) -> in_hullb H2 x = in_hullb H0p x.
  Proof.
    intros x N1 N2. (first [ pose proof ((ka8_geo p n0 G)) as dR_13; dand7 dR_13 as G1 G2 G3 G4 G5 G6 _ | pose proof (ka8_geo p n0 G) as (G1 & G2 & G3 & G4 & G5 & G6 & _) ]).
    unfold AFreeX2.H0p, AFreeX2.H2. cbn [in_hullb existsb].
    set (RR := existsb (in_ivb x) (AFreeX2.REST A i)). clearbody RR. unfold AFreeX2.e1, AFreeX2.e2, in_ivb. cbn [fst snd].
    destruct RR; [rewrite !Bool.orb_true_r; reflexivity|]. rewrite !Bool.orb_false_r.
    clear -N1 N2 G1 G5 G6.
    destruct (Z.leb_spec (sh h) x); destruct (Z.ltb_spec x pbeg); destruct (Z.leb_spec pend x); destruct (Z.ltb_spec x (sh h + msz / 8));
      destruct (Z.leb_spec h x); destruct (Z.ltb_spec x (h + msz)); cbn [andb orb]; try reflexivity; exfalso; lia.
  Qed.
End KChainG.
