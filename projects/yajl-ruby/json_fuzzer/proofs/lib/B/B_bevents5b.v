(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr ITree Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages LazyModel NodesA Shadow NodesA_mm NodesA_mmW BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase KLiveCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanRep AsanFakeStack AsanPS AsanKern AsanClient AsanDepot AsanBudget AsanBudget2 AsanRepFrame AsanFrame AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base B_alloc_iface B_live B_policy5 B_budget5 B_slack5 B_bundle B_benv5 B_balloc5 B_mmchk5 B_bevents5 BF_fakestack_rep BF_place.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Ltac mproj := rewrite ?m_vmmaps_vm_add_lazy, ?m_vm_lazy_vm_add_lazy, ?m_vm_materialized_vm_add_lazy,
                      ?m_vmmaps_vm_forget_range, ?m_vm_lazy_vm_forget_range, ?m_vm_materialized_vm_forget_range,
                      ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps, ?m_vm_materialized_with_vmmaps,
                      ?m_vmmaps_with_vm_backing, ?m_vm_lazy_with_vm_backing, ?m_vm_materialized_with_vm_backing in *.

Section Ev2.
Variable StdioRep : stdout_st -> mem -> Prop.
Variable RTMisc : aenv -> mem -> Prop.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis LS_L0 : In (Z_to_bv 64 0x7fff7000, Z_to_bv 64 (2^28)) L0.
Hypothesis GS_L0 : In (Z_to_bv 64 0x8fff7000, Z_to_bv 64 (2^41)) L0.
Hypothesis HS_L0 : In (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000) L0.
Hypothesis RES0_low : Forall (fun e => 0x10000 <= elo e /\ ehi e <= 0x603000) RES0.
Hypothesis RES0_cover : forall x, 0x10000 <= x < 0x603000 -> exists e, In e RES0 /\ elo e <= x < ehi e.
Hypothesis RSVD : forall rr x, In rr (ae_reserved E0) -> fst rr <= x < fst rr + snd rr ->
  (exists e, In e (RES0 ++ L0) /\ elo e <= x < ehi e) \/ alloc_ceiling <= x.
Hypothesis RSVD_pos : Forall (fun rr => 0 < snd rr) (ae_reserved E0).

#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (B_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (B_bundle.aN E0 FSB0 HR0).
#[local] Notation aNzc := (B_bundle.aNz E0 FSB0 HR0).
#[local] Notation aEBc := (B_bundle.aEB EB0).
Ltac cstat := try clear HR0_ok.

(* [comment removed for export] *)
Theorem ev_anon_nr : forall R R' s mo mo1 (L : Z),
  let a := aps_alloc s in
  ATOKc R R' s mo -> magree mo mo1 -> KIA (aSc s) (aNc s) (aEBc s) mo1 ->
  L mod 4096 = 0 -> 0x10000 <= L <= NMAXA ->
     (forall eff, mmap_CHK 0 L 3 0x4022 mo1 eff <> CheckUnmodeled)
  /\ (exists eff mo', mmap_CHK 0 L 3 0x4022 mo1 eff = CheckOk mo' [] /\ node_refusal (NMmap 0 L 3 0x4022) mo1 (eff_ret eff) = false)
  /\ (forall eff mo', mmap_CHK 0 L 3 0x4022 mo1 eff = CheckOk mo' [] -> node_refusal (NMmap 0 L 3 0x4022) mo1 (eff_ret eff) = false ->
        mm_answer mo1 eff mo' [] /\ exists r, eff = mkEffectU r [] [(r, Z_to_bv 64 L)] [] [] []
        /\ bv_unsigned r mod 4096 = 0 /\ placed (bv_unsigned r) L
        /\ (forall rr, In rr (ae_reserved E0) -> bv_unsigned r + L <= fst rr \/ fst rr + snd rr <= bv_unsigned r)
        /\ region_free (vm_reserved (m_vmmaps mo1) ++ vm_maps (m_vmmaps mo1)) r (Z_to_bv 64 L) = true
        /\ r = Z_to_bv 64 (bv_unsigned r)
        /\ mo' = m_anon_nr mo1 (bv_unsigned r) L
        /\ KIA (aSc s) (aNc s) (aEBc s) mo' /\ vm_limit (m_vmmaps mo') = 2^39
        /\ vm_maps (m_vmmaps mo') = (r, Z_to_bv 64 L) :: vm_maps (m_vmmaps mo1)
        /\ vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo1) /\ m_vm_lazy mo' = (r, Z_to_bv 64 L) :: m_vm_lazy mo1
        /\ vm_reserved (m_vmmaps mo') = RES0 /\ model_ivs_wf mo' /\ alloc_top (m_vmmaps mo') = alloc_ceiling
        /\ nao (vm_noaccess (m_vmmaps mo')) (vm_maps (m_vmmaps mo')) /\ mwf ((r, Z_to_bv 64 L) :: vm_maps (m_vmmaps mo1))
        /\ OSL aEBc aNzc R s mo' /\ PSL (R' - (L + NMAXA + 4095)) (m_vmmaps mo')).
Proof.
  intros R R' s mo mo1 L a TOK Hag KIA1 LA HL.
  pose proof (ATOK_magree E0 FSB0 HR0 L0 RES0 EB0 R R' s mo mo1 TOK Hag KIA1) as TOK1.
  pose proof (ATOK_window E0 FSB0 HR0 L0 RES0 EB0 R R' s mo1 L TOK1 ltac:(lia)) as WIN.
  destruct TOK1 as ((LI1 & MI1 & HH1) & [O0 OS1] & EV1 & LIM1 & KVM1 & [P0 PS1]). pose proof KVM1 as (KR & KP & KW & KWF & KNA & TOP).
  pose proof alloc_ceiling_range as CR.
  assert (LB : L < 2^47) by (unfold NMAXA in HL; lia).
  pose proof (chk_anon_nr_red L mo1 LA ltac:(lia) LB) as RED.
  assert (PR : page_round_up_Z L = L) by (apply page_round_up_aligned; exact LA).
  split; [| split].
  - intros eff. rewrite RED. apply anon_match_nu.
  - pose proof (mmap_grant_null_rw_lazy L mo1 ltac:(lia)) as G. cbv zeta in G. rewrite PR in G.
    exact (G ltac:(rewrite TOP; lia) WIN).
  - intros eff mo' HC NR. pose proof HC as HC0. rewrite RED in HC. rewrite refusal_errno in NR.
    apply (anon_match_ok L mo1) in HC as (_ & r & -> & RA & R0 & RC & RF & NB & C4); [| exact NR].
    pose proof (check_mmap_only _ _ _ _ _ _ _ _ _ _ HC0) as MMA. split; [exact MMA|]. exists r. split; [reflexivity|].
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr.
    pose proof (grant_placed L0 RES0 LS_L0 GS_L0 HS_L0 RES0_cover mo1 a r L KVM1 ltac:(lia) R0 RC RF) as PL.
    assert (Er : r = Z_to_bv 64 (bv_unsigned r)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (EM : mo' = m_anon_nr mo1 (bv_unsigned r) L).
    { rewrite C4. unfold anon_post, with_mmap_backing. rewrite (proj1 (proj2 cls_anon_nr)). unfold m_anon_nr. rewrite <- Er. reflexivity. }
    split; [exact RA|]. split; [exact PL|].
    split; [intros rr Hrr; exact (grant_apart_reserved E0 L0 RES0 RSVD RSVD_pos mo1 a r L rr KVM1 ltac:(lia) RC RF Hrr)|].
    split; [exact RF|]. split; [exact Er|]. split; [exact EM|]. clear C4. subst mo'. rewrite TOP in RC.
    assert (WF' : model_ivs_wf (m_anon_nr mo1 (bv_unsigned r) L)) by (apply anr_wf; try assumption; lia).
    assert (MW : mwf ((r, Z_to_bv 64 L) :: vm_maps (m_vmmaps mo1))).
    { destruct KW as [D1 D2]. split.
      - intros i j e1 e2 Hi Hj NE. destruct i as [|i]; destruct j as [|j].
        + exfalso; exact (NE eq_refl).
        + cbn in Hi. injection Hi as <-. cbn in Hj. destruct e2 as [b2 s2].
          pose proof (State.region_free_In _ _ _ _ _ RF ltac:(apply in_app_iff; right; eapply nth_error_In; exact Hj)) as OV.
          unfold iv_overlap in OV. unfold elo, ehi. cbn [fst snd]. rewrite !u64_small in OV |- * by lia.
          pose proof (bv_unsigned_in_range 64 s2). apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
        + cbn in Hj. injection Hj as <-. cbn in Hi. destruct e1 as [b1 s1].
          pose proof (State.region_free_In _ _ _ _ _ RF ltac:(apply in_app_iff; right; eapply nth_error_In; exact Hi)) as OV.
          unfold iv_overlap in OV. unfold elo, ehi. cbn [fst snd]. rewrite !u64_small in OV |- * by lia.
          pose proof (bv_unsigned_in_range 64 s1). apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
        + cbn in Hi, Hj. exact (D1 i j e1 e2 Hi Hj ltac:(lia)).
      - constructor; [| exact D2]. unfold elo, ehi. cbn [fst snd]. rewrite !u64_small by lia. lia. }
    split.
    + split; [| split; [eapply mm_answer_minvA; [exact MMA| exact MI1]| rewrite (mm_answer_halted _ _ _ _ MMA); exact HH1]].
      destruct LI1 as [Q1 Q2 Q3 Q4 Q5]. constructor; rewrite ?anr_mat, ?anr_limit; try assumption.
      pose proof (anr_eager mo1 (bv_unsigned r) L KWF ltac:(lia) ltac:(lia) ltac:(lia) RA LA). clear -H Q4. lia.
    + split; [rewrite anr_limit; exact LIM1|]. split; [rewrite anr_maps; rewrite <- Er; reflexivity|].
      split; [apply anr_noaccess|]. split; [rewrite (anr_lazy mo1 (bv_unsigned r) L) by lia; rewrite <- Er; reflexivity|].
      split; [rewrite anr_reserved; exact KR|]. split; [exact WF'|].
      split; [unfold m_anon_nr; mproj; cbn; exact TOP|]. split; [| split; [exact MW| split]].
      * rewrite anr_noaccess, anr_maps. rewrite <- Er. intros e He. destruct (KNA e He) as (Q1 & m1 & Hm1 & Q2 & Q3).
        split; [exact Q1|]. exists m1. split; [right; exact Hm1| exact (conj Q2 Q3)].
      * unfold OSL in *. rewrite anr_limit. exact OS1.
      * pose proof (PSL_grant R' (m_vmmaps mo1) (m_vmmaps (m_anon_nr mo1 (bv_unsigned r) L)) r (Z_to_bv 64 L)
                      (anr_reserved _ _ _) ltac:(rewrite anr_maps, <- Er; reflexivity) ltac:(unfold m_anon_nr; mproj; cbn; reflexivity) PS1) as X.
        rewrite u64_small in X by lia. exact X.
Qed.

(* [comment removed for export] *)
Section Store4.
Variables (s : aps) (a2 : astate) (mo1 mo' : Model) (r : word) (R R' : Z).
Let a := aps_alloc s.
Let rZ := bv_unsigned r.
Let L := kStoreBlockBytes.
Hypothesis Esb : as_store_blocks a2 = as_store_blocks a ++ [rZ].
Hypothesis Esec : as_sec a2 = as_sec a.
Hypothesis Eres : as_residue a2 = as_residue a.
Hypothesis Ereg : forall c, get_region a2 c = get_region a c.
Hypothesis Eptr : as_ptr_committed a2 = as_ptr_committed a.
Hypothesis Enb : as_node_blocks a2 = as_node_blocks a.
Hypothesis RA : rZ mod 4096 = 0.
Hypothesis RP : placed rZ L.
Hypothesis RSV : forall rr, In rr (ae_reserved E0) -> rZ + L <= fst rr \/ fst rr + snd rr <= rZ.
Hypothesis KI : KIA (aSc s) (aNc s) (aEBc s) mo'.
Hypothesis LIM : vm_limit (m_vmmaps mo') = 2^39.
Hypothesis MAPS : vm_maps (m_vmmaps mo') = (r, Z_to_bv 64 L) :: vm_maps (m_vmmaps mo1).
Hypothesis NOACC : vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo1).
Hypothesis LAZY : m_vm_lazy mo' = (r, Z_to_bv 64 L) :: m_vm_lazy mo1.
Hypothesis RES : vm_reserved (m_vmmaps mo') = RES0.
Hypothesis WF' : model_ivs_wf mo'.
Hypothesis TOP' : alloc_top (m_vmmaps mo') = alloc_ceiling.
Hypothesis NA' : nao (vm_noaccess (m_vmmaps mo')) (vm_maps (m_vmmaps mo')).
Hypothesis MW' : mwf ((r, Z_to_bv 64 L) :: vm_maps (m_vmmaps mo1)).
Hypothesis RF : region_free (vm_reserved (m_vmmaps mo1) ++ vm_maps (m_vmmaps mo1)) r (Z_to_bv 64 L) = true.
Hypothesis KV1 : KVM L0 RES0 mo1 a.
Hypothesis OS1 : 0 <= R /\ OSL aEBc aNzc R s mo'.
Hypothesis PS1 : 0 <= R' /\ PSL R' (m_vmmaps mo').
Hypothesis EV1 : ENVOK E0 FSB0 s.
Hypothesis CR : 2050 <= R.

Lemma regions_bytes_s2 : regions_bytes a2 = regions_bytes a.
Proof. cstat. unfold regions_bytes. induction classes30 as [|c l IH]; [reflexivity|]. cbn [fold_right]. rewrite Ereg, IH. reflexivity. Qed.

Lemma aS_s2_grow : forall w, aSc s w -> aSc (sA a2 s) w.
Proof.
  cstat. intros w [M H]. unfold B_bundle.aS, B_policy5.aS, aSa, sA, aps_set_alloc, in_interiors, in_stores in *. cbn [aps_alloc] in *.
  split; [exact M|]. fold a. fold a in H. rewrite Esec, Eres, Esb.
  destruct H as [H|[H|[H|H]]]; [left; exact H| right; left; exact H| right; right; left; exact H|].
  right; right; right. destruct H as (b & Hb & X). exists b. split; [apply in_app_iff; left; exact Hb| exact X].
Qed.

Lemma ATOK_store_append : ATOKc (R - 2050) R' (sA a2 s) mo'.
Proof.
  pose proof KV1 as (KR & (fog & PM & FG1 & FG2) & KW & KWF & KNA & KT). destruct OS1 as [O0 O1].
  assert (EE : aEBc (sA a2 s) = aEBc s).
  { unfold B_bundle.aEB, B_policy5.aEB, aEBa, a_eager_bytes, AsanState.sec_bytes, sA, aps_set_alloc. cbn [aps_alloc]. fold a. rewrite regions_bytes_s2, Esec, Eptr, Enb. reflexivity. }
  assert (EZ : aNzc (sA a2 s) = aNzc s + 2050).
  { unfold B_bundle.aNz, B_policy5.aNz, aNza, interiors_bound, sA, aps_set_alloc. cbn [aps_alloc]. fold a. rewrite Esec, Eres, Esb.
    unfold zlen. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn. lia. }
  pose proof (AHK_aN_bound E0 FSB0 HR0 HR0_ok (sA a2 s)) as NB.
  change (B_bundle.aN E0 FSB0 HR0 (sA a2 s)) with (aNc (sA a2 s)) in NB. change (B_bundle.aNz E0 FSB0 HR0 (sA a2 s)) with (aNzc (sA a2 s)) in NB.
  split; [| split; [| split; [| split; [| split]]]].
  - destruct KI as (L1 & M1 & H1). split; [| split; [exact M1| exact H1]].
    eapply LI_grow; [exact L1| exact aS_s2_grow| intros l ND HF; exact (aS_card (A0 E0 FSB0 HR0) (aps_alloc (sA a2 s)) l ND HF)| rewrite EE; lia|].
    rewrite LIM, EE, page_size_val. unfold OSL in O1. rewrite LIM in O1. clear -O1 EZ NB CR. nia.
  - unfold OSL in *. rewrite EE, EZ. split; [clear -O0 CR; lia| clear -O1 CR; lia].
  - unfold ENVOK, sA, aps_set_alloc in *. cbn [aps_env aps_fsbase] in *. exact EV1.
  - exact LIM.
  - unfold KVM. split; [exact RES|]. split; [| split; [rewrite MAPS; exact MW'| split; [exact WF'| split; [exact NA'| exact TOP']]]].
    exists fog. split; [| split; [exact FG1| exact FG2]]. rewrite MAPS.
    unfold sA, aps_set_alloc, amaps. cbn [aps_alloc]. fold a. rewrite Esec, Enb, Esb, map_app. cbn [map].
    assert (EW : went rZ kStoreBlockBytes = (r, Z_to_bv 64 L)) by (unfold went, kwz, rZ, L; rewrite Z_to_bv_bv_unsigned; reflexivity).
    rewrite EW. eapply Permutation_trans; [apply Permutation_cons; [reflexivity| exact PM]|].
    unfold amaps. rewrite !app_assoc. apply Permutation_cons_append.
  - exact PS1.
Qed.

Lemma AKern_store_append : forall P D,
  AKern E0 a mo1 -> AWf E0 P D a -> AKern E0 a2 mo'.
Proof.
  cstat. intros P D K1 WF. pose proof KV1 as (KR & KP & KW & KWF & KNA & KT).
  pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. pose proof alloc_ceiling_range as ACR.
  pose proof RP as (RP1 & RP2 & RP3). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, rZ, L, kStoreBlockBytes in RP1, RP2, RP3.
  assert (DJ : forall m, In m (vm_maps (m_vmmaps mo1)) -> ehi m <= rZ \/ rZ + L <= elo m).
  { intros [b sz] Hm. pose proof (State.region_free_In _ _ _ _ _ RF ltac:(apply in_app_iff; right; exact Hm)) as OV.
    unfold iv_overlap in OV. unfold elo, ehi, rZ, L, kStoreBlockBytes in *. cbn [fst snd]. pose proof (bv_unsigned_in_range 64 sz).
    rewrite !u64_small in OV by lia. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia. }
  (* [comment removed for export] *)
  assert (ERW : forall x n, eager_rw mo1 x n -> eager_rw mo' x n).
  { intros x n (I1 & I2 & I3). destruct I1 as (m & Hm & X1 & X2). split; [| split]; [exists m; rewrite MAPS; split; [right; exact Hm| split; assumption]| rewrite NOACC; exact I2|].
    rewrite LAZY. intros e [<-|He]; [| exact (I3 e He)]. unfold elo, ehi. cbn [fst snd]. fold rZ.
    pose proof (DJ m Hm). unfold L, kStoreBlockBytes in *. rewrite u64_small by lia. lia. }
  assert (INS : forall x n, inside (vm_maps (m_vmmaps mo1)) x n -> inside (vm_maps (m_vmmaps mo')) x n).
  { intros x n (m & Hm & X). exists m. rewrite MAPS. split; [right; exact Hm| exact X]. }
  destruct K1. constructor.
  - rewrite MAPS. right. exact ak_resv.
  - exact ak_resv_geom.
  - destruct ak_reginfo as [I1 I2]. split; [apply INS; exact I1| rewrite NOACC; exact I2].
  - intros c Hc Hm. rewrite Ereg in *. apply ERW. exact (ak_user c Hc Hm).
  - intros c Hc Hm. rewrite Ereg in *. apply ERW. exact (ak_fa c Hc Hm).
  - rewrite MAPS. right. exact ak_ptr.
  - rewrite Eptr. intros Hp. apply ERW. exact (ak_ptr_head Hp).
  - rewrite Eptr, NOACC. exact ak_ptr_tail.
  - rewrite Esec. intros sc' Hsc'. destruct (ak_sec sc' Hsc') as [S1 S2]. split; [rewrite MAPS; right; exact S1| apply ERW; exact S2].
  - apply ERW. exact ak_thread.
  - apply ERW. exact ak_depot_nodes.
  - destruct ak_store as [I1 I2]. split; [apply INS; exact I1| rewrite NOACC; exact I2].
  - rewrite Enb. intros b Hb. destruct (ak_node_blocks b Hb) as [N1 N2]. split; [rewrite MAPS; right; exact N1| apply ERW; exact N2].
  - rewrite Esb. intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|[]]].
    + destruct (ak_store_blocks b Hb) as [I1 I2]. split; [apply INS; exact I1| rewrite NOACC; exact I2].
    + split.
      * exists (r, Z_to_bv 64 L). rewrite MAPS. split; [left; reflexivity|]. unfold elo, ehi, rZ, L, kStoreBlockBytes. cbn [fst snd]. rewrite u64_small by lia. lia.
      * rewrite NOACC. intros e He Hpos. destruct (KNA e He) as (_ & m & Hm & Q1 & Q2). pose proof (DJ m Hm). unfold L in *. lia.
  - rewrite Enb, Esb, Esec. intros b len Hb.
    assert (OLD : (In b (as_node_blocks a) /\ len = kDepotNodeBlockBytes) \/ (In b (as_store_blocks a) /\ len = kStoreBlockBytes) \/ (b = rZ /\ len = L)).
    { destruct Hb as [[Hb E]|[Hb E]]; [left; auto|]. apply in_app_iff in Hb; destruct Hb as [Hb|[<-|[]]]; [right; left; auto| right; right; auto]. }
    destruct OLD as [Hb'|[Hb'|[-> ->]]]; [exact (ak_blocks_sep b len (or_introl Hb'))| exact (ak_blocks_sep b len (or_intror Hb'))|].
    split; [exact (placed_app_mem _ _ RP)|]. split; [exact (proj1 (proj2 RP))|]. split; [unfold kPageSize; exact RA|].
    split. { pose proof (DJ _ ak_resv) as DR. unfold went, kwz, elo, ehi, kResvLen in DR. cbn [fst snd] in DR.
             pose proof WF as ((_ & E2 & _ & _ & E5 & _) & _). rewrite kHighMemBeg_val in E2.
             rewrite !u64_small in DR by lia. unfold kResvLen. clear -DR. lia. }
    split. { intros sc' Hsc'. destruct (ak_sec sc' Hsc') as [S1 _]. pose proof (DJ _ S1) as DS. unfold went, kwz, elo, ehi in DS. cbn [fst snd] in DS.
             pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & SC3 & _) & _). destruct (SC3 sc' Hsc') as (_ & Q2 & Q3 & Q4 & _).
             unfold app_mem in Q2. rewrite kLowAppEnd_val, kHighMemBeg_val in Q2. rewrite !u64_small in DS by lia. clear -DS. lia. }
    exact RSV.
  - rewrite LAZY, Esb, Eptr. intros e [<-|He].
    + right; right; left. exists rZ. split; [apply in_app_iff; right; left; reflexivity|]. unfold elo, ehi, rZ, L. cbn [fst snd]. unfold kStoreBlockBytes. rewrite u64_small by lia. lia.
    + destruct (ak_lazy e He) as [X|[X|[X|[X|X]]]]; [left; exact X| right; left; exact X| | right; right; right; left; exact X|].
      * right; right; left. destruct X as (b & Hb & X1 & X2). exists b. split; [apply in_app_iff; left; exact Hb| split; assumption].
      * right; right; right; right. destruct X as (X0 & X1 & X2 & X3). split; [exact X0|]. split; [exact X1|]. split; intros c Hc Hm; rewrite Ereg in *; [exact (X2 c Hc Hm)| exact (X3 c Hc Hm)].
  - rewrite Esec. exact ak_store_sep.
Qed.
End Store4.
End Ev2.
End RC__1.
