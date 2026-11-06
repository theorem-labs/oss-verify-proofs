(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc APrimCover ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A F_sec_B F_quar_P AQuarT AQuarU F_gct F_depot F_depot_C F_quar_C F_prim_L0 F_hooks F_dealloc
                        F_ialloc F_unwind F_stacktrace F_free_icpt F_free_null AHeap2.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section FF.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation D := (al_depot AL).
Notation THR := (at_thr (al_thread AL)).
Notation TQ := (at_thr (al_thread AL) + TQ_OFF).
Hypothesis AO : alayout_ok AL.

#[using="AO"] Lemma nb_hull_dj : forall (X : pstate) (m : mem) (PN : prim) (VN : Z) hs ch' iv A n,
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch' ->
  0 <= VN -> 16 * VN + Q_BBYTES <= FA_OFF ->
  held_ok PN ((K_BCLASS, VN) :: hs) -> (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls PN c)) ->
  (forall cv, In cv (prim_of ch') -> In cv hs) ->
  chunk_iv AL K_BCLASS VN iv \/ chunk_sh_iv AL K_BCLASS VN iv ->
  qc_hull AL ch' A n -> disjoint_from [iv] A n.
Proof.
  intros X m PN VN hs ch' [a b] A n RP RS HK V0 V1 [ND FH] WFN INH CI HU.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  pose proof (region_range AL K_BCLASS ltac:(lia)) as [RN1 RN2].
  assert (RG : region AL K_BCLASS = al_space AL + K_BCLASS * K_REGION) by reflexivity.
  apply NoDup_cons_iff in ND as [NI _]. apply Forall_cons_iff in FH as [HN FH].
  pose proof (held_geo AL PN AO WFN K_BCLASS VN HN) as GN. cbv zeta in GN. destruct GN as (_ & N1 & N2 & N3 & _ & N5 & N6 & N7). rewrite N5 in N7.
  change (class_size K_BCLASS) with 8192 in *. change (8192 / 8) with 1024 in *.
  unfold chunk_iv, chunk_sh_iv in CI. cbn [fst snd] in CI. change (class_size K_BCLASS) with 8192 in CI. change (8192 / 8) with 1024 in CI.
  cbn [disjoint_from]. split; [| exact I].
  destruct ch' as [[c v|sc] rz n0]; unfold held_kind in HK; cbn [qc_kind] in HK; unfold qc_hull, qc_blk, qc_bsize in HU; cbn [qc_kind prim_of] in HU, INH.
  - assert (HP : held1 PN (c, v)) by (apply (proj1 (Forall_forall _ _) FH); apply INH; left; reflexivity).
    assert (NE : (K_BCLASS, VN) <> (c, v)) by (intros EQ; apply NI; rewrite EQ; apply INH; left; reflexivity).
    destruct (held_pair_apart AL PN K_BCLASS VN c v AO WFN HN HP NE) as [PB PS]. cbv zeta in PB, PS. change (class_size K_BCLASS) with 8192 in PB, PS. change (8192 / 8) with 1024 in PS.
    pose proof (held_geo AL PN AO WFN c v HP) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CS & G5 & G6 & G7). rewrite G5 in G7.
    pose proof (region_range AL c Hc) as [RR1 RR2].
    destruct HU as [[-> ->]|[[-> ->]|[]]]; destruct CI as [CI|CI].
    + clear - CI PB. lia.
    + clear - CI N6 N7 G1 G2 G3 RR1 RR2 SP1. lia.
    + clear - CI G6 G7 N1 N2 N3 RN1 RN2 SP1. lia.
    + clear - CI PS. lia.
  - pose proof (sec_geo AL (snd X) SOK sc HK) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite D8 in D10.
    pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2]. destruct CK as (CK1 & _).
    assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
    assert (DV : (sc_msize sc - 4096) / 8 = sc_msize sc / 8 - 512) by (clear - CM2; Z.div_mod_to_equations; lia).

    assert (MB : b <= sc_beg sc \/ sc_beg sc + sc_msize sc <= a \/ False) by (destruct CI as [CI|CI]; [clear - CI D5 N1 N2 N3 RN1 RN2; lia| clear - CI D4 N6 N7; lia]).
    assert (MS : b <= sh (sc_beg sc) \/ sh (sc_beg sc) + sc_msize sc / 8 <= a).
    { destruct CI as [CI|CI]; [clear - CI D9 D10 N1 RN1 SP1; lia|].
      destruct D5 as [D5|D5].
      - right. pose proof (sh_le (sc_beg sc + sc_msize sc) (region AL K_BCLASS + 16 * VN) ltac:(clear - D5 N1 RN1; lia)) as SL. rewrite D8 in SL. clear - SL CI. lia.
      - left. pose proof (sh_le (region AL K_BCLASS + 16 * VN + 8192) (sc_beg sc) ltac:(clear - D5 N2 N3 RN2; lia)) as SL. rewrite N5 in SL. clear - SL CI. lia. }
    destruct HU as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
    + clear - MB CM1. lia.
    + rewrite SHB, DV. clear - MS CM1 CM2. lia.
    + clear - MB CM1. lia.
    + clear - MS CM1 CM2. Z.div_mod_to_equations. lia.
Qed.

#[using="AO"] Lemma hull_ftouch_dj : forall (lo q : Z) (X : pstate) (m : mem) (glob loc : list qbatch) (ch : qchunk) (hrest : list (Z * Z)) ch' iv A n,
  0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch) -> incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X)) ->
  held_kind X ch' ->
  (forall cv, In cv (prim_of ch') -> ~ In cv (tc_of (glob ++ loc) ++ prim_of ch)) ->
  (forall sc, In sc (sec_of ch') -> ~ In sc (tsc_of (glob ++ loc) ++ sec_of ch)) ->
  (forall cv, In cv (prim_of ch') -> In cv hrest) ->
  (need_batch loc = true -> 0 <= snd (enq_prim (fst X) loc) /\ 16 * snd (enq_prim (fst X) loc) + Q_BBYTES <= FA_OFF) ->
  (need_batch loc = true -> held_ok (fst (enq_prim (fst X) loc)) ((K_BCLASS, snd (enq_prim (fst X) loc)) :: prim_of ch ++ hrest)
                            /\ (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls (fst (enq_prim (fst X) loc)) c))) ->
  ftouch AL q lo X glob loc ch iv ->
  qc_hull AL ch' A n -> disjoint_from [iv] A n.
Proof.
  intros lo q X m glob loc ch hrest ch' iv A n LOH CLO RP RS TCH TSI HK NP NS INH VNG NBX FT HU.
  destruct FT as [AT|[[NB CI]|[DS|[DR|[IA|ZE]]]]].
  - exact (hull_atouch_dj AL X m lo q [iv] _ _ ch' A n AO LOH CLO RP RS TCH TSI ltac:(constructor; [exact AT| constructor]) HK NP NS HU).
  - destruct (VNG NB) as [V0 V1]. destruct (NBX NB) as [HOKN WFN].
    eapply (nb_hull_dj X m _ _ (prim_of ch ++ hrest) ch' iv A n RP RS HK V0 V1 HOKN WFN); [| exact CI| exact HU].
    intros cv Hcv. apply in_or_app. right. exact (INH cv Hcv).
  - exact (hull_dzone_dj AL X m lo [iv] ch' A n AO LOH CLO RP RS HK ltac:(constructor; [right; left; exact DS| constructor]) HU).
  - exact (hull_dzone_dj AL X m lo [iv] ch' A n AO LOH CLO RP RS HK ltac:(constructor; [right; right; exact DR| constructor]) HU).
  - exact (hull_izone_dj AL X m lo [iv] ch' A n AO LOH CLO RP RS HK ltac:(constructor; [right; left; exact IA| constructor]) HU).
  - exact (hull_izone_dj AL X m lo [iv] ch' A n AO LOH CLO RP RS HK ltac:(constructor; [right; right; exact ZE| constructor]) HU).
Qed.

#[using="AO"] Lemma hull_lo : forall (X : pstate) (m : mem) ch' A n, RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch' -> qc_hull AL ch' A n -> 6328320 <= A.
Proof.
  intros X m ch' A n RP RS HK HU. destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  destruct (pchunk_geo AL X m ch' AO RP RS HK) as (_ & _ & _ & GLO & _).
  destruct ch' as [[c v|sc] rz n0]; unfold held_kind in HK; cbn [qc_kind] in HK; unfold qc_hull, qc_blk, qc_bsize in HU, GLO; cbn [qc_kind] in HU, GLO.
  - pose proof (held_geo AL (fst X) AO WF0 c v HK) as G. cbv zeta in G. destruct G as (_ & _ & _ & _ & _ & _ & G6 & _).
    destruct HU as [[-> ->]|[[-> ->]|[]]]; lia.
  - pose proof (sec_geo AL (snd X) SOK sc HK) as (D1 & _ & _ & _ & _ & _ & _ & _ & D9 & _).
    pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. destruct CK as (CK1 & _).
    assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
    destruct HU as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; lia.
Qed.

#[using="AO"] Lemma live_other_frame : forall (lo q : Z) (X : pstate) (m m' : mem) (glob loc : list qbatch) (ch : qchunk) (hrest : list (Z * Z)) W ch',
  0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch) -> incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X)) ->
  held_kind X ch' -> qchunk_wf ch' ->
  (forall cv, In cv (prim_of ch') -> ~ In cv (tc_of (glob ++ loc) ++ prim_of ch)) ->
  (forall sc, In sc (sec_of ch') -> ~ In sc (tsc_of (glob ++ loc) ++ sec_of ch)) ->
  (forall cv, In cv (prim_of ch') -> In cv hrest) ->
  (need_batch loc = true -> 0 <= snd (enq_prim (fst X) loc) /\ 16 * snd (enq_prim (fst X) loc) + Q_BBYTES <= FA_OFF) ->
  (need_batch loc = true -> held_ok (fst (enq_prim (fst X) loc)) ((K_BCLASS, snd (enq_prim (fst X) loc)) :: prim_of ch ++ hrest)
                            /\ (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls (fst (enq_prim (fst X) loc)) c))) ->
  munch ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W) m m' -> Forall (ftouch AL q lo X glob loc ch) W ->
  lchunk_rep AL m ch' -> lchunk_rep AL m' ch'.
Proof.
  intros lo q X m m' glob loc ch hrest W ch' LOH CLO RP RS TCH TSI HK WF NP NS INH VNG NBX MU FW R.
  eapply (lchunk_rep_hull AL X _ m m' ch' AO RP RS HK R WF MU). clear MU R. intros A n HU.
  pose proof (hull_lo X m ch' A n RP RS HK HU) as HL.
  cbn [disjoint_from]. split; [right; clear - HL; lia|]. split; [right; clear - HL; lia|].
  split. { pose proof (hull_tq_dj AL X m ch' A n AO RP RS HK HU) as DT. cbn [disjoint_from] in DT. exact (proj1 DT). }
  induction FW as [|iv W' FT FW' IH]; [exact I|].
  pose proof (hull_ftouch_dj lo q X m glob loc ch hrest ch' iv A n LOH CLO RP RS TCH TSI HK NP NS INH VNG NBX FT HU) as DI.
  destruct iv as [a b]. cbn [disjoint_from] in DI |- *. split; [exact (proj1 DI)| apply IH].
Qed.

#[using="AO"] Lemma ftouch_above : forall (lo q : Z) (X : pstate) (m : mem) (glob loc : list qbatch) (ch : qchunk) W A k,
  0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch) -> incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X)) ->
  (need_batch loc = true -> 0 <= snd (enq_prim (fst X) loc) /\ 16 * snd (enq_prim (fst X) loc) + Q_BBYTES <= FA_OFF) ->
  Forall (ftouch AL q lo X glob loc ch) W -> q <= A ->
  disjoint_from ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W) A k.
Proof.
  intros lo q X m glob loc ch W A k LOH CLO LQ RP RS TCH TSI VNG FW HA.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
  cbn [disjoint_from]. split; [clear - HA LOH LQ; lia|]. split; [clear - HA LOH LQ; lia|]. split; [clear - HA T3 T4 CLO LQ; lia|].
  induction FW as [|[a b] W' HIV FW' IH]; cbn [disjoint_from]; [exact I|]. split; [| exact IH].
  destruct HIV as [AT|[[NB CI]|[DS|[DR|[IA|ZE]]]]].
  - pose proof (atouch_above AL X m lo q [(a, b)] _ _ A k AO LOH CLO LQ RP RS TCH TSI ltac:(constructor; [exact AT| constructor]) HA) as DD.
    cbn [disjoint_from] in DD. exact (proj1 DD).
  - destruct (VNG NB) as [V0 V1]. pose proof (region_range AL K_BCLASS ltac:(lia)) as [RN1 RN2].
    assert (RG : region AL K_BCLASS = al_space AL + K_BCLASS * K_REGION) by reflexivity. change Q_BBYTES with 8192 in V1.
    destruct CI as [CI|CI]; unfold chunk_iv, chunk_sh_iv in CI; cbn [fst snd] in CI; change (class_size K_BCLASS) with 8192 in CI.
    + clear - CI V0 V1 RN1 RN2 RG SP1 SP2 SP5 HA CLO LQ. lia.
    + assert (BBR : 0 <= region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc) /\ region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc) + 8192 <= 2^47)
        by (clear - V0 V1 RN1 RN2 RG SP1 SP5; lia).
      change (8192 / 8) with 1024 in CI. unfold sh, SHADOW_OFF in CI. clear - CI BBR HA LOH LQ. Z.div_mod_to_equations. lia.
  - unfold dstat in DS. cbn [fst snd] in DS. clear - DS HA LOH LQ. lia.
  - unfold dreg in DR. cbn [fst snd] in DR. clear - DR HA N2d S2d CLO LQ. lia.
  - unfold iastat in IA. cbn [fst snd] in IA. clear - IA HA LOH LQ. lia.
  - inversion ZE; subst a b. clear - HA T4 CLO LQ. lia.
Qed.

#[using="AO"] Lemma atouch_img_lo_dj : forall X (m : mem) lo q W tc tsc A n,
  0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  Forall (atouch AL lo q (fst X) (snd X) tc tsc) W -> 65536 <= A -> A + n <= SEC -> disjoint_from W A n.
Proof.
  intros X m lo q W tc tsc A n LOH CLO RP RS TCH TSI FW QA QN.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _).
  assert (RGE : forall c0, region AL c0 = al_space AL + c0 * K_REGION) by reflexivity.
  assert (SHL : forall x, 0 <= x -> 2147450880 <= sh x) by (intros x Hx; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros iv AT. unfold atouch, sub_iv in AT.
  destruct AT as [AT|[AT|[AT|[AT|[AT|[AT|[AT|AT]]]]]]].
  - left. clear - AT QN LOH. lia.
  - left. clear - AT QN. lia.
  - clear - AT QA QN T3. lia.
  - destruct AT as (c0 & Hc0 & [AT|[AT|AT]]).
    + left. unfold ri_addr, RIB in AT. clear - AT QN SP1 Hc0. lia.
    + left. pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & _). rewrite !RGE in *. clear - AT QN SP1 Hc0 K1. lia.
    + left. pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & _).
      pose proof (SHL (region AL c0 + p_au (get_cls (fst X) c0)) ltac:(rewrite RGE; clear - SP1 Hc0 K1; lia)) as SHX. clear - AT QN SHX. lia.
  - destruct AT as ([c1 v1] & Hin & AT). cbn [fst snd] in AT.
    pose proof (proj1 (Forall_forall _ _) TCH _ Hin) as HE1. pose proof (held_geo AL (fst X) AO WF0 c1 v1 HE1) as G'. cbv zeta in G'.
    destruct G' as (Hc1 & H1 & H2 & H3 & CS1 & H5 & H6 & H7). pose proof (region_range AL c1 Hc1) as [Q1 Q2]. rewrite RGE in *.
    left. unfold chunk_iv, chunk_sh_iv in AT. rewrite RGE in AT. destruct AT as [AT|AT]; [clear - AT QN H1 SP1 Hc1; lia| clear - AT QN H6; lia].
  - destruct AT as (sc & Hin & AT). pose proof (sec_geo AL (snd X) SOK sc (TSI sc Hin)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
    left. destruct AT as [AT|AT]; [clear - AT QN D1; lia| clear - AT QN D9; lia].
  - destruct AT as (d & Hin & AT). pose proof (sec_geo AL (snd X) SOK d Hin) as (D1 & _). left. clear - AT QN D1. lia.
  - clear - AT QA QN P1. lia.
Qed.

#[using="AO"] Lemma ftouch_img_dj : forall (lo q : Z) (X : pstate) (m : mem) (glob loc : list qbatch) (ch : qchunk) W A k,
  0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch) -> incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X)) ->
  (need_batch loc = true -> 0 <= snd (enq_prim (fst X) loc) /\ 16 * snd (enq_prim (fst X) loc) + Q_BBYTES <= FA_OFF) ->
  Forall (ftouch AL q lo X glob loc ch) W ->
  (65536 <= A /\ A + k <= SEC) \/ (GSTATS_A + 16 <= A /\ A + k <= QUAR_MTX) \/ (QUAR_GQ + 32 <= A /\ A + k <= 743232)
  \/ (1271664 <= A /\ A + k <= 1327048) \/ (1327052 <= A /\ A + k <= 1598472) \/ (5858360 <= A /\ A + k <= 6328320) ->
  disjoint_from ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W) A k.
Proof.
  intros lo q X m glob loc ch W A k LOH CLO RP RS TCH TSI VNG FW HA.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
  assert (IMG : 65536 <= A /\ A + k <= 6328320) by (clear - HA; lia).
  cbn [disjoint_from]. split; [clear - HA; lia|]. split; [clear - HA; lia|]. split; [clear - IMG T3; lia|].
  induction FW as [|[a b] W' HIV FW' IH]; cbn [disjoint_from]; [exact I|]. split; [| exact IH].
  destruct HIV as [AT|[[NB CI]|[DS|[DR|[IA|ZE]]]]].
  - assert (CASE : (65536 <= A /\ A + k <= SEC) \/ (GSTATS_A + 16 <= A /\ A + k <= 6328320)) by (clear - HA; lia).
    destruct CASE as [[C1 C2]|[C1 C2]].
    + pose proof (atouch_img_lo_dj X m lo q [(a, b)] _ _ A k LOH CLO RP RS TCH TSI ltac:(constructor; [exact AT| constructor]) C1 C2) as DD. cbn [disjoint_from] in DD. exact (proj1 DD).
    + pose proof (atouch_img_dj AL X m lo q [(a, b)] _ _ A k AO LOH CLO RP RS TCH TSI ltac:(constructor; [exact AT| constructor]) C1 C2) as DD. cbn [disjoint_from] in DD. exact (proj1 DD).
  - destruct (VNG NB) as [V0 V1]. pose proof (region_range AL K_BCLASS ltac:(lia)) as [RN1 RN2].
    assert (RG : region AL K_BCLASS = al_space AL + K_BCLASS * K_REGION) by reflexivity. change Q_BBYTES with 8192 in V1.
    destruct CI as [CI|CI]; unfold chunk_iv, chunk_sh_iv in CI; cbn [fst snd] in CI; change (class_size K_BCLASS) with 8192 in CI.
    + clear - CI V0 V1 RN1 RN2 RG SP1 IMG. lia.
    + assert (BBR : 0 <= region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc)) by (clear - V0 RN1 RG SP1; lia).
      change (8192 / 8) with 1024 in CI. unfold sh, SHADOW_OFF in CI. clear - CI BBR IMG. Z.div_mod_to_equations. lia.
  - unfold dstat in DS. cbn [fst snd] in DS. clear - DS HA. lia.
  - unfold dreg in DR. cbn [fst snd] in DR. clear - DR IMG N1d S1d. lia.
  - unfold iastat in IA. cbn [fst snd] in IA. clear - IA HA. lia.
  - inversion ZE; subst a b. clear - IMG T3. lia.
Qed.

End FF.
