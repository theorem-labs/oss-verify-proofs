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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc APrimCover ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A F_sec_B F_quar_P AQuarT AQuarU F_gct F_depot F_depot_C F_quar_C F_prim_L0 F_hooks F_dealloc
                        F_ialloc F_unwind F_stacktrace F_free_icpt F_free_null ALedger AHeap2 AFreeF AFreeZ AFsEnv AFteF.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section AF.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation THR := (at_thr (al_thread AL)).
Hypothesis AO : alayout_ok AL.

#[using="AO"] Lemma fresh_hull_dj : forall (X : pstate) (m : mem) (PN : prim) (c v : Z) hs ch' iv A n,
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch' ->
  held_ok PN ((c, v) :: hs) -> (forall c0, 1 <= c0 <= 31 -> pclass_wf c0 (get_cls PN c0)) ->
  (forall cv, In cv (prim_of ch') -> In cv hs) ->
  chunk_iv AL c v iv \/ chunk_sh_iv AL c v iv ->
  qc_hull AL ch' A n -> disjoint_from [iv] A n.
Proof.
  intros X m PN c v hs ch' [a b] A n RP RS HK [ND FH] WFN INH CI HU.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  apply NoDup_cons_iff in ND as [NI _]. apply Forall_cons_iff in FH as [HN FH].
  pose proof (held_geo AL PN AO WFN c v HN) as GN. cbv zeta in GN. destruct GN as (HcN & N1 & N2 & N3 & CSN & N5 & N6 & N7). rewrite N5 in N7.
  pose proof (region_range AL c HcN) as [RN1 RN2].
  unfold chunk_iv, chunk_sh_iv in CI. cbn [fst snd] in CI.
  cbn [disjoint_from]. split; [| exact I].
  destruct ch' as [[c' v'|sc] rz n0]; unfold held_kind in HK; cbn [qc_kind] in HK; unfold qc_hull, qc_blk, qc_bsize in HU; cbn [qc_kind prim_of] in HU, INH.
  - assert (HP : held1 PN (c', v')) by (apply (proj1 (Forall_forall _ _) FH); apply INH; left; reflexivity).
    assert (NE : (c, v) <> (c', v')) by (intros EQ; apply NI; rewrite EQ; apply INH; left; reflexivity).
    destruct (held_pair_apart AL PN c v c' v' AO WFN HN HP NE) as [PB PS]. cbv zeta in PB, PS.
    pose proof (held_geo AL PN AO WFN c' v' HP) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CS & G5 & G6 & G7). rewrite G5 in G7.
    pose proof (region_range AL c' Hc) as [RR1 RR2].
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
      - right. pose proof (sh_le (sc_beg sc + sc_msize sc) (region AL c + 16 * v) ltac:(clear - D5 N1 RN1; lia)) as SL. rewrite D8 in SL. clear - SL CI. lia.
      - left. pose proof (sh_le (region AL c + 16 * v + class_size c) (sc_beg sc) ltac:(clear - D5 N2 N3 RN2; lia)) as SL. rewrite N5 in SL. clear - SL CI. lia. }
    destruct HU as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
    + clear - MB CM1. lia.
    + rewrite SHB, DV. clear - MS CM1 CM2. lia.
    + clear - MB CM1. lia.
    + clear - MS CM1 CM2. Z.div_mod_to_equations. lia.
Qed.

#[using="HC AO"] Lemma fresh_czone : forall (PN : prim) (c v lo q : Z) (S0 : asec) iv,
  held1 PN (c, v) -> (forall c0, 1 <= c0 <= 31 -> pclass_wf c0 (get_cls PN c0)) ->
  chunk_iv AL c v iv \/ chunk_sh_iv AL c v iv -> czone AL lo q S0 iv.
Proof.
  intros PN c v lo q S0 [a b] HN WFN CI.
  pose proof (held_geo AL PN AO WFN c v HN) as GN. cbv zeta in GN. destruct GN as (HcN & N1 & N2 & N3 & CSN & N5 & N6 & N7).
  pose proof (region_range AL c HcN) as [RN1 RN2].
  unfold chunk_iv, chunk_sh_iv in CI. cbn [fst snd] in CI. unfold czone, sub_iv. cbn [fst snd]. destruct CI as [CI|CI].
  - do 4 right. left. clear - CI N1 N2 N3 RN1 RN2. lia.
  - do 5 right. left. rewrite <- N5 in CI.
    pose proof (sh_le (al_space AL) (region AL c + 16 * v) ltac:(clear - N1 RN1; lia)) as S1.
    pose proof (sh_le (region AL c + 16 * v + class_size c) (al_space AL + K_SPACE) ltac:(clear - N2 N3 RN2; lia)) as S2.
    clear - CI S1 S2. lia.
Qed.

Definition mtouch (lo q : Z) (X : pstate) (c v : Z) (iv : Z * Z) : Prop :=
  atouch AL lo q (fst X) (snd X) [] [] iv
  \/ chunk_iv AL c v iv \/ chunk_sh_iv AL c v iv \/ dstat iv \/ dreg AL iv \/ iastat iv \/ iv = (THR + 3168, THR + 3169).

#[using="AO"] Lemma hull_mtouch_dj : forall (lo q : Z) (X : pstate) (m : mem) (PN : prim) (c v : Z) hs ch' iv A n,
  0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch' ->
  held_ok PN ((c, v) :: hs) -> (forall c0, 1 <= c0 <= 31 -> pclass_wf c0 (get_cls PN c0)) ->
  (forall cv, In cv (prim_of ch') -> In cv hs) ->
  mtouch lo q X c v iv -> qc_hull AL ch' A n -> disjoint_from [iv] A n.
Proof.
  intros lo q X m PN c v hs ch' iv A n LOH CLO RP RS HK HON WFN INH MT HU.
  destruct MT as [AT|[CI|[CI|[DS|[DR|[IA|ZE]]]]]].
  - exact (hull_atouch_dj AL X m lo q [iv] [] [] ch' A n AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) ltac:(constructor; [exact AT| constructor]) HK
             ltac:(intros cv _ []) ltac:(intros sc _ []) HU).
  - exact (fresh_hull_dj X m PN c v hs ch' iv A n RP RS HK HON WFN INH (or_introl CI) HU).
  - exact (fresh_hull_dj X m PN c v hs ch' iv A n RP RS HK HON WFN INH (or_intror CI) HU).
  - exact (hull_dzone_dj AL X m lo [iv] ch' A n AO LOH CLO RP RS HK ltac:(constructor; [right; left; exact DS| constructor]) HU).
  - exact (hull_dzone_dj AL X m lo [iv] ch' A n AO LOH CLO RP RS HK ltac:(constructor; [right; right; exact DR| constructor]) HU).
  - exact (hull_izone_dj AL X m lo [iv] ch' A n AO LOH CLO RP RS HK ltac:(constructor; [right; left; exact IA| constructor]) HU).
  - exact (hull_izone_dj AL X m lo [iv] ch' A n AO LOH CLO RP RS HK ltac:(constructor; [right; right; exact ZE| constructor]) HU).
Qed.

#[using="AO"] Lemma mtouch_czone : forall (lo q : Z) (X : pstate) (m : mem) (PN : prim) (c v : Z) iv,
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held1 PN (c, v) -> (forall c0, 1 <= c0 <= 31 -> pclass_wf c0 (get_cls PN c0)) ->
  mtouch lo q X c v iv -> czone AL lo q (snd X) iv.
Proof.
  intros lo q X m PN c v [a b] RP RS HN WFN MT.
  destruct MT as [AT|[CI|[CI|[DS|[DR|[IA|ZE]]]]]].
  - exact (atouch_czone AL AO X m lo q [] [] (a, b) RP RS ltac:(constructor) ltac:(intros d []) AT).
  - exact (fresh_czone PN c v lo q (snd X) (a, b) HN WFN (or_introl CI)).
  - exact (fresh_czone PN c v lo q (snd X) (a, b) HN WFN (or_intror CI)).
  - right; right; left. exact DS.
  - do 8 right. left. exact DR.
  - right; right; right; left. exact IA.
  - inversion ZE; subst a b. do 7 right. left. unfold sub_iv. cbn [fst snd]. clear. lia.
Qed.

#[using="Type"] Lemma qlist_rep_hull : forall W (m m' : mem) l nxt, munch W m m' -> qlist_rep AL m l nxt ->
  Forall (fun b => disjoint_from W (qb_addr AL b) 8192 /\ disjoint_from W (sh (qb_addr AL b)) 1024) l -> qlist_rep AL m' l nxt.
Proof.
  intros W m m' l nxt MU. induction l as [|b l IH]; intros QL FB; [exact I|].
  cbn [qlist_rep] in *. destruct QL as [RB QL]. apply Forall_cons_iff in FB as [(D1 & D2) FB]. split; [| exact (IH QL FB)].
  exact (qbatch_rep_frame_m AL W m m' b _ RB MU D1 D2).
Qed.

Section MT.
Variables (lo q : Z) (X : pstate) (m : mem) (PN : prim) (c v : Z).
Hypothesis LOH : 0x10007fff8000 <= lo.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis RP : RPRIM AL (fst X) m.
Hypothesis RS : RSEC AL (snd X) m.
Hypothesis HN : held1 PN (c, v).
Hypothesis WFN : forall c0, 1 <= c0 <= 31 -> pclass_wf c0 (get_cls PN c0).

#[using="AO PN HN WFN"] Lemma fresh_bounds : let B := region AL c + 16 * v in
  17594333495296 <= B /\ B + class_size c <= alloc_ceiling /\ 2147450880 <= sh B /\ sh B + class_size c / 8 <= 17594333495296
  /\ al_space AL <= B /\ B + class_size c <= al_space AL + K_SPACE.
Proof.
  cbv zeta. pose proof (held_geo AL PN AO WFN c v HN) as GN. cbv zeta in GN. destruct GN as (HcN & N1 & N2 & N3 & CSN & N5 & N6 & N7). rewrite N5 in N7.
  pose proof (region_range AL c HcN) as [RN1 RN2]. layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _).
  repeat split; lia.
Qed.

#[using="HC AO m PN LOH CLO RP RS HN WFN"] Lemma mtouch_above : forall W A k, lo <= q -> Forall (mtouch lo q X c v) W -> q <= A -> disjoint_from W A k.
Proof.
  intros W A k LQ FW HA. destruct fresh_bounds as (B1 & B2 & B3 & B4 & _).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros [a b] MT. cbn [fst snd].
  destruct MT as [AT|[CI|[CI|[DS|[DR|[IA|ZE]]]]]].
  - pose proof (atouch_above AL X m lo q [(a, b)] [] [] A k AO LOH CLO LQ RP RS ltac:(constructor) ltac:(intros d []) ltac:(constructor; [exact AT| constructor]) HA) as DD.
    cbn [disjoint_from] in DD. exact (proj1 DD).
  - unfold chunk_iv in CI. cbn [fst snd] in CI. right. clear - CI B2 CLO LQ HA. lia.
  - unfold chunk_sh_iv in CI. cbn [fst snd] in CI. right. clear - CI B4 LOH LQ HA. lia.
  - unfold dstat in DS. cbn [fst snd] in DS. right. clear - DS HA LOH LQ. lia.
  - unfold dreg in DR. cbn [fst snd] in DR. right. clear - DR HA N2d S2d CLO LQ. lia.
  - unfold iastat in IA. cbn [fst snd] in IA. right. clear - IA HA LOH LQ. lia.
  - inversion ZE; subst a b. right. clear - HA T4 CLO LQ. lia.
Qed.

#[using="HC AO m PN LOH CLO RP RS HN WFN"] Lemma mtouch_img_dj : forall W A k, Forall (mtouch lo q X c v) W ->
  (65536 <= A /\ A + k <= SEC) \/ (GSTATS_A + 16 <= A /\ A + k <= 740096)
  \/ (1268528 <= A /\ A + k <= 1323912) \/ (1323916 <= A /\ A + k <= 1595336) \/ (5855224 <= A /\ A + k <= 6328320) ->
  disjoint_from W A k.
Proof.
  intros W A k FW HA. destruct fresh_bounds as (B1 & B2 & B3 & B4 & _).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
  assert (IMG : 65536 <= A /\ A + k <= 6328320) by (clear - HA; lia).
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros [a b] MT. cbn [fst snd].
  destruct MT as [AT|[CI|[CI|[DS|[DR|[IA|ZE]]]]]].
  - assert (CASE : (65536 <= A /\ A + k <= SEC) \/ (GSTATS_A + 16 <= A /\ A + k <= 6328320)) by (clear - HA; lia).
    destruct CASE as [[C1 C2]|[C1 C2]].
    + pose proof (atouch_img_lo_dj AL AO X m lo q [(a, b)] [] [] A k LOH CLO RP RS ltac:(constructor) ltac:(intros d []) ltac:(constructor; [exact AT| constructor]) C1 C2) as DD. cbn [disjoint_from] in DD. exact (proj1 DD).
    + pose proof (atouch_img_dj AL X m lo q [(a, b)] [] [] A k AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) ltac:(constructor; [exact AT| constructor]) C1 C2) as DD. cbn [disjoint_from] in DD. exact (proj1 DD).
  - unfold chunk_iv in CI. cbn [fst snd] in CI. left. clear - CI B1 IMG. lia.
  - unfold chunk_sh_iv in CI. cbn [fst snd] in CI. left. clear - CI B3 IMG. lia.
  - unfold dstat in DS. cbn [fst snd] in DS. clear - DS HA. lia.
  - unfold dreg in DR. cbn [fst snd] in DR. clear - DR IMG N1d S1d. lia.
  - unfold iastat in IA. cbn [fst snd] in IA. clear - IA HA. lia.
  - inversion ZE; subst a b. clear - IMG T3. lia.
Qed.

#[using="HC AO m PN LOH CLO RP RS HN WFN"] Lemma mtouch_thr_dj : forall W A k, Forall (mtouch lo q X c v) W ->
  (THR <= A /\ A + k <= THR + TQ_OFF) \/ (at_ctx (al_thread AL) <= A /\ A + k <= at_ctx (al_thread AL) + 4096)
  \/ (THR + TQ_OFF <= A /\ A + k <= THR + TQ_OFF + 32) -> disjoint_from W A k.
Proof.
  intros W A k FW HA. destruct fresh_bounds as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  layout_facts AO 2%nat LF2. destruct LF2 as ((PL2 & _) & CE2 & _). layout_facts AO 3%nat LF3. destruct LF3 as ((PL3 & _) & CE3 & _).
  layout_apart_fact AO 2%nat 3%nat AP23.
  assert (PG : exists base, base <= A /\ A + k <= base + 4096
                 /\ ((0 < base /\ base + 4096 <= 0x10000) \/ (6328320 <= base /\ base + 4096 <= 0x7fff7000) \/ 0x10007fff8000 <= base)
                 /\ base + 4096 <= alloc_ceiling
                 /\ (al_space AL + (K_SPACE + 4096) <= base \/ base + 4096 <= al_space AL)
                 /\ (DN0 (al_depot AL) + 2^20 <= base \/ base + 4096 <= DN0 (al_depot AL)) /\ (SS0 (al_depot AL) + 2^23 <= base \/ base + 4096 <= SS0 (al_depot AL))
                 /\ (A + k <= THR + 3168 \/ THR + 3169 <= A)).
  { layout_apart_fact AO 0%nat 2%nat AP02. layout_apart_fact AO 0%nat 3%nat AP03.
    layout_apart_fact AO 2%nat 5%nat AP25. layout_apart_fact AO 2%nat 6%nat AP26. layout_apart_fact AO 3%nat 5%nat AP35. layout_apart_fact AO 3%nat 6%nat AP36.
    assert (HA2 : (THR <= A /\ A + k <= THR + 112) \/ (at_ctx (al_thread AL) <= A /\ A + k <= at_ctx (al_thread AL) + 4096)) by (clear - HA; lia).
    destruct HA2 as [HA2|HA2]; [exists THR| exists (at_ctx (al_thread AL))].
    - split; [clear - HA2; lia|]. split; [clear - HA2; lia|]. split; [exact PL3|]. split; [exact CE3|].
      split; [clear - AP03; lia|]. split; [clear - AP35; lia|]. split; [clear - AP36; lia|]. left; clear - HA2; lia.
    - split; [clear - HA2; lia|]. split; [clear - HA2; lia|]. split; [exact PL2|]. split; [exact CE2|].
      split; [clear - AP02; lia|]. split; [clear - AP25; lia|]. split; [clear - AP26; lia|]. clear - HA2 AP23; lia. }
  destruct PG as (base & P1 & P2 & BPL & BCE & BSP & BDN & BSS & BZE).
  assert (IMG : A + k <= 0x10000 \/ 6328320 <= A) by (clear - P1 P2 BPL; lia).
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros [a b] MT. cbn [fst snd].
  destruct MT as [AT|[CI|[CI|[DS|[DR|[IA|ZE]]]]]].
  - assert (FA1 : Forall (atouch AL lo q (fst X) (snd X) [] []) [(a, b)]) by (constructor; [exact AT| constructor]).
    destruct HA as [HA|[HA|HA]].
    + pose proof (atouch_thr_dj AL X m lo q [(a, b)] [] [] A k AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) FA1 (or_introl HA)) as DD. cbn [disjoint_from] in DD. exact (proj1 DD).
    + pose proof (atouch_thr_dj AL X m lo q [(a, b)] [] [] A k AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) FA1 (or_intror HA)) as DD. cbn [disjoint_from] in DD. exact (proj1 DD).
    + pose proof (atouch_tq_dj AL X m lo q [(a, b)] [] [] A k AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) FA1 (proj1 HA) (proj2 HA)) as DD. cbn [disjoint_from] in DD. exact (proj1 DD).
  - unfold chunk_iv in CI. cbn [fst snd] in CI. clear - CI B5 B6 BSP P1 P2. lia.
  - unfold chunk_sh_iv in CI. cbn [fst snd] in CI. clear - CI B3 B4 BPL P1 P2. lia.
  - unfold dstat in DS. cbn [fst snd] in DS. clear - DS IMG. lia.
  - unfold dreg in DR. cbn [fst snd] in DR. destruct DR as [DR|DR]; [clear - DR BDN P1 P2; lia| clear - DR BSS P1 P2; lia].
  - unfold iastat in IA. cbn [fst snd] in IA. clear - IA IMG. lia.
  - inversion ZE; subst a b. clear - BZE. lia.
Qed.

#[using="HC AO m PN LOH CLO RP RS HN WFN"] Lemma mtouch_fte : forall W, Forall (mtouch lo q X c v) W -> fte_apart THR A0_DTV A0_TLSB (al_dtls AL) W.
Proof.
  intros W FW. unfold fte_apart.
  pose proof (fun A k HA => mtouch_img_dj W A k FW HA) as IMG.
  split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|].
  split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|].
  split.
  { destruct (clear_ctx AL X m RP RS) as (_ & SOK & _).
    apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros iv MT.
    pose proof (czone_dtls_dj AL AO lo q (snd X) CLO SOK iv (mtouch_czone lo q X m PN c v iv RP RS HN WFN MT)) as DJ. lia. }
  exact (mtouch_thr_dj W (THR + 48) 16 FW ltac:(left; clear; lia)).
Qed.
End MT.

End AF.
