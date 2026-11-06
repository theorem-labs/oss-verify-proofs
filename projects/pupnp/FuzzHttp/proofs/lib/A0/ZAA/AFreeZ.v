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
                        F_ialloc F_unwind F_stacktrace F_free_icpt F_free_null F_alloc_env AHeap2 AFreeF AFsEnv AFteF.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section FZ.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation D := (al_depot AL).
Notation THR := (at_thr (al_thread AL)).
Notation TQ := (at_thr (al_thread AL) + TQ_OFF).
Hypothesis AO : alayout_ok AL.

Definition czone (lo q : Z) (S0 : asec) (iv : Z * Z) : Prop :=
  sub_iv lo q iv
  \/ sub_iv SEC (QUAR_GQ + 32) iv \/ dstat iv \/ iastat iv
  \/ sub_iv (al_space AL) (al_space AL + (K_SPACE + 4096)) iv
  \/ sub_iv (sh (al_space AL)) (sh (al_space AL + K_SPACE)) iv
  \/ sub_iv (al_parr AL) (al_parr AL + 2^23) iv
  \/ sub_iv THR (THR + 4096) iv
  \/ dreg AL iv
  \/ (exists sc, In sc (se_chunks S0) /\ (sub_iv (sc_beg sc) (sc_beg sc + sc_msize sc) iv \/ sub_iv (sh (sc_beg sc)) (sh (sc_beg sc) + sc_msize sc / 8) iv)).

#[using="AO"] Lemma atouch_czone : forall X (m : mem) lo q tc tsc iv,
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  atouch AL lo q (fst X) (snd X) tc tsc iv -> czone lo q (snd X) iv.
Proof.
  intros X m lo q tc tsc [a b] RP RS TCH TSI AT.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  assert (RGE : forall c0, region AL c0 = al_space AL + c0 * K_REGION) by reflexivity.
  unfold atouch, sub_iv in AT. unfold czone, sub_iv. cbn [fst snd] in *.
  destruct AT as [AT|[AT|[AT|[AT|[AT|[AT|[AT|AT]]]]]]].
  - left. exact AT.
  - right; left. clear - AT. lia.
  - do 7 right. left. clear - AT. lia.
  - destruct AT as (c0 & Hc0 & [AT|[AT|AT]]).
    + do 4 right. left. unfold ri_addr, RIB in AT. clear - AT Hc0. lia.
    + do 4 right. left. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & _). rewrite !RGE in AT. clear - AT Hc0 K1. lia.
    + do 5 right. left. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & _). rewrite !RGE in AT.
      pose proof (sh_le (al_space AL) (al_space AL + c0 * K_REGION + p_au (get_cls (fst X) c0)) ltac:(clear - Hc0 K1; lia)) as S1.
      pose proof (sh_le (al_space AL + (c0 + 1) * K_REGION) (al_space AL + K_SPACE) ltac:(clear - Hc0; lia)) as S2.
      clear - AT S1 S2. lia.
  - destruct AT as ([c1 v1] & Hin & AT). cbn [fst snd] in AT.
    pose proof (proj1 (Forall_forall _ _) TCH _ Hin) as HE1. pose proof (held_geo AL (fst X) AO WF0 c1 v1 HE1) as G'. cbv zeta in G'.
    destruct G' as (Hc1 & H1 & H2 & H3 & CS1 & H5 & H6 & H7). pose proof (region_range AL c1 Hc1) as [Q1 Q2].
    unfold chunk_iv, chunk_sh_iv in AT. cbn [fst snd] in AT. destruct AT as [AT|AT].
    + do 4 right. left. clear - AT H1 H2 H3 Q1 Q2. lia.
    + do 5 right. left. rewrite <- H5 in AT.
      pose proof (sh_le (al_space AL) (region AL c1 + 16 * v1) ltac:(clear - H1 Q1; lia)) as S1.
      pose proof (sh_le (region AL c1 + 16 * v1 + class_size c1) (al_space AL + K_SPACE) ltac:(clear - H2 H3 Q2; lia)) as S2.
      clear - AT S1 S2. lia.
  - destruct AT as (sc & Hin & AT). do 9 right. exists sc. split; [exact (TSI sc Hin)| exact AT].
  - destruct AT as (d & Hin & AT). do 9 right. exists d. split; [exact Hin|]. left.
    pose proof (sec_geo AL (snd X) SOK d Hin) as (_ & D2 & _). clear - AT D2. lia.
  - do 6 right. left. exact AT.
Qed.

#[using="AO"] Lemma ftouch_czone : forall (lo q : Z) (X : pstate) (m : mem) (glob loc : list qbatch) (ch : qchunk) iv,
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch) -> incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X)) ->
  (need_batch loc = true -> 0 <= snd (enq_prim (fst X) loc) /\ 16 * snd (enq_prim (fst X) loc) + Q_BBYTES <= FA_OFF) ->
  ftouch AL q lo X glob loc ch iv -> czone lo q (snd X) iv.
Proof.
  intros lo q X m glob loc ch [a b] RP RS TCH TSI VNG FT.
  destruct FT as [AT|[[NB CI]|[DS|[DR|[IA|ZE]]]]].
  - exact (atouch_czone X m lo q _ _ (a, b) RP RS TCH TSI AT).
  - destruct (VNG NB) as [V0 V1]. pose proof (region_range AL K_BCLASS ltac:(lia)) as [RN1 RN2]. change Q_BBYTES with 8192 in V1.
    unfold chunk_iv, chunk_sh_iv in CI; cbn [fst snd] in CI; change (class_size K_BCLASS) with 8192 in CI. change (8192 / 8) with 1024 in CI.
    unfold czone, sub_iv. cbn [fst snd]. destruct CI as [CI|CI].
    + do 4 right. left. clear - CI V0 V1 RN1 RN2. lia.
    + do 5 right. left.
      pose proof (sh_le (al_space AL) (region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc)) ltac:(clear - V0 RN1; lia)) as S1.
      pose proof (sh_le (region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc) + 8192) (al_space AL + K_SPACE) ltac:(clear - V1 RN2; lia)) as S2.
      assert (S3 : sh (region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc) + 8192) = sh (region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc)) + 1024).
      { layout_facts AO 0%nat SPF. destruct SPF as (_ & _ & SPM & _). assert (RG : region AL K_BCLASS = al_space AL + K_BCLASS * K_REGION) by reflexivity.
        unfold sh. rewrite RG. clear - SPM. Z.div_mod_to_equations. lia. }
      clear - CI S1 S2 S3. lia.
  - right; right; left. exact DS.
  - do 8 right. left. exact DR.
  - right; right; right; left. exact IA.
  - inversion ZE; subst a b. do 7 right. left. unfold sub_iv. cbn [fst snd]. clear. lia.
Qed.

#[using="AO"] Lemma ficpt_W_czone : forall (lo q : Z) (X : pstate) (m : mem) (glob loc : list qbatch) (ch : qchunk) W,
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch) -> incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X)) ->
  (need_batch loc = true -> 0 <= snd (enq_prim (fst X) loc) /\ 16 * snd (enq_prim (fst X) loc) + Q_BBYTES <= FA_OFF) ->
  Forall (ftouch AL q lo X glob loc ch) W ->
  Forall (czone lo q (snd X)) ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W).
Proof.
  intros lo q X m glob loc ch W RP RS TCH TSI VNG FW.
  constructor; [right; left; unfold sub_iv; cbn [fst snd]; lia|]. constructor; [right; left; unfold sub_iv; cbn [fst snd]; lia|].
  constructor; [do 7 right; left; unfold sub_iv; cbn [fst snd]; lia|].
  eapply Forall_impl; [| exact FW]. intros iv FT. exact (ftouch_czone lo q X m glob loc ch iv RP RS TCH TSI VNG FT).
Qed.

Section MISS.
Variables (lo q : Z) (S0 : asec).
Hypothesis LOH : 0x10007fff8000 <= lo.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis SOK : Forall (chunk_ok AL) (se_chunks S0).

#[using="HC AO LOH SOK"] Lemma czone_env_safe : forall W, Forall (czone lo q S0) W -> env_safe W.
Proof.
  intros W FW. unfold env_safe. eapply Forall_impl; [| exact FW]. intros [a b] CZ. cbn [fst snd].
  unfold czone, sub_iv, dstat, iastat, dreg in CZ. cbn [fst snd] in CZ.
  destruct CZ as [CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|CZ]]]]]]]]].
  - left. clear - CZ LOH. lia.
  - do 11 right. left. clear - CZ. lia.
  - do 12 right. left. clear - CZ. lia.
  - destruct CZ as [CZ|CZ]; [do 13 right; left; clear - CZ; lia| do 14 right; clear - CZ; lia].
  - layout_facts AO 0%nat SPF. destruct SPF as (SP1 & _). left. clear - CZ SP1. lia.
  - layout_facts AO 0%nat SPF. destruct SPF as (SP1 & _). left. unfold sh, SHADOW_OFF in CZ. clear - CZ SP1. Z.div_mod_to_equations. lia.
  - layout_facts AO 1%nat LF. destruct LF as (_ & _ & _ & PL & _). clear - CZ PL. lia.
  - layout_facts AO 3%nat LF. destruct LF as (_ & _ & _ & PL & _). clear - CZ PL. lia.
  - layout_facts AO 5%nat LF5. destruct LF5 as (_ & _ & _ & PL5 & _). layout_facts AO 6%nat LF6. destruct LF6 as (_ & _ & _ & PL6 & _).
    destruct CZ as [CZ|CZ]; [clear - CZ PL5; lia| clear - CZ PL6; lia].
  - destruct CZ as (sc & Hin & CZ). pose proof (sec_geo AL S0 SOK sc Hin) as (D1 & _ & _ & _ & _ & _ & _ & _ & D9 & _).
    left. destruct CZ as [CZ|CZ]; [clear - CZ D1; lia| clear - CZ D9; lia].
Qed.

#[using="HC AO LOH CLO SOK"] Lemma czone_fs_dj : forall iv, czone lo q S0 iv ->
  (snd iv <= al_fsb AL \/ al_fsb AL + A0_FS_SIZE <= fst iv) /\ (snd iv <= sh (al_fsb AL) \/ sh (al_fsb AL) + A0_FS_SHSIZE <= fst iv).
Proof.
  intros [a b] CZ. cbn [fst snd].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  layout_facts AO 4%nat LF4. destruct LF4 as ((FPL & _) & FCE & FMOD & _).
  assert (FSH : sh (al_fsb AL) + A0_FS_SHSIZE = sh (al_fsb AL + A0_FS_SIZE)) by (unfold sh; clear - FMOD; Z.div_mod_to_equations; lia).
  assert (FS1 : 2147450880 <= sh (al_fsb AL) /\ sh (al_fsb AL + A0_FS_SIZE) <= 17594333495296 /\ 0x800b9200 <= sh (al_fsb AL))
    by (unfold sh, SHADOW_OFF; clear - FPL FCE ACR; Z.div_mod_to_equations; lia).
  assert (FPL' : (6328320 <= al_fsb AL /\ al_fsb AL + A0_FS_SIZE <= 0x7fff7000) \/ 0x10007fff8000 <= al_fsb AL) by (clear - FPL; lia).
  clear FPL. rewrite FSH. clear FSH.
  unfold czone, sub_iv, dstat, iastat, dreg in CZ. cbn [fst snd] in CZ.
  destruct CZ as [CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|CZ]]]]]]]]].
  - split; right; clear - CZ LOH CLO FCE FS1; lia.
  - split; left; clear - CZ FPL' FS1; lia.
  - split; left; clear - CZ FPL' FS1; lia.
  - split; left; clear - CZ FPL' FS1; lia.
  - layout_facts AO 0%nat SPF. destruct SPF as (SP1 & _). layout_apart_fact AO 0%nat 4%nat AP.
    split; [clear - CZ AP; lia| right; clear - CZ SP1 FS1; lia].
  - layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _). layout_apart_fact AO 0%nat 4%nat AP.
    assert (SS : 2147450880 + 2199023255552 <= sh (al_space AL) /\ sh (al_space AL + K_SPACE) <= 17594333495296)
      by (unfold sh, SHADOW_OFF; clear - SP1 SP2 ACR; Z.div_mod_to_equations; lia).
    split; [clear - CZ SS FPL' FCE ACR; lia|].
    destruct AP as [AP|AP].
    + left. pose proof (sh_le (al_space AL + K_SPACE) (al_fsb AL) ltac:(clear - AP; lia)) as S1. clear - CZ S1. lia.
    + right. pose proof (sh_le (al_fsb AL + A0_FS_SIZE) (al_space AL) AP) as S1. clear - CZ S1. lia.
  - layout_facts AO 1%nat LF. destruct LF as ((PL & _) & _). layout_apart_fact AO 1%nat 4%nat AP.
    split; [clear - CZ AP; lia| clear - CZ PL FS1; lia].
  - layout_facts AO 3%nat LF. destruct LF as ((PL & _) & _). layout_apart_fact AO 3%nat 4%nat AP.
    split; [clear - CZ AP; lia| clear - CZ PL FS1; lia].
  - layout_facts AO 5%nat LF5. destruct LF5 as ((PL5 & _) & _). layout_facts AO 6%nat LF6. destruct LF6 as ((PL6 & _) & _).
    layout_apart_fact AO 4%nat 5%nat AP5. layout_apart_fact AO 4%nat 6%nat AP6.
    destruct CZ as [CZ|CZ]; (split; [first [clear - CZ AP5; lia | clear - CZ AP6; lia]| first [clear - CZ PL5 FS1; lia | clear - CZ PL6 FS1; lia]]).
  - destruct CZ as (sc & Hin & CZ). pose proof (sec_geo AL S0 SOK sc Hin) as (D1 & D2 & D3 & D4 & _ & _ & _ & D8 & D9 & D10).
    pose proof (proj1 (Forall_forall _ _) SOK sc Hin) as CK. destruct CK as (_ & _ & _ & _ & _ & _ & CK7).
    pose proof (proj1 (Forall_forall _ _) CK7 (al_fsb AL, A0_FS_SIZE) ltac:(unfold al_regions; cbn [In]; tauto)) as AP. unfold apart in AP. cbn [fst snd] in AP.
    destruct CZ as [CZ|CZ].
    + split; [clear - CZ AP; lia| clear - CZ D4 FS1; lia].
    + rewrite <- D8 in CZ. split; [clear - CZ D9 D10 D8 FPL' FCE ACR; lia|].
      destruct AP as [AP|AP].
      * left. pose proof (sh_le _ _ AP) as S1. clear - CZ S1. lia.
      * right. pose proof (sh_le _ _ AP) as S1. clear - CZ S1. lia.
Qed.

#[using="HC AO CLO SOK"] Lemma czone_dtls_dj : forall iv, czone lo q S0 iv -> snd iv <= al_dtls AL \/ al_dtls AL + 4096 <= fst iv.
Proof.
  intros [a b] CZ. cbn [fst snd].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  layout_facts AO 7%nat LF7. destruct LF7 as ((DPL & _) & DCE & DMOD & _ & D47 & _ & DSH).
  unfold czone, sub_iv, dstat, iastat, dreg in CZ. cbn [fst snd] in CZ.
  destruct CZ as [CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|CZ]]]]]]]]].
  - right; clear - CZ LOH CLO DCE; lia.
  - clear - CZ DPL; lia.
  - clear - CZ DPL; lia.
  - clear - CZ DPL; lia.
  - layout_apart_fact AO 0%nat 7%nat AP. clear - CZ AP; lia.
  - layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _).
    assert (SS : 2147450880 <= sh (al_space AL) /\ sh (al_space AL + K_SPACE) <= 17594333495296)
      by (unfold sh, SHADOW_OFF; clear - SP1 SP2 ACR; Z.div_mod_to_equations; lia).
    clear - CZ SS DPL DCE ACR. lia.
  - layout_apart_fact AO 1%nat 7%nat AP. clear - CZ AP; lia.
  - layout_apart_fact AO 3%nat 7%nat AP. clear - CZ AP; lia.
  - layout_apart_fact AO 5%nat 7%nat AP5. layout_apart_fact AO 6%nat 7%nat AP6.
    destruct CZ as [CZ|CZ]; [clear - CZ AP5; lia| clear - CZ AP6; lia].
  - destruct CZ as (sc & Hin & CZ). pose proof (sec_geo AL S0 SOK sc Hin) as (D1 & D2 & D3 & D4 & _ & _ & _ & D8 & D9 & D10).
    pose proof (proj1 (Forall_forall _ _) SOK sc Hin) as CK. destruct CK as (_ & _ & _ & _ & _ & _ & CK7).
    pose proof (proj1 (Forall_forall _ _) CK7 (al_dtls AL, 4096) ltac:(unfold al_regions; cbn [In]; tauto)) as AP. unfold apart in AP. cbn [fst snd] in AP.
    destruct CZ as [CZ|CZ]; [clear - CZ AP; lia|].
    rewrite <- D8 in CZ. clear - CZ D9 D10 D8 DPL DCE ACR. lia.
Qed.

#[using="Type"] Lemma a0_static_groups : forall lo' hi', a0_static lo' hi' ->
  lo' <= hi' /\ ((0x10000 <= lo' /\ hi' <= SEC) \/ (0x14338c <= lo' /\ hi' <= 0x1857c8) \/ (0x5957f8 <= lo' /\ hi' <= 0x609000)
                 \/ (0x7fffa000 <= lo' /\ hi' <= 0x800b9200) \/ (sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' /\ hi' <= 0x10007fff8000)).
Proof. intros lo' hi' [LE ST]. split; [exact LE|]. clear LE. lia. Qed.

#[using="Type"] Lemma sh_aligned_le : forall e, 0 <= e -> e mod 4096 = 0 -> e <= alloc_ceiling -> sh e <= sh alloc_ceiling - sh alloc_ceiling mod 8.
Proof. intros e E0 EM EC. unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia. Qed.

#[using="AO LOH SOK"] Lemma czone_static_dj : forall iv lo' hi', czone lo q S0 iv -> a0_static lo' hi' -> snd iv <= lo' \/ hi' <= fst iv.
Proof.
  intros [a b] lo' hi' CZ ST. apply a0_static_groups in ST. destruct ST as [LE ST]. cbn [fst snd].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (S6LO : 2147450880 + 2199023255552 <= sh alloc_ceiling - sh alloc_ceiling mod 8) by (unfold sh, SHADOW_OFF; clear - ACR; Z.div_mod_to_equations; lia).
  unfold czone, sub_iv, dstat, iastat, dreg in CZ. cbn [fst snd] in CZ.
  destruct CZ as [CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|CZ]]]]]]]]].
  - right. clear - CZ LOH ST. lia.
  - clear - CZ ST S6LO. lia.
  - clear - CZ ST S6LO. lia.
  - clear - CZ ST S6LO. lia.
  - layout_facts AO 0%nat SPF. destruct SPF as (SP1 & _). right. clear - CZ SP1 ST. lia.
  - layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _).
    assert (SS : 2147450880 + 2199023255552 <= sh (al_space AL)) by (unfold sh, SHADOW_OFF; clear - SP1; Z.div_mod_to_equations; lia).
    pose proof (sh_aligned_le (al_space AL + K_SPACE) ltac:(clear - SP1; lia) ltac:(clear - SPM; Z.div_mod_to_equations; lia) ltac:(clear - SP2; lia)) as SA.
    clear - CZ ST SS SA. lia.
  - layout_facts AO 1%nat LF. destruct LF as ((PL & _) & _). clear - CZ PL ST S6LO. lia.
  - layout_facts AO 3%nat LF. destruct LF as ((PL & _) & _). clear - CZ PL ST S6LO. lia.
  - layout_facts AO 5%nat LF5. destruct LF5 as ((PL5 & _) & _). layout_facts AO 6%nat LF6. destruct LF6 as ((PL6 & _) & _).
    destruct CZ as [CZ|CZ]; [clear - CZ PL5 ST S6LO; lia| clear - CZ PL6 ST S6LO; lia].
  - destruct CZ as (sc & Hin & CZ). pose proof (sec_geo AL S0 SOK sc Hin) as (D1 & D2 & D3 & D4 & _ & _ & _ & D8 & D9 & D10).
    pose proof (proj1 (Forall_forall _ _) SOK sc Hin) as CK. pose proof (chunk_ok_msize AL sc CK) as [_ CM2]. destruct CK as (CK1 & _).
    destruct CZ as [CZ|CZ].
    + clear - CZ D1 D4 ST S6LO. lia.
    + rewrite <- D8 in CZ.
      pose proof (sh_aligned_le (sc_beg sc + sc_msize sc) ltac:(clear - D1 D2; lia) ltac:(clear - CK1 CM2; Z.div_mod_to_equations; lia) D3) as SA.
      assert (SL : 0x800b9200 <= sh (sc_beg sc)) by (unfold sh, SHADOW_OFF; clear - D1; Z.div_mod_to_equations; lia).
      clear - CZ ST SA SL. lia.
Qed.

End MISS.

#[using="AO"] Lemma ftouch_thr_dj : forall (lo q : Z) (X : pstate) (m : mem) (glob loc : list qbatch) (ch : qchunk) W A n,
  0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch) -> incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X)) ->
  (need_batch loc = true -> 0 <= snd (enq_prim (fst X) loc) /\ 16 * snd (enq_prim (fst X) loc) + Q_BBYTES <= FA_OFF) ->
  Forall (ftouch AL q lo X glob loc ch) W ->
  (THR <= A /\ A + n <= THR + TQ_OFF) \/ (at_ctx L <= A /\ A + n <= at_ctx L + 4096) ->
  disjoint_from ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W) A n.
Proof.
  intros lo q X m glob loc ch W A n LOH CLO RP RS TCH TSI VNG FW HA.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _).
  layout_facts AO 2%nat LF2. destruct LF2 as ((PL2 & _) & CE2 & _). layout_facts AO 3%nat LF3. destruct LF3 as ((PL3 & _) & CE3 & _).
  layout_apart_fact AO 2%nat 3%nat AP23.

  assert (PG : exists base, base <= A /\ A + n <= base + 4096
                 /\ ((0 < base /\ base + 4096 <= 0x10000) \/ (6328320 <= base /\ base + 4096 <= 0x7fff7000) \/ 0x10007fff8000 <= base)
                 /\ base + 4096 <= alloc_ceiling
                 /\ (al_space AL + (K_SPACE + 4096) <= base \/ base + 4096 <= al_space AL)
                 /\ (DN0 D + 2^20 <= base \/ base + 4096 <= DN0 D) /\ (SS0 D + 2^23 <= base \/ base + 4096 <= SS0 D)
                 /\ (A + n <= TQ \/ TQ + 32 <= A) /\ (A + n <= THR + 3168 \/ THR + 3169 <= A)).
  { layout_apart_fact AO 0%nat 2%nat AP02. layout_apart_fact AO 0%nat 3%nat AP03.
    layout_apart_fact AO 2%nat 5%nat AP25. layout_apart_fact AO 2%nat 6%nat AP26. layout_apart_fact AO 3%nat 5%nat AP35. layout_apart_fact AO 3%nat 6%nat AP36.
    destruct HA as [HA|HA]; [exists THR| exists (at_ctx L)].
    - split; [clear - HA; lia|]. split; [clear - HA; lia|]. split; [exact PL3|]. split; [exact CE3|].
      split; [clear - AP03; lia|]. split; [clear - AP35; lia|]. split; [clear - AP36; lia|]. split; [left; clear - HA; lia| left; clear - HA; lia].
    - split; [clear - HA; lia|]. split; [clear - HA; lia|]. split; [exact PL2|]. split; [exact CE2|].
      split; [clear - AP02; lia|]. split; [clear - AP25; lia|]. split; [clear - AP26; lia|]. split; [clear - HA AP23; lia| clear - HA AP23; lia]. }
  destruct PG as (base & B1 & B2 & BPL & BCE & BSP & BDN & BSS & BTQ & BZE). clear PL2 PL3 CE2 CE3 AP23.
  assert (IMG : A + n <= 0x10000 \/ 6328320 <= A) by (clear - B1 B2 BPL; lia).
  cbn [disjoint_from]. split; [clear - IMG; lia|]. split; [clear - IMG; lia|]. split; [clear - BTQ; lia|].
  induction FW as [|[a b] W' HIV FW' IH]; cbn [disjoint_from]; [exact I|]. split; [| exact IH].
  destruct HIV as [AT|[[NB CI]|[DS|[DR|[IA|ZE]]]]].
  - pose proof (atouch_thr_dj AL X m lo q [(a, b)] _ _ A n AO LOH CLO RP RS TCH TSI ltac:(constructor; [exact AT| constructor]) HA) as DD.
    cbn [disjoint_from] in DD. exact (proj1 DD).
  - destruct (VNG NB) as [V0 V1]. pose proof (region_range AL K_BCLASS ltac:(lia)) as [RN1 RN2]. change Q_BBYTES with 8192 in V1.
    unfold chunk_iv, chunk_sh_iv in CI; cbn [fst snd] in CI; change (class_size K_BCLASS) with 8192 in CI. change (8192 / 8) with 1024 in CI.
    destruct CI as [CI|CI].
    + clear - CI V0 V1 RN1 RN2 BSP B1 B2. lia.
    + assert (SS : 2147450880 <= sh (region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc))
                   /\ sh (region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc)) + 1024 <= 17594333495296)
        by (unfold sh, SHADOW_OFF; clear - V0 V1 RN1 RN2 SP1 SP2 ACR; Z.div_mod_to_equations; lia).
      clear - CI SS BPL B1 B2. lia.
  - unfold dstat in DS. cbn [fst snd] in DS. clear - DS IMG. lia.
  - unfold dreg in DR. cbn [fst snd] in DR. destruct DR as [DR|DR]; [clear - DR BDN B1 B2; lia| clear - DR BSS B1 B2; lia].
  - unfold iastat in IA. cbn [fst snd] in IA. clear - IA IMG. lia.
  - inversion ZE; subst a b. clear - BZE. lia.
Qed.

Section CLIENT.
Variable FI : fs_if.
Variable AI : am_if FI.
Hypothesis FSBE : FSB FI = al_fsb AL.
Hypothesis STAT : forall lo' hi', am_static FI AI lo' hi' -> a0_static lo' hi'.
Variables (lo q : Z) (X : pstate) (m m' : mem) (glob loc : list qbatch) (ch : qchunk) (hrest : list (Z * Z)) (W : list (Z * Z)).
Notation FW_ := ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W).
Hypothesis LOH : 0x10007fff8000 <= lo.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LQ : lo <= q.
Hypothesis RP : RPRIM AL (fst X) m.
Hypothesis RS : RSEC AL (snd X) m.
Hypothesis TCH : Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch).
Hypothesis TSI : incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X)).
Hypothesis VNG : need_batch loc = true -> 0 <= snd (enq_prim (fst X) loc) /\ 16 * snd (enq_prim (fst X) loc) + Q_BBYTES <= FA_OFF.
Hypothesis NBX : need_batch loc = true -> held_ok (fst (enq_prim (fst X) loc)) ((K_BCLASS, snd (enq_prim (fst X) loc)) :: prim_of ch ++ hrest)
                            /\ (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls (fst (enq_prim (fst X) loc)) c)).
Hypothesis MU : munch FW_ m m'.
Hypothesis FW : Forall (ftouch AL q lo X glob loc ch) W.

#[using="HC AO m glob loc ch RP RS TCH TSI VNG FW"] Lemma fw_czone : Forall (czone lo q (snd X)) FW_.
Proof. exact (ficpt_W_czone lo q X m glob loc ch W RP RS TCH TSI VNG FW). Qed.
#[using="m RP RS"] Lemma fw_sok : Forall (chunk_ok AL) (se_chunks (snd X)).
Proof. destruct (clear_ctx AL X m RP RS) as (_ & SOK & _). exact SOK. Qed.

#[using="HC AL AO lo q X glob loc ch W LOH RP RS TCH TSI VNG MU FW"] Lemma free_asan_env : asan_env asegs m -> asan_env asegs m'.
Proof. intros AE. exact (asan_env_frame_m asegs m m' FW_ AE MU (czone_env_safe lo q (snd X) LOH fw_sok FW_ fw_czone)). Qed.

#[using="AL AO FSBE lo q X glob loc ch W LOH CLO RP RS TCH TSI VNG MU FW"] Lemma free_rfake : forall st, RFAKE FI st m -> RFAKE FI st m'.
Proof.
  intros st RF. eapply (rfake_frame_m FI st m m' FW_ RF MU). eapply Forall_impl; [| exact fw_czone]. intros iv CZ. left.
  rewrite FSBE. exact (czone_fs_dj lo q (snd X) LOH CLO fw_sok iv CZ).
Qed.

#[using="HC AO lo q m LOH CLO RP RS TCH TSI VNG NBX FW"] Lemma hull_W_dj : forall ch' A n, held_kind X ch' ->
  (forall cv, In cv (prim_of ch') -> ~ In cv (tc_of (glob ++ loc) ++ prim_of ch)) ->
  (forall sc, In sc (sec_of ch') -> ~ In sc (tsc_of (glob ++ loc) ++ sec_of ch)) ->
  (forall cv, In cv (prim_of ch') -> In cv hrest) ->
  qc_hull AL ch' A n -> disjoint_from FW_ A n.
Proof.
  intros ch' A n HK NP NS INH HU. pose proof (hull_lo AL AO X m ch' A n RP RS HK HU) as HL.
  cbn [disjoint_from]. split; [right; clear - HL; lia|]. split; [right; clear - HL; lia|].
  split. { pose proof (hull_tq_dj AL X m ch' A n AO RP RS HK HU) as DT. cbn [disjoint_from] in DT. exact (proj1 DT). }
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros iv FT.
  pose proof (hull_ftouch_dj AL AO lo q X m glob loc ch hrest ch' iv A n LOH CLO RP RS TCH TSI HK NP NS INH VNG NBX FT HU) as DI.
  destruct iv as [a b]. cbn [disjoint_from] in DI. cbn [fst snd]. exact (proj1 DI).
Qed.

#[using="Type"] Lemma dj_narrow : forall Wx A n a, disjoint_from Wx A n -> A <= a -> a + 1 <= A + n -> disjoint_from Wx a 1.
Proof.
  induction Wx as [|[x y] Wx IH]; intros A n a DJ H1 H2; cbn [disjoint_from] in *; [exact I|].
  destruct DJ as [D1 D2]. split; [clear - D1 H1 H2; lia| exact (IH A n a D2 H1 H2)].
Qed.

#[using="AO FSBE STAT lo W LOH CLO LQ RP RS TCH TSI VNG NBX MU FW"] Lemma free_apres : forall (live' : list (qchunk * Z)) (LBk : list (block (am_K FI AI))),
  (forall b, In b LBk -> exists r, In r live' /\ blk_addr b = lc_user AL (fst r) /\ blk_size b = snd r) ->
  (forall r, In r live' -> lr_ok r /\ held_kind X (fst r) /\ qchunk_wf (fst r)
       /\ (forall cv, In cv (prim_of (fst r)) -> ~ In cv (tc_of (glob ++ loc) ++ prim_of ch))
       /\ (forall sc, In sc (sec_of (fst r)) -> ~ In sc (tsc_of (glob ++ loc) ++ sec_of ch))
       /\ (forall cv, In cv (prim_of (fst r)) -> In cv hrest)) ->
  apres FI AI LBk q m m'.
Proof.
  intros live' LBk HB HR a Ha AC.
  assert (DJ : disjoint_from FW_ a 1).
  { destruct AC as [AC|[AC|[AC|[AC|[AC|AC]]]]].
    - exact (ftouch_above AL AO lo q X m glob loc ch W a 1 LOH CLO LQ RP RS TCH TSI VNG FW AC).
    - destruct AC as (lo' & hi' & ST & RNG). apply STAT in ST. apply dj_of_Forall. eapply Forall_impl; [| exact fw_czone].
      intros iv CZ. pose proof (czone_static_dj lo q (snd X) LOH fw_sok iv lo' hi' CZ ST) as DD. clear - DD RNG. lia.
    - destruct AC as (b & Hb & RNG). destruct (HB b Hb) as ([ch' cn] & Hr & BA & BS). cbn [fst snd] in BA, BS.
      destruct (HR _ Hr) as (LR & HK & WF & NP & NS & INH). cbn [fst snd] in LR, HK, WF, NP, NS, INH.
      pose proof (hull_W_dj ch' (qc_blk AL ch') (qc_bsize ch') HK NP NS INH ltac:(left; split; reflexivity)) as DH.
      destruct WF as (RZ16 & RZM & NR & RZN & _). unfold lc_user, qc_hdr in BA. unfold rup8 in RZN.
      eapply dj_narrow; [exact DH| |].
      + clear - RNG BA RZ16. lia.
      + destruct LR as [LR|[LR _]]; cbn [fst snd] in LR; [| clear - RNG BS LR; lia]. clear - RNG BA BS LR RZN NR. Z.div_mod_to_equations. lia.
    - apply dj_of_Forall. eapply Forall_impl; [| exact fw_czone]. intros iv CZ.
      pose proof (czone_fs_dj lo q (snd X) LOH CLO fw_sok iv CZ) as [DD _]. rewrite FSBE in AC. clear - DD AC. lia.
    - apply dj_of_Forall. eapply Forall_impl; [| exact fw_czone]. intros iv CZ.
      pose proof (czone_fs_dj lo q (snd X) LOH CLO fw_sok iv CZ) as [_ DD]. rewrite FSBE in AC. clear - DD AC. lia.
    - destruct AC as (b & Hb & RNG). destruct (HB b Hb) as ([ch' cn] & Hr & BA & BS). cbn [fst snd] in BA, BS.
      destruct (HR _ Hr) as (LR & HK & WF & NP & NS & INH). cbn [fst snd] in LR, HK, WF, NP, NS, INH.
      pose proof (hull_W_dj ch' (sh (qc_blk AL ch')) (qc_bsize ch' / 8) HK NP NS INH ltac:(right; left; split; reflexivity)) as DH.
      destruct (pchunk_geo AL X m ch' AO RP RS HK) as (B8 & S8 & _).
      destruct WF as (RZ16 & RZM & NR & RZN & _). unfold lc_user, qc_hdr in BA. rewrite BA, BS in RNG.
      destruct LR as [LR|[LR _]]; cbn [fst snd] in LR; [| rewrite LR in RNG; change (Z.of_nat (length (block_shadow 0))) with 0 in RNG; clear - RNG; lia].
      rewrite LR in RNG. rewrite (block_shadow_len (qc_n ch') ltac:(clear - NR; lia)) in RNG.
      replace (qc_blk AL ch' + qc_rz ch' - 16 + 16) with (qc_blk AL ch' + qc_rz ch') in RNG by (clear; lia).
      rewrite (sh_add8 (qc_blk AL ch') (qc_rz ch') B8 ltac:(clear - RZM; Z.div_mod_to_equations; lia)) in RNG.
      eapply dj_narrow; [exact DH| |].
      + clear - RNG RZ16. Z.div_mod_to_equations. lia.
      + unfold rup8 in *. clear - RNG RZN RZM S8 NR. Z.div_mod_to_equations. lia. }
  assert (O : outside FW_ (bv_unsigned (wa a))) by (eapply disjoint_outside; [exact DJ|]; rewrite wa_unsigned by lia; lia).
  split; [left; exact (MU _ O)|]. unfold wview. rewrite (MU _ O). exact (fun Hx => Hx).
Qed.

#[using="HC AO lo q X glob loc ch W LOH CLO RP RS TCH TSI VNG MU FW"] Lemma free_cells : thread_env2 AL m -> hooks_env m -> trace_env m -> quar_env m ->
  thread_env2 AL m' /\ hooks_env m' /\ trace_env m' /\ quar_env m'.
Proof.
  intros TE2 HKE (T1 & T2 & T3) (Q1 & Q2).
  pose proof (fun A k HA => ftouch_img_dj AL AO lo q X m glob loc ch W A k LOH CLO RP RS TCH TSI VNG FW HA) as IMG.
  split.
  { eapply (thread_env2_frame_m AL FW_ m m' TE2 MU).
    - exact (ftouch_thr_dj lo q X m glob loc ch W THR 8 LOH CLO RP RS TCH TSI VNG FW ltac:(left; clear; lia)).
    - exact (ftouch_thr_dj lo q X m glob loc ch W (at_ctx L + 8) 4 LOH CLO RP RS TCH TSI VNG FW ltac:(right; clear; lia)). }
  split. { unfold hooks_env in *. eapply rw_cells_transport_m; [exact HKE| exact MU|]. apply IMG. cbn [cells_size csize Nat.add Z.of_nat]. lia. }
  split.
  { unfold trace_env. split; [| split]; (eapply rw_cells_transport_m; [eassumption| exact MU|]); apply IMG; cbn [cells_size csize Nat.add Z.of_nat]; lia. }
  unfold quar_env. split; (eapply rw_cells_transport_m; [eassumption| exact MU|]); apply IMG; cbn [cells_size csize Nat.add Z.of_nat]; lia.
Qed.

#[using="AO lo q X glob loc ch W LOH CLO RP RS TCH TSI VNG MU FW"] Lemma free_fte : fs_tls_env THR A0_DTV A0_TLSB (al_dtls AL) (al_fsb AL) m -> fs_tls_env THR A0_DTV A0_TLSB (al_dtls AL) (al_fsb AL) m'.
Proof.
  intros FTE.
  pose proof (fun A k HA => ftouch_img_dj AL AO lo q X m glob loc ch W A k LOH CLO RP RS TCH TSI VNG FW HA) as IMG.
  eapply (fs_tls_env_frame_m _ _ _ _ _ FW_ m m' FTE MU). unfold fte_apart.
  split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|].
  split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|].
  split.
  { apply dj_of_Forall. eapply Forall_impl; [| exact fw_czone]. intros iv CZ.
    pose proof (czone_dtls_dj lo q (snd X) CLO fw_sok iv CZ) as DJ. lia. }
  exact (ftouch_thr_dj lo q X m glob loc ch W (THR + 48) 16 LOH CLO RP RS TCH TSI VNG FW ltac:(left; clear; lia)).
Qed.

#[using="HC AL AO lo q X glob loc ch W LOH CLO RP RS TCH TSI VNG MU FW"] Lemma free_aenv : alloc_env m -> alloc_env m'.
Proof.
  intros AE. ae_split AE.
  pose proof (fun A k HA => ftouch_img_dj AL AO lo q X m glob loc ch W A k LOH CLO RP RS TCH TSI VNG FW HA) as IMG.
  unfold alloc_env. repeat match goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport_m; [eassumption| exact MU|]; apply IMG; cbn [cells_size csize Nat.add Z.of_nat]; lia).
Qed.

End CLIENT.
End FZ.
