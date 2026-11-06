(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc APrimCover ASec ASecD AQuar AQuarM AHeap AFoot AQuarR AQuarS AQuarP ATacFix AQuarT AQuarU
                        AFrameG AQuarG AAllocInvS AHeap2 AHeapB AFreeF AFreeZ AFsEnv AFteF AAllocF.
Import ListNotations.
Open Scope Z_scope.

Ltac demodt H z :=
  unfold id in H;
  lazymatch type of H with
  | ?a mod ?b = 0 => apply (proj1 (Z.mod_divide a b ltac:(lia))) in H; unfold Z.divide in H; destruct H as [z H]
  end.

Section GL.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation THR := (at_thr (al_thread AL)).
Notation D := (al_depot AL).
Hypothesis AO : alayout_ok AL.

#[using="Type"] Lemma lchunk_rep_frame_g : forall W (m m' : mem) ch,
  lchunk_rep AL m ch -> qchunk_wf ch -> qc_blk AL ch mod 8 = 0 -> qc_bsize ch mod 8 = 0 -> gmunch W m m' -> wmono asegs m m' ->
  disjoint_from W (qc_blk AL ch) (qc_bsize ch) -> disjoint_from W (sh (qc_blk AL ch)) (qc_bsize ch / 8) ->
  match qc_kind ch with
  | QPrim _ _ => True
  | QSec sc => disjoint_from W (sc_beg sc + 32) 4064 /\ disjoint_from W (sh (sc_beg sc)) 512
  end ->
  lchunk_rep AL m' ch.
Proof.
  intros W m m' ch R WF B8 S8 GM WM DA DS DK. unfold lchunk_rep in *. cbv zeta in *.
  destruct WF as (RZ16 & RZM & NR & RZN & _).
  set (B := qc_blk AL ch) in *. set (bs := qc_bsize ch) in *. set (rz := qc_rz ch) in *. set (n := qc_n ch) in *.
  assert (EH : qc_hdr AL ch = B + rz - 16) by reflexivity. rewrite EH in *. clear EH.
  assert (N8 : n <= rup8 n < n + 8 /\ rup8 n mod 8 = 0) by (unfold rup8; clear; Z.div_mod_to_equations; lia).
  demodt B8 kb. demodt S8 ks. demodt RZM kr. destruct N8 as [N8 N8m]. demodt N8m kn.
  assert (SHX : forall k, 0 <= k -> sh (B + 8 * k) = sh B + k) by (intros k Hk; unfold sh; rewrite B8; clear - Hk; Z.div_mod_to_equations; lia).
  assert (DV : rz / 8 = 2 * kr /\ rup8 n / 8 = kn /\ bs / 8 = ks /\ (bs - rz - rup8 n) / 8 = ks - 2 * kr - kn)
    by (rewrite RZM, N8m, S8; clear; Z.div_mod_to_equations; lia).
  destruct DV as (DV1 & DV2 & DV3 & DV4). rewrite DV3 in DS.
  assert (TRA : forall A cs, rw_cells asegs m A cs -> B <= A -> A + Z.of_nat (cells_size cs) <= B + bs -> rw_cells asegs m' A cs).
  { intros A cs X H1 H2. eapply rw_cells_gtransport; [exact X| exact GM| exact WM|]. eapply disjoint_from_sub; [exact DA| exact H1| exact H2]. }
  assert (TRS : forall A cs, rw_cells asegs m A cs -> sh B <= A -> A + Z.of_nat (cells_size cs) <= sh B + ks -> rw_cells asegs m' A cs).
  { intros A cs X H1 H2. eapply rw_cells_gtransport; [exact X| exact GM| exact WM|]. eapply disjoint_from_sub; [exact DS| exact H1| exact H2]. }
  destruct R as ((bits & actx & BITS & R1) & R2 & (ub & R3) & (j4 & R4) & R5 & R6 & R7 & R8).
  split. { exists bits, actx. split; [exact BITS|]. apply TRA; [exact R1| clear - RZ16; lia| cbn [cells_size csize Nat.add]; clear - RZ16 RZN N8 NR; lia]. }
  split.
  { intros RZ32. destruct (R2 RZ32) as [R2a (j2 & R2b)]. split.
    - apply TRA; [exact R2a| clear; lia| cbn [cells_size csize Nat.add]; clear - RZ32 RZM RZN N8 NR; lia].
    - exists j2. apply TRA; [exact R2b| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZ32 RZM; lia). clear - RZ32 RZM RZN N8 NR. lia. }
  split. { exists ub. apply TRA; [exact R3| clear - RZ16; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - NR; lia). clear - RZN N8. lia. }
  split. { exists j4. apply TRA; [exact R4| clear - RZ16 NR; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZN N8 NR; lia). clear. lia. }
  split. { apply TRS; [exact R5| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV1, Z2Nat.id by (clear - RZ16 RZM; lia). clear - RZN RZM N8m S8 N8 NR. lia. }
  split.
  { replace (B + rz - 16 + 16) with (B + 8 * (2 * kr)) in * by (clear - RZM; lia). rewrite (SHX (2 * kr)) in * by (clear - RZ16 RZM; lia).
    pose proof (block_shadow_len n ltac:(clear - NR; lia)) as BL. rewrite DV2 in BL.
    apply TRS; [exact R6| clear - RZ16 RZM; lia|]. rewrite cells_size_shadow, BL. clear - RZN RZM N8m S8. lia. }
  split.
  { replace (B + rz - 16 + 16 + rup8 n) with (B + 8 * (2 * kr + kn)) in * by (clear - RZM N8m; lia).
    rewrite (SHX (2 * kr + kn)) in * by (clear - RZ16 RZM N8 NR N8m; lia).
    apply TRS; [exact R7| clear - RZ16 RZM N8 NR N8m; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV4, Z2Nat.id by (clear - RZN RZM N8m S8; lia). clear. lia. }
  destruct (qc_kind ch) as [c v| sc]; [exact I|]. destruct DK as [DK1 DK2]. destruct R8 as [(j7 & R7a) R7b]. split.
  - exists j7. eapply rw_cells_gtransport; [exact R7a| exact GM| exact WM| cbn [cells_size csize Nat.add]; exact DK1].
  - eapply rw_cells_gtransport; [exact R7b| exact GM| exact WM| cbn [cells_size csize Nat.add]; exact DK2].
Qed.

#[using="AO"] Lemma lchunk_rep_hull_g : forall X W (m m' : mem) ch, alayout_ok AL -> RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch ->
  lchunk_rep AL m ch -> qchunk_wf ch -> gmunch W m m' -> wmono asegs m m' -> (forall A n, qc_hull AL ch A n -> disjoint_from W A n) -> lchunk_rep AL m' ch.
Proof.
  intros X W m m' ch _ RP RS HK R WF GM WM HU.
  destruct (pchunk_geo AL X m ch AO RP RS HK) as (GB8 & GS8 & _).
  eapply lchunk_rep_frame_g; [exact R| exact WF| exact GB8| exact GS8| exact GM| exact WM| | |].
  - apply HU. left. split; reflexivity.
  - apply HU. right; left. split; reflexivity.
  - destruct (qc_kind ch) as [c v|sc] eqn:EK; [exact I|]. split; apply HU; right; right; rewrite EK; [left| right]; split; reflexivity.
Qed.

#[using="Type"] Lemma qlist_rep_hull_g : forall W (m m' : mem) l nxt, gmw W m m' -> qlist_rep AL m l nxt ->
  Forall (fun b => disjoint_from W (qb_addr AL b) 8192 /\ disjoint_from W (sh (qb_addr AL b)) 1024) l -> qlist_rep AL m' l nxt.
Proof.
  intros W m m' l nxt MU. induction l as [|b l IH]; intros QL FB; [exact I|].
  cbn [qlist_rep] in *. destruct QL as [RB QL]. apply Forall_cons_iff in FB as [(D1 & D2) FB]. split; [| exact (IH QL FB)].
  exact (qbatch_rep_frame_g AL W m m' b _ RB MU D1 D2).
Qed.

Section ST.
Variables (lo q : Z) (X : pstate) (m : mem) (a msz : Z) (avoid : list (Z * Z)).
Hypothesis LOH : 0x10007fff8000 <= lo.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis RP : RPRIM AL (fst X) m.
Hypothesis RS : RSEC AL (snd X) m.
Hypothesis A4K : a mod 4096 = 0.
Hypothesis ALO : 0x609000 <= a.
Hypothesis APL : anon_place a msz.
Hypothesis MB : 8192 <= msz.
Hypothesis MB4K : msz mod 4096 = 0.
Hypothesis AV : Forall (fun iv => a + msz <= fst iv \/ snd iv <= a) avoid.
Hypothesis AREG : Forall (fun rg : Z * Z => In (fst rg, fst rg + snd rg) avoid) (al_regions AL).
Hypothesis ACH : Forall (fun c => In (sc_beg c, sc_beg c + sc_msize c) avoid) (se_chunks (snd X)).

Definition stouch (iv : Z * Z) : Prop :=
  atouch AL lo q (fst X) (snd X) [] [] iv
  \/ sub_iv a (a + msz) iv \/ sub_iv (sh a) (sh a + msz / 8) iv \/ dstat iv \/ dreg AL iv \/ iastat iv \/ iv = (THR + 3168, THR + 3169).

#[using="avoid AV AREG"] Lemma snew_region_apart : forall rg, In rg (al_regions AL) -> a + msz <= fst rg \/ fst rg + snd rg <= a.
Proof. intros rg Hrg. pose proof (proj1 (Forall_forall _ _) AV _ (proj1 (Forall_forall _ _) AREG rg Hrg)) as X0. cbn [fst snd] in X0. exact X0. Qed.

#[using="A4K ALO APL MB4K"] Lemma snew_bounds : 0 <= a /\ a + msz <= 2^47 /\ a mod 8 = 0 /\ msz mod 8 = 0 /\ app_mem a msz /\ a + msz <= alloc_ceiling
  /\ 0x7fff8000 <= sh a /\ sh a + msz / 8 <= 0x10007fff8000 /\ 0x800b9200 <= sh a.
Proof.
  pose proof (anon_place_app_mem a msz APL) as AM. destruct APL as [_ ACE]. pose proof (@alloc_ceiling_lt47 HC) as C47.
  unfold app_mem in AM. unfold sh, SHADOW_OFF. repeat split; try (clear - AM ALO A4K MB MB4K ACE C47; Z.div_mod_to_equations; lia). exact AM.
Qed.

#[using="HC AO m avoid RP RS A4K ALO APL MB MB4K AV AREG ACH"] Lemma salloc_hull_dj : forall ch' A n, held_kind X ch' -> qc_hull AL ch' A n -> disjoint_from [(a, a + msz); (sh a, sh a + msz / 8)] A n.
Proof.
  intros ch' A n HK' HU.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  destruct snew_bounds as (A0 & ATOP & A8 & M8 & AM & ACE & _).
  pose proof (snew_region_apart _ (or_introl eq_refl)) as APS. cbn [fst snd] in APS.
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _ & _ & SP5 & _ & SP7).
  destruct ch' as [[c v|sc] rz' n']; unfold held_kind in HK'; unfold qc_hull, qc_blk, qc_bsize in HU; cbn [qc_kind] in HK', HU.
  - pose proof (held_range AL (fst X) m c v RP HK') as (R1 & R2 & R3 & R4).
    pose proof HK' as (Hc & V0 & _). cbn [fst snd] in Hc, V0. pose proof (class_size_pos c Hc) as CS. pose proof (REG_mod8 AL AO c) as RG8.
    destruct HU as [(-> & ->)|[(-> & ->)|[]]].
    + apply (salloc_dj_app a msz (al_space AL) (K_SPACE + 4096)); [exact A0| clear - MB; lia| exact ATOP| clear - APS; lia| right; exact SP1| clear - R3; lia| clear - R4; lia].
    + apply (salloc_dj_sh a msz (al_space AL) (K_SPACE + 4096)); [exact AM| exact A8| clear - MB; lia| exact M8| clear - APS; lia| clear - SP1; lia| clear - SP5; lia
                                                                  | clear - R3; lia| clear - R4; lia| clear - CS; lia| clear - RG8; Z.div_mod_to_equations; lia].
  - pose proof (proj1 (Forall_forall _ _) SOK sc HK') as CK. pose proof (chunk_ok_msize AL sc CK) as (CM1 & CM2). destruct CK as (CK1 & CK2 & _ & _ & CK5 & CK6 & _).
    pose proof (proj1 (Forall_forall _ _) AV _ (proj1 (Forall_forall _ _) ACH sc HK')) as APC. cbn [fst snd] in APC.
    assert (SHULL : forall b' s', sc_beg sc <= b' -> b' + s' <= sc_beg sc + sc_msize sc -> 0 <= s' -> b' mod 8 = 0 ->
              disjoint_from [(a, a + msz); (sh a, sh a + msz / 8)] b' s'
              /\ disjoint_from [(a, a + msz); (sh a, sh a + msz / 8)] (sh b') (s' / 8)).
    { intros b' s' B1 B2 S'0 B8. split.
      - apply (salloc_dj_app a msz (sc_beg sc) (sc_msize sc)); [exact A0| clear - MB; lia| exact ATOP| exact APC| clear - CK5; lia| exact B1| exact B2].
      - apply (salloc_dj_sh a msz (sc_beg sc) (sc_msize sc)); [exact AM| exact A8| clear - MB; lia| exact M8| exact APC| clear - CK2; lia| clear - CK6 ACR; lia
                                                               | exact B1| exact B2| exact S'0| exact B8]. }
    destruct HU as [(-> & ->)|[(-> & ->)|[(-> & ->)|(-> & ->)]]].
    + apply (SHULL (sc_beg sc + 4096) (sc_msize sc - 4096)); [clear; lia| clear; lia| clear - CM1; lia| clear - CK1; Z.div_mod_to_equations; lia].
    + apply (SHULL (sc_beg sc + 4096) (sc_msize sc - 4096)); [clear; lia| clear; lia| clear - CM1; lia| clear - CK1; Z.div_mod_to_equations; lia].
    + apply (SHULL (sc_beg sc + 32) 4064); [clear; lia| clear - CM1; lia| clear; lia| clear - CK1; Z.div_mod_to_equations; lia].
    + change 512 with (4096 / 8). apply (SHULL (sc_beg sc) 4096); [clear; lia| clear - CM1; lia| clear; lia| clear - CK1; Z.div_mod_to_equations; lia].
Qed.

#[using="HC AO m avoid LOH CLO RP RS A4K ALO APL MB MB4K AV AREG ACH"] Lemma hull_stouch_dj : forall ch' iv A n, held_kind X ch' -> stouch iv -> qc_hull AL ch' A n -> disjoint_from [iv] A n.
Proof.
  intros ch' iv A n HK MT HU.
  destruct MT as [AT|[CI|[CI|[DS|[DR|[IA|ZE]]]]]].
  - exact (hull_atouch_dj AL X m lo q [iv] [] [] ch' A n AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) ltac:(constructor; [exact AT| constructor]) HK
             ltac:(intros cv _ []) ltac:(intros sc _ []) HU).
  - pose proof (salloc_hull_dj ch' A n HK HU) as DD. destruct iv as [x y]. unfold sub_iv in CI. cbn [fst snd disjoint_from] in *. clear - DD CI. lia.
  - pose proof (salloc_hull_dj ch' A n HK HU) as DD. destruct iv as [x y]. unfold sub_iv in CI. cbn [fst snd disjoint_from] in *. clear - DD CI. lia.
  - exact (hull_dzone_dj AL X m lo [iv] ch' A n AO LOH CLO RP RS HK ltac:(constructor; [right; left; exact DS| constructor]) HU).
  - exact (hull_dzone_dj AL X m lo [iv] ch' A n AO LOH CLO RP RS HK ltac:(constructor; [right; right; exact DR| constructor]) HU).
  - exact (hull_izone_dj AL X m lo [iv] ch' A n AO LOH CLO RP RS HK ltac:(constructor; [right; left; exact IA| constructor]) HU).
  - exact (hull_izone_dj AL X m lo [iv] ch' A n AO LOH CLO RP RS HK ltac:(constructor; [right; right; exact ZE| constructor]) HU).
Qed.

#[using="HC AO m LOH CLO RP RS A4K ALO APL MB4K"] Lemma stouch_above : forall W A k, lo <= q -> Forall stouch W -> q <= A -> disjoint_from W A k.
Proof.
  intros W A k LQ FW HA. destruct snew_bounds as (A0 & ATOP & A8 & M8 & AM & ACE & SH1 & SH2 & _).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros [x y] MT. cbn [fst snd].
  destruct MT as [AT|[CI|[CI|[DS|[DR|[IA|ZE]]]]]].
  - pose proof (atouch_above AL X m lo q [(x, y)] [] [] A k AO LOH CLO LQ RP RS ltac:(constructor) ltac:(intros d []) ltac:(constructor; [exact AT| constructor]) HA) as DD.
    cbn [disjoint_from] in DD. exact (proj1 DD).
  - unfold sub_iv in CI. cbn [fst snd] in CI. right. clear - CI ACE CLO LQ HA. lia.
  - unfold sub_iv in CI. cbn [fst snd] in CI. right. clear - CI SH2 LOH LQ HA. lia.
  - unfold dstat in DS. cbn [fst snd] in DS. right. clear - DS HA LOH LQ. lia.
  - unfold dreg in DR. cbn [fst snd] in DR. right. clear - DR HA N2d S2d CLO LQ. lia.
  - unfold iastat in IA. cbn [fst snd] in IA. right. clear - IA HA LOH LQ. lia.
  - inversion ZE; subst x y. right. clear - HA T4 CLO LQ. lia.
Qed.

#[using="HC AO m LOH CLO RP RS A4K ALO APL MB4K"] Lemma stouch_img_dj : forall W A k, Forall stouch W ->
  (65536 <= A /\ A + k <= SEC) \/ (GSTATS_A + 16 <= A /\ A + k <= 743232)
  \/ (1271664 <= A /\ A + k <= 1327048) \/ (1327052 <= A /\ A + k <= 1598472) \/ (5858360 <= A /\ A + k <= 6328320) ->
  disjoint_from W A k.
Proof.
  intros W A k FW HA. destruct snew_bounds as (A0 & ATOP & A8 & M8 & AM & ACE & SH1 & SH2 & _).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
  assert (IMG : 65536 <= A /\ A + k <= 6328320) by (clear - HA; lia).
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros [x y] MT. cbn [fst snd].
  destruct MT as [AT|[CI|[CI|[DS|[DR|[IA|ZE]]]]]].
  - assert (CASE : (65536 <= A /\ A + k <= SEC) \/ (GSTATS_A + 16 <= A /\ A + k <= 6328320)) by (clear - HA; lia).
    destruct CASE as [[C1 C2]|[C1 C2]].
    + pose proof (atouch_img_lo_dj AL AO X m lo q [(x, y)] [] [] A k LOH CLO RP RS ltac:(constructor) ltac:(intros d []) ltac:(constructor; [exact AT| constructor]) C1 C2) as DD. cbn [disjoint_from] in DD. exact (proj1 DD).
    + pose proof (atouch_img_dj AL X m lo q [(x, y)] [] [] A k AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) ltac:(constructor; [exact AT| constructor]) C1 C2) as DD. cbn [disjoint_from] in DD. exact (proj1 DD).
  - unfold sub_iv in CI. cbn [fst snd] in CI. left. clear - CI ALO IMG. lia.
  - unfold sub_iv in CI. cbn [fst snd] in CI. left. clear - CI SH1 IMG. lia.
  - unfold dstat in DS. cbn [fst snd] in DS. clear - DS HA. lia.
  - unfold dreg in DR. cbn [fst snd] in DR. clear - DR IMG N1d S1d. lia.
  - unfold iastat in IA. cbn [fst snd] in IA. clear - IA HA. lia.
  - inversion ZE; subst x y. clear - IMG T3. lia.
Qed.

#[using="HC AO avoid A4K ALO APL MB4K AV AREG"] Lemma snew_region_dj : forall i A k, (1 <= i < 8)%nat ->
  let rg := nth i (al_regions AL) (0, 0) in fst rg <= A -> A + k <= fst rg + snd rg ->
  disjoint_from [(a, a + msz); (sh a, sh a + msz / 8)] A k.
Proof.
  intros i A k Hi rg P1 P2. destruct snew_bounds as (A0 & ATOP & A8 & M8 & AM & ACE & SH1 & SH2 & _).
  pose proof (region_facts AL i AO ltac:(lia)) as RF. cbv zeta in RF. fold rg in RF. destruct RF as ((RF1 & _) & RF2 & _ & _ & _ & _ & RSH).
  assert (INR : In rg (al_regions AL)) by (subst rg; apply nth_In; cbn; lia).
  pose proof (snew_region_apart rg INR) as AP.
  assert (SR : fst rg + snd rg <= 0x7fff7000 \/ 0x10007fff8000 <= fst rg) by (clear - RF1; lia).
  cbn [disjoint_from]. split; [clear - AP P1 P2; lia|]. split; [| exact I]. clear - SH1 SH2 SR P1 P2. lia.
Qed.

#[using="HC AO m avoid LOH CLO RP RS A4K ALO APL MB4K AV AREG"] Lemma stouch_thr_dj : forall W A k, Forall stouch W ->
  (THR <= A /\ A + k <= THR + TQ_OFF) \/ (at_ctx (al_thread AL) <= A /\ A + k <= at_ctx (al_thread AL) + 4096)
  \/ (THR + TQ_OFF <= A /\ A + k <= THR + TQ_OFF + 32) -> disjoint_from W A k.
Proof.
  intros W A k FW HA.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  layout_facts AO 2%nat LF2. destruct LF2 as ((PL2 & _) & CE2 & _). layout_facts AO 3%nat LF3. destruct LF3 as ((PL3 & _) & CE3 & _).
  layout_apart_fact AO 2%nat 3%nat AP23.
  assert (PG : exists base, base <= A /\ A + k <= base + 4096
                 /\ ((0 < base /\ base + 4096 <= 0x10000) \/ (6328320 <= base /\ base + 4096 <= 0x7fff7000) \/ 0x10007fff8000 <= base)
                 /\ base + 4096 <= alloc_ceiling
                 /\ (DN0 (al_depot AL) + 2^20 <= base \/ base + 4096 <= DN0 (al_depot AL)) /\ (SS0 (al_depot AL) + 2^23 <= base \/ base + 4096 <= SS0 (al_depot AL))
                 /\ (A + k <= THR + 3168 \/ THR + 3169 <= A)
                 /\ disjoint_from [(a, a + msz); (sh a, sh a + msz / 8)] A k).
  { layout_apart_fact AO 2%nat 5%nat AP25. layout_apart_fact AO 2%nat 6%nat AP26. layout_apart_fact AO 3%nat 5%nat AP35. layout_apart_fact AO 3%nat 6%nat AP36.
    assert (HA2 : (THR <= A /\ A + k <= THR + 112) \/ (at_ctx (al_thread AL) <= A /\ A + k <= at_ctx (al_thread AL) + 4096)) by (clear - HA; lia).
    destruct HA2 as [HA2|HA2]; [exists THR| exists (at_ctx (al_thread AL))].
    - split; [clear - HA2; lia|]. split; [clear - HA2; lia|]. split; [exact PL3|]. split; [exact CE3|].
      split; [clear - AP35; lia|]. split; [clear - AP36; lia|]. split; [left; clear - HA2; lia|].
      apply (snew_region_dj 3 A k ltac:(lia)); cbn [nth al_regions fst snd]; clear - HA2; lia.
    - split; [clear - HA2; lia|]. split; [clear - HA2; lia|]. split; [exact PL2|]. split; [exact CE2|].
      split; [clear - AP25; lia|]. split; [clear - AP26; lia|]. split; [clear - HA2 AP23; lia|].
      apply (snew_region_dj 2 A k ltac:(lia)); cbn [nth al_regions fst snd]; clear - HA2; lia. }
  destruct PG as (base & P1 & P2 & BPL & BCE & BDN & BSS & BZE & BNEW).
  assert (IMG : A + k <= 0x10000 \/ 6328320 <= A) by (clear - P1 P2 BPL; lia).
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros [x y] MT. cbn [fst snd].
  destruct MT as [AT|[CI|[CI|[DS|[DR|[IA|ZE]]]]]].
  - assert (FA1 : Forall (atouch AL lo q (fst X) (snd X) [] []) [(x, y)]) by (constructor; [exact AT| constructor]).
    destruct HA as [HA|[HA|HA]].
    + pose proof (atouch_thr_dj AL X m lo q [(x, y)] [] [] A k AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) FA1 (or_introl HA)) as DD. cbn [disjoint_from] in DD. exact (proj1 DD).
    + pose proof (atouch_thr_dj AL X m lo q [(x, y)] [] [] A k AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) FA1 (or_intror HA)) as DD. cbn [disjoint_from] in DD. exact (proj1 DD).
    + pose proof (atouch_tq_dj AL X m lo q [(x, y)] [] [] A k AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) FA1 (proj1 HA) (proj2 HA)) as DD. cbn [disjoint_from] in DD. exact (proj1 DD).
  - unfold sub_iv in CI. cbn [fst snd disjoint_from] in *. clear - CI BNEW. lia.
  - unfold sub_iv in CI. cbn [fst snd disjoint_from] in *. clear - CI BNEW. lia.
  - unfold dstat in DS. cbn [fst snd] in DS. clear - DS IMG. lia.
  - unfold dreg in DR. cbn [fst snd] in DR. destruct DR as [DR|DR]; [clear - DR BDN P1 P2; lia| clear - DR BSS P1 P2; lia].
  - unfold iastat in IA. cbn [fst snd] in IA. clear - IA IMG. lia.
  - inversion ZE; subst x y. clear - BZE. lia.
Qed.

#[using="Type"] Lemma czone_mono : forall (S0 S1 : asec) iv, incl (se_chunks S0) (se_chunks S1) -> czone AL lo q S0 iv -> czone AL lo q S1 iv.
Proof.
  intros S0 S1 iv INC CZ. unfold czone in *.
  destruct CZ as [CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|[CZ|(sc & Hin & CZ)]]]]]]]]]; try tauto.
  do 9 right. exists sc. split; [apply INC; exact Hin| exact CZ].
Qed.

#[using="HC AO m RP RS"] Lemma stouch_czone : forall (S1 : asec) sc iv, se_chunks S1 = se_chunks (snd X) ++ [sc] -> sc_beg sc = a -> sc_msize sc = msz ->
  stouch iv -> czone AL lo q S1 iv.
Proof.
  intros S1 sc [x y] ES EB EM MT.
  assert (INC : incl (se_chunks (snd X)) (se_chunks S1)) by (rewrite ES; intros d Hd; apply in_or_app; left; exact Hd).
  assert (INS : In sc (se_chunks S1)) by (rewrite ES; apply in_or_app; right; left; reflexivity).
  destruct MT as [AT|[CI|[CI|[DS|[DR|[IA|ZE]]]]]].
  - apply (czone_mono (snd X) S1 _ INC). exact (atouch_czone AL AO X m lo q [] [] (x, y) RP RS ltac:(constructor) ltac:(intros d []) AT).
  - do 9 right. exists sc. split; [exact INS|]. left. rewrite EB, EM. exact CI.
  - do 9 right. exists sc. split; [exact INS|]. right. rewrite EB, EM. exact CI.
  - right; right; left. exact DS.
  - do 8 right. left. exact DR.
  - right; right; right; left. exact IA.
  - inversion ZE; subst x y. do 7 right. left. unfold sub_iv. cbn [fst snd]. clear. lia.
Qed.

#[using="HC AO m avoid LOH CLO RP RS A4K ALO APL MB4K AV AREG"] Lemma stouch_fte : forall W, Forall stouch W -> fte_apart THR A0_DTV A0_TLSB (al_dtls AL) W.
Proof.
  intros W FW. unfold fte_apart.
  pose proof (fun A k HA => stouch_img_dj W A k FW HA) as IMG.
  split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|].
  split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|]. split; [apply IMG; lia|].
  split; [| exact (stouch_thr_dj W (THR + 48) 16 FW ltac:(left; clear; lia))].
  destruct (clear_ctx AL X m RP RS) as (_ & SOK & _).
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros [x y] MT. cbn [fst snd].
  destruct MT as [AT|[CI|[CI|MT]]].
  - pose proof (czone_dtls_dj AL AO lo q (snd X) CLO SOK (x, y) (atouch_czone AL AO X m lo q [] [] (x, y) RP RS ltac:(constructor) ltac:(intros d []) AT)) as DJ. cbn [fst snd] in DJ. lia.
  - pose proof (snew_region_dj 7 (al_dtls AL + 24) 8 ltac:(lia) ltac:(cbn [nth al_regions fst snd]; lia) ltac:(cbn [nth al_regions fst snd]; lia)) as DD.
    unfold sub_iv in CI. cbn [fst snd disjoint_from] in *. clear - CI DD. lia.
  - pose proof (snew_region_dj 7 (al_dtls AL + 24) 8 ltac:(lia) ltac:(cbn [nth al_regions fst snd]; lia) ltac:(cbn [nth al_regions fst snd]; lia)) as DD.
    unfold sub_iv in CI. cbn [fst snd disjoint_from] in *. clear - CI DD. lia.
  - assert (CZ : czone AL lo q (snd X) (x, y)).
    { destruct MT as [DS|[DR|[IA|ZE]]]; [right; right; left; exact DS| do 8 right; left; exact DR| right; right; right; left; exact IA|].
      inversion ZE; subst x y. do 7 right. left. unfold sub_iv. cbn [fst snd]. clear. lia. }
    pose proof (czone_dtls_dj AL AO lo q (snd X) CLO SOK (x, y) CZ) as DJ. cbn [fst snd] in DJ. lia.
Qed.
End ST.

End GL.
