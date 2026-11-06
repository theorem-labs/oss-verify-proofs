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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc APrimCover ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A F_sec_B F_quar_P AQuarT AQuarU F_gct F_depot F_depot_C F_quar_C F_prim_L0 F_hooks F_dealloc
                        F_ialloc F_unwind F_stacktrace F_free_icpt F_free_null F_alloc_env F_alloc_A F_alloc_B F_alloc_C AAllocInv AAllocCarve AAllocEnvF F_alloc_P F_alloc_M
                        F_malloc_icpt ALedger AHeap2 AHeapB AFreeF AFreeZ AFreeL8 AAllocF AMallocP AMallocL8 AAllocL8 AHeapLaws
                        AFrameG AQuarG AAllocInvS AAllocCarveS F_alloc_S1 F_alloc_S2 F_alloc_S AFsEnv AFteF AFrameGL AMallocGL8.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section ASL8.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation D := (al_depot AL).
Notation THR := (at_thr (al_thread AL)).
Notation PARR := (al_parr AL).
Variable FI : fs_if.
Variable AI : am_if FI.
Hypothesis AO : alayout_ok AL.
Hypothesis SWIN_LO : 65536 <= SWIN D.
Hypothesis FSBE : FSB FI = al_fsb AL.
Hypothesis STAT : forall lo' hi', am_static FI AI lo' hi' -> a0_static lo' hi'.

#[using="AO FSBE STAT"] Lemma apres_of_czone_g : forall (lo q : Z) (X : pstate) (S1 : asec) (m m' : mem) W (live' : list (qchunk * Z)) (LBk : list (block (am_K FI AI))),
  0x10007fff8000 <= lo -> alloc_ceiling <= lo -> RPRIM AL (fst X) m -> RSEC AL (snd X) m -> Forall (chunk_ok AL) (se_chunks S1) ->
  gmunch W m m' -> wmono asegs m m' -> Forall (czone AL lo q S1) W ->
  (forall A k, q <= A -> disjoint_from W A k) ->
  (forall b, In b LBk -> exists r, In r live' /\ blk_addr b = lc_user AL (fst r) /\ blk_size b = snd r) ->
  (forall r, In r live' -> lr_ok r /\ held_kind X (fst r) /\ qchunk_wf (fst r) /\ (forall A n, qc_hull AL (fst r) A n -> disjoint_from W A n)) ->
  apres FI AI LBk q m m'.
Proof.
  intros lo q X S1 m m' W live' LBk LOH CLO RP RS SOK GM WM FZ ABOVE HB HR a Ha AC.
  assert (DJ : disjoint_from W a 1).
  { destruct AC as [AC|[AC|[AC|[AC|[AC|AC]]]]].
    - exact (ABOVE a 1 AC).
    - destruct AC as (lo' & hi' & ST & RNG). apply STAT in ST. apply dj_of_Forall. eapply Forall_impl; [| exact FZ].
      intros iv CZ. pose proof (czone_static_dj AL AO lo q S1 LOH SOK iv lo' hi' CZ ST) as DD. clear - DD RNG. lia.
    - destruct AC as (b & Hb & RNG). destruct (HB b Hb) as ([ch' cn] & Hr & BA & BS). cbn [fst snd] in BA, BS.
      destruct (HR _ Hr) as (LR & HK & WF & HU). cbn [fst snd] in LR, HK, WF, HU.
      pose proof (HU (qc_blk AL ch') (qc_bsize ch') ltac:(left; split; reflexivity)) as DH.
      destruct WF as (RZ16 & RZM & NR & RZN & _). unfold lc_user, qc_hdr in BA. unfold rup8 in RZN.
      eapply dj_narrow; [exact DH| |].
      + clear - RNG BA RZ16. lia.
      + destruct LR as [LR|[LR _]]; cbn [fst snd] in LR; [| clear - RNG BS LR; lia]. clear - RNG BA BS LR RZN NR. Z.div_mod_to_equations. lia.
    - apply dj_of_Forall. eapply Forall_impl; [| exact FZ]. intros iv CZ.
      pose proof (czone_fs_dj AL AO lo q S1 LOH CLO SOK iv CZ) as [DD _]. rewrite FSBE in AC. clear - DD AC. lia.
    - apply dj_of_Forall. eapply Forall_impl; [| exact FZ]. intros iv CZ.
      pose proof (czone_fs_dj AL AO lo q S1 LOH CLO SOK iv CZ) as [_ DD]. rewrite FSBE in AC. clear - DD AC. lia.
    - destruct AC as (b & Hb & RNG). destruct (HB b Hb) as ([ch' cn] & Hr & BA & BS). cbn [fst snd] in BA, BS.
      destruct (HR _ Hr) as (LR & HK & WF & HU). cbn [fst snd] in LR, HK, WF, HU.
      pose proof (HU (sh (qc_blk AL ch')) (qc_bsize ch' / 8) ltac:(right; left; split; reflexivity)) as DH.
      destruct (pchunk_geo AL X m ch' AO RP RS HK) as (B8 & S8 & _).
      destruct WF as (RZ16 & RZM & NR & RZN & _). unfold lc_user, qc_hdr in BA. rewrite BA, BS in RNG.
      destruct LR as [LR|[LR _]]; cbn [fst snd] in LR; [| rewrite LR in RNG; change (Z.of_nat (length (block_shadow 0))) with 0 in RNG; clear - RNG; lia].
      rewrite LR in RNG. rewrite (block_shadow_len (qc_n ch') ltac:(clear - NR; lia)) in RNG.
      replace (qc_blk AL ch' + qc_rz ch' - 16 + 16) with (qc_blk AL ch' + qc_rz ch') in RNG by (clear; lia).
      rewrite (sh_add8 (qc_blk AL ch') (qc_rz ch') B8 ltac:(clear - RZM; Z.div_mod_to_equations; lia)) in RNG.
      eapply dj_narrow; [exact DH| |].
      + clear - RNG RZ16. Z.div_mod_to_equations. lia.
      + unfold rup8 in *. clear - RNG RZN RZM S8 NR. Z.div_mod_to_equations. lia. }
  assert (O : outside W (bv_unsigned (wa a))) by (eapply disjoint_outside; [exact DJ|]; rewrite wa_unsigned by lia; lia).
  split; [exact (GM _ O)| intros Hw; apply WM; exact Hw].
Qed.

Section SW.
Variables (lo q' : Z) (X : pstate) (m : mem) (a n : Z).
Hypothesis LOH : 0x10007fff8000 <= lo.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LQ : lo <= q'.
Hypothesis RP : RPRIM AL (fst X) m.
Hypothesis RS : RSEC AL (snd X) m.
Hypothesis ALO : 0x609000 <= a.
Hypothesis APL : anon_place a (sec_msize (al_sneed n)).
Hypothesis MB : 8192 <= sec_msize (al_sneed n).

#[using="HC AO m LOH CLO LQ RP RS ALO APL MB"] Lemma salloc_iv_facts : forall iv, salloc_iv AL q' lo X a n iv ->
  (0x609000 <= fst iv \/ env_safe [iv]) /\ (forall B k, q' <= B -> disjoint_from [iv] B k)
  /\ (forall A k, 740096 <= A -> A + k <= 1323916 -> disjoint_from [iv] A k).
Proof.
  intros [x y] SI.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. pose proof (@alloc_ceiling_lt47 HC) as C47.
  destruct (clear_ctx AL X m RP RS) as (_ & SOK & _). pose proof RS as (SWF & _). destruct SWF as (W0a & _ & W0b & _).
  destruct APL as [_ ACE].
  layout_facts AO 1%nat LP. destruct LP as ((PL1 & _) & PCE & _).
  layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _ & PL5 & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _ & PL6 & _).
  assert (PLO : 0x609000 <= PARR) by (clear - PL1; lia).
  destruct SI as [AT|[CI|[CI|[CI|[DS|DR]]]]].
  - assert (CZ : czone AL lo q' (snd X) (x, y)) by exact (atouch_czone AL AO X m lo q' [] [] (x, y) RP RS ltac:(constructor) ltac:(intros d []) AT).
    split; [right; exact (czone_env_safe AL AO lo q' (snd X) LOH SOK [(x, y)] ltac:(constructor; [exact CZ| constructor]))|].
    split.
    + intros B k HB. exact (atouch_above AL X m lo q' [(x, y)] [] [] B k AO LOH CLO LQ RP RS ltac:(constructor) ltac:(intros d []) ltac:(constructor; [exact AT| constructor]) HB).
    + intros A k H1 H2. exact (atouch_img_dj AL X m lo q' [(x, y)] [] [] A k AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) ltac:(constructor; [exact AT| constructor])
                                 ltac:(clear - H1; lia) ltac:(clear - H2; lia)).
  - unfold sub_iv in CI. cbn [fst snd] in CI. split; [left; cbn [fst]; clear - CI ALO; lia|].
    split; intros; cbn [disjoint_from]; (split; [| exact I]); [right; clear - CI ACE CLO LQ H; lia| left; clear - CI ALO H0; lia].
  - unfold sub_iv in CI. cbn [fst snd] in CI.
    pose proof (sw_bounds a (sec_msize (al_sneed n)) ALO ltac:(clear - MB; lia)) as (_ & _ & _ & _ & SW5 & _).
    pose proof (sw_range a (sec_msize (al_sneed n)) ALO ltac:(clear - MB; lia) ltac:(clear - ACE C47; lia)) as (SR1 & SR2).
    split; [left; cbn [fst]; clear - CI SW5; lia|].
    split; intros; cbn [disjoint_from]; (split; [| exact I]); [right; clear - CI SR2 LOH LQ H; lia| left; clear - CI SW5 H0; lia].
  - unfold sub_iv in CI. cbn [fst snd] in CI.
    assert (NR0 : 0 <= se_nres (snd X) /\ PARR + 8 * se_nres (snd X) + K_PARR_STEP <= 2^47).
    { clear - W0a W0b PCE ACR. lia. }
    pose proof (sw_bounds (PARR + 8 * se_nres (snd X)) K_PARR_STEP ltac:(clear - PLO NR0; lia) ltac:(clear; lia)) as (_ & _ & _ & _ & SW5 & _).
    pose proof (sw_range (PARR + 8 * se_nres (snd X)) K_PARR_STEP ltac:(clear - PLO NR0; lia) ltac:(clear; lia) ltac:(clear - NR0; lia)) as (SR1 & SR2).
    split; [left; cbn [fst]; clear - CI SW5; lia|].
    split; intros; cbn [disjoint_from]; (split; [| exact I]); [right; clear - CI SR2 LOH LQ H; lia| left; clear - CI SW5 H0; lia].
  - assert (CZ : czone AL lo q' (snd X) (x, y)) by (right; right; left; exact DS).
    split; [right; exact (czone_env_safe AL AO lo q' (snd X) LOH SOK [(x, y)] ltac:(constructor; [exact CZ| constructor]))|].
    unfold dstat in DS. cbn [fst snd] in DS.
    split; intros; cbn [disjoint_from]; (split; [| exact I]); [right; clear - DS LOH LQ H; lia| left; clear - DS H0; lia].
  - assert (CZ : czone AL lo q' (snd X) (x, y)) by (do 8 right; left; exact DR).
    split; [right; exact (czone_env_safe AL AO lo q' (snd X) LOH SOK [(x, y)] ltac:(constructor; [exact CZ| constructor]))|].
    unfold dreg in DR. cbn [fst snd] in DR.
    split; intros; cbn [disjoint_from]; (split; [| exact I]); [right; clear - DR N2d S2d CLO LQ H; lia|].
    destruct DR as [DR|DR]; [clear - DR PL5 H H0; lia| clear - DR PL6 H H0; lia].
Qed.
End SW.

#[using="Type"] Lemma dj_of_each : forall (W : list (Z * Z)) A k, (forall iv, In iv W -> disjoint_from [iv] A k) -> disjoint_from W A k.
Proof.
  induction W as [|[x y] W IH]; intros A k H; cbn [disjoint_from]; [exact I|].
  split; [exact (proj1 (H (x, y) (or_introl eq_refl)))| apply IH; intros iv Hiv; apply H; right; exact Hiv].
Qed.

#[using="Type"] Lemma fclass_stouch : forall lo q0 X a msz iv, fclass AL lo q0 iv -> stouch AL lo q0 X a msz iv.
Proof.
  intros lo q0 X a msz iv [S1|[IA|[UB|TS]]].
  - left. left. exact S1.
  - do 5 right. left. exact IA.
  - do 6 right. exact UB.
  - left. right. right. left. unfold sub_iv in *. lia.
Qed.

#[using="AO SWIN_LO FSBE STAT"] Lemma alloc_sec_L8 : forall s LB (st : fsstate FI) n tr q0 lo (avoid : list (Z * Z)) alo ahi,
  alloc_ceiling <= lo -> In tr A0_TRACES -> 0 <= n <= A0_MAXREQ -> 65536 < a0_need n ->
  In (alo, ahi) avoid -> alo <= lo -> q0 <= ahi ->
  Forall (fun rg : Z * Z => In (fst rg, fst rg + snd rg) avoid) (al_regions AL) ->
  Forall (fun c => In (sc_beg c, sc_beg c + sc_msize c) avoid) (se_chunks (bs_sec s)) ->
  se_n (bs_sec s) < K_MAX_CHUNKS ->
  sec_live_cnt s + 1 <= A0_SEC_CNT -> sec_live_bytes s + n <= A0_SEC_BYTES -> bs_nsec s + 1 <= A0_NSEC_MAX ->
  al8_stmt AL E FI AI (sec_alloc_tree AL (bs_sec s) (al_sneed n) avoid) (fun a : Z => (bs_prim s, sec_alloc (bs_sec s) a (al_sneed n))) 1 ALLOC_STACK s LB st n tr q0 lo.
Proof.
  intros s LB st n tr q0 lo avoid alo ahi CLO TRIN NR NS AIN ALOW AHI AREG ACH WMAX BC BB BN. unfold al8_stmt.
  intros gp F_ fc q' ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m0 mS FT0 STK TR ws
         HR MI AE RF MU0 WM0 FC0 MC ST INVS AENVS TE2S HKES RDS IAS SOBJ QSTK STKH BUF TRW LENW QTR TRH LOQ QQ0 Q0H Q16.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
  destruct (traces_rng tr TRIN) as [LTR RNG].
  assert (DOK0 : depot_ok (bs_depot0 s) (bs_depot s) (bs_dtotal s)) by (destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DOK & _); exact DOK).
  destruct (depot_room AL _ _ _ tr DOK0 ltac:(clear - LTR; lia) SWIN_LO) as (RN & RFo & RT).
  assert (AS : 128 <= ALLOC_STACK) by (vm_compute; discriminate).
  eapply implA_mono.
  - eapply (allocate_sec_spec AL E AO gp F_ fc q' lo LOH CLO LOQ ltac:(clear - QQ0 Q0H; lia) Q16
              ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (bs_X s) (bs_H s) mS n (bs_gl s) (flat_map qb_chunks (bs_gl s)) (heldB s)
              STK TR (bs_dtotal s) (bs_depot s) ws tr avoid alo ahi);
      [ exact MC | exact ST | exact INVS | exact NR | exact NS | exact AIN | exact ALOW | clear - AHI QQ0; lia | exact AREG | exact ACH | exact WMAX
      | exact AENVS | exact TE2S | exact HKES | exact RDS
      | exact SOBJ | exact QSTK | exact STKH | exact BUF | exact TRW | exact LENW | exact LTR | exact RNG | exact QTR | exact TRH | exact RN | exact RFo | exact RT ].
  - intros a H' ms' PO. unfold allocate_post_s in PO. cbv zeta in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & W & Wg & hs' & total' & EMS & EH & MU2 & WM2 & FW2 & GM2 & FWg & INV' & WFC & HKN & LREP
                    & STK' & ECH & ESN & COK & A4K & ALO & AM & APL & AVD & SLK0 & CLS0 & RD' & DEP).
    assert (LQ : lo <= q0) by (clear - LOQ QQ0 AS; lia). assert (LQ' : lo <= q') by (clear - LOQ AS; lia).
    set (X := bs_X s) in *. set (ch := al_chunk_s a n) in *. set (sc := al_schunk a n) in *.
    set (S' := sec_alloc (snd X) a (al_sneed n)) in *. set (msz := sec_msize (al_sneed n)) in *.
    assert (EK : qc_kind ch = QSec sc) by reflexivity.
    destruct (al_sec_facts n NR NS) as (N1 & EALN & ERZ & _ & _ & ECLS & _).
    assert (SN0 : 0 < al_sneed n) by (unfold al_sneed; rewrite ERZ; clear - NS; lia).
    assert (MB : 8192 <= msz /\ msz mod 4096 = 0) by (unfold msz, sec_msize, rup4k; clear - SN0; Z.div_mod_to_equations; lia).
    destruct MB as (MB & MB4K).
    assert (AVD' : Forall (fun iv => a + msz <= fst iv \/ snd iv <= a) avoid) by exact AVD.
    pose proof HR as (PLB & LOK & AOx & INVB & QLG & GC & (TQC & QLL) & MTX & (CST & AFM) & QWF & RD & DOK & WFL & REPL & HKL & PSEC & COV & TE2 & HKE & (TR1 & TR2 & TR3) & AENV & _ & CCL & CCQ & SLK & BUD & FTE).
    pose proof (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI) as INV. pose proof INV as (RP & _ & RS & _ & _ & _ & _ & _ & _ & _ & HOK & _).
    pose proof INV' as (RP' & _ & RS' & MI' & _).
    destruct (clear_ctx AL X m0 RP RS) as (_ & SOK & _).
    destruct (clear_ctx AL (fst X, S') m1 RP' RS') as (_ & SOK' & _). cbn [snd] in SOK'.
    assert (ACH' : Forall (fun c => In (sc_beg c, sc_beg c + sc_msize c) avoid) (se_chunks (snd X))) by exact ACH.

    set (FT := FT0 ++ Wg).
    assert (GMT : gmunch FT m0 m1) by (unfold FT; exact (gmunch_join _ _ m0 mS m1 (gmunch_of_munch _ _ _ MU0) GM2)).
    pose proof (wmono_trans asegs _ _ _ WM0 WM2) as WMT.
    assert (GMW : gmw FT m0 m1) by (split; assumption).
    assert (FTC : Forall (stouch AL lo q0 X a msz) FT).
    { unfold FT. apply Forall_app. split.
      - eapply Forall_impl; [| exact FC0]. intros iv FCx. exact (fclass_stouch lo q0 X a msz iv FCx).
      - eapply Forall_impl; [| exact FWg]. intros iv [AT|[CI|[CI|[DS|DR]]]].
        + left. eapply (atouch_mono AL lo q0 (fst X) (snd X) _ _ lo q' (fst X) (snd X) _ _); [lia| lia| intros; lia| apply incl_refl| apply incl_refl| apply incl_refl| exact AT].
        + right; left; exact CI.
        + right; right; left; exact CI.
        + right; right; right; left; exact DS.
        + right; right; right; right; left; exact DR. }
    assert (FTZ : Forall (czone AL lo q0 S') FT).
    { eapply Forall_impl; [| exact FTC]. intros iv MT. exact (stouch_czone AL AO lo q0 X m0 a msz RP RS S' sc iv ECH eq_refl eq_refl MT). }
    pose proof (fun W1 A k => stouch_img_dj AL AO lo q0 X m0 a msz LOH CLO RP RS A4K ALO APL MB4K W1 A k) as IMGD.
    pose proof (fun A k => stouch_thr_dj AL AO lo q0 X m0 a msz avoid LOH CLO RP RS A4K ALO APL MB4K AVD' AREG FT A k FTC) as THRD.
    assert (HULL : forall ch', held_kind X ch' -> forall A k, qc_hull AL ch' A k -> disjoint_from FT A k).
    { intros ch' HK' A k HU. apply dj_of_Forall. eapply Forall_impl; [| exact FTC]. intros iv MT.
      pose proof (hull_stouch_dj AL AO lo q0 X m0 a msz avoid LOH CLO RP RS A4K ALO APL MB MB4K AVD' AREG ACH' ch' iv A k HK' MT HU) as DD.
      destruct iv as [x y]. cbn [disjoint_from] in DD. exact (proj1 DD). }
    destruct (malloc_sec_budget AL E s LB m0 a (al_sneed n) ch n H' hs' total' HR ltac:(destruct RS' as (SWF' & _); exact SWF') EK BC BB BN) as [PI1 BUD']. cbv zeta in PI1, BUD'.
    pose proof LREP as (_ & _ & (ub & UB) & _ & _ & SHU & _). cbv zeta in UB, SHU.
    assert (ENQ : qc_n ch = n) by (unfold ch, al_chunk_s; cbn [qc_n]; exact EALN).
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m1,
           (mkASB H' (bs_pages s) (bs_prim s) S' (bs_quar s) hs' total' (bs_nsec s + 1) ((ch, n) :: bs_live s) (bs_depot0 s)),
           (qc_hdr AL ch + 16), ub, W.
    split; [exact EMS|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exists ch; split; reflexivity|].
    split; [exact MI'|]. split; [exact STK'|].
    assert (SWF : forall iv, In iv W -> (0x609000 <= fst iv \/ env_safe [iv]) /\ (forall B k, q' <= B -> disjoint_from [iv] B k)
                                         /\ (forall A k, 740096 <= A -> A + k <= 1323916 -> disjoint_from [iv] A k)).
    { intros iv Hiv. pose proof INVS as (RPS & _ & RSS & _).
      exact (salloc_iv_facts lo q' X mS a n LOH CLO LQ' RPS RSS ALO APL MB iv (proj1 (Forall_forall _ _) FW2 iv Hiv)). }
    split.
    {
      eapply (asan_env_frame_m asegs m0 m1 (FT0 ++ W) AE (munch_joinP _ _ m0 mS m1 MU0 MU2)).
      unfold env_safe. apply Forall_app. split.
      - assert (ES0 : env_safe FT0).
        { apply (czone_env_safe AL AO lo q0 S' LOH SOK'). eapply Forall_impl; [| exact FC0]. intros iv FCx.
          exact (stouch_czone AL AO lo q0 X m0 a msz RP RS S' sc iv ECH eq_refl eq_refl (fclass_stouch lo q0 X a msz iv FCx)). }
        exact ES0.
      - apply Forall_forall. intros iv Hiv. destruct (SWF iv Hiv) as ([E1|E1] & _); [left; exact E1|].
        unfold env_safe in E1. apply Forall_cons_iff in E1 as [E1 _]. exact E1. }
    split.
    { eapply (rfake_frame_g FI st m0 m1 _ RF GMT WMT). eapply Forall_impl; [| exact FTZ]. intros iv CZ. left. rewrite FSBE.
      exact (czone_fs_dj AL AO lo q0 S' LOH CLO SOK' iv CZ). }
    split.
    { intros LBk HB. apply (apres_of_czone_g lo q0 X S' m0 m1 FT (bs_live s) LBk LOH CLO RP RS SOK' GMT WMT FTZ); [| exact HB|].
      - intros A k HA. exact (stouch_above AL AO lo q0 X m0 a msz LOH CLO RP RS A4K ALO APL MB4K FT A k LQ FTC HA).
      - intros r0 Hr. assert (INC : In (fst r0) (live_chunks s)) by (unfold live_chunks; apply in_map; exact Hr).
        split; [exact (proj1 (Forall_forall _ _) LOK r0 Hr)|]. split; [exact (proj1 (Forall_forall _ _) HKL _ INC)|].
        split; [exact (proj1 (Forall_forall _ _) WFL _ INC)|]. exact (HULL _ (proj1 (Forall_forall _ _) HKL _ INC)). }
    split.
    { intros r0 B cs Hr HB1 HB2 CS. assert (INC : In (fst r0) (live_chunks s)) by (unfold live_chunks; apply in_map; exact Hr).
      eapply rw_cells_gtransport; [exact CS| exact GMT| exact WMT|].
      eapply disjoint_from_sub; [exact (HULL _ (proj1 (Forall_forall _ _) HKL _ INC) _ _ ltac:(left; split; reflexivity))| exact HB1| exact HB2]. }
    split.
    {
      unfold RHEAP_B. cbv zeta. unfold bs_X, bs_gl, live_chunks, heldB. cbn [bs_H bs_prim bs_sec bs_quar bs_depot bs_dtotal bs_live bs_depot0 q_glob q_loc map flat_map fst].
      split; [apply perm_skip; exact PLB|].
      split; [constructor; [unfold lr_ok; cbn [fst snd]; left; symmetry; exact ENQ| exact LOK]|].
      split; [exact AO|].
      split; [exact (proj1 (dr_invB_of AL E _ _ _ _ _ _ INV'))|].
      assert (HBP : forall b, In b (bs_gl s) -> held1 (fst X) (bpair b)).
      { intros b Hb. destruct HOK as [_ FH]. apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb. }
      assert (QLF : forall l, incl l (bs_gl s) -> qlist_rep AL m0 l 0 -> qlist_rep AL m1 l 0).
      { intros l INC QL. apply (qlist_rep_hull_g AL FT m0 m1 l 0 GMW QL). apply Forall_forall. intros b Hb. pose proof (HBP b (INC b Hb)) as HB1.
        split; [exact (HULL (mkQC (QPrim K_BCLASS (qb_v b)) 16 1) HB1 _ _ ltac:(left; split; reflexivity))
               | exact (HULL (mkQC (QPrim K_BCLASS (qb_v b)) 16 1) HB1 _ _ ltac:(right; left; split; reflexivity))]. }
      split; [apply QLF; [unfold bs_gl; intros b Hb; apply in_or_app; left; exact Hb| exact QLG]|].
      split; [eapply rw_cells_gtransport; [exact GC| exact GMT| exact WMT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add qcells]; clear; lia]]|].
      split.
      { split; [eapply rw_cells_gtransport; [exact TQC| exact GMT| exact WMT| apply THRD; cbn [cells_size csize Nat.add]; clear; lia]|].
        apply QLF; [unfold bs_gl; intros b Hb; apply in_or_app; right; exact Hb| exact QLL]. }
      split; [eapply rw_cells_gtransport; [exact MTX| exact GMT| exact WMT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]]|].
      split; [split; (eapply rw_cells_gtransport; [eassumption| exact GMT| exact WMT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]])|].
      split; [exact QWF|]. split; [exact RD'|].
      split; [exact (depot_ok_step _ _ _ tr hs' total' DOK TRIN ltac:(clear - LTR; lia) DEP)|].
      split; [constructor; [exact WFC| exact WFL]|].
      split.
      { constructor; [exact LREP|]. apply Forall_forall. intros ch' Hch'. pose proof (proj1 (Forall_forall _ _) HKL ch' Hch') as HK'.
        exact (lchunk_rep_hull_g AL AO X FT m0 m1 ch' AO RP RS HK' (proj1 (Forall_forall _ _) REPL ch' Hch') (proj1 (Forall_forall _ _) WFL ch' Hch') GMT WMT (HULL ch' HK')). }
      split.
      { constructor; [exact HKN|]. apply Forall_forall. intros ch' Hch'. pose proof (proj1 (Forall_forall _ _) HKL ch' Hch') as HK'.
        unfold held_kind in *. destruct (qc_kind ch') as [c' v'|sc'] eqn:EK'; [exact HK'|]. cbn [snd]. unfold S', sec_alloc. cbn [se_chunks]. apply in_or_app. left. exact HK'. }
      pose proof PI1 as (_ & _ & COV' & _ & _ & _ & PSEC').
      split; [exact PSEC'|]. split; [exact COV'|].
      split.
      { destruct TE2 as (C1t & tid & C2t). split; [| exists tid].
        - eapply rw_cells_gtransport; [exact C1t| exact GMT| exact WMT| apply THRD; cbn [cells_size csize Nat.add]; left; clear; lia].
        - eapply rw_cells_gtransport; [exact C2t| exact GMT| exact WMT| apply THRD; cbn [cells_size csize Nat.add]; right; left; clear; lia]. }
      split; [unfold hooks_env in *; eapply rw_cells_gtransport; [exact HKE| exact GMT| exact WMT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]]|].
      split; [unfold trace_env; split; [| split]; (eapply rw_cells_gtransport; [eassumption| exact GMT| exact WMT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]])|].
      split; [ae_split AENV; unfold alloc_env; repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_gtransport; [eassumption| exact GMT| exact WMT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]])|].
      split.
      {
        destruct IAS as (inited & IA). exists inited. apply (ia_cells_band mS m1 inited); [| exact IA].
        intros A cs C0 H1 H2. eapply rw_cells_transport_m; [exact C0| exact MU2|].
        apply dj_of_each. intros iv Hiv. exact (proj2 (proj2 (SWF iv Hiv)) A _ H1 H2). }
      split.
      { constructor; [| exact CCL]. unfold ch_cls_ok. rewrite EK, ENQ. split; [exact ECLS|].
        unfold sc, al_schunk. cbn [sc_msize]. destruct (al_sec_facts n NR NS) as (_ & _ & _ & _ & _ & _ & (rk & NEED & RK & _)).
        unfold sec_msize, rup4k, al_sneed. rewrite ERZ, NEED. clear - RK. Z.div_mod_to_equations. lia. }
      split; [exact CCQ|]. split; [constructor; [unfold sec_slack_ok; rewrite EK; exact SLK0| exact SLK]|]. split; [exact BUD'|].
      exact (fs_tls_env_frame_g _ _ _ _ _ FT m0 m1 FTE GMT WMT (stouch_fte AL AO lo q0 X m0 a msz avoid LOH CLO RP RS A4K ALO APL MB4K AVD' AREG FT FTC)). }
    split; [rewrite ENQ in UB; exact UB|].
    split; [rewrite ENQ in SHU; exact SHU|].
    split; [exact WMT|].
    split; [exact MU2|].
    intros B k HB. apply dj_of_each. intros iv Hiv. exact (proj1 (proj2 (SWF iv Hiv)) B k HB).
Qed.

End ASL8.
