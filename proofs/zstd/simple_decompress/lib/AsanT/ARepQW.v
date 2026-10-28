(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes AQConst AModelFacts ARep ALayout AHeapP ARepKit ARepFrame ARepExt AFreeGeo AFreeStore AFreeStoreK ARefillP ARecGeo AInstanceF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition qwp (L : alayout) (X : aconc) (iv : Z * Z) : Prop :=
  fst iv < snd iv ->
     ATOP <= fst iv
  \/ (AQ_MUTEX <= fst iv /\ snd iv <= AQ_GCACHE + 32)
  \/ (exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_alloc L b <= fst iv /\ snd iv <= xb_alloc L b + size_of_class (xb_class b)).

Section K.
Variables (L : alayout) (st : astate) (X : aconc) (W : list (Z * Z)).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis QW : Forall (qwp L X) W.
Let W' := List.filter nonempty W.

Lemma qw_clear : forall A k, 0 <= k ->
  (   (0 <= A /\ A + k <= 2201439137792 /\ (A + k <= AQ_MUTEX \/ AQ_GCACHE + 32 <= A))
   \/ (2201439137792 <= A /\ A + k <= 17594333495296)
   \/ (17594333495296 <= A /\ A + k <= ATOP /\ (A + k <= al_res L \/ al_res L + 137439023104 <= A))
   \/ (al_res L <= A /\ A + k <= ATOP /\ (forall b, In b (x_busy X) -> xb_st b = BBatch -> A + k <= xb_alloc L b \/ xb_alloc L b + size_of_class (xb_class b) <= A))) ->
  disjoint_from W' A k.
Proof.
  intros A k Hk KIND. apply disjoint_from_Forall. subst W'.
  pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_res_hi L ALO) as ORH.   (* [comment removed for export] *)
  revert QW. generalize W. intros W0 QW0.
  induction W0 as [|[lo hi] W0 IH]; [constructor|].
  inversion QW0 as [| x l E1 E2]; subst.
  rewrite filter_cons_eq. unfold nonempty at 1. cbn [fst snd].
  destruct (Z.ltb_spec lo hi) as [LT|GE]; [| apply IH; exact E2].
  constructor; [| apply IH; exact E2]. cbn [fst snd].
  unfold qwp in E1. cbn [fst snd] in E1. specialize (E1 LT). unfold AQ_MUTEX, AQ_GCACHE in *.
  destruct E1 as [E|[E|(b & Hb & Sb & B1 & B2)]].
  - clear -E KIND Hk ORS ORH. lia.
  - clear -E KIND Hk ORS ORH. lia.
  - pose proof (busy_slot_geo L st X ALO WF b Hb) as (_ & _ & _ & _ & _ & G4 & G5 & G6 & G7). atop_facts.
    destruct KIND as [K|[K|[K|(K1 & K2 & K3)]]]; [clear -K B1 B2 G4; lia| clear -K B1 B2 G4; lia| clear -K B1 B2 G6 G7; lia|].
    destruct (K3 b Hb Sb) as [D|D]; clear -D B1 B2 LT; lia.   (* [comment removed for export] *)
Qed.
End K.

Section QW.
Variables (AQ AS : alayout -> astate -> aconc -> amem -> Prop) (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop).
Let H := mkAHoles AQ AS AD AF.
Hypothesis HL : ahole_laws H.

Theorem AREP_frame_qw : forall (AQ' : alayout -> astate -> aconc -> amem -> Prop) L st X m m' W,
  alayout_ok L -> AREP H L st X m -> munch W m m' -> wmono bsegs m m' ->
  Forall (qwp L X) W ->
  AQ' L st X m' ->
  AREP (mkAHoles AQ' AS AD AF) L st X m'.
Proof.
  intros AQ' L st X m m' W ALO AR MU0 WM QWP HQ'.
  pose proof (munch_filter_nonempty W m m' MU0) as MU. clear MU0. set (W' := List.filter nonempty W) in *.
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot] in HQ, HS, HD.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  (* [comment removed for export] *)
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (ao_fake L ALO) as OF. pose proof (ao_res_hi L ALO) as ORH. pose proof (aobj_img _ _ OC ltac:(clear; lia)) as OCI.
  unfold aobj in OT, OC, ORS, ON, OS, OF. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, OC, ON, OS. unfold AIMG_HI in OCI.   (* [comment removed for export] *)
  pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  unfold adisj in D_t_res, D_c_res, D_n_res, D_s_res.
  pose proof (fun A k => qw_clear L st X W ALO WF QWP A k) as KX. cbn beta in KX. fold W' in KX.
  (* [comment removed for export] *)
  assert (Kimg : forall A k, 0 <= A -> 0 <= k -> A + k <= AIMG_HI -> (A + k <= AQ_MUTEX \/ AQ_GCACHE + 32 <= A) -> disjoint_from W' A k).
  { intros A k H1 H2 H3 H4. apply KX; [exact H2|]. left. unfold AIMG_HI in H3. clear -H1 H3 H4. lia. }
  assert (Ksh : forall A k, 2201439137792 <= A -> A + k <= 17594333495296 -> 0 <= k -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply KX; [exact H3|]. right; left. clear -H1 H2. lia. }
  assert (Kobj : forall A k, 0 <= A -> 0 <= k -> A + k <= ATOP -> (A + k <= 2147446784 \/ 17594333495296 <= A) ->      (* [comment removed for export] *)
                 (A + k <= AQ_MUTEX \/ AQ_GCACHE + 32 <= A) -> (A + k <= al_res L \/ al_res L + 137439023104 <= A) -> disjoint_from W' A k).
  { intros A k H0 H2 H3 HB H4 H5. apply KX; [exact H2|]. destruct HB as [HB|HB].
    - left. split; [exact H0|]. split; [clear -HB; lia| exact H4].
    - right; right; left. clear -HB H3 H5. lia. }
  assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= ATOP ->
            (forall b, In b (x_busy X) -> xb_st b = BBatch -> A + k <= xb_alloc L b \/ xb_alloc L b + size_of_class (xb_class b) <= A) -> disjoint_from W' A k).
  { intros A k H1 H2 H3 H4. apply KX; [exact H2|]. right; right; right. split; [exact H1| split; [exact H3| exact H4]]. }
  clear KX.
  assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [clear -H1 OT; lia | exact H2 | clear -H3 OT; lia | clear -H1 H3 OT; lia | unfold AQ_MUTEX, AQ_GCACHE; clear -H1 H3 OT; lia | clear -H1 H3 D_t_res; lia]. }
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [clear -H1 OC; lia | exact H2 | clear -H3 OC; lia | clear -H1 H3 OC; lia | unfold AQ_MUTEX, AQ_GCACHE; clear -H1 OCI; lia | clear -H1 H3 D_c_res; lia]. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) -> xb_st b = BBatch ->
             aregion L (xb_class b) <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= aregion L (xb_class b) + c_allocated_user (get_cls st (xb_class b))
          /\ c_allocated_user (get_cls st (xb_class b)) <= c_mapped_user (get_cls st (xb_class b)) <= K_FREEARR_OFF
          /\ aregion L (xb_class b) + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ 1 <= xb_class b < K_NUM_CLASSES /\ 0 <= xb_slot b < ndist st (xb_class b)).
  { intros b Hb _. pose proof (busy_slot_geo L st X ALO WF b Hb) as (CLB & KB & G1 & G2 & (G3a & G3 & G3b) & _).
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G3b| exact (conj CLB KB)]. }
  (* [comment removed for export] *)
  split; [exact WF|].
  split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI, AQ_MUTEX, AQ_GCACHE; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI, AQ_MUTEX, AQ_GCACHE; lia. }
  split.
  { destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW). unfold athread.
    split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
             unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
    split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
    split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
    eapply cells_frame; [exact UNW | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]. }
  split.
  { intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. pose proof Hc as Hc0. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    (* [comment removed for export] *)
    assert (BBR : forall b, In b (x_busy X) -> xb_st b = BBatch -> forall A k,
               ((aregion L c + c_allocated_user (get_cls st c) <= A /\ A + k <= aregion L c + K_REGION) \/ (al_space_beg L + K_SPACE_SIZE <= A)) ->
               A + k <= xb_alloc L b \/ xb_alloc L b + size_of_class (xb_class b) <= A).
    { intros b Hb Sb A k HA. destruct (BB b Hb Sb) as (G1 & G2 & G3 & G3b & CLB & KB).
      destruct HA as [(HA1 & HA2)|HA].
      - destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
        + right. rewrite EC in G2 |- *. clear -G2 HA1. lia.
        + pose proof (region_other_geo L c (xb_class b) ALO Hc ltac:(unfold K_NUM_CLASSES in CLB; exact CLB) NC) as (_ & RD & _).
          unfold K_REGION, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. clear -G1 G2 G3 RD HA1 HA2 Q1. lia.
      - right. unfold K_REGION, K_SPACE_SIZE, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *. clear -G2 G3 G3b HA. lia. }
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply Kres; [unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia| clear; lia
                  | unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *; change (2^37) with 137438953472 in *; clear -Hc RSP ORS ORH; lia|].
      intros b Hb Sb. apply (BBR b Hb Sb). right. unfold aregion_info, ARI_STRIDE. clear -Hc. lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6 ORS ORH; lia |].
        intros b Hb Sb. apply (BBR b Hb Sb). left. unfold K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, afreearr in *. change (2^32) with 4294967296. clear -Q1 Q2 Q5 Q6. lia.
      + apply Ksh; [| | apply shlen_nonneg; clear -Q5 Q6; lia].
        * rewrite shad_div. unfold afreearr, K_FREEARR_OFF, ASHOFF. clear -RI1 ORS ORH. Z.div_mod_to_equations. lia.
        * rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia).
          rewrite shad_div. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, ASHOFF in *. clear -RI2 RI3 Q6 ORS ORH. Z.div_mod_to_equations. lia.
    - eapply (aslots_update_gen L W' m m' MU WM st st X X c); [exact SLOTS | reflexivity | reflexivity | reflexivity | |].
      + intros k Hk. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        destruct (busy_of X c k) as [b0|] eqn:EBK.
        * destruct (busy_of_Some_facts X c k b0 EBK) as (Hb0 & Cb0 & Kb0).
          destruct (xb_st b0) eqn:ES0.
          -- left. split; [reflexivity|]. split.
             ++ apply Kres; [clear -P5 RI1; lia | clear -QS; lia | atop_facts; clear -P4 Q1 Q2 RI2 RI3 ORS ORH; unfold K_FREEARR_OFF in *; lia|].
                intros b Hb Sb. destruct (BB b Hb Sb) as (_ & _ & _ & _ & CLB & KB).
                assert (NEQ : c <> xb_class b \/ k <> xb_slot b).
                { destruct (Z.eq_dec c (xb_class b)) as [EC|NC]; [right| left; exact NC]. intros EK.
                  pose proof (AFreeStore.busy_of_In_nodup L st X b WF Hb) as E. rewrite <- EC, <- EK, EBK in E. injection E as E. subst b0. congruence. }
                pose proof (slots_sep_any L st X c k (xb_class b) (xb_slot b) ALO WF Hc0 CLB Hk KB NEQ) as D. unfold xb_alloc. clear -D. lia.
             ++ intros b Hb. injection Hb as <-. split; [exact Cb0|]. split; [exact Kb0| exact (awf_fits L st X b0 WF Hb0)].
          -- left. split; [reflexivity|]. split.
             ++ apply Kres; [clear -P5 RI1; lia | clear -QS; lia | atop_facts; clear -P4 Q1 Q2 RI2 RI3 ORS ORH; unfold K_FREEARR_OFF in *; lia|].
                intros b Hb Sb. destruct (BB b Hb Sb) as (_ & _ & _ & _ & CLB & KB).
                assert (NEQ : c <> xb_class b \/ k <> xb_slot b).
                { destruct (Z.eq_dec c (xb_class b)) as [EC|NC]; [right| left; exact NC]. intros EK.
                  pose proof (AFreeStore.busy_of_In_nodup L st X b WF Hb) as E. rewrite <- EC, <- EK, EBK in E. injection E as E. subst b0. congruence. }
                pose proof (slots_sep_any L st X c k (xb_class b) (xb_slot b) ALO WF Hc0 CLB Hk KB NEQ) as D. unfold xb_alloc. clear -D. lia.
             ++ intros b Hb. injection Hb as <-. split; [exact Cb0|]. split; [exact Kb0| exact (awf_fits L st X b0 WF Hb0)].
          -- (* [comment removed for export] *)
             right. pose proof (proj1 SLOTS k Hk) as SB. rewrite EBK in SB. unfold aslot_busy in SB |- *. rewrite ES0 in SB |- *.
             eapply junk_any; [exact SB| exact WM|]. unfold xb_alloc. pose proof (busy_slot_geo L st X ALO WF b0 Hb0) as (_ & _ & _ & _ & _ & G4 & _). unfold xb_alloc in G4. clear -G4. lia.
        * left. split; [reflexivity|]. split; [| intros b Hb; discriminate].
          apply Kres; [clear -P5 RI1; lia | clear -QS; lia | atop_facts; clear -P4 Q1 Q2 RI2 RI3 ORS ORH; unfold K_FREEARR_OFF in *; lia|].
          intros b Hb Sb. destruct (BB b Hb Sb) as (_ & _ & _ & _ & CLB & KB).
          assert (NEQ : c <> xb_class b \/ k <> xb_slot b).
          { destruct (Z.eq_dec c (xb_class b)) as [EC|NC]; [right| left; exact NC]. intros EK.
            pose proof (AFreeStore.busy_of_In_nodup L st X b WF Hb) as E. rewrite <- EC, <- EK, EBK in E. discriminate. }
          pose proof (slots_sep_any L st X c k (xb_class b) (xb_slot b) ALO WF Hc0 CLB Hk KB NEQ) as D. unfold xb_alloc. clear -D. lia.
      + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | atop_facts; clear -Q1 Q2 RI2 RI3 ORS ORH; unfold K_FREEARR_OFF in *; lia|].
        intros b Hb Sb. apply (BBR b Hb Sb). left. unfold K_REGION, K_FREEARR_OFF in *. change (2^32) with 4294967296. clear -Q1 Q2 POS. lia.
    - eapply (aslot_shadow_update_gen L W' m m' MU WM st st X X c); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | apply shlen_nonneg; clear -QS; lia].
      + intros k Hk. left. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply Ksh; [| | apply shlen_nonneg; clear -QS; lia].
        * rewrite shad_div. unfold ASHOFF. clear -P5 RI1 ORS ORH. Z.div_mod_to_equations. lia.
        * rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -P4 Q1 Q2 RI2 RI3 ORS ORH. Z.div_mod_to_equations. lia.
      + intros POS. apply Ksh; [| | clear -POS; lia].
        * rewrite shad_div. unfold ASHOFF. clear -Q1 RI1 ORS ORH. Z.div_mod_to_equations. lia.
        * rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
          rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -Q1 Q2 RI2 RI3 ORS ORH. Z.div_mod_to_equations. lia. }
  split; [exact HQ'|].
  split.
  { eapply (hs_frame _ HL L st st X X m m' W'); [exact HS | exact MU | exact WM | | apply sec_same_refl].
    unfold sec_untouched, aknown. apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
    unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
    pose proof (proj1 (Forall_forall _ _) QWP _ Hin) as E. unfold qwp in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)).
    unfold AQ_MUTEX, AQ_GCACHE, AINSTANCE in *.
    destruct E as [E|[E|(b & Hb & Sb & B1 & B2)]].
    - do 4 right. left. clear -E Ha. lia.
    - left. left. unfold AIMG_HI. clear -E Ha. lia.   (* [comment removed for export] *)
    - pose proof (busy_slot_geo L st X ALO WF b Hb) as (_ & _ & _ & _ & _ & _ & _ & G6 & G7). do 7 right. left. clear -Ha B1 B2 G6 G7. lia. }
  split.
  { eapply (hd_frame _ HL L m m' W'); [exact HD | exact MU | exact WM |].
    apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
    unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
    pose proof (proj1 (Forall_forall _ _) QWP _ Hin) as E. unfold qwp in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)).
    unfold AQ_MUTEX, AQ_GCACHE in *.
    destruct E as [E|[E|(b & Hb & Sb & B1 & B2)]]; [clear -E Ha ON OS; lia| clear -E Ha ON OS; lia|].
    pose proof (busy_slot_geo L st X ALO WF b Hb) as (_ & _ & _ & _ & _ & _ & _ & G6 & G7). clear -Ha B1 B2 G6 G7 ON OS ORS ORH D_n_res D_s_res. lia. }
  split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AQ_MUTEX, AQ_GCACHE; lia]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI, AQ_MUTEX, AQ_GCACHE; lia|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
            repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI, AQ_MUTEX, AQ_GCACHE; lia |]); apply Forall_nil].
  intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
               /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
  { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
  destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
  eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
  - intros POS. apply Ksh; [| | clear -POS; lia].
    + rewrite shad_div. unfold ASHOFF, aregion in *. clear -Q1 RI1 ORS ORH. Z.div_mod_to_equations. lia.
    + rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
      rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -Q1 Q2 RI2 RI3 ORS ORH. Z.div_mod_to_equations. lia.
  - intros POS. apply Ksh; [| | clear -POS; lia].
    + rewrite shad_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, aregion in *. clear -Q5 Q6 RI1 ORS ORH. Z.div_mod_to_equations. lia.
    + rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
      rewrite shad_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -Q5 Q6 RI2 RI3 ORS ORH. Z.div_mod_to_equations. lia.
Qed.
End QW.
End CANSEC1.
