(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl KLedger JLedger
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_Joint1 MI_Joint2.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Record JF (J J' : jled) : Prop := mkJF {
  jf_resvG : j_resvG J' = j_resvG J;
  jf_resvC : j_resvC J' = j_resvC J;
  jf_groups : j_groups J' = j_groups J;
  jf_live : j_live J' = j_live J
}.
Lemma jf_refl J : JF J J. Proof. constructor; reflexivity. Qed.
Lemma jf_trans a b c : JF a b -> JF b c -> JF a c.
Proof. intros [A1 A2 A3 A4] [B1 B2 B3 B4]; constructor; congruence. Qed.

Lemma lf_of_projG J J' : JF J J' -> L_frame (projG J) (projG J').
Proof. intros [A1 A2 A3 A4]. constructor; cbn; rewrite ?A1, ?A3, ?A4; reflexivity. Qed.
Lemma lf_of_projC J J' : JF J J' -> L_frame (projC J) (projC J').
Proof. intros [A1 A2 A3 A4]. constructor; cbn; rewrite ?A2, ?A3, ?A4; reflexivity. Qed.

Lemma strip_carve_rest s p : carve_rest (strip s) p = strip (carve_rest s p).
Proof. unfold carve_rest. rewrite !ctx_strip, !s_areas_strip. destruct (c_meta_area_tail (ctx s)); reflexivity. Qed.
Lemma rebase_carve_rest rho resv ceil s p : carve_rest (rebase rho resv ceil s) p = rebase rho resv ceil (carve_rest s p).
Proof. unfold carve_rest. rewrite !ctx_rebase, !s_areas_rebase. destruct (c_meta_area_tail (ctx s)); reflexivity. Qed.
Lemma RC_carve_rest rho resv ceil sG sC p : RC rho resv ceil sG sC -> RC rho resv ceil (carve_rest sG p) (carve_rest sC p).
Proof. apply (RC_lift rho resv ceil (fun s => carve_rest s p)); [intros s; apply strip_carve_rest| intros cs; apply rebase_carve_rest]. Qed.
Lemma RC_adv rho resv ceil sG sC p : RC rho resv ceil sG sC -> RC rho resv ceil (adv sG p) (adv sC p).
Proof. unfold adv. apply RC_upd_ctx. Qed.

Section AM2.
Variables (X : extras) (BLG BLC : list blk).

Variables (sG0 sC0 : mstate) (J0 : jled).

Definition PostAM (J' : jled) (x y : option (mstate * optr)) : Prop :=
  match x, y with
  | Some (sG1, moG), Some (sC1, moC) => moC = moG /\ exists rho' LSG1 LSC1,
      JR J' rho' sG1 sC1 /\ AM_frame sG0 sG1 /\ AM_frame sC0 sC1 /\ JF J0 J' /\
      match moG with
      | None => INVL X sG1 (projG J') BLG LSG1 /\ INVL X sC1 (projC J') BLC LSC1
      | Some m => INVL (xidle X (m :: x_idle X)) sG1 (projG J') BLG LSG1 /\ INVL (xidle X (m :: x_idle X)) sC1 (projC J') BLC LSC1
                  /\ ~ In m (x_idle X)
      end
  | None, None => True
  | _, _ => False
  end.

Definition ENT (J : jled) (rho : N -> Z) (sG sC : mstate) (LSG LSC : lhead -> list aptr) : Prop :=
  INVL X sG (projG J) BLG LSG /\ INVL X sC (projC J) BLC LSC /\ JR J rho sG sC /\ AM_frame sG0 sG /\ AM_frame sC0 sC /\ JF J0 J.

#[using="Type"] Lemma am_take_rel J rho sG sC LSG LSC : ENT J rho sG sC LSG LSC ->
  0 < c_avail_meta_count (s_ctx sG) -> jsim J (am_take sG kP bP) (am_take sC kP bP) PostAM.
Proof.
  intros (INVG & INVC & R & AFG & AFC & JFJ) HC. pose proof (jr_rc _ _ _ _ R) as HRC.
  assert (HC' : 0 < c_avail_meta_count (s_ctx sC)) by (rewrite (RC_ctx _ _ _ _ _ HRC); exact HC).
  destruct (am_take_ok X sG (projG J) BLG LSG INVG HC kP bP) as (m & sG2 & EG & INVG2 & AFG2 & NI).
  destruct (am_take_ok X sC (projC J) BLC LSC INVC HC' kP bP) as (m' & sC2 & EC & INVC2 & AFC2 & _).
  unfold am_take in *. unfold ctx in *. rewrite (RC_ctx _ _ _ _ _ HRC) in *.
  destruct (c_avail_meta (s_ctx sG)) as [m0|]; [| apply jsim_undef].
  unfold kP in EG, EC. apply SRet_pair_inj in EG as [EG EM]. apply SRet_pair_inj in EC as [EC EM']. injection EM as <-. injection EM' as <-.
  apply jsim_ret. cbn. split; [reflexivity|]. exists rho, LSG, LSC.
  split.
  { apply (JR_frame J rho sG sC); [exact R| reflexivity| reflexivity| reflexivity|].
    apply RC_upd_meta. apply RC_upd_ctx. exact HRC. }
  rewrite EG, EC.
  split; [exact (amf_trans _ _ _ AFG AFG2)|]. split; [exact (amf_trans _ _ _ AFC AFC2)|]. split; [exact JFJ|].
  split; [exact INVG2|]. split; [exact INVC2| exact NI].
Qed.

#[using="Type"] Lemma am_carve_rel J rho sG sC LSG LSC p : ENT J rho sG sC LSG LSC ->
  c_avail_meta_areas (s_ctx sG) = Some (aadd p 4096) -> s_areas sG !! p = None -> (forall k, 0 <= k < NSLOTS -> s_metas sG !! mslot p k = None) ->
  PGSZ <= snd p -> snd p mod PGSZ = 0 -> c_init_done (s_ctx sG) = 1 ->
  jsim J (am_take (carve_rest sG p) kP bP) (am_take (carve_rest sC p) kP bP) PostAM.
Proof.
  intros (INVG & INVC & R & AFG & AFC & JFJ) H1 H2 H3 H4 H5 H6. pose proof (jr_rc _ _ _ _ R) as HRC.
  destruct (INVL_carve X sG (projG J) BLG LSG p INVG H1 H2 H3 H4 H5 H6) as (INVG' & AFG' & HCG).
  destruct (INVL_carve X sC (projC J) BLC LSC p INVC) as (INVC' & AFC' & HCC).
  1-6: rewrite ?(RC_ctx _ _ _ _ _ HRC), ?(RC_areas _ _ _ _ _ HRC), ?(RC_metas _ _ _ _ _ HRC); auto.
  apply (am_take_rel J rho _ _ LSG LSC); [| exact HCG].
  split; [exact INVG'|]. split; [exact INVC'|]. split.
  { destruct (cr_shape X sG (projG J) BLG LSG p INVG H2) as (EA & EH & ET & EAM & EAC & ER & EM & EG & ESL & ESH & ETK & EN & ESE & ERS & ECA & ECC & EC1 & EC2 & EC3 & EC4 & EC5 & EC6 & EC7 & REST).
    apply (JR_frame J rho sG sC); [exact R| exact ER| exact EC7| exact ECA| apply RC_carve_rest; exact HRC]. }
  split; [exact (amf_trans _ _ _ AFG AFG')|]. split; [exact (amf_trans _ _ _ AFC AFC')| exact JFJ].
Qed.
#[using="Type"] Lemma projG_eq J : projG J = mkLed (j_resvG J) (map gG (j_groups J)) (map mG (j_metas J)) (option_map rG (j_brkreg J)) (phG (j_brk J)) (j_live J) (j_ceilG J).
Proof. reflexivity. Qed.
#[using="Type"] Lemma projC_eq J : projC J = mkLed (j_resvC J) (map gC (j_groups J)) (map mC (j_metas J)) (option_map rC (j_brkreg J)) (phC (j_brk J)) (j_live J) (j_ceilC J).
Proof. reflexivity. Qed.

#[using="Type"] Lemma am_finish_rel J rho sG sC LSG LSC : ENT J rho sG sC LSG LSC ->
  0 < c_avail_meta_area_count (s_ctx sG) -> c_init_done (s_ctx sG) = 1 ->
  jsim J (am_finish sG true kP bP) (am_finish sC true kP bP) PostAM.
Proof.
  intros (INVG & INVC & R & AFG & AFC & JFJ) HC HI. pose proof (jr_rc _ _ _ _ R) as HRC.
  pose proof (RC_ctx _ _ _ _ _ HRC) as ECX.
  destruct (ir_cursor _ _ _ (proj1 INVG)) as (C1 & C2 & C3).
  destruct (c_avail_meta_areas (s_ctx sG)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 HC eq_refl)].
  destruct (C3 _ _ eq_refl) as (r & Hr & K & P1 & P2 & P3 & P4). specialize (P4 HC).
  unfold am_finish, ctx. rewrite ECX, EC. cbn [snd]. rewrite (proj2 (Z.eqb_eq _ _) P2). cbn [negb].
  assert (EaG : conc sG (rid, off) = r_base r + off) by (unfold conc, get_region; cbn; rewrite Hr; reflexivity).
  assert (EaC : conc sC (rid, off) = rho rid + off) by (rewrite (RC_conc _ _ _ _ _ (rid, off) HRC); cbn; rewrite Hr; reflexivity).
  assert (Ek : (1 + (off / PGSZ - 1)) * PGSZ = off) by (unfold PGSZ in *; pose proof (Z.div_mod off 4096 ltac:(lia)); lia).
  apply jsim_vis.
  - cbn. split; [reflexivity|]. split; [reflexivity|]. split; [exact (brk_quiet_of _ _ _ (proj1 INVG))|]. split; [reflexivity|]. split; [reflexivity|].
    destruct (jmeta_cursor X BLG LSG J rho sG sC INVG R rid off EC HC) as (r' & Hr' & Hin & _ & _ & _).
    rewrite Hr in Hr'. injection Hr' as <-.
    exists (r_base r), (rho rid), (r_len r), (off / PGSZ - 1). split; [exact Hin|]. rewrite Ek.
    split; [exact EaG|]. split; [exact EaC|]. pose proof (MI_WFree2.round_up_ge (r_len r)). unfold PGSZ in *. lia.
  - cbn. exact (coh_mprotect X BLG LSG J rho sG sC INVG (proj1 INVC) R rid off EC HC).
  - intros zG zC Hz. pose proof (jans_ok_G _ _ _ _ _ Hz) as AG. pose proof (jans_ok_C _ _ _ _ _ Hz) as AC. pose proof (jans_ok_class _ _ _ _ _ Hz) as CL.
    cbn in AG, AC, CL. rewrite AG, AC. cbn [negb].
    change ((zG =? 0) || (zG =? TWO64 - ENOSYS)) with (mprot_okb zG). change ((zC =? 0) || (zC =? TWO64 - ENOSYS)) with (mprot_okb zC).
    apply Bool.eqb_prop in CL. rewrite <- CL.
    cbn [jevent_post].
    destruct (mprot_okb zG) eqn:OK.
    +
      rewrite !am_carve_eq.
      destruct (INVL_meta_adv X sG (projG J) BLG LSG rid off INVG EC HC) as (INVG' & F1 & F2 & F3 & F4 & F5 & F6 & AFG').
      destruct (INVL_meta_adv X sC (projC J) BLC LSC rid off INVC ltac:(rewrite ECX; exact EC) ltac:(rewrite ECX; exact HC)) as (INVC' & _ & _ & _ & _ & _ & _ & AFC').
      set (J' := jset_metas (map (jbump (conc sG (rid, off))) (j_metas J)) J).
      assert (LG' : KLedger.set_metas (map (bump_meta (conc sG (rid, off))) (ld_metas (projG J))) (projG J) = projG J').
      { unfold J'. rewrite !projG_eq. cbn. rewrite map_mG_bump. reflexivity. }
      assert (LC' : KLedger.set_metas (map (bump_meta (conc sC (rid, off))) (ld_metas (projC J))) (projC J) = projC J').
      { unfold J'. rewrite !projC_eq. cbn. rewrite (map_mC_bump (conc sG (rid, off)) (conc sC (rid, off))); [reflexivity|].
        exact (coh_mprotect X BLG LSG J rho sG sC INVG (proj1 INVC) R rid off EC HC). }
      rewrite LG' in INVG'. rewrite LC' in INVC'.
      apply (am_carve_rel J' rho (adv sG (rid, off)) (adv sC (rid, off)) LSG LSC); try assumption.
      * split; [exact INVG'|]. split; [exact INVC'|]. split; [exact (JR_meta_adv J rho sG sC (rid, off) (conc sG (rid, off)) R)|].
        split; [exact (amf_trans _ _ _ AFG AFG')|]. split; [exact (amf_trans _ _ _ AFC AFC')|]. destruct JFJ; constructor; assumption.
    + apply jsim_ret. cbn. split; [reflexivity|]. exists rho, LSG, LSC. split; [exact R|]. split; [exact AFG|]. split; [exact AFC|]. split; [exact JFJ|]. split; [exact INVG| exact INVC].
Qed.

#[using="Type"] Lemma am_after_brk_rel J rho sG sC LSG LSC : ENT J rho sG sC LSG LSC ->
  c_init_done (s_ctx sG) = 1 -> jsim J (am_after_brk sG true kP bP) (am_after_brk sC true kP bP) PostAM.
Proof.
  intros ENT HI. pose proof ENT as (INVG & INVC & R & AFG & AFC & JFJ). pose proof (jr_rc _ _ _ _ R) as HRC.
  pose proof (RC_ctx _ _ _ _ _ HRC) as ECX. pose proof (RC_next_rid _ _ _ _ _ HRC) as ENR.
  unfold am_after_brk, ctx. rewrite ECX.
  destruct (Z.eqb_spec (c_avail_meta_area_count (s_ctx sG)) 0) as [HC|HC].
  - set (n := Z.shiftl 2 (c_meta_alloc_shift (s_ctx sG))). set (len := n * PGSZ).
    pose proof (nm_len X sG (projG J) BLG LSG INVG) as HL. fold n len in HL.
    apply jsim_vis.
    + cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. left.
      split; [exact (brk_quiet_of _ _ _ (proj1 INVG))|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [left; reflexivity| exact HL].
    + exact I.
    + intros zG zC Hz. pose proof (jans_ok_G _ _ _ _ _ Hz) as AG. pose proof (jans_ok_C _ _ _ _ _ Hz) as AC. pose proof (jans_ok_class _ _ _ _ _ Hz) as CL.
      unfold answer_ok in AG, AC. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in AG, AC. cbn iota in AG, AC.
      rewrite (mmap_answer_ok_eq X sG (projG J) (proj1 INVG)) in AG. rewrite (mmap_answer_ok_eq X sC (projC J) (proj1 INVC)) in AC.
      rewrite AG, AC. cbn [negb].
      cbn in CL. apply Bool.eqb_prop in CL. rewrite <- CL.
      cbn [jevent_post]. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn iota.
      destruct (is_err zG) eqn:ER.
      * apply jsim_ret. cbn. split; [reflexivity|]. exists rho, LSG, LSC. split; [exact R|]. split; [exact AFG|]. split; [exact AFC|]. split; [exact JFJ|]. split; [exact INVG| exact INVC].
      * cbn [new_region].
        destruct (INVL_new_meta X sG (projG J) BLG LSG zG INVG HC AG ER) as (INVG' & HCG' & HIG' & AFG').
        destruct (INVL_new_meta X sC (projC J) BLC LSC zC INVC ltac:(rewrite ECX; exact HC) ltac:(rewrite ECX; exact AC) (eq_sym CL)) as (INVC' & _ & _ & AFC').
        rewrite ECX in INVC', AFC'. fold n len in INVG', INVC', AFG', AFC', HCG', HIG'. unfold new_region in INVG', INVC', AFG', AFC', HCG', HIG'. cbn [fst snd] in INVG', INVC', AFG', AFC', HCG', HIG'.
        set (J' := jset_metas ((zG, zC, len, 0) :: j_metas J) J).
        change (KLedger.set_metas ((zG, len, 0) :: ld_metas (projG J)) (projG J)) with (projG J') in INVG'.
        change (KLedger.set_metas ((zC, len, 0) :: ld_metas (projC J)) (projC J)) with (projC J') in INVC'.
        eapply (am_finish_rel J' (nupd rho (s_next_rid sG) zC) _ _ LSG LSC).
        -- split; [exact INVG'|]. split; [exact INVC'|]. split; [exact (JR_new_meta X (projG J) J rho sG sC zG zC (proj1 INVG) R)|].
           split; [exact (amf_trans _ _ _ AFG AFG')|]. split; [exact (amf_trans _ _ _ AFC AFC')|]. destruct JFJ; constructor; assumption.
        -- exact HCG'.
        -- rewrite HIG'. exact HI.
  - apply (am_finish_rel J rho sG sC LSG LSC ENT); [| exact HI]. pose proof (proj1 (ir_cursor _ _ _ (proj1 INVG))). lia.
Qed.

#[using="Type"] Lemma am_reuse_facts X0 st L BL LS m : INVL X0 st L BL LS -> c_free_meta_head (s_ctx st) = Some m ->
  exists LS', INVL (xidle X0 (m :: x_idle X0)) (dequeue LFree m st) L BL LS' /\ ~ In m (x_idle X0) /\ AM_frame st (dequeue LFree m st).
Proof.
  intros INV EFH. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (il_head _ _ IL LFree) as HH. cbn in HH. unfold ctx in HH. rewrite EFH in HH.
  destruct (LS LFree) as [|m' rest] eqn:ELS; [discriminate|]. cbn in HH. inversion HH. subst m'.
  pose proof (INVL_dequeue X0 (xidle X0 (m :: x_idle X0)) st L BL LS m LFree [] rest INV ltac:(rewrite ELS; reflexivity) ltac:(right; split; reflexivity)) as INV1.
  destruct (dequeue_frame LFree m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC).
  eexists. split; [exact INV1|]. split.
  { intros Hin. apply (proj2 (im_idle _ _ _ IM m Hin)). exists LFree. rewrite ELS. left. reflexivity. }
  destruct FC. constructor; auto; try congruence.
  all: try (intros sc; change (active (dequeue LFree m st) sc) with (get_head (dequeue LFree m st) (LActive sc)); rewrite dequeue_head;
            destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]).
  all: try (intros sc; unfold usage, ctx; rewrite cb_usage; reflexivity).
  all: try (intros rid r H _; rewrite F1; exact H).
  all: rewrite ?F3; lia.
Qed.

#[using="Type"] Lemma brk_dead_rel J J' rho sG sC LSG LSC : ENT J rho sG sC LSG LSC ->
  j_resvG J' = j_resvG J -> j_resvC J' = j_resvC J -> j_groups J' = j_groups J -> j_metas J' = j_metas J -> j_brkreg J' = j_brkreg J -> j_live J' = j_live J ->
  j_brk J' = JDead -> c_init_done (s_ctx sG) = 1 ->
  j_ceilG J' = j_ceilG J -> j_ceilC J' = j_ceilC J ->
  jsim J' (am_after_brk (upd_ctx (set_brk BrkDead) sG) true kP bP) (am_after_brk (upd_ctx (set_brk BrkDead) sC) true kP bP) PostAM.
Proof.
  intros (INVG & INVC & R & AFG & AFC & JFJ) E1 E2 E3 E4 E5 E6 E7 HI EC1 EC2.
  destruct (INVL_brk_dead X sG (projG J) (projG J') BLG LSG INVG) as [INVG' AFG']; [cbn; congruence..| cbn; rewrite E7; reflexivity| cbn; congruence|].
  destruct (INVL_brk_dead X sC (projC J) (projC J') BLC LSC INVC) as [INVC' AFC']; [cbn; congruence..| cbn; rewrite E7; reflexivity| cbn; congruence|].
  apply (am_after_brk_rel J' rho _ _ LSG LSC); [| exact HI].
  split; [exact INVG'|]. split; [exact INVC'|]. split.
  { apply (JR_regions J J' rho rho sG sC); try assumption; try (cbn; first [reflexivity | exact E7 | (intros; split; intros; assumption) | (intros; reflexivity)]).
    - rewrite E5. exact (jr_brkreg _ _ _ _ R).
    - rewrite E2, EC2. apply RC_upd_ctx. exact (jr_rc _ _ _ _ R). }
  split; [exact (amf_trans _ _ _ AFG AFG')|]. split; [exact (amf_trans _ _ _ AFC AFC')|]. destruct JFJ; constructor; congruence.
Qed.

#[using="Type"] Lemma JR_brk_first X0 J rho sG sC LG BLG0 LSG0 cG cC J3 :
  INVL X0 sG LG BLG0 LSG0 -> JR J rho sG sC ->
  c_brk (s_ctx sG) = BrkUntried -> c_avail_meta_area_count (s_ctx sG) = 0 ->
  j_resvC J3 = j_resvC J -> j_groups J3 = j_groups J -> j_metas J3 = j_metas J ->
  j_brkreg J3 = Some (round_up_pg cG, round_up_pg cC, 2 * PGSZ) -> j_brk J3 = JLive ->
  j_ceilC J3 = j_ceilC J ->
  let rid := s_next_rid sG in
  let f := fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, PGSZ)) (set_brk (BrkLive rid (2 * PGSZ)) c)) in
  JR J3 (nupd rho rid (round_up_pg cC))
     (adv (upd_ctx f (fst (new_region RKBrk (round_up_pg cG) (2 * PGSZ) sG))) (rid, PGSZ))
     (adv (upd_ctx f (fst (new_region RKBrk (round_up_pg cC) (2 * PGSZ) sC))) (rid, PGSZ)).
Proof.
  intros INVG R EBRK HC E1 E2 E3 E4 E5 E6. cbn zeta. set (rid := s_next_rid sG).
  pose proof (proj1 INVG) as IR. pose proof (next_rid_fresh _ _ _ IR) as FR. fold rid in FR.
  pose proof (ir_brk _ _ _ IR) as IBK. rewrite EBRK in IBK. destruct IBK as [_ NB].
  assert (LK : forall q, s_regions (adv (upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, PGSZ)) (set_brk (BrkLive rid (2 * PGSZ)) c)))
                           (fst (new_region RKBrk (round_up_pg cG) (2 * PGSZ) sG))) (rid, PGSZ)) !! q
                      = if (q =? rid)%N then Some (mkRegion RKBrk (round_up_pg cG) (2 * PGSZ)) else s_regions sG !! q).
  { intros q. unfold adv. cbn -[new_region Z.mul]. apply lookup_new_region. }
  apply (JR_regions J J3 rho _ sG sC); try assumption.
  - intros q rq K. rewrite LK. destruct (N.eqb_spec q rid) as [->|NE]; [| split; intro; assumption]. rewrite FR. split; intros H; [discriminate| inversion H; subst; cbn in K; congruence].
  - intros q rq Hq _. apply nupd_other. intros ->. rewrite FR in Hq. discriminate.
  - intros bG bC l. rewrite E4. split.
    + intros H. injection H as <- <- <-. exists rid, (mkRegion RKBrk (round_up_pg cG) (2 * PGSZ)). rewrite LK, N.eqb_refl, nupd_same. cbn. auto 10.
    + intros (q & rq & Hq & K & <- & <- & <-). rewrite LK in Hq. destruct (N.eqb_spec q rid) as [->|NE].
      * inversion Hq. subst. cbn. rewrite nupd_same. reflexivity.
      * exfalso. exact (NB q rq Hq K).
  - rewrite E1, E6. apply RC_adv. apply RC_upd_ctx. exact (proj1 (RC_new_region rho (j_resvC J) (j_ceilC J) RKBrk _ _ _ sG sC (jr_rc _ _ _ _ R))).
Qed.

#[using="Type"] Lemma JR_brk_grow X0 J rho sG sC LG BLG0 LSG0 rid off r J1 :
  INVL X0 sG LG BLG0 LSG0 -> JR J rho sG sC ->
  c_brk (s_ctx sG) = BrkLive rid off -> c_avail_meta_area_count (s_ctx sG) = 0 ->
  s_regions sG !! rid = Some r -> r_kind r = RKBrk -> r_len r = off ->
  j_resvC J1 = j_resvC J -> j_groups J1 = j_groups J -> j_metas J1 = j_metas J ->
  j_brkreg J1 = Some (r_base r, rho rid, off + PGSZ) -> j_brk J1 = JLive ->
  j_ceilC J1 = j_ceilC J ->
  let g := fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ) in
  let f := fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, off)) (set_brk (BrkLive rid (off + PGSZ)) c)) in
  JR J1 rho (adv (upd_ctx f (upd_region rid g sG)) (rid, off)) (adv (upd_ctx f (upd_region rid g sC)) (rid, off)).
Proof.
  intros INVG R EBRK HC Hr K Elen E1 E2 E3 E4 E5 E6. cbn zeta.
  pose proof (proj1 INVG) as IR.
  assert (LK : forall q, s_regions (adv (upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, off)) (set_brk (BrkLive rid (off + PGSZ)) c)))
                           (upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) sG)) (rid, off)) !! q
                      = if (q =? rid)%N then Some (mkRegion RKBrk (r_base r) (off + PGSZ)) else s_regions sG !! q).
  { intros q. unfold adv. cbn -[upd_region Z.add]. rewrite lookup_upd_region, Hr. cbn. rewrite K. reflexivity. }
  apply (JR_regions J J1 rho rho sG sC); try assumption.
  - intros q rq Kq. rewrite LK. destruct (N.eqb_spec q rid) as [->|NE]; [| split; intro; assumption]. rewrite Hr. split; intros H; inversion H; subst; cbn in Kq; congruence.
  - intros; reflexivity.
  - intros bG bC l. rewrite E4. split.
    + intros H. injection H as <- <- <-. exists rid, (mkRegion RKBrk (r_base r) (off + PGSZ)). rewrite LK, N.eqb_refl. cbn. auto 10.
    + intros (q & rq & Hq & Kq & <- & <- & <-). rewrite LK in Hq. destruct (N.eqb_spec q rid) as [->|NE].
      * inversion Hq. subst. cbn. reflexivity.
      * exfalso. exact (NE (ir_brk1 _ _ _ IR _ _ _ _ Hq Hr Kq K)).
  - rewrite E1, E6. apply RC_adv. apply RC_upd_ctx. apply RC_upd_region; [| exact (jr_rc _ _ _ _ R)]. intros rg. reflexivity.
Qed.

#[using="Type"] Lemma RC_am_init rho resv ceil sG sC : RC rho resv ceil sG sC -> RC rho resv ceil (am_init sG) (am_init sC).
Proof.
  intros H. unfold am_init, ctx. rewrite (RC_ctx _ _ _ _ _ H), (RC_secret _ _ _ _ _ H).
  destruct (c_init_done (s_ctx sG) =? 0); [apply RC_upd_ctx; exact H| exact H].
Qed.

#[using="Type"] Theorem alloc_meta_rel J rho sG sC LSG LSC : ENT J rho sG sC LSG LSC ->
  jsim J (alloc_meta sG kP bP) (alloc_meta sC kP bP) PostAM.
Proof.
  intros (INVG0 & INVC0 & R0 & AFG0 & AFC0 & JFJ).
  destruct (INVL_am_init X sG (projG J) BLG LSG INVG0) as (INVG & HIG & AFiG).
  destruct (INVL_am_init X sC (projC J) BLC LSC INVC0) as (INVC & HIC & AFiC).
  pose proof (jr_rc _ _ _ _ R0) as HRC0.
  assert (R : JR J rho (am_init sG) (am_init sC)).
  { apply (JR_frame J rho sG sC); [exact R0| | | | apply RC_am_init; exact HRC0]; unfold am_init; destruct (c_init_done _ =? 0); reflexivity. }
  pose proof (amf_trans _ _ _ AFG0 AFiG) as AFG. pose proof (amf_trans _ _ _ AFC0 AFiC) as AFC. clear AFiG AFiC.
  unfold alloc_meta. fold (am_init sG). fold (am_init sC).
  set (sg := am_init sG) in *. set (sc := am_init sC) in *. clearbody sg sc. clear INVG0 INVC0 R0 HRC0 AFG0 AFC0.
  assert (ENT1 : ENT J rho sg sc LSG LSC) by (split; [exact INVG|]; split; [exact INVC|]; split; [exact R|]; split; [exact AFG|]; split; [exact AFC| exact JFJ]).
  pose proof (jr_rc _ _ _ _ R) as HRC. pose proof (RC_ctx _ _ _ _ _ HRC) as ECX. pose proof (RC_next_rid _ _ _ _ _ HRC) as ENR.
  pose proof INVG as (IR & IA & IM & IL & IG & IS & ISH).
  unfold ctx. rewrite ECX.

  destruct (c_free_meta_head (s_ctx sg)) as [m|] eqn:EFH.
  { destruct (am_reuse_facts X sg (projG J) BLG LSG m INVG EFH) as (LSG' & INVG' & NI & AFG').
    destruct (am_reuse_facts X sc (projC J) BLC LSC m INVC ltac:(rewrite ECX; exact EFH)) as (LSC' & INVC' & _ & AFC').
    apply jsim_ret. cbn. split; [reflexivity|]. exists rho, LSG', LSC'.
    split.
    { destruct (dequeue_frame LFree m sg) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC).
      apply (JR_frame J rho sg sc); [exact R| exact F1| exact (cb_brk _ _ FC)| exact (cb_amas _ _ FC)| apply RC_dequeue; exact HRC]. }
    split; [exact (amf_trans _ _ _ AFG AFG')|]. split; [exact (amf_trans _ _ _ AFC AFC')|]. split; [exact JFJ|].
    split; [exact INVG'|]. split; [exact INVC'| exact NI]. }

  destruct (Z.eqb_spec (c_avail_meta_count (s_ctx sg)) 0) as [HAC|HAC]; cbn [negb].
  2:{ apply (am_take_rel J rho sg sc LSG LSC ENT1). pose proof (proj1 (ia_avail _ IA)). lia. }

  destruct (Z.eqb_spec (c_avail_meta_area_count (s_ctx sg)) 0) as [HC|HC]; cbn [andb].
  2:{ exact (am_after_brk_rel J rho sg sc LSG LSC ENT1 HIG). }
  pose proof (ir_brk _ _ _ IR) as IBK. pose proof (jr_brk _ _ _ _ R) as JB.
  destruct (c_brk (s_ctx sg)) as [| |rid off] eqn:EBRK; cbn [negb].
  -
    destruct IBK as [BP NB].
    apply jsim_vis; [cbn; left; auto| exact I|].
    intros cG cC Hc. pose proof (jans_ok_G _ _ _ _ _ Hc) as AG. pose proof (jans_ok_C _ _ _ _ _ Hc) as AC. cbn in AG, AC. rewrite AG, AC. cbn [negb].
    cbn [jevent_post Z.eqb].
    set (J1 := jset_brk (JQueried cG cC) J).
    set (baseG := round_up_pg cG). set (newG := baseG + 2 * PGSZ). set (baseC := round_up_pg cC). set (newC := baseC + 2 * PGSZ).
    assert (PG : 0 < cG /\ 0 < cC).
    { unfold brk0_answer_ok in AG, AC. apply andb_prop in AG as [AG _]. apply andb_prop in AG as [AG _]. apply andb_prop in AC as [AC _]. apply andb_prop in AC as [AC _].
      apply Z.ltb_lt in AG. apply Z.ltb_lt in AC. auto. }
    pose proof (MI_WFree2.round_up_ge cG) as RG. pose proof (MI_WFree2.round_up_ge cC) as RCC.
    assert (NZG : (newG =? 0) = false) by (apply Z.eqb_neq; unfold newG, baseG, PGSZ; lia).
    assert (NZC : (newC =? 0) = false) by (apply Z.eqb_neq; unfold newC, baseC, PGSZ; lia).
    apply jsim_vis.
    { cbn. right. left. exists cG, cC. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. unfold newG, newC, baseG, baseC, PGSZ. lia. }
    { exact I. }
    intros rG rC Hr. pose proof (jans_ok_G _ _ _ _ _ Hr) as AG1. pose proof (jans_ok_C _ _ _ _ _ Hr) as AC1. pose proof (jans_ok_class _ _ _ _ _ Hr) as CL1.
    unfold answer_ok in AG1, AC1. rewrite NZG in AG1. rewrite NZC in AC1. cbn [ld_brk projG projC J1 jset_brk j_brk phG phC] in AG1, AC1.
    apply andb_prop in AG1 as [HbG HpG]. apply andb_prop in AC1 as [HbC HpC]. rewrite HbG, HbC. cbn [negb].
    cbn [same_class] in CL1. rewrite NZG in CL1. apply Bool.eqb_prop in CL1.
    cbn [jevent_post]. rewrite NZG. cbn [j_brk J1 jset_brk].
    destruct (Z.eqb_spec rG newG) as [->|NEG].
    +
      rewrite <- CL1 in HpC. rewrite <- CL1. cbn [negb orb] in HpG, HpC |- *.
      rewrite (lbrk_pages_ok_ext (projG J1) (projG J)) in HpG by reflexivity. rewrite (brk_pages_ok_eq X sg (projG J) IR) in HpG. fold baseG in HpG.
      rewrite (lbrk_pages_ok_ext (projC J1) (projC J)) in HpC by reflexivity. rewrite (brk_pages_ok_eq X sc (projC J) (proj1 INVC)) in HpC. fold baseC in HpC.
      rewrite HpG, HpC. cbn [negb].
      set (J2 := jset_brk (JGuard cG cC) J1).
      apply jsim_vis.
      { cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. right. exists cG, cC. repeat split; reflexivity. }
      { exact I. }
      intros gG gC Hg. pose proof (jans_ok_G _ _ _ _ _ Hg) as AG2. pose proof (jans_ok_C _ _ _ _ _ Hg) as AC2.
      unfold answer_ok in AG2, AC2. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in AG2, AC2. cbn [andb] in AG2, AC2.
      fold baseG in AG2. fold baseC in AC2. rewrite AG2, AC2. cbn [negb].
      cbn [jevent_post]. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
      set (J3 := jset_brk JLive (jset_brkreg (Some (baseG, baseC, 2 * PGSZ)) J2)).
      cbn [new_region].
      unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb set_next_rid set_regions].
      unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd set_next_rid set_regions].
      change (PGSZ mod PGSZ =? 0) with true. cbn [negb]. rewrite !am_carve_eq.
      destruct (INVL_brk_first X sg (projG J) BLG LSG cG INVG EBRK HC HpG (projG J2) (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))) as (INVG3 & G1 & G2 & G3 & G4 & G5 & G6 & AFG3).
      destruct (INVL_brk_first X sc (projC J) BLC LSC cC INVC ltac:(rewrite ECX; exact EBRK) ltac:(rewrite ECX; exact HC) HpC (projC J2) (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))) as (INVC3 & C1 & C2 & C3 & C4 & C5 & C6 & AFC3).
      fold baseG in INVG3, G1, G2, G3, G4, G5, G6, AFG3. fold baseC in INVC3, C1, C2, C3, C4, C5, C6, AFC3.
      change (KLedger.set_brkph BPLive (KLedger.set_brkreg (Some (baseG, 2 * PGSZ)) (projG J2))) with (projG J3) in INVG3.
      change (KLedger.set_brkph BPLive (KLedger.set_brkreg (Some (baseC, 2 * PGSZ)) (projC J2))) with (projC J3) in INVC3.
      unfold new_region in INVG3, G1, G2, G3, AFG3, INVC3, C1, C2, C3, AFC3. cbn [fst snd] in INVG3, G1, G2, G3, AFG3, INVC3, C1, C2, C3, AFC3.
      rewrite ENR in INVC3, C1, C2, C3, AFC3.
      pose proof (JR_brk_first X J rho sg sc (projG J) BLG LSG cG cC J3 INVG R EBRK HC eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as R3.
      cbn zeta in R3. unfold new_region in R3. cbn [fst snd] in R3. fold baseG baseC in R3.
      rewrite ENR in R3. rewrite ENR. apply (am_carve_rel J3 (nupd rho (s_next_rid sg) baseC) _ _ LSG LSC).
      * split; [exact INVG3|]. split; [exact INVC3|]. split; [exact R3|].
        split; [exact (amf_trans _ _ _ AFG AFG3)|]. split; [exact (amf_trans _ _ _ AFC AFC3)|]. destruct JFJ; constructor; cbn; assumption.
      * exact G1.
      * exact G2.
      * exact G3.
      * exact G4.
      * exact G5.
      * rewrite G6. exact HIG.
    +
      rewrite <- CL1. cbn [negb].
      apply (brk_dead_rel J (jset_brk JDead J1) rho sg sc LSG LSC ENT1); try reflexivity; exact HIG.
  -
    exact (am_after_brk_rel J rho sg sc LSG LSC ENT1 HIG).
  -
    destruct IBK as [BP (r & Hr & K & Elen)].
    pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (S6 ltac:(left; exact K)) as [S7 S8].
    pose proof (RC_region _ _ _ _ _ rid HRC) as HrC. rewrite Hr in HrC. cbn in HrC.
    pose proof (ir_shape _ _ _ (proj1 INVC) _ _ HrC) as (T1 & _). cbn in T1.
    set (oldG := conc sg (rid, off)). set (newG := oldG + PGSZ). set (oldC := conc sc (rid, off)). set (newC := oldC + PGSZ).
    assert (EoG : oldG = r_base r + off) by (unfold oldG, conc, get_region; rewrite Hr; reflexivity).
    assert (EoC : oldC = rho rid + off) by (unfold oldC; rewrite (RC_conc _ _ _ _ _ (rid, off) HRC); cbn; rewrite Hr; reflexivity).
    assert (NZG : (newG =? 0) = false) by (apply Z.eqb_neq; unfold newG; rewrite EoG; unfold PGSZ in *; lia).
    assert (NZC : (newC =? 0) = false) by (apply Z.eqb_neq; unfold newC; rewrite EoC; unfold PGSZ in *; lia).
    assert (JBR : j_brkreg J = Some (r_base r, rho rid, off)).
    { apply (proj2 (jr_brkreg _ _ _ _ R (r_base r) (rho rid) off)). exists rid, r. auto 10. }
    apply jsim_vis.
    { cbn. right. right. exists (r_base r), (rho rid), off. split; [exact JB|]. split; [exact JBR|].
      unfold newG, newC. rewrite EoG, EoC. unfold PGSZ in *. lia. }
    { exact I. }
    intros zG zC Hz. pose proof (jans_ok_G _ _ _ _ _ Hz) as AG. pose proof (jans_ok_C _ _ _ _ _ Hz) as AC. pose proof (jans_ok_class _ _ _ _ _ Hz) as CL.
    unfold answer_ok in AG, AC. rewrite NZG in AG. rewrite NZC in AC.
    change (ld_brk (projG J)) with (phG (j_brk J)) in AG. change (ld_brk (projC J)) with (phC (j_brk J)) in AC.
    change (ld_brkreg (projG J)) with (option_map rG (j_brkreg J)) in AG. change (ld_brkreg (projC J)) with (option_map rC (j_brkreg J)) in AC.
    rewrite JB, JBR in AG, AC. cbn [phG phC option_map rG rC] in AG, AC. rewrite <- EoG in AG. rewrite <- EoC in AC. fold newG in AG. fold newC in AC.
    apply andb_prop in AG as [HbG HpG]. apply andb_prop in AC as [HbC HpC]. rewrite HbG, HbC. cbn [negb].
    cbn [same_class] in CL. rewrite NZG in CL. apply Bool.eqb_prop in CL.
    cbn [jevent_post]. rewrite NZG, JB, JBR.
    destruct (Z.eqb_spec zG newG) as [->|NEG].
    +
      rewrite <- CL in HpC. rewrite <- CL. cbn [negb orb] in HpG, HpC |- *.
      rewrite (brk_pages_ok_eq X sg (projG J) IR) in HpG. rewrite (brk_pages_ok_eq X sc (projC J) (proj1 INVC)) in HpC.
      rewrite HpG, HpC. cbn [negb].
      set (J1 := jset_brkreg (Some (r_base r, rho rid, off + PGSZ)) J).
      unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb upd_region].
      unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd upd_region].
      rewrite (proj2 (Z.eqb_eq _ _) S7') || idtac.
      idtac.
      replace (if negb (off mod PGSZ =? 0) then false else false) with false by (destruct (negb (off mod PGSZ =? 0)); reflexivity).
      cbn iota. rewrite !am_carve_eq.
      destruct (INVL_brk_grow X sg (projG J) BLG LSG rid off INVG EBRK HC HpG) as (INVG3 & G1 & G2 & G3 & G4 & G5 & G6 & AFG3).
      destruct (INVL_brk_grow X sc (projC J) BLC LSC rid off INVC ltac:(rewrite ECX; exact EBRK) ltac:(rewrite ECX; exact HC) HpC) as (INVC3 & C1 & C2 & C3 & C4 & C5 & C6 & AFC3).
      fold oldG in INVG3. fold oldC in INVC3.
      replace (oldG - off) with (r_base r) in INVG3 by (clear - EoG; lia). replace (oldC - off) with (rho rid) in INVC3 by (clear - EoC; lia).
      change (KLedger.set_brkreg (Some (r_base r, off + PGSZ)) (projG J)) with (projG J1) in INVG3.
      change (KLedger.set_brkreg (Some (rho rid, off + PGSZ)) (projC J)) with (projC J1) in INVC3.
      pose proof (JR_brk_grow X J rho sg sc (projG J) BLG LSG rid off r J1 INVG R EBRK HC Hr K Elen eq_refl eq_refl eq_refl eq_refl JB eq_refl) as R3. cbn zeta in R3.
      apply (am_carve_rel J1 rho _ _ LSG LSC).
      * split; [exact INVG3|]. split; [exact INVC3|]. split; [exact R3|].
        split; [exact (amf_trans _ _ _ AFG AFG3)|]. split; [exact (amf_trans _ _ _ AFC AFC3)|]. destruct JFJ; constructor; cbn; assumption.
      * exact G1.
      * exact G2.
      * exact G3.
      * exact G4.
      * exact G5.
      * rewrite G6. exact HIG.
    +
      rewrite <- CL. cbn [negb].
      apply (brk_dead_rel J (jset_brk JDead J) rho sg sc LSG LSC ENT1); try reflexivity; exact HIG.
Qed.

End AM2.
