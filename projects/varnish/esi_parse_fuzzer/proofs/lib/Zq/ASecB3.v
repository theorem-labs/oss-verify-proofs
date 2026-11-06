(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMalmys ATransp ABudget ACover ASecB2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.
Definition sec_cover (A : AState) (h : VmMaps) : Prop :=
     In (Z_to_bv 64 kShadowGapBeg, Z_to_bv 64 (kHighShadowMapBeg - kShadowGapBeg)) (vm_maps h)       (* [comment removed for export] *)
  /\ (forall x, 0x10000 <= x < 0x60a000 -> zcovb (vm_reserved h) x = true)                            (* [comment removed for export] *)
  /\ (forall lo hi a, In (lo, hi) (p_extra (a_pl A)) -> lo <= a < hi -> 0 <= a < alloc_ceiling ->    (* [comment removed for export] *)
        ~ (kLowShadowMapBeg <= a < kHighMemBeg) -> zcovb (vm_reserved h ++ vm_maps h) a = true).
(* [comment removed for export] *)

(* [comment removed for export] *)
Context {DR : DepotRep}.
Lemma pa_sec_cover : forall A m md, pa_ainv A m md -> sec_cover A (m_vmmaps md).
Proof.
  intros A m md AI. (first [ pose proof ((ai_cover _ _ _ _ _ _ _ AI)) as dR_1; dand3 dR_1 as (fog & FL & FS & COV & F1 & F2) GAP RSV | pose proof (ai_cover _ _ _ _ _ _ _ AI) as ((fog & FL & FS & COV & F1 & F2) & GAP & RSV) ]).
  pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. destruct (ai_ledger _ _ _ _ _ _ _ AI) as (L1 & _).
  split; [exact GAP|]. split; [intros x Hx; exact (pa_cover_image_reserved A m md x AI Hx)|].
  intros lo hi a Hin Ha Hac NB. rewrite zcovb_app. apply orb_true_iff.
  destruct (F2 lo hi a Hin Ha Hac NB) as [IM|[(b & s & Hbs & Hab)|(b & s & Hbs & Hab)]].
  - left. cbn [cl_image_lo cl_image_hi LPA] in IM. exact (pa_cover_image_reserved A m md a AI IM).
  - right. (* [comment removed for export] *)
    assert (Hin' : In (b, s) (big_maps A)).
    { unfold big_maps, big_maps_ in *. apply in_app_iff. left. apply in_app_iff in Hbs as [Hbs|[]]. exact Hbs. }
    (first [ pose proof ((bm_bounds A b s W Hin')) as dR_2; dand3 dR_2 as B0 B1 B2 | pose proof (bm_bounds A b s W Hin') as (B0 & B1 & B2) ]).
    apply zcovb_true. exists (Z_to_bv 64 b, Z_to_bv 64 s). split; [exact (L1 b s Hin')|]. unfold Ledger.lo, Ledger.hi. cbn [fst snd].
    rewrite !unsigned_lit by lia. lia.
  - right. (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) FS _ Hbs) as X. cbn [fst snd] in X.
    apply zcovb_true. exists (Z_to_bv 64 b, Z_to_bv 64 s). split; [exact (F1 _ Hbs)|]. unfold Ledger.lo, Ledger.hi. cbn [fst snd].
    rewrite !unsigned_lit by lia. lia.
Qed.
End CEIL.

(* [comment removed for export] *)
Lemma shadow_region_aligned : forall b s, b mod 64 = 0 -> s mod 64 = 0 -> 0 < s -> shadow_region b s = (sh b, s / 8).
Proof.
  intros b s Hb Hs Hp. unfold shadow_region, sh.
  pose proof (Z_div_mod_eq_full b 64). pose proof (Z_div_mod_eq_full s 64).
  assert (E1 : b / 8 = 8 * (b / 64)) by lia. assert (E2 : s / 8 = 8 * (s / 64)) by lia.
  assert (E3 : (b + s - 1) / 8 = b / 8 + s / 8 - 1) by lia.
  rewrite E3. unfold kShadowOffset, round_down.
  replace ((b / 8 + 2147450880) / 8 * 8) with (b / 8 + 2147450880) by (rewrite E1; replace (8 * (b / 64) + 2147450880) with ((b / 64 + 268431360) * 8) by lia; rewrite Z_div_mult by lia; lia).
  replace (b / 8 + s / 8 - 1 + 2147450880 + 1) with (b / 8 + 2147450880 + s / 8) by lia.
  rewrite (round_up_id (b / 8 + 2147450880 + s / 8) 8); [f_equal; lia| lia|].
  rewrite E1, E2. replace (8 * (b / 64) + 2147450880 + 8 * (s / 64)) with ((b / 64 + 268431360 + s / 64) * 8) by lia. apply Z_mod_mult.
Qed.

Section GrantFacts.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (mbw : word) (ms : Z).
  Hypothesis AI : pa_ainv A m md.
  Let SC : sec_cover A (m_vmmaps md). Proof. exact (pa_sec_cover A m md AI). Qed.   (* [comment removed for export] *)
  Local Notation mb := (bv_unsigned mbw).
  Local Notation h := (m_vmmaps md).
  Hypothesis MBA : mb mod 4096 = 0.
  Hypothesis MB0 : 0 < mb.
  Hypothesis MBC : mb + ms <= alloc_ceiling.
  Hypothesis MSP : 0 < ms < 2^40.
  Hypothesis MSA : ms mod 4096 = 0.
  Hypothesis RF : region_free (vm_reserved h ++ vm_maps h) mbw (wz ms) = true.
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  Let MSW : bv_unsigned (wz ms) = ms. Proof. apply unsigned_lit. lia. Qed.

  (* [comment removed for export] *)
  Lemma gf_apart_entry : forall e, In e (vm_reserved h ++ vm_maps h) ->
    bv_unsigned (fst e) + bv_unsigned (snd e) <= mb \/ mb + ms <= bv_unsigned (fst e).
  Proof.
    intros e He. pose proof (region_free_disjoint_all _ mbw (wz ms) e RF He) as D. unfold Ledger.lo, Ledger.hi in D. cbn [fst snd] in D.
    rewrite MSW in D. lia.
  Qed.
  Lemma gf_not_covered : forall x, mb <= x < mb + ms -> zcovb (vm_reserved h ++ vm_maps h) x = false.
  Proof.
    intros x Hx. destruct (zcovb (vm_reserved h ++ vm_maps h) x) eqn:E; [| reflexivity]. exfalso.
    apply zcovb_true in E as (r & Hr & Hxr). pose proof (gf_apart_entry r Hr). unfold Ledger.lo, Ledger.hi in Hxr. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma gf_APART : forall i b s, nth_error (big_maps A) i = Some (b, s) -> b + s <= mb \/ mb + ms <= b.
  Proof.
    intros i b s Hi. pose proof (nth_error_In _ _ Hi) as Hin. (first [ pose proof ((bm_bounds A b s W Hin)) as dR_3; dand3 dR_3 as B0 B1 B2 | pose proof (bm_bounds A b s W Hin) as (B0 & B1 & B2) ]).
    destruct (ai_ledger _ _ _ _ _ _ _ AI) as (L1 & _). specialize (L1 b s Hin).
    pose proof (gf_apart_entry _ (in_or_app _ _ _ (or_intror L1))) as D. cbn [fst snd] in D. rewrite !unsigned_lit in D by lia. exact D.
  Qed.

  (* [comment removed for export] *)
  Lemma gf_aobj : aobj mb ms.
  Proof.
    destruct SC as (GAP & IMG & _). (first [ pose proof ((bm_nth_fixed A)) as dR_4; dand5 dR_4 as _ _ E2 E3 _ | pose proof (bm_nth_fixed A) as (_ & _ & E2 & E3 & _) ]).
    pose proof (gf_APART _ _ _ E2) as D2. pose proof (gf_APART _ _ _ E3) as D3.
    pose proof (gf_apart_entry _ (in_or_app _ _ _ (or_intror GAP))) as DG. cbn [fst snd] in DG.
    rewrite !unsigned_lit in DG by (unfold kShadowGapBeg, kHighShadowMapBeg; lia).
    assert (OFF : mb + ms <= 0x10000 \/ 0x60a000 <= mb).
    { destruct (Z_lt_le_dec mb 0x60a000) as [L|G]; [| right; exact G]. destruct (Z_lt_le_dec 0x10000 (mb + ms)) as [L2|G2]; [| left; lia]. exfalso.
      (* [comment removed for export] *)
      set (x := Z.max mb 0x10000). assert (Hx : 0x10000 <= x < 0x60a000 /\ mb <= x < mb + ms) by lia.
      pose proof (IMG x (proj1 Hx)) as C. pose proof (gf_not_covered x (proj2 Hx)) as NC.
      unfold zcovb in C, NC. rewrite existsb_app in NC. apply orb_false_iff in NC as [NC _]. rewrite C in NC. discriminate. }
    unfold aobj. kung_all. lia.
  Qed.
  Lemma gf_lin : 4096 <= mb /\ (mb + ms <= 0x10000 \/ 0x60a000 <= mb) /\ (mb + ms <= kLowShadowMapBeg \/ kHighMemBeg <= mb).
  Proof. pose proof (aobj_facts _ _ gf_aobj). lia. Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma gf_shadow_apart : forall b' s' x, b' mod 8 = 0 -> 0 < s' ->
    ((4096 <= b' /\ b' + s' <= kLowShadowMapBeg) \/ (kHighMemBeg <= b' /\ b' + s' <= 2^47)) ->
    fst (shadow_region b' s') <= x < fst (shadow_region b' s') + snd (shadow_region b' s') -> ~ (mb <= x < mb + ms).
  Proof.
    intros b' s' x H8 Hs R Hx IN. pose proof (shadow_region_strict b' s' x H8 Hs R Hx) as ST. (first [ pose proof (gf_lin) as dR_5; dand3 dR_5 as _ _ SX | pose proof gf_lin as (_ & _ & SX) ]).
    unfold in_shadow_strict in ST. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem gf_hidden : forall lo hi x, In (lo, hi) (pa_hull A) -> lo <= x < hi -> ~ (mb <= x < mb + ms).
  Proof.
    intros lo hi x Hin Hx IN. (first [ pose proof (gf_lin) as dR_6; dand3 dR_6 as G4 GI GS | pose proof gf_lin as (G4 & GI & GS) ]).
    unfold pa_hull, ahull_of, ahull_of_ in Hin. apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
    - (* [comment removed for export] *) cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; subst lo hi; lia.
    - unfold hull_of in Hin. apply in_map_iff in Hin as ([b s] & E & Hbs). cbn in E. injection E as E1 E2. subst lo hi.
      unfold aregions_ in Hbs. apply in_app_iff in Hbs as [Hbs|Hbs]; [|apply in_app_iff in Hbs as [Hbs|Hbs]].
      + (* [comment removed for export] *)
        (first [ pose proof ((place_facts A W)) as dR_7; dand14 dR_7 as Pthr Pctx Pn0 Pf0 Pfs Pitab Pm64k Pgvec Pdvec Pm11 Pdtls Ppa Psp0 _ | pose proof (place_facts A W) as (Pthr & Pctx & Pn0 & Pf0 & Pfs & Pitab & Pm64k & Pgvec & Pdvec & Pm11 & Pdtls & Ppa & Psp0 & _) ]).
        cbv zeta in Pthr, Pctx, Pn0, Pf0, Pfs, Pitab, Pm64k, Pgvec, Pdvec, Pm11, Pdtls, Ppa, Psp0.
        (first [ pose proof ((sb_facts A W)) as dR_8; dand5 dR_8 as _ SBM HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBM & HB6 & RSB & SCE) ]). unfold a_sb, a_b6 in *.
        (first [ pose proof ((bm_nth_fixed A)) as dR_9; dand15 dR_9 as E0 E1 _ _ E4 E5 E6 E7 E8 E9 E10 _ _ _ E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & _ & _ & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _ & _ & _ & E14) ]).
        unfold a_b6, a_pa, a_thr, a_ctx, a_fs, a_nodes0, a_frames0, a_itab, a_m64k in *.
        pose proof (gf_APART _ _ _ E0) as D0. pose proof (gf_APART _ _ _ E1) as D1. pose proof (gf_APART _ _ _ E4) as D4.
        pose proof (gf_APART _ _ _ E5) as D5. pose proof (gf_APART _ _ _ E6) as D6. pose proof (gf_APART _ _ _ E7) as D7.
        pose proof (gf_APART _ _ _ E8) as D8. pose proof (gf_APART _ _ _ E9) as D9. pose proof (gf_APART _ _ _ E10) as D10.
        pose proof (gf_APART _ _ _ E14) as D14.
        (* [comment removed for export] *)
        assert (SHP : forall p k, app_rangeA AL_pboth p k /\ p + k <= alloc_ceiling /\ p mod 4096 = 0 -> 0 < k ->
                  (b, s) = shadow_region p k -> False).
        { (intros p k; (first [ intro dR_24; dand3 dR_24 as X1 X2 X3 | intros (X1 & X2 & X3) ]); intros Xk Q). apply app_facts in X1.
          apply (gf_shadow_apart p k x); [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact X3] | exact Xk | clear - X1 X2 CE; kung_all; lia | rewrite <- Q; cbn [fst snd]; lia | exact IN]. }
        pose proof alloc_ceiling_mod16 as ACAL. assert (AC8 : alloc_ceiling mod 8 = 0) by (apply (mod0_down _ 16 8); [exists 2; reflexivity| exact ACAL]).
        assert (RI8 : p_ri (a_pl A) mod 8 = 0).
        { unfold p_ri. apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity|]. unfold kSpaceSize. rewrite <- Zplus_mod_idemp_l, SBM. reflexivity. }
        assert (RIR : kHighMemBeg <= p_ri (a_pl A) /\ p_ri (a_pl A) + 4096 <= alloc_ceiling /\ p_b6 (a_pl A) <= p_ri (a_pl A) /\ p_ri (a_pl A) + 4096 <= p_b6 (a_pl A) + kSpaceReserve).
        { unfold p_ri. kung_all. lia. }
        cbn -[shadow_region Z.add Z.sub Z.mul] in Hbs. cbn [al_image_lo al_image_hi AL_pboth] in Hbs.
        destruct Hbs as [Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[]]]]]]]]]]]]]]]]]]]]]]]]]];
          lazymatch type of Q with
          | shadow_region ?p ?k = _ =>
              first [ eapply (SHP p k); [eassumption | reflexivity | exact (eq_sym Q)]
                    | eapply (gf_shadow_apart p k x); [ first [exact AC8 | exact RI8 | reflexivity] | reflexivity || (clear - CE; lia)
                        | first [right; clear - CE RIR; kung_all; lia | left; clear - CE; kung_all; lia] | rewrite Q; cbn [fst snd]; lia | exact IN] ]
          | stack_shadow_iv = _ => (first [ pose proof (stack_shadow_iv_facts) as dR_10; dand4 dR_10 as _ _ SSF SSL | pose proof stack_shadow_iv_facts as (_ & _ & SSF & SSL) ]); rewrite Q in SSF, SSL; cbn [fst snd] in SSF, SSL;
                                   clear - SSF SSL Hx IN GS CE; kung_all; lia
          | (p_sp0 _ - _, _) = _ => injection Q as Q1 Q2; subst b s; clear - Psp0 CE Hx IN MBC; lia
          | (p_ri _, _) = _ => injection Q as Q1 Q2; subst b s; clear - RIR D0 Hx IN; kung_all; lia
          | (p_pa _, _) = _ => injection Q as Q1 Q2; subst b s; clear - D1 Hx IN; kung_all; lia
          | _ => injection Q as Q1 Q2; subst b s; clear - D4 D5 D6 D7 D8 D9 D10 D14 Hx IN; kung_all; lia
          end.
      + (* [comment removed for export] *)
        (first [ pose proof ((classes_regions_inv _ _ _ _ Hbs)) as dR_11; dex1 dR_11 as c; destruct dR_11 as [Hc Hr] | pose proof ((classes_regions_inv _ _ _ _ Hbs)) as dR_11; dand3 dR_11 as c Hc Hr | destruct (classes_regions_inv _ _ _ _ Hbs) as (c & Hc & Hr) ]). (first [ pose proof ((wfR A W)) as dR_12; dand3 dR_12 as WR1 WR2 _ | destruct (wfR A W) as (WR1 & WR2 & _) ]).
        destruct (Z.eq_dec c 31) as [->|N31]. { rewrite (WR2 31) in Hr by lia. cbn in Hr. destruct Hr. }
        pose proof (region_piece_bounds A c W ltac:(lia)) as RB. cbv zeta in RB. unfold a_sb in RB.
        (first [ pose proof ((sb_facts A W)) as dR_13; dand5 dR_13 as _ _ HB6 RSB _ | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & _) ]). unfold a_sb, a_b6 in *.
        pose proof (proj1 (bm_nth_fixed A)) as E0. pose proof (gf_APART _ _ _ E0) as D0. unfold a_b6 in D0.
        assert (R8 : region_beg (p_sb (a_pl A)) c mod 8 = 0) by (apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| lia]).
        assert (F8 : (region_beg (p_sb (a_pl A)) c + kFreeArrayOffset) mod 8 = 0).
        { rewrite Z.add_mod by lia. rewrite (mod0_down (region_beg (p_sb (a_pl A)) c) 0x10000 8 ltac:(exists 8192; reflexivity) ltac:(lia)). reflexivity. }
        destruct (class_regions_inv _ _ _ _ Hr) as [[Q NZ]|[[Q NZ]|[[Q NZ]|[Q NZ]]]].
        * injection Q as Q1 Q2; subst b s. clear - RB HB6 RSB D0 Hx IN. kung_all. lia.
        * eapply (gf_shadow_apart (region_beg (p_sb (a_pl A)) c) (rg_mapped_user (a_reg A c)) x); [exact R8| lia| right; clear - RB CE; kung_all; lia| rewrite <- Q; cbn [fst snd]; lia| exact IN].
        * injection Q as Q1 Q2; subst b s. clear - RB HB6 RSB D0 Hx IN. kung_all. lia.
        * eapply (gf_shadow_apart (region_beg (p_sb (a_pl A)) c + kFreeArrayOffset) (rg_mapped_fa (a_reg A c)) x); [exact F8| lia| right; clear - RB CE; kung_all; lia| rewrite <- Q; cbn [fst snd]; lia| exact IN].
      + (* [comment removed for export] *)
        unfold sec_regions_ in Hbs. apply in_flat_map in Hbs as (sc & Hsc & Hr).
        (first [ pose proof ((sec_chunk_bounds A sc W Hsc)) as dR_14; dand5 dR_14 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A sc W Hsc) as (B1 & B2 & B3 & B4 & B5) ]). pose proof (map_size_room (cs_n sc)).
        apply app_facts in B3. apply In_nth_error' in Hsc as [j Hj]. pose proof (gf_APART _ _ _ (bm_nth_sec A j sc Hj)) as Dj.
        pose proof (rounded_size_ge (cs_n sc)) as RG. rewrite needed_size2_secondary in B5 by lia.
        destruct Hr as [Q|[Q|[]]].
        * injection Q as Q1 Q2; subst b s. clear - Dj Hx IN. lia.
        * eapply (gf_shadow_apart (cs_map sc) (map_size (cs_n sc)) x); [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact B2] | unfold kPageSize in *; lia
            | clear - B3 B4 CE; kung_all; lia | rewrite Q; cbn [fst snd]; lia | exact IN].
    - apply in_app_iff in Hin as [Hin|Hin].
      + (* [comment removed for export] *)
        (first [ pose proof ((wfE A W)) as dR_15; dand4 dR_15 as _ DF _ _ | destruct (wfE A W) as (_ & DF & _ & _) ]). (first [ pose proof ((proj1 (Forall_forall _ _) DF _ Hin)) as dR_16; dand4 dR_16 as B _ _ _ | pose proof (proj1 (Forall_forall _ _) DF _ Hin) as (B & _ & _ & _) ]). cbn [fst snd] in B.
        clear - B Hx IN GS. kung_all. lia.
      + (* [comment removed for export] *)
        destruct SC as (_ & _ & EXT).
        destruct (Z_lt_le_dec x alloc_ceiling) as [L|G]; [| lia].
        pose proof (EXT lo hi x Hin Hx ltac:(lia) ltac:(clear - IN GS; kung_all; lia)) as C.
        rewrite (gf_not_covered x IN) in C. discriminate.
  Qed.
  Corollary gf_hidc : forall x, mb <= x < mb + ms -> hidc (pa_hull A) (wz x) = true.
  Proof.
    intros x Hx. unfold hidc. rewrite unsigned_lit by lia. destruct (in_hullb (pa_hull A) x) eqn:E; [| reflexivity]. exfalso.
    apply in_hullb_true in E as (lo & hi & Hin & R). exact (gf_hidden lo hi x Hin R Hx).
  Qed.
  Corollary gf_view_none : forall x, mb <= x < mb + ms -> aview_of (pa_hull A) m (wz x) = None.
  Proof. intros x Hx. unfold aview_of, mrestrict. rewrite (gf_hidc x Hx). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma gf_sh : shadow_region mb ms = (sh mb, ms / 8).
  Proof. apply shadow_region_aligned; [apply (mod0_down _ 4096 64); [exists 64; reflexivity| exact MBA] | apply (mod0_down _ 4096 64); [exists 64; reflexivity| exact MSA] | lia]. Qed.
  Lemma gf_sh_range : forall z, sh mb <= z < sh mb + ms / 8 -> in_shadow_maps z /\ (kLowShadowBeg <= z /\ z < kHighMemBeg).
  Proof.
    intros z Hz. (first [ pose proof (gf_lin) as dR_17; dand3 dR_17 as G4 _ GS | pose proof gf_lin as (G4 & _ & GS) ]).
    destruct GS as [LOW|HIGH].
    - pose proof (sh_lowapp_range mb ltac:(kung_all; lia)). pose proof (sh_lowapp_range (mb + ms - 8) ltac:(kung_all; lia)).
      unfold sh in *. unfold in_shadow_maps. kung_all. lia.
    - pose proof (sh_high_range mb ltac:(kung_all; lia)). pose proof (sh_high_range (mb + ms - 8) ltac:(kung_all; lia)).
      unfold sh in *. unfold in_shadow_maps. kung_all. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma sh_apart : forall b' s' z, b' + s' <= mb \/ mb + ms <= b' -> 0 <= b' ->
    kShadowOffset + b' / 8 <= z < kShadowOffset + (b' + s') / 8 -> ~ (sh mb <= z < sh mb + ms / 8).
  Proof.
    intros b' s' z D Hb Hz IN. unfold sh in IN.
    pose proof (Z_div_mod_eq_full mb 8). pose proof (Z_div_mod_eq_full ms 8). pose proof (Z_div_mod_eq_full b' 8). pose proof (Z.mod_pos_bound b' 8 ltac:(lia)).
    pose proof (Z_div_mod_eq_full (b' + s') 8). pose proof (Z.mod_pos_bound (b' + s') 8 ltac:(lia)).
    assert (M1 : mb mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MBA]).
    assert (M2 : ms mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSA]).
    lia.
  Qed.
  Theorem gf_shadow : forall z, sh mb <= z < sh mb + ms / 8 -> ghost_hs_ (a_pl A) z /\ ~ heap_shadow A z.
  Proof.
    intros z Hz. pose proof (gf_sh_range z Hz) as [ISM SB]. (first [ pose proof (gf_lin) as dR_18; dand3 dR_18 as G4 GI GS | pose proof gf_lin as (G4 & GI & GS) ]).
    (first [ pose proof ((bm_nth_fixed A)) as dR_19; dand15 dR_19 as E0 E1 _ _ E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & _ & _ & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
    (first [ pose proof ((sb_facts A W)) as dR_20; dand5 dR_20 as _ SBM HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBM & HB6 & RSB & SCE) ]). unfold a_sb, a_b6, a_pa, a_thr, a_ctx, a_fs, a_nodes0, a_frames0, a_itab, a_m64k in *.
    (first [ pose proof ((place_facts A W)) as dR_21; dand14 dR_21 as Pthr Pctx Pn0 Pf0 Pfs Pitab Pm64k Pgvec Pdvec Pm11 Pdtls Ppa Psp0 _ | pose proof (place_facts A W) as (Pthr & Pctx & Pn0 & Pf0 & Pfs & Pitab & Pm64k & Pgvec & Pdvec & Pm11 & Pdtls & Ppa & Psp0 & _) ]).
    cbv zeta in Pthr, Pctx, Pn0, Pf0, Pfs, Pitab, Pm64k, Pgvec, Pdvec, Pm11, Pdtls, Ppa, Psp0.
    assert (APL : forall i p k k', nth_error (big_maps A) i = Some (p, k) -> app_rangeA AL_pboth p k /\ p + k <= alloc_ceiling /\ p mod 4096 = 0 -> 0 <= k' <= k ->
              ~ (kShadowOffset + p / 8 <= z < kShadowOffset + (p + k') / 8)).
    { (intros i p k k' Hi; (first [ intro dR_25; dand3 dR_25 as X1 _ _ | intros (X1 & _ & _) ]); intros Hk Hz'). apply app_facts in X1. apply (sh_apart p k' z); [pose proof (gf_APART _ _ _ Hi); clear - H Hk; lia| clear - X1; lia| exact Hz'| exact Hz]. }
    split.
    - split; [exact ISM|]. ((first [ intro dR_26; dex2 dR_26 as b nn; destruct dR_26 as [Hin Hzz] | intro dR_26; dand4 dR_26 as b nn Hin Hzz | intros (b & nn & Hin & Hzz) ])). unfold VIS0 in Hin. cbn [In] in Hin.
      assert (RIV : ~ (kShadowOffset + p_ri (a_pl A) / 8 <= z < kShadowOffset + (p_ri (a_pl A) + 4096) / 8)).
      { intros X. pose proof (gf_APART _ _ _ E0) as D0. apply (sh_apart (p_ri (a_pl A)) 4096 z); [unfold p_ri; clear - D0 HB6 RSB; kung_all; lia| unfold p_ri; kung_all; lia| exact X| exact Hz]. }
      assert (IMV : ~ (kShadowOffset + 0x10000 / 8 <= z < kShadowOffset + (0x10000 + 0x5fa000) / 8)).
      { intros X. apply (sh_apart 0x10000 0x5fa000 z); [clear - GI MSP; lia| lia| exact X| exact Hz]. }
      assert (STV : ~ (kShadowOffset + alloc_ceiling / 8 <= z < kShadowOffset + (alloc_ceiling + (2^47 - alloc_ceiling)) / 8)).
      { intros X. apply (sh_apart alloc_ceiling (2^47 - alloc_ceiling) z); [right; exact MBC| lia| exact X| exact Hz]. }
      (* [comment removed for export] *)
      destruct Hin as [Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[]]]]]]]]]]]]]]];
        (* [comment removed for export] *)
        [ injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E11 Pgvec _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E12 Pdvec _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E8 Pf0 _ Hzz); clear; kung_all; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E7 Pn0 _ Hzz); clear; kung_all; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E6 Pfs _ Hzz); clear; kung_all; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E4 Pthr _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E13 Pm11 _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E5 Pctx _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E14 Pdtls _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; exact (RIV Hzz)
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E9 Pitab _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; refine (APL _ _ _ _ E10 Pm64k _ Hzz); clear; lia
        | injection Q as Q1 Q2; subst b nn; exact (IMV Hzz)
        | unfold stack_band_iv in Q; injection Q as Q1 Q2; subst b nn; exact (STV Hzz) ].
    - intros HS. unfold heap_shadow, heap_shadow_ in HS. change (p_sb (a_pl A)) with (a_sb A) in HS.
      pose proof (gf_APART _ _ _ E0) as D0.
      destruct HS as [(c & Hc & Hzz)|[(c & Hc & Hzz)|(sc & Hsc & Hzz)]]; cbv zeta in Hzz.
      + pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB.
        apply (sh_apart (region_beg (a_sb A) c) (rg_mapped_user (a_reg A c)) z); [| clear - RB; kung_all; lia| | exact Hz].
        * unfold a_sb in *. clear - RB D0 HB6 RSB. kung_all. lia.
        * unfold sh in Hzz. pose proof (sh_add' := I). assert (E : (region_beg (a_sb A) c + rg_mapped_user (a_reg A c)) / 8 = region_beg (a_sb A) c / 8 + rg_mapped_user (a_reg A c) / 8) by (clear - RB; lia). clear - Hzz E. kung_all. lia.
      + pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB.
        apply (sh_apart (region_beg (a_sb A) c + kFreeArrayOffset) (rg_mapped_fa (a_reg A c)) z); [| clear - RB; kung_all; lia| | exact Hz].
        * unfold a_sb in *. clear - RB D0 HB6 RSB. kung_all. lia.
        * unfold sh in Hzz. assert (E : (region_beg (a_sb A) c + kFreeArrayOffset + rg_mapped_fa (a_reg A c)) / 8 = (region_beg (a_sb A) c + kFreeArrayOffset) / 8 + rg_mapped_fa (a_reg A c) / 8) by (clear - RB; kung_all; lia). clear - Hzz E. kung_all. lia.
      + (first [ pose proof ((sec_chunk_bounds A sc W Hsc)) as dR_22; dand5 dR_22 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A sc W Hsc) as (B1 & B2 & B3 & B4 & B5) ]). apply app_facts in B3.
        apply In_nth_error' in Hsc as [j Hj]. pose proof (gf_APART _ _ _ (bm_nth_sec A j sc Hj)) as Dj.
        pose proof (map_size_page (cs_n sc)) as MP.
        apply (sh_apart (cs_map sc) (map_size (cs_n sc)) z); [exact Dj| clear - B3; lia| | exact Hz].
        unfold sh in Hzz. assert (E : (cs_map sc + map_size (cs_n sc)) / 8 = cs_map sc / 8 + map_size (cs_n sc) / 8) by (clear - B2 MP; unfold kPageSize in MP; lia). clear - Hzz E. kung_all. lia.
  Qed.
  (* [comment removed for export] *)
End GrantFacts.
