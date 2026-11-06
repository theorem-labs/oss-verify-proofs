(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARt2_lib AMalmys ABudget.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AQPart ATransp ATranspR AFreeRS AFreeRT AFreeRI AFreeRK2 AFreeRP AFreeRQ AFreeRU.

Module AFreeRW.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AQPart ATransp ATranspR AFreeRS AFreeRT AFreeRI AFreeRK2 AFreeRU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kFreeArraySize, kLowShadowMapBeg, kPtrArrayReserve in *.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Lemma classes_eager_exteq : forall reg1 reg2 n, (forall c, reg1 c = reg2 c) -> classes_eager_ reg1 n = classes_eager_ reg2 n.
Proof. intros reg1 reg2 n E. induction n as [|n IH]; [reflexivity|]. cbn [classes_eager_]. rewrite IH, (E (Z.of_nat (S n))). reflexivity. Qed.

Section RW.
Context {Clg : Ceiling}.
  Variables (A : AState) (c : Z) (reg' : Z -> region) (cache' : Z -> pcache) (limbo' : list batch) (d : Z).
  Let A' := mkA (a_pl A) reg' (a_cache_inited A) cache' (a_livemap A) [] (a_qglobal A) (a_sec A) (a_depot A) (a_fhint A) (a_fframes A)
                (a_ia_inited A) (a_oom A) (a_tiny A) limbo' (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
  Hypothesis W : WFT A.
  Hypothesis CR : 1 <= c <= 30.
  Hypothesis D0 : 0 <= d.
  Hypothesis RO : forall c', c' <> c -> reg' c' = a_reg A c'.
  Hypothesis RC : rg_mapped_user (reg' c) = rg_mapped_user (a_reg A c) /\ rg_mapped_fa (reg' c) = rg_mapped_fa (a_reg A c) + d.
  Hypothesis FAC : rg_mapped_fa (a_reg A c) + d <= kFreeArraySize.
  Local Notation sb := (a_sb A).
  Local Notation fa := (region_beg (a_sb A) c + kFreeArrayOffset).
  Local Notation mfa := (rg_mapped_fa (a_reg A c)).

  (* [comment removed for export] *)
  Lemma gw_ext_le : forall c', 0 <= rg_mapped_user (a_reg A c') <= rg_mapped_user (reg' c') /\ 0 <= rg_mapped_fa (a_reg A c') <= rg_mapped_fa (reg' c').
  Proof.
    intros c'. (first [ pose proof ((wtR A W)) as dR_1; dand3 dR_1 as WR WZ _ | destruct (wtR A W) as (WR & WZ & _) ]).
    assert (NN : 0 <= rg_mapped_user (a_reg A c') /\ 0 <= rg_mapped_fa (a_reg A c')).
    { destruct (Z_le_dec 1 c') as [L|L]; [destruct (Z_le_dec c' 30) as [L2|L2]|].
      - (first [ pose proof ((region_piece_boundsT A c' W ltac:(lia))) as dR_2; dand6 dR_2 as _ _ Q3 _ Q5 _ | pose proof (region_piece_boundsT A c' W ltac:(lia)) as (_ & _ & Q3 & _ & Q5 & _) ]). lia.
      - rewrite (WZ c') by lia. cbn. lia.
      - rewrite (WZ c') by lia. cbn. lia. }
    destruct (Z.eq_dec c' c) as [->|NE]; [destruct RC as [E1 E2]; rewrite E1, E2; lia| rewrite (RO c' NE); lia].
  Qed.
  Lemma gw_reg_upd : forall c', reg' c' = reg_upd (a_reg A) c (reg' c) c'.
  Proof. intros c'. unfold reg_upd. destruct (Z.eqb_spec c' c) as [->|NE]; [reflexivity| exact (RO c' NE)]. Qed.

  Lemma gw_hull_le : hull_le (pa_hull A) (pa_hull A').
  Proof.
    unfold pa_hull, ahull_of, ahull_of_, aregions_. subst A'. cbn [a_pl a_reg a_sec a_deadsh].
    rewrite !hull_of_app.
    apply hull_le_app2; [apply hull_le_refl|]. apply hull_le_app2; [| apply hull_le_refl].
    apply hull_le_app2; [apply hull_le_refl|]. apply hull_le_app2; [| apply hull_le_refl].
    apply classes_regions_le. exact gw_ext_le.
  Qed.
  (* [comment removed for export] *)
  Lemma gw_lhull_le : hull_le (pa_lhull A) (pa_lhull A').
  Proof.
    unfold pa_lhull, alhull_of, alhull_of_, alregions_. subst A'. cbn [a_pl a_reg a_sec a_deadsh].
    rewrite !hull_of_app.
    apply hull_le_app2; [| apply hull_le_refl]. apply hull_le_app2; [apply hull_le_refl|]. apply hull_le_app2; [| apply hull_le_refl].
    apply lclasses_regions_le. exact gw_ext_le.
  Qed.
  Lemma gw_aledger : forall md, aledger_ AL_pasan (a_pl A) (a_reg A) (a_sec A) md -> lazy_free (m_vm_lazy md) (fa + mfa) (fa + mfa + d) ->
    aledger_ AL_pasan (a_pl A) reg' (a_sec A) md.
  Proof.
    intros md LED LZ. apply (aledger_upd _ _ (a_reg A) _ _ _ LED). pose proof (aledger_lzfree _ _ _ _ _ LED) as Z9.
    apply (alzfree_upd _ _ (a_reg A) reg' md c Z9).
    - intros c' _ NE. rewrite (RO c' NE). split; reflexivity.
    - destruct Z9 as (_ & _ & Z3). destruct RC as [E1 _]. rewrite E1. exact (proj1 (Z3 c ltac:(lia))).
    - destruct Z9 as (_ & _ & Z3). destruct RC as [_ E2]. rewrite E2. apply (lazy_free_join _ _ (fa + mfa)); [exact (proj2 (Z3 c ltac:(lia)))|].
      unfold a_sb in LZ |- *. replace (region_beg (p_sb (a_pl A)) c + kFreeArrayOffset + (mfa + d)) with (region_beg (p_sb (a_pl A)) c + kFreeArrayOffset + mfa + d) by lia. exact LZ.
  Qed.
  (* [comment removed for export] *)

  Lemma gw_eager : pa_eager A' = pa_eager A + d.
  Proof.
    unfold pa_eager, aeager_of, aeager_of_. subst A'. cbn [a_pl a_reg a_sec].
    rewrite (classes_eager_exteq reg' (reg_upd (a_reg A) c (reg' c)) 31 gw_reg_upd).
    rewrite (classes_eager_upd (a_reg A) c _ 31) by lia. destruct RC as [E1 E2]. rewrite E1, E2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma gw_runtime_maps_in : forall b s, In (b, s) (runtime_maps A) -> exists b' s', In (b', s') (runtime_maps A') /\ b' <= b /\ b + s <= b' + s'.
  Proof.
    intros b s Hin. unfold runtime_maps, runtime_maps_ in *. subst A'. cbn [a_pl a_reg a_sec] in *.
    apply in_app_iff in Hin as [Hin|Hin].
    { exists b, s. split; [apply in_or_app; left; exact Hin| lia]. }
    apply in_app_iff in Hin as [Hin|Hin].
    2: { exists b, s. split; [apply in_or_app; right; apply in_or_app; right; exact Hin| lia]. }
    apply in_flat_map in Hin as (c' & Hc' & Hin).
    lazymatch goal with |- context [flat_map ?F ?l] =>
      assert (E : exists b' s', In (b', s') (F c') /\ b' <= b /\ b + s <= b' + s');
      [| (first [ dex2 E as b' s'; destruct E as [E1 E2] | dand4 E as b' s' E1 E2 | destruct E as (b' & s' & E1 & E2) ]); exists b', s'; split; [| exact E2]; apply in_or_app; right; apply in_or_app; left; apply in_flat_map; exists c'; split; [exact Hc'| exact E1]]
    end.
    cbv beta. pose proof (gw_ext_le c') as [X1 X2].
    destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-.
    - eexists _, _. split; [left; reflexivity| lia].
    - eexists _, _. split; [right; left; reflexivity| lia].
  Qed.
  Lemma gw_heap_shadow_mono : forall z, heap_shadow A z -> heap_shadow A' z.
  Proof.
    intros z Hz. unfold heap_shadow, heap_shadow_, a_sb in *. subst A'. cbn [a_pl a_reg a_sec].
    destruct Hz as [(c' & Hc' & Hz)|[(c' & Hc' & Hz)|Hz]]; [left| right; left| right; right; exact Hz]; exists c'; (split; [exact Hc'|]);
      cbv zeta in *; pose proof (gw_ext_le c') as [X1 X2].
    - assert (M : rg_mapped_user (a_reg A c') / 8 <= rg_mapped_user (reg' c') / 8) by (apply Z.div_le_mono; lia). lia.
    - assert (M : rg_mapped_fa (a_reg A c') / 8 <= rg_mapped_fa (reg' c') / 8) by (apply Z.div_le_mono; lia). lia.
  Qed.
  Lemma gw_owned_mono : forall a, pa_owned A a -> pa_owned A' a.
  Proof.
    pose proof gw_runtime_maps_in as gw_runtime_maps_in'. pose proof gw_heap_shadow_mono as gw_heap_shadow_mono'.
    intros a [Ha|Ha]; [left| right; exact Ha]. unfold aowned, aowned_ in *. subst A'. cbn [a_pl a_reg a_livemap a_sec a_fframes] in *.
    destruct Ha as [Ha|[[(Hr & NU & NF)|[Hs|Hf]]|Hg]]; [left; exact Ha| right; left| right; left; right; left| right; left; right; right; exact Hf| right; right; exact Hg].
    - left. split; [| exact (conj NU NF)]. (first [ dex2 Hr as b s; destruct Hr as [Hin Hb] | dand4 Hr as b s Hin Hb | destruct Hr as (b & s & Hin & Hb) ]). (first [ pose proof ((gw_runtime_maps_in' b s Hin)) as dR_5; dex2 dR_5 as b' s'; dand3 dR_5 as Hin' L1 L2 | pose proof ((gw_runtime_maps_in' b s Hin)) as dR_5; dand5 dR_5 as b' s' Hin' L1 L2 | destruct (gw_runtime_maps_in' b s Hin) as (b' & s' & Hin' & L1 & L2) ]).
      exists b', s'. split; [exact Hin'| lia].
    - exact (gw_heap_shadow_mono' a Hs).
  Qed.

  (* [comment removed for export] *)
  Lemma sh_apart_space : forall b n z, 0 <= n -> (b + n <= sb \/ sb + kSpaceSize <= b) ->
    sh sb <= z < sh sb + kSpaceSize / 8 -> ~ (kShadowOffset + b / 8 <= z < kShadowOffset + (b + n) / 8).
  Proof.
    intros b n z N AP Hz X. (first [ pose proof ((sb_factsT A W)) as dR_6; dand3 dR_6 as _ SBM _ | pose proof (sb_factsT A W) as (_ & SBM & _) ]).
    set (q := sb / 8) in *.
    assert (SB8 : sb = q * 8).
    { subst q. pose proof (Z_div_mod_eq_full sb 8). rewrite (mod0_down _ 0x10000 8 ltac:(exists 8192; reflexivity) SBM) in H. unfold a_sb in *. lia. }
    unfold sh in Hz. rewrite SB8, Z.div_mul in Hz by lia.
    assert (KS : kSpaceSize / 8 = 17179869184) by reflexivity. rewrite KS in Hz.
    destruct AP as [AP|AP].
    - assert (M : (b + n) / 8 <= (q * 8) / 8) by (apply Z.div_le_mono; lia). rewrite Z.div_mul in M by lia. lia.
    - assert (M : (q * 8 + kSpaceSize) / 8 <= b / 8) by (apply Z.div_le_mono; lia).
      replace (q * 8 + kSpaceSize) with ((q + 17179869184) * 8) in M by (unfold kSpaceSize; lia). rewrite Z.div_mul in M by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma gw_prim_shadow_ghost : forall z, sh sb <= z < sh sb + kSpaceSize / 8 -> ghost_hs_ (a_pl A) z.
  Proof.
    intros z Hz. (first [ pose proof ((sb_factsT A W)) as dR_7; dand5 dR_7 as S1 S2 S3 S4 S5 | pose proof (sb_factsT A W) as (S1 & S2 & S3 & S4 & S5) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bm_nth_fixed A)) as dR_8; dand15 dR_8 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
    assert (APB : forall i b n, nth_error (big_maps A) i = Some (b, n) -> (i <> 0)%nat -> b + n <= sb \/ sb + kSpaceSize <= b).
    { intros i b n Hi NZ. pose proof (bm_sepT A 0 i _ _ _ _ W E0 Hi ltac:(lia)) as D. unfold a_b6, a_sb in *. clear -D S4. kung_all. lia. }
    split.
    - unfold in_shadow_maps. right. unfold sh, a_sb in *. clear -Hz S3 S4 S5 CE. kung_all. lia.
    - ((first [ intro dR_12; dex2 dR_12 as b n; destruct dR_12 as [Hin Hb] | intro dR_12; dand4 dR_12 as b n Hin Hb | intros (b & n & Hin & Hb) ])). unfold VIS0 in Hin. cbn [In] in Hin.
      destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]]]]]]]]]];
        first [injection Hin as <- <- | rewrite <- Hin in Hb; unfold stack_band_iv in Hb; cbn [fst snd] in Hb];
        (eapply (sh_apart_space _ _ z); [| | exact Hz| exact Hb]).
      all: first [ exact (APB 11%nat _ _ E11 ltac:(lia)) | exact (APB 12%nat _ _ E12 ltac:(lia)) | exact (APB 8%nat _ _ E8 ltac:(lia))
                 | exact (APB 7%nat _ _ E7 ltac:(lia)) | exact (APB 6%nat _ _ E6 ltac:(lia)) | exact (APB 4%nat _ _ E4 ltac:(lia))
                 | exact (APB 13%nat _ _ E13 ltac:(lia)) | exact (APB 5%nat _ _ E5 ltac:(lia)) | exact (APB 14%nat _ _ E14 ltac:(lia))
                 | exact (APB 9%nat _ _ E9 ltac:(lia)) | exact (APB 10%nat _ _ E10 ltac:(lia))
                 | right; unfold p_ri, a_sb; clear; lia
                 | left; unfold a_sb in *; clear -S3 S4; kung_all; lia
                 | right; unfold a_sb in *; clear -S5; kung_all; lia
                 | clear -CE; unfold kFakeStackBytes; kung_all; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma gw_owned_new : forall a, pa_owned A' a -> pa_owned A a \/ (fa + mfa <= a < fa + mfa + d).
  Proof.
    intros a [Ha|Ha]; [| left; right; exact Ha]. unfold aowned, aowned_ in Ha. subst A'. cbn [a_pl a_reg a_livemap a_sec a_fframes] in Ha.
    unfold pa_owned, aowned, aowned_, a_sb.
    destruct Ha as [Ha|[[(Hr & NU & NF)|[Hs|Hf]]|Hg]].
    - left. left. left. exact Ha.
    - (first [ dex2 Hr as b s; destruct Hr as [Hin Hb] | dand4 Hr as b s Hin Hb | destruct Hr as (b & s & Hin & Hb) ]). unfold runtime_maps_ in Hin. apply in_app_iff in Hin as [Hin|Hin].
      { left. left. right. left. left. split; [| exact (conj NU NF)]. exists b, s. split; [apply in_or_app; left; exact Hin| exact Hb]. }
      apply in_app_iff in Hin as [Hin|Hin].
      2: { left. left. right. left. left. split; [| exact (conj NU NF)]. exists b, s. split; [apply in_or_app; right; apply in_or_app; right; exact Hin| exact Hb]. }
      apply in_flat_map in Hin as (c' & Hc' & Hin). cbv beta in Hin.
      destruct (Z.eq_dec c' c) as [->|NE].
      + destruct RC as [E1 E2]. rewrite E1, E2 in Hin. destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-.
        * left. left. right. left. left. split; [| exact (conj NU NF)]. exists (region_beg (p_sb (a_pl A)) c), (rg_mapped_user (a_reg A c)). split; [| lia].
          apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists c. split; [exact Hc'| left; reflexivity].
        * destruct (Z_lt_le_dec a (region_beg (p_sb (a_pl A)) c + kFreeArrayOffset + mfa)) as [L|L]; [| right; unfold a_sb; lia].
          left. left. right. left. left. split; [| exact (conj NU NF)]. exists (region_beg (p_sb (a_pl A)) c + kFreeArrayOffset), mfa. split; [| lia].
          apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists c. split; [exact Hc'| right; left; reflexivity].
      + rewrite (RO c' NE) in Hin. left. left. right. left. left. split; [| exact (conj NU NF)]. exists b, s. split; [| exact Hb].
        apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists c'. split; [exact Hc'|]. exact Hin.
    - unfold heap_shadow_ in Hs. cbv zeta in Hs.
      destruct Hs as [(c' & Hc' & Hs)|[(c' & Hc' & Hs)|Hs]].
      + left. left. right. left. right. left. left.
        destruct (Z.eq_dec c' c) as [->|NE]; [destruct RC as [E1 _]; rewrite E1 in Hs; exists c; tauto| rewrite (RO c' NE) in Hs; exists c'; tauto].
      + destruct (Z.eq_dec c' c) as [->|NE].
        * (* [comment removed for export] *)
          left. left. right. right. apply gw_prim_shadow_ghost. destruct RC as [_ E2]. rewrite E2 in Hs.
          (first [ pose proof ((region_piece_boundsT A c W CR)) as dR_10; dand10 dR_10 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 _ | pose proof (region_piece_boundsT A c W CR) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & _) ]). cbv zeta in *.
          (first [ pose proof ((sb_factsT A W)) as dR_11; dand3 dR_11 as _ SBM _ | pose proof (sb_factsT A W) as (_ & SBM & _) ]).
          assert (LO1 : sh (p_sb (a_pl A)) <= sh (region_beg (p_sb (a_pl A)) c + kFreeArrayOffset)) by (apply sh_mono; unfold a_sb in *; lia).
          assert (HI1 : sh (region_beg (p_sb (a_pl A)) c + kFreeArrayOffset) + (mfa + d) / 8 <= sh (p_sb (a_pl A)) + kSpaceSize / 8).
          { unfold sh. unfold a_sb, region_beg in *. kung_all.
            set (q := p_sb (a_pl A) / 8) in *.
            assert (SB8 : p_sb (a_pl A) = q * 8).
            { subst q. pose proof (Z_div_mod_eq_full (p_sb (a_pl A)) 8). rewrite (mod0_down _ 0x10000 8 ltac:(exists 8192; reflexivity) SBM) in H. lia. }
            replace (p_sb (a_pl A) + c * 2 ^ 32 + 3758096384) with ((q + c * 536870912 + 469762048) * 8) by lia.
            rewrite !Z.div_mul by lia.
            assert (M : (mfa + d) / 8 <= 536870912 / 8) by (apply Z.div_le_mono; lia). change (536870912 / 8) with 67108864 in M.
            change (2 ^ 37 / 8) with 17179869184. clear -M CR. lia. }
          unfold a_sb. lia.
        * rewrite (RO c' NE) in Hs. left. left. right. left. right. left. right. left. exists c'. tauto.
      + left. left. right. left. right. left. right. right. exact Hs.
    - left. left. right. left. right. right. exact Hf.
    - left. left. right. right. exact Hg.
  Qed.

  (* [comment removed for export] *)
  Lemma gw_hidden : forall (m m' : mem),
    hidden_repr (a_pl A) (a_reg A) (a_sec A) m ->
    (forall z, ghost_hs_ (a_pl A) z -> m (wz z) <> None -> m' (wz z) <> None) ->
    (forall z, ghost_hs_ (a_pl A) z -> ~ heap_shadow A' z -> m' (wz z) = m (wz z)) ->
    (forall z, kLowShadowMapBeg <= z < kLowShadowMapBeg + 0x10000000 -> ~ in_vis_shadow (VIS0 (a_pl A)) z -> m (wz z) <> None -> m' (wz z) <> None) ->
    hidden_repr (a_pl A') (a_reg A') (a_sec A') m'.
  Proof.
    pose proof gw_heap_shadow_mono as HSM.
    intros m m' [H1 H2] NNg AGg NNl. subst A'. cbn [a_pl a_reg a_sec]. unfold hidden_repr. split.
    - intros z Gz. destruct (H1 z Gz) as [P1 P2]. split; [exact (NNg z Gz P1)|].
      intros NH. assert (NH0 : ~ heap_shadow A z) by (intros HS; apply NH; exact (HSM z HS)).
      rewrite (AGg z Gz NH). exact (P2 NH0).
    - intros z Hz NV. apply (NNl z Hz NV). exact (H2 z Hz NV).
  Qed.

  (* [comment removed for export] *)
  Lemma gw_virgin : forall c', a_reg A c <> region_zero -> (forall c'', c'' <> c -> cache' c'' = a_cache A c'') ->
    a_virgin A c' -> a_virgin A' c'.
  Proof.
    intros c' NZ CO [R0 K0]. subst A'. unfold a_virgin. cbn [a_reg a_cache].
    destruct (Z.eq_dec c' c) as [->|NE]; [exfalso; exact (NZ R0)|]. rewrite (RO c' NE), (CO c' NE). exact (conj R0 K0).
  Qed.
End RW.
End AFreeRW.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRP OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRQ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRW2.AFreeRW.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dl_first | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma thread_cells_munch {Clg : Ceiling} : forall W (m m' : mem) tp tsd ctx thr,
  thread_cells m tp tsd ctx thr -> munch W m m' -> tp = Z_to_bv 64 0x5e83d8 -> 0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000 ->
  (forall a l, 0x10000 <= a -> a + l <= 0x60a000 -> disjoint_from W a l) -> disjoint_from W (ctx + 152) 8 ->
  thread_cells m' tp tsd ctx thr.
Proof.
  (intros W m m' tp tsd ctx thr; (first [ intro dR_22; dand6 dR_22 as X1 X2 X3 X4 X5 X6 | intros (X1 & X2 & X3 & X4 & X5 & X6) ]); intros MU TPE TSDL IMG DC).
  assert (TPL : bv_unsigned tp = 0x5e83d8) by (rewrite TPE; apply unsigned_lit; lia).
  eapply (ro_cells_transport rsegs _ m m') in X1; [| exact MU| apply IMG; cbn; lia].
  eapply (ro_cells_transport rsegs _ m m') in X2; [| exact MU| apply IMG; cbn; lia].
  eapply (ro_cells_transport rsegs _ m m') in X3; [| exact MU| apply IMG; rewrite TPL; cbn; lia].
  eapply (ro_cells_transport rsegs _ m m') in X4; [| exact MU| apply IMG; cbn; lia].
  eapply (ro_cells_transport rsegs _ m m') in X5; [| exact MU| exact DC].
  exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 X6))))).
Qed.

(* [comment removed for export] *)
Lemma poison_consts_munch : forall W (m m' : mem),
  poison_consts m -> munch W m m' -> (forall a l, 0x10000 <= a -> a + l <= 0x60a000 -> disjoint_from W a l) -> poison_consts m'.
Proof.
  (intros W m m'; (first [ intro dR_23; dand13 dR_23 as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 | intros (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13) ]); intros MU IMG).
  unfold poison_consts. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
    (eapply (ro_cells_transport rsegs _ m m'); [eassumption| exact MU| apply IMG; cbn; lia]).
Qed.

(* [comment removed for export] *)
Lemma mapped_u32arr : forall (m : mem) a (h : nat), mapped m a (Z.of_nat (4 * h)) -> 0 <= a -> a + Z.of_nat (4 * h) <= 2^64 ->
  exists junk : list word, length junk = h /\ u32arr rsegs m a junk.
Proof.
  intros m a h MJ A0 A1. pose proof (rdbytes_bytes_at m a (4 * h) MJ A0 A1) as BJ.
  exists (words4 (rdbytes m a (4 * h)) h). split; [apply words4_length|]. split.
  - rewrite u32s_words4 by (rewrite rdbytes_length; lia). exact BJ.
  - rewrite words4_length. apply mapped_wr_at; [replace (4 * Z.of_nat h) with (Z.of_nat (4 * h)) by lia; exact MJ| exact A0| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RQ2.
Context {Clg : Ceiling}.
  Lemma region_return_of_cells_grow : forall (v v' : mem) sb (R : region) c (out : list Z) (w80 w88 : word) (mfa' : Z),
    1 <= c <= 30 ->
    let ria := region_info_addr sb c in let fa := free_array_beg sb c in let nf := Z.of_nat (length (rg_free R)) in
    region_repr_ LPA sb R v c ->
    0 <= nf + Z.of_nat (length out) < 2^64 -> 0 <= mfa' < 2^64 ->
    (forall a, ria + 32 <= a < ria + 80 -> v' (wz a) = v (wz a)) ->
    (forall a, ria + 96 <= a < ria + 128 -> v' (wz a) = v (wz a)) ->
    (forall a, fa <= a < fa + 4 * nf -> v' (wz a) = v (wz a)) ->
    mapped v' fa mfa' ->
    (forall a, region_beg sb c <= a < region_beg sb c + rg_mapped_user R -> v (wz a) <> None -> v' (wz a) <> None) ->
    rw_cells rsegs v' (ria + 16) [C8 (wz (nf + Z.of_nat (length out)))] ->
    rw_cells rsegs v' (ria + 24) [C8 (wz mfa')] ->
    rw_cells rsegs v' (ria + 80) [C8 w80; C8 w88] ->
    u32arr rsegs v' (fa + 4 * nf) (map (fun k => Z_to_bv 64 (k * class_size c / kCompactPtrScale)) out) ->
    region_repr_ LPA sb (reg_return R out mfa') v' c.
  Proof.
    intros v v' sb R c out w80 w88 mfa' Hc. cbv zeta. intros RR NFR MFR AG1 AG2 AG3 MFA' NNu C16 C24 C80 ARR.
    unfold region_repr_ in RR |- *. cbv zeta in RR |- *.
    (first [ dand13 RR as Hnf Hfa Hal Ham Hmu Hmm Hex J64 Jna Jrt ENT MFA MUS | destruct RR as (Hnf & Hfa & Hal & Ham & Hmu & Hmm & Hex & J64 & Jna & Jrt & ENT & MFA & MUS) ]).
    rewrite reg_return_free, reg_return_mapped_fa, reg_return_allocated, reg_return_mapped_user.
    unfold off_ri_num_freed, off_ri_mapped_free_array, off_ri_allocated_user, off_ri_allocated_meta, off_ri_mapped_user, off_ri_mapped_meta,
           off_ri_exhausted, off_ri_n_allocated, off_ri_rtoi in *.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - rewrite length_app, Nat2Z.inj_add. apply u64_of_rw; [exact NFR| exact C16].
    - apply u64_of_rw; [exact MFR| exact C24].
    - eapply u64_at_agree; [exact Hal|]. intros i Hi. apply AG1. lia.
    - eapply u64_at_agree; [exact Ham|]. intros i Hi. apply AG1. lia.
    - eapply u64_at_agree; [exact Hmu|]. intros i Hi. apply AG1. lia.
    - eapply u64_at_agree; [exact Hmm|]. intros i Hi. apply AG1. lia.
    - eapply u8_at_agree; [exact Hex|]. apply AG1. lia.
    - eapply junk_at_agree; [exact J64|]. intros i Hi. apply AG1. lia.
    - (* [comment removed for export] *)
      (first [ dex1 Jna as bs; destruct Jna as [L B] | dand3 Jna as bs L B | destruct Jna as (bs & L & B) ]). destruct C80 as [[_ B80] _]. cbn [cells_bytes cbytes] in B80. rewrite app_nil_r in B80. apply bytes_at_app in B80 as [B80 _].
      exists (firstn 8 bs ++ le8 w80). split; [rewrite length_app, firstn_length_le, length_le8 by lia; lia|].
      apply bytes_at_app. split.
      + pose proof (bytes_at_mid v _ bs 0 8 B ltac:(lia)) as X. rewrite Z.add_0_r, skipn_O in X.
        eapply bytes_at_agree_gen; [exact X|]. intros i Hi. rewrite firstn_length_le in Hi by lia. apply AG1. lia.
      + rewrite firstn_length_le by lia. replace (region_info_addr sb c + 72 + Z.of_nat 8) with (region_info_addr sb c + 80) by lia. exact B80.
    - (* [comment removed for export] *)
      (first [ dex1 Jrt as bs; destruct Jrt as [L B] | dand3 Jrt as bs L B | destruct Jrt as (bs & L & B) ]). destruct C80 as [[_ B80] _]. cbn [cells_bytes cbytes] in B80. rewrite app_nil_r in B80. apply bytes_at_app in B80 as [_ B88]. rewrite length_le8 in B88.
      exists (le8 w88 ++ skipn 8 bs). split; [rewrite length_app, length_le8, length_skipn; lia|].
      apply bytes_at_app. split.
      + replace (region_info_addr sb c + 88) with (region_info_addr sb c + 80 + Z.of_nat 8) by lia. exact B88.
      + rewrite length_le8. pose proof (bytes_at_mid v _ bs 8 32 B ltac:(lia)) as X. rewrite firstn_all2 in X by (rewrite length_skipn; lia).
        eapply bytes_at_agree_gen; [exact X|]. intros i Hi. rewrite length_skipn in Hi. apply AG2. lia.
    - intros i k Hk. destruct (Nat.lt_ge_cases i (length (rg_free R))) as [LT|GE].
      + rewrite nth_error_app1 in Hk by exact LT. eapply u32_at_agree; [exact (ENT i k Hk)|]. intros j Hj. apply AG3. lia.
      + rewrite nth_error_app2 in Hk by exact GE. destruct ARR as [BA _].
        pose proof (nth_error_Some_lt _ _ _ Hk) as IL.
        pose proof (bytes_at_mid v' _ _ (4 * (i - length (rg_free R))) 4 BA ltac:(rewrite u32s_length, length_map; lia)) as X.
        rewrite (u32s_nth _ (i - length (rg_free R))%nat (Z_to_bv 64 (k * class_size c / kCompactPtrScale))) in X by (rewrite nth_error_map, Hk; reflexivity).
        unfold u32_at. replace (free_array_beg sb c + 4 * Z.of_nat i) with (free_array_beg sb c + 4 * Z.of_nat (length (rg_free R)) + Z.of_nat (4 * (i - length (rg_free R)))) by lia.
        exact X.
    - exact MFA'.
    - intros i Hi. apply NNu; [lia|]. apply MUS. lia.
  Qed.
End RQ2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FreshHidden.
Context {Clg : Ceiling}.
  Variable A : AState.
  Hypothesis W : WFT A.
  Hypothesis X : wf_extra LPA pa_site_pcs (a_pl A).
  Hypothesis DEAD : forall lo hi, In (lo, hi) (a_deadsh A) -> hi <= kHighMemBeg.

  #[using="DEAD X W"] Lemma prim_unmapped_hidden : forall c x, 1 <= c <= 30 ->
    (region_beg (a_sb A) c + rg_mapped_user (a_reg A c) <= x < region_beg (a_sb A) c + kFreeArrayOffset \/
     region_beg (a_sb A) c + kFreeArrayOffset + rg_mapped_fa (a_reg A c) <= x < region_beg (a_sb A) c + kRegionSize) ->
    in_hullb (pa_hull A) x = false.
  Proof.
    intros c x CR Hx. destruct (in_hullb (pa_hull A) x) eqn:EH; [| reflexivity]. exfalso.
    apply in_hullb_true in EH as (lo & hi & Hin & R).
    pose proof alloc_ceiling_val as CE.
    pose proof (region_piece_boundsT A c W CR) as RB. cbv zeta in RB. (first [ dand12 RB as B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 _ B12 | destruct RB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & _ & B12) ]).
    assert (XS : a_sb A <= x < a_sb A + kSpaceSize /\ kHighMemBeg <= x < 2^47).
    { clear -Hx B1 B2 B3 B4 B5 B6 B7 B8 CE. unfold kRegionSize, kSpaceSize, kFreeArrayOffset, kHighMemBeg in *. lia. }
    pose proof (primary_in_b6T A x W ltac:(clear -XS; lia)) as XB6.
    (first [ pose proof ((bm_nth_fixed A)) as dR_5; dand15 dR_5 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
    assert (BM : forall i bb bs, (1 <= i)%nat -> nth_error (big_maps A) i = Some (bb, bs) -> bb <= x < bb + bs -> False).
    { intros i bb bs Hi Hn Hb. destruct (bm_sepT A i 0 _ _ _ _ W Hn E0 ltac:(lia)); clear -H Hb XB6; lia. }
    unfold pa_hull, ahull_of, ahull_of_ in Hin. apply in_app_iff in Hin as [Hin|Hin].
    { (* [comment removed for export] *) cbn in Hin. destruct XS as [_ XH]. unfold kHighMemBeg in XH.
      repeat match type of Hin with _ \/ _ => destruct Hin as [Q|Hin]; [injection Q as <- <-; clear -R XH; lia|] end. destruct Hin. }
    apply in_app_iff in Hin as [Hin|HinX].
    2:{ apply in_app_iff in HinX as [HinD|HinX].
        - pose proof (DEAD _ _ HinD) as D. clear -D R XS. lia.
        - destruct X as (_ & _ & _ & _ & _ & _ & WX4 & _). apply (WX4 lo hi x HinX R). unfold a_sb in XS. exact (proj1 XS). }   (* [comment removed for export] *)
    unfold hull_of in Hin. apply in_map_iff in Hin as ([b s] & Eq & Hbs). cbn in Eq. injection Eq as <- <-.
    assert (NOTAPP : forall b' s', ((4096 <= b' /\ b' + s' <= kLowShadowMapBeg) \/ (kHighMemBeg <= b' /\ b' + s' <= 2^47)) ->
                     0 < s' -> b' mod 8 = 0 -> (b, s) = shadow_region b' s' -> False).
    { intros b' s' Q1 Q3 Q8 Q4. apply (strict_not_app x); [| right; exact (proj1 (proj2 XS))].
      apply (shadow_region_strict b' s' x Q8 Q3 Q1). rewrite <- Q4. cbn [fst snd]. exact R. }
    assert (M8 : forall p, p mod 4096 = 0 -> p mod 8 = 0) by (intros p Hp; apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact Hp]).
    pose proof (place_factsT A W) as PF. cbv zeta in PF.
    (first [ dand14 PF as (T1 & T2 & T3) (C1 & C2 & C3) (N1 & N2 & N3) (F1 & F2 & F3) (S1 & S2 & S3) (I1 & I2 & I3) (K1 & K2 & K3) (G1 & G2 & G3) (V1 & V2 & V3) (Y1 & Y2 & Y3) (L1 & L2 & L3) (P1 & P2 & P3) (Z1 & Z2 & Z3) _ | destruct PF as ((T1 & T2 & T3) & (C1 & C2 & C3) & (N1 & N2 & N3) & (F1 & F2 & F3) & (S1 & S2 & S3) & (I1 & I2 & I3) & (K1 & K2 & K3) &
                    (G1 & G2 & G3) & (V1 & V2 & V3) & (Y1 & Y2 & Y3) & (L1 & L2 & L3) & (P1 & P2 & P3) & (Z1 & Z2 & Z3) & _) ]).
    unfold aregions_ in Hbs. apply in_app_iff in Hbs as [Hbs|Hbs]; [| apply in_app_iff in Hbs as [Hbs|Hbs]].
    - (* [comment removed for export] *)
      cbn -[shadow_region stack_shadow_iv Z.add Z.sub Z.mul] in Hbs. cbn [al_image_lo al_image_hi AL_pasan] in Hbs.
      destruct Hbs as [Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[]]]]]]]]]]]]]]]]]]]]]]]]]].
      + (* [comment removed for export] *) injection Q as <- <-. clear -R Z1 XS B8 CE. lia.
      + (* [comment removed for export] *) (first [ pose proof (stack_shadow_iv_facts) as dR_7; dand4 dR_7 as SF1 SF2 SF3 SF4 | pose proof stack_shadow_iv_facts as (SF1 & SF2 & SF3 & SF4) ]). rewrite Q in SF3, SF4. cbn [fst snd] in SF3, SF4. clear -R SF3 SF4 XS. lia.
      + (* [comment removed for export] *) cbv in Q. injection Q as <- <-. clear -R XS. unfold kHighMemBeg in XS. lia.
      + injection Q as <- <-. exact (BM 4%nat _ _ ltac:(lia) E4 R).
      + injection Q as <- <-. exact (BM 5%nat _ _ ltac:(lia) E5 R).
      + (* [comment removed for export] *) injection Q as <- <-. clear -R XS. unfold p_ri, a_sb in *. lia.
      + injection Q as <- <-. exact (BM 6%nat _ _ ltac:(lia) E6 R).
      + apply app_facts in S1. eapply (NOTAPP (p_fs (a_pl A)) kFakeStackBytes); [clear -S1 S2 CE; lia| unfold kFakeStackBytes; lia| apply M8; exact S3| exact (eq_sym Q)].
      + injection Q as <- <-. exact (BM 7%nat _ _ ltac:(lia) E7 R).
      + injection Q as <- <-. exact (BM 8%nat _ _ ltac:(lia) E8 R).
      + injection Q as <- <-. apply (BM 1%nat _ _ ltac:(lia) E1). clear -R. unfold a_pa, kChunksBlockCount, kPtrArrayReserve in *. lia.
      + injection Q as <- <-. exact (BM 9%nat _ _ ltac:(lia) E9 R).
      + injection Q as <- <-. exact (BM 10%nat _ _ ltac:(lia) E10 R).
      + injection Q as <- <-. exact (BM 14%nat _ _ ltac:(lia) E14 R).
      + apply app_facts in G1. eapply (NOTAPP (p_gvec (a_pl A)) 4096); [clear -G1 G2 CE; lia| lia| apply M8; exact G3| exact (eq_sym Q)].
      + apply app_facts in V1. eapply (NOTAPP (p_dvec (a_pl A)) 4096); [clear -V1 V2 CE; lia| lia| apply M8; exact V3| exact (eq_sym Q)].
      + apply app_facts in Y1. eapply (NOTAPP (p_m11 (a_pl A)) 4096); [clear -Y1 Y2 CE; lia| lia| apply M8; exact Y3| exact (eq_sym Q)].
      + apply app_facts in T1. eapply (NOTAPP (p_thr (a_pl A)) 4096); [clear -T1 T2 CE; lia| lia| apply M8; exact T3| exact (eq_sym Q)].
      + apply app_facts in C1. eapply (NOTAPP (p_ctx (a_pl A)) 0x10000); [clear -C1 C2 CE; lia| lia| apply M8; exact C3| exact (eq_sym Q)].
      + apply app_facts in L1. eapply (NOTAPP (p_dtls (a_pl A)) 4096); [clear -L1 L2 CE; lia| lia| apply M8; exact L3| exact (eq_sym Q)].
      + (first [ pose proof ((sb_factsT A W)) as dR_8; dand5 dR_8 as _ SBA HB6 RSB SCE | pose proof (sb_factsT A W) as (_ & SBA & HB6 & RSB & SCE) ]). eapply (NOTAPP (p_ri (a_pl A)) 4096); [| lia| | exact (eq_sym Q)].
        * right. clear -HB6 RSB SCE CE. unfold p_ri, a_sb, a_b6, kSpaceSize, kHighMemBeg in *. lia.
        * unfold p_ri. unfold a_sb in SBA. rewrite Z.add_mod by lia. rewrite (mod0_down _ 0x10000 8 ltac:(exists 8192; reflexivity) SBA). reflexivity.
      + apply app_facts in N1. eapply (NOTAPP (p_nodes0 (a_pl A)) kDepotNodesBlock); [clear -N1 N2 CE; lia| unfold kDepotNodesBlock; lia| apply M8; exact N3| exact (eq_sym Q)].
      + apply app_facts in F1. eapply (NOTAPP (p_frames0 (a_pl A)) kStackStoreBlockBytes); [clear -F1 F2 CE; lia| unfold kStackStoreBlockBytes; lia| apply M8; exact F3| exact (eq_sym Q)].
      + apply app_facts in I1. eapply (NOTAPP (p_itab (a_pl A)) 0x38e000); [clear -I1 I2 CE; lia| lia| apply M8; exact I3| exact (eq_sym Q)].
      + apply app_facts in K1. eapply (NOTAPP (p_m64k (a_pl A)) 0x10000); [clear -K1 K2 CE; lia| lia| apply M8; exact K3| exact (eq_sym Q)].
    - (* [comment removed for export] *)
      (first [ pose proof ((classes_regions_inv _ _ _ _ Hbs)) as dR_9; dex1 dR_9 as c'; destruct dR_9 as [Hc' Hr] | pose proof ((classes_regions_inv _ _ _ _ Hbs)) as dR_9; dand3 dR_9 as c' Hc' Hr | destruct (classes_regions_inv _ _ _ _ Hbs) as (c' & Hc' & Hr) ]). (first [ pose proof ((wtR A W)) as dR_10; dand3 dR_10 as WR1 WR2 _ | destruct (wtR A W) as (WR1 & WR2 & _) ]).
      destruct (Z.eq_dec c' 31) as [->|N31]. { rewrite (WR2 31) in Hr by lia. cbn in Hr. destruct Hr. }
      assert (HC : 1 <= c' <= 30) by (clear - Hc' N31; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hc'; lia).
      pose proof (region_piece_boundsT A c' W HC) as RB'. cbv zeta in RB'. (first [ dand12 RB' as B1' B2' B3' B4' B5' B6' B7' B8' B9' B10' _ B12' | destruct RB' as (B1' & B2' & B3' & B4' & B5' & B6' & B7' & B8' & B9' & B10' & _ & B12') ]).
      (first [ pose proof ((WR1 c' HC)) as dR_12; dand7 dR_12 as _ _ MUK _ _ MFK _ | pose proof (WR1 c' HC) as (_ & _ & MUK & _ & _ & MFK & _) ]).
      assert (MU64 : rg_mapped_user (a_reg A c') mod 64 = 0) by (apply (mod0_down _ kUserMapSize 64); [exists 4096; reflexivity| exact MUK]).
      assert (MF64 : rg_mapped_fa (a_reg A c') mod 64 = 0) by (apply (mod0_down _ kFreeArrayMapSize 64); [exists 4096; reflexivity| exact MFK]).
      assert (RB64 : region_beg (p_sb (a_pl A)) c' mod 64 = 0) by (apply (mod0_down _ 0x10000 64); [exists 1024; reflexivity| exact B9']).
      assert (RB8 : region_beg (p_sb (a_pl A)) c' mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact RB64]).
      destruct (class_regions_inv _ _ _ _ Hr) as [[Q NZ]|[[Q NZ]|[[Q NZ]|[Q NZ]]]].
      + injection Q as -> ->. destruct (Z.eq_dec c' c) as [->|NE].
        * clear -R Hx B3 B4 B5. unfold a_sb in *. lia.
        * destruct (regions_disjoint (a_sb A) c' c NE ltac:(lia) ltac:(lia)) as [D|D]; clear -D R Hx B3' B4' B5 B6 B3; unfold a_sb, kRegionSize, kFreeArrayOffset in *; lia.
      + eapply (NOTAPP (region_beg (p_sb (a_pl A)) c') (rg_mapped_user (a_reg A c'))); [| | exact RB8| exact Q];
          clear -B1' B3' B4' B6' B7' B8' NZ CE; unfold a_sb, kHighMemBeg, kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia.
      + injection Q as -> ->. destruct (Z.eq_dec c' c) as [->|NE].
        * clear -R Hx B3 B4 B5. unfold a_sb, free_array_beg in *. lia.
        * destruct (regions_disjoint (a_sb A) c' c NE ltac:(lia) ltac:(lia)) as [D|D]; clear -D R Hx B3' B4' B5' B6' B5 B6 B3; unfold a_sb, free_array_beg, kRegionSize, kFreeArrayOffset in *; lia.
      + eapply (NOTAPP (region_beg (p_sb (a_pl A)) c' + kFreeArrayOffset) (rg_mapped_fa (a_reg A c'))); [| | | exact Q].
        * right. clear -B1' B5' B6' B7' B8' CE. unfold a_sb, kHighMemBeg, kRegionSize, kSpaceSize, kFreeArrayOffset in *. lia.
        * clear -B5' NZ. lia.
        * rewrite Z.add_mod, RB8 by lia. reflexivity.
    - (* [comment removed for export] *)
      unfold sec_regions_ in Hbs. apply in_flat_map in Hbs as (sc & Hsc & Hr). destruct (In_nth_error' _ _ Hsc) as [j Hj].
      pose proof (bm_nth_sec A j sc Hj) as Ej. (first [ pose proof ((sec_chunk_boundsT A sc W Hsc)) as dR_13; dand5 dR_13 as SN SB5 SB3 SB4 _ | pose proof (sec_chunk_boundsT A sc W Hsc) as (SN & SB5 & SB3 & SB4 & _) ]).
      destruct Hr as [Q|[Q|[]]].
      + injection Q as <- <-. exact (BM (15 + j)%nat _ _ ltac:(lia) Ej R).
      + apply app_facts in SB3. pose proof (map_size_ge (cs_n sc) ltac:(clear -SN; unfold kMaxPrimaryUser in SN; lia)) as MSG.
        eapply (NOTAPP (cs_map sc) (map_size (cs_n sc))); [clear -SB3 SB4 CE; lia| clear -MSG SN; unfold kMaxPrimaryUser in SN; lia| apply M8; exact SB5| exact (eq_sym Q)].
  Qed.
End FreshHidden.

Section RW2.
Context {Clg : Ceiling}.
  Variables (A : AState) (c : Z) (reg' : Z -> region) (cache' : Z -> pcache) (limbo' : list batch) (d : Z).
  Let A' := mkA (a_pl A) reg' (a_cache_inited A) cache' (a_livemap A) [] (a_qglobal A) (a_sec A) (a_depot A) (a_fhint A) (a_fframes A)
                (a_ia_inited A) (a_oom A) (a_tiny A) limbo' (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
  Hypothesis W : WFT A.
  Hypothesis CR : 1 <= c <= 30.
  Hypothesis D0 : 0 <= d.
  Hypothesis DM : d mod kFreeArrayMapSize = 0.
  Hypothesis RO : forall c', c' <> c -> reg' c' = a_reg A c'.
  Hypothesis RC : rg_mapped_user (reg' c) = rg_mapped_user (a_reg A c) /\ rg_mapped_fa (reg' c) = rg_mapped_fa (a_reg A c) + d.
  Local Notation sb := (a_sb A).
  Local Notation rb := (region_beg (a_sb A) c).
  Local Notation fa := (region_beg (a_sb A) c + kFreeArrayOffset).
  Local Notation mu := (rg_mapped_user (a_reg A c)).
  Local Notation mfa := (rg_mapped_fa (a_reg A c)).

  #[using="DM D0 CR W Clg"] Lemma gw_align : rb mod 64 = 0 /\ fa mod 64 = 0 /\ mu mod 64 = 0 /\ mfa mod 64 = 0 /\ d mod 64 = 0 /\ 0 <= mu /\ 0 <= mfa.
  Proof.
    (first [ pose proof ((wtR A W)) as dR_14; dand3 dR_14 as WR _ _ | destruct (wtR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c CR)) as dR_15; dand7 dR_15 as A1 A2 A3 A4 A5 A6 _ | destruct (WR c CR) as (A1 & A2 & A3 & A4 & A5 & A6 & _) ]).
    pose proof (region_piece_boundsT A c W CR) as RB. cbv zeta in RB. (first [ dand10 RB as _ _ _ _ _ _ _ _ R9 _ | destruct RB as (_ & _ & _ & _ & _ & _ & _ & _ & R9 & _) ]).
    assert (RB64 : rb mod 64 = 0) by (apply (mod0_down _ 0x10000 64); [exists 1024; reflexivity| exact R9]).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit.
    - exact RB64.
    - rewrite Zplus_mod, RB64. replace (kFreeArrayOffset mod 64) with 0 by reflexivity. reflexivity.
    - apply (mod0_down _ kUserMapSize 64); [exists 4096; reflexivity| exact A3].
    - apply (mod0_down _ kFreeArrayMapSize 64); [exists 4096; reflexivity| exact A6].
    - apply (mod0_down _ kFreeArrayMapSize 64); [exists 4096; reflexivity| exact DM].
    - lia.
    - lia.
  Qed.

  (* [comment removed for export] *)
  #[using="RC DM D0 CR W Clg"] Lemma gw_class_ivs_new : forall lo hi, In (lo, hi) (hull_of (class_regions_ sb (reg' c) c)) ->
    (lo = rb /\ hi = rb + mu /\ mu <> 0) \/ (lo = sh rb /\ hi = sh rb + mu / 8 /\ mu <> 0) \/
    (lo = fa /\ hi = fa + (mfa + d) /\ mfa + d <> 0) \/ (lo = sh fa /\ hi = sh fa + (mfa + d) / 8 /\ mfa + d <> 0).
  Proof.
    intros lo hi Hin. (first [ pose proof (gw_align) as dR_17; dand7 dR_17 as M1 M2 M3 M4 M5 P1 P2 | pose proof gw_align as (M1 & M2 & M3 & M4 & M5 & P1 & P2) ]). destruct RC as [E1 E2].
    unfold hull_of in Hin. apply in_map_iff in Hin as ([b s] & E & Hin). cbn [fst snd] in E.
    injection E as <- <-. apply class_regions_inv in Hin. cbv zeta in Hin. rewrite E1, E2 in Hin.
    assert (M4' : (mfa + d) mod 64 = 0) by (rewrite Zplus_mod, M4, M5; reflexivity).
    destruct Hin as [[E NZ]|[[E NZ]|[[E NZ]|[E NZ]]]].
    - injection E as -> ->. left. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [exact NZ| lia].
    - rewrite (shadow_region_aligned _ _ M1 M3 ltac:(lia)) in E. injection E as -> ->. right; left. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [exact NZ| lia].
    - injection E as -> ->. right; right; left. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [exact NZ| lia].
    - unfold free_array_beg in E |- *. rewrite (shadow_region_aligned _ _ M2 M4' ltac:(lia)) in E. injection E as -> ->. right; right; right. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [exact NZ| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="DM D0 CR W d"] Lemma gw_old_has : (mu <> 0 -> In (rb, rb + mu) (pa_hull A) /\ In (sh rb, sh rb + mu / 8) (pa_hull A)) /\
                     (mfa <> 0 -> In (fa, fa + mfa) (pa_hull A) /\ In (sh fa, sh fa + mfa / 8) (pa_hull A)).
  Proof.
    (first [ pose proof (gw_align) as dR_18; dand7 dR_18 as M1 M2 M3 M4 _ P1 P2 | pose proof gw_align as (M1 & M2 & M3 & M4 & _ & P1 & P2) ]).
    assert (IN : forall r, In r (class_regions_ sb (a_reg A c) c) -> In (fst r, fst r + snd r) (pa_hull A)).
    { intros r Hr. unfold pa_hull, ahull_of, ahull_of_. apply in_or_app. right. apply in_or_app. left. unfold hull_of. apply in_map_iff. exists r. split; [reflexivity|].
      exact (class_in_aregions A r c ltac:(lia) Hr). }
    unfold class_regions_ in IN. cbv zeta in IN. unfold free_array_beg in IN. split; intros NZ.
    - rewrite (proj2 (Z.eqb_neq mu 0) NZ) in IN. split.
      + apply (IN (rb, mu)). apply in_or_app. left. left. reflexivity.
      + pose proof (IN (shadow_region rb mu) ltac:(apply in_or_app; left; right; left; reflexivity)) as X. rewrite (shadow_region_aligned _ _ M1 M3 ltac:(lia)) in X. exact X.
    - rewrite (proj2 (Z.eqb_neq mfa 0) NZ) in IN. split.
      + apply (IN (fa, mfa)). apply in_or_app. right. left. reflexivity.
      + pose proof (IN (shadow_region fa mfa) ltac:(apply in_or_app; right; right; left; reflexivity)) as X.
        rewrite (shadow_region_aligned _ _ M2 M4 ltac:(lia)) in X. exact X.
  Qed.

  #[using="RC RO DM D0 CR W"] Theorem gw_hull_cases : forall x, in_hullb (pa_hull A') x = true ->
    in_hullb (pa_hull A) x = true \/ (fa + mfa <= x < fa + mfa + d) \/ (sh (fa + mfa) <= x < sh (fa + mfa) + d / 8).
  Proof.
    intros x H. (first [ pose proof (gw_align) as dR_19; dand7 dR_19 as M1 M2 M3 M4 M5 P1 P2 | pose proof gw_align as (M1 & M2 & M3 & M4 & M5 & P1 & P2) ]).
    assert (M2' : fa mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M2]).
    assert (M4' : mfa mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M4]).
    assert (M5' : d mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M5]).
    pose proof (sh_add fa mfa M2' M4') as E2.
    assert (D2 : (mfa + d) / 8 = mfa / 8 + d / 8).
    { pose proof (Z_div_mod_eq_full mfa 8). pose proof (Z_div_mod_eq_full d 8). rewrite M4' in *. rewrite M5' in *.
      replace (mfa + d) with ((mfa / 8 + d / 8) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
    apply in_hullb_true in H as (lo & hi & Hin & Rg).
    unfold pa_hull, ahull_of, ahull_of_, aregions_ in Hin. subst A'. cbn [a_pl a_reg a_sec a_deadsh] in Hin.
    rewrite !hull_of_app, !in_app_iff in Hin.
    assert (OLD_or : In (lo, hi) (pa_hull A) \/ In (lo, hi) (hull_of (class_regions_ sb (reg' c) c))).
    { unfold pa_hull, ahull_of, ahull_of_, aregions_. rewrite !hull_of_app, !in_app_iff. change (p_sb (a_pl A)) with sb in *.
      destruct Hin as [Hin|[[Hin|[Hin|Hin]]|[Hin|Hin]]]; try tauto.
      (* [comment removed for export] *)
      unfold hull_of in Hin. apply in_map_iff in Hin as (r & E & Hr). apply classes_regions_inv in Hr as (c' & Hc' & Hr).
      destruct (Z.eq_dec c' c) as [->|NE].
      - right. unfold hull_of. apply in_map_iff. exists r. split; [exact E| exact Hr].
      - left. right. left. right. left. unfold hull_of. apply in_map_iff. exists r. split; [exact E|]. rewrite (RO c' NE) in Hr.
        replace c' with (Z.of_nat (Z.to_nat c')) in Hr by lia. apply (classes_regions_in _ _ 31 r (Z.to_nat c')); [lia| lia| exact Hr]. }
    destruct OLD_or as [OLD|NEWc]; [left; apply (in_hullb_intro _ _ _ _ OLD); exact Rg|].
    pose proof gw_old_has as [OU OF].
    destruct (gw_class_ivs_new lo hi NEWc) as [(-> & -> & NZ)|[(-> & -> & NZ)|[(-> & -> & NZ)|(-> & -> & NZ)]]].
    - left. destruct (OU NZ) as [I _]. apply (in_hullb_intro _ _ _ _ I). lia.
    - left. destruct (OU NZ) as [_ I]. apply (in_hullb_intro _ _ _ _ I). lia.
    - destruct (Z_lt_le_dec x (fa + mfa)) as [L|L]; [| right; left; lia]. left. destruct (OF ltac:(lia)) as [I _]. apply (in_hullb_intro _ _ _ _ I). lia.
    - destruct (Z_lt_le_dec x (sh fa + mfa / 8)) as [L|L]; [| right; right; rewrite E2; lia]. left.
      assert (NZ' : mfa <> 0) by (intros E0; rewrite E0 in L; change (0 / 8) with 0 in L; lia).
      destruct (OF NZ') as [_ I]. apply (in_hullb_intro _ _ _ _ I). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="RC CR"] Lemma gw_fa_owned : forall a, fa <= a < fa + (mfa + d) -> ~ in_live_user A a -> ~ in_live_frame A a -> pa_owned A' a.
  Proof.
    intros a Ha NU NF. destruct RC as [E1 E2]. apply (owned_rt A' a fa (mfa + d)); [| exact Ha| exact NU| exact NF].
    unfold runtime_maps, runtime_maps_. subst A'. cbn [a_pl a_reg a_sec]. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists c.
    split; [apply in_map_iff; exists (Z.to_nat c); split; [clear -CR; lia| apply in_seq; clear -CR; lia]|].
    cbv zeta. right. left. rewrite E2. reflexivity.
  Qed.
  #[using="RC DM D0 CR W"] Lemma gw_fsh_owned : forall z, sh (fa + mfa) <= z < sh (fa + mfa) + d / 8 -> pa_owned A' z.
  Proof.
    intros z Hz. (first [ pose proof (gw_align) as dR_20; dand7 dR_20 as M1 M2 M3 M4 M5 P1 P2 | pose proof gw_align as (M1 & M2 & M3 & M4 & M5 & P1 & P2) ]). destruct RC as [E1 E2].
    assert (M2' : fa mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M2]).
    assert (M4' : mfa mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M4]).
    assert (D2 : (mfa + d) / 8 = mfa / 8 + d / 8).
    { pose proof (Z_div_mod_eq_full mfa 8) as X0. rewrite M4' in X0. replace (mfa + d) with (mfa / 8 * 8 + d) by lia. rewrite Z.div_add_l by lia. reflexivity. }
    rewrite (sh_add fa mfa M2' M4') in Hz. assert (0 <= mfa / 8) by (apply Z.div_pos; lia).
    left. right. left. right. left. subst A'. cbn [a_pl a_reg a_sec]. unfold heap_shadow_. right. left. exists c. split; [exact CR|]. cbv zeta.
    rewrite E2, D2. change (p_sb (a_pl A)) with sb. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="RC D0 CR"] Lemma gw_vis_fa : 0 < mfa + d -> forall x, fa <= x < fa + (mfa + d) -> in_hullb (pa_hull A') x = true.
  Proof.
    intros P x Hx. destruct RC as [E1 E2]. apply (in_hullb_intro _ _ fa (fa + (mfa + d))); [| exact Hx].
    unfold pa_hull, ahull_of, ahull_of_. apply in_or_app. right. apply in_or_app. left. unfold hull_of. apply in_map_iff. exists (fa, mfa + d). split; [reflexivity|].
    apply (class_in_aregions A' _ c ltac:(lia)). subst A'. cbn [a_reg a_pl]. unfold class_regions_. cbv zeta. rewrite E1, E2. unfold free_array_beg. change (a_sb _) with sb.
    destruct (Z.eqb_spec (mfa + d) 0); [lia|]. apply in_or_app. right. left. reflexivity.
  Qed.
  #[using="RC DM D0 CR W"] Lemma gw_vis_fsh : 0 < mfa + d -> forall x, sh fa <= x < sh fa + (mfa + d) / 8 -> in_hullb (pa_hull A') x = true.
  Proof.
    intros P x Hx. (first [ pose proof (gw_align) as dR_21; dand7 dR_21 as M1 M2 M3 M4 M5 P1 P2 | pose proof gw_align as (M1 & M2 & M3 & M4 & M5 & P1 & P2) ]). destruct RC as [E1 E2].
    assert (M4' : (mfa + d) mod 64 = 0) by (rewrite Zplus_mod, M4, M5; reflexivity).
    apply (in_hullb_intro _ _ (sh fa) (sh fa + (mfa + d) / 8)); [| exact Hx].
    unfold pa_hull, ahull_of, ahull_of_. apply in_or_app. right. apply in_or_app. left. unfold hull_of. apply in_map_iff. exists (shadow_region fa (mfa + d)).
    split; [rewrite (shadow_region_aligned _ _ M2 M4' P); reflexivity|].
    apply (class_in_aregions A' _ c ltac:(lia)). subst A'. cbn [a_reg a_pl]. unfold class_regions_. cbv zeta. rewrite E1, E2. unfold free_array_beg. change (a_sb _) with sb.
    destruct (Z.eqb_spec (mfa + d) 0); [lia|]. apply in_or_app. right. right. left. reflexivity.
  Qed.
End RW2.
