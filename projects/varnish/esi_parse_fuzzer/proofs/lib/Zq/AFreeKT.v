(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ATransp ATranspR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg, kFakeStackBytes,
                        kPtrArrayReserve, kQuarantineBatchBytes in *.

Lemma chunk_lo_S : forall sb s, chunk_lo sb (ChS s) = cs_map s. Proof. intros sb [mb n]; reflexivity. Qed.
Lemma chunk_hi_S : forall sb s, chunk_hi sb (ChS s) = cs_map s + map_size (cs_n s). Proof. intros sb [mb n]; reflexivity. Qed.

Section TransportKT.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variables (A : AState) (v v' : mem).
  Hypothesis AR : WFT A /\ arepr LPA AL_pboth [] A v.
  Let WF0 : WFT A. Proof. exact (proj1 AR). Qed.
  Let R : arepr LPA AL_pboth [] A v. Proof. exact (proj2 AR). Qed.
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation sb := (a_sb A).
  (* [comment removed for export] *)
  Variables (s0 : chunkS) (slo shi : Z).
  Hypothesis S0 : In s0 (sr_chunks (a_sec A)).
  Local Notation h0 := (cs_map s0).
  Local Notation z0 := (map_size (cs_n s0)).
  Hypothesis SLO : sh h0 <= slo.
  Hypothesis SHI : shi <= sh (h0 + z0).
  Hypothesis SHI8 : shi mod 8 = 0.
  Definition hole (a : Z) : Prop := (h0 <= a < h0 + z0) \/ (slo <= a < shi).
  Hypothesis NNH : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> ~ hole a ->
                             v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.

  (* [comment removed for export] *)
  Lemma hole_map : 0x60a000 <= h0 /\ h0 + z0 <= alloc_ceiling /\ h0 < h0 + z0 /\ h0 mod 4096 = 0 /\ z0 mod 4096 = 0 /\
                   (h0 + z0 <= kLowShadowMapBeg \/ kHighMemBeg <= h0) /\ carved A (ChS s0).
  Proof.
    assert (C : carved A (ChS s0)) by exact S0.
    pose proof (carved_range A v [] AR (ChS s0) C) as RG. rewrite chunk_lo_S, chunk_hi_S in RG. (first [ pose proof ((sec_chunk_boundsT A _ WF0 S0)) as dR_1; dand5 dR_1 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_boundsT A _ WF0 S0) as (B1 & B2 & B3 & B4 & B5) ]).
    apply app_facts in B3. pose proof (map_size_page (cs_n s0)) as MP. unfold kPageSize in MP.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. exact C.
  Qed.
  Lemma hole_shadow : 0x800b9400 <= sh h0 /\ sh (h0 + z0) = sh h0 + z0 / 8 /\ sh (h0 + z0) <= sh alloc_ceiling /\ sh (h0 + z0) < kHighMemBeg.
  Proof.
    (first [ pose proof (hole_map) as dR_2; dand7 dR_2 as M1 M2 M3 M4 M5 M6 _ | pose proof hole_map as (M1 & M2 & M3 & M4 & M5 & M6 & _) ]). pose proof alloc_ceiling_val as CE.
    split; [| split; [apply sh_add; [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact M4]| apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact M5]]| split; [apply sh_mono; lia|]]];
      unfold sh, kShadowOffset, kLowShadowBeg, kHighMemBeg in *.
    - pose proof (Z.div_le_mono 0x60a000 (cs_map s0) 8 ltac:(lia) ltac:(lia)) as L. change (0x60a000 / 8) with 791552 in L. lia.
    - pose proof (Z.div_le_mono (cs_map s0 + map_size (cs_n s0)) 0x7fffff800000 8 ltac:(lia) ltac:(lia)) as U. change (0x7fffff800000 / 8) with 0xffffff00000 in U. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hole_free_app : forall a k x, (a + k <= kLowShadowMapBeg \/ kHighMemBeg <= a) -> (a + k <= h0 \/ h0 + z0 <= a) ->
    a <= x < a + k -> ~ hole x.
  Proof.
    intros a k x APP AP Hx [H|H]; [lia|]. (first [ pose proof (hole_shadow) as dR_3; dand4 dR_3 as S1 S2 S3 S4 | pose proof hole_shadow as (S1 & S2 & S3 & S4) ]). (first [ pose proof (hole_map) as dR_4; dand4 dR_4 as _ _ M3 _ | pose proof hole_map as (_ & _ & M3 & _) ]).
    unfold kLowShadowBeg, kLowShadowMapBeg, kHighMemBeg in *. pose proof (Z.div_pos (map_size (cs_n s0)) 8). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma hole_free_shadow : forall a k x, kLowShadowBeg <= a -> a + k <= kHighMemBeg -> (a + k <= slo \/ shi <= a) ->
    a <= x < a + k -> ~ hole x.
  Proof.
    intros a k x LO HI AP Hx [H|H]; [| lia]. (first [ pose proof (hole_map) as dR_5; dand7 dR_5 as _ _ _ _ _ M6 _ | pose proof hole_map as (_ & _ & _ & _ & _ & M6 & _) ]).
    unfold kLowShadowBeg, kLowShadowMapBeg, kHighMemBeg in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mapped_NH : forall a k, 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) -> a + k <= 2^64 ->
    (forall x, a <= x < a + k -> ~ hole x) -> mapped v a k -> mapped v' a k.
  Proof. intros a k H0 H1 H2 HF M. eapply mapped_mono; [exact M|]. intros i Hi. apply NNH; try lia. apply HF. lia. Qed.
  Lemma junk_NH : forall a k, 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) ->
    (forall x, a <= x < a + k -> ~ hole x) -> junk_at rsegs v a k -> junk_at rsegs v' a k.
  Proof.
    (intros a k H0 H1 HF; (first [ intro dR_43; dex1 dR_43 as bs; destruct dR_43 as [L B] | intro dR_43; dand3 dR_43 as bs L B | intros (bs & L & B) ])). pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite L in BB.
    apply junk_at_of_mapped; [lia| lia| lia|]. apply mapped_NH; [lia| lia| lia| exact HF|]. rewrite <- L. eapply bytes_at_mapped_off; [exact B| lia| lia].
  Qed.

  Ltac leaf H AG :=
    lazymatch type of H with
    | u64_at _ _ _ _ => eapply u64_at_agree; [exact H|]; intros i__ Hi__; AG
    | u32_at _ _ _ _ => eapply u32_at_agree; [exact H|]; intros i__ Hi__; AG
    | u16_at _ _ _ _ => eapply u16_at_agree; [exact H|]; intros i__ Hi__; AG
    | u8_at _ _ _ _ => eapply u8_at_agree;  [exact H|]; AG
    | fill_at _ _ _ _ _ => eapply fill_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    | junk_at _ _ _ _ => eapply junk_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    end.

  (* [comment removed for export] *)
  Lemma hole_free_space : forall a k x, sb <= a -> a + k <= sb + kSpaceSize + 4096 -> a <= x < a + k -> ~ hole x.
  Proof.
    intros a k x LO HI Hx. (first [ pose proof ((sb_factsT A WF0)) as dR_6; dand5 dR_6 as _ _ HB6 RSB SCE | pose proof (sb_factsT A WF0) as (_ & _ & HB6 & RSB & SCE) ]). pose proof (sec_apart_b6 A v [] AR _ S0) as D.
    unfold a_b6, a_sb in *. apply (hole_free_app a k x); [right; kung_all; lia| kung_all; lia| exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma region_PH : forall c', 1 <= c' <= 30 -> (forall a, rfoot sb (a_reg A c') c' a -> v' (wz a) = v (wz a)) ->
    region_repr_ LPA sb (a_reg A c') v' c'.
  Proof.
    intros c' Hc AG. pose proof (ar_regions _ _ _ _ _ R c' Hc) as C. pose proof alloc_ceiling_val as CE.
    pose proof (region_piece_boundsT A c' WF0 Hc) as RB. cbv zeta in RB. (first [ pose proof ((wtR A WF0)) as dR_7; dand3 dR_7 as WR _ _ | destruct (wtR A WF0) as (WR & _ & _) ]). (first [ pose proof ((WR c' Hc)) as dR_8; dand8 dR_8 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 _ | pose proof (WR c' Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _) ]).
    unfold region_repr_ in *. cbv zeta in *.
    assert (AGri' : forall x, region_info_addr sb c' <= x < region_info_addr sb c' + 128 -> v' (wz x) = v (wz x)).
    { intros x Hx. apply AG. unfold rfoot, kRegionInfoSize. left. exact Hx. }
    assert (AGfa' : forall x, free_array_beg sb c' <= x < free_array_beg sb c' + rg_mapped_fa (a_reg A c') -> v' (wz x) = v (wz x)).
    { intros x Hx. apply AG. unfold rfoot. right. exact Hx. }
    clear AG.
    do 10 (let L := fresh "L" in destruct C as [L C]; split; [leaf L ltac:(apply AGri'; offs; lia) |]).
    (first [ dand3 C as CF M1 M2 | destruct C as (CF & M1 & M2) ]). split; [|split].
    - intros i k E. pose proof (CF i k E) as LF. assert (Z.of_nat i < Z.of_nat (length (rg_free (a_reg A c')))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
      leaf LF ltac:(apply AGfa'; offs; lia).
    - unfold free_array_beg in *. apply mapped_NH; [unfold kHighMemBeg, kFreeArrayOffset in *; lia| right; unfold kHighMemBeg, kFreeArrayOffset in *; lia| unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia| | exact M1].
      intros x Hx. apply (hole_free_space (region_beg sb c' + kFreeArrayOffset) (rg_mapped_fa (a_reg A c')) x); unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia.
    - apply mapped_NH; [unfold kHighMemBeg in *; lia| right; unfold kHighMemBeg in *; lia| unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia| | exact M2].
      intros x Hx. apply (hole_free_space (region_beg sb c') (rg_mapped_user (a_reg A c')) x); unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fsbase_PH : (forall a, a_fs A <= a < a_fs A + kFakeFlagsOffset -> v' (wz a) = v (wz a)) -> fs_base_ LPA (a_pl A) (a_fhint A) v'.
  Proof.
    intros AGfs. pose proof (ar_fsbase _ _ _ _ _ R) as C. pose proof alloc_ceiling_val as CE. (first [ pose proof ((place_fsT A WF0)) as dR_10; dand3 dR_10 as FS1 FS2 FSM | pose proof (place_fsT A WF0) as (FS1 & FS2 & FSM) ]). unfold a_fs in FS1, FS2, FSM, AGfs.
    pose proof (carved_apart_fs A v [] AR (ChS s0) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hole_map))))))) as Dfs. rewrite chunk_lo_S, chunk_hi_S in Dfs.
    unfold fs_base_ in *. cbv zeta in *. (first [ dand5 C as H0 H1 H2 M1 M2 | destruct C as (H0 & H1 & H2 & M1 & M2) ]).
    split; [|split; [leaf H1 ltac:(apply AGfs; unfold kFakeFlagsOffset; offs; lia)| split; [leaf H2 ltac:(apply AGfs; unfold kFakeFlagsOffset; offs; lia)| split]]].
    - intros k Hk. pose proof (H0 k Hk) as L. leaf L ltac:(apply AGfs; unfold kFakeFlagsOffset; offs; lia).
    - pose proof FS1 as FS1'. apply app_facts in FS1. apply mapped_NH; [lia| unfold kFakeStackBytes in *; lia| lia| | exact M1].
      intros x Hx. (first [ pose proof ((app_rangeA_arith _ _ _ FS1')) as dR_12; dand5 dR_12 as _ _ _ _ APP | pose proof (app_rangeA_arith _ _ _ FS1') as (_ & _ & _ & _ & APP) ]). apply (hole_free_app (p_fs (a_pl A)) kFakeStackBytes x); [exact APP| clear -Dfs; lia| exact Hx].
    - pose proof (fs_shadow_strictT A (sh (p_fs (a_pl A))) WF0 ltac:(unfold a_fs, kFakeStackBytes; lia)) as X1.
      pose proof (fs_shadow_strictT A (sh (p_fs (a_pl A)) + (kFakeStackBytes / 8 - 1)) WF0 ltac:(unfold a_fs, kFakeStackBytes; lia)) as X2.
      unfold in_shadow_strict, kLowShadowBeg, kShadowGapBeg, kHighShadowMapBeg, kHighMemBeg in X1, X2.
      apply mapped_NH; [lia| right; lia| lia| | exact M2].
      (first [ pose proof (hole_shadow) as dR_13; dand4 dR_13 as T1 T2 T3 T4 | pose proof hole_shadow as (T1 & T2 & T3 & T4) ]). (first [ pose proof (hole_map) as dR_14; dand6 dR_14 as _ _ _ M4 M5 _ | pose proof hole_map as (_ & _ & _ & M4 & M5 & _) ]).
      assert (SHD : sh (p_fs (a_pl A)) + kFakeStackBytes / 8 <= sh h0 \/ sh h0 + z0 / 8 <= sh (p_fs (a_pl A))).
      { apply sh_disjoint; [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact FSM] | apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact M4] | reflexivity | apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact M5] | clear -Dfs; lia]. }
      intros x Hx. apply (hole_free_shadow (sh (p_fs (a_pl A))) (kFakeStackBytes / 8) x); [unfold kLowShadowBeg; lia| unfold kHighMemBeg; lia| rewrite T2 in SHI; lia| exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma maps_PH : maps_repr_ AL_pboth (a_pl A) v'.
  Proof.
    (first [ pose proof ((ar_maps _ _ _ _ _ R)) as dR_15; dand4 dR_15 as M1 M2 M3 M4 | pose proof (ar_maps _ _ _ _ _ R) as (M1 & M2 & M3 & M4) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((place_factsT A WF0)) as dR_16; dand14 dR_16 as _ _ _ _ _ _ _ _ _ _ _ _ Psp0 _ | pose proof (place_factsT A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Psp0 & _) ]). cbv zeta in Psp0.
    (first [ pose proof ((sb_factsT A WF0)) as dR_17; dand5 dR_17 as _ _ HB6 RSB SCE | pose proof (sb_factsT A WF0) as (_ & _ & HB6 & RSB & SCE) ]). (first [ pose proof (hole_map) as dR_18; dand7 dR_18 as HM1 HM2 HM3 HM4 HM5 HM6 _ | pose proof hole_map as (HM1 & HM2 & HM3 & HM4 & HM5 & HM6 & _) ]). (first [ pose proof (hole_shadow) as dR_19; dand4 dR_19 as T1 T2 T3 T4 | pose proof hole_shadow as (T1 & T2 & T3 & T4) ]).
    pose proof (sec_apart_b6 A v [] AR _ S0) as D6.
    unfold maps_repr_. unfold a_sb, a_b6, p_ri in *.
    cbn [al_image_lo al_image_hi AL_pboth] in M4 |- *.
    change (shadow_region 65536 (6332416 - 65536)) with (0x7fffa000, 0xbf400) in M4 |- *. cbn [fst snd] in M4 |- *.
    (first [ pose proof (stack_shadow_iv_facts) as dR_20; dand4 dR_20 as SF1 SF2 SF3 SF4 | pose proof stack_shadow_iv_facts as (SF1 & SF2 & SF3 & SF4) ]).
    ALogic2.kun.
    split; [| split; [| split]].
    - apply mapped_NH; [lia| right; lia| lia| | exact M1]. intros x Hx. apply (hole_free_app (p_sp0 (a_pl A) - 8388608) 8388608 x); [right; kung_all; lia| kung_all; lia| exact Hx].
    - apply mapped_NH; [lia| right; lia| lia| | exact M2]. intros x Hx. apply (hole_free_app (p_sb (a_pl A) + 137438953472) 4096 x); [right; kung_all; lia| kung_all; lia| exact Hx].
    - apply mapped_NH; [lia| right; lia| lia| | exact M3]. intros x Hx.
      (* [comment removed for export] *)
      pose proof (Z_div_mod_eq_full shi 8) as E8. rewrite SHI8, Z.add_0_r in E8. pose proof (Z_div_mod_eq_full (fst stack_shadow_iv) 8) as F8. rewrite SF1, Z.add_0_r in F8.
      apply (hole_free_shadow (fst stack_shadow_iv) (snd stack_shadow_iv) x); [unfold kLowShadowBeg; lia| unfold kHighMemBeg; lia| right; lia| exact Hx].
    - apply mapped_NH; [lia| right; lia| lia| | exact M4]. intros x Hx. apply (hole_free_shadow 0x7fffa000 0xbf400 x); [unfold kLowShadowBeg; lia| unfold kHighMemBeg; lia| left; lia| exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma hole_free_thr : forall x, thr <= x < thr + 4096 -> ~ hole x.
  Proof.
    intros x Hx. pose proof (place_factsT A WF0) as (Pthr & _). cbv zeta in Pthr. destruct Pthr as (Pthr1 & _). (first [ pose proof ((app_rangeA_arith _ _ _ Pthr1)) as dR_21; dand5 dR_21 as _ _ _ _ APP | pose proof (app_rangeA_arith _ _ _ Pthr1) as (_ & _ & _ & _ & APP) ]).
    pose proof (carved_apart_thr A v [] AR (ChS s0) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hole_map))))))) as D. rewrite chunk_lo_S, chunk_hi_S in D.
    apply (hole_free_app thr 4096 x APP); [clear -D; lia| exact Hx].
  Qed.
  Lemma hole_free_ctx : forall x, p_ctx (a_pl A) <= x < p_ctx (a_pl A) + 0x10000 -> ~ hole x.
  Proof.
    intros x Hx. (first [ pose proof ((place_factsT A WF0)) as dR_22; dand3 dR_22 as _ Pctx _ | pose proof (place_factsT A WF0) as (_ & Pctx & _) ]). cbv zeta in Pctx. destruct Pctx as (Pctx1 & _). (first [ pose proof ((app_rangeA_arith _ _ _ Pctx1)) as dR_23; dand5 dR_23 as _ _ _ _ APP | pose proof (app_rangeA_arith _ _ _ Pctx1) as (_ & _ & _ & _ & APP) ]).
    pose proof (carved_apart_ctx A v [] AR (ChS s0) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hole_map))))))) as D. rewrite chunk_lo_S, chunk_hi_S in D.
    apply (hole_free_app (p_ctx (a_pl A)) 0x10000 x APP); [clear -D; lia| exact Hx].
  Qed.

  Lemma cache_line_PH : forall (cache : Z -> pcache) c', 0 <= c' < 32 -> pk_chunks (cache c') = pk_chunks (a_cache A c') ->
    (forall a, thr + off_th_per_class c' <= a < thr + off_th_per_class c' + 80 -> v' (wz a) = v (wz a)) ->
    let e := thr + off_th_per_class c' in let ks := pk_chunks (cache c') in
    Z.of_nat (length ks) <= 16 /\
    u32_at rsegs v' (e + off_pc_count) (Z.of_nat (length ks)) /\
    (if a_cache_inited A && negb (c' =? 0) then u32_at rsegs v' (e + off_pc_max_count) (max_count c') /\ u64_at rsegs v' (e + off_pc_class_size) (class_size c')
     else u32_at rsegs v' (e + off_pc_max_count) 0 /\ u64_at rsegs v' (e + off_pc_class_size) 0) /\
    (forall i k, nth_error ks i = Some k -> u32_at rsegs v' (e + off_pc_chunk (Z.of_nat i)) (k * class_size c' / kCompactPtrScale)) /\
    junk_at rsegs v' (e + off_pc_chunk (Z.of_nat (length ks))) (4 * (16 - Z.of_nat (length ks))).
  Proof.
    intros cache c' Hc' EQ AGe. cbv zeta. rewrite EQ. pose proof (ar_cache _ _ _ _ _ R) as (C0 & _). pose proof alloc_ceiling_val as CE.
    pose proof (place_factsT A WF0) as (Pthr & _). cbv zeta in Pthr. (first [ dand3 Pthr as Pthr1 Pthr2 Pthr3 | destruct Pthr as (Pthr1 & Pthr2 & Pthr3) ]). apply app_facts in Pthr1.
    (first [ pose proof ((C0 c' Hc')) as dR_25; dand5 dR_25 as LEN X1 X2 X3 X4 | destruct (C0 c' Hc') as (LEN & X1 & X2 & X3 & X4) ]). split; [exact LEN|].
    split; [leaf X1 ltac:(apply AGe; offs; lia)|]. split; [|split].
    - destruct (a_cache_inited A && negb (c' =? 0)); destruct X2 as [Y1 Y2]; split; first [leaf Y1 ltac:(apply AGe; offs; lia) | leaf Y2 ltac:(apply AGe; offs; lia)].
    - intros i k E. pose proof (X3 i k E) as L.
      assert (Z.of_nat i < Z.of_nat (length (pk_chunks (a_cache A c')))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
      leaf L ltac:(apply AGe; offs; lia).
    - apply junk_NH; [clear - Pthr1 Hc' LEN; kung_all; offs; lia| clear - Pthr1 Hc' LEN; kung_all; offs; lia| | exact X4].
      intros x Hx. apply hole_free_thr. clear - Pthr1 Hc' LEN Hx. offs_h Hx. offs. lia.
  Qed.

  Lemma cache_PH : forall (cache : Z -> pcache),
    (forall c', 0 <= c' < 32 ->
      let e := thr + off_th_per_class c' in let ks := pk_chunks (cache c') in
      Z.of_nat (length ks) <= 16 /\
      u32_at rsegs v' (e + off_pc_count) (Z.of_nat (length ks)) /\
      (if a_cache_inited A && negb (c' =? 0) then u32_at rsegs v' (e + off_pc_max_count) (max_count c') /\ u64_at rsegs v' (e + off_pc_class_size) (class_size c')
       else u32_at rsegs v' (e + off_pc_max_count) 0 /\ u64_at rsegs v' (e + off_pc_class_size) 0) /\
      (forall i k, nth_error ks i = Some k -> u32_at rsegs v' (e + off_pc_chunk (Z.of_nat i)) (k * class_size c' / kCompactPtrScale)) /\
      junk_at rsegs v' (e + off_pc_chunk (Z.of_nat (length ks))) (4 * (16 - Z.of_nat (length ks)))) ->
    cache_repr_ LPA (a_pl A) cache (a_cache_inited A) v'.
  Proof.
    intros cache LINES. (first [ pose proof ((ar_cache _ _ _ _ _ R)) as dR_26; dand5 dR_26 as _ J1 J2 M1 M2 | pose proof (ar_cache _ _ _ _ _ R) as (_ & J1 & J2 & M1 & M2) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((place_factsT A WF0)) as dR_27; dand3 dR_27 as Pthr Pctx _ | pose proof (place_factsT A WF0) as (Pthr & Pctx & _) ]). cbv zeta in Pthr, Pctx.
    (first [ dand3 Pthr as Pthr1 Pthr2 Pthr3 | destruct Pthr as (Pthr1 & Pthr2 & Pthr3) ]). apply app_facts in Pthr1. (first [ dand3 Pctx as Pctx1 Pctx2 Pctx3 | destruct Pctx as (Pctx1 & Pctx2 & Pctx3) ]). apply app_facts in Pctx1.
    unfold cache_repr_. cbv zeta. split; [exact LINES|].
    split; [apply junk_NH; [clear - Pthr1; offs; lia| clear - Pthr1; kung_all; offs; lia| intros x Hx; apply hole_free_thr; clear -Hx; offs_h Hx; offs; lia| exact J1]|].
    split; [apply junk_NH; [clear - Pthr1; offs; lia| clear - Pthr1; kung_all; offs; lia| intros x Hx; apply hole_free_thr; clear -Hx; offs_h Hx; offs; lia| exact J2]|].
    split; [apply mapped_NH; [| | | exact hole_free_thr| exact M1]; clear - Pthr1 Pthr2 CE; kung_all; lia|].
    apply mapped_NH; [| | | exact hole_free_ctx| exact M2]; clear - Pctx1 Pctx2 CE; kung_all; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hole_free_carved : forall ch x, carved A ch -> ch <> ChS s0 -> chunk_lo sb ch <= x < chunk_hi sb ch -> ~ hole x.
  Proof.
    intros ch x C NE Hx. (first [ pose proof (hole_map) as dR_30; dand7 dR_30 as _ _ _ _ _ _ C0 | pose proof hole_map as (_ & _ & _ & _ & _ & _ & C0) ]).
    pose proof (carved_disjoint A v [] AR ch (ChS s0) C C0 NE) as D. rewrite chunk_lo_S, chunk_hi_S in D.
    pose proof (carved_app A v [] AR ch C) as APP. apply app_rangeA_arith in APP. (first [ dand5 APP as _ _ _ _ APP | destruct APP as (_ & _ & _ & _ & APP) ]).
    apply (hole_free_app (chunk_lo sb ch) (chunk_hi sb ch - chunk_lo sb ch) x); [clear -APP; lia| clear -D; lia| lia].
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Lemma batches_PH : forall bs, (forall b, In b bs -> In b (a_qthread A ++ (a_qglobal A ++ a_qlimbo A))) ->
    (forall b a, In b bs -> batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes -> v' (wz a) = v (wz a)) ->
    batches_repr LPA v sb bs -> batches_repr LPA v' sb bs.
  Proof.
    induction bs as [|b bs IH]; intros SUB AG BR; [exact I|]. pose proof alloc_ceiling_val as CE.
    cbn [batches_repr] in *. (first [ dand6 BR as X1 X2 X3 X4 M BR | destruct BR as (X1 & X2 & X3 & X4 & M & BR) ]).
    assert (INb : In b (a_qthread A ++ (a_qglobal A ++ a_qlimbo A))) by (apply SUB; left; reflexivity).
    destruct (batch_known A v [] AR b INb) as [Hk LEN]. (first [ pose proof ((batch_range A v [] AR b INb)) as dR_37; dand3 dR_37 as R1 R2 R3 | pose proof (batch_range A v [] AR b INb) as (R1 & R2 & R3) ]).
    assert (AGb : forall x, batch_addr sb b <= x < batch_addr sb b + kQuarantineBatchBytes -> v' (wz x) = v (wz x)).
    { intros x Hx. apply (AG b x); [left; reflexivity| exact Hx]. }
    split; [leaf X1 ltac:(apply AGb; offs; lia)|]. split; [leaf X2 ltac:(apply AGb; offs; lia)|]. split; [leaf X3 ltac:(apply AGb; offs; lia)|].
    split; [|split].
    - intros i e E. pose proof (X4 i e E) as L.
      assert (Z.of_nat i < Z.of_nat (length (ba_entries b))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
      leaf L ltac:(apply AGb; unfold kQuarantineBatchCount in *; offs; lia).
    - apply mapped_NH; [| right| | | exact M]; [unfold kQuarantineBatchBytes in *; kung_all; lia ..|].
      intros x Hx. pose proof (batch_carved A v [] AR b INb) as Cb.
      apply (hole_free_carved _ x Cb ltac:(discriminate)). cbn [chunk_lo chunk_hi alloc_beg]. rewrite class_size_24.
      unfold batch_addr, kQuarantineBatchBytes in *. lia.
    - apply IH; [| | exact BR]. { intros b' Hb'. apply SUB. right. exact Hb'. } { intros b' a Hb' Ha. apply (AG b' a); [right; exact Hb'| exact Ha]. }
  Qed.

  (* [comment removed for export] *)
End TransportKT.
