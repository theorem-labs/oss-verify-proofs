(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs ARtS4t2 ARtSrgm AMalmys AFreeB1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AQPart ATransp ATranspR AFreeRS AFreeRX AFreeRI AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kFreeArraySize, kLowShadowMapBeg, kPtrArrayReserve in *.

(* [comment removed for export] *)
Lemma sh_range_before : forall a n b z, a mod 8 = 0 -> n mod 8 = 0 -> a + n <= b -> sh a <= z < sh a + n / 8 -> z < sh b.
Proof. intros a n b z Ha Hn LE Hz. rewrite <- (sh_add a n Ha Hn) in Hz. pose proof (sh_mono (a + n) b LE). lia. Qed.
Lemma sh_range_after : forall a n b m z, b mod 8 = 0 -> m mod 8 = 0 -> b + m <= a -> sh a <= z < sh a + n / 8 -> sh b + m / 8 <= z.
Proof. intros a n b m z Hb Hm LE Hz. rewrite <- (sh_add b m Hb Hm). pose proof (sh_mono (b + m) a LE). lia. Qed.

Section ReprRecp.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Variables (A : AState) (v v' : mem) (held : list Z) (c k kb : Z) (es1 : list qentry) (more : list batch).
  Variables (reg' : Z -> region) (cache' : Z -> pcache).
  Hypothesis AR : WFT A /\ @arepr _ DepotRepL LPA AL_pasan held A v.
  Hypothesis WR : WFR A.
  Hypothesis L : a_qlimbo A = BA kb es1 :: more.
  Let WF0 : WFT A. Proof. exact (proj1 AR). Qed.
  Let R : @arepr _ DepotRepL LPA AL_pasan held A v. Proof. exact (proj2 AR). Qed.
  #[warnings="-notation-for-abbreviation"] Local Notation P := (a_pl A).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation ri := (a_ri A).
  #[warnings="-notation-for-abbreviation"] Local Notation QGL := (a_qglobal A ++ a_qlimbo A).
  #[warnings="-notation-for-abbreviation"] Local Notation p := (chunk_addr (a_sb A) c k).
  #[warnings="-notation-for-abbreviation"] Local Notation size := (class_size c).
  #[warnings="-notation-for-abbreviation"] Local Notation nf := (Z.of_nat (length (rg_free (a_reg A c)))).
  #[warnings="-notation-for-abbreviation"] Local Notation fac := (free_array_of (a_sb A) c).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa := (rg_mapped_fa (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa' := (rg_mapped_fa (reg' c)).

  (* [comment removed for export] *)
  Variable Wn : Z -> Prop.
  Hypothesis WNH : forall a, Wn a -> alloc_ceiling <= a.
  Variable SHP : Z -> Prop.
  Hypothesis SHPW : forall a, SHP a -> sh p <= a < sh p + size / 8.

  (* [comment removed for export] *)
  Hypothesis CVe : carved A (ChP (CP c k)).
  Hypothesis NE_live : forall u li, a_livemap A !! u = Some li -> li_chunk li <> ChP (CP c k).
  Hypothesis NE_batch : forall b, In b (a_qthread A ++ a_qglobal A) \/ In b more -> ChP (CP kQuarantineBatchClass (ba_idx b)) <> ChP (CP c k).
  Hypothesis NE_cached : forall c' k', 1 <= c' <= 30 -> p_cached_ (a_cache A) c' k' -> ChP (CP c' k') <> ChP (CP c k).
  Hypothesis NE_free : forall c' k', 1 <= c' <= 30 -> p_free_ (a_reg A) c' k' -> ChP (CP c' k') <> ChP (CP c k).
  Hypothesis NE_rest : forall e', In e' (q_entries (a_qthread A ++ a_qglobal A)) -> qe_chunk e' <> ChP (CP c k).

  (* [comment removed for export] *)
  Hypothesis C'O : forall c', c' <> c -> cache' c' = a_cache A c'.
  Hypothesis C'S : forall k', In k' (pk_chunks (cache' c)) -> In k' (pk_chunks (a_cache A c)) \/ k' = k.
  Hypothesis R'O : forall c', c' <> c -> reg' c' = a_reg A c'.
  Hypothesis R'E : rg_mapped_user (reg' c) = rg_mapped_user (a_reg A c) /\ rg_allocated_user (reg' c) = rg_allocated_user (a_reg A c) /\
                   mfa <= mfa' /\ mfa' <= kFreeArraySize /\ mfa' mod 8 = 0.
  Hypothesis R'F : forall k', In k' (rg_free (reg' c)) -> In k' (rg_free (a_reg A c)) \/ In k' (pk_chunks (a_cache A c)).

  Definition rp_foot (a : Z) : Prop :=
       Wn a
    \/ (p <= a < p + size)
    \/ SHP a
    \/ (thr + 208 + 80 * c <= a < thr + 208 + 80 * c + 80)
    \/ (thr + 2768 <= a < thr + 3168)
    \/ (ri + 128 * c <= a < ri + 128 * c + 8)
    \/ (ri + 128 * c + 16 <= a < ri + 128 * c + 128)
    \/ (fac + 4 * nf <= a < fac + mfa')
    \/ (sh (fac + mfa) <= a < sh (fac + mfa) + (mfa' - mfa) / 8).
  Hypothesis MU : forall a, 0 <= a < 2^64 -> ~ rp_foot a -> v' (wz a) = v (wz a).
  Hypothesis NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.

  (* [comment removed for export] *)
  Lemma qt_nil : a_qthread A = [].
  Proof. exact (wrT A WR). Qed.
  Lemma limbo_in : forall e', In e' (es1 ++ q_entries more) -> In e' (q_entries (a_qthread A ++ QGL)).
  Proof.
    intros e' He. rewrite qt_nil, L. cbn [app]. unfold q_entries in *. rewrite flat_map_app. apply in_or_app. right. cbn [flat_map].
    apply in_or_app. apply in_app_or in He. exact He.
  Qed.
  Lemma more_in : forall b, In b more -> In b (a_qthread A ++ QGL).
  Proof. intros b Hb. rewrite qt_nil, L. cbn [app]. apply in_or_app. right. right. exact Hb. Qed.
  Lemma rest_in : forall b, In b (a_qthread A ++ a_qglobal A) -> In b (a_qthread A ++ QGL).
  Proof. intros b Hb. rewrite qt_nil in Hb |- *. cbn [app] in Hb |- *. apply in_or_app. left. exact Hb. Qed.
  Lemma head_in : In (BA kb es1) (a_qthread A ++ QGL).
  Proof. rewrite qt_nil, L. cbn [app]. apply in_or_app. right. left. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma GEO :
    1 <= c <= 30 /\ 0 <= k < carved_count A c /\ 32 <= size /\ size mod 32 = 0 /\
    region_beg sb c = sb + c * 2^32 /\ region_beg sb c <= p /\ p + size <= region_beg sb c + rg_allocated_user (a_reg A c) /\
    rg_allocated_user (a_reg A c) <= rg_mapped_user (a_reg A c) /\ rg_mapped_user (a_reg A c) <= kFreeArrayOffset /\
    fac = region_beg sb c + kFreeArrayOffset /\ 0 <= 4 * nf <= mfa /\ mfa <= mfa' <= kFreeArraySize /\
    kHighMemBeg <= sb /\ ri = sb + kSpaceSize /\ ri + 4096 <= alloc_ceiling /\ region_beg sb c + kRegionSize <= ri /\
    p mod 32 = 0 /\ sb mod 4096 = 0 /\ mfa mod 8 = 0 /\ mfa' mod 8 = 0 /\
    sh (p + size) = sh p + size / 8 /\
    kHighShadowMapBeg <= sh sb /\ sh alloc_ceiling + 1 <= kHighMemBeg /\
    sh p + size / 8 <= sh alloc_ceiling /\ sh (fac + mfa) + (mfa' - mfa) / 8 <= sh alloc_ceiling /\ sh sb <= sh p /\ sh sb <= sh (fac + mfa) /\
    4096 <= thr /\ thr + 4096 <= alloc_ceiling /\ (thr + 4096 <= 0x10000 \/ 0x60a000 <= thr) /\ (thr + 4096 <= kLowShadowMapBeg \/ kHighMemBeg <= thr) /\
    (thr + 4096 <= a_b6 A \/ a_b6 A + kSpaceReserve <= thr) /\ a_b6 A <= sb /\ ri + 4096 <= a_b6 A + kSpaceReserve /\ kHighMemBeg <= a_b6 A.
  Proof.
    pose proof CVe as [CR KR]. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((carved_chunk_boundsT A c k WF0 CR KR)) as dR_1; dand4 dR_1 as RBP KA0 PM CSR | pose proof (carved_chunk_boundsT A c k WF0 CR KR) as (RBP & KA0 & PM & CSR) ]). cbv zeta in RBP, KA0, PM, CSR. pose proof (class_size_mod32 c CR) as CM.
    (first [ pose proof ((region_piece_boundsT A c WF0 CR)) as dR_2; dand12 dR_2 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | pose proof (region_piece_boundsT A c WF0 CR) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]). cbv zeta in *.
    (first [ pose proof ((rk_ri A v held AR)) as dR_3; dand10 dR_3 as RI RLO RHI RAL SBAL SBLO SBRI RIA FAE RBE | pose proof (rk_ri A v held AR) as (RI & RLO & RHI & RAL & SBAL & SBLO & SBRI & RIA & FAE & RBE) ]).
    (first [ pose proof ((wtR A WF0)) as dR_4; dand3 dR_4 as WRg _ _ | destruct (wtR A WF0) as (WRg & _ & _) ]). (first [ pose proof ((WRg c CR)) as dR_5; dand9 dR_5 as _ _ _ _ _ F6 F7 F8 _ | destruct (WRg c CR) as (_ & _ & _ & _ & _ & F6 & F7 & F8 & _) ]). cbv zeta in F6, F7, F8.
    (first [ pose proof ((sb_factsT A WF0)) as dR_6; dand5 dR_6 as _ _ HB6 RSB SCE | pose proof (sb_factsT A WF0) as (_ & _ & HB6 & RSB & SCE) ]).
    (first [ pose proof ((rk_place A v held AR)) as dR_7; dand3 dR_7 as PT PTC _ | pose proof (rk_place A v held AR) as (PT & PTC & _) ]). pose proof (proj1 (aobj_app_rangeA _ _) PT) as PTA. (first [ pose proof ((app_facts _ _ PTA)) as dR_8; dand5 dR_8 as T1 T2 T3 T4 T5 | pose proof (app_facts _ _ PTA) as (T1 & T2 & T3 & T4 & T5) ]).
    (first [ pose proof ((bm_nth_fixed A)) as dR_9; dand6 dR_9 as E0 _ _ _ E4 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & E4 & _) ]). pose proof (bm_sepT A 4 0 _ _ _ _ WF0 E4 E0 ltac:(lia)) as TB.
    destruct R'E as (_ & _ & LE1 & LE2 & M8').
    assert (SHS : sh (p + size) = sh p + size / 8) by (apply sh_add; [apply (mod0_down _ 32 8); [exists 4; reflexivity| exact PM]| apply (mod0_down _ 32 8); [exists 4; reflexivity| exact CM]]).
    assert (PE : p = sb + c * 2^32 + k * size) by (unfold chunk_addr, region_beg, kRegionSize; reflexivity).
    unfold a_thr, a_b6, a_sb, a_ri in *.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption.
    - clear -CR. lia.
    - clear -CR. lia.
    - clear -KR. lia.
    - clear -KR. lia.
    - clear -CSR. lia.
    - apply RBE.
    - clear -Q3. lia.
    - clear -Q4. lia.
    - unfold free_array_of, region_beg, kRegionSize, kFreeArrayOffset. clear. lia.
    - clear. lia.
    - clear -SBLO. unfold sh. kung_all. pose proof (Z.div_le_mono _ _ 8 ltac:(lia) SBLO). cbn in *. lia.
    - clear -CE. unfold sh. kung_all. assert (alloc_ceiling / 8 <= 17592185978880) by (apply Z.div_le_upper_bound; lia). lia.
    - rewrite <- SHS. apply sh_mono. clear -KA0 Q3 Q4 Q6 Q7 Q8 RBE. specialize (RBE c). unfold region_beg, kRegionSize, kSpaceSize, kFreeArrayOffset in *. lia.
    - rewrite <- sh_add.
      + apply sh_mono. clear -LE2 Q7 Q8 RBE. specialize (RBE c). unfold free_array_of, region_beg, kRegionSize, kSpaceSize, kFreeArrayOffset, kFreeArraySize in *. lia.
      + clear -Q12 SBAL. unfold free_array_of. lia.
      + clear -Q12 M8' LE1. lia.
    - apply sh_mono. clear -RBP Q2. lia.
    - apply sh_mono. unfold free_array_of. clear -Q5 CR. lia.
    - clear -RSB. lia.
    - clear -RSB RI. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac geo := (first [ pose proof (GEO) as dR_10; dand35 dR_10 as Gcr Gk Gsz Gszm Grb Grbp Gpa Gam Gmk Gfac Gnf Gmfa Gsb Gri Grice Grbri Gpm Gsbm Gm8 Gm8' Gshs Gshsb Gshce Gshp Gshf Gsbp Gsbf Gt1 Gt2 Gt3 Gt4 Gtb6 Gb6sb Grib6 Gb6 | pose proof GEO as (Gcr & Gk & Gsz & Gszm & Grb & Grbp & Gpa & Gam & Gmk & Gfac & Gnf & Gmfa & Gsb & Gri & Grice & Grbri
                                & Gpm & Gsbm & Gm8 & Gm8' & Gshs & Gshsb & Gshce & Gshp & Gshf & Gsbp & Gsbf & Gt1 & Gt2 & Gt3 & Gt4 & Gtb6 & Gb6sb & Grib6 & Gb6) ]).

  (* [comment removed for export] *)
  Lemma foot_where : forall a, rp_foot a ->
    Wn a \/ (thr <= a < thr + 4096) \/ (sb <= a < ri + 4096) \/ (kHighShadowMapBeg <= a < kHighMemBeg).
  Proof.
    intros a F. geo. unfold rp_foot in F. destruct F as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
    - left. exact H.
    - right; right; left. clear -H Grb Grbp Gpa Gam Gmk Gri Grbri Gcr. kung_all. lia.
    - right; right; right. pose proof (SHPW a H) as X. clear -X Gshsb Gshce Gshp Gsbp. lia.
    - right; left. clear -H Gcr. lia.
    - right; left. clear -H. lia.
    - right; right; left. clear -H Gcr Gri. kung_all. lia.
    - right; right; left. clear -H Gcr Gri. kung_all. lia.
    - right; right; left. clear -H Gfac Grb Gcr Gnf Gmfa Gri Grbri. kung_all. lia.
    - right; right; right. clear -H Gshsb Gshce Gshf Gsbf Gmfa. lia.
  Qed.

  Lemma AGimg : forall a, 0x10000 <= a < 0x60a000 -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha. geo. pose proof alloc_ceiling_val as CE. apply MU; [clear -Ha; lia|]. intros F. apply foot_where in F.
    destruct F as [H|[H|[H|H]]].
    - pose proof (WNH a H) as H0. clear -Ha CE H0. lia.
    - clear -Ha H Gt3. lia.
    - clear -Ha H Gsb Gri. kung_all. lia.
    - clear -Ha H. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bm_below : forall i b s, nth_error (big_maps A) i = Some (b, s) -> (i <> 0)%nat -> b + s <= alloc_ceiling.
  Proof.
    intros i b s Hn Hi. pose proof alloc_ceiling_val as CE.
    pose proof (place_factsT A WF0) as PF. cbv zeta in PF.
    (first [ dand13 PF as (_ & Pthr & _) (_ & Pctx & _) (_ & Pn0 & _) (_ & Pf0 & _) (_ & Pfs & _) (_ & Pit & _) (_ & Pm64 & _) (_ & Pgv & _) (_ & Pdv & _) (_ & Pm11 & _) (_ & Pdt & _) (_ & Ppa & _) _ | destruct PF as ((_ & Pthr & _) & (_ & Pctx & _) & (_ & Pn0 & _) & (_ & Pf0 & _) & (_ & Pfs & _) & (_ & Pit & _) & (_ & Pm64 & _) & (_ & Pgv & _) & (_ & Pdv & _) & (_ & Pm11 & _) & (_ & Pdt & _) & (_ & Ppa & _) & _) ]).
    destruct (Nat.lt_ge_cases i 15) as [LT|GE].
    - unfold big_maps, big_maps_ in Hn. rewrite nth_error_app1 in Hn by (cbn [length]; lia).
      do 15 (destruct i as [|i]; [cbn in Hn; first [exfalso; clear -Hi; lia | injection Hn as <- <-; clear Hi LT; kung_all; lia] |]).
      exfalso. clear -LT. lia.
    - destruct (nth_error (sr_chunks (a_sec A)) (i - 15)) as [sc|] eqn:Es.
      + pose proof (bm_nth_sec A _ _ Es) as X. replace (15 + (i - 15))%nat with i in X by lia. rewrite Hn in X. injection X as -> ->.
        (first [ pose proof ((sec_chunk_boundsT A sc WF0 (nth_error_In _ _ Es))) as dR_12; dand5 dR_12 as _ _ _ B4 _ | pose proof (sec_chunk_boundsT A sc WF0 (nth_error_In _ _ Es)) as (_ & _ & _ & B4 & _) ]). exact B4.
      + exfalso. apply nth_error_None in Es. pose proof (nth_error_Some_lt _ _ _ Hn) as LT. unfold big_maps, big_maps_ in LT. rewrite length_app, length_map in LT. cbn [length] in LT. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma AG_bm : forall i b s a, nth_error (big_maps A) i = Some (b, s) -> (i <> 0)%nat -> (i <> 2)%nat -> (i <> 4)%nat ->
    b <= a < b + s -> v' (wz a) = v (wz a).
  Proof.
    intros i b s a Hn H0 H2 H4 Ha. geo. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bm_boundsT A b s WF0 (nth_error_In _ _ Hn))) as dR_13; dand3 dR_13 as B0 _ B2 | pose proof (bm_boundsT A b s WF0 (nth_error_In _ _ Hn)) as (B0 & _ & B2) ]). pose proof (bm_below i b s Hn H0) as BC.
    (first [ pose proof ((bm_nth_fixed A)) as dR_14; dand6 dR_14 as E0 _ E2 _ E4 _ | pose proof (bm_nth_fixed A) as (E0 & _ & E2 & _ & E4 & _) ]). unfold a_thr, a_b6 in *.
    apply MU; [clear -Ha B0 B2; lia|]. intros F. apply foot_where in F. destruct F as [H|[H|[H|H]]].
    - pose proof (WNH a H) as X. clear -X Ha BC. lia.
    - pose proof (bm_sepT A i 4 _ _ _ _ WF0 Hn E4 H4) as D. clear -D Ha H. lia.
    - pose proof (bm_sepT A i 0 _ _ _ _ WF0 Hn E0 H0) as D. clear -D Ha H Gb6sb Grib6. lia.
    - pose proof (bm_sepT A i 2 _ _ _ _ WF0 Hn E2 H2) as D. clear -D Ha H. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma AGthr : forall a, thr <= a < thr + 4096 -> ~ (thr + 208 + 80 * c <= a < thr + 208 + 80 * c + 80) -> ~ (thr + 2768 <= a < thr + 3168) ->
    v' (wz a) = v (wz a).
  Proof.
    intros a Ha N1 N2. geo. pose proof alloc_ceiling_val as CE.
    apply MU; [clear -Ha Gt1 Gt2 CE; lia|]. intros F. unfold rp_foot in F. destruct F as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
    - pose proof (WNH a H) as X. clear -X Ha Gt2. lia.
    - pose proof (carved_apart_thr A v held AR _ CVe) as D. cbn [chunk_lo chunk_hi alloc_beg] in D. clear -D Ha H. lia.
    - pose proof (SHPW a H) as X. clear -X Ha Gt4 Gshsb Gshce Gshp Gsbp. kung_all. lia.
    - exact (N1 H).
    - exact (N2 H).
    - clear -H Ha Gtb6 Gb6sb Grib6 Gri Gcr. kung_all. lia.
    - clear -H Ha Gtb6 Gb6sb Grib6 Gri Gcr. kung_all. lia.
    - clear -H Ha Gtb6 Gb6sb Grib6 Gri Gcr Gfac Grb Grbri Gnf Gmfa. kung_all. lia.
    - clear -H Ha Gt4 Gshsb Gshce Gshf Gsbf Gmfa. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma AGb6 : forall a, sb <= a < ri + 4096 ->
    ~ (p <= a < p + size) -> ~ (ri + 128 * c <= a < ri + 128 * c + 8) -> ~ (ri + 128 * c + 16 <= a < ri + 128 * c + 128) ->
    ~ (fac + 4 * nf <= a < fac + mfa') -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha N1 N2 N3 N4. geo. pose proof alloc_ceiling_val as CE.
    apply MU; [clear -Ha Gsb Grice CE; kung_all; lia|]. intros F. unfold rp_foot in F. destruct F as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
    - pose proof (WNH a H) as X. clear -X Ha Grice. lia.
    - exact (N1 H).
    - pose proof (SHPW a H) as X. clear -X Ha Gsb Gri Gshsb Gshce Gshp Gsbp. kung_all. lia.
    - clear -H Ha Gtb6 Gb6sb Grib6 Gri Gcr. kung_all. lia.
    - clear -H Ha Gtb6 Gb6sb Grib6 Gri. kung_all. lia.
    - exact (N2 H).
    - exact (N3 H).
    - exact (N4 H).
    - clear -H Ha Gsb Gshsb Gshce Gshf Gsbf Gmfa. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma AGhs : forall a, kHighShadowMapBeg <= a < kHighMemBeg ->
    ~ SHP a -> ~ (sh (fac + mfa) <= a < sh (fac + mfa) + (mfa' - mfa) / 8) ->
    v' (wz a) = v (wz a).
  Proof.
    intros a Ha N1 N2. geo. pose proof alloc_ceiling_val as CE.
    apply MU; [clear -Ha CE; kung_all; lia|]. intros F. unfold rp_foot in F. destruct F as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
    - pose proof (WNH a H) as X. clear -X Ha CE. kung_all. lia.
    - clear -H Ha Grb Grbp Gsb Gcr. kung_all. lia.
    - exact (N1 H).
    - clear -H Ha Gt4 Gcr. kung_all. lia.
    - clear -H Ha Gt4. kung_all. lia.
    - clear -H Ha Gri Gsb Gcr. kung_all. lia.
    - clear -H Ha Gri Gsb Gcr. kung_all. lia.
    - clear -H Ha Gfac Grb Gsb Gcr Gnf. kung_all. lia.
    - exact (N2 H).
  Qed.

  (* [comment removed for export] *)
  Lemma AGlow : forall a, 0x60a000 <= a < kHighShadowMapBeg -> ~ (thr <= a < thr + 4096) -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha NT. geo. pose proof alloc_ceiling_val as CE.
    apply MU; [clear -Ha; kung_all; lia|]. intros F. apply foot_where in F. destruct F as [H|[H|[H|H]]].
    - pose proof (WNH a H) as X. clear -X Ha CE. kung_all. lia.
    - exact (NT H).
    - clear -Ha H Gsb. kung_all. lia.
    - clear -Ha H. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma AGstatic : forall a, cl_static LPA a \/ cl_shared LPA a -> v' (wz a) = v (wz a).
  Proof.
    intros a [St|Sh]; apply AGimg.
    - cbn [cl_static LPA] in St. unfold pa_static in St. clear -St. lia.
    - pose proof (asI_shared_where a Sh) as X. cbn [cl_rw_lo cl_image_hi LPA] in X. clear -X. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma AGctx : forall a, p_ctx P <= a < p_ctx P + 0x10000 -> v' (wz a) = v (wz a).
  Proof. intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_15; dand7 dR_15 as _ _ _ _ _ E5 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & E5 & _) ]). exact (AG_bm 5 _ _ a E5 ltac:(lia) ltac:(lia) ltac:(lia) Ha). Qed.
  Lemma AGdtls : forall a, p_dtls P <= a < p_dtls P + 4096 -> v' (wz a) = v (wz a).
  Proof. intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_16; dand15 dR_16 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ E14 | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E14) ]). exact (AG_bm 14 _ _ a E14 ltac:(lia) ltac:(lia) ltac:(lia) Ha). Qed.
  Lemma AGfs : forall a, a_fs A <= a < a_fs A + kFakeStackBytes -> v' (wz a) = v (wz a).
  Proof. intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_17; dand8 dR_17 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]). exact (AG_bm 6 _ _ a E6 ltac:(lia) ltac:(lia) ltac:(lia) Ha). Qed.
  Lemma AGn0 : forall a, p_nodes0 P <= a < p_nodes0 P + kDepotNodesBlock -> v' (wz a) = v (wz a).
  Proof. intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_18; dand9 dR_18 as _ _ _ _ _ _ _ E7 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & E7 & _) ]). exact (AG_bm 7 _ _ a E7 ltac:(lia) ltac:(lia) ltac:(lia) Ha). Qed.
  Lemma AGf0 : forall a, p_frames0 P <= a < p_frames0 P + kStackStoreBlockBytes -> v' (wz a) = v (wz a).
  Proof. intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_19; dand10 dR_19 as _ _ _ _ _ _ _ _ E8 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & _ & E8 & _) ]). exact (AG_bm 8 _ _ a E8 ltac:(lia) ltac:(lia) ltac:(lia) Ha). Qed.
  Lemma AGpa : forall a, p_pa P <= a < p_pa P + kPtrArrayReserve -> v' (wz a) = v (wz a).
  Proof. intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_20; dand3 dR_20 as _ E1 _ | pose proof (bm_nth_fixed A) as (_ & E1 & _) ]). exact (AG_bm 1 _ _ a E1 ltac:(lia) ltac:(lia) ltac:(lia) Ha). Qed.
  Lemma AGsec : forall sc a, In sc (sr_chunks (a_sec A)) -> cs_map sc <= a < cs_map sc + map_size (cs_n sc) -> v' (wz a) = v (wz a).
  Proof.
    intros sc a Hin Ha. destruct (In_nth_error' _ _ Hin) as [j Hj]. pose proof (bm_nth_sec A _ _ Hj) as E.
    exact (AG_bm (15 + j) _ _ a E ltac:(lia) ltac:(lia) ltac:(lia) Ha).
  Qed.

  Lemma consts_P' : consts_repr_ LPA AL_pasan P v'.
  Proof.
    geo. apply (consts_P A v v' held AR).
    - intros cst a Hin Ha. cbn [cl_consts LPA] in Hin. destruct (pa_consts_where cst a Hin Ha) as [Sh|[IS|St]].
      + apply AGstatic. right. exact Sh.
      + apply AGlow; unfold pa_image_shadow, sh in IS; [clear -IS | clear -IS Gt4]; kung_all; lia.
      + apply AGstatic. left. exact St.
    - intros a Sh. apply AGstatic. right. exact Sh.
    - intros a H. apply AGimg. unfold cfoot_stat in H. cbn [al_instance al_kHighMemEnd_var al_malloc_context_size al_can_poison_memory al_page_size_cache al_may_return_null
        al_rss_limit_exceeded al_dying_flag al_malloc_hooks AL_pasan] in H. clear -H.
      unfold off_primary_reserved_base, off_primary_reserved_size, off_SpaceBeg, off_release_interval, off_RegionInfo_ptr, off_PremappedHeap, off_sec_page_size,
        off_sec_chunks, off_sec_ptr_array_base, off_sec_ptr_array_size, off_q_max_size, off_q_min_size, off_q_max_cache_size, off_max_user_malloc,
        off_min_redzone, off_max_redzone, off_alloc_dealloc_mismatch in H. lia.
    - intros a H. unfold cfoot_thr, off_th_context, off_th_stack_top, off_th_stack_bottom, off_th_stack_switching, off_th_unwinding in H.
      apply AGthr; clear -H Gcr; lia.
    - intros a H. unfold cfoot_misc in H. cbn [cl_tp LPA] in H. rewrite unsigned_lit in H by (clear; lia).
      destruct H as [H|[H|[H|[H|[H|H]]]]]; first [apply AGctx; clear -H; lia | apply AGimg; clear -H; lia | apply AGdtls; clear -H; lia].
  Qed.

  (* [comment removed for export] *)
  Hypothesis P_mx : u64_at rsegs v' (ri + 128 * c) 0.
  Lemma locks_P' : locks_repr_ LPA AL_pasan P held v'.
  Proof.
    geo. pose proof (ar_locks _ _ _ _ _ R) as C. unfold locks_repr_ in *. cbv zeta in *. destruct C as (C0 & C).
    change (al_internal_alloc_inited AL_pasan) with 0x144e48 in *. change (al_instance AL_pasan) with 0xb1d58 in *. change (p_ri P) with ri in *.
    unfold kRegionInfoSize in *.
    split.
    - intros c' Hc. destruct (C0 c' Hc) as [X Y]. destruct (Z.eq_dec c' c) as [->|NE].
      + split; [rewrite Z.add_0_r; exact P_mx|]. eapply u64_at_agree; [exact Y|]. intros i Hi. apply AGb6.
        * clear -Hi Gcr Gri Gsb. kung_all. lia.
        * clear -Hi Grbri Gpa Gam Gmk Gcr Gri. kung_all. lia.
        * clear -Hi. lia.
        * clear -Hi. lia.
        * clear -Hi Gfac Grb Grbri Gcr Gmfa Gri. kung_all. lia.
      + split; (eapply u64_at_agree; [eassumption|]; intros i Hi; apply AGb6;
          [ clear -Hi Hc Gri Gsb; kung_all; lia | clear -Hi Hc Grbri Gpa Gam Gmk Gri; kung_all; lia | clear -Hi Hc NE; nia | clear -Hi Hc NE; nia
          | clear -Hi Hc Gfac Grb Grbri Gcr Gmfa Gri; kung_all; lia ]).
    - (first [ dand5 C as L1 L2 L3 L4 L5 | destruct C as (L1 & L2 & L3 & L4 & L5) ]).
      unfold off_sec_mutex, off_q_cache_mutex, off_q_recycle_mutex, off_fallback_mutex in *.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; (eapply u8_at_agree; [eassumption|]; apply AGimg; clear; lia).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma prim_where : forall c'' k'', carved A (ChP (CP c'' k'')) ->
    sb <= chunk_addr sb c'' k'' /\ chunk_addr sb c'' k'' + class_size c'' <= region_beg sb c'' + rg_allocated_user (a_reg A c'') /\
    region_beg sb c'' + rg_allocated_user (a_reg A c'') <= region_beg sb c'' + kFreeArrayOffset /\
    region_beg sb c'' = sb + c'' * 2^32 /\ region_beg sb c'' + kRegionSize <= ri /\ 1 <= c'' <= 30 /\
    chunk_addr sb c'' k'' mod 32 = 0 /\ class_size c'' mod 32 = 0 /\
    (c'' <> c -> chunk_addr sb c'' k'' + class_size c'' <= region_beg sb c \/ region_beg sb c + kRegionSize <= chunk_addr sb c'' k'').
  Proof.
    intros c'' k'' CV. geo. pose proof CV as [Hc Hk].
    (first [ pose proof ((carved_prim_where A v held AR c'' k'' CV)) as dR_22; dand7 dR_22 as W1 W2 W3 W4 W5 W6 _ | pose proof (carved_prim_where A v held AR c'' k'' CV) as (W1 & W2 & W3 & W4 & W5 & W6 & _) ]).
    (first [ pose proof ((carved_chunk_boundsT A c'' k'' WF0 Hc Hk)) as dR_23; dand4 dR_23 as _ _ M32 _ | pose proof (carved_chunk_boundsT A c'' k'' WF0 Hc Hk) as (_ & _ & M32 & _) ]).
    (first [ pose proof ((rk_ri A v held AR)) as dR_24; dand10 dR_24 as RI _ _ _ _ _ _ _ _ RBE | pose proof (rk_ri A v held AR) as (RI & _ & _ & _ & _ & _ & _ & _ & _ & RBE) ]).
    pose proof (class_size_mod32 c'' Hc) as CM.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption.
    - clear -W1 W6. lia.
    - clear -W3 W4. lia.
    - apply RBE.
    - clear -Hc. lia.
    - clear -Hc. lia.
    - intros NE. clear -NE W1 W2 W3 W4 Hc Gcr RBE. pose proof (RBE c'') as E1. pose proof (RBE c) as E2. rewrite E1 in W1, W2, W4. rewrite E2. clear RBE E1 E2.
      unfold kRegionSize, kFreeArrayOffset in *.
      assert (c'' + 1 <= c \/ c + 1 <= c'') as [X|X] by lia; [left | right]; nia.
  Qed.

  Lemma AGchunk : forall ch, carved A ch -> ch <> ChP (CP c k) -> forall a, chunk_lo sb ch <= a < chunk_hi sb ch -> v' (wz a) = v (wz a).
  Proof.
    intros ch CV NE a Ha. destruct ch as [[c'' k'']|sc].
    - geo. cbn [chunk_lo chunk_hi alloc_beg] in Ha. (first [ pose proof ((prim_where c'' k'' CV)) as dR_25; dand9 dR_25 as W1 W2 W3 W4 W5 W6 _ _ W9 | pose proof (prim_where c'' k'' CV) as (W1 & W2 & W3 & W4 & W5 & W6 & _ & _ & W9) ]).
      pose proof (carved_disjoint A v held AR _ _ CV CVe NE) as D. cbn [chunk_lo chunk_hi alloc_beg] in D.
      apply AGb6.
      + clear -Ha W1 W2 W3 W4 W5. kung_all. lia.
      + clear -Ha D. lia.
      + clear -Ha W2 W3 W5 Gcr. kung_all. lia.
      + clear -Ha W2 W3 W5 Gcr. kung_all. lia.
      + destruct (Z.eq_dec c'' c) as [->|NEc].
        * clear -Ha W2 W3 Gfac. kung_all. lia.
        * specialize (W9 NEc). clear -Ha W9 Gfac Gmfa Gnf. kung_all. lia.
    - cbn [chunk_lo chunk_hi] in Ha. destruct sc as [mb n1]. apply (AGsec (CS mb n1)); [exact CV| exact Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma AGsh_prim : forall c'' k'', carved A (ChP (CP c'' k'')) -> ChP (CP c'' k'') <> ChP (CP c k) ->
    forall z, sh (chunk_addr sb c'' k'') <= z < sh (chunk_addr sb c'' k'') + class_size c'' / 8 -> v' (wz z) = v (wz z).
  Proof.
    intros c'' k'' CV NE z Hz. geo. pose proof alloc_ceiling_val as CE. pose proof CV as [Hc Hk].
    (first [ pose proof ((prim_where c'' k'' CV)) as dR_26; dand9 dR_26 as W1 W2 W3 W4 W5 W6 M32 CM W9 | pose proof (prim_where c'' k'' CV) as (W1 & W2 & W3 & W4 & W5 & W6 & M32 & CM & W9) ]).
    (first [ pose proof ((chunk_shadow A v held AR c'' k'' Hc Hk)) as dR_27; dand4 dR_27 as S1 _ S3 S4 | pose proof (chunk_shadow A v held AR c'' k'' Hc Hk) as (S1 & _ & S3 & S4) ]).
    pose proof (carved_disjoint A v held AR _ _ CV CVe NE) as D. cbn [chunk_lo chunk_hi alloc_beg] in D.
    assert (A8 : chunk_addr sb c'' k'' mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact M32]).
    assert (S8 : class_size c'' mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact CM]).
    assert (P8 : p mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact Gpm]).
    assert (Z8 : size mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact Gszm]).
    apply AGhs.
    - rewrite S1 in S4. clear -Hz S3 S4 Gshce. lia.
    - intros SP. pose proof (SHPW z SP) as PZ. destruct D as [D|D].
      + pose proof (sh_range_before _ _ p z A8 S8 D Hz) as X. clear -X PZ. lia.
      + pose proof (sh_mono (p + size) (chunk_addr sb c'' k'') D). clear -H Hz PZ Gshs. lia.
    - (* [comment removed for export] *)
      assert (FA8 : (fac + mfa) mod 8 = 0) by (rewrite Gfac, Grb; clear -Gsbm Gm8; unfold kFreeArrayOffset; lia).
      destruct (Z.eq_dec c'' c) as [->|NEc].
      + pose proof (sh_range_before _ _ (fac + mfa) z A8 S8 ltac:(clear -W2 W3 Gfac Gnf; lia) Hz) as X. clear -X. lia.
      + destruct (W9 NEc) as [D2|D2].
        * pose proof (sh_range_before _ _ (fac + mfa) z A8 S8 ltac:(clear -D2 Gfac Gnf; unfold kFreeArrayOffset in *; lia) Hz) as X. clear -X. lia.
        * assert (LE8 : (mfa' - mfa) mod 8 = 0) by (clear -Gm8 Gm8'; lia).
          pose proof (sh_range_after (chunk_addr sb c'' k'') (class_size c'') (fac + mfa) (mfa' - mfa) z FA8 LE8
                        ltac:(clear -D2 Gfac Gmfa; unfold kFreeArrayOffset, kFreeArraySize, kRegionSize in *; lia) Hz) as X. clear -X. lia.
  Qed.

  Lemma AGsh_sec : forall sc, In sc (sr_chunks (a_sec A)) ->
    forall z, sh (cs_map sc) <= z < sh (cs_map sc) + map_size (cs_n sc) / 8 -> v' (wz z) = v (wz z).
  Proof.
    intros sc Hin z Hz. geo. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((sec_chunk_boundsT A sc WF0 Hin)) as dR_28; dand5 dR_28 as SB1 SB2 SB3 SB4 SB5 | pose proof (sec_chunk_boundsT A sc WF0 Hin) as (SB1 & SB2 & SB3 & SB4 & SB5) ]). (first [ pose proof ((app_facts _ _ SB3)) as dR_29; dand5 dR_29 as F1 F2 F3 F4 F5 | pose proof (app_facts _ _ SB3) as (F1 & F2 & F3 & F4 & F5) ]).
    (first [ pose proof ((sec_shadow A v held AR sc Hin)) as dR_30; dand3 dR_30 as S1 _ S3 | pose proof (sec_shadow A v held AR sc Hin) as (S1 & _ & S3) ]). pose proof (map_size_page (cs_n sc)) as MP.
    assert (M8 : cs_map sc mod 8 = 0) by (clear -SB2; lia). assert (Z8 : map_size (cs_n sc) mod 8 = 0) by (clear -MP; unfold kPageSize in MP; lia).
    destruct F5 as [LOW|HIGH].
    - (* [comment removed for export] *)
      apply AGlow.
      + unfold sh in *. clear -Hz LOW F1 F4 M8 Z8. kung_all. lia.
      + intros T. unfold sh in *. clear -Hz T LOW F1 F4 Gt4 M8 Z8. kung_all. lia.
    - apply AGhs.
      + pose proof (sh_mono (cs_map sc + map_size (cs_n sc)) alloc_ceiling SB4). unfold sh in *. clear -Hz HIGH H Gshce M8 Z8. kung_all. lia.
      + (* [comment removed for export] *)
        destruct (sec_apart_b6 A v held AR sc Hin) as [D|D].
        * intros SP. pose proof (SHPW z SP) as PZ. pose proof (sh_range_before _ _ p z M8 Z8 ltac:(clear -D Gb6sb Grb Grbp Gcr; lia) Hz) as X. clear -X PZ. lia.
        * intros SP. pose proof (SHPW z SP) as PZ. assert (P8 : p mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact Gpm]).
          assert (S8 : size mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact Gszm]).
          pose proof (sh_range_after (cs_map sc) (map_size (cs_n sc)) p size z P8 S8 ltac:(clear -D Grib6 Gri Grbri Gpa Gam Gmk; kung_all; lia) Hz) as X.
          clear -X PZ. lia.
      + destruct (sec_apart_b6 A v held AR sc Hin) as [D|D].
        * assert (FA8 : (fac + mfa) mod 8 = 0) by (rewrite Gfac, Grb; clear -Gsbm Gm8; unfold kFreeArrayOffset; lia).
          pose proof (sh_range_before _ _ (fac + mfa) z M8 Z8 ltac:(clear -D Gb6sb Gfac Grb Gcr Gnf; unfold kFreeArrayOffset in *; lia) Hz) as X. clear -X. lia.
        * assert (FA8 : (fac + mfa) mod 8 = 0) by (rewrite Gfac, Grb; clear -Gsbm Gm8; unfold kFreeArrayOffset; lia).
          assert (LE8 : (mfa' - mfa) mod 8 = 0) by (clear -Gm8 Gm8'; lia).
          pose proof (sh_range_after (cs_map sc) (map_size (cs_n sc)) (fac + mfa) (mfa' - mfa) z FA8 LE8
                        ltac:(clear -D Grib6 Gri Grbri Gfac Gmfa; kung_all; lia) Hz) as X. clear -X. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma live_user_not_foot : forall a, in_live_user A a ->
    ~ (ri <= a < ri + 4096) /\ ~ (fac <= a < fac + kFreeArraySize).
  Proof.
    (intros a; (first [ intro dR_63; dex2 dR_63 as u li; destruct dR_63 as [Hl Hu] | intro dR_63; dand4 dR_63 as u li Hl Hu | intros (u & li & Hl & Hu) ])). geo.
    pose proof (live_user_whereT A u li a WF0 Hl Hu) as X.
    (first [ pose proof ((rk_ri A v held AR)) as dR_31; dand10 dR_31 as _ _ _ _ _ _ _ _ _ RBE | pose proof (rk_ri A v held AR) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RBE) ]).
    destruct (li_chunk li) as [[c'' k'']|[mb n1]] eqn:EC.
    - (first [ dand9 X as Hc Hk _ _ _ RA W1 W2 W3 | destruct X as (Hc & Hk & _ & _ & _ & RA & W1 & W2 & W3) ]).
      (first [ pose proof ((prim_where c'' k'' (conj Hc Hk))) as dR_33; dand9 dR_33 as _ _ P3 P4 P5 _ _ _ P9 | pose proof (prim_where c'' k'' (conj Hc Hk)) as (_ & _ & P3 & P4 & P5 & _ & _ & _ & P9) ]).
      split.
      + clear -RA W2 P3 P5. kung_all. lia.
      + destruct (Z.eq_dec c'' c) as [->|NE].
        * clear -RA W2 P3 Gfac. kung_all. lia.
        * specialize (P9 NE). clear -RA W1 W2 P3 P9 Gfac. kung_all. lia.
    - (first [ dand5 X as Hin _ _ _ RA | destruct X as (Hin & _ & _ & _ & RA) ]). pose proof (sec_apart_b6 A v held AR _ Hin) as D.
      split.
      + clear -RA D Gb6sb Grib6 Gri. kung_all. lia.
      + clear -RA D Gb6sb Grib6 Gri Gfac Grb Grbri Gcr. kung_all. lia.
  Qed.

  Lemma foot_owned : forall a, rp_foot a ->
    Wn a \/ pa_owned A a \/ (fac + mfa <= a < fac + mfa') \/ (sh (fac + mfa) <= a < sh (fac + mfa) + (mfa' - mfa) / 8).
  Proof.
    intros a F. geo. pose proof alloc_ceiling_val as CE. unfold rp_foot in F. destruct F as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
    - left. exact H.
    - right; left. apply (carved_owned A v held AR (ChP (CP c k)) a CVe); [cbn [chunk_lo chunk_hi alloc_beg]; exact H|].
      intros u li Hl E _. exact (NE_live u li Hl E).
    - right; left. pose proof (SHPW a H) as X. (first [ pose proof ((chunk_shadow A v held AR c k Gcr Gk)) as dR_35; dand3 dR_35 as _ S2 _ | pose proof (chunk_shadow A v held AR c k Gcr Gk) as (_ & S2 & _) ]).
      left. right. left. right. left. exact (S2 a X).
    - right; left. apply (thr_owned A v held AR). clear -H Gcr. lia.
    - right; left. apply (thr_owned A v held AR). clear -H. lia.
    - right; left. apply (owned_rt A a ri 4096); [apply rt_fixed_in; cbn; tauto| clear -H Gcr; lia| |].
      + intros LU. exact (proj1 (live_user_not_foot a LU) ltac:(clear -H Gcr; lia)).
      + intros LF. pose proof (live_frame_zoneT A a WF0 LF) as Z1. (first [ pose proof ((bm_nth_fixed A)) as dR_36; dand8 dR_36 as E0 _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & _ & _ & E6 & _) ]).
        pose proof (bm_sepT A 6 0 _ _ _ _ WF0 E6 E0 ltac:(lia)) as D. unfold a_fs, a_b6 in *. clear -H Z1 D Gb6sb Grib6 Gri Gcr. kung_all. unfold kFakeStackBytes, kFakeFramesOffset in *. lia.
    - right; left. apply (owned_rt A a ri 4096); [apply rt_fixed_in; cbn; tauto| clear -H Gcr; lia| |].
      + intros LU. exact (proj1 (live_user_not_foot a LU) ltac:(clear -H Gcr; lia)).
      + intros LF. pose proof (live_frame_zoneT A a WF0 LF) as Z1. (first [ pose proof ((bm_nth_fixed A)) as dR_37; dand8 dR_37 as E0 _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & _ & _ & E6 & _) ]).
        pose proof (bm_sepT A 6 0 _ _ _ _ WF0 E6 E0 ltac:(lia)) as D. unfold a_fs, a_b6 in *. clear -H Z1 D Gb6sb Grib6 Gri Gcr. kung_all. unfold kFakeStackBytes, kFakeFramesOffset in *. lia.
    - destruct (Z.lt_ge_cases a (fac + mfa)) as [LT|GE]; [| right; right; left; clear -H GE; lia]. right; left.
      apply (owned_rt A a fac mfa).
      + unfold runtime_maps, runtime_maps_. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists c.
        split; [apply in_map_iff; exists (Z.to_nat c); split; [clear -Gcr; lia| apply in_seq; clear -Gcr; lia]|].
        cbv zeta. right. left. rewrite Gfac. unfold a_sb. reflexivity.
      + clear -H LT. lia.
      + intros LU. exact (proj2 (live_user_not_foot a LU) ltac:(clear -H Gmfa; lia)).
      + intros LF. pose proof (live_frame_zoneT A a WF0 LF) as Z1. (first [ pose proof ((bm_nth_fixed A)) as dR_38; dand8 dR_38 as E0 _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & _ & _ & E6 & _) ]).
        pose proof (bm_sepT A 6 0 _ _ _ _ WF0 E6 E0 ltac:(lia)) as D. unfold a_fs, a_b6 in *. clear -H Z1 D Gb6sb Grib6 Gri Gcr Gfac Grb Grbri Gmfa Gnf. kung_all. unfold kFakeStackBytes, kFakeFramesOffset in *. lia.
    - right; right; right. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma AG_shadow_maps : forall z, in_shadow_maps z -> ~ SHP z -> ~ (sh (fac + mfa) <= z < sh (fac + mfa) + (mfa' - mfa) / 8) -> v' (wz z) = v (wz z).
  Proof.
    intros z Hz N1 N2. geo. unfold in_shadow_maps in Hz. destruct Hz as [Hz|Hz].
    - apply AGlow; [clear -Hz; kung_all; lia|]. intros T. clear -Hz T Gt4. kung_all. lia.
    - apply AGhs; [clear -Hz; kung_all; lia| exact N1| exact N2].
  Qed.

  (* [comment removed for export] *)
  Hypothesis P_regc : region_repr_ LPA sb (reg' c) v' c.
  Lemma regions_P' : forall c', 1 <= c' <= 30 -> region_repr_ LPA sb (reg' c') v' c'.
  Proof.
    intros c' Hc. destruct (Z.eq_dec c' c) as [->|NE]; [exact P_regc|]. rewrite (R'O c' NE). geo.
    (first [ pose proof ((rk_ri A v held AR)) as dR_39; dand10 dR_39 as _ _ _ _ _ _ _ RIA FAE RBE | pose proof (rk_ri A v held AR) as (_ & _ & _ & _ & _ & _ & _ & RIA & FAE & RBE) ]).
    (first [ pose proof ((region_piece_boundsT A c' WF0 Hc)) as dR_40; dand8 dR_40 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 _ | pose proof (region_piece_boundsT A c' WF0 Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _) ]). cbv zeta in *.
    apply (region_P A v v' held AR NN c' Hc). intros a H. unfold rfoot in H. rewrite RIA, FAE in H.
    assert (RR : region_beg sb c' + kRegionSize <= region_beg sb c \/ region_beg sb c + kRegionSize <= region_beg sb c').
    { rewrite (RBE c'), (RBE c). clear -NE Hc Gcr. unfold kRegionSize. assert (c' + 1 <= c \/ c + 1 <= c') as [X|X] by lia; [left|right]; nia. }
    destruct H as [H|H].
    - unfold kRegionInfoSize in H. apply AGb6.
      + clear -H Hc Gri Gsb. kung_all. lia.
      + clear -H Hc Gri Grbri Gpa Gam Gmk. kung_all. lia.
      + clear -H Hc NE. nia.
      + clear -H Hc NE. nia.
      + clear -H Hc Gri Grbri Gfac Gmfa Gnf. kung_all. lia.
    - unfold free_array_of in H. pose proof (RBE c') as E'.
      apply AGb6.
      + clear -H Q2 Q5 Q6 Q7 Gri E'. kung_all. lia.
      + pose proof (carved_apart_fa A v held AR _ c' CVe Hc) as D. cbn [chunk_lo chunk_hi alloc_beg] in D. rewrite FAE in D. unfold free_array_of in D.
        clear -H D Q5. kung_all. lia.
      + clear -H Q5 Q6 Q7 Gri Gcr E'. kung_all. lia.
      + clear -H Q5 Q6 Q7 Gri Gcr E'. kung_all. lia.
      + clear -H RR Q5 Q6 Gfac Gmfa Gnf E'. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis P_linec :
    let e := thr + off_th_per_class c in let ks := pk_chunks (cache' c) in
    Z.of_nat (length ks) <= 16 /\
    u32_at rsegs v' (e + off_pc_count) (Z.of_nat (length ks)) /\
    (if a_cache_inited A && negb (c =? 0) then u32_at rsegs v' (e + off_pc_max_count) (max_count c) /\ u64_at rsegs v' (e + off_pc_class_size) (class_size c)
     else u32_at rsegs v' (e + off_pc_max_count) 0 /\ u64_at rsegs v' (e + off_pc_class_size) 0) /\
    (forall i k', nth_error ks i = Some k' -> u32_at rsegs v' (e + off_pc_chunk (Z.of_nat i)) (k' * class_size c / kCompactPtrScale)) /\
    junk_at rsegs v' (e + off_pc_chunk (Z.of_nat (length ks))) (4 * (16 - Z.of_nat (length ks))).
  Lemma cache_P' : cache_repr_ LPA P cache' (a_cache_inited A) v'.
  Proof.
    geo. apply (cache_P A v v' held AR NN cache'). intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact P_linec|].
    apply (cache_line_P A v v' held AR NN cache' c' Hc'); [rewrite (C'O c' NE); reflexivity|].
    intros a Ha. unfold off_th_per_class, off_th_alloc_cache, kPerClassSize in Ha. apply AGthr.
    - clear -Ha Hc'. lia.
    - clear -Ha Hc' NE Gcr. assert (c' + 1 <= c \/ c + 1 <= c') as [X|X] by lia; nia.
    - clear -Ha Hc'. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_P' : live_repr_ LPA sb (a_livemap A) v'.
  Proof.
    apply (live_sub_P A v v' held AR NN (a_livemap A)); [intros u li Hl; exact Hl|].
    intros u li a Hl Ha. apply (AGchunk (li_chunk li)); [exact (known_carved A v held AR _ _ (known_live A v held AR u li Hl))| exact (NE_live u li Hl)| exact Ha].
  Qed.

  Lemma quar_P' : quarantine_repr_ LPA AL_pasan P (a_qthread A) (a_qglobal A) v'.
  Proof.
    geo. apply (quar_P A v v' held AR NN).
    - intros a Ha. unfold off_th_qcache in Ha. apply AGthr; clear -Ha Gcr; lia.
    - intros a Ha. apply AGimg. change (al_instance AL_pasan) with 0xb1d58 in Ha. unfold off_q_cache_list_size in Ha. clear -Ha. lia.
    - intros b a Hb Ha. apply (AGchunk (ChP (CP kQuarantineBatchClass (ba_idx b)))).
      + apply (batch_carved A v held AR). apply rest_in. exact Hb.
      + apply NE_batch. left. exact Hb.
      + cbn [chunk_lo chunk_hi alloc_beg]. unfold batch_addr, kQuarantineBatchBytes in Ha. change (class_size kQuarantineBatchClass) with 8192. exact Ha.
    - intros e a He Ha. apply (AGchunk (qe_chunk e)).
      + exact (known_carved A v held AR _ _ (known_quar A v held AR e (q_in_big A e He))).
      + exact (NE_rest e He).
      + exact Ha.
  Qed.

  Lemma sec_P' : sec_repr_ LPA AL_pasan P (a_sec A) v'.
  Proof.
    (first [ pose proof ((wtS A WF0)) as dR_41; dand4 dR_41 as _ LEN RES _ | destruct (wtS A WF0) as (_ & LEN & RES & _) ]). unfold kChunksBlockCount in RES.
    apply (sec_P A v v' held AR NN).
    - intros a H. apply AGimg. unfold sfoot_stat in H. change (al_instance AL_pasan) with 0xb1d58 in H.
      unfold off_sec_n_reserved, off_sec_n_chunks, off_sec_chunks_sorted, off_sec_stat_n_allocs, off_global_stats in H. clear -H. lia.
    - intros a Ha. apply AGpa. clear -Ha LEN RES. kung_all. lia.
    - intros sc a Hin Ha. apply (AGsec sc a Hin). (first [ pose proof ((sec_chunk_boundsT A sc WF0 Hin)) as dR_42; dand5 dR_42 as _ _ _ _ SB5 | pose proof (sec_chunk_boundsT A sc WF0 Hin) as (_ & _ & _ & _ & SB5) ]).
      pose proof (needed_size_ge (cs_n sc)) as N1. pose proof (rz_size_range (cs_n sc)) as N2. unfold needed_size2 in SB5.
      destruct (from_primary (cs_n sc)); clear -Ha SB5 N1 N2; unfold kSecondaryHeaderSize, kPageSize in *; lia.
  Qed.

  Lemma depot_P' : depot_repr_ LPA AL_pasan P (a_depot A) v'.
  Proof.
    apply (depot_P A v' (a_depot A) v); [exact (ar_depot _ _ _ _ _ R)|].
    intros a H. unfold depot_foot in H. cbn [al_stackStore al_depot_nodes_map1 AL_pasan] in H. destruct H as [H|[H|H]].
    - apply AGimg. clear -H. unfold kDepotNodesL1 in H. lia.
    - exact (AGn0 a H).
    - exact (AGf0 a H).
  Qed.

  Lemma ia_P' : ia_repr_ LPA AL_pasan (a_ia_inited A) v'.
  Proof.
    apply (ia_P A v v' held AR). intros a H. apply AGimg. unfold iafoot in H.
    cbn [al_internal_allocator_inst al_internal_alloc_inited AL_pasan] in H. clear -H. lia.
  Qed.

  Lemma fsbase_P' : fs_base_ LPA P (a_fhint A) v'.
  Proof. apply (fsbase_P A v v' held AR NN). intros a Ha. apply AGfs. clear -Ha. unfold kFakeFlagsOffset, kFakeStackBytes in *. lia. Qed.
  Lemma fsptrs_P' : fs_ptrs_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof. apply (fsptrs_P A v v' held AR). intros a Ha. apply AGfs. clear -Ha. unfold kFakeFramesOffset, kFakeStackBytes in *. lia. Qed.
  Lemma fsflags_P' : fs_flags_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof. apply (fsflags_P A v v' held AR). intros a Ha. apply AGfs. clear -Ha. unfold kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *. lia. Qed.
  Lemma maps_P' : maps_repr_ AL_pasan P v'.
  Proof. exact (maps_P A v v' held AR NN). Qed.

  (* [comment removed for export] *)
  Hypothesis VSH : bytes_at rsegs v' (sh p) (pshadow_free c).
  Hypothesis P_fash : bytes_at rsegs v' (sh (fac + mfa)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat ((mfa' - mfa) / 8))).

  (* [comment removed for export] *)
  Lemma old_state : forall c' k', 1 <= c' <= 30 ->
    p_free_ reg' c' k' \/ p_cached_ cache' c' k' \/ p_batch_ (a_qthread A) (a_qglobal A) c' k' ->
    (c' = c /\ k' = k) \/
    (ChP (CP c' k') <> ChP (CP c k) /\ (p_free_ (a_reg A) c' k' \/ p_cached_ (a_cache A) c' k' \/ p_batch_ (a_qthread A) (a_qglobal A) c' k')).
  Proof.
    intros c' k' Hc ST. destruct (chunk_eq_dec (ChP (CP c' k')) (ChP (CP c k))) as [E|NE]; [left; injection E as -> ->; split; reflexivity| right].
    split; [exact NE|]. unfold p_free_, p_cached_ in *. destruct ST as [F|[C|B]].
    - destruct (Z.eq_dec c' c) as [->|NEc]; [| rewrite (R'O c' NEc) in F; left; exact F].
      destruct (R'F k' F) as [F0|C0]; [left; exact F0| right; left; exact C0].
    - destruct (Z.eq_dec c' c) as [->|NEc]; [| rewrite (C'O c' NEc) in C; right; left; exact C].
      destruct (C'S k' C) as [C0| ->]; [right; left; exact C0|]. exfalso. exact (NE eq_refl).
    - right; right. exact B.
  Qed.

  Lemma shadow_P' : shadow_repr_ LPA sb reg' cache' (a_livemap A) (a_qthread A) (a_qglobal A) v'.
  Proof.
    geo. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((chunk_shadow A v held AR c k Gcr Gk)) as dR_43; dand4 dR_43 as S1 _ S3 S4 | pose proof (chunk_shadow A v held AR c k Gcr Gk) as (S1 & _ & S3 & S4) ]).
    split; [|split; [|split; [|split; [|split]]]].
    - intros c' k' Hc ST. destruct (old_state c' k' Hc ST) as [[-> ->]|[NE ST0]].
      + exact VSH.
      + apply (shadow_free_P A v v' held AR c' k' Hc ST0). apply (AGsh_prim c' k'); [| exact NE].
        destruct ST0 as [F|[C|[E B]]]; [exact (free_carved A v held AR c' k' Hc F)| exact (cached_carved A v held AR c' k' Hc C)| subst c'; split; [exact Hc| exact (batch_idx_range A v held AR k' (bi_in_big A k' B))]].
    - intros u c' k' n1 Hl. apply (shadow_live_P A v v' held AR u c' k' n1 Hl). apply (AGsh_prim c' k').
      + exact (known_carved A v held AR _ _ (known_live A v held AR u _ Hl)).
      + exact (NE_live u _ Hl).
    - intros c' k' n1 He. apply (shadow_quar_P A v v' held AR c' k' n1 He). apply (AGsh_prim c' k').
      + exact (known_carved A v held AR _ _ (known_quar A v held AR _ (q_in_big A _ He))).
      + exact (NE_rest _ He).
    - intros c' Hc. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
      + (* [comment removed for export] *)
        destruct R'E as (EMU & EAL & _). rewrite EMU, EAL.
        (first [ pose proof ((region_tail_shadow A v held AR c Gcr)) as dR_44; dand7 dR_44 as T1 T2 T3 _ _ T6 T7 | pose proof (region_tail_shadow A v held AR c Gcr) as (T1 & T2 & T3 & _ & _ & T6 & T7) ]). cbv zeta in *.
        (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_45; dand5 dR_45 as _ _ _ SH4 _ | pose proof (ar_shadow _ _ _ _ _ R) as (_ & _ & _ & SH4 & _) ]). destruct (SH4 c Gcr) as [X Y]. cbv zeta in X, Y. change (p_sb (a_pl A)) with sb in *.
        (first [ pose proof ((rk_ri A v held AR)) as dR_46; dand10 dR_46 as _ _ _ _ _ _ _ _ FAE RBE | pose proof (rk_ri A v held AR) as (_ & _ & _ & _ & _ & _ & _ & _ & FAE & RBE) ]).
        assert (FAB : region_beg sb c + kFreeArrayOffset = fac) by (rewrite Gfac; reflexivity).
        split.
        * eapply fill_at_agree; [exact X|]. intros i Hi.
          assert (X2 : region_beg sb c + rg_mapped_user (a_reg A c) <= alloc_ceiling) by (clear -Grbri Gmk Grice; kung_all; lia). apply sh_mono in X2.
          assert (X1 : sb <= region_beg sb c + rg_allocated_user (a_reg A c)) by (clear -Grbp Gpa Gsz Gsb Grb Gcr; lia). apply sh_mono in X1.
          pose proof (T6 k Gk) as Q. pose proof T7 as Q7. rewrite FAB in Q7. assert (X3 : fac <= fac + mfa) by (clear -Gnf; lia). apply sh_mono in X3.
          apply AGhs.
          -- clear -Hi X1 X2 T1 Gshsb Gshce. lia.
          -- intros SP. pose proof (SHPW _ SP) as PZ. clear -Hi Q PZ Gshs. lia.
          -- clear -Hi T1 Q7 X3. lia.
        * unfold fill_at. replace (Z.to_nat (mfa' / 8)) with (Z.to_nat (mfa / 8) + Z.to_nat ((mfa' - mfa) / 8))%nat by (clear -Gmfa Gnf Gm8 Gm8'; lia).
          rewrite repeat_app. apply bytes_at_app. split.
          -- eapply bytes_at_xfer; [exact Y|]. rewrite repeat_length. intros z Hz. rewrite Z2Nat.id in Hz by (apply Z.div_pos; clear -Gnf; lia). apply AGhs.
             ++ rewrite FAB in Hz. assert (H : sb <= fac) by (clear -Gsbf Gnf Gfac Grb Gcr; unfold kFreeArrayOffset in *; lia). apply sh_mono in H.
                assert (H0 : (fac + mfa) <= alloc_ceiling) by (clear -Gfac Grb Grbri Gmfa Gri Grice; kung_all; lia). apply sh_mono in H0.
                rewrite (sh_add fac mfa) in H0; [| clear -Gfac Grb Gsbm; unfold kFreeArrayOffset in *; lia| exact Gm8]. clear -Hz H H0 Gshsb Gshce. lia.
             ++ intros SP. pose proof (SHPW _ SP) as PZ. rewrite FAB in Hz. assert (H : (p + size) <= fac) by (clear -Gpa Gam Gmk Gfac; unfold kFreeArrayOffset in *; lia). apply sh_mono in H. clear -Hz H PZ Gshs. lia.
             ++ rewrite FAB in Hz. rewrite (sh_add fac mfa); [| clear -Gfac Grb Gsbm; unfold kFreeArrayOffset in *; lia| exact Gm8]. clear -Hz. lia.
          -- rewrite repeat_length, Z2Nat.id by (apply Z.div_pos; clear -Gnf; lia). rewrite FAB.
             rewrite <- (sh_add fac mfa); [| clear -Gfac Grb Gsbm; unfold kFreeArrayOffset in *; lia| exact Gm8]. exact P_fash.
      + rewrite (R'O c' NE). (first [ pose proof ((region_tail_shadow A v held AR c' Hc)) as dR_47; dand7 dR_47 as T1 T2 T3 _ _ T6 T7 | pose proof (region_tail_shadow A v held AR c' Hc) as (T1 & T2 & T3 & _ & _ & T6 & T7) ]). cbv zeta in *.
        (first [ pose proof ((region_piece_boundsT A c' WF0 Hc)) as dR_48; dand12 dR_48 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | pose proof (region_piece_boundsT A c' WF0 Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]). cbv zeta in *.
        (first [ pose proof ((rk_ri A v held AR)) as dR_49; dand10 dR_49 as _ _ _ _ _ _ _ _ FAE RBE | pose proof (rk_ri A v held AR) as (_ & _ & _ & _ & _ & _ & _ & _ & FAE & RBE) ]).
        assert (RR : region_beg sb c' + kRegionSize <= region_beg sb c \/ region_beg sb c + kRegionSize <= region_beg sb c').
        { rewrite (RBE c'), (RBE c). clear -NE Hc Gcr. unfold kRegionSize. assert (c' + 1 <= c \/ c + 1 <= c') as [X|X] by lia; [left|right]; nia. }
        assert (RB8 : region_beg sb c' mod 8 = 0) by (clear -Q9; lia).
        apply (shadow_tails_P A v v' held AR c' Hc); cbv zeta; intros z Hz; apply AGhs.
        * assert (H : sb <= (region_beg sb c' + rg_allocated_user (a_reg A c'))) by (clear -Q2 Q3; lia). apply sh_mono in H.
          assert (H0 : (region_beg sb c' + rg_mapped_user (a_reg A c')) <= alloc_ceiling) by (clear -Q4 Q5 Q6 Q7 Q8; kung_all; lia). apply sh_mono in H0. clear -Hz H H0 T1 Gshsb Gshce. lia.
        * destruct RR as [D|D].
          -- intros SP. pose proof (SHPW _ SP) as PZ. assert (H : (region_beg sb c' + rg_mapped_user (a_reg A c')) <= p) by (clear -D Q4 Grbp; kung_all; lia). apply sh_mono in H. clear -Hz H T1 PZ. lia.
          -- intros SP. pose proof (SHPW _ SP) as PZ. assert (H : (p + size) <= (region_beg sb c' + rg_allocated_user (a_reg A c'))) by (clear -D Q3 Gpa Gam Gmk; kung_all; lia). apply sh_mono in H. clear -Hz H T1 PZ Gshs. lia.
        * assert (FA8 : (fac + mfa) mod 8 = 0) by (rewrite Gfac, Grb; clear -Gsbm Gm8; unfold kFreeArrayOffset; lia).
          assert (LE8 : (mfa' - mfa) mod 8 = 0) by (clear -Gm8 Gm8'; lia). rewrite <- (sh_add (fac + mfa) (mfa' - mfa) FA8 LE8). destruct RR as [D|D].
          -- assert (H : (region_beg sb c' + rg_mapped_user (a_reg A c')) <= (fac + mfa)) by (clear -D Q4 Gfac Gnf; kung_all; lia). apply sh_mono in H. clear -Hz H T1. lia.
          -- assert (H : (fac + mfa + (mfa' - mfa)) <= (region_beg sb c' + rg_allocated_user (a_reg A c'))) by (clear -D Q3 Gfac Gmfa; kung_all; lia). apply sh_mono in H. clear -Hz H T1. lia.
        * assert (H : sb <= (region_beg sb c' + kFreeArrayOffset)) by (clear -Q2; kung_all; lia). apply sh_mono in H.
          rewrite <- (sh_add (region_beg sb c' + kFreeArrayOffset) (rg_mapped_fa (a_reg A c'))) in Hz; [| clear -RB8; unfold kFreeArrayOffset; lia| exact Q12].
          assert (H0 : (region_beg sb c' + kFreeArrayOffset + rg_mapped_fa (a_reg A c')) <= alloc_ceiling) by (clear -Q6 Q7 Q8; kung_all; lia). apply sh_mono in H0. clear -Hz H H0 T1 Gshsb Gshce. lia.
        * rewrite <- (sh_add (region_beg sb c' + kFreeArrayOffset) (rg_mapped_fa (a_reg A c'))) in Hz; [| clear -RB8; unfold kFreeArrayOffset; lia| exact Q12]. destruct RR as [D|D].
          -- intros SP. pose proof (SHPW _ SP) as PZ. assert (H : (region_beg sb c' + kFreeArrayOffset + rg_mapped_fa (a_reg A c')) <= p) by (clear -D Q6 Grbp; kung_all; lia). apply sh_mono in H. clear -Hz H PZ. lia.
          -- intros SP. pose proof (SHPW _ SP) as PZ. assert (H : (p + size) <= (region_beg sb c' + kFreeArrayOffset)) by (clear -D Gpa Gam Gmk; kung_all; lia). apply sh_mono in H. clear -Hz H PZ Gshs. lia.
        * rewrite <- (sh_add (region_beg sb c' + kFreeArrayOffset) (rg_mapped_fa (a_reg A c'))) in Hz; [| clear -RB8; unfold kFreeArrayOffset; lia| exact Q12].
          assert (FA8 : (fac + mfa) mod 8 = 0) by (rewrite Gfac, Grb; clear -Gsbm Gm8; unfold kFreeArrayOffset; lia).
          assert (LE8 : (mfa' - mfa) mod 8 = 0) by (clear -Gm8 Gm8'; lia). rewrite <- (sh_add (fac + mfa) (mfa' - mfa) FA8 LE8). destruct RR as [D|D].
          -- assert (H : (region_beg sb c' + kFreeArrayOffset + rg_mapped_fa (a_reg A c')) <= (fac + mfa)) by (clear -D Q6 Gfac Gnf; kung_all; lia). apply sh_mono in H. clear -Hz H. lia.
          -- assert (H : (fac + mfa + (mfa' - mfa)) <= (region_beg sb c' + kFreeArrayOffset)) by (clear -D Gfac Gmfa; kung_all; lia). apply sh_mono in H. clear -Hz H. lia.
    - intros u mb n1 Hl. apply (shadow_seclive_P A v v' held AR u mb n1 Hl).
      pose proof (known_live A v held AR u _ Hl) as KN. unfold known in KN. cbn [li_chunk li_n] in KN. destruct KN as (Hin & _).
      intros z Hz. exact (AGsh_sec (CS mb n1) Hin z Hz).
    - intros mb n2 n1 He. apply (shadow_secquar_P A v v' held AR mb n2 n1 He).
      pose proof (known_quar A v held AR _ (q_in_big A _ He)) as KN. unfold known in KN. cbn [qe_chunk qe_n] in KN. (first [ dand3 KN as Hin _ -> | destruct KN as (Hin & _ & ->) ]).
      intros z Hz. exact (AGsh_sec (CS mb n1) Hin z Hz).
  Qed.

  (* [comment removed for export] *)
  Lemma vsh_entry : forall n,
    wf_qentry_ (a_reg A) (a_sec A) (QE (ChP (CP c k)) n) -> lentry_cells sb v (QE (ChP (CP c k)) n) ->
    (forall a, SHP a <-> sh (p + rz_size n) <= a < sh (p + rz_size n) + (user_size n + 7) / 8) ->
    bytes_at rsegs v' (sh (p + rz_size n)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (round_up (user_size n) 8 / 8))) ->
    bytes_at rsegs v' (sh p) (pshadow_free c).
  Proof.
    intros n WE LE SHPE P_sh. geo. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((ek_geo A v held c k n AR WE)) as dR_51; dand4 dR_51 as _ CC NR _ | pose proof (ek_geo A v held c k n AR WE) as (_ & CC & NR & _) ]).
    (first [ pose proof ((ek_cells A v held c k n AR WE LE)) as dR_52; dex2 dR_52 as b1 ctxw; dand10 dR_52 as _ _ _ _ _ SHQ QL SHA R88 _ | pose proof ((ek_cells A v held c k n AR WE LE)) as dR_52; dand12 dR_52 as b1 ctxw _ _ _ _ _ SHQ QL SHA R88 _ | pose proof (ek_cells A v held c k n AR WE LE) as (b1 & ctxw & _ & _ & _ & _ & _ & SHQ & QL & SHA & R88 & _) ]).
    (first [ pose proof ((chunk_shadow A v held AR c k Gcr Gk)) as dR_53; dand4 dR_53 as S1 _ S3 S4 | pose proof (chunk_shadow A v held AR c k Gcr Gk) as (S1 & _ & S3 & S4) ]).
    apply (shadow_recycled v v' c n (sh p) NR CC SHQ); [rewrite <- SHA; exact P_sh|].
    intros z Hz Nz. apply AGhs.
    - rewrite S1 in S4. clear -Hz S3 S4 Gshce. lia.
    - intros SP. apply Nz. rewrite <- SHA. exact (proj1 (SHPE z) SP).
    - assert (A8 : p mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact Gpm]).
      assert (S8 : size mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact Gszm]).
      pose proof (sh_range_before p size (fac + mfa) z A8 S8 ltac:(clear -Gpa Gam Gmk Gfac Gnf; unfold kFreeArrayOffset in *; lia) Hz) as X. clear -X. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable limbo' : list batch.
  Definition recA' : AState :=
    mkA (a_pl A) reg' (a_cache_inited A) cache' (a_livemap A) [] (a_qglobal A) (a_sec A) (a_depot A) (a_fhint A) (a_fframes A)
        (a_ia_inited A) (a_oom A) (a_tiny A) limbo' (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).

  Theorem recp_arepr : @arepr _ DepotRepL LPA AL_pasan held recA' v'.
  Proof.
    pose proof qt_nil as QT.
    constructor; cbn [recA' a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh];
      unfold a_sb, a_fs; cbn [a_pl].
    - exact consts_P'.
    - exact locks_P'.
    - exact regions_P'.
    - exact cache_P'.
    - exact live_P'.
    - rewrite <- QT. exact quar_P'.
    - exact sec_P'.
    - exact depot_P'.
    - exact ia_P'.
    - exact fsbase_P'.
    - exact fsptrs_P'.
    - exact fsflags_P'.
    - exact maps_P'.
    - rewrite <- QT. exact shadow_P'.
  Qed.

  (* [comment removed for export] *)
  Lemma lentry_xfer : forall e', In e' (q_entries (a_qthread A ++ QGL)) -> qe_chunk e' <> ChP (CP c k) -> lentry_cells sb v e' -> lentry_cells sb v' e'.
  Proof.
    (intros e' HeQ NE; (first [ intro dR_64; dand4 dR_64 as HR J MC SH | intros (HR & J & MC & SH) ])). pose proof alloc_ceiling_val as CE.
    pose proof (known_quar A v held AR e' HeQ) as CL. pose proof (known_range A v held AR _ _ CL) as RNG.
    pose proof (known_carved A v held AR _ _ CL) as CV.
    assert (AG : forall a, chunk_lo sb (qe_chunk e') <= a < chunk_hi sb (qe_chunk e') -> v' (wz a) = v (wz a)) by (intros a Ha; exact (AGchunk _ CV NE a Ha)).
    split; [|split; [|split]].
    - apply (hdr_P A v v'); [| exact HR]. intros a Ha. apply AG. apply (hdr_foot_in A _ (qe_n e')); [exact CL| left; exact Ha].
    - pose proof (user_in A _ _ CL) as UI. apply (junk_N v v' NN); [lia| right; pose proof (qentry_wf A v held AR _ HeQ) as [N0 _]; lia| exact J].
    - apply (mapped_N v v' NN); [lia| right; lia| lia| exact MC].
    - destruct (qe_chunk e') as [[c'' k'']|[mb n1]] eqn:EC.
      + eapply bytes_at_xfer; [exact SH|]. intros z Hz. apply (AGsh_prim c'' k''); [exact CV| exact NE|].
        unfold known in CL. (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]). rewrite (pshadow_quar_length c'' (qe_n e')) in Hz by lia. exact Hz.
      + eapply bytes_at_xfer; [exact SH|]. intros z Hz. unfold known in CL. (first [ dand3 CL as Hin Hn En | destruct CL as (Hin & Hn & En) ]). subst n1.
        apply (AGsh_sec (CS mb (qe_n e')) Hin). cbn [cs_map cs_n]. rewrite (sshadow_quar_length (qe_n e')) in Hz by lia. exact Hz.
  Qed.

  Lemma lbatch_xfer : forall idx es (j : nat) sz, carved A (ChP (CP kQuarantineBatchClass idx)) -> ChP (CP kQuarantineBatchClass idx) <> ChP (CP c k) ->
    Z.of_nat (length es) <= kQuarantineBatchCount ->
    let ba := chunk_addr sb kQuarantineBatchClass idx in
    lbatch_cells sb v ba es j sz ->
    lbatch_cells sb v' ba es j sz /\
    (bytes_at rsegs v (sh ba) (pshadow_free kQuarantineBatchClass) -> bytes_at rsegs v' (sh ba) (pshadow_free kQuarantineBatchClass)).
  Proof.
    intros idx es j sz CV NE LEN. cbv zeta. ((first [ intro dR_65; dand3 dR_65 as SL SZ MP | intros (SL & SZ & MP) ])). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((carved_range A v held AR _ CV)) as dR_56; dand3 dR_56 as R1 R2 R3 | pose proof (carved_range A v held AR _ CV) as (R1 & R2 & R3) ]). cbn [chunk_lo chunk_hi alloc_beg] in R1, R2, R3.
    assert (AG : forall a, chunk_addr sb kQuarantineBatchClass idx <= a < chunk_addr sb kQuarantineBatchClass idx + kQuarantineBatchBytes -> v' (wz a) = v (wz a)).
    { intros a Ha. apply (AGchunk _ CV NE a). cbn [chunk_lo chunk_hi alloc_beg]. unfold kQuarantineBatchBytes in Ha. change (class_size kQuarantineBatchClass) with 8192. exact Ha. }
    split; [split; [|split]|].
    - intros i e Hi He. eapply u64_at_agree; [exact (SL i e Hi He)|]. intros q Hq. apply AG. pose proof (nth_error_Some_lt _ _ _ He).
      unfold off_qb_batch, kQuarantineBatchBytes, kQuarantineBatchCount in *. lia.
    - eapply u64_at_agree; [exact SZ|]. intros q Hq. apply AG. unfold off_qb_size, kQuarantineBatchBytes in *. lia.
    - change (class_size kQuarantineBatchClass) with 8192 in R2. unfold kQuarantineBatchBytes in *. apply (mapped_N v v' NN); [lia| right; lia| lia| exact MP].
    - intros SH. eapply bytes_at_xfer; [exact SH|]. intros z Hz. apply (AGsh_prim kQuarantineBatchClass idx CV NE).
      unfold pshadow_free, fa8 in Hz. rewrite repeat_length, Z2Nat.id in Hz by (change (class_size kQuarantineBatchClass) with 8192; lia). exact Hz.
  Qed.

  Lemma tmp_chain_xfer : forall bs, (forall b', In b' bs -> In b' more) -> tmp_chain sb v bs -> tmp_chain sb v' bs.
  Proof.
    induction bs as [|b' bs IH]; intros SUB TC; [exact I|]. cbn [tmp_chain] in *. destruct TC as [X TC].
    assert (Hb : In b' (a_qthread A ++ QGL)) by (apply more_in; apply SUB; left; reflexivity).
    pose proof (batch_carved A v held AR b' Hb) as CV. pose proof (NE_batch b' ltac:(right; apply SUB; left; reflexivity)) as NE. (first [ pose proof ((batch_range A v held AR b' Hb)) as dR_57; dand3 dR_57 as R1 R2 R3 | pose proof (batch_range A v held AR b' Hb) as (R1 & R2 & R3) ]).
    split; [| apply IH; [intros b'' Hb''; apply SUB; right; exact Hb''| exact TC]].
    eapply rw_cells_agree; [exact X|]. cbn [cells_size csize Nat.add]. intros i Hi. apply (AGchunk _ CV NE).
    cbn [chunk_lo chunk_hi alloc_beg]. unfold batch_addr in *. change (class_size kQuarantineBatchClass) with 8192. lia.
  Qed.
End ReprRecp.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section EntryVictim.
Context {Clg : Ceiling}.
  Variables (A : AState) (v : mem) (held : list Z) (c k n kb : Z) (es : list qentry) (more : list batch).
  Hypothesis AR : WFT A /\ @arepr _ DepotRepL LPA AL_pasan held A v.
  Hypothesis WR : WFR A.
  Hypothesis L : a_qlimbo A = BA kb (QE (ChP (CP c k)) n :: es) :: more.
  #[warnings="-notation-for-abbreviation"] Local Notation QGL := (a_qglobal A ++ a_qlimbo A).

  Lemma ev_in : In (QE (ChP (CP c k)) n) (q_entries (a_qthread A ++ QGL)).
  Proof. apply (limbo_in A kb _ more WR L). apply in_or_app. left. left. reflexivity. Qed.
  Lemma ev_wf : wf_qentry_ (a_reg A) (a_sec A) (QE (ChP (CP c k)) n).
  Proof. exact (qentry_wf A v held AR _ ev_in). Qed.
  Lemma ev_carved : carved A (ChP (CP c k)).
  Proof. (first [ pose proof ((ek_geo A v held c k n AR ev_wf)) as dR_58; dand5 dR_58 as CR _ _ KR _ | pose proof (ek_geo A v held c k n AR ev_wf) as (CR & _ & _ & KR & _) ]). exact (conj CR KR). Qed.
  Lemma ev_ne_live : forall u li, a_livemap A !! u = Some li -> li_chunk li <> ChP (CP c k).
  Proof. intros u li Hl. exact (live_not_quar_chunk A v held AR u li _ Hl ev_in). Qed.
  Lemma ev_ne_batch : forall b, In b (a_qthread A ++ a_qglobal A) \/ In b more -> ChP (CP kQuarantineBatchClass (ba_idx b)) <> ChP (CP c k).
  Proof.
    intros b Hb E. refine (quar_not_batch A v held AR _ b ev_in _ (eq_sym E)).
    destruct Hb as [Hb|Hb]; [exact (rest_in A WR b Hb)| exact (more_in A kb _ more WR L b Hb)].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ev_nodup : NoDup (map qe_chunk (q_entries (a_qglobal A)) ++ (ChP (CP c k) :: map qe_chunk (es ++ q_entries more))).
  Proof.
    (first [ pose proof ((wrL A WR)) as dR_60; dand4 dR_60 as _ _ ND _ | destruct (wrL A WR) as (_ & _ & ND & _) ]). unfold quarantined_chunks_ in ND. cbn [app] in ND. rewrite L in ND.
    unfold q_entries in ND |- *. rewrite flat_map_app, map_app in ND. cbn [flat_map ba_entries app map qe_chunk] in ND. exact ND.
  Qed.
  Lemma ev_ne_rest : forall e', In e' (q_entries (a_qthread A ++ a_qglobal A)) -> qe_chunk e' <> ChP (CP c k).
  Proof.
    intros e' He E. rewrite (wrT A WR) in He. cbn [app] in He. pose proof ev_nodup as ND.
    apply (NoDup_app_In _ _ (ChP (CP c k)) ND); [| left; reflexivity]. rewrite <- E. apply in_map. exact He.
  Qed.
  Lemma ev_ne_limbo : forall e', In e' (es ++ q_entries more) -> qe_chunk e' <> ChP (CP c k).
  Proof.
    intros e' He E. pose proof ev_nodup as ND. apply (proj1 (list.NoDup_app _ _)) in ND as (_ & _ & ND). rewrite <- E in ND. inversion ND as [|x l NI ND']; subst x l.
    apply NI. apply list_elem_of_In. apply in_map. exact He.
  Qed.
End EntryVictim.

Section BatchVictim.
Context {Clg : Ceiling}.
  Variables (A : AState) (v : mem) (held : list Z) (kb : Z) (more : list batch).
  Hypothesis AR : WFT A /\ @arepr _ DepotRepL LPA AL_pasan held A v.
  Hypothesis WR : WFR A.
  Hypothesis L : a_qlimbo A = BA kb [] :: more.
  #[warnings="-notation-for-abbreviation"] Local Notation QGL := (a_qglobal A ++ a_qlimbo A).
  #[local] Notation c24 := kQuarantineBatchClass.

  Lemma bv_head : In (BA kb []) (a_qthread A ++ QGL).
  Proof. exact (head_in A kb [] more WR L). Qed.
  Lemma bv_carved : carved A (ChP (CP c24 kb)).
  Proof. exact (batch_carved A v held AR (BA kb []) bv_head). Qed.
  Lemma bv_ne_live : forall u li, a_livemap A !! u = Some li -> li_chunk li <> ChP (CP c24 kb).
  Proof. intros u li Hl. exact (live_not_batch A v held AR u li (BA kb []) Hl bv_head). Qed.
  Lemma bv_nodup : NoDup (map ba_idx (a_qglobal A) ++ kb :: map ba_idx more).
  Proof.
    (first [ pose proof ((wrL A WR)) as dR_61; dand3 dR_61 as _ ND _ | destruct (wrL A WR) as (_ & ND & _) ]). unfold batch_indices_ in ND. cbn [app] in ND. rewrite L, map_app in ND. cbn [map ba_idx] in ND. exact ND.
  Qed.
  Lemma bv_ne_batch : forall b, In b (a_qthread A ++ a_qglobal A) \/ In b more -> ChP (CP c24 (ba_idx b)) <> ChP (CP c24 kb).
  Proof.
    intros b Hb E. injection E as E. pose proof bv_nodup as ND. rewrite (wrT A WR) in Hb. cbn [app] in Hb. destruct Hb as [Hb|Hb].
    - apply (NoDup_app_In _ _ kb ND); [rewrite <- E; apply in_map; exact Hb| left; reflexivity].
    - apply (proj1 (list.NoDup_app _ _)) in ND as (_ & _ & ND). rewrite <- E in ND. inversion ND as [|x l NI ND']; subst x l. apply NI. apply list_elem_of_In. apply in_map. exact Hb.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bv_ne_rest : forall e', In e' (q_entries (a_qthread A ++ a_qglobal A)) -> qe_chunk e' <> ChP (CP c24 kb).
  Proof. intros e' He. exact (quar_not_batch A v held AR e' (BA kb []) (q_in_big A e' He) bv_head). Qed.
  Lemma bv_ne_limbo : forall e', In e' (q_entries more) -> qe_chunk e' <> ChP (CP c24 kb).
  Proof.
    intros e' He. exact (quar_not_batch A v held AR e' (BA kb []) (limbo_in A kb [] more WR L e' He) bv_head).
  Qed.
End BatchVictim.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u32s_nth : forall ws i w, nth_error ws i = Some w -> firstn 4 (skipn (4 * i) (u32s ws)) = le4 w.
Proof.
  induction ws as [|x ws IH]; intros [|i] w H; cbn [nth_error] in H; try discriminate.
  - injection H as ->. cbn [u32s]. replace (4 * 0)%nat with 0%nat by lia. rewrite skipn_O.
    rewrite firstn_app, length_le4, Nat.sub_diag, firstn_O, app_nil_r. rewrite firstn_all2 by (rewrite length_le4; lia). reflexivity.
  - cbn [u32s]. rewrite skipn_app, length_le4. rewrite skipn_all2 by (rewrite length_le4; lia). cbn [app].
    replace (4 * S i - 4)%nat with (4 * i)%nat by lia. exact (IH i w H).
Qed.

Section PostCells.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Lemma line_of_cells : forall (v' : mem) (e : Z) (c : Z) (ks : list word) (chunks : list Z) (ci : bool),
    1 <= c <= 30 -> ci = true -> length ks = 16%nat -> Z.of_nat (length chunks) <= 16 ->
    (forall i k', nth_error chunks i = Some k' -> nth_error ks i = Some (Z_to_bv 64 (k' * class_size c / kCompactPtrScale)) /\ 0 <= k' * class_size c / kCompactPtrScale < 2^32) ->
    rw_cells rsegs v' e [C4 (Z_to_bv 64 (Z.of_nat (length chunks))); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)] ->
    Z.of_nat (length chunks) <= 16 /\
    u32_at rsegs v' (e + off_pc_count) (Z.of_nat (length chunks)) /\
    (if ci && negb (c =? 0) then u32_at rsegs v' (e + off_pc_max_count) (max_count c) /\ u64_at rsegs v' (e + off_pc_class_size) (class_size c)
     else u32_at rsegs v' (e + off_pc_max_count) 0 /\ u64_at rsegs v' (e + off_pc_class_size) 0) /\
    (forall i k', nth_error chunks i = Some k' -> u32_at rsegs v' (e + off_pc_chunk (Z.of_nat i)) (k' * class_size c / kCompactPtrScale)) /\
    junk_at rsegs v' (e + off_pc_chunk (Z.of_nat (length chunks))) (4 * (16 - Z.of_nat (length chunks))).
  Proof.
    intros v' e c ks chunks ci Hc CI LK LC ENT RW. rewrite CI. cbn [andb negb]. destruct (Z.eqb_spec c 0); [lia|].
    destruct RW as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    apply bytes_at_app in B as [B1 B]. rewrite length_le4 in B. apply bytes_at_app in B as [B2 B]. rewrite length_le4 in B.
    apply bytes_at_app in B as [B3 B]. rewrite length_le8 in B.
    replace (e + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8) with (e + 16) in B by lia.
    pose proof (max_count_range c Hc) as MC. pose proof (class_size_range c Hc) as CS.
    unfold off_pc_count, off_pc_max_count, off_pc_class_size, off_pc_chunk.
    unfold u32_at, u64_at, junk_at.
    split; [exact LC|]. split; [| split; [split|split]].
    - rewrite Z.add_0_r. exact B1.
    - replace (e + 4) with (e + Z.of_nat 4) by lia. exact B2.
    - replace (e + 8) with (e + Z.of_nat 4 + Z.of_nat 4) by lia. exact B3.
    - intros i k' Hk. destruct (ENT i k' Hk) as [NK RK]. pose proof (nth_error_Some_lt _ _ _ NK) as IL.
      pose proof (bytes_at_mid v' (e + 16) (u32s ks) (4 * i) 4 B ltac:(rewrite u32s_length; lia)) as X.
      rewrite (u32s_nth ks i _ NK) in X. replace (e + 16 + Z.of_nat (4 * i)) with (e + (16 + 4 * Z.of_nat i)) in X by lia. exact X.
    - exists (firstn (Z.to_nat (4 * (16 - Z.of_nat (length chunks)))) (skipn (4 * length chunks) (u32s ks))). split.
      + rewrite firstn_length_le; [lia|]. rewrite length_skipn, u32s_length. lia.
      + replace (e + (16 + 4 * Z.of_nat (length chunks))) with (e + 16 + Z.of_nat (4 * length chunks)) by lia.
        apply bytes_at_mid; [exact B|]. rewrite u32s_length. lia.
  Qed.
End PostCells.

