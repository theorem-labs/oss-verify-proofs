(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Refund.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Ledger OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Restrict OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Lazyiq4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Fixej5z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.EvtAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund.Madv3tp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocI AMalmys ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ABudget ASecB3 AFreeB6 ANodijx APgGeo AFreeX1 AFreeX2 AFreeRS.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize, kSecondaryHeaderSize, kMaxPrimaryUser in *.


(* [comment removed for export] *)
Definition kgeo {Clg : Ceiling} (p n0 : Z) : Prop :=
  (aobj (p - 6144) (map_size n0) /\ (p - 6144) mod 4096 = 0 /\ 4096 + 32 <= map_size n0 /\ map_size n0 mod 4096 = 0 /\ p - 6144 + map_size n0 <= alloc_ceiling /\
                    p = p - 6144 + 6144 /\ p + 8 * ((n0 + 7) / 8) <= p - 6144 + map_size n0 /\ n0 + 6144 <= map_size n0 /\ kMaxPrimaryUser < n0 < REQ_MAX /\
                    0x60a000 <= p - 6144 /\ p mod 16 = 0) /\
  (sh (p - 6144 + map_size n0) = sh (p - 6144) + map_size n0 / 8 /\ (sh (p - 6144)) mod 512 = 0 /\ (map_size n0 / 8) mod 512 = 0 /\
                    ((kHighShadowMapBeg <= sh (p - 6144) /\ sh (p - 6144) + map_size n0 / 8 <= kHighMemBeg /\ kHighMemBeg <= p - 6144) \/
                     (kLowShadowBeg + 0x200 <= sh (p - 6144) /\ sh (p - 6144) + map_size n0 / 8 < kShadowGapBeg /\ p - 6144 + map_size n0 <= kLowShadowMapBeg))).

Section KHulls.
Context {Clg : Ceiling}.
  Variables (A : AState) (p n0 : Z) (i : nat).
  Hypothesis G : kgeo p n0.
  Let GEO := proj1 G.
  Let SHR := proj2 G.
  Hypothesis NTH : nth_error (sr_chunks (a_sec A)) i = Some (CS (p - 6144) n0).

  #[warnings="-notation-for-abbreviation"] Local Notation P := (a_pl A).
  #[warnings="-notation-for-abbreviation"] Local Notation chunks := (sr_chunks (a_sec A)).
  #[warnings="-notation-for-abbreviation"] Local Notation h := (p - 6144).
  #[warnings="-notation-for-abbreviation"] Local Notation msz := (map_size n0).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation pbeg := (a8_pbeg (p - 6144)).
  #[warnings="-notation-for-abbreviation"] Local Notation pend := (a8_pend (p - 6144) (map_size n0)).


  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation e1 := (AFreeX2.e1 p).
  #[warnings="-notation-for-abbreviation"] Local Notation emid := (AFreeX2.emid p n0).
  #[warnings="-notation-for-abbreviation"] Local Notation e2 := (AFreeX2.e2 p n0).
  #[warnings="-notation-for-abbreviation"] Local Notation dead2 := (AFreeX2.dead2 p n0).
  #[warnings="-notation-for-abbreviation"] Local Notation REST := (AFreeX2.REST A i).
  #[warnings="-notation-for-abbreviation"] Local Notation H0p := (AFreeX2.H0p A p n0 i).
  #[warnings="-notation-for-abbreviation"] Local Notation H0s := (AFreeX2.H0s A p n0 i).
  #[warnings="-notation-for-abbreviation"] Local Notation H1 := (AFreeX2.H1 A p n0 i).
  #[warnings="-notation-for-abbreviation"] Local Notation H2 := (AFreeX2.H2 A p n0 i).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation LREST := (AFreeX2.LREST A i).
  #[warnings="-notation-for-abbreviation"] Local Notation L0p := (AFreeX2.L0p A p n0 i).
  #[warnings="-notation-for-abbreviation"] Local Notation L0s := (AFreeX2.L0s A p n0 i).
  #[warnings="-notation-for-abbreviation"] Local Notation L1 := (AFreeX2.L1 A p n0 i).

  (* [comment removed for export] *)
  #[using="SHR GEO G Clg"] Lemma ka8_geo : pg_dn (sh h) <= sh h <= pbeg /\ pbeg < pg_dn (sh h) + 4096 + 1 /\ sh h < pg_dn (sh h) + 4096 /\ pbeg <= sh h + 4095 /\
                 pbeg + 4096 <= pend /\ pend <= sh h + msz / 8 <= pg_up (sh h + msz / 8) /\ sh h + msz / 8 < pend + 4096 /\
                 pg_up (sh h + msz / 8) <= sh h + msz / 8 + 4095 /\
                 pg_dn (sh h) mod 4096 = 0 /\ pbeg mod 4096 = 0 /\ pend mod 4096 = 0 /\ pg_up (sh h + msz / 8) mod 4096 = 0 /\
                 sh (h + msz) = sh h + msz / 8 /\ 9216 <= msz / 8 /\
                 ((kHighShadowMapBeg <= pg_dn (sh h) /\ pg_up (sh h + msz / 8) <= kHighMemBeg /\ kHighMemBeg <= h) \/
                  (kLowShadowBeg <= pg_dn (sh h) /\ pg_up (sh h + msz / 8) <= kShadowGapBeg /\ h + msz <= kLowShadowMapBeg)).
  Proof.
    pose proof GEO as (HLO & HAL & MSZ & MSZAL & HHI & PH & PIN & N6 & NR & H5 & PM).
    pose proof SHR as (SHA & M512 & D512 & SIDE).
    (first [ pose proof ((pg_facts (sh h))) as dR_1; dand4 dR_1 as A1 A2 A3 A4 | pose proof (pg_facts (sh h)) as (A1 & A2 & A3 & A4) ]). (first [ pose proof ((pg_facts (sh h + msz / 8))) as dR_2; dand4 dR_2 as B1 B2 B3 B4 | pose proof (pg_facts (sh h + msz / 8)) as (B1 & B2 & B3 & B4) ]).
    unfold a8_pbeg, a8_pend.
    assert (BIG : 9216 <= msz / 8).
    { pose proof (Z_div_mod_eq_full msz 4096) as QM. rewrite MSZAL, Z.add_0_r in QM. unfold kMaxPrimaryUser in NR.
      apply Z.div_le_lower_bound; [lia|]. lia. }
    pose proof (Z_div_mod_eq_full (pg_dn (sh h)) 4096) as Q1. rewrite A2, Z.add_0_r in Q1.
    pose proof (Z_div_mod_eq_full (pg_up (sh h)) 4096) as Q2. rewrite A4, Z.add_0_r in Q2.
    pose proof (Z_div_mod_eq_full (pg_dn (sh h + msz / 8)) 4096) as Q3. rewrite B2, Z.add_0_r in Q3.
    pose proof (Z_div_mod_eq_full (pg_up (sh h + msz / 8)) 4096) as Q4. rewrite B4, Z.add_0_r in Q4.
    (* [comment removed for export] *)
    split; [lia|]. split; [clear - A1 A3 Q1 Q2; lia|]. split; [lia|]. split; [lia|]. split; [clear - A3 B1 BIG Q2 Q3; lia|].
    repeat (split; [lia|]).
    unfold kHighShadowMapBeg, kHighMemBeg, kLowShadowBeg, kShadowGapBeg, kLowShadowMapBeg in *.
    destruct SIDE as [(X1 & X2 & X3)|(X1 & X2 & X3)]; [left| right]; (first [ solve [clear - X1 X2 X3 A1 A3 B1 B3 Q1 Q4 SHA HLO HAL MSZ MSZAL HHI H5; lia] | lia ]).
  Qed.

  (* [comment removed for export] *)
  #[using="NTH GEO G"] Lemma khull_perm0 : Permutation (pa_hull A) H0p.
  Proof.
    pose proof GEO as (HLO & HAL & MSZ & MSZAL & _).
    (first [ pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_3; dex2 dR_3 as l1 l2; destruct dR_3 as [E LEN] | pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_3; dand4 dR_3 as l1 l2 E LEN | destruct (@nth_error_split _ chunks i _ NTH) as (l1 & l2 & E & LEN) ]).
    assert (F1 : firstn i chunks = l1) by (rewrite E, <- LEN; rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r; reflexivity).
    assert (F2 : skipn (S i) chunks = l2).
    { rewrite E, <- LEN. rewrite skipn_app. replace (S (length l1) - length l1)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity. }
    unfold AFreeX2.H0p, AFreeX2.REST. rewrite F1, F2. unfold pa_hull, ahull_of, ahull_of_, aregions_. change (p_sb P) with sb.
    rewrite E at 1. rewrite sec_regions_app, sec_regions_cons. cbn [cs_map cs_n].
    rewrite (shadow_region_aligned h msz) by first [apply (mod0_down _ 4096 64); [exists 64; reflexivity| assumption] | lia].
    rewrite sec_regions_app, !hull_of_app. cbn [hull_of map fst snd app].
    (* [comment removed for export] *)
    apply Permutation_sym.
    lazymatch goal with |- Permutation (?a :: ?b :: ?img ++ (?X ++ ?Y ++ ?Z1 ++ ?Z2) ++ ?D ++ ?EX) _ =>
      apply (Permutation_trans (l' := (img ++ X ++ Y ++ Z1) ++ [a; b] ++ (Z2 ++ D ++ EX)));
      [ replace (a :: b :: img ++ (X ++ Y ++ Z1 ++ Z2) ++ D ++ EX) with ([a; b] ++ (img ++ X ++ Y ++ Z1) ++ (Z2 ++ D ++ EX)) by (repeat rewrite <- app_assoc; reflexivity);
        apply Permutation_app_swap_app
      | repeat rewrite <- app_assoc; apply Permutation_refl ]
    end.
  Qed.

  (* [comment removed for export] *)
  #[using="NTH GEO G"] Lemma klhull_perm0 : Permutation (pa_lhull A) L0p.
  Proof.
    pose proof GEO as (HLO & HAL & MSZ & MSZAL & _).
    (first [ pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_3; dex2 dR_3 as l1 l2; destruct dR_3 as [E LEN] | pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_3; dand4 dR_3 as l1 l2 E LEN | destruct (@nth_error_split _ chunks i _ NTH) as (l1 & l2 & E & LEN) ]).
    assert (F1 : firstn i chunks = l1) by (rewrite E, <- LEN; rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r; reflexivity).
    assert (F2 : skipn (S i) chunks = l2).
    { rewrite E, <- LEN. rewrite skipn_app. replace (S (length l1) - length l1)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity. }
    unfold AFreeX2.L0p, AFreeX2.LREST. rewrite F1, F2. unfold pa_lhull, alhull_of, alhull_of_, alregions_. change (p_sb P) with sb.
    rewrite E at 1. rewrite lsec_regions_app, lsec_regions_cons. cbn [cs_map cs_n].
    rewrite (shadow_region_aligned h msz) by first [apply (mod0_down _ 4096 64); [exists 64; reflexivity| assumption] | lia].
    rewrite lsec_regions_app, !hull_of_app. cbn [hull_of map fst snd app].
    apply Permutation_sym.
    lazymatch goal with |- Permutation (?b :: (?X ++ ?Y ++ ?Z1 ++ ?Z2) ++ ?DD ++ ?EX) _ =>
      apply (Permutation_trans (l' := (X ++ Y ++ Z1) ++ [b] ++ (Z2 ++ DD ++ EX)));
      [ replace (b :: (X ++ Y ++ Z1 ++ Z2) ++ DD ++ EX) with ([b] ++ (X ++ Y ++ Z1) ++ (Z2 ++ DD ++ EX)) by (repeat rewrite <- app_assoc; reflexivity);
        apply Permutation_app_swap_app
      | repeat rewrite <- app_assoc; apply Permutation_refl ]
    end.
  Qed.
  (* [comment removed for export] *)
  #[using="NTH GEO G"] Lemma kcover_REST : forall mdx,
    (forall s, In s chunks -> 0 <= cs_map s /\ 0 <= map_size (cs_n s) /\ cs_map s + map_size (cs_n s) < 2^64) ->
    alzfree_ AL_pasan P (a_reg A) mdx ->
    Forall (fun sc => eager_map (wz (cs_map sc)) (wz (map_size (cs_n sc))) mdx) (firstn i chunks ++ skipn (S i) chunks) ->
    hull_cover REST LREST (m_vm_lazy mdx).
  Proof.
    intros mdx SB Z9 EM. unfold AFreeX2.REST, AFreeX2.LREST. change sb with (p_sb P).
    apply (ahull_cover_ P (a_reg A) (SR (firstn i chunks ++ skipn (S i) chunks) 0) (a_deadsh A) mdx Z9 EM).
    cbn [sr_chunks]. intros sc Hsc. exact (SB sc (in_firstn_skipn_S chunks i sc Hsc)).
  Qed.

  #[using="SHR GEO G"] Lemma khull_bytes_H0s : hull_bytes H0s = hull_bytes H0p.
  Proof.
    (first [ pose proof (ka8_geo) as dR_4; dand15 dR_4 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 SHA BIG _ | pose proof ka8_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & SHA & BIG & _) ]).
    unfold AFreeX2.H0s, AFreeX2.H0p, AFreeX2.e1, AFreeX2.emid, AFreeX2.e2. rewrite !hull_bytes_cons.
    unfold hull_npages, page_size. cbn [fst snd].
    set (x := sh h + msz / 8) in *. set (u := pg_up x) in *. set (dn := pg_dn (sh h)) in *.
    set (K := 4096 * Z.of_nat (Z.to_nat ((h + msz - 1) / 4096 - h / 4096 + 1))). clearbody K.
    pose proof (Z_div_mod_eq_full dn 4096) as Q1. rewrite M1, Z.add_0_r in Q1.
    pose proof (Z_div_mod_eq_full pbeg 4096) as Q2. rewrite M2, Z.add_0_r in Q2.
    pose proof (Z_div_mod_eq_full pend 4096) as Q3. rewrite M3, Z.add_0_r in Q3.
    pose proof (Z_div_mod_eq_full u 4096) as Q4. rewrite M4, Z.add_0_r in Q4.
    assert (E0 : (x - 1) / 4096 = u / 4096 - 1) by (clear - G6 G8 Q4; lia).
    assert (E1 : sh h / 4096 = dn / 4096) by (clear - G1 G3 Q1; lia).
    assert (E2 : (pbeg - 1) / 4096 = pbeg / 4096 - 1) by (clear - Q2; lia).
    assert (E3 : (pend - 1) / 4096 = pend / 4096 - 1) by (clear - Q3; lia).
    assert (E4 : (u - 1) / 4096 = u / 4096 - 1) by (clear - Q4; lia).
    rewrite ?E0, ?E1, ?E2, ?E3, ?E4.
    set (qa := dn / 4096) in *. set (qb := pbeg / 4096) in *. set (qc := pend / 4096) in *. set (qd := u / 4096) in *.
    clearbody qa qb qc qd. clear - G1 G5 G6 Q1 Q2 Q3 Q4. lia.
  Qed.

  #[using="SHR GEO G"] Lemma klhull_bytes_H0s : hull_bytes L0s = hull_bytes L0p.
  Proof.
    pose proof khull_bytes_H0s as X. unfold AFreeX2.H0s, AFreeX2.H0p in X. unfold AFreeX2.L0s, AFreeX2.L0p. cbn [hull_bytes] in X |- *.
    set (KR := hull_bytes REST) in X. set (KL := hull_bytes LREST). clearbody KR KL. clear - X. Zify.zify; xlia zchecker.
  Qed.
  #[using="SHR GEO G"] Lemma kMInv_H0s : forall E mdx, MInv H0p L0p E mdx ->
    hull_cover REST LREST (m_vm_lazy mdx) -> lazy_free (m_vm_lazy mdx) h (h + msz) -> MInv H0s L0s E mdx.   (* [comment removed for export] *)
  Proof.
    intros E mdx HI CR LZC. (first [ pose proof (ka8_geo) as dR_5; dand13 dR_5 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 _ | pose proof ka8_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & _) ]).
    apply (MInv_rehull H0p L0p H0s L0s E E mdx HI).
    - intros q Hq. pose proof (minv_hull HI q Hq) as X. unfold AFreeX2.L0p, AFreeX2.L0s in *.
      cbn [page_hullb existsb] in X |- *. set (RR := existsb (page_meets_ivb (bv_unsigned q)) LREST) in *. clearbody RR.
      unfold AFreeX2.e1, AFreeX2.emid, AFreeX2.e2, page_meets_ivb in *. cbn [fst snd] in *. unfold page_size in *.
      apply Bool.orb_true_iff in X as [X|X]; [| rewrite X, !Bool.orb_true_r; reflexivity].
      apply andb_true_iff in X as [X1 X2]. apply Z.ltb_lt in X1. apply Z.ltb_lt in X2.
      clear - X1 X2 G1 G5 G6.
      destruct (Z.lt_ge_cases (bv_unsigned q) pbeg) as [C1|C1]; [apply Bool.orb_true_iff; left; apply andb_true_iff; split; apply Z.ltb_lt; lia|].
      apply Bool.orb_true_iff; right.
      destruct (Z.lt_ge_cases (bv_unsigned q) pend) as [C2|C2]; [apply Bool.orb_true_iff; left; apply andb_true_iff; split; apply Z.ltb_lt; lia|].
      apply Bool.orb_true_iff; right. apply Bool.orb_true_iff; left. apply andb_true_iff; split; apply Z.ltb_lt; lia.
    - exact (cover_H0s A p n0 i mdx CR LZC).
    - lia.
    - rewrite klhull_bytes_H0s. exact (minv_budget HI).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="SHR GEO G"] Lemma kMInv_H1 : forall E mdx, MInv H0s L0s E mdx ->
    hull_cover REST LREST (m_vm_lazy mdx) -> lazy_free (m_vm_lazy mdx) h (h + msz) ->
    MInv H1 L1 E (madvise_model (wz pbeg) (wz (pend - pbeg)) mdx).   (* [comment removed for export] *)
  Proof.
    intros E mdx HI CR LZC. (first [ pose proof (ka8_geo) as dR_6; dand15 dR_6 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 SHA BIG SIDE | pose proof ka8_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & SHA & BIG & SIDE) ]). pose proof alloc_ceiling_val as CE.
    assert (R1 : bv_unsigned (wz pbeg) = pbeg) by (apply unsigned_lit; kung_all; lia).
    assert (R2 : bv_unsigned (wz (pend - pbeg)) = pend - pbeg) by (apply unsigned_lit; kung_all; lia).
    replace H1 with ([(h, h + msz); e1] ++ e2 :: REST) by reflexivity.
    replace L1 with ([e1] ++ e2 :: LREST) by reflexivity.
    apply (MInv_madvise_remove [(h, h + msz); e1] [emid] (e2 :: REST) [e1] (e2 :: LREST) E (wz pbeg) (wz (pend - pbeg)) mdx).
    - exact HI.
    - rewrite R1. exact M2.
    - intros l hh Hin. destruct Hin as [EQ|[]]. unfold AFreeX2.emid in EQ. injection EQ as <- <-. rewrite R1, R2. lia.
    - (* [comment removed for export] *)
      intros lo hi Hin _. cbn [app In] in Hin. destruct Hin as [EQ|[EQ|[EQ|Hin]]].
      + injection EQ as <- <-. right. exact LZC.
      + left. apply iv_sub_In. rewrite <- EQ. cbn [app In]. left. reflexivity.
      + left. apply iv_sub_In. rewrite <- EQ. cbn [app In]. right. left. reflexivity.
      + destruct (CR lo hi Hin) as [S|F]; [left| right; exact F]. change ([e1] ++ e2 :: LREST) with ([e1; e2] ++ LREST). apply iv_sub_app_r. exact S.
  Qed.

  (* [comment removed for export] *)
  #[using="GEO G"] Lemma kMInv_H2 : forall E mdx, MInv H1 L1 E mdx -> map_has (vm_maps (m_vmmaps mdx)) (wz h) (wz msz) = true -> eager_map (wz h) (wz msz) mdx ->
    MInv H2 L1 (E - msz) (munmap_modelL (wz h) (wz msz) mdx).   (* [comment removed for export] *)
  Proof.
    intros E mdx HI HAS EM. pose proof GEO as (HLO & HAL & MSZ & MSZAL & HHI & PH & PIN & N6 & NR & H5 & PM). pose proof alloc_ceiling_val as CE.
    assert (R1 : bv_unsigned (wz h) = h) by (apply unsigned_lit; lia). assert (R2 : bv_unsigned (wz msz) = msz) by (apply unsigned_lit; lia).
    pose proof (MInv_munmap_refund H1 L1 E (wz h) (wz msz) mdx HI HAS EM) as HI'. rewrite R2 in HI'.
    change H2 with ([] ++ e1 :: e2 :: REST). exact (MInv_hull_remove_all [] [(h, h + msz)] (e1 :: e2 :: REST) L1 (E - msz) _ HI').
  Qed.

  (* [comment removed for export] *)
  #[using="NTH GEO G"] Lemma klhull_permF : forall kb es more, Permutation L1 (pa_lhull (recsA A kb i es more dead2)).
  Proof.
    intros kb es more. unfold AFreeX2.L1, AFreeX2.LREST, AFreeX2.dead2, pa_lhull, alhull_of, alhull_of_, alregions_.
    cbn [recsA a_pl a_reg a_sec a_deadsh sec_remove sr_chunks]. change (p_sb (a_pl A)) with sb.
    assert (PR : Permutation (swap_remove chunks i (CS 0 0)) (firstn i chunks ++ skipn (S i) chunks)).
    { apply (Permutation_cons_inv (a := CS h n0)). apply (Permutation_trans (swap_remove_perm chunks i (CS h n0) (CS 0 0) NTH)).
      (first [ pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_7; dex2 dR_7 as l1 l2; destruct dR_7 as [E LEN] | pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_7; dand4 dR_7 as l1 l2 E LEN | destruct (@nth_error_split _ chunks i _ NTH) as (l1 & l2 & E & LEN) ]).
      assert (F1 : firstn i chunks = l1) by (rewrite E, <- LEN; rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r; reflexivity).
      assert (F2 : skipn (S i) chunks = l2).
      { rewrite E, <- LEN. rewrite skipn_app. replace (S (length l1) - length l1)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity. }
      rewrite F1, F2. rewrite E at 1. apply Permutation_sym. apply Permutation_middle. }
    set (CH' := swap_remove chunks i (CS 0 0)) in *. set (CH := firstn i chunks ++ skipn (S i) chunks) in *.
    set (X := lfixed_regions_ AL_pasan P). set (Y := lclasses_regions_ sb (a_reg A) 31). set (DD := a_deadsh A). set (EX := p_extra P).
    rewrite !hull_of_app.
    apply (Permutation_trans (l' := [e1; e2] ++ (hull_of X ++ hull_of Y ++ hull_of (lsec_regions_ CH')) ++ DD ++ EX)).
    - cbn [app]. apply perm_skip. apply perm_skip. apply Permutation_app_tail. apply Permutation_app_head. apply Permutation_app_head.
      apply hull_of_perm. apply lsec_regions_perm. apply Permutation_sym. exact PR.
    - rewrite <- (app_assoc DD [e1; e2] EX).
      apply (Permutation_trans (l' := ((hull_of X ++ hull_of Y ++ hull_of (lsec_regions_ CH')) ++ DD) ++ [e1; e2] ++ EX)).
      + replace ([e1; e2] ++ (hull_of X ++ hull_of Y ++ hull_of (lsec_regions_ CH')) ++ DD ++ EX)
          with ([e1; e2] ++ ((hull_of X ++ hull_of Y ++ hull_of (lsec_regions_ CH')) ++ DD) ++ EX) by (rewrite <- !app_assoc; reflexivity).
        apply Permutation_app_swap_app.
      + rewrite <- !app_assoc. apply Permutation_refl.
  Qed.
  (* [comment removed for export] *)
  #[using="NTH GEO G"] Lemma khull_permF : forall kb es more, Permutation H2 (pa_hull (recsA A kb i es more dead2)).
  Proof.
    intros kb es more. unfold AFreeX2.H2, AFreeX2.REST, AFreeX2.dead2, pa_hull, ahull_of, ahull_of_, aregions_.
    cbn [recsA a_pl a_reg a_sec a_deadsh sec_remove sr_chunks]. change (p_sb (a_pl A)) with sb.
    (* [comment removed for export] *)
    assert (PR : Permutation (swap_remove chunks i (CS 0 0)) (firstn i chunks ++ skipn (S i) chunks)).
    { apply (Permutation_cons_inv (a := CS h n0)). apply (Permutation_trans (swap_remove_perm chunks i (CS h n0) (CS 0 0) NTH)).
      (first [ pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_7; dex2 dR_7 as l1 l2; destruct dR_7 as [E LEN] | pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_7; dand4 dR_7 as l1 l2 E LEN | destruct (@nth_error_split _ chunks i _ NTH) as (l1 & l2 & E & LEN) ]).
      assert (F1 : firstn i chunks = l1) by (rewrite E, <- LEN; rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r; reflexivity).
      assert (F2 : skipn (S i) chunks = l2).
      { rewrite E, <- LEN. rewrite skipn_app. replace (S (length l1) - length l1)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity. }
      rewrite F1, F2. rewrite E at 1. apply Permutation_sym. apply Permutation_middle. }
    set (CH' := swap_remove chunks i (CS 0 0)) in *. set (CH := firstn i chunks ++ skipn (S i) chunks) in *.
    set (X := fixed_regions_ AL_pasan P). set (Y := classes_regions_ sb (a_reg A) 31). set (D := a_deadsh A). set (EX := p_extra P).
    rewrite !hull_of_app.
    apply (Permutation_trans (l' := [e1; e2] ++ pa_image_ivs ++ (hull_of X ++ hull_of Y ++ hull_of (sec_regions_ CH')) ++ D ++ EX)).
    - cbn [app]. apply perm_skip. apply perm_skip. apply Permutation_app_head. apply Permutation_app_tail. apply Permutation_app_head. apply Permutation_app_head.
      apply hull_of_perm. apply sec_regions_perm. apply Permutation_sym. exact PR.
    - (* [comment removed for export] *)
      rewrite <- (app_assoc D [e1; e2] EX).
      apply (Permutation_trans (l' := (pa_image_ivs ++ (hull_of X ++ hull_of Y ++ hull_of (sec_regions_ CH')) ++ D) ++ [e1; e2] ++ EX)).
      + replace ([e1; e2] ++ pa_image_ivs ++ (hull_of X ++ hull_of Y ++ hull_of (sec_regions_ CH')) ++ D ++ EX)
          with ([e1; e2] ++ (pa_image_ivs ++ (hull_of X ++ hull_of Y ++ hull_of (sec_regions_ CH')) ++ D) ++ EX) by (rewrite <- !app_assoc; reflexivity).
        apply Permutation_app_swap_app.
      + rewrite <- !app_assoc. apply Permutation_refl.
  Qed.

  (* [comment removed for export] *)
  #[using="SHR GEO G Clg"] Lemma kdead2_ok :
    Forall (fun lh => ((kHighShadowMapBeg <= fst lh /\ snd lh <= kHighMemBeg) \/ (kLowShadowBeg <= fst lh /\ snd lh <= kShadowGapBeg))
                      /\ fst lh <= snd lh <= fst lh + kDeadShadowBytes /\ fst lh mod 8 = 0 /\ snd lh mod 8 = 0) dead2 /\
    (length dead2 <= 2)%nat /\ hull_bytes dead2 <= kDeadShadowBytes.
  Proof.
    (first [ pose proof (ka8_geo) as dR_8; dand15 dR_8 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 SHA BIG SIDE | pose proof ka8_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & SHA & BIG & SIDE) ]).
    pose proof SHR as (_ & M512 & D512 & SIDE').
    assert (A1 : sh h mod 8 = 0) by (apply (mod0_down _ 512 8); [exists 64; reflexivity| exact M512]).
    assert (A2 : pbeg mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact M2]).
    assert (A3 : pend mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact M3]).
    assert (A4 : (sh h + msz / 8) mod 8 = 0).
    { rewrite Z.add_mod by lia. rewrite A1, (mod0_down _ 512 8 ltac:(exists 64; reflexivity) D512). reflexivity. }
    unfold AFreeX2.dead2, AFreeX2.e1, AFreeX2.e2, kDeadShadowBytes. split; [| split; [cbn; lia|]].
    - constructor; [| constructor; [| constructor]]; cbn [fst snd];
        (split; [destruct SIDE' as [(X1 & X2 & X3)|(X1 & X2 & X3)]; [left| right]; unfold kLowShadowBeg in *; lia| split; [lia| split; assumption]]).
    - rewrite !hull_bytes_cons. cbn [hull_bytes]. unfold hull_npages, page_size. cbn [fst snd].
      pose proof (Z_div_mod_eq_full (pg_dn (sh h)) 4096) as Q1. rewrite M1, Z.add_0_r in Q1.
      pose proof (Z_div_mod_eq_full pbeg 4096) as Q2. rewrite M2, Z.add_0_r in Q2.
      pose proof (Z_div_mod_eq_full pend 4096) as Q3. rewrite M3, Z.add_0_r in Q3.
      pose proof (Z_div_mod_eq_full (pg_up (sh h + msz / 8)) 4096) as Q4. rewrite M4, Z.add_0_r in Q4.
      set (x := sh h + msz / 8) in *. set (u := pg_up x) in *. set (dn := pg_dn (sh h)) in *.
      assert (E0 : (x - 1) / 4096 = u / 4096 - 1) by (clear - G6 G8 Q4; lia).
      assert (E1 : sh h / 4096 = dn / 4096) by (clear - G1 G3 Q1; lia).
      assert (E2 : (pbeg - 1) / 4096 = pbeg / 4096 - 1) by (clear - Q2; lia).
      rewrite E0, E1, E2.
      set (qa := dn / 4096) in *. set (qb := pbeg / 4096) in *. set (qc := pend / 4096) in *. set (qd := u / 4096) in *.
      clearbody qa qb qc qd. clear - G1 G2 G3 G5 G6 G7 G8 Q1 Q2 Q3 Q4. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma koff_segments_H : forall X, Permutation X H0s \/ Permutation X H1 \/ Permutation X H2 \/ Permutation X H0p -> H_off_segments rsegs (hidc X).
  Proof.
    intros X PX.
    assert (GEN : forall front, H_off_segments rsegs (hidc (front ++ REST))).
    { intros front. unfold AFreeX2.REST. apply (H_off_segments_perm rsegs (pa_image_ivs ++ (front ++ hull_of (fixed_regions_ AL_pasan P ++ classes_regions_ sb (a_reg A) 31 ++ sec_regions_ (firstn i chunks ++ skipn (S i) chunks)) ++ a_deadsh A ++ p_extra P))).
      - rewrite (app_assoc pa_image_ivs front). rewrite (app_assoc front pa_image_ivs) || idtac.
        apply (Permutation_trans (l' := (front ++ pa_image_ivs) ++ hull_of (fixed_regions_ AL_pasan P ++ classes_regions_ sb (a_reg A) 31 ++ sec_regions_ (firstn i chunks ++ skipn (S i) chunks)) ++ a_deadsh A ++ p_extra P)).
        + rewrite <- !app_assoc. rewrite (app_assoc pa_image_ivs front), (app_assoc front pa_image_ivs). apply Permutation_app_tail. apply Permutation_app_comm.
        + rewrite <- !app_assoc. apply Permutation_refl.
      - apply pa_hull_off_segments. }
    destruct PX as [PX|[PX|[PX|PX]]]; apply (H_off_segments_perm rsegs _ X (Permutation_sym PX));
      [exact (GEN [(h, h + msz); e1; emid; e2])| exact (GEN [(h, h + msz); e1; e2])| exact (GEN [e1; e2])| exact (GEN [(h, h + msz); (sh h, sh h + msz / 8)])].
  Qed.

  (* [comment removed for export] *)
  #[using="NTH GEO G"] Lemma khidc_H0p : hidc (pa_hull A) = hidc H0p.
  Proof. apply hidc_perm. exact khull_perm0. Qed.
  #[using="NTH GEO G"] Lemma khidc_H2 : forall kb es more, hidc (pa_hull (recsA A kb i es more dead2)) = hidc H2.
  Proof. intros kb es more. symmetry. apply hidc_perm. apply khull_permF. Qed.

  (* [comment removed for export] *)
  #[using="SHR GEO G"] Lemma kvis_H1 : forall x, in_hullb H0p x = true -> ~ (pbeg <= x < pend) -> in_hullb H1 x = true.
  Proof.
    intros x Hx NM. (first [ pose proof (ka8_geo) as dR_9; dand7 dR_9 as G1 G2 G3 G4 G5 G6 _ | pose proof ka8_geo as (G1 & G2 & G3 & G4 & G5 & G6 & _) ]). unfold AFreeX2.H0p, AFreeX2.H1 in *. cbn [in_hullb existsb] in Hx |- *.
    set (RR := existsb (in_ivb x) REST) in *. clearbody RR. unfold AFreeX2.e1, AFreeX2.e2, in_ivb in *. cbn [fst snd] in *.
    destruct RR; [rewrite !Bool.orb_true_r; reflexivity|]. rewrite !Bool.orb_false_r in Hx |- *.
    rewrite !Bool.orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt in Hx |- *. clear - Hx NM G1 G2 G3 G4 G5 G6. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="SHR GEO G"] Lemma kvis_H1_H0p : forall x, in_hullb H1 x = true -> in_hullb H0p x = true.
  Proof.
    intros x Hx. (first [ pose proof (ka8_geo) as dR_10; dand7 dR_10 as G1 G2 G3 G4 G5 G6 _ | pose proof ka8_geo as (G1 & G2 & G3 & G4 & G5 & G6 & _) ]). unfold AFreeX2.H0p, AFreeX2.H1 in *. cbn [in_hullb existsb] in Hx |- *.
    set (RR := existsb (in_ivb x) REST) in *. clearbody RR. unfold AFreeX2.e1, AFreeX2.e2, in_ivb in *. cbn [fst snd] in *.
    destruct RR; [rewrite !Bool.orb_true_r; reflexivity|]. rewrite !Bool.orb_false_r in Hx |- *.
    rewrite !Bool.orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt in Hx |- *. clear - Hx G1 G2 G3 G4 G5 G6. lia.
  Qed.
  Lemma kvis_H2_H1 : forall x, in_hullb H2 x = true -> in_hullb H1 x = true.
  Proof. intros x Hx. unfold AFreeX2.H1, AFreeX2.H2 in *. cbn [in_hullb existsb] in Hx |- *. rewrite Hx. apply Bool.orb_true_r. Qed.
End KHulls.

Section KLen.
Context {Clg : Ceiling}.
  Variables (p n0 : Z).
  Hypothesis G : kgeo p n0.
  #[warnings="-notation-for-abbreviation"] Local Notation h := (p - 6144).
  #[warnings="-notation-for-abbreviation"] Local Notation msz := (map_size n0).
  #[warnings="-notation-for-abbreviation"] Local Notation pbeg := (a8_pbeg (p - 6144)).
  #[warnings="-notation-for-abbreviation"] Local Notation pend := (a8_pend (p - 6144) (map_size n0)).
  #[warnings="-notation-for-abbreviation"] Local Notation len := (a8_pend (p - 6144) (map_size n0) - a8_pbeg (p - 6144)).

  #[using="G"] Lemma klen_facts0 : 0 < len /\ pbeg + len = pend /\ 0 < pbeg /\ pend <= kHighMemBeg /\ pbeg mod 4096 = 0 /\ len mod 4096 = 0 /\
                    bv_unsigned (wz pbeg) = pbeg /\ bv_unsigned (wz len) = len /\ bv_unsigned (wz h) = h /\ bv_unsigned (wz msz) = msz /\
                    0x60a000 <= h /\ h + msz <= alloc_ceiling /\ 0 < msz /\ h mod 4096 = 0 /\ msz mod 4096 = 0 /\
                    page_round_up_Z len = len /\ page_round_up_Z msz = msz.
  Proof.
    (first [ pose proof ((ka8_geo p n0 G)) as dR_11; dand15 dR_11 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 SHA BIG SIDE | pose proof (ka8_geo p n0 G) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & SHA & BIG & SIDE) ]).
    (first [ pose proof ((proj1 G)) as dR_12; dand11 dR_12 as HLO HAL MSZ MSZAL HHI _ _ _ _ H5 _ | pose proof (proj1 G) as (HLO & HAL & MSZ & MSZAL & HHI & _ & _ & _ & _ & H5 & _) ]). pose proof alloc_ceiling_val as CE.
    assert (LM : len mod 4096 = 0) by (rewrite <- Zminus_mod_idemp_l, M3, <- Zminus_mod_idemp_r, M2; reflexivity).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try (kung_all; lia); try (apply unsigned_lit; kung_all; lia); try assumption.
    - unfold page_round_up_Z, page_size. pose proof (Z_div_mod_eq_full len 4096) as Q. rewrite LM, Z.add_0_r in Q.
      set (q := len / 4096) in *. clearbody q. clear -Q. rewrite Q. replace (4096 * q + 4096 - 1) with (q * 4096 + 4095) by lia.
      rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
    - unfold page_round_up_Z, page_size. pose proof (Z_div_mod_eq_full msz 4096) as Q. rewrite MSZAL, Z.add_0_r in Q.
      set (q := msz / 4096) in *. clearbody q. clear -Q. rewrite Q. replace (4096 * q + 4096 - 1) with (q * 4096 + 4095) by lia.
      rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
  Qed.
End KLen.
