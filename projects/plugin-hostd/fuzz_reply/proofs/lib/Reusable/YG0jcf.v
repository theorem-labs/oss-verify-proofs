(* CARRIED from a working branch 9c1523337150ca248f14193526c53e4227497136,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YG0jcf.v, sha256 a7fa58f98f9f1d373118f32fc13c05cd295612d9b9e84cb5ed9419a8034d4b62.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the cf twin of cgif's ledger lemma YG0j.v anon_grant_facts, over WfP_cf / ALedger_cf, for
   the event-free allocator instance (generic: no image, no unit numeral). Text taken by path from a Theorem Labs lane's
   working branch 2093a8411df, proofs/plugin-hostd/fuzz_reply/lib/A/AFiacf.v:83-159 (XcfFinish), module
   paths fuzz_reply -> fuzz_preset; no other change. The proof is YG0j.v:299-367 with three changes: ALedger_cf's
   fields, the secondary sizes from YG08cf.sec_extents_sizes64P_cf, and the hole case (a cf class may carry ONE hole,
   the zero-length sentinel (EXH_HOLE, 0) (YG01cf.v:52-54), which covers no address). The zify flag is set LOCALLY
   here, so it does not leak into importers. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0v YK00 YK13 YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG00 YG0a YG01 YG0n YG0s YG0h YG08 YG0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG01cf YG08cf YG0ncf YG0scf YGcfNames YGcfPlace.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.

Lemma anon_grant_facts_cf : forall segs U pp cc bb ly S md (a n : word),
layout_ok ly -> WfP_cf U pp cc bb S -> sec_placed ly S -> ALedger_cf segs ly S md ->
grant_ok_na_pin md a (bv_unsigned n) = true -> 0 < bv_unsigned n -> bv_unsigned n mod 4096 = 0 ->
page_aligned (bv_unsigned a) /\ in_app (bv_unsigned a) (bv_unsigned n) /\ bv_unsigned a + bv_unsigned n <= ASAN_CEIL /\
Forall (zdisjoint (bv_unsigned a, bv_unsigned n)) (static_extents ly ++ sec_extents ly S ++ perm_maps ly ++ band_maps).
Proof.
intros segs U pp cc bb ly S md a n LO W PL L G Hn Hnal.
pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn. unfold bv_modulus in Ra, Rn.
unfold grant_ok_na_pin in G. apply andb_prop in G as [G G4]. apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2].
apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. unfold page_size in G1.
assert (Hn64 : Z_to_bv 64 (bv_unsigned n) = n) by (apply w64_uw). rewrite Hn64 in G4.
set (lo := bv_unsigned a) in *. set (len := bv_unsigned n) in *.
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
assert (CE : lo + len <= ASAN_CEIL).
{ unfold ASAN_CEIL. apply (YM05.grant_below_ceil (alloc_top (m_vmmaps md)) (lo + len) L13); [| exact G3].
apply Z.mod_divide in G1 as [q Hq]; [|lia]. apply Z.mod_divide in Hnal as [q' Hq']; [|lia]. rewrite Hq, Hq'.
replace (q * 4096 + q' * 4096) with ((q + q') * 4096) by lia. apply Z_mod_mult. }
ceil.
assert (RF : forall z, 0 <= fst z -> 0 <= snd z -> fst z + snd z < 2 ^ 64 ->
In (wiv z) (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) -> zdisjoint (lo, len) z).
{ intros z Z1 Z2 Z3 Hin. pose proof (YK13.region_free_In _ a n (w64 (fst z)) (w64 (snd z)) G4 Hin) as D.
unfold w64 in D. rewrite !Z_to_bv_unsigned, !bv_wrap_small in D by (unfold bv_modulus; lia). unfold zdisjoint. cbn [fst snd]. subst lo len. lia. }
assert (RFm : forall z, 0 <= fst z -> 0 <= snd z -> fst z + snd z < 2 ^ 64 -> In (wiv z) (vm_maps (m_vmmaps md)) -> zdisjoint (lo, len) z).
{ intros z Z1 Z2 Z3 Hin. apply RF; [exact Z1 | exact Z2 | exact Z3 | apply in_app_iff; right; exact Hin]. }
assert (BAND : Forall (zdisjoint (lo, len)) band_maps).
{ apply Forall_forall. intros z Hz. apply RFm; [ | | | exact (L11 z Hz)]; unfold band_maps in Hz; cbn in Hz;
destruct Hz as [<-|[<-|[<-|[]]]]; cbn [fst snd]; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; lia. }
assert (APP : in_app lo len).
{ pose proof BAND as B'. unfold band_maps in B'. apply Forall_cons_iff in B' as [D1 B']. apply Forall_cons_iff in B' as [D2 B']. apply Forall_cons_iff in B' as [D3 _].
unfold zdisjoint in D1, D2, D3. cbn [fst snd] in D1, D2, D3. unfold in_app.
unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *.
split; [| clear - D1 D2 D3 Hn CE CR0; lia].
apply Z.mod_divide in G1 as [q Hq]; [|lia]. subst lo len. clear - Hq G2. lia. }
split; [exact G1|]. split; [exact APP|]. split; [exact CE|].
pose proof (lo_high ly LO) as [HP1 HP2].
assert (PRIM : zdisjoint (lo, len) (ly_prim ly, kPrimResvSize)).
{ destruct L4 as (pieces & (P1 & P2 & P3) & P4).
unfold zdisjoint. cbn [fst snd].
destruct (Z_lt_le_dec lo (ly_prim ly + kPrimResvSize)) as [X1|X1]; [|right; lia].
destruct (Z_lt_le_dec (ly_prim ly) (lo + len)) as [X2|X2]; [|left; lia]. exfalso.
set (x := Z.max lo (ly_prim ly)).
assert (Hx : ly_prim ly <= x < ly_prim ly + kPrimResvSize) by (subst x; unfold kPrimResvSize in *; lia).
assert (NH : ~ prim_hole_at ly S x).
{ intros (c0 & h & Hc0 & Hh & Hz). pose proof (proj1 (wrc_holes _ _ _ _ _ _ (wfc_classes _ _ _ _ _ W c0 Hc0))) as HH.
rewrite Forall_forall in HH. rewrite (HH h Hh) in Hz. unfold in_zr in Hz. cbn [fst snd] in Hz. lia. }
apply (P3 x Hx) in NH. apply Exists_exists in NH as (p0 & Hp0 & Hin0). unfold in_zr in Hin0.
pose proof (proj1 (P4 p0) Hp0) as (Hm0 & C1 & C2 & C3).
pose proof (RFm p0 ltac:(unfold kHighMemBeg in HP1; lia) ltac:(lia) ltac:(clear - C2 C3 HP1 HP2 CR CR0; unfold kPrimResvSize, kHighMemBeg, ASAN_CEIL in *; lia) Hm0) as D.
unfold zdisjoint in D. cbn [fst snd] in D. subst x. lia. }
pose proof (lo_stk_ceil ly LO) as STK.
assert (IMG : zdisjoint (lo, len) (ly_img ly)).
{ pose proof (lo_img ly LO) as (J0 & J1 & J2 & J3). unfold zdisjoint. cbn [fst snd].
destruct (Z_lt_le_dec lo (fst (ly_img ly) + snd (ly_img ly))) as [X1|X1]; [|right; lia].
destruct (Z_lt_le_dec (fst (ly_img ly)) (lo + len)) as [X2|X2]; [|left; lia]. exfalso.
set (x := Z.max lo (fst (ly_img ly))).
destruct (L14 x ltac:(unfold in_zr; subst x; lia)) as (e & He & E1).
pose proof (YK13.region_free_In _ a n (fst e) (snd e) G4 ltac:(apply in_app_iff; left; rewrite L3, <- surjective_pairing; exact He)) as D.
subst lo len x. lia. }
assert (PERM : Forall (zdisjoint (lo, len)) (perm_maps ly)).
{ apply Forall_forall. intros z Hz. pose proof (perm_facts ly 1 LO ltac:(lia) z Hz) as (Z1 & Z2 & Z3 & _). apply RFm; [lia | lia | lia | exact (L10 z Hz)]. }
assert (QQ : zdisjoint (lo, len) (ly_Q ly, kPtrArrayResv)).
{ pose proof (proj1 (Forall_forall _ _) (lo_app ly LO) (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as [Q1 Q2]. cbn [fst snd] in Q1, Q2.
apply RFm; [cbn [fst]; lia | cbn [snd]; unfold kPtrArrayResv; lia | cbn [fst snd]; unfold kLowShadowBeg, kPtrArrayResv, ASAN_CEIL in *; lia | exact L5]. }
assert (SEC : Forall (zdisjoint (lo, len)) (sec_extents ly S)).
{ apply Forall_forall. intros e He. destruct PL as [PF _]. pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & [E1 E2] & E3).
pose proof (proj1 (Forall_forall _ _) (sec_extents_sizes64P_cf U pp cc bb ly S W) e He) as E4. cbn beta in E4.
apply RFm; [lia | lia | unfold ASAN_CEIL in *; lia | exact (L7 e He)]. }
rewrite !Forall_app. split; [| split; [exact SEC | split; [exact PERM | exact BAND]]].
unfold static_extents, owned_extents. apply Forall_app. split.
- pose proof PERM as PM. unfold perm_maps in PM. apply Forall_app in PM as [PM _].
apply Forall_cons_iff in PM as [PT PM]. apply Forall_cons_iff in PM as [PFk PM]. apply Forall_cons_iff in PM as [PNB PM].
apply Forall_cons_iff in PM as [PSB PM]. apply Forall_cons_iff in PM as [PC PM]. apply Forall_cons_iff in PM as [PD _].
repeat apply Forall_cons; try apply Forall_nil; try assumption.
unfold zdisjoint in PC |- *. cbn [fst snd] in PC |- *. unfold kCtxMapSize in PC. lia.
- apply Forall_cons; [| apply Forall_cons; [exact IMG | apply Forall_nil]].
unfold zdisjoint. cbn [fst snd]. left. unfold ASAN_CEIL in *. lia.
Qed.

End b.
