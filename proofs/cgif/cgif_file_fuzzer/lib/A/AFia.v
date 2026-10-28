(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0v YK00 YK13 YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YF06.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0f YG00 YG0a YG01 YG0n YG0s YG0h YG08 YG0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma free_from_entry : forall l (a : word) nZ (z : Z * Z),
region_free l a (Z_to_bv 64 nZ) = true -> In (wiv z) l ->
0 <= nZ < 2 ^ 64 -> 0 <= fst z < 2 ^ 64 -> 0 <= snd z < 2 ^ 64 ->
zdisjoint (bv_unsigned a, nZ) z.
Proof.
intros l a nZ [lo len] Hrf Hin HnZ Hlo Hlen. unfold wiv, YG0n.w64 in Hin. cbn [fst snd] in Hin, Hlo, Hlen.
pose proof (YK13.region_free_In l a (Z_to_bv 64 nZ) (Z_to_bv 64 lo) (Z_to_bv 64 len) Hrf Hin) as D.
rewrite !u64_lit in D by lia. unfold zdisjoint. cbn [fst snd]. lia.
Qed.
Lemma sec_extents_count_le : forall ly S, (length (sec_extents ly S) <= length (st_chunks S))%nat.
Proof.
intros ly S. unfold sec_extents. generalize (st_chunks S) as l. intros l.
induction l as [|k l IH]; cbn; [lia|]. rewrite length_app. destruct (ck_beg k); cbn; lia.
Qed.
Lemma sec_extents_count : forall B ly S rd, ARm B ly S rd -> Z.of_nat (length (sec_extents ly S)) <= YF06.SEC_LIVE_N.
Proof.
intros B ly S rd M. pose proof (am_wf _ _ _ _ M) as WF.
pose proof (YG09.nsec_le_arr _ 0 0 0 S WF) as H1. pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF)) as H2.
assert (E : Z.of_nat (length (sec_extents ly S)) = YG09.nsec_l (st_chunks S)).
{ unfold sec_extents, YG09.nsec_l. generalize (st_chunks S) as l. induction l as [|k l IH]; [reflexivity|]. cbn [flat_map fold_right]. rewrite length_app, Nat2Z.inj_add, IH. destruct (ck_beg k); cbn [length]; lia. }
unfold YF06.SEC_LIVE_N, kPtrArrayEntriesPerCommit in *. lia.
Qed.
Lemma sec_extents_sizes : forall B ly S rd, ARm B ly S rd -> Forall (fun e => 0 <= snd e <= YF06.NOB) (sec_extents ly S).
Proof.
intros B ly S rd M. pose proof (wf_chunks _ _ _ _ _ (am_wf _ _ _ _ M)) as CK. pose proof (sec_extents_len B ly S rd M) as SL.
apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) SL e He) as X. cbn beta in X.
unfold sec_extents in He. apply in_flat_map in He as (k & Hk & He).
pose proof (proj1 (Forall_forall _ _) CK k Hk) as [Hn _]. destruct (ck_beg k) as [|o|r o|c p]; try destruct He as [<-|[]]; try destruct He.
cbn [snd] in *. pose proof (YG08.sec_map_size_bound (ck_req k) ltac:(lia)) as SB. pose proof (req_size_bounds (ck_req k) ltac:(lia)) as RB.
unfold YF06.NOB, MALLOC_MAX in *. lia.
Qed.
Lemma sec_grant_exists_AR : forall B ly S rd md nZ,
ARm B ly S rd -> ALedger tfibsegs ly S md -> amwf md -> 0 < nZ <= YF06.NOB ->
exists a, grant_ok_na_pin md a nZ = true.
Proof.
intros B ly S rd md nZ M L [_ NZ] HnZ.
exact (sec_grant_exists tfibsegs ly S md nZ (am_layout _ _ _ _ M) L NZ (sec_extents_count B ly S rd M) (sec_extents_sizes B ly S rd M) HnZ).
Qed.
Section G.
Variable B : asyms.
Variables (ly : alayout) (S : astate) (rd : reader) (md : Model) (a : word) (nZ : Z).
Hypothesis M : ARm B ly S rd.
Hypothesis L : ALedger tfibsegs ly S md.
Hypothesis Hev : aregime S.
Hypothesis HnZ : 0 < nZ <= MALLOC_MAX + 4 * 4096.
Hypothesis HnZal : nZ mod 4096 = 0.
Hypothesis HG : grant_ok_na_pin md a nZ = true.
Let A : Z := bv_unsigned a.
Let LY : layout_ok ly := am_layout _ _ _ _ M.
Lemma nZ_word : bv_unsigned (Z_to_bv 64 nZ) = nZ.
Proof. apply u64_lit. unfold MALLOC_MAX in HnZ. lia. Qed.
Lemma grant_facts :
page_aligned A /\ in_app A nZ /\ A + nZ <= ASAN_CEIL /\
Forall (zdisjoint (A, nZ)) (static_extents ly ++ sec_extents ly S ++ perm_maps ly ++ band_maps).
Proof.
pose proof (am_wf _ _ _ _ M : WfP (as_universe B) 0 0 0 S) as W.
pose proof (anon_grant_facts tfibsegs (as_universe B) 0 0 0 ly S md a (Z_to_bv 64 nZ) LY W (am_placed _ _ _ _ M) L) as X.
rewrite nZ_word in X. exact (X HG (proj1 HnZ) HnZal).
Qed.
Lemma grant_parts :
A mod 4096 = 0 /\ 0 < A /\ A + nZ <= alloc_top (m_vmmaps md) /\
region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a (Z_to_bv 64 nZ) = true /\
A + nZ <= alloc_top (m_vmmaps md).
Proof.
clear LY. pose proof HG as Hg. unfold grant_ok_na_pin in Hg.
apply andb_prop in Hg as [Hg Hrf]. apply andb_prop in Hg as [Hg Htop]. apply andb_prop in Hg as [Hal Hpos].
apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
unfold page_size in Hal. unfold A. repeat split; assumption.
Qed.
Lemma grant_A_range : 0 <= A /\ A + nZ < 2 ^ 64.
Proof. pose proof grant_facts as (_ & _ & C & _). pose proof grant_parts as (_ & P & _). ceil; unfold ASAN_CEIL in C. lia. Qed.
Lemma grant_zone : zone3 A nZ.
Proof.
pose proof grant_facts as (_ & AP & _ & FA). rewrite !Forall_app in FA. destruct FA as (FS & _ & _ & _).
apply (zone3_intro ly A nZ (img_cover_of_ledger ly S md L) ltac:(lia) AP).
apply (proj1 (Forall_forall _ _) FS). unfold static_extents. apply in_or_app. right. cbn. tauto.
Qed.
Lemma grant_apart : Forall (zdisjoint (A, nZ)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S).
Proof.
pose proof grant_facts as (_ & _ & _ & FA). rewrite !Forall_app in FA. destruct FA as (FS & FSEC & FP & FB).
rewrite !Forall_app. split; [exact FS | split; [| exact FSEC]].
pose proof FP as FP'. unfold perm_maps in FP'. apply Forall_app in FP' as [FP6 FX].
apply Forall_cons_iff in FP6 as [PT FP6]. apply Forall_cons_iff in FP6 as [PF FP6]. apply Forall_cons_iff in FP6 as [PNB FP6].
apply Forall_cons_iff in FP6 as [PSB FP6]. apply Forall_cons_iff in FP6 as [PC FP6]. apply Forall_cons_iff in FP6 as [PD _].
assert (PQ : zdisjoint (A, nZ) (ly_Q ly, kPtrArrayResv)).
{ apply (proj1 (Forall_forall _ _) FS). unfold static_extents, owned_extents. cbn. tauto. }
assert (PP : zdisjoint (A, nZ) (ly_prim ly, kPrimResvSize)).
{ apply (proj1 (Forall_forall _ _) FS). unfold static_extents, owned_extents. cbn. tauto. }
assert (PI : zdisjoint (A, nZ) (ly_img ly)).
{ apply (proj1 (Forall_forall _ _) FS). unfold static_extents. apply in_or_app. right. cbn. tauto. }
pose proof (lo_space_in ly LY) as SPI.
unfold vis0_zones. apply Forall_app. split; [| exact FX].
repeat (apply Forall_cons; [first [assumption | unfold zdisjoint in *; cbn [fst snd] in *; unfold kRegionInfoOff, kPrimResvSize, kSpaceSize in *; lia] |]).
apply Forall_nil.
Qed.
Lemma grant_hfree : forall g, A <= g -> g + 8 <= A + nZ -> hfree ly S g.
Proof.
intros g G1 G2. unfold hfree. apply Forall_impl with (2 := grant_apart). intros z Hz. unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
Qed.
Lemma grant_shadow_zero : forall mem g, ahz ly S mem -> g mod 8 = 0 -> A <= g -> g + 8 <= A + nZ -> mem (Z_to_bv 64 (shadow_addr g)) = Some (Z_to_bv 8 0).
Proof.
intros mem g HZ Hg G1 G2. pose proof grant_facts as (_ & AP & Hce & _).
apply (HZ g Hg); [| exact (grant_hfree g G1 G2)].
ceil. unfold in_app, ASAN_CEIL in *. lia.
Qed.
End G.
Lemma tfib_region_free_reserved : forall lo len, 0 <= len -> lo + len < 2 ^ 64 ->
(4096 <= lo /\ lo + len <= TFIB_IMG_LO) \/ TFIB_IMG_END <= lo ->
region_free (segments_reserved tfibsegs) (w64 lo) (w64 len) = true.
Proof.
intros lo len Hlen Hhi Hz. apply YG0h.region_free_intro. intros e He.
assert (E : map (fun e => (YG0h.uw (fst e), YG0h.uw (snd e))) (segments_reserved tfibsegs)
= [(65536, 131072); (196608, 446464); (643072, 8192); (651264, 5619712)]) by (vm_compute; reflexivity).
apply (in_map (fun e => (YG0h.uw (fst e), YG0h.uw (snd e)))) in He. rewrite E in He.
unfold TFIB_IMG_LO, TFIB_IMG_END in Hz. unfold YG0h.uw, w64 in *. rewrite !u64_lit by lia.
cbn [In] in He. destruct He as [He|[He|[He|[He|[]]]]]; injection He as <- <-; lia.
Qed.
End b.
