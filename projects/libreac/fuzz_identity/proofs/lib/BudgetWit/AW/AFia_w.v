(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFia.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFia.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed sec_grant_exists_AR, HG, grant_parts). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0v YK00 YK13.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YF06_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0f YG00 YG0a YG01.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0s_w YG0h_w YG08_w YG0j_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma sec_extents_count : forall B ly S rd, ARm B ly S rd -> Z.of_nat (length (sec_extents ly S)) <= YF06_w.SEC_LIVE_N.
Proof.
intros B ly S rd M. pose proof (am_wf _ _ _ _ M) as WF.
pose proof (YG09.nsec_le_arr _ 0 0 0 S WF) as H1. pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF)) as H2.
assert (E : Z.of_nat (length (sec_extents ly S)) = YG09.nsec_l (st_chunks S)).
{ unfold sec_extents, YG09.nsec_l. generalize (st_chunks S) as l. induction l as [|k l IH]; [reflexivity|]. cbn [flat_map fold_right]. rewrite length_app, Nat2Z.inj_add, IH. destruct (ck_beg k); cbn [length]; lia. }
unfold YF06_w.SEC_LIVE_N, kPtrArrayEntriesPerCommit in *. lia.
Qed.
Lemma sec_extents_sizes : forall B ly S rd, ARm B ly S rd -> Forall (fun e => 0 <= snd e <= YF06_w.NOB) (sec_extents ly S).
Proof.
intros B ly S rd M. pose proof (wf_chunks _ _ _ _ _ (am_wf _ _ _ _ M)) as CK. pose proof (sec_extents_len B ly S rd M) as SL.
apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) SL e He) as X. cbn beta in X.
unfold sec_extents in He. apply in_flat_map in He as (k & Hk & He).
pose proof (proj1 (Forall_forall _ _) CK k Hk) as [Hn _]. destruct (ck_beg k) as [|o|r o|c p]; try destruct He as [<-|[]]; try destruct He.
cbn [snd] in *. pose proof (YG08_w.sec_map_size_bound (ck_req k) ltac:(lia)) as SB. pose proof (req_size_bounds (ck_req k) ltac:(lia)) as RB.
unfold YF06_w.NOB, MALLOC_MAX in *. lia.
Qed.
Lemma sec_grant_exists_AR : forall B ly S rd md nZ,
ARm B ly S rd -> ALedger tfibsegs ly S md -> amwf md -> 0 < nZ <= YF06_w.NOB -> nZ mod page_size = 0 ->
exists a, grant_ok_na_pin (Z_to_bv 64 0) md a nZ = true.
Proof.
intros B ly S rd md nZ M L [_ NZ] HnZ HnZal.
exact (sec_grant_exists tfibsegs ly S md nZ (am_layout _ _ _ _ M) L NZ (sec_extents_count B ly S rd M) (sec_extents_sizes B ly S rd M) HnZ HnZal).
Qed.
Section G.
Variable B : asyms.
Variables (ly : alayout) (S : astate) (rd : reader) (md : Model) (a : word) (nZ : Z).
Hypothesis M : ARm B ly S rd.
Hypothesis L : ALedger tfibsegs ly S md.
Hypothesis Hev : aregime S.
Hypothesis HnZ : 0 < nZ <= MALLOC_MAX + 4 * 4096.
Hypothesis HnZal : nZ mod 4096 = 0.
Hypothesis HG : grant_ok_na_pin (Z_to_bv 64 0) md a nZ = true.
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
clear LY. pose proof (YK13.grant_ok_na_pin_facts _ _ _ _ (proj1 HnZ) ltac:(unfold page_size; exact HnZal) HG) as Hg.
unfold YK13.grant_ok_na_pin_b in Hg.
apply andb_prop in Hg as [Hg Hrf]. apply andb_prop in Hg as [Hg Htop]. apply andb_prop in Hg as [Hal Hpos].
apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
unfold page_size in Hal. unfold A. repeat split; assumption.
Qed.
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
intros lo len Hlen Hhi Hz. apply YG0h_w.region_free_intro. intros e He.
assert (E : map (fun e => (YG0h_w.uw (fst e), YG0h_w.uw (snd e))) (segments_reserved tfibsegs)
(* Theorem Labs, 2026-10-29: the third entry's length 8192 -> 16384. DERIVED from identity's own program
   headers: its third PT_LOAD is vaddr 0x9ad50, memsz 0x32b0, so page-aligned the segment runs 0x9a000 ..
   0x9ad50+0x32b0 = 0x9e000, i.e. 630784 .. +0x4000 = **16384**; 8192 is cgif's. The other three entries
   already match identity's headers exactly (0x10000/0x20000, 0x30000/0x6a000, 0x9e000/0x55c000), which is why
   only this one was wrong. Closed by `vm_compute; reflexivity`, so it was false by computation.
   A check on B found the twin (YFia, third entry 8192 where B's PT_LOAD pages to 12288) and noted the
   port_core tag abfd17f8b3d2 is wrong there too - so this is a release defect, not skew. *)
= [(65536, 131072); (196608, 434176); (630784, 16384); (647168, 5619712)]) by (vm_compute; reflexivity).
apply (in_map (fun e => (YG0h_w.uw (fst e), YG0h_w.uw (snd e)))) in He. rewrite E in He.
unfold TFIB_IMG_LO, TFIB_IMG_END in Hz. unfold YG0h_w.uw, w64 in *. rewrite !u64_lit by lia.
cbn [In] in He. destruct He as [He|[He|[He|[He|[]]]]]; injection He as <- <-; lia.
Qed.
End b.
