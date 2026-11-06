(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMrecS.v (commit ce1a656b52b7, file sha256 4718e7ba654f) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrecS.v (commit 67fc7ef5787, lane B1 drain composition, DoRecycle chain; the chain's two function pairs, Quarantine::DoRecycle and LocalCache::Deallocate, re-checked EQUAL-mod-pcrel by cmpkit 4bbd3a74be89 strictcmp2 16982e3ef42b; file sha256 e33b074512f2) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (4 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1 of ReallocPrimary's Theorem Labs walk lanes, slice H2, a prior worker; interface
   DMwalkIF.v at 3e29c198d40): the FACTS DoRecycle's walk reads at a cut, over the opaque
   relations.  The released walk takes them from cgif's AR (YFhl.slot_facts / item_facts / sb_cell / slot_puser /
   slot_vs_chunk, from ARm and RIx); here they come from
   - the layout ([layout_ok ly], [img_cover ly]: requested of WalkB1 as dr_pre_r conjuncts, 00:4xZ), and
   - DMwalkIF.di_rview_x_t at RMAXD (the space-base word, the header range of every chunk still to recycle, the carved
     class-24 position of every batch object still to free, apart from those chunks, and the class-24 allocated bound).
   rule 24: proves function __sanitizer::Quarantine<__asan::QuarantineCallback, __asan::AsanChunk>::DoRecycle (cut
   facts; lane B1 reuse search the internal file LOOKUP-B1-drain.txt, B1LookupCheck CONFIRM). *)
(* Theorem Labs, 2026-10-30 (a prior worker): the image-B (asan-ubsan) twin of lib/A/DMrecS.v at 14a6b2561a69, relocated by a Theorem Labs lane alreloc a5c53bb2bed4ad03 (every moved numeral a DoRecycle / LocalCache::Deallocate pc, +0x58) with the A twins A<r> renamed to the B twins Y<r>; the comment blocks above keep the A file's text and its A pcs. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YP09 YN3v YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x YFl1 YFeq YFeu YFf2 YFh9 YFhd YFhf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMwalkIF.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The layout facts DoRecycle's seeds read (DMrec.RZ.LYB's body, from layout_ok and img_cover alone). *)
Lemma ly_facts : forall ly, layout_ok ly -> img_cover ly ->
kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ ly_prim ly <= ly_space ly /\
ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly) /\ ly_space ly mod 65536 = 0 /\
zone3 (ly_T ly) kThreadObjSize /\ ly_T ly + kThreadObjSize <= ASAN_CEIL /\ ly_T ly mod 4096 = 0.
Proof.
intros ly LY IMG.
pose proof (lo_high ly LY) as HI. unfold in_high in HI. cbn [fst snd] in HI.
pose proof (zone3_intro ly (ly_T ly) kThreadObjSize IMG ltac:(clear; unfold kThreadObjSize; lia) (Forall_nth_f _ _ 2 _ (lo_app ly LY) eq_refl) (pairwise_ij_f _ _ 2 6 _ _ (lo_disj ly LY) eq_refl eq_refl)) as ZT.
assert (ZT2 : ly_T ly + kThreadObjSize <= ASAN_CEIL) by (clear - ZT; unfold zone3 in ZT; lia).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in ly LY) as HSPC. pose proof (lo_space_al ly LY) as SAL.
pose proof (lo_T_al ly LY) as TAL. unfold page_aligned in TAL.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
unfold zdisjoint in PSTK. cbn [fst snd] in *.
repeat match goal with |- _ /\ _ => split end; first [exact ZT | exact TAL | exact ZT2 | clear ZT; lia].
Qed.

Section f.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.
Hypothesis TB : TfibSyms B.
Hypothesis HRM : DMwalkIF.rmaxd_ok RMAXD.
Hypothesis RV : DMwalkIF.di_rview_x_t B ARXr DRq RMAXD.
Variable ly : alayout.
Hypothesis HLY : layout_ok ly /\ img_cover ly.
Local Notation SB := (ly_space ly).
Local Notation hdra := (YFhd.hdra B ly).

Lemma inst_alloc : as_inst B = A_ALLOCATOR.
Proof. rewrite (ts_inst B TB). reflexivity. Qed.

(* the space-base word DoRecycle loads at 0x33e20 (YFhl.sb_cell's twin) *)
Lemma sb_cell_r : forall X W mem md its zs, ARXr (as_inst B) ly X W mem md -> DRq X its zs ->
val_mem tfibsegs (mrestrict (w_H W) mem) (A_ALLOCATOR + 32) 8 SB.
Proof.
intros X W mem md its zs HA HQ. pose proof (proj1 RV _ _ _ _ _ _ _ _ HA HQ) as (V & _). rewrite inst_alloc in V. exact V.
Qed.

(* the header of every chunk still to recycle (YFhl.item_facts' twin) *)
Lemma item_facts_r : forall X W mem md its zs k, ARXr (as_inst B) ly X W mem md -> DRq X its zs -> In k its ->
hdra k = ck_base B ly k + ck_rz k - kChunkHeaderSize /\ 4096 <= hdra k /\ hdra k + 16 <= ASAN_CEIL /\ hdra k mod 16 = 0 /\ 0 <= hdra k < 2 ^ 64.
Proof.
intros X W mem md its zs k HA HQ Hk. pose proof (proj1 RV _ _ _ _ _ _ _ _ HA HQ) as (_ & HI & _).
destruct (HI k Hk) as (E & H1 & H2 & H3). unfold YFhd.hdra. rewrite E.
ceil. unfold ASAN_CEIL in *. repeat split; lia.
Qed.

(* the carved class-24 position of every batch object still to free (YFhl.slot_facts' twin, the class bound at RMAXD) *)
Lemma slot_facts_r : forall X W mem md its zs z, ARXr (as_inst B) ly X W mem md -> DRq X its zs -> In z zs ->
kHighMemBeg <= SB + z /\ SB + z + kBatchBytes <= ASAN_CEIL /\ (SB + z) mod 8192 = 0 /\
ly_prim ly <= SB + z /\ SB + z + kBatchBytes <= ly_prim ly + kPrimResvSize /\
SB + region_off kBatchClass <= SB + z /\ SB + z + kBatchBytes <= SB + region_off kBatchClass + RMAXD /\ 0 <= SB + z < 2 ^ 64 /\
(forall a, bslot ly z a -> ~ (ly_stk_lo ly <= a < ly_stk_hi ly)).
Proof.
intros X W mem md its zs z HA HQ Hz. pose proof (proj1 RV _ _ _ _ _ _ _ _ HA HQ) as (_ & _ & HZ).
pose proof (proj2 RV _ _ _ _ _ _ _ _ HA HQ) as HU.
destruct (HZ z Hz) as (Z1 & Z2 & Z3 & _).
destruct HLY as [LY IMG]. pose proof (ly_facts ly LY IMG) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & _).
destruct HRM as [R1 R2]. unfold kFreeArrayOffset in R2.
rewrite region_off_24 in *. unfold kBatchBytes, kSpaceSize, kPrimResvSize, kHighMemBeg in *.
assert (ZM : (SB + z) mod 8192 = 0).
{ replace (SB + z) with (SB + 24 * 2 ^ 32 + (z - 24 * 2 ^ 32)) by lia.
  rewrite Z.add_mod, Z3 by lia. rewrite Z.add_0_r, Z.mod_mod by lia.
  replace (SB + 24 * 2 ^ 32) with (8 * (SB / 65536) * 8192 + 24 * 2 ^ 32 + SB mod 65536 * 1) by (pose proof (Z.div_mod SB 65536 ltac:(lia)); lia).
  rewrite L8. rewrite Z.mul_1_r, Z.add_0_r. rewrite Z.add_mod by lia. rewrite Z.mod_mul by lia. reflexivity. }
ceil. unfold ASAN_CEIL in *.
repeat split; try lia.
intros a Ha Hs. unfold bslot, kBatchBytes in Ha. lia.
Qed.

(* a batch object still to free is in the user part of the primary (YFhl.slot_puser's twin) *)
Lemma slot_puser_r : forall X W mem md its zs z, ARXr (as_inst B) ly X W mem md -> DRq X its zs -> In z zs ->
forall a, bslot ly z a -> YFeuC.puser ly X a.
Proof.
intros X W mem md its zs z HA HQ Hz a Ha. pose proof (proj1 RV _ _ _ _ _ _ _ _ HA HQ) as (_ & _ & HZ).
destruct (HZ z Hz) as (Z1 & Z2 & _). exists kBatchClass. split; [unfold kBatchClass; lia|].
unfold region_base. unfold bslot, kBatchBytes in *. lia.
Qed.

(* a batch object still to free is apart from every chunk still to recycle (YFhl.slot_vs_chunk's twin) *)
Lemma slot_vs_chunk_r : forall X W mem md its zs z k, ARXr (as_inst B) ly X W mem md -> DRq X its zs -> In z zs -> In k its ->
forall a, bslot ly z a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k).
Proof.
intros X W mem md its zs z k HA HQ Hz Hk a Ha. pose proof (proj1 RV _ _ _ _ _ _ _ _ HA HQ) as (_ & _ & HZ).
destruct (HZ z Hz) as (_ & _ & _ & HN). apply (HN k a Hk). unfold bslot in Ha. exact Ha.
Qed.
End f.
End d.
