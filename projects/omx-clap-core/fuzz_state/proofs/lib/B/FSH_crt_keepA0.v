(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YE05.v, with its module paths changed; 2671 of its 2756 lines of code are new or changed and 333 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segA.v, with its module paths and module names changed; 214 of its 310 lines of code are new or changed and 2660 lines of the source are left out. *)
(* rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from a working branch
   ff3fb23bb7b lib/A/FSH_crt_keepA0.v)
   Port source: a working branch ff3fb23bb7b proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_keepA0.v (381 lines,
   on S0 61e39a80fc9 + A base v32 a working branch 9ffe6bce6eb), itself PORTED from a working branch
   d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sdglue.v crt_keep_blk :612 / crt_spared_blk
   :659 (the donor's footprint lemmas; the checker's CONFIRM on that hit is a Theorem Labs lane, crt-lane-head.md). The
   function's rule-24 line: proves function check_round_trip - PORTED from a working branch d25a984c903
   proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip.v:11. The donor is a concrete-execution proof and is not
   importable; only the argument is ported.
   Same Lemma names and statements as the A file, over image B (lib/B/YB1v.v tfibsegs, fs.asan-ubsan), on the B interface
   lib/B/FSH_crt_base.v (crt_base, crt_frame_ok, crt_keepA, crt_l5_mem, crt_pstat_img, crt_F_ly; base v32 shape: crt_keepA
   carries `4096 <= crt_F cx /\ crt_F cx + 512 <= alloc_ceiling`, the below-0x10000-or-above-FS_IMG_END bounds of want and
   same, and `4096 <= c_want cx`), lib/B/FSH_crt_site.v (crt_F_facts, crt_raw_of_unp) and the B kit lib/B/FSW_K.v (fsw_ARU,
   fsw_sp), FSW_rd.v (fsw_ablock_low, fsw_ablock_off_img, fsw_ablock_off_shadow, fsw_block_body_addressable,
   fsw_head_ush_out) and FSW_frame.v (fsw_apresent_notowned); B's FS_IMG_END (lib/B/FSH_Base.v) is 0x5fd000, fs.asan-ubsan's
   last PT_LOAD ending at 0x5fcd10.

   check_round_trip (fs.asan-ubsan 0x81b9c; A: fs.asan 0x81a9c), build B: crt6_keepA, the exit facts of lane A0 of its ASan
   walk at B 0x81e18 (A 0x81d0c; the head of the expected_text encode loop): crt_keepA and, when the body is not empty,
   crt_l5_mem, from the facts lane A0 holds there (its last call, malloc same, returns at B 0x81db8; A 0x81cbc): the three
   new blocks on top of the entry's, U3, the journal from the entry, ARU, the frame, the text block and bytes, the input
   bytes, the statics, the n cell's granule and the four registers. No engine run: pure reasoning over the base's
   definitions. Copied with statements kept (prefix crt6_): a Theorem Labs lane's crtA_blk_keep, crtA_blk_sep, crtA_blk_new,
   crtA_addr_uniq, crtA_body_addressable_U, crtA_len, crtA_zs_bz and crtA_bb (a working branch 6eca7c1f51f
   lib/A/FSH_crt_segA.v, which the comments below cite at 636fafafadc with its line numbers); crtA_U_fresh / crtA_U_miss
   are restated over this lemma's premises as crt6_fresh / crt6_U_new.

   A name / fact -> A pc -> B pc (re-measured on (internal path); no name of this file
   carries a pc, so every name and statement is A's):
     A0's exit, encode loop head      A 0x81d0c `add a1, s5, a3`        -> B 0x81e18 `add a1, s5, a3` (an `equal` row)
     encode call / return             A jal 0x81c80, ret 0x81c84        -> B jal 0x81d7c, ret 0x81d80
     malloc want call / return        A jal 0x81ca4, ret 0x81ca8        -> B jal 0x81da0, ret 0x81da4
     strlen (t) call / return         A jal 0x81cb0, ret 0x81cb4        -> B jal 0x81dac, ret 0x81db0
     malloc same call / return        A jal 0x81cb8, ret 0x81cbc        -> B jal 0x81db4, ret 0x81db8
     n cell's granule unpoisoned      A 0x81cbc `sb zero, 0x38(s3)`     -> B 0x81db8 `sb zero, 0x38(s10)` (SF: A s3, B s10)
     n cell zeroed (F + 0x1c0)        A 0x81cc4 `sd zero, 0x1c0(s7)`    -> B 0x81dbc `sd zero, 0x1c0(s6)` (F: A s7, B s6)
   The four registers of the premise HR are A's on B too: x20 = s4 = |bs| (B 0x81be4 `mv s4, a2`), x21 = s5 = bd (B 0x81be8
   `mv s5, a1`), x24 = s8 = same (B 0x81dc8 `mv s8, a0` after malloc same), x25 = s9 = t (B 0x81c04 `mv s9, a0`); B's
   0x81dc8 .. 0x81e14 writes none of them (only s6 / s3 := want at 0x81e08 / 0x81e0c, a3 .. t6 and the s1 slots).
   B differences from A in the A0 window (none reaches a statement here): text's spill slot 0x18(s1) (B 0x81d80; A 0x30 at
   0x81c84), want in s7 then slot 0x30 (B 0x81da4 / 0x81dc0; A s10 then slot 0x38 at 0x81ca8 / 0x81cc8), En in s11 (B
   0x81d98; A s6), F in slot 0x10 (B 0x81dd4 `sd s6, 0x10(s1)`; A slot 0x28 at 0x81cc0 `sd s7, 0x28(s1)`) and on the loop
   path En and F in slots 0x28 / 0x38 (B 0x81ddc / 0x81de0; crt_cs1L), and loop-5's constants set up from B 0x81de4 (A
   0x81ce0).
   A new file: no licence lines (internal).

   SK is an EXPLICIT variable (lib/B/FSH_Fn_crt.v's check_round_trip_spec takes it): crt_F_facts needs it; build B's
   sink head FSH_Base.fsB_sink_head (lib/B/FSH_Base.v, ofl_head 0x5fbb28; a plain Definition) is passed by whoever
   applies crt6_keepA. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSH_crt_base FSH_crt_site.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSW_frame FSH_Fn_writer FSW_rd FSW_strkit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts HState.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a sink instance resolved
   in this file's scope; SK is passed explicitly instead *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section K. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.

(* ================= the block facts the exit reads =================
   The donor's two footprint lemmas, in the S0 form: what a block live at both ends of a run keeps (sdglue.v
   crt_keep_blk :612 - here the journal's block clause, crt6_blk_keep) and what a block the run made is spared by (sdglue.v
   crt_spared_blk :659 - here AR's block separation and the block law: crt6_blk_sep, crt6_blk_new, crt6_U_new). ---- *)

(* a Theorem Labs lane's crtA_blk_keep (a working branch 636fafafadc lib/A/FSH_crt_segA.v:842), statement kept: a byte of
   a block live at both ends of a journal keeps its value on the machine's memory (the journal's block clause; FS_PSTAT_FP
   holds image bytes only, and no block byte is one: YCbq.blk_img, crt_pstat_img) *)
Lemma crt6_blk_keep : forall ly S U (W : world tfibsegs) mem md ly' S' U' (W' : world tfibsegs) mem' md' k STK sp0 own
  p n i,
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  ajournal tfibsegs B STK sp0 FS_PSTAT_FP ly S W (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
  aview tfibsegs (w_H W') mem' (p + i) = aview tfibsegs (w_H W) mem (p + i).
Proof.
intros ly S U W mem md ly' S' U' W' mem' md' k STK sp0 own p n i HARU HARU' HJ Hin Hin' Hi.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4096 & Hceil & Happ & _).
cbv [in_app kLowShadowBeg kHighMemBeg] in Happ.
assert (Hnfp : ~ inFP FS_PSTAT_FP (p + i)).
{ intros HFP. exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md p n (p + i) HAR Hin ltac:(lia)
    (crt_pstat_img _ HFP)). }
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _).
apply (crt_raw_of_unp B ly S U W mem md ly' S' U' W' mem' md' (p + i) HARU HARU').
- pose proof (@alloc_ceiling_lt rc) as HC47.
  change (2 ^ 47) with 140737488355328 in HC47. change (2 ^ 64) with 18446744073709551616. lia.
- cbv [SHADOW_OFF kHighMemBeg]. lia.
- exact (K2 p n i Hin Hin' Hi Hnfp).
Qed.

(* a Theorem Labs lane's crtA_blk_sep (FSH_crt_segA.v:2508 at 636fafafadc), statement kept: two distinct live blocks are disjoint *)
Lemma crt6_blk_sep : forall ly S (W : world tfibsegs) mem md x y,
  AR tfibsegs B ly S W mem md -> In x (ablocks B ly S) -> In y (ablocks B ly S) -> x <> y ->
  zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md x y HAR Hx Hy Hne.
destruct (in_split _ _ Hx) as (l1 & l2 & E1). rewrite E1 in Hy.
apply in_app_or in Hy as [Hy | [Hy | Hy]]; [| exfalso; exact (Hne Hy) |].
- destruct (in_split _ _ Hy) as (m1 & m2 & E2). rewrite E2, <- app_assoc in E1. cbn [app] in E1.
  pose proof (sep_blocks_pos tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md y x m1 m2 l2 HAR E1) as D.
  unfold zdisjoint in D |- *. lia.
- destruct (in_split _ _ Hy) as (m1 & m2 & E2). rewrite E2 in E1.
  exact (sep_blocks_pos tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md x y l1 m1 m2 HAR E1).
Qed.
(* a Theorem Labs lane's crtA_blk_new (FSH_crt_segA.v:2522 at 636fafafadc), statement kept: a block that joins the list after the
   entry's is not one of the entry's (a block is never disjoint from itself) *)
Lemma crt6_blk_new : forall ly3 S3 (W3 : world tfibsegs) mem md ly S x l,
  AR tfibsegs B ly3 S3 W3 mem md -> ablocks B ly3 S3 = ablocks B ly S ++ l -> In x l -> 0 <= snd x ->
  ~ In x (ablocks B ly S).
Proof.
intros ly3 S3 W3 mem md ly S x l HAR E Hx Hs Hin.
destruct (in_split _ _ Hin) as (l1 & l2 & E1). destruct (in_split _ _ Hx) as (m1 & m2 & E2).
assert (EA : ablocks B ly3 S3 = l1 ++ x :: (l2 ++ m1) ++ x :: m2)
  by (rewrite E, E1, E2, <- !app_assoc; reflexivity).
pose proof (sep_blocks_pos tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 mem md x x l1 (l2 ++ m1) m2 HAR EA) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
destruct (req_size_pos (snd x) Hs) as (R1 & R2). lia.
Qed.
(* a Theorem Labs lane's crtA_addr_uniq (FSH_crt_segA.v:2535 at 636fafafadc), statement kept: two live blocks at one address are one
   block *)
Lemma crt6_addr_uniq : forall ly S (W : world tfibsegs) mem md p m m',
  AR tfibsegs B ly S W mem md -> In (p, m) (ablocks B ly S) -> In (p, m') (ablocks B ly S) -> m = m'.
Proof.
intros ly S W mem md p m m' HAR H1 H2.
destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) _ _ _ _ _ _ _ HAR H1) as (_ & _ & _ & _ & _ & _ & Hm).
destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) _ _ _ _ _ _ _ HAR H2) as (_ & _ & _ & _ & _ & _ & Hm').
destruct (Z.eq_dec m m') as [E|Hne]; [exact E|exfalso].
pose proof (crt6_blk_sep ly S W mem md (p, m) (p, m') HAR H1 H2 ltac:(injection 1; lia)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
pose proof (req_size_pos m ltac:(lia)) as (R1 & _). pose proof (req_size_pos m' ltac:(lia)) as (R2 & _). lia.
Qed.

(* a block that joined after the entry, and is disjoint from the block whose head the walk added to U, has no head in
   U3 = U0 ++ [(h, HEAD)]: the entry's heads are entry blocks' (fs_heads), and the added one is the other block's.
   a Theorem Labs lane's crtA_U_fresh (FSH_crt_segA.v:2566 at 636fafafadc), restated over U3's two parts with the separation in
   place of its size test. *)
Lemma crt6_fresh : forall ly0 S0 U0 ly3 S3 (W3 : world tfibsegs) mem md h hs p m,
  AR tfibsegs B ly3 S3 W3 mem md -> FSupoisonU.fs_heads B ly0 S0 U0 ->
  (forall b, In b (ablocks B ly0 S0) -> In b (ablocks B ly3 S3)) ->
  In (p, m) (ablocks B ly3 S3) -> ~ In (p, m) (ablocks B ly0 S0) ->
  In (h, hs) (ablocks B ly3 S3) -> zdisjoint (block_rng (h, hs)) (block_rng (p, m)) ->
  ~ In (p, 16) (U0 ++ [(h, HEAD)]).
Proof.
intros ly0 S0 U0 ly3 S3 W3 mem md h hs p m HAR FH Hsub Hin Hnew Hh D Hbad.
apply in_app_or in Hbad as [Hb | [Hb | []]].
- destruct (FH (p, 16) Hb) as (_ & m0 & Hin0 & _). cbn [fst] in Hin0.
  rewrite <- (crt6_addr_uniq ly3 S3 W3 mem md p m m0 HAR Hin (Hsub _ Hin0)) in Hin0. exact (Hnew Hin0).
- pose proof (f_equal fst Hb) as Eh. cbn [fst] in Eh. subst h.
  destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) _ _ _ _ _ _ _ HAR Hh) as (_ & _ & _ & _ & _ & _ & Hs).
  destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos hs (proj1 Hs)) as (R1 & _). pose proof (req_size_pos m (proj1 Hm)) as (R2 & _).
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.
(* a live block with no head in U meets no range of U: every range is a live block's 16-byte head (fs_heads), and two
   live blocks are disjoint (a Theorem Labs lane's crtA_U_miss, FSH_crt_segA.v:2550 at 636fafafadc, restated without its crtA_core) *)
Lemma crt6_U_new : forall ly3 S3 (W3 : world tfibsegs) mem md U3 p m,
  AR tfibsegs B ly3 S3 W3 mem md -> FSupoisonU.fs_heads B ly3 S3 U3 ->
  In (p, m) (ablocks B ly3 S3) -> ~ In (p, 16) U3 ->
  forall r, In r U3 -> p + req_size m <= fst r \/ fst r + snd r <= p.
Proof.
intros ly3 S3 W3 mem md U3 p m HAR FH Hin Hno (x, y) Hxy.
destruct (FH (x, y) Hxy) as (Hy & m' & Hin' & Hm'). cbn [fst snd] in Hy, Hin', Hm' |- *. subst y.
destruct (Z.eq_dec x p) as [->|Hne]; [exfalso; exact (Hno Hxy)|].
pose proof (crt6_blk_sep ly3 S3 W3 mem md (p, m) (x, m') HAR Hin Hin' ltac:(injection 1; lia)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

(* a Theorem Labs lane's crtA_body_addressable_U (FSH_crt_segA.v:2139 at 636fafafadc), statement kept: a block's bytes clear of
   every range of U are addressable on the machine's memory (FSW_rd.fsw_block_body_addressable with the head clause
   replaced by U-disjointness) *)
Lemma crt6_body_addressable_U : forall ly S U (W : world tfibsegs) mem md P n z len,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (P, n) (ablocks B ly S) -> P <= z -> 0 <= len -> z + len <= P + req_size n ->
  (forall r, In r U -> z + len <= fst r \/ fst r + snd r <= z) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF z len.
Proof.
intros ly S U W mem md P n z len HARU FH Hin Hz Hl Hn HUo.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof (YCbq.range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md P n z len HAR Hin ltac:(lia) Hn)
  as HRA.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md P n HAR Hin) as (HP16 & HP4096 & HPc & _).
pose proof asan_consts as (C1 & _).
intros x Hx. destruct (HRA x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
assert (NI : in_ush U (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))) = false).
{ rewrite wz by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  apply FSW_rd.fsw_head_ush_out; [lia|]. intros (h & q) Hr. cbn [fst snd].
  destruct (FH (h, q) Hr) as (E16 & m & Hm & M16). cbn [fst snd] in E16, Hm. subst q.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md h m HAR Hm) as (Hh16 & _).
  split; [reflexivity|].
  split; [apply Z.mod_divide in Hh16 as [k Hk]; [|lia]; rewrite Hk; replace (k * 16) with ((k * 2) * 8) by lia;
          apply Z_mod_mult|].
  destruct (HUo (h, 16) Hr) as [D|D]; cbn [fst snd] in D; lia. }
rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem _ NI). exact Es.
Qed.

(* a Theorem Labs lane's crtA_len (FSH_crt_segA.v:875 at 636fafafadc), statement kept: the decoded body's length, at most 3/4 of the
   text's (WriterSpecFacts.b64_dec_bound) *)
Lemma crt6_len : forall (tb : list byte) (bs : list Z),
  WriterSpec.b64_dec (HState.zs tb) = Some bs -> Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
  WriterSpec.bytes_ok bs /\ 0 <= Z.of_nat (length bs) <= 2359298 /\
  FSH_Fn_writer.enc_size (Z.of_nat (length bs)) + HEAD <= LIVE_check_round_trip.
Proof.
intros tb bs Hdec Htb. split; [exact (WriterSpecFacts.b64_dec_ok _ _ Hdec)|].
pose proof (WriterSpecFacts.b64_dec_bound _ _ Hdec) as Hb.
assert (Hzs : Z.of_nat (length (HState.zs tb)) = Z.of_nat (length tb)) by (unfold HState.zs; rewrite length_map; reflexivity).
rewrite Hzs in Hb. pose proof (Zle_0_nat (length bs)) as Hnn. pose proof (Zle_0_nat (length tb)) as Hnt.
assert (Hn : 0 <= Z.of_nat (length bs) <= 2359298) by (Z.div_mod_to_equations; lia).
split; [exact Hn|]. unfold FSH_Fn_writer.enc_size, LIVE_check_round_trip, HEAD. Z.div_mod_to_equations. lia.
Qed.
(* a Theorem Labs lane's crtA_zs_bz (FSH_crt_segA.v:952 at 636fafafadc), statement kept: crt_base states the body's bytes as
   `zs (bz bs)`, which is bs on bytes *)
Lemma crt6_zs_bz : forall l : list Z, WriterSpec.bytes_ok l -> HState.zs (HState.bz l) = l.
Proof.
intros l H. unfold HState.zs, HState.bz. rewrite map_map.
induction l as [|a l IH]; [reflexivity|].
pose proof (proj1 (Forall_cons_iff _ _ _) H) as (Ha & Hl). cbn [map]. rewrite (IH Hl).
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Ha.
Qed.
(* a Theorem Labs lane's crtA_bb (FSH_crt_segA.v:1863 at 636fafafadc), statement kept: blocks_bytes of a state, from its ablocks *)
Lemma crt6_bb : forall ly S ly' S' l,
  ablocks B ly' S' = ablocks B ly S ++ l -> blocks_bytes S' = blocks_bytes S + bsum l.
Proof.
intros ly S ly' S' l E. rewrite (blocks_bytes_bsum B ly' S'), (blocks_bytes_bsum B ly S), E, bsum_app. reflexivity.
Qed.

(* ================= crt6_keepA: A0's exit facts at B 0x81e18 (A 0x81d0c) =================
   The thirteen premises are lane A0's facts after malloc (same) returns at B 0x81db8 (the brief a0-keepA-brief.md,
   a Theorem Labs lane 08:5xZ): HB HAB HU HH HARU HJ HFO HRB HZX HZT HG HN HR, in that order. HR's registers are A's (header). *)
Lemma crt6_keepA : forall cx same ly3 S3 U3 (W3 : world tfibsegs) ms md,
  crt_base B cx ->
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++
    [(c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD);
     (c_want cx, (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1); (same, Z.of_nat (length (c_tb cx)) + 1)] ->
  U3 = c_U cx ++ [(c_text cx - HEAD, HEAD)] ->
  FSupoisonU.fs_heads B ly3 S3 U3 ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) md ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms)) md
    (EV_preset_base64_encode + 2 * CRT_EV_WRAP) ->
  crt_frame_ok cx S3 W3 ms ->
  fs_rblock tfibsegs B ly3 S3 W3 (ms_mem ms) (c_text cx) (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))) ->
  zbytes_at tfibsegs W3 (ms_mem ms) (c_text cx) (WriterSpec.b64_enc (c_bs cx) ++ [0]) ->
  zbytes_at tfibsegs W3 (ms_mem ms) (c_t cx) (HState.zs (c_tb cx ++ [Z_to_bv 8 0])) ->
  (exists peak, fs_glob tfibsegs W3 (ms_mem ms) (c_live cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))))
     peak (c_cnt cx + 1) SIZE_MAXZ) ->
  range_addressable (aview tfibsegs (w_H W3) (ms_mem ms)) SHADOW_OFF (crt_F cx + 0x1c0) 8 ->
  YK11.getr (ms_regs ms) 20%bv = w64 (Z.of_nat (length (c_bs cx))) /\ YK11.getr (ms_regs ms) 21%bv = w64 (c_bd cx) /\
  YK11.getr (ms_regs ms) 24%bv = w64 same /\ YK11.getr (ms_regs ms) 25%bv = w64 (c_t cx) ->
  crt_keepA B cx same (EV_preset_base64_encode + 2 * CRT_EV_WRAP) ly3 S3 U3 W3 ms /\
  (1 <= Z.of_nat (length (c_bs cx)) -> crt_l5_mem B cx ly3 S3 W3 (ms_mem ms)).
Proof.
intros cx same ly3 S3 U3 W3 ms md HB HAB HU HH HARU HJ HFO HRB HZX HZT HG HN HR.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly3 S3 U3 W3 (ms_mem ms) md HARU) as HAR.
pose proof HB as (HPRE & FH0 & _ & _ & _ & _ & _ & _ & _ & Htb & _ & (pt & kt & Hpt & Hpt1 & Hpt2) & Hdec & _ & Hzbd &
  (kb & Hrbd & Hkb) & _).
pose proof (fsw_ARU B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as HARU0.
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (_ & Hceil0 & _ & HSTK0).
destruct (crt6_len (c_tb cx) (c_bs cx) Hdec Htb) as (Hbok & Hlen & _).
destruct HFO as (Hfr & _ & _).
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 (ms_mem ms) md _ HJ HARU Hfr) as (_ & HF4096 & HFceil & _).
pose proof HJ as (_ & Hly & _).
pose proof (crt_F_ly cx _ ly3 Hly) as EF.
destruct HR as (R20 & R21 & R24 & _).
destruct Hrbd as (InD0 & _ & Hkb0 & _).
assert (EH : HEAD = 16) by reflexivity.
(* the walk's three blocks on top of the entry's, and the two entry blocks the exit reads: the body's and the input's *)
assert (Hsub : forall b, In b (ablocks B (c_ly cx) (c_S cx)) -> In b (ablocks B ly3 S3))
  by (intros b Hb; rewrite HAB; apply in_or_app; left; exact Hb).
assert (InT : In (c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD) (ablocks B ly3 S3))
  by (rewrite HAB; apply in_or_app; right; left; reflexivity).
assert (InW : In (c_want cx, (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1) (ablocks B ly3 S3))
  by (rewrite HAB; apply in_or_app; right; right; left; reflexivity).
assert (InS : In (same, Z.of_nat (length (c_tb cx)) + 1) (ablocks B ly3 S3))
  by (rewrite HAB; apply in_or_app; right; right; right; left; reflexivity).
pose proof (Hsub _ InD0) as InD. pose proof (Hsub _ Hpt) as InP.
assert (HEn0 : 0 <= (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4)
  by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
assert (NW : ~ In (c_want cx, (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1) (ablocks B (c_ly cx) (c_S cx)))
  by (apply (crt6_blk_new ly3 S3 W3 _ md (c_ly cx) (c_S cx) _ _ HAR HAB); [right; left; reflexivity | cbn [snd]; lia]).
assert (NS : ~ In (same, Z.of_nat (length (c_tb cx)) + 1) (ablocks B (c_ly cx) (c_S cx)))
  by (apply (crt6_blk_new ly3 S3 W3 _ md (c_ly cx) (c_S cx) _ _ HAR HAB);
      [right; right; left; reflexivity | cbn [snd]; lia]).
(* their bounds (AR's block law) *)
destruct (FSW_rd.fsw_ablock_low B _ _ _ _ _ _ _ HAR InT) as (LT1 & LT2 & LT3).
destruct (FSW_rd.fsw_ablock_low B _ _ _ _ _ _ _ HAR InW) as (LW1 & LW2 & LW3).
destruct (FSW_rd.fsw_ablock_low B _ _ _ _ _ _ _ HAR InS) as (LS1 & LS2 & LS3).
destruct (FSW_rd.fsw_ablock_low B _ _ _ _ _ _ _ HAR InD) as (LD1 & LD2 & LD3).
destruct (FSW_rd.fsw_ablock_low B _ _ _ _ _ _ _ HAR InP) as (LP1 & LP2 & LP3).
(* their separations (AR's block separation): the three new blocks pairwise by position, an entry block and a new one
   because the new one is not the entry's *)
pose proof (sep_blocks_pos tfibsegs B LAWS ly3 S3 W3 _ md _ _ (ablocks B (c_ly cx) (c_S cx)) []
  [(same, Z.of_nat (length (c_tb cx)) + 1)] HAR HAB) as DTW.
pose proof (sep_blocks_pos tfibsegs B LAWS ly3 S3 W3 _ md _ _ (ablocks B (c_ly cx) (c_S cx))
  [(c_want cx, (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1)] [] HAR HAB) as DTS.
assert (EWS : ablocks B ly3 S3 =
  (ablocks B (c_ly cx) (c_S cx) ++ [(c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD)]) ++
  (c_want cx, (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 + 1) :: [] ++ (same, Z.of_nat (length (c_tb cx)) + 1) :: [])
  by (rewrite HAB, <- app_assoc; reflexivity).
pose proof (sep_blocks_pos tfibsegs B LAWS ly3 S3 W3 _ md _ _ _ [] [] HAR EWS) as DWS.
pose proof (crt6_blk_sep ly3 S3 W3 _ md _ _ HAR InP InW ltac:(intros E; rewrite <- E in NW; exact (NW Hpt))) as DPW.
pose proof (crt6_blk_sep ly3 S3 W3 _ md _ _ HAR InP InS ltac:(intros E; rewrite <- E in NS; exact (NS Hpt))) as DPS.
pose proof (crt6_blk_sep ly3 S3 W3 _ md _ _ HAR InD InW ltac:(intros E; rewrite <- E in NW; exact (NW InD0))) as DDW.
(* want and same hold no head of U3: U3's heads are the entry's and the text's *)
assert (NHW : ~ In (c_want cx, 16) U3)
  by (rewrite HU; exact (crt6_fresh (c_ly cx) (c_S cx) (c_U cx) ly3 S3 W3 _ md _ _ _ _ HAR FH0 Hsub InW NW InT DTW)).
unfold zdisjoint, block_rng in DTW, DTS, DWS, DPW, DPS, DDW. cbn [fst snd] in DTW, DTS, DWS, DPW, DPS, DDW.
(* want's window and the class-3 frame (YCbq.sep_block_frame; the frame's address is the walk's crt_F) *)
assert (InF : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 _ md _ _ 3 (c_pos cx) HAR InW InF) as DF.
rewrite EF in DF. unfold zdisjoint in DF. cbn [fst snd] in DF.
(* a window inside a new block is writable on the machine's memory (AR's block law gives it present and not owned on the
   unpoisoned reading, which is the machine's there: FSW_frame.fsw_apresent_notowned) and is awr_byte's in_tmp_block arm *)
assert (WR : forall p m a, In (p, m) (ablocks B ly3 S3) -> ~ In (p, m) (ablocks B (c_ly cx) (c_S cx)) ->
  p <= a < p + m ->
  writable_at tfibsegs (mrestrict (w_H W3) (ms_mem ms)) a /\
  awr_byte tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx))
    (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)) a).
{ intros p m a Hin Hnew Ha.
  destruct (FSW_rd.fsw_ablock_low B _ _ _ _ _ _ _ HAR Hin) as (L1 & L2 & L3).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & _ & _ & _ & Hpa & _).
  destruct (Hpa a ltac:(lia)) as (Hp & Hno).
  split.
  - apply (apresent_writable tfibsegs).
    apply (FSW_frame.fsw_apresent_notowned B ly3 S3 U3 W3 (ms_mem ms) md a HARU); [| exact Hno | exact Hp].
    pose proof (@alloc_ceiling_lt rc) as HC47.
    change (2 ^ 47) with 140737488355328 in HC47. change (2 ^ 64) with 18446744073709551616. lia.
  - unfold awr_byte, awr_byte0, in_tmp_block. left. right. right. left.
    exists p, m. split; [exact Hin|]. split; [exact Hnew | lia]. }
split.
- (* crt_keepA *)
  unfold crt_keepA. cbv zeta.
  split; [exact R20|]. split; [exact R21|]. split; [exact R24|].
  split; [rewrite HAB; apply Permutation_refl|].
  split; [rewrite HU; apply Permutation_refl|].
  split; [exact HH|]. split; [exact HRB|]. split; [exact HZX|]. split; [exact HZT|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; exact (WR _ _ a InS NS ltac:(lia))|].
  split.
  { destruct HG as (peak & HG').
    exists (c_live cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))), peak, (c_cnt cx + 1).
    split; [exact HG'|]. split; [reflexivity|]. unfold CNT_82068. lia. }
  split.
  { rewrite (crt6_bb (c_ly cx) (c_S cx) ly3 S3 _ HAB). unfold bsum, LIVE_82068, crt_len.
    cbn [fold_right fst snd]. unfold FSH_Fn_writer.enc_size. lia. }
  split; [unfold K_82068; lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [pose proof (FSW_rd.fsw_ablock_off_img B _ _ _ _ _ _ _ HAR InW); lia|].
  split; [pose proof (FSW_rd.fsw_ablock_off_img B _ _ _ _ _ _ _ HAR InS); lia|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; exact (FSW_rd.fsw_ablock_off_shadow B _ _ _ _ _ _ _ HAR InW a ltac:(lia))|].
  split; [intros a Ha; exact (FSW_rd.fsw_ablock_off_shadow B _ _ _ _ _ _ _ HAR InS a ltac:(lia))|].
  exact HN.
- (* crt_l5_mem *)
  intros Hl1. unfold crt_l5_mem. cbv zeta.
  split.
  { (* the body's bytes: its entry block is live at both ends of the journal (crt6_blk_keep) *)
    pose proof (crt6_zs_bz (c_bs cx) Hbok) as Ezs. rewrite Ezs in Hzbd. unfold zbytes_at in Hzbd.
    intros j Hj. destruct (Hzbd j Hj) as (Hv & Hb). split; [|exact Hb].
    intros q Hq. etransitivity; [|exact (Hv q Hq)].
    apply mbyte_of_aview.
    assert (Hjl : Z.of_nat j < Z.of_nat (length (c_bs cx))) by lia.
    replace (c_bd cx + Z.of_nat j + Z.of_nat q) with (c_bd cx - HEAD + (HEAD + Z.of_nat j + Z.of_nat q)) by lia.
    apply (crt6_blk_keep (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_mem cx) (c_md cx) ly3 S3 U3 W3 (ms_mem ms) md _ _ _ _
      (c_bd cx - HEAD) (kb + HEAD) _ HARU0 HARU HJ InD0 InD).
    lia. }
  split.
  { apply (FSW_rd.fsw_block_body_addressable B ly3 S3 U3 W3 (ms_mem ms) md (c_bd cx - HEAD) (kb + HEAD) (c_bd cx)
      (Z.of_nat (length (c_bs cx))) HARU HH InD); lia. }
  split.
  { apply (crt6_body_addressable_U ly3 S3 U3 W3 (ms_mem ms) md (c_want cx) _ (c_want cx) _ HARU HH InW); [lia | lia | lia |].
    intros r Hr. destruct (crt6_U_new ly3 S3 W3 _ md U3 _ _ HAR HH InW NHW r Hr); [left | right]; lia. }
  split; [intros a Ha; exact (proj1 (WR _ _ a InW NW ltac:(lia)))|].
  split; [intros a Ha; exact (proj2 (WR _ _ a InW NW ltac:(lia)))|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; exact (FSW_rd.fsw_ablock_off_shadow B _ _ _ _ _ _ _ HAR InD a ltac:(lia))|].
  split; [intros a Ha; exact (FSW_rd.fsw_ablock_off_shadow B _ _ _ _ _ _ _ HAR InW a ltac:(lia))|].
  split; [lia|].
  intros a Ha Hw. unfold HState.in_window in Hw. lia.
Qed.

End K.
