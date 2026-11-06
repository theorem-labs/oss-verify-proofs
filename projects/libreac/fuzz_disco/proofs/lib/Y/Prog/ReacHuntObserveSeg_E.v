(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_lay_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of ctrl_lay_block on image B (fuzz_grant.asan-ubsan), ported from
   image A's closed walk lib/A/Prog/CtrlLayBlock.v (a working branch 5aae1e8a0ce), itself written with proof steps adapted
   from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, AC8k.v, AChz.v, ACa2.v and ACb8.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlLayBlock.v, with its module paths, module names and numbers changed; 805 of its 880 lines of code are new or changed and 987 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacHuntObserveSeg_A.v; 1158 of its 1253 lines of code are new or changed and 785 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i YXcalls YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd YCbf YCj1 YCja YCjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacFrameCleanLen.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacHuntObserveCore.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
Context {PW : PAWinImg lib_both3_0_listing}.
Context {PV : PAObjVal lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASM1 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TCOS : treac_disco_classify_on_segment_spec B.
Hypothesis TOBS : treac_disco_table_observe_spec B.
Hypothesis HRO : YRo.tfib_ro_unowned B.
#[local] Notation treac_hunt_observe_kept := (@ReacHuntObserveCore.treac_hunt_observe_kept rc PI B).
#[local] Notation ho_count := (@ReacHuntObserveCore.ho_count rc PI).
#[local] Notation ho_shent_gen := (@ReacHuntObserveCore.ho_shent_gen rc PI).
#[local] Notation hoC := (@ReacHuntObserveCore.hoC rc PI).
#[local] Notation ho_pre := (@ReacHuntObserveCore.ho_pre rc SK PI B).
#[local] Notation ho_post := (@ReacHuntObserveCore.ho_post rc SK PI B).
#[local] Notation ho_mid := (@ReacHuntObserveCore.ho_mid rc SK PI B).
#[local] Notation ho_fsh := (@ReacHuntObserveCore.ho_fsh rc PI).
#[local] Notation ho_saved := (@ReacHuntObserveCore.ho_saved rc PI).
#[local] Notation ho_regs_mid := (@ReacHuntObserveCore.ho_regs_mid rc PI B).
#[local] Notation ho_sp1 := (@ReacHuntObserveCore.ho_sp1 rc PI).
#[local] Notation ho_cfg := (@ReacHuntObserveCore.ho_cfg rc PI).
#[local] Notation ho_base := (@ReacHuntObserveCore.ho_base rc SK PI B).
#[local] Notation ho_L := (@ReacHuntObserveCore.ho_L rc PI).
#[local] Notation ho_U := (@ReacHuntObserveCore.ho_U rc PI).
#[local] Notation ho_Lk := (@ReacHuntObserveCore.ho_Lk rc PI).
#[local] Notation ho_Lk' := (@ReacHuntObserveCore.ho_Lk' rc PI).
#[local] Notation ho_Hcls := (@ReacHuntObserveCore.ho_Hcls rc PI).
#[local] Notation EHOm := (@ReacHuntObserveCore.EHOm rc PI B).
#[local] Notation ho_seg_E_stmt := (@ReacHuntObserveCore.ho_seg_E_stmt rc SK PI B).
#[local] Notation ho_seg_F_stmt := (@ReacHuntObserveCore.ho_seg_F_stmt rc SK PI B).
#[local] Notation hoEF_region_wc := (@ReacHuntObserveCore.hoEF_region_wc rc PI).
#[local] Notation hoF_e32 := (@ReacHuntObserveCore.hoF_e32 rc PI B).
#[local] Notation hoF_val_mem_ext := (@ReacHuntObserveCore.hoF_val_mem_ext rc PI).
#[local] Notation hoF_garr_ext := (@ReacHuntObserveCore.hoF_garr_ext rc PI).
#[local] Notation hoF_aview_frame := (@ReacHuntObserveCore.hoF_aview_frame rc PI).
Hypothesis ho_mid_entry : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F SH (wo : bool) af,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  ho_fsh W2 mem2 F SH -> length SH = 16%nat -> Forall (fun z : Z => 0 <= z < 256) SH ->
  (wo = true -> c_out c <> 0 /\ getr regs2 19 = w64 (c_out c)) ->
  st_ok_pi (fx := c_fq c) SEGS VAL (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) (ss_hoM SH wo af)
    (restrict (w_H W2) (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + af)) mem2 (seg_rom SEGS)))
  /\ img_env VAL A_LIM (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)).
Hypothesis hoF_ereg : forall (c : hoC) (regs2 : bvmap 5 word) (FL : Z) (n : nat) (rr : bv 5),
  (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew (EHOm c regs2 FL) n = getr regs2 rr.
Hypothesis ho_segF : ho_seg_F_stmt.

Lemma ho_garr8_cat5 : forall m (p : Z) (X Y U8 OP R : list byte),
  length X = 400%nat -> length Y = 12%nat -> length U8 = 12%nat -> length OP = 8%nat ->
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) X) ->
  garr8 SEGS m (p + 400) (map (fun b : byte => bv_unsigned b) Y) ->
  garr8 SEGS m (p + 412) (map (fun b : byte => bv_unsigned b) U8) ->
  garr8 SEGS m (p + 424) (map (fun b : byte => bv_unsigned b) OP) ->
  garr8 SEGS m (p + 432) (map (fun b : byte => bv_unsigned b) R) ->
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) (X ++ Y ++ U8 ++ OP ++ R)).
Proof.
  intros m p X Y U8 OP R LX LY LU LO GX GY GU GO GR. rewrite !map_app.
  apply garr8_app. split; [exact GX|]. rewrite length_map, LX.
  apply garr8_app. split; [replace (p + Z.of_nat 400) with (p + 400) by lia; exact GY|].
  rewrite length_map, LY.
  apply garr8_app. split; [replace (p + Z.of_nat 400 + Z.of_nat 12) with (p + 412) by lia; exact GU|].
  rewrite length_map, LU.
  apply garr8_app.
  split; [replace (p + Z.of_nat 400 + Z.of_nat 12 + Z.of_nat 12) with (p + 424) by lia; exact GO|].
  rewrite length_map, LO.
  replace (p + Z.of_nat 400 + Z.of_nat 12 + Z.of_nat 12 + Z.of_nat 8) with (p + 432) by lia. exact GR.
Qed.

Lemma tho_skip_cut : forall (l : list byte) (k n j : nat), j = (n + k)%nat ->
  skipn k l = firstn n (skipn k l) ++ skipn j l.
Proof. intros l k n j ->. rewrite <- skipn_skipn. symmetry. apply firstn_skipn. Qed.

Lemma ho_split480 : forall (Hh : list byte), length Hh = 480%nat ->
  Hh = disco_table_c.sub Hh 0 400 ++ disco_table_c.sub Hh 400 12 ++ disco_table_c.sub Hh 412 12 ++
       disco_table_c.sub Hh 424 8 ++ skipn 432 Hh /\
  skipn 412 Hh = disco_table_c.sub Hh 412 12 ++ disco_table_c.sub Hh 424 8 ++ skipn 432 Hh /\
  length (disco_table_c.sub Hh 0 400) = 400%nat /\ length (disco_table_c.sub Hh 400 12) = 12%nat /\
  length (disco_table_c.sub Hh 412 12) = 12%nat /\ length (disco_table_c.sub Hh 424 8) = 8%nat /\
  length (skipn 432 Hh) = 48%nat.
Proof.
  intros Hh LH.
  assert (E412 : skipn 412 Hh = disco_table_c.sub Hh 412 12 ++ disco_table_c.sub Hh 424 8 ++ skipn 432 Hh).
  { unfold disco_table_c.sub. change (Z.to_nat 412) with 412%nat. change (Z.to_nat 424) with 424%nat.
    transitivity (firstn 12 (skipn 412 Hh) ++ skipn 424 Hh); [apply tho_skip_cut; reflexivity|].
    f_equal. apply tho_skip_cut. reflexivity. }
  assert (E0 : Hh = disco_table_c.sub Hh 0 400 ++ disco_table_c.sub Hh 400 12 ++ skipn 412 Hh).
  { unfold disco_table_c.sub. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 400) with 400%nat.
    change (skipn 0 Hh) with Hh.
    transitivity (firstn 400 Hh ++ skipn 400 Hh); [symmetry; apply firstn_skipn|].
    f_equal. apply tho_skip_cut. reflexivity. }
  split; [rewrite <- E412; exact E0|]. split; [exact E412|].
  split; [apply HuntObsLib.len_sub; lia|]. split; [apply HuntObsLib.len_sub; lia|].
  split; [apply HuntObsLib.len_sub; lia|]. split; [apply HuntObsLib.len_sub; lia|].
  rewrite length_skipn. lia.
Qed.

Lemma ho_hunt_ok_ok : forall (Hh T' Lk' OP : list byte) (now : Z),
  hunt_c.hunt_ok Hh -> length T' = 400%nat -> disco_table_c.table_ok T' ->
  length Lk' = 12%nat -> disco_classify_c.lock_ok Lk' ->
  OP = (if disco_table_c.n_of (disco_table_c.sub Hh 0 400) =? 0
        then Mem.le8 (Z_to_bv 64 now) else disco_table_c.sub Hh 424 8) ->
  hunt_c.hunt_ok (T' ++ Lk' ++ disco_table_c.sub Hh 412 12 ++ OP ++ skipn 432 Hh).
Proof.
  intros Hh T' Lk' OP now HOK LT TOK LL LOK EOP. pose proof HOK as (LH & _).
  assert (LOP : length OP = 8%nat).
  { rewrite EOP. destruct (_ =? 0); [apply Mem.length_le8 | apply HuntObsLib.len_sub; lia]. }
  assert (LU : length (disco_table_c.sub Hh 412 12) = 12%nat) by (apply HuntObsLib.len_sub; lia).
  apply (ho_hok_gen Hh T' Lk' _ LH HOK LT TOK LL LOK).
  - rewrite !length_app, length_skipn. lia.
  - rewrite HuntObsLib.sub_app_r by lia. rewrite HuntObsLib.sub_app_r by lia.
    rewrite HuntObsLib.sub_skipn by lia. f_equal; lia.
Qed.

Lemma hoEF_hfacts : forall (c : hoC) ly2 S2 (W2 : world SEGS) mem2 md2,
  ho_pre c -> AR SEGS B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B (c_lyc c) (c_Sc c)) ->
  0 < c_h c /\ c_h c mod 8 = 0 /\ c_h c + 480 <= YM05.alloc_ceiling /\
  YM05.alloc_ceiling <= 2 ^ 63 /\ amem_range (c_h c) 480 /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (c_h c) 480 /\
  shadow_hull_vis (aview SEGS (w_H W2) mem2) (c_h c) 480 /\
  (forall a, c_h c <= a < c_h c + 480 -> apresent (w_H W2) mem2 a) /\
  In (c_hb c, c_hn c) (ablocks B ly2 S2).
Proof.
intros c ly2 S2 W2 mem2 md2 HPRE HAR Hperm.
destruct HPRE as (_&_&_&_&_&_&_&_&_&_&_&_&_&Hh0&Hh8&Hin&Hhb1&Hhb2&_).
assert (Hin2 : In (c_hb c, c_hn c) (ablocks B ly2 S2))
by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) HAR Hin2)
  as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact Hh0|]. split; [exact Hh8|]. split; [lia|]. split; [lia|].
split; [unfold amem_range; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp;
        unfold kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|].
split; [apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) (c_h c) 480 HAR Hin2); lia|].
split; [apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) (c_h c) 480 HAR Hin2); lia|].
split; [intros a Ha; exact (proj1 (Hbpres a ltac:(lia))) | exact Hin2].
Qed.

Ltac hoEF_wc HS i wlo whi ch tac :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth i rs got_regionP) in
let r' := eval vm_compute in (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) wlo whi
                                (ch :: YP09.r_chunks r)) in
lazymatch r with YP09.mkRegion (Some ?nn) ?lo ?hi ?wlo0 ?whi0 ?cs =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r r' HS
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (hoEF_region_wc Ex (ms_mem msx) nn lo hi wlo0 whi0 cs wlo whi ch
     (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(first [left; lia | right; split; lia])
     ltac:(tac))) as HS3;
clear HS; rename HS3 into HS end end; norm_ss HS.

Lemma hoEF_spfacts : forall (c : hoC) sp1,
  ho_pre c -> astk_ok (c_STK c) (c_ly c) (c_sp0 c) -> ho_sp1 c sp1 ->
  0 < sp1 /\ sp1 + 56 <= spZ (c_regs c) - 104 /\ spZ (c_regs c) <= 2 ^ 47 /\
  c_sp0 c - c_STK c <= spZ (c_regs c) - 8688 /\ spZ (c_regs c) <= c_sp0 c /\
  spZ (c_regs c) - 176 <= sp1 <= spZ (c_regs c) - 160 /\ 0 < c_sp0 c /\ c_sp0 c <= 2 ^ 47 /\
  YM05.alloc_ceiling <= c_sp0 c - c_STK c.
Proof.
intros c sp1 HPRE (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) (He & Hr & Hm).
destruct HPRE as (_&_&_&_&_&_&_&Hwin&Hspl&_).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
repeat split; lia.
Qed.

Lemma hoEF_awr_hunt : forall (c : hoC) fpos ly2 S2 a,
  ho_pre c ->
  (forall cid p, frame_addr ly2 cid p = frame_addr (c_lyc c) cid p) ->
  Permutation (ablocks B ly2 S2) (ablocks B (c_lyc c) (c_Sc c)) ->
  c_h c <= a < c_h c + 480 ->
  awr_byte (c_STK c) (c_sp0 c) (c_FP c) (ablocks B (c_ly c) (c_S c))
    (ablocks B ly2 S2) ly2 ((1, fpos) :: c_own c) a.
Proof.
intros c fpos ly2 S2 a HPRE Hfa Hperm Ha.
destruct HPRE as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hhw&_).
apply (hoEF_awr_mid (c_STK c) (c_sp0 c) (c_FP c) (ablocks B (c_ly c) (c_S c))
         (ablocks B (c_lyc c) (c_Sc c)) (ablocks B ly2 S2) (c_lyc c) ly2 (c_own c) (1, fpos) a).
- intros p Hp. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hp.
- exact Hfa.
- apply Hhw. exact Ha.
Qed.

Ltac hoEF_awrtac AG E2x E21x HAWRH :=
intros a (rr & Hin & Hrng); cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng; revert Hrng;
    rewrite ?(AG 2%nat ltac:(lia)), ?(AG 21%nat ltac:(lia)), ?E2x, ?E21x;
    rewrite ?unsigned_lit_small by lia; intros Hrng;
    first [ solve [exfalso; lia] | solve [left; lia] | solve [apply HAWRH; lia] ] |]);
destruct Hin.

Lemma hoEF_fa_journal : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world SEGS) mem' md' k,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall cid p, frame_addr ly' cid p = frame_addr ly cid p.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJx cid p.
destruct HJx as (_ & (_ & _ & _ & _ & _ & HFx & _) & _).
unfold frame_addr. rewrite HFx. reflexivity.
Qed.

Lemma hoEF_fl_journal : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world SEGS) mem' md' k,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall cid p, flag_addr ly' cid p = flag_addr ly cid p.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJx cid p.
destruct HJx as (_ & (_ & _ & _ & _ & _ & HFx & _) & _).
unfold flag_addr. rewrite HFx. reflexivity.
Qed.

Lemma hoEF_blkbnd : forall (c : hoC) ly2 S2 (W2 : world SEGS) mem2 md2 b m i,
  ho_pre c -> astk_ok (c_STK c) (c_ly c) (c_sp0 c) ->
  AR SEGS B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B (c_lyc c) (c_Sc c)) ->
  In (b, m) (ablocks B (c_lyc c) (c_Sc c)) -> 0 <= i < req_size m ->
  0 <= b + i < 2 ^ 64 /\ b + i < spZ (c_regs c) - REAC_HUNT_OBSERVE_STK /\ ~ in_img SEGS (b + i).
Proof.
intros c ly2 S2 W2 mem2 md2 b m i HPRE Hstk HAR Hperm Hin Hi.
assert (Hin2 : In (b, m) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR Hin2) as (_ & Hb4096 & Hbceil & _ & _ & _).
pose proof (blk_img _ _ LAWS ly2 S2 W2 mem2 md2 b m (b + i) HAR Hin2 ltac:(lia)) as Hni.
destruct HPRE as (_&_&_&_&_&_&_&Hwin&Hspl&_).
destruct Hstk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
split; [clear - Hb4096 Hbceil Hi C1; lia|].
split; [clear - Hb4096 Hbceil Hi C1 Hwin Hspl Hceil Hslo HSTK; lia | exact Hni].
Qed.

Lemma hoEF_frmbnd : forall (c : hoC) fpos ly2 S2 (W2 : world SEGS) mem2 md2 cid pos a,
  ho_pre c -> astk_ok (c_STK c) (c_ly c) (c_sp0 c) ->
  AR SEGS B ly2 S2 W2 mem2 md2 -> frames S2 = (1, fpos) :: frames (c_Sc c) ->
  In (cid, pos) (frames (c_Sc c)) ->
  (frame_addr ly2 cid pos <= a < frame_addr ly2 cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr ly2 cid pos) <= a < shadow_addr (frame_addr ly2 cid pos) + fs_frame_bytes cid / 8) ->
  0 <= a < 2 ^ 64 /\ a < spZ (c_regs c) - REAC_HUNT_OBSERVE_STK.
Proof.
intros c fpos ly2 S2 W2 mem2 md2 cid pos a HPRE Hstk HAR Hfrs Hin Ha.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; right; exact Hin).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 cid pos HAR Hin2) as (H4096 & Hceilf & _).
destruct HPRE as (_&_&_&_&_&_&_&Hwin&Hspl&_).
destruct Hstk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
unfold shadow_addr in Ha.
assert (Hd8 : frame_addr ly2 cid pos / 8 <= frame_addr ly2 cid pos)
  by (apply Z.div_le_upper_bound; lia).
assert (Hd8b : 0 <= frame_addr ly2 cid pos / 8) by (apply Z.div_pos; lia).
assert (Hfb8 : fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia).
unfold SHADOW_OFF in *.
split; [clear - Ha H4096 Hceilf C1 Hfb Hd8 Hd8b Hfb8; lia |
        clear - Ha H4096 Hceilf C1 Hfb Hd8 Hd8b Hfb8 Hwin Hspl Hceil Hslo HSTK; lia].
Qed.

Lemma hoEF_kept_agree : forall (c : hoC) fpos ly2 S2 (W2 : world SEGS) mem2 mem3 md2 (Wr : Z -> Prop),
  ho_pre c -> astk_ok (c_STK c) (c_ly c) (c_sp0 c) ->
  AR SEGS B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B (c_lyc c) (c_Sc c)) ->
  frames S2 = (1, fpos) :: frames (c_Sc c) ->
  (forall cid p, frame_addr ly2 cid p = frame_addr (c_lyc c) cid p) ->
  (forall a, Wr a -> tho_wr (c_h c) (c_out c) a) ->
  (forall a, in_img SEGS a -> ~ Wr a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a ->
     ~ (spZ (c_regs c) - REAC_HUNT_OBSERVE_STK <= a < spZ (c_regs c)) ->
     aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, spZ (c_regs c) - REAC_HUNT_OBSERVE_STK <= a < spZ (c_regs c) -> apresent (w_H W2) mem3 a) ->
  treac_hunt_observe_kept (c_lyc c) (c_Sc c) (c_W c) (c_memc c) W2 mem2 (spZ (c_regs c)) (c_h c) (c_out c) ->
  treac_hunt_observe_kept (c_lyc c) (c_Sc c) (c_W c) (c_memc c) W2 mem3 (spZ (c_regs c)) (c_h c) (c_out c).
Proof.
intros c fpos ly2 S2 W2 mem2 mem3 md2 Wr HPRE Hstk HAR Hperm Hfrs Hfa Hsub Himg HAG HMG HPR
  (K1 & K2 & K3 & K4 & K5 & K6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PI) as Hsegs.
assert (Hwin2 : YM05.alloc_ceiling <= spZ (c_regs c) - REAC_HUNT_OBSERVE_STK).
{ destruct HPRE as (_&_&_&_&_&_&_&Hwin&Hspl&_). destruct Hstk as (_ & Hstk0 & Hceil & Hslo & _).
  clear - Hwin Hspl Hceil Hslo. lia. }
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw Htw. rewrite (HAG a ltac:(lia) ltac:(intros HW; exact (Htw (Hsub a HW))) Hw).
  exact (K1 a Ha Hw Htw).
- intros b m i Hin Hi Htw.
  destruct (hoEF_blkbnd c ly2 S2 W2 mem2 md2 b m i HPRE Hstk HAR Hperm Hin Hi) as (Hb1 & Hb2 & Hb3).
  rewrite (HAG (b + i) ltac:(lia) ltac:(intros HW; exact (Htw (Hsub (b + i) HW))) ltac:(lia)).
  exact (K2 b m i Hin Hi Htw).
- intros a Hi Ho He. pose proof (Hsegs a Hi) as Hlo. unfold kLowMemEnd in Hlo.
  rewrite (HAG a ltac:(lia) (Himg a Hi) ltac:(lia)). exact (K3 a Hi Ho He).
- intros cid pos a Hin Hrng Htw.
  assert (Hrng2 : frame_addr ly2 cid pos <= a < frame_addr ly2 cid pos + fs_frame_bytes cid \/
    shadow_addr (frame_addr ly2 cid pos) <= a < shadow_addr (frame_addr ly2 cid pos) + fs_frame_bytes cid / 8).
  { rewrite (Hfa cid pos). unfold in_zr, frame_rng in Hrng. cbn [fst snd] in Hrng. exact Hrng. }
  destruct (hoEF_frmbnd c fpos ly2 S2 W2 mem2 md2 cid pos a HPRE Hstk HAR Hfrs Hin Hrng2) as (Hf1 & Hf2).
  rewrite (HAG a Hf1 ltac:(intros HW; exact (Htw (Hsub a HW))) ltac:(lia)).
  exact (K4 cid pos a Hin Hrng Htw).
- intros a Ha Hw Hp. exact (HMG a (K5 a Ha Hw Hp)).
- exact HPR.
Qed.

Lemma hoEF_kept_call : forall (c : hoC) fpos ly2 S2 (W2 W4 : world SEGS) mem3 mem4 md3 sp1,
  ho_pre c -> astk_ok (c_STK c) (c_ly c) (c_sp0 c) -> ho_sp1 c sp1 ->
  AR SEGS B ly2 S2 W2 mem3 md3 ->
  Permutation (ablocks B ly2 S2) (ablocks B (c_lyc c) (c_Sc c)) ->
  frames S2 = (1, fpos) :: frames (c_Sc c) ->
  (forall cid p, frame_addr ly2 cid p = frame_addr (c_lyc c) cid p) ->
  treac_hunt_observe_kept (c_lyc c) (c_Sc c) (c_W c) (c_memc c) W2 mem3 (spZ (c_regs c)) (c_h c) (c_out c) ->
  treac_disco_table_observe_kept B ly2 S2 W2 mem3 W4 mem4 sp1 (c_h c) ->
  treac_hunt_observe_kept (c_lyc c) (c_Sc c) (c_W c) (c_memc c) W4 mem4 (spZ (c_regs c)) (c_h c) (c_out c).
Proof.
intros c fpos ly2 S2 W2 W4 mem3 mem4 md3 sp1 HPRE Hstk HSP1 HAR Hperm Hfrs Hfa
  (K1 & K2 & K3 & K4 & K5 & K6) (T1 & T2 & T3 & T4 & T5 & T6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PI) as Hsegs.
destruct HSP1 as (Hsp1e & Hsp1r & Hsp1m).
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
assert (HOST : REAC_DISCO_TABLE_OBSERVE_STK = 8304) by reflexivity.
assert (Hsp47 : spZ (c_regs c) <= 2 ^ 47).
{ destruct HPRE as (_&_&_&_&_&_&_&_&Hspl&_). destruct Hstk as (_&_&_&_&Hshi&H47&_).
  clear - Hspl Hshi H47. lia. }
assert (Hwin2 : YM05.alloc_ceiling <= spZ (c_regs c) - REAC_HUNT_OBSERVE_STK).
{ destruct HPRE as (_&_&_&_&_&_&_&Hwin&Hspl&_). destruct Hstk as (_ & Hstk0 & Hceil & Hslo & _).
  clear - Hwin Hspl Hceil Hslo. lia. }
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw Htw. rewrite (T1 a ltac:(clear - Ha; lia) ltac:(clear - Hw Hsp1r HSTK HOST Hsp47; lia)
    ltac:(intros HTq; apply Htw; left; clear - HTq; lia)).
  exact (K1 a Ha Hw Htw).
- intros b m i Hin Hi Htw.
  assert (Hin2 : In (b, m) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
  rewrite (T2 b m i Hin2 Hi ltac:(intros HTq; apply Htw; left; clear - HTq; lia)).
  exact (K2 b m i Hin Hi Htw).
- intros a Hi Ho He. rewrite (T3 a Hi Ho He). exact (K3 a Hi Ho He).
- intros cid pos a Hin Hrng Htw.
  assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; right; exact Hin).
  assert (Hrng2 : in_zr a (frame_rng ly2 (cid, pos)) \/
     in_zr a (shadow_addr (frame_addr ly2 cid pos), fs_frame_bytes cid / 8)).
  { unfold in_zr, frame_rng in Hrng |- *. cbn [fst snd] in Hrng |- *. rewrite (Hfa cid pos). exact Hrng. }
  rewrite (T4 cid pos a Hin2 Hrng2 ltac:(intros HTq; apply Htw; left; clear - HTq; lia)).
  exact (K4 cid pos a Hin Hrng Htw).
- intros a Ha Hw Hp.
  apply (T5 a ltac:(lia) ltac:(clear - Hw Hsp1r HSTK HOST Hsp47; lia)). exact (K5 a Ha Hw Hp).
- intros a Ha.
  destruct (Z_lt_le_dec a sp1) as [Hlt | Hge].
  + destruct (Z_lt_le_dec a (sp1 - REAC_DISCO_TABLE_OBSERVE_STK)) as [Hlt2 | Hge2].
    * apply (T5 a ltac:(clear - Ha Hwin2 HSTK Hsp47 C1; lia) ltac:(clear - Hlt2; lia)). exact (K6 a Ha).
    * apply T6. clear - Hlt Hge2. lia.
  + apply (T5 a ltac:(clear - Ha Hwin2 HSTK Hsp47 C1; lia) ltac:(clear - Hge; lia)). exact (K6 a Ha).
Qed.

Lemma hoEF_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(s & Hs & _ & Hr) | Hrel]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hrel)].
Qed.

Lemma hoEF_rod_keep : forall (Wa Wb : world SEGS) ma mb,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wa) ma) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H Wb) mb a = aview SEGS (w_H Wa) ma a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wb) mb).
Proof.
intros Wa Wb ma mb HR HK a Hro Ho He.
rewrite (HK a (hoEF_ro_img a Hro) Ho He). exact (HR a Hro Ho He).
Qed.

Lemma hoEF_garr_keep : forall (Wa Wb : world SEGS) ma mb p L,
  (forall i, 0 <= i < Z.of_nat (length L) ->
     aview SEGS (w_H Wb) mb (p + i) = aview SEGS (w_H Wa) ma (p + i)) ->
  garr8 SEGS (mrestrict (w_H Wa) ma) p L -> garr8 SEGS (mrestrict (w_H Wb) mb) p L.
Proof.
intros Wa Wb ma mb p L HE HGa j Hj. destruct (HGa j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. rewrite <- (Hv kk Hk). apply (mbyte_of_aview SEGS).
replace (p + Z.of_nat j + Z.of_nat kk) with (p + (Z.of_nat j + Z.of_nat kk)) by lia.
apply HE. lia.
Qed.

Lemma hoEF_ra_kept : forall (rd rd' : reader) a nn,
  (forall x, a <= x < a + nn -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd SHADOW_OFF a nn -> range_addressable rd' SHADOW_OFF a nn.
Proof.
intros rd rd' a nn HK HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
exists s. rewrite (HK x Hx). split; [exact Hs | exact Hok].
Qed.

Lemma hoEF_shadow_frame : forall (W2 : world SEGS) mem Fa,
  ho_fsh W2 mem Fa ho_shC -> Fa mod 64 = 0 -> 0 <= Fa ->
  range_addressable (aview SEGS (w_H W2) mem) SHADOW_OFF (Fa + 32) 24 /\
  shadow_hull_vis (aview SEGS (w_H W2) mem) (Fa + 32) 24.
Proof.
intros W2 mem Fa HFSH H64 H0.
apply (proj1 (Z.mod_divide Fa 64 ltac:(lia))) in H64. destruct H64 as [z Hz].
assert (Hd : forall d, 0 <= d < 64 -> (Fa + d) / 8 = 8 * z + d / 8).
{ intros d Hdr. rewrite Hz. replace (z * 64 + d) with (8 * z * 8 + d) by lia.
  rewrite Z.div_add_l by lia. reflexivity. }
assert (HF8 : Fa / 8 = 8 * z)
by (rewrite Hz; replace (z * 64) with (8 * z * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HSB : SHADOW_OFF = 8 * 268431360) by reflexivity.
split.
- intros x Hx. exists 0.
  assert (Hx8 : shadow_of_addr SHADOW_OFF x = SB + Fa / 8 + (x - Fa) / 8).
  { unfold shadow_of_addr. rewrite HF8. replace x with (Fa + (x - Fa)) by lia.
    rewrite (Hd (x - Fa) ltac:(lia)). unfold SB. lia. }
  rewrite Hx8. split; [|left; reflexivity].
  rewrite (HFSH ((x - Fa) / 8) ltac:(split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia])).
  f_equal.
  assert (Hv : (x - Fa) / 8 = 4 \/ (x - Fa) / 8 = 5 \/ (x - Fa) / 8 = 6).
  { pose proof (Z.div_mod (x - Fa) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x - Fa) 8 ltac:(lia)). lia. }
  destruct Hv as [Hv | [Hv | Hv]]; rewrite Hv; reflexivity.
- intros s Hs.
  assert (Hlo : shadow_addr (Fa + 32) / 8 * 8 = SB + Fa / 8).
  { unfold shadow_addr. rewrite (Hd 32 ltac:(lia)), HF8, HSB.
    replace (8 * 268431360 + (8 * z + 32 / 8)) with ((268431360 + z) * 8 + 4) by (cbn; lia).
    rewrite Z.div_add_l by lia. change (4 / 8) with 0. unfold SB. lia. }
  assert (Hhi : shadow_addr (Fa + 32 + 24 - 1) / 8 * 8 + 8 = SB + Fa / 8 + 8).
  { unfold shadow_addr. replace (Fa + 32 + 24 - 1) with (Fa + 55) by lia.
    rewrite (Hd 55 ltac:(lia)), HF8, HSB.
    replace (8 * 268431360 + (8 * z + 55 / 8)) with ((268431360 + z) * 8 + 6) by (cbn; lia).
    rewrite Z.div_add_l by lia. change (6 / 8) with 0. unfold SB. lia. }
  rewrite Hlo, Hhi in Hs.
  replace s with (SB + Fa / 8 + (s - (SB + Fa / 8))) by lia.
  rewrite (HFSH (s - (SB + Fa / 8)) ltac:(lia)). discriminate.
Qed.

Ltac hoF_ro HS i :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 0
     (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(intros o Ho; exfalso; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Ltac hoF_awr1 U2 :=
let a := fresh "a" in let Ha := fresh "Ha" in let rg := fresh "rg" in
let Hrg := fresh "Hrg" in let Hrng := fresh "Hrng" in
intros a Ha; destruct Ha as (rg & Hrg & Hrng);
cbn [ss_mem In] in Hrg;
repeat (destruct Hrg as [<- | Hrg];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng; rewrite ?U2 in Hrng;
   first [exfalso; lia | left; lia] | ]);
destruct Hrg.

Ltac hoF_ms MSn :=
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msk) |- _ => rename msk into MSn
| HSx : st_ok _ _ _ (restrict _ ?msk) |- _ => rename msk into MSn end.

Ltac hoF_hw m0 MS sp U2 HWn :=
lazymatch goal with HFx : frame_of _ _ (mrestrict (w_H ?Wx) m0) (mrestrict _ (ms_mem MS)) |- _ =>
assert (HWn : forall a, 0 <= a < 2 ^ 64 -> ~ (sp <= a < sp + 56) ->
   aview SEGS (w_H Wx) (ms_mem MS) a = aview SEGS (w_H Wx) m0 a);
[ let a := fresh "a" in let Ha := fresh "Ha" in let Hs := fresh "Hs" in
  let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hrng := fresh "Hrng" in
  intros a Ha Hs; apply (hoF_aview_frame _ _ Wx m0 (ms_mem MS) a HFx Ha);
  intros (rg & Hrg & Hrng); cbn [ss_mem In] in Hrg;
  repeat (destruct Hrg as [<- | Hrg];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng; rewrite ?U2 in Hrng; lia | ]);
  destruct Hrg
| clear HFx ] end;
try (lazymatch goal with HFx : frame_of _ _ m0 (ms_mem MS) |- _ => clear HFx end).

Ltac hoF_hp m0 MS HPn :=
lazymatch goal with HGx : mem_grows (mrestrict (w_H ?Wx) m0) (mrestrict _ (ms_mem MS)) |- _ =>
assert (HPn : forall a, apresent (w_H Wx) m0 a -> apresent (w_H Wx) (ms_mem MS) a)
  by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; eapply apresent_grows; [exact HGx | exact Ha]);
clear HGx end.

Ltac hoF_rd HS r Hr :=
lazymatch type of HS with
| st_ok_pi _ _ ?Ev ?ssx (restrict ?Hv ?msx) =>
  pose proof (st_ok_pi_restrict_reg Hv Ev ssx msx r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
  change (sr_get (ss_regs ssx) r) with e in Hr
| st_ok ?sg ?Ev ?ssx (restrict ?Hv ?msx) =>
  pose proof (st_ok_restrict_reg sg Hv Ev ssx msx r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
  change (sr_get (ss_regs ssx) r) with e in Hr end.

Ltac hoF_same HS AG Ren r n :=
let Hr := fresh "Hr" in hoF_rd HS r Hr;
rewrite Hr, hoF_off0; try rewrite (AG n ltac:(lia)); apply Ren; [lia | reflexivity].

Lemma hoE_v1 : forall x, Z_to_bv 8 (YG0f.le_byte x 1 0) = Z_to_bv 8 x.
Proof.
intros x. unfold YG0f.le_byte. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.

Lemma hoE_le8_nth : forall v k, 0 <= v < 2 ^ 64 -> (k < 8)%nat ->
  YG0f.le_byte v 8 k = nth k (map (fun b : byte => bv_unsigned b) (Mem.le8 (Z_to_bv 64 v))) 0.
Proof.
intros v k Hv Hk.
change (Mem.le8 (Z_to_bv 64 v)) with (Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 v))).
rewrite unsigned_lit_small by lia.
unfold YG0f.le_byte. rewrite (Z.mod_small v) by (cbn [Z.of_nat Z.mul]; lia).
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try (exfalso; lia);
cbn [Z_to_le_bytes map nth Z.of_nat Z.mul];
rewrite ?Z.shiftr_0_r, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; reflexivity.
Qed.

Lemma hoE_garr8_of_val8 : forall m a v, 0 <= v < 2 ^ 64 ->
  val_mem SEGS m a 8 v ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) (Mem.le8 (Z_to_bv 64 v))).
Proof.
intros m a v Hv HV j Hj. rewrite length_map, Mem.length_le8 in Hj.
assert (Hn : nth j (map (fun b : byte => bv_unsigned b) (Mem.le8 (Z_to_bv 64 v))) 0
             = YG0f.le_byte v 8 j) by (symmetry; apply hoE_le8_nth; [lia | exact Hj]).
split.
- intros kk Hk. replace kk with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (HV j Hj). f_equal. rewrite Hn. symmetry. apply hoE_v1.
- rewrite Hn. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma hoE_splitH : forall (c : hoC), hunt_c.hunt_ok (c_H c) -> length (ho_Lk' c) = 12%nat ->
  ho_Hcls c = disco_table_c.sub (c_H c) 0 400 ++ ho_Lk' c ++ disco_table_c.sub (c_H c) 412 12 ++
              disco_table_c.sub (c_H c) 424 8 ++ skipn 432 (c_H c).
Proof.
intros c HOK0 LL. pose proof HOK0 as (LH & _).
destruct (ho_split480 (c_H c) LH) as (_ & E412 & _).
unfold ho_Hcls. rewrite E412. reflexivity.
Qed.

Lemma hoE_mid_step : forall (c : hoC) fpos ly2 S2 (W2 : world SEGS) mem2 md2 mem3 md3 k2 H2 H3 sp1,
  ho_pre c -> ho_sp1 c sp1 ->
  ho_mid c fpos ly2 S2 W2 mem2 md2 k2 H2 ->
  ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 mem3 md3 k2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_h c + 424 <= a < c_h c + 432) ->
     ~ (spZ (c_regs c) - REAC_HUNT_OBSERVE_STK <= a < spZ (c_regs c)) ->
     aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, spZ (c_regs c) - REAC_HUNT_OBSERVE_STK <= a < spZ (c_regs c) -> apresent (w_H W2) mem3 a) ->
  garr8 SEGS (mrestrict (w_H W2) mem3) (c_h c) (map (fun b : byte => bv_unsigned b) H3) ->
  length H3 = 480%nat ->
  ho_mid c fpos ly2 S2 W2 mem3 md3 k2 H3.
Proof.
intros c fpos ly2 S2 W2 mem2 md2 mem3 md3 k2 H2 H3 sp1 HPRE HSP1 HMID HJ3 HAG HMG HPR HG3 LH3.
pose proof HMID as (HJ & Hfrs & Hfa & Hperm & HKEPT & HROm & HGH & HLH & HFLAG).
pose proof (proj1 HJ) as HARj.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct (hoEF_hfacts c ly2 S2 W2 mem2 md2 HPRE HARj Hperm)
  as (Hh0 & Hh8 & Hhceil & Hceil63 & Hamr & Hraz & Hshv & Hpres & Hin2).
destruct (hoEF_spfacts c sp1 HPRE Hstk HSP1)
  as (Hsp1pos & Hsp1hi & Hsplim & Hwin8 & Hspl2 & Hsp1lo & Hsp0pos & Hsp0hi & Hceil0).
pose proof HPRE as (Hj0 & Hro0 & Hra0 & Hra4 & Hgp & Htp & Hsp16 & Hwin & Hspl & Hdep &
  Hlenr & Hnowr & Houtr & Hh0' & Hh8' & Hinb & Hhb1 & Hhb2 & Hhw & HOK0 & HFBl & HGH0 & HF50 & HOUT & HKM & HKT).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 1 fpos HARj Hfin2) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp.
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) 1 fpos HARj Hin2 Hfin2) as HdFH.
unfold zdisjoint in HdFH. cbn [fst snd] in HdFH. change (fs_frame_bytes 1) with 128 in HdFH.
assert (Himg : forall a, in_img SEGS a -> ~ (c_h c + 424 <= a < c_h c + 432)).
{ intros a Hi Hb. exact (blk_img _ _ LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) a HARj Hin2
    ltac:(clear - Hb Hhb1 Hhb2; lia) Hi). }
pose proof (@pa_segs_low _ _ PI) as Hsegs.
split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hfa|]. split; [exact Hperm|].
split.
{ exact (hoEF_kept_agree c fpos ly2 S2 W2 mem2 mem3 md2
    (fun a => c_h c + 424 <= a < c_h c + 432)
    HPRE Hstk HARj Hperm Hfrs Hfa
    ltac:(intros a Ha; cbv beta in Ha; unfold tho_wr; left; clear - Ha; lia) Himg HAG HMG HPR HKEPT). }
split.
{ apply (hoEF_rod_keep W2 W2 mem2 mem3 HROm).
  intros a Hi _ _. pose proof (Hsegs a Hi) as Hlo. unfold kLowMemEnd in Hlo.
  apply (HAG a ltac:(clear - Hlo; lia) (Himg a Hi) ltac:(clear - Hlo Hwin8 Hceil0 HSTK C1; lia)). }
split; [exact HG3|]. split; [exact LH3|].
assert (HFLAGa : forall kk, 0 <= kk < 8 ->
  aview SEGS (w_H W2) mem3 (frame_addr ly2 1 fpos + 120 + kk)
  = aview SEGS (w_H W2) mem2 (frame_addr ly2 1 fpos + 120 + kk)).
{ intros kk Hk. apply HAG.
  - clear - Hk HF4096 HFceil C1. lia.
  - clear - Hk HdFH Hhb1 Hhb2 HF4096 HFceil Hh0. lia.
  - clear - Hk HFceil Hwin8 Hceil0 HSTK. lia. }
rewrite (rdword_ext (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3)
  (frame_addr ly2 1 fpos + 120) HFLAGa).
exact HFLAG.
Qed.

Lemma hoE_ret01 : forall T G ow now T' ret,
  reac_disco_table_observe_c.observe_model T G ow now T' ret -> ret = 0 \/ ret = 1.
Proof.
intros T G ow now T' ret (r & _ & [[_ He] | [(_ & _ & He) | (_ & _ & He)]]).
- unfold reac_disco_table_observe_c.observe_known in He.
  lazymatch type of He with _ = (if ?b then _ else _) => destruct b end;
  inversion He; [right | left]; reflexivity.
- unfold reac_disco_table_observe_c.observe_full in He.
  lazymatch type of He with _ = (if ?b then _ else _) => destruct b end;
  inversion He; left; reflexivity.
- unfold reac_disco_table_observe_c.observe_new in He. inversion He. right. reflexivity.
Qed.

Lemma hoE_lk : forall (c : hoC),
  hunt_c.hunt_ok (c_H c) -> hunt_c.hunt_ok (ho_Hcls c) ->
  length (ho_Lk' c) = 12%nat /\ disco_classify_c.lock_ok (ho_Lk' c).
Proof.
intros c HOK0 HOKc.
pose proof HOK0 as (LH0 & _).
pose proof HOKc as (LHc & _ & LOK & _).
assert (L400 : length (disco_table_c.sub (c_H c) 0 400) = 400%nat)
by (apply HuntObsLib.len_sub; lia).
assert (L68 : length (skipn 412 (c_H c)) = 68%nat) by (rewrite length_skipn; lia).
assert (LL : length (ho_Lk' c) = 12%nat)
by (unfold ho_Hcls in LHc; rewrite !length_app, L400, L68 in LHc; lia).
split; [exact LL|].
unfold ho_Hcls in LOK.
rewrite (ho_skipn_exact (disco_table_c.sub (c_H c) 0 400) _ 400 L400) in LOK.
rewrite (ho_firstn_exact (ho_Lk' c) (skipn 412 (c_H c)) 12 LL) in LOK.
exact LOK.
Qed.

Lemma hoE_pres_get : forall (regs regs' : bvmap 5 word) (r : Z) (rb : bv 5),
  aregs_preserved regs regs' -> acallee_saved r -> Z_to_bv 5 r = rb -> getr regs' rb = getr regs rb.
Proof. intros regs regs' r rb HP Hc Hr. rewrite <- Hr. apply HP. exact Hc. Qed.

Lemma hoE_call : forall (c : hoC) fpos ly2 S2 (W2 : world SEGS) mem3 md3 k2 regs3 sp1 F H3 OP,
  ho_seg_F_stmt ->
  ho_base c fpos ly2 S2 W2 mem3 md3 k2 H3 regs3 sp1 F ->
  getr regs3 1 = w64 (BASE + 29692) ->
  getr regs3 10 = w64 (c_h c) -> getr regs3 11 = w64 (F + 32) ->
  getr regs3 12 = w64 0 -> getr regs3 13 = w64 (c_now c) ->
  getr regs3 19 = w64 (c_out c) -> getr regs3 20 = w64 (c_now c) ->
  getr regs3 22 = w64 (c_h c + 384) -> getr regs3 23 = w64 (F + 32) ->
  getr regs3 26 = w64 SB -> getr regs3 27 = w64 (SB + (c_h c + 384) / 8) ->
  ho_fsh W2 mem3 F ho_shC ->
  hunt_c.hunt_ok H3 -> hunt_c.hunt_ok (ho_Hcls c) ->
  disco_table_c.sub H3 0 400 = disco_table_c.sub (c_H c) 0 400 ->
  skipn 400 H3 = ho_Lk' c ++ disco_table_c.sub (c_H c) 412 12 ++ OP ++ skipn 432 (c_H c) ->
  OP = (if disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400) =? 0
        then Mem.le8 (Z_to_bv 64 (c_now c)) else disco_table_c.sub (c_H c) 424 8) ->
  disco_classify_c.cm_ret (c_FB c) (ho_L c) (ho_U c) (ho_Lk c) = 0 ->
  garr8 SEGS (mrestrict (w_H W2) mem3) (F + 32)
    (map (fun b : byte => bv_unsigned b) (disco_classify_c.sight (c_FB c) (ho_L c))) ->
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem3) (c_out c)
     (map (fun b : byte => bv_unsigned b) (c_O c))) ->
  SRr SEGS W2 (mkCfg (mkst (fx := c_fq c) regs3
                       (Z_to_bv 64 (SIGMA AS_reac_disco_table_observe)) mem3 (seg_rom SEGS)) md3)
    (ho_post c).
Proof.
intros c fpos ly2 S2 W2 mem3 md3 k2 regs3 sp1 F H3 OP HFST HB
  Rra R10 R11 R12 R13 R19 R20 R22 R23 R26 R27 HFSH HOK3 HOKc HT400 HSK400 HOPdef HRET HGS HGO.
pose proof HB as (HPRE & HMID & HSP1 & HFeq & HRG & HSV).
pose proof HMID as (HJ & Hfrs & Hfa & Hperm & HKEPT & HROm & HGH & HLH & HFLAG).
pose proof HRG as (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R24 & R25).
pose proof HPRE as (Hj0 & Hro0 & Hra0 & Hra4 & Hgp & Htp & Hsp16 & Hwin & Hspl & Hdep &
  Hlenr & Hnowr & Houtr & Hh0' & Hh8' & Hinb & Hhb1 & Hhb2 & Hhw & HOK0 & HFBl & HGH0 & HF50 & HOUT & HKM & HKT).
pose proof HJ as (HARj & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & Hstk & _).
destruct (hoEF_spfacts c sp1 HPRE Hstk HSP1)
  as (Hsp1pos & Hsp1hi & Hsplim & Hwin8 & Hspl2 & Hsp1lo & Hsp0pos & Hsp0hi & Hceil0).
destruct (hoEF_hfacts c ly2 S2 W2 mem3 md3 HPRE HARj Hperm)
  as (Hh0 & Hh8 & Hhceil & Hceil63 & Hamr & Hraz & Hshv & Hpres & Hin2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_B_ok _ _ PI) as HBo.
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
assert (HOST : REAC_DISCO_TABLE_OBSERVE_STK = 8304) by reflexivity.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem3 md3 1 fpos HARj Hfin2) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem3 md3 1 fpos HARj Hfin2) as (HFal & HFb & HFpres & HFSpres).
destruct (frame_al64 SEGS B ly2 S2 W2 mem3 md3 1 fpos HARj Hfin2) as (Hal64 & Hbal64 & Hb64).
assert (HFA1 : frame_addr ly2 1 fpos = F) by (rewrite (Hfa 1 fpos); symmetry; exact HFeq).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp, HFpres, HFSpres, Hbal64.
rewrite HFA1 in HF4096, HFceil, HFapp, HFpres, HFSpres, Hal64.
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem3 md3 (c_hb c) (c_hn c) 1 fpos HARj Hin2 Hfin2) as HdFH.
unfold zdisjoint in HdFH. cbn [fst snd] in HdFH.
change (fs_frame_bytes 1) with 128 in HdFH. rewrite HFA1 in HdFH.
assert (Hsp3 : spZ regs3 = sp1) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (Hra3 : raZ regs3 = BASE + 29692)
by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - HBo; lia).
assert (LT3 : length (disco_table_c.sub H3 0 400) = 400%nat) by (apply HuntObsLib.len_sub; lia).
assert (HGT3 : garr8 SEGS (mrestrict (w_H W2) mem3) (c_h c)
  (map (fun b : byte => bv_unsigned b) (disco_table_c.sub H3 0 400))).
{ replace (map (fun b : byte => bv_unsigned b) (disco_table_c.sub H3 0 400))
    with (firstn 400 (skipn 0 (map (fun b : byte => bv_unsigned b) H3)))
    by (unfold disco_table_c.sub; cbn [Z.to_nat]; rewrite skipn_map, firstn_map; reflexivity).
  replace (c_h c) with (c_h c + Z.of_nat 0) by lia.
  apply (garr8_sub_x SEGS (mrestrict (w_H W2) mem3) (c_h c) _ 0 400 HGH).
  rewrite length_map. lia. }
destruct (HuntObsFacts.sight_ok (c_FB c) (ho_L c) HFBl) as [HS1 HS2].
pose proof (HuntObsFacts.sight_len (c_FB c) (ho_L c) HFBl) as HSlen.
destruct (hoEF_shadow_frame W2 mem3 F HFSH Hal64 ltac:(lia)) as [HFra HFhull].
assert (HTOK : disco_table_c.table_ok (disco_table_c.sub H3 0 400)).
{ pose proof HOK3 as (LH3 & TOK3 & _).
  replace (disco_table_c.sub H3 0 400) with (firstn 400 H3)
    by (unfold disco_table_c.sub; cbn [Z.to_nat skipn]; reflexivity).
  exact TOK3. }
destruct HTOK as (HTT1 & HTT2 & HTT3 & HTT4).
eapply SRr_bind.
{ rewrite pa_sigma_reac_disco_table_observe.
  apply (TOBS (c_fq c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
     ((1, fpos) :: c_own c) ly2 S2 W2 mem3 md3 k2 regs3 (c_h c) (F + 32) 0 (c_now c)
     (disco_table_c.sub H3 0 400) (disco_classify_c.sight (c_FB c) (ho_L c))).
  - exact HJ.
  - exact HROm.
  - rewrite Rra. apply ret_ok_codeptr_v; [clear - HBo; lia | reflexivity].
  - rewrite Hra3. clear - HBo. lia.
  - exact R3.
  - exact R4.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R13.
  - clear - HBo. lia.
  - clear - Hnowr. lia.
  - rewrite Hsp3. destruct HSP1 as (_ & _ & Hm). clear - Hm.
    rewrite Z.mod_divide in Hm by lia. destruct Hm as [q Hq].
    rewrite Z.mod_divide by lia. exists (2 * q). lia.
  - rewrite Hsp3. clear - Hwin8 Hsp1lo HOST HSTK. lia.
  - rewrite Hsp3. clear - Hspl2 Hsp1lo. lia.
  - clear - Hh0. lia.
  - exact Hh8.
  - clear - Hhceil Hceil63. lia.
  - clear - Hamr. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - right. rewrite Hsp3. clear - Hhceil Hwin8 Hsp1lo HOST HSTK Hceil0. lia.
  - intros a Ha. split.
    + apply (hoEF_awr_hunt c fpos ly2 S2 a HPRE Hfa Hperm). clear - Ha. lia.
    + apply Hpres. clear - Ha. lia.
  - apply (hoEF_ra_kept (aview SEGS (w_H W2) mem3) (aview SEGS (w_H W2) mem3) (c_h c) 400);
    [intros x Hx; reflexivity|].
    intros x Hx. apply Hraz. clear - Hx. lia.
  - intros s Hs. apply Hshv. unfold shadow_addr in Hs |- *. clear - Hs. lia.
  - exact HGT3.
  - exact LT3.
  - clear - HF4096. lia.
  - clear - HFceil Hceil63. lia.
  - clear - HFapp C1 HF4096 HFceil. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - clear - Hal64. rewrite Z.mod_divide by lia. rewrite Z.mod_divide in Hal64 by lia.
    destruct Hal64 as [q Hq]. exists (8 * q + 4). lia.
  - intros a Ha. apply (proj1 (HFpres a ltac:(clear - Ha; lia))).
  - exact HFra.
  - right. rewrite Hsp3. clear - HFceil Hwin8 Hsp1lo HOST HSTK Hceil0. lia.
  - exact HFhull.
  - exact HGS.
  - exact HSlen.
  - left. exists 1, fpos. split; [rewrite Hfrs; left; reflexivity|]. rewrite HFA1.
    change (fs_frame_bytes 1) with 128. split; clear - HF4096; lia.
  - clear - HdFH Hhb1 Hhb2 HF4096 HFceil Hh0. lia.
  - exact HTT1.
  - exact HTT2.
  - exact HTT3.
  - exact HS1.
  - exact HS2. }
cbv beta. intros W4 c4 Hwle4
  (ly4 & S4 & regs4 & mem4 & md4 & T' & ret & Hc4 & HJ4 & HP4 & Hr10 & Hfrs4 & Hperm4 & HKEPT4 &
   HGT4 & HLT4 & HGS4 & HOM & HQ1 & HQ2 & HQ3 & HQ4).
rewrite Rra in Hc4. subst c4.
destruct HKEPT4 as (T1 & T2 & T3 & T4 & T5 & T6).
rewrite Hsp3 in T1, T5, T6.
assert (HF8b : 0 <= F / 8 <= F) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (Hnf : forall a, SB <= a < SB + 17592186044416 -> ~ (c_h c <= a < c_h c + 400)).
{ intros a Ha Hb. clear - Ha Hb Hamr C1.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. unfold SB in Ha. lia. }
assert (Hdfr : forall a, F <= a < F + 128 -> ~ (c_h c <= a < c_h c + 400)).
{ intros a Ha Hb. clear - Ha Hb HdFH Hhb1 Hhb2 Hh0. lia. }
set (H4 := T' ++ skipn 400 H3) in *.
assert (Lskip : length (skipn 400 H3) = 80%nat) by (rewrite length_skipn; lia).
assert (LH4 : length H4 = 480%nat) by (unfold H4; rewrite length_app, HLT4, Lskip; reflexivity).
assert (HSK4 : skipn 400 H4 = skipn 400 H3)
by (unfold H4; apply (ho_skipn_exact T' (skipn 400 H3) 400 HLT4)).
assert (HH4eq : H4 = T' ++ skipn 400 H4) by (rewrite HSK4; reflexivity).
rewrite <- (firstn_skipn 400 (map (fun b : byte => bv_unsigned b) H3)) in HGH.
destruct (proj1 (garr8_app _ _ _ _ _) HGH) as [_ HGr3].
rewrite length_firstn, length_map, HLH in HGr3.
cbn [Init.Nat.min] in HGr3.
assert (HGrest4 : garr8 SEGS (mrestrict (w_H W4) mem4) (c_h c + Z.of_nat 400)
  (skipn 400 (map (fun b : byte => bv_unsigned b) H3))).
{ apply (hoEF_garr_keep W2 W4 mem3 mem4 (c_h c + Z.of_nat 400) _ ); [|exact HGr3].
  intros i Hi. rewrite length_skipn, length_map, HLH in Hi.
  replace (c_h c + Z.of_nat 400 + i) with (c_hb c + (c_h c + 400 + i - c_hb c)) by lia.
  apply (T2 (c_hb c) (c_hn c) (c_h c + 400 + i - c_hb c) Hin2
    ltac:(clear - Hi Hhb1 Hhb2; lia) ltac:(clear - Hi Hhb1; lia)). }
assert (HG4 : garr8 SEGS (mrestrict (w_H W4) mem4) (c_h c)
  (map (fun b : byte => bv_unsigned b) H4)).
{ unfold H4. rewrite map_app. apply garr8_app. split; [exact HGT4|].
  rewrite length_map, HLT4. rewrite skipn_map in HGrest4. exact HGrest4. }
assert (HFSH4 : ho_fsh W4 mem4 F ho_shC).
{ intros i Hi. rewrite (T4 1 fpos (SB + F / 8 + i) Hfin2
    ltac:(right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite HFA1, <- SB_SHADOW_OFF;
          change (fs_frame_bytes 1 / 8) with 16; clear - Hi; lia)
    ltac:(apply Hnf; clear - Hi HF8b HFceil C1; unfold SB; lia)).
  exact (HFSH i Hi). }
assert (HSV4 : ho_saved c W4 mem4).
{ intros j Hj. specialize (HSV j Hj). intros kk Hk.
  rewrite <- (HSV kk Hk). apply (mbyte_of_aview SEGS).
  apply (T1 (spZ (c_regs c) - 8 * (Z.of_nat j + 1) + Z.of_nat kk)
    ltac:(clear - Hj Hk Hwin8 Hsplim Hceil0 HSTK; lia)
    ltac:(clear - Hj Hk Hsp1lo HOST; lia)
    ltac:(clear - Hj Hk Hhceil Hwin8 Hceil0 HSTK; lia)). }
assert (Hfa4 : forall cid p, frame_addr ly4 cid p = frame_addr (c_lyc c) cid p).
{ intros cid p. rewrite (hoEF_fa_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 cid p).
  rewrite <- (hoEF_fa_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ cid p). apply Hfa. }
assert (Hfl4 : flag_addr ly4 1 fpos = flag_addr ly2 1 fpos).
{ rewrite (hoEF_fl_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 1 fpos).
  rewrite (hoEF_fl_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ 1 fpos). reflexivity. }
assert (HMID4 : ho_mid c fpos ly4 S4 W4 mem4 md4 k2 H4).
{ split; [exact HJ4|]. split; [rewrite Hfrs4; exact Hfrs|]. split; [exact Hfa4|].
  split; [exact (Permutation_trans Hperm4 Hperm)|].
  split; [exact (hoEF_kept_call c fpos ly2 S2 W2 W4 mem3 mem4 md3 sp1 HPRE Hstk HSP1 HARj Hperm Hfrs Hfa
                   HKEPT (conj T1 (conj T2 (conj T3 (conj T4 (conj T5 T6))))))|].
  split; [exact (hoEF_rod_keep W2 W4 mem3 mem4 HROm T3)|].
  split; [exact HG4|]. split; [exact LH4|].
  rewrite Hfa4, Hfl4, <- (Hfa 1 fpos).
  rewrite (rdword_ext (aview SEGS (w_H W2) mem3) (aview SEGS (w_H W4) mem4)
    (frame_addr ly2 1 fpos + 120)
    ltac:(intros kk Hk; apply (T4 1 fpos (frame_addr ly2 1 fpos + 120 + kk) Hfin2
            ltac:(left; unfold in_zr, frame_rng; cbn [fst snd];
                  change (fs_frame_bytes 1) with 128; clear - Hk; lia)
            ltac:(apply Hdfr; rewrite HFA1 in *; clear - Hk; lia)))).
  exact HFLAG. }
assert (HRG4 : ho_regs_mid c regs4 sp1 F).
{ split; [exact (eq_trans (hoE_pres_get regs3 regs4 2 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R2)|].
  split; [exact (eq_trans (hoE_pres_get regs3 regs4 3 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R3)|].
  split; [exact (eq_trans (hoE_pres_get regs3 regs4 4 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R4)|].
  split; [exact (eq_trans (hoE_pres_get regs3 regs4 8 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R8)|].
  split; [exact (eq_trans (hoE_pres_get regs3 regs4 9 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R9)|].
  split; [exact (eq_trans (hoE_pres_get regs3 regs4 18 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R18)|].
  split; [exact (eq_trans (hoE_pres_get regs3 regs4 21 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R21)|].
  split; [exact (eq_trans (hoE_pres_get regs3 regs4 24 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R24)|].
  exact (eq_trans (hoE_pres_get regs3 regs4 25 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R25). }
assert (HB4 : ho_base c fpos ly4 S4 W4 mem4 md4 k2 H4 regs4 sp1 F)
by (split; [exact HPRE|]; split; [exact HMID4|]; split; [exact HSP1|];
    split; [exact HFeq|]; split; [exact HRG4 | exact HSV4]).
destruct (hoE_lk c HOK0 HOKc) as [LLk LOKk].
assert (HOK4 : hunt_c.hunt_ok H4).
{ unfold H4. rewrite HSK400.
  apply (ho_hunt_ok_ok (c_H c) T' (ho_Lk' c) OP (c_now c) HOK0 HLT4
    (conj HQ1 (conj HQ2 (conj HQ3 (HQ4 HTT4)))) LLk LOKk HOPdef). }
change (SRr SEGS W4 (ho_cfg c regs4 mem4 md4 0x73fc) (ho_post c)).
apply (HFST c fpos ly4 S4 W4 mem4 md4 k2 regs4 sp1 F H4 T' ret HB4 Hr10).
- destruct (hoE_ret01 _ _ _ _ _ _ HOM) as [-> | ->]; clear; lia.
- exact (eq_trans (hoE_pres_get regs3 regs4 19 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R19).
- exact (eq_trans (hoE_pres_get regs3 regs4 20 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R20).
- exact (eq_trans (hoE_pres_get regs3 regs4 22 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R22).
- exact (eq_trans (hoE_pres_get regs3 regs4 23 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R23).
- exact (eq_trans (hoE_pres_get regs3 regs4 27 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R27).
- exact (eq_trans (hoE_pres_get regs3 regs4 26 _ HP4 ltac:(unfold acallee_saved; lia) eq_refl) R26).
- exact HFSH4.
- exact HOK4.
- exact HH4eq.
- exact HLT4.
- exact HGS4.
- rewrite <- HT400. exact HOM.
- exact HRET.
- rewrite HSK4, HSK400, HOPdef. reflexivity.
- intros Hout. destruct (HOUT Hout) as (HTO & Hdj1 & Hdj2).
  destruct HTO as (_ & _ & _ & _ & _ & _ & _ & _ & LO & HGOc & HR1).
  apply (hoEF_garr_keep W2 W4 mem3 mem4 (c_out c) _ ); [|exact (HGO Hout)].
  intros i Hi. rewrite length_map, LO in Hi.
  destruct HR1 as [(cid & pos & Hinf & Hlo & Hhi) | (b & m & Hinb2 & Hlo & Hhi)].
  + apply (T4 cid pos (c_out c + i) ltac:(rewrite Hfrs; right; exact Hinf)
      ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite (Hfa cid pos); clear - Hi Hlo Hhi; lia)
      ltac:(clear - Hi Hdj1; lia)).
  + replace (c_out c + i) with (b + (c_out c + i - b)) by lia.
    apply (T2 b m (c_out c + i - b)
      ltac:(apply (Permutation_in _ (Permutation_sym Hperm)); exact Hinb2)
      ltac:(clear - Hi Hlo Hhi; lia) ltac:(clear - Hi Hdj1 Hlo; lia)).
Qed.

Lemma hoE_open_ok : forall E m (nn : nat) lo hi wlo whi cs wlo' whi',
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  (forall o, wlo' <= o < whi' -> writable_at SEGS m (base_val E (Some nn) + o)) ->
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi wlo' whi' cs).
Proof.
intros E m nn lo hi wlo whi cs wlo' whi' (A1 & A2 & A3 & A4) HW.
split; [exact A1|]. split; [exact A2|]. split; [exact HW | exact A4].
Qed.

Ltac hoE_open HS i wlo whi tac :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
let r' := eval vm_compute in (set_window r wlo whi) in
lazymatch r with YP09.mkRegion (Some ?nn) ?lo ?hi ?wlo0 ?whi0 ?cs =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r r' HS
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (hoE_open_ok Ex (ms_mem msx) nn lo hi wlo0 whi0 cs wlo whi
     (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(tac))) as HS3;
clear HS; rename HS3 into HS end end; norm_ss HS.

Lemma ho_segE : ho_seg_E_stmt.
Proof.
unfold ho_seg_E_stmt.
intros c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F HB R19 R20 R23 R26 HFSH HRET HOKc HGS HGO.
pose proof HB as (HPRE & HMID & HSP1 & HFeq & HRG & HSV).
pose proof HMID as (HJ & Hfrs & Hfa & Hperm & HKEPT & HROm & HGH & HLH & HFLAG).
pose proof HRG as (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R24 & R25).
pose proof HPRE as (Hj0 & Hro0 & Hra0 & Hra4 & Hgp & Htp & Hsp16 & Hwin & Hspl & Hdep &
  Hlenr & Hnowr & Houtr & Hh0' & Hh8' & Hinb & Hhb1 & Hhb2 & Hhw & HOK0 & HFBl & HGH0 & HF50 & HOUT & HKM & HKT).
pose proof HJ as (HARj & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & Hstk & _).
destruct (hoEF_spfacts c sp1 HPRE Hstk HSP1)
  as (Hsp1pos & Hsp1hi & Hsplim & Hwin8 & Hspl2 & Hsp1lo & Hsp0pos & Hsp0hi & Hceil0).
destruct (hoEF_hfacts c ly2 S2 W2 mem2 md2 HPRE HARj Hperm)
  as (Hh0 & Hh8 & Hhceil & Hceil63 & Hamr & Hraz & Hshv & Hpres & Hin2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 1 fpos HARj Hfin2) as (HF4096 & HFceil & HFapp).
assert (HFA1 : frame_addr ly2 1 fpos = F) by (rewrite (Hfa 1 fpos); symmetry; exact HFeq).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp.
rewrite HFA1 in HF4096, HFceil, HFapp.
assert (Hamr2 : c_h c + 480 <= SB \/ SB + 17592186044416 <= c_h c).
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. unfold SB. clear - Hamr C1. lia. }
assert (HF8b : 0 <= F / 8 <= F)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; clear - HF4096; lia).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) 1 fpos HARj Hin2 Hfin2) as HdFH2.
unfold zdisjoint in HdFH2. cbn [fst snd] in HdFH2.
change (fs_frame_bytes 1) with 128 in HdFH2. rewrite HFA1 in HdFH2.
destruct (hoE_lk c HOK0 HOKc) as [LLk LOKk].
assert (LHc : length (ho_Hcls c) = 480%nat) by (pose proof HOKc as (X & _); exact X).
assert (L400 : length (disco_table_c.sub (c_H c) 0 400) = 400%nat)
by (apply HuntObsLib.len_sub; [lia | pose proof HOK0 as (X & _); lia]).
assert (Hsub400 : disco_table_c.sub (ho_Hcls c) 0 400 = disco_table_c.sub (c_H c) 0 400).
{ unfold ho_Hcls. unfold disco_table_c.sub at 1. cbn [Z.to_nat skipn].
  exact (ho_firstn_exact (disco_table_c.sub (c_H c) 0 400) _ 400 L400). }
assert (Hskip400 : skipn 400 (ho_Hcls c)
  = ho_Lk' c ++ disco_table_c.sub (c_H c) 412 12 ++ disco_table_c.sub (c_H c) 424 8 ++ skipn 432 (c_H c)).
{ pose proof HOK0 as (LH0 & _). destruct (ho_split480 (c_H c) LH0) as (_ & E412 & _).
  unfold ho_Hcls. rewrite (ho_skipn_exact (disco_table_c.sub (c_H c) 0 400) _ 400 L400), E412. reflexivity. }
destruct (ho_count _ (c_h c) (ho_Hcls c) HOKc HGH) as [Hn HV].
rewrite Hsub400 in Hn, HV.
assert (HAWRH : forall x, c_h c <= x < c_h c + 480 ->
  awr_byte (c_STK c) (c_sp0 c) (c_FP c) (ablocks B (c_ly c) (c_S c))
    (ablocks B ly2 S2) ly2 ((1, fpos) :: c_own c) x)
  by (intros x Hx; exact (hoEF_awr_hunt c fpos ly2 S2 x HPRE Hfa Hperm Hx)).
destruct (ho_mid_entry c fpos ly2 S2 W2 mem2 md2 k2 (ho_Hcls c) regs2 sp1 F ho_shC false 0x73b4 HB HFSH
   eq_refl ltac:(unfold ho_shC; repeat (apply Forall_cons; [lia|]); apply Forall_nil) ltac:(discriminate)) as [HS HEI].
pose (RUN := paj_run (fx := c_fq c) B LAWS).
pose (BR := paj_branch (fx := c_fq c) (PI := PI)).
assert (AG : forall m, (m < 33)%nat -> ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) m
                                     = ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) m) by reflexivity.
assert (E2x : ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 2 = Z_to_bv 64 sp1)
  by (rewrite (hoF_ereg c regs2 _ 2 2%bv ltac:(lia) ltac:(reflexivity)); exact R2).
assert (E20x : ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 20 = Z_to_bv 64 (c_now c))
  by (rewrite (hoF_ereg c regs2 _ 20 20%bv ltac:(lia) ltac:(reflexivity)); exact R20).
assert (E21x : ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 21 = Z_to_bv 64 (c_h c))
  by (rewrite (hoF_ereg c regs2 _ 21 21%bv ltac:(lia) ltac:(reflexivity)); exact R21).
assert (E23x : ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 23 = Z_to_bv 64 (F + 32))
  by (rewrite (hoF_ereg c regs2 _ 23 23%bv ltac:(lia) ltac:(reflexivity)); exact R23).
pose proof (hoF_e32 c regs2 (flag_addr (c_lyc c) 1 fpos)) as E32x.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ex ssx msx (26%bv : bv 5) (SOff 32 0) HS ltac:(vm_compute; reflexivity)
  ltac:(rewrite hoF_off0, E32x; cbn [ms_regs restrict mkst]; symmetry; exact R26)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
hoF_ro HS 1%nat. hoF_ro HS 6%nat. hoF_ro HS 7%nat. hoF_ro HS 8%nat.
add_atom HS 60%nat (Z_to_bv 64 (disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400))) E60.
rebaseE HS AG HEv. clear HEv.
ra_join_fact HS 60%nat (mkAF 0 8 0)
  ltac:(rewrite E60, unsigned_lit_small by lia;
        change (2 ^ 0) with 1; rewrite Z.mod_1_r; split; [lia|]; split; [reflexivity | lia]).
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ ?msx =>
hoEF_wc HS 8%nat 0 0 (YP09.mkChunk 384 (CVal 4 (SOff 60 0)))
  ltac:(cbn [base_val]; rewrite (AG 21%nat ltac:(lia)), E21x, unsigned_lit_small by lia;
        apply (chunk_ok_val SEGS Ex (ms_mem msx) (c_h c) 384 4 (SOff 60 0)
                 (disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400)));
        [ cbn [sv_denot]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | zside | zside | exact HV ]) end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (U2 : bv_unsigned (ew Ex 2) = sp1)
  by (rewrite (AG 2%nat ltac:(lia)), E2x; apply unsigned_lit_small; lia);
assert (U21 : bv_unsigned (ew Ex 21) = c_h c)
  by (rewrite (AG 21%nat ltac:(lia)), E21x; apply unsigned_lit_small; lia);
assert (SHOK : sh_ok SEGS HOBx (ho_SHM false) Ex (mrestrict (w_H W2) mem2)) end.
{ unfold ho_SHM. cbn [app]. apply Forall_cons; [|apply Forall_nil].
  apply (ho_shent_gen _ _ _ 21%nat (c_h c) 0 480);
  [ rewrite (AG 32%nat ltac:(lia)); exact E32x
  | rewrite (AG 21%nat ltac:(lia)); exact E21x
  | lia | lia
  | replace (c_h c + 0) with (c_h c) by lia; replace (480 - 0) with 480 by lia; exact Hamr
  | replace (c_h c + 0) with (c_h c) by lia; replace (480 - 0) with 480 by lia; exact Hraz ]. }
unfold ho_cfg.
paj_run_tok RUN HS HJ SHOK HOspan.
{ hoF_awr1 U2. }
hoF_ms MS1. hoF_hw mem2 MS1 sp1 U2 HW1. hoF_hp mem2 MS1 HP1.
psrr_branch_tok RUN BR HS SHOK HOspan.
- rewrite branch_ne_U in Hc.
  rewrite (U_atom _ 60%nat (disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400)) E60) in Hc by lia.
  rewrite U_lit in Hc by lia. apply (proj1 (negb_true_iff _)) in Hc.
  apply (proj1 (Z.eqb_neq _ _)) in Hc.
  norm_ss HS.
  paj_run_tok RUN HS HJ SHOK HOspan.
  { hoF_awr1 U2. }
  hoF_ms MS2. hoF_hw (ms_mem MS1) MS2 sp1 U2 HW2. hoF_hp (ms_mem MS1) MS2 HP2.
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 56) ->
    aview SEGS (w_H W2) (ms_mem MS2) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha Hs; rewrite (HW2 a Ha Hs); exact (HW1 a Ha Hs)).
  assert (HP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem MS2) a)
    by (intros a Ha; exact (HP2 a (HP1 a Ha))).
  assert (HG2 : garr8 SEGS (mrestrict (w_H W2) (ms_mem MS2)) (c_h c)
    (map (fun b : byte => bv_unsigned b) (ho_Hcls c))).
  { apply (hoF_garr_ext W2 mem2 (ms_mem MS2)); [|exact HGH].
    intros i Hi. rewrite length_map, LHc in Hi. change (Z.of_nat 480) with 480 in Hi. apply HW; clear - Hi Hh0 Hhceil Hceil63 Hceil0 Hwin8 HSTK Hsp1lo; lia. }
  assert (Q2 : getr (ms_regs MS2) 2 = getr regs2 2) by hoF_same HS AG hoF_ereg (2%bv : bv 5) 2%nat.
  assert (Q3 : getr (ms_regs MS2) 3 = getr regs2 3) by hoF_same HS AG hoF_ereg (3%bv : bv 5) 3%nat.
  assert (Q4 : getr (ms_regs MS2) 4 = getr regs2 4) by hoF_same HS AG hoF_ereg (4%bv : bv 5) 4%nat.
  assert (Q8 : getr (ms_regs MS2) 8 = getr regs2 8) by hoF_same HS AG hoF_ereg (8%bv : bv 5) 8%nat.
  assert (Q9 : getr (ms_regs MS2) 9 = getr regs2 9) by hoF_same HS AG hoF_ereg (9%bv : bv 5) 9%nat.
  assert (Q18 : getr (ms_regs MS2) 18 = getr regs2 18) by hoF_same HS AG hoF_ereg (18%bv : bv 5) 18%nat.
  assert (Q19 : getr (ms_regs MS2) 19 = getr regs2 19) by hoF_same HS AG hoF_ereg (19%bv : bv 5) 19%nat.
  assert (Q20 : getr (ms_regs MS2) 20 = getr regs2 20) by hoF_same HS AG hoF_ereg (20%bv : bv 5) 20%nat.
  assert (Q21 : getr (ms_regs MS2) 21 = getr regs2 21) by hoF_same HS AG hoF_ereg (21%bv : bv 5) 21%nat.
  assert (Q23 : getr (ms_regs MS2) 23 = getr regs2 23) by hoF_same HS AG hoF_ereg (23%bv : bv 5) 23%nat.
  assert (Q24 : getr (ms_regs MS2) 24 = getr regs2 24) by hoF_same HS AG hoF_ereg (24%bv : bv 5) 24%nat.
  assert (Q25 : getr (ms_regs MS2) 25 = getr regs2 25) by hoF_same HS AG hoF_ereg (25%bv : bv 5) 25%nat.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdX) _ =>
  apply (hoE_call c fpos ly2 S2 W2 (ms_mem MS2) mdX k2 (ms_regs MS2) sp1 F (ho_Hcls c)
           (disco_table_c.sub (c_H c) 424 8) ho_segF) end.
  + split; [exact HPRE|]. split;
    [ exact (hoE_mid_step c fpos ly2 S2 W2 mem2 md2 (ms_mem MS2) _ k2 (ho_Hcls c) (ho_Hcls c) sp1
               HPRE HSP1 HMID HJ ltac:(intros a Ha _ Hs; apply HW; [exact Ha | clear - Hs Hsp1lo HSTK; lia]) HP
               ltac:(intros a Ha; apply HP; apply Hpresj; clear - Ha Hwin8 Hspl2 HSTK; lia) HG2 LHc) |].
    split; [exact HSP1|]. split; [exact HFeq|]. split.
    * split; [rewrite Q2; exact R2|].
      split; [rewrite Q3; exact R3|].
      split; [rewrite Q4; exact R4|].
      split; [rewrite Q8; exact R8|].
      split; [rewrite Q9; exact R9|].
      split; [rewrite Q18; exact R18|].
      split; [rewrite Q21; exact R21|].
      split; [rewrite Q24; exact R24|].
      rewrite Q25; exact R25.
    * intros j Hj. apply (hoF_val_mem_ext W2 mem2 (ms_mem MS2)); [|exact (HSV j Hj)].
      intros kk Hk. apply HW; clear - Hj Hk Hwin8 Hsp1lo HSTK Hsplim Hceil0 Hceil63 C1; lia.
  + let Hr := fresh "Hr" in hoF_rd HS (1%bv : bv 5) Hr; rewrite Hr;
    lazymatch goal with |- sv_denot ?Ex _ = _ =>
      lazymatch goal with Hx : img_env _ _ Ex |- _ => exact (codeptr_val Ex 29692 Hx) end end.
  + let Hr := fresh "Hr" in hoF_rd HS (10%bv : bv 5) Hr;
    rewrite Hr, hoF_off0, (AG 21%nat ltac:(lia)); exact E21x.
  + let Hr := fresh "Hr" in hoF_rd HS (11%bv : bv 5) Hr;
    rewrite Hr, hoF_off0, (AG 23%nat ltac:(lia)); exact E23x.
  + let Hr := fresh "Hr" in hoF_rd HS (12%bv : bv 5) Hr; rewrite Hr; reflexivity.
  + let Hr := fresh "Hr" in hoF_rd HS (13%bv : bv 5) Hr;
    rewrite Hr, hoF_off0, (AG 20%nat ltac:(lia)); exact E20x.
  + rewrite Q19; exact R19.
  + rewrite Q20; exact R20.
  + let Hr := fresh "Hr" in hoF_rd HS (22%bv : bv 5) Hr; rewrite Hr.
    cbn [sv_denot]. rewrite (AG 21%nat ltac:(lia)), E21x, unsigned_lit_small by lia. reflexivity.
  + rewrite Q23; exact R23.
  + let Hr := fresh "Hr" in hoF_rd HS (26%bv : bv 5) Hr;
    rewrite Hr, hoF_off0, (AG 32%nat ltac:(lia)); exact E32x.
  + let Hr := fresh "Hr" in hoF_rd HS (27%bv : bv 5) Hr; rewrite Hr.
    rewrite (hoF_u_shadow _ 21 32 (c_h c) 384 SB ltac:(rewrite (AG 21%nat ltac:(lia)); exact E21x)
      ltac:(rewrite (AG 32%nat ltac:(lia)); exact E32x)) by (unfold SB; lia).
    reflexivity.
  + intros i Hi. rewrite HW;
    [ exact (HFSH i Hi)
    | unfold SB; clear - Hi Hwin8 Hsp1lo HSTK Hceil0 Hceil63 C1 HF4096 HFceil HF8b; lia
    | unfold SB; clear - Hi Hwin8 Hsp1lo HSTK Hceil0 Hceil63 C1 HF4096 HFceil HF8b; lia].
  + exact HOKc.
  + exact HOKc.
  + exact Hsub400.
  + rewrite Hskip400. destruct (Z.eqb_spec (disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400)) 0)
      as [He | _]; [exfalso; exact (Hc He) | reflexivity].
  + destruct (Z.eqb_spec (disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400)) 0)
      as [He | _]; [exfalso; exact (Hc He) | reflexivity].
  + exact HRET.
  + apply (hoF_garr_ext W2 mem2 (ms_mem MS2)); [|exact HGS].
    intros i Hi. rewrite length_map, (HuntObsFacts.sight_len (c_FB c) (ho_L c) HFBl) in Hi.
    change (Z.of_nat 24) with 24 in Hi.
    apply HW; clear - Hi Hwin8 Hsp1lo HSTK Hceil0 Hceil63 C1 HF4096 HFceil; lia.
  + intros Hout. apply (hoF_garr_ext W2 mem2 (ms_mem MS2)); [|exact (HGO Hout)].
    intros i Hi. destruct (HOUT Hout) as (HTO & _ & _).
    destruct HTO as (_ & Hout63 & _ & Hoff & _ & _ & _ & _ & LO & _ & _).
    rewrite length_map, LO in Hi. change (Z.of_nat 24) with 24 in Hi. apply HW; clear - Hi Hout63 Hoff Houtr Hwin8 Hsp1lo HSTK Hceil0 Hceil63 C1; lia.
- rewrite branch_ne_U in Hc.
  rewrite (U_atom _ 60%nat (disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400)) E60) in Hc by lia.
  rewrite U_lit in Hc by lia. apply (proj1 (negb_false_iff _)) in Hc.
  apply (proj1 (Z.eqb_eq _ _)) in Hc.
  norm_ss HS.
  hoE_open HS 8%nat 424 432
    ltac:(intros o Ho; cbn [base_val];
          rewrite (AG 21%nat ltac:(lia)), E21x, unsigned_lit_small by lia;
          apply (apresent_writable SEGS); apply HP1; apply Hpres; clear - Ho; lia).
  paj_run_tok RUN HS HJ SHOK HOspan.
  { hoEF_awrtac AG E2x E21x HAWRH. }
  hoF_ms MS2.
  assert (HW2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 56) ->
    ~ (c_h c + 424 <= a < c_h c + 432) ->
    aview SEGS (w_H W2) (ms_mem MS2) a = aview SEGS (w_H W2) (ms_mem MS1) a).
  { intros a Ha Hs Hh.
    lazymatch goal with HFx : frame_of _ _ (mrestrict (w_H W2) (ms_mem MS1)) (mrestrict _ (ms_mem MS2)) |- _ =>
      apply (hoF_aview_frame _ _ W2 (ms_mem MS1) (ms_mem MS2) a HFx Ha) end.
    intros (rg & Hrg & Hrng). cbn [ss_mem In] in Hrg.
    repeat (destruct Hrg as [<- | Hrg];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng; rewrite ?U2, ?U21 in Hrng;
       clear - Hrng Hs Hh; lia | ]).
    destruct Hrg. }
  hoF_hp (ms_mem MS1) MS2 HP2.
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 56) ->
    ~ (c_h c + 424 <= a < c_h c + 432) ->
    aview SEGS (w_H W2) (ms_mem MS2) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha Hs Hh; rewrite (HW2 a Ha Hs Hh); apply HW1; [exact Ha | exact Hs]).
  assert (HP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem MS2) a)
    by (intros a Ha; exact (HP2 a (HP1 a Ha))).
  lazymatch type of HS with
  | st_ok _ ?Ex ?ssx ?msx =>
    pose proof (st_ok_region_nth Ex ssx msx 8%nat
      (YP09.mkRegion (Some 21%nat) 0 480 424 432
        [YP09.mkChunk 424 (CVal 8 (SOff 20 0)); YP09.mkChunk 384 (CVal 4 (SOff 60 0))]) HS
      ltac:(vm_compute; reflexivity)) as HR21;
    assert (HVal : val_mem SEGS (mrestrict (w_H W2) (ms_mem MS2)) (c_h c + 424) 8 (c_now c))
      by (exact (field_of_region Ex (ms_mem msx) 21%nat (c_h c) _ 0 480 424 432 424 8 (SOff 20 0) (c_now c)
           HR21 U21 ltac:(left; reflexivity)
           ltac:(rewrite hoF_off0, (AG 20%nat ltac:(lia)); exact E20x)
           ltac:(clear - Hnowr; cbn [Z.of_N N.mul]; lia) ltac:(cbn; lia)))
  | st_ok_pi _ _ ?Ex ?ssx ?msx =>
    pose proof (st_ok_pi_region_nth Ex ssx msx 8%nat
      (YP09.mkRegion (Some 21%nat) 0 480 424 432
        [YP09.mkChunk 424 (CVal 8 (SOff 20 0)); YP09.mkChunk 384 (CVal 4 (SOff 60 0))]) HS
      ltac:(vm_compute; reflexivity)) as HR21;
    assert (HVal : val_mem SEGS (mrestrict (w_H W2) (ms_mem MS2)) (c_h c + 424) 8 (c_now c))
      by (exact (field_of_region Ex (ms_mem msx) 21%nat (c_h c) _ 0 480 424 432 424 8 (SOff 20 0) (c_now c)
           HR21 U21 ltac:(left; reflexivity)
           ltac:(rewrite hoF_off0, (AG 20%nat ltac:(lia)); exact E20x)
           ltac:(clear - Hnowr; cbn [Z.of_N N.mul]; lia) ltac:(cbn; lia)))
  end.
  assert (HG424 : garr8 SEGS (mrestrict (w_H W2) (ms_mem MS2)) (c_h c + 424)
    (map (fun b : byte => bv_unsigned b) (Mem.le8 (Z_to_bv 64 (c_now c)))))
    by (apply hoE_garr8_of_val8; [clear - Hnowr; lia | exact HVal]).
  pose proof HOK0 as (LH0 & _).
  destruct (ho_split480 (c_H c) LH0) as (_ & _ & _ & _ & L412 & L424 & L432).
  rewrite (hoE_splitH c HOK0 LLk), !map_app in HGH.
  destruct (proj1 (garr8_app _ _ _ _ _) HGH) as [G1 Hr1]. rewrite length_map, L400 in Hr1.
  destruct (proj1 (garr8_app _ _ _ _ _) Hr1) as [G2 Hr2]. rewrite length_map, LLk in Hr2.
  destruct (proj1 (garr8_app _ _ _ _ _) Hr2) as [G3 Hr3]. rewrite length_map, L412 in Hr3.
  destruct (proj1 (garr8_app _ _ _ _ _) Hr3) as [G4 G5]. rewrite length_map, L424 in G5.
  set (H3 := disco_table_c.sub (c_H c) 0 400 ++ ho_Lk' c ++ disco_table_c.sub (c_H c) 412 12 ++
             Mem.le8 (Z_to_bv 64 (c_now c)) ++ skipn 432 (c_H c)) in *.
  assert (LH3 : length H3 = 480%nat)
    by (unfold H3; rewrite !length_app, L400, LLk, L412, L432, Mem.length_le8; reflexivity).
  assert (HG3 : garr8 SEGS (mrestrict (w_H W2) (ms_mem MS2)) (c_h c)
    (map (fun b : byte => bv_unsigned b) H3)).
  { unfold H3. apply (ho_garr8_cat5 _ (c_h c) _ _ _ _ _ L400 LLk L412 (Mem.length_le8 _)).
    - apply (hoF_garr_ext W2 mem2 (ms_mem MS2)); [|exact G1].
      intros i Hi. rewrite length_map, L400 in Hi. change (Z.of_nat 400) with 400 in Hi.
      apply HW; clear - Hi Hh0 Hhceil Hceil63 Hceil0 Hwin8 HSTK Hsp1lo; lia.
    - apply (hoF_garr_ext W2 mem2 (ms_mem MS2)); [|replace (c_h c + 400) with (c_h c + Z.of_nat 400) by lia; exact G2].
      intros i Hi. rewrite length_map, LLk in Hi. change (Z.of_nat 12) with 12 in Hi.
      apply HW; clear - Hi Hh0 Hhceil Hceil63 Hceil0 Hwin8 HSTK Hsp1lo; lia.
    - apply (hoF_garr_ext W2 mem2 (ms_mem MS2));
      [|replace (c_h c + 412) with (c_h c + Z.of_nat 400 + Z.of_nat 12) by lia; exact G3].
      intros i Hi. rewrite length_map, L412 in Hi. change (Z.of_nat 12) with 12 in Hi.
      apply HW; clear - Hi Hh0 Hhceil Hceil63 Hceil0 Hwin8 HSTK Hsp1lo; lia.
    - exact HG424.
    - apply (hoF_garr_ext W2 mem2 (ms_mem MS2));
      [|replace (c_h c + 432) with (c_h c + Z.of_nat 400 + Z.of_nat 12 + Z.of_nat 12 + Z.of_nat 8) by lia; exact G5].
      intros i Hi. rewrite length_map, L432 in Hi. change (Z.of_nat 48) with 48 in Hi.
      apply HW; clear - Hi Hh0 Hhceil Hceil63 Hceil0 Hwin8 HSTK Hsp1lo; lia. }
  assert (HOK3 : hunt_c.hunt_ok H3).
  { unfold H3. apply (ho_hunt_ok_ok (c_H c) (disco_table_c.sub (c_H c) 0 400) (ho_Lk' c)
      (Mem.le8 (Z_to_bv 64 (c_now c))) (c_now c) HOK0 L400
      ltac:(pose proof HOK0 as (_ & TOK & _); unfold disco_table_c.sub; cbn [Z.to_nat skipn]; exact TOK)
      LLk LOKk ltac:(rewrite Hc; reflexivity)). }
  assert (Q2 : getr (ms_regs MS2) 2 = getr regs2 2) by hoF_same HS AG hoF_ereg (2%bv : bv 5) 2%nat.
  assert (Q3 : getr (ms_regs MS2) 3 = getr regs2 3) by hoF_same HS AG hoF_ereg (3%bv : bv 5) 3%nat.
  assert (Q4 : getr (ms_regs MS2) 4 = getr regs2 4) by hoF_same HS AG hoF_ereg (4%bv : bv 5) 4%nat.
  assert (Q8 : getr (ms_regs MS2) 8 = getr regs2 8) by hoF_same HS AG hoF_ereg (8%bv : bv 5) 8%nat.
  assert (Q9 : getr (ms_regs MS2) 9 = getr regs2 9) by hoF_same HS AG hoF_ereg (9%bv : bv 5) 9%nat.
  assert (Q18 : getr (ms_regs MS2) 18 = getr regs2 18) by hoF_same HS AG hoF_ereg (18%bv : bv 5) 18%nat.
  assert (Q19 : getr (ms_regs MS2) 19 = getr regs2 19) by hoF_same HS AG hoF_ereg (19%bv : bv 5) 19%nat.
  assert (Q20 : getr (ms_regs MS2) 20 = getr regs2 20) by hoF_same HS AG hoF_ereg (20%bv : bv 5) 20%nat.
  assert (Q21 : getr (ms_regs MS2) 21 = getr regs2 21) by hoF_same HS AG hoF_ereg (21%bv : bv 5) 21%nat.
  assert (Q23 : getr (ms_regs MS2) 23 = getr regs2 23) by hoF_same HS AG hoF_ereg (23%bv : bv 5) 23%nat.
  assert (Q24 : getr (ms_regs MS2) 24 = getr regs2 24) by hoF_same HS AG hoF_ereg (24%bv : bv 5) 24%nat.
  assert (Q25 : getr (ms_regs MS2) 25 = getr regs2 25) by hoF_same HS AG hoF_ereg (25%bv : bv 5) 25%nat.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdX) _ =>
  apply (hoE_call c fpos ly2 S2 W2 (ms_mem MS2) mdX k2 (ms_regs MS2) sp1 F H3
           (Mem.le8 (Z_to_bv 64 (c_now c))) ho_segF) end.
  + split; [exact HPRE|]. split;
    [ exact (hoE_mid_step c fpos ly2 S2 W2 mem2 md2 (ms_mem MS2) _ k2 (ho_Hcls c) H3 sp1
               HPRE HSP1 HMID HJ
               ltac:(intros a Ha Hr Hs; apply HW;
                     [exact Ha | clear - Hs Hsp1lo HSTK; lia | exact Hr]) HP
               ltac:(intros a Ha; apply HP; apply Hpresj; clear - Ha Hwin8 Hspl2 HSTK; lia) HG3 LH3) |].
    split; [exact HSP1|]. split; [exact HFeq|]. split.
    * split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|].
      split; [rewrite Q4; exact R4|]. split; [rewrite Q8; exact R8|].
      split; [rewrite Q9; exact R9|]. split; [rewrite Q18; exact R18|].
      split; [rewrite Q21; exact R21|]. split; [rewrite Q24; exact R24|].
      rewrite Q25; exact R25.
    * intros j Hj. apply (hoF_val_mem_ext W2 mem2 (ms_mem MS2)); [|exact (HSV j Hj)].
      intros kk Hk. apply HW;
      clear - Hj Hk Hwin8 Hsp1lo HSTK Hsplim Hceil0 Hceil63 C1 Hhceil Hh0; lia.
  + let Hr := fresh "Hr" in hoF_rd HS (1%bv : bv 5) Hr; rewrite Hr;
    lazymatch goal with |- sv_denot ?Ex _ = _ =>
      lazymatch goal with Hx : img_env _ _ Ex |- _ => exact (codeptr_val Ex 29692 Hx) end end.
  + let Hr := fresh "Hr" in hoF_rd HS (10%bv : bv 5) Hr;
    rewrite Hr, hoF_off0, (AG 21%nat ltac:(lia)); exact E21x.
  + let Hr := fresh "Hr" in hoF_rd HS (11%bv : bv 5) Hr;
    rewrite Hr, hoF_off0, (AG 23%nat ltac:(lia)); exact E23x.
  + let Hr := fresh "Hr" in hoF_rd HS (12%bv : bv 5) Hr; rewrite Hr; reflexivity.
  + let Hr := fresh "Hr" in hoF_rd HS (13%bv : bv 5) Hr;
    rewrite Hr, hoF_off0, (AG 20%nat ltac:(lia)); exact E20x.
  + rewrite Q19; exact R19.
  + rewrite Q20; exact R20.
  + let Hr := fresh "Hr" in hoF_rd HS (22%bv : bv 5) Hr; rewrite Hr.
    cbn [sv_denot]. rewrite (AG 21%nat ltac:(lia)), E21x, unsigned_lit_small by lia. reflexivity.
  + rewrite Q23; exact R23.
  + let Hr := fresh "Hr" in hoF_rd HS (26%bv : bv 5) Hr;
    rewrite Hr, hoF_off0, (AG 32%nat ltac:(lia)); exact E32x.
  + let Hr := fresh "Hr" in hoF_rd HS (27%bv : bv 5) Hr; rewrite Hr.
    rewrite (hoF_u_shadow _ 21 32 (c_h c) 384 SB ltac:(rewrite (AG 21%nat ltac:(lia)); exact E21x)
      ltac:(rewrite (AG 32%nat ltac:(lia)); exact E32x)) by (unfold SB; lia).
    reflexivity.
  + intros i Hi. rewrite HW;
    [ exact (HFSH i Hi)
    | unfold SB; clear - Hi Hwin8 Hsp1lo HSTK Hceil0 Hceil63 C1 HF4096 HFceil HF8b; lia
    | unfold SB; clear - Hi Hwin8 Hsp1lo HSTK Hceil0 Hceil63 C1 HF4096 HFceil HF8b; lia
    | unfold SB in *; clear - Hi Hamr2 Hh0 Hhceil C1 HF4096 HFceil HF8b; lia ].
  + exact HOK3.
  + exact HOKc.
  + unfold H3. exact (ho_firstn_exact (disco_table_c.sub (c_H c) 0 400) _ 400 L400).
  + unfold H3. rewrite (ho_skipn_exact (disco_table_c.sub (c_H c) 0 400) _ 400 L400).
    destruct (Z.eqb_spec (disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400)) 0)
      as [_ | Hne]; [reflexivity | exfalso; exact (Hne Hc)].
  + destruct (Z.eqb_spec (disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400)) 0)
      as [_ | Hne]; [reflexivity | exfalso; exact (Hne Hc)].
  + exact HRET.
  + apply (hoF_garr_ext W2 mem2 (ms_mem MS2)); [|exact HGS].
    intros i Hi. rewrite length_map, (HuntObsFacts.sight_len (c_FB c) (ho_L c) HFBl) in Hi.
    change (Z.of_nat 24) with 24 in Hi.
    apply HW;
    [ clear - Hi Hwin8 Hsp1lo HSTK Hceil0 Hceil63 C1 HF4096 HFceil; lia
    | clear - Hi Hwin8 Hsp1lo HSTK Hceil0 Hceil63 C1 HF4096 HFceil; lia
    | clear - Hi HdFH2 Hhb1 Hhb2 HF4096 HFceil Hh0; lia ].
  + intros Hout. apply (hoF_garr_ext W2 mem2 (ms_mem MS2)); [|exact (HGO Hout)].
    intros i Hi. destruct (HOUT Hout) as (HTO & Hdj1 & _).
    destruct HTO as (_ & Hout63 & _ & Hoff & _ & _ & _ & _ & LO & _ & _).
    rewrite length_map, LO in Hi. change (Z.of_nat 24) with 24 in Hi.
    apply HW;
    [ clear - Hi Hout63 Hoff Houtr Hwin8 Hsp1lo HSTK Hceil0 Hceil63 C1; lia
    | clear - Hi Hout63 Hoff Houtr Hwin8 Hsp1lo HSTK Hceil0 Hceil63 C1; lia
    | clear - Hi Hdj1 Hh0; lia ].
Qed.

End h.
End f.
End d.
