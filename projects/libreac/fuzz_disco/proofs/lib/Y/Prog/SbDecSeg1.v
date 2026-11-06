(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:49-57;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACan.v:337-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-147, 156-161;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:193-195, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg1.v, with its module paths, module names and numbers changed; 459 of its 550 lines of code are new or changed and 365 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC81 YC45 YC85 YCkd YC1i YCbf YCj1 YCjr YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh SbDec SbDecCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma sbd1_sh8 : forall a, 0 <= a -> shadow_addr a / 8 = 268431360 + a / 64.
Proof. intros a Ha. unfold shadow_addr, SHADOW_OFF. lia. Qed.
Lemma sbd1_hull_bytes : forall (rd : Z -> option Z) x n, 0 <= x -> 0 < n ->
  (forall a, x <= a < x + n -> shadow_hull_vis rd a 1) -> shadow_hull_vis rd x n.
Proof.
intros rd x n Hx Hn H s Hs.
rewrite (sbd1_sh8 x Hx), (sbd1_sh8 (x + n - 1)) in Hs by lia.
assert (Hs8 : 8 * (s / 8) <= s < 8 * (s / 8) + 8)
  by (pose proof (Z.mod_pos_bound s 8 ltac:(lia)); pose proof (Z.div_mod s 8 ltac:(lia)); lia).
assert (Hu1 : x / 64 <= s / 8 - 268431360) by lia.
assert (Hu2 : s / 8 - 268431360 <= (x + n - 1) / 64) by lia.
pose proof (Z.mul_div_le (x + n - 1) 64 ltac:(lia)) as D.
set (u := s / 8 - 268431360) in *.
assert (Ha64 : Z.max x (64 * u) / 64 = u).
{ destruct (Z.le_ge_cases x (64 * u)) as [Hle | Hge].
  - rewrite Z.max_r by exact Hle. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
  - rewrite Z.max_l by lia. assert (u <= x / 64) by (apply Z.div_le_lower_bound; lia). lia. }
apply (H (Z.max x (64 * u))); [lia|].
replace (Z.max x (64 * u) + 1 - 1) with (Z.max x (64 * u)) by lia.
rewrite (sbd1_sh8 (Z.max x (64 * u))) by lia. rewrite Ha64. unfold u. lia.
Qed.
Lemma sbd1_stk_arith : forall lo hi a s, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= a < hi ->
  shadow_addr a / 8 * 8 <= s < shadow_addr a / 8 * 8 + 8 ->
  s = shadow_of_addr SHADOW_OFF lo + (s - shadow_of_addr SHADOW_OFF lo) /\
  0 <= s - shadow_of_addr SHADOW_OFF lo < (hi - lo) / 8.
Proof. intros lo hi a s H1 H2 H3 H4. unfold shadow_of_addr, shadow_addr, SHADOW_OFF in *. split; [lia|]. lia. Qed.
Lemma sbd1_stk_arith2 : forall lo hi y, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= y < hi ->
  shadow_of_addr SHADOW_OFF y = shadow_of_addr SHADOW_OFF lo + (y / 8 - lo / 8) /\ 0 <= y / 8 - lo / 8 < (hi - lo) / 8.
Proof. intros lo hi y H1 H2 H3. unfold shadow_of_addr. split; [lia|]. lia. Qed.
Lemma sbd1_frame_arith : forall f bs y, f mod 64 = 0 -> bs mod 64 = 0 -> f <= y < f + bs ->
  in_zr (shadow_of_addr SHADOW_OFF y) (shadow_addr f, bs / 8).
Proof. intros f bs y H1 H2 H3. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. lia. Qed.
Lemma sbd1_awr_cons : forall STK sp0 FP bl0 blc ly own c a,
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly (c :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own c a [H | [H | [H | (cid & pos & Hin & Hr)]]].
- left. exact H.
- right. left. exact H.
- right. right. left. exact H.
- right. right. right. exists cid, pos. split; [right; exact Hin | exact Hr].
Qed.
Lemma sbd1_D_len : forall v md, (1 <= length (sb_dec_c.sb_dec_D v md))%nat.
Proof.
intros v md. unfold sb_dec_c.sb_dec_D. cbv zeta. rewrite length_rev.
destruct (Z.of_nat (length (sb_dec_c.sb_dec_lsd v 3)) <? md); [rewrite length_app|];
cbn [sb_dec_c.sb_dec_lsd length]; lia.
Qed.
Lemma sbd1_regs_pres : forall (regsT regs2 : bvmap 5 word), aregs_preserved regsT regs2 ->
  getr regs2 2 = getr regsT 2 /\ getr regs2 3 = getr regsT 3 /\ getr regs2 4 = getr regsT 4 /\
  getr regs2 8 = getr regsT 8 /\ getr regs2 9 = getr regsT 9 /\ getr regs2 19 = getr regsT 19 /\
  getr regs2 20 = getr regsT 20 /\ getr regs2 21 = getr regsT 21 /\ getr regs2 22 = getr regsT 22 /\
  getr regs2 27 = getr regsT 27.
Proof.
intros regsT regs2 HP.
split; [exact (HP 2 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 3 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 4 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 8 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 9 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 19 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 20 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 21 ltac:(unfold acallee_saved; lia))|].
split; [exact (HP 22 ltac:(unfold acallee_saved; lia))|].
exact (HP 27 ltac:(unfold acallee_saved; lia)).
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma sbd1_frame_low : forall f bs a, 4096 <= f -> 0 <= bs -> f + bs <= alloc_ceiling ->
  (in_zr a (f, bs) \/ in_zr a (shadow_addr f, bs / 8)) -> 0 <= a < alloc_ceiling.
Proof.
intros f bs a H1 H2 H3 Ha. pose proof asan_consts as (C1 & _).
unfold in_zr, shadow_addr, SHADOW_OFF in Ha. cbn [fst snd] in Ha. destruct Ha as [Ha | Ha]; lia.
Qed.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma sbd1_acc_pos : forall X : sbd_in, 0 < sbd_room X -> 0 < sbd_acc X.
Proof.
intros X H. pose proof (sbd1_D_len (si_v X) (si_md X)) as HL.
unfold sbd_acc, sbd_room in *. unfold sb_dec_c.sb_dec_acc. lia.
Qed.
Lemma sbd1_kept_frame : forall E rs H (m m' : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_wrange E rs a -> lo <= a < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' lo hi HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma sbd1_frame_of_region : forall (X : sbd_in) E m lo hi wlo whi cs,
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = sbd_SP X ->
  (forall j r, nth_error sbd_saved_regs j = Some r ->
     In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  (forall r, 0 <= r < 32 -> ew E (Z.to_nat r) = getr (si_regs X) (Z_to_bv 5 r)) ->
  sbd_frame X m.
Proof.
intros X E m lo hi wlo whi cs HR Hsp Hin Hew. unfold sbd_frame. intros j r Hj.
assert (Hr : 0 <= r < 32).
{ apply nth_error_In in Hj. unfold sbd_saved_regs in Hj. cbn [In] in Hj. lia. }
replace (sbd_SP X - 8 - 8 * Z.of_nat j) with (sbd_SP X + (-8 - 8 * Z.of_nat j)) by lia.
apply (slot_of_region E m (sbd_SP X) cs lo hi wlo whi (-8 - 8 * Z.of_nat j) (SOff (Z.to_nat r) 0)
  (bv_unsigned (getr (si_regs X) (Z_to_bv 5 r))) HR Hsp (Hin j r Hj)).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite (Hew r Hr). symmetry. apply Z_to_bv_bv_unsigned.
- apply bv_unsigned_in_range.
Qed.
Definition sbd1_regions : smem :=
  [stack_region 128; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33].
Definition sbd1_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0)] [] [].
Definition ss_sbd1 : sstate := mkSS AF_both3_sb_dec sr_atoms sbd1_regions None sbd1_facts.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 0.
Hypothesis TLF : PALibF B.
Hypothesis SMP : stack_malloc_progressP B.
Lemma sbd1_byte : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k S2 mem2 md2 a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR SEGS B lyc S2 W mem2 md2 ->
  ablocks B lyc S2 = ablocks B lyc Sc ->
  (forall c, In c (frames Sc) -> In c (frames S2)) ->
  (forall cid pos y, In (cid, pos) (frames Sc) ->
     in_zr y (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview SEGS (w_H W) mem2 y = aview SEGS (w_H W) memc y) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  a < kLowMemEnd \/ kHighMemBeg <= a ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF a 1 ->
  range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF a 1 /\ shadow_hull_vis (aview SEGS (w_H W) mem2) a 1.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem2 md2 a HJ HAR2 Eab Hfin Hfk Hw Hzone Hra.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as (_ & Hc).
destruct Hc as [(Hac & Hsw) | [(Happ & b & n & Hin & Hr & _) | (cid & pos & Hown & [(Happ & Hr) | (Hsh & _)])]].
- pose proof (am_layout B lyc S2 _ (proj1 HAR2)) as HLY.
  pose proof (lo_top lyc HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg). unfold page_aligned in Lplo, Lphi.
  pose proof (al_zshadow _ _ LAWS lyc S2 W mem2 md2 (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR2
    ltac:(left; reflexivity)) as Hz.
  cbn [fst snd] in Hz. unfold zero_shadow in Hz.
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  assert (Hin : ly_stk_lo lyc <= a < ly_stk_hi lyc) by lia.
  split.
  + intros y Hy. exists 0. split; [|left; reflexivity].
    destruct (sbd1_stk_arith2 (ly_stk_lo lyc) (ly_stk_hi lyc) y Lplo Lphi ltac:(lia)) as (Ey & Ry).
    rewrite Ey. apply Hz. exact Ry.
  + intros s Hs. replace (a + 1 - 1) with a in Hs by lia.
    destruct (sbd1_stk_arith (ly_stk_lo lyc) (ly_stk_hi lyc) a s Lplo Lphi Hin Hs) as (Es & Rs).
    rewrite Es. rewrite Hz by exact Rs. discriminate.
- rewrite <- Eab in Hin. split.
  + exact (range_addressable_of_block SEGS B LAWS lyc S2 W mem2 md2 b n a 1 HAR2 Hin ltac:(lia) ltac:(lia)).
  + exact (shadow_hull_vis_of_block SEGS B LAWS lyc S2 W mem2 md2 b n a 1 HAR2 Hin ltac:(lia) ltac:(lia) ltac:(lia)).
- assert (Hc : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  destruct (frame_al64 SEGS B lyc Sc W memc mdc cid pos HAR Hc) as (Hfal & Hbal & Hb64).
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
  split.
  + apply (range_addressable_agree (aview SEGS (w_H W) memc) (aview SEGS (w_H W) mem2) SHADOW_OFF a 1); [|exact Hra].
    intros y Hy. apply (Hfk cid pos _ Hc). apply sbd1_frame_arith; [exact Hfal | exact Hbal | lia].
  + exact (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W mem2 md2 cid pos a 1 HAR2 (Hfin _ Hc)
      ltac:(lia) ltac:(lia) ltac:(lia)).
- exfalso. lia.
Qed.
Lemma sbd1_triple : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k S2 mem2 md2 pos x n,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc S2 W mem2 md2 k ->
  ablocks B lyc S2 = ablocks B lyc Sc -> frames S2 = (0, pos) :: frames Sc ->
  (forall cid p y, In (cid, p) (frames Sc) ->
     in_zr y (shadow_addr (frame_addr lyc cid p), fs_frame_bytes cid / 8) ->
     aview SEGS (w_H W) mem2 y = aview SEGS (w_H W) memc y) ->
  0 <= x -> 0 < n -> amem_range x n ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF x n ->
  (forall a, x <= a < x + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF x n /\ shadow_hull_vis (aview SEGS (w_H W) mem2) x n /\
  (forall a, x <= a < x + n ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S2) lyc ((0, pos) :: own) a /\ apresent (w_H W) mem2 a).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem2 md2 pos x n HJ HJ2 Eab Efr Hfk Hx Hn Ham Hra Hw.
assert (Hfin : forall c, In c (frames Sc) -> In c (frames S2)) by (intros c Hc; rewrite Efr; right; exact Hc).
assert (HB : forall a, x <= a < x + n ->
  range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF a 1 /\ shadow_hull_vis (aview SEGS (w_H W) mem2) a 1).
{ intros a Ha.
  apply (sbd1_byte STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem2 md2 a HJ (proj1 HJ2) Eab Hfin Hfk (Hw a Ha)).
  - unfold amem_range in Ham. lia.
  - apply (range_addressable_sub _ _ x n); [exact Hra | lia | lia]. }
split; [|split].
- intros y Hy. destruct (HB y Hy) as [Hr _]. apply Hr. lia.
- apply sbd1_hull_bytes; [exact Hx | exact Hn | intros a Ha; exact (proj2 (HB a Ha))].
- intros a Ha.
  assert (Hw' : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S2) lyc ((0, pos) :: own) a)
    by (rewrite Eab; apply sbd1_awr_cons; exact (Hw a Ha)).
  split; [exact Hw' | exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ2 Hw'))].
Qed.
Lemma sbd1_kept_comp : forall lyc Sc (W : world SEGS) memc memT mem2 md lo hi slo shi wlo whi,
  AR SEGS B lyc Sc W memc md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (wlo <= a < whi) -> aview SEGS (w_H W) memT a = aview SEGS (w_H W) memc a) ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memT) ->
  acall_kept SEGS B lyc Sc W memT W mem2 slo shi (fun _ => False) ->
  alloc_ceiling <= lo -> lo <= wlo -> whi <= hi -> lo <= slo -> shi <= hi -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent (w_H W) mem2 a) ->
  acall_kept SEGS B lyc Sc W memc W mem2 lo hi (fun _ => False).
Proof.
intros lyc Sc W memc memT mem2 md lo hi slo shi wlo whi HAR KR HG (K1 & K2 & K3 & K4 & K5 & K6)
  Hlo Hw1 Hw2 Hs1 Hs2 H64 Hpr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hn. rewrite (K1 a Ha) by lia. apply KR; lia.
- intros b m i Hb Hi Hf. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4 & Hbc & _).
  rewrite (K2 b m i Hb Hi Hf). apply KR; lia.
- intros a Hia Ho He. pose proof (pa_segs_low a Hia) as Hl. rewrite (K3 a Hia Ho He). apply KR; lia.
- intros cid pos a Hc Ha Hf. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hc) as (Hf1 & Hf2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  assert (Hac : 0 <= a < alloc_ceiling)
    by (apply (sbd1_frame_low (frame_addr lyc cid pos) (fs_frame_bytes cid) a Hf1 Hnn Hf2);
        unfold frame_rng in Ha; cbn [fst snd] in Ha; exact Ha).
  rewrite (K4 cid pos a Hc Ha Hf). apply KR; lia.
- intros a Ha Hn Hp. apply (K5 a Ha ltac:(lia)). apply (apresent_grows _ _ _ _ HG). exact Hp.
- exact Hpr.
Qed.
Lemma sbd1_awr_view : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k mem2 lo hi a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  acall_kept SEGS B lyc Sc W memc W mem2 lo hi (fun _ => False) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  a < kLowMemEnd \/ kHighMemBeg <= a -> ~ (lo <= a < hi) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mem2 lo hi a HJ (K1 & K2 & _ & K4 & _) Hw Hz Hn.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & Hhi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as (_ & Hc).
destruct Hc as [(Hac & Hs) | [(Happ & b & n & Hin & Hr & _) | (cid & pos & Hown & [(Happ & Hr) | (Hsh & _)])]].
- apply K1; lia.
- replace a with (b + (a - b)) by lia. apply (K2 b n (a - b) Hin); [lia | intros []].
- assert (Hc : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  apply (K4 cid pos a Hc); [left; exact Hr | intros []].
- exfalso. lia.
Qed.
Lemma sbd1_post : forall (X : sbd_in) (regsT : bvmap 5 word) memT S2 (regs2 : bvmap 5 word) mem2 md2 pos,
  sbd_cx B X ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sbd_SP X - 128 <= a < sbd_SP X) ->
     aview SEGS (w_H (si_W X)) memT a = aview SEGS (w_H (si_W X)) (si_memc X) a) ->
  mem_grows (mrestrict (w_H (si_W X)) (si_memc X)) (mrestrict (w_H (si_W X)) memT) ->
  sbd_frame X (mrestrict (w_H (si_W X)) memT) ->
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) (si_lyc X) S2 (si_W X) mem2 md2 (si_k X) ->
  aregs_preserved regsT regs2 -> getr regs2 10 = w64 (frame_addr (si_lyc X) 0 pos) ->
  ablocks B (si_lyc X) S2 = ablocks B (si_lyc X) (si_Sc X) -> frames S2 = (0, pos) :: frames (si_Sc X) ->
  rdword (aview SEGS (w_H (si_W X)) mem2) (frame_addr (si_lyc X) 0 pos + fs_frame_bytes 0 - 8) =
    Some (flag_addr (si_lyc X) 0 pos) ->
  acall_kept SEGS B (si_lyc X) (si_Sc X) (si_W X) memT (si_W X) mem2 (sbd_S1 X - ESTACK) (sbd_S1 X) (fun _ => False) ->
  getr regsT 2 = w64 (sbd_S1 X) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 8 = w64 (sbd_SP X) -> getr regsT 9 = w64 (sbd_S1 X) -> getr regsT 19 = w64 (si_A X) ->
  getr regsT 20 = w64 (si_md X) -> getr regsT 21 = w64 (si_v X) -> getr regsT 22 = w64 SHADOW_OFF ->
  getr regsT 27 = getr (si_regs X) 27 ->
  sbd_stA B X pos regs2 (si_lyc X) S2 (si_W X) mem2 md2.
Proof.
intros X regsT memT S2 regs2 mem2 md2 pos HX KR HG Hfr HJ2 HP Ha0 Eab Efr Hflag HK
  G2 G3 G4 G8 G9 G19 G20 G21 G22 G27.
unfold sbd_cx in HX.
destruct HX as (HJ & Hro & _ & _ & _ & _ & _ & _ & _ & Hal & Hbud & Hsp & _ & _ & _ & HA0 & _ & _ & HAam & _ & HAside &
  _ & _ & Hn & _ & _ & Hrec & HrecP & Hout).
unfold sbd_recP in HrecP.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (WS : SB_DEC_STK = 4256) by reflexivity.
destruct (sp1_facts (sbd_SP X - 128) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal; reflexivity))
  as (HS1 & _ & _).
change (32 * ((sbd_SP X - 128) / 32)) with (sbd_S1 X) in HS1.
pose proof HK as (K1h & _).
assert (KC : acall_kept SEGS B (si_lyc X) (si_Sc X) (si_W X) (si_memc X) (si_W X) mem2
  (sbd_SP X - SB_DEC_STK) (sbd_SP X) (fun _ => False)).
{ apply (sbd1_kept_comp _ _ _ _ memT _ _ _ _ (sbd_S1 X - ESTACK) (sbd_S1 X) (sbd_SP X - 128) (sbd_SP X) HAR KR HG HK);
    try lia.
  intros a Ha. apply Hpres2. lia. }
pose proof KC as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6).
assert (Hfk : forall cid p y, In (cid, p) (frames (si_Sc X)) ->
  in_zr y (shadow_addr (frame_addr (si_lyc X) cid p), fs_frame_bytes cid / 8) ->
  aview SEGS (w_H (si_W X)) mem2 y = aview SEGS (w_H (si_W X)) (si_memc X) y)
  by (intros cid p y Hc Hy; apply (KC4 cid p y Hc); [right; exact Hy | intros []]).
assert (KV : forall a, si_A X <= a < si_A X + 28 ->
  aview SEGS (w_H (si_W X)) mem2 a = aview SEGS (w_H (si_W X)) (si_memc X) a).
{ intros a Ha. destruct HrecP as (_ & _ & Hw).
  eapply sbd1_awr_view; [exact HJ | exact KC | exact (proj1 (Hw a Ha)) | unfold amem_range in HAam; lia | lia]. }
assert (HrecP2 : sbd_recP B X (si_lyc X) S2 (si_W X) mem2 ((0, pos) :: si_own X)).
{ destruct HrecP as (Hra & _ & Hw).
  pose proof (sbd1_triple _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos (si_A X) 28 HJ HJ2 Eab Efr Hfk
    ltac:(lia) ltac:(lia) HAam Hra (fun a Ha => proj1 (Hw a Ha))) as (R1 & R2 & R3).
  unfold sbd_recP. split; [exact R1|]. split; [exact R2 | exact R3]. }
assert (Hout2 : 0 < sbd_room X -> sbd_outP B X (si_lyc X) S2 (si_W X) mem2 ((0, pos) :: si_own X)).
{ intros Hr. destruct (Hout Hr) as (Hp0 & _ & Ham & _ & _ & _ & HO). unfold sbd_outP in HO.
  destruct HO as (Hra & _ & Hw).
  pose proof (sbd1_acc_pos X Hr) as Hacc.
  pose proof (sbd1_triple _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos (si_p X + si_n X) (sbd_acc X) HJ HJ2 Eab Efr Hfk
    ltac:(lia) Hacc Ham Hra (fun a Ha => proj1 (Hw a Ha))) as (R1 & R2 & R3).
  unfold sbd_outP. split; [exact R1|]. split; [exact R2 | exact R3]. }
destruct (sbd1_regs_pres regsT regs2 HP) as (P2 & P3 & P4 & P8 & P9 & P19 & P20 & P21 & P22 & P27).
unfold sbd_stA, sbd_mid0.
split.
{ split; [exact HJ2|]. split; [exact Efr|]. split; [exact Eab|].
  split.
  { intros a Hro0 Ho He.
    assert (Hia : in_img SEGS a)
      by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
    rewrite (KC3 a Hia Ho He). exact (Hro a Hro0 Ho He). }
  split.
  { unfold sbd_kept. split; [intros a Ha Hn' _; exact (KC1 a Ha Hn')|].
    split; [intros b m j Hb Hj _; exact (KC2 b m j Hb Hj (fun H => H))|].
    split; [intros a Hia Ho He; exact (KC3 a Hia Ho He)|].
    split; [intros cid p a Hc Ha _; exact (KC4 cid p a Hc Ha (fun H => H))|].
    split; [exact KC5 | exact KC6]. }
  split.
  { unfold sbd_frame in *. intros j r Hj.
    assert (Hjl : (j < length sbd_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbn [length sbd_saved_regs] in Hjl.
    apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memT mem2); [|exact (Hfr j r Hj)].
    intros i Hi. apply K1h; lia. }
  split.
  { unfold sbd_F, sbd_FL.
    replace (frame_addr (si_lyc X) 0 pos + 56) with (frame_addr (si_lyc X) 0 pos + fs_frame_bytes 0 - 8)
      by (change (fs_frame_bytes 0) with 64; lia).
    exact (val_mem_of_rdword SEGS _ _ _ _ Hflag). }
  split; [exact HrecP2 | exact Hout2]. }
split.
{ destruct Hrec as (V0 & V8 & V16 & V24 & Vg).
  split; [apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) (si_memc X) mem2); [intros i Hi; apply KV; lia | exact V0]|].
  split; [apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) (si_memc X) mem2); [intros i Hi; apply KV; lia | exact V8]|].
  split; [apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) (si_memc X) mem2); [intros i Hi; apply KV; lia | exact V16]|].
  split; [apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) (si_memc X) mem2); [intros i Hi; apply KV; lia | exact V24]|].
  intros Hr. replace (Z.min 0 (sbd_room X)) with 0 by lia. cbn [Z.to_nat firstn]. apply garr8_nil. }
split; [rewrite P2; exact G2|]. split; [rewrite P3; exact G3|]. split; [rewrite P4; exact G4|].
split; [rewrite P8; exact G8|]. split; [rewrite P9; exact G9|]. split; [unfold sbd_F; exact Ha0|].
split; [rewrite P19; exact G19|]. split; [rewrite P20; exact G20|]. split; [rewrite P21; exact G21|].
split; [rewrite P22; exact G22 | rewrite P27; exact G27].
Qed.
Definition sbd1_extra : list word := map (Z_to_bv 64) [SB; as_uar_cell B].
Lemma sbd1_entry : forall X : sbd_in,
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X) (si_own X)
    (si_lyc X) (si_Sc X) (si_W X) (si_memc X) (si_mdc X) (si_k X) ->
  sbd_SP X mod 16 = 0 -> si_sp0 X - si_STK X <= sbd_SP X - SB_DEC_STK -> sbd_SP X <= si_sp0 X ->
  st_ok_pi (fx := si_fq X) SEGS VAL (Eimg (Ereg (si_regs X) sbd1_extra)) ss_sbd1
    (restrict (w_H (si_W X)) (mkst (fx := si_fq X) (si_regs X) (Z_to_bv 64 (BASE + AF_both3_sb_dec)) (si_memc X) (seg_rom SEGS))).
Proof.
intros X HJ Hal16 Hbud Hsp.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4256) by reflexivity.
destruct (al_const _ _ LAWS (si_lyc X) (si_Sc X) (si_W X) (si_memc X) (si_mdc X) HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg (si_regs X) sbd1_extra)).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg (si_regs X) sbd1_extra) m)
  by (intros m Hm; subst E; apply Eimg_low; exact Hm).
assert (E2 : ew E 2 = getr (si_regs X) 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (si_regs X) _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (si_regs X) _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (si_regs X) _ 1)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = sbd_SP X) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as VR0. pose proof (pa_val_range (A_OBJ 1)) as VR1.
pose proof (pa_val_range (A_OBJ 12)) as VR12.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
unfold ss_sbd1, sbd1_regions. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (si_W X)) (si_memc X) _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (si_W X)) (si_memc X) _ _ Kcell).
  + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (si_W X)) (si_memc X) _ _ Kguar).
  + rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1);
    [reflexivity | lia | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H (si_W X)) (si_memc X) _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- unfold sbd1_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
          split; [lia|]; split; [exact Hal16 | lia]|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by (unfold SB; lia);
          rewrite Z.pow_0_r; split; [unfold SB; lia|]; split; [apply Z.mod_1_r | unfold SB; lia]|].
  exact I.
Qed.
Theorem sbd_seg1 : sbd_seg1_stmt B.
Proof.
intros X HX. pose proof HX as HX0. unfold sbd_cx in HX.
destruct HX as (HJ & _ & Hrv & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hal & Hbud & Hsp & Hfrl & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (sbd1_entry X HJ Hal Hbud Hsp) as HS.
pose proof (@SRr_run_pi_AJ (si_fq X) _ _ _ PL_both3_0 PI B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call (si_fq X) _ _ _ PL_both3_0 PI B LAWS) as RUNC.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4256) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (sp1_facts (sbd_SP X - 128) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal; reflexivity))
  as (HS1 & HS1a & HS1b).
change (32 * ((sbd_SP X - 128) / 32)) with (sbd_S1 X) in HS1, HS1a, HS1b.
remember (Eimg (Ereg (si_regs X) sbd1_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (si_regs X) r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E2 : ew E 2 = getr (si_regs X) 2) by (exact (EE 2%nat 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = sbd_SP X) by (rewrite E2; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (si_regs X) _ 0)).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_both3_sb_dec)) with (Z_to_bv 64 (BASE + AF_both3_sb_dec)).
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off E _ _ (si_STK X) (si_sp0 X) (si_FP X) _ _ (si_lyc X) (si_own X) 2%nat (sbd_SP X - si_sp0 X));
    [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (sbd1_kept_frame _ _ _ _ _ (sbd_SP X - 128) (sbd_SP X) HFr
  ltac:(intros a (r & Hr & Hw); unfold ss_sbd1, sbd1_regions in Hr; cbn [ss_mem In] in Hr;
        repeat destruct Hr as [<- | Hr]; try destruct Hr;
        unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP in Hw;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp in Hw; lia)) as K1.
rename HG into G1. clear HF HFr.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict] in HR0.
assert (HFRT : sbd_frame X (mrestrict (w_H (si_W X)) (ms_mem ms))).
{ apply (sbd1_frame_of_region X E _ _ _ _ _ _ HR0 Usp).
  - intros j r Hj. unfold sbd_saved_regs in Hj.
    do 12 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [In]; repeat (first [left; reflexivity | right])|]).
    cbn in Hj. destruct j; discriminate.
  - intros r Hr. apply EE. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
clear HR0.
pmkst HS.
assert (EA : sv_denot E (SAlu ALU_AND (SOff 2 (-128)) (SLit (-32))) = Z_to_bv 64 (sbd_S1 X)).
{ unfold sbd_S1. replace (sbd_SP X - 128) with (sbd_SP X + -128) by lia.
  apply denot_and_m32; [rewrite E2; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | unfold sbd_SP, spZ; apply bv_unsigned_in_range]. }
assert (EA9 : sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-128)) (SLit (-32))) (SLit 0)) = Z_to_bv 64 (sbd_S1 X)).
{ change (alu64 ALU_ADD (sv_denot E (SAlu ALU_AND (SOff 2 (-128)) (SLit (-32)))) (Z_to_bv 64 0) = Z_to_bv 64 (sbd_S1 X)).
  rewrite EA, alu_add_small by (unfold M64; lia). f_equal; lia. }
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 (sbd_S1 X)) EA R2.
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 (sbd_S1 X)) EA9 R9.
prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8.
prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21.
prreg HS (22%bv : bv 5) R22. prreg HS (27%bv : bv 5) R27.
assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite R3, (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite R4, (EE 4%nat 4%bv eq_refl); exact Htp).
assert (G8 : getr (ms_regs ms) 8 = w64 (sbd_SP X))
  by (rewrite R8, E2; unfold w64, sbd_SP, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (G19 : getr (ms_regs ms) 19 = w64 (si_A X)) by (rewrite R19, (EE 10%nat 10%bv eq_refl); exact H10).
assert (G20 : getr (ms_regs ms) 20 = w64 (si_md X)) by (rewrite R20, (EE 12%nat 12%bv eq_refl); exact H12).
assert (G21 : getr (ms_regs ms) 21 = w64 (si_v X)) by (rewrite R21, (EE 11%nat 11%bv eq_refl); exact H11).
assert (G22 : getr (ms_regs ms) 22 = w64 SHADOW_OFF) by (rewrite R22, E32; reflexivity).
assert (G27 : getr (ms_regs ms) 27 = getr (si_regs X) 27) by (rewrite R27; exact (EE 27%nat 27%bv eq_refl)).
rewrite (palf_sm0 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply (aj_stack_malloc_at SEGS B LAWS Hsegs (pal_env B TL) ML SMP 0 (ASM0 (si_fq X)) ltac:(lia) (si_W X) rg mm
    (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X) (si_own X) (si_lyc X) (si_Sc X) _
    (si_k X) (sbd_S1 X - si_sp0 X) _ HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, HS1b, <- Zminus_mod_idemp_r, Hsp0al. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - exact G3.
  - exact G4.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof (count_cid_le_length 0 (frames (si_Sc X))) as Hcnt.
    assert (Hfs0 : 9 < fs_frames 0) by (vm_compute; reflexivity). lia. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & _ & _ & _ & _ & Hflag & HK).
apply SRr_ret. unfold sbd_atA.
exists pos, regs2, (si_lyc X), S2, mem2, md2. split.
{ unfold sbd_cfg, cfg_at, w64.
  replace (BASE + AF_both3_sb_dec + SBD_PA) with (BASE + 16272) by (unfold AF_both3_sb_dec, SBD_PA; lia).
  reflexivity. }
replace (si_sp0 X + (sbd_S1 X - si_sp0 X)) with (sbd_S1 X) in HK by lia.
exact (sbd1_post X (ms_regs ms) (ms_mem ms) S2 regs2 mem2 md2 pos HX0 K1 G1 HFRT HJ2 HP2 Ha0 Eab Hfrs2 Hflag HK
  R2 G3 G4 G8 R9 G19 G20 G21 G22 G27).
Qed.
End h.
End f.
End d.
