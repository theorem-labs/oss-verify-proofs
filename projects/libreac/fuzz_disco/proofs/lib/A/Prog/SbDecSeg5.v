(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths, module names and numbers changed; 379 of its 508 lines of code are new or changed and 531 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YC88 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec SbDecLib SbDecCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition sbd5_chunks : list YP09.chunk :=
  [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 41 0))].
Definition sbd5_regions : smem :=
  [ YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 17%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 16%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 10%nat) 56 64 0 0 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 8%nat) (-72) 0 0 0 sbd5_chunks ].
Definition sbd5_facts : facts := mkFacts [ (10%nat, mkAF 4096 (2 ^ 47) 0) ] [] [].
Definition ss_sbd5 : sstate := mkSS (AF_sb_dec + SBD_P5) sr_atoms sbd5_regions None sbd5_facts.
Definition sbd5_extra (X : sbd_in) (pos : Z) : list word :=
  Z_to_bv 64 (sbd_FL X pos) :: map (fun r => getr (si_regs X) (Z_to_bv 5 r)) sbd_saved_regs.
Lemma sbd5_kept_frame : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma sbd5_ew_saved : forall X pos (regs : bvmap 5 word) j r, nth_error sbd_saved_regs j = Some r ->
  ew (Eimg (Ereg regs (sbd5_extra X pos))) (33 + j) = getr (si_regs X) (Z_to_bv 5 r).
Proof.
intros X pos regs j r Hj.
assert (Hj9 : (j < length sbd_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite Eimg_low by (cbn [length sbd_saved_regs] in Hj9; unfold A_TEXT; lia).
replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra. unfold sbd5_extra. cbn [nth].
rewrite (nth_indep _ _ (getr (si_regs X) (Z_to_bv 5 0))) by (rewrite length_map; exact Hj9).
rewrite (map_nth (fun r0 => getr (si_regs X) (Z_to_bv 5 r0)) sbd_saved_regs 0 j).
rewrite (nth_error_nth sbd_saved_regs j 0 Hj). reflexivity.
Qed.
Lemma sbd5_chunks_ok : forall X pos (regs : bvmap 5 word) (m : word -> option byte),
  sbd_frame X m -> Forall (YP09.chunk_ok SEGS (Eimg (Ereg regs (sbd5_extra X pos))) m (sbd_SP X)) sbd5_chunks.
Proof.
intros X pos regs m Hfr.
assert (K : forall j r off n, nth_error sbd_saved_regs j = Some r -> off = -8 - 8 * Z.of_nat j -> n = (33 + j)%nat ->
  YP09.chunk_ok SEGS (Eimg (Ereg regs (sbd5_extra X pos))) m (sbd_SP X) (YP09.mkChunk off (CVal 8 (SOff n 0)))).
{ intros j r off n Hj -> ->.
  apply (chunk_ok_val SEGS _ m (sbd_SP X) _ 8 _ (bv_unsigned (getr (si_regs X) (Z_to_bv 5 r)))).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (sbd5_ew_saved X pos regs j r Hj).
    symmetry. apply Z_to_bv_bv_unsigned.
  - pose proof (bv_unsigned_in_range 64 (getr (si_regs X) (Z_to_bv 5 r))) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia.
  - change (N.to_nat 8) with 8%nat.
    replace (sbd_SP X + (-8 - 8 * Z.of_nat j)) with (sbd_SP X - 8 - 8 * Z.of_nat j) by lia. exact (Hfr j r Hj). }
unfold sbd5_chunks.
apply Forall_cons; [apply (K 0%nat 1); reflexivity|]. apply Forall_cons; [apply (K 1%nat 8); reflexivity|].
apply Forall_cons; [apply (K 2%nat 9); reflexivity|]. apply Forall_cons; [apply (K 3%nat 18); reflexivity|].
apply Forall_cons; [apply (K 4%nat 19); reflexivity|]. apply Forall_cons; [apply (K 5%nat 20); reflexivity|].
apply Forall_cons; [apply (K 6%nat 21); reflexivity|]. apply Forall_cons; [apply (K 7%nat 22); reflexivity|].
apply Forall_cons; [apply (K 8%nat 23); reflexivity|]. apply Forall_nil.
Qed.
Lemma sbd5_entry : forall (fq : YK11.FPState) X pos (regs : bvmap 5 word) (W : world SEGS) (m : word -> option byte),
  bv_unsigned (getr regs 17) = sbd_SH X pos -> bv_unsigned (getr regs 16) = sbd_F X pos ->
  bv_unsigned (getr regs 10) = sbd_F X pos -> bv_unsigned (getr regs 8) = sbd_SP X ->
  4096 <= sbd_F X pos -> sbd_F X pos + 64 <= 2 ^ 47 -> 0 <= sbd_SH X pos -> sbd_SH X pos + 8 <= 2 ^ 47 ->
  0 <= sbd_FL X pos -> sbd_FL X pos + 1 <= 2 ^ 47 -> 72 <= sbd_SP X <= 2 ^ 47 ->
  sbd_F X pos + 64 <= sbd_SP X - 72 ->
  (sbd_SH X pos + 8 <= sbd_F X pos \/ sbd_F X pos + 64 <= sbd_SH X pos) ->
  sbd_SH X pos + 8 <= sbd_SP X - 72 ->
  (sbd_FL X pos + 1 <= sbd_F X pos \/ sbd_F X pos + 64 <= sbd_FL X pos) ->
  (sbd_FL X pos + 1 <= sbd_SH X pos \/ sbd_SH X pos + 8 <= sbd_FL X pos) ->
  sbd_FL X pos + 1 <= sbd_SP X - 72 ->
  apresent (w_H W) m (sbd_FL X pos) ->
  (forall o, 0 <= o < 8 -> apresent (w_H W) m (sbd_SH X pos + o)) ->
  (forall o, 0 <= o < 8 -> apresent (w_H W) m (sbd_F X pos + o)) ->
  val_mem SEGS (mrestrict (w_H W) m) (sbd_F X pos + 56) 8 (sbd_FL X pos) ->
  sbd_frame X (mrestrict (w_H W) m) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (sbd5_extra X pos))) ss_sbd5
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_sb_dec + SBD_P5))) m (seg_rom SEGS))).
Proof.
intros fq X pos regs W m H17 H16 H10 H8 HF4 HF47 HSH0 HSH47 HFL0 HFL47 HSP D1 D2 D3 D4 D5 D6 Pfl Psh Pfr Hfl Hfr.
rewrite restrict_mkst_fx.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs (sbd5_extra X pos))) n = getr regs r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E17 : bv_unsigned (ew (Eimg (Ereg regs (sbd5_extra X pos))) 17) = sbd_SH X pos)
  by (rewrite (EE 17%nat 17%bv eq_refl); exact H17).
assert (E16 : bv_unsigned (ew (Eimg (Ereg regs (sbd5_extra X pos))) 16) = sbd_F X pos)
  by (rewrite (EE 16%nat 16%bv eq_refl); exact H16).
assert (E10 : bv_unsigned (ew (Eimg (Ereg regs (sbd5_extra X pos))) 10) = sbd_F X pos)
  by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E8 : bv_unsigned (ew (Eimg (Ereg regs (sbd5_extra X pos))) 8) = sbd_SP X)
  by (rewrite (EE 8%nat 8%bv eq_refl); exact H8).
assert (E32 : ew (Eimg (Ereg regs (sbd5_extra X pos))) 32 = Z_to_bv 64 (sbd_FL X pos))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E32u : bv_unsigned (ew (Eimg (Ereg regs (sbd5_extra X pos))) 32) = sbd_FL X pos)
  by (rewrite E32; apply unsigned_lit_small; lia).
unfold ss_sbd5, sbd5_regions. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E32u. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. replace (sbd_FL X pos + o) with (sbd_FL X pos) by lia. apply (apresent_writable SEGS). exact Pfl.
  + rewrite E17. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply Psh. lia.
  + rewrite E16. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply Pfr. lia.
  + rewrite E10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (sbd_F X pos) 56 8 (SOff 32 0) (sbd_FL X pos));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Hfl].
  + rewrite E8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply sbd5_chunks_ok. exact Hfr.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E32u, E17, E16, E10, E8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- unfold sbd5_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
  split; [|exact I]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E10, Z.pow_0_r, Z.mod_1_r. lia.
Qed.
Definition sbd5_W (ly : alayout) (pos a : Z) : Prop :=
  (frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 8) \/
  (shadow_addr (frame_addr ly 0 pos) <= a < shadow_addr (frame_addr ly 0 pos) + 8) \/
  a = flag_addr ly 0 pos.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Lemma sbd5_avoid_hi : forall ly S W m md pos a,
  AR SEGS B ly S W m md -> In (0, pos) (frames S) -> alloc_ceiling <= a -> ~ sbd5_W ly pos a.
Proof.
intros ly S W m md pos a HAR Hin Ha.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR Hin) as (H4 & Hc & _).
destruct (FFL _ _ _ _ _ 0 pos HAR Hin) as (_ & _ & _ & (_ & _ & Hfc)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in Hc.
assert (Hx : 0 <= frame_addr ly 0 pos + 64 < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds _ Hx) as Hsb.
assert (Hse : shadow_addr (frame_addr ly 0 pos) + 8 <= shadow_addr (frame_addr ly 0 pos + 64))
  by exact (shadow_range_end (frame_addr ly 0 pos) 64 ltac:(lia)).
unfold sbd5_W. lia.
Qed.
Lemma sbd5_avoid_img : forall ly S W m md pos a,
  AR SEGS B ly S W m md -> In (0, pos) (frames S) -> in_img SEGS a -> ~ sbd5_W ly pos a.
Proof.
intros ly S W m md pos a HAR Hin Hi.
pose proof (pa_segs_low a Hi) as Hlow.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR Hin) as (H4 & Hc & _).
destruct (FFL _ _ _ _ _ 0 pos HAR Hin) as (_ & _ & (_ & Hfi) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in Hc.
assert (Hx : 0 <= frame_addr ly 0 pos < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds _ Hx) as Hsb.
unfold sbd5_W. intros [Hr | [Hr | ->]].
- assert (Hr' : frame_addr ly 0 pos <= a < frame_addr ly 0 pos + fs_frame_bytes 0) by (rewrite Hfb; lia).
  exact (frm_img SEGS B LAWS _ _ _ _ _ 0 pos a HAR Hin Hr' Hi).
- lia.
- exact (Hfi Hi).
Qed.
Lemma sbd5_avoid_blk : forall ly S W m md pos b n a,
  AR SEGS B ly S W m md -> In (0, pos) (frames S) -> In (b, n) (ablocks B ly S) -> b <= a < b + req_size n ->
  ~ sbd5_W ly pos a.
Proof.
intros ly S W m md pos b n a HAR Hin Hb Ha.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR Hin) as (H4 & Hc & _).
destruct (FFL _ _ _ _ _ 0 pos HAR Hin) as (_ & Hfo & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & Hb4 & Hbc & Happ & Hbp & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b n 0 pos HAR Hb Hin) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in Hc, Hd.
assert (Hx : 0 <= frame_addr ly 0 pos + 64 < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds _ Hx) as Hsb2.
assert (Hx1 : 0 <= frame_addr ly 0 pos < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds _ Hx1) as Hsb1.
assert (Hse : shadow_addr (frame_addr ly 0 pos) + 8 <= shadow_addr (frame_addr ly 0 pos + 64))
  by exact (shadow_range_end (frame_addr ly 0 pos) 64 ltac:(lia)).
unfold sbd5_W. intros [Hr | [Hr | ->]].
- lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia.
- exact (proj2 (Hbp _ Ha) Hfo).
Qed.
Lemma sbd5_avoid_frm : forall ly S W m md pos rest c p a,
  AR SEGS B ly S W m md -> frames S = (0, pos) :: rest -> In (c, p) rest ->
  (in_zr a (frame_rng ly (c, p)) \/ in_zr a (shadow_addr (frame_addr ly c p), fs_frame_bytes c / 8)) ->
  ~ sbd5_W ly pos a.
Proof.
intros ly S W m md pos rest c p a HAR Hfrs Hcp Ha.
assert (Hin : In (0, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Hin' : In (c, p) (frames S)) by (rewrite Hfrs; right; exact Hcp).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR Hin) as (H4 & Hc & Happ).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c p HAR Hin') as (H4' & Hc' & Happ').
destruct (FFL _ _ _ _ _ 0 pos HAR Hin) as (_ & Hfo & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ c p HAR Hin') as (_ & _ & Hfb' & Hfsh').
apply in_split in Hcp as (l1 & l2 & El).
assert (Hd : zdisjoint (frame_rng ly (0, pos)) (frame_rng ly (c, p))).
{ apply (sep_frames_pos SEGS B LAWS _ _ _ _ _ (0, pos) (c, p) [] l1 l2 HAR). rewrite Hfrs, El. reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fs_frame_bytes_nonneg c) as Hnn.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in Hc, Hd, Happ.
assert (Hx1 : 0 <= frame_addr ly 0 pos < kHighMemEnd) by (rewrite C4; lia).
assert (Hx2 : 0 <= frame_addr ly 0 pos + 64 < kHighMemEnd) by (rewrite C4; lia).
assert (Hx3 : 0 <= frame_addr ly c p < kHighMemEnd) by (rewrite C4; lia).
assert (Hx4 : 0 <= frame_addr ly c p + fs_frame_bytes c < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds _ Hx1) as Hsb1. pose proof (shadow_addr_bounds _ Hx2) as Hsb2.
pose proof (shadow_addr_bounds _ Hx3) as Hsb3. pose proof (shadow_addr_bounds _ Hx4) as Hsb4.
assert (Hse : shadow_addr (frame_addr ly 0 pos) + 8 <= shadow_addr (frame_addr ly 0 pos + 64))
  by exact (shadow_range_end (frame_addr ly 0 pos) 64 ltac:(lia)).
pose proof (shadow_range_end (frame_addr ly c p) (fs_frame_bytes c) Hnn) as Hse'.
unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, Happ'.
unfold sbd5_W. intros [Hr | [Hr | ->]].
- destruct Ha as [Ha | Ha]; lia.
- destruct Ha as [Ha | Ha]; [lia|].
  destruct Hd as [Hd | Hd]; pose proof (shadow_mono _ _ Hd); lia.
- destruct Ha as [Ha | Ha].
  + exact (proj2 (Hfb' _ Ha) Hfo).
  + specialize (Hfsh' (flag_addr ly 0 pos - shadow_addr (frame_addr ly c p)) ltac:(lia)).
    replace (shadow_addr (frame_addr ly c p) + (flag_addr ly 0 pos - shadow_addr (frame_addr ly c p)))
      with (flag_addr ly 0 pos) in Hfsh' by lia.
    exact (proj2 Hfsh' Hfo).
Qed.
Lemma sbd5_avoid_buf : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly1 S1 W1 m1 md1 pos a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR SEGS B ly1 S1 W1 m1 md1 -> frames S1 = (0, pos) :: frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ->
  (forall c p, frame_addr ly1 c p = frame_addr lyc c p) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  0 <= a < 2 ^ 64 /\ ~ sbd5_W ly1 pos a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly1 S1 W1 m1 md1 pos a HJ HAR1 Hfrs1 Eab Efa Hw.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof Hstatic as (_ & _ & _ & _ & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (0, pos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw)
  as (_ & [[Hc Hs] | [(Happ & b & n & Hb & Hr & _) | (c & p & Hcp & Hr)]]).
- split; [lia | exact (sbd5_avoid_hi _ _ _ _ _ pos a HAR1 Hin Hc)].
- split; [unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ; lia|].
  exact (sbd5_avoid_blk _ _ _ _ _ pos b n a HAR1 Hin ltac:(rewrite Eab; exact Hb) Hr).
- assert (Ha' : in_zr a (frame_rng ly1 (c, p)) \/ in_zr a (shadow_addr (frame_addr ly1 c p), fs_frame_bytes c / 8)).
  { unfold frame_rng. cbn [fst snd]. rewrite !Efa. unfold frame_rng in Hr. cbn [fst snd] in Hr.
    destruct Hr as [[_ Hr] | [_ Hr]]; [left | right]; exact Hr. }
  split.
  + destruct Hr as [[Happ _] | [Hsh _]]; [unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ; lia | lia].
  + apply (sbd5_avoid_frm _ _ _ _ _ pos (frames Sc) c p a HAR1 Hfrs1); [|exact Ha'].
    rewrite Hfrs. apply in_or_app. left. exact Hcp.
Qed.
Lemma sbd5_post : forall X pos lyc1 Sc1 memc1 mdc1 regsF memF mdF,
  sbd_cx B X -> sbd_mid B X pos lyc1 Sc1 memc1 mdc1 sbd_sh_hdr ->
  sbd_rec (mrestrict (w_H (si_W X)) memc1) (si_A X) (si_p X) (si_cap X) (si_n X + sbm_acc X) (sbm_over X) ->
  (0 < sbm_room X ->
     garr8 SEGS (mrestrict (w_H (si_W X)) memc1) (si_p X + si_n X) (firstn (Z.to_nat (sbm_acc X)) (sbm_D X))) ->
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    (si_own X) lyc1 (stack_free_state 0 pos Sc1) (si_W X) memF mdF (si_k X) ->
  aregs_preserved (si_regs X) regsF ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ sbd5_W lyc1 pos a ->
     aview SEGS (w_H (si_W X)) memF a = aview SEGS (w_H (si_W X)) memc1 a) ->
  sbd_post B X (si_W X) (mkCfg (mkst (fx := si_fq X) regsF (getr (si_regs X) 1) memF (seg_rom SEGS)) mdF).
Proof.
intros X pos lyc1 Sc1 memc1 mdc1 regsF memF mdF HX HM Hrec Hdig HJF HP KK.
pose proof HX as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & HAawr & Hroom).
pose proof HM as (HJ1 & Hfrs1 & Eab & Efa & _ & HK & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof HJ1 as (AR1 & _).
pose proof HJF as (_ & _ & _ & _ & _ & HfrsF & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (bv_unsigned_in_range 64 (getr (si_regs X) 2)) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
change (bv_unsigned (getr (si_regs X) 2)) with (spZ (si_regs X)) in Rsp.
assert (WS : SB_DEC_STK = 4208) by reflexivity.
assert (Hin0 : In (0, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
assert (KB : forall a, awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X))
    (ablocks B (si_lyc X) (si_Sc X)) (si_lyc X) (si_own X) a ->
  aview SEGS (w_H (si_W X)) memF a = aview SEGS (w_H (si_W X)) memc1 a).
{ intros a Hw.
  destruct (sbd5_avoid_buf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lyc1 Sc1 (si_W X) memc1 mdc1 pos a HJ AR1 Hfrs1 Eab Efa Hw)
    as (Ha & Hn).
  exact (KK a Ha Hn). }
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6). unfold sbd_SP in K1, K5, K6.
unfold sbm_room, sbm_acc, sbm_D, sbm_over in *.
unfold sbd_post, tsb_dec_post.
exists lyc1, (stack_free_state 0 pos Sc1), regsF, memF, mdF.
split; [reflexivity|]. split; [exact HJF|]. split; [exact HP|].
split; [rewrite HfrsF, Hfrs0; reflexivity|].
split.
{ replace (ablocks B lyc1 (stack_free_state 0 pos Sc1)) with (ablocks B lyc1 Sc1)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  rewrite Eab. apply Permutation_refl. }
split.
{ intros a Ha Hn HnA HnP.
  rewrite (KK a ltac:(lia) (sbd5_avoid_hi _ _ _ _ _ pos a AR1 Hin0 ltac:(lia))).
  apply K1; [exact Ha | exact Hn | unfold sbd_Er; tauto]. }
split.
{ intros b m j Hb Hj HnA HnP.
  assert (Hb1 : In (b, m) (ablocks B lyc1 Sc1)) by (rewrite Eab; exact Hb).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m AR1 Hb1) as (_ & Hb4 & Hbc & _).
  rewrite (KK (b + j) ltac:(lia) (sbd5_avoid_blk _ _ _ _ _ pos b m (b + j) AR1 Hin0 Hb1 ltac:(lia))).
  apply (K2 b m j); [exact Hb | exact Hj | unfold sbd_Er; tauto]. }
split.
{ intros a Hi Ho He. pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite (KK a ltac:(lia) (sbd5_avoid_img _ _ _ _ _ pos a AR1 Hin0 Hi)). exact (K3 a Hi Ho He). }
split.
{ intros cid p a Hcp Ha HnA HnP.
  assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs1; right; exact Hcp).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p AR1 Hcp1) as (Hc4 & Hcc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  assert (Ha' : in_zr a (frame_rng lyc1 (cid, p)) \/ in_zr a (shadow_addr (frame_addr lyc1 cid p), fs_frame_bytes cid / 8)).
  { unfold frame_rng in *. cbn [fst snd] in *. rewrite !Efa. exact Ha. }
  assert (Hx : 0 <= frame_addr lyc1 cid p + fs_frame_bytes cid < kHighMemEnd) by (rewrite C4; lia).
  pose proof (shadow_addr_bounds _ Hx) as Hsb.
  pose proof (shadow_range_end (frame_addr lyc1 cid p) (fs_frame_bytes cid) Hnn) as Hse.
  assert (Hx0 : 0 <= frame_addr lyc1 cid p < kHighMemEnd) by (rewrite C4; lia).
  pose proof (shadow_addr_bounds _ Hx0) as Hsb0.
  assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold in_zr, frame_rng in Ha'; cbn [fst snd] in Ha'; lia).
  rewrite (KK a Ha64 (sbd5_avoid_frm _ _ _ _ _ pos (frames (si_Sc X)) cid p a AR1 Hfrs1 Hcp Ha')).
  apply (K4 cid p a); [exact Hcp | exact Ha | unfold sbd_Er; tauto]. }
split.
{ intros a Ha Hn Hp.
  apply (apresent_transfer SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 memF a);
    [lia | intros Hi; pose proof (pa_segs_low a Hi) as Hlow; unfold kLowMemEnd in Hlow; lia | | exact (K5 a Ha Hn Hp)].
  apply KK; [lia | exact (sbd5_avoid_hi _ _ _ _ _ pos a AR1 Hin0 ltac:(lia))]. }
split.
{ intros a Ha.
  apply (apresent_transfer SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 memF a);
    [lia | intros Hi; pose proof (pa_segs_low a Hi) as Hlow; unfold kLowMemEnd in Hlow; lia | | exact (K6 a Ha)].
  apply KK; [lia | exact (sbd5_avoid_hi _ _ _ _ _ pos a AR1 Hin0 ltac:(lia))]. }
destruct Hrec as (Mp & Mcap & Mn & Mover).
assert (KA : forall x, si_A X <= x < si_A X + 28 ->
  aview SEGS (w_H (si_W X)) memF x = aview SEGS (w_H (si_W X)) memc1 x)
  by (intros x Hx; apply KB; apply HAawr; exact Hx).
split; [apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 memF);
  [intros j Hj; apply KA; simpl in Hj; lia | exact Mp]|].
split; [apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 memF);
  [intros j Hj; apply KA; simpl in Hj; lia | exact Mcap]|].
split; [apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 memF);
  [intros j Hj; apply KA; simpl in Hj; lia | exact Mn]|].
split; [apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 memF);
  [intros j Hj; apply KA; simpl in Hj; lia | exact Mover]|].
intros Hr0.
specialize (Hdig Hr0).
destruct (Hroom Hr0) as (_ & _ & _ & _ & _ & _ & Hpw).
eapply (garr8_aview_kept SEGS); [|exact Hdig].
intros a Ha. rewrite length_firstn in Ha.
apply KB. apply (proj1 (Hpw a ltac:(lia))).
Qed.
Theorem sbd_seg5 : sbd_seg5_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 memc1 mdc1 HX H5.
pose proof HX as (HJ & _ & Hra & _ & Hgp & Htp & _ & _ & _ & _ & _ & Hstk & Hsp & _).
pose proof H5 as (HM & HB & G16 & G17 & Hrec & Hdig).
pose proof HM as (HJ1 & Hfrs1 & Eab & Efa & Efl & _ & Hfr & Hfl & _).
destruct HB as (G2 & G3 & G4 & G8 & G9 & G18 & G21 & G10 & G24).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof HJ1 as (HAR1 & _).
pose proof Hstatic as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
assert (EF : frame_addr lyc1 0 pos = sbd_F X pos) by (unfold sbd_F; apply Efa).
assert (EFL : flag_addr lyc1 0 pos = sbd_FL X pos) by (unfold sbd_FL; apply Efl).
assert (Hin0 : In (0, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR1 Hin0) as (HF4 & HFc & HFapp).
destruct (FFL _ _ _ _ _ 0 pos HAR1 Hin0) as (HFLp & HFLo & (HFLa & _) & (HFL4 & _ & HFLc)).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR1 Hin0) as (_ & _ & HFb & HFs).
assert (Hfb0 : fs_frame_bytes 0 = 64) by reflexivity.
rewrite Hfb0, EF in HFc, HFb, HFapp, HFs. rewrite EF in HF4. change (64 / 8) with 8 in HFs.
rewrite EFL in HFLp, HFLo, HFLa, HFL4, HFLc.
assert (HFLnf : ~ (sbd_F X pos <= sbd_FL X pos < sbd_F X pos + 64)) by (intros Hr; exact (proj2 (HFb _ Hr) HFLo)).
pose proof (bv_unsigned_in_range 64 (getr (si_regs X) 2)) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
change (bv_unsigned (getr (si_regs X) 2)) with (spZ (si_regs X)) in Rsp.
assert (ESP : sbd_SP X = spZ (si_regs X)) by reflexivity.
assert (HSPc : alloc_ceiling + 4208 <= sbd_SP X /\ sbd_SP X <= 2 ^ 47) by (rewrite ESP; lia).
assert (Hx1 : 0 <= sbd_F X pos < kHighMemEnd) by (rewrite C4; lia).
assert (Hx2 : 0 <= sbd_F X pos + 64 < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds _ Hx1) as Hsb1. pose proof (shadow_addr_bounds _ Hx2) as Hsb2.
assert (Hse : sbd_SH X pos + 8 <= shadow_addr (sbd_F X pos + 64))
  by (unfold sbd_SH; exact (shadow_range_end (sbd_F X pos) 64 ltac:(lia))).
change (shadow_addr (sbd_F X pos)) with (sbd_SH X pos) in Hsb1.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLa.
assert (H17u : bv_unsigned (getr regs1 17) = sbd_SH X pos) by (rewrite G17; unfold w64; apply unsigned_lit_small; lia).
assert (H16u : bv_unsigned (getr regs1 16) = sbd_F X pos) by (rewrite G16; unfold w64; apply unsigned_lit_small; lia).
assert (H10u : bv_unsigned (getr regs1 10) = sbd_F X pos) by (rewrite G10; unfold w64; apply unsigned_lit_small; lia).
assert (H8u : bv_unsigned (getr regs1 8) = sbd_SP X)
  by (rewrite G8; unfold w64, sbd_SP, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (sbd5_entry (si_fq X) X pos regs1 (si_W X) memc1 H17u H16u H10u H8u ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  HFLp (fun o Ho => proj1 (HFs o Ho)) (fun o Ho => proj1 (HFb (sbd_F X pos + o) ltac:(lia))) Hfl Hfr) as HS.
unfold sbd_cfg, cfg_at, w64.
replace (BASE + AF_sb_dec + SBD_P5) with (BASE + (AF_sb_dec + SBD_P5)) by lia.
set (fq := si_fq X) in *.
pose proof (@aj_flag_store_pi fq _ _ _ _ _ B LAWS ML ASF FFL) as RUNF.
remember (Eimg (Ereg regs1 (sbd5_extra X pos))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (sbd_FL X pos))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (ES : forall j r, nth_error sbd_saved_regs j = Some r -> ew E (33 + j) = getr (si_regs X) (Z_to_bv 5 r))
  by (intros j r Hj; subst E; apply sbd5_ew_saved; exact Hj).
assert (E17 : bv_unsigned (ew E 17) = sbd_SH X pos) by (rewrite (EE 17%nat 17%bv eq_refl); exact H17u).
assert (E16 : bv_unsigned (ew E 16) = sbd_F X pos) by (rewrite (EE 16%nat 16%bv eq_refl); exact H16u).
assert (E10 : bv_unsigned (ew E 10) = sbd_F X pos) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10u).
assert (E8 : bv_unsigned (ew E 8) = sbd_SP X) by (rewrite (EE 8%nat 8%bv eq_refl); exact H8u).
assert (E32u : bv_unsigned (ew E 32) = sbd_FL X pos) by (rewrite E32; apply unsigned_lit_small; lia).
clear HE.
paj_run_flag_sh RUNF HS HJ1.
- lia.
- intros a (r & Hr & Hw). unfold ss_sbd5, sbd5_regions in Hr. cbn [ss_mem In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  + right. rewrite EFL. rewrite E32u in Hw. lia.
  + left. right. right. right. exists 0, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EF, Hfb0. change (64 / 8) with 8. rewrite E17 in Hw. unfold sbd_SH in Hw. lia.
  + left. right. right. right. exists 0, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EF, Hfb0. rewrite E16 in Hw. lia.
  + rewrite E10 in Hw. lia.
  + rewrite E8 in Hw. lia.
- intros msr HSr.
  pose proof (st_ok_pi_region_nth E _ msr 0 _ HSr eq_refl) as HR.
  pose proof (field_of_region E (ms_mem msr) 32 (sbd_FL X pos) _ _ _ _ _ 0 1%N (SLit 0) 0 HR E32u
    ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite EFL. specialize (V 0%nat ltac:(cbn; lia)). cbn [Z.of_nat] in V. rewrite !Z.add_0_r in V. exact V.
- match goal with |- context [mkCfg ?msF _] => rename msF into msZ end.
  match goal with H : frame_of _ _ _ (mrestrict _ (ms_mem msZ)) |- _ => rename H into HFr3 end.
  assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ sbd5_W lyc1 pos a ->
    aview SEGS (w_H (si_W X)) (ms_mem msZ) a = aview SEGS (w_H (si_W X)) memc1 a).
  { unfold sbd5_W. rewrite EF, EFL.
    lazymatch type of HFr3 with frame_of _ ?rsx _ _ =>
    apply (sbd5_kept_frame E rsx (w_H (si_W X)) memc1 (ms_mem msZ)
      (fun a => (sbd_F X pos <= a < sbd_F X pos + 8) \/
                (shadow_addr (sbd_F X pos) <= a < shadow_addr (sbd_F X pos) + 8) \/ a = sbd_FL X pos) HFr3) end.
    intros a (r & Hr & Hw). unfold ss_sbd5, sbd5_regions in Hr. cbn [ss_mem In] in Hr.
    repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
    rewrite ?E32u, ?E17, ?E16, ?E10, ?E8 in Hw; unfold sbd_SH in Hw; lia. }
  eapply (@paj_ret_at fq _ _ _ _ (si_W X) E _ msZ _ _ HS); [vm_compute; reflexivity | vm_compute; reflexivity |].
  intros mat3.
  prreg HS (1%bv : bv 5) Q1.
  assert (EPC : v_jalr (getr (ms_regs msZ) 1) 0 = getr (si_regs X) 1).
  { rewrite Q1. pose proof (ES 0%nat 1 eq_refl) as S1. cbn [Nat.add] in S1. rewrite S1.
    change (Z_to_bv 5 1) with (Z_to_bv 5 (bv_unsigned (1%bv : bv 5))). rewrite Z_to_bv_bv_unsigned. exact Hra. }
  assert (HPF : aregs_preserved (si_regs X) (ms_regs msZ)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | Hr']]].
    - prreg HS (Z_to_bv 5 2) Q. rewrite Q. rewrite (EE 8%nat 8%bv eq_refl), G8.
      change (Z_to_bv 5 2) with (Z_to_bv 5 (bv_unsigned (2%bv : bv 5))).
      unfold w64, sbd_SP, spZ. rewrite !Z_to_bv_bv_unsigned. reflexivity.
    - prreg HS (Z_to_bv 5 3) Q. rewrite Q. rewrite (EE 3%nat 3%bv eq_refl), G3.
      change (Z_to_bv 5 3) with (Z_to_bv 5 (bv_unsigned (3%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      symmetry. exact Hgp.
    - prreg HS (Z_to_bv 5 4) Q. rewrite Q. rewrite (EE 4%nat 4%bv eq_refl), G4.
      change (Z_to_bv 5 4) with (Z_to_bv 5 (bv_unsigned (4%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      symmetry. exact Htp.
    - destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]].
      + prreg HS (Z_to_bv 5 8) Q. rewrite Q. exact (ES 1%nat 8 eq_refl).
      + prreg HS (Z_to_bv 5 9) Q. rewrite Q. exact (ES 2%nat 9 eq_refl).
      + prreg HS (Z_to_bv 5 18) Q. rewrite Q. exact (ES 3%nat 18 eq_refl).
      + prreg HS (Z_to_bv 5 19) Q. rewrite Q. exact (ES 4%nat 19 eq_refl).
      + prreg HS (Z_to_bv 5 20) Q. rewrite Q. exact (ES 5%nat 20 eq_refl).
      + prreg HS (Z_to_bv 5 21) Q. rewrite Q. exact (ES 6%nat 21 eq_refl).
      + prreg HS (Z_to_bv 5 22) Q. rewrite Q. exact (ES 7%nat 22 eq_refl).
      + prreg HS (Z_to_bv 5 23) Q. rewrite Q. exact (ES 8%nat 23 eq_refl).
      + prreg HS (Z_to_bv 5 24) Q. rewrite Q. rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl). exact (G24 24 ltac:(lia)).
      + prreg HS (Z_to_bv 5 25) Q. rewrite Q. rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl). exact (G24 25 ltac:(lia)).
      + prreg HS (Z_to_bv 5 26) Q. rewrite Q. rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl). exact (G24 26 ltac:(lia)).
      + prreg HS (Z_to_bv 5 27) Q. rewrite Q. rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl). exact (G24 27 ltac:(lia)). }
  rewrite EPC.
  apply (sbd5_post X pos lyc1 Sc1 memc1 mdc1 (ms_regs msZ) (ms_mem msZ) _ HX HM Hrec Hdig); [| exact HPF | exact KK].
  exact (ajournal_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ1).
Qed.
End h.
End f.
End d.
