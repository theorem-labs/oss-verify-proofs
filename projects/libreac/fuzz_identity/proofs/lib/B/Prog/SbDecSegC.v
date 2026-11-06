(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC93.v:56-59, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_inv.v, with its module names changed; 579 of its 615 lines of code are new or changed and 300 lines of the source are left out. *)
(* sb_dec (fuzz_identity.asan-ubsan 0x835d0, listing offset AF_sb_dec = 0x2e5c), segment C: the release of the
   class-0 side-stack frame and the epilogue, 0x83790 (BASE + 0x301c) to the ret at 0x83830, ending in tsb_dec_post
   (lib/B/Prog/sb_dec.v). Its entry is segment B's exit predicate sbd_at2 (lib/B/Prog/SbDecSegB.v).
   The code: 0x83790..0x837a0 shadow byte 4 := 0xf8 and the released-frame magic word at F; 0x837a4 beqz s2 (s2 = F
   is not 0: not taken); 0x837a8..0x837c8 the 8 shadow bytes of the frame := 0xf5; 0x837cc ld a0,56(s2) (the flag
   address, the frame's last word) and 0x837d0 sb zero,0(a0), the flag store that releases the frame
   (IdentBFrame.aj_flag_store_pi); 0x837d4 j 0x837f8; 0x837f8..0x83830 the epilogue: sp := s0 - 128, the 12 reloads
   of ra, s0..s10 from [s0 - 96, s0), sp := sp + 128, ret.
   The model for the whole file is the proved caller-journal walk lib/B/Prog/sb_ch.v (sb_entry / sb_post / sb_go);
   the frame release follows cgif lib/A/AChx.v (add_flag_regionFL / paj_run_flag_sh / flag0 / wrangeFL). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib YC1g YC1h IdentBFrame IdentBCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import sb_dec SbDecSegB.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section h.
Variable B : asyms.
Definition sbd_segC_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (regs : bvmap 5 word) (b v md p cap n ov : Z)
    fpos S2 (regs2 : bvmap 5 word) mem2 md2,
  sbd_at2 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 regs2 mem2 md2 ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x301c) regs2 mem2 md2)
    (tsb_dec_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov).
Section walkC.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let RUNF := aj_flag_store_pi (PL := PL_identb) (PI := PI) B LAWS ML ASF FFL.
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Definition sbd_cx (regs : bvmap 5 word) (FL : Z) : list word :=
  [getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21;
   getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; Z_to_bv 64 FL;
   getr regs 1].
Definition sbd_cE (regs regs2 : bvmap 5 word) (FL : Z) : env := Eimg (Ereg regs2 (sbd_cx regs FL)).
Definition sbd_cflag_region : YP09.region := YP09.mkRegion (Some 43%nat) 0 1 0 1 [].
Definition sbd_cframe_region : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 64 0 8 [YP09.mkChunk 56 (CVal 8 (SOff 43 0))].
Definition sbd_cshadow_region : YP09.region := YP09.mkRegion (Some 24%nat) 0 8 0 8 [].
Definition sbd_cstack_region : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-96) 0 0 0
    [YP09.mkChunk (-96) (CVal 8 (SOff 42 0)); YP09.mkChunk (-88) (CVal 8 (SOff 41 0));
     YP09.mkChunk (-80) (CVal 8 (SOff 40 0)); YP09.mkChunk (-72) (CVal 8 (SOff 39 0));
     YP09.mkChunk (-64) (CVal 8 (SOff 38 0)); YP09.mkChunk (-56) (CVal 8 (SOff 37 0));
     YP09.mkChunk (-48) (CVal 8 (SOff 36 0)); YP09.mkChunk (-40) (CVal 8 (SOff 35 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 34 0)); YP09.mkChunk (-24) (CVal 8 (SOff 33 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 32 0)); YP09.mkChunk (-8) (CVal 8 (SOff 44 0))].
Definition sbd_cregions : smem :=
  [sbd_cflag_region; sbd_cframe_region; sbd_cshadow_region; sbd_cstack_region].
Definition sbd_cfacts : facts := mkFacts [(18%nat, HPTR 6)] [] [].
Definition sbd_cSR : list sv := sr_set sr_atoms 23%bv (SOff 18 0).
Definition sbd_css : sstate := mkSS 0x301c sbd_cSR sbd_cregions None sbd_cfacts.
Definition sbd_cwz (F SH FL : Z) (a : Z) : Prop := (F <= a < F + 8) \/ (SH <= a < SH + 8) \/ a = FL.
Lemma sbd_c_shb : forall F, 4096 <= F -> F + 64 <= alloc_ceiling ->
  kLowMemEnd <= SHADOW_OFF + F / 8 /\ SHADOW_OFF + F / 8 + 8 < kHighShadowEnd.
Proof.
intros F H1 H2. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (E64 : (F + 64) / 8 = F / 8 + 8) by (replace (F + 64) with (F + 8 * 8) by lia; apply Z.div_add; lia).
pose proof (shadow_addr_bounds F ltac:(clear - H1 H2 C1 C4; lia)) as (S1 & S2).
pose proof (shadow_addr_bounds (F + 64) ltac:(clear - H1 H2 C1 C4; lia)) as (S3 & S4).
unfold shadow_addr in S1, S2, S3, S4. rewrite E64 in S4. clear - S1 S4. lia.
Qed.
Lemma sbd_c_frames_free : forall S2 Sc fpos,
  frames S2 = (0, fpos) :: frames Sc -> frames (stack_free_state 0 fpos S2) = frames Sc.
Proof.
intros S2 Sc fpos Hfr. unfold frames, stack_free_state in *. cbn [set_fs st_fs fs_live] in *.
rewrite Hfr. cbn [del_pos]. rewrite Z.eqb_refl, Z.eqb_refl. cbn [andb]. reflexivity.
Qed.
Lemma sbd_c_ablocks_free : forall lyc cid pos S, ablocks B lyc (stack_free_state cid pos S) = ablocks B lyc S.
Proof. intros lyc cid pos S. unfold ablocks. rewrite blocks_stack_free_state. reflexivity. Qed.
Lemma sbd_c_val_keep : forall (W : world SEGS) (m m' : word -> option byte) a (nn : nat) v,
  (forall x, a <= x < a + Z.of_nat nn -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (mrestrict (w_H W) m) a nn v -> val_mem SEGS (mrestrict (w_H W) m') a nn v.
Proof.
intros W m m' a nn v Hk Hv.
apply (val_mem_moved SEGS (w_H W) (w_H W) m m' a a nn v); [|exact Hv].
intros j Hj. apply Hk. clear - Hj. lia.
Qed.
Lemma sbd_c_garr_keep : forall (W : world SEGS) (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros W m m' a l Hk Hg j Hj. destruct (Hg j Hj) as (Hv & Hr). split; [|exact Hr].
apply (sbd_c_val_keep W m m' (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros x Hx. apply Hk. clear - Hx Hj. lia.
Qed.
(* A byte of a heap block or of a frame of the caller's state is none of the bytes this segment writes. *)
Lemma sbd_c_notwz : forall lyc Sc S2 (W : world SEGS) mem2 md2 fpos F SH FL x,
  AR SEGS B lyc S2 W mem2 md2 -> frames S2 = (0, fpos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  F = frame_addr lyc 0 fpos -> FL = flag_addr lyc 0 fpos -> SH = SHADOW_OFF + F / 8 ->
  ((exists bb m, In (bb, m) (ablocks B lyc Sc) /\ bb <= x < bb + req_size m) \/
   (exists cid pos, In (cid, pos) (frames Sc) /\
      (in_zr x (frame_rng lyc (cid, pos)) \/
       in_zr x (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)))) ->
  ~ sbd_cwz F SH FL x /\ ~ in_frames lyc [(0, fpos)] x.
Proof.
intros lyc Sc S2 W mem2 md2 fpos F SH FL x HAR2 Hfr2 Hab2 EF EFL ESH Hx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin2 : In (0, fpos) (frames S2)) by (rewrite Hfr2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hin2) as (HF0 & HFc & HFapp).
change (fs_frame_bytes 0) with 64 in HFc, HFapp. rewrite <- EF in HF0, HFc, HFapp.
destruct (sbd_c_shb F HF0 HFc) as (HSHlo & HSHhi). rewrite <- ESH in HSHlo, HSHhi.
destruct (FFL lyc S2 W mem2 md2 0 fpos HAR2 Hin2) as (HFLpres & HFLown & (HFLapp & HFLnimg) & (HFL4096 & HFLz & HFLcl)).
rewrite <- EFL in HFLpres, HFLown, HFLapp, HFLnimg, HFL4096, HFLz, HFLcl.
assert (HIF : forall y, in_frames lyc [(0, fpos)] y -> (F <= y < F + 64) \/ (SH <= y < SH + 8)).
{ intros y (cid & pos & Hc & Hr). cbn [In] in Hc. destruct Hc as [Hc | []]. injection Hc as <- <-.
  unfold in_zr, shadow_addr in Hr. cbn [fst snd] in Hr.
  change (fs_frame_bytes 0) with 64 in Hr. change (64 / 8) with 8 in Hr.
  rewrite <- EF in Hr. rewrite <- ESH in Hr. exact Hr. }
destruct Hx as [(bb & m & Hbin & Hbx) | (cid & pos & Hcin & Hcr)].
- assert (Hbin2 : In (bb, m) (ablocks B lyc S2)) by (rewrite Hab2; exact Hbin).
  destruct (al_blocks SEGS B LAWS lyc S2 W mem2 md2 bb m HAR2 Hbin2) as (_ & Hb4096 & Hbc & Hbapp & Hbpres & _).
  pose proof (sep_block_frame SEGS B LAWS lyc S2 W mem2 md2 bb m 0 fpos HAR2 Hbin2 Hin2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. rewrite <- EF in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  assert (HnoF : ~ (F <= x < F + 64) /\ ~ (SH <= x < SH + 8)).
  { split; intros Hz; [clear - Hd Hbx Hz; lia |].
    unfold kLowMemEnd in HSHlo. unfold kHighShadowEnd in HSHhi.
    clear - Hbapp Hbx Hz HSHlo HSHhi C1 C2 C3 C5. lia. }
  assert (HnoFL : x <> FL).
  { intros ->. exact (proj2 (Hbpres FL Hbx) HFLown). }
  split.
  + intros [Hz | [Hz | Hz]]; [apply (proj1 HnoF); clear - Hz; lia | exact (proj2 HnoF Hz) | exact (HnoFL Hz)].
  + intros Hz. destruct (HIF x Hz) as [Hz2 | Hz2]; [exact (proj1 HnoF Hz2) | exact (proj2 HnoF Hz2)].
- assert (Hcin2 : In (cid, pos) (frames S2)) by (rewrite Hfr2; right; exact Hcin).
  apply in_split in Hcin as (l1 & l2 & El).
  assert (HFZ : forall y, (in_zr y (frame_rng lyc (cid, pos)) \/
                           in_zr y (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
                          ~ in_frames lyc [(0, fpos)] y).
  { intros y Hy Hz.
    apply (frames_zone_disj SEGS B LAWS lyc S2 W mem2 md2 (0, fpos) (cid, pos) [] l1 l2 y HAR2
      ltac:(rewrite Hfr2, El; reflexivity)); cbn [fst snd].
    - destruct (HIF y Hz) as [Hz2 | Hz2]; [left | right]; unfold in_zr, frame_rng, shadow_addr; cbn [fst snd];
      change (fs_frame_bytes 0) with 64; change (64 / 8) with 8; rewrite <- EF; try rewrite <- ESH;
      clear - Hz2; lia.
    - exact Hy. }
  destruct (al_frames SEGS B LAWS lyc S2 W mem2 md2 cid pos HAR2 Hcin2) as (_ & _ & Hfb & Hfs).
  assert (HnoFL : x <> FL).
  { intros ->. destruct Hcr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
    - exact (proj2 (Hfb FL ltac:(clear - Hr; lia)) HFLown).
    - unfold shadow_addr in Hr. cbn [fst snd] in Hr.
      pose proof (Hfs (FL - (SHADOW_OFF + frame_addr lyc cid pos / 8)) ltac:(clear - Hr; lia)) as Hp.
      unfold shadow_addr in Hp.
      replace (SHADOW_OFF + frame_addr lyc cid pos / 8 + (FL - (SHADOW_OFF + frame_addr lyc cid pos / 8)))
        with FL in Hp by (clear; lia).
      exact (proj2 Hp HFLown). }
  assert (HnoF : ~ in_frames lyc [(0, fpos)] x) by (apply HFZ; exact Hcr).
  split; [|exact HnoF].
  intros [Hz | [Hz | Hz]]; [| | exact (HnoFL Hz)];
  apply HnoF; exists 0, fpos; split; [left; reflexivity| |left; reflexivity|];
  unfold in_zr, shadow_addr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; change (64 / 8) with 8;
  rewrite <- EF; [left | right]; try rewrite <- ESH; clear - Hz; lia.
Qed.
(* The symbolic state at 0x83790 and the machine state it abstracts. *)
Lemma sbd_c_entry : forall (W : world SEGS) (regs regs2 : bvmap 5 word) mem2 F SH FL,
  getr regs2 18 = w64 F -> getr regs2 23 = w64 F -> getr regs2 24 = w64 SH -> SH = SHADOW_OFF + F / 8 ->
  4096 <= F -> F + 64 <= alloc_ceiling -> F mod 64 = 0 -> in_app F 64 ->
  app_addr FL -> FL < alloc_ceiling -> (FL + 1 <= F \/ F + 64 <= FL) ->
  alloc_ceiling + 4096 <= spZ regs -> spZ regs <= 2 ^ 47 ->
  (forall o, 0 <= o < 64 -> apresent (w_H W) mem2 (F + o)) ->
  (forall o, 0 <= o < 8 -> apresent (w_H W) mem2 (SH + o)) ->
  apresent (w_H W) mem2 FL ->
  rdword (aview SEGS (w_H W) mem2) (F + 64 - 8) = Some FL ->
  getr regs2 8 = getr regs 2 ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 80) 8 (bv_unsigned (getr regs 24)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 88) 8 (bv_unsigned (getr regs 25)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 96) 8 (bv_unsigned (getr regs 26)) ->
  st_ok_pi SEGS VAL (sbd_cE regs regs2 FL) sbd_css
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + 0x301c)) mem2 (seg_rom SEGS))).
Proof.
intros W regs regs2 mem2 F SH FL E18r E23r E24r ESH HF0 HFc HFal HFapp HFLapp HFLcl HFLF HSP0 HSP1
  HFpres HSHpres HFLpres Hflag E8 V1 V8 V9 V18 V19 V20 V21 V22 V23 V24 V25 V26.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (sbd_c_shb F HF0 HFc) as (HSHlo & HSHhi). rewrite <- ESH in HSHlo, HSHhi.
unfold kLowMemEnd in HSHlo. unfold kHighShadowEnd in HSHhi.
unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
set (E := sbd_cE regs regs2 FL).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs2 (sbd_cx regs FL)) i)
  by (intros i Hi; subst E; unfold sbd_cE; apply Eimg_low; exact Hi).
assert (E18 : ew E 18 = getr regs2 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 18 18%bv eq_refl)).
assert (E24 : ew E 24 = getr regs2 24) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 24 24%bv eq_refl)).
assert (E8w : ew E 8 = getr regs2 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
assert (X32 : ew E 32 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (X33 : ew E 33 = getr regs 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (X34 : ew E 34 = getr regs 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (X35 : ew E 35 = getr regs 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (X36 : ew E 36 = getr regs 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (X37 : ew E 37 = getr regs 21) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
assert (X38 : ew E 38 = getr regs 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 6)).
assert (X39 : ew E 39 = getr regs 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 7)).
assert (X40 : ew E 40 = getr regs 24) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 8)).
assert (X41 : ew E 41 = getr regs 25) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 9)).
assert (X42 : ew E 42 = getr regs 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 10)).
assert (X43 : ew E 43 = Z_to_bv 64 FL) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 11)).
assert (X44 : ew E 44 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 12)).
assert (UF : bv_unsigned (ew E 18) = F)
  by (rewrite E18, E18r; unfold w64; apply unsigned_lit_small; clear - HF0 HFc C1; lia).
assert (USH : bv_unsigned (ew E 24) = SH)
  by (rewrite E24, E24r; unfold w64; apply unsigned_lit_small; clear - HSHlo HSHhi; lia).
assert (UFL : bv_unsigned (ew E 43) = FL)
  by (rewrite X43; apply unsigned_lit_small; clear - HFLapp HFLcl C1; lia).
assert (USP : bv_unsigned (ew E 8) = spZ regs) by (rewrite E8w, E8; reflexivity).
assert (W8 : Z.of_N 8 <= 8) by (cbn; lia).
assert (BVR : forall x : word, 0 <= bv_unsigned x < 2 ^ (8 * Z.of_N 8)).
{ intros x. pose proof (bv_unsigned_in_range 64 x) as Hx. change (bv_modulus 64) with (2 ^ 64) in Hx.
  cbn [Z.of_N]. change (8 * 8) with 64. clear - Hx. lia. }
assert (FLR : 0 <= FL < 2 ^ (8 * Z.of_N 8))
  by (cbn [Z.of_N]; change (8 * 8) with 64; clear - HFLapp HFLcl C1; lia).
rewrite restrict_mkst_fx.
assert (RO_flag : region_ok SEGS E (mrestrict (w_H W) mem2) sbd_cflag_region).
{ unfold region_ok, sbd_cflag_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite UFL. split; [clear - HFLapp; lia|]. split; [clear - HFLapp HFLcl C1; lia|].
  split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS).
  replace (FL + o) with FL by (clear - Ho; lia). exact HFLpres. }
assert (RO_frame : region_ok SEGS E (mrestrict (w_H W) mem2) sbd_cframe_region).
{ unfold region_ok, sbd_cframe_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite UF. split; [clear - HF0; lia|]. split; [clear - HFc C1; lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply HFpres; clear - Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ F 56 8 _ FL);
  [ cbn [sv_denot]; rewrite X43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | exact FLR | exact W8 |].
  replace (F + 56) with (F + 64 - 8) by (clear; lia). exact (val_mem_of_rdword SEGS (w_H W) mem2 _ _ Hflag). }
assert (RO_shadow : region_ok SEGS E (mrestrict (w_H W) mem2) sbd_cshadow_region).
{ unfold region_ok, sbd_cshadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite USH. split; [clear - HSHlo; lia|]. split; [clear - HSHhi; lia|].
  split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply HSHpres. clear - Ho; lia. }
assert (RO_stack : region_ok SEGS E (mrestrict (w_H W) mem2) sbd_cstack_region).
{ unfold region_ok, sbd_cstack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite USP. split; [clear - HSP0 C1; lia|]. split; [clear - HSP1; lia|].
  split; [intros o Ho; exfalso; clear - Ho; lia|].
  apply Forall_cons; [apply (chunk_ok_val SEGS E _ (spZ regs) (-96) 8 _ (bv_unsigned (getr regs 26)));
    [cbn [sv_denot]; rewrite X42, Z.add_0_r; reflexivity | exact (BVR _) | exact W8
    | replace (spZ regs + -96) with (spZ regs - 96) by (clear; lia); exact V26] |].
  apply Forall_cons; [apply (chunk_ok_val SEGS E _ (spZ regs) (-88) 8 _ (bv_unsigned (getr regs 25)));
    [cbn [sv_denot]; rewrite X41, Z.add_0_r; reflexivity | exact (BVR _) | exact W8
    | replace (spZ regs + -88) with (spZ regs - 88) by (clear; lia); exact V25] |].
  apply Forall_cons; [apply (chunk_ok_val SEGS E _ (spZ regs) (-80) 8 _ (bv_unsigned (getr regs 24)));
    [cbn [sv_denot]; rewrite X40, Z.add_0_r; reflexivity | exact (BVR _) | exact W8
    | replace (spZ regs + -80) with (spZ regs - 80) by (clear; lia); exact V24] |].
  apply Forall_cons; [apply (chunk_ok_val SEGS E _ (spZ regs) (-72) 8 _ (bv_unsigned (getr regs 23)));
    [cbn [sv_denot]; rewrite X39, Z.add_0_r; reflexivity | exact (BVR _) | exact W8
    | replace (spZ regs + -72) with (spZ regs - 72) by (clear; lia); exact V23] |].
  apply Forall_cons; [apply (chunk_ok_val SEGS E _ (spZ regs) (-64) 8 _ (bv_unsigned (getr regs 22)));
    [cbn [sv_denot]; rewrite X38, Z.add_0_r; reflexivity | exact (BVR _) | exact W8
    | replace (spZ regs + -64) with (spZ regs - 64) by (clear; lia); exact V22] |].
  apply Forall_cons; [apply (chunk_ok_val SEGS E _ (spZ regs) (-56) 8 _ (bv_unsigned (getr regs 21)));
    [cbn [sv_denot]; rewrite X37, Z.add_0_r; reflexivity | exact (BVR _) | exact W8
    | replace (spZ regs + -56) with (spZ regs - 56) by (clear; lia); exact V21] |].
  apply Forall_cons; [apply (chunk_ok_val SEGS E _ (spZ regs) (-48) 8 _ (bv_unsigned (getr regs 20)));
    [cbn [sv_denot]; rewrite X36, Z.add_0_r; reflexivity | exact (BVR _) | exact W8
    | replace (spZ regs + -48) with (spZ regs - 48) by (clear; lia); exact V20] |].
  apply Forall_cons; [apply (chunk_ok_val SEGS E _ (spZ regs) (-40) 8 _ (bv_unsigned (getr regs 19)));
    [cbn [sv_denot]; rewrite X35, Z.add_0_r; reflexivity | exact (BVR _) | exact W8
    | replace (spZ regs + -40) with (spZ regs - 40) by (clear; lia); exact V19] |].
  apply Forall_cons; [apply (chunk_ok_val SEGS E _ (spZ regs) (-32) 8 _ (bv_unsigned (getr regs 18)));
    [cbn [sv_denot]; rewrite X34, Z.add_0_r; reflexivity | exact (BVR _) | exact W8
    | replace (spZ regs + -32) with (spZ regs - 32) by (clear; lia); exact V18] |].
  apply Forall_cons; [apply (chunk_ok_val SEGS E _ (spZ regs) (-24) 8 _ (bv_unsigned (getr regs 9)));
    [cbn [sv_denot]; rewrite X33, Z.add_0_r; reflexivity | exact (BVR _) | exact W8
    | replace (spZ regs + -24) with (spZ regs - 24) by (clear; lia); exact V9] |].
  apply Forall_cons; [apply (chunk_ok_val SEGS E _ (spZ regs) (-16) 8 _ (bv_unsigned (getr regs 8)));
    [cbn [sv_denot]; rewrite X32, Z.add_0_r; reflexivity | exact (BVR _) | exact W8
    | replace (spZ regs + -16) with (spZ regs - 16) by (clear; lia); exact V8] |].
  apply Forall_cons; [apply (chunk_ok_val SEGS E _ (spZ regs) (-8) 8 _ (bv_unsigned (getr regs 1)));
    [cbn [sv_denot]; rewrite X44, Z.add_0_r; reflexivity | exact (BVR _) | exact W8
    | replace (spZ regs + -8) with (spZ regs - 8) by (clear; lia); exact V1] |].
  apply Forall_nil. }
assert (A18 : afact_ok E 18 (HPTR 6)).
{ unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2]. rewrite UF. change (2 ^ 6) with 64.
  split; [clear - HF0 HFc C1; lia|]. split; [exact HFal | clear; lia]. }
assert (HD : zpairwise_disjoint (map (extent_of_region E) sbd_cregions)).
{ unfold sbd_cregions, sbd_cflag_region, sbd_cframe_region, sbd_cshadow_region, sbd_cstack_region,
    extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite UF, USH, UFL, USP.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  clear - HF0 HFc HFapp HFLapp HFLcl HFLF HSHlo HSHhi HSP0 HSP1 C1 C2 C3 C4 C5.
  repeat split; lia. }
assert (HS0 : st_ok_pi SEGS VAL E (mkSS 0x301c sr_atoms sbd_cregions None sbd_cfacts)
  (mkst regs2 (Z_to_bv 64 (BASE + 0x301c)) (mrestrict (w_H W) mem2) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  - subst E. unfold sbd_cE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold sbd_cregions. repeat apply Forall_cons; try apply Forall_nil;
    first [exact RO_flag | exact RO_frame | exact RO_shadow | exact RO_stack].
  - apply pairwise_disjoint_of_extents. exact HD.
  - unfold facts_ok, sbd_cfacts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [split; [exact A18 | exact I] | split; exact I]. }
assert (Hv : sv_denot E (SOff 18 0)
  = getr (ms_regs (mkst regs2 (Z_to_bv 64 (BASE + 0x301c)) (mrestrict (w_H W) mem2) (seg_rom SEGS))) 23).
{ cbn [ms_regs mkst restrict sv_denot]. rewrite UF, Z.add_0_r, E23r. reflexivity. }
pose proof (ast_ok_pi_set_reg_fp E _ _ (23%bv : bv 5) (SOff 18 0) HS0 ltac:(vm_compute; reflexivity) Hv) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
exact HS1.
Qed.
(* The post at the return slot. *)
Lemma sbd_c_post : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mem2 md2 k
  (regs : bvmap 5 word) (b v md p cap n ov fpos : Z) S2 (regsF : bvmap 5 word) memF mdF F SH FL,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc (stack_free_state 0 fpos S2) W memF mdF k ->
  AR SEGS B lyc S2 W mem2 md2 ->
  frames S2 = (0, fpos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  F = frame_addr lyc 0 fpos -> FL = flag_addr lyc 0 fpos -> SH = SHADOW_OFF + F / 8 ->
  alloc_ceiling <= ly_stk_lo lyc ->
  YK0s.ret_ok (getr regs 1) -> getr regsF 1 = getr regs 1 -> aregs_preserved regs regsF ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ sbd_cwz F SH FL a -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem2 a) ->
  mem_grows (mrestrict (w_H W) mem2) (mrestrict (w_H W) memF) ->
  tcj_kept B SB_DEC_STK lyc Sc W memc W mem2 (spZ regs)
    (fun a => tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n) a \/ in_frames lyc [(0, fpos)] a) ->
  tsb_dec_rec_at lyc b ->
  (0 < sb_dec_c.sb_dec_room cap n -> tdst_ok B lyc Sc (p + n) (sb_dec_c.sb_dec_acc v md cap n)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) b 8 p ->
  val_mem SEGS (mrestrict (w_H W) mem2) (b + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) mem2) (b + 16) 8 (n + sb_dec_c.sb_dec_acc v md cap n) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (b + 24) 4
    (if sb_dec_c.sb_dec_room cap n <? Z.of_nat (length (sb_dec_c.sb_dec_D v md)) then 1 else ov) ->
  garr8 SEGS (mrestrict (w_H W) mem2) (p + n)
    (firstn (Z.to_nat (sb_dec_c.sb_dec_acc v md cap n)) (sb_dec_c.sb_dec_D v md)) ->
  tsb_dec_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov W
    (mkCfg (mkst regsF (v_jalr (getr regsF 1) 0) memF (seg_rom SEGS)) mdF).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mem2 md2 k regs b v md p cap n ov fpos S2 regsF memF mdF
  F SH FL HJF HAR2 Hfr2 Hab2 EF EFL ESH HSLO Hra R1 HP KEEPF HG KEEP2 HRECAT HDST Vp Vcap Vn Vov Vd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_segs_low) as Hsegs.
assert (Hin2 : In (0, fpos) (frames S2)) by (rewrite Hfr2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hin2) as (HF0 & HFc & HFapp).
change (fs_frame_bytes 0) with 64 in HFc, HFapp. rewrite <- EF in HF0, HFc, HFapp.
destruct (sbd_c_shb F HF0 HFc) as (HSHlo & HSHhi). rewrite <- ESH in HSHlo, HSHhi.
destruct (FFL lyc S2 W mem2 md2 0 fpos HAR2 Hin2) as (HFLpres & HFLown & (HFLapp & HFLnimg) & (HFL4096 & HFLz & HFLcl)).
rewrite <- EFL in HFLpres, HFLown, HFLapp, HFLnimg, HFL4096, HFLz, HFLcl.
pose proof (frm_off_imgP B lyc S2 W mem2 md2 0 fpos HAR2 Hin2) as HFimg.
change (fs_frame_bytes 0) with 64 in HFimg. rewrite <- EF in HFimg.
pose proof (lo_top lyc (am_layout B lyc S2 _ (proj1 HAR2))) as (L1 & (L2 & L3) & L4 & L5 & L6 & L7 & L8).
unfold kLowMemEnd in HSHlo. unfold kHighShadowEnd in HSHhi.
destruct KEEP2 as (K1 & K2 & K3 & K4 & K5 & K6).
(* nothing above the allocator ceiling is written here *)
assert (NWhi : forall a, alloc_ceiling <= a -> ~ sbd_cwz F SH FL a)
  by (intros a Ha [Hz | [Hz | Hz]]; clear - Ha Hz HFc HSHhi HFLcl C1; lia).
assert (NFhi : forall a, alloc_ceiling <= a -> ~ in_frames lyc [(0, fpos)] a).
{ intros a Ha (cid & pos & Hc & Hr). cbn [In] in Hc. destruct Hc as [Hc | []]. injection Hc as <- <-.
  unfold in_zr, shadow_addr in Hr. cbn [fst snd] in Hr.
  change (fs_frame_bytes 0) with 64 in Hr. change (64 / 8) with 8 in Hr.
  rewrite <- EF in Hr. rewrite <- ESH in Hr. clear - Ha Hr HFc HSHhi C1. lia. }
(* the caller's struct lies in the machine stack, above the allocator ceiling *)
assert (NWb : forall x, b <= x < b + 28 -> ~ sbd_cwz F SH FL x).
{ intros x Hx. apply NWhi. unfold tsb_dec_rec_at in HRECAT. clear - Hx HRECAT HSLO. lia. }
assert (KEEPb : forall x, b <= x < b + 28 -> aview SEGS (w_H W) memF x = aview SEGS (w_H W) mem2 x).
{ intros x Hx. apply KEEPF; [|exact (NWb x Hx)].
  unfold tsb_dec_rec_at in HRECAT. unfold kHighMemEnd in L5. clear - Hx HRECAT HSLO L2 L3 L5 C1. lia. }
(* the digits lie in the caller's blocks or frames *)
assert (KEEPd : forall x, p + n <= x < p + n + sb_dec_c.sb_dec_acc v md cap n ->
  aview SEGS (w_H W) memF x = aview SEGS (w_H W) mem2 x).
{ intros x Hx.
  assert (Hroom : 0 < sb_dec_c.sb_dec_room cap n).
  { unfold sb_dec_c.sb_dec_acc in Hx. pose proof (Z.le_min_r (Z.of_nat (length (sb_dec_c.sb_dec_D v md)))
      (sb_dec_c.sb_dec_room cap n)) as Hm. clear - Hx Hm. lia. }
  destruct (HDST Hroom x ltac:(clear - Hx; lia)) as [Hc | Hc].
  - destruct Hc as (bb & m & Hbin & Hbx).
    destruct (al_blocks SEGS B LAWS lyc S2 W mem2 md2 bb m HAR2 ltac:(rewrite Hab2; exact Hbin))
      as (_ & Hb4096 & Hbc & _ & _ & _).
    apply KEEPF; [clear - Hbx Hbc Hb4096 C1; lia|].
    exact (proj1 (sbd_c_notwz lyc Sc S2 W mem2 md2 fpos F SH FL x HAR2 Hfr2 Hab2 EF EFL ESH
      (or_introl (ex_intro _ bb (ex_intro _ m (conj Hbin Hbx)))))).
  - destruct Hc as (cid & pos & Hcin & Hcr).
    destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 cid pos HAR2 ltac:(rewrite Hfr2; right; exact Hcin))
      as (Hc0 & Hcc & _).
    unfold in_zr, frame_rng in Hcr. cbn [fst snd] in Hcr.
    apply KEEPF; [clear - Hcr Hc0 Hcc C1; lia|].
    exact (proj1 (sbd_c_notwz lyc Sc S2 W mem2 md2 fpos F SH FL x HAR2 Hfr2 Hab2 EF EFL ESH
      (or_intror (ex_intro _ cid (ex_intro _ pos (conj Hcin (or_introl Hcr))))))). }
unfold tsb_dec_post. split; [reflexivity|].
exists lyc, (stack_free_state 0 fpos S2), regsF, memF, mdF.
split; [rewrite R1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [replace (k + EV_SB_DEC) with k by (unfold EV_SB_DEC; clear; lia); exact HJF|].
split; [exact HP|].
split; [exact (sbd_c_frames_free S2 Sc fpos Hfr2)|].
split; [rewrite sbd_c_ablocks_free, Hab2; apply Permutation_refl|].
split.
{ unfold tcj_kept. split.
  { intros a Ha Hs Hw. rewrite (KEEPF a ltac:(clear - Ha C1; lia) (NWhi a ltac:(clear - Ha; lia))).
    apply K1; [exact Ha | exact Hs|]. intros [Hz | Hz]; [exact (Hw Hz) | exact (NFhi a ltac:(clear - Ha; lia) Hz)]. }
  split.
  { intros bb m i Hbin Hi Hw.
    destruct (al_blocks SEGS B LAWS lyc S2 W mem2 md2 bb m HAR2 ltac:(rewrite Hab2; exact Hbin))
      as (_ & Hb4096 & Hbc & _ & _ & _).
    assert (Hbx : bb <= bb + i < bb + req_size m) by (clear - Hi; lia).
    destruct (sbd_c_notwz lyc Sc S2 W mem2 md2 fpos F SH FL (bb + i) HAR2 Hfr2 Hab2 EF EFL ESH
      (or_introl (ex_intro _ bb (ex_intro _ m (conj Hbin Hbx))))) as (NW & NF).
    rewrite (KEEPF (bb + i) ltac:(clear - Hi Hbc Hb4096 C1; lia) NW).
    apply (K2 bb m i Hbin Hi). intros [Hz | Hz]; [exact (Hw Hz) | exact (NF Hz)]. }
  split.
  { intros a Hi Hns He.
    pose proof (Hsegs a Hi) as Hlow. pose proof (pa_img_range a Hi) as Hrng. unfold kLowMemEnd in Hlow.
    rewrite (KEEPF a ltac:(clear - Hlow C5; lia)).
    - apply K3; [exact Hi | exact Hns | exact He].
    - intros [Hz | [Hz | Hz]]; [clear - Hz Hrng HFimg; lia | clear - Hz Hrng HSHlo; lia |].
      apply HFLnimg. rewrite <- Hz. exact Hi. }
  split.
  { intros cid pos a Hcin Hr Hw.
    destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 cid pos HAR2 ltac:(rewrite Hfr2; right; exact Hcin))
      as (Hc0 & Hcc & _).
    destruct (frame_zone SEGS B LAWS lyc S2 W mem2 md2 cid pos a HAR2 ltac:(rewrite Hfr2; right; exact Hcin) Hr)
      as (Hac & Hain).
    assert (Ha64 : 0 <= a < 2 ^ 64)
      by (destruct Hain as [(Hz1 & _) | Hz1]; clear - Hz1 Hac Hc0 C1 C5; unfold kLowMemEnd in Hz1; lia).
    destruct (sbd_c_notwz lyc Sc S2 W mem2 md2 fpos F SH FL a HAR2 Hfr2 Hab2 EF EFL ESH
      (or_intror (ex_intro _ cid (ex_intro _ pos (conj Hcin Hr))))) as (NW & NF).
    rewrite (KEEPF a Ha64 NW).
    apply (K4 cid pos a Hcin Hr). intros [Hz | Hz]; [exact (Hw Hz) | exact (NF Hz)]. }
  split.
  { intros a Ha Hs Hp. apply (apresent_grows (w_H W) mem2 memF a HG). apply K5; assumption. }
  { intros a Ha. apply (apresent_grows (w_H W) mem2 memF a HG). apply K6. exact Ha. } }
split; [apply (sbd_c_val_keep W mem2 memF b 8 p); [intros x Hx; apply KEEPb; clear - Hx; cbn in Hx; lia | exact Vp]|].
split; [apply (sbd_c_val_keep W mem2 memF (b + 8) 8 cap);
  [intros x Hx; apply KEEPb; clear - Hx; cbn in Hx; lia | exact Vcap]|].
split; [apply (sbd_c_val_keep W mem2 memF (b + 16) 8 (n + sb_dec_c.sb_dec_acc v md cap n));
  [intros x Hx; apply KEEPb; clear - Hx; cbn in Hx; lia | exact Vn]|].
split; [apply (sbd_c_val_keep W mem2 memF (b + 24) 4 _);
  [intros x Hx; apply KEEPb; clear - Hx; cbn in Hx; lia | exact Vov]|].
apply (sbd_c_garr_keep W mem2 memF (p + n) _); [|exact Vd].
intros x Hx. apply KEEPd.
pose proof (length_firstn (Z.to_nat (sb_dec_c.sb_dec_acc v md cap n)) (sb_dec_c.sb_dec_D v md)) as Hlen.
pose proof (Z.le_min_r (Z.of_nat (length (sb_dec_c.sb_dec_D v md))) (sb_dec_c.sb_dec_room cap n)) as Hm.
pose proof (Z.le_min_l (Z.of_nat (length (sb_dec_c.sb_dec_D v md))) (sb_dec_c.sb_dec_room cap n)) as Hm2.
unfold sb_dec_c.sb_dec_acc in *. clear - Hx Hlen Hm Hm2. lia.
Qed.
Theorem sbd_segC : sbd_segC_spec.
Proof.
unfold sbd_segC_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 regs2 mem2 md2 HAT.
destruct HAT as (HJ & Hfr2 & Hab2 & Hra & Hal16 & Hwlo & Hwhi & Hflag & R3 & R4 & R8 &
  R18 & R23 & R24 & R27 & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 &
  HRECAT & Vp & Vcap & Vn & Vov & Vd & HDST & KEEP2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_segs_low) as Hsegs.
pose proof HJ as (HAR2 & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres
  & Hstatic & F5 & HQT).
pose proof Hstatic as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ESLO & _).
assert (HSTK : SB_DEC_STK = 4256) by reflexivity.
assert (Hin2 : In (0, fpos) (frames S2)) by (rewrite Hfr2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hin2) as (HF0 & HFc & HFapp).
change (fs_frame_bytes 0) with 64 in HFc, HFapp.
destruct (frame_al64 SEGS B lyc S2 W mem2 md2 0 fpos HAR2 Hin2) as (HFal & _ & _).
destruct (FFL lyc S2 W mem2 md2 0 fpos HAR2 Hin2)
  as (HFLpres & HFLown & (HFLapp & HFLnimg) & (HFL4096 & HFLz & HFLcl)).
destruct (al_frames SEGS B LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hin2) as (_ & _ & Hfb & Hfs).
change (fs_frame_bytes 0) with 64 in Hfb, Hfs. change (64 / 8) with 8 in Hfs.
unfold shadow_addr in Hfs.
destruct (sbd_c_shb (frame_addr lyc 0 fpos) HF0 HFc) as (HSHlo & HSHhi).
unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
unfold kLowMemEnd in HSHlo. unfold kHighShadowEnd in HSHhi.
assert (HSLO : alloc_ceiling <= ly_stk_lo lyc) by (rewrite ESLO; exact Hceil).
assert (HSP0 : alloc_ceiling + 4096 <= spZ regs) by (clear - Hceil Hslo Hwlo HSTK; lia).
assert (HSP1 : spZ regs <= 2 ^ 47) by (clear - Hwhi Hshi H47; lia).
assert (HFpres : forall o, 0 <= o < 64 -> apresent (w_H W) mem2 (frame_addr lyc 0 fpos + o))
  by (intros o Ho; exact (proj1 (Hfb (frame_addr lyc 0 fpos + o) ltac:(clear - Ho; lia)))).
assert (HSHpres : forall o, 0 <= o < 8 ->
  apresent (w_H W) mem2 (SHADOW_OFF + frame_addr lyc 0 fpos / 8 + o))
  by (intros o Ho; exact (proj1 (Hfs o Ho))).
assert (HFLF : flag_addr lyc 0 fpos + 1 <= frame_addr lyc 0 fpos \/
               frame_addr lyc 0 fpos + 64 <= flag_addr lyc 0 fpos).
{ destruct (Z_lt_ge_dec (flag_addr lyc 0 fpos) (frame_addr lyc 0 fpos)) as [Hc|Hc];
  [left; clear - Hc; lia|].
  destruct (Z_lt_ge_dec (flag_addr lyc 0 fpos) (frame_addr lyc 0 fpos + 64)) as [Hc2|Hc2];
  [exfalso | right; clear - Hc2; lia].
  exact (proj2 (Hfb (flag_addr lyc 0 fpos) ltac:(clear - Hc Hc2; lia)) HFLown). }
remember (sbd_cE regs regs2 (flag_addr lyc 0 fpos)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; unfold sbd_cE; apply Eimg_env).
assert (ELt : forall i, (i < A_TEXT)%nat ->
  ew E i = ew (Ereg regs2 (sbd_cx regs (flag_addr lyc 0 fpos))) i)
  by (intros i Hi; rewrite HE; unfold sbd_cE; apply Eimg_low; exact Hi).
assert (E3w : ew E 3 = getr regs2 3) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 3 3%bv eq_refl)).
assert (E4w : ew E 4 = getr regs2 4) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 4 4%bv eq_refl)).
assert (E8w : ew E 8 = getr regs2 8) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
assert (E18w : ew E 18 = getr regs2 18) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 18 18%bv eq_refl)).
assert (E24w : ew E 24 = getr regs2 24) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 24 24%bv eq_refl)).
assert (E27w : ew E 27 = getr regs2 27) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 27 27%bv eq_refl)).
assert (X32 : ew E 32 = getr regs 8) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (X33 : ew E 33 = getr regs 9) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (X34 : ew E 34 = getr regs 18) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (X35 : ew E 35 = getr regs 19) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (X36 : ew E 36 = getr regs 20) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (X37 : ew E 37 = getr regs 21) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
assert (X38 : ew E 38 = getr regs 22) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 6)).
assert (X39 : ew E 39 = getr regs 23) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 7)).
assert (X40 : ew E 40 = getr regs 24) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 8)).
assert (X41 : ew E 41 = getr regs 25) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 9)).
assert (X42 : ew E 42 = getr regs 26) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 10)).
assert (X43 : ew E 43 = Z_to_bv 64 (flag_addr lyc 0 fpos))
  by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 11)).
assert (X44 : ew E 44 = getr regs 1) by (rewrite ELt by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 12)).
assert (UF : bv_unsigned (ew E 18) = frame_addr lyc 0 fpos)
  by (rewrite E18w, R18; unfold w64; apply unsigned_lit_small; clear - HF0 HFc C1; lia).
assert (USH : bv_unsigned (ew E 24) = SHADOW_OFF + frame_addr lyc 0 fpos / 8)
  by (rewrite E24w, R24; unfold w64; apply unsigned_lit_small; clear - HSHlo HSHhi; lia).
assert (UFL : bv_unsigned (ew E 43) = flag_addr lyc 0 fpos)
  by (rewrite X43; apply unsigned_lit_small; clear - HFLapp HFLcl C1; lia).
assert (USP : bv_unsigned (ew E 8) = spZ regs) by (rewrite E8w, R8; reflexivity).
clear ELt.
pose proof (sbd_c_entry W regs regs2 mem2 (frame_addr lyc 0 fpos)
  (SHADOW_OFF + frame_addr lyc 0 fpos / 8) (flag_addr lyc 0 fpos)
  R18 R23 R24 eq_refl HF0 HFc HFal HFapp
  ltac:(unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; clear - HFLapp; lia)
  HFLcl HFLF HSP0 HSP1 HFpres HSHpres HFLpres Hflag R8
  V1 V8 V9 V18 V19 V20 V21 V22 V23 V24 V25 V26) as HS.
rewrite <- HE in HS. clear HE.
unfold cfg_at. change (w64 (BASE + 0x301c)) with (Z_to_bv 64 (BASE + 0x301c)).
paj_run_flag_sh RUNF HS HJ.
- clear; lia.
- intros a (r & Hin & Hr). vm_compute in Hin.
  destruct Hin as [Hin | [Hin | [Hin | [Hin | []]]]]; subst r;
  cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr.
  + rewrite UFL in Hr. right. clear - Hr. lia.
  + rewrite UF in Hr. left. right. right. right. exists 0, fpos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. clear - Hr. lia.
  + rewrite USH in Hr. left. right. right. right. exists 0, fpos. split; [left; reflexivity|].
    right. unfold in_zr, shadow_addr. cbn [fst snd].
    change (fs_frame_bytes 0) with 64. change (64 / 8) with 8. clear - Hr. lia.
  + rewrite USP in Hr. exfalso. clear - Hr. lia.
- intros msr HSr.
  pose proof (st_ok_pi_region_nth E _ msr 0%nat _ HSr eq_refl) as HR.
  cbn [ms_mem] in HR.
  pose proof (field_of_region E (ms_mem msr) 43%nat (flag_addr lyc 0 fpos) _ 0 1 0 1 0 1%N (SLit 0) 0 HR
    UFL ltac:(left; reflexivity) ltac:(cbn [sv_denot zcanon]; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(cbn; lia)) as V0.
  cbn [Z.of_nat N.to_nat le_byte] in V0. rewrite Z.add_0_r in V0. exact V0.
- assert (KEEPF : forall a, 0 <= a < 2 ^ 64 ->
    ~ sbd_cwz (frame_addr lyc 0 fpos) (SHADOW_OFF + frame_addr lyc 0 fpos / 8) (flag_addr lyc 0 fpos) a ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem2 a).
  { intros a Ha Hz.
    refine (kept_of_frame E (ss_mem sbd_css) (w_H W) mem2 (ms_mem ms) _ HFr _ a Ha Hz).
    intros bq wlo whi x Hin Hx. vm_compute in Hin.
    repeat (destruct Hin as [Hin | Hin];
      [ injection Hin as <- <- <-; cbn [base_val] in Hx;
        repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Hx end;
        unfold sbd_cwz; clear - Hx; lia | ]);
    destruct Hin. }
  eapply (RET W E _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  apply (sbd_c_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mem2 md2 k regs b v md p cap n ov fpos S2
    (ms_regs ms) (ms_mem ms) _ (frame_addr lyc 0 fpos)
    (SHADOW_OFF + frame_addr lyc 0 fpos / 8) (flag_addr lyc 0 fpos)).
  + apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ.
  + exact HAR2.
  + exact Hfr2.
  + exact Hab2.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + exact HSLO.
  + exact Hra.
  + prreg HS (1%bv : bv 5) RR1. rewrite RR1, X44. reflexivity.
  + apply aregs_preserved_eqs.
    * prreg HS (2%bv : bv 5) RR2. rewrite RR2, E8w, R8. reflexivity.
    * prreg HS (3%bv : bv 5) RR3. rewrite RR3, E3w, R3. reflexivity.
    * prreg HS (4%bv : bv 5) RR4. rewrite RR4, E4w, R4. reflexivity.
    * prreg HS (8%bv : bv 5) RR8. rewrite RR8, X32. reflexivity.
    * prreg HS (9%bv : bv 5) RR9. rewrite RR9, X33. reflexivity.
    * prreg HS (18%bv : bv 5) RRa. rewrite RRa, X34. reflexivity.
    * prreg HS (19%bv : bv 5) RRb. rewrite RRb, X35. reflexivity.
    * prreg HS (20%bv : bv 5) RRc. rewrite RRc, X36. reflexivity.
    * prreg HS (21%bv : bv 5) RRd. rewrite RRd, X37. reflexivity.
    * prreg HS (22%bv : bv 5) RRe. rewrite RRe, X38. reflexivity.
    * prreg HS (23%bv : bv 5) RRf. rewrite RRf, X39. reflexivity.
    * prreg HS (24%bv : bv 5) RRg. rewrite RRg, X40. reflexivity.
    * prreg HS (25%bv : bv 5) RRh. rewrite RRh, X41. reflexivity.
    * prreg HS (26%bv : bv 5) RRi. rewrite RRi, X42. reflexivity.
    * prreg HS (27%bv : bv 5) RRj. rewrite RRj, E27w, R27. reflexivity.
  + exact KEEPF.
  + exact HG.
  + exact KEEP2.
  + exact HRECAT.
  + exact HDST.
  + exact Vp.
  + exact Vcap.
  + exact Vn.
  + exact Vov.
  + exact Vd.
Qed.
End walkC.
End h.
End f.
End d.
