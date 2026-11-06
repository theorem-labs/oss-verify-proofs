(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_lay_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of ctrl_lay_block on image B (fuzz_grant.asan-ubsan), ported from
   image A's closed walk lib/A/Prog/CtrlLayBlock.v (a working branch 5aae1e8a0ce), itself written with proof steps adapted
   from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, AC8k.v, AChz.v, ACa2.v and ACb8.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlLayBlock.v, with its module paths, module names and numbers changed; 805 of its 880 lines of code are new or changed and 987 lines of the source are left out. *)
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
#[local] Notation treac_hunt_observe_spec := (@ReacHuntObserveCore.treac_hunt_observe_spec rc SK PI B).
#[local] Notation ho_count := (@ReacHuntObserveCore.ho_count rc PI).
#[local] Notation EHO := (@ReacHuntObserveCore.EHO rc PI).
#[local] Notation ho_shent_gen := (@ReacHuntObserveCore.ho_shent_gen rc PI).
#[local] Notation ho_pre := (@ReacHuntObserveCore.ho_pre rc SK PI B).
#[local] Notation ho_mid := (@ReacHuntObserveCore.ho_mid rc SK PI B).
#[local] Notation ho_fsh := (@ReacHuntObserveCore.ho_fsh rc PI).
#[local] Notation ho_saved := (@ReacHuntObserveCore.ho_saved rc PI).
#[local] Notation ho_regs_mid := (@ReacHuntObserveCore.ho_regs_mid rc PI B).
#[local] Notation ho_sp1 := (@ReacHuntObserveCore.ho_sp1 rc PI).
#[local] Notation ho_base := (@ReacHuntObserveCore.ho_base rc SK PI B).
#[local] Notation ho_seg_C_stmt := (@ReacHuntObserveCore.ho_seg_C_stmt rc SK PI B).
#[local] Notation hoT_aview_frame := (@ReacHuntObserveCore.hoT_aview_frame rc PI).
#[local] Notation hoT_garr_kept := (@ReacHuntObserveCore.hoT_garr_kept rc PI).
Hypothesis ho_entry : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs : bvmap 5 word) (h n hb hn : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 h ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_HUNT_OBSERVE_STK -> spZ regs <= sp0 ->
  In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn ->
  0 < h -> h mod 8 = 0 -> 0 <= n <= 8 ->
  val_mem SEGS (mrestrict (w_H W) memc) (h + 384) 4 n ->
  st_ok_pi SEGS VAL (EHO regs n (as_uar_cell B)) ss_ho
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_reac_hunt_observe)) memc (seg_rom SEGS))) /\
  sh_ok SEGS HOBx ho_SH (EHO regs n (as_uar_cell B)) (mrestrict (w_H W) memc).

Lemma denot_add0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
intros E e. rewrite (denot_lit_U E (SAlu ALU_ADD e (SLit 0))), (denot_lit_U E e). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
exact (zcanon_id _ (U_range E e)).
Qed.

Lemma ho_kept_inblk : forall E lyc2 Sc2 W1 memc1 W2 mem2 slo shi (Er : Z -> Prop) nn lo hi wlo whi cs p b m ly2 S2 md2,
  acall_kept SEGS B lyc2 Sc2 W1 memc1 W2 mem2 slo shi Er -> AR SEGS B ly2 S2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
  bv_unsigned (ew E nn) = p -> In (b, m) (ablocks B lyc2 Sc2) -> b <= p + lo -> p + hi <= b + req_size m ->
  lo <= wlo -> whi <= hi -> (forall a, p + lo <= a < p + hi -> ~ Er a) ->
  region_kept SEGS E (mrestrict (w_H W1) memc1) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some nn) lo hi wlo whi cs).
Proof.
intros E lyc2 Sc2 W1 memc1 W2 mem2 slo shi Er nn lo hi wlo whi cs p b m ly2 S2 md2 (_ & K2 & _) HAR2 Hin2 Hn Hin Hlo Hhi Hwlo Hwhi HnE.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres2 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
  replace (b + (a - b)) with a by lia. apply HnE. exact Ha.
- intros _. apply (apresent_writable SEGS). apply (proj1 (Hpres2 a ltac:(lia))).
Qed.

Lemma hoT_awr_mv : forall STK sp0 FP bl0 blc blc' ly ly' own x a,
  Permutation blc' blc -> (forall cid p, frame_addr ly' cid p = frame_addr ly cid p) ->
  awr_byte STK sp0 FP bl0 blc ly own a ->
  awr_byte STK sp0 FP bl0 blc' ly' (x :: own) a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own x a HP HF
  [H | [[H1 (b & n & Hin & Hr)] | [(b & n & Hin & Hn0 & Hr) | (cid & pos & Hin & Hr)]]].
- left. exact H.
- right; left. split; [exact H1|]. exists b, n.
  split; [apply (Permutation_in _ (Permutation_sym HP)); exact Hin | exact Hr].
- right; right; left. exists b, n.
  split; [apply (Permutation_in _ (Permutation_sym HP)); exact Hin|].
  split; [exact Hn0 | exact Hr].
- right; right; right. exists cid, pos. split; [right; exact Hin|].
  rewrite (HF cid pos). exact Hr.
Qed.

Lemma hoA_chunk_byte : forall E (m : word -> option byte) (nb : nat) (b : Z) cs lo hi wlo whi (off v : Z),
  region_ok SEGS E m (YP09.mkRegion (Some nb) lo hi wlo whi cs) ->
  base_val E (Some nb) = b ->
  In (YP09.mkChunk off (CVal 1 (SLit v))) cs ->
  mbyte SEGS m (b + off) = Some (byte_of_word (Z_to_bv 64 v) 0).
Proof.
intros E m nb b cs lo hi wlo whi off v (_ & _ & _ & Hcs) Hb Hin.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
cbn [YP09.r_base] in Hck. rewrite Hb in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hcb & Hmb).
cbn [cbyte YP09.c_off YP09.c_val sv_denot] in Hcb. injection Hcb as <-.
rewrite Z.add_0_r in Hmb. exact Hmb.
Qed.

Lemma hoA_aview_of_mbyte : forall (Wx : world SEGS) m a (bb : byte),
  mbyte SEGS (mrestrict (w_H Wx) m) a = Some bb -> aview SEGS (w_H Wx) m a = Some (bv_unsigned bb).
Proof. intros Wx m a bb Hm. unfold aview. rewrite Hm. reflexivity. Qed.

Lemma hoA_val_kept : forall (Wa Wb : world SEGS) ma mb a (n : nat) v,
  (forall i, a <= i < a + Z.of_nat n -> aview SEGS (w_H Wb) mb i = aview SEGS (w_H Wa) ma i) ->
  val_mem SEGS (mrestrict (w_H Wa) ma) a n v -> val_mem SEGS (mrestrict (w_H Wb) mb) a n v.
Proof.
intros Wa Wb ma mb a n v HE Hv kk Hk. rewrite <- (Hv kk Hk).
apply (mbyte_of_aview SEGS). apply HE. lia.
Qed.

Lemma hoA_pres_hi : forall (Wx : world SEGS) ma mb a,
  YM05.alloc_ceiling <= a < 2 ^ 64 ->
  aview SEGS (w_H Wx) mb a = aview SEGS (w_H Wx) ma a -> apresent (w_H Wx) ma a -> apresent (w_H Wx) mb a.
Proof.
intros Wx ma mb a Ha HE Hp.
pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
assert (Hb : 0 <= a < 2 ^ 64) by (clear - Ha D1; lia).
assert (Hni : ~ in_img SEGS a)
by (intros Him; pose proof (pa_segs_low a Him) as Hl; clear - Hl Ha D1 D5; unfold kLowMemEnd in *; lia).
exact (apresent_transfer SEGS (w_H Wx) (w_H Wx) ma mb a Hb Hni HE Hp).
Qed.

Lemma hoA_tail_kept : forall lyc Sc ly2 S2 (Wc W2 : world SEGS) memc mem2 mem3 md2 fpos F sp h out,
  AR SEGS B ly2 S2 W2 mem2 md2 ->
  frames S2 = (1, fpos) :: frames Sc ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall cid p, frame_addr ly2 cid p = frame_addr lyc cid p) ->
  F = frame_addr ly2 1 fpos ->
  treac_hunt_observe_kept lyc Sc Wc memc W2 mem2 sp h out ->
  YM05.alloc_ceiling <= sp - REAC_HUNT_OBSERVE_STK -> sp <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - REAC_HUNT_OBSERVE_STK <= a < sp) ->
     ~ (F <= a < F + 128) -> ~ (SB + F / 8 <= a < SB + F / 8 + 16) ->
     a <> flag_addr ly2 1 fpos -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  treac_hunt_observe_kept lyc Sc Wc memc W2 mem3 sp h out.
Proof.
intros lyc Sc ly2 S2 Wc W2 memc mem2 mem3 md2 fpos F sp h out HAR Hfrs HPerm HFA HFe HK Hspc Hsp64 HUN HPr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : In (1, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR Hfin) as (HF4096 & HFceil & HFhigh).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR Hfin) as (HFal & _ & HFpres & HFSpres).
destruct (FFL ly2 S2 W2 mem2 md2 1 fpos HAR Hfin) as (HFLpres & HFLown & HFLapp & HFLrng).
change (fs_frame_bytes 1) with 128 in *.
rewrite <- HFe in *.
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; [lia | clear - HFceil C1; lia]).
assert (HF8t : F / 8 <= 17592184995824) by (apply Z.div_le_upper_bound; [lia | clear - HFceil C1; lia]).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFhigh.
destruct HFLapp as (HFLa4096 & HFLapp). unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hnw Hnt. rewrite HUN; [exact (K1 a Ha Hnw Hnt) | clear - Ha C1; lia | exact Hnw
  | clear - Ha HFceil C1; lia | clear - Ha HF8hi C1; unfold SB; lia
  | intros ->; clear - Ha HFLrng C1; destruct HFLrng as (_ & _ & Q3); lia].
- intros b m i Hb Hi Hnt.
  assert (Hb2 : In (b, m) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb2) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 b m 1 fpos HAR Hb2 Hfin) as Hdbf.
  unfold zdisjoint in Hdbf. cbn [fst snd] in Hdbf. change (fs_frame_bytes 1) with 128 in Hdbf. rewrite <- HFe in Hdbf.
  destruct Hbapp as (Hba4096 & Hbapp). unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  rewrite HUN; [exact (K2 b m i Hb Hi Hnt) | clear - Hi Hb4096 Hbceil C1; lia | clear - Hi Hb4096 Hbceil Hspc C1; lia
  | clear - Hi Hdbf; lia
  | destruct Hbapp as [Hbapp | [Hbapp Hbapp2]]; clear - Hi Hbapp HF8lo HF8t Hb4096 Hbceil C1; unfold SB; lia
  | intros Heq; apply (proj2 (Hbpres (b + i) ltac:(lia))); rewrite Heq; exact HFLown].
- intros a Hia Ho He.
  pose proof (pa_segs_low a Hia) as Hl. unfold kLowMemEnd in Hl.
  rewrite HUN; [exact (K3 a Hia Ho He) | clear - Hl; lia | clear - Hl Hspc C1; lia
  | intros Hr; apply (frm_img SEGS B LAWS ly2 S2 W2 mem2 md2 1 fpos a HAR Hfin ltac:(rewrite <- HFe; change (fs_frame_bytes 1) with 128; clear - Hr; lia)); exact Hia
  | clear - Hl HF8lo; unfold SB; lia
  | intros ->; apply (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 (flag_addr ly2 1 fpos) HAR
      ltac:(right; right; exists 1, fpos; split; [exact Hfin | reflexivity])); exact Hia].
- intros cid pos a Hf Hr Hnt.
  assert (Hf2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; right; exact Hf).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf2) as (HG4096 & HGceil & HGhigh).
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hf2) as (HGal & _ & HGpres & HGSpres).
  pose proof (fs_frame_bytes_nonneg cid) as HGn.
  pose proof Hf as Hfc. apply in_split in Hfc as (l1 & l2 & El).
  pose proof (sep_frames_pos SEGS B LAWS ly2 S2 W2 mem2 md2 (1, fpos) (cid, pos) [] l1 l2 HAR
    ltac:(rewrite Hfrs, El; reflexivity)) as Hdff.
  unfold zdisjoint, frame_rng in Hdff. cbn [fst snd] in Hdff.
  change (fs_frame_bytes 1) with 128 in Hdff. rewrite <- HFe in Hdff.
  destruct HGhigh as (HGa4096 & HGhigh). unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGhigh.
  assert (HGd8 : forall x, 0 <= x -> x / 8 <= x) by (intros x Hx; apply Z.div_le_upper_bound; lia).
  assert (HSsep : SB + F / 8 + 16 <= shadow_addr (frame_addr ly2 cid pos) \/
                  shadow_addr (frame_addr ly2 cid pos) + fs_frame_bytes cid / 8 <= SB + F / 8).
  { unfold shadow_addr, SHADOW_OFF. destruct Hdff as [Hd | Hd].
    - left. assert (Hq : (F + 128) / 8 <= frame_addr ly2 cid pos / 8) by (apply Z.div_le_mono; lia).
      assert (Hq2 : F / 8 + 16 = (F + 128) / 8)
        by (replace (F + 128) with (F + 16 * 8) by lia; rewrite Z.div_add by lia; lia).
      unfold SB; lia.
    - right. assert (Hq : (frame_addr ly2 cid pos + fs_frame_bytes cid) / 8 <= F / 8) by (apply Z.div_le_mono; lia).
      assert (Hq2 : frame_addr ly2 cid pos / 8 + fs_frame_bytes cid / 8
                    <= (frame_addr ly2 cid pos + fs_frame_bytes cid) / 8)
        by (apply Z.div_le_lower_bound; [lia|];
            pose proof (Z.div_mod (frame_addr ly2 cid pos) 8 ltac:(lia));
            pose proof (Z.mod_pos_bound (frame_addr ly2 cid pos) 8 ltac:(lia));
            pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia));
            pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)); lia).
      unfold SB; lia. }
  assert (Hrng : (frame_addr ly2 cid pos <= a < frame_addr ly2 cid pos + fs_frame_bytes cid) \/
                 (shadow_addr (frame_addr ly2 cid pos) <= a < shadow_addr (frame_addr ly2 cid pos) + fs_frame_bytes cid / 8)).
  { pose proof Hr as Hr2. unfold in_zr, frame_rng in Hr2. cbn [fst snd] in Hr2.
    rewrite <- (HFA cid pos) in Hr2. destruct Hr2 as [Hr2 | Hr2]; [left | right]; exact Hr2. }
  assert (HSlo : SB <= shadow_addr (frame_addr ly2 cid pos))
    by (unfold shadow_addr, SHADOW_OFF, SB; pose proof (Z.div_pos (frame_addr ly2 cid pos) 8 ltac:(lia) ltac:(lia)); lia).
  assert (HShi : shadow_addr (frame_addr ly2 cid pos) + fs_frame_bytes cid / 8 <= SB + 17592186044416).
  { unfold shadow_addr, SHADOW_OFF, SB.
    assert (Hq : (frame_addr ly2 cid pos + fs_frame_bytes cid) / 8 <= 17592186044416)
      by (apply Z.div_le_upper_bound; [lia | clear - HGceil C1; lia]).
    assert (Hq2 : frame_addr ly2 cid pos / 8 + fs_frame_bytes cid / 8
                  <= (frame_addr ly2 cid pos + fs_frame_bytes cid) / 8)
      by (apply Z.div_le_lower_bound; [lia|];
          pose proof (Z.div_mod (frame_addr ly2 cid pos) 8 ltac:(lia));
          pose proof (Z.mod_pos_bound (frame_addr ly2 cid pos) 8 ltac:(lia));
          pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia));
          pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)); lia). lia. }
  rewrite HUN; [exact (K4 cid pos a Hf Hr Hnt)
  | destruct Hrng as [Hq | Hq]; clear - Hq HG4096 HGceil HSlo HShi C1; unfold SB in *; lia
  | destruct Hrng as [Hq | Hq]; clear - Hq HG4096 HGceil HSlo HShi Hspc C1; unfold SB in *; lia
  | intros Hin; destruct Hrng as [Hq | Hq];
    [clear - Hq Hin Hdff; lia | destruct HFhigh as (HFh0 & [HFhigh | [HFhigh HFhigh2]]); clear - Hq Hin HSlo HShi HFhigh HF4096 HFceil C1; unfold SB in *; lia]
  | intros Hin; destruct Hrng as [Hq | Hq];
    [destruct HGhigh as [HGhigh | [HGhigh HGhigh2]]; clear - Hq Hin HGhigh HG4096 HGceil HF8lo HF8t C1; unfold SB in *; lia | clear - Hq Hin HSsep; lia]
  | intros ->; destruct Hrng as [Hq | Hq];
    [apply (proj2 (HGpres (flag_addr ly2 1 fpos) Hq)); exact HFLown
    | destruct HFLa4096 as (HFLz & [HFLa | [HFLa HFLa2]]);
       unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLa;
       clear - Hq HSlo HShi HFLa; unfold SB in *; lia]].
- intros a Ha Hnw Hp. apply HPr; [exact Ha|]. exact (K5 a Ha Hnw Hp).
- intros a Ha. apply HPr; [clear - Ha Hspc Hsp64 C1; lia|]. exact (K6 a Ha).
Qed.


Lemma hoA_ew_of_U : forall E (m : nat) v, bv_unsigned (ew E m) = v -> ew E m = Z_to_bv 64 v.
Proof. intros E m v Hv. rewrite <- Hv. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Ltac hoA_bvr := lazymatch goal with |- 0 <= bv_unsigned ?x < _ =>
  pose proof (bv_unsigned_in_range _ x) as Hbvr; unfold bv_modulus in Hbvr; cbn [Z.of_N Z.mul] in *; lia end.

Lemma ho_segA : ho_seg_C_stmt -> treac_hunt_observe_spec.
Proof.
intros HC. unfold treac_hunt_observe_spec.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch h f len now out hb hn H FB O
  HJ HROm Hra Hra4 Hgp Htp Hch Hal16 Hwin Hsp Hdep H10 H11 H12 H13 H14 Rlen Rnow Rout Hh0 Hh8 Hin Hhb Hhe Hhw HOK HHg HFBl HF50 HOUT HKM HKT.
pose proof HJ as HJ0.
destruct (ho_count _ h H HOK HHg) as [Hn HV].
set (n := disco_table_c.n_of (disco_table_c.sub H 0 400)) in *.
destruct (ho_entry fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs h n hb hn HJ H10 Hal16 Hwin Hsp Hin Hhb Hhe Hh0 Hh8 Hn HV) as [HS SHOK].
pose proof (Eimg_env (Ereg regs (ho_extra n (as_uar_cell B)))) as HEI. fold (EHO regs n (as_uar_cell B)) in HEI.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (AG : forall m, (m < 33)%nat -> ew (EHO regs n (as_uar_cell B)) m = ew (EHO regs n (as_uar_cell B)) m) by reflexivity.
assert (E2 : ew (EHO regs n (as_uar_cell B)) 2 = Z_to_bv 64 (spZ regs))
by (unfold EHO; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew (EHO regs n (as_uar_cell B)) 2) = spZ regs) by (rewrite E2; apply unsigned_lit_small; lia).


destruct (al_blocks _ _ LAWS lyc Sc W memc mdc hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ hb hn HAR Hin) as Hbimg.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. unfold off_img in Hbimg.
assert (E10 : ew (EHO regs n (as_uar_cell B)) 10 = Z_to_bv 64 h)
by (unfold EHO; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Uh : bv_unsigned (ew (EHO regs n (as_uar_cell B)) 10) = h) by (rewrite E10; apply unsigned_lit_small; lia).


assert (E1 : ew (EHO regs n (as_uar_cell B)) 1 = getr regs 1)
by (unfold EHO; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E3 : ew (EHO regs n (as_uar_cell B)) 3 = getr regs 3)
by (unfold EHO; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew (EHO regs n (as_uar_cell B)) 4 = getr regs 4)
by (unfold EHO; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E32 : ew (EHO regs n (as_uar_cell B)) 32 = Z_to_bv 64 SB)
by (unfold EHO; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (EHO regs n (as_uar_cell B)) 33 = Z_to_bv 64 n)
by (unfold EHO; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E59 : ew (EHO regs n (as_uar_cell B)) 59 = Z_to_bv 64 (as_uar_cell B))
by (unfold EHO; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 27)).
img_factsF (EHO regs n (as_uar_cell B)). img_hull_factsF.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hob241, Hob242, Hob253, Huar.
pose proof (pa_val_range 241%nat) as VR241. pose proof (pa_val_range 242%nat) as VR242. pose proof (pa_val_range 253%nat) as VR253.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_hunt_observe)) with (Z_to_bv 64 (BASE + AF_both3_reac_hunt_observe)).
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK HOspan 29244.
{ intros a (r & Hr & Hrng). cbn [ss_mem ss_ho ho_regions In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region got_regionP bcell_regionP uar_got_regionP uar_cell_regionP ho_hregion] in Hrng;
  try (exfalso; lia).
  rewrite Usp in Hrng. left. unfold REAC_HUNT_OBSERVE_FRAME in Hrng. lia. }

set (sp1 := 32 * ((spZ regs + -160) / 32)).
destruct (sp1_facts (spZ regs + -160) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by lia. clear Hsp1r.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
  (denot_and_m32 Ev 2 (spZ regs) (-160) E2 ltac:(lia) ltac:(lia) ltac:(lia)) R2 end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 sp1)
  (eq_trans (denot_add0 Ev (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))))
     (denot_and_m32 Ev 2 (spZ regs) (-160) E2 ltac:(lia) ltac:(lia) ltac:(lia))) R9 end.
add_atom HS 60%nat (Z_to_bv 64 sp1) E60.
rebaseE HS AG HEv. clear HEv.

lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R9; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
ra_join_fact HS 60%nat (mkAF (2 ^ 46) (2 ^ 47) 5)
  ltac:(rewrite E60, unsigned_lit_small by lia; change (2 ^ 5) with 32; split; [lia|]; split; [exact Hsp1al | lia]).
norm_ss HS.

pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 56 0 56 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E60, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply Hpres2; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E60, E241, E242, E253, E59, !unsigned_lit_small by lia;
repeat match goal with |- context [bv_unsigned (ew ?Ex 2)] => rewrite (AG 2%nat ltac:(lia)), Usp end;
repeat match goal with |- context [bv_unsigned (ew ?Ex 10)] => rewrite (AG 10%nat ltac:(lia)), Uh end;
repeat match goal with Hx : _ /\ _ |- _ => destruct Hx as [? ?] end;
repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.


lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict (w_H ?Wx) ?msx) =>
assert (SHOK2 : sh_ok SEGS HOBx [mkSHE 10 0 480] Ev (mrestrict (w_H Wx) (ms_mem msx)));
[ apply Forall_cons; [|apply Forall_nil];
  apply (ho_shent_gen _ _ _ 10%nat h 0 480);
  [ rewrite (AG 32%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E32
  | rewrite (AG 10%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E10
  | clear - Hh0 Hhe Hbceil C1; lia | apply Z.leb_le; reflexivity
  | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; unfold kLowShadowBeg, ASAN_CEIL in Hbapp; clear - Hbapp Hhb Hhe C1; lia
  | replace (h + 0) with h by ring; replace (480 - 0) with 480 by ring;
    apply (range_addressable_of_block SEGS B LAWS lyc Sc W (ms_mem msx) _ hb hn h 480 (proj1 HJ) Hin); clear - Hhb Hhe; lia ]
| ] end.
clear SHOK. rename SHOK2 into SHOK.

lazymatch goal with H : frame_of _ _ _ _ |- _ => rename H into HFRa end.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK HOspan.
{ intros a (r & Hr & Hrng). cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng; revert Hrng;
     repeat match goal with |- context [ew ?Ex ?m] =>
       lazymatch (eval cbv in (Nat.ltb m 33)) with true => rewrite (AG m ltac:(apply Nat.ltb_lt; reflexivity)) end end;
     rewrite ?E60, ?E2, ?E10, ?unsigned_lit_small by (clear - Hsp1 Hsp Hwin HSTK Hslo Hceil Hshi H47 C1 Hh0 Hhe Hbceil; lia); intros Hrng;
     first [ exfalso; clear - Hrng; lia | left; clear - Hrng Hsp1 Hsp Hwin HSTK; lia | apply Hhw; clear - Hrng; lia ] |]).
  destruct Hr. }

lazymatch goal with H : frame_of _ _ _ _ |- _ => rename H into HFRb end.
lazymatch type of HFRb with frame_of ?Er2 ?rs2 _ _ =>
assert (NW2 : forall a, ~ (spZ regs - REAC_HUNT_OBSERVE_STK <= a < spZ regs) -> ~ in_wrange Er2 rs2 a);
[ intros a Hs (rr & Hinw & Hr);
  lazymatch type of Hinw with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hinw end;
  cbn [In] in Hinw;
  repeat (destruct Hinw as [<- | Hinw];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr;
      repeat match goal with |- context [ew ?Ex ?m] =>
        lazymatch (eval cbv in (Nat.ltb m 33)) with true => rewrite (AG m ltac:(lia)) end end;
      rewrite ?E60, ?E2, ?E10, ?unsigned_lit_small by lia; intros Hr;
      clear - Hr Hs Hsp1 HSTK; try unfold REAC_HUNT_OBSERVE_FRAME in *;
      try unfold REAC_HUNT_OBSERVE_STK in *; lia
    | ]);
  destruct Hinw
| ] end.
prreg HS (1%bv : bv 5) R1b. prreg HS (2%bv : bv 5) R2b. prreg HS (3%bv : bv 5) R3b. prreg HS (4%bv : bv 5) R4b.
rewrite E60 in R2b.
pmkst HS.
rewrite (palf_sm1 B TLF).
pose proof (count_cid_le_length 1 (frames Sc)) as Hcnt.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rgs _ ?mm _) _) _ =>
eapply SRr_bind;
[ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 1 (ASM1 fq) ltac:(lia)
    W rgs mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) | ] end.

- unfold spZ. rewrite R2b, unsigned_lit_small by lia. lia.
- rewrite <- Zminus_mod_idemp_l, <- Zminus_mod_idemp_r, Hsp1al16, Hsp0al. reflexivity.
- lia.
- unfold ESTACK, CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED in *. lia.
- rewrite R3b, (AG 3%nat ltac:(lia)), E3. exact Hgp.
- rewrite R4b, (AG 4%nat ltac:(lia)), E4. exact Htp.
- exact R1b.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- change (fs_frames 1) with 8192. unfold REAC_HUNT_OBSERVE_DEPTH, CLS_DEPTH in Hdep. lia.
- cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJin & (fS2 & ES2)).
clear SHOK.
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
reseat HS HJ2 HP2 [0;1;2;3;4;5;6]%nat AG
ltac:(idtac; first
 [ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
     eapply (ho_kept_inblk _ lyc Sc W _ _ _ _ _ _ 10%nat 0 480 0 0 _ h hb hn _ S2 md2);
     [ exact HK | exact (proj1 HJ2) | rewrite Eab; exact Hin
     | rewrite (AG 10%nat ltac:(lia)), E10; apply unsigned_lit_small; lia
     | exact Hin | lia | lia | lia | lia | intros a Ha HE; destruct HE ] end
 | keptFL HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail) ]).

prreg HS (10%bv : bv 5) RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ2) Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos (proj1 HJ2) Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ (proj1 HJ2) Hfin2) as HFimg.
change (fs_frame_bytes 1) with 128 in *.
destruct (FFL lyc S2 W mem2 md2 1 fpos (proj1 HJ2) Hfin2) as (HFLpres & HFLown & HFLapp & HFLrng).
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32))
by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
ra_join_fact HS 516%nat (HPTR 5)
  ltac:(unfold HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia).
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 528%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]; clear HS; rename HS3 into HS end.
rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL)
  by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8))
  by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.

assert (Hin2b : In (hb, hn) (ablocks B lyc S2)) by (rewrite Eab; exact Hin).
pose proof (sep_block_frame SEGS B LAWS lyc S2 W mem2 md2 hb hn 1 fpos (proj1 HJ2) Hin2b Hfin2) as HdFH.
unfold zdisjoint in HdFH. cbn [fst snd] in HdFH. change (fs_frame_bytes 1) with 128 in HdFH. fold F in HdFH.
assert (ZS : forall j, 0 <= j < 2 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
  replace (SB + F / 8 + 8 * j + ii) with (SB + F / 8 + (8 * j + ii)) by lia. apply Hz. change (128 / 8) with 16. lia. }
ra_join_fact HS 528%nat (HPTR 0)
  ltac:(unfold HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by (clear - HFLrng C1 C3; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - HFLrng C1 C3; lia).
norm_ss HS.
ra_join_fact HS 529%nat (mkAF (SB + 512) (SB + 17592186044416) 2)
  ltac:(cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
        split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia]).
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
assert (E32v : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact E32);
pose proof (st_ok_pi_add_alias Ev ssx msx _ _ HS (shadow_decl_ok Ev 516 32 529 F SB RF ltac:(lia) E32v E529)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.

lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (U2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact Usp);
assert (U10 : bv_unsigned (ew Ev 10) = h) by (rewrite (AG 10%nat ltac:(lia)); exact Uh);
assert (U60 : bv_unsigned (ew Ev 60) = sp1) by (rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hwin Hsp Hshi H47 C1 C3 HSTK; lia);
assert (U516 : bv_unsigned (ew Ev 516) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1 C3; lia);
assert (U241 : bv_unsigned (ew Ev 241) = VAL 241) by (rewrite E241; apply unsigned_lit_small; pose proof (pa_val_range 241%nat); lia);
assert (U242 : bv_unsigned (ew Ev 242) = VAL 242) by (rewrite E242; apply unsigned_lit_small; pose proof (pa_val_range 242%nat); lia);
assert (U253 : bv_unsigned (ew Ev 253) = VAL 253) by (rewrite E253; apply unsigned_lit_small; pose proof (pa_val_range 253%nat); lia);
assert (U59 : bv_unsigned (ew Ev 59) = as_uar_cell B) by (rewrite E59; apply unsigned_lit_small; clear - Huar; lia);
assert (U528 : bv_unsigned (ew Ev 528) = FL) by (rewrite E528; apply unsigned_lit_small; clear - HFLrng C1 C3; lia);
assert (U529 : bv_unsigned (ew Ev 529) = SB + F / 8) by (rewrite E529; apply unsigned_lit_small; clear - HF8lo HF8hi; unfold SB; lia) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 0 128 0 24 [YP09.mkChunk 120 (CVal 8 (SOff 528 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U516; split; [clear - HF4096; lia|]; split; [clear - HFceil C1 C3; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 120 8 _ FL);
  [cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | (cbn [Z.of_N N.to_nat Pos.to_nat Z.mul Pos.mul Pos.iter_op Nat.add Nat.mul]; clear - HFLrng C1; lia) | (cbn [Z.of_N N.to_nat Pos.to_nat Z.mul Pos.mul Pos.iter_op Nat.add Nat.mul]; clear - HFLrng C1; lia) |
   replace (F + 120) with (F + 128 - 8) by ring; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite U516, U60, U2, U10, U241, U242, U253, U59;
repeat split; ((clear - Hsp1 HF4096 HFceil HFimg HFhigh Hceil Hslo Hshi H47 Hwin Hsp Hbapp Hbceil Hbimg Hb4096 Hhb Hhe Hh0 Hob241 Hob242 Hob253 Huar HdFH HF8lo HF8hi C1 C3 HSTK HFLrng;
  try unfold off_img in *; try unfold YImgTop.IMG_LO in *; try unfold YImgTop.IMG_TOP in *;
  try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *;
  try unfold ASAN_CEIL in *; try unfold kLowMemEnd in *;
  try unfold REAC_HUNT_OBSERVE_STK in *; try unfold REAC_HUNT_OBSERVE_FRAME in *; try unfold CLS_STK in *;
  try unfold CLS_OWN_BCMP in *; try unfold CLS_VIA_PARSE in *; try unfold CLS_FRAME in *;
  try unfold CLS_PARSE_NEED in *; try unfold ESTACK in *; try unfold SB in *;
  lia)))) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.

lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
  (fshadow_region 529 1 0 12 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
change (fs_frame_bytes 1 / 8) with 16; rewrite U529;
split; [clear - HF8lo; unfold SB; lia|]; split; [clear - HF8hi; unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
  apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; clear - Ho; lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside |
    replace (SB + F / 8 + 0) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
  apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside |
    replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|]; apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16; rewrite U529, U516, U60, U2, U10, U241, U242, U253, U59;
repeat split; (clear - Hsp1 HF4096 HFceil HFimg HFhigh Hceil Hslo Hshi H47 Hwin Hsp Hbapp Hbceil Hbimg Hb4096
  Hhb Hhe Hh0 Hob241 Hob242 Hob253 Huar HdFH HF8lo HF8hi C1 C3 HSTK HFLrng;
  try unfold off_img in *; try unfold YImgTop.IMG_LO in *; try unfold YImgTop.IMG_TOP in *;
  try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *;
  try unfold ASAN_CEIL in *; try unfold kLowMemEnd in *;
  try unfold REAC_HUNT_OBSERVE_STK in *; try unfold REAC_HUNT_OBSERVE_FRAME in *; try unfold CLS_STK in *;
  try unfold CLS_OWN_BCMP in *; try unfold CLS_VIA_PARSE in *; try unfold CLS_FRAME in *;
  try unfold CLS_PARSE_NEED in *; try unfold ESTACK in *; try unfold SB in *; lia))) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.

pose proof HJ2 as HJ2m.
pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
paj_run_to_sh RUNTOP HS HJ2 29452.

{ intros a (r & Hr & Hrng). cbn [In] in Hr.
  assert (HWm : forall x, awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x ->
      awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S2) lyc ((1, fpos) :: own) x)
  by (intros x Hx; eapply (hoT_awr_mv _ _ _ _ _ _ _ _ _ (1, fpos));
      [rewrite Eab; apply Permutation_refl | reflexivity | exact Hx]).
  repeat (destruct Hr as [<- | Hr];
   [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fshadow_region] in Hrng;
     rewrite ?U529, ?U516, ?U60, ?U2, ?U10, ?U241, ?U242, ?U253, ?U59 in Hrng;
     change (fs_frame_bytes 1 / 8) with 16 in Hrng;
     (first
     [ (exfalso; clear - Hrng; lia)
     | (left; clear - Hrng Hsp1 Hwin Hsp HSTK; try unfold REAC_HUNT_OBSERVE_FRAME in *;
        try unfold REAC_HUNT_OBSERVE_STK in *; lia)
     | (apply HWm; apply Hhw; clear - Hrng; lia)
     | (right; right; right; exists 1, fpos; split; [left; reflexivity|];
        left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; try fold F; clear - Hrng; lia)
     | (right; right; right; exists 1, fpos; split; [left; reflexivity|];
        right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF;
        change (fs_frame_bytes 1 / 8) with 16; try fold F; unfold SB in *; clear - Hrng; lia) ]) | ]);
  destruct Hr. }


lazymatch goal with Hx : frame_of _ _ _ _ |- _ => rename Hx into HFRc end.
cbn [ms_mem] in HFRc.
pose proof HJ2 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
assert (HF8t : F / 8 <= 17592184995824) by (apply Z.div_le_upper_bound; [lia | clear - HFceil C1; lia]).
assert (HSHhi : SB + F / 8 + 16 < YM05.alloc_ceiling)
  by (clear - HF4096 HFceil C1 HF8lo HF8hi; unfold SB; lia).
assert (HSTKlo : YM05.alloc_ceiling <= spZ regs - REAC_HUNT_OBSERVE_STK)
  by (clear - Hceil Hslo Hwin HSTK; unfold REAC_HUNT_OBSERVE_STK, CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK in *; lia).
assert (HFstk : F + 128 <= spZ regs - REAC_HUNT_OBSERVE_STK) by (clear - HFceil HSTKlo; lia).
assert (HSHstk : SB + F / 8 + 16 <= spZ regs - REAC_HUNT_OBSERVE_STK) by (clear - HSHhi HSTKlo; lia).
assert (UNCH3 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (spZ regs - REAC_HUNT_OBSERVE_STK <= a < spZ regs) ->
  ~ (F <= a < F + 24) -> ~ (SB + F / 8 <= a < SB + F / 8 + 12) ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha Hs Hf Hsh. apply (hoT_aview_frame _ _ W mem2 (ms_mem ms1) a HFRc Ha).
  intros (rr & Hinw & Hr).
  lazymatch type of Hinw with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hinw end.
  cbn [In] in Hinw.
  destruct Hinw as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fshadow_region] in Hr;
  rewrite ?U529, ?U516, ?U60, ?U2, ?U10, ?U241, ?U242, ?U253, ?U59 in Hr;
  change (fs_frame_bytes 1 / 8) with 16 in Hr;
  (clear - Hr Hs Hf Hsh Hsp1 HSTK; try unfold REAC_HUNT_OBSERVE_FRAME in *;
   try unfold REAC_HUNT_OBSERVE_STK in *; lia). }

lazymatch type of HK with acall_kept _ _ _ _ _ ?mc _ _ _ _ _ =>
assert (UNCH12 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (spZ regs - REAC_HUNT_OBSERVE_STK <= a < spZ regs) ->
  aview SEGS (w_H W) mc a = aview SEGS (w_H W) memc a);
[ intros a Ha Hs;
  rewrite (hoT_aview_frame _ _ W _ _ a HFRb Ha (NW2 a Hs));
  apply (hoT_aview_frame _ _ W _ _ a HFRa Ha);
  intros (rr & Hinw & Hr);
  cbn [ss_mem ss_ho ho_regions In] in Hinw;
  destruct Hinw as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region got_regionP bcell_regionP
       uar_got_regionP uar_cell_regionP ho_hregion] in Hr;
  rewrite ?Usp, ?Uh in Hr;
  (clear - Hr Hs HSTK; try unfold REAC_HUNT_OBSERVE_FRAME in *;
   try unfold REAC_HUNT_OBSERVE_STK in *; lia)
| ] end.

pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as Hreg0.
pose proof (st_ok_pi_region_nth _ _ _ 3%nat _ HS eq_refl) as Hreg3.
cbn [ms_mem restrict] in Hreg0, Hreg3.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (ER : forall (m : nat) (r : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned r -> ew Ev m = getr regs r)
  by (intros m r Hm Hr; rewrite (AG m ltac:(lia)); unfold EHO; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_nat regs _ m r Hr)) end.
assert (HSV : forall j, (j < 13)%nat ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs - 8 * (Z.of_nat j + 1)) 8
    (bv_unsigned (getr regs (ho_sreg j)))).
{ intros j Hj.
  assert (Hc : j = 0%nat \/ j = 1%nat \/ j = 2%nat \/ j = 3%nat \/ j = 4%nat \/ j = 5%nat \/ j = 6%nat \/ j = 7%nat \/ j = 8%nat \/ j = 9%nat \/ j = 10%nat \/ j = 11%nat \/ j = 12%nat) by (clear - Hj; lia).
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]; unfold ho_sreg; cbn [nth Z.of_nat].
  - replace (spZ regs - 8 * (0 + 1)) with (spZ regs + -8) by lia. change 8%nat with (N.to_nat 8).
    exact (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-8) 8 (SOff 1 0) (bv_unsigned (getr regs 1%bv)) Hreg3 U2 ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (ER 1%nat 1%bv ltac:(lia) eq_refl), Z.add_0_r; reflexivity)
      ltac:(hoA_bvr) ltac:(cbn; lia)).
  - replace (spZ regs - 8 * (1 + 1)) with (spZ regs + -16) by lia. change 8%nat with (N.to_nat 8).
    exact (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-16) 8 (SOff 8 0) (bv_unsigned (getr regs 8%bv)) Hreg3 U2 ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (ER 8%nat 8%bv ltac:(lia) eq_refl), Z.add_0_r; reflexivity)
      ltac:(hoA_bvr) ltac:(cbn; lia)).
  - replace (spZ regs - 8 * (2 + 1)) with (spZ regs + -24) by lia. change 8%nat with (N.to_nat 8).
    exact (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-24) 8 (SOff 9 0) (bv_unsigned (getr regs 9%bv)) Hreg3 U2 ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (ER 9%nat 9%bv ltac:(lia) eq_refl), Z.add_0_r; reflexivity)
      ltac:(hoA_bvr) ltac:(cbn; lia)).
  - replace (spZ regs - 8 * (3 + 1)) with (spZ regs + -32) by lia. change 8%nat with (N.to_nat 8).
    exact (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-32) 8 (SOff 18 0) (bv_unsigned (getr regs 18%bv)) Hreg3 U2 ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (ER 18%nat 18%bv ltac:(lia) eq_refl), Z.add_0_r; reflexivity)
      ltac:(hoA_bvr) ltac:(cbn; lia)).
  - replace (spZ regs - 8 * (4 + 1)) with (spZ regs + -40) by lia. change 8%nat with (N.to_nat 8).
    exact (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-40) 8 (SOff 19 0) (bv_unsigned (getr regs 19%bv)) Hreg3 U2 ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (ER 19%nat 19%bv ltac:(lia) eq_refl), Z.add_0_r; reflexivity)
      ltac:(hoA_bvr) ltac:(cbn; lia)).
  - replace (spZ regs - 8 * (5 + 1)) with (spZ regs + -48) by lia. change 8%nat with (N.to_nat 8).
    exact (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-48) 8 (SOff 20 0) (bv_unsigned (getr regs 20%bv)) Hreg3 U2 ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (ER 20%nat 20%bv ltac:(lia) eq_refl), Z.add_0_r; reflexivity)
      ltac:(hoA_bvr) ltac:(cbn; lia)).
  - replace (spZ regs - 8 * (6 + 1)) with (spZ regs + -56) by lia. change 8%nat with (N.to_nat 8).
    exact (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-56) 8 (SOff 21 0) (bv_unsigned (getr regs 21%bv)) Hreg3 U2 ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (ER 21%nat 21%bv ltac:(lia) eq_refl), Z.add_0_r; reflexivity)
      ltac:(hoA_bvr) ltac:(cbn; lia)).
  - replace (spZ regs - 8 * (7 + 1)) with (spZ regs + -64) by lia. change 8%nat with (N.to_nat 8).
    exact (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-64) 8 (SOff 22 0) (bv_unsigned (getr regs 22%bv)) Hreg3 U2 ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (ER 22%nat 22%bv ltac:(lia) eq_refl), Z.add_0_r; reflexivity)
      ltac:(hoA_bvr) ltac:(cbn; lia)).
  - replace (spZ regs - 8 * (8 + 1)) with (spZ regs + -72) by lia. change 8%nat with (N.to_nat 8).
    exact (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-72) 8 (SOff 23 0) (bv_unsigned (getr regs 23%bv)) Hreg3 U2 ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (ER 23%nat 23%bv ltac:(lia) eq_refl), Z.add_0_r; reflexivity)
      ltac:(hoA_bvr) ltac:(cbn; lia)).
  - replace (spZ regs - 8 * (9 + 1)) with (spZ regs + -80) by lia. change 8%nat with (N.to_nat 8).
    exact (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-80) 8 (SOff 24 0) (bv_unsigned (getr regs 24%bv)) Hreg3 U2 ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (ER 24%nat 24%bv ltac:(lia) eq_refl), Z.add_0_r; reflexivity)
      ltac:(hoA_bvr) ltac:(cbn; lia)).
  - replace (spZ regs - 8 * (10 + 1)) with (spZ regs + -88) by lia. change 8%nat with (N.to_nat 8).
    exact (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-88) 8 (SOff 25 0) (bv_unsigned (getr regs 25%bv)) Hreg3 U2 ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (ER 25%nat 25%bv ltac:(lia) eq_refl), Z.add_0_r; reflexivity)
      ltac:(hoA_bvr) ltac:(cbn; lia)).
  - replace (spZ regs - 8 * (11 + 1)) with (spZ regs + -96) by lia. change 8%nat with (N.to_nat 8).
    exact (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-96) 8 (SOff 26 0) (bv_unsigned (getr regs 26%bv)) Hreg3 U2 ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (ER 26%nat 26%bv ltac:(lia) eq_refl), Z.add_0_r; reflexivity)
      ltac:(hoA_bvr) ltac:(cbn; lia)).
  - replace (spZ regs - 8 * (12 + 1)) with (spZ regs + -104) by lia. change 8%nat with (N.to_nat 8).
    exact (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-104) 8 (SOff 27 0) (bv_unsigned (getr regs 27%bv)) Hreg3 U2 ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (ER 27%nat 27%bv ltac:(lia) eq_refl), Z.add_0_r; reflexivity)
      ltac:(hoA_bvr) ltac:(cbn; lia)). }

assert (HZ12 : forall k, 12 <= k < 16 -> aview SEGS (w_H W) mem2 (SB + F / 8 + k) = Some 0).
{ intros kk Hk. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
  apply Hz. change (128 / 8) with 16. clear - Hk; lia. }
pose proof HFhigh as HFapp. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (HSH3 : forall k, 12 <= k < 16 ->
  aview SEGS (w_H W) (ms_mem ms1) (SB + F / 8 + k) = aview SEGS (w_H W) mem2 (SB + F / 8 + k)).
{ intros kk Hk. apply UNCH3.
  - clear - Hk HF8lo HF8hi; unfold SB; lia.
  - clear - Hk HSHstk; lia.
  - destruct HFapp as (_ & [Hq | (Hq & _)]); clear - Hk Hq HF8lo HF8hi HF4096; unfold SB in *; lia.
  - clear - Hk; lia. }
lazymatch type of Hreg0 with region_ok _ ?Ev _ _ =>
assert (B529 : base_val Ev (Some 529%nat) = SB + F / 8) by (cbn [base_val]; exact U529) end.
assert (HFSH : ho_fsh W (ms_mem ms1) F ho_shC).
{ intros i Hi.
  assert (Hcase : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15) by (clear - Hi; lia).
  destruct Hcase as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]];
  [ rewrite (hoA_aview_of_mbyte W _ _ _ (hoA_chunk_byte _ _ 529%nat (SB + F / 8) _ _ _ _ _ 0 18446744073709551601 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (hoA_aview_of_mbyte W _ _ _ (hoA_chunk_byte _ _ 529%nat (SB + F / 8) _ _ _ _ _ 1 18446744073709551601 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (hoA_aview_of_mbyte W _ _ _ (hoA_chunk_byte _ _ 529%nat (SB + F / 8) _ _ _ _ _ 2 18446744073709551601 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (hoA_aview_of_mbyte W _ _ _ (hoA_chunk_byte _ _ 529%nat (SB + F / 8) _ _ _ _ _ 3 18446744073709551601 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (hoA_aview_of_mbyte W _ _ _ (hoA_chunk_byte _ _ 529%nat (SB + F / 8) _ _ _ _ _ 4 0 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (hoA_aview_of_mbyte W _ _ _ (hoA_chunk_byte _ _ 529%nat (SB + F / 8) _ _ _ _ _ 5 0 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (hoA_aview_of_mbyte W _ _ _ (hoA_chunk_byte _ _ 529%nat (SB + F / 8) _ _ _ _ _ 6 0 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (hoA_aview_of_mbyte W _ _ _ (hoA_chunk_byte _ _ 529%nat (SB + F / 8) _ _ _ _ _ 7 18446744073709551603 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (hoA_aview_of_mbyte W _ _ _ (hoA_chunk_byte _ _ 529%nat (SB + F / 8) _ _ _ _ _ 8 18446744073709551603 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (hoA_aview_of_mbyte W _ _ _ (hoA_chunk_byte _ _ 529%nat (SB + F / 8) _ _ _ _ _ 9 18446744073709551603 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (hoA_aview_of_mbyte W _ _ _ (hoA_chunk_byte _ _ 529%nat (SB + F / 8) _ _ _ _ _ 10 18446744073709551603 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (hoA_aview_of_mbyte W _ _ _ (hoA_chunk_byte _ _ 529%nat (SB + F / 8) _ _ _ _ _ 11 18446744073709551603 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (HSH3 12 ltac:(lia)), (HZ12 12 ltac:(lia))
  | rewrite (HSH3 13 ltac:(lia)), (HZ12 13 ltac:(lia))
  | rewrite (HSH3 14 ltac:(lia)), (HZ12 14 ltac:(lia))
  | rewrite (HSH3 15 ltac:(lia)), (HZ12 15 ltac:(lia)) ];
  vm_compute; reflexivity. }
assert (HFLG3 : rdword (aview SEGS (w_H W) (ms_mem ms1)) (F + 120) = Some FL).
{ replace (F + 128 - 8) with (F + 120) in Hflag by lia. rewrite <- Hflag. apply rdword_ext. intros kk Hkk. apply UNCH3.
  - clear - Hkk HF4096 HFceil C1; lia.
  - clear - Hkk HFstk; lia.
  - clear - Hkk; lia.
  - destruct HFapp as (_ & [Hq | (Hq & _)]); clear - Hkk Hq HF8lo HF8hi HF4096; unfold SB in *; lia. }

pose proof HJ2m as (HAR2m & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2m & _).
assert (Hes4 : ESTACK = 4096) by reflexivity.
assert (HKEPT0 : treac_hunt_observe_kept lyc Sc W memc W mem2 (spZ regs) h out).
{ destruct HK as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hnw Hnt. rewrite KC1; [apply UNCH12; [clear - Ha C1; lia | exact Hnw] | exact Ha
      | clear - Hnw Hsp1 HSTK Hes4; lia].
  - intros b m i Hb Hi Hnt.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hbx4096 & Hbxceil & _).
    rewrite (KC2 b m i Hb Hi (fun Hx => Hx)).
    apply UNCH12; [clear - Hi Hbx4096 Hbxceil C1; lia | clear - Hi Hbx4096 Hbxceil HSTKlo; lia].
  - intros a Hia Ho He. rewrite KC3; [| exact Hia | exact Ho | exact He].
    pose proof (pa_segs_low a Hia) as Hl. unfold kLowMemEnd in Hl.
    apply UNCH12; [clear - Hl; lia | clear - Hl HSTKlo C1; lia].
  - intros cid pos a Hf Hr Hnt.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf) as (HG4096 & HGceil & _).
    pose proof (fs_frame_bytes_nonneg cid) as HGn.
    rewrite (KC4 cid pos a Hf Hr (fun Hx => Hx)).
    assert (HGd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 17592186044416)
      by (apply Z.div_le_upper_bound; [lia | clear - HGceil C1; lia]).
    assert (HGd2 : frame_addr lyc cid pos / 8 + fs_frame_bytes cid / 8 <= (frame_addr lyc cid pos + fs_frame_bytes cid) / 8)
      by (apply Z.div_le_lower_bound; [lia|];
          pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(lia));
          pose proof (Z.mod_pos_bound (frame_addr lyc cid pos) 8 ltac:(lia));
          pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia));
          pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)); lia).
    assert (HGd3 : 0 <= frame_addr lyc cid pos / 8) by (apply Z.div_pos; lia).
    unfold in_zr, frame_rng, shadow_addr in Hr. cbn [fst snd] in Hr.
    apply UNCH12;
    destruct Hr as [Hr | Hr]; clear - Hr HG4096 HGceil HGd HGd2 HGd3 HSTKlo C1; unfold SHADOW_OFF in *; lia.
  - intros a Ha Hnw Hp. apply KC5; [exact Ha | clear - Hnw Hsp1 HSTK Hes4; lia |].
    apply (hoA_pres_hi W memc _ a Ha); [apply UNCH12; [clear - Ha C1; lia | exact Hnw] | exact Hp].
  - intros a Ha. apply Hpres2m. clear - Ha Hwin Hsp HSTK; lia. }
assert (HKEPT : treac_hunt_observe_kept lyc Sc W memc W (ms_mem ms1) (spZ regs) h out).
{ apply (hoA_tail_kept lyc Sc lyc S2 W W memc mem2 (ms_mem ms1) md2 fpos F (spZ regs) h out
          (proj1 HJ2m) Hfrs2 ltac:(rewrite Eab; apply Permutation_refl) (fun _ _ => eq_refl) eq_refl
          HKEPT0 HSTKlo ltac:(unfold spZ; pose proof (bv_unsigned_in_range _ (getr regs 2%bv)) as Hq;
                              unfold bv_modulus in Hq; lia)).
  - intros a Ha Hs Hf Hsh Hfl. apply UNCH3; [exact Ha | exact Hs | clear - Hf; lia | clear - Hsh; lia].
  - intros a Ha Hp.
    destruct (Z_lt_le_dec a (spZ regs - REAC_HUNT_OBSERVE_STK)) as [Hlo | Hge];
    [| destruct (Z_lt_le_dec a (spZ regs)) as [Hin2 | Hhi]].
    + apply (hoA_pres_hi W mem2 _ a Ha); [| exact Hp].
      apply UNCH3; [clear - Ha C1; lia | clear - Hlo; lia | clear - Ha HFceil; lia
        | clear - Ha HSHhi; lia].
    + apply Hpres3. clear - Hge Hin2 Hwin Hsp HSTK; lia.
    + apply (hoA_pres_hi W mem2 _ a Ha); [| exact Hp].
      apply UNCH3; [clear - Ha C1; lia | clear - Hhi; lia | clear - Ha HFceil HSTKlo Hhi; lia
        | clear - Ha HSHhi; lia]. }
pose proof HOK as HOKc. destruct HOKc as (HHL & _).
assert (HHB : forall i, h <= i < h + 480 -> aview SEGS (w_H W) (ms_mem ms1) i = aview SEGS (w_H W) memc i).
{ intros i Hi. destruct HK as (KC1 & KC2 & _).
  rewrite UNCH3;
  [ | clear - Hi Hhb Hhe Hb4096 Hbceil C1; lia | clear - Hi Hhb Hhe Hbceil HSTKlo; lia
    | clear - Hi Hhb Hhe HdFH; lia
    | destruct Hbapp as (_ & [Hq | (Hq & _)]); clear - Hi Hhb Hhe Hq Hb4096 Hbceil HF8lo HF8hi HF8t; unfold SB in *; lia ].
  replace i with (hb + (i - hb)) by lia.
  rewrite (KC2 hb hn (i - hb) Hin ltac:(clear - Hi Hhb Hhe; lia) (fun Hx => Hx)).
  replace (hb + (i - hb)) with i by lia.
  apply UNCH12; [clear - Hi Hhb Hhe Hb4096 Hbceil C1; lia | clear - Hi Hhb Hhe Hbceil HSTKlo; lia]. }
assert (HGH3 : garr8 SEGS (mrestrict (w_H W) (ms_mem ms1)) h (map (fun b : byte => bv_unsigned b) H)).
{ apply (hoT_garr_kept W memc (ms_mem ms1) h _); [| exact HHg].
  intros i Hi. rewrite length_map, HHL in Hi. apply HHB. clear - Hi; lia. }
assert (HPRE : ho_pre (mkHoC fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs h f len now out hb hn H FB O)).
{ unfold ho_pre; cbn [c_fq c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_k c_regs
     c_h c_f c_len c_now c_out c_hb c_hn c_H c_FB c_O].
  split; [exists mdc; exact HJ0|].
  repeat (split; [assumption|]); assumption. }

pose proof HFimg as HFimg2. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg2.
assert (HOBJ : forall io, In io [63; 64]%nat -> forall a, VAL (A_OBJ io) <= a < VAL (A_OBJ io) + 8 ->
   aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros io Hio a Ha.
  destruct (pa_obj_ro_unowned B io HRO Hio a Ha) as (Hown & Herr).
  assert (Hlt : (io < tfib_nobj)%nat) by (destruct Hio as [<- | [<- | []]]; apply Nat.ltb_lt; vm_compute; reflexivity).
  pose proof (pa_obj_img_all io Hlt) as (Hilo & Hihi). unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hilo, Hihi.
  assert (Himg : in_img SEGS a).
  { replace a with (VAL (A_OBJ io) + 0 + (a - VAL (A_OBJ io))) by lia.
    apply (pa_obj_win io 0 (a - VAL (A_OBJ io)) Hlt).
    destruct Hio as [<- | [<- | []]];
    match goal with |- 0 <= ?k < ?w => let w' := eval vm_compute in w in change w with w' end; lia. }
  destruct HK as (KC1 & KC2 & KC3 & _).
  rewrite UNCH3;
  [ | clear - Ha Hilo Hihi; lia | clear - Ha Hihi HSTKlo C1 C5; try unfold kLowMemEnd in *; lia
    | clear - Ha Hilo Hihi HFimg2; lia
    | clear - Ha Hihi HF8lo; unfold SB; lia ].
  rewrite KC3; [| exact Himg | exact Hown | exact Herr].
  apply UNCH12; [clear - Ha Hilo Hihi; lia | clear - Ha Hihi HSTKlo C1 C5; try unfold kLowMemEnd in *; lia]. }
assert (HKM3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (VAL (A_OBJ 63)) 8 reac_frame_clean_len_c.KM)
  by (apply (hoA_val_kept W W memc (ms_mem ms1) _ 8 _); [intros i Hi; apply (HOBJ 63%nat ltac:(cbn; tauto)); cbn [Z.of_nat] in Hi; lia | exact HKM]).
assert (HKT3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (VAL (A_OBJ 64)) 8 reac_frame_clean_len_c.KT)
  by (apply (hoA_val_kept W W memc (ms_mem ms1) _ 8 _); [intros i Hi; apply (HOBJ 64%nat ltac:(cbn; tauto)); cbn [Z.of_nat] in Hi; lia | exact HKT]).
assert (HRO3 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem ms1))).
{ intros a Hro Ho He. rewrite (proj1 (proj2 (proj2 HKEPT)) a); [exact (HROm a Hro Ho He) | | exact Ho | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hgot)]. }

assert (HOB3 : out <> 0 -> garr8 SEGS (mrestrict (w_H W) (ms_mem ms1)) out (map (fun b : byte => bv_unsigned b) O)).
{ intros Hout. destruct (HOUT Hout) as (HTO & _ & _).
  destruct HTO as (_ & Hot & Ham & Hos & _ & _ & _ & _ & HOL & HOG & HR1).
  apply (hoT_garr_kept W memc (ms_mem ms1) out _); [| exact HOG].
  intros i Hi. rewrite length_map, HOL in Hi. cbn [Z.of_nat] in Hi.
  destruct HK as (KC1 & KC2 & KC3 & KC4 & _).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
  destruct HR1 as [(cid & pos & Hf & Hlo & Hhi) | (b & m & Hb & Hlo & Hhi)].
  - pose proof Hf as Hfc. apply in_split in Hfc as (l1 & l2 & El).
    pose proof (sep_frames_pos SEGS B LAWS lyc S2 W mem2 md2 (1, fpos) (cid, pos) [] l1 l2 (proj1 HJ2m)
      ltac:(rewrite Hfrs2, El; reflexivity)) as Hdff.
    unfold zdisjoint, frame_rng in Hdff. cbn [fst snd] in Hdff. change (fs_frame_bytes 1) with 128 in Hdff. fold F in Hdff.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf) as (HG4096 & HGceil & _).
    pose proof (fs_frame_bytes_nonneg cid) as HGn.
    rewrite UNCH3;
    [ | clear - Hi Hlo Hhi HG4096 HGceil C1; lia | clear - Hi Hlo Hhi HGceil HSTKlo; lia
      | clear - Hi Hlo Hhi Hdff; lia
      | clear - Hi Ham HF8lo HF8hi HF8t; unfold SB in *; lia ].
    rewrite (KC4 cid pos i Hf ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; clear - Hi Hlo Hhi; lia) (fun Hx => Hx)).
    apply UNCH12; [clear - Hi Hlo Hhi HG4096 HGceil C1; lia | clear - Hi Hlo Hhi HGceil HSTKlo; lia].
  - assert (Hb2 : In (b, m) (ablocks B lyc S2)) by (rewrite Eab; exact Hb).
    pose proof (sep_block_frame SEGS B LAWS lyc S2 W mem2 md2 b m 1 fpos (proj1 HJ2m) Hb2 Hfin2) as Hdbf.
    unfold zdisjoint in Hdbf. cbn [fst snd] in Hdbf. change (fs_frame_bytes 1) with 128 in Hdbf. fold F in Hdbf.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hbx4096 & Hbxceil & _).
    rewrite UNCH3;
    [ | clear - Hi Hlo Hhi Hbx4096 Hbxceil C1; lia | clear - Hi Hlo Hhi Hbxceil HSTKlo; lia
      | clear - Hi Hlo Hhi Hdbf; lia
      | clear - Hi Ham HF8lo HF8hi HF8t; unfold SB in *; lia ].
    replace i with (b + (i - b)) by lia.
    rewrite (KC2 b m (i - b) Hb ltac:(clear - Hi Hlo Hhi; lia) (fun Hx => Hx)).
    replace (b + (i - b)) with i by lia.
    apply UNCH12; [clear - Hi Hlo Hhi Hbx4096 Hbxceil C1; lia | clear - Hi Hlo Hhi Hbxceil HSTKlo; lia]. }
pose proof (HSV 0%nat ltac:(lia)) as HSV0. pose proof (HSV 1%nat ltac:(lia)) as HSV1.
unfold ho_sreg in HSV0, HSV1. cbn [nth Z.of_nat] in HSV0, HSV1.
replace (spZ regs - 8 * (0 + 1)) with (spZ regs - 8) in HSV0 by lia.
replace (spZ regs - 8 * (1 + 1)) with (spZ regs - 16) in HSV1 by lia.
assert (HCH3 : exists ch', achain lyc (aview SEGS (w_H W) (ms_mem ms1)) (spZ regs - 16) (spZ regs) ch').
{ destruct (Z_lt_le_dec (spZ regs) (ly_top lyc - 16)) as [Ht | Ht].
  - eexists. apply (achain_push lyc (aview SEGS (w_H W) memc) _ (spZ regs) (s0Z regs) (raZ regs) ch (spZ regs - 16) Hch).
    + pose proof HJ0 as (_ & HLE & _). destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & HLT & _).
      rewrite HLT. clear - Htop H47; lia.
    + intros a Ha. destruct HK as (KC1 & _).
      rewrite UNCH3;
      [ | clear - Ha HSTKlo HSTK C1; lia | clear - Ha; lia | clear - Ha HFceil HSTKlo HSTK; lia
        | clear - Ha HSHhi HSTKlo HSTK; lia ].
      rewrite KC1; [| clear - Ha HSTKlo HSTK C1; lia | clear - Ha Hsp1; lia].
      apply UNCH12; [clear - Ha HSTKlo HSTK C1; lia | clear - Ha; lia].
    + apply (rdword_of_val_mem _ _ _ _ _ HSV0). hoA_bvr.
    + apply (rdword_of_val_mem _ _ _ _ _ HSV1). hoA_bvr.
    + exact Hra4.
    + clear - HSTKlo HSTK; lia.
    + clear - Hal16; lia.
    + exact Ht.
    + clear - Ht; lia.
  - exists []. left. split; [right; left; exact Ht | reflexivity]. }


pmkst HS.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
refine (HC (mkHoC fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs h f len now out hb hn H FB O)
          fpos lyc S2 W _ _ k _ sp1 F _ _ _ _ _ _ _ _ _ _ _).
all: cbn [c_fq c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_k c_regs c_h c_f c_len c_now c_out c_hb c_hn c_H c_FB c_O].
* unfold ho_base. refine (conj HPRE (conj _ (conj _ (conj eq_refl (conj _ _))))).
  + unfold ho_mid. cbn [c_fq c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_k c_regs c_h c_f c_len c_now c_out c_hb c_hn c_H c_FB c_O].
    split; [exact HJ2|]. split; [exact Hfrs2|]. split; [intros; reflexivity|].
    split; [rewrite Eab; apply Permutation_refl|]. split; [exact HKEPT|]. split; [exact HRO3|].
    split; [exact HGH3|]. split; [exact HHL|]. split; [exact HFLG3|]. lia.
  + unfold ho_sp1. cbn [c_fq c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_k c_regs c_h c_f c_len c_now c_out c_hb c_hn c_H c_FB c_O]. split; [reflexivity|]. split; [exact Hsp1 | exact Hsp1al].
  + unfold ho_regs_mid. cbn [c_fq c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_k c_regs c_h c_f c_len c_now c_out c_hb c_hn c_H c_FB c_O].
    split; [rewrite P2, (hoA_ew_of_U _ _ _ U60); reflexivity|].
    split; [rewrite P3, (ER 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp|].
    split; [rewrite P4, (ER 4%nat 4%bv ltac:(lia) eq_refl); exact Htp|].
    split; [rewrite P8, (hoA_ew_of_U _ _ _ U2); reflexivity|].
    split; [rewrite P9, (hoA_ew_of_U _ _ _ U60); reflexivity|].
    split; [rewrite P18, (hoA_ew_of_U _ _ _ U516); reflexivity|].
    split; [rewrite P21, (ER 10%nat 10%bv ltac:(lia) eq_refl); exact H10|].
    split; [rewrite P24, (hoA_ew_of_U _ _ _ U529); reflexivity|].
    rewrite P25, (hoA_ew_of_U _ _ _ U516); reflexivity.
  + unfold ho_saved. cbn [c_fq c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_k c_regs c_h c_f c_len c_now c_out c_hb c_hn c_H c_FB c_O]. exact HSV.
* rewrite P19, (ER 14%nat 14%bv ltac:(lia) eq_refl). exact H14.
* rewrite P20, (ER 13%nat 13%bv ltac:(lia) eq_refl). exact H13.
* rewrite P22, (ER 11%nat 11%bv ltac:(lia) eq_refl). exact H11.
* rewrite P23, (ER 12%nat 12%bv ltac:(lia) eq_refl). exact H12.
* rewrite P26, (AG 32%nat ltac:(lia)), E32. reflexivity.
* exact HFSH.
* exact HCH3.
* exact HOB3.
* exact HKM3.
* exact HKT3.
Qed.

End h.
End f.
End d.
