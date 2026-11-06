(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_lay_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlLayBlock.v, with its module paths and module names changed; 1072 of its 1143 lines of code are new or changed and 873 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd ACbf ACj1 DiscoACja DiscoACjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve DiscoRo ReacFrameCleanLen ReacHuntObserve ReacHuntObserveSeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis DRO : disco_ro_unowned B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Hypothesis ASM1 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TCOS : treac_disco_classify_on_segment_spec B.
Hypothesis TOBS : treac_disco_table_observe_spec B.

Lemma ho_pres_hi : forall (Wx : world SEGS) ma mb a,
  YM05.alloc_ceiling <= a < 2 ^ 64 ->
  aview SEGS (w_H Wx) mb a = aview SEGS (w_H Wx) ma a -> apresent (w_H Wx) ma a -> apresent (w_H Wx) mb a.
Proof.
intros Wx ma mb a Ha HE Hp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hb : 0 <= a < 2 ^ 64) by (clear - Ha C1; lia).
assert (Hni : ~ in_img SEGS a)
by (intros Him; pose proof (pa_segs_low a Him) as Hl; clear - Hl Ha C1 C5; unfold kLowMemEnd in *; lia).
exact (apresent_transfer SEGS (w_H Wx) (w_H Wx) ma mb a Hb Hni HE Hp).
Qed.

Lemma ho_val_kept : forall (Wa Wb : world SEGS) ma mb a (n : nat) v,
  (forall i, a <= i < a + Z.of_nat n -> aview SEGS (w_H Wb) mb i = aview SEGS (w_H Wa) ma i) ->
  val_mem SEGS (mrestrict (w_H Wa) ma) a n v -> val_mem SEGS (mrestrict (w_H Wb) mb) a n v.
Proof.
intros Wa Wb ma mb a n v HE Hv k Hk. rewrite <- (Hv k Hk).
apply (mbyte_of_aview SEGS). apply HE. lia.
Qed.

Lemma ho_val_of_bytes8 : forall (Wx : world SEGS) mx a v,
  (forall k, (k < 8)%nat -> aview SEGS (w_H Wx) mx (a + Z.of_nat k) = Some (YO0f.le_byte v 8 k)) ->
  val_mem SEGS (mrestrict (w_H Wx) mx) a 8 v.
Proof.
intros Wx mx a v HB k Hk.
destruct (aview_byte SEGS (w_H Wx) mx (a + Z.of_nat k) _ (HB k Hk)) as (b & Hb & Hv & Hr).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. rewrite <- Hv. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma ho_tail_kept : forall lyc Sc ly2 S2 (Wc W2 : world SEGS) memc mem2 mem3 md2 fpos F sp h out,
  AR SEGS B ly2 S2 W2 mem2 md2 ->
  frames S2 = (1, fpos) :: frames Sc ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall cid p, frame_addr ly2 cid p = frame_addr lyc cid p) ->
  F = frame_addr ly2 1 fpos ->
  treac_hunt_observe_kept B lyc Sc Wc memc W2 mem2 sp h out ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 128) -> ~ (SB + F / 8 <= a < SB + F / 8 + 16) ->
     a <> flag_addr ly2 1 fpos -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  treac_hunt_observe_kept B lyc Sc Wc memc W2 mem3 sp h out.
Proof.
intros lyc Sc ly2 S2 Wc W2 memc mem2 mem3 md2 fpos F sp h out HAR Hfrs HPerm HFA HFe HK HUN HPr.
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
- intros a Ha Hnw Hnt. rewrite HUN; [exact (K1 a Ha Hnw Hnt) | clear - Ha C1; lia
  | clear - Ha HFceil C1; lia | clear - Ha HF8hi C1; unfold SB; lia
  | intros ->; clear - Ha HFLrng C1; destruct HFLrng as (_ & _ & Q3); lia].
- intros b m i Hb Hi Hnt.
  assert (Hb2 : In (b, m) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb2) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 b m 1 fpos HAR Hb2 Hfin) as Hdbf.
  unfold zdisjoint in Hdbf. cbn [fst snd] in Hdbf. change (fs_frame_bytes 1) with 128 in Hdbf. rewrite <- HFe in Hdbf.
  destruct Hbapp as (Hba4096 & Hbapp). unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  rewrite HUN; [exact (K2 b m i Hb Hi Hnt) | clear - Hi Hb4096 Hbceil C1; lia
  | clear - Hi Hdbf; lia
  | destruct Hbapp as [Hbapp | [Hbapp Hbapp2]]; clear - Hi Hbapp HF8lo HF8t Hb4096 Hbceil C1; unfold SB; lia
  | intros Heq; apply (proj2 (Hbpres (b + i) ltac:(lia))); rewrite Heq; exact HFLown].
- intros a Hia Ho He.
  pose proof (pa_segs_low a Hia) as Hl. unfold kLowMemEnd in Hl.
  rewrite HUN; [exact (K3 a Hia Ho He) | clear - Hl; lia
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
  | intros Hin; destruct Hrng as [Hq | Hq];
    [clear - Hq Hin Hdff; lia | destruct HFhigh as (HFh0 & [HFhigh | [HFhigh HFhigh2]]); clear - Hq Hin HSlo HShi HFhigh HF4096 HFceil C1; unfold SB in *; lia]
  | intros Hin; destruct Hrng as [Hq | Hq];
    [destruct HGhigh as [HGhigh | [HGhigh HGhigh2]]; clear - Hq Hin HGhigh HG4096 HGceil HF8lo HF8t C1; unfold SB in *; lia | clear - Hq Hin HSsep; lia]
  | intros ->; destruct Hrng as [Hq | Hq];
    [apply (proj2 (HGpres (flag_addr ly2 1 fpos) Hq)); exact HFLown
    | destruct HFLa4096 as (HFLz & [HFLa | [HFLa HFLa2]]);
       unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLa;
       clear - Hq HSlo HShi HFLa; unfold SB in *; lia]].
- intros a Ha Hnw Hp. apply HPr. exact (K5 a Ha Hnw Hp).
- intros a Ha. apply HPr. exact (K6 a Ha).
Qed.

Lemma ho_frames_free : forall S2 Sc fpos,
  frames S2 = (1, fpos) :: frames Sc -> frames (stack_free_state 1 fpos S2) = frames Sc.
Proof.
intros S2 Sc fpos He. unfold stack_free_state, frames in *. cbn [st_fs fs_live set_fs] in *.
rewrite He. cbn [del_pos]. rewrite Z.eqb_refl, Z.eqb_refl. cbn [andb]. reflexivity.
Qed.

Lemma ho_sub_len_le : forall l (o : Z) (n : nat), (length (disco_table_c.sub l o n) <= n)%nat.
Proof.
intros l o n. unfold disco_table_c.sub. rewrite length_firstn. apply Nat.le_min_l.
Qed.

Lemma ho_answer_len : forall T G A, length G = 24%nat ->
  reac_hunt_observe_c.ho_answer T G A -> (length A <= 24)%nat.
Proof.
intros T G A HG (rr & Hr & HA). rewrite HA. destruct (rr <? 0); [rewrite HG; lia|].
unfold reac_hunt_observe_c.ho_entry. rewrite !length_app.
pose proof (ho_sub_len_le G 0 8) as L1. pose proof (ho_sub_len_le T (48 * rr + 8) 9) as L2.
pose proof (ho_sub_len_le G 17 3) as L3. pose proof (ho_sub_len_le T (48 * rr + 20) 4) as L4. lia.
Qed.

Lemma ho_model_mono : forall H FB O len now out r H' (P Q : list byte -> Prop),
  (out <> 0 -> length O = 24%nat) -> length FB = 50%nat ->
  (out <> 0 -> forall A, (length A <= 24)%nat -> P A -> Q A) ->
  tho_model H FB O len now out r H' P -> tho_model H FB O len now out r H' Q.
Proof.
intros H FB O len now out r H' P Q HO HFB HPQ (M1 & M2). split.
- intros Hr. destruct (M1 Hr) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|].
  intros Ho. apply (HPQ Ho); [rewrite (HO Ho); lia | exact (Q3 Ho)].
- intros Hr. destruct (M2 Hr) as (T' & cc & Q1 & Q2 & Q3 & Q4). exists T', cc.
  split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
  intros Ho. destruct (Q4 Ho) as (A & R1 & R2 & R3). exists A. split; [exact R1|].
  split; [apply (HPQ Ho); [|exact R2] | exact R3].
  apply (ho_answer_len T' (disco_classify_c.sight FB (reac_frame_clean_len_c.reac_frame_clean_len_model len)) A);
  [apply HuntObsFacts.sight_len; exact HFB | exact R1].
Qed.

Lemma ho_unwr_blk : forall ly2 S2 (W2 : world SEGS) mem2 md2 fpos F b m a,
  AR SEGS B ly2 S2 W2 mem2 md2 -> In (1, fpos) (frames S2) -> F = frame_addr ly2 1 fpos ->
  In (b, m) (ablocks B ly2 S2) -> b <= a < b + req_size m ->
  (0 <= a < 2 ^ 64) /\ ~ (F <= a < F + 128) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 16) /\
  a <> flag_addr ly2 1 fpos.
Proof.
intros ly2 S2 W2 mem2 md2 fpos F b m a HAR Hfin HFe Hb Ha.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR Hfin) as (HF4096 & HFceil & HFhigh).
destruct (FFL ly2 S2 W2 mem2 md2 1 fpos HAR Hfin) as (HFLpres & HFLown & HFLapp & HFLrng).
change (fs_frame_bytes 1) with 128 in *. rewrite <- HFe in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 b m 1 fpos HAR Hb Hfin) as Hdbf.
unfold zdisjoint in Hdbf. cbn [fst snd] in Hdbf. change (fs_frame_bytes 1) with 128 in Hdbf. rewrite <- HFe in Hdbf.
destruct Hbapp as (Hba0 & Hbapp). unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8t : F / 8 <= 17592184995824) by (apply Z.div_le_upper_bound; [lia | clear - HFceil C1; lia]).
split; [clear - Ha Hb4096 Hbceil C1; lia|].
split; [clear - Ha Hdbf; lia|].
split; [destruct Hbapp as [Hbapp | [Hbapp Hbapp2]]; clear - Ha Hbapp HF8lo HF8t Hb4096 Hbceil C1; unfold SB; lia|].
intros Heq. apply (proj2 (Hbpres a Ha)). rewrite Heq. exact HFLown.
Qed.


Lemma ho_unwr_frm : forall ly2 S2 (W2 : world SEGS) mem2 md2 fpos F cid pos a l1 l2,
  AR SEGS B ly2 S2 W2 mem2 md2 -> frames S2 = (1, fpos) :: l1 ++ (cid, pos) :: l2 ->
  F = frame_addr ly2 1 fpos ->
  frame_addr ly2 cid pos <= a < frame_addr ly2 cid pos + fs_frame_bytes cid ->
  (0 <= a < 2 ^ 64) /\ ~ (F <= a < F + 128) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 16) /\
  a <> flag_addr ly2 1 fpos.
Proof.
intros ly2 S2 W2 mem2 md2 fpos F cid pos a l1 l2 HAR Hfrs HFe Ha.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : In (1, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hf2 : In (cid, pos) (frames S2))
by (rewrite Hfrs; right; apply in_or_app; right; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR Hfin) as (HF4096 & HFceil & HFhigh).
destruct (FFL ly2 S2 W2 mem2 md2 1 fpos HAR Hfin) as (HFLpres & HFLown & HFLapp & HFLrng).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf2) as (HG4096 & HGceil & HGhigh).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hf2) as (HGal & _ & HGpres & _).
change (fs_frame_bytes 1) with 128 in *. rewrite <- HFe in *.
pose proof (sep_frames_pos SEGS B LAWS ly2 S2 W2 mem2 md2 (1, fpos) (cid, pos) [] l1 l2 HAR
  ltac:(rewrite Hfrs; reflexivity)) as Hdff.
unfold zdisjoint, frame_rng in Hdff. cbn [fst snd] in Hdff.
change (fs_frame_bytes 1) with 128 in Hdff. rewrite <- HFe in Hdff.
destruct HGhigh as (HGa0 & HGhigh). unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGhigh.
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8t : F / 8 <= 17592184995824) by (apply Z.div_le_upper_bound; [lia | clear - HFceil C1; lia]).
split; [clear - Ha HG4096 HGceil C1; lia|].
split; [clear - Ha Hdff; lia|].
split; [destruct HGhigh as [HGhigh | [HGhigh HGhigh2]];
        clear - Ha HGhigh HG4096 HGceil HF8lo HF8t C1; unfold SB; lia|].
intros Heq. apply (proj2 (HGpres a Ha)). rewrite Heq. exact HFLown.
Qed.

Lemma ho_seg_A : ho_seg_B_stmt B -> treac_hunt_observe_spec B.
Proof.
intros SEGB. unfold treac_hunt_observe_spec.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch h f len now out hb hn H FB O
HJ HROD Hra Hra4 Hgp Htp Hch Hal16 Hwin Hsp Hdepth H10 H11 H12 H13 H14
Rlen Rnow Rout Hh0 Hh8 Hin Hhb Hhe Hwr HOK HGH LFB Hfr50 Hout HKM HKT.
pose proof HJ as HJ0.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
pose proof (paj_ret_at (fx := fq) (PL := PL_disco) (PI := PI)) as RET.
destruct (ho_count (mrestrict (w_H W) memc) h H HOK HGH) as [Hnr HVn].
destruct (ho_entry B LAWS TL TLF fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs h
  (disco_table_c.n_of (disco_table_c.sub H 0 400)) hb hn HJ H10 Hal16 Hwin Hsp Hin Hhb Hhe Hh0 Hh8 Hnr HVn)
  as [HS SHOK].
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ hb hn HAR Hin) as Hbimg.
pose proof (al_shadow _ _ LAWS lyc Sc W memc mdc hb hn HAR Hin) as (Hbsh & Hbhull).
assert (Hhr : 0 <= h /\ h + 480 <= 2 ^ 63) by (clear - Hh0 Hhb Hhe Hbceil C1; lia).
assert (Hfr : REAC_HUNT_OBSERVE_STK = REAC_HUNT_OBSERVE_FRAME + CLS_STK) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hcls : 8192 <= CLS_STK)
by (unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK; lia).
assert (Hfr0 : REAC_HUNT_OBSERVE_FRAME = 176) by reflexivity.
set (E := EHO regs (disco_table_c.n_of (disco_table_c.sub H 0 400))) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, EHO; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2)
by (unfold E, EHO; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 h)
by (unfold E, EHO; rewrite Eimg_low by (unfold A_TEXT; lia);
    rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold cfg_at. change (w64 (BASE + AF_reac_hunt_observe)) with (Z_to_bv 64 (BASE + AF_reac_hunt_observe)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (unfold E, EHO; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (disco_table_c.n_of (disco_table_c.sub H 0 400)))
by (unfold E, EHO; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := idx_of_base rs 10%nat in let i := eval vm_compute in i in
  let r := eval vm_compute in (nth i rs got_regionP) in
  pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
       ltac:(intros o Ho; lia))) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end.
paj_run_to_tok RUNTO HS HJ SHOK HOspan 0x70a0.
{ eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - sp0);
  [reflexivity | cbn [ew ewset Nat.eqb]; rewrite Usp; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (HAV0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 176 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hnw. apply (ho_aview_frame _ _ W memc (ms_mem ms) a HFr Ha).
  intros (rr & Hinw & Hr).
  lazymatch type of Hinw with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hinw end;
  cbn [In] in Hinw;
  repeat (destruct Hinw as [<- | Hinw];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr;
     cbn [ew ewset Nat.eqb]; rewrite ?Usp; intros Hr;
     clear - Hr Hnw Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0; lia|]);
  destruct Hinw. }
clear_frames.
set (sp1 := 32 * ((spZ regs + -160) / 32)) in *.
destruct (sp1_facts (spZ regs + -160) ltac:(clear - Hceil Hslo Hwin Hsp Hstk0 C1 Hfr Hcls Hfr0; lia)
  ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al32 & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al32, Hsp1al16.
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by (clear - Hsp1r; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
    (denot_and_m32 Ev 2 (spZ regs) (-160)
       ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
       ltac:(clear - Hceil Hslo Hwin Hsp Hstk0 C1 Hfr Hcls Hfr0; lia)
       ltac:(clear - Hshi Hsp H47 Hstk0; lia)
       ltac:(clear - Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0; lia)) R2 end.
assert (Hsp1r64 : 0 <= sp1 < 2 ^ 64) by (clear - Hsp1 Hsp1al32 Hsp1al16 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 C3 Hfr Hcls Hfr0; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 60 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3;
  hei_pose Ev 60%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (E60 : ew Ev 60 = Z_to_bv 64 sp1)
  by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2; rewrite unsigned_lit_small by exact Hsp1r64; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 60%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by exact Hsp1r64; change (2 ^ 5) with 32;
          clear - Hsp1 Hsp1al32 Hsp1al16 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 C3 Hfr Hcls Hfr0; lia)) as HS3;
  clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
  pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
img_factsF E0.
pose proof (pa_obj_img 0%nat ltac:(unfold disco_nobj; lia)) as Hob241.
pose proof (pa_obj_img 1%nat ltac:(unfold disco_nobj; lia)) as Hob242.
pose proof (pa_obj_img 66%nat ltac:(unfold disco_nobj; lia)) as Hob307.
pose proof (pa_obj_img 67%nat ltac:(unfold disco_nobj; lia)) as Hob308.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob307, Hob308.
pose proof (palf_uar_img _ TL) as Huar. pose proof (palf_uar_al _ TLF) as Huar4.
pose proof (pa_val_range 241%nat) as VR241. pose proof (pa_val_range 242%nat) as VR242.
pose proof (pa_val_range 307%nat) as VR307. pose proof (pa_val_range 308%nat) as VR308.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 56 0 56 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
          rewrite E60, unsigned_lit_small by exact Hsp1r64;
          split; [clear - Hsp1 Hsp1al32 Hsp1al16 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 C3 Hfr Hcls Hfr0; lia|]; split; [clear - Hsp1 Hsp1al32 Hsp1al16 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 C3 Hfr Hcls Hfr0; lia|]; split; [|apply Forall_nil];
          intros o Ho; apply (apresent_writable SEGS); apply HJpres; clear - Ho Hsp1 Hsp1al32 Hsp1al16 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 C3 Hfr Hcls Hfr0; lia)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          evalE AG;
          clear - Hsp1 Hsp1al32 Hsp1al16 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 C3 Hfr Hcls Hfr0 VR241 VR242 VR307 VR308 Hob241 Hob242 Hob307 Hob308 Huar Hbceil Hbimg Hbapp Hhb Hhe Hh0 Hb4096; unfold off_img, IMG_LO, IMG_TOP in *; repeat split; first [zone_lia | match goal with |- ?g => idtac "ZLFAIL"; idtac g end; fail])) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
reshok HS.
paj_run_tok RUN HS HJ SHOK HOspan.
{ eapply awr_ok_cons_stack_off with (n := 60%nat) (d := sp1 - sp0);
  [reflexivity | cbn [ew ewset Nat.eqb]; rewrite E60, unsigned_lit_small by exact Hsp1r64; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - sp0);
  [reflexivity | cbn [ew ewset Nat.eqb]; rewrite (AG 2%nat) by lia; rewrite Usp; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 10%nat) (b := h);
  [reflexivity | cbn [ew ewset Nat.eqb]; rewrite (AG 10%nat) by lia; rewrite E10; apply unsigned_lit_small; lia
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply Hwr; lia | apply awr_ok_nil]. }
assert (HAV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 176 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha Hnw. apply (ho_aview_frame _ _ W (ms_mem ms) (ms_mem ms0) a HFr Ha).
  intros (rr & Hinw & Hr).
  lazymatch type of Hinw with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hinw end;
  cbn [In] in Hinw;
  repeat (destruct Hinw as [<- | Hinw];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
     clear - Hr Hnw Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0; lia|]);
  destruct Hinw. }
clear_frames.
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pmkst HS.
rewrite (palf_sm1 B TLF).
pose proof (count_cid_le_length 1 (frames Sc)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msY) _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 1 (ASM1 fq) ltac:(lia)
    W (ms_regs msX) (ms_mem msY) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) end.
- unfold spZ at 1. rewrite R2, E60, unsigned_lit_small by exact Hsp1r64. lia.
- rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al. cbn. reflexivity.
- clear - Hsp1 Hsp; lia.
- clear - Hsp1 Hsp Hwin Hfr Hcls Hfr0 Hes; lia.
- rewrite R3, (AG 3%nat) by lia. unfold E, EHO. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl). exact Hgp.
- rewrite R4, (AG 4%nat) by lia. unfold E, EHO. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl). exact Htp.
- exact R1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- assert (Hff : fs_frames 1 = 8192) by (vm_compute; reflexivity). rewrite Hff.
  clear - Hcnt Hdepth; unfold REAC_HUNT_OBSERVE_DEPTH, CLS_DEPTH in Hdepth; lia. }
cbv beta. clear R1 R2 R3 R4.
intros W2 c2 Hwle2 (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin
  & Hnev2 & Hbb2 & Hz & Hflag & HK & HJ1 & (fS2 & ES2)).
rewrite Hes in HK. replace (sp0 + (sp1 - sp0) - 4096) with (sp1 - 4096) in HK by lia.
replace (sp0 + (sp1 - sp0)) with sp1 in HK by lia.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6]%nat AG
  ltac:(idtac; first [keptFL_with ltac:(idtac; lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
  eapply (ho_kept_inblk B LAWS _ _ _ _ _ _ _ _ _ _ 10%nat _ _ _ _ _ h hb hn);
  [exact HK | exact (proj1 HJ2) | rewrite Eab; exact Hin | evalE AG | exact Hin | lia | lia | lia | lia | intros a Ha Hn; exact Hn] end) HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)
                     | match goal with |- ?g => idtac "KEPTFAIL" g end]).
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
change (fs_frame_bytes 1) with 128 in *.
set (F := frame_addr lyc 1 fpos) in *.
clear SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (ho_shok B LAWS Ev lyc S2 W mem2 md2 hb hn h (proj1 HJ2) ltac:(rewrite Eab; exact Hin) Hhb Hhe Hh0
  ltac:(rewrite (AG 10%nat) by lia; exact E10) ltac:(rewrite (AG 32%nat) by lia; exact E32)) as SHOK end.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
fold F in HFal, HFhi, HFpres, HFSpres.
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 516 (HPTR 5) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia;
          change (2 ^ 5) with 32; lia)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
paj_run_to_tok RUNTO HS HJ2 SHOK HOspan 0x710c.
{ eapply awr_ok_cons_stack_off with (n := 60%nat) (d := sp1 - sp0);
  [reflexivity | cbn [ew ewset Nat.eqb]; rewrite E60, unsigned_lit_small by exact Hsp1r64; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - sp0);
  [reflexivity | cbn [ew ewset Nat.eqb]; rewrite (AG 2%nat) by lia; rewrite Usp; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS.
assert (EE : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn Hr. unfold E, EHO. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ n r Hr). }
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24. prreg HS (26%bv : bv 5) Q26.
prreg HS (27%bv : bv 5) Q27.
lazymatch type of HS with st_ok_pi _ _ ?Ev0 ?ssx ?msx =>
  pose proof (st_ok_pi_region_nth Ev0 ssx msx 1 _ HS eq_refl) as HR;
  assert (HB : bv_unsigned (ew Ev0 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
cbn [ms_mem restrict mkst] in HR.
assert (V0 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + (-8)) 8 (bv_unsigned (getr regs 1%bv))).
{ eapply ho_slot;
  [exact HR | exact HB | cbn [In]; tauto
  | rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (1%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
    symmetry; apply Z_to_bv_bv_unsigned
  | apply u64_range]. }
assert (V1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + (-16)) 8 (bv_unsigned (getr regs 8%bv))).
{ eapply ho_slot;
  [exact HR | exact HB | cbn [In]; tauto
  | rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (8%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
    symmetry; apply Z_to_bv_bv_unsigned
  | apply u64_range]. }
assert (V2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + (-24)) 8 (bv_unsigned (getr regs 9%bv))).
{ eapply ho_slot;
  [exact HR | exact HB | cbn [In]; tauto
  | rewrite (AG 9%nat) by lia; rewrite (EE 9%nat (9%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
    symmetry; apply Z_to_bv_bv_unsigned
  | apply u64_range]. }
assert (V3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + (-32)) 8 (bv_unsigned (getr regs 18%bv))).
{ eapply ho_slot;
  [exact HR | exact HB | cbn [In]; tauto
  | rewrite (AG 18%nat) by lia; rewrite (EE 18%nat (18%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
    symmetry; apply Z_to_bv_bv_unsigned
  | apply u64_range]. }
assert (V4 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + (-40)) 8 (bv_unsigned (getr regs 19%bv))).
{ eapply ho_slot;
  [exact HR | exact HB | cbn [In]; tauto
  | rewrite (AG 19%nat) by lia; rewrite (EE 19%nat (19%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
    symmetry; apply Z_to_bv_bv_unsigned
  | apply u64_range]. }
assert (V5 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + (-48)) 8 (bv_unsigned (getr regs 20%bv))).
{ eapply ho_slot;
  [exact HR | exact HB | cbn [In]; tauto
  | rewrite (AG 20%nat) by lia; rewrite (EE 20%nat (20%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
    symmetry; apply Z_to_bv_bv_unsigned
  | apply u64_range]. }
assert (V6 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + (-56)) 8 (bv_unsigned (getr regs 21%bv))).
{ eapply ho_slot;
  [exact HR | exact HB | cbn [In]; tauto
  | rewrite (AG 21%nat) by lia; rewrite (EE 21%nat (21%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
    symmetry; apply Z_to_bv_bv_unsigned
  | apply u64_range]. }
assert (V7 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + (-64)) 8 (bv_unsigned (getr regs 22%bv))).
{ eapply ho_slot;
  [exact HR | exact HB | cbn [In]; tauto
  | rewrite (AG 22%nat) by lia; rewrite (EE 22%nat (22%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
    symmetry; apply Z_to_bv_bv_unsigned
  | apply u64_range]. }
assert (V8 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + (-72)) 8 (bv_unsigned (getr regs 23%bv))).
{ eapply ho_slot;
  [exact HR | exact HB | cbn [In]; tauto
  | rewrite (AG 23%nat) by lia; rewrite (EE 23%nat (23%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
    symmetry; apply Z_to_bv_bv_unsigned
  | apply u64_range]. }
assert (V9 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + (-80)) 8 (bv_unsigned (getr regs 24%bv))).
{ eapply ho_slot;
  [exact HR | exact HB | cbn [In]; tauto
  | rewrite (AG 24%nat) by lia; rewrite (EE 24%nat (24%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
    symmetry; apply Z_to_bv_bv_unsigned
  | apply u64_range]. }
assert (V10 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + (-88)) 8 (bv_unsigned (getr regs 25%bv))).
{ eapply ho_slot;
  [exact HR | exact HB | cbn [In]; tauto
  | rewrite (AG 25%nat) by lia; rewrite (EE 25%nat (25%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
    symmetry; apply Z_to_bv_bv_unsigned
  | apply u64_range]. }
assert (V11 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + (-96)) 8 (bv_unsigned (getr regs 26%bv))).
{ eapply ho_slot;
  [exact HR | exact HB | cbn [In]; tauto
  | rewrite (AG 26%nat) by lia; rewrite (EE 26%nat (26%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
    symmetry; apply Z_to_bv_bv_unsigned
  | apply u64_range]. }
assert (V12 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + (-104)) 8 (bv_unsigned (getr regs 27%bv))).
{ eapply ho_slot;
  [exact HR | exact HB | cbn [In]; tauto
  | rewrite (AG 27%nat) by lia; rewrite (EE 27%nat (27%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
    symmetry; apply Z_to_bv_bv_unsigned
  | apply u64_range]. }
assert (HSV : ho_saved (mkHoC fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs h f len now out hb hn H FB O)
  W (ms_mem ms1)).
{ unfold ho_saved. cbn [c_regs]. intros j Hj.
  destruct j as [|j]; [cbn [ho_sreg nth]; replace (spZ regs - 8 * (Z.of_nat 0 + 1)) with (spZ regs + (-8)) by (cbn; lia); exact V0|];
  destruct j as [|j]; [cbn [ho_sreg nth]; replace (spZ regs - 8 * (Z.of_nat 1 + 1)) with (spZ regs + (-16)) by (cbn; lia); exact V1|];
  destruct j as [|j]; [cbn [ho_sreg nth]; replace (spZ regs - 8 * (Z.of_nat 2 + 1)) with (spZ regs + (-24)) by (cbn; lia); exact V2|];
  destruct j as [|j]; [cbn [ho_sreg nth]; replace (spZ regs - 8 * (Z.of_nat 3 + 1)) with (spZ regs + (-32)) by (cbn; lia); exact V3|];
  destruct j as [|j]; [cbn [ho_sreg nth]; replace (spZ regs - 8 * (Z.of_nat 4 + 1)) with (spZ regs + (-40)) by (cbn; lia); exact V4|];
  destruct j as [|j]; [cbn [ho_sreg nth]; replace (spZ regs - 8 * (Z.of_nat 5 + 1)) with (spZ regs + (-48)) by (cbn; lia); exact V5|];
  destruct j as [|j]; [cbn [ho_sreg nth]; replace (spZ regs - 8 * (Z.of_nat 6 + 1)) with (spZ regs + (-56)) by (cbn; lia); exact V6|];
  destruct j as [|j]; [cbn [ho_sreg nth]; replace (spZ regs - 8 * (Z.of_nat 7 + 1)) with (spZ regs + (-64)) by (cbn; lia); exact V7|];
  destruct j as [|j]; [cbn [ho_sreg nth]; replace (spZ regs - 8 * (Z.of_nat 8 + 1)) with (spZ regs + (-72)) by (cbn; lia); exact V8|];
  destruct j as [|j]; [cbn [ho_sreg nth]; replace (spZ regs - 8 * (Z.of_nat 9 + 1)) with (spZ regs + (-80)) by (cbn; lia); exact V9|];
  destruct j as [|j]; [cbn [ho_sreg nth]; replace (spZ regs - 8 * (Z.of_nat 10 + 1)) with (spZ regs + (-88)) by (cbn; lia); exact V10|];
  destruct j as [|j]; [cbn [ho_sreg nth]; replace (spZ regs - 8 * (Z.of_nat 11 + 1)) with (spZ regs + (-96)) by (cbn; lia); exact V11|];
  destruct j as [|j]; [cbn [ho_sreg nth]; replace (spZ regs - 8 * (Z.of_nat 12 + 1)) with (spZ regs + (-104)) by (cbn; lia); exact V12|].
  exfalso. clear - Hj. lia. }
assert (HAV : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 176 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha Hnw. apply (ho_aview_frame _ _ W mem2 (ms_mem ms1) a HFr Ha).
  intros (rr & Hinw & Hr).
  lazymatch type of Hinw with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hinw end;
  cbn [In] in Hinw;
  repeat (destruct Hinw as [<- | Hinw];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
     clear - Hr Hnw Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0 Hes; lia|]);
  destruct Hinw. }
assert (HKEPT : treac_hunt_observe_kept B lyc Sc W memc W (ms_mem ms1) (spZ regs) h out).
{ pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Jpres & _).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hnw _.
    assert (Hb : 0 <= a < 2 ^ 64) by (clear - Ha C1; lia).
    assert (Hn1 : ~ (spZ regs - 176 <= a < spZ regs)) by (clear - Hnw Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0 Hes; lia).
    rewrite (HAV a Hb Hn1), (K1 a Ha ltac:(clear - Hnw Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0 Hes; lia)). rewrite (HAV1 _ Hb Hn1). apply HAV0; [exact Hb | exact Hn1].
  - intros b m i Hbl Hi _.
    destruct (al_blocks _ _ LAWS lyc Sc _ _ _ b m (proj1 HJ) Hbl) as (_ & Gb4096 & Gbceil & _ & _ & _).
    assert (Hb : 0 <= b + i < 2 ^ 64) by (clear - Hi Gb4096 Gbceil C1; lia).
    assert (Hn1 : ~ (spZ regs - 176 <= b + i < spZ regs)) by (clear - Hi Gbceil C1 Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0 Hes; lia).
    rewrite (HAV (b + i) Hb Hn1), (K2 b m i Hbl Hi ltac:(intros [])).
    rewrite (HAV1 _ Hb Hn1). apply HAV0; [exact Hb | exact Hn1].
  - intros a Hia Ho He.
    pose proof (pa_segs_low a Hia) as Hl. unfold kLowMemEnd in Hl.
    assert (Hb : 0 <= a < 2 ^ 64) by (clear - Hl; lia).
    assert (Hn1 : ~ (spZ regs - 176 <= a < spZ regs)) by (clear - Hl C1 Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0 Hes; lia).
    rewrite (HAV a Hb Hn1), (K3 a Hia Ho He). rewrite (HAV1 _ Hb Hn1). apply HAV0; [exact Hb | exact Hn1].
  - intros cid pos a Hf Hr _.
    destruct (frames_bounds SEGS B LAWS lyc Sc _ _ _ cid pos (proj1 HJ) Hf) as (G1 & G2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Gn.
    assert (Grng : 0 <= a /\ a < YM05.alloc_ceiling).
    { pose proof Hr as Hr2. unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr2. cbn [fst snd] in Hr2.
      destruct Hr2 as [Hr2 | Hr2]; clear - Hr2 G1 G2 Gn C1; lia. }
    assert (Hb : 0 <= a < 2 ^ 64) by (clear - Grng C1; unfold SHADOW_OFF in *; lia).
    assert (Hn1 : ~ (spZ regs - 176 <= a < spZ regs))
      by (clear - Grng C1 Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0 Hes; unfold SHADOW_OFF in *; lia).
    rewrite (HAV a Hb Hn1), (K4 cid pos a Hf Hr ltac:(intros [])).
    rewrite (HAV1 _ Hb Hn1). apply HAV0; [exact Hb | exact Hn1].
  - intros a Ha Hnw Hp.
    assert (Hb : 0 <= a < 2 ^ 64) by (clear - Ha C1; lia).
    assert (Hn1 : ~ (spZ regs - 176 <= a < spZ regs)) by (clear - Hnw Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0 Hes; lia).
    apply (ho_pres_hi W mem2 (ms_mem ms1) a Ha (HAV a Hb Hn1)).
    apply (K5 a Ha ltac:(clear - Hnw Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0 Hes; lia)).
    apply (ho_pres_hi W (ms_mem ms) (ms_mem ms0) a Ha (HAV1 a Hb Hn1)).
    apply (ho_pres_hi W memc (ms_mem ms) a Ha (HAV0 a Hb Hn1)). exact Hp.
  - intros a Ha. apply Jpres. clear - Ha Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0 Hes; lia. }
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof HOK as HOK2. destruct HOK2 as (HL & _ & _ & _).
assert (HGH2 : garr8 SEGS (mrestrict (w_H W) (ms_mem ms1)) h (map (fun b : byte => bv_unsigned b) H)).
{ apply (ho_garr_kept W W memc (ms_mem ms1) h _); [|exact HGH].
  intros i Hi. rewrite length_map in Hi.
  assert (Hb : 0 <= i < 2 ^ 64) by (clear - Hi HL Hh0 Hhb Hhe Hbceil C1; lia).
  assert (Hn1 : ~ (spZ regs - 176 <= i < spZ regs))
    by (clear - Hi HL Hhb Hhe Hbceil C1 Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0 Hes; lia).
  assert (Hk2 : aview SEGS (w_H W) mem2 i = aview SEGS (w_H W) (ms_mem ms0) i).
  { replace i with (hb + (i - hb)) by lia. apply (K2 hb hn (i - hb) Hin); [clear - Hi HL Hhb Hhe; lia | intros []]. }
  rewrite (HAV i Hb Hn1), Hk2, (HAV1 i Hb Hn1). apply HAV0; [exact Hb | exact Hn1]. }
assert (HFSH : ho_fsh W (ms_mem ms1) F ho_shZ).
{ intros i Hi.
  assert (Hnz : nth (Z.to_nat i) ho_shZ 0 = 0).
  { unfold ho_shZ. destruct (Z.to_nat i) as [|kk]; [reflexivity|].
    do 15 (destruct kk as [|kk]; [reflexivity|]). apply nth_overflow. cbn [length]. lia. }
  rewrite Hnz.
  assert (Hb : 0 <= SB + F / 8 + i < 2 ^ 64) by (clear - Hi HF4096 HFceil C1; unfold SB; lia).
  assert (Hn1 : ~ (spZ regs - 176 <= SB + F / 8 + i < spZ regs))
    by (clear - Hi HF4096 HFceil C1 Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0 Hes; unfold SB; lia).
  rewrite (HAV _ Hb Hn1).
  unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
  change (fs_frame_bytes 1) with 128 in Hz.
  apply Hz. change (128 / 8) with 16. lia. }
destruct (FFL lyc S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLapp & HFLrng).
assert (HFLG : rdword (aview SEGS (w_H W) (ms_mem ms1)) (F + 120) = Some (flag_addr lyc 1 fpos)).
{ apply rdword_of_val_mem; [|clear - HFLrng C1; destruct HFLrng as (R1 & _ & R3); lia].
  apply (ho_val_kept W W mem2 (ms_mem ms1) (F + 120) 8 (flag_addr lyc 1 fpos)).
  - intros i Hi.
    assert (Hb : 0 <= i < 2 ^ 64) by (clear - Hi HF4096 HFceil C1; cbn [Z.of_nat] in Hi; lia).
    assert (Hn1 : ~ (spZ regs - 176 <= i < spZ regs))
      by (clear - Hi HF4096 HFceil C1 Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0 Hes; cbn [Z.of_nat] in Hi; lia).
    exact (HAV _ Hb Hn1).
  - apply val_mem_of_rdword. change (fs_frame_bytes 1) with 128 in Hflag.
    replace (F + 120) with (F + 128 - 8) by lia. exact Hflag. }
pose proof (proj1 (proj2 HJ0)) as Hlyle.
destruct Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & Elytop & Elyslo & Elyshi & _).
assert (HCH : exists ch0, achain lyc (aview SEGS (w_H W) (ms_mem ms1)) (spZ regs - 16) (spZ regs) ch0).
{ destruct (Z_lt_ge_dec (spZ regs) (ly_top lyc - 16)) as [Htp16 | Htp16];
  [|exists []; left; split; [right; left; clear - Htp16; lia | reflexivity]].
  assert (HKa : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
  { intros a Ha.
    assert (Hb : 0 <= a < 2 ^ 64) by (clear - Ha Hceil Hslo Hwin Hsp Hstk0 C1 Hfr Hcls Hfr0; lia).
    assert (Hn1 : ~ (spZ regs - 176 <= a < spZ regs)) by (clear - Ha; lia).
    assert (Hce : YM05.alloc_ceiling <= a) by (clear - Ha Hceil Hslo Hwin Hsp Hstk0 C1 Hfr Hcls Hfr0; lia).
    rewrite (HAV a Hb Hn1), (K1 a (conj Hce (proj2 Ha)) ltac:(clear - Ha Hsp1; lia)).
    rewrite (HAV1 a Hb Hn1). apply HAV0; [exact Hb | exact Hn1]. }
  exists ((spZ regs, raZ regs, s0Z regs) :: ch).
  apply (achain_push lyc (aview SEGS (w_H W) memc) (aview SEGS (w_H W) (ms_mem ms1))
    (spZ regs) (s0Z regs) (raZ regs) ch (spZ regs - 16) Hch
    ltac:(clear - Htop H47 Elytop Elyshi; lia) HKa).
  - apply rdword_of_val_mem; [|unfold raZ; apply u64_range].
    replace (spZ regs - 8) with (spZ regs - 8 * (Z.of_nat 0 + 1)) by (cbn; lia).
    exact (HSV 0%nat ltac:(lia)).
  - apply rdword_of_val_mem; [|unfold s0Z; apply u64_range].
    replace (spZ regs - 16) with (spZ regs - 8 * (Z.of_nat 1 + 1)) by (cbn; lia).
    exact (HSV 1%nat ltac:(lia)).
  - exact Hra4.
  - clear - Hceil Hslo Hwin Hsp Hstk0 Hfr Hcls Hfr0 Hes; lia.
  - clear - Hal16; lia.
  - clear - Htp16; lia.
  - lia. }
assert (HOUT2 : out <> 0 -> garr8 SEGS (mrestrict (w_H W) (ms_mem ms1)) out
  (map (fun b : byte => bv_unsigned b) O)).
{ intros Ho. destruct (Hout Ho) as (HTO & _ & _).
  destruct HTO as (Ho8 & Ho63 & Hoam & Howin & Hosep & Hora & Hohull & Hoawr & HoL & HoG & HoR1).
  apply (ho_garr_kept W W memc (ms_mem ms1) out _); [|exact HoG].
  intros i Hi. rewrite length_map in Hi. rewrite HoL in Hi.
  assert (Hb : 0 <= i < 2 ^ 64) by (clear - Hi Ho63 Rout; lia).
  assert (Hn1 : ~ (spZ regs - 176 <= i < spZ regs))
    by (clear - Hi Howin Hsp1 Hsp1al32 Hceil Hslo Hwin Hsp Hstk0 Hshi H47 C1 Hfr Hcls Hfr0 Hes; lia).
  assert (Hk2o : aview SEGS (w_H W) mem2 i = aview SEGS (w_H W) (ms_mem ms0) i).
  { destruct HoR1 as [(cid & pos & Hcf & Hc1 & Hc2) | (bb & mm & Hbb & Hb1 & Hb2)].
    - apply (K4 cid pos i Hcf); [left; unfold in_zr, frame_rng; cbn [fst snd]; clear - Hi Hc1 Hc2; lia | intros []].
    - replace i with (bb + (i - bb)) by lia.
      apply (K2 bb mm (i - bb) Hbb); [clear - Hi Hb1 Hb2; lia | intros []]. }
  rewrite (HAV i Hb Hn1), Hk2o, (HAV1 i Hb Hn1). apply HAV0; [exact Hb | exact Hn1]. }
apply (SEGB (mkHoC fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs h f len now out hb hn H FB O)
  fpos lyc S2 W (ms_mem ms1) _ k _ sp1 F).
- unfold ho_base. cbn [c_fq c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_k
    c_regs c_h c_f c_len c_now c_out c_hb c_hn c_H c_FB c_O].
  split.
  + unfold ho_pre. cbn [c_fq c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_k
      c_regs c_h c_f c_len c_now c_out c_hb c_hn c_H c_FB c_O].
    repeat match goal with |- _ /\ _ => split end.
    all: first [assumption | (exists mdc; exact HJ0) | (exists ch; exact Hch) | (clear - Rlen Rnow Rout; lia)].
  + split.
    * unfold ho_mid. cbn [c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_regs c_h c_out c_H].
      split; [exact HJ2|]. split; [exact Hfrs2|]. split; [intros; reflexivity|].
      split; [rewrite Eab; apply Permutation_refl|]. split; [exact HKEPT|].
      split; [exact HGH2|]. split; [exact HFLG|]. split; [reflexivity | cbn [c_k]; lia].
    * split.
      -- unfold ho_sp1. cbn [c_regs]. split; [reflexivity|]. split; [clear - Hsp1; lia | exact Hsp1al32].
      -- split; [reflexivity|].
         split.
         ++ unfold ho_regs_mid. cbn [c_regs c_h c_out c_now c_f c_len].
            split; [rewrite Q2, E60; reflexivity|].
            split; [rewrite Q3, (AG 3%nat) by lia;
                    rewrite (EE 3%nat (3%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Hgp|].
            split; [rewrite Q4, (AG 4%nat) by lia;
                    rewrite (EE 4%nat (4%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Htp|].
            split; [rewrite Q8, (AG 2%nat) by lia;
                    rewrite (EE 2%nat (2%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
                    unfold spZ, w64; symmetry; apply Z_to_bv_bv_unsigned|].
            split; [rewrite Q9, E60; reflexivity|].
            split; [rewrite Q18, RF; reflexivity|].
            split; [rewrite Q22, (AG 10%nat) by lia; rewrite E10; reflexivity|].
            split; [rewrite Q26, RF; reflexivity|].
            rewrite Q27, (AG 32%nat) by lia. rewrite E32. reflexivity.
         ++ exact HSV.
- rewrite Q19, (AG 14%nat) by lia.
  rewrite (EE 14%nat (14%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact H14.
- rewrite Q20, (AG 13%nat) by lia.
  rewrite (EE 13%nat (13%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact H13.
- rewrite Q21, (AG 11%nat) by lia.
  rewrite (EE 11%nat (11%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact H11.
- rewrite Q24, (AG 12%nat) by lia.
  rewrite (EE 12%nat (12%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact H12.
- exact HFSH.
- destruct HCH as [ch0 Hch0]. exists ch0. exact Hch0.
- cbn [c_out c_O]. exact HOUT2.

Qed.

Lemma ho_seg_T : ho_seg_T_stmt B.
Proof.
unfold ho_seg_T_stmt.
intros c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 r.
intros (HPRE & HMID & HSP1 & HFeq & HREGS & HSAVED) Hr20 Hrv H25 HFSH HOK2 HMODEL.
destruct HPRE as (HJ0e & HROD & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin & Hsp & Hdepth &
  Rlen & Rnow & Rout & Hh0 & Hh8 & Hin & Hhb & Hhe & Hwr & HOK & LFB & HGH & Hfr50 & Hout & HKM & HKT & Hchx).
destruct HMID as (HJ2 & Hfrs2 & HFA & HPerm & HKEPT & HGH2 & HFLG & HLEN & Hk2).
destruct HSP1 as (Hsp1e & Hsp1 & Hsp1al32).
destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R22 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (FFL ly2 S2 W2 mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLapp & HFLrng).
change (fs_frame_bytes 1) with 128 in *.
rewrite (HFA 1 fpos) in *.
assert (HFL : forall cid p, flag_addr ly2 cid p = flag_addr (c_lyc c) cid p).
{ intros cid p. unfold flag_addr, frame_addr in *. pose proof (HFA 0 0) as E0. lia. }
rewrite (HFL 1 fpos) in *.
rewrite <- HFeq in *.
assert (HSH0 : val_mem SEGS (mrestrict (w_H W2) mem2) (SB + F / 8) 8 17509995355275653617).
{ apply ho_val_of_bytes8. intros k Hk. rewrite (HFSH (Z.of_nat k) ltac:(clear - Hk; lia)).
  do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). clear - Hk; lia. }
assert (HSH1 : val_mem SEGS (mrestrict (w_H W2) mem2) (SB + F / 8 + 8) 8 4092851187).
{ apply ho_val_of_bytes8. intros k Hk.
  replace (SB + F / 8 + 8 + Z.of_nat k) with (SB + F / 8 + Z.of_nat (8 + k)) by (rewrite Nat2Z.inj_add; cbn; lia).
  rewrite (HFSH (Z.of_nat (8 + k)) ltac:(clear - Hk; lia)).
  do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). clear - Hk; lia. }
set (E := Eimg (Ereg regs2 [])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr).
{ intros n rr Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs2 _ n rr Hr). }
assert (E8 : ew E 8 = Z_to_bv 64 (spZ (c_regs c)))
by (rewrite (EE 8%nat (8%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 F)
by (rewrite (EE 18%nat (18%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact R18).
assert (E26 : ew E 26 = Z_to_bv 64 F)
by (rewrite (EE 26%nat (26%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact R26).
assert (E25 : ew E 25 = Z_to_bv 64 (SB + F / 8))
by (rewrite (EE 25%nat (25%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact H25).
assert (E20 : ew E 20 = Z_to_bv 64 r)
by (rewrite (EE 20%nat (20%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Hr20).
assert (HF8 : F / 8 = 4 * (F / 32)).
{ assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
  rewrite HFq at 1. replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; [lia | clear - HFceil C1; lia]).
pose proof (proj1 HJ2) as HARx.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
assert (HSTKe : REAC_HUNT_OBSERVE_STK = 176 + CLS_STK) by reflexivity.
assert (HCLSe : 8192 <= CLS_STK) by (unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK; lia).
assert (HspZ : YM05.alloc_ceiling + 8368 <= spZ (c_regs c) <= 2 ^ 47)
by (clear - Hwin Hsp Hslo Hshi H47 Hceil Hstk0 HSTKe HCLSe; lia).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v)
by (intros m v Hm Hv; cbn [base_val]; rewrite Hm; apply unsigned_lit_small; exact Hv).
assert (HS : st_ok_pi (fx := c_fq c) SEGS VAL E
  (mkSS 29088 sr_atoms
    [ YP09.mkRegion (Some 25%nat) 0 16 0 16
        [YP09.mkChunk 0 (CVal 8 (SLit 17509995355275653617)); YP09.mkChunk 8 (CVal 8 (SLit 4092851187))];
      YP09.mkRegion (Some 8%nat) (-104) 0 0 0
      [ YP09.mkChunk (-8) (CVal 8 (SLit (bv_unsigned (getr (c_regs c) 1%bv))));
       YP09.mkChunk (-16) (CVal 8 (SLit (bv_unsigned (getr (c_regs c) 8%bv))));
       YP09.mkChunk (-24) (CVal 8 (SLit (bv_unsigned (getr (c_regs c) 9%bv))));
       YP09.mkChunk (-32) (CVal 8 (SLit (bv_unsigned (getr (c_regs c) 18%bv))));
       YP09.mkChunk (-40) (CVal 8 (SLit (bv_unsigned (getr (c_regs c) 19%bv))));
       YP09.mkChunk (-48) (CVal 8 (SLit (bv_unsigned (getr (c_regs c) 20%bv))));
       YP09.mkChunk (-56) (CVal 8 (SLit (bv_unsigned (getr (c_regs c) 21%bv))));
       YP09.mkChunk (-64) (CVal 8 (SLit (bv_unsigned (getr (c_regs c) 22%bv))));
       YP09.mkChunk (-72) (CVal 8 (SLit (bv_unsigned (getr (c_regs c) 23%bv))));
       YP09.mkChunk (-80) (CVal 8 (SLit (bv_unsigned (getr (c_regs c) 24%bv))));
       YP09.mkChunk (-88) (CVal 8 (SLit (bv_unsigned (getr (c_regs c) 25%bv))));
       YP09.mkChunk (-96) (CVal 8 (SLit (bv_unsigned (getr (c_regs c) 26%bv))));
       YP09.mkChunk (-104) (CVal 8 (SLit (bv_unsigned (getr (c_regs c) 27%bv)))) ] ]
    None
    (mkFacts [ (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (18%nat, HPTR 5);
               (25%nat, mkAF (SB + 512) (SB + 17592186044416) 2) ] [] []))
  (restrict (w_H W2) (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + 29088)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - unfold E. apply (regs_ok_agree 32 (Ereg regs2 [])).
    + split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
    + vm_compute. reflexivity.
    + apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E25, unsigned_lit_small by (unfold SB; clear - HF8lo HF8hi; lia).
      split; [unfold SB; clear - HF8lo; lia|]. split; [unfold SB; clear - HF8hi; lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS).
        unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres.
        apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia))).
      * apply Forall_cons;
        [apply (chunk_ok_val SEGS E _ (SB + F / 8) 0 8 _ 17509995355275653617);
         [reflexivity | cbn [Z.of_N Z.mul]; lia | zside | change (N.to_nat 8) with 8%nat; rewrite Z.add_0_r; exact HSH0]|].
        apply Forall_cons;
        [apply (chunk_ok_val SEGS E _ (SB + F / 8) 8 8 _ 4092851187);
         [reflexivity | cbn [Z.of_N Z.mul]; lia | zside | change (N.to_nat 8) with 8%nat; exact HSH1]|].
        apply Forall_nil.
    + rewrite E8, unsigned_lit_small by (clear - HspZ C1; lia).
      split; [clear - HspZ C1; lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons;
      [ apply (chunk_ok_val SEGS E _ (spZ (c_regs c)) (-8) 8 _ (bv_unsigned (getr (c_regs c) 1%bv)));
        [reflexivity | cbn [Z.of_N Z.mul]; apply u64_range | zside
        | change (N.to_nat 8) with 8%nat;
          replace (spZ (c_regs c) + -8) with (spZ (c_regs c) - 8 * (Z.of_nat 0 + 1)) by (cbn; lia);
          exact (HSAVED 0%nat ltac:(lia))] |];
      apply Forall_cons;
      [ apply (chunk_ok_val SEGS E _ (spZ (c_regs c)) (-16) 8 _ (bv_unsigned (getr (c_regs c) 8%bv)));
        [reflexivity | cbn [Z.of_N Z.mul]; apply u64_range | zside
        | change (N.to_nat 8) with 8%nat;
          replace (spZ (c_regs c) + -16) with (spZ (c_regs c) - 8 * (Z.of_nat 1 + 1)) by (cbn; lia);
          exact (HSAVED 1%nat ltac:(lia))] |];
      apply Forall_cons;
      [ apply (chunk_ok_val SEGS E _ (spZ (c_regs c)) (-24) 8 _ (bv_unsigned (getr (c_regs c) 9%bv)));
        [reflexivity | cbn [Z.of_N Z.mul]; apply u64_range | zside
        | change (N.to_nat 8) with 8%nat;
          replace (spZ (c_regs c) + -24) with (spZ (c_regs c) - 8 * (Z.of_nat 2 + 1)) by (cbn; lia);
          exact (HSAVED 2%nat ltac:(lia))] |];
      apply Forall_cons;
      [ apply (chunk_ok_val SEGS E _ (spZ (c_regs c)) (-32) 8 _ (bv_unsigned (getr (c_regs c) 18%bv)));
        [reflexivity | cbn [Z.of_N Z.mul]; apply u64_range | zside
        | change (N.to_nat 8) with 8%nat;
          replace (spZ (c_regs c) + -32) with (spZ (c_regs c) - 8 * (Z.of_nat 3 + 1)) by (cbn; lia);
          exact (HSAVED 3%nat ltac:(lia))] |];
      apply Forall_cons;
      [ apply (chunk_ok_val SEGS E _ (spZ (c_regs c)) (-40) 8 _ (bv_unsigned (getr (c_regs c) 19%bv)));
        [reflexivity | cbn [Z.of_N Z.mul]; apply u64_range | zside
        | change (N.to_nat 8) with 8%nat;
          replace (spZ (c_regs c) + -40) with (spZ (c_regs c) - 8 * (Z.of_nat 4 + 1)) by (cbn; lia);
          exact (HSAVED 4%nat ltac:(lia))] |];
      apply Forall_cons;
      [ apply (chunk_ok_val SEGS E _ (spZ (c_regs c)) (-48) 8 _ (bv_unsigned (getr (c_regs c) 20%bv)));
        [reflexivity | cbn [Z.of_N Z.mul]; apply u64_range | zside
        | change (N.to_nat 8) with 8%nat;
          replace (spZ (c_regs c) + -48) with (spZ (c_regs c) - 8 * (Z.of_nat 5 + 1)) by (cbn; lia);
          exact (HSAVED 5%nat ltac:(lia))] |];
      apply Forall_cons;
      [ apply (chunk_ok_val SEGS E _ (spZ (c_regs c)) (-56) 8 _ (bv_unsigned (getr (c_regs c) 21%bv)));
        [reflexivity | cbn [Z.of_N Z.mul]; apply u64_range | zside
        | change (N.to_nat 8) with 8%nat;
          replace (spZ (c_regs c) + -56) with (spZ (c_regs c) - 8 * (Z.of_nat 6 + 1)) by (cbn; lia);
          exact (HSAVED 6%nat ltac:(lia))] |];
      apply Forall_cons;
      [ apply (chunk_ok_val SEGS E _ (spZ (c_regs c)) (-64) 8 _ (bv_unsigned (getr (c_regs c) 22%bv)));
        [reflexivity | cbn [Z.of_N Z.mul]; apply u64_range | zside
        | change (N.to_nat 8) with 8%nat;
          replace (spZ (c_regs c) + -64) with (spZ (c_regs c) - 8 * (Z.of_nat 7 + 1)) by (cbn; lia);
          exact (HSAVED 7%nat ltac:(lia))] |];
      apply Forall_cons;
      [ apply (chunk_ok_val SEGS E _ (spZ (c_regs c)) (-72) 8 _ (bv_unsigned (getr (c_regs c) 23%bv)));
        [reflexivity | cbn [Z.of_N Z.mul]; apply u64_range | zside
        | change (N.to_nat 8) with 8%nat;
          replace (spZ (c_regs c) + -72) with (spZ (c_regs c) - 8 * (Z.of_nat 8 + 1)) by (cbn; lia);
          exact (HSAVED 8%nat ltac:(lia))] |];
      apply Forall_cons;
      [ apply (chunk_ok_val SEGS E _ (spZ (c_regs c)) (-80) 8 _ (bv_unsigned (getr (c_regs c) 24%bv)));
        [reflexivity | cbn [Z.of_N Z.mul]; apply u64_range | zside
        | change (N.to_nat 8) with 8%nat;
          replace (spZ (c_regs c) + -80) with (spZ (c_regs c) - 8 * (Z.of_nat 9 + 1)) by (cbn; lia);
          exact (HSAVED 9%nat ltac:(lia))] |];
      apply Forall_cons;
      [ apply (chunk_ok_val SEGS E _ (spZ (c_regs c)) (-88) 8 _ (bv_unsigned (getr (c_regs c) 25%bv)));
        [reflexivity | cbn [Z.of_N Z.mul]; apply u64_range | zside
        | change (N.to_nat 8) with 8%nat;
          replace (spZ (c_regs c) + -88) with (spZ (c_regs c) - 8 * (Z.of_nat 10 + 1)) by (cbn; lia);
          exact (HSAVED 10%nat ltac:(lia))] |];
      apply Forall_cons;
      [ apply (chunk_ok_val SEGS E _ (spZ (c_regs c)) (-96) 8 _ (bv_unsigned (getr (c_regs c) 26%bv)));
        [reflexivity | cbn [Z.of_N Z.mul]; apply u64_range | zside
        | change (N.to_nat 8) with 8%nat;
          replace (spZ (c_regs c) + -96) with (spZ (c_regs c) - 8 * (Z.of_nat 11 + 1)) by (cbn; lia);
          exact (HSAVED 11%nat ltac:(lia))] |];
      apply Forall_cons;
      [ apply (chunk_ok_val SEGS E _ (spZ (c_regs c)) (-104) 8 _ (bv_unsigned (getr (c_regs c) 27%bv)));
        [reflexivity | cbn [Z.of_N Z.mul]; apply u64_range | zside
        | change (N.to_nat 8) with 8%nat;
          replace (spZ (c_regs c) + -104) with (spZ (c_regs c) - 8 * (Z.of_nat 12 + 1)) by (cbn; lia);
          exact (HSAVED 12%nat ltac:(lia))] |];
      apply Forall_nil.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 25%nat (SB + F / 8) E25) by (unfold SB; clear - HF8lo HF8hi; lia).
    rewrite (VB 8%nat (spZ (c_regs c)) E8) by (clear - HspZ C1; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct HFhigh as (HFa0 & HFa);
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFa;
    unfold SB;
    repeat split;
    first [clear - HF4096 HFceil HF8lo HF8hi HF8 HFa HspZ C1 C5; destruct HFa as [HFa | [HFa HFa2]]; lia
          | match goal with |- ?g => idtac "DJFAIL"; idtac g end; fail].
  - unfold facts_ok. split; [|split; exact I]. cbn [f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E8, unsigned_lit_small by (clear - HspZ C1; lia);
            change (2 ^ 4) with 16; clear - Hal16 HspZ C1; lia|].
    split; [unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E18, unsigned_lit_small by (clear - HF4096 HFceil C1; lia);
            change (2 ^ 5) with 32; clear - HF4096 HFceil HFal C1; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E25, unsigned_lit_small by (unfold SB; clear - HF8lo HF8hi; lia);
            change (2 ^ 2) with 4; unfold SB;
            split; [clear - HF8lo HF8hi HF4096; lia|]; split;
            [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult
            | clear - HF8hi HF4096; lia]|].
    exact I. }
assert (HnoF : forall a, F <= a < F + 128 -> ~ aowned B ly2 S2 a)
by (intros a Ha; exact (proj2 (HFpres a Ha))).
assert (HnoS : forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> ~ aowned B ly2 S2 a).
{ intros a Ha. unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres.
  pose proof (proj2 (HFSpres (a - (SB + F / 8)) ltac:(change (128 / 8) with 16; lia))) as Hq.
  replace (SB + F / 8 + (a - (SB + F / 8))) with a in Hq by lia. exact Hq. }
assert (HnoK : forall a, spZ (c_regs c) - 104 <= a < spZ (c_regs c) -> ~ aowned B ly2 S2 a).
{ intros a Ha Ho. pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HARx Ho) as Hlow.
  clear - Ha Hlow HspZ C1; lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 (flag_addr (c_lyc c) 1 fpos)] HS
    ltac:(vm_compute; reflexivity)) as HS3;
  hei_pose Ev 528%nat [Z_to_bv 64 (flag_addr (c_lyc c) 1 fpos)] end.
clear HS. rename HS3 into HS.
assert (AG : forall n, (n < 33)%nat -> ew (havoc E 528 [Z_to_bv 64 (flag_addr (c_lyc c) 1 fpos)]) n = ew E n)
by (intros n Hn; rewrite ew_havoc_old by lia; reflexivity).
assert (E528 : ew (havoc E 528 [Z_to_bv 64 (flag_addr (c_lyc c) 1 fpos)]) 528
  = Z_to_bv 64 (flag_addr (c_lyc c) 1 fpos))
by (exact (ew_havoc_new _ 528 [Z_to_bv 64 (flag_addr (c_lyc c) 1 fpos)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E18' : ew (havoc E 528 [Z_to_bv 64 (flag_addr (c_lyc c) 1 fpos)]) 18 = Z_to_bv 64 F)
by (rewrite (AG 18%nat) by lia; exact E18).
assert (E25' : ew (havoc E 528 [Z_to_bv 64 (flag_addr (c_lyc c) 1 fpos)]) 25 = Z_to_bv 64 (SB + F / 8))
by (rewrite (AG 25%nat) by lia; exact E25).
assert (E8' : ew (havoc E 528 [Z_to_bv 64 (flag_addr (c_lyc c) 1 fpos)]) 8 = Z_to_bv 64 (spZ (c_regs c)))
by (rewrite (AG 8%nat) by lia; exact E8).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _
    (YP09.mkRegion (Some 18%nat) 0 128 0 128 [YP09.mkChunk 120 (CVal 8 (SOff 528 0))]) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
          rewrite E18', unsigned_lit_small by (clear - HF4096 HFceil C1; lia);
          split; [clear - HF4096; lia|]; split; [clear - HF4096 HFceil C1; lia|]; split;
          [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
          | apply Forall_cons; [|apply Forall_nil];
            apply (chunk_ok_val SEGS Ev _ F 120 8 _ (flag_addr (c_lyc c) 1 fpos));
            [cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | cbn [Z.of_N Z.mul]; clear - HFLrng C1; destruct HFLrng as (Q1 & _ & Q3); lia | zside
            | change (N.to_nat 8) with 8%nat; apply val_mem_of_rdword; exact HFLG] ])
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite E18', E25', E8';
          rewrite ?unsigned_lit_small by (unfold SB; clear - HF4096 HFceil HF8lo HF8hi HspZ C1; lia);
          destruct HFhigh as (HFa0 & HFa);
          unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFa; unfold SB;
          repeat split;
          first [clear - HF4096 HFceil HF8lo HF8hi HF8 HFa HspZ C1 C5; destruct HFa as [HFa | [HFa HFa2]]; lia
                | match goal with |- ?g => idtac "DJ2FAIL"; idtac g end; fail])) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
add_flag_region HS AG E528 HFLpres HFLrng HFLown HnoF HnoS HnoK.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (26%bv : bv 5) (SOff 18 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E18';
          rewrite unsigned_lit_small by (clear - HF4096 HFceil C1; lia);
          rewrite Z.add_0_r; rewrite R26; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
pose proof (aj_flag_store_pi (fx := c_fq c) B LAWS ML ASF FFL) as RUNF.
paj_run_flag_sh RUNF HS HJ2.
- lia.
- intros a (rr & Hinw & Hr).
  lazymatch type of Hinw with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hinw end.
  cbn [In] in Hinw.
  repeat (destruct Hinw as [<- | Hinw];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
     first [ right; rewrite (HFL 1 fpos); clear - Hr; lia
           | left; right; right; right; exists 1, fpos; split; [left; reflexivity|]; left;
             unfold in_zr, frame_rng; cbn [fst snd]; rewrite (HFA 1 fpos); rewrite <- HFeq;
             change (fs_frame_bytes 1) with 128; clear - Hr; lia
           | left; right; right; right; exists 1, fpos; split; [left; reflexivity|]; right;
             unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; rewrite (HFA 1 fpos);
             rewrite <- HFeq; change (fs_frame_bytes 1) with 128; change (128 / 8) with 16;
             unfold SB; clear - Hr; lia
           | exfalso; clear - Hr; lia
           | match goal with |- ?g => idtac "WRFAIL"; idtac g end; fail ]|]).
  destruct Hinw.
- intros msr HSr. rewrite ?HFL.
  lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
    pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
    pose proof (field_of_region Ex (ms_mem msr) 528%nat (flag_addr (c_lyc c) 1 fpos)
      [YP09.mkChunk 0 (CVal 1 (SLit 0))] 0 1 0 1 0 1%N (SLit 0) 0 HR
      ltac:(rewrite E528; apply unsigned_lit_small; clear - HFLrng C1;
            destruct HFLrng as (Q1 & _ & Q3); lia)
      ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0.
  cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0.
- pose proof (paj_ret_at (fx := c_fq c) (PL := PL_disco) (PI := PI)) as RET.
  prreg HS (1%bv : bv 5) RR1. prreg HS (10%bv : bv 5) RR10.
  prreg HS (2%bv : bv 5) RP2. prreg HS (3%bv : bv 5) RP3. prreg HS (4%bv : bv 5) RP4.
  prreg HS (8%bv : bv 5) RP8. prreg HS (9%bv : bv 5) RP9. prreg HS (18%bv : bv 5) RP18.
  prreg HS (19%bv : bv 5) RP19. prreg HS (20%bv : bv 5) RP20. prreg HS (21%bv : bv 5) RP21.
  prreg HS (22%bv : bv 5) RP22. prreg HS (23%bv : bv 5) RP23. prreg HS (24%bv : bv 5) RP24.
  prreg HS (25%bv : bv 5) RP25. prreg HS (26%bv : bv 5) RP26. prreg HS (27%bv : bv 5) RP27.
  assert (HUNCH : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 128) ->
    ~ (SB + F / 8 <= a < SB + F / 8 + 16) -> a <> flag_addr ly2 1 fpos ->
    aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hq1 Hq2 Hq3. apply (ho_aview_frame _ _ W2 mem2 (ms_mem ms) a HFr Ha).
    intros (rr & Hinw & Hr).
    lazymatch type of Hinw with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hinw end.
    cbn [In] in Hinw.
    repeat (destruct Hinw as [<- | Hinw];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
       first [ apply Hq3; rewrite (HFL 1 fpos); clear - Hr; lia
             | apply Hq1; clear - Hr; lia
             | apply Hq2; unfold SB in *; clear - Hr; lia
             | exfalso; clear - Hr; lia
             | match goal with |- ?g => idtac "UNFAIL"; idtac g end; fail ]|]).
    destruct Hinw. }
  assert (HPRES3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a).
  { intros a (Hh & bb & Hbb). split; [exact Hh|].
    assert (Hne : mrestrict (w_H W2) (ms_mem ms) (Z_to_bv 64 a) <> None).
    { apply HG. unfold mrestrict. rewrite Hh. cbn. rewrite Hbb. discriminate. }
    unfold mrestrict in Hne. rewrite Hh in Hne. cbn in Hne.
    destruct (ms_mem ms (Z_to_bv 64 a)) as [b2|]; [exists b2; reflexivity | exfalso; apply Hne; reflexivity]. }
  eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold ho_post, treac_hunt_observe_post.
  assert (HFe2 : F = frame_addr ly2 1 fpos) by (rewrite (HFA 1 fpos); exact HFeq).
  assert (HOUTUN : c_out c <> 0 -> forall i, c_out c <= i < c_out c + 24 ->
    aview SEGS (w_H W2) (ms_mem ms) i = aview SEGS (w_H W2) mem2 i).
  { intros Ho i Hi. destruct (Hout Ho) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HR1) & _ & _).
    destruct HR1 as [(cid & pos & Hcf & Hc1 & Hc2) | (bb & mm & Hbb & Hb1 & Hb2)].
    - apply in_split in Hcf as (l1 & l2 & El).
      destruct (ho_unwr_frm ly2 S2 W2 mem2 md2 fpos F cid pos i l1 l2 HARx
        ltac:(rewrite Hfrs2, El; reflexivity) HFe2
        ltac:(rewrite (HFA cid pos); clear - Hi Hc1 Hc2; lia)) as (P1 & P2 & P3 & P4).
      apply HUNCH; [exact P1 | exact P2 | exact P3 | exact P4].
    - assert (Hbb2 : In (bb, mm) (ablocks B ly2 S2))
        by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hbb]).
      destruct (ho_unwr_blk ly2 S2 W2 mem2 md2 fpos F bb mm i HARx Hfin2 HFe2 Hbb2
        ltac:(clear - Hi Hb1 Hb2; lia)) as (P1 & P2 & P3 & P4).
      apply HUNCH; [exact P1 | exact P2 | exact P3 | exact P4]. }
  assert (HHUN : forall i, c_h c <= i < c_h c + 480 ->
    aview SEGS (w_H W2) (ms_mem ms) i = aview SEGS (w_H W2) mem2 i).
  { intros i Hi.
    assert (Hhb2 : In (c_hb c, c_hn c) (ablocks B ly2 S2))
      by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hin]).
    destruct (ho_unwr_blk ly2 S2 W2 mem2 md2 fpos F (c_hb c) (c_hn c) i HARx Hfin2 HFe2 Hhb2
      ltac:(clear - Hi Hhb Hhe; lia)) as (P1 & P2 & P3 & P4).
    apply HUNCH; [exact P1 | exact P2 | exact P3 | exact P4]. }
  exists (c_fq c), ly2, (stack_free_state 1 fpos S2), (ms_regs ms), (ms_mem ms),
    (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat md2)) mat'
      (with_vm_backing (m_vm_lazy md2) mat md2)), r, H2.
  assert (HRA1 : getr (ms_regs ms) 1 = getr (c_regs c) 1) by (rewrite RR1; apply Z_to_bv_bv_unsigned).
  split.
  { cbn [ms_regs]. rewrite HRA1, Hra. reflexivity. }
  split; [intros kk _; reflexivity|].
  split; [left; reflexivity|].
  split.
  { eapply (ajournal_mono_k _ _); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ2 | exact Hk2]. }
  split.
  { apply aregs_preserved_eqs;
    [ rewrite RP2 | rewrite RP3 | rewrite RP4 | rewrite RP8 | rewrite RP9 | rewrite RP18 | rewrite RP19
    | rewrite RP20 | rewrite RP21 | rewrite RP22 | rewrite RP23 | rewrite RP24 | rewrite RP25
    | rewrite RP26 | rewrite RP27 ];
    cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
    first [ apply Z_to_bv_bv_unsigned
          | rewrite E8; unfold spZ; apply Z_to_bv_bv_unsigned
          | rewrite (EE 3%nat (3%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)), R3, Hgp; reflexivity
          | rewrite (EE 4%nat (4%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)), R4, Htp; reflexivity
          | match goal with |- ?g => idtac "AREGFAIL"; idtac g end; fail ]. }
  split; [cbn [ms_regs]; rewrite RR10, E20; reflexivity|].
  split; [exact (ho_frames_free S2 (c_Sc c) fpos Hfrs2)|].
  split; [unfold ablocks; rewrite blocks_stack_free_state; exact HPerm|].
  split.
  { apply (ho_tail_kept (c_lyc c) (c_Sc c) ly2 S2 (c_W c) W2 (c_memc c) mem2 (ms_mem ms) md2 fpos F
      (spZ (c_regs c)) (c_h c) (c_out c) HARx Hfrs2 HPerm HFA HFe2 HKEPT HUNCH HPRES3). }
  split.
  { apply (ho_garr_kept W2 W2 mem2 (ms_mem ms) (c_h c) _); [|exact HGH2].
    intros i Hi. rewrite length_map in Hi. apply HHUN. clear - Hi HLEN HOK; destruct HOK as (HL & _).
    rewrite HLEN in Hi. lia. }
  split; [exact HOK2|].
  split; [exact Hrv|].
  apply (ho_model_mono _ _ _ _ _ _ _ _ (fun A => garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c)
    (map (fun b : byte => bv_unsigned b) A)));
  [ intros Hz0; destruct (Hout Hz0) as (HTO & _ & _);
    destruct HTO as (_ & _ & _ & _ & _ & _ & _ & _ & HoL & _ & _); exact HoL
  | exact LFB
  | intros Hz0 A HA HP;
    apply (ho_garr_kept W2 W2 mem2 (ms_mem ms) (c_out c) _); [|exact HP];
    intros i Hi; rewrite length_map in Hi; apply (HOUTUN Hz0); clear - Hi HA; lia
  | exact HMODEL ].
Qed.

End h.
End f.
End d.
