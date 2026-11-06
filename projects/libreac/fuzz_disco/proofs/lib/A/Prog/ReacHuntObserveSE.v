(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 794 of its 823 lines of code are new or changed and 40 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis DRO : disco_ro_unowned B.
Hypothesis TOBS : treac_disco_table_observe_spec B.

Definition ho_H3 (c : hoC) : list byte :=
  disco_table_c.sub (c_H c) 0 400 ++ ho_Lk' c ++ disco_table_c.sub (c_H c) 412 12 ++
  (if disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400) =? 0
   then Mem.le8 (Z_to_bv 64 (c_now c)) else disco_table_c.sub (c_H c) 424 8) ++ skipn 432 (c_H c).

Lemma ec_firstn_app : forall {X} (a b : list X) n, length a = n -> firstn n (a ++ b) = a.
Proof. intros X a b n H. subst n. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma ec_skipn_app : forall {X} (a b : list X) n, length a = n -> skipn n (a ++ b) = b.
Proof. intros X a b n H. subst n. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.

Lemma ec_garr8_l : forall m p (l1 l2 : list Z), garr8 SEGS m p (l1 ++ l2) -> garr8 SEGS m p l1.
Proof.
intros m p l1 l2 H j Hj.
destruct (H j ltac:(rewrite length_app; lia)) as [Hv Hr].
rewrite app_nth1 in Hv, Hr by exact Hj.
split; [exact Hv | exact Hr].
Qed.

Lemma ec_garr8_r : forall m p (l1 l2 : list Z), garr8 SEGS m p (l1 ++ l2) ->
  garr8 SEGS m (p + Z.of_nat (length l1)) l2.
Proof.
intros m p l1 l2 H j Hj.
destruct (H (length l1 + j)%nat ltac:(rewrite length_app; lia)) as [Hv Hr].
rewrite app_nth2 in Hv, Hr by lia.
replace (length l1 + j - length l1)%nat with j in Hv, Hr by lia.
replace (p + Z.of_nat (length l1) + Z.of_nat j) with (p + Z.of_nat (length l1 + j)) by lia.
split; [exact Hv | exact Hr].
Qed.

Lemma ec_garr8_app : forall m p (l1 l2 : list Z), garr8 SEGS m p l1 ->
  garr8 SEGS m (p + Z.of_nat (length l1)) l2 -> garr8 SEGS m p (l1 ++ l2).
Proof.
intros m p l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. exact (H1 j Hlt).
- rewrite app_nth2 by exact Hge.
  destruct (H2 (j - length l1)%nat ltac:(lia)) as [Hv Hr].
  replace (p + Z.of_nat (length l1) + Z.of_nat (j - length l1)) with (p + Z.of_nat j) in Hv by lia.
  split; [exact Hv | exact Hr].
Qed.

Lemma ec_val_tr : forall (W1 : world SEGS) m1 (W2 : world SEGS) m2 a (n : nat) v,
  val_mem SEGS (mrestrict (w_H W1) m1) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x) ->
  val_mem SEGS (mrestrict (w_H W2) m2) a n v.
Proof.
intros W1 m1 W2 m2 a n v HV HK k Hk. rewrite <- (HV k Hk).
apply (mbyte_of_aview SEGS). apply HK. lia.
Qed.

Lemma ho_awr_tr : forall STK sp0 FP bl0 blc blc' ly ly' own a,
  Permutation blc' blc -> (forall cid p, frame_addr ly' cid p = frame_addr ly cid p) ->
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc' ly' own a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own a HP HF [H | [(Hfp & b & n & Hb & Hr) | [(b & n & Hb & Hn & Hr) | (cid & pos & Hin & Hr)]]].
- left; exact H.
- right; left. split; [exact Hfp|]. exists b, n. split; [apply (Permutation_in _ (Permutation_sym HP)); exact Hb | exact Hr].
- right; right; left. exists b, n. split; [apply (Permutation_in _ (Permutation_sym HP)); exact Hb | split; [exact Hn | exact Hr]].
- right; right; right. exists cid, pos. split; [exact Hin|]. rewrite HF. exact Hr.
Qed.

Lemma ec_frame_eq : forall ly ly', ly_F ly' = ly_F ly -> forall cid p, frame_addr ly' cid p = frame_addr ly cid p.
Proof. intros ly ly' H cid p. unfold frame_addr. rewrite H. reflexivity. Qed.

Lemma ec_kept : forall lyc Sc (W : world SEGS) memc ly2 S2 (W2 : world SEGS) mem2 (W3 : world SEGS) mem3 sp sp1 h out,
  treac_hunt_observe_kept B lyc Sc W memc W2 mem2 sp h out ->
  treac_disco_table_observe_kept B ly2 S2 W2 mem2 W3 mem3 sp1 h ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall cid pos, In (cid, pos) (frames Sc) -> In (cid, pos) (frames S2)) ->
  (forall cid p, frame_addr ly2 cid p = frame_addr lyc cid p) ->
  sp - REAC_HUNT_OBSERVE_STK <= sp1 - REAC_DISCO_TABLE_OBSERVE_STK -> sp1 <= sp ->
  YM05.alloc_ceiling <= sp - REAC_HUNT_OBSERVE_STK -> sp <= 2 ^ 64 ->
  treac_hunt_observe_kept B lyc Sc W memc W3 mem3 sp h out.
Proof.
intros lyc Sc W memc ly2 S2 W2 mem2 W3 mem3 sp sp1 h out HK HT HP Hfr HFA Hw1 Hw2 Hac Hsp.
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6). destruct HT as (T1 & T2 & T3 & T4 & T5 & T6).
assert (Ht : forall a, ~ tho_wr h out a -> ~ (h <= a < h + 400))
  by (intros a Hn Ha; apply Hn; unfold tho_wr; left; lia).
split.
{ intros a Ha Hns Hnw.
  assert (Hn1 : ~ (sp1 - REAC_DISCO_TABLE_OBSERVE_STK <= a < sp1)) by lia.
  rewrite (T1 a Ha Hn1 (Ht a Hnw)). apply K1; assumption. }
split.
{ intros b m i Hin Hi Hnw.
  rewrite (T2 b m i (Permutation_in _ (Permutation_sym HP) Hin) Hi (Ht _ Hnw)). apply (K2 b m i); assumption. }
split; [intros a H1 H2 H3; rewrite (T3 a H1 H2 H3); apply K3; assumption|].
split.
{ intros cid pos a Hin Hr Hnw.
  assert (Hr2 : in_zr a (frame_rng ly2 (cid, pos)) \/
                in_zr a (shadow_addr (frame_addr ly2 cid pos), fs_frame_bytes cid / 8))
    by (unfold frame_rng in *; cbn [fst snd] in *; rewrite !HFA; exact Hr).
  rewrite (T4 cid pos a (Hfr cid pos Hin) Hr2 (Ht a Hnw)). apply (K4 cid pos a); assumption. }
split.
{ intros a Ha Hns Hp.
  assert (Hn1 : ~ (sp1 - REAC_DISCO_TABLE_OBSERVE_STK <= a < sp1)) by lia.
  apply (T5 a Ha Hn1). apply K5; assumption. }
intros a Ha. destruct (Z_lt_le_dec a (sp1 - REAC_DISCO_TABLE_OBSERVE_STK)) as [Hlt | Hge].
- apply T5; [lia | lia | apply K6; lia].
- destruct (Z_lt_le_dec a sp1) as [Hlt2 | Hge2]; [apply T6; lia|].
  apply T5; [lia | lia | apply K6; lia].
Qed.

Lemma ec_hok : forall H T' Lk' Rest, length H = 480%nat -> hunt_c.hunt_ok H -> length T' = 400%nat ->
  disco_table_c.table_ok T' -> length Lk' = 12%nat -> disco_classify_c.lock_ok Lk' -> length Rest = 68%nat ->
  disco_table_c.sub Rest 28 4 = disco_table_c.sub H 440 4 -> hunt_c.hunt_ok (T' ++ Lk' ++ Rest).
Proof.
intros H T' Lk' Rest LH (_ & _ & _ & V) LT TOK LL LOK LR SR.
split; [rewrite !length_app; lia|].
split; [rewrite (ec_firstn_app T' _ 400 LT); exact TOK|].
split; [rewrite (ec_skipn_app T' _ 400 LT), (ec_firstn_app Lk' _ 12 LL); exact LOK|].
unfold disco_table_c.s32_at, disco_table_c.u_at in *.
rewrite !HuntObsLib.sub_app_r by lia.
replace (440 - Z.of_nat (length T') - Z.of_nat (length Lk')) with 28 by lia.
rewrite SR. exact V.
Qed.

Lemma ho_E_call : ho_seg_F_stmt B ->
  forall (c : hoC) fpos ly2 S2 W2 mem3 md3 k2 regs3 sp1 F,
  ho_base B c fpos ly2 S2 W2 mem3 md3 k2 (ho_H3 c) regs3 sp1 F ->
  getr regs3 1 = Z_to_bv 64 (BASE + 0x7258) ->
  getr regs3 10 = w64 (c_h c) -> getr regs3 11 = w64 (F + 32) ->
  getr regs3 12 = w64 0 -> getr regs3 13 = w64 (c_now c) ->
  getr regs3 19 = w64 (c_out c) ->
  getr regs3 21 = w64 (c_h c + 384) -> getr regs3 24 = w64 (SB + (c_h c + 384) / 8) ->
  getr regs3 23 = w64 (F + 32) -> getr regs3 25 = w64 (SB + F / 8) ->
  ho_fsh W2 mem3 F ho_shC ->
  disco_classify_c.cm_ret (c_FB c) (ho_L c) (ho_U c) (ho_Lk c) = 0 ->
  hunt_c.hunt_ok (ho_Hcls c) ->
  garr8 SEGS (mrestrict (w_H W2) mem3) (F + 32)
    (map (fun b : byte => bv_unsigned b) (disco_classify_c.sight (c_FB c) (ho_L c))) ->
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem3) (c_out c)
     (map (fun b : byte => bv_unsigned b) (c_O c))) ->
  SRr SEGS W2 (mkCfg (mkst (fx := c_fq c) regs3 (Z_to_bv 64 (BASE + AF_reac_disco_table_observe)) mem3 (seg_rom SEGS)) md3)
    (ho_post B c).
Proof.
intros HF c fpos ly2 S2 W2 mem3 md3 k2 regs3 sp1 F HB Hra H10 H11 H12 H13 H19 H21 H24 H23 H25 HFSH HCM HHOK HGS HGO.
pose proof HB as (HPRE & HMID & HSP1 & HFeq & HRM & HSV).
pose proof HPRE as ((mdc & HJ0) & HROD & HRET & HRA4 & HGP & HTP & HAL16 & HWIN & HSPLE & HDEP & HLEN & HNOW & HOUTR &
  HH0 & HH8 & HHB & HHBLO & HHBHI & HAWR & HHOK0 & HFB50 & HGH & HFQ & HOUT & HKM & HKT & HCH).
destruct HMID as (HJ2 & Hfrs2 & HFA2 & Hperm2 & HK2 & HG2 & HFL2 & HL2 & Hkk2).
pose proof HSP1 as (HSPa & HSPb & HSPc).
destruct HRM as (R2 & R3 & R4 & R8 & R9 & R18 & R22 & R26 & R27).
pose proof HJ2 as (HAR2 & HLY2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8) & _).
pose proof HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBok.
pose proof HHOK0 as (HLH & (TT1 & TT2 & TT3 & TT4) & _ & _).
assert (ERH : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
assert (ERT : REAC_DISCO_TABLE_OBSERVE_STK = 8288) by reflexivity.
assert (Hspc : spZ regs3 = sp1) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (Hfb : fs_frame_bytes 1 = 128) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem3 md3 1 fpos HAR2 Hin1) as (Hf4096 & Hfceil & Hfapp).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem3 md3 1 fpos HAR2 Hin1) as (Hf32 & _ & Hfpres & _).
rewrite HFA2, <- HFeq in Hf4096, Hfceil, Hfapp, Hf32, Hfpres.
rewrite Hfb in Hfceil, Hfapp, Hfpres.
assert (Hhb2 : In (c_hb c, c_hn c) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm2)); exact HHB).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem3 md3 (c_hb c) (c_hn c) HAR2 Hhb2) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem3 md3 (c_hb c) (c_hn c) 1 fpos HAR2 Hhb2 Hin1) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite HFA2, <- HFeq, Hfb in Hsep.
assert (HL400 : length (disco_table_c.sub (c_H c) 0 400) = 400%nat)
  by (apply HuntObsLib.len_sub; lia).
unfold ho_H3 in HG2. rewrite map_app in HG2.
pose proof (ec_garr8_l _ _ _ _ HG2) as HGT0.
pose proof (ec_garr8_r _ _ _ _ HG2) as HGR0. clear HG2.
rewrite length_map, HL400 in HGR0.
set (X8 := if disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400) =? 0
   then Mem.le8 (Z_to_bv 64 (c_now c)) else disco_table_c.sub (c_H c) 424 8) in *.
set (Rest := disco_table_c.sub (c_H c) 412 12 ++ X8 ++ skipn 432 (c_H c)) in *.
assert (L12 : length (disco_table_c.sub (c_H c) 412 12) = 12%nat) by (apply HuntObsLib.len_sub; lia).
assert (HLX : length X8 = 8%nat).
{ unfold X8. destruct (disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400) =? 0);
  [apply Mem.length_le8 | apply HuntObsLib.len_sub; lia]. }
assert (HLRest : length Rest = 68%nat).
{ unfold Rest. rewrite !length_app, HLX, length_skipn, HLH, L12. lia. }
assert (HLcls : length (ho_Hcls c) = 480%nat) by exact (proj1 HHOK).
assert (HLLk : length (ho_Lk' c) = 12%nat).
{ unfold ho_Hcls in HLcls. rewrite !length_app, HL400, length_skipn, HLH in HLcls. lia. }
assert (HLOK : disco_classify_c.lock_ok (ho_Lk' c)).
{ pose proof HHOK as (_ & _ & HLK & _). unfold ho_Hcls in HLK.
  rewrite (ec_skipn_app _ _ 400 HL400), (ec_firstn_app _ _ 12 HLLk) in HLK. exact HLK. }
pose proof (HuntObsFacts.sight_len _ (ho_L c) HFB50) as HSL.
pose proof (HuntObsFacts.sight_ok _ (ho_L c) HFB50) as HSOK.
assert (HRA0 : range_addressable (aview SEGS (w_H W2) mem3) SHADOW_OFF (F + 32) 24).
{ intros x Hx. exists 0. split; [|left; reflexivity].
  assert (Hi : 4 <= x / 8 - F / 8 <= 6) by lia.
  replace (shadow_of_addr SHADOW_OFF x) with (SB + F / 8 + (x / 8 - F / 8))
    by (unfold shadow_of_addr, SB, SHADOW_OFF; lia).
  rewrite (HFSH (x / 8 - F / 8) ltac:(lia)).
  assert (Hc : x / 8 - F / 8 = 4 \/ x / 8 - F / 8 = 5 \/ x / 8 - F / 8 = 6) by lia.
  destruct Hc as [E | [E | E]]; rewrite E; reflexivity. }
eapply SRr_bind.
{ eapply (TOBS (c_fq c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 mem3 md3 k2 regs3 (c_h c) (F + 32) 0 (c_now c)
    (disco_table_c.sub (c_H c) 0 400) (disco_classify_c.sight (c_FB c) (ho_L c))).
  - exact HJ2.
  - eapply ho_rod_kept; [exact HROD | exact K3].
  - rewrite Hra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Hra, unsigned_lit_small by lia. lia.
  - exact R3.
  - exact R4.
  - exact H10.
  - exact H11.
  - exact H12.
  - exact H13.
  - lia.
  - exact HNOW.
  - rewrite Hspc. lia.
  - rewrite Hspc. lia.
  - rewrite Hspc. lia.
  - exact HH0.
  - exact HH8.
  - lia.
  - eapply (amem_range_of_block SEGS B LAWS ly2 S2 W2 _ _ (c_hb c) (c_hn c)); [exact HAR2 | exact Hhb2 | lia | lia].
  - right. rewrite Hspc. lia.
  - intros a Ha. split.
    + eapply ho_awr_tr; [exact Hperm2 | exact HFA2 |]. apply ho_awr_own. apply HAWR. lia.
    + exact (proj1 (Hbpres a ltac:(lia))).
  - eapply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 _ _ (c_hb c) (c_hn c)); [exact HAR2 | exact Hhb2 | lia | lia].
  - eapply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 _ _ (c_hb c) (c_hn c));
      [exact HAR2 | exact Hhb2 | lia | lia | lia].
  - exact HGT0.
  - exact HL400.
  - lia.
  - lia.
  - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia.
  - lia.
  - intros a Ha. exact (proj1 (Hfpres a ltac:(lia))).
  - exact HRA0.
  - right. rewrite Hspc. lia.
  - eapply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 mem3 md3 1 fpos);
      [exact HAR2 | exact Hin1 | rewrite HFA2, <- HFeq; lia | rewrite HFA2, <- HFeq, Hfb; lia | lia].
  - exact HGS.
  - exact HSL.
  - left. exists 1, fpos. split; [exact Hin1|]. rewrite HFA2, <- HFeq, Hfb. lia.
  - lia.
  - exact TT1.
  - exact TT2.
  - exact TT3.
  - exact (proj1 HSOK).
  - exact (proj2 HSOK). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs4 & mem4 & md4 & T' & ret & Hc3 & HJ3 & HP3 & Hr10 & Hfrs3 & Hperm3 &
  HK3 & HGT & HLT & HGS3 & HOM & T1' & T2' & T3' & T4i).
rewrite Hra in Hc3. subst c3.
pose proof HJ3 as (_ & HLY3 & _).
destruct HLY2 as (_ & _ & _ & _ & _ & HLF2 & _).
destruct HLY3 as (_ & _ & _ & _ & _ & HLF3 & _).
assert (HFA3 : forall cid p, frame_addr ly3 cid p = frame_addr (c_lyc c) cid p).
{ intros cid p. rewrite <- (HFA2 cid p). apply ec_frame_eq. lia. }
assert (Hfrs3' : frames S3 = (1, fpos) :: frames (c_Sc c)) by (rewrite Hfrs3; exact Hfrs2).
assert (Hperm3' : Permutation (ablocks B ly3 S3) (ablocks B (c_lyc c) (c_Sc c)))
  by (eapply Permutation_trans; [exact Hperm3 | exact Hperm2]).
pose proof HK3 as (KT1 & KT2 & KT3 & KT4 & KT5 & KT6).
rewrite Hspc in KT1, KT5, KT6.
assert (HKC : treac_hunt_observe_kept B (c_lyc c) (c_Sc c) (c_W c) (c_memc c) W3 mem4
  (spZ (c_regs c)) (c_h c) (c_out c)).
{ apply (ec_kept (c_lyc c) (c_Sc c) (c_W c) (c_memc c) ly2 S2 W2 mem3 W3 mem4 (spZ (c_regs c)) (spZ regs3)
    (c_h c) (c_out c) HK2 HK3 Hperm2);
  [intros cid pos Hin; rewrite Hfrs2; right; exact Hin | exact HFA2 | lia | lia | lia | lia]. }
assert (HG3 : garr8 SEGS (mrestrict (w_H W3) mem4) (c_h c)
  (map (fun b : byte => bv_unsigned b) (T' ++ ho_Lk' c ++ Rest))).
{ rewrite map_app. apply ec_garr8_app; [exact HGT|].
  rewrite length_map, HLT.
  eapply ho_garr_kept; [|exact HGR0].
  intros i Hi. rewrite length_map, length_app, HLLk, HLRest in Hi.
  replace i with (c_hb c + (i - c_hb c)) by lia.
  apply (KT2 (c_hb c) (c_hn c) (i - c_hb c)); [exact Hhb2 | lia | lia]. }
assert (HOK2 : hunt_c.hunt_ok (T' ++ ho_Lk' c ++ Rest)).
{ apply (ec_hok (ho_Hcls c) T' (ho_Lk' c) Rest HLcls HHOK HLT); [| exact HLLk | exact HLOK | exact HLRest |].
  - split; [exact T1'|]. split; [exact T2'|]. split; [exact T3'|]. exact (T4i TT4).
  - unfold Rest, ho_Hcls. rewrite !HuntObsLib.sub_app_r by lia.
    rewrite !HuntObsLib.sub_skipn by lia. f_equal. lia. }
assert (HFSH3 : ho_fsh W3 mem4 F ho_shC).
{ intros i Hi. rewrite <- (HFSH i Hi). apply (KT4 1 fpos).
  - exact Hin1.
  - right. unfold in_zr. cbn [fst snd]. rewrite HFA2, <- HFeq, Hfb. unfold shadow_addr, SB, SHADOW_OFF. lia.
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia. }
assert (HSV3 : ho_saved c W3 mem4).
{ intros j Hj. apply (ec_val_tr W2 mem3); [exact (HSV j Hj)|].
  intros x Hx. apply KT1; lia. }
assert (PR : forall q : Z, acallee_saved q -> getr regs4 (Z_to_bv 5 q) = getr regs3 (Z_to_bv 5 q)) by exact HP3.
assert (HGO3 : c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W3) mem4) (c_out c)
  (map (fun b : byte => bv_unsigned b) (c_O c))).
{ intros Hout. destruct (HOUT Hout) as ((_ & _ & _ & _ & _ & _ & _ & _ & HOL & _ & HFB) & Hoh & _).
  eapply ho_garr_kept; [|exact (HGO Hout)].
  intros i Hi. rewrite length_map, HOL in Hi.
  destruct HFB as [(cid & pos & Hin & Hlo & Hhi) | (b & m & Hin & Hlo & Hhi)].
  - apply (KT4 cid pos i).
    + rewrite Hfrs2. right. exact Hin.
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFA2. lia.
    + lia.
  - replace i with (b + (i - b)) by lia.
    apply (KT2 b m (i - b)); [apply (Permutation_in _ (Permutation_sym Hperm2)); exact Hin | lia | lia]. }
assert (HFL3 : rdword (aview SEGS (w_H W3) mem4) (frame_addr (c_lyc c) 1 fpos + 120) =
  Some (flag_addr (c_lyc c) 1 fpos)).
{ rewrite <- HFL2. apply rdword_ext. intros kk Hkk. apply (KT4 1 fpos).
  - exact Hin1.
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFA2, Hfb. lia.
  - lia. }
assert (HB3 : ho_base B c fpos ly3 S3 W3 mem4 md4 k2 (T' ++ ho_Lk' c ++ Rest) regs4 sp1 F).
{ unfold ho_base. split; [exact HPRE|]. split.
  { unfold ho_mid. split; [exact HJ3|]. split; [exact Hfrs3'|]. split; [exact HFA3|]. split; [exact Hperm3'|].
    split; [exact HKC|]. split; [exact HG3|]. split; [exact HFL3|].
    split; [rewrite !length_app, HLT, HLLk, HLRest, HLH; reflexivity | exact Hkk2]. }
  split; [exact HSP1|]. split; [exact HFeq|]. split; [|exact HSV3].
  unfold ho_regs_mid.
  split; [etransitivity; [exact (PR 2 ltac:(unfold acallee_saved; lia)) | exact R2]|].
  split; [etransitivity; [exact (PR 3 ltac:(unfold acallee_saved; lia)) | exact R3]|].
  split; [etransitivity; [exact (PR 4 ltac:(unfold acallee_saved; lia)) | exact R4]|].
  split; [etransitivity; [exact (PR 8 ltac:(unfold acallee_saved; lia)) | exact R8]|].
  split; [etransitivity; [exact (PR 9 ltac:(unfold acallee_saved; lia)) | exact R9]|].
  split; [etransitivity; [exact (PR 18 ltac:(unfold acallee_saved; lia)) | exact R18]|].
  split; [etransitivity; [exact (PR 22 ltac:(unfold acallee_saved; lia)) | exact R22]|].
  split; [etransitivity; [exact (PR 26 ltac:(unfold acallee_saved; lia)) | exact R26]|].
  etransitivity; [exact (PR 27 ltac:(unfold acallee_saved; lia)) | exact R27]. }
eapply (HF c fpos ly3 S3 W3 mem4 md4 k2 regs4 sp1 F (T' ++ ho_Lk' c ++ Rest) T'
  (disco_classify_c.sight (c_FB c) (ho_L c)) ret).
- exact HB3.
- exact Hr10.
- pose proof (HuntObsFacts.obs_c01 _ _ _ _ _ _ HOM). lia.
- etransitivity; [exact (PR 19 ltac:(unfold acallee_saved; lia)) | exact H19].
- etransitivity; [exact (PR 21 ltac:(unfold acallee_saved; lia)) | exact H21].
- etransitivity; [exact (PR 24 ltac:(unfold acallee_saved; lia)) | exact H24].
- etransitivity; [exact (PR 23 ltac:(unfold acallee_saved; lia)) | exact H23].
- etransitivity; [exact (PR 25 ltac:(unfold acallee_saved; lia)) | exact H25].
- exact HFSH3.
- exact HOK2.
- rewrite (ec_skipn_app T' _ 400 HLT). reflexivity.
- exact HLT.
- exact HGS3.
- exact HSL.
- exact HOM.
- exact HCM.
- reflexivity.
- exact (ec_skipn_app T' _ 400 HLT).
- exact HGO3.
Qed.

Lemma ho_skip412 : forall (H : list byte),
  skipn 412 H = disco_table_c.sub H 412 12 ++ disco_table_c.sub H 424 8 ++ skipn 432 H.
Proof.
intros H. unfold disco_table_c.sub. change (Z.to_nat 412) with 412%nat. change (Z.to_nat 424) with 424%nat.
rewrite <- (firstn_skipn 12 (skipn 412 H)) at 1. rewrite skipn_skipn. f_equal.
rewrite <- (firstn_skipn 8 (skipn (12 + 412) H)) at 1. rewrite skipn_skipn. reflexivity.
Qed.

Lemma ho_H3_eq : forall c, disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400) = 0 ->
  ho_H3 c = (disco_table_c.sub (c_H c) 0 400 ++ ho_Lk' c ++ disco_table_c.sub (c_H c) 412 12) ++
    Mem.le8 (Z_to_bv 64 (c_now c)) ++ skipn 432 (c_H c) /\
  ho_Hcls c = (disco_table_c.sub (c_H c) 0 400 ++ ho_Lk' c ++ disco_table_c.sub (c_H c) 412 12) ++
    disco_table_c.sub (c_H c) 424 8 ++ skipn 432 (c_H c).
Proof.
intros c Hn. unfold ho_H3, ho_Hcls. rewrite (proj2 (Z.eqb_eq _ 0) Hn), (ho_skip412 (c_H c)), <- !app_assoc.
split; reflexivity.
Qed.

Lemma ho_garr_splice : forall (Wa Wb : world SEGS) ma mb a (P X Y Q : list Z),
  garr8 SEGS (mrestrict (w_H Wa) ma) a (P ++ X ++ Q) -> length X = length Y ->
  (forall i, a <= i < a + Z.of_nat (length P + length X + length Q) ->
     ~ (a + Z.of_nat (length P) <= i < a + Z.of_nat (length P) + Z.of_nat (length X)) ->
     aview SEGS (w_H Wb) mb i = aview SEGS (w_H Wa) ma i) ->
  garr8 SEGS (mrestrict (w_H Wb) mb) (a + Z.of_nat (length P)) Y ->
  garr8 SEGS (mrestrict (w_H Wb) mb) a (P ++ Y ++ Q).
Proof.
intros Wa Wb ma mb a P X Y Q HG HL HK HY.
apply garr8_app in HG as [HP HXQ]. apply garr8_app in HXQ as [HX HQ].
apply garr8_app. split.
- apply (ho_garr_kept Wa Wb ma mb a P); [|exact HP]. intros i Hi. apply HK; lia.
- apply garr8_app. split; [exact HY|].
  rewrite <- HL. apply (ho_garr_kept Wa Wb ma mb _ Q); [|exact HQ]. intros i Hi. apply HK; lia.
Qed.

Lemma ec_splice8 : forall (Wa Wb : world SEGS) ma mb a (P X Y Q : list byte),
  garr8 SEGS (mrestrict (w_H Wa) ma) a (map (fun b : byte => bv_unsigned b) (P ++ X ++ Q)) ->
  length X = length Y ->
  (forall i, a <= i < a + Z.of_nat (length P + length X + length Q) ->
     ~ (a + Z.of_nat (length P) <= i < a + Z.of_nat (length P) + Z.of_nat (length X)) ->
     aview SEGS (w_H Wb) mb i = aview SEGS (w_H Wa) ma i) ->
  garr8 SEGS (mrestrict (w_H Wb) mb) (a + Z.of_nat (length P)) (map (fun b : byte => bv_unsigned b) Y) ->
  garr8 SEGS (mrestrict (w_H Wb) mb) a (map (fun b : byte => bv_unsigned b) (P ++ Y ++ Q)).
Proof.
intros Wa Wb ma mb a P X Y Q HG HL HK HY.
rewrite !map_app in HG |- *.
apply (ho_garr_splice Wa Wb ma mb a _ _ _ _ HG).
- rewrite !length_map. exact HL.
- intros i Hi Hn. rewrite !length_map in Hi. rewrite !length_map in Hn. exact (HK i Hi Hn).
- rewrite length_map. exact HY.
Qed.

Lemma ho_lb1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small x 256) by lia. rewrite (Z.mod_small x 256) by lia. reflexivity.
Qed.

Lemma ho_le8_nth : forall v k, 0 <= v < 2 ^ 64 -> (k < 8)%nat ->
  YO0f.le_byte v 8 k = nth k (map (fun b : byte => bv_unsigned b) (Mem.le8 (Z_to_bv 64 v))) 0.
Proof.
intros v k Hv Hk. unfold Mem.le8, word_to_le_bytes. rewrite unsigned_lit_small by lia.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by (cbn [Z.of_nat Z.mul]; lia).
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try (exfalso; lia);
cbn [Z_to_le_bytes map nth Z.of_nat Z.mul];
rewrite ?Z.shiftr_0_r, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; reflexivity.
Qed.

Lemma ho_garr8_le8 : forall m a v, 0 <= v < 2 ^ 64 -> val_mem SEGS m a 8 v ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) (Mem.le8 (Z_to_bv 64 v))).
Proof.
intros m a v Hv HV j Hj. rewrite length_map, Mem.length_le8 in Hj.
rewrite <- (ho_le8_nth v j Hv Hj).
assert (Hr : 0 <= YO0f.le_byte v 8 j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (HV j Hj). rewrite (ho_lb1 _ Hr). reflexivity.
Qed.
Lemma ec_apresent_grows : forall (Hh : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict Hh m) (mrestrict Hh m') -> apresent Hh m a -> apresent Hh m' a.
Proof.
intros Hh m m' a HG [Hf [b Hb]]. split; [exact Hf|].
assert (H1 : mrestrict Hh m (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hf, Hb; discriminate).
specialize (HG _ H1). unfold mrestrict in HG. rewrite Hf in HG.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply HG; reflexivity].
Qed.

Lemma ho_E_store : forall (c : hoC) fpos ly2 S2 (W2 : world SEGS) mem2 md2 k2 mem3 md3 regs3 sp1 F,
  ho_pre B c ->
  ho_mid B c fpos ly2 S2 W2 mem2 md2 k2 (ho_Hcls c) ->
  ho_sp1 c sp1 -> F = frame_addr (c_lyc c) 1 fpos ->
  ho_regs_mid B c regs3 sp1 F -> ho_saved c W2 mem2 ->
  hunt_c.hunt_ok (ho_Hcls c) ->
  disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400) = 0 ->
  ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 mem3 md3 k2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_h c + 424 <= a < c_h c + 432) ->
     aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) mem3) ->
  val_mem SEGS (mrestrict (w_H W2) mem3) (c_h c + 424) 8 (c_now c) ->
  ho_fsh W2 mem2 F ho_shC ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (F + 32)
    (map (fun b : byte => bv_unsigned b) (disco_classify_c.sight (c_FB c) (ho_L c))) ->
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c)
     (map (fun b : byte => bv_unsigned b) (c_O c))) ->
  ho_base B c fpos ly2 S2 W2 mem3 md3 k2 (ho_H3 c) regs3 sp1 F /\
  ho_fsh W2 mem3 F ho_shC /\
  garr8 SEGS (mrestrict (w_H W2) mem3) (F + 32)
    (map (fun b : byte => bv_unsigned b) (disco_classify_c.sight (c_FB c) (ho_L c))) /\
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem3) (c_out c)
     (map (fun b : byte => bv_unsigned b) (c_O c))).
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 mem3 md3 regs3 sp1 F HPRE HMID HSP1 HFeq HRM HSV HHOK Hn0 HJ3 HA HGR HV
  HFSH HGS HGO.
pose proof HPRE as ((mdc & HJ0) & HROD & HRET & HRA4 & HGP & HTP & HAL16 & HWIN & HSPLE & HDEP & HLEN & HNOW & HOUTR &
  HH0 & HH8 & HHB & HHBLO & HHBHI & HAWR & HHOK0 & HFB50 & HGH & HFQ & HOUT & HKM & HKT & HCH).
pose proof HMID as (HJ2 & Hfrs2 & HFA2 & Hperm2 & HK2 & HG2 & HFL2 & HL2 & Hkk2).
pose proof HJ0 as (HAR0 & _).
pose proof HJ3 as (HAR3 & HLY3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HHOK0 as (HLH & _).
assert (ERH : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_hb c) (c_hn c) HAR0 HHB) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (Hfb : fs_frame_bytes 1 = 128) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem3 md3 1 fpos HAR3 Hin1) as (Hf4096 & Hfceil & _).
rewrite HFA2, <- HFeq in Hf4096, Hfceil.
rewrite Hfb in Hfceil.
assert (Hhb2 : In (c_hb c, c_hn c) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm2)); exact HHB).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem3 md3 (c_hb c) (c_hn c) 1 fpos HAR3 Hhb2 Hin1) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite HFA2, <- HFeq, Hfb in Hsep.
assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ (c_h c <= a < c_h c + 480) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a)
  by (intros a Ha Hn; apply HA; [exact Ha | lia]).
assert (HKC : treac_hunt_observe_kept B (c_lyc c) (c_Sc c) (c_W c) (c_memc c) W2 mem3
  (spZ (c_regs c)) (c_h c) (c_out c)).
{ destruct HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (Ht : forall a, ~ tho_wr (c_h c) (c_out c) a -> ~ (c_h c <= a < c_h c + 480))
    by (intros a Hn Ha; apply Hn; unfold tho_wr; left; exact Ha).
  split.
  { intros a Ha Hns Hnw. rewrite (HW a ltac:(lia) (Ht a Hnw)). apply K1; assumption. }
  split.
  { intros b m i Hin Hi Hnw.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hin) as (_ & Hb4 & Hbc & _).
    rewrite (HW (b + i) ltac:(lia) (Ht _ Hnw)). apply (K2 b m i); assumption. }
  split.
  { intros a H1 H2 H3. pose proof (pa_segs_low a H1) as Hlow.
    assert (Hnb : ~ (c_h c + 424 <= a < c_h c + 432)).
    { intros Hw. exact (blk_img SEGS B LAWS _ _ _ _ _ (c_hb c) (c_hn c) a HAR0 HHB ltac:(lia) H1). }
    rewrite (HA a ltac:(unfold kLowMemEnd in Hlow; lia) Hnb). apply K3; assumption. }
  split.
  { intros cid pos a Hin Hr Hnw.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR0 Hin) as (Hg4 & Hgc & _).
    assert (Ha : 0 <= a < 2 ^ 64).
    { unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr. lia. }
    rewrite (HW a Ha (Ht a Hnw)). apply (K4 cid pos a); assumption. }
  split.
  { intros a Ha Hns Hp. exact (ec_apresent_grows _ _ _ a HGR (K5 a Ha Hns Hp)). }
  intros a Ha. exact (ec_apresent_grows _ _ _ a HGR (K6 a Ha)). }
assert (HL400 : length (disco_table_c.sub (c_H c) 0 400) = 400%nat) by (apply HuntObsLib.len_sub; lia).
assert (L12 : length (disco_table_c.sub (c_H c) 412 12) = 12%nat) by (apply HuntObsLib.len_sub; lia).
assert (L8 : length (disco_table_c.sub (c_H c) 424 8) = 8%nat) by (apply HuntObsLib.len_sub; lia).
assert (HLcls : length (ho_Hcls c) = 480%nat) by exact (proj1 HHOK).
assert (HLLk : length (ho_Lk' c) = 12%nat).
{ unfold ho_Hcls in HLcls. rewrite !length_app, HL400, length_skipn, HLH in HLcls. lia. }
destruct (ho_H3_eq c Hn0) as (E3 & Ecls).
assert (HLP : length (disco_table_c.sub (c_H c) 0 400 ++ ho_Lk' c ++ disco_table_c.sub (c_H c) 412 12) = 424%nat)
  by (rewrite !length_app, HL400, HLLk, L12; reflexivity).
assert (HG3 : garr8 SEGS (mrestrict (w_H W2) mem3) (c_h c) (map (fun b : byte => bv_unsigned b) (ho_H3 c))).
{ rewrite E3. rewrite Ecls in HG2.
  apply (ec_splice8 W2 W2 mem2 mem3 (c_h c) _ (disco_table_c.sub (c_H c) 424 8) _ _ HG2).
  - rewrite L8, Mem.length_le8. reflexivity.
  - intros i Hi Hn. rewrite HLP, L8, length_skipn, HLH in Hi. rewrite HLP, L8 in Hn. apply HA; lia.
  - rewrite HLP. apply ho_garr8_le8; [exact HNOW|].
    replace (c_h c + Z.of_nat 424) with (c_h c + 424) by lia. exact HV. }
assert (HFL3 : rdword (aview SEGS (w_H W2) mem3) (frame_addr (c_lyc c) 1 fpos + 120) =
  Some (flag_addr (c_lyc c) 1 fpos)).
{ rewrite <- HFL2. apply rdword_ext. intros kk Hkk. apply HA; lia. }
assert (HSV3 : ho_saved c W2 mem3).
{ intros j Hj. apply (ec_val_tr W2 mem2); [exact (HSV j Hj)|].
  intros x Hx. apply HA; lia. }
assert (HFSH3 : ho_fsh W2 mem3 F ho_shC).
{ intros i Hi. rewrite <- (HFSH i Hi). apply HA; unfold SB; lia. }
assert (HGS3 : garr8 SEGS (mrestrict (w_H W2) mem3) (F + 32)
  (map (fun b : byte => bv_unsigned b) (disco_classify_c.sight (c_FB c) (ho_L c)))).
{ eapply ho_garr_kept; [|exact HGS].
  intros i Hi. rewrite length_map, (HuntObsFacts.sight_len _ _ HFB50) in Hi. apply HA; lia. }
assert (HGO3 : c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem3) (c_out c)
  (map (fun b : byte => bv_unsigned b) (c_O c))).
{ intros Hout. destruct (HOUT Hout) as ((_ & Ho63 & _ & _ & _ & _ & _ & _ & HOL & _ & _) & Hoh & _).
  eapply ho_garr_kept; [|exact (HGO Hout)].
  intros i Hi. rewrite length_map, HOL in Hi. apply HA; lia. }
split.
{ unfold ho_base. split; [exact HPRE|]. split.
  { unfold ho_mid. split; [exact HJ3|]. split; [exact Hfrs2|]. split; [exact HFA2|]. split; [exact Hperm2|].
    split; [exact HKC|]. split; [exact HG3|]. split; [exact HFL3|].
    split; [rewrite E3, !length_app, HL400, HLLk, L12, Mem.length_le8, length_skipn, HLH; reflexivity | exact Hkk2]. }
  split; [exact HSP1|]. split; [exact HFeq|]. split; [exact HRM | exact HSV3]. }
split; [exact HFSH3|]. split; [exact HGS3 | exact HGO3].
Qed.

Lemma ho_H3_ne : forall c, disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400) <> 0 -> ho_H3 c = ho_Hcls c.
Proof.
intros c Hn. unfold ho_H3, ho_Hcls. rewrite (proj2 (Z.eqb_neq _ 0) Hn), (ho_skip412 (c_H c)). reflexivity.
Qed.

Definition ho_E_facts : facts :=
  mkFacts [ (22%nat, mkAF 4096 140737479966720 3); (27%nat, mkAF SB SB 0); (32%nat, mkAF 0 8 0) ] [] [].
Definition ho_E_rg (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 22%nat) 0 480 wlo whi [YP09.mkChunk 384 (CVal 4 (SOff 32 0))].
Definition ho_E_SH : list shent := [ mkSHE 22 0 480 ].

Lemma ho_seg_E : ho_seg_F_stmt B -> ho_seg_E_stmt B.
Proof.
intros HF. unfold ho_seg_E_stmt.
intros c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F HB H19 H20 H23 H25 Hfsh Hret0 HOKc HGs Hout.
pose proof HB as (Hpre & Hmid & Hsp1 & HFa & Hregs & Hsav).
pose proof Hmid as (HJ & Hfrm & Hfad & Hperm & HK & HGH & Hfl & HLH).
pose proof Hpre as (HJ0 & HROD & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin & Hsp & Hdepth & Rlen & Rnow & Rout
  & Hh0 & Hh8 & Hin & Hhb & Hhe & Hwr & HOK & HFBl & HGH0 & Hfr50 & Hout0 & HKM & HKT & Hch).
pose proof Hregs as (G2 & G3 & G4 & G8 & G9 & G18 & G22 & G26 & G27).
pose proof (proj1 HJ) as HAR2.
assert (Hin2 : In (c_hb c, c_hn c) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hin2) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ho_count _ _ _ HOKc HGH) as [Hnr HVn].
assert (Hsub0 : disco_table_c.sub (ho_Hcls c) 0 400 = disco_table_c.sub (c_H c) 0 400).
{ unfold ho_Hcls. rewrite HuntObsLib.sub_app_l; [apply HuntObsLib.sub_whole|lia|].
  - apply HuntObsLib.len_sub; [lia|]. destruct HOK as (HL480 & _). rewrite HL480. cbn. lia.
  - rewrite (HuntObsLib.len_sub (c_H c) 0 400) by (try lia; destruct HOK as (HL480 & _); rewrite HL480; cbn; lia). cbn. lia. }
rewrite Hsub0 in Hnr, HVn.
set (n := disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400)) in *.
pose proof (paj_run (fx := c_fq c) B LAWS) as RUN.
pose proof (paj_branch (fx := c_fq c) (PI := PI)) as BR.
remember (Eimg (Ereg regs2 [Z_to_bv 64 n])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs2 r)
by (intros k r Hk; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E22 : ew E 22 = Z_to_bv 64 (c_h c)) by (rewrite (EE 22%nat 22%bv eq_refl); exact G22).
assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EE 27%nat 27%bv eq_refl); exact G27).
assert (E32 : ew E 32 = Z_to_bv 64 n) by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (Hhr : 0 < c_h c /\ c_h c + 480 <= 140737479966720 + 480).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. lia. }
destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
- assert (HS : st_ok_pi (fx := c_fq c) SEGS VAL E (mkSS 0x7210 sr_atoms [ho_E_rg 424 432] None ho_E_facts)
    (restrict (w_H W2) (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + 0x7210)) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ho_E_rg.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E22, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split.
      + intros o Ho. apply (apresent_writable SEGS). apply (fun Hq => proj1 (Hbpres (c_h c + o) Hq)). lia.
      + constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (c_h c) 384 4 (SOff 32 0) n);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        change (N.to_nat 4) with 4%nat. exact HVn.
    - cbn. tauto.
    - unfold ho_E_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
      unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E22, E27, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat split; try lia; exact Hh8. }
  assert (SHOK : sh_ok SEGS (SOff 27 0) ho_E_SH E (mrestrict (w_H W2) mem2)).
  { unfold sh_ok, ho_E_SH. apply Forall_cons; [|apply Forall_nil].
    assert (HU : U E (SOff 22 0) = c_h c) by (shent_U_norm; reflexivity).
    assert (HUB : U E (SOff 27 0) = SHADOW_OFF) by (shent_U_norm; unfold SB, SHADOW_OFF; reflexivity).
    unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU, HUB. split.
    - replace (c_h c + 0) with (c_h c) by lia. replace (480 - 0) with 480 by lia.
      apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) (c_h c) 480 HAR2 Hin2); lia.
    - intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. lia. }
  unfold ho_cfg.
  paj_run_tok RUN HS HJ SHOK HOspan;
  [ eapply awr_ok_cons_gen with (n := 22%nat) (b := c_h c);
    [reflexivity | cbn [ew ewset Nat.eqb]; rewrite E22; apply unsigned_lit_small; lia
    | cbn [ho_E_rg YP09.r_wlo YP09.r_whi]; intros a Ha;
      eapply ho_awr_tr; [exact Hperm | exact Hfad | apply ho_awr_own; apply Hwr; lia]
    | apply awr_ok_nil] |].
  lazymatch goal with HFm : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem ?m1)) |- _ =>
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_h c + 424 <= a < c_h c + 432) ->
      aview SEGS (w_H W2) (ms_mem m1) a = aview SEGS (w_H W2) mem2 a);
    [ intros a Ha Hx; apply (ho_aview_frame E _ W2 mem2 (ms_mem m1) a HFm Ha);
      intros (r & Hinr & Hr); cbn [ss_mem In] in Hinr; destruct Hinr as [<- | []];
      cbn [ho_E_rg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite E22, unsigned_lit_small in Hr by lia; lia |] end.
  lazymatch goal with HGm : mem_grows (mrestrict _ mem2) (mrestrict _ (ms_mem ?m1)) |- _ =>
    assert (GM1 : forall x, mrestrict (w_H W2) mem2 x <> None ->
      mrestrict (w_H W2) (ms_mem m1) x <> None) by exact HGm end.
  clear_frames.
  psrr_branch_tok RUN BR HS SHOK HOspan.
  + exfalso. cbn [branch_taken sv_denot] in Hc.
    rewrite E32, unsigned_lit_small, Z.add_0_r, bv_eqb_unsigned, !unsigned_lit_small, Hn0 in Hc by lia.
    cbn in Hc. discriminate Hc.
  + paj_run_tok RUN HS HJ SHOK HOspan;
    [ eapply awr_ok_cons_gen with (n := 22%nat) (b := c_h c);
      [reflexivity | cbn [ew ewset Nat.eqb]; rewrite E22; apply unsigned_lit_small; lia
      | cbn [ho_E_rg YP09.r_wlo YP09.r_whi]; intros a Ha;
        eapply ho_awr_tr; [exact Hperm | exact Hfad | apply ho_awr_own; apply Hwr; lia]
      | apply awr_ok_nil] |].
    lazymatch goal with HFm : frame_of _ _ (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)),
      HGm : mem_grows (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)) |- _ =>
      assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_h c + 424 <= a < c_h c + 432) ->
        aview SEGS (w_H W2) (ms_mem m1) a = aview SEGS (w_H W2) mem2 a);
      [ intros a Ha Hx; rewrite <- (K1 a Ha Hx);
        apply (ho_aview_frame E _ W2 (ms_mem m0) (ms_mem m1) a HFm Ha);
        intros (r & Hinr & Hr); cbn [ss_mem add_cond In] in Hinr; destruct Hinr as [<- | []];
        cbn [ho_E_rg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite E22, unsigned_lit_small in Hr by lia; lia
      | assert (GM2 : forall x, mrestrict (w_H W2) mem2 x <> None ->
          mrestrict (w_H W2) (ms_mem m1) x <> None)
        by (intros x Hx; apply HGm, GM1, Hx) ] end.
    pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as HR0.
    cbn [ms_mem restrict mkst] in HR0.
    assert (E20 : ew E 20 = Z_to_bv 64 (c_now c)) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
    assert (Hval : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms0)) (c_h c + 424) 8 (c_now c)).
    { change 8%nat with (N.to_nat 8). apply (field_of_region E _ 22%nat (c_h c) _ 0 480 424 432 424 8 (SOff 20 0) (c_now c) HR0).
      - rewrite E22. apply unsigned_lit_small. lia.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - cbn [Z.of_N Z.mul]. lia.
      - cbn. lia. }
    clear_frames.
    prreg HS (1%bv : bv 5) Kr1. prreg HS (10%bv : bv 5) Kr10. prreg HS (11%bv : bv 5) Kr11.
    prreg HS (12%bv : bv 5) Kr12. prreg HS (13%bv : bv 5) Kr13. prreg HS (19%bv : bv 5) Kr19.
    prreg HS (21%bv : bv 5) Kr21. prreg HS (23%bv : bv 5) Kr23.
    rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (c_h c + 384) / 8))
      (denot_shx E 22%nat 27%nat 384 (c_h c) SB E22 E27 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) Kr24'.
    prreg HS (25%bv : bv 5) Kr25. prreg HS (2%bv : bv 5) Kr2. prreg HS (3%bv : bv 5) Kr3.
    prreg HS (4%bv : bv 5) Kr4. prreg HS (8%bv : bv 5) Kr8. prreg HS (9%bv : bv 5) Kr9.
    prreg HS (18%bv : bv 5) Kr18. prreg HS (22%bv : bv 5) Kr22. prreg HS (26%bv : bv 5) Kr26.
    prreg HS (27%bv : bv 5) Kr27.
    pmkst HS. rewrite pa_sigma_reac_disco_table_observe.
    assert (Kr10' : getr (ms_regs ms0) 10 = w64 (c_h c)) by (rewrite Kr10, E22; reflexivity).
    assert (Kr11' : getr (ms_regs ms0) 11 = w64 (F + 32))
    by (rewrite Kr11, (EE 23%nat 23%bv eq_refl); exact H23).
    assert (Kr13' : getr (ms_regs ms0) 13 = w64 (c_now c))
    by (rewrite Kr13, (EE 20%nat 20%bv eq_refl); exact H20).
    assert (Kr19' : getr (ms_regs ms0) 19 = w64 (c_out c))
    by (rewrite Kr19, (EE 19%nat 19%bv eq_refl); exact H19).
    assert (Kr23' : getr (ms_regs ms0) 23 = w64 (F + 32))
    by (rewrite Kr23, (EE 23%nat 23%bv eq_refl); exact H23).
    assert (Kr25' : getr (ms_regs ms0) 25 = w64 (SB + F / 8))
    by (rewrite Kr25, (EE 25%nat 25%bv eq_refl); exact H25).
    assert (Kr21' : getr (ms_regs ms0) 21 = w64 (c_h c + 384))
    by (rewrite Kr21, E22, unsigned_lit_small by lia; reflexivity).
    assert (Hrm : ho_regs_mid B c (ms_regs ms0) sp1 F).
    { unfold ho_regs_mid.
      rewrite Kr2, (EE 2%nat 2%bv eq_refl), Kr3, (EE 3%nat 3%bv eq_refl), Kr4, (EE 4%nat 4%bv eq_refl),
        Kr8, (EE 8%nat 8%bv eq_refl), Kr9, (EE 9%nat 9%bv eq_refl), Kr18, (EE 18%nat 18%bv eq_refl),
        Kr22, E22, Kr26, (EE 26%nat 26%bv eq_refl), Kr27, E27.
      pose proof Hregs as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q22 & Q26 & Q27).
      repeat split; assumption. }
    destruct (ho_E_store c fpos ly2 S2 W2 mem2 md2 k2 (ms_mem ms0) _ (ms_regs ms0) sp1 F
      Hpre Hmid Hsp1 HFa Hrm Hsav HOKc Hn0 HJ K2 GM2 Hval Hfsh HGs Hout)
      as (HB3 & HFSH3 & HGS3 & HOUT3).
    eapply (ho_E_call HF c fpos ly2 S2 W2 (ms_mem ms0) _ k2 (ms_regs ms0) sp1 F HB3 Kr1 Kr10' Kr11' Kr12 Kr13'
      Kr19' Kr21' Kr24' Kr23' Kr25' HFSH3 Hret0 HOKc HGS3 HOUT3).
- assert (HS : st_ok_pi (fx := c_fq c) SEGS VAL E (mkSS 0x7210 sr_atoms [ho_E_rg 0 0] None ho_E_facts)
    (restrict (w_H W2) (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + 0x7210)) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ho_E_rg.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E22, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (c_h c) 384 4 (SOff 32 0) n);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      change (N.to_nat 4) with 4%nat. exact HVn.
    - cbn. tauto.
    - unfold ho_E_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
      unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E22, E27, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat split; try lia; exact Hh8. }
  assert (SHOK : sh_ok SEGS (SOff 27 0) ho_E_SH E (mrestrict (w_H W2) mem2)).
  { unfold sh_ok, ho_E_SH. apply Forall_cons; [|apply Forall_nil].
    assert (HU : U E (SOff 22 0) = c_h c) by (shent_U_norm; reflexivity).
    assert (HUB : U E (SOff 27 0) = SHADOW_OFF) by (shent_U_norm; unfold SB, SHADOW_OFF; reflexivity).
    unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU, HUB. split.
    - replace (c_h c + 0) with (c_h c) by lia. replace (480 - 0) with 480 by lia.
      apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) (c_h c) 480 HAR2 Hin2); lia.
    - intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. lia. }
  unfold ho_cfg.
  paj_run_tok RUN HS HJ SHOK HOspan; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
  lazymatch goal with HFm : frame_of _ _ mem2 (ms_mem ?m1) |- _ =>
    assert (Hm1 : ms_mem m1 = mem2)
    by (apply functional_extensionality; intros x; apply HFm; intros (r & Hr & Hx);
        cbn [ss_mem In] in Hr; destruct Hr as [<- | []]; cbn [ho_E_rg YP09.r_wlo YP09.r_whi] in Hx; lia) end.
  clear_frames.
  psrr_branch_tok RUN BR HS SHOK HOspan.
  + paj_run_tok RUN HS HJ SHOK HOspan; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
    lazymatch goal with HFm : frame_of _ _ (ms_mem ?m0) (ms_mem ?m1), Hm0 : ms_mem ?m0 = mem2 |- _ =>
      assert (Hm2 : ms_mem m1 = mem2)
      by (rewrite <- Hm0; apply functional_extensionality; intros x; apply HFm; intros (r & Hr & Hx);
          cbn [ss_mem add_cond In] in Hr; destruct Hr as [<- | []]; cbn [ho_E_rg YP09.r_wlo YP09.r_whi] in Hx; lia) end.
    clear_frames.
    prreg HS (1%bv : bv 5) Kr1. prreg HS (10%bv : bv 5) Kr10. prreg HS (11%bv : bv 5) Kr11.
    prreg HS (12%bv : bv 5) Kr12. prreg HS (13%bv : bv 5) Kr13. prreg HS (19%bv : bv 5) Kr19.
    prreg HS (21%bv : bv 5) Kr21. prreg HS (23%bv : bv 5) Kr23.
    rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (c_h c + 384) / 8))
      (denot_shx E 22%nat 27%nat 384 (c_h c) SB E22 E27 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) Kr24'.
    prreg HS (25%bv : bv 5) Kr25. prreg HS (2%bv : bv 5) Kr2. prreg HS (3%bv : bv 5) Kr3.
    prreg HS (4%bv : bv 5) Kr4. prreg HS (8%bv : bv 5) Kr8. prreg HS (9%bv : bv 5) Kr9.
    prreg HS (18%bv : bv 5) Kr18. prreg HS (22%bv : bv 5) Kr22. prreg HS (26%bv : bv 5) Kr26.
    prreg HS (27%bv : bv 5) Kr27.
    pmkst HS. rewrite pa_sigma_reac_disco_table_observe.
    assert (Kr10' : getr (ms_regs ms0) 10 = w64 (c_h c)) by (rewrite Kr10, E22; reflexivity).
    assert (Kr11' : getr (ms_regs ms0) 11 = w64 (F + 32))
    by (rewrite Kr11, (EE 23%nat 23%bv eq_refl); exact H23).
    assert (Kr13' : getr (ms_regs ms0) 13 = w64 (c_now c))
    by (rewrite Kr13, (EE 20%nat 20%bv eq_refl); exact H20).
    assert (Kr19' : getr (ms_regs ms0) 19 = w64 (c_out c))
    by (rewrite Kr19, (EE 19%nat 19%bv eq_refl); exact H19).
    assert (Kr23' : getr (ms_regs ms0) 23 = w64 (F + 32))
    by (rewrite Kr23, (EE 23%nat 23%bv eq_refl); exact H23).
    assert (Kr25' : getr (ms_regs ms0) 25 = w64 (SB + F / 8))
    by (rewrite Kr25, (EE 25%nat 25%bv eq_refl); exact H25).
    assert (Kr21' : getr (ms_regs ms0) 21 = w64 (c_h c + 384))
    by (rewrite Kr21, E22, unsigned_lit_small by lia; reflexivity).
    rewrite Hm2 in HJ |- *.
    eapply (ho_E_call HF c fpos ly2 S2 W2 mem2 _ k2 (ms_regs ms0) sp1 F).
    * rewrite (ho_H3_ne c Hn0).
      refine (conj Hpre (conj (conj HJ (conj Hfrm (conj Hfad (conj Hperm (conj HK (conj HGH (conj Hfl HLH)))))))
        (conj Hsp1 (conj HFa (conj _ Hsav))))).
      unfold ho_regs_mid.
      rewrite Kr2, (EE 2%nat 2%bv eq_refl), Kr3, (EE 3%nat 3%bv eq_refl), Kr4, (EE 4%nat 4%bv eq_refl),
        Kr8, (EE 8%nat 8%bv eq_refl), Kr9, (EE 9%nat 9%bv eq_refl), Kr18, (EE 18%nat 18%bv eq_refl),
        Kr22, E22, Kr26, (EE 26%nat 26%bv eq_refl), Kr27, E27.
      pose proof Hregs as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q22 & Q26 & Q27).
      repeat split; assumption.
    * exact Kr1.
    * exact Kr10'.
    * exact Kr11'.
    * exact Kr12.
    * exact Kr13'.
    * exact Kr19'.
    * exact Kr21'.
    * exact Kr24'.
    * exact Kr23'.
    * exact Kr25'.
    * exact Hfsh.
    * exact Hret0.
    * exact HOKc.
    * exact HGs.
    * exact Hout.
  + exfalso. apply Hn0. cbn [branch_taken sv_denot] in Hc.
    rewrite E32, unsigned_lit_small, Z.add_0_r, bv_eqb_unsigned, !unsigned_lit_small in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc. exact Hc.
Qed.

End h.
End f.
End d.
