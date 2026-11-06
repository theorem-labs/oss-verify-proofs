(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_lay_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of ctrl_lay_block on image B (fuzz_grant.asan-ubsan), ported from
   image A's closed walk lib/A/Prog/CtrlLayBlock.v (a working branch 5aae1e8a0ce), itself written with proof steps adapted
   from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, AC8k.v, AChz.v, ACa2.v and ACb8.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlLayBlock.v, with its module paths, module names and numbers changed; 805 of its 880 lines of code are new or changed and 987 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacHuntObserveSeg_A.v; 486 of its 574 lines of code are new or changed and 792 lines of the source are left out. *)
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
#[local] Notation treac_hunt_observe_post := (@ReacHuntObserveCore.treac_hunt_observe_post rc SK PI B).
#[local] Notation hoC := (@ReacHuntObserveCore.hoC rc PI).
#[local] Notation ho_post := (@ReacHuntObserveCore.ho_post rc SK PI B).
#[local] Notation ho_mid := (@ReacHuntObserveCore.ho_mid rc SK PI B).
#[local] Notation ho_fsh := (@ReacHuntObserveCore.ho_fsh rc PI).
#[local] Notation ho_saved := (@ReacHuntObserveCore.ho_saved rc PI).
#[local] Notation ho_regs_mid := (@ReacHuntObserveCore.ho_regs_mid rc PI B).
#[local] Notation ho_cfg := (@ReacHuntObserveCore.ho_cfg rc PI).
#[local] Notation ho_base := (@ReacHuntObserveCore.ho_base rc SK PI B).
#[local] Notation ho_L := (@ReacHuntObserveCore.ho_L rc PI).
#[local] Notation ho_U := (@ReacHuntObserveCore.ho_U rc PI).
#[local] Notation ho_Lk := (@ReacHuntObserveCore.ho_Lk rc PI).
#[local] Notation ho_Lk' := (@ReacHuntObserveCore.ho_Lk' rc PI).
#[local] Notation ho_Hcls := (@ReacHuntObserveCore.ho_Hcls rc PI).
#[local] Notation ho_seg_E_stmt := (@ReacHuntObserveCore.ho_seg_E_stmt rc SK PI B).
#[local] Notation ho_seg_T_stmt := (@ReacHuntObserveCore.ho_seg_T_stmt rc SK PI B).
#[local] Notation ho_setfq := (@ReacHuntObserveCore.ho_setfq rc PI).

Lemma ho_garr8_cat3 : forall m (p : Z) (X Y Z3 : list byte),
  length X = 400%nat -> length Y = 12%nat ->
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) X) ->
  garr8 SEGS m (p + 400) (map (fun b : byte => bv_unsigned b) Y) ->
  garr8 SEGS m (p + 412) (map (fun b : byte => bv_unsigned b) Z3) ->
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) (X ++ Y ++ Z3)).
Proof.
  intros m p X Y Z3 LX LY GX GY GZ. rewrite !map_app.
  apply garr8_app. split; [exact GX|]. rewrite length_map, LX.
  apply garr8_app. split; [replace (p + Z.of_nat 400) with (p + 400) by lia; exact GY|].
  rewrite length_map, LY. replace (p + Z.of_nat 400 + Z.of_nat 12) with (p + 412) by lia. exact GZ.
Qed.

Lemma ho_hunt_ok_fail : forall (Hh Lk' : list byte),
  hunt_c.hunt_ok Hh -> length Lk' = 12%nat -> disco_classify_c.lock_ok Lk' ->
  hunt_c.hunt_ok (disco_table_c.sub Hh 0 400 ++ Lk' ++ skipn 412 Hh).
Proof.
  intros Hh Lk' HOK LL LOK. pose proof HOK as (LH & TOK & _).
  apply (ho_hok_gen Hh (disco_table_c.sub Hh 0 400) Lk' (skipn 412 Hh) LH HOK).
  - apply HuntObsLib.len_sub; lia.
  - exact TOK.
  - exact LL.
  - exact LOK.
  - rewrite length_skipn. lia.
  - rewrite HuntObsLib.sub_skipn by lia. f_equal; lia.
Qed.

Lemma tho_model_fail : forall (Hh FB O : list byte) (len now out : Z) (Lk' : list byte)
    (OUT : list byte -> Prop),
  disco_classify_c.cm_ret FB (reac_frame_clean_len_c.reac_frame_clean_len_model len)
    (disco_table_c.sub Hh 412 6) (Some (disco_table_c.sub Hh 400 12)) <> 0 ->
  disco_classify_c.cm_lock FB (reac_frame_clean_len_c.reac_frame_clean_len_model len)
    (disco_table_c.sub Hh 412 6) (Some (disco_table_c.sub Hh 400 12)) = Some Lk' ->
  (out <> 0 -> OUT O) ->
  tho_model Hh FB O len now out (-1) (disco_table_c.sub Hh 0 400 ++ Lk' ++ skipn 412 Hh) OUT.
Proof.
  intros Hh FB O len now out Lk' OUT R EL HO. unfold tho_model. cbv zeta. rewrite EL. split.
  - intros _. split; [reflexivity|]. split; [reflexivity|]. exact HO.
  - intros X. contradiction.
Qed.

Lemma hoc_frame_eq : forall ly ly', ly_F ly' = ly_F ly ->
  (forall cid p, frame_addr ly' cid p = frame_addr ly cid p) /\ (forall cid p, flag_addr ly' cid p = flag_addr ly cid p).
Proof. intros ly ly' H. split; intros cid p; unfold frame_addr, flag_addr; rewrite H; reflexivity. Qed.

Lemma hoc_awr_tr : forall STK sp0 FP bl0 blc blc' ly ly' own a,
  Permutation blc' blc -> (forall cid p, frame_addr ly' cid p = frame_addr ly cid p) ->
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc' ly' own a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own a HP HF
  [H | [(Hfp & b & n & Hb & Hr) | [(b & n & Hb & Hn & Hr) | (cid & pos & Hin & Hr)]]].
- left; exact H.
- right; left. split; [exact Hfp|]. exists b, n. split; [apply (Permutation_in _ (Permutation_sym HP)); exact Hb | exact Hr].
- right; right; left. exists b, n.
  split; [apply (Permutation_in _ (Permutation_sym HP)); exact Hb | split; [exact Hn | exact Hr]].
- right; right; right. exists cid, pos. split; [exact Hin|]. rewrite HF. exact Hr.
Qed.

Lemma hoc_awr_own : forall STK sp0 FP bl0 blc ly own x a,
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly (x :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own x a [H | [H | [H | (cid & pos & Hin & Hr)]]];
[left; exact H | right; left; exact H | right; right; left; exact H |].
right; right; right. exists cid, pos. split; [right; exact Hin | exact Hr].
Qed.

Lemma hoc_rod_kept : forall (Wa Wb : world SEGS) ma mb,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wa) ma) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H Wb) mb a = aview SEGS (w_H Wa) ma a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wb) mb).
Proof.
intros Wa Wb ma mb HR HK a Hro Ho He.
assert (Hi : in_img SEGS a)
  by (destruct Hro as [(s & Hs & _ & Hr) | Hrel]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hrel)]).
rewrite (HK a Hi Ho He). exact (HR a Hro Ho He).
Qed.

Lemma hoc_val_tr : forall (W1 : world SEGS) m1 (W2 : world SEGS) m2 a (n : nat) v,
  val_mem SEGS (mrestrict (w_H W1) m1) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x) ->
  val_mem SEGS (mrestrict (w_H W2) m2) a n v.
Proof.
intros W1 m1 W2 m2 a n v HV HK k Hk. rewrite <- (HV k Hk).
apply (mbyte_of_aview SEGS). apply HK. lia.
Qed.

Lemma hoc_bytes_of : forall l : list Z, Forall (fun x => 0 <= x < 256) l ->
  map (fun b : byte => bv_unsigned b) (map (Z_to_bv 8) l) = l.
Proof.
induction l as [|x l IH]; intros HF; [reflexivity|].
inversion HF as [|y t Hx Hl]; subst. cbn [map]. rewrite (IH Hl). f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hx.
Qed.

Lemma hoc_garr8_rng : forall m p l, garr8 SEGS m p l -> Forall (fun x => 0 <= x < 256) l.
Proof.
intros m p l HG. apply Forall_forall. intros x Hx. destruct (In_nth l x 0 Hx) as (j & Hj & <-). exact (proj2 (HG j Hj)).
Qed.

Lemma hoc_sub_garr : forall m p (Hh : list byte) k n, garr8 SEGS m p (map (fun b : byte => bv_unsigned b) Hh) ->
  0 <= k -> (Z.to_nat k + n <= length Hh)%nat ->
  garr8 SEGS m (p + k) (map (fun b : byte => bv_unsigned b) (disco_table_c.sub Hh k n)).
Proof.
intros m p Hh k n HG Hk Hle.
replace (p + k) with (p + Z.of_nat (Z.to_nat k)) by lia.
replace (map (fun b : byte => bv_unsigned b) (disco_table_c.sub Hh k n))
  with (firstn n (skipn (Z.to_nat k) (map (fun b : byte => bv_unsigned b) Hh))).
- apply garr8_sub_x; [exact HG | rewrite length_map; exact Hle].
- unfold disco_table_c.sub. rewrite skipn_map, firstn_map. reflexivity.
Qed.

Lemma hoc_skip_garr : forall m p (Hh : list byte) k, garr8 SEGS m p (map (fun b : byte => bv_unsigned b) Hh) ->
  (k <= length Hh)%nat -> garr8 SEGS m (p + Z.of_nat k) (map (fun b : byte => bv_unsigned b) (skipn k Hh)).
Proof.
intros m p Hh k HG Hk.
pose proof (garr8_sub_x SEGS _ p _ k (length Hh - k) HG ltac:(rewrite length_map; lia)) as X.
rewrite <- skipn_map. rewrite firstn_all2 in X; [exact X|]. rewrite length_skipn, length_map. lia.
Qed.

Lemma ho_base_setfq : forall c fx fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  ho_base (ho_setfq c fx) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F.
Proof. intros c fx fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB. exact HB. Qed.

Lemma ho_SRr_setfq : forall c (fx : YK11.FPState) (Wx : world SEGS) cf,
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx) k = Sem.reg_get (@YK11.fp_regs (c_fq c)) k) ->
  (@YK11.fp_csr fx = @YK11.fp_csr (c_fq c) \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx)) 5) 7 = 0) ->
  SRr SEGS Wx cf (ho_post (ho_setfq c fx)) -> SRr SEGS Wx cf (ho_post c).
Proof.
intros c fx Wx cf Hfr Hcs HR. eapply SRr_mono; [exact HR|].
intros W5 c5 _ HP. unfold ho_post, treac_hunt_observe_post in HP |- *.
destruct HP as (fx' & ly5 & S5 & regs5 & mem5 & md5 & r5 & H5 & Hc5 & Hfr5 & Hcs5 & HR5).
exists fx', ly5, S5, regs5, mem5, md5, r5, H5. split; [exact Hc5|]. split.
- intros kk Hk. rewrite (Hfr5 kk Hk). exact (Hfr kk Hk).
- split; [|exact HR5]. destruct Hcs5 as [Hcs5|Hcs5]; [rewrite Hcs5; exact Hcs | right; exact Hcs5].
Qed.

Lemma hoC_call : ho_seg_E_stmt -> ho_seg_T_stmt ->
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F (regsY : bvmap 5 word) mdY,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 (c_H c) regs2 sp1 F ->
  getr regs2 19 = w64 (c_out c) -> getr regs2 20 = w64 (c_now c) -> getr regs2 22 = w64 (c_f c) ->
  getr regs2 26 = w64 SB -> ho_fsh W2 mem2 F ho_shC ->
  (exists ch, achain ly2 (aview SEGS (w_H W2) mem2) (spZ (c_regs c) - 16) (spZ (c_regs c)) ch) ->
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c) (map (fun b : byte => bv_unsigned b) (c_O c))) ->
  ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 mem2 mdY k2 ->
  getr regsY 1 = Z_to_bv 64 (BASE + 0x733c) ->
  getr regsY 10 = Z_to_bv 64 (c_h c + 400) -> getr regsY 11 = Z_to_bv 64 (c_f c) ->
  getr regsY 12 = w64 (ho_L c) -> getr regsY 13 = Z_to_bv 64 (c_h c + 412) ->
  getr regsY 14 = Z_to_bv 64 (F + 32) -> getr regsY 23 = Z_to_bv 64 (F + 32) ->
  getr regsY 2 = getr regs2 2 -> getr regsY 3 = getr regs2 3 -> getr regsY 4 = getr regs2 4 ->
  getr regsY 8 = getr regs2 8 -> getr regsY 9 = getr regs2 9 -> getr regsY 18 = getr regs2 18 ->
  getr regsY 19 = getr regs2 19 -> getr regsY 20 = getr regs2 20 -> getr regsY 21 = getr regs2 21 ->
  getr regsY 22 = getr regs2 22 -> getr regsY 24 = getr regs2 24 -> getr regsY 25 = getr regs2 25 ->
  getr regsY 26 = getr regs2 26 -> getr regsY 27 = getr regs2 27 ->
  SRr SEGS W2 (mkCfg (mkst (fx := c_fq c) regsY (Z_to_bv 64 (BASE + AF_both3_reac_disco_classify_on_segment)) mem2
    (seg_rom SEGS)) mdY) (ho_post c).
Proof.
intros HE HT c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F regsY mdY Hbase H19 H20 H22 H26 Hfsh Hch HGO HJ
  Y1 Y10 Y11 Y12 Y13 Y14 Y23 G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G24 G25 G26 G27.
pose proof Hbase as (HPRE & HMID & HSP1 & HFeq & HREGS & HSAVED).
pose proof HMID as (HJm & Hfrs2 & Hfa2 & Hperm & HKEPT & HROD2 & HGh & HlenH & Hflag120 & Hk2le).
pose proof HSP1 as (Hsp1eq & Hsp1win & Hsp1mod).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R24 & R25).
pose proof HPRE as ((mdc & HJ0) & HROD & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin1 & Hwin2 & Hdepth & Hlen & Hnow & Hout &
  Hh0 & Hh8 & Hin & Hhb & Hhe & Hwr & HOK & LFB & HGH & Hfr50 & Houtp & HKM & HKT).
pose proof HJ as (HAR2 & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & HcA & HcB & HcC & HcD & HcE & Hpres2 &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBlo. unfold YImgTop.IMG_LO in HBlo.
assert (Hin1 : In (1%Z, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hin1) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hin1) as (HFal & [HFhi _] & HFpres & HFSpres).
assert (HFaddr : frame_addr ly2 1 fpos = F) by (rewrite Hfa2; symmetry; exact HFeq).
rewrite HFaddr in HF4096, HFceil, HFapp, HFal, HFpres, HFSpres.
assert (Hfb : fs_frame_bytes 1 = 128) by reflexivity.
rewrite Hfb in HFceil, HFapp, HFpres, HFSpres.
assert (Hhb2 : In (c_hb c, c_hn c) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_hb c) (c_hn c) HAR2 Hhb2) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ (c_hb c) (c_hn c) 1 fpos HAR2 Hhb2 Hin1) as Hsephf.
unfold zdisjoint in Hsephf. cbn [fst snd] in Hsephf. rewrite HFaddr, Hfb in Hsephf.
pose proof (am_layout _ _ _ _ (proj1 HAR2)) as LO. pose proof (lo_stk_ceil _ LO) as Hstkc. unfold ASAN_CEIL in Hstkc.
assert (HFR : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
assert (HCS : CLS_STK = 8512) by reflexivity.
assert (Hlyt : ly_top ly2 = ly_top (c_ly c)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
assert (Hlylo : ly_stk_lo ly2 = ly_stk_lo (c_ly c))
  by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
assert (HspZr : 0 <= spZ (c_regs c) < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
assert (Ysp : spZ regsY = sp1) by (unfold spZ; rewrite G2, R2; apply unsigned_lit_small; lia).
assert (Ys0 : s0Z regsY = spZ (c_regs c)) by (unfold s0Z; rewrite G8, R8; apply unsigned_lit_small; lia).
assert (Hp24 : forall a, F + 32 <= a < F + 32 + Z.of_nat 24 -> exists b, mrestrict (w_H W2) mem2 (Z_to_bv 64 a) = Some b).
{ intros a Ha. destruct (proj1 (HFpres a ltac:(lia))) as [Hh0' [b Hb]]. exists b. unfold mrestrict. rewrite Hh0'. exact Hb. }
destruct (garr8_of_present SEGS (mrestrict (w_H W2) mem2) (F + 32) 24 Hp24) as (lO & HlO & HGO0).
set (OB := map (Z_to_bv 8) lO).
assert (HGOB : garr8 SEGS (mrestrict (w_H W2) mem2) (F + 32) (cls_bytes OB))
  by (unfold cls_bytes, OB; rewrite hoc_bytes_of by exact (hoc_garr8_rng _ _ _ HGO0); exact HGO0).
assert (LOB : length OB = 24%nat) by (unfold OB; rewrite length_map; exact HlO).
destruct (HuntObsLib.cm_lock_some (c_FB c) (ho_L c) (ho_U c) (disco_table_c.sub (c_H c) 400 12)) as (Lb' & HLb').
assert (HLk0 : disco_classify_c.lock_ok (disco_table_c.sub (c_H c) 400 12)) by (destruct HOK as (_ & _ & X & _); exact X).
assert (HLbok : disco_classify_c.lock_ok Lb')
  by exact (HuntObsLib.cm_lock_ok (c_FB c) (ho_L c) (ho_U c) _ Lb' (fun _ => LFB) HLk0 HLb').
assert (HLk' : ho_Lk' c = Lb') by (unfold ho_Lk', ho_Lk; rewrite HLb'; reflexivity).
assert (HRA0 : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (F + 32) 24).
{ intros x Hx. exists 0. split; [|left; reflexivity].
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Bx.
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as BF.
  pose proof (Z.div_mod F 32 ltac:(lia)) as DF32.
  assert (Hi : 4 <= x / 8 - F / 8 <= 6) by lia.
  replace (shadow_of_addr SHADOW_OFF x) with (SB + F / 8 + (x / 8 - F / 8))
    by (unfold shadow_of_addr, SB, SHADOW_OFF; lia).
  rewrite (Hfsh (x / 8 - F / 8) ltac:(lia)).
  assert (Hc : x / 8 - F / 8 = 4 \/ x / 8 - F / 8 = 5 \/ x / 8 - F / 8 = 6) by lia.
  destruct Hc as [E | [E | E]]; rewrite E; reflexivity. }
assert (HL50 : 50 <= ho_L c -> 50 <= c_len c).
{ unfold ho_L, reac_frame_clean_len_c.reac_frame_clean_len_model.
  destruct ((54 <=? c_len c) && ((c_len c - 52) mod 36 =? 2)); intros X; clear - X; lia. }
assert (HLr : 0 <= ho_L c < 2 ^ 64).
{ unfold ho_L, reac_frame_clean_len_c.reac_frame_clean_len_model.
  destruct ((54 <=? c_len c) && ((c_len c - 52) mod 36 =? 2)) eqn:EL; [|clear - Hlen; lia].
  apply andb_prop in EL. destruct EL as [EL _]. apply Z.leb_le in EL. clear - Hlen EL. lia. }
destruct Hch as (ch & Hch).
eapply SRr_bind.
{ eapply (TCOS (c_fq c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 mem2 mdY k2 regsY ch (c_h c + 400) (c_f c) (ho_L c) (c_h c + 412) (F + 32)
    (c_FB c) (ho_U c) OB (ho_Lk c)).
  - exact HJ.
  - exact HROD2.
  - rewrite Y1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Y1, unsigned_lit_small by lia. lia.
  - rewrite G3. exact R3.
  - rewrite G4. exact R4.
  - exact Y10.
  - exact Y11.
  - exact Y12.
  - exact Y13.
  - exact Y14.
  - rewrite Ysp, Ys0. eapply achain_lower; [exact Hch | lia].
  - rewrite Ysp. pose proof (Z.div_mod sp1 16 ltac:(lia)). pose proof (Z.mod_pos_bound sp1 16 ltac:(lia)).
    pose proof (Z.div_mod sp1 32 ltac:(lia)). lia.
  - rewrite Ysp, HCS. lia.
  - rewrite Ysp. lia.
  - rewrite Ysp, Hlyt. lia.
  - rewrite Hfrs2. cbn [length]. unfold REAC_HUNT_OBSERVE_DEPTH, CLS_DEPTH in *. lia.
  - exact HLr.
  - exact LFB.
  - unfold ho_U. apply HuntObsLib.len_sub; lia.
  - exact LOB.
  - intros HLx. pose proof (HL50 HLx) as Hl50.
    destruct (Hfr50 Hl50) as (Hf0 & (fb & fn & Hfin & Hfb1 & Hfb2) & Hfh & HGF).
    assert (Hfin2 : In (fb, fn) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hfin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ fb fn HAR2 Hfin2) as (_ & Hfb4096 & Hfbceil & Hfbapp & Hfbpres & _).
    split; [exact Hf0|]. split; [|split].
    + unfold cls_read. rewrite Ysp.
      split; [lia|]. split; [lia|]. split; [eapply (amem_range_of_block SEGS B LAWS); [exact HAR2 | exact Hfin2 | lia | lia]|].
      split; [right; rewrite HCS; lia|]. split; [intros a Ha; exact (proj1 (Hfbpres a ltac:(lia)))|].
      split; [eapply (range_addressable_of_block SEGS B LAWS); [exact HAR2 | exact Hfin2 | lia | lia]|].
      eapply (shadow_hull_vis_of_block SEGS B LAWS); [exact HAR2 | exact Hfin2 | lia | lia | lia].
    + right. left. exists fb, fn. split; [exact Hfin2|]. lia.
    + unfold cls_bytes. apply (garr8_aview_kept SEGS (w_H (c_W c)) (w_H W2) (c_memc c) mem2 (c_f c)); [|exact HGF].
      intros a Ha. rewrite length_map, LFB in Ha.
      pose proof HKEPT as (_ & K2 & _). replace a with (fb + (a - fb)) by lia. apply (K2 fb fn (a - fb) Hfin); [lia|].
      replace (fb + (a - fb)) with a by lia. unfold tho_wr. intros [Hx | (Hx1 & Hx2)]; [clear - Ha Hx Hfh; lia|].
      destruct (Houtp Hx1) as (_ & _ & Hof). specialize (Hof Hl50). clear - Ha Hx2 Hof; lia.
  - unfold cls_read. rewrite Ysp.
    split; [lia|]. split; [lia|]. split; [eapply (amem_range_of_block SEGS B LAWS); [exact HAR2 | exact Hhb2 | lia | lia]|].
    split; [right; rewrite HCS; lia|]. split; [intros a Ha; exact (proj1 (Hbpres a ltac:(lia)))|].
    split; [eapply (range_addressable_of_block SEGS B LAWS); [exact HAR2 | exact Hhb2 | lia | lia]|].
    eapply (shadow_hull_vis_of_block SEGS B LAWS); [exact HAR2 | exact Hhb2 | lia | lia | lia].
  - right. left. exists (c_hb c), (c_hn c). split; [exact Hhb2|]. lia.
  - unfold cls_bytes, ho_U. apply hoc_sub_garr; [exact HGh | lia | rewrite HlenH; lia].
  - lia.
  - pose proof (Z.div_mod (F + 32) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (F + 32) 4 ltac:(lia)).
    pose proof (Z.div_mod F 32 ltac:(lia)). lia.
  - unfold cls_read. rewrite Ysp.
    split; [lia|]. split; [lia|].
    split; [unfold amem_range; clear - HFapp C1; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *; lia|].
    split; [right; rewrite HCS; lia|]. split; [intros a Ha; exact (proj1 (HFpres a ltac:(lia)))|].
    split; [exact HRA0|].
    eapply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 mem2 mdY 1 fpos);
      [exact HAR2 | exact Hin1 | rewrite HFaddr; lia | rewrite HFaddr, Hfb; lia | lia].
  - exact HGOB.
  - intros a Ha. right; right; right. exists 1%Z, fpos. split; [left; reflexivity|].
    left. unfold in_zr; try unfold frame_rng; cbn [fst snd]. rewrite HFaddr, Hfb. lia.
  - left. rewrite Hlylo. lia.
  - unfold ho_Lk. cbv beta iota.
    split; [lia|].
    split; [pose proof (Z.div_mod (c_h c + 400) 4 ltac:(lia)); pose proof (Z.mod_pos_bound (c_h c + 400) 4 ltac:(lia));
            pose proof (Z.div_mod (c_h c) 8 ltac:(lia)); lia|].
    split; [apply HuntObsLib.len_sub; lia|].
    split.
    { unfold cls_read. rewrite Ysp.
      split; [lia|]. split; [lia|]. split; [eapply (amem_range_of_block SEGS B LAWS); [exact HAR2 | exact Hhb2 | lia | lia]|].
      split; [right; rewrite HCS; lia|]. split; [intros a Ha; exact (proj1 (Hbpres a ltac:(lia)))|].
      split; [eapply (range_addressable_of_block SEGS B LAWS); [exact HAR2 | exact Hhb2 | lia | lia]|].
      eapply (shadow_hull_vis_of_block SEGS B LAWS); [exact HAR2 | exact Hhb2 | lia | lia | lia]. }
    split; [unfold cls_bytes; apply hoc_sub_garr; [exact HGh | lia | rewrite HlenH; lia]|].
    split; [intros a Ha; eapply hoc_awr_tr; [exact Hperm | exact Hfa2 |]; apply hoc_awr_own; apply Hwr; lia|].
    left. rewrite Hlylo. lia.
  - clear - Hsephf Hhb Hhe; lia.
  - intros HLx. pose proof (HL50 HLx) as Hl50.
    destruct (Hfr50 Hl50) as (Hf0 & (fb & fn & Hfin & Hfb1 & Hfb2) & Hfh & HGF).
    assert (Hfin2 : In (fb, fn) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hfin).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ fb fn 1 fpos HAR2 Hfin2 Hin1) as Hsd.
    unfold zdisjoint in Hsd. cbn [fst snd] in Hsd. rewrite HFaddr, Hfb in Hsd. clear - Hsd Hfb1 Hfb2; lia.
  - unfold ho_Lk. cbv beta iota. split; [clear - Hsephf Hhb Hhe; lia|]. split; [lia|].
    intros HLx. pose proof (HL50 HLx) as Hl50. destruct (Hfr50 Hl50) as (_ & _ & Hfh & _). lia. }
cbv beta. intros W3 c3 Hwle3
  (fx' & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfr3 & Hcs3 & HJ3 & HP3 & Hfrs3 & Hperm3 & Hr10 & HGo3 & HLk3 & HK3).
rewrite Y1 in Hc3. subst c3.
apply (ho_SRr_setfq c fx' W3 _ Hfr3 Hcs3).
replace (k2 + EV_CLS) with k2 in HJ3 by (unfold EV_CLS; lia).
pose proof HJ3 as (HAR3 & HLY3 & _).
assert (HlyF2 : ly_F ly2 = ly_F (c_ly c)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (HlyF3 : ly_F ly3 = ly_F (c_ly c)) by (destruct HLY3 as (_ & _ & _ & _ & _ & X & _); exact X).
destruct (hoc_frame_eq ly2 ly3 ltac:(lia)) as (HFA32 & HFL32).
assert (HFA3 : forall cid p, frame_addr ly3 cid p = frame_addr (c_lyc c) cid p)
  by (intros cid p; rewrite HFA32; apply Hfa2).
assert (Hfrs3' : frames S3 = (1, fpos) :: frames (c_Sc c)) by (rewrite Hfrs3; exact Hfrs2).
assert (Hperm3' : Permutation (ablocks B ly3 S3) (ablocks B (c_lyc c) (c_Sc c)))
  by (eapply Permutation_trans; [exact Hperm3 | exact Hperm]).
pose proof HK3 as (T1 & T2 & T3 & T4 & T5 & T6). rewrite Ysp in T1, T5, T6.
assert (NCW : forall a, ~ (F + 32 <= a < F + 32 + 24) -> ~ (c_h c + 400 <= a < c_h c + 400 + 12) ->
  ~ cls_wr (c_h c + 400) (F + 32) (ho_Lk c) a) by (intros a X1 X2 [X | X]; [exact (X1 X) | exact (X2 X)]).
pose proof HKEPT as (K1 & K2 & K3 & K4 & K5 & K6).
assert (Htw : forall a, ~ tho_wr (c_h c) (c_out c) a -> ~ (c_h c + 400 <= a < c_h c + 400 + 12))
  by (intros a Hn Ha; apply Hn; left; lia).
assert (HKC : treac_hunt_observe_kept (c_lyc c) (c_Sc c) (c_W c) (c_memc c) W3 mem3 (spZ (c_regs c)) (c_h c) (c_out c)).
{ split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hns Hnw. rewrite (T1 a Ha ltac:(clear - Hns HCS HFR Hsp1win; lia) (NCW a ltac:(clear - Ha HFceil; lia) (Htw a Hnw))). exact (K1 a Ha Hns Hnw).
  - intros b m i Hbm Hi Hnw.
    assert (Hbm2 : In (b, m) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hbm).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 1 fpos HAR2 Hbm2 Hin1) as Hsd.
    unfold zdisjoint in Hsd. cbn [fst snd] in Hsd. rewrite HFaddr, Hfb in Hsd.
    rewrite (T2 b m i Hbm2 Hi (NCW (b + i) ltac:(clear - Hsd Hi; lia) (Htw _ Hnw))). exact (K2 b m i Hbm Hi Hnw).
  - intros a X1 X2 X3. rewrite (T3 a X1 X2 X3). exact (K3 a X1 X2 X3).
  - intros cid pos a Hcp Hr Hnw.
    destruct (in_split _ _ Hcp) as (l2 & l3 & Hsplit).
    assert (Hd : zdisjoint (frame_rng ly2 (1%Z, fpos)) (frame_rng ly2 (cid, pos)))
      by (apply (sep_frames_pos SEGS B LAWS ly2 S2 W2 mem2 mdY (1%Z, fpos) (cid, pos) [] l2 l3 HAR2);
          rewrite Hfrs2, Hsplit; reflexivity).
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite HFaddr, Hfb in Hd.
    assert (Hcp2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hcp).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR2 Hcp2) as (Gb1 & Gb2 & Gb3).
    pose proof (fs_frame_bytes_nonneg cid) as Gn.
    rewrite (Hfa2 cid pos) in Hd, Gb1, Gb2, Gb3.
    assert (Hr2 : in_zr a (frame_rng ly2 (cid, pos)) \/
                  in_zr a (shadow_addr (frame_addr ly2 cid pos), fs_frame_bytes cid / 8))
      by (unfold frame_rng in *; cbn [fst snd] in *; rewrite !Hfa2; exact Hr).
    assert (Hno : ~ (F + 32 <= a < F + 32 + 24)).
    { intros Ha'. unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr.
      pose proof (Z.div_mod (frame_addr (c_lyc c) cid pos) 8 ltac:(lia)) as D1.
      pose proof (Z.mod_pos_bound (frame_addr (c_lyc c) cid pos) 8 ltac:(lia)) as D2.
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as D4.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in Gb3, HFapp. clear - Ha' Hr Hd Gb1 Gb2 Gb3 Gn D1 D2 D3 D4 HFapp HFceil HF4096 C1; lia. }
    rewrite (T4 cid pos a Hcp2 Hr2 (NCW a Hno (Htw a Hnw))). exact (K4 cid pos a Hcp Hr Hnw).
  - intros a Ha Hns Hp. apply (T5 a Ha ltac:(clear - Hns HCS HFR Hsp1win; lia)). exact (K5 a Ha Hns Hp).
  - intros a Ha. destruct (Z_lt_le_dec a (sp1 - CLS_STK)) as [Hlt | Hge].
    + apply T5; [lia | lia | apply K6; lia].
    + destruct (Z_lt_le_dec a sp1) as [Hlt2 | Hge2]; [apply T6; lia|]. apply T5; [lia | lia | apply K6; lia]. }
assert (KH : forall a, c_h c <= a < c_h c + 480 -> ~ (c_h c + 400 <= a < c_h c + 412) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn.
  pose proof (T2 (c_hb c) (c_hn c) (a - c_hb c) Hhb2 ltac:(clear - Ha Hhb Hhe; lia) (NCW (c_hb c + (a - c_hb c)) ltac:(clear - Ha Hsephf Hhb Hhe; lia) ltac:(clear - Hn; lia))) as X.
  replace (c_hb c + (a - c_hb c)) with a in X by lia. exact X. }
assert (LT400 : length (disco_table_c.sub (c_H c) 0 400) = 400%nat) by (apply HuntObsLib.len_sub; lia).
assert (LLb : length Lb' = 12%nat) by exact (proj1 HLbok).
assert (HG3 : garr8 SEGS (mrestrict (w_H W3) mem3) (c_h c) (map (fun b : byte => bv_unsigned b) (ho_Hcls c))).
{ unfold ho_Hcls. rewrite HLk'. apply ho_garr8_cat3; [exact LT400 | exact LLb | | | ].
  - apply (garr8_aview_kept SEGS (w_H W2) (w_H W3) mem2 mem3 (c_h c)).
    + intros a Ha. rewrite length_map, LT400 in Ha. apply KH; lia.
    + pose proof (hoc_sub_garr _ _ _ 0 400 HGh ltac:(lia) ltac:(rewrite HlenH; lia)) as X.
      rewrite Z.add_0_r in X. exact X.
  - exact (HLk3 Lb' HLb').
  - apply (garr8_aview_kept SEGS (w_H W2) (w_H W3) mem2 mem3 (c_h c + 412)).
    + intros a Ha. rewrite length_map, length_skipn, HlenH in Ha. apply KH; lia.
    + exact (hoc_skip_garr _ _ _ 412 HGh ltac:(lia)). }
assert (HFL3 : rdword (aview SEGS (w_H W3) mem3) (frame_addr ly3 1 fpos + 120) = Some (flag_addr ly3 1 fpos)).
{ rewrite HFA32, HFL32, <- Hflag120. apply rdword_ext. intros kk Hkk. rewrite HFaddr.
  apply (T4 1 fpos); [exact Hin1 | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFaddr, Hfb; clear - Hkk; lia | apply NCW; clear - Hkk Hsephf Hhb Hhe; lia]. }
assert (HSV3 : ho_saved c W3 mem3).
{ intros j Hj. apply (hoc_val_tr W2 mem2); [exact (HSAVED j Hj)|].
  intros x Hx. apply T1; [lia | lia | apply NCW; lia]. }
assert (HFSH3 : ho_fsh W3 mem3 F ho_shC).
{ intros i Hi. rewrite <- (Hfsh i Hi).
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as BF8.
  apply (T4 1 fpos); [exact Hin1 | |].
  - right. unfold in_zr. cbn [fst snd]. rewrite HFaddr, Hfb. unfold shadow_addr, SB, SHADOW_OFF. change (128 / 8) with 16. lia.
  - apply NCW; clear - BF8 DF8 Hi HFapp Hbapp Hhb Hhe C1; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd, SB, SHADOW_OFF in *; lia. }
assert (HGO3 : c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W3) mem3) (c_out c) (map (fun b : byte => bv_unsigned b) (c_O c))).
{ intros Hout'. destruct (Houtp Hout') as ((_ & _ & _ & _ & _ & _ & _ & _ & HOL & _ & HFB) & Hoh & _).
  apply (garr8_aview_kept SEGS (w_H W2) (w_H W3) mem2 mem3 (c_out c)); [|exact (HGO Hout')].
  intros i Hi. rewrite length_map, HOL in Hi.
  destruct HFB as [(cid & pos & Hcp & Hlo & Hhi) | (b & m & Hbm & Hlo & Hhi)].
  - destruct (in_split _ _ Hcp) as (l2 & l3 & Hsplit).
    assert (Hd : zdisjoint (frame_rng ly2 (1%Z, fpos)) (frame_rng ly2 (cid, pos)))
      by (apply (sep_frames_pos SEGS B LAWS ly2 S2 W2 mem2 mdY (1%Z, fpos) (cid, pos) [] l2 l3 HAR2);
          rewrite Hfrs2, Hsplit; reflexivity).
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite HFaddr, Hfb, (Hfa2 cid pos) in Hd.
    assert (Hcp2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hcp).
    apply (T4 cid pos i Hcp2); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite (Hfa2 cid pos); clear - Hi Hlo Hhi; lia | apply NCW; clear - Hi Hd Hlo Hhi Hoh; lia].
  - assert (Hbm2 : In (b, m) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hbm).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 1 fpos HAR2 Hbm2 Hin1) as Hsd.
    unfold zdisjoint in Hsd. cbn [fst snd] in Hsd. rewrite HFaddr, Hfb in Hsd.
    pose proof (T2 b m (i - b) Hbm2 ltac:(clear - Hi Hlo Hhi; lia) (NCW (b + (i - b)) ltac:(clear - Hi Hsd Hlo Hhi; lia) ltac:(clear - Hi Hoh; lia))) as X.
    replace (b + (i - b)) with i in X by lia. exact X. }
assert (HB4 : forall (regs4 : bvmap 5 word) md4,
  ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly3 S3 W3 mem3 md4 k2 ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 21 = getr regs3 21 -> getr regs4 24 = getr regs3 24 -> getr regs4 25 = getr regs3 25 ->
  ho_base c fpos ly3 S3 W3 mem3 md4 k2 (ho_Hcls c) regs4 sp1 F).
{ intros regs4 md4 HJ4 P2 P3 P4 P8 P9 P18 P21 P24 P25.
  unfold ho_base. split; [exact HPRE|]. split.
  { unfold ho_mid. split; [exact HJ4|]. split; [exact Hfrs3'|]. split; [exact HFA3|]. split; [exact Hperm3'|].
    split; [exact HKC|]. split; [exact (hoc_rod_kept W2 W3 mem2 mem3 HROD2 T3)|]. split; [exact HG3|].
    split; [unfold ho_Hcls; rewrite HLk', !length_app, LT400, LLb, length_skipn, HlenH; reflexivity|].
    split; [exact HFL3 | exact Hk2le]. }
  split; [exact HSP1|]. split; [exact HFeq|]. split; [|exact HSV3].
  unfold ho_regs_mid.
  split; [rewrite P2; etransitivity; [exact (HP3 2 ltac:(unfold acallee_saved; lia))|];
          etransitivity; [exact G2 | exact R2]|].
  split; [rewrite P3; etransitivity; [exact (HP3 3 ltac:(unfold acallee_saved; lia))|];
          etransitivity; [exact G3 | exact R3]|].
  split; [rewrite P4; etransitivity; [exact (HP3 4 ltac:(unfold acallee_saved; lia))|];
          etransitivity; [exact G4 | exact R4]|].
  split; [rewrite P8; etransitivity; [exact (HP3 8 ltac:(unfold acallee_saved; lia))|];
          etransitivity; [exact G8 | exact R8]|].
  split; [rewrite P9; etransitivity; [exact (HP3 9 ltac:(unfold acallee_saved; lia))|];
          etransitivity; [exact G9 | exact R9]|].
  split; [rewrite P18; etransitivity; [exact (HP3 18 ltac:(unfold acallee_saved; lia))|];
          etransitivity; [exact G18 | exact R18]|].
  split; [rewrite P21; etransitivity; [exact (HP3 21 ltac:(unfold acallee_saved; lia))|];
          etransitivity; [exact G21 | exact R21]|].
  split; [rewrite P24; etransitivity; [exact (HP3 24 ltac:(unfold acallee_saved; lia))|];
          etransitivity; [exact G24 | exact R24]|].
  rewrite P25; etransitivity; [exact (HP3 25 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact G25 | exact R25]. }
remember (Eimg (Ereg regs3 [])) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply Eimg_env).
assert (HAE3 : env_agree 32 (Ereg regs3 []) E3)
  by (rewrite HE3; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS3 : st_ok_pi (fx := fx') SEGS VAL E3 (mkSS 0x733c sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst (fx := fx') regs3 (Z_to_bv 64 (BASE + 0x733c)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
  [rewrite HE3; apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK3 : sh_ok SEGS (SLit SHADOW_OFF) [] E3
  (mrestrict (w_H W3) (ms_mem (mkst (fx := fx') regs3 (Z_to_bv 64 (BASE + 0x733c)) mem3 (seg_rom SEGS)))))
  by constructor.
pose (RUNTO := paj_run_to (fx := fx') B LAWS).
unfold ho_seg_E_stmt, ho_cfg in HE. unfold ho_seg_T_stmt, ho_cfg in HT.
destruct (HuntObsLib.cm_ret_cases (c_FB c) (ho_L c) (ho_U c) (ho_Lk c)) as [R0 | Rm].
- rewrite R0 in Hr10.
  pose proof (st_ok_pi_pin_reg' E3 _ _ (10%bv : bv 5) 0 HS3 ltac:(cbn [ms_regs restrict mkst]; exact Hr10) eq_refl) as HS4.
  clear HS3. norm_ss HS4.
  paj_run_to_tok RUNTO HS4 HJ3 SHOK3 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) 0x73b4; [apply awr_ok_nil|].
  assert (Em4 : ms_mem ms = mem3)
    by (apply FunctionalExtensionality.functional_extensionality; intros x; apply HF; intros (r & Hr & _); destruct Hr).
  pose proof (regs_kept_of_st_ok_pi E3 _ _ regs3 [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26]%bv HS4 HAE3
    ltac:(vm_compute; reflexivity)) as RK3. cbn [ms_regs restrict] in RK3.
  pmkst HS4. rewrite Em4. rewrite Em4 in HJ3.
  apply (HE (ho_setfq c fx') fpos ly3 S3 W3 mem3 _ k2 (ms_regs ms) sp1 F).
  + apply ho_base_setfq. change (ho_Hcls (ho_setfq c fx')) with (ho_Hcls c).
    apply HB4; [exact HJ3 | exact (RK3 2%bv ltac:(cbn; tauto)) | exact (RK3 3%bv ltac:(cbn; tauto))
     | exact (RK3 4%bv ltac:(cbn; tauto)) | exact (RK3 8%bv ltac:(cbn; tauto)) | exact (RK3 9%bv ltac:(cbn; tauto))
     | exact (RK3 18%bv ltac:(cbn; tauto)) | exact (RK3 21%bv ltac:(cbn; tauto)) | exact (RK3 24%bv ltac:(cbn; tauto))
     | exact (RK3 25%bv ltac:(cbn; tauto))].
  + etransitivity; [exact (RK3 19%bv ltac:(cbn; tauto))|].
    etransitivity; [exact (HP3 19 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact G19 | exact H19].
  + etransitivity; [exact (RK3 20%bv ltac:(cbn; tauto))|].
    etransitivity; [exact (HP3 20 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact G20 | exact H20].
  + etransitivity; [exact (RK3 23%bv ltac:(cbn; tauto))|].
    etransitivity; [exact (HP3 23 ltac:(unfold acallee_saved; lia))|]. exact Y23.
  + etransitivity; [exact (RK3 26%bv ltac:(cbn; tauto))|].
    etransitivity; [exact (HP3 26 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact G26 | exact H26].
  + exact HFSH3.
  + exact R0.
  + change (hunt_c.hunt_ok (ho_Hcls c)).
    unfold ho_Hcls. rewrite HLk'. apply ho_hunt_ok_fail; [exact HOK | exact LLb | exact HLbok].
  + pose proof HGo3 as X. unfold cls_bytes in X. unfold ho_Lk in R0, X.
    rewrite (HuntObsLib.cm_out_ok _ _ _ _ OB R0) in X. exact X.
  + exact HGO3.
- rewrite Rm in Hr10.
  pose proof (st_ok_pi_pin_reg' E3 _ _ (10%bv : bv 5) (-1) HS3 ltac:(cbn [ms_regs restrict mkst]; exact Hr10) eq_refl) as HS4.
  clear HS3. norm_ss HS4.
  paj_run_to_tok RUNTO HS4 HJ3 SHOK3 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) 0x7344; [apply awr_ok_nil|].
  assert (Em4 : ms_mem ms = mem3)
    by (apply FunctionalExtensionality.functional_extensionality; intros x; apply HF; intros (r & Hr & _); destruct Hr).
  pose proof (regs_kept_of_st_ok_pi E3 _ _ regs3 [] [2; 3; 4; 8; 9; 18; 21; 24; 25]%bv HS4 HAE3
    ltac:(vm_compute; reflexivity)) as RK3. cbn [ms_regs restrict] in RK3.
  prreg HS4 (20%bv : bv 5) Q20.
  pmkst HS4. rewrite Em4. rewrite Em4 in HJ3.
  apply (HT (ho_setfq c fx') fpos ly3 S3 W3 mem3 _ k2 (ms_regs ms) sp1 F (ho_Hcls c) (-1)).
  + apply ho_base_setfq.
    apply HB4; [exact HJ3 | exact (RK3 2%bv ltac:(cbn; tauto)) | exact (RK3 3%bv ltac:(cbn; tauto))
     | exact (RK3 4%bv ltac:(cbn; tauto)) | exact (RK3 8%bv ltac:(cbn; tauto)) | exact (RK3 9%bv ltac:(cbn; tauto))
     | exact (RK3 18%bv ltac:(cbn; tauto)) | exact (RK3 21%bv ltac:(cbn; tauto)) | exact (RK3 24%bv ltac:(cbn; tauto))
     | exact (RK3 25%bv ltac:(cbn; tauto))].
  + rewrite Q20. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
  + left. reflexivity.
  + exact HFSH3.
  + unfold ho_Hcls. rewrite HLk'. apply ho_hunt_ok_fail; [exact HOK | exact LLb | exact HLbok].
  + change (tho_model (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) (-1) (ho_Hcls c)
      (fun A => garr8 SEGS (mrestrict (w_H W3) mem3) (c_out c) (map (fun b : byte => bv_unsigned b) A))).
    unfold ho_Hcls. rewrite HLk'. apply tho_model_fail; [| exact HLb' | exact HGO3].
    unfold ho_L, ho_U, ho_Lk in Rm. rewrite Rm. lia.
Qed.

End h.
End f.
End d.
