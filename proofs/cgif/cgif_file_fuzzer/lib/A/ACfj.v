(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YC20 YC7x YC21 YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI17 YE00 YE01 YE02 YE03 YO08 YI0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACfn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACek ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACel ACer ACfm ACf5 ACf9 ACf7 ACf8 ACf6 ACfh ACez ACf0 ACf1 ACf2 ACf3 ACf4 ACfk ACfg ACfb ACfc ACfd ACfe ACff ACfa ACey ACet.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma hdr5_short : forall P, Z.of_nat (length P) < 14 -> fst (fst (hdr5 P)) = true.
Proof.
intros P HP. unfold hdr5.
assert (R0 : forall n, 0 < n -> YO07.rd [] n = (true, [], [])) by (intros n Hn; apply rd_short; cbn; lia).
destruct (Z_lt_le_dec (Z.of_nat (length P)) 2) as [H1|H1].
{ rewrite (rd_short P 2 H1), !R0 by lia. reflexivity. }
rewrite (rd_ok P 2) by lia.
destruct (Z_lt_le_dec (Z.of_nat (length (skipn (Z.to_nat 2) P))) 2) as [H2|H2].
{ rewrite (rd_short _ 2 H2), !R0 by lia. reflexivity. }
rewrite (rd_ok (skipn (Z.to_nat 2) P) 2) by lia.
destruct (Z_lt_le_dec (Z.of_nat (length (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) P)))) 4) as [H3|H3].
{ rewrite (rd_short _ 4 H3), !R0 by lia. reflexivity. }
rewrite (rd_ok (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) P)) 4) by lia.
destruct (Z_lt_le_dec (Z.of_nat (length (skipn (Z.to_nat 4) (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) P))))) 4) as [H4|H4].
{ rewrite (rd_short _ 4 H4), !R0 by lia. reflexivity. }
rewrite (rd_ok (skipn (Z.to_nat 4) (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) P))) 4) by lia.
destruct (Z_lt_le_dec (Z.of_nat (length (skipn (Z.to_nat 4) (skipn (Z.to_nat 4) (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) P)))))) 2) as [H5|H5].
{ rewrite (rd_short _ 2 H5). reflexivity. }
exfalso. rewrite !length_skipn in H5. change (Z.to_nat 4) with 4%nat in H5. change (Z.to_nat 2) with 2%nat in H5. lia.
Qed.
Lemma ff_cfg_hdr_short : forall P, fst (fst (hdr5 P)) = true -> ff_cfg P = None.
Proof.
intros P HP. unfold ff_cfg. destruct (hdr5 P) as [[e [[[[W H] attr] gen] ngp]] s5]. cbn [fst] in HP. subst e.
destruct (if YO07.flag attr 4 then (false, [], s5) else YO07.rd s5 (ngp * 3)) as [[e6 gp] s6]. reflexivity.
Qed.
Lemma ff_cfg_pal_short : forall P W H attr gen ngp,
hdr5 P = (false, (W, H, attr, gen, ngp), skipn 14 P) -> Z.land attr 4 = 0 ->
14 <= Z.of_nat (length P) -> Z.of_nat (length P) < 14 + 3 * ngp -> ff_cfg P = None.
Proof.
intros P W H attr gen ngp Hh Ha Hl Hs. unfold ff_cfg. rewrite Hh. unfold YO07.flag. rewrite (proj2 (Z.eqb_eq _ _) Ha). cbn [negb].
rewrite rd_short by (rewrite length_skipn; lia). reflexivity.
Qed.
Lemma ff_cfg_too_large : forall P W H attr gen ngp,
hdr5 P = (false, (W, H, attr, gen, ngp), skipn 14 P) -> 100000000 < W * H -> ff_cfg P = None.
Proof.
intros P W H attr gen ngp Hh HWH. unfold ff_cfg. rewrite Hh.
destruct (if YO07.flag attr 4 then (false, [], skipn 14 P) else YO07.rd (skipn 14 P) (ngp * 3)) as [[e6 gp] s6].
destruct e6; [reflexivity|]. cbn [orb]. destruct (Z.ltb_spec 100000000 (W * H)); [reflexivity | lia].
Qed.
Lemma land4_mod32_any : forall x, Z.land (x mod 2 ^ 32) 4 = Z.land x 4.
Proof.
intros x. apply Z.bits_inj'. intros i Hi.
rewrite !Z.land_spec. destruct (Z.ltb_spec i 32) as [Hl|Hl].
- rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 4 i) with false; [rewrite !Bool.andb_false_r; reflexivity|].
symmetry. apply Z.bits_above_log2; [lia|]. cbn. lia.
Qed.
Lemma zbytes_nth_range : forall pl j, 0 <= nth j (zbytes pl) 0 < 256.
Proof.
intros pl j. unfold zbytes. destruct (nth_in_or_default j (map (fun b : byte => bv_unsigned b) pl) 0) as [Hin | ->]; [| lia].
apply in_map_iff in Hin as (b & Hb & _). rewrite <- Hb.
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Lemma rt_from_mono : forall B MT FP (P Q : rtcx -> world tfibsegs -> config -> Prop) ss INV,
(forall cx W c, rt_base B MT cx -> P cx W c -> Q cx W c) ->
rt_from B MT FP P ss INV -> rt_from B MT FP Q ss INV.
Proof.
intros B MT FP P Q ss INV HPQ HR cx E k acc ly3 S3 W3 ms3 md3 HB HE HJ Hfr HM HI HS.
eapply SRr_mono; [exact (HR cx E k acc ly3 S3 W3 ms3 md3 HB HE HJ Hfr HM HI HS)|].
intros W' c' _ HP. exact (HPQ cx W' c' HB HP).
Qed.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM2 : astack_malloc_realizes tfibsegs B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet A_asan_memset.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy A_asan_memcpy.
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B MT.
Hypothesis AFREE4 : afree04_rule tfibsegs B MT.
Hypothesis AFREEN4 : afree_null04_rule tfibsegs B MT.
Hypothesis AIL : asink_img_laws tfibsegs B tfib_K.
Variable XN : xnums.
Variable XL : Z -> Z.
Variables (wfn rlo rhi : Z).
Hypothesis TNEWGIFX : tnewgif_x tfibsegs tfib_K B MT XN A_cgif_newgif CTX_cgif_newgif wfn rlo rhi.
Hypothesis AUNLINKX : aunlink_x tfibsegs B tfib_K 0x9c9cc.
Hypothesis XNpos : forall n, 0 <= n -> 0 <= xm_newgif XN n.
Hypothesis XNle : forall n, 0 <= n -> 0 <= xn_newgif XN n <= xm_newgif XN n.
Hypothesis HRO : forall rd, arodata_ok B rd -> arodata_okP tfibsegs rlo rhi B rd.
Hypothesis TADDFX : taddframe_specX tfibsegs tfib_K B MT XN A_cgif_addframe CTX_cgif_addframe wfn rlo rhi.
Hypothesis TCLOSEX : tclose_specX tfibsegs tfib_K B MT XN A_cgif_close CTX_cgif_close wfn rlo rhi.
Hypothesis XApos : forall n, 0 <= n -> 0 <= xn_addframe XN n <= xm_addframe XN n.
Hypothesis XCpos : forall n, 0 <= n -> 0 <= xn_close XN n <= xm_close XN n.
Hypothesis HXL : forall n ngp, 0 <= ngp < 2 ^ 16 -> RT_NEED1 MT + xm_newgif XN ngp + mo_free MT <= XL n.
Hypothesis HXL2 : forall n ngp N, 0 <= ngp < 2 ^ 16 -> 1 <= N <= 100000000 ->
RT_NEED1 MT + xn_newgif XN ngp + mo_free MT + 15 * (RFC_COST MT N + xn_addframe XN N + (mo_free MT + mo_free MT)) + RFC_COST MT N + xm_addframe XN N <= XL n /\
RT_NEED1 MT + xn_newgif XN ngp + mo_free MT + 16 * (RFC_COST MT N + xn_addframe XN N + (mo_free MT + mo_free MT)) + RFC_COST MT N + xm_close XN N <= XL n.
Definition POSTX1 (cx : rtcx) : world tfibsegs -> config -> Prop :=
fun W' c' => AI tfibsegs (w_H W') (w_A W') (cfg_model c') ->
forall (pl : list byte) (aM : Z) (Kl : lleaf -> TSet),
rt_xbase B MT XL cx pl aM Kl ->
srealizes tfibsegs c' (aff_tree Kl (m_fs (c_md cx)) (zbytes pl)).
Lemma TRFCX : trfc_specX B MT.
Proof. exact (tfib_read_frameconfigX B TL LAWS MT MTL AMALLOC4 AFREE4 AFREEN4 AMEMCPY AMEMSET). Qed.
Lemma ff_cfg_ngp : forall pl G loops rest, ff_cfg (zbytes pl) = Some (G, loops, rest) -> 0 <= YO07.g_ngp G < 2 ^ 16.
Proof.
intros pl G loops rest H.
destruct (Nat.lt_ge_cases (length (zbytes pl)) 14) as [Hs | Hl].
{ rewrite (ff_cfg_hdr_short (zbytes pl) (hdr5_short (zbytes pl) ltac:(clear - Hs; lia))) in H. discriminate H. }
unfold ff_cfg in H. rewrite (hdr5_bytes (zbytes pl) Hl) in H.
destruct (if YO07.flag _ 4 then _ else _) as [[e6 gpal] s6]. cbn [orb] in H.
destruct e6; [discriminate H|]. destruct (100000000 <? _); [discriminate H|].
injection H as <- _ _. cbn [YO07.g_ngp].
pose proof (zbytes_nth_range pl 12) as R12. pose proof (zbytes_nth_range pl 13) as R13. clear - R12 R13. lia.
Qed.
Lemma HXL2x : forall cx xc, rt_base B MT cx -> rt_xbase2 B MT XL cx xc -> XROOM MT XN xc (c_T cx).
Proof.
intros cx [pl aM Kl G rest0 g f N] HB ((Hnpl & _ & _ & _ & _ & _ & _ & HTX) & HCFG & _ & _ & HNG & HN1 & _). cbn [x_pl x_aM x_K x_G x_rest x_gp x_f x_N] in *.
unfold XROOM, ACC_H, ACC_G, ACC_F, ITER. cbn [x_G x_N]. rewrite HTX.
pose proof (HXL2 (c_n cx) (YO07.g_ngp G) N (ff_cfg_ngp pl G 0 rest0 HCFG) HN1) as [H1 H2]. split; [clear - H1; lia | clear - H2; lia].
Qed.
Ltac xhyps := first [exact HXL2x | exact TRFCX | eassumption].
Lemma RU : rt_fromX B MT XL PTF ss_U (fun cx xc => INV_U B (fsFIN cx xc) cx xc).
Proof. intros cx xc. eapply (lx_U B MT MTL TL LAWS ML ASF FFL MTF XL wfn AIL AUNLINKX (fsFIN cx xc) cx xc). Qed.
Lemma RH : rt_fromX B MT XL PTF ss_H (INV_HX B MT XN wfn).
Proof. eapply rt_HX; first [exact RU | xhyps]. Qed.
Lemma rt_G_allX : forall (m : nat) (c : Z), c <= Z.of_nat m -> rt_fromX B MT XL PTF ss_G (INV_G1X B MT XN wfn c).
Proof.
induction m as [|m IH]; intros c Hcm.
- intros cx xc E k acc ly3 S3 W3 ms3 md3 _ _ _ _ _ _ HINV _. destruct HINV as (_ & _ & Hc & _). exfalso. clear - Hc Hcm. cbn in Hcm. lia.
- eapply rt_G1X; [xhyps .. |]. eapply rt_G2X; [xhyps .. |]. eapply rt_G3X; [xhyps .. | exact RH |].
apply IH. rewrite Nat2Z.inj_succ in Hcm. clear - Hcm. lia.
Qed.
Lemma RF : rt_fromX B MT XL PTF ss_F (INV_FX B MT XN wfn).
Proof. eapply rt_FX; [xhyps .. | exact RH | apply (rt_G_allX 16 16); cbn; lia]. Qed.
Lemma hdr_fail_cfg_none : forall cx pl,
garr8 tfibsegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx) (zbytes pl) -> c_n cx = Z.of_nat (length pl) ->
hdr_fail cx -> ff_cfg (zbytes pl) = None.
Proof.
intros cx pl HG Hn HF.
assert (Hlz : length (zbytes pl) = length pl) by (unfold zbytes; apply length_map).
destruct (Z_lt_le_dec (c_n cx) 14) as [Hs|Hl].
{ apply ff_cfg_hdr_short. apply hdr5_short. rewrite Hlz. lia. }
destruct HF as [Hs | (attr & gen & w16 & h16 & ngp & Hprov & Hwhy)]; [exfalso; lia|].
pose proof (hdr_prov_hdr5 cx pl attr gen w16 h16 ngp HG Hprov ltac:(lia)) as Hh.
destruct Hwhy as [[Ha Hshort] | Hbig].
- eapply ff_cfg_pal_short; [exact Hh | rewrite land4_mod32_any; exact Ha | rewrite Hlz; lia | rewrite Hlz; lia].
- eapply ff_cfg_too_large; [exact Hh | exact Hbig].
Qed.
Lemma lx_leaf_fail : forall cx W' c', rt_base B MT cx -> rt_post B MT [] cx W' c' -> POSTX1 cx W' c'.
Proof.
intros cx W' c' HB HP HAI pl aM Kl (Hnpl & HPL & HSNK0 & HFD0 & HSORT0 & HAM0 & HLEAF & HTX).
destruct HP as (ly' & S' & regs' & mem' & md' & k' & -> & HJ & Hk & HPR & Ha0 & HPerm & HMLE & HF).
unfold aff_tree. rewrite (hdr_fail_cfg_none cx pl HPL Hnpl HF). unfold ff_leaf.
destruct (ajournal_nil_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efds Efs].
apply (HLEAF (LL 0 (m_fs (c_md cx)) []) W').
{ pose proof HJ as (_ & _ & _ & Hwle & _). exact Hwle. }
{ exact HAI. }
exists ly', S', regs', mem', md', k'. split; [reflexivity|].
unfold tfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
pose proof HB as (HPRE & Hra & Hp & Hn & Hpn & _). pose proof (proj1 HPRE) as HAR.
assert (HSNK' : asink_none tfibsegs tfib_K (mrestrict (w_H W') mem') md').
{ eapply (asink_none_kept tfibsegs B tfib_K AIL); [exact HJ | intros Ho; exact (sink_closed_nil Ho) | exact HSNK0]. }
split; [apply ajournal_fp_nil; exact HJ|]. split; [exact Hk|]. split; [exact HPR|]. split; [exact Ha0|].
split; [exact HPerm|].
split; [intros fd; rewrite Efds; reflexivity|].
split; [exact Efs|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT0|].
split; [exact HSNK'|].
split; [exact (ameta_inv_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAM0)|].
split; [rewrite <- HTX; exact HMLE|].
intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hi Hn0; lia|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 (c_p cx) (c_n cx) i Hpin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. exact Hpin.
- unfold req_size. destruct (Z.eqb_spec (c_n cx) 0) as [Heq0|Hne0]; [exfalso; clear - Hnpos Heq0; lia | exact Hi].
- apply inFP_nil.
Qed.
Lemma lx_RX : rt_from B MT [] POSTX1 ss_X (INV_X B MT).
Proof. exact (rt_from_mono B MT [] _ _ ss_X (INV_X B MT) lx_leaf_fail (rt_X B MT [] MTL TL LAWS ML ASF FFL MTF)). Qed.
Lemma lx_RE : rt_from B MT [] POSTX1 ss_E (INV_E B MT []).
Proof.
intros cx E k acc ly3 S3 W3 ms3 md3 HB HE HJ Hfr HM HI HS. apply SRr_ret.
intros HAI pl aM Kl HXB.
eapply (lx_E B MT MTL TL LAWS ML ASF FFL MTF XN XL wfn rlo rhi AFREE4 AFREEN4 AIL TNEWGIFX AUNLINKX XNpos XNle HRO RF
cx E k acc ly3 S3 W3 ms3 md3 HB HE HJ Hfr HM HI HS pl aM Kl HAI HXB).
pose proof HI as (_ & Hacc & _). pose proof HXB as (Hnpl & _ & _ & _ & _ & _ & _ & HTX). rewrite HTX.
pose proof (zbytes_nth_range pl 12) as R12. pose proof (zbytes_nth_range pl 13) as R13.
pose proof (HXL (c_n cx) (hdr_ngp (zbytes pl)) ltac:(unfold hdr_ngp; lia)) as HX.
unfold RT_NEED1 in HX. pose proof (mo_free_nonneg MT MTL) as HF0. clear - Hacc HX HF0. lia.
Qed.
Lemma lx_RA2 : rt_from B MT [] POSTX1 ss_A2 (INV_0 B MT 0).
Proof.
pose proof lx_RX as RX. pose proof lx_RE as RE.
assert (RDX : rt_from B MT [] POSTX1 ss_Dx (INV_Dx B MT [])) by (eapply rt_Dx; first [eassumption | reflexivity]).
assert (RD : rt_from B MT [] POSTX1 ss_D (INV_D B MT [])) by (eapply rt_D; first [eassumption | reflexivity]).
assert (RC : rt_from B MT [] POSTX1 ss_C (INV_C B MT)) by (eapply rt_C; first [eassumption | reflexivity]).
assert (RB1 : rt_from B MT [] POSTX1 ss_B (INV_0 B MT 0)) by (eapply rt_B; first [eassumption | reflexivity]).
eapply rt_A2; first [eassumption | reflexivity].
Qed.
Theorem tfib_lib_x_body :
forall ly S (W : world tfibsegs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI tfibsegs (w_H W) (w_A W) md ->
tfib_lib_pre_x B MT XL 0x9da38 0x9eca8 regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world tfibsegs) (c' : config),
wle W W' -> AI tfibsegs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
tfib_lib_post_x B MT XL regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes tfibsegs c' (K l)) ->
srealizes tfibsegs (cfg_at tfibsegs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
Proof.
intros ly S W regs mem md p n pl M K HAI HPRE HK.
change (LIBK pl (m_fs md) K) with (aff_tree K (m_fs md) (zbytes pl)).
destruct HPRE as (HPRE0 & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK & HFD & HSORT & HAM & HMOK).
assert (HROD : arodata_ok B (aview tfibsegs (w_H W) mem)) by (intros a Ha; apply (HROS a); exact Ha).
assert (HNEED : RT_NEED1 MT <= XL n).
{ pose proof (HXL n 0 ltac:(lia)) as HX. pose proof (XNpos 0 ltac:(lia)) as H0. pose proof (mo_free_nonneg MT MTL) as H1. lia. }
apply (srz_enter tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md) _ HAI).
eapply SRr_mono.
{ exact (tfib_lib_A_seg B MT MTL TL LAWS ML ASM2 SMP FFL MTF [] POSTX1 lx_RA2 ly S W regs mem md p n (XL n)
HPRE0 Hra Hp Hn Hpn Hfr0 Hev Hlive HROD HMOK HNEED). }
intros W' c' Hwle (fpos & sp1 & E0 & HPOST) HAI'.
apply (HPOST HAI' pl M K).
split; [exact Hnpl|]. split; [exact HPL|]. split; [exact HSNK|]. split; [exact HFD|]. split; [exact HSORT|]. split; [exact HAM|].
split; [|reflexivity].
intros l W'' c'' Hwle'' HAI'' Hex. exact (HK l W'' c'' Hwle'' HAI'' Hex).
Qed.
Theorem tfib_lib_x : tfib_lib_contract_x B MT XL XL 0x9da38 0x9eca8.
Proof. exact tfib_lib_x_body. Qed.
End h.
End d.
