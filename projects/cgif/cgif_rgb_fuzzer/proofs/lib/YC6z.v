(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YG0f YC04 YC07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z
YC53.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP15 YC6e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n YC6o YC6p YC6q YC6r YC6u YC77 YC78 YC79 YC6x YC6y.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Hypothesis Hs1 : s1v = sp0 - 512.
Hypothesis HSTK : 512 <= STK.
Hypothesis Hsp32 : sp0 mod 32 = 0.
Hypothesis HOP : hk_opaque_ok hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN : 1 <= N <= 10000.
Hypothesis HimgP : In (img, fmt * N) PROT.
Hypothesis Himgl : zlen imgl = fmt * N.
Local Notation hcore_raw := (hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation hcore := (hcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_BC := (at_BC B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_BR := (at_BR B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_PA := (at_PA B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HRS := (hcore_run_same B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation FRAMEF := (hk_frame_facts B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hs1 HSTK Hsp32).
Local Notation IMGF := (hk_img_facts B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hfmt HN HimgP).
Local Notation at_M1C := (at_M1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RT := (at_RT B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HSTEP := (hcore_raw_step B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation OTHERK := (hk_tbl_other_kept B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M1R := (at_M1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M2C := (at_M2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M2R := (at_M2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HRRS := (hcore_raw_run_same B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation APARTN := (hk_tbl_apart_nth B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation pxc := (pxc fmt imgl).
Local Notation at_RA1C := (at_RA1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RA1R := (at_RA1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RA2C := (at_RA2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RA2R := (at_RA2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA1C := (at_MA1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA1R := (at_MA1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA2C := (at_MA2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA2R := (at_MA2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA3C := (at_MA3C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA3R := (at_MA3R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_FAIL := (at_FAIL B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MSC := (at_MSC B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rh_pre := (rh_pre B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rz_common := (rz_common B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rcore := (rcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rz_old := (rz_old).
Local Notation hspill := (hspill s1v).
Local Notation slot_is := (slot_is s1v).
Local Notation rh_slots := (rh_slots s1v).
Local Notation at_MSR := (at_MSR B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_LH := (at_LH B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rh_common := (rh_common B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Hypothesis AMEMSET : aintrin_realizes trasegs B OSet A_asan_memset.
Local Notation cfgat regs pc mem md := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom trasegs)) md).
Hypothesis TL : TraLib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AREALLOC : arealloc_realizes trasegs B 0x53108 0x53640.
Variable ch0 : list (Z * Z * Z).
Hypothesis HSTKA : 512 + ASTACK <= STK.
Hypothesis Htop32 : sp0 + 32 <= ly_top ly.
Hypothesis HCH0 : achain ly (aview trasegs (w_H W0) mem0) sp0 s0v ch0.
Hypothesis Hrav : rav = 0x81368.
Hypothesis Hspine : spine ch0 = [] \/ spine ch0 = [0x80ea8].
Hypothesis HEV : vev S + 80 <= VEV_MAX.
Hypothesis HLIVE : bsum PROT + 2 ^ 30 <= LIVE_MAX.
Local Notation hk_ch := (hk_ch sp0 rav s0v ch0).
Lemma hk_memset_call : forall lyc Sc W (regs : bvmap 5 word) mem md k (d v n : Z) (raw : word) bd nd,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 v -> getr regs 12 = Z_to_bv 64 n -> 0 < n < 2 ^ 32 ->
getr regs 2 = Z_to_bv 64 s1v -> getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 (as_tp B) ->
getr regs 1 = raw -> YK0s.ret_ok raw ->
In (bd, nd) (ablocks B lyc Sc) -> bd <= d -> d + n <= bd + req_size nd ->
(forall blc lyq ownq i, In (bd, nd) blc -> 0 <= i < req_size nd -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (bd + i)) ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 A_asan_memset) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom trasegs)) md2 /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
aregs_preserved regs regs2 /\
(forall i, 0 <= i < n -> aview trasegs (w_H W) mem2 (d + i) = Some (v mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (alloc_ceiling <= a < s1v) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem a)).
Proof.
intros lyc Sc W regs mem md k d v n raw bd nd HJ G10 G11 G12 Hn G2 G3 G4 Gra Hraw Hbd Hd0 Hd1 Hperm.
pose proof tra_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W mem md bd nd HAR Hbd) as (_ & Hd4096 & Hdceil & _ & Hdpres & _).
assert (Usp : spZ regs = sp0 + -512).
{ unfold spZ. rewrite G2, unsigned_lit_small by (rewrite Hs1; clear - Hceil Hslo Hshi H47 C1 HSTKA Has; lia). rewrite Hs1. lia. }
eapply SRr_mono.
{ eapply (aj_intrin_at trasegs B LAWS Hsegs OSet A_asan_memset AMEMSET W regs mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc md k d v n (-512) raw HJ G10 G11 G12).
- clear - Hn; lia.
- clear - Hd4096 Hd0; lia.
- clear - Hd1 Hdceil C1; lia.
- exact Usp.
- reflexivity.
- clear; lia.
- clear - HSTKA Hes Has; lia.
- exact G3.
- exact G4.
- exact Gra.
- exact Hraw.
- intros a Ha. split.
+ replace a with (bd + (a - bd)) by lia. apply Hperm; [exact Hbd | clear - Ha Hd0 Hd1; lia].
+ rewrite Hes. clear - Ha Hd1 Hdceil Hceil Hslo HSTKA Hes Has. lia.
- apply (amem_range_of_block trasegs B LAWS lyc Sc W mem md bd nd _ _ HAR Hbd); assumption.
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md bd nd _ _ HAR Hbd); assumption.
- intros Hn0. apply (shadow_hull_vis_of_block trasegs B LAWS lyc Sc W mem md bd nd _ _ HAR Hbd); assumption.
- exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset & Hout2 & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split; [exact Hset|].
intros a Ha Hnd Hn'. apply Hout2; [exact Ha | exact Hnd|]. rewrite Hes, Hs1 in *. clear - Hn' Hceil Hslo HSTKA Hes Has. lia.
Qed.
Lemma rh_BL_nth : forall C p1 x1 h1 u1 f1,
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 0 = Some (tb, CHT_SIZE) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 1 = Some (ac_f C, 4 * ac_T C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 2 = Some (ac_h C, 3 * ac_T C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 3 = Some (ac_u C, ac_T C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 4 = Some (p1, 3 * ac_Tn C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 5 = Some (x1, 4 * ac_Tn C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 6 = Some (h1, 3 * ac_Tn C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 7 = Some (u1, ac_Tn C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 8 = Some (f1, 4 * ac_Tn C).
Proof. intros. repeat split. Qed.
Lemma rh_apart : forall lyc Sc W regs mem md k cells C p1 x1 h1 u1 f1 (p q : nat) x y,
rcore lyc Sc W regs mem md k cells (rh_BL C p1 x1 h1 u1 f1) ->
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) p = Some x -> nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some y -> p <> q ->
fst x + req_size (snd x) <= fst y \/ fst y + req_size (snd y) <= fst x.
Proof.
intros lyc Sc W regs mem md k cells C p1 x1 h1 u1 f1 p q x y HC Hp Hq Hne.
pose proof HC as (HJ & _ & _ & _ & _ & HPerm & _). pose proof (proj1 HJ) as HAR.
eapply rperm_apart_nth with (L := (tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) (p := p) (q := q); eassumption.
Qed.
Lemma rh_old_apart : forall lyc Sc W regs mem md k cells C p1 x1 h1 u1 f1 (q : nat) y a,
rcore lyc Sc W regs mem md k cells (rh_BL C p1 x1 h1 u1 f1) -> In (ac_T C) ts_chain -> ac_T C < MAX_TABLE_SIZE ->
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some y -> (1 <= q <= 3)%nat -> fst y <= a < fst y + req_size (snd y) ->
~ (tb <= a < tb + 48) /\ ~ rh_innew C p1 x1 h1 u1 f1 a.
Proof.
intros lyc Sc W regs mem md k cells C p1 x1 h1 u1 f1 q y a HC HTc HTlt Hq Hrng Ha.
destruct (rh_BL_nth C p1 x1 h1 u1 f1) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
pose proof (rh_apart _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 q 0%nat y _ HC Hq N0 ltac:(lia)) as A0.
pose proof (rh_apart _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 q 4%nat y _ HC Hq N4 ltac:(lia)) as A4.
pose proof (rh_apart _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 q 5%nat y _ HC Hq N5 ltac:(lia)) as A5.
pose proof (rh_apart _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 q 6%nat y _ HC Hq N6 ltac:(lia)) as A6.
pose proof (rh_apart _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 q 7%nat y _ HC Hq N7 ltac:(lia)) as A7.
pose proof (rh_apart _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 q 8%nat y _ HC Hq N8 ltac:(lia)) as A8.
cbn [fst snd] in A0, A4, A5, A6, A7, A8. change (req_size CHT_SIZE) with 48 in A0.
split; [clear - A0 Ha; lia|]. unfold rh_innew. clear - A4 A5 A6 A7 A8 Ha. lia.
Qed.
Lemma rh_pre_step : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 cnt cnt' regs' mem' md',
rh_pre lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 cnt ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
(forall r, In r HK_CONST -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (alloc_ceiling <= a < s1v) -> ~ (tb <= a < tb + 48) -> ~ rh_innew C p1 x1 h1 u1 f1 a ->
aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
hspill W mem' i ha -> rh_slots W mem' C h1 u1 f1 ->
obj_at trasegs (mrestrict (w_H W) mem') tb LAY_Cht (rh_cells C p1 x1 cnt') ->
rh_pre lyc Sc W regs' mem' md' k C i ha p1 x1 h1 u1 f1 cnt'.
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 cnt cnt' regs' mem' md' (HC & (Af & Ah & Au) & HF & Hk & _ & _ & Hptrs) HJ' Hregs KM Hsp Hsl' Hobj'.
pose proof HF as (Hinv & HTc & HTlt & _). pose proof Hinv as ((L1 & L2 & L3 & _) & _).
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3).
pose proof HC as (HJ & _ & _ & Hobj & _ & HPerm & _). pose proof (proj1 HJ) as HAR.
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
destruct (rh_BL_nth C p1 x1 h1 u1 f1) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
assert (Hold : forall (q : nat) y, nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some y -> (1 <= q <= 3)%nat ->
rg_blk_kept (w_H W) (w_H W) mem mem' (fst y) (req_size (snd y))).
{ intros q [yb yn] Hq Hrng j Hj. cbn [fst snd] in *.
assert (Hin' : In (yb, yn) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; exact (nth_error_In _ _ Hq)).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md yb yn HAR Hin' Fceil) as (Hb0 & Hb1 & Hb2 & Hb3).
destruct (rh_old_apart _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 q (yb, yn) (yb + j) HC HTc HTlt Hq Hrng ltac:(cbn [fst snd]; clear - Hj; lia)) as [Hnt Hnn].
apply KM; [clear - Hj Hb0 Hb1 F47; lia | clear - Hj Hb1; lia | clear - Hj Hb1 Fceil Hb2; lia | exact Hnt | exact Hnn]. }
split.
{ eapply rcore_run with (regs := regs) (mem := mem) (md := md) (cells := rh_cells C p1 x1 cnt); try eassumption.
intros a Ha H1 H2 Hnb. apply KM; [exact Ha | exact H1 | exact H2 | |].
- intros Hx. apply Hnb. exists tb, CHT_SIZE. split; [left; reflexivity | change (req_size CHT_SIZE) with 48; exact Hx].
- intros Hx. apply Hnb. unfold rh_innew in Hx.
destruct Hx as [Hx | [Hx | [Hx | [Hx | Hx]]]]; [exists p1, (3 * ac_Tn C) | exists x1, (4 * ac_Tn C) | exists h1, (3 * ac_Tn C) | exists u1, (ac_Tn C) | exists f1, (4 * ac_Tn C)];
(split; [right; unfold rh_BL; cbn; tauto | exact Hx]). }
split.
{ unfold ac_T in *. split; [|split].
- apply (arr32_frame trasegs _ _ _ _ Af). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L3 in Ha.
pose proof (req_size_pos (4 * ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_f C + (a - ac_f C)) by lia. apply (Hold 1%nat _ N1 ltac:(lia)). cbn [fst snd]. unfold ac_T. clear - Ha Hrq. lia.
- apply (arr8_frame trasegs _ _ _ _ Ah). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L2 in Ha.
pose proof (req_size_pos (3 * ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_h C + (a - ac_h C)) by lia. apply (Hold 2%nat _ N2 ltac:(lia)). cbn [fst snd]. unfold ac_T. clear - Ha Hrq. lia.
- apply (arr8_frame trasegs _ _ _ _ Au). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L1 in Ha.
pose proof (req_size_pos (ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_u C + (a - ac_u C)) by lia. apply (Hold 3%nat _ N3 ltac:(lia)). cbn [fst snd]. unfold ac_T. clear - Ha Hrq. lia. }
split; [exact HF|]. split; [exact Hk|]. split; [exact Hsp|]. split; [exact Hsl' | exact Hptrs].
Qed.
Lemma rh_blocks_same : forall lyc Sc W regs mem md k cells C p1 x1 h1 u1 f1 (mem' : word -> option byte),
rcore lyc Sc W regs mem md k cells (rh_BL C p1 x1 h1 u1 f1) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
forall (q : nat) b n, nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some (b, n) -> rg_blk_kept (w_H W) (w_H W) mem mem' b (req_size n).
Proof.
intros lyc Sc W regs mem md k cells C p1 x1 h1 u1 f1 mem' HC KM q b n Hq j Hj.
pose proof HC as (HJ & _ & _ & _ & _ & HPerm & _). pose proof (proj1 HJ) as HAR.
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
assert (Hin' : In (b, n) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; exact (nth_error_In _ _ Hq)).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md b n HAR Hin' Fceil) as (Hb0 & Hb1 & Hb2 & Hb3).
apply KM; [clear - Hj Hb0 Hb1 F47; lia | intros [Hx _]; clear - Hx Hj Hb1; lia].
Qed.
Lemma rh_new_kept : forall (W : world trasegs) (mem mem' : word -> option byte) C p1 x1 h1 u1 f1 K,
rh_new W mem C p1 x1 h1 u1 f1 K -> 0 <= ac_Tn C ->
rg_blk_kept (w_H W) (w_H W) mem mem' p1 (req_size (3 * ac_Tn C)) -> rg_blk_kept (w_H W) (w_H W) mem mem' x1 (req_size (4 * ac_Tn C)) ->
rg_blk_kept (w_H W) (w_H W) mem mem' h1 (req_size (3 * ac_Tn C)) -> rg_blk_kept (w_H W) (w_H W) mem mem' u1 (req_size (ac_Tn C)) ->
rg_blk_kept (w_H W) (w_H W) mem mem' f1 (req_size (4 * ac_Tn C)) ->
rh_new W mem' C p1 x1 h1 u1 f1 K.
Proof.
intros W mem mem' C p1 x1 h1 u1 f1 K ((Af & Ah & Au & Ap & Ax) & Hlens & HTK) HTn Kp Kx Kh Ku Kf.
pose proof Hlens as (L1 & L2 & L3 & L4 & L5). rewrite HTK in L1, L2, L3, L4, L5.
pose proof (req_size_pos (ac_Tn C) HTn) as [_ Hr1]. pose proof (req_size_pos (3 * ac_Tn C) ltac:(lia)) as [_ Hr3]. pose proof (req_size_pos (4 * ac_Tn C) ltac:(lia)) as [_ Hr4].
split; [|split; assumption].
split; [apply (arr32_frame trasegs _ _ _ _ Af); intros a Ha; apply (mbyte_of_aview trasegs); rewrite L3 in Ha; replace a with (f1 + (a - f1)) by lia; apply Kf; clear - Ha Hr4; lia|].
split; [apply (arr8_frame trasegs _ _ _ _ Ah); intros a Ha; apply (mbyte_of_aview trasegs); rewrite L2 in Ha; replace a with (h1 + (a - h1)) by lia; apply Kh; clear - Ha Hr3; lia|].
split; [apply (arr8_frame trasegs _ _ _ _ Au); intros a Ha; apply (mbyte_of_aview trasegs); rewrite L1 in Ha; replace a with (u1 + (a - u1)) by lia; apply Ku; clear - Ha Hr1; lia|].
split; [apply (arr8_frame trasegs _ _ _ _ Ap); intros a Ha; apply (mbyte_of_aview trasegs); rewrite L5 in Ha; replace a with (p1 + (a - p1)) by lia; apply Kp; clear - Ha Hr3; lia|].
apply (arr32_frame trasegs _ _ _ _ Ax); intros a Ha; apply (mbyte_of_aview trasegs); rewrite L4 in Ha; replace a with (x1 + (a - x1)) by lia; apply Kx; clear - Ha Hr4; lia.
Qed.
Lemma rh_common_run_same : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K regs' mem' md',
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
(forall r, In r HK_CONST -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
hspill W mem' i ha -> rh_slots W mem' C h1 u1 f1 ->
rh_common lyc Sc W regs' mem' md' k C i ha p1 x1 h1 u1 f1 K.
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K regs' mem' md' [HP HNw] HJ' Hregs KM Hsp Hsl.
pose proof HP as (HC & _ & (_ & HTc & HTlt & _) & _). pose proof HC as (_ & _ & _ & Hobj & _).
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & _). fold (ac_Tn C) in Tn1, Tn2.
destruct (rh_BL_nth C p1 x1 h1 u1 f1) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
pose proof (rh_blocks_same _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 mem' HC KM) as Hlow.
split.
- apply (rh_pre_step lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 _ _ regs' mem' md' HP HJ' Hregs); [intros a Ha H1 _ _ _; exact (KM a Ha H1) | exact Hsp | exact Hsl|].
apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem mem' tb LAY_Cht _ 48 Hobj lay_inside_Cht). exact (Hlow 0%nat _ _ N0).
- apply (rh_new_kept W mem mem' C p1 x1 h1 u1 f1 K HNw ltac:(clear - Tn2; lia)); [exact (Hlow 4%nat _ _ N4) | exact (Hlow 5%nat _ _ N5) | exact (Hlow 6%nat _ _ N6) | exact (Hlow 7%nat _ _ N7) | exact (Hlow 8%nat _ _ N8)].
Qed.
Lemma mbyte_of_apresent : forall H (m : word -> option byte) a, apresent H m a -> exists b, mbyte trasegs (mrestrict H m) a = Some b.
Proof.
intros H m a HP. destruct (mbyte trasegs (mrestrict H m) a) as [b|] eqn:Eb; [exists b; reflexivity|].
exfalso. apply (aview_some_of_apresent trasegs H m a HP). unfold aview. rewrite Eb. reflexivity.
Qed.
Lemma saved_20_21 : acallee_saved 20 /\ acallee_saved 21.
Proof. split; unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate. Qed.
Lemma hl_ms : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_MSC lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 ->
SRr trasegs W (cfgat regs A_asan_memset mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_MSR mem2 md2 /\ at_MSR lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (HP & G10 & G11 & G12 & Gra & G20 & G21).
pose proof HP as (HC & Hold & HF & Hk & [SP72 SP56] & (S160 & S168 & S176 & S296) & Pp & Px & Ph & Pu & Pf).
pose proof HF as (Hinv & HTc & HTlt & _).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept). pose proof (proj1 HJ) as HAR.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
destruct (rh_BL_nth C p1 x1 h1 u1 f1) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
assert (Huin : In (u1, ac_Tn C) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; exact (nth_error_In _ _ N7)).
pose proof (req_size_pos (ac_Tn C) ltac:(clear - Tn2; lia)) as [_ HrqU].
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md u1 (ac_Tn C) HAR Huin Fceil) as (Hu0 & Hu1 & Hu2 & Hu3).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
eapply SRr_mono.
{ eapply (hk_memset_call lyc Sc W regs mem md k u1 0 (ac_Tn C) (Z_to_bv 64 HL_MSR) u1 (ac_Tn C) HJ G10 G11 G12); try eassumption.
- clear - Tn2. lia.
- apply YK0s.ret_ok_even. rewrite unsigned_lit_small by (unfold HL_MSR; clear; lia). reflexivity.
- clear; lia.
- clear - HrqU; lia.
- exact (proj2 (Hperm u1 (ac_Tn C) ltac:(exact (nth_error_In _ _ N7)))). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hset & Hout).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
assert (Hfr : forall a, s1v <= a < s1v + 512 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem a).
{ intros a Ha. apply Hout; [clear - Ha Fceil F47 C1; lia | clear - Ha Hu1 HrqU; lia | clear - Ha; lia]. }
destruct saved_20_21 as [Sv20 Sv21].
split; [|split; [intros j Hj; exact (Hset j Hj)|]; rewrite (aregs_get regs regs2 20%bv HP2 Sv20), (aregs_get regs regs2 21%bv HP2 Sv21); split; [exact G20 | exact G21]].
apply (rh_pre_step lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 _ _ regs2 mem2 md2 HP HJ2).
- intros r Hr. apply (aregs_get regs regs2 r HP2). apply hk_const_saved. exact Hr.
- intros a Ha H1 H2 H3 H4. apply Hout; [exact Ha | | exact H2]. intros Hx. apply H4. unfold rh_innew. right. right. right. left. clear - Hx HrqU. lia.
- split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia | eapply slot_kept with (W := W) (mem := mem); try eassumption; lia].
- split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia|].
split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia|].
split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia | eapply slot_kept with (W := W) (mem := mem); try eassumption; lia].
- apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem mem2 tb LAY_Cht _ 48 Hobj lay_inside_Cht). intros j Hj.
pose proof (rh_apart _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 0%nat 7%nat _ _ HC N0 N7 ltac:(lia)) as A07. cbn [fst snd] in A07. change (req_size CHT_SIZE) with 48 in A07.
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md tb CHT_SIZE HAR Htbin Fceil) as (Ht0 & Ht1 & Ht2 & Ht3). change (req_size CHT_SIZE) with 48 in Ht1, Ht2.
apply Hout; [clear - Hj Ht0 Ht2 C1; lia | clear - Hj A07 HrqU; lia | clear - Hj Ht2; lia].
Qed.
Lemma hl_msr : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 ,
at_MSR lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 ->
SRr trasegs W (cfgat regs HL_MSR mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_LH mem2 md2 /\ exists K, at_LH lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K 0).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1  (HP & Hzero & G20 & G21).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HP as (HC & Hold & HF & Hk & [SP72 SP56] & (S160 & S168 & S176 & S296) & Pp & Px & Ph & Pu & Pf).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
assert (FI : 4096 <= img /\ img + fmt * N <= alloc_ceiling) by (eapply rk_img_facts; eassumption). destruct FI as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
destruct (rh_BL_nth C p1 x1 h1 u1 f1) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
set (Tn := ac_Tn C) in *. set (T := ac_T C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht rh_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Bc, BT.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
unfold rh_ptr in Pp, Px, Ph, Pu, Pf.
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt (ac_H C)) T).
set (xv := [i; ha; Tn; f1; h1; u1] ++ []).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 (ac_f C)) by exact (HV 1%nat _ eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (ac_h C)) by exact (HV 2%nat _ eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 (ac_u C)) by exact (HV 3%nat _ eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 p1) by exact (HV 4%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 x1) by exact (HV 5%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 (ht_cnt (ac_H C))) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 T) by exact (HV 7%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E54 : ew E 54 = Z_to_bv 64 Tn) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 f1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 h1) by exact (HV 24%nat _ eq_refl).
assert (E57 : ew E 57 = Z_to_bv 64 u1) by exact (HV 25%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
set (xat0 := [(39%nat, mkAF 524309 8388617 0)]).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_MSR true [(20%bv, SOff 32 0); (21%bv, SOff 32 40)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] [ck 296 (SOff 57 0)] [] xat0 [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt (ac_H C)) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; (split; [reflexivity|]); cbn [fst snd].
- rewrite G20. symmetry. rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r. reflexivity.
- rewrite G21. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 55 f1 0 E55 ltac:(clear - Pf; lia)), Z.add_0_r; reflexivity | clear - Pf; lia | lia | exact S168].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | clear - Ph; lia | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | clear - Pu; lia | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ subst xat0. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E39. rewrite !unsigned_lit_small by (clear - BT; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - HTc HTlt. subst T. unfold MAX_TABLE_SIZE in HTlt. cbv [ts_chain In] in HTc. repeat split; lia. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 58 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_LH.
{ apply (hk_awr_ok s1v tb fmt E true _ _ _ _ _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros _ a Ha; destruct (Hperm tb CHT_SIZE ltac:(left; reflexivity)) as [_ Hw]; replace a with (tb + (a - tb)) by lia; apply Hw; [exact Htbin | change (req_size CHT_SIZE) with 48; clear - Ha; lia] | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (tb <= a < tb + 48) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn Hnt. apply (hk_frame_kept s1v tb fmt _ true _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros _; exact Hnt | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 58 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 58 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv | exact Hv]);
assert (DA : forall n z, (n < 58)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
by (intros n z Hn En Hz0; rewrite (denot_off Ex n z 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact En | exact Hz0]);
assert (UX32 : bv_unsigned (ew Ex 32) = tb) by (rewrite (proj1 HAE1) by lia; exact U32);
destruct (st_ok_mem_ok trasegs Ex ssx _ HS) as (_ & Hrs & _);
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 8%nat eq_refl)) as HRtb; cbn [ms_mem restrict] in HRtb end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
assert (Hsl' : rh_slots W (ms_mem ms) C h1 u1 f1).
{ split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 160 (SOff 54 0) Tn eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Tn2; lia]|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 168 (SOff 55 0) f1 eq_refl ltac:(right; left; reflexivity)); [rewrite (denot_off E 55 f1 0 E55 ltac:(clear - Pf; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Pf; lia]|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 176 (SOff 56 0) h1 eq_refl ltac:(right; right; left; reflexivity)); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Ph; lia]|].
apply (SLOT 6%nat 296 304 [ck 296 (SOff 57 0)] 296 (SOff 57 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Pu; lia]. }
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of UX32 with bv_unsigned (ew ?Ex 32) = _ =>
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 0 8%N (SOff 33 0) (ac_f C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 33%nat _ ltac:(lia) E33 Bf) Bf ltac:(lia)) as Vf';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 8 8%N (SOff 34 0) (ac_h C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 34%nat _ ltac:(lia) E34 Bh) Bh ltac:(lia)) as Vh';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 16 8%N (SOff 35 0) (ac_u C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 35%nat _ ltac:(lia) E35 Bu) Bu ltac:(lia)) as Vu';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 24 8%N (SOff 36 0) p1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 36%nat _ ltac:(lia) E36 Bp) Bp ltac:(lia)) as Vp';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 32 8%N (SOff 37 0) x1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 37%nat _ ltac:(lia) E37 Bx) Bx ltac:(lia)) as Vx';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 40 4%N (SLit 0) 0 HRtb UX32 ltac:(cbn; clear; tauto) eq_refl ltac:(cbn; lia) ltac:(lia)) as Vc';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 44 4%N (SOff 39 0) T HRtb UX32 ltac:(cbn; clear; tauto) (DA 39%nat _ ltac:(lia) E39 ltac:(clear - BT; lia)) ltac:(clear - BT; cbn; lia) ltac:(lia)) as VT' end.
rewrite !Z.add_0_r in Vf'.
assert (Hobj' : obj_at trasegs (mrestrict (w_H W) (ms_mem ms)) tb LAY_Cht (rh_cells C p1 x1 0)).
{ cbn [obj_at LAY_Cht rh_cells]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
split; [split; [exact Vf' | exact Bf]|]. split; [split; [exact Vh' | exact Bh]|]. split; [split; [exact Vu' | exact Bu]|].
split; [split; [exact Vp' | exact Bp]|]. split; [split; [exact Vx' | exact Bx]|]. split; [split; [exact Vc' | clear; lia]|].
split; [split; [exact VT' | exact BT]|]. exact I. }
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HP' : rh_pre lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha p1 x1 h1 u1 f1 0) end.
{ apply (rh_pre_step lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 _ 0 _ _ _ HP HJ); [intros r Hr; apply HKR; exact Hr | | split; [exact SP72' | exact SP56'] | exact Hsl' | exact Hobj'].
intros a Ha H1 H2 H3 H4. apply KM1; [exact Ha | exact H1 | exact H3]. }
pose proof (proj1 HJ) as HAR'.
pose proof HP' as (HC' & _).
assert (PRES : forall (q : nat) b n, nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some (b, n) -> forall a, b <= a < b + n ->
exists bb, mbyte trasegs (mrestrict (w_H W) (ms_mem ms)) a = Some bb).
{ intros q b n Hq a Ha. apply mbyte_of_apresent.
assert (Hin' : In (b, n) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; exact (nth_error_In _ _ Hq)).
destruct (al_blocks _ _ LAWS lyc Sc W (ms_mem ms) _ b n HAR' Hin') as (_ & _ & _ & _ & Hpres & _ & Hn0).
pose proof (req_size_pos n (proj1 Hn0)) as [_ Hrq]. apply (proj1 (Hpres a ltac:(clear - Ha Hrq; lia))). }
destruct (arr32_of_present trasegs (mrestrict (w_H W) (ms_mem ms)) f1 (Z.to_nat Tn)) as (frN & AfrN & LfrN); [intros a Ha; apply (PRES 8%nat f1 (4 * Tn) N8); clear - Ha Tn2; lia|].
destruct (arr8_of_present trasegs (mrestrict (w_H W) (ms_mem ms)) h1 (Z.to_nat (3 * Tn))) as (keysN & AkN & LkN); [intros a Ha; apply (PRES 6%nat h1 (3 * Tn) N6); clear - Ha Tn2; lia|].
destruct (arr8_of_present trasegs (mrestrict (w_H W) (ms_mem ms)) p1 (Z.to_nat (3 * Tn))) as (palN & ApN & LpN); [intros a Ha; apply (PRES 4%nat p1 (3 * Tn) N4); clear - Ha Tn2; lia|].
destruct (arr32_of_present trasegs (mrestrict (w_H W) (ms_mem ms)) x1 (Z.to_nat Tn)) as (cixN & AcN & LcN); [intros a Ha; apply (PRES 5%nat x1 (4 * Tn) N5); clear - Ha Tn2; lia|].
assert (AuN : arr8 trasegs (mrestrict (w_H W) (ms_mem ms)) u1 (repeat 0 (Z.to_nat Tn))).
{ apply arr8_zero. intros j Hj. apply hk_byte_of_av.
assert (Huin : In (u1, Tn) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; exact (nth_error_In _ _ N7)).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md u1 Tn HAR Huin Fceil) as (Hu0 & Hu1 & Hu2 & Hu3).
pose proof (rh_apart _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 0%nat 7%nat _ _ HC N0 N7 ltac:(lia)) as A07. cbn [fst snd] in A07. change (req_size CHT_SIZE) with 48 in A07.
rewrite KM1; [exact (Hzero j Hj) | clear - Hj Hu0 Hu1 Hu3 F47; lia | intros [Hx _]; clear - Hx Hj Hu1 Hu3; lia | clear - Hj A07 Hu3; lia]. }
set (K0 := mkHT frN keysN (repeat 0 (Z.to_nat Tn)) palN cixN 0 Tn).
assert (INV0 : ht_inv K0 (ents_below (ac_H C) 0)).
{ rewrite ents_below_0. subst K0. apply ht_empty_inv; [clear - Tn2; lia | unfold zlen; rewrite LfrN; clear - Tn2; lia | unfold zlen; rewrite LkN; clear - Tn2; lia
| unfold zlen; rewrite LpN; clear - Tn2; lia | unfold zlen; rewrite LcN; clear - Tn2; lia | exact (arr8_Forall _ _ _ _ AkN) | exact (arr8_Forall _ _ _ _ ApN)]. }
exists K0. split; [|split; [exact INV0|]; split; [subst T; clear - HTc; cbv [ts_chain In] in HTc; lia|]].
- split; [exact HP'|].
split; [split; [exact AfrN | split; [exact AkN | split; [exact AuN | split; [exact ApN | exact AcN]]]]|].
split; [|reflexivity]. unfold ht_lens, K0. cbn [ht_used ht_keys ht_frequ ht_colidx ht_pal ht_T]. unfold zlen. rewrite repeat_length, LfrN, LkN, LpN, LcN. clear - Tn2. lia.
- unfold rh_loop_regs.
split; [exact (RD 21%bv (SLit 0) 0 eq_refl eq_refl eq_refl)|]. split; [exact (RD 26%bv (SLit 0) (4 * 0) eq_refl eq_refl eq_refl)|].
split; [exact (RD 27%bv (SLit 0) (3 * 0) eq_refl eq_refl eq_refl)|]. split; [exact (RD 5%bv (SLit 1) 1 eq_refl eq_refl eq_refl)|].
split; [apply (RD 15%bv (SOff 32 44) (tb + 44) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [apply (RD 16%bv (SOff 32 8) (tb + 8) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [apply (RD 17%bv (SOff 32 16) (tb + 16) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
apply (RD 20%bv (SOff 32 0) tb eq_refl); [rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r; reflexivity | reflexivity].
Qed.
End c.
