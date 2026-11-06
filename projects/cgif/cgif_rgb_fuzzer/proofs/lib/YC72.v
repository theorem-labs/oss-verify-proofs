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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n YC6o YC6p YC6q YC6r YC6u YC77 YC78 YC79 YC6x YC6y YC6z YC70 YC71.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition uj_reg (v : Z) : YQ0b.region := YQ0b.mkRegion (Some 58%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SLit v))].
Definition UJE : sv := SAlu ALU_ADD (SOff 35 0) (SOff 21 0).
Definition er1 : YQ0b.region := YQ0b.mkRegion (Some 58%nat) 0 1 0 1 [].
Definition er2 : YQ0b.region := YQ0b.mkRegion (Some 59%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 62 0))].
Definition er3 : YQ0b.region := YQ0b.mkRegion (Some 60%nat) 0 4 0 4 [].
Definition er4 : YQ0b.region := YQ0b.mkRegion (Some 61%nat) 0 4 0 4 [].
Definition EA1 : sv * sv := (SAlu ALU_ADD (SOff 23 0) (SOff 57 0), SOff 58 0).
Definition EA2 : sv * sv := (SAlu ALU_ADD (SOff 26 0) (SOff 33 0), SOff 59 0).
Definition EA3 : sv * sv := (SAlu ALU_ADD (SOff 55 0) (SAlu ALU_SLL (SOff 23 0) (SLit 2)), SOff 60 0).
Definition EA4 : sv * sv := (SAlu ALU_ADD (SOff 37 0) (SAlu ALU_SLL (SOff 23 0) (SLit 2)), SOff 61 0).
Section d.
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
Local Notation at_LN := (at_LN B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_CHC := (at_CHC B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RM1C := (at_RM1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RM1R := (at_RM1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RM2C := (at_RM2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RM2R := (at_RM2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_CHR := (at_CHR B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Hypothesis TCOLHASH : tcolhash_spec B.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Lemma rh_BL_nth_3 : forall C p1 x1 h1 u1 f1,
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 0 = Some (tb, CHT_SIZE) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 1 = Some (ac_f C, 4 * ac_T C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 2 = Some (ac_h C, 3 * ac_T C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 3 = Some (ac_u C, ac_T C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 4 = Some (p1, 3 * ac_Tn C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 5 = Some (x1, 4 * ac_Tn C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 6 = Some (h1, 3 * ac_Tn C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 7 = Some (u1, ac_Tn C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 8 = Some (f1, 4 * ac_Tn C).
Proof. intros; eapply rh_BL_nth; eassumption. Qed.
Lemma rh_apart_3 : forall lyc Sc W regs mem md k cells C p1 x1 h1 u1 f1 (p q : nat) x y,
rcore lyc Sc W regs mem md k cells (rh_BL C p1 x1 h1 u1 f1) ->
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) p = Some x -> nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some y -> p <> q ->
fst x + req_size (snd x) <= fst y \/ fst y + req_size (snd y) <= fst x.
Proof. intros; eapply rh_apart; eassumption. Qed.

Lemma rh_pre_step_3 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 cnt cnt' regs' mem' md',
rh_pre lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 cnt ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
(forall r, In r HK_CONST -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (alloc_ceiling <= a < s1v) -> ~ (tb <= a < tb + 48) -> ~ rh_innew C p1 x1 h1 u1 f1 a ->
aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
hspill W mem' i ha -> rh_slots W mem' C h1 u1 f1 ->
obj_at trasegs (mrestrict (w_H W) mem') tb LAY_Cht (rh_cells C p1 x1 cnt') ->
rh_pre lyc Sc W regs' mem' md' k C i ha p1 x1 h1 u1 f1 cnt'.
Proof. intros; eapply rh_pre_step; eassumption. Qed.

Lemma rh_new_kept_3 : forall (W : world trasegs) (mem mem' : word -> option byte) C p1 x1 h1 u1 f1 K,
rh_new W mem C p1 x1 h1 u1 f1 K -> 0 <= ac_Tn C ->
rg_blk_kept (w_H W) (w_H W) mem mem' p1 (req_size (3 * ac_Tn C)) -> rg_blk_kept (w_H W) (w_H W) mem mem' x1 (req_size (4 * ac_Tn C)) ->
rg_blk_kept (w_H W) (w_H W) mem mem' h1 (req_size (3 * ac_Tn C)) -> rg_blk_kept (w_H W) (w_H W) mem mem' u1 (req_size (ac_Tn C)) ->
rg_blk_kept (w_H W) (w_H W) mem mem' f1 (req_size (4 * ac_Tn C)) ->
rh_new W mem' C p1 x1 h1 u1 f1 K.
Proof. intros; eapply rh_new_kept; eassumption. Qed.
Lemma rh_common_run_same_3 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K regs' mem' md',
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
(forall r, In r HK_CONST -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
hspill W mem' i ha -> rh_slots W mem' C h1 u1 f1 ->
rh_common lyc Sc W regs' mem' md' k C i ha p1 x1 h1 u1 f1 K.
Proof. intros; eapply rh_common_run_same; eassumption. Qed.
Lemma hl_rm2r : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2,
at_RM2R lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2 ->
SRr trasegs W (cfgat regs HL_RM2R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_LN mem2 md2 /\ at_LN lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 (ht_ins K h2 (key (ac_H C) j) (freq (ac_H C) j)) j).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2 ([HP HNw] & HG & HR & G23 & G24).
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
destruct (rh_BL_nth_3 C p1 x1 h1 u1 f1) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
set (Tn := ac_Tn C) in *. set (T := ac_T C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht rh_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Bc, BT.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
unfold rh_ptr in Pp, Px, Ph, Pu, Pf.
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) T).
set (xv := [i; ha; Tn; f1; h1; u1] ++ [u1 + h2; ac_f C + 4 * j; f1 + 4 * h2; x1 + 4 * h2; freq (ac_H C) j]).
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
assert (E38 : ew E 38 = Z_to_bv 64 (ht_cnt K)) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 T) by exact (HV 7%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E54 : ew E 54 = Z_to_bv 64 Tn) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 f1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 h1) by exact (HV 24%nat _ eq_refl).
assert (E57 : ew E 57 = Z_to_bv 64 u1) by exact (HV 25%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
pose proof HG as (HinvK & Hj & Hused & Hfs & Hh2 & Hfree & Hcle & Hins). pose proof HR as (R20 & R21 & R22 & R26 & R27).
pose proof HNw as (_ & _ & HTK). cbn [ht_T K_m1 K_m2] in HTK. rewrite HTK in Hh2. fold Tn in Hh2.
pose proof Hinv as (_ & (HcntH & HlenH & _) & _). pose proof HinvK as (_ & (HcntK & _) & _).
pose proof (zsum_ge_length (ac_ent C) (ent_freq_pos _ _ Hinv)) as Hzl.
assert (Rcnt : 0 <= ht_cnt K <= 10000) by (clear - HcntH HcntK Hcle Hzl HlenH Hz Hi HN; lia).
assert (Hin_h : In (ac_h C, 3 * T) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; exact (nth_error_In _ _ N2)).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md (ac_h C) (3 * T) HAR Hin_h Fceil) as (Hh0 & Hh1 & Hh2' & Hh3).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * j)) by (rewrite (HE 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = Z_to_bv 64 h1) by (rewrite (HE 22%nat 22%bv eq_refl); exact R22).
assert (RT0 : 0 < T <= 8388617) by (subst T; clear - HTc HTlt; unfold MAX_TABLE_SIZE in HTlt; cbv [ts_chain In] in HTc; lia).
set (c := key (ac_H C) j) in *. set (fq := freq (ac_H C) j) in *.
pose proof Hold as (Af & Ah & Au). pose proof Hinv as ((LU & LK & LF & _) & _ & _ & I4 & _). change (ht_T (ac_H C)) with T in LU, LK, LF.
destruct (arr32_getz trasegs _ (ac_f C) (ht_frequ (ac_H C)) j Af ltac:(rewrite LF; exact Hj)) as [Vfj Rfq32]. change (getz (ht_frequ (ac_H C)) j) with fq in Vfj, Rfq32.
assert (Rfq : 1 <= fq <= 10000).
{ destruct (I4 j ltac:(split; [exact Hj | rewrite Hused; clear; lia])) as (Hci & Hnth & Hf1). split; [exact Hf1|].
pose proof (zsum_pos_le (ac_ent C) _ _ _ (ent_freq_pos _ _ Hinv) Hnth) as X. fold fq in X. clear - X Hz Hi HN. lia. }
assert (INB : forall (q : nat) y, nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some y -> In y (ablocks B lyc Sc)).
{ intros q y Hq. eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. exact (nth_error_In _ _ Hq). }
destruct (al_blocks _ _ LAWS lyc Sc W mem md u1 Tn HAR (INB 7%nat _ N7)) as (Hu16 & Hu4096 & Huceil & Huapp & Hupres & _).
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_f C) (4 * T) HAR (INB 1%nat _ N1)) as (Hf16 & Hf4096 & Hfceil & Hfapp & Hfpres & _).
destruct (al_blocks _ _ LAWS lyc Sc W mem md f1 (4 * Tn) HAR (INB 8%nat _ N8)) as (Hg16 & Hg4096 & Hgceil & Hgapp & Hgpres & _).
destruct (al_blocks _ _ LAWS lyc Sc W mem md x1 (4 * Tn) HAR (INB 5%nat _ N5)) as (Hx16 & Hx4096 & Hxceil & Hxapp & Hxpres & _).
pose proof (req_size_pos Tn ltac:(clear - Tn2; lia)) as [_ HrqU]. pose proof (req_size_pos (4 * T) ltac:(clear - RT0; lia)) as [_ HrqF]. pose proof (req_size_pos (4 * Tn) ltac:(clear - Tn2; lia)) as [_ HrqG].
pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 0%nat 7%nat _ _ HC N0 N7 ltac:(lia)) as A07. pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 0%nat 1%nat _ _ HC N0 N1 ltac:(lia)) as A01.
pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 0%nat 8%nat _ _ HC N0 N8 ltac:(lia)) as A08. pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 0%nat 5%nat _ _ HC N0 N5 ltac:(lia)) as A05.
pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 7%nat 1%nat _ _ HC N7 N1 ltac:(lia)) as A71. pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 7%nat 8%nat _ _ HC N7 N8 ltac:(lia)) as A78.
pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 7%nat 5%nat _ _ HC N7 N5 ltac:(lia)) as A75. pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 1%nat 8%nat _ _ HC N1 N8 ltac:(lia)) as A18.
pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 1%nat 5%nat _ _ HC N1 N5 ltac:(lia)) as A15. pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 8%nat 5%nat _ _ HC N8 N5 ltac:(lia)) as A85.
cbn [fst snd] in A07, A01, A08, A05, A71, A78, A75, A18, A15, A85. change (req_size CHT_SIZE) with 48 in A07, A01, A08, A05.
assert (E23 : ew E 23 = Z_to_bv 64 h2) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E26 : ew E 26 = Z_to_bv 64 (4 * j)) by (rewrite (HE 26%nat 26%bv eq_refl); exact R26).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (E58 : ew E 58 = Z_to_bv 64 (u1 + h2)) by exact (HV 26%nat _ eq_refl).
assert (E59 : ew E 59 = Z_to_bv 64 (ac_f C + 4 * j)) by exact (HV 27%nat _ eq_refl).
assert (E60 : ew E 60 = Z_to_bv 64 (f1 + 4 * h2)) by exact (HV 28%nat _ eq_refl).
assert (E61 : ew E 61 = Z_to_bv 64 (x1 + 4 * h2)) by exact (HV 29%nat _ eq_refl).
assert (E62 : ew E 62 = Z_to_bv 64 fq) by exact (HV 30%nat _ eq_refl).
assert (U58 : bv_unsigned (ew E 58) = u1 + h2) by (rewrite E58; apply unsigned_lit_small; clear - Hu4096 Huceil HrqU Hh2 C1; lia).
assert (U59 : bv_unsigned (ew E 59) = ac_f C + 4 * j) by (rewrite E59; apply unsigned_lit_small; clear - Hf4096 Hfceil HrqF Hj C1; lia).
assert (U60 : bv_unsigned (ew E 60) = f1 + 4 * h2) by (rewrite E60; apply unsigned_lit_small; clear - Hg4096 Hgceil HrqG Hh2 C1; lia).
assert (U61 : bv_unsigned (ew E 61) = x1 + 4 * h2) by (rewrite E61; apply unsigned_lit_small; clear - Hx4096 Hxceil HrqG Hh2 C1; lia).
assert (Hm4 : forall b t, b mod 16 = 0 -> (b + 4 * t) mod 4 = 0) by (intros b t Hb; exact (mod4_of16 b t Hb)).
assert (U4H : forall n b, ew E n = Z_to_bv 64 b -> 4096 <= b -> b + 4 * Tn <= 140737479966720 -> U E (SAlu ALU_ADD (SOff n 0) (SAlu ALU_SLL (SOff 23 0) (SLit 2))) = b + 4 * h2).
{ intros n b En Hb0 Hb1. rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 23 h2 E23) by (clear - Hh2 Tn2; lia). rewrite (U_lit E 2) by lia.
rewrite (U_atom E n b En) by (clear - Hb0 Hb1 Tn2; lia). change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite (zcanon_id (h2 * 4)) by (unfold M64; clear - Hh2 Tn2; lia). rewrite zcanon_id by (unfold M64; clear - Hb0 Hb1 Hh2; lia). lia. }
assert (UB : U E hk_Bx = SHADOW_OFF) by (unfold U, hk_Bx; cbn [sv_denot]; rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity).
set (xat0 := [(23%nat, mkAF 0 16777215 0); (26%nat, mkAF 0 33554464 0); (38%nat, mkAF 0 10000 0); (58%nat, mkAF 4096 140737479966720 0); (59%nat, mkAF 4096 140737479966720 2);
(60%nat, mkAF 4096 140737479966720 2); (61%nat, mkAF 4096 140737479966720 2); (62%nat, mkAF 1 10000 0)]).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_RM2R true [(24%bv, SOff 32 40)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] [ck 296 (SOff 57 0)] [er1; er2; er3; er4] xat0 [] [EA1; EA2; EA3; EA4] [mkSHE 58 0 1; mkSHE 59 0 4; mkSHE 60 0 4; mkSHE 61 0 4]
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G24. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 55 f1 0 E55 ltac:(clear - Pf; lia)), Z.add_0_r; reflexivity | clear - Pf; lia | lia | exact S168].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | clear - Ph; lia | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | clear - Pu; lia | lia | exact S296]. }
{ repeat apply Forall_cons; try apply Forall_nil; unfold er1, er2, er3, er4, region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]; rewrite ?U58, ?U59, ?U60, ?U61.
- split; [clear - Hu4096 Hh2; lia|]. split; [clear - Huceil HrqU Hh2 C1; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hupres (u1 + h2 + o) ltac:(clear - Ho Hh2 HrqU; lia))).
- split; [clear - Hf4096 Hj; lia|]. split; [clear - Hfceil HrqF Hj C1; lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E _ (ac_f C + 4 * j) 0 4 _ fq); [rewrite (denot_off E 62 fq 0 E62 ltac:(clear - Rfq; lia)), Z.add_0_r; reflexivity | clear - Rfq; cbn; lia | lia | rewrite Z.add_0_r; exact Vfj].
- split; [clear - Hg4096 Hh2; lia|]. split; [clear - Hgceil HrqG Hh2 C1; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hgpres (f1 + 4 * h2 + o) ltac:(clear - Ho Hh2 HrqG; lia))).
- split; [clear - Hx4096 Hh2; lia|]. split; [clear - Hxceil HrqG Hh2 C1; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hxpres (x1 + 4 * h2 + o) ltac:(clear - Ho Hh2 HrqG; lia))). }
{ intros e [<- | [<- | [<- | [<- | []]]]]; unfold extent_of_region, er1, er2, er3, er4; cbn [fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite ?U58, ?U59, ?U60, ?U61.
- clear - A07 Huceil HrqU Hh2. lia.
- clear - A01 Hfceil HrqF Hj. lia.
- clear - A08 Hgceil HrqG Hh2. lia.
- clear - A05 Hxceil HrqG Hh2. lia. }
{ cbn [map zpairwise_disjoint zall_disjoint]. unfold extent_of_region, er1, er2, er3, er4, zdisj. cbn [fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite U58, U59, U60, U61.
clear - A71 A78 A75 A18 A15 A85 HrqU HrqF HrqG Hh2 Hj. repeat split; try exact I; lia. }
{ subst xat0. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E23, E26, E38, E62, U58, U59, U60, U61.
rewrite !unsigned_lit_small by (clear - Hh2 Tn2 Hj RT0 Rcnt Rfq; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 2) with 4.
pose proof (Hm4 _ j Hf16) as Mf. pose proof (Hm4 _ h2 Hg16) as Mg. pose proof (Hm4 _ h2 Hx16) as Mx.
clear - Hh2 Tn2 Hj RT0 Rcnt Rfq Hu4096 Huceil HrqU Hf4096 Hfceil HrqF Hg4096 Hgceil Hx4096 Hxceil HrqG C1 Mf Mg Mx. subst T. repeat split; lia. }
{ exact I. }
{ unfold EA1, EA2, EA3, EA4. cbn [alias_ok]. split; [|split; [|split; [|split; [|exact I]]]]; apply U_inj.
- rewrite (U_atom E 58 (u1 + h2) E58) by (clear - Hu4096 Huceil HrqU Hh2 C1; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 23 h2 E23) by (clear - Hh2 Tn2; lia). rewrite (U_atom E 57 u1 E57) by (clear - Pu; lia).
rewrite zcanon_id by (unfold M64; clear - Hu4096 Huceil HrqU Hh2 C1; lia). lia.
- rewrite (U_atom E 59 (ac_f C + 4 * j) E59) by (clear - Hf4096 Hfceil HrqF Hj C1; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 26 (4 * j) E26) by (clear - Hj RT0; lia). rewrite (U_atom E 33 (ac_f C) E33) by (clear - Hf4096 Hfceil HrqF C1 RT0; lia).
rewrite zcanon_id by (unfold M64; clear - Hf4096 Hfceil HrqF Hj C1; lia). lia.
- rewrite (U_atom E 60 (f1 + 4 * h2) E60) by (clear - Hg4096 Hgceil HrqG Hh2 C1; lia). apply (U4H 55%nat f1 E55); [exact Hg4096 | clear - Hgceil HrqG C1; lia].
- rewrite (U_atom E 61 (x1 + 4 * h2) E61) by (clear - Hx4096 Hxceil HrqG Hh2 C1; lia). apply (U4H 37%nat x1 E37); [exact Hx4096 | clear - Hxceil HrqG C1; lia]. }
{ repeat apply Forall_cons; try apply Forall_nil.
- apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 58 (u1 + h2) 1 (u1 + h2) 0 1); [|exact UB| | lia | lia |].
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md u1 Tn _ _ HAR (INB 7%nat _ N7)); clear - Hh2 HrqU; lia.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U58.
+ intros x Hx. revert Hx Huapp Hh2 HrqU. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 59 (ac_f C + 4 * j) 4 (ac_f C + 4 * j) 0 4); [|exact UB| | lia | lia |].
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md (ac_f C) (4 * T) _ _ HAR (INB 1%nat _ N1)); clear - Hj HrqF; lia.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U59.
+ intros x Hx. revert Hx Hfapp Hj HrqF. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 60 (f1 + 4 * h2) 4 (f1 + 4 * h2) 0 4); [|exact UB| | lia | lia |].
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md f1 (4 * Tn) _ _ HAR (INB 8%nat _ N8)); clear - Hh2 HrqG; lia.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U60.
+ intros x Hx. revert Hx Hgapp Hh2 HrqG. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 61 (x1 + 4 * h2) 4 (x1 + 4 * h2) 0 4); [|exact UB| | lia | lia |].
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md x1 (4 * Tn) _ _ HAR (INB 5%nat _ N5)); clear - Hh2 HrqG; lia.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U61.
+ intros x Hx. revert Hx Hxapp Hh2 HrqG. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
assert (HAE : env_agree 63 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_LN.
{ apply (hk_awr_ok s1v tb fmt E true _ _ _ _ _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros _ a Ha; destruct (Hperm tb CHT_SIZE ltac:(left; reflexivity)) as [_ Hw]; replace a with (tb + (a - tb)) by lia; apply Hw; [exact Htbin | change (req_size CHT_SIZE) with 48; clear - Ha; lia] | assert (PW : forall (q : nat) b n, nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some (b, n) -> forall a, b <= a < b + req_size n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a)
by (intros q b n Hq a Ha; destruct (Hperm b n (nth_error_In _ _ Hq)) as [_ Hw]; replace a with (b + (a - b)) by lia; apply Hw; [exact (INB q _ Hq) | clear - Ha; lia]);
eapply (awr_ok_cons_gen _ _ _ STK sp0 FP _ _ lyc own 58%nat (u1 + h2)); [reflexivity | exact U58 | unfold er1; cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; apply (PW 7%nat _ _ N7); clear - Ha Hh2 HrqU; lia|];
apply awr_ok_cons_ro; [cbn; lia|];
eapply (awr_ok_cons_gen _ _ _ STK sp0 FP _ _ lyc own 60%nat (f1 + 4 * h2)); [reflexivity | exact U60 | unfold er3; cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; apply (PW 8%nat _ _ N8); clear - Ha Hh2 HrqG; lia|];
eapply (awr_ok_cons_gen _ _ _ STK sp0 FP _ _ lyc own 61%nat (x1 + 4 * h2)); [reflexivity | exact U61 | unfold er4; cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; apply (PW 5%nat _ _ N5); clear - Ha Hh2 HrqG; lia | apply awr_ok_nil]]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 63 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (tb <= a < tb + 48) -> ~ (u1 + h2 <= a < u1 + h2 + 1) ->
~ (f1 + 4 * h2 <= a < f1 + 4 * h2 + 4) -> ~ (x1 + 4 * h2 <= a < x1 + 4 * h2 + 4) ->
aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn Hnt Hnu Hnf Hnx. apply (hk_frame_kept s1v tb fmt _ true _ _ _ _ _ _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros _; exact Hnt|].
intros (rr & [<- | [<- | [<- | [<- | []]]]] & Hr); unfold er1, er2, er3, er4 in Hr; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; fold vals in Hr; fold E in Hr;
rewrite ?U58, ?U59, ?U60, ?U61 in Hr; clear - Hr Hnu Hnf Hnx; lia. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 63 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [21; 23; 26; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 63 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 63 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 63 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 63 E Ex e HAE1 Hat); exact Dv | exact Hv]);
assert (DA : forall n z, (n < 63)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
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
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 40 4%N (SOff 38 1) ((ht_cnt K) + 1) HRtb UX32 ltac:(cbn; clear; tauto) ltac:(apply denot_off; [rewrite (proj1 HAE1) by lia; exact E38 | clear - Rcnt; lia]) ltac:(clear - Rcnt; cbn; lia) ltac:(lia)) as Vc';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 44 4%N (SOff 39 0) T HRtb UX32 ltac:(cbn; clear; tauto) (DA 39%nat _ ltac:(lia) E39 ltac:(clear - BT; lia)) ltac:(clear - BT; cbn; lia) ltac:(lia)) as VT' end.
rewrite !Z.add_0_r in Vf'.
assert (Hobj' : obj_at trasegs (mrestrict (w_H W) (ms_mem ms)) tb LAY_Cht (rh_cells C p1 x1 ((ht_cnt K) + 1))).
{ cbn [obj_at LAY_Cht rh_cells]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
split; [split; [exact Vf' | exact Bf]|]. split; [split; [exact Vh' | exact Bh]|]. split; [split; [exact Vu' | exact Bu]|].
split; [split; [exact Vp' | exact Bp]|]. split; [split; [exact Vx' | exact Bx]|]. split; [split; [exact Vc' | clear - Rcnt; lia]|].
split; [split; [exact VT' | exact BT]|]. exact I. }
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 9%nat eq_refl)) as HRu;
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 11%nat eq_refl)) as HRf;
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 12%nat eq_refl)) as HRx; cbn [ms_mem restrict] in HRu, HRf, HRx;
pose proof (field_of_region Ex _ 58 (u1 + h2) _ 0 1 0 1 0 1%N (SLit 1) 1 HRu ltac:(rewrite (proj1 HAE1) by lia; exact U58) ltac:(cbn; clear; tauto) eq_refl ltac:(cbn; lia) ltac:(lia)) as Vuh;
pose proof (field_of_region Ex _ 60 (f1 + 4 * h2) _ 0 4 0 4 0 4%N (SOff 62 0) fq HRf ltac:(rewrite (proj1 HAE1) by lia; exact U60) ltac:(cbn; clear; tauto)
(DA 62%nat _ ltac:(lia) E62 ltac:(clear - Rfq; lia)) ltac:(clear - Rfq; cbn; lia) ltac:(lia)) as Vfh;
pose proof (field_of_region Ex _ 61 (x1 + 4 * h2) _ 0 4 0 4 0 4%N (SOff 38 0) (ht_cnt K) HRx ltac:(rewrite (proj1 HAE1) by lia; exact U61) ltac:(cbn; clear; tauto)
(DA 38%nat _ ltac:(lia) E38 ltac:(clear - Rcnt; lia)) ltac:(clear - Rcnt; cbn; lia) ltac:(lia)) as Vxh end.
rewrite !Z.add_0_r in Vuh, Vfh, Vxh.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HP' : rh_pre lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha p1 x1 h1 u1 f1 ((ht_cnt K) + 1)) end.
{ apply (rh_pre_step_3 lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 _ ((ht_cnt K) + 1) _ _ _ HP HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | | split; [exact SP72' | exact SP56'] | exact Hsl' | exact Hobj'].
intros a Ha H1 H2 H3 H4. apply KM1; [exact Ha | exact H1 | exact H3 | | |]; intros Hx; apply H4; unfold rh_innew; fold Tn.
- right. right. right. left. clear - Hx Hh2 HrqU. lia.
- right. right. right. right. clear - Hx Hh2 HrqG. lia.
- right. left. clear - Hx Hh2 HrqG. lia. }
pose proof HNw as ((AfK & AhK & AuK & ApK & AxK) & HlensK & _). pose proof HlensK as (LK1 & LK2 & LK3 & LK4 & LK5). cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx ht_T K_m2] in LK1, LK2, LK3, LK4, LK5, AfK, AhK, AuK, ApK, AxK.
rewrite HTK in LK1, LK2, LK3, LK4, LK5. fold Tn in LK1, LK2, LK3, LK4, LK5. rewrite zlen_set_col in LK2, LK5.
pose proof (req_size_pos (3 * Tn) ltac:(clear - Tn2; lia)) as [_ HrqK].
pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 6%nat 7%nat _ _ HC N6 N7 ltac:(lia)) as A67. pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 6%nat 8%nat _ _ HC N6 N8 ltac:(lia)) as A68.
pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 6%nat 5%nat _ _ HC N6 N5 ltac:(lia)) as A65. pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 6%nat 0%nat _ _ HC N6 N0 ltac:(lia)) as A60.
pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 4%nat 7%nat _ _ HC N4 N7 ltac:(lia)) as A47. pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 4%nat 8%nat _ _ HC N4 N8 ltac:(lia)) as A48.
pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 4%nat 5%nat _ _ HC N4 N5 ltac:(lia)) as A45. pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 4%nat 0%nat _ _ HC N4 N0 ltac:(lia)) as A40.
cbn [fst snd] in A67, A68, A65, A60, A47, A48, A45, A40. change (req_size CHT_SIZE) with 48 in A60, A40. fold Tn in A67, A68, A65, A60, A47, A48, A45, A40.
assert (KB : forall (q : nat) b n, nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some (b, n) -> forall a, b <= a < b + req_size n -> ~ (tb <= a < tb + 48) -> ~ (u1 + h2 <= a < u1 + h2 + 1) ->
~ (f1 + 4 * h2 <= a < f1 + 4 * h2 + 4) -> ~ (x1 + 4 * h2 <= a < x1 + 4 * h2 + 4) ->
mbyte trasegs (mrestrict (w_H W) (ms_mem ms)) a = mbyte trasegs (mrestrict (w_H W) mem) a).
{ intros q b n Hq a Ha M1 M2 M3 M4. apply (mbyte_of_aview trasegs).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md b n HAR (INB q _ Hq) Fceil) as (Hb0 & Hb1 & Hb2 & Hb3).
apply KM1; [clear - Ha Hb0 Hb2 C1; lia | intros [Hx _]; clear - Hx Ha Hb1; lia | exact M1 | exact M2 | exact M3 | exact M4]. }
split; [split; [exact HP'|]|split; [exact Hins|split; [exact Hj|]]].
- split; [|split; [destruct HNw as (_ & HL & _); unfold ht_lens in HL |- *; unfold ht_ins; unfold K_m2 in HL; cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx ht_T] in HL |- *; rewrite ?zlen_set_col in HL; rewrite !zlen_setz, ?zlen_set_col; exact HL | exact HTK]].
unfold ht_ins. cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx]. fold (ht_cnt K). fold c.
split.
{ apply (arr32_setz_mem _ _ f1 (ht_frequ K) h2 fq AfK); [rewrite LK3; exact Hh2 | clear - Rfq; lia | exact Vfh|].
intros t Ht Hne kk Hkk. rewrite LK3 in Ht. apply (KB 8%nat _ _ N8); [clear - Ht Hkk HrqG; lia | clear - Ht Hkk A08 HrqG; lia | clear - Ht Hkk A78 HrqG HrqU Hh2; lia | clear - Ht Hkk Hne; lia | clear - Ht Hkk A85 HrqG Hh2; lia]. }
split.
{ apply (arr8_frame trasegs _ _ _ _ AhK). intros a Ha. rewrite zlen_set_col, LK2 in Ha.
apply (KB 6%nat _ _ N6); [clear - Ha HrqK; lia | clear - Ha A60 HrqK; lia | clear - Ha A67 HrqK HrqU Hh2; lia | clear - Ha A68 HrqK HrqG Hh2; lia | clear - Ha A65 HrqK HrqG Hh2; lia]. }
split.
{ apply (arr8_setz_mem _ _ u1 (ht_used K) h2 1 AuK); [rewrite LK1; exact Hh2 | lia | |].
- pose proof (Vuh 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X. rewrite Z.add_0_r in X. exact X.
- intros t Ht Hne. rewrite LK1 in Ht. apply (KB 7%nat _ _ N7); [clear - Ht HrqU; lia | clear - Ht A07 HrqU; lia | clear - Ht Hne; lia | clear - Ht A78 HrqU HrqG Hh2; lia | clear - Ht A75 HrqU HrqG Hh2; lia]. }
split.
{ apply (arr8_frame trasegs _ _ _ _ ApK). intros a Ha. rewrite zlen_set_col, LK5 in Ha.
apply (KB 4%nat _ _ N4); [clear - Ha HrqK; lia | clear - Ha A40 HrqK; lia | clear - Ha A47 HrqK HrqU Hh2; lia | clear - Ha A48 HrqK HrqG Hh2; lia | clear - Ha A45 HrqK HrqG Hh2; lia]. }
apply (arr32_setz_mem _ _ x1 (ht_colidx K) h2 (ht_cnt K) AxK); [rewrite LK4; exact Hh2 | clear - Rcnt; lia | exact Vxh|].
intros t Ht Hne kk Hkk. rewrite LK4 in Ht. apply (KB 5%nat _ _ N5); [clear - Ht Hkk HrqG; lia | clear - Ht Hkk A05 HrqG; lia | clear - Ht Hkk A75 HrqG HrqU Hh2; lia | clear - Ht Hkk A85 HrqG Hh2; lia | clear - Ht Hkk Hne; lia].
- unfold rh_loop_regs. rewrite (HKR 21%bv ltac:(cbv; clear; tauto)), (HKR 26%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)).
split; [exact R21|]. split; [exact R26|]. split; [exact R27|]. split; [exact (RD 5%bv (SLit 1) 1 eq_refl eq_refl eq_refl)|].
split; [apply (RD 15%bv (SOff 32 44) (tb + 44) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|]. split; [apply (RD 16%bv (SOff 32 8) (tb + 8) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|]. split; [apply (RD 17%bv (SOff 32 16) (tb + 16) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
apply (RD 20%bv (SOff 32 0) tb eq_refl); [rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r; reflexivity | reflexivity].
Qed.
End d.
