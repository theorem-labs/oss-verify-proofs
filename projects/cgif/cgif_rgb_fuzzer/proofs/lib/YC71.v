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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n YC6o YC6p YC6q YC6r YC6u YC77 YC78 YC79 YC6x YC6y YC6z YC70.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition uj_reg (v : Z) : YQ0b.region := YQ0b.mkRegion (Some 58%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SLit v))].
Definition UJE : sv := SAlu ALU_ADD (SOff 35 0) (SOff 21 0).
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
Lemma rh_common_call_same : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K regs2 mem2 md2 (slo : Z),
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
aregs_preserved regs regs2 ->
acall_kept trasegs B lyc Sc W mem W mem2 slo s1v (fun _ => False) ->
rh_common lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K.
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K regs2 mem2 md2 slo [HP HNw] HJ2 HPr HK.
pose proof HP as (HC & (Af & Ah & Au) & HF & Hk & [SP72 SP56] & (S160 & S168 & S176 & S296) & Hptrs).
pose proof HF as (Hinv & HTc & HTlt & _). pose proof Hinv as ((L1 & L2 & L3 & _) & _).
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3).
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & _). fold (ac_Tn C) in Tn1, Tn2.
pose proof HC as (HJ & _ & _ & _ & _ & HPerm & Hperm & _). pose proof (proj1 HJ) as HAR.
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres). pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rh_BL_nth_3 C p1 x1 h1 u1 f1) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
pose proof HK as (A1 & A2 & _).
assert (Hfr : forall a, s1v <= a < s1v + 512 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem a).
{ intros a Ha. apply A1; [clear - Ha Fceil F47 C1; lia | clear - Ha; lia]. }
assert (Hblk : forall (q : nat) b n, nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some (b, n) -> rg_blk_kept (w_H W) (w_H W) mem mem2 b (req_size n)).
{ intros q b n Hq j Hj. apply (A2 b n j); [| exact Hj | intros []].
eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. exact (nth_error_In _ _ Hq). }
split.
- split.
{ eapply rcore_call with (lyc := lyc) (Sc := Sc) (W := W) (regs := regs) (mem := mem) (md := md) (k := k) (BL := rh_BL C p1 x1 h1 u1 f1) (E := fun _ : Z => False); try eassumption;
[reflexivity | intros a []]. }
split.
{ unfold ac_T in *. split; [|split].
- apply (arr32_frame trasegs _ _ _ _ Af). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L3 in Ha.
pose proof (req_size_pos (4 * ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_f C + (a - ac_f C)) by lia. apply (Hblk 1%nat _ _ N1). unfold ac_T. clear - Ha Hrq. lia.
- apply (arr8_frame trasegs _ _ _ _ Ah). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L2 in Ha.
pose proof (req_size_pos (3 * ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_h C + (a - ac_h C)) by lia. apply (Hblk 2%nat _ _ N2). unfold ac_T. clear - Ha Hrq. lia.
- apply (arr8_frame trasegs _ _ _ _ Au). intros a Ha. apply (mbyte_of_aview trasegs). rewrite L1 in Ha.
pose proof (req_size_pos (ht_T (ac_H C)) ltac:(clear - RT1; lia)) as [_ Hrq].
replace a with (ac_u C + (a - ac_u C)) by lia. apply (Hblk 3%nat _ _ N3). unfold ac_T. clear - Ha Hrq. lia. }
split; [exact HF|]. split; [exact Hk|].
split; [split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia | eapply slot_kept with (W := W) (mem := mem); try eassumption; lia]|].
split; [|exact Hptrs].
split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia|]. split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia|].
split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia | eapply slot_kept with (W := W) (mem := mem); try eassumption; lia].
- apply (rh_new_kept_3 W mem mem2 C p1 x1 h1 u1 f1 K HNw ltac:(clear - Tn2; lia)); [exact (Hblk 4%nat _ _ N4) | exact (Hblk 5%nat _ _ N5) | exact (Hblk 6%nat _ _ N6) | exact (Hblk 7%nat _ _ N7) | exact (Hblk 8%nat _ _ N8)].
Qed.
Lemma rh_key_views : forall (W : world trasegs) (mem : word -> option byte) C j, rz_old W mem C -> ht_inv (ac_H C) (ac_ent C) -> 0 <= j < ac_T C ->
aview trasegs (w_H W) mem (ac_h C + 3 * j) = Some (cR (key (ac_H C) j)) /\ aview trasegs (w_H W) mem (ac_h C + 3 * j + 1) = Some (cG (key (ac_H C) j)) /\
aview trasegs (w_H W) mem (ac_h C + 3 * j + 2) = Some (cB (key (ac_H C) j)) /\ colour_ok (key (ac_H C) j).
Proof.
intros W mem C j (_ & Ah & _) Hinv Hj. pose proof Hinv as ((_ & L2 & _) & _ & (_ & Bk & _) & _). unfold ac_T in Hj.
assert (KV : aview trasegs (w_H W) mem (ac_h C + 3 * j) = Some (cR (col_at (ht_keys (ac_H C)) j)) /\
aview trasegs (w_H W) mem (ac_h C + 3 * j + 1) = Some (cG (col_at (ht_keys (ac_H C)) j)) /\
aview trasegs (w_H W) mem (ac_h C + 3 * j + 2) = Some (cB (col_at (ht_keys (ac_H C)) j)))
by (eapply hk_key_views; first [exact Ah | exact 0 | (clear - Hj; lia) | (rewrite L2; clear - Hj; lia)]).
destruct KV as (V0 & V1 & V2). unfold key. split; [exact V0|]. split; [exact V1|]. split; [exact V2|]. apply (col_at_ok _ _ Bk); [clear - Hj; lia | rewrite L2; clear - Hj; lia].
Qed.
Lemma rh_copy3 : forall (which : bool) lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j idx ret,
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K -> 0 <= j < ac_T C -> 0 <= idx < ac_Tn C ->
getr regs 10 = Z_to_bv 64 ((if which then h1 else p1) + 3 * idx) -> getr regs 11 = Z_to_bv 64 (ac_h C + 3 * j) -> getr regs 12 = Z_to_bv 64 3 ->
getr regs 1 = Z_to_bv 64 ret -> 4096 <= ret < 2 ^ 63 -> ret mod 2 = 0 ->
SRr trasegs W (cfgat regs A_asan_memcpy mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 ret mem2 md2 /\
rh_common lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 (H_col K which idx (key (ac_H C) j)) /\ aregs_preserved regs regs2).
Proof.
intros which lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j idx ret [HP HNw] Hj Hidx G10 G11 G12 Gra Hret Hret2.
pose proof HP as (HC & Hold & HF & Hk & [SP72 SP56] & (S160 & S168 & S176 & S296) & Pp & Px & Ph & Pu & Pf).
pose proof HF as (Hinv & HTc & HTlt & _).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hslots & Hobj & Himg & HPerm & Hperm & Hkept). pose proof (proj1 HJ) as HAR.
pose proof HNw as ((AfK & AhK & AuK & ApK & AxK) & HlensK & HTK). pose proof HlensK as (LK1 & LK2 & LK3 & LK4 & LK5). rewrite HTK in LK1, LK2, LK3, LK4, LK5.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & _). fold (ac_Tn C) in Tn1, Tn2.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3).
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres). pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rh_BL_nth_3 C p1 x1 h1 u1 f1) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
set (Tn := ac_Tn C) in *. set (T := ac_T C) in *. set (c := key (ac_H C) j).
set (bd := if which then h1 else p1) in *. set (qd := if which then 6%nat else 4%nat).
assert (Nd : nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) qd = Some (bd, 3 * Tn)) by (subst bd qd; destruct which; [exact N6 | exact N4]).
assert (INB : forall (q : nat) y, nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some y -> In y (ablocks B lyc Sc)).
{ intros q y Hq. eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. exact (nth_error_In _ _ Hq). }
pose proof (INB qd _ Nd) as Hbdin'. pose proof (INB 2%nat _ N2) as Hsrcin.
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md bd (3 * Tn) HAR Hbdin' Fceil) as (Hd0 & Hd1 & Hd2 & Hd3).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md (ac_h C) (3 * T) HAR Hsrcin Fceil) as (Hs0 & Hs1' & Hs2 & Hs3).
destruct (al_blocks _ _ LAWS lyc Sc W mem md bd (3 * Tn) HAR Hbdin') as (_ & Hd4096 & _).
assert (Asd : bd + req_size (3 * Tn) <= ac_h C \/ ac_h C + req_size (3 * T) <= bd).
{ pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 qd 2%nat _ _ HC Nd N2 ltac:(subst qd; destruct which; lia)) as X. cbn [fst snd] in X. exact X. }
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 ret)) by (apply YK0s.ret_ok_even; rewrite unsigned_lit_small by (clear - Hret; lia); exact Hret2).
eapply SRr_mono.
{ apply (hk_memcpy_call B LAWS AMEMCPY STK sp0 FP ly S W0 mem0 md0 own s1v Hs1 ltac:(unfold ESTACK, ASTACK in *; clear - HSTKA; lia) lyc Sc W regs mem md k (bd + 3 * idx) (ac_h C + 3 * j) 3 (Z_to_bv 64 ret)
bd (3 * Tn) (ac_h C) (3 * T) HJ G10 G11 G12 ltac:(lia) G2 G3 G4 Gra Hraw Hbdin' ltac:(clear - Hidx; lia) ltac:(clear - Hidx Hd3; lia)
(proj2 (Hperm bd (3 * Tn) (nth_error_In _ _ Nd))) Hsrcin ltac:(clear - Hj; lia) ltac:(clear - Hj Hs3; lia)).
clear - Asd Hidx Hj Hd3 Hs3. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcp & Hout2 & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [|exact HP2].
assert (Hfr : forall a, s1v <= a < s1v + 512 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem a).
{ intros a Ha. apply Hout2; [clear - Ha Fceil F47 C1; lia | clear - Ha Hd1 Hidx Hd3; lia | clear - Ha; lia]. }
assert (Hoth : forall (q : nat) b n, nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some (b, n) -> q <> qd -> rg_blk_kept (w_H W) (w_H W) mem mem2 b (req_size n)).
{ intros q b n Hq Hne t Ht. pose proof (INB q _ Hq) as Hbin.
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md b n HAR Hbin Fceil) as (Hb0 & Hb1 & Hb2 & Hb3).
pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 q qd _ _ HC Hq Nd Hne) as X. cbn [fst snd] in X.
apply Hout2; [clear - Ht Hb0 Hb2 C1; lia | clear - Ht X Hidx Hd3; lia | clear - Ht Hb2; lia]. }
destruct (rh_key_views W mem C j Hold Hinv Hj) as (V0 & V1 & V2 & Cok). fold c in V0, V1, V2, Cok.
assert (B0 : mbyte trasegs (mrestrict (w_H W) mem2) (bd + 3 * idx) = Some (Z_to_bv 8 (cR c))).
{ apply hk_byte_of_av. rewrite <- V0. pose proof (Hcp 0 ltac:(lia)) as X. rewrite !Z.add_0_r in X. exact X. }
assert (B1 : mbyte trasegs (mrestrict (w_H W) mem2) (bd + 3 * idx + 1) = Some (Z_to_bv 8 (cG c))) by (apply hk_byte_of_av; rewrite <- V1; exact (Hcp 1 ltac:(lia))).
assert (B2 : mbyte trasegs (mrestrict (w_H W) mem2) (bd + 3 * idx + 2) = Some (Z_to_bv 8 (cB c))) by (apply hk_byte_of_av; rewrite <- V2; exact (Hcp 2 ltac:(lia))).
assert (KIN : forall t, 0 <= t < 3 * Tn -> ~ (3 * idx <= t < 3 * idx + 3) -> mbyte trasegs (mrestrict (w_H W) mem2) (bd + t) = mbyte trasegs (mrestrict (w_H W) mem) (bd + t)).
{ intros t Ht Hnt. apply (mbyte_of_aview trasegs). apply Hout2; [clear - Ht Hd4096 Hd2 Hd3 C1; lia | clear - Hnt; lia | clear - Ht Hd2 Hd3 Fceil; lia]. }
assert (HP' : rh_pre lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 (ht_cnt (H_col K which idx c))).
{ replace (ht_cnt (H_col K which idx c)) with (ht_cnt K) by (destruct which; reflexivity).
apply (rh_pre_step_3 lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 _ _ regs2 mem2 md2 HP HJ2).
- intros r Hr. apply (aregs_get regs regs2 r HP2). apply hk_const_saved. exact Hr.
- intros a Ha H1 H2 H3 H4. apply Hout2; [exact Ha | | exact H2]. intros Hx. apply H4. unfold rh_innew. fold Tn. subst bd. destruct which; [right; right; left | left]; clear - Hx Hidx Hd3; lia.
- split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia | eapply slot_kept with (W := W) (mem := mem); try eassumption; lia].
- split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia|]. split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia|].
split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia | eapply slot_kept with (W := W) (mem := mem); try eassumption; lia].
- apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem mem2 tb LAY_Cht _ 48 Hobj lay_inside_Cht). apply (Hoth 0%nat _ _ N0). subst qd. destruct which; lia. }
split; [exact HP'|].
pose proof (req_size_pos Tn ltac:(clear - Tn2; lia)) as [_ Hr1]. pose proof (req_size_pos (3 * Tn) ltac:(clear - Tn2; lia)) as [_ Hr3]. pose proof (req_size_pos (4 * Tn) ltac:(clear - Tn2; lia)) as [_ Hr4].
assert (KF : forall a, f1 <= a < f1 + 4 * Tn -> mbyte trasegs (mrestrict (w_H W) mem2) a = mbyte trasegs (mrestrict (w_H W) mem) a).
{ intros a Ha. apply (mbyte_of_aview trasegs). replace a with (f1 + (a - f1)) by lia. apply (Hoth 8%nat _ _ N8); [subst qd; destruct which; lia | clear - Ha Hr4; lia]. }
assert (KU : forall a, u1 <= a < u1 + Tn -> mbyte trasegs (mrestrict (w_H W) mem2) a = mbyte trasegs (mrestrict (w_H W) mem) a).
{ intros a Ha. apply (mbyte_of_aview trasegs). replace a with (u1 + (a - u1)) by lia. apply (Hoth 7%nat _ _ N7); [subst qd; destruct which; lia | clear - Ha Hr1; lia]. }
assert (KX : forall a, x1 <= a < x1 + 4 * Tn -> mbyte trasegs (mrestrict (w_H W) mem2) a = mbyte trasegs (mrestrict (w_H W) mem) a).
{ intros a Ha. apply (mbyte_of_aview trasegs). replace a with (x1 + (a - x1)) by lia. apply (Hoth 5%nat _ _ N5); [subst qd; destruct which; lia | clear - Ha Hr4; lia]. }
split; [|split; [unfold ht_lens, H_col; destruct which; cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx ht_T]; rewrite ?zlen_set_col; exact HlensK | destruct which; exact HTK]].
unfold H_col. subst bd qd. destruct which; cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx].
- split; [apply (arr32_frame trasegs _ _ _ _ AfK); intros a Ha; rewrite LK3 in Ha; exact (KF a Ha)|].
split; [apply (arr8_set_col_mem _ _ h1 (ht_keys K) idx c AhK ltac:(clear - Hidx; lia) ltac:(rewrite LK2; clear - Hidx; lia) Cok B0 B1 B2); intros t Ht Hnt; apply KIN; [rewrite LK2 in Ht; exact Ht | exact Hnt]|].
split; [apply (arr8_frame trasegs _ _ _ _ AuK); intros a Ha; rewrite LK1 in Ha; exact (KU a Ha)|].
split; [apply (arr8_frame trasegs _ _ _ _ ApK); intros a Ha; rewrite LK5 in Ha; apply (mbyte_of_aview trasegs); replace a with (p1 + (a - p1)) by lia; apply (Hoth 4%nat _ _ N4); [lia | clear - Ha Hr3; lia]|].
apply (arr32_frame trasegs _ _ _ _ AxK); intros a Ha; rewrite LK4 in Ha; exact (KX a Ha).
- split; [apply (arr32_frame trasegs _ _ _ _ AfK); intros a Ha; rewrite LK3 in Ha; exact (KF a Ha)|].
split; [apply (arr8_frame trasegs _ _ _ _ AhK); intros a Ha; rewrite LK2 in Ha; apply (mbyte_of_aview trasegs); replace a with (h1 + (a - h1)) by lia; apply (Hoth 6%nat _ _ N6); [lia | clear - Ha Hr3; lia]|].
split; [apply (arr8_frame trasegs _ _ _ _ AuK); intros a Ha; rewrite LK1 in Ha; exact (KU a Ha)|].
split; [apply (arr8_set_col_mem _ _ p1 (ht_pal K) idx c ApK ltac:(clear - Hidx; lia) ltac:(rewrite LK5; clear - Hidx; lia) Cok B0 B1 B2); intros t Ht Hnt; apply KIN; [rewrite LK5 in Ht; exact Ht | exact Hnt]|].
apply (arr32_frame trasegs _ _ _ _ AxK); intros a Ha; rewrite LK4 in Ha; exact (KX a Ha).
Qed.
Lemma saved_used : acallee_saved 20 /\ acallee_saved 21 /\ acallee_saved 22 /\ acallee_saved 24 /\ acallee_saved 26 /\ acallee_saved 27 /\ acallee_saved 23.
Proof. repeat split; unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate. Qed.
Lemma hl_ch : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2,
at_CHC lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2 ->
SRr trasegs W (cfgat regs A_col_hash mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_CHR mem2 md2 /\ at_CHR lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K j h2).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2 (HCM & HG & HR & G24 & G10 & G11 & G12 & G13 & G14 & Gra).
pose proof HCM as [HP HNw].
pose proof HP as (HC & (Af & Ah & Au) & HF & Hk & Hsp & Hsl & Pp & Px & Ph & Pu & Pf).
pose proof HF as (Hinv & HTc & HTlt & _). pose proof Hinv as ((L1 & L2 & L3 & _) & _).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hslots & Hobj & Himg & HPerm & Hperm & Hkept). pose proof (proj1 HJ) as HAR.
pose proof HG as (HinvK & Hj & Hused & Hfs & Hh2 & Hfree & Hcle & Hins).
pose proof HNw as ((AfK & AhK & AuK & ApK & AxK) & (LK1 & LK2 & _) & HTK). rewrite HTK in LK1, LK2.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & _). fold (ac_Tn C) in Tn1, Tn2.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3).
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres). pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rh_BL_nth_3 C p1 x1 h1 u1 f1) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
assert (INB : forall (q : nat) y, nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some y -> In y (ablocks B lyc Sc)).
{ intros q y Hq. eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. exact (nth_error_In _ _ Hq). }
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (Usp : spZ regs = sp0 + -512).
{ unfold spZ. rewrite G2, unsigned_lit_small by (rewrite Hs1; clear - Hceil Hslo Hshi H47 C1 HSTKA Has; lia). rewrite Hs1. lia. }
assert (Us0 : s0Z regs = sp0).
{ unfold s0Z. rewrite G8, unsigned_lit_small by (rewrite Hs1; clear - Hceil Hslo Hshi H47 C1 HSTKA Has; lia). rewrite Hs1. lia. }
assert (Hach : achain lyc (aview trasegs (w_H W) mem) (spZ regs) (s0Z regs) hk_ch).
{ rewrite Usp, Us0. replace (sp0 + -512) with (sp0 - 512) by lia. eapply hk_achain with (s1v := s1v); try eassumption.
- exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HOP))))))))).
- apply (Hslots 496 s0v). unfold hk_tab. cbn. clear. tauto.
- apply (Hslots 504 rav). unfold hk_tab. cbn. clear. tauto. }
assert (HPRE : afn_pre trasegs B TCOLHASH_STK lyc Sc W regs mem md hk_ch).
{ eapply afn_pre_at with (o := -512) (STK := STK) (sp0 := sp0); try eassumption.
- reflexivity.
- clear; lia.
- unfold TCOLHASH_STK. rewrite Hes. clear; lia.
- unfold TCOLHASH_STK. rewrite Hes. clear - HSTKA Has. lia.
- rewrite Gra. apply YK0s.ret_ok_even. rewrite unsigned_lit_small by (unfold HL_CHR; clear; lia). reflexivity.
- unfold raZ. rewrite Gra, unsigned_lit_small by (unfold HL_CHR; clear; lia). unfold HL_CHR. clear. lia. }
eapply SRr_mono.
{ apply (TCOLHASH lyc Sc W regs mem md hk_ch (ac_h C) (3 * ac_T C) (3 * j) h1 (3 * ac_Tn C) u1 (ac_Tn C) (ac_Tn C) 3 (ht_used K) (ht_keys K) (key (ac_H C) j) true h2 HPRE G10 G11 G12 G13 G14
(INB 2%nat _ N2) ltac:(clear - Hj; lia) ltac:(clear - Hj; lia) (INB 6%nat _ N6) ltac:(clear; lia) (INB 7%nat _ N7) ltac:(clear; lia)).
- split; [|left; split; reflexivity]. unfold key. apply (arr8_col3 trasegs _ _ _ _ Ah); [clear - Hj; lia | rewrite L2; unfold ac_T in Hj; clear - Hj; lia].
- exact AuK.
- exact AhK.
- exact LK1.
- exact LK2.
- clear - Tn2. lia.
- intros _. rewrite <- HTK. rewrite <- probe_of_htab. exact Hfs. }
cbv beta. intros W2 c2 _ (ly' & S' & regs' & mem' & md' & -> & HJsub & HPres & -> & -> & -> & Ha0).
split; [reflexivity|]. exists regs', mem', md'. split; [rewrite Gra; reflexivity|].
assert (HJ' : ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k).
{ replace k with (k + 0) by lia. change own with ([] ++ own).
eapply (ajournal_sub trasegs B LAWS tra_segs_low); [exact HJ | exact HJsub | rewrite Usp; unfold TCOLHASH_STK; rewrite Hes; clear - HSTKA Has; lia | rewrite Usp; clear; lia | intros a (r0 & [] & _)]. }
assert (HKc : acall_kept trasegs B lyc Sc W mem W mem' (spZ regs - TCOLHASH_STK) (spZ regs) (fun _ => False)).
{ eapply acall_kept_of_journal; first [exact HJsub | exact HAR | exact tra_segs_low | exact LAWS | (intros a (r0 & [] & _)) | (intros b m i0 Hb _ _; exact Hb)]. }
rewrite Usp in HKc. replace (sp0 + -512) with s1v in HKc by (rewrite Hs1; lia).
destruct saved_used as (Sv20 & Sv21 & Sv22 & Sv24 & Sv26 & Sv27 & Sv23).
split; [exact (rh_common_call_same lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K regs' mem' md' _ HCM HJ' HPres HKc)|].
split; [exact HG|].
destruct HR as (R20 & R21 & R22 & R26 & R27).
split; [unfold rh_used_regs; rewrite (aregs_get regs regs' 20%bv HPres Sv20), (aregs_get regs regs' 21%bv HPres Sv21), (aregs_get regs regs' 22%bv HPres Sv22),
(aregs_get regs regs' 26%bv HPres Sv26), (aregs_get regs regs' 27%bv HPres Sv27); repeat split; assumption|].
split; [rewrite (aregs_get regs regs' 24%bv HPres Sv24); exact G24 | exact Ha0].
Qed.
Lemma D_mul3_add : forall E n m v w, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 w -> 0 <= v < 2 ^ 30 -> 0 <= w < 2 ^ 62 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (w + 3 * v).
Proof.
intros E n m v w En Em Hv Hw. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n v En) by lia. rewrite (U_lit E 3) by lia. rewrite (U_atom E m w Em) by lia.
rewrite (zcanon_id (v * 3)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma D_add_mul3 : forall E n m v w, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 w -> 0 <= v < 2 ^ 30 -> 0 <= w < 2 ^ 62 ->
sv_denot E (SAlu ALU_ADD (SOff m 0) (SMd M_MUL (SOff n 0) (SLit 3))) = Z_to_bv 64 (w + 3 * v).
Proof.
intros E n m v w En Em Hv Hw. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n v En) by lia. rewrite (U_lit E 3) by lia. rewrite (U_atom E m w Em) by lia.
rewrite (zcanon_id (v * 3)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma D_add2 : forall E n m v w, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 w -> 0 <= v < 2 ^ 62 -> 0 <= w < 2 ^ 62 ->
sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = Z_to_bv 64 (w + v).
Proof.
intros E n m v w En Em Hv Hw. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n v En) by lia. rewrite (U_atom E m w Em) by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma hl_rm1 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2,
at_RM1C lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2 ->
SRr trasegs W (cfgat regs A_asan_memcpy mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_RM1R mem2 md2 /\ at_RM1R lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K j h2).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2 (HCM & HG & HR & G23 & G24 & G10 & G11 & G12 & Gra).
pose proof HG as (HinvK & Hj & Hused & Hfs & Hh2 & Hfree & Hcle & Hins). pose proof HCM as [_ (_ & _ & HTK)]. rewrite HTK in Hh2.
eapply SRr_mono; [exact (rh_copy3 true lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2 HL_RM1R HCM Hj Hh2 G10 G11 G12 Gra ltac:(unfold HL_RM1R; clear; lia) eq_refl)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HCM2 & HP2). split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
destruct saved_used as (Sv20 & Sv21 & Sv22 & Sv24 & Sv26 & Sv27 & Sv23). destruct HR as (R20 & R21 & R22 & R26 & R27).
split; [exact HCM2|]. split; [exact HG|].
split; [unfold rh_used_regs; rewrite (aregs_get regs regs2 20%bv HP2 Sv20), (aregs_get regs regs2 21%bv HP2 Sv21), (aregs_get regs regs2 22%bv HP2 Sv22),
(aregs_get regs regs2 26%bv HP2 Sv26), (aregs_get regs regs2 27%bv HP2 Sv27); repeat split; assumption|].
rewrite (aregs_get regs regs2 23%bv HP2 Sv23). exact G23.
Qed.
Lemma hl_rm2 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2,
at_RM2C lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2 ->
SRr trasegs W (cfgat regs A_asan_memcpy mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_RM2R mem2 md2 /\ at_RM2R lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K j h2).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2 (HCM & HG & HR & G23 & G24 & G10 & G11 & G12 & Gra).
pose proof HG as (HinvK & Hj & Hused & Hfs & Hh2 & Hfree & Hcle & Hins).
pose proof HCM as [(_ & _ & (Hinv & HTc & HTlt & _) & _) _]. pose proof Hinv as (_ & (HcntH & _) & _). pose proof HinvK as (_ & (HcntK & _) & _).
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & _). fold (ac_Tn C) in Tn1. unfold ac_T in Tn1.
eapply SRr_mono; [exact (rh_copy3 false lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (K_m1 K h2 (key (ac_H C) j)) j (ht_cnt K) HL_RM2R HCM Hj ltac:(clear - HcntH HcntK Hcle Tn1; lia) G10 G11 G12 Gra ltac:(unfold HL_RM2R; clear; lia) eq_refl)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HCM2 & HP2). split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
destruct saved_used as (Sv20 & Sv21 & Sv22 & Sv24 & Sv26 & Sv27 & Sv23). destruct HR as (R20 & R21 & R22 & R26 & R27).
split; [exact HCM2|]. split; [exact HG|].
split; [unfold rh_used_regs; rewrite (aregs_get regs regs2 20%bv HP2 Sv20), (aregs_get regs regs2 21%bv HP2 Sv21), (aregs_get regs regs2 22%bv HP2 Sv22),
(aregs_get regs regs2 26%bv HP2 Sv26), (aregs_get regs regs2 27%bv HP2 Sv27); repeat split; assumption|].
rewrite (aregs_get regs regs2 23%bv HP2 Sv23), (aregs_get regs regs2 24%bv HP2 Sv24). split; [exact G23 | exact G24].
Qed.
Lemma hl_chr : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2,
at_CHR lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2 ->
SRr trasegs W (cfgat regs HL_CHR mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_asan_memcpy mem2 md2 /\ at_RM1C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K j h2).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2 ([HP HNw] & HG & HR & G24 & G10).
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
assert (RT0 : 0 < T < 2 ^ 30) by (subst T; clear - HTc; cbv [ts_chain In] in HTc; lia).
assert (Rcnt : 0 <= ht_cnt K <= 10000) by (clear - HcntH HcntK Hcle Hzl HlenH Hz Hi HN; lia).
assert (Hin_h : In (ac_h C, 3 * T) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; exact (nth_error_In _ _ N2)).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md (ac_h C) (3 * T) HAR Hin_h Fceil) as (Hh0 & Hh1 & Hh2' & Hh3).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * j)) by (rewrite (HE 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = Z_to_bv 64 h1) by (rewrite (HE 22%nat 22%bv eq_refl); exact R22).
assert (E10 : ew E 10 = Z_to_bv 64 h2) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (E24 : ew E 24 = Z_to_bv 64 (ac_h C + 3 * j)) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
set (xat0 := [(10%nat, mkAF 0 16777215 0)]).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_CHR false [] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] [ck 296 (SOff 57 0)] [] xat0 [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_nil. }
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
{ subst xat0. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10, unsigned_lit_small by (clear - Hh2 Tn2; lia). rewrite Z.pow_0_r, Z.mod_1_r. clear - Hh2 Tn2. repeat split; lia. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 58 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_asan_memcpy.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 22; 24; 26; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
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
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HCM' : rh_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha p1 x1 h1 u1 f1 K) end.
{ apply (rh_common_run_same_3 lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K _ _ _ (conj HP HNw) HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | exact KM1 | split; [exact SP72' | exact SP56'] | exact Hsl']. }
split; [exact HCM'|]. split; [exact HG|]. split; [unfold rh_used_regs; rewrite (HKR 20%bv ltac:(cbv; clear; tauto)), (HKR 21%bv ltac:(cbv; clear; tauto)), (HKR 22%bv ltac:(cbv; clear; tauto)), (HKR 26%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)); exact HR|].
split; [apply (RD 23%bv (SOff 10 0) h2 eq_refl); [rewrite (denot_off E 10 h2 0 E10 ltac:(clear - Hh2 Tn2; lia)), Z.add_0_r; reflexivity | reflexivity]|].
split; [rewrite (HKR 24%bv ltac:(cbv; clear; tauto)); exact G24|].
split; [exact (RD 10%bv _ (h1 + 3 * h2) eq_refl (D_mul3_add E 10 22 h2 h1 E10 E22 ltac:(clear - Hh2 Tn2; lia) ltac:(clear - Ph; lia)) eq_refl)|].
split; [apply (RD 11%bv (SOff 24 0) (ac_h C + 3 * j) eq_refl); [rewrite (denot_off E 24 _ 0 E24 ltac:(clear - Hj Hh0 Hh2' Hh3 C1; lia)), Z.add_0_r; reflexivity | reflexivity]|].
split; [exact (RD 12%bv (SLit 3) 3 eq_refl eq_refl eq_refl) | exact (RD 1%bv (SLit HL_RM1R) HL_RM1R eq_refl eq_refl eq_refl)].
Qed.
Lemma hl_rm1r : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2,
at_RM1R lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2 ->
SRr trasegs W (cfgat regs HL_RM1R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_asan_memcpy mem2 md2 /\ at_RM2C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K j h2).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j h2 ([HP HNw] & HG & HR & G23).
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
assert (RT0 : 0 < T < 2 ^ 30) by (subst T; clear - HTc; cbv [ts_chain In] in HTc; lia).
assert (Rcnt : 0 <= ht_cnt K <= 10000) by (clear - HcntH HcntK Hcle Hzl HlenH Hz Hi HN; lia).
assert (Hin_h : In (ac_h C, 3 * T) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; exact (nth_error_In _ _ N2)).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md (ac_h C) (3 * T) HAR Hin_h Fceil) as (Hh0 & Hh1 & Hh2' & Hh3).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * j)) by (rewrite (HE 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = Z_to_bv 64 h1) by (rewrite (HE 22%nat 22%bv eq_refl); exact R22).
set (xat0 := [(38%nat, mkAF 0 10000 0)]).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_RM1R false [] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] [ck 296 (SOff 57 0)] [] xat0 [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_nil. }
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
{ subst xat0. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E38, unsigned_lit_small by (clear - Rcnt; lia). rewrite Z.pow_0_r, Z.mod_1_r. clear - Rcnt. repeat split; lia. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 58 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_asan_memcpy.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 22; 23; 26; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
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
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HCM' : rh_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha p1 x1 h1 u1 f1 (K_m1 K h2 (key (ac_H C) j))) end.
{ apply (rh_common_run_same_3 lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (K_m1 K h2 (key (ac_H C) j)) _ _ _ (conj HP HNw) HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | exact KM1 | split; [exact SP72' | exact SP56'] | exact Hsl']. }
split; [exact HCM'|]. split; [exact HG|]. split; [unfold rh_used_regs; rewrite (HKR 20%bv ltac:(cbv; clear; tauto)), (HKR 21%bv ltac:(cbv; clear; tauto)), (HKR 22%bv ltac:(cbv; clear; tauto)), (HKR 26%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)); exact HR|].
split; [rewrite (HKR 23%bv ltac:(cbv; clear; tauto)); exact G23|].
split; [apply (RD 24%bv (SOff 32 40) (tb + 40) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [exact (RD 10%bv _ (p1 + 3 * ht_cnt K) eq_refl (D_add_mul3 E 38 36 (ht_cnt K) p1 E38 E36 ltac:(clear - Rcnt; lia) ltac:(clear - Pp; lia)) eq_refl)|].
split; [exact (RD 11%bv _ (ac_h C + 3 * j) eq_refl (D_add2 E 20 34 (3 * j) (ac_h C) E20 E34 ltac:(clear - Hj RT0; lia) ltac:(clear - Hh0 Hh2' Hh3 C1; lia)) eq_refl)|].
split; [exact (RD 12%bv (SLit 3) 3 eq_refl eq_refl eq_refl) | exact (RD 1%bv (SLit HL_RM2R) HL_RM2R eq_refl eq_refl eq_refl)].
Qed.
End d.
