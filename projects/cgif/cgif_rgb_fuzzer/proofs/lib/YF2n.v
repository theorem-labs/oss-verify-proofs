(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k YF0q YF0o YF1g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, zone3cases, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, KSTACK, TFX_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFX_TP, TFX_TSD,
A_QUAR, A_ALLOCATOR, o_quar, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kMaxSize, kChunkHeaderSize in *.
Definition rT : nat := 32.
Definition rC : nat := 33.
Definition rSB : nat := 34.
Definition rM : nat := 35.
Definition rCL : nat := 36.
Definition rBASE : nat := 37.
Definition rHW : nat := 38.
Definition rN : nat := 39.
Definition rSHB : nat := 40.
Definition rSP : nat := 41.
Definition rN8 : nat := 42.
Definition rCNT8 : nat := 43.
Definition rCBP : nat := 44.
Definition rMU : nat := 45.
Definition rRG : nat := 46.
Definition rRI : nat := 47.
Definition rSZ : nat := 48.
Definition rJ1 : nat := 49.   Definition rJ2 : nat := 50.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (c base rz nn hb1 cbp muc j1 j2 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Definition Mv : Z := base + rz - kChunkHeaderSize.
Definition Uv : Z := base + rz.
Definition HWv : Z := 3 + 256 * hb1.
Definition SPv : Z := SHADOW_OFF + Uv / 8.
Definition N8v : Z := (nn + 7) / 8 * 8.
Definition CNT8v : Z := N8v / 8.
Definition RIv : Z := SB + kRegionInfoOff.
Definition RGv : Z := RIv + 128 * c.
Definition SZv : Z := class_size c.
Definition RELv : Z := base - SB - region_off c.
Definition OFFv : Z := base - SB.
Definition XW : list word :=
[ w64 T; w64 (ly_C ly); w64 SB; w64 Mv; w64 c; w64 base; w64 HWv; w64 nn; w64 SHADOW_OFF; w64 SPv; w64 N8v; w64 CNT8v;
w64 cbp; w64 muc; w64 RGv; w64 RIv; w64 SZv; w64 j1; w64 j2 ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. img_exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. img_exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. img_exact (Er 1 1%bv eq_refl). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. img_refl. Qed.
Lemma EqC : ew E0 33 = w64 (ly_C ly). Proof. img_refl. Qed.
Lemma EqSB : ew E0 34 = w64 SB. Proof. img_refl. Qed.
Lemma EqM : ew E0 35 = w64 Mv. Proof. img_refl. Qed.
Lemma EqCL : ew E0 36 = w64 c. Proof. img_refl. Qed.
Lemma EqBASE : ew E0 37 = w64 base. Proof. img_refl. Qed.
Lemma EqHW : ew E0 38 = w64 HWv. Proof. img_refl. Qed.
Lemma EqN : ew E0 39 = w64 nn. Proof. img_refl. Qed.
Lemma EqSHB : ew E0 40 = w64 SHADOW_OFF. Proof. img_refl. Qed.
Lemma EqSP : ew E0 41 = w64 SPv. Proof. img_refl. Qed.
Lemma EqN8 : ew E0 42 = w64 N8v. Proof. img_refl. Qed.
Lemma EqCNT8 : ew E0 43 = w64 CNT8v. Proof. img_refl. Qed.
Lemma EqCBP : ew E0 44 = w64 cbp. Proof. img_refl. Qed.
Lemma EqMU : ew E0 45 = w64 muc. Proof. img_refl. Qed.
Lemma EqRG : ew E0 46 = w64 RGv. Proof. img_refl. Qed.
Lemma EqRI : ew E0 47 = w64 RIv. Proof. img_refl. Qed.
Lemma EqSZ : ew E0 48 = w64 SZv. Proof. img_refl. Qed.
Lemma EqJ1 : ew E0 49 = w64 j1. Proof. img_refl. Qed.
Lemma EqJ2 : ew E0 50 = w64 j2. Proof. img_refl. Qed.
Definition R_STK : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- 256) 0 (- 256) 0 [].
Definition R_CB : YQ0b.region := YQ0b.mkRegion (Some 44%nat) 0 16 0 0 [YQ0b.mkChunk 0 (CVal 8 (SOff 32%nat t_cache))].
Definition R_HDR : YQ0b.region := YQ0b.mkRegion (Some 35%nat) 0 8 0 4 [YQ0b.mkChunk 0 (CVal 4 (SOff 38%nat 0)); YQ0b.mkChunk 4 (CVal 4 (SOff 39%nat 0))].
Definition R_RGMU : YQ0b.region := YQ0b.mkRegion (Some 46%nat) 48 56 0 0 [YQ0b.mkChunk 48 (CVal 8 (SOff 45%nat 0))].
Definition R_CTX : YQ0b.region := YQ0b.mkRegion (Some 33%nat) 0 160 0 0 [YQ0b.mkChunk 8 (CVal 4 (SLit 0)); YQ0b.mkChunk 152 (CVal 8 (SOff 32%nat 0))].
Definition R_JST : YQ0b.region :=
YQ0b.mkRegion (Some 32%nat) (t_stats + 40) (t_stats + 56) (t_stats + 40) (t_stats + 56)
[YQ0b.mkChunk (t_stats + 40) (CVal 8 (SOff 49%nat 0)); YQ0b.mkChunk (t_stats + 48) (CVal 8 (SOff 50%nat 0))].
Definition REG0 {imgk : img} : smem :=
[ R_STK; R_CB; R_HDR; R_RGMU; R_CTX; R_JST;
fatom8 (A_ALLOCATOR + 32) 34%nat  ; fatom8 (A_ALLOCATOR + 48) 47%nat  ;
flit8 (0x10328 + D_10) 0xCC6E96B9CC6E96B9  ;
flit1 (0xaae98 + D_10c0) 1; flit4 (0xaaebc + D_10c0) 30; flit8 (0xa2150 + D_10f0) (0x13bce8 + D_10c0); flit8 (0x13bd08 + D_10c0) 0x1e00010000;
flit1 (0xa9a20 + D_10c0) 1; flit4 (0xa9a24 + D_10c0) 0; flit1 (0xa9a1c + D_10c0) 1;
flit8 (0xa2158 + D_10f0) (0xa79b8 + D_10c0); flit8 (0xa79e8 + D_10c0) 0xbe00000000; flits8 (0xa7a00 + D_10c0) [0x1000100000000; 0x101010101000001];
flit8 (0xa2160 + D_10f0) (0xaa1b8 + D_10c0); fatom8 (0xaa1b8 + D_10c0) 40%nat;
flit8 (0xa2168 + D_10f0) (0xaaea8 + D_10c0); flit8 (0xa2170 + D_10f0) (0xaaeb0 + D_10c0); flit8 (0xa2178 + D_10f0) (0xaaea0 + D_10c0);
flit8 (0xaaea0 + D_10c0) 0x7fffffffffff; flit8 (0xaaea8 + D_10c0) 0; flit8 (0xaaeb0 + D_10c0) 0;
flit8 (0xa2180 + D_10f0) (0xa4000 + D_10f0); flit8 (0xa4000 + D_10f0) (0x9b894 + D_10ec);
flit8 (TFX_TP - 88) TFX_TSD; fatom8 TFX_TSD 33%nat ].
Definition R_MAG : YQ0b.region := YQ0b.mkRegion (Some 37%nat) 0 8 0 8 [YQ0b.mkChunk 0 (CVal 8 (SLit 0xCC6E96B9CC6E96B9))].
Definition FFR : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + KSTACK) kHighMemEnd 4);
(32%nat, mkAF 4096 (CEIL_MAX - 4096) 12)    ;
(33%nat, mkAF 4096 (CEIL_MAX - 256) 3)      ;
(34%nat, mkAF kHighMemBeg CEIL_MAX 16);
(35%nat, mkAF kHighMemBeg (CEIL_MAX - 16) 4);
(36%nat, mkAF 1 30 0);
(37%nat, mkAF kHighMemBeg (CEIL_MAX - 32) 4);
(38%nat, mkAF 0 65535 0);
(39%nat, mkAF 1 (2 ^ 28) 0);
(40%nat, mkAF 0x7fff8000 0x7fff8000 12);
(41%nat, mkAF 0x2008fff7000 0x10007fff7fff 1);
(42%nat, mkAF 8 (2 ^ 28 + 8) 3);
(43%nat, mkAF 1 (2 ^ 25 + 1) 0);
(44%nat, mkAF kHighMemBeg (kHighMemEnd - 16) 3);
(45%nat, mkAF 0 kFreeArrayOffset 0);
(46%nat, mkAF kHighMemBeg (CEIL_MAX - 128) 7);
(47%nat, mkAF kHighMemBeg (CEIL_MAX - 4096) 12);
(48%nat, mkAF 32 kMaxSize 5);
(49%nat, mkAF 0 (2 ^ 64 - 1) 0);
(50%nat, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition SR0 {imgk : img} : list sv := sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFX_TP)) 10%bv (SOff 44%nat 0)) 11%bv (SOff 35%nat 0).
Definition SS0 {imgk : img} : sstate := mkSS (0x33b74 + D_150) SR0 REG0 None FFR.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x33b74 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_Htp : getr regs0 4 = w64 TFX_TP;
fh_Hra : YK0s.ret_ok (getr regs0 1);
fh_Hra4096 : 4096 <= bv_unsigned (getr regs0 1);
fh_Hsp : ly_stk_lo ly + KSTACK <= sp0 /\ sp0 <= ly_stk_hi ly;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 - KSTACK <= a < sp0 -> apresent (w_H W) mem0 a;
fh_cb : sp0 <= cbp /\ cbp + 16 <= ly_stk_hi ly /\ cbp mod 8 = 0 /\ (forall a, cbp <= a < cbp + 16 -> apresent (w_H W) mem0 a) /\
val_mem tfxsegs m0 cbp 8 (T + t_cache);
fh_Hc : 1 <= c <= 30;
fh_Hbase : 0 <= RELv /\ RELv + SZv <= muc /\ RELv mod SZv = 0 /\ 0 <= muc <= kFreeArrayOffset /\ base mod 16 = 0;
fh_Hrz : 16 <= rz <= 2048 /\ rz mod 16 = 0 /\ rz + nn <= SZv;
fh_Hnn : 1 <= nn < 2 ^ 28;
fh_Hhb1 : 0 <= hb1 < 256;
fh_hdr : val_mem tfxsegs m0 Mv 4 HWv /\ val_mem tfxsegs m0 (Mv + 4) 4 nn /\ (forall a, base <= a < base + SZv -> apresent (w_H W) mem0 a);
fh_mag : rz <> 16 -> val_mem tfxsegs m0 base 8 0xCC6E96B9CC6E96B9;
fh_sh_pres : forall a, SPv <= a < SPv + CNT8v -> apresent (w_H W) mem0 a;
fh_rg : (forall a, RGv + 48 <= a < RGv + 56 -> apresent (w_H W) mem0 a) /\ val_mem tfxsegs m0 (RGv + 48) 8 muc;
fh_Hjunk : 0 <= j1 < 2 ^ 64 /\ 0 <= j2 < 2 ^ 64;
fh_SEED : st_ok tfxsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 (0x33b74 + D_150)) mem0 (seg_rom tfxsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH :=
pose proof (fh_LY FH) as LY;
pose proof (fh_IMG FH) as IMG;
pose proof (fh_Htp FH) as Htp;
pose proof (fh_Hra FH) as Hra;
pose proof (fh_Hra4096 FH) as Hra4096;
pose proof (fh_Hsp FH) as Hsp;
pose proof (fh_Hsp_al FH) as Hsp_al;
pose proof (fh_pres FH) as Hpres;
pose proof (fh_cb FH) as Hcb;
pose proof (fh_Hc FH) as Hc;
pose proof (fh_Hbase FH) as Hbase;
pose proof (fh_Hrz FH) as Hrz;
pose proof (fh_Hnn FH) as Hnn;
pose proof (fh_Hhb1 FH) as Hhb1;
pose proof (fh_hdr FH) as Hhdr;
pose proof (fh_mag FH) as Hmag;
pose proof (fh_sh_pres FH) as Hsh_pres;
pose proof (fh_rg FH) as Hrg;
pose proof (fh_Hjunk FH) as Hjunk;
pose proof (fh_SEED FH) as SEED.
Lemma LYB :
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly <= SB /\
SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < ly_top ly /\ ly_top ly <= ly_stk_hi ly /\ ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly /\
(T + kThreadObjSize <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= T) /\
(T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_hi ly <= T) /\ (ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly) /\
SB mod 65536 = 0 /\ zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ ly_C ly mod 8 = 0 /\
(T + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= T) /\ (ly_prim ly + kPrimResvSize <= ly_C ly \/ ly_C ly + 256 <= ly_prim ly) /\
(ly_C ly + 256 <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_C ly) /\ T mod 4096 = 0.
Proof.
open_FH.
pose proof (lo_high ly LY) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD0.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(img_try (clear_all; unfold kThreadObjSize; img_lia)) (Forall_nth_f _ _ 2 _ HA eq_refl) (pairwise_ij_f _ _ 2 6 _ _ HD0 eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(img_try (clear_all; img_lia)) (Forall_nth_f _ _ 6 _ HA eq_refl) (pairwise_ij_f _ _ 6 2 _ _ HD0 eq_refl eq_refl)) as ZC. clear HA.
pose proof (lo_space_in ly LY) as HSP. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_al ly LY) as SAL.
pose proof (lo_C_al ly LY) as CAL. pose proof (lo_T_al ly LY) as TAL. unfold page_aligned in TAL.
pose proof HD0 as HD. clear HD0. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & _ & _ & _ & DC & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PC DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DC as [_ DC]. apply Forall_cons_iff in DC as [CSTK _].
unfold zdisjoint in PT, PSTK, TSTK, PC, TC, CSTK. cbn [fst snd] in *. unfold T, SB in *.
split; [img_try (img_exact ZT)|]. split; [img_try (clear - ZT; unfold zone3 in ZT; img_lia)|].
assert (ZC2 : ly_C ly + 256 <= ASAN_CEIL) by (img_try (clear - ZC; unfold zone3 in ZC; img_lia)).
clear - IP HSP T1 T2 T3 T4 T5 T6 T7 PT PSTK TSTK PC TC CSTK SAL CAL TAL ZC ZC2. unfold kHighMemBeg, kThreadObjSize, kPrimResvSize in *.
repeat match goal with |- _ /\ _ => split end; first [img_exact ZC | img_lia].
Qed.
Lemma class_facts : 32 <= SZv <= kMaxSize /\ SZv mod 32 = 0 /\ region_off c = c * 2 ^ 32 /\ 0 <= region_off c /\ region_off c + 2 ^ 32 <= 31 * 2 ^ 32.
Proof.
open_FH. pose proof (class_ok c ltac:(img_lia)) as (K1 & K2 & K3 & _). unfold SZv. unfold region_off. rewrite Z.shiftl_mul_pow2 by img_lia.
assert (32 <= class_size c) by (img_try (apply Z.mod_divide in K2 as [q Hq]; [|img_lia]; nia)).
repeat split; img_lia.
Qed.
Lemma derived_ranges :
4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= SB /\ SB + kSpaceSize <= ASAN_CEIL /\ SB mod 65536 = 0 /\
kHighMemBeg + KSTACK <= sp0 /\ sp0 <= kHighMemEnd /\ sp0 <= cbp /\ cbp + 16 <= kHighMemEnd /\ cbp mod 8 = 0 /\
SB + 2 ^ 32 <= base /\ base + SZv <= SB + 31 * 2 ^ 32 /\ base mod 16 = 0 /\ base = SB + region_off c + RELv /\
Mv = base + rz - 16 /\ Uv = base + rz /\ Mv mod 16 = 0 /\ Uv mod 16 = 0 /\ base <= Mv /\ Uv + nn <= base + SZv /\
0 <= HWv < 65536 /\ HWv = 3 + 256 * hb1 /\ 1 <= nn < 2 ^ 28 /\ 16 <= rz <= 2048 /\
0x2008fff7000 <= SPv /\ SPv + CNT8v <= kHighMemBeg /\ N8v = 8 * CNT8v /\ nn <= N8v < nn + 8 /\ 1 <= CNT8v /\
RIv = SB + kRegionInfoOff /\ RGv = RIv + 128 * c /\ RIv + 128 <= RGv /\ RGv + 128 <= RIv + 4096 /\ RIv + 4096 <= ASAN_CEIL /\
0 <= muc <= kFreeArrayOffset /\ 0 <= RELv /\ RELv + SZv <= muc /\ OFFv = region_off c + RELv /\
4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL /\ 0 <= j1 < 2 ^ 64 /\ 0 <= j2 < 2 ^ 64.
Proof.
open_FH. pose proof LYB as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _ & _ & _ & L15 & L16 & L17 & L18 & _ & _ & _ & L22).
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). destruct Hsp as [S1 S2]. destruct Hcb as (C1 & C2 & C3 & _ & _).
destruct Hbase as (B1 & B2 & B3 & B4 & B5). destruct Hrz as (R1 & R2 & R3). destruct Hjunk as [J1 J2].
clear Hpres Hhdr Hmag Hsh_pres Hrg SEED Hra Htp LY FH.
assert (L1' : 4096 <= T) by (img_try (clear - L1; unfold zone3 in L1; img_lia)). assert (L16' : 4096 <= ly_C ly) by (img_try (clear - L16; unfold zone3 in L16; img_lia)). clear L1 L16 IMG.
unfold SPv, CNT8v, N8v, RGv, RIv, Mv, Uv, OFFv, RELv, HWv, SZv in *. rewrite K3 in *.
assert (U16 : (base + rz) mod 16 = 0).
{ apply Z.mod_divide in B5 as [q Hq]; [|img_lia]. apply Z.mod_divide in R2 as [q' Hq']; [|img_lia]. img_apply Z.mod_divide; [img_lia|]. exists (q + q'). img_lia. }
assert (M16 : (base + rz - kChunkHeaderSize) mod 16 = 0).
{ pose proof U16 as U16'. apply Z.mod_divide in U16' as [q Hq]; [|img_lia]. img_apply Z.mod_divide; [img_lia|]. exists (q - 1). unfold kChunkHeaderSize. img_lia. }
pose proof (Z.div_mod (nn + 7) 8 ltac:(img_lia)) as DM. pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(img_lia)) as MB.
set (q8 := (nn + 7) / 8) in *. rewrite (Z_div_mult q8 8) by img_lia.
numconst. unfold kChunkHeaderSize in *.
assert (UB1 : (base + rz + q8 * 8) / 8 <= 140737479966720 / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). rewrite Z_div_plus in UB1 by img_lia.
assert (UB3 : 17594333495296 / 8 <= (base + rz) / 8) by (img_try (img_apply Z.div_le_mono; img_lia)).
repeat split; try assumption; clear B3 B5 R2 U16 M16 L15 L18 L22 C3 Hsp_al K2 MB; img_lia.
Qed.
Definition WINF (a : Z) : Prop :=
(Mv <= a < Mv + 4) \/ (rz <> 16 /\ base <= a < base + 8) \/ (T + t_stats + 40 <= a < T + t_stats + 56).
Definition WINS (a : Z) : Prop := SPv <= a < SPv + CNT8v.
Definition WIN (a : Z) : Prop := (sp0 - 256 <= a < sp0) \/ WINF a \/ WINS a.
Definition win_sub (t w : option nat * Z * Z) : bool :=
obase_eqb (fst (fst t)) (fst (fst w)) && (snd (fst w) <=? snd (fst t)) && (snd t <=? snd w).
Lemma win_sub_sound : forall E a t w, win_sub t w = true ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t ->
base_val E (fst (fst w)) + snd (fst w) <= a < base_val E (fst (fst w)) + snd w.
Proof.
intros E a [[bt lt] ht] [[bu lu] hu] Hs Hr. unfold win_sub in Hs. cbn [fst snd] in *.
apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct bt as [x|], bu as [y|]; cbn in H1; try discriminate.
- apply Nat.eqb_eq in H1. (subst; cbv beta). img_lia.
- img_lia.
Qed.
Definition WSK0 : list (option nat * Z * Z) :=
[(Some 2%nat, -256, 0); (Some 35%nat, 0, 4); (Some 32%nat, t_stats + 40, t_stats + 56)].
Definition WSKM : list (option nat * Z * Z) := WSK0 ++ [(Some 37%nat, 0, 8)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. pose proof derived_ranges as DR. decompose [and] DR. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN, WINF.
unfold aHAVf in *. numconst.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (img_try ((img_case; cbv); img_lia)); rewrite ?E2, ?EqT, ?EqM in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by img_lia;
unfold sp0 in *; img_lia.
Qed.
Lemma WSKM_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> rz <> 16 -> sk_ok E WSKM.
Proof.
open_FH. intros E HE Hrz16 t a Hin Hr. unfold WSKM in Hin. apply in_app_iff in Hin as [Hin|Hin]; [img_try (img_exact (WSK0_ok E HE t a Hin Hr))|].
pose proof derived_ranges as DR. decompose [and] DR. cbn [In] in Hin. unfold WIN, WINF. unfold aHAVf in *. numconst.
destruct Hin as [<-|[]]; cbn [fst snd base_val] in Hr; rewrite HE in Hr by (img_try ((img_case; cbv); img_lia)); rewrite ?EqBASE in Hr; unfold w64 in Hr;
rewrite unsigned_lit_small in Hr by img_lia; right; left; right; left; split; [img_try (img_exact Hrz16) | img_lia].
Qed.
Lemma windows_WIN : forall (E : env) SK rs a,
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
intros E SK rs a HSK Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). img_exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. img_lia.
Qed.
Lemma WIN_zone : forall a, WIN a -> ~ (TFX_IMG_LO <= a < TFX_IMG_END) /\ (~ (kLowShadowBeg <= a < kHighMemBeg) \/ WINS a) /\ 0 <= a < 2 ^ 64.
Proof.
open_FH. intros a Hw. pose proof derived_ranges as DR. pose proof LYB as (F1 & _). unfold WIN, WINF in Hw.
destruct Hw as [Hw|[Hw|Hw]].
- clear - Hw DR. numconst. img_lia.
- clear - Hw DR F1. numconst. img_lia.
- split; [|img_try (split; [right; img_exact Hw|])]; unfold WINS in Hw; clear - Hw DR; numconst; img_lia.
Qed.
Lemma WIN_off : forall a, WIN a -> off_img a.
Proof. intros a Hw. destruct (WIN_zone a Hw) as (A & B & C). unfold off_img. clear - A C. unfold TFX_IMG_LO, TFX_IMG_END in *. img_lia. Qed.
Lemma notWIN_img : forall a, TFX_IMG_LO <= a < TFX_IMG_END -> ~ WIN a.
Proof. intros a Ha Hw. destruct (WIN_zone a Hw) as (A & _). img_exact (A Ha). Qed.
Lemma off_T : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. img_exact (zone3_off_img _ _ a (proj1 LYB) Ha). Qed.
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats, t_stats; tac
| unfold off_img; unfold TFX_IMG_LO; unfold TFX_IMG_END; tac ].
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> m x = mem0 x.
Lemma MEQ_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQ m -> MEQ m'.
Proof. intros E SK rs m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WIN E SK rs _ HSK Hb Hw). Qed.
Lemma MEQ_0 : MEQ mem0. Proof. intros x _. img_refl. Qed.
Lemma st_ok_forget_reg : forall (E : env) ss ms (r : bv 5) (k : nat),
st_ok tfxsegs E ss ms -> r <> 0%bv -> ss_atoms_lt k ss = true ->
st_ok tfxsegs (havoc E k [getr (ms_regs ms) r]) (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff k 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r k HS Hr Hk.
img_apply st_ok_pin_reg; [ | img_try (img_exact Hr) | ].
- eapply (st_ok_agree tfxsegs k); [img_try (img_exact HS) | img_try (img_apply env_agree_havoc) | img_try (img_exact Hk)].
- pose proof (ew_havoc_new E k [getr (ms_regs ms) r] 0 (Z_to_bv 64 0) ltac:(img_try (cbn; img_lia))) as Hn. rewrite Nat.add_0_r in Hn. cbn [nth] in Hn.
cbn [sv_denot]. rewrite Hn, Z.add_0_r. img_apply Z_to_bv_bv_unsigned.
Qed.
Definition within {imgk : img} (D : Z -> Prop) (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> D a.
Lemma within_mono : forall (D D' : Z -> Prop) E SK, (forall a, D a -> D' a) -> within D E SK -> within D' E SK.
Proof. intros D D' E SK HD HK t a Hin Hr. img_apply HD. img_exact (HK t a Hin Hr). Qed.
Lemma windows_within : forall (D : Z -> Prop) (E : env) SK rs a,
within D E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> D a.
Proof.
intros D E SK rs a HSK Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). img_exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. img_lia.
Qed.
Lemma frame_within : forall (D : Z -> Prop) (E : env) SK rs (m m' : word -> option byte),
within D E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ D (bv_unsigned x) -> m' x = m x.
Proof. intros D E SK rs m m' HK Hb HF x Hx. img_apply HF. intros Hw. img_apply Hx. img_exact (windows_within D E SK rs _ HK Hb Hw). Qed.
Definition MEQP {imgk : img} (D : Z -> Prop) (m : word -> option byte) : Prop := forall x : word, ~ D (bv_unsigned x) -> m x = mem0 x.
Lemma MEQP_frame : forall (D : Z -> Prop) (E : env) SK rs (m m' : word -> option byte),
within D E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQP D m -> MEQP D m'.
Proof. intros D E SK rs m m' HK Hb HF M x Hx. rewrite <- (M x Hx). img_exact (frame_within D E SK rs m m' HK Hb HF x Hx). Qed.
Lemma MEQP_weaken : forall (D D' : Z -> Prop) m, (forall a, D a -> D' a) -> MEQP D m -> MEQP D' m.
Proof. intros D D' m HD M x Hx. img_apply M. intros Hd. img_apply Hx. img_exact (HD _ Hd). Qed.
Lemma MEQP_0 : forall D, MEQP D mem0. Proof. intros D x _. img_refl. Qed.
Lemma MEQ_of_MEQP : forall m, MEQP WIN m -> MEQ m. Proof. intros m M x Hx. img_exact (M x Hx). Qed.
Definition WIN0 (a : Z) : Prop := (sp0 - 256 <= a < sp0) \/ (Mv <= a < Mv + 4) \/ (T + t_stats + 40 <= a < T + t_stats + 56).
Definition WINX (a : Z) : Prop := (sp0 - 256 <= a < sp0) \/ WINF a.
Definition MAGR (a : Z) : Prop := rz <> 16 /\ base <= a < base + 8.
Lemma WIN0_WINX : forall a, WIN0 a -> WINX a. Proof. intros a Ha. unfold WIN0, WINX, WINF in *. tauto. Qed.
Lemma WINX_WIN : forall a, WINX a -> WIN a. Proof. intros a Ha. unfold WINX, WIN in *. tauto. Qed.
Lemma WINS_WIN : forall a, WINS a -> WIN a. Proof. intros a Ha. unfold WIN. tauto. Qed.
Lemma MAGR_WINX : forall a, MAGR a -> WINX a. Proof. intros a [H1 H2]. unfold WINX, WINF. tauto. Qed.
Lemma WINX_not_WINS : forall a, WINX a -> ~ WINS a.
Proof.
open_FH. intros a Ha Hs.
pose proof derived_ranges as (dT1 & dT2 & dS1 & dS2 & dSal & dK1 & dK2 & dCB1 & dCB2 & dCBal & dB1 & dB2 & dBal & dBeq & dM1 & dU1 & dMal & dUal & dBM & dUN & dHW1 & dHW2 & dN1 & dRZ & dSP1 & dSP2 & _).
pose proof (proj1 LYB) as F1.
clear SEED Hpres Hcb Hhdr Hmag Hsh_pres Hrg LY Hbase Hrz. unfold WINX, WINF, WINS in *. numconst. unfold sp0, T, SB in *. img_lia.
Qed.
Lemma WIN0_not_MAGR : forall a, WIN0 a -> ~ MAGR a.
Proof.
open_FH. intros a Ha [Hne Hm]. destruct Hrz as (R1 & R2 & R3).
assert (R32 : 32 <= rz). { apply Z.mod_divide in R2 as [q Hq]; [|img_lia]. assert (Hq1 : q <> 1) by (img_try (intros ->; img_apply Hne; img_lia)). clear - Hq Hq1 R1. img_lia. }
pose proof derived_ranges as (dT1 & dT2 & dS1 & dS2 & dSal & dK1 & dK2 & dCB1 & dCB2 & dCBal & dB1 & dB2 & dBal & dBeq & dM1 & _). pose proof class_facts as (K1 & _).
pose proof LYB as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & _).
destruct Hsp as [S1 S2]. clear SEED Hpres Hcb Hhdr Hmag Hsh_pres Hrg LY Hbase.
unfold WIN0 in Ha. numconst. unfold sp0, T, SB in *.
destruct Ha as [Ha|[Ha|Ha]]; [img_try (clear L12 L13) | img_try (clear L12 L13 L14) | img_try (clear L13 L14)]; img_lia.
Qed.
Lemma WSK0_within : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> within WIN0 E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. pose proof derived_ranges as DR. decompose [and] DR. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN0.
unfold aHAVf in *. numconst.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (img_try ((img_case; cbv); img_lia)); rewrite ?E2, ?EqT, ?EqM in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by img_lia;
unfold sp0 in *; img_lia.
Qed.
Lemma WSKM_within : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> rz <> 16 -> within WINX E WSKM.
Proof.
open_FH. intros E HE Hrz16 t a Hin Hr. unfold WSKM in Hin. apply in_app_iff in Hin as [Hin|Hin]; [img_try (img_exact (WIN0_WINX a (WSK0_within E HE t a Hin Hr)))|].
pose proof derived_ranges as DR. decompose [and] DR. cbn [In] in Hin. unfold WINX, WINF. unfold aHAVf in *. numconst.
destruct Hin as [<-|[]]; cbn [fst snd base_val] in Hr; rewrite HE in Hr by (img_try ((img_case; cbv); img_lia)); rewrite ?EqBASE in Hr; unfold w64 in Hr;
rewrite unsigned_lit_small in Hr by img_lia; right; right; left; split; [img_try (img_exact Hrz16) | img_lia].
Qed.
Definition MAG (m : word -> option byte) : Prop :=
rz <> 16 -> val_mem tfxsegs (mrestrict (w_H W) m) base 8 0 /\ (forall a, base <= a < base + 8 -> apresent (w_H W) m a).
Lemma MAG_frame : forall (E : env) SK rs (m m' : word -> option byte),
within WIN0 E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MAG m -> MAG m'.
Proof.
open_FH. intros E SK rs m m' HK Hb HF MG Hne. destruct (MG Hne) as [V P].
pose proof derived_ranges as (dT1 & dT2 & dS1 & dS2 & dSal & dK1 & dK2 & dCB1 & dCB2 & dCBal & dB1 & dB2 & _). pose proof class_facts as (K1 & _).
assert (EQ : forall a, base <= a < base + 8 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
{ intros a Ha. img_apply (frame_within WIN0 E SK rs m m' HK Hb HF). rewrite unsigned_lit_small by (img_try (clear - Ha dS1 dS2 dB1 dB2 K1; numconst; img_lia)).
intros Hw. img_apply (WIN0_not_MAGR _ Hw). split; [img_try (img_exact Hne) | img_try (img_exact Ha)]. }
split.
- eapply val_mem_frame; [|img_try (img_exact V)]. intros k Hk. img_apply EQ. img_lia.
- intros a Ha. img_apply (apresent_same (w_H W) m); [img_try (img_apply EQ; img_exact Ha) | img_try (img_apply P; img_exact Ha)].
Qed.
Definition SHD (m : word -> option byte) : Prop := forall i, 0 <= i < CNT8v -> m (w64 (SPv + i)) = Some (Z_to_bv 8 250).
Lemma SHD_frame : forall (E : env) SK rs (m m' : word -> option byte),
within WIN0 E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> SHD m -> SHD m'.
Proof.
open_FH. intros E SK rs m m' HK Hb HF SH i Hi. rewrite <- (SH i Hi).
pose proof derived_ranges as (dT1 & dT2 & dS1 & dS2 & dSal & dK1 & dK2 & dCB1 & dCB2 & dCBal & dB1 & dB2 & dBal & dBeq & dM1 & dU1 & dMal & dUal & dBM & dUN & dHW1 & dHW2 & dN1 & dRZ & dSP1 & dSP2 & _).
img_apply (frame_within WIN0 E SK rs m m' HK Hb HF). unfold w64. rewrite unsigned_lit_small by (img_try (clear - Hi dSP1 dSP2; numconst; img_lia)).
intros Hw. img_apply (WINX_not_WINS _ (WIN0_WINX _ Hw)). unfold WINS. clear - Hi. img_lia.
Qed.
Lemma all_disjoint_of_forall : forall (E : env) r rs,
(forall r', In r' rs -> extent_disjoint E r r') -> all_disjoint E r rs.
Proof. intros E r rs H. induction rs as [|r' rs IH]; cbn; [img_try (img_exact I)|]. split; [img_try (img_apply H; left; img_refl) | img_try (img_apply IH; intros x Hx; img_apply H; right; img_exact Hx)]. Qed.
Definition SREGS : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition at_CD (W' : world tfxsegs) (cfg' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
cfg' = mkCfg (mkst regs' (w64 (0x33f78 + D_150)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ getr regs' 1 = getr regs0 1 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 10 = w64 (T + t_cache) /\ getr regs' 11 = w64 A_ALLOCATOR /\ getr regs' 12 = w64 c /\ getr regs' 13 = w64 base /\
MEQ mem' /\
(forall a, WIN a -> apresent (w_H W) mem' a) /\
let mr := mrestrict (w_H W) mem' in
val_mem tfxsegs mr Mv 4 (HWv - 3) /\
(rz <> 16 -> val_mem tfxsegs mr base 8 0) /\
(forall i, 0 <= i < CNT8v -> mem' (w64 (SPv + i)) = Some (Z_to_bv 8 250)).
End e.
End d.
