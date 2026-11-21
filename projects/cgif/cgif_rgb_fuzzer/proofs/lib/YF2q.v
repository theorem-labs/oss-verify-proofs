(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (munmap's refused answer, -ENOMEM: the new die_at_ecall walks that child through the munmap-failure report to its self-jump spin, the walk being a check, die_walk_ok, computed on the ecall state its callers hold, and at_MUN carries that walk, at_DIE, beside the unmapping arm; the walk starts with a region for the image's zero cell that the report reads, whose value is the new free_hyps field fh_gate; YK0k required, without import, for is_self_jump). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g YQ0k YK0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF8x YF0k YF0q YF0o YF1g YF7y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
(* #38: [is_self_jump] and [is_self_jump_to_spin] are this unit's OWN
   (YK0k.v:255 and :269, inside [Section f]'s [Variable segs], hence the leading
   [tfxsegs] at the call sites).  YK0k is already in this file's transitive
   Require closure but was never IMPORTED, so the names were out of scope and
   :431 read "The variable is_self_jump was not found in the current
   environment".  Required without Import and qualified at the three use sites,
   per the stream's solved REFERENCE-NOT-FOUND class (fuzz_pcap's
   stack_window_depth, libdiginet's ivs_bytes): no numeral, binder, carrier or
   published delta.  Not Import, to avoid disturbing the 30 import lines above. *)
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YK0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, zone3cases, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFX_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFX_TP, TFX_TSD,
A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Definition dT : nat := 32.   Definition dC : nat := 33.   Definition dMAP : nat := 34. Definition dLEN : nat := 35. Definition dIDX : nat := 36.
Definition dN : nat := 37.   Definition dQ : nat := 38.   Definition dQI : nat := 39.  Definition dQL : nat := 40.  Definition dLAST : nat := 41.
Definition dJ1 : nat := 42.  Definition dJ2 : nat := 43.  Definition dJ3 : nat := 44.  Definition dJ4 : nat := 45.  Definition dJ5 : nat := 46.
Definition dJ6 : nat := 47.  Definition dSHB : nat := 48. Definition dSHA : nat := 49. Definition dCNT : nat := 50. Definition dRA : nat := 51.
Definition dS0 : nat := 52.  Definition dS1 : nat := 53.  Definition dS2 : nat := 54.  Definition dSHE : nat := 55.
Definition GDEPTH : Z := 96.
Definition SHAv (map : Z) : Z := SHADOW_OFF + map / 8.
Definition CNTv (len : Z) : Z := len / 8.
Definition SHEv (map len : Z) : Z := SHAv map + CNTv len.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma land_m4096 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof. intros x Hx. img_change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by img_lia. img_refl. Qed.
Lemma region_kept_ext {imgk : img} : forall (E : env) (ma mb : word -> option byte) (r : YQ0b.region),
(forall z, (base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= z < base_val E (YQ0b.r_base r) + YQ0b.r_hi r \/
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= z < base_val E (YQ0b.r_base r) + YQ0b.r_whi r) ->
mb (Z_to_bv 64 z) = ma (Z_to_bv 64 z)) ->
region_kept tfxsegs E ma mb r.
Proof.
intros E ma mb r Hm. split; intros z Hz.
- unfold mbyte. rewrite (Hm z (or_introl Hz)). img_refl.
- unfold writable_at, wview. rewrite (Hm z (or_intror Hz)). intros Hw. img_exact Hw.
Qed.
Lemma mrestrict_unfill_out : forall (Hh : word -> bool) (a nw : word) (m : word -> option byte) z,
0 <= z < 2 ^ 64 -> (z < bv_unsigned a \/ bv_unsigned a + bv_unsigned nw <= z) ->
mrestrict Hh (unfill a nw m) (Z_to_bv 64 z) = mrestrict Hh m (Z_to_bv 64 z).
Proof. intros Hh a nw m z Hz Ho. unfold mrestrict. destruct (Hh (Z_to_bv 64 z)); [img_refl|]. img_apply unfill_out. rewrite unsigned_lit_small by img_exact Hz. img_exact Ho. Qed.
Lemma st_ok_ecall_restrict_reg {imgk : img} : forall (Hh : word -> bool) E ss ms (r : bv 5),
st_ok_ecall tfxsegs E ss (restrict Hh ms) -> getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof. intros Hh E ss ms r HS. destruct HS as (_ & _ & _ & _ & _ & _ & HR & _). destruct ms; cbn in HR |- *. img_apply HR. Qed.
Section d. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 : Z).
Variables (own small : bool).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Definition XW : list word :=
[ w64 T; w64 (ly_C ly); w64 map; w64 len; w64 idx; w64 n; w64 q; w64 qi; w64 ql; w64 lst; w64 j1; w64 j2; w64 j3; w64 j4; w64 j5; w64 j6;
w64 SHADOW_OFF; w64 (SHAv map); w64 (CNTv len); w64 vra; w64 vs0; w64 vs1; w64 vs2; w64 (SHEv map len) ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. img_exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. img_exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. img_exact (Er 1 1%bv eq_refl). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. img_refl. Qed.
Lemma EqC : ew E0 33 = w64 (ly_C ly). Proof. img_refl. Qed.
Lemma EqMAP : ew E0 34 = w64 map. Proof. img_refl. Qed.
Lemma EqLEN : ew E0 35 = w64 len. Proof. img_refl. Qed.
Lemma EqIDX : ew E0 36 = w64 idx. Proof. img_refl. Qed.
Lemma EqN : ew E0 37 = w64 n. Proof. img_refl. Qed.
Lemma EqQ : ew E0 38 = w64 q. Proof. img_refl. Qed.
Lemma EqQI : ew E0 39 = w64 qi. Proof. img_refl. Qed.
Lemma EqQL : ew E0 40 = w64 ql. Proof. img_refl. Qed.
Lemma EqLAST : ew E0 41 = w64 lst. Proof. img_refl. Qed.
Lemma EqJ1 : ew E0 42 = w64 j1. Proof. img_refl. Qed.
Lemma EqJ2 : ew E0 43 = w64 j2. Proof. img_refl. Qed.
Lemma EqJ3 : ew E0 44 = w64 j3. Proof. img_refl. Qed.
Lemma EqJ4 : ew E0 45 = w64 j4. Proof. img_refl. Qed.
Lemma EqJ5 : ew E0 46 = w64 j5. Proof. img_refl. Qed.
Lemma EqJ6 : ew E0 47 = w64 j6. Proof. img_refl. Qed.
Lemma EqSHB : ew E0 48 = w64 SHADOW_OFF. Proof. img_refl. Qed.
Lemma EqSHA : ew E0 49 = w64 (SHAv map). Proof. img_refl. Qed.
Lemma EqCNT : ew E0 50 = w64 (CNTv len). Proof. img_refl. Qed.
Lemma EqRA : ew E0 51 = w64 vra. Proof. img_refl. Qed.
Lemma EqS0 : ew E0 52 = w64 vs0. Proof. img_refl. Qed.
Lemma EqS1 : ew E0 53 = w64 vs1. Proof. img_refl. Qed.
Lemma EqS2 : ew E0 54 = w64 vs2. Proof. img_refl. Qed.
Lemma EqSHE : ew E0 55 = w64 (SHEv map len). Proof. img_refl. Qed.
Definition R_MAPH : YQ0b.region :=
YQ0b.mkRegion (Some 34%nat) 0 32 24 (if own then 32 else 24)
[YQ0b.mkChunk 0 (CVal 8 (SOff 34%nat 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 35%nat 0)); YQ0b.mkChunk 24 (CVal 8 (SOff 36%nat 0))].
Definition R_STK : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- GDEPTH) 0 (- GDEPTH) 0 [].
Definition R_MW0 {imgk : img} : YQ0b.region :=
YQ0b.mkRegion None (A_ALLOCATOR + 680) (A_ALLOCATOR + 684) (A_ALLOCATOR + 680) (A_ALLOCATOR + 684) [YQ0b.mkChunk (A_ALLOCATOR + 680) (CZero 4)].
Definition R_MW1 {imgk : img} : YQ0b.region :=
YQ0b.mkRegion None (A_ALLOCATOR + 680) (A_ALLOCATOR + 684) (A_ALLOCATOR + 680) (A_ALLOCATOR + 684)
[YQ0b.mkChunk (A_ALLOCATOR + 680) (CVal 1 (SLit 1)); YQ0b.mkChunk (A_ALLOCATOR + 681) (CZero 3)].
Definition R_NS {imgk : img} : YQ0b.region :=
YQ0b.mkRegion None (A_ALLOCATOR + 120) (A_ALLOCATOR + 129) (A_ALLOCATOR + 120) (A_ALLOCATOR + 129) [YQ0b.mkChunk (A_ALLOCATOR + 120) (CVal 8 (SOff 37%nat 0))].
Definition R_J12 {imgk : img} : YQ0b.region :=
YQ0b.mkRegion None (A_ALLOCATOR + 144) (A_ALLOCATOR + 160) (A_ALLOCATOR + 144) (A_ALLOCATOR + 160)
[YQ0b.mkChunk (A_ALLOCATOR + 144) (CVal 8 (SOff 42%nat 0)); YQ0b.mkChunk (A_ALLOCATOR + 152) (CVal 8 (SOff 43%nat 0))].
Definition R_J34 {imgk : img} : YQ0b.region :=
YQ0b.mkRegion None (A_ALLOCATOR + 704) (A_ALLOCATOR + 720) (A_ALLOCATOR + 704) (A_ALLOCATOR + 720)
[YQ0b.mkChunk (A_ALLOCATOR + 704) (CVal 8 (SOff 44%nat 0)); YQ0b.mkChunk (A_ALLOCATOR + 712) (CVal 8 (SOff 45%nat 0))].
Definition R_QI : YQ0b.region := YQ0b.mkRegion (Some 39%nat) 0 8 0 8 [YQ0b.mkChunk 0 (CVal 8 (SOff 34%nat 0))].
Definition R_CTX : YQ0b.region := YQ0b.mkRegion (Some 33%nat) 0 160 0 0 [YQ0b.mkChunk 8 (CVal 4 (SLit 0)); YQ0b.mkChunk 152 (CVal 8 (SOff 32%nat 0))].
Definition R_JST : YQ0b.region :=
YQ0b.mkRegion (Some 32%nat) (t_stats + 88) (t_stats + 104) (t_stats + 88) (t_stats + 104)
[YQ0b.mkChunk (t_stats + 88) (CVal 8 (SOff 46%nat 0)); YQ0b.mkChunk (t_stats + 96) (CVal 8 (SOff 47%nat 0))].
Definition R_LASTH : YQ0b.region := YQ0b.mkRegion (Some 41%nat) 24 32 24 32 [].
Definition R_QL : YQ0b.region := YQ0b.mkRegion (Some 40%nat) 0 8 0 0 [YQ0b.mkChunk 0 (CVal 8 (SOff 41%nat 0))].
Definition COMMON {imgk : img} : smem :=
[ R_STK; R_MW0; R_NS; R_J12; R_J34; R_QI; R_CTX; R_JST;
flit8 (A_ALLOCATOR + 64) 4096  ; fatom8 (A_ALLOCATOR + 72) 38%nat  ;
flit8 (0xa2150 + D_10f0) (0x13bce8 + D_10c0); flit8 (0x13bd60 + D_10c0) 0xffffffffffffffff;
flit8 (0x13bd78 + D_10c0) 0;
flit8 (0xa2160 + D_10f0) (0xaa1b8 + D_10c0); fatom8 (0xaa1b8 + D_10c0) 48%nat;
flit8 (0xa2168 + D_10f0) (0xaaea8 + D_10c0); flit8 (0xa2170 + D_10f0) (0xaaeb0 + D_10c0); flit8 (0xa2178 + D_10f0) (0xaaea0 + D_10c0);
flit8 (0xaaea0 + D_10c0) 0x7fffffffffff; flit8 (0xaaea8 + D_10c0) 0; flit8 (0xaaeb0 + D_10c0) 0;
flit8 (0xa2180 + D_10f0) (0xa4000 + D_10f0); flit8 (0xa4000 + D_10f0) (0x9b894 + D_10ec);
flit8 (0xa2140 + D_10f0) (0x139c60 + D_10c0); flit8 (0x139c60 + D_10c0) 4096; flit8 (0xa21a0 + D_10f0) 1;
flit1 (0xa9a20 + D_10c0) 1; flit4 (0xa9a24 + D_10c0) 0; flit8 (TFX_TP - 88) TFX_TSD; fatom8 TFX_TSD 33%nat ].
Definition REG0 {imgk : img} : smem := R_MAPH :: COMMON ++ (if own then [] else [R_LASTH; R_QL]).
Definition FFD : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + KSTACK) kHighMemEnd 4);
(32%nat, mkAF 4096 (CEIL_MAX - 4096) 12)    ;
(33%nat, mkAF 4096 (CEIL_MAX - 256) 3)      ;
(34%nat, mkAF 4096 (CEIL_MAX - 8192) 12)    ;
(35%nat, if small then mkAF 8192 (2 ^ 29 - 4096) 12   else mkAF (2 ^ 19) (2 ^ 29) 12);
(36%nat, mkAF 0 16383 0);
(37%nat, mkAF 1 16384 0);
(38%nat, mkAF 4096 (CEIL_MAX - kPtrArrayResv) 12)    ;
(39%nat, mkAF 4096 (CEIL_MAX - 8) 3);
(40%nat, mkAF 4096 (CEIL_MAX - 8) 3);
(41%nat, mkAF 4096 (CEIL_MAX - 8192) 12)    ;
(42%nat, mkAF 0 (2 ^ 64 - 1) 0); (43%nat, mkAF 0 (2 ^ 64 - 1) 0); (44%nat, mkAF 0 (2 ^ 64 - 1) 0);
(45%nat, mkAF 0 (2 ^ 64 - 1) 0); (46%nat, mkAF 0 (2 ^ 64 - 1) 0); (47%nat, mkAF 0 (2 ^ 64 - 1) 0);
(48%nat, mkAF 0x7fff8000 0x7fff8000 12);
(49%nat, mkAF (0x7fff8000 + 512) 0x10007fef7c00 9)    ;
(50%nat, if small then mkAF 1024 (2 ^ 26 - 512) 9   else mkAF (2 ^ 16) (2 ^ 26) 9);
(51%nat, mkAF 0 (2 ^ 64 - 1) 0); (52%nat, mkAF 0 (2 ^ 64 - 1) 0); (53%nat, mkAF 0 (2 ^ 64 - 1) 0); (54%nat, mkAF 0 (2 ^ 64 - 1) 0);
(55%nat, mkAF (0x7fff8000 + 512 + 1024) (0x10007fef7c00 + 2 ^ 16) 9)     ] [] [].
Definition SR0 {imgk : img} : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
4%bv (SLit TFX_TP)) 10%bv (SLit (A_ALLOCATOR + 64))) 11%bv (SLit (A_ALLOCATOR + 688))) 12%bv (SOff 34%nat 4096))
1%bv (SOff 51%nat 0)) 8%bv (SOff 52%nat 0)) 9%bv (SOff 53%nat 0)) 18%bv (SOff 54%nat 0).
Definition SS0 {imgk : img} : sstate := mkSS (0x34140 + D_150) SR0 REG0 None FFD.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x34140 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_Htp : getr regs0 4 = w64 TFX_TP;
fh_Hra : YK0s.ret_ok (w64 vra);
fh_regs : getr regs0 10 = w64 (A_ALLOCATOR + 64) /\ getr regs0 11 = w64 (A_ALLOCATOR + 688) /\ getr regs0 12 = w64 (map + 4096) /\
getr regs0 1 = w64 vra /\ getr regs0 8 = w64 vs0 /\ getr regs0 9 = w64 vs1 /\ getr regs0 18 = w64 vs2;
fh_Hsp : ly_stk_lo ly + KSTACK <= sp0 /\ sp0 <= ly_stk_hi ly;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 - KSTACK <= a < sp0 -> apresent (w_H W) mem0 a;
fh_Hsaved : 0 <= vra < 2 ^ 64 /\ 0 <= vs0 < 2 ^ 64 /\ 0 <= vs1 < 2 ^ 64 /\ 0 <= vs2 < 2 ^ 64;
fh_Hmap : zone3 map len /\ map + len <= ASAN_CEIL /\ map mod 4096 = 0 /\ 8192 <= len < 2 ^ 29 /\ len mod 4096 = 0 /\
(if small then True   else 2 ^ 19 <= len);
fh_Hdisj : (ly_T ly + kThreadObjSize <= map \/ map + len <= ly_T ly) /\ (ly_C ly + 256 <= map \/ map + len <= ly_C ly);
fh_maph : val_mem tfxsegs m0 map 8 map /\ val_mem tfxsegs m0 (map + 8) 8 len /\ val_mem tfxsegs m0 (map + 24) 8 idx /\
(forall a, map <= a < map + 32 -> apresent (w_H W) mem0 a);
fh_Harr : 0 <= idx < n /\ n <= 16384 /\ qi = q + 8 * idx /\ ql = q + 8 * (n - 1) /\
zone3 q kPtrArrayResv /\ q + kPtrArrayResv <= ASAN_CEIL /\ q mod 4096 = 0 /\ (q + kPtrArrayResv <= map \/ map + len <= q);
fh_q : val_mem tfxsegs m0 (A_ALLOCATOR + 72) 8 q;
fh_qi : val_mem tfxsegs m0 qi 8 map /\ (forall a, qi <= a < qi + 8 -> apresent (w_H W) mem0 a);
fh_ql : own = false -> val_mem tfxsegs m0 ql 8 lst /\ (forall a, ql <= a < ql + 8 -> apresent (w_H W) mem0 a);
fh_Hlst : zone3 lst 8192 /\ lst + 8192 <= ASAN_CEIL /\ lst mod 4096 = 0;
fh_own : if own then idx = n - 1 /\ lst = map else (lst + 4096 <= map \/ map + len <= lst);
fh_lsth : own = false -> forall a, lst + 24 <= a < lst + 32 -> apresent (w_H W) mem0 a;
fh_ns : val_mem tfxsegs m0 (A_ALLOCATOR + 120) 8 n;
fh_junk : val_mem tfxsegs m0 (A_ALLOCATOR + 144) 8 j1 /\ val_mem tfxsegs m0 (A_ALLOCATOR + 152) 8 j2 /\
val_mem tfxsegs m0 (A_ALLOCATOR + 704) 8 j3 /\ val_mem tfxsegs m0 (A_ALLOCATOR + 712) 8 j4 /\
0 <= j1 < 2 ^ 64 /\ 0 <= j2 < 2 ^ 64 /\ 0 <= j3 < 2 ^ 64 /\ 0 <= j4 < 2 ^ 64;
fh_mut : val_mem tfxsegs m0 (A_ALLOCATOR + 680) 4 0;
fh_tsd : val_mem tfxsegs m0 TFX_TSD 8 (ly_C ly) /\ val_mem tfxsegs m0 (ly_C ly + 8) 4 0 /\ val_mem tfxsegs m0 (ly_C ly + 152) 8 T
;
fh_jst : val_mem tfxsegs m0 (T + t_stats + 88) 8 j5 /\ val_mem tfxsegs m0 (T + t_stats + 96) 8 j6 /\ 0 <= j5 < 2 ^ 64 /\ 0 <= j6 < 2 ^ 64 /\
(forall a, T + t_stats + 88 <= a < T + t_stats + 104 -> apresent (w_H W) mem0 a);
fh_sh_pres : forall a, SHAv map <= a < SHAv map + CNTv len -> apresent (w_H W) mem0 a;
fh_gate : val_mem tfxsegs m0 (0x13bcdc + D_10c0) 4 0;
fh_SEED : st_ok tfxsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 (0x34140 + D_150)) mem0 (seg_rom tfxsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH :=
pose proof (fh_LY FH) as LY;
pose proof (fh_IMG FH) as IMG;
pose proof (fh_Htp FH) as Htp;
pose proof (fh_Hra FH) as Hra;
pose proof (fh_regs FH) as Hregs;
pose proof (fh_Hsp FH) as Hsp;
pose proof (fh_Hsp_al FH) as Hsp_al;
pose proof (fh_pres FH) as Hpres;
pose proof (fh_Hsaved FH) as Hsaved;
pose proof (fh_Hmap FH) as Hmap;
pose proof (fh_Hdisj FH) as Hdisj;
pose proof (fh_maph FH) as Hmaph;
pose proof (fh_Harr FH) as Harr;
pose proof (fh_q FH) as Hq;
pose proof (fh_qi FH) as Hqi;
pose proof (fh_ql FH) as Hql;
pose proof (fh_Hlst FH) as Hlst;
pose proof (fh_own FH) as Hown;
pose proof (fh_lsth FH) as Hlsth;
pose proof (fh_ns FH) as Hns;
pose proof (fh_junk FH) as Hjunk;
pose proof (fh_mut FH) as Hmut;
pose proof (fh_tsd FH) as Htsd;
pose proof (fh_jst FH) as Hjst;
pose proof (fh_sh_pres FH) as Hsh_pres;
pose proof (fh_SEED FH) as SEED.
Lemma LYB :
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ T mod 4096 = 0 /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ ly_C ly mod 8 = 0 /\
ASAN_CEIL <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
(T + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= T) /\
zone3 (ly_Q ly) kPtrArrayResv /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
(ly_Q ly + kPtrArrayResv <= T \/ T + kThreadObjSize <= ly_Q ly) /\ (ly_Q ly + kPtrArrayResv <= ly_C ly \/ ly_C ly + 256 <= ly_Q ly).
Proof.
open_FH.
pose proof (lo_high ly LY) as HI. unfold in_high in HI. cbn [fst snd] in HI.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(img_try (clear_all; unfold kThreadObjSize; img_lia)) (Forall_nth_f _ _ 2 _ (lo_app ly LY) eq_refl) (pairwise_ij_f _ _ 2 6 _ _ (lo_disj ly LY) eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(img_try (clear_all; img_lia)) (Forall_nth_f _ _ 6 _ (lo_app ly LY) eq_refl) (pairwise_ij_f _ _ 6 2 _ _ (lo_disj ly LY) eq_refl eq_refl)) as ZC.
assert (ZT2 : ly_T ly + kThreadObjSize <= ASAN_CEIL) by (img_try (clear - ZT; unfold zone3 in ZT; img_lia)). assert (ZC2 : ly_C ly + 256 <= ASAN_CEIL) by (img_try (clear - ZC; unfold zone3 in ZC; img_lia)).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_stk_ceil ly LY) as CE.
pose proof (lo_C_al ly LY) as CAL. pose proof (lo_T_al ly LY) as TAL. unfold page_aligned in TAL.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & _ & _ & _ & DC & _).
apply Forall_cons_iff in DQ as [QT DQ]. apply Forall_cons_iff in DQ as [_ DQ]. apply Forall_cons_iff in DQ as [_ DQ]. apply Forall_cons_iff in DQ as [_ DQ].
apply Forall_cons_iff in DQ as [QC _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TC _].
pose proof (zone3_intro ly (ly_Q ly) kPtrArrayResv IMG ltac:(img_try (clear_all; unfold kPtrArrayResv; img_lia)) (Forall_nth_f _ _ 1 _ (lo_app ly LY) eq_refl) (pairwise_ij_f _ _ 1 7 _ _ (lo_disj ly LY) eq_refl eq_refl)) as ZQ.
assert (ZQ2 : ly_Q ly + kPtrArrayResv <= ASAN_CEIL) by (img_try (clear - ZQ; unfold zone3 in ZQ; img_lia)).
unfold zdisjoint in QT, QC, TC. cbn [fst snd] in *. unfold T in *. ceil; unfold kHighMemBeg in *.
repeat match goal with |- _ /\ _ => split end; first [img_exact ZT | img_exact ZC | img_exact ZQ | clear ZT ZC ZQ; unfold ASAN_CEIL in *; img_lia].
Qed.
Lemma derived_ranges :
4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL /\ 4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL /\
kHighMemBeg + KSTACK <= sp0 /\ sp0 <= kHighMemEnd /\
4096 <= map /\ map + len <= ASAN_CEIL /\ 8192 <= len < 2 ^ 29 /\
0 <= idx < n /\ n <= 16384 /\ 4096 <= q /\ q + kPtrArrayResv <= ASAN_CEIL /\ qi = q + 8 * idx /\ ql = q + 8 * (n - 1) /\
4096 <= lst /\ lst + 8192 <= ASAN_CEIL /\
0x7fff8000 + 512 <= SHAv map /\ SHAv map + CNTv len <= 0x10007fef7c00 + 2 ^ 16 /\ SHAv map <= 0x10007fef7c00 /\ len = 8 * CNTv len /\ map = 8 * (map / 8) /\
1024 <= CNTv len < 2 ^ 26 /\
0 <= j1 < 2 ^ 64 /\ 0 <= j2 < 2 ^ 64 /\ 0 <= j3 < 2 ^ 64 /\ 0 <= j4 < 2 ^ 64 /\ 0 <= j5 < 2 ^ 64 /\ 0 <= j6 < 2 ^ 64 /\
0 <= vra < 2 ^ 64 /\ 0 <= vs0 < 2 ^ 64 /\ 0 <= vs1 < 2 ^ 64 /\ 0 <= vs2 < 2 ^ 64.
Proof.
open_FH. pose proof LYB as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & _).
destruct Hsp as [S1 S2]. destruct Hmap as (P1 & P2 & P3 & P4 & P5 & P6). destruct Harr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
destruct Hlst as (X1 & X2 & X3). destruct Hjunk as (_ & _ & _ & _ & G1 & G2 & G3 & G4). destruct Hjst as (_ & _ & G5 & G6 & _). destruct Hsaved as (V1 & V2 & V3 & V4).
clear Hpres Hmaph Hqi Hql Hlsth Hns Hmut Htsd Hsh_pres SEED Htp LY FH Hown Hq Hregs Hra.
unfold SHAv, CNTv. numconst.
pose proof (Z.div_mod map 8 ltac:(img_lia)) as DM1. pose proof (Z.div_mod len 8 ltac:(img_lia)) as DM2.
assert (M8 : map mod 8 = 0) by (img_try (apply Z.mod_divide in P3 as [k Hk]; [|img_lia]; rewrite Hk; replace (k * 4096) with ((k * 512) * 8) by img_lia; img_apply Z_mod_mult)).
assert (L8m : len mod 8 = 0) by (img_try (apply Z.mod_divide in P5 as [k Hk]; [|img_lia]; rewrite Hk; replace (k * 4096) with ((k * 512) * 8) by img_lia; img_apply Z_mod_mult)).
assert (P1' : 4096 <= map) by (img_try (clear - P1; unfold zone3 in P1; img_lia)). assert (A5' : 4096 <= q) by (img_try (clear - A5; unfold zone3 in A5; img_lia)). assert (X1' : 4096 <= lst) by (img_try (clear - X1; unfold zone3 in X1; img_lia)). assert (L1' : 4096 <= T) by (img_try (clear - L1; unfold zone3 in L1; img_lia)). assert (L4' : 4096 <= ly_C ly) by (img_try (clear - L4; unfold zone3 in L4; img_lia)). clear P1 A5 X1 L1 L4 IMG.
assert (UB1 : map / 8 <= (140737479966720 - 8192) / 8) by (img_try (img_apply Z.div_le_mono; img_lia)).
assert (LB1 : 4096 / 8 <= map / 8) by (img_try (img_apply Z.div_le_mono; img_lia)).
assert (UB2 : len / 8 < 536870912 / 8) by (img_try (img_apply Z.div_lt_upper_bound; img_lia)).
assert (LB2 : 8192 / 8 <= len / 8) by (img_try (img_apply Z.div_le_mono; img_lia)).
repeat split; try assumption; try img_lia.
Qed.
Definition WIN (a : Z) : Prop :=
(sp0 - GDEPTH <= a < sp0) \/ (A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684) \/ (A_ALLOCATOR + 120 <= a < A_ALLOCATOR + 129) \/
(A_ALLOCATOR + 144 <= a < A_ALLOCATOR + 160) \/ (A_ALLOCATOR + 704 <= a < A_ALLOCATOR + 720) \/ (qi <= a < qi + 8) \/
(T + t_stats + 88 <= a < T + t_stats + 104) \/ (lst + 24 <= a < lst + 32).
Definition WINS (a : Z) : Prop := SHAv map <= a < SHAv map + CNTv len.
Definition WINM (a : Z) : Prop := map <= a < map + len.
Definition WIN2 (a : Z) : Prop := WIN a \/ WINS a.
Definition WIN3 (a : Z) : Prop := WIN a \/ WINS a \/ WINM a.
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
Definition WSK0 {imgk : img} : list (option nat * Z * Z) :=
[ (Some 2%nat, - GDEPTH, 0); (None, A_ALLOCATOR + 680, A_ALLOCATOR + 684); (None, A_ALLOCATOR + 120, A_ALLOCATOR + 129);
(None, A_ALLOCATOR + 144, A_ALLOCATOR + 160); (None, A_ALLOCATOR + 704, A_ALLOCATOR + 720); (Some 39%nat, 0, 8);
(Some 32%nat, t_stats + 88, t_stats + 104) ] ++ (if own then [(Some 34%nat, 24, 32)] else [(Some 41%nat, 24, 32)]).
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
Lemma WIN_WIN2 : forall a, WIN a -> WIN2 a. Proof. intros a Ha. unfold WIN2. tauto. Qed.
Lemma WIN2_WIN3 : forall a, WIN2 a -> WIN3 a. Proof. intros a Ha. unfold WIN2, WIN3 in *. tauto. Qed.
Lemma WINS_WIN2 : forall a, WINS a -> WIN2 a. Proof. intros a Ha. unfold WIN2. tauto. Qed.
Lemma WSK0_within : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> within WIN E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. pose proof derived_ranges as DR. decompose [and] DR. unfold WSK0 in Hin. unfold WIN.
assert (OW : if own then lst = map else True) by (img_try (destruct own; [img_try (img_exact (proj2 Hown)) | img_try (img_exact I)])). clear Hown.
unfold aHAVf, GDEPTH in *. numconst.
apply in_app_iff in Hin as [Hin|Hin]; cbn [In] in Hin.
- repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (img_try ((img_case; cbv); img_lia)); rewrite ?E2, ?EqT, ?EqQI in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by img_lia;
unfold sp0, T in *; img_lia.
- destruct own; cbn [In] in Hin; destruct Hin as [<-|[]]; cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (img_try ((img_case; cbv); img_lia)); rewrite ?EqMAP, ?EqLAST in Hr; unfold w64 in Hr;
rewrite ?unsigned_lit_small in Hr by img_lia; img_lia.
Qed.
Lemma WIN_not_WINS : forall a, WIN a -> ~ WINS a.
Proof.
open_FH. intros a Ha Hs. pose proof derived_ranges as DR. pose proof LYB as (F1 & _).
destruct Harr as (_ & _ & _ & _ & A5 & _). destruct Hlst as (X1 & _).
clear SEED Hpres Hmaph Hqi Hql Hlsth Htsd Hsh_pres Hown. unfold WIN, WINS, GDEPTH in *.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]];
[ img_try (clear - Ha Hs DR) | img_try (clear - Ha Hs DR) | img_try (clear - Ha Hs DR) | img_try (clear - Ha Hs DR) | img_try (clear - Ha Hs DR) | img_try (clear - Ha Hs DR A5) | img_try (clear - Ha Hs DR F1) | img_try (clear - Ha Hs DR X1) ];
numconst; unfold sp0, T in *; img_lia.
Qed.
Definition SHD (m : word -> option byte) : Prop := forall x : word, WINS (bv_unsigned x) -> m x = Some (Z_to_bv 8 0).
Lemma SHD_frame : forall (E : env) SK rs (m m' : word -> option byte),
within WIN E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> SHD m -> SHD m'.
Proof. intros E SK rs m m' HK Hb HF SH x Hx. rewrite <- (SH x Hx). img_apply (frame_within WIN E SK rs m m' HK Hb HF). intros Hw. img_exact (WIN_not_WINS _ Hw Hx). Qed.
Definition SREGS : list (bv 5) := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition at_RET (md' : Model) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 vra) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md') mat md') /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 2 = getr regs0 2 /\ getr regs' 8 = w64 vs0 /\ getr regs' 9 = w64 vs1 /\ getr regs' 18 = w64 vs2 /\
MEQP WIN3 mem' /\ SHD mem' /\
(forall a, sp0 - GDEPTH <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, (qi <= a < qi + 8) \/ (T + t_stats + 88 <= a < T + t_stats + 104) -> apresent (w_H W) mem' a) /\
let mr := mrestrict (w_H W) mem' in
val_mem tfxsegs mr (A_ALLOCATOR + 680) 4 0 /\
val_mem tfxsegs mr (A_ALLOCATOR + 120) 8 (n - 1) /\
val_mem tfxsegs mr (A_ALLOCATOR + 128) 1 0 /\
(exists v, val_mem tfxsegs mr (A_ALLOCATOR + 144) 8 v) /\ (exists v, val_mem tfxsegs mr (A_ALLOCATOR + 152) 8 v) /\
(exists v, val_mem tfxsegs mr (A_ALLOCATOR + 704) 8 v) /\ (exists v, val_mem tfxsegs mr (A_ALLOCATOR + 712) 8 v) /\
val_mem tfxsegs mr qi 8 lst /\
(own = false -> val_mem tfxsegs mr (lst + 24) 8 idx /\ forall a, lst + 24 <= a < lst + 32 -> apresent (w_H W) mem' a).
(* 75d69e00 Sys/Mm/Munmap.v: [check_munmap] dispatches [errno_ret_in munmap_errnos] before the
   exact-unmap arm, so the node at the munmap ecall carries refusal children beside the unmapping
   one (YF1h.v:37).  [munmap_errnos] is the singleton [ENOMEM] and [errno_ret ENOMEM] is 2^64-12,
   so a refusal child resumes at 0x64c98 + D_2c4 with a0 = -12 and with memory and model unchanged.
   That child SPINS: internal_munmap (0x64c90..0x64c9c, YB10.v:302) returns into UnmapOrDie
   (0x664d4..0x66550, YB10.v:345), whose internal_iserror (0x64c64..0x64c84, YB10.v:300) test takes
   the die arm into ReportMunmapFailureAndDie (0x605a8..0x60644, YB10.v:258), and 0x605d0 is that
   function's self-jump and an image stop -- tra records it at YB06.v:16, trb at YB11.v:16 as
   0x60894 = 0x605d0 + 0x2c4 = 0x605d0 + D_2c4 (YF00.v:43).  The one img-generic address is a stop
   in both images, so this walk needs no trb twin.  No ecall lies on the way, so the trace is
   [t_nil]; the mmap sibling closes the same way at 0x60500 (YF60.v:1056-1066, YF00.v:143
   [pc_spin_mmapdie]).
   The walk runs with [tfxtbl_rtD], not the [tfxtbl_rtM] the success arm uses: rtD carries 0x604d0
   for 93 instructions (YB0u.v:27), spanning both report functions, plus 0x64c64 for 27 and
   0x66460 for 128; rtM (YB0x.v:27) covers neither report function.
   It lives beside [at_MUN] because the walk needs the symbolic state at the ecall: the [mem1] that
   [at_MUN] binds carries no memory invariant at all, so nothing about this walk is derivable from
   [at_MUN] downstream.  [YF12.segGD] and [YF12a.segGD_f] supply it at their four ecall sites, and
   [YF23.plumbing] discharges the refusal child straight from it (YF23.v:376) -- no premise. *)
Definition ENOMEM_RET : Z := 18446744073709551604.
Definition at_DIE (regs1 : bvmap 5 word) (mem1 : word -> option byte) (mat1 : list word) : Prop :=
forall e : Z, In e munmap_errnos ->
AI tfxsegs (w_H W) (w_A W) (with_vm_backing (m_vm_lazy md0) mat1 md0) ->
srealizesM tfxsegs false
(mkCfg (mkst (regupd regs1 10 (errno_ret e)) (v_addi (w64 (0x64c94 + D_2c4)) 4) mem1 (seg_rom tfxsegs))
(with_vm_backing (m_vm_lazy md0) mat1 md0)) t_nil.
Lemma errno_ENOMEM_ret : errno_ret ENOMEM = Z_to_bv 64 ENOMEM_RET.
Proof. clear. unfold ENOMEM_RET. img_apply bv_eq. vm_compute. img_refl. Qed.
Lemma pc_after_ecall : v_addi (w64 (0x64c94 + D_2c4)) 4 = Z_to_bv 64 (0x64c98 + D_2c4).
Proof.
(* #38 added [unsigned_lit_small]'s side condition [0 <= 0x64c94 + D_2c4 < 2^64]
   (measured: a build of this unit printed it).  It is an ARITHMETIC
   goal, and [vm_compute] normalises [<=] and [<] into their [Z.compare]
   unfoldings ([Lt <> Gt], [Lt = Lt]), which carry no atom for [lia] -- so every
   arm of [img_lia] fails and [img_try] exhausts ("No applicable tactic").  The
   [vm_compute] on the NEXT line is right, because that goal is an EQUALITY and
   its finisher is [img_refl].  Verified against the printed obligation by
   a later build, which also proves the old tactic fails. *)
clear. unfold v_addi, w64. rewrite unsigned_lit_small by (img_try (img_case; cbn [D_2c4]; img_lia)).
img_try ((img_case; vm_compute); img_refl).
Qed.
(* The refusal walk reads one image cell before its self-jump: ReportMunmapFailureAndDie loads the
   4-byte zero cell at 0x13bcdc + D_10c0 at 0x605c8 + D_2c4 (auipc a0, 0xdb; lw a0, 0x718(a0); in trb
   auipc a0, 0xdc; lw a0, 0x514(a0)), and its bnez at 0x605cc + D_2c4 falls through to the self-jump
   on zero.  The ecall state has no region for that cell, so [die_run] adds [R_gate2], the region the
   mmap-failure walk adds for the same cell (YF4f.v:71, YF60.v:758-761).  The cell's value is
   [fh_gate], which YF13.DSEED proves from the allocator invariant's constant table; the ecall memory
   agrees with [mem0] outside [WIN2] ([gate_cell]); [gate_free_b] is the check, computed by the
   callers, that the ecall state's regions are disjoint from the cell ([gate_disjoint]). *)
Definition R_gate2 {imgk : img} : YQ0b.region := flit4 (0x13bcdc + D_10c0) 0.
Definition gate_free_b {imgk : img} (r : YQ0b.region) : bool :=
match YQ0b.r_base r with
| None => (YQ0b.r_hi r <=? 0x13bcdc + D_10c0) || (0x13bce0 + D_10c0 <=? YQ0b.r_lo r)
| Some k => (Nat.eqb k 2 && (-16384 <=? YQ0b.r_lo r)) ||
((0 <=? YQ0b.r_lo r) && ((Nat.eqb k 32 && (YQ0b.r_hi r <=? 4096)) || (Nat.eqb k 33 && (YQ0b.r_hi r <=? 256)) ||
(Nat.eqb k 34 && (YQ0b.r_hi r <=? 8192)) || (Nat.eqb k 39 && (YQ0b.r_hi r <=? 8)) ||
(Nat.eqb k 40 && (YQ0b.r_hi r <=? 8)) || (Nat.eqb k 41 && (YQ0b.r_hi r <=? 8192))))
end.
(* The image constant is unfolded before [img_case]: [vm_compute] under an undetermined image
   leaves its arithmetic stuck on [D_10c0] and its normal form grows without bound. *)
Lemma R_gate2_wf : YQ0b.region_wf R_gate2 = true.
Proof. clear. unfold R_gate2, flit4. img_try ((img_case; vm_compute); img_refl). Qed.
Lemma gate_out : forall a, 0x13bcdc + D_10c0 <= a < 0x13bce0 + D_10c0 -> ~ WIN2 a.
Proof.
open_FH. intros a Ha Hw. pose proof derived_ranges as DR. pose proof LYB as (F1 & _).
destruct Harr as (_ & _ & _ & _ & A5 & _). destruct Hlst as (X1 & _).
clear SEED Hpres Hmaph Hqi Hql Hlsth Htsd Hsh_pres Hown. unfold WIN2, WIN, WINS, GDEPTH in *.
destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]]]|Hw];
[ img_try (clear - Ha Hw DR) | img_try (clear - Ha Hw DR) | img_try (clear - Ha Hw DR) | img_try (clear - Ha Hw DR) | img_try (clear - Ha Hw DR)
| img_try (clear - Ha Hw DR A5) | img_try (clear - Ha Hw DR F1) | img_try (clear - Ha Hw DR X1) | img_try (clear - Ha Hw DR) ];
numconst; unfold sp0, T in *; img_lia.
Qed.
Lemma gate_cell : forall m, MEQP WIN2 m -> val_mem tfxsegs (mrestrict (w_H W) m) (0x13bcdc + D_10c0) 4 0.
Proof.
intros m M. img_apply (YF8r.val_mem_frame (w_H W) mem0 m); [| img_try (img_exact (fh_gate FH))].
intros k Hk. img_apply M. rewrite unsigned_lit_small by img_lia. img_apply gate_out. img_lia.
Qed.
Lemma gate_region_ok : forall (E : env) (m : word -> option byte), val_mem tfxsegs m (0x13bcdc + D_10c0) 4 0 ->
YQ0b.region_ok tfxsegs E m R_gate2.
Proof.
intros E m Hv. unfold R_gate2, flit4, YQ0b.region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_try (img_lia)|]. split; [img_try (img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply YI00.chunk_ok_val; [img_refl | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (rewrite Z.add_0_l; img_exact Hv)].
Qed.
Lemma gate_disjoint : forall (E : env) (rs : smem), (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb gate_free_b rs = true -> YQ0b.all_disjoint E R_gate2 rs.
Proof.
open_FH. intros E rs HE. pose proof derived_ranges as DR. pose proof LYB as (F1 & F2 & _ & F4 & F5 & _).
destruct Hmap as (M1 & M2 & _ & M4 & _). destruct Harr as (A1 & A2 & A3 & A4 & A5 & A6 & _). destruct Hlst as (X1 & X2 & _).
induction rs as [|r rs IH]; intros Hb; cbn [YQ0b.all_disjoint]; [exact I|].
cbn [forallb] in Hb. apply andb_prop in Hb as [Hr Hb]. split; [|exact (IH Hb)].
unfold YQ0b.extent_disjoint, R_gate2, flit4. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
unfold gate_free_b in Hr. destruct (YQ0b.r_base r) as [k|]; cbn [base_val].
- apply Bool.orb_prop in Hr. destruct Hr as [Hr|Hr].
+ apply andb_prop in Hr as [Hk Hl]. apply Nat.eqb_eq in Hk. subst k. apply Z.leb_le in Hl. left.
rewrite (HE 2%nat ltac:(unfold aHAVf; lia)), E2. clear - Hl DR. numconst. unfold sp0, T in *. img_lia.
+ apply andb_prop in Hr as [Hl Hr]. apply Z.leb_le in Hl.
repeat (apply Bool.orb_prop in Hr; destruct Hr as [Hr|Hr]); apply andb_prop in Hr as [Hk Hh]; apply Nat.eqb_eq in Hk; subst k; apply Z.leb_le in Hh.
* rewrite (HE 32%nat ltac:(unfold aHAVf; lia)), EqT. unfold w64. rewrite unsigned_lit_small by (clear - F1 F2; numconst; unfold T in *; img_lia).
clear - Hl Hh F1. numconst. unfold T in *. img_lia.
* rewrite (HE 33%nat ltac:(unfold aHAVf; lia)), EqC. unfold w64. rewrite unsigned_lit_small by (clear - F4 F5; numconst; img_lia).
clear - Hl Hh F4. numconst. img_lia.
* rewrite (HE 34%nat ltac:(unfold aHAVf; lia)), EqMAP. unfold w64. rewrite unsigned_lit_small by (clear - M1 M2 M4; numconst; img_lia).
clear - Hl Hh M1 M4. numconst. img_lia.
* rewrite (HE 39%nat ltac:(unfold aHAVf; lia)), EqQI. unfold w64. rewrite unsigned_lit_small by (clear - A1 A2 A3 A5 A6; numconst; img_lia).
clear - Hl Hh A1 A2 A3 A5. numconst. img_lia.
* rewrite (HE 40%nat ltac:(unfold aHAVf; lia)), EqQL. unfold w64. rewrite unsigned_lit_small by (clear - A1 A2 A4 A5 A6; numconst; img_lia).
clear - Hl Hh A1 A2 A4 A5. numconst. img_lia.
* rewrite (HE 41%nat ltac:(unfold aHAVf; lia)), EqLAST. unfold w64. rewrite unsigned_lit_small by (clear - X1 X2; numconst; img_lia).
clear - Hl Hh X1. numconst. img_lia.
- apply Bool.orb_prop in Hr. destruct Hr as [Hr|Hr]; apply Z.leb_le in Hr; img_lia.
Qed.
(* The walk is run on the CONCRETE ecall state each caller holds.  On an abstract [ss] the
   symbolic run cannot take a step (every register, region and fact is unknown), and its
   normal form under [vm_compute] grows without bound.  [die_walk_ok] runs it and checks that
   it stops at the self-jump with no reservation; the four callers in YF12 and YF12a discharge
   it, and [gate_free_b], by [vm_compute] on their own state, as they do the other premises, and
   give the environment agreement and [MEQP WIN2] they already hold at the ecall. *)
Definition die_run (ss : sstate) : sstate * run_status :=
sym_run_toN_sh tfxsegs tfxtbl_rtD YQ04.FUEL (0x605d0 + D_2c4)
(YF3w.addreg R_gate2 (YF7z.setpc (YF3w.pin ss 10%bv (SLit ENOMEM_RET)) (0x64c98 + D_2c4))).
Definition die_walk_ok (ss : sstate) : bool :=
match die_run ss with
| (ssF, RS_running) => (ss_pc ssF =? 0x605d0 + D_2c4) && match ss_resv ssF with None => true | Some _ => false end
| _ => false
end.
Lemma die_at_ecall : forall (E : env) (ss : sstate) (ms : machine_state) (mat : list word),
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> MEQP WIN2 (ms_mem ms) ->
st_ok_ecall tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
ss_pc ss = 0x64c94 + D_2c4 -> no_cdata (ss_mem ss) = true -> die_walk_ok ss = true -> forallb gate_free_b (ss_mem ss) = true ->
at_DIE (ms_regs ms) (ms_mem ms) mat.
Proof.
intros E ss ms mat HE MQ HS Hrv Hpc Hnc Hwalk Hfree.
revert Hwalk. unfold die_walk_ok. destruct (die_run ss) as [ssF stF] eqn:Hrun. intros Hwalk.
destruct stF as [| |why]; cbv beta iota in Hwalk; try discriminate Hwalk.
apply andb_prop in Hwalk as [HpcF HrvF]. apply Z.eqb_eq in HpcF.
assert (HrvF' : ss_resv ssF = None).
{ revert HrvF. destruct (ss_resv ssF); intros X; [cbv beta iota in X; discriminate X | reflexivity]. }
clear HrvF. unfold die_run in Hrun.
intros e He HAI.
cbn [munmap_errnos In] in He. destruct He as [<-|[]].
pose proof (@YF8r.Hwx_tfa imgk) as Hwx.
assert (KEPT : Forall (region_kept tfxsegs E (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms))) (ss_mem ss))
by (img_try (img_apply Forall_forall; intros rr _; img_apply region_kept_ext; intros z _; img_refl)).
pose proof (st_node_cont (w_H W) E ss ms (SLit ENOMEM_RET) ENOMEM_RET (0x64c98 + D_2c4) (ms_mem ms)
HS Hrv eq_refl Hnc KEPT) as HD.
clear KEPT.
assert (HG : val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms)) (0x13bcdc + D_10c0) 4 0) by (img_exact (gate_cell (ms_mem ms) MQ)).
assert (HRG : YQ0b.region_ok tfxsegs E (ms_mem (restrict (w_H W) (mkst (regupd (ms_regs ms) 10%bv (Z_to_bv 64 ENOMEM_RET)) (Z_to_bv 64 (0x64c98 + D_2c4)) (ms_mem ms) (seg_rom tfxsegs)))) R_gate2)
by (img_apply gate_region_ok; img_exact HG).
assert (HDJ : YQ0b.all_disjoint E R_gate2 (ss_mem (YF7z.setpc (YF3w.pin ss 10%bv (SLit ENOMEM_RET)) (0x64c98 + D_2c4))))
by (img_exact (gate_disjoint E (ss_mem ss) HE Hfree)).
assert (HWF : YQ0b.region_wf R_gate2 = true) by (img_exact R_gate2_wf).
assert (HD2 : st_ok tfxsegs E (YF3w.addreg R_gate2 (YF7z.setpc (YF3w.pin ss 10%bv (SLit ENOMEM_RET)) (0x64c98 + D_2c4)))
(restrict (w_H W) (mkst (regupd (ms_regs ms) 10%bv (Z_to_bv 64 ENOMEM_RET)) (Z_to_bv 64 (0x64c98 + D_2c4)) (ms_mem ms) (seg_rom tfxsegs))))
by (img_exact (YF8r.st_ok_add_region E _ _ R_gate2 HD HWF HRG HDJ)).
clear HD HG HRG HDJ HWF. rename HD2 into HD.
rewrite errno_ENOMEM_ret, pc_after_ecall.
assert (SR : SRr tfxsegs W
(mkCfg (mkst (regupd (ms_regs ms) 10%bv (Z_to_bv 64 ENOMEM_RET)) (Z_to_bv 64 (0x64c98 + D_2c4)) (ms_mem ms) (seg_rom tfxsegs))
(with_vm_backing (m_vm_lazy md0) mat md0))
(fun (W'' : world tfxsegs) (c'' : config) => YK0k.is_self_jump tfxsegs (cfg_ms c'') = true)).
{ eapply (YA0n.SRr_run_to_sh_gen tfxsegs tfxtbl_rtD (@tfxtbl_rtD_ok imgk) Hwx W YQ04.FUEL (0x605d0 + D_2c4)
E _ ssF RS_running _ _ _ HD Hrun).
intros ms' mat' HS' _ _.
img_apply SRr_ret.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E ssF ms' HS' HrvF') as SHf.
pose proof (f_equal ms_svc_pending SHf) as Hsv. pose proof (f_equal ms_pc_val SHf) as Hpcf.
cbn [ms_svc_pending ms_pc_val YK11.mkst] in Hsv, Hpcf.
rewrite HpcF in Hpcf.
unfold YK0k.is_self_jump, ms_pc. cbn [cfg_ms]. rewrite Hsv, Hpcf.
rewrite (tfxtbl_rtD_ok (0x605d0 + D_2c4) 111 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))).
img_case; vm_compute. all: img_refl. }
img_apply (SR false HAI t_nil). intros W' c' _ HI' HJ. img_apply srz_spinning.
split; [img_try (img_apply YK0k.is_self_jump_to_spin; img_exact HJ) | img_try (img_exact (AI_halted _ _ _ _ HI'))].
Qed.
Definition at_MUN (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regs1 mem1 mat1,
c' = mkCfg (pend_at regs1 (w64 (0x64c94 + D_2c4)) mem1 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat1 md0) /\
getr regs1 17 = w64 215 /\ getr regs1 10 = w64 map /\ getr regs1 11 = w64 len /\
(let md1 := with_vm_backing (m_vm_lazy md0) mat1 md0 in
SRr tfxsegs W (mkCfg (mkst (regupd regs1 10 (w64 0)) (w64 (0x64c98 + D_2c4)) (unfill (w64 map) (w64 len) mem1) (seg_rom tfxsegs))
(munmap_model (w64 map) (w64 len) md1))
(at_RET (munmap_model (w64 map) (w64 len) md1))) /\
at_DIE regs1 mem1 mat1.
Definition at_PS (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 (0x542ec + D_2c4)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 2 = w64 (sp0 - 32) /\ getr regs' 1 = w64 (0x34234 + D_150) /\ getr regs' 10 = w64 map /\ getr regs' 11 = w64 len /\ getr regs' 12 = w64 0 /\
getr regs' 8 = w64 map /\ getr regs' 9 = w64 map /\ getr regs' 18 = w64 len /\
MEQP WIN mem' /\
(forall a, sp0 - GDEPTH <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, (qi <= a < qi + 8) \/ (T + t_stats + 88 <= a < T + t_stats + 104) -> apresent (w_H W) mem' a) /\
let mr := mrestrict (w_H W) mem' in
val_mem tfxsegs mr (A_ALLOCATOR + 680) 4 0 /\
val_mem tfxsegs mr (A_ALLOCATOR + 120) 8 (n - 1) /\
val_mem tfxsegs mr (A_ALLOCATOR + 128) 1 0 /\
(exists v, val_mem tfxsegs mr (A_ALLOCATOR + 144) 8 v) /\ (exists v, val_mem tfxsegs mr (A_ALLOCATOR + 152) 8 v) /\
(exists v, val_mem tfxsegs mr (A_ALLOCATOR + 704) 8 v) /\ (exists v, val_mem tfxsegs mr (A_ALLOCATOR + 712) 8 v) /\
val_mem tfxsegs mr qi 8 lst /\
(own = false -> val_mem tfxsegs mr (lst + 24) 8 idx /\ forall a, lst + 24 <= a < lst + 32 -> apresent (w_H W) mem' a) /\
val_mem tfxsegs mr (sp0 - 32) 8 vs2 /\ val_mem tfxsegs mr (sp0 - 24) 8 vs1 /\ val_mem tfxsegs mr (sp0 - 16) 8 vs0 /\ val_mem tfxsegs mr (sp0 - 8) 8 vra.
End d.
End c.
