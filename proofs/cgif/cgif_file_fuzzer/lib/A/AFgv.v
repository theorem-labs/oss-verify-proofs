(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n YK0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFl3 AFeq AFew AFeu AFfm AFk7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD,
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
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma land_m4096 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof. intros x Hx. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by lia. reflexivity. Qed.
Lemma region_kept_ext : forall (E : env) (ma mb : word -> option byte) (r : YP09.region),
(forall z, (base_val E (YP09.r_base r) + YP09.r_lo r <= z < base_val E (YP09.r_base r) + YP09.r_hi r \/
base_val E (YP09.r_base r) + YP09.r_wlo r <= z < base_val E (YP09.r_base r) + YP09.r_whi r) ->
mb (Z_to_bv 64 z) = ma (Z_to_bv 64 z)) ->
region_kept tfibsegs E ma mb r.
Proof.
intros E ma mb r Hm. split; intros z Hz.
- unfold mbyte. rewrite (Hm z (or_introl Hz)). reflexivity.
- unfold writable_at, wview. rewrite (Hm z (or_intror Hz)). intros Hw. exact Hw.
Qed.
Lemma mrestrict_unfill_out : forall (Hh : word -> bool) (a nw : word) (m : word -> option byte) z,
0 <= z < 2 ^ 64 -> (z < bv_unsigned a \/ bv_unsigned a + bv_unsigned nw <= z) ->
mrestrict Hh (unfill a nw m) (Z_to_bv 64 z) = mrestrict Hh m (Z_to_bv 64 z).
Proof. intros Hh a nw m z Hz Ho. unfold mrestrict. destruct (Hh (Z_to_bv 64 z)); [reflexivity|]. apply unfill_out. rewrite unsigned_lit_small by exact Hz. exact Ho. Qed.
Lemma st_ok_ecall_restrict_reg : forall (Hh : word -> bool) E ss ms (r : bv 5),
st_ok_ecall tfibsegs E ss (restrict Hh ms) -> getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof. intros Hh E ss ms r HS. destruct HS as (_ & _ & _ & _ & _ & _ & HR & _). destruct ms; cbn in HR |- *. apply HR. Qed.
Section d.
Variables (W : world tfibsegs) (ly : alayout).
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
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EqC : ew E0 33 = w64 (ly_C ly). Proof. reflexivity. Qed.
Lemma EqMAP : ew E0 34 = w64 map. Proof. reflexivity. Qed.
Lemma EqLEN : ew E0 35 = w64 len. Proof. reflexivity. Qed.
Lemma EqIDX : ew E0 36 = w64 idx. Proof. reflexivity. Qed.
Lemma EqN : ew E0 37 = w64 n. Proof. reflexivity. Qed.
Lemma EqQ : ew E0 38 = w64 q. Proof. reflexivity. Qed.
Lemma EqQI : ew E0 39 = w64 qi. Proof. reflexivity. Qed.
Lemma EqQL : ew E0 40 = w64 ql. Proof. reflexivity. Qed.
Lemma EqLAST : ew E0 41 = w64 lst. Proof. reflexivity. Qed.
Lemma EqJ1 : ew E0 42 = w64 j1. Proof. reflexivity. Qed.
Lemma EqJ2 : ew E0 43 = w64 j2. Proof. reflexivity. Qed.
Lemma EqJ3 : ew E0 44 = w64 j3. Proof. reflexivity. Qed.
Lemma EqJ4 : ew E0 45 = w64 j4. Proof. reflexivity. Qed.
Lemma EqJ5 : ew E0 46 = w64 j5. Proof. reflexivity. Qed.
Lemma EqJ6 : ew E0 47 = w64 j6. Proof. reflexivity. Qed.
Lemma EqSHB : ew E0 48 = w64 SHADOW_OFF. Proof. reflexivity. Qed.
Lemma EqSHA : ew E0 49 = w64 (SHAv map). Proof. reflexivity. Qed.
Lemma EqCNT : ew E0 50 = w64 (CNTv len). Proof. reflexivity. Qed.
Lemma EqRA : ew E0 51 = w64 vra. Proof. reflexivity. Qed.
Lemma EqS0 : ew E0 52 = w64 vs0. Proof. reflexivity. Qed.
Lemma EqS1 : ew E0 53 = w64 vs1. Proof. reflexivity. Qed.
Lemma EqS2 : ew E0 54 = w64 vs2. Proof. reflexivity. Qed.
Lemma EqSHE : ew E0 55 = w64 (SHEv map len). Proof. reflexivity. Qed.
Definition R_MAPH : YP09.region :=
YP09.mkRegion (Some 34%nat) 0 32 24 (if own then 32 else 24)
[YP09.mkChunk 0 (CVal 8 (SOff 34%nat 0)); YP09.mkChunk 8 (CVal 8 (SOff 35%nat 0)); YP09.mkChunk 24 (CVal 8 (SOff 36%nat 0))].
Definition R_STK : YP09.region := YP09.mkRegion (Some 2%nat) (- GDEPTH) 0 (- GDEPTH) 0 [].
Definition R_MW0 : YP09.region :=
YP09.mkRegion None (A_ALLOCATOR + 680) (A_ALLOCATOR + 684) (A_ALLOCATOR + 680) (A_ALLOCATOR + 684) [YP09.mkChunk (A_ALLOCATOR + 680) (CZero 4)].
Definition R_MW1 : YP09.region :=
YP09.mkRegion None (A_ALLOCATOR + 680) (A_ALLOCATOR + 684) (A_ALLOCATOR + 680) (A_ALLOCATOR + 684)
[YP09.mkChunk (A_ALLOCATOR + 680) (CVal 1 (SLit 1)); YP09.mkChunk (A_ALLOCATOR + 681) (CZero 3)].
Definition R_NS : YP09.region :=
YP09.mkRegion None (A_ALLOCATOR + 120) (A_ALLOCATOR + 129) (A_ALLOCATOR + 120) (A_ALLOCATOR + 129) [YP09.mkChunk (A_ALLOCATOR + 120) (CVal 8 (SOff 37%nat 0))].
Definition R_J12 : YP09.region :=
YP09.mkRegion None (A_ALLOCATOR + 144) (A_ALLOCATOR + 160) (A_ALLOCATOR + 144) (A_ALLOCATOR + 160)
[YP09.mkChunk (A_ALLOCATOR + 144) (CVal 8 (SOff 42%nat 0)); YP09.mkChunk (A_ALLOCATOR + 152) (CVal 8 (SOff 43%nat 0))].
Definition R_J34 : YP09.region :=
YP09.mkRegion None (A_ALLOCATOR + 704) (A_ALLOCATOR + 720) (A_ALLOCATOR + 704) (A_ALLOCATOR + 720)
[YP09.mkChunk (A_ALLOCATOR + 704) (CVal 8 (SOff 44%nat 0)); YP09.mkChunk (A_ALLOCATOR + 712) (CVal 8 (SOff 45%nat 0))].
Definition R_QI : YP09.region := YP09.mkRegion (Some 39%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 34%nat 0))].
Definition R_CTX : YP09.region := YP09.mkRegion (Some 33%nat) 0 160 0 0 [YP09.mkChunk 8 (CVal 4 (SLit 0)); YP09.mkChunk 152 (CVal 8 (SOff 32%nat 0))].
Definition R_JST : YP09.region :=
YP09.mkRegion (Some 32%nat) (t_stats + 88) (t_stats + 104) (t_stats + 88) (t_stats + 104)
[YP09.mkChunk (t_stats + 88) (CVal 8 (SOff 46%nat 0)); YP09.mkChunk (t_stats + 96) (CVal 8 (SOff 47%nat 0))].
Definition R_LASTH : YP09.region := YP09.mkRegion (Some 41%nat) 24 32 24 32 [].
Definition R_QL : YP09.region := YP09.mkRegion (Some 40%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 41%nat 0))].
Definition COMMON : smem :=
[ R_STK; R_MW0; R_NS; R_J12; R_J34; R_QI; R_CTX; R_JST;
flit8 (A_ALLOCATOR + 64) 4096  ; fatom8 (A_ALLOCATOR + 72) 38%nat  ;
flit8 0x9df88 0x137b28; flit8 0x137ba0 0xffffffffffffffff;
flit8 0x137bb8 0;
flit8 0x9df98 0xa5ff8; fatom8 0xa5ff8 48%nat;
flit8 0x9dfa0 0xa6ce8; flit8 0x9dfa8 0xa6cf0; flit8 0x9dfb0 0xa6ce0;
flit8 0xa6ce0 0x7fffffffffff; flit8 0xa6ce8 0; flit8 0xa6cf0 0;
flit8 0x9dfb8 0x9fe28; flit8 0x9fe28 0x97698;
flit8 0x9df78 0x135aa0; flit8 0x135aa0 4096; flit8 0x9dfd8 1;
flit1 0xa5860 1; flit4 0xa5864 0; flit8 (TFIB_TP - 88) TFIB_TSD; fatom8 TFIB_TSD 33%nat ].
Definition REG0 : smem := R_MAPH :: COMMON ++ (if own then [] else [R_LASTH; R_QL]).
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
Definition SR0 : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
4%bv (SLit TFIB_TP)) 10%bv (SLit (A_ALLOCATOR + 64))) 11%bv (SLit (A_ALLOCATOR + 688))) 12%bv (SOff 34%nat 4096))
1%bv (SOff 51%nat 0)) 8%bv (SOff 52%nat 0)) 9%bv (SOff 53%nat 0)) 18%bv (SOff 54%nat 0).
Definition SS0 : sstate := mkSS 0x33b38 SR0 REG0 None FFD.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33b38) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_Htp : getr regs0 4 = w64 TFIB_TP;
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
fh_maph : val_mem tfibsegs m0 map 8 map /\ val_mem tfibsegs m0 (map + 8) 8 len /\ val_mem tfibsegs m0 (map + 24) 8 idx /\
(forall a, map <= a < map + 32 -> apresent (w_H W) mem0 a);
fh_Harr : 0 <= idx < n /\ n <= 16384 /\ qi = q + 8 * idx /\ ql = q + 8 * (n - 1) /\
zone3 q kPtrArrayResv /\ q + kPtrArrayResv <= ASAN_CEIL /\ q mod 4096 = 0 /\ (q + kPtrArrayResv <= map \/ map + len <= q);
fh_q : val_mem tfibsegs m0 (A_ALLOCATOR + 72) 8 q;
fh_qi : val_mem tfibsegs m0 qi 8 map /\ (forall a, qi <= a < qi + 8 -> apresent (w_H W) mem0 a);
fh_ql : own = false -> val_mem tfibsegs m0 ql 8 lst /\ (forall a, ql <= a < ql + 8 -> apresent (w_H W) mem0 a);
fh_Hlst : zone3 lst 8192 /\ lst + 8192 <= ASAN_CEIL /\ lst mod 4096 = 0;
fh_own : if own then idx = n - 1 /\ lst = map else (lst + 4096 <= map \/ map + len <= lst);
fh_lsth : own = false -> forall a, lst + 24 <= a < lst + 32 -> apresent (w_H W) mem0 a;
fh_ns : val_mem tfibsegs m0 (A_ALLOCATOR + 120) 8 n;
fh_junk : val_mem tfibsegs m0 (A_ALLOCATOR + 144) 8 j1 /\ val_mem tfibsegs m0 (A_ALLOCATOR + 152) 8 j2 /\
val_mem tfibsegs m0 (A_ALLOCATOR + 704) 8 j3 /\ val_mem tfibsegs m0 (A_ALLOCATOR + 712) 8 j4 /\
0 <= j1 < 2 ^ 64 /\ 0 <= j2 < 2 ^ 64 /\ 0 <= j3 < 2 ^ 64 /\ 0 <= j4 < 2 ^ 64;
fh_mut : val_mem tfibsegs m0 (A_ALLOCATOR + 680) 4 0;
fh_tsd : val_mem tfibsegs m0 TFIB_TSD 8 (ly_C ly) /\ val_mem tfibsegs m0 (ly_C ly + 8) 4 0 /\ val_mem tfibsegs m0 (ly_C ly + 152) 8 T
;
fh_jst : val_mem tfibsegs m0 (T + t_stats + 88) 8 j5 /\ val_mem tfibsegs m0 (T + t_stats + 96) 8 j6 /\ 0 <= j5 < 2 ^ 64 /\ 0 <= j6 < 2 ^ 64 /\
(forall a, T + t_stats + 88 <= a < T + t_stats + 104 -> apresent (w_H W) mem0 a);
fh_sh_pres : forall a, SHAv map <= a < SHAv map + CNTv len -> apresent (w_H W) mem0 a;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x33b38) mem0 (seg_rom tfibsegs)))
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
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) (Forall_nth_f _ _ 2 _ (lo_app ly LY) eq_refl) (pairwise_ij_f _ _ 2 6 _ _ (lo_disj ly LY) eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(clear_all; lia) (Forall_nth_f _ _ 6 _ (lo_app ly LY) eq_refl) (pairwise_ij_f _ _ 6 2 _ _ (lo_disj ly LY) eq_refl eq_refl)) as ZC.
assert (ZT2 : ly_T ly + kThreadObjSize <= ASAN_CEIL) by (clear - ZT; unfold zone3 in ZT; lia). assert (ZC2 : ly_C ly + 256 <= ASAN_CEIL) by (clear - ZC; unfold zone3 in ZC; lia).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_stk_ceil ly LY) as CE.
pose proof (lo_C_al ly LY) as CAL. pose proof (lo_T_al ly LY) as TAL. unfold page_aligned in TAL.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & _ & _ & _ & DC & _).
apply Forall_cons_iff in DQ as [QT DQ]. apply Forall_cons_iff in DQ as [_ DQ]. apply Forall_cons_iff in DQ as [_ DQ]. apply Forall_cons_iff in DQ as [_ DQ].
apply Forall_cons_iff in DQ as [QC _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TC _].
pose proof (zone3_intro ly (ly_Q ly) kPtrArrayResv IMG ltac:(clear_all; unfold kPtrArrayResv; lia) (Forall_nth_f _ _ 1 _ (lo_app ly LY) eq_refl) (pairwise_ij_f _ _ 1 7 _ _ (lo_disj ly LY) eq_refl eq_refl)) as ZQ.
assert (ZQ2 : ly_Q ly + kPtrArrayResv <= ASAN_CEIL) by (clear - ZQ; unfold zone3 in ZQ; lia).
unfold zdisjoint in QT, QC, TC. cbn [fst snd] in *. unfold T in *. ceil; unfold kHighMemBeg in *.
repeat match goal with |- _ /\ _ => split end; first [exact ZT | exact ZC | exact ZQ | clear ZT ZC ZQ; unfold ASAN_CEIL in *; lia].
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
pose proof (Z.div_mod map 8 ltac:(lia)) as DM1. pose proof (Z.div_mod len 8 ltac:(lia)) as DM2.
assert (M8 : map mod 8 = 0) by (apply Z.mod_divide in P3 as [k Hk]; [|lia]; rewrite Hk; replace (k * 4096) with ((k * 512) * 8) by lia; apply Z_mod_mult).
assert (L8m : len mod 8 = 0) by (apply Z.mod_divide in P5 as [k Hk]; [|lia]; rewrite Hk; replace (k * 4096) with ((k * 512) * 8) by lia; apply Z_mod_mult).
assert (P1' : 4096 <= map) by (clear - P1; unfold zone3 in P1; lia). assert (A5' : 4096 <= q) by (clear - A5; unfold zone3 in A5; lia). assert (X1' : 4096 <= lst) by (clear - X1; unfold zone3 in X1; lia). assert (L1' : 4096 <= T) by (clear - L1; unfold zone3 in L1; lia). assert (L4' : 4096 <= ly_C ly) by (clear - L4; unfold zone3 in L4; lia). clear P1 A5 X1 L1 L4 IMG.
assert (UB1 : map / 8 <= (140737479966720 - 8192) / 8) by (apply Z.div_le_mono; lia).
assert (LB1 : 4096 / 8 <= map / 8) by (apply Z.div_le_mono; lia).
assert (UB2 : len / 8 < 536870912 / 8) by (apply Z.div_lt_upper_bound; lia).
assert (LB2 : 8192 / 8 <= len / 8) by (apply Z.div_le_mono; lia).
repeat split; try assumption; try lia.
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
- apply Nat.eqb_eq in H1. subst. lia.
- lia.
Qed.
Definition WSK0 : list (option nat * Z * Z) :=
[ (Some 2%nat, - GDEPTH, 0); (None, A_ALLOCATOR + 680, A_ALLOCATOR + 684); (None, A_ALLOCATOR + 120, A_ALLOCATOR + 129);
(None, A_ALLOCATOR + 144, A_ALLOCATOR + 160); (None, A_ALLOCATOR + 704, A_ALLOCATOR + 720); (Some 39%nat, 0, 8);
(Some 32%nat, t_stats + 88, t_stats + 104) ] ++ (if own then [(Some 34%nat, 24, 32)] else [(Some 41%nat, 24, 32)]).
Definition within (D : Z -> Prop) (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> D a.
Lemma within_mono : forall (D D' : Z -> Prop) E SK, (forall a, D a -> D' a) -> within D E SK -> within D' E SK.
Proof. intros D D' E SK HD HK t a Hin Hr. apply HD. exact (HK t a Hin Hr). Qed.
Lemma windows_within : forall (D : Z -> Prop) (E : env) SK rs a,
within D E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> D a.
Proof.
intros D E SK rs a HSK Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Lemma frame_within : forall (D : Z -> Prop) (E : env) SK rs (m m' : word -> option byte),
within D E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ D (bv_unsigned x) -> m' x = m x.
Proof. intros D E SK rs m m' HK Hb HF x Hx. apply HF. intros Hw. apply Hx. exact (windows_within D E SK rs _ HK Hb Hw). Qed.
Definition MEQP (D : Z -> Prop) (m : word -> option byte) : Prop := forall x : word, ~ D (bv_unsigned x) -> m x = mem0 x.
Lemma MEQP_frame : forall (D : Z -> Prop) (E : env) SK rs (m m' : word -> option byte),
within D E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQP D m -> MEQP D m'.
Proof. intros D E SK rs m m' HK Hb HF M x Hx. rewrite <- (M x Hx). exact (frame_within D E SK rs m m' HK Hb HF x Hx). Qed.
Lemma MEQP_weaken : forall (D D' : Z -> Prop) m, (forall a, D a -> D' a) -> MEQP D m -> MEQP D' m.
Proof. intros D D' m HD M x Hx. apply M. intros Hd. apply Hx. exact (HD _ Hd). Qed.
Lemma MEQP_0 : forall D, MEQP D mem0. Proof. intros D x _. reflexivity. Qed.
Lemma WIN_WIN2 : forall a, WIN a -> WIN2 a. Proof. intros a Ha. unfold WIN2. tauto. Qed.
Lemma WIN2_WIN3 : forall a, WIN2 a -> WIN3 a. Proof. intros a Ha. unfold WIN2, WIN3 in *. tauto. Qed.
Lemma WINS_WIN2 : forall a, WINS a -> WIN2 a. Proof. intros a Ha. unfold WIN2. tauto. Qed.
Lemma WSK0_within : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> within WIN E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. pose proof derived_ranges as DR. decompose [and] DR. unfold WSK0 in Hin. unfold WIN.
assert (OW : if own then lst = map else True) by (destruct own; [exact (proj2 Hown) | exact I]). clear Hown.
unfold aHAVf, GDEPTH in *. numconst.
apply in_app_iff in Hin as [Hin|Hin]; cbn [In] in Hin.
- repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (cbv; lia); rewrite ?E2, ?EqT, ?EqQI in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0, T in *; lia.
- destruct own; cbn [In] in Hin; destruct Hin as [<-|[]]; cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (cbv; lia); rewrite ?EqMAP, ?EqLAST in Hr; unfold w64 in Hr;
rewrite ?unsigned_lit_small in Hr by lia; lia.
Qed.
Lemma WIN_not_WINS : forall a, WIN a -> ~ WINS a.
Proof.
open_FH. intros a Ha Hs. pose proof derived_ranges as DR. pose proof LYB as (F1 & _).
destruct Harr as (_ & _ & _ & _ & A5 & _). destruct Hlst as (X1 & _).
clear SEED Hpres Hmaph Hqi Hql Hlsth Htsd Hsh_pres Hown. unfold WIN, WINS, GDEPTH in *.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]];
[ clear - Ha Hs DR | clear - Ha Hs DR | clear - Ha Hs DR | clear - Ha Hs DR | clear - Ha Hs DR | clear - Ha Hs DR A5 | clear - Ha Hs DR F1 | clear - Ha Hs DR X1 ];
numconst; unfold sp0, T in *; lia.
Qed.
Definition SHD (m : word -> option byte) : Prop := forall x : word, WINS (bv_unsigned x) -> m x = Some (Z_to_bv 8 0).
Lemma SHD_frame : forall (E : env) SK rs (m m' : word -> option byte),
within WIN E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> SHD m -> SHD m'.
Proof. intros E SK rs m m' HK Hb HF SH x Hx. rewrite <- (SH x Hx). apply (frame_within WIN E SK rs m m' HK Hb HF). intros Hw. exact (WIN_not_WINS _ Hw Hx). Qed.
Definition SREGS : list (bv 5) := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition at_RET (md' : Model) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 vra) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md') mat md') /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 2 = getr regs0 2 /\ getr regs' 8 = w64 vs0 /\ getr regs' 9 = w64 vs1 /\ getr regs' 18 = w64 vs2 /\
MEQP WIN3 mem' /\ SHD mem' /\
(forall a, sp0 - GDEPTH <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, (qi <= a < qi + 8) \/ (T + t_stats + 88 <= a < T + t_stats + 104) -> apresent (w_H W) mem' a) /\
let mr := mrestrict (w_H W) mem' in
val_mem tfibsegs mr (A_ALLOCATOR + 680) 4 0 /\
val_mem tfibsegs mr (A_ALLOCATOR + 120) 8 (n - 1) /\
val_mem tfibsegs mr (A_ALLOCATOR + 128) 1 0 /\
(exists v, val_mem tfibsegs mr (A_ALLOCATOR + 144) 8 v) /\ (exists v, val_mem tfibsegs mr (A_ALLOCATOR + 152) 8 v) /\
(exists v, val_mem tfibsegs mr (A_ALLOCATOR + 704) 8 v) /\ (exists v, val_mem tfibsegs mr (A_ALLOCATOR + 712) 8 v) /\
val_mem tfibsegs mr qi 8 lst /\
(own = false -> val_mem tfibsegs mr (lst + 24) 8 idx /\ forall a, lst + 24 <= a < lst + 32 -> apresent (w_H W) mem' a).
Definition at_MUN (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs1 mem1 mat1,
c' = mkCfg (pend_at regs1 (w64 0x64178) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat1 md0) /\
getr regs1 17 = w64 215 /\ getr regs1 10 = w64 map /\ getr regs1 11 = w64 len /\
let md1 := with_vm_backing (m_vm_lazy md0) mat1 md0 in
SRr tfibsegs W (mkCfg (mkst (regupd regs1 10 (w64 0)) (w64 0x6417c) (unfill (w64 map) (w64 len) mem1) (seg_rom tfibsegs))
(munmap_model (w64 map) (w64 len) md1))
(at_RET (munmap_model (w64 map) (w64 len) md1)).
Definition at_PS (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x537d0) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 2 = w64 (sp0 - 32) /\ getr regs' 1 = w64 0x33c2c /\ getr regs' 10 = w64 map /\ getr regs' 11 = w64 len /\ getr regs' 12 = w64 0 /\
getr regs' 8 = w64 map /\ getr regs' 9 = w64 map /\ getr regs' 18 = w64 len /\
MEQP WIN mem' /\
(forall a, sp0 - GDEPTH <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, (qi <= a < qi + 8) \/ (T + t_stats + 88 <= a < T + t_stats + 104) -> apresent (w_H W) mem' a) /\
let mr := mrestrict (w_H W) mem' in
val_mem tfibsegs mr (A_ALLOCATOR + 680) 4 0 /\
val_mem tfibsegs mr (A_ALLOCATOR + 120) 8 (n - 1) /\
val_mem tfibsegs mr (A_ALLOCATOR + 128) 1 0 /\
(exists v, val_mem tfibsegs mr (A_ALLOCATOR + 144) 8 v) /\ (exists v, val_mem tfibsegs mr (A_ALLOCATOR + 152) 8 v) /\
(exists v, val_mem tfibsegs mr (A_ALLOCATOR + 704) 8 v) /\ (exists v, val_mem tfibsegs mr (A_ALLOCATOR + 712) 8 v) /\
val_mem tfibsegs mr qi 8 lst /\
(own = false -> val_mem tfibsegs mr (lst + 24) 8 idx /\ forall a, lst + 24 <= a < lst + 32 -> apresent (w_H W) mem' a) /\
val_mem tfibsegs mr (sp0 - 32) 8 vs2 /\ val_mem tfibsegs mr (sp0 - 24) 8 vs1 /\ val_mem tfibsegs mr (sp0 - 16) 8 vs0 /\ val_mem tfibsegs mr (sp0 - 8) 8 vra.
End d.
End c.
