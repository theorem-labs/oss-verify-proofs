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
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFep AFeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, KSTACK, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD,
A_QUAR, A_ALLOCATOR, o_quar, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kMaxSize in *.
Definition kT : nat := 32.
Definition kSB : nat := 33.
Definition kP : nat := 34.
Definition kC : nat := 35.
Definition kPC : nat := 36.
Definition kCNT : nat := 37.
Definition kMAX : nat := 38.
Definition kSZ : nat := 39.
Definition kSLOT : nat := 40.
Definition kRG : nat := 41.
Definition kOLD : nat := 42.
Definition kMF : nat := 43.
Definition kDST : nat := 44.
Definition kSRC : nat := 45.
Definition kJ80 : nat := 46.
Definition kJ88 : nat := 47.
Definition kJST : nat := 48.
Definition kRI : nat := 49.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (c off cnt old mf j80 j88 jst : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Definition Pv : Z := SB + off.
Definition PCv : Z := T + t_cache + 80 * c.
Definition MAXv : Z := max_cached c.
Definition SZv : Z := class_size c.
Definition Nv : Z := MAXv / 2.
Definition CNTPv : Z := if cnt =? MAXv then cnt - Nv else cnt.
Definition SLOTv : Z := PCv + 16 + 4 * CNTPv.
Definition RIv : Z := SB + kRegionInfoOff.
Definition RGv : Z := RIv + 128 * c.
Definition RBv : Z := SB + region_off c.
Definition FAv : Z := RBv + kFreeArrayOffset.
Definition DSTv : Z := FAv + 4 * old.
Definition SRCv : Z := PCv + 16 + 4 * (cnt - Nv).
Definition RELv : Z := off - region_off c.
Definition XW : list word :=
[ w64 T; w64 SB; w64 Pv; w64 c; w64 PCv; w64 cnt; w64 MAXv; w64 SZv; w64 SLOTv; w64 RGv; w64 old; w64 mf; w64 DSTv; w64 SRCv;
w64 j80; w64 j88; w64 jst; w64 RIv ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EqSB : ew E0 33 = w64 SB. Proof. reflexivity. Qed.
Lemma EqP : ew E0 34 = w64 Pv. Proof. reflexivity. Qed.
Lemma EqC : ew E0 35 = w64 c. Proof. reflexivity. Qed.
Lemma EqPC : ew E0 36 = w64 PCv. Proof. reflexivity. Qed.
Lemma EqCNT : ew E0 37 = w64 cnt. Proof. reflexivity. Qed.
Lemma EqMAX : ew E0 38 = w64 MAXv. Proof. reflexivity. Qed.
Lemma EqSZ : ew E0 39 = w64 SZv. Proof. reflexivity. Qed.
Lemma EqSLOT : ew E0 40 = w64 SLOTv. Proof. reflexivity. Qed.
Lemma EqRG : ew E0 41 = w64 RGv. Proof. reflexivity. Qed.
Lemma EqOLD : ew E0 42 = w64 old. Proof. reflexivity. Qed.
Lemma EqMF : ew E0 43 = w64 mf. Proof. reflexivity. Qed.
Lemma EqDST : ew E0 44 = w64 DSTv. Proof. reflexivity. Qed.
Lemma EqSRC : ew E0 45 = w64 SRCv. Proof. reflexivity. Qed.
Lemma EqJ80 : ew E0 46 = w64 j80. Proof. reflexivity. Qed.
Lemma EqJ88 : ew E0 47 = w64 j88. Proof. reflexivity. Qed.
Lemma EqJST : ew E0 48 = w64 jst. Proof. reflexivity. Qed.
Lemma EqRI : ew E0 49 = w64 RIv. Proof. reflexivity. Qed.
Definition R_PC : YP09.region :=
YP09.mkRegion (Some 36%nat) 0 16 0 4
[YP09.mkChunk 0 (CVal 4 (SOff 37%nat 0)); YP09.mkChunk 4 (CVal 4 (SOff 38%nat 0)); YP09.mkChunk 8 (CVal 8 (SOff 39%nat 0))].
Definition R_JST : YP09.region :=
YP09.mkRegion (Some 32%nat) (t_cache + 2576) (t_cache + 2584) (t_cache + 2576) (t_cache + 2584) [YP09.mkChunk (t_cache + 2576) (CVal 8 (SOff 48%nat 0))].
Definition R_STK_HI : YP09.region := YP09.mkRegion (Some 2%nat) (- 240) 0 (- 240) 0 [].
Definition R_STK_LO : YP09.region := YP09.mkRegion (Some 2%nat) (- 320) (- 240) (- 320) (- 240) [].
Definition REG0 : smem :=
[ R_STK_HI; R_STK_LO; R_PC; R_JST;
fatom8 (A_ALLOCATOR + 32) 33%nat  ; fatom8 (A_ALLOCATOR + 48) 49%nat  ;
flit4 (A_ALLOCATOR + 40) 4294967295  ;
flit8 0x9df78 0x135aa0; flit8 0x135aa0 4096  ;
flit8 0x103a0 0xafffff00000fffff   ].
Definition R_SLOT : YP09.region := YP09.mkRegion (Some 40%nat) 0 4 0 4 [].
Definition R_RGA : YP09.region := YP09.mkRegion (Some 41%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))].
Definition R_RGB : YP09.region :=
YP09.mkRegion (Some 41%nat) 8 80 16 24 [YP09.mkChunk 16 (CVal 8 (SOff 42%nat 0)); YP09.mkChunk 24 (CVal 8 (SOff 43%nat 0))].
Definition R_RGC : YP09.region :=
YP09.mkRegion (Some 41%nat) 80 128 80 88 [YP09.mkChunk 80 (CVal 8 (SOff 46%nat 0)); YP09.mkChunk 88 (CVal 8 (SOff 47%nat 0))].
Definition WRG (a : Z) : Prop := (RGv <= a < RGv + 8) \/ (RGv + 16 <= a < RGv + 24) \/ (RGv + 80 <= a < RGv + 88).
Definition FFK : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + KSTACK) kHighMemEnd 4);
(32%nat, mkAF 4096 (CEIL_MAX - 4096) 12)    ;
(33%nat, mkAF kHighMemBeg CEIL_MAX 16);
(34%nat, mkAF kHighMemBeg CEIL_MAX 4);
(35%nat, mkAF 1 30 0);
(36%nat, mkAF 4096 (CEIL_MAX - 80) 4)       ;
(37%nat, mkAF 0 16 0);
(38%nat, mkAF 2 16 1);
(39%nat, mkAF 32 kMaxSize 5);
(40%nat, mkAF 4096 (CEIL_MAX - 4) 2)        ;
(41%nat, mkAF kHighMemBeg (CEIL_MAX - 128) 7);
(42%nat, mkAF 0 (2 ^ 27) 0);
(43%nat, mkAF 0 kFreeArrayMax 0);
(44%nat, mkAF kHighMemBeg (CEIL_MAX - 64) 2);
(45%nat, mkAF 4096 (CEIL_MAX - 64) 2)       ;
(46%nat, mkAF 0 (2 ^ 64 - 1) 0);
(47%nat, mkAF 0 (2 ^ 64 - 1) 0);
(48%nat, mkAF 0 (2 ^ 64 - 1) 0);
(49%nat, mkAF kHighMemBeg (CEIL_MAX - 4096) 12) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 10%bv (SOff 32%nat t_cache)) 11%bv (SLit A_ALLOCATOR))
12%bv (SOff 35%nat 0)) 13%bv (SOff 34%nat 0).
Definition SS0 : sstate := mkSS 0x33970 SR0 REG0 None FFK.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33970) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_Htp : getr regs0 4 = w64 TFIB_TP;
fh_Hra : YK0s.ret_ok (getr regs0 1);
fh_Hra4096 : 4096 <= bv_unsigned (getr regs0 1);
fh_Hsp : ly_stk_lo ly + KSTACK <= sp0 /\ sp0 <= ly_stk_hi ly;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 - KSTACK <= a < sp0 -> apresent (w_H W) mem0 a;
fh_Hc : 1 <= c <= 30;
fh_Hcnt : 0 <= cnt <= MAXv;
fh_Hoff : 0 <= RELv /\ RELv + SZv <= kFreeArrayOffset /\ RELv mod 16 = 0;
fh_slot : forall a, SLOTv <= a < SLOTv + 4 -> apresent (w_H W) mem0 a;
fh_Hjunk : 0 <= j80 < 2 ^ 64 /\ 0 <= j88 < 2 ^ 64 /\ 0 <= jst < 2 ^ 64;
fh_full : cnt = MAXv ->
0 <= old /\ 4 * (old + Nv) <= mf /\ mf <= kFreeArrayMax /\
(forall a, RGv <= a < RGv + 128 -> apresent (w_H W) mem0 a) /\
val_mem tfibsegs m0 RGv 8 0 /\ val_mem tfibsegs m0 (RGv + 16) 8 old /\ val_mem tfibsegs m0 (RGv + 24) 8 mf /\
val_mem tfibsegs m0 (RGv + 80) 8 j80 /\ val_mem tfibsegs m0 (RGv + 88) 8 j88 /\
(forall a, DSTv <= a < DSTv + 4 * Nv -> apresent (w_H W) mem0 a) /\
(forall a, SRCv <= a < SRCv + 4 * Nv -> apresent (w_H W) mem0 a);
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x33970) mem0 (seg_rom tfibsegs)))
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
pose proof (fh_Hc FH) as Hc;
pose proof (fh_Hcnt FH) as Hcnt;
pose proof (fh_Hoff FH) as Hoff;
pose proof (fh_slot FH) as Hslot;
pose proof (fh_Hjunk FH) as Hjunk;
pose proof (fh_full FH) as Hfull;
pose proof (fh_SEED FH) as SEED.
Lemma LYB :
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly <= SB /\
SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < ly_top ly /\ ly_top ly <= ly_stk_hi ly /\ ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly /\
(T + kThreadObjSize <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= T) /\
(T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_hi ly <= T) /\ (ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly) /\
SB mod 65536 = 0.
Proof.
open_FH.
pose proof (lo_high ly LY) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD0.
pose proof (Forall_nth_f _ _ 2 _ HA eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) IT (pairwise_ij_f _ _ 2 6 _ _ HD0 eq_refl eq_refl)) as ZT. clear HA IT.
pose proof (lo_space_in ly LY) as HSP. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_al ly LY) as SAL.
pose proof HD0 as HD. clear HD0. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TSTK _].
unfold zdisjoint in PT, PSTK, TSTK. cbn [fst snd] in *. unfold T, SB in *.
split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|].
clear - IP HSP T1 T2 T3 T4 T5 T6 T7 PT PSTK TSTK SAL. unfold kHighMemBeg, kThreadObjSize, kPrimResvSize in *. repeat split; lia.
Qed.
Lemma class_facts : 32 <= SZv <= kMaxSize /\ SZv mod 32 = 0 /\ 2 <= MAXv <= 16 /\ MAXv mod 2 = 0 /\ 1 <= Nv <= 8 /\ MAXv = 2 * Nv /\
0 <= region_off c /\ region_off c = c * 2 ^ 32 /\ region_off c + 2 ^ 32 <= 31 * 2 ^ 32.
Proof.
open_FH. pose proof (class_ok c ltac:(lia)) as (K1 & K2 & K3 & K4 & K5 & K6). unfold Nv, MAXv, SZv. unfold region_off. rewrite Z.shiftl_mul_pow2 by lia.
assert (32 <= class_size c) by (apply Z.mod_divide in K2 as [q Hq]; [|lia]; nia).
assert (D1 : 1 <= max_cached c / 2) by (apply Z.div_le_lower_bound; lia).
assert (D2 : max_cached c / 2 <= 8) by (apply Z.div_le_upper_bound; lia).
assert (D3 : max_cached c = 2 * (max_cached c / 2)) by (pose proof (Z.div_mod (max_cached c) 2 ltac:(lia)); lia).
repeat split; lia.
Qed.
Lemma derived_ranges :
4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= SB /\ SB + kSpaceSize <= ASAN_CEIL /\ SB mod 65536 = 0 /\
kHighMemBeg + KSTACK <= sp0 /\ sp0 <= kHighMemEnd /\
kHighMemBeg <= Pv /\ Pv + SZv <= ASAN_CEIL /\ Pv mod 16 = 0 /\
T + t_cache + 80 <= PCv /\ PCv + 80 <= T + t_cache + 2480 /\ PCv mod 16 = T mod 16 /\
0 <= cnt <= MAXv /\ 0 <= CNTPv < MAXv /\ PCv + 16 <= SLOTv /\ SLOTv + 4 <= PCv + 80 /\
kHighMemBeg <= RIv /\ RIv = SB + kRegionInfoOff /\ RGv = RIv + 128 * c /\ RIv + 128 <= RGv /\ RGv + 128 <= RIv + 4096 /\ RIv + 4096 <= ASAN_CEIL /\
RBv = SB + c * 2 ^ 32 /\ SB + 2 ^ 32 <= RBv /\ RBv + 2 ^ 32 <= SB + 31 * 2 ^ 32 /\ FAv = RBv + kFreeArrayOffset /\
0 <= j80 < 2 ^ 64 /\ 0 <= j88 < 2 ^ 64 /\ 0 <= jst < 2 ^ 64.
Proof.
open_FH. pose proof LYB as LB. pose proof class_facts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9). destruct Hsp as [S1 S2]. destruct Hoff as (O1 & O2 & O3). destruct Hjunk as (J1 & J2 & J3).
unfold SLOTv, SRCv, DSTv, FAv, RGv, CNTPv, Nv, MAXv, SZv, PCv, Pv, RIv, RBv, RELv in *.
assert (HP16 : (SB + off) mod 16 = 0).
{ replace (SB + off) with (SB + region_off c + (off - region_off c)) by lia. rewrite K8.
destruct LB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SAL).
apply Z.mod_divide in SAL as [q Hq]; [|lia]. apply Z.mod_divide in O3 as [q3 Hq3]; [|lia]. apply Z.mod_divide; [lia|]. exists (q * 4096 + c * 2 ^ 28 + q3). lia. }
assert (HPC16 : (T + t_cache + 80 * c) mod 16 = T mod 16).
{ unfold t_cache. replace (T + 208 + 80 * c) with (T + (208 + 80 * c)) by lia. rewrite <- Zplus_mod_idemp_r.
replace ((208 + 80 * c) mod 16) with 0; [rewrite Z.add_0_r; reflexivity|]. symmetry. apply Z.mod_divide; [lia|]. exists (13 + 5 * c). lia. }
numconst. destruct (Z.eqb_spec cnt (max_cached c)); repeat split; lia.
Qed.
Definition WINF (a : Z) : Prop :=
(PCv <= a < PCv + 4) \/ (SLOTv <= a < SLOTv + 4) \/ (T + t_cache + 2576 <= a < T + t_cache + 2584).
Definition WINR (a : Z) : Prop := cnt = MAXv /\ (WRG a \/ (DSTv <= a < DSTv + 4 * Nv)).
Definition WIN (a : Z) : Prop := (sp0 - 320 <= a < sp0) \/ WINF a \/ WINR a.
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
[(Some 2%nat, -320, 0); (Some 36%nat, 0, 4); (Some 40%nat, 0, 4); (Some 32%nat, t_cache + 2576, t_cache + 2584)].
Definition WSKR : list (option nat * Z * Z) := WSK0 ++ [(Some 41%nat, 0, 8); (Some 41%nat, 16, 24); (Some 41%nat, 80, 88)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. pose proof derived_ranges as DR. decompose [and] DR. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN, WINF.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, aHAVf, KSTACK, t_cache in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (cbv; lia); rewrite ?E2, ?EqT, ?EqPC, ?EqSLOT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0 in *; lia.
Qed.
Lemma WSKR_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> cnt = MAXv -> sk_ok E WSKR.
Proof.
open_FH. intros E HE Hf t a Hin Hr. unfold WSKR in Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (WSK0_ok E HE t a Hin Hr)|].
pose proof derived_ranges as DR. decompose [and] DR. pose proof class_facts as (_ & _ & _ & _ & K5 & _). destruct (Hfull Hf) as (F1 & F2 & F3 & _).
cbn [In] in Hin. unfold WIN, WINR, WRG. unfold DSTv, FAv in *. unfold aHAVf in *. numconst.
destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd base_val] in Hr; rewrite HE in Hr by (cbv; lia); rewrite ?EqRG, ?EqDST in Hr; unfold w64 in Hr; unfold DSTv, FAv, kFreeArrayOffset in Hr;
rewrite unsigned_lit_small in Hr by lia; do 2 right; (split; [exact Hf|]); left; lia.
Qed.
Lemma windows_WIN : forall (E : env) SK rs a,
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
intros E SK rs a HSK Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Lemma WIN_zone : forall a, WIN a -> ~ (TFIB_IMG_LO <= a < TFIB_IMG_END) /\ ~ (kLowShadowBeg <= a < kHighMemBeg) /\ 0 <= a < 2 ^ 64.
Proof.
open_FH. intros a Hw. pose proof derived_ranges as DR. pose proof class_facts as (_ & _ & _ & _ & K5 & _). pose proof LYB as (F1 & _).
unfold WIN, WINF, WINR, WRG in Hw.
destruct Hw as [Hw|[Hw|[Hf Hw]]].
- clear - Hw DR. numconst. lia.
- clear - Hw DR F1. numconst. lia.
- destruct (Hfull Hf) as (X1 & X2 & X3 & _). clear - Hw DR X1 X2 X3 K5. unfold DSTv, FAv in *. numconst. unfold kFreeArrayOffset, kFreeArrayMax in *. lia.
Qed.
Lemma WIN_off : forall a, WIN a -> off_img a.
Proof. intros a Hw. destruct (WIN_zone a Hw) as (A & B & C). unfold off_img. clear - A B C. unfold TFIB_IMG_LO, TFIB_IMG_END in *. lia. Qed.
Lemma notWIN_img : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ~ WIN a.
Proof. intros a Ha Hw. destruct (WIN_zone a Hw) as (A & _). exact (A Ha). Qed.
Lemma notWIN_shb : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ WIN a.
Proof. intros a Ha Hw. destruct (WIN_zone a Hw) as (_ & B & _). exact (B Ha). Qed.
Lemma off_T : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. exact (zone3_off_img _ _ a (proj1 LYB) Ha). Qed.
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold TFIB_IMG_END; tac ].
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> m x = mem0 x.
Lemma MEQ_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQ m -> MEQ m'.
Proof. intros E SK rs m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WIN E SK rs _ HSK Hb Hw). Qed.
Lemma MEQ_0 : MEQ mem0. Proof. intros x _. reflexivity. Qed.
Definition WINX (a : Z) : Prop :=
(sp0 - 320 <= a < sp0) \/ (PCv <= a < PCv + 4) \/ (T + t_cache + 2576 <= a < T + t_cache + 2584) \/ (cnt = MAXv /\ WRG a).
Lemma WINX_WIN : forall a, WINX a -> WIN a.
Proof. intros a Ha. unfold WINX, WIN, WINF, WINR in *. tauto. Qed.
Definition sk_okX (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINX a.
Definition WSKX : list (option nat * Z * Z) :=
[(Some 2%nat, -320, 0); (Some 36%nat, 0, 4); (Some 32%nat, t_cache + 2576, t_cache + 2584); (Some 41%nat, 0, 8); (Some 41%nat, 16, 24); (Some 41%nat, 80, 88)].
Lemma WSKX_okX : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> cnt = MAXv -> sk_okX E WSKX.
Proof.
open_FH. intros E HE Hf t a Hin Hr. pose proof derived_ranges as DR. decompose [and] DR. unfold WSKX in Hin. cbn [In] in Hin. unfold WINX, WRG.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, aHAVf, KSTACK, t_cache in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (cbv; lia); rewrite ?E2, ?EqT, ?EqPC, ?EqRG in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0 in *; lia.
Qed.
Lemma windows_WINX : forall (E : env) SK rs a,
sk_okX E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINX a.
Proof.
intros E SK rs a HSK Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Definition MEQX (m : word -> option byte) : Prop := forall x : word, ~ WINX (bv_unsigned x) -> m x = mem0 x.
Lemma MEQX_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_okX E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQX m -> MEQX m'.
Proof. intros E SK rs m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WINX E SK rs _ HSK Hb Hw). Qed.
Lemma MEQX_0 : MEQX mem0. Proof. intros x _. reflexivity. Qed.
Lemma MEQX_MEQ : forall m, MEQX m -> MEQ m.
Proof. intros m M x Hx. apply M. intros Hw. apply Hx. exact (WINX_WIN _ Hw). Qed.
Lemma DST_notWINX : cnt = MAXv -> forall a, DSTv <= a < DSTv + 4 * Nv -> ~ WINX a.
Proof.
open_FH. intros Hf a Ha Hw. pose proof derived_ranges as DR. decompose [and] DR. pose proof LYB as LB. decompose [and] LB.
pose proof class_facts as (_ & _ & _ & _ & K5 & _). destruct (Hfull Hf) as (F1 & F2 & F3 & _). destruct Hsp as [S1 S2].
unfold WINX, WRG in Hw. unfold DSTv, FAv in *. numconst. unfold T, SB, sp0 in *. lia.
Qed.
Lemma SRC_notWINX : cnt = MAXv -> forall a, SRCv <= a < SRCv + 4 * Nv -> ~ WINX a.
Proof.
open_FH. intros Hf a Ha Hw. pose proof derived_ranges as DR. decompose [and] DR. pose proof LYB as LB. decompose [and] LB.
pose proof class_facts as (_ & _ & K3 & K4 & K5 & K6 & _). destruct Hsp as [S1 S2].
unfold WINX, WRG in Hw. unfold SRCv in *. numconst. unfold T, SB, sp0 in *. lia.
Qed.
Definition WINY (a : Z) : Prop := (sp0 - 320 <= a < sp0) \/ WINF a \/ (cnt = MAXv /\ WRG a).
Lemma WINY_WIN : forall a, WINY a -> WIN a.
Proof. intros a Ha. unfold WINY, WIN, WINR in *. tauto. Qed.
Lemma WINX_WINY : forall a, WINX a -> WINY a.
Proof. intros a Ha. unfold WINX, WINY, WINF in *. tauto. Qed.
Lemma DST_notWINY : cnt = MAXv -> forall a, DSTv <= a < DSTv + 4 * Nv -> ~ WINY a.
Proof.
open_FH. intros Hf a Ha Hw. pose proof derived_ranges as DR. decompose [and] DR. pose proof LYB as LB. decompose [and] LB.
pose proof class_facts as (_ & _ & _ & _ & K5 & _). destruct (Hfull Hf) as (F1 & F2 & F3 & _). destruct Hsp as [S1 S2].
unfold WINY, WINF, WRG in Hw. unfold DSTv, FAv in *. numconst. unfold T, SB, sp0 in *. lia.
Qed.
Definition sk_okY (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINY a.
Lemma WSKR_okY : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> cnt = MAXv -> sk_okY E WSKR.
Proof.
open_FH. intros E HE Hf t a Hin Hr. pose proof derived_ranges as DR. decompose [and] DR. unfold WSKR, WSK0 in Hin. cbn [In app] in Hin. unfold WINY, WINF, WRG.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, aHAVf, KSTACK, t_cache in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (cbv; lia); rewrite ?E2, ?EqT, ?EqPC, ?EqSLOT, ?EqRG in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0 in *; lia.
Qed.
Lemma windows_WINY : forall (E : env) SK rs a,
sk_okY E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINY a.
Proof.
intros E SK rs a HSK Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Definition MEQY (m3 m : word -> option byte) : Prop := forall x : word, ~ WINY (bv_unsigned x) -> m x = m3 x.
Lemma MEQY_frame : forall (E : env) SK rs (m3 m m' : word -> option byte),
sk_okY E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQY m3 m -> MEQY m3 m'.
Proof. intros E SK rs m3 m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WINY E SK rs _ HSK Hb Hw). Qed.
Lemma MEQY_0 : forall m3, MEQY m3 m3. Proof. intros m3 x _. reflexivity. Qed.
Ltac clear_lets := try clear cfg0; try clear H0.
Lemma all_disjoint_of_forall : forall (E : env) r rs,
(forall r', In r' rs -> extent_disjoint E r r') -> all_disjoint E r rs.
Proof. intros E r rs H. induction rs as [|r' rs IH]; cbn; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros x Hx; apply H; right; exact Hx]. Qed.
Definition SREGS : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition at_RETK (W' : world tfibsegs) (cfg' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
cfg' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
MEQ mem' /\
(forall a, WIN a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem tfibsegs m PCv 4 (CNTPv + 1) /\ val_mem tfibsegs m SLOTv 4 (RELv / 16) /\
(cnt = MAXv ->
val_mem tfibsegs m RGv 8 0 /\ val_mem tfibsegs m (RGv + 16) 8 (old + Nv) /\ val_mem tfibsegs m (RGv + 24) 8 mf /\
(forall i v, 0 <= i < Nv -> val_mem tfibsegs m0 (SRCv + 4 * i) 4 v -> val_mem tfibsegs m (DSTv + 4 * i) 4 v)).
End e.
End d.
