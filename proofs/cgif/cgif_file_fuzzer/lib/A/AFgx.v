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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD,
A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Definition xT : nat := 32.   Definition xC : nat := 33.   Definition xSB : nat := 34.  Definition xM : nat := 35.   Definition xMAP : nat := 36.
Definition xLEN : nat := 37. Definition xHW : nat := 38.  Definition xNN : nat := 39.  Definition xJ1 : nat := 40.  Definition xJ2 : nat := 41.
Definition xCBP : nat := 42. Definition xRA : nat := 43.  Definition xS0 : nat := 44.  Definition xS1 : nat := 45.  Definition xS2 : nat := 46.
Definition xS3 : nat := 47.  Definition xS4 : nat := 48.
Definition GFRAME : Z := 80.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Definition XW : list word :=
[ w64 T; w64 (ly_C ly); w64 SB; w64 m; w64 map; w64 len; w64 hw; w64 nn; w64 j1; w64 j2; w64 cbp; w64 vra; w64 vs0; w64 vs1; w64 vs2; w64 vs3; w64 vs4 ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EqC : ew E0 33 = w64 (ly_C ly). Proof. reflexivity. Qed.
Lemma EqSB : ew E0 34 = w64 SB. Proof. reflexivity. Qed.
Lemma EqM : ew E0 35 = w64 m. Proof. reflexivity. Qed.
Lemma EqMAP : ew E0 36 = w64 map. Proof. reflexivity. Qed.
Lemma EqLEN : ew E0 37 = w64 len. Proof. reflexivity. Qed.
Lemma EqHW : ew E0 38 = w64 hw. Proof. reflexivity. Qed.
Lemma EqNN : ew E0 39 = w64 nn. Proof. reflexivity. Qed.
Lemma EqJ1 : ew E0 40 = w64 j1. Proof. reflexivity. Qed.
Lemma EqJ2 : ew E0 41 = w64 j2. Proof. reflexivity. Qed.
Lemma EqCBP : ew E0 42 = w64 cbp. Proof. reflexivity. Qed.
Lemma EqRA : ew E0 43 = w64 vra. Proof. reflexivity. Qed.
Lemma EqS0 : ew E0 44 = w64 vs0. Proof. reflexivity. Qed.
Lemma EqS1 : ew E0 45 = w64 vs1. Proof. reflexivity. Qed.
Lemma EqS2 : ew E0 46 = w64 vs2. Proof. reflexivity. Qed.
Lemma EqS3 : ew E0 47 = w64 vs3. Proof. reflexivity. Qed.
Lemma EqS4 : ew E0 48 = w64 vs4. Proof. reflexivity. Qed.
Definition R_STK : YP09.region := YP09.mkRegion (Some 2%nat) 0 80 0 32
[YP09.mkChunk 0 (CVal 8 (SOff 46%nat 0)); YP09.mkChunk 8 (CVal 8 (SOff 35%nat 0)); YP09.mkChunk 16 (CVal 8 (SOff 42%nat 0)); YP09.mkChunk 24 (CVal 8 (SLit 0x335e4));
YP09.mkChunk 32 (CVal 8 (SOff 48%nat 0)); YP09.mkChunk 40 (CVal 8 (SOff 47%nat 0)); YP09.mkChunk 48 (CVal 8 (SOff 46%nat 0));
YP09.mkChunk 56 (CVal 8 (SOff 45%nat 0)); YP09.mkChunk 64 (CVal 8 (SOff 44%nat 0)); YP09.mkChunk 72 (CVal 8 (SOff 43%nat 0))].
Definition R_MAPH : YP09.region := YP09.mkRegion (Some 36%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36%nat 0)); YP09.mkChunk 8 (CVal 8 (SOff 37%nat 0))].
Definition R_HDR : YP09.region := YP09.mkRegion (Some 35%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 38%nat 0)); YP09.mkChunk 4 (CVal 4 (SOff 39%nat 0))].
Definition R_MUT1 : YP09.region := YP09.mkRegion None (A_ALLOCATOR + 680) (A_ALLOCATOR + 681) (A_ALLOCATOR + 680) (A_ALLOCATOR + 681) [YP09.mkChunk (A_ALLOCATOR + 680) (CVal 1 (SLit 1))].
Definition R_CTX : YP09.region := YP09.mkRegion (Some 33%nat) 0 160 0 0 [YP09.mkChunk 8 (CVal 4 (SLit 0)); YP09.mkChunk 152 (CVal 8 (SOff 32%nat 0))].
Definition R_JST : YP09.region :=
YP09.mkRegion (Some 32%nat) (t_stats + 40) (t_stats + 56) (t_stats + 40) (t_stats + 56)
[YP09.mkChunk (t_stats + 40) (CVal 8 (SOff 40%nat 0)); YP09.mkChunk (t_stats + 48) (CVal 8 (SOff 41%nat 0))].
Definition REG0 : smem :=
[ R_STK; R_MAPH; R_HDR; R_MUT1; R_CTX; R_JST;
flit8 (A_ALLOCATOR + 64) 4096  ; fatom8 (A_ALLOCATOR + 32) 34%nat  ;
flit1 0xa5860 1; flit4 0xa5864 0  ;
flit8 (TFIB_TP - 88) TFIB_TSD; fatom8 TFIB_TSD 33%nat ].
Definition FFX : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + KSTACK - GFRAME) (kHighMemEnd - GFRAME) 4);
(32%nat, mkAF 4096 (CEIL_MAX - 4096) 12)    ;
(33%nat, mkAF 4096 (CEIL_MAX - 256) 3)      ;
(34%nat, mkAF kHighMemBeg CEIL_MAX 16);
(35%nat, mkAF 4096 (CEIL_MAX - 16) 4)      ;
(36%nat, mkAF 4096 (CEIL_MAX - 8192) 12)   ;
(37%nat, mkAF 8192 (2 ^ 29) 12);
(38%nat, mkAF 0 65535 0);
(39%nat, mkAF 1 (2 ^ 28) 0);
(40%nat, mkAF 0 (2 ^ 64 - 1) 0);
(41%nat, mkAF 0 (2 ^ 64 - 1) 0);
(42%nat, mkAF kHighMemBeg (kHighMemEnd - 16) 3);
(43%nat, mkAF 0 (2 ^ 64 - 1) 0); (44%nat, mkAF 0 (2 ^ 64 - 1) 0); (45%nat, mkAF 0 (2 ^ 64 - 1) 0);
(46%nat, mkAF 0 (2 ^ 64 - 1) 0); (47%nat, mkAF 0 (2 ^ 64 - 1) 0); (48%nat, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
4%bv (SLit TFIB_TP)) 10%bv (SLit (A_ALLOCATOR + 64))) 11%bv (SOff 35%nat 0)) 13%bv (SOff 36%nat 0)) 8%bv (SLit (A_ALLOCATOR + 680)))
9%bv (SOff 35%nat 0)) 18%bv (SOff 46%nat 0)) 19%bv (SLit A_ALLOCATOR)) 20%bv (SLit (2 ^ 37)).
Definition SS0 : sstate := mkSS 0x33888 SR0 REG0 None FFX.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33888) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_Htp : getr regs0 4 = w64 TFIB_TP;
fh_regs : getr regs0 10 = w64 (A_ALLOCATOR + 64) /\ getr regs0 11 = w64 m /\ getr regs0 13 = w64 map /\ getr regs0 8 = w64 (A_ALLOCATOR + 680) /\
getr regs0 9 = w64 m /\ getr regs0 18 = w64 vs2 /\ getr regs0 19 = w64 A_ALLOCATOR /\ getr regs0 20 = w64 (2 ^ 37);
fh_Hsp : ly_stk_lo ly + KSTACK <= sp0 + GFRAME /\ sp0 + GFRAME <= ly_stk_hi ly;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 + GFRAME - KSTACK <= a < sp0 + GFRAME -> apresent (w_H W) mem0 a;
fh_frames : val_mem tfibsegs m0 sp0 8 vs2 /\ val_mem tfibsegs m0 (sp0 + 8) 8 m /\ val_mem tfibsegs m0 (sp0 + 16) 8 cbp /\ val_mem tfibsegs m0 (sp0 + 24) 8 0x335e4 /\
val_mem tfibsegs m0 (sp0 + 32) 8 vs4 /\ val_mem tfibsegs m0 (sp0 + 40) 8 vs3 /\ val_mem tfibsegs m0 (sp0 + 48) 8 vs2 /\
val_mem tfibsegs m0 (sp0 + 56) 8 vs1 /\ val_mem tfibsegs m0 (sp0 + 64) 8 vs0 /\ val_mem tfibsegs m0 (sp0 + 72) 8 vra;
fh_Hsaved : 0 <= cbp < 2 ^ 64 /\ 0 <= vra < 2 ^ 64 /\ 0 <= vs0 < 2 ^ 64 /\ 0 <= vs1 < 2 ^ 64 /\ 0 <= vs2 < 2 ^ 64 /\ 0 <= vs3 < 2 ^ 64 /\ 0 <= vs4 < 2 ^ 64 /\
kHighMemBeg <= cbp /\ cbp + 16 <= kHighMemEnd /\ cbp mod 8 = 0;
fh_Hmap : zone3 map len /\ map + len <= ASAN_CEIL /\ map mod 4096 = 0 /\ 8192 <= len <= 2 ^ 29 /\ len mod 4096 = 0 /\
map + 4096 + 16 <= m /\ m + nn <= map + len /\ m mod 16 = 0 /\ (map + 4096 < SB \/ SB + 2 ^ 37 <= map + 4096);
fh_maph : val_mem tfibsegs m0 map 8 map /\ val_mem tfibsegs m0 (map + 8) 8 len /\ (forall a, map <= a < map + 16 -> apresent (w_H W) mem0 a);
fh_Hhw : 0 <= hw < 65536 /\ 1 <= nn < 2 ^ 28;
fh_hdr : val_mem tfibsegs m0 m 4 hw /\ val_mem tfibsegs m0 (m + 4) 4 nn /\ (forall a, m <= a < m + 8 -> apresent (w_H W) mem0 a);
fh_mut : val_mem tfibsegs m0 (A_ALLOCATOR + 680) 1 1;
fh_sb : val_mem tfibsegs m0 (A_ALLOCATOR + 32) 8 SB;
fh_tsd : val_mem tfibsegs m0 TFIB_TSD 8 (ly_C ly) /\ val_mem tfibsegs m0 (ly_C ly + 8) 4 0 /\ val_mem tfibsegs m0 (ly_C ly + 152) 8 T
;
fh_jst : val_mem tfibsegs m0 (T + t_stats + 40) 8 j1 /\ val_mem tfibsegs m0 (T + t_stats + 48) 8 j2 /\ 0 <= j1 < 2 ^ 64 /\ 0 <= j2 < 2 ^ 64 /\
(forall a, T + t_stats + 40 <= a < T + t_stats + 56 -> apresent (w_H W) mem0 a);
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x33888) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH :=
pose proof (fh_LY FH) as LY;
pose proof (fh_IMG FH) as IMG;
pose proof (fh_Htp FH) as Htp;
pose proof (fh_regs FH) as Hregs;
pose proof (fh_Hsp FH) as Hsp;
pose proof (fh_Hsp_al FH) as Hsp_al;
pose proof (fh_pres FH) as Hpres;
pose proof (fh_frames FH) as Hframes;
pose proof (fh_Hsaved FH) as Hsaved;
pose proof (fh_Hmap FH) as Hmap;
pose proof (fh_maph FH) as Hmaph;
pose proof (fh_Hhw FH) as Hhw;
pose proof (fh_hdr FH) as Hhdr;
pose proof (fh_mut FH) as Hmut;
pose proof (fh_sb FH) as Hsb;
pose proof (fh_tsd FH) as Htsd;
pose proof (fh_jst FH) as Hjst;
pose proof (fh_SEED FH) as SEED.
Lemma LYB :
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly <= SB /\
SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly /\ SB mod 65536 = 0 /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ ly_C ly mod 8 = 0 /\ T mod 4096 = 0 /\
(T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_hi ly <= T) /\ (ly_C ly + 256 <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_C ly) /\
(T + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= T).
Proof.
open_FH.
pose proof (lo_high ly LY) as HI. unfold in_high in HI. cbn [fst snd] in HI.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) (Forall_nth_f _ _ 2 _ (lo_app ly LY) eq_refl) (pairwise_ij_f _ _ 2 6 _ _ (lo_disj ly LY) eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(clear_all; lia) (Forall_nth_f _ _ 6 _ (lo_app ly LY) eq_refl) (pairwise_ij_f _ _ 6 2 _ _ (lo_disj ly LY) eq_refl eq_refl)) as ZC.
assert (ZT2 : ly_T ly + kThreadObjSize <= ASAN_CEIL) by (clear - ZT; unfold zone3 in ZT; lia). assert (ZC2 : ly_C ly + 256 <= ASAN_CEIL) by (clear - ZC; unfold zone3 in ZC; lia).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in ly LY) as HSPC. pose proof (lo_space_al ly LY) as SAL.
pose proof (lo_stk_ceil ly LY) as CE. pose proof (lo_C_al ly LY) as CAL. pose proof (lo_T_al ly LY) as TAL. unfold page_aligned in TAL.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & _ & _ & _ & DC & _).
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DC as [_ DC]. apply Forall_cons_iff in DC as [CSTK _].
unfold zdisjoint in TSTK, TC, CSTK. cbn [fst snd] in *. unfold T, SB in *. ceil; unfold kHighMemBeg in *.
repeat match goal with |- _ /\ _ => split end; first [exact ZT | exact ZC | clear ZT ZC; unfold ASAN_CEIL in *; lia].
Qed.
Definition WIN (a : Z) : Prop := (sp0 <= a < sp0 + 32) \/ (A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 681) \/ (T + t_stats + 40 <= a < T + t_stats + 56).
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
Definition WSK0 : list (option nat * Z * Z) := [ (Some 2%nat, 0, 32); (None, A_ALLOCATOR + 680, A_ALLOCATOR + 681); (Some 32%nat, t_stats + 40, t_stats + 56) ].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK0.
Proof.
intros E HE t a Hin Hr. unfold WIN. cbn [WSK0 In] in Hin. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd base_val] in Hr.
- left. rewrite (HE 2%nat ltac:(cbv; lia)), E2 in Hr. unfold sp0. lia.
- right. left. lia.
- right. right. rewrite (HE 32%nat ltac:(cbv; lia)), EqT in Hr. pose proof LYB as (L1 & L2 & _). unfold w64 in Hr. rewrite unsigned_lit_small in Hr by (clear - L1 L2; ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia). lia.
Qed.
Lemma windows_WIN : forall (E : env) SK rs a,
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
intros E SK rs a HSK Hb0 Hw. destruct (in_wrange_windows E rs a Hw) as (b0 & lo & hi' & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb0 _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Definition MEQ (mm : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> mm x = mem0 x.
Lemma MEQ_frame : forall (E : env) SK rs (ma mb : word -> option byte),
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs ma mb -> MEQ ma -> MEQ mb.
Proof. intros E SK rs ma mb HSK Hb0 HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WIN E SK rs _ HSK Hb0 Hw). Qed.
Lemma MEQ_0 : MEQ mem0. Proof. intros x _. reflexivity. Qed.
Definition SREGS : list (bv 5) := [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition at_LMD (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33b38) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 2 = w64 (sp0 + GFRAME) /\ getr regs' 1 = w64 vra /\ getr regs' 8 = w64 vs0 /\ getr regs' 9 = w64 vs1 /\ getr regs' 18 = w64 vs2 /\
getr regs' 19 = w64 vs3 /\ getr regs' 20 = w64 vs4 /\
getr regs' 10 = w64 (A_ALLOCATOR + 64) /\ getr regs' 11 = w64 (A_ALLOCATOR + 688) /\ getr regs' 12 = w64 (map + 4096) /\
MEQ mem' /\
(forall a, sp0 <= a < sp0 + 32 -> apresent (w_H W) mem' a) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 680) 1 0 /\
val_mem tfibsegs (mrestrict (w_H W) mem') (T + t_stats + 40) 8 ((j1 + 1) mod 2 ^ 64) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (T + t_stats + 48) 8 ((j2 + nn) mod 2 ^ 64).
End c.
End b.
