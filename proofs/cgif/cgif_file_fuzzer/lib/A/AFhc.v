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
Definition YFRAME : Z := 112.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD,
A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax, YFRAME in *.
Definition rT : nat := 32.
Definition rSB : nat := 34.
Definition rB : nat := 40.
Definition rBC : nat := 43.
Definition rHI : nat := 44.
Definition rS7 : nat := 45.
Definition rI : nat := 52.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (b bc hi i : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Definition S7v : Z := b + 144 + 8 * i.
Definition XW : list word :=
[ w64 T; w64 0; w64 SB; w64 0; w64 0; w64 0; w64 0; w64 0; w64 b; w64 0; w64 0; w64 bc; w64 hi; w64 S7v; w64 0; w64 0; w64 0; w64 0;
w64 0; w64 0; w64 i ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EqSB : ew E0 34 = w64 SB. Proof. reflexivity. Qed.
Lemma EqB : ew E0 40 = w64 b. Proof. reflexivity. Qed.
Lemma EqBC : ew E0 43 = w64 bc. Proof. reflexivity. Qed.
Lemma EqHI : ew E0 44 = w64 hi. Proof. reflexivity. Qed.
Lemma EqS7 : ew E0 45 = w64 S7v. Proof. reflexivity. Qed.
Lemma EqI : ew E0 52 = w64 i. Proof. reflexivity. Qed.
Definition R_STK : YP09.region := YP09.mkRegion (Some 2%nat) 0 (YFRAME + 32) 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 32%nat t_cache))].
Definition REG0 : smem := [ R_STK; fatom8 (A_ALLOCATOR + 32) 34%nat ].
Definition R_SLOT : YP09.region := YP09.mkRegion (Some 45%nat) (-120) (-112) 0 0 [YP09.mkChunk (-120) (CVal 8 (SOff 44%nat 0))].
Definition FFY : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + DRSTACK - YFRAME) (kHighMemEnd - YFRAME - 32) 4);
(32%nat, mkAF 4096 (CEIL_MAX - 4096) 12)    ;
(34%nat, mkAF kHighMemBeg CEIL_MAX 16);
(40%nat, mkAF kHighMemBeg (CEIL_MAX - 8192) 13);
(43%nat, mkAF 1 kBatchSlots 0);
(44%nat, mkAF 0 CEIL_MAX 4);
(45%nat, mkAF kHighMemBeg CEIL_MAX 3);
(52%nat, mkAF 1 kBatchSlots 0) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
4%bv (SLit TFIB_TP)) 8%bv (SOff 2%nat YFRAME)) 9%bv (SLit A_ALLOCATOR)) 18%bv (SLit (A_ALLOCATOR + 64))) 19%bv (SLit (A_ALLOCATOR + 688)))
21%bv (SLit (2 ^ 37))) 20%bv (SOff 40%nat 0)) 22%bv (SOff 43%nat 0)) 23%bv (SOff 45%nat 0)) 24%bv (SOff 43%nat 16)) 25%bv (SOff 52%nat 15).
Definition SS0 : sstate := mkSS 0x334f8 SR0 REG0 None FFY.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x334f8) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_Htp : getr regs0 4 = w64 TFIB_TP;
fh_Hsp : ly_stk_lo ly + DRSTACK <= sp0 + YFRAME /\ sp0 + YFRAME + 32 <= ly_stk_hi ly;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 <= a < sp0 + YFRAME + 32 -> apresent (w_H W) mem0 a;
fh_regs : getr regs0 8 = w64 (sp0 + YFRAME) /\ getr regs0 9 = w64 A_ALLOCATOR /\ getr regs0 18 = w64 (A_ALLOCATOR + 64) /\
getr regs0 19 = w64 (A_ALLOCATOR + 688) /\ getr regs0 21 = w64 (2 ^ 37) /\
getr regs0 20 = w64 b /\ getr regs0 22 = w64 bc /\ getr regs0 23 = w64 S7v /\ getr regs0 24 = w64 (bc + 16) /\ getr regs0 25 = w64 (i + 15);
fh_cb : val_mem tfibsegs m0 (sp0 + 8) 8 (T + t_cache);
fh_sb : val_mem tfibsegs m0 (A_ALLOCATOR + 32) 8 SB;
fh_Hb : SB + region_off kBatchClass <= b /\ b + kBatchBytes <= SB + region_off kBatchClass + 2 ^ 31 /\ b mod 8192 = 0;
fh_Hi : 1 <= i <= bc /\ bc <= kBatchSlots;
fh_slot : i < bc -> val_mem tfibsegs m0 (b + 24 + 8 * i) 8 hi /\ (forall a, b + 24 + 8 * i <= a < b + 32 + 8 * i -> apresent (w_H W) mem0 a) /\
4096 <= hi /\ hi + 16 <= ASAN_CEIL /\ hi mod 16 = 0;
fh_Hhi : 0 <= hi < ASAN_CEIL /\ hi mod 16 = 0;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x334f8) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH :=
pose proof (fh_LY FH) as LY;
pose proof (fh_IMG FH) as IMG;
pose proof (fh_Htp FH) as Htp;
pose proof (fh_Hsp FH) as Hsp;
pose proof (fh_Hsp_al FH) as Hsp_al;
pose proof (fh_pres FH) as Hpres;
pose proof (fh_regs FH) as Hregs;
pose proof (fh_cb FH) as Hcb;
pose proof (fh_sb FH) as Hsb;
pose proof (fh_Hb FH) as Hb;
pose proof (fh_Hi FH) as Hi;
pose proof (fh_slot FH) as Hslot;
pose proof (fh_Hhi FH) as Hhi0;
pose proof (fh_SEED FH) as SEED.
Lemma LYB :
kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly) /\ SB mod 65536 = 0 /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ T mod 4096 = 0.
Proof.
open_FH.
pose proof (lo_high ly LY) as HI. unfold in_high in HI. cbn [fst snd] in HI.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) (Forall_nth_f _ _ 2 _ (lo_app ly LY) eq_refl) (pairwise_ij_f _ _ 2 6 _ _ (lo_disj ly LY) eq_refl eq_refl)) as ZT.
assert (ZT2 : ly_T ly + kThreadObjSize <= ASAN_CEIL) by (clear - ZT; unfold zone3 in ZT; lia).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in ly LY) as HSPC. pose proof (lo_space_al ly LY) as SAL.
pose proof (lo_T_al ly LY) as TAL. unfold page_aligned in TAL.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
unfold zdisjoint in PSTK. cbn [fst snd] in *. unfold SB, T in *.
repeat match goal with |- _ /\ _ => split end; first [exact ZT | exact TAL | exact ZT2 | clear ZT; lia].
Qed.
Lemma derived_ranges :
kHighMemBeg <= SB /\ SB + kSpaceSize <= ASAN_CEIL /\ SB mod 65536 = 0 /\ SB + 24 * 2 ^ 32 <= b /\ b + kBatchBytes <= SB + 24 * 2 ^ 32 + 2 ^ 31 /\ b mod 8192 = 0 /\
1 <= i <= bc /\ bc <= kBatchSlots /\ 0 <= hi < ASAN_CEIL /\ S7v = b + 144 + 8 * i /\
4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg + DRSTACK - YFRAME <= sp0 /\ sp0 + YFRAME + 32 <= kHighMemEnd.
Proof.
open_FH. pose proof LYB as LB. destruct Hb as (B1 & B2 & B3). destruct Hsp as [S1 S2]. destruct Hhi0 as [H1 _].
assert (RO : region_off kBatchClass = 24 * 2 ^ 32) by reflexivity. rewrite RO in B1, B2.
unfold S7v. clear - LB B1 B2 B3 S1 S2 H1 Hi. numconst. repeat split; lia.
Qed.
Definition WIN (a : Z) : Prop := False.
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
Definition WSK0 : list (option nat * Z * Z) := [].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK0.
Proof. intros E HE t a Hin Hr. destruct Hin. Qed.
Lemma windows_WIN : forall (E : env) SK rs a,
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
intros E SK rs a HSK Hb0 Hw. destruct (in_wrange_windows E rs a Hw) as (b0 & lo & hi' & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb0 _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> m x = mem0 x.
Lemma MEQ_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQ m -> MEQ m'.
Proof. intros E SK rs m m' HSK Hb0 HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WIN E SK rs _ HSK Hb0 Hw). Qed.
Lemma MEQ_0 : MEQ mem0. Proof. intros x _. reflexivity. Qed.
Definition SREGS : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27]%bv.
Definition at_RCi (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ i < bc /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 A_RChunk) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ getr regs' 1 = w64 0x334f8 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 10 = w64 (sp0 + 8) /\ getr regs' 11 = w64 hi /\ getr regs' 23 = w64 (S7v + 8) /\ getr regs' 25 = w64 (i + 16) /\
MEQ mem'.
Definition at_CD24 (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ i = bc /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 A_CDealloc) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ getr regs' 1 = w64 0x33530 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 10 = w64 (T + t_cache) /\ getr regs' 11 = w64 A_ALLOCATOR /\ getr regs' 12 = w64 kBatchClass /\ getr regs' 13 = w64 b /\
MEQ mem'.
Definition postR : world tfibsegs -> config -> Prop := if i <? bc then at_RCi else at_CD24.
End d.
End c.
