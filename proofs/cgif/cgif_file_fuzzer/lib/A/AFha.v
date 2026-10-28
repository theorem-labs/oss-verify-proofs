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
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD,
A_QUAR, A_ALLOCATOR, A_RChunk, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax, YFRAME in *.
Definition oT : nat := 32.
Definition oB : nat := 40.
Definition oNX : nat := 41.
Definition oBB : nat := 42.
Definition oBC : nat := 43.
Definition oH0 : nat := 44.
Definition oSZ : nat := 46.
Definition oQB : nat := 47.
Definition oLZ : nat := 49.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (b nx bb bc h0 sz qb lz : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let m0 := mrestrict (w_H W) mem0.
Definition XW : list word :=
[ w64 T; w64 0; w64 0; w64 0; w64 0; w64 0; w64 0; w64 0; w64 b; w64 nx; w64 bb; w64 bc; w64 h0; w64 0; w64 sz; w64 qb; w64 0; w64 lz ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EqB : ew E0 40 = w64 b. Proof. reflexivity. Qed.
Lemma EqNX : ew E0 41 = w64 nx. Proof. reflexivity. Qed.
Lemma EqBB : ew E0 42 = w64 bb. Proof. reflexivity. Qed.
Lemma EqBC : ew E0 43 = w64 bc. Proof. reflexivity. Qed.
Lemma EqH0 : ew E0 44 = w64 h0. Proof. reflexivity. Qed.
Lemma EqSZ : ew E0 46 = w64 sz. Proof. reflexivity. Qed.
Lemma EqQB : ew E0 47 = w64 qb. Proof. reflexivity. Qed.
Lemma EqLZ : ew E0 49 = w64 lz. Proof. reflexivity. Qed.
Definition R_STK : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 (YFRAME + 32) YFRAME (YFRAME + 32)
[YP09.mkChunk (YFRAME + 0) (CVal 8 (SOff 46%nat 0)); YP09.mkChunk (YFRAME + 8) (CVal 8 (SOff 40%nat 0));
YP09.mkChunk (YFRAME + 16) (CVal 8 (SOff 49%nat 0)); YP09.mkChunk (YFRAME + 24) (CVal 8 (SOff 47%nat 0))].
Definition R_B : YP09.region :=
YP09.mkRegion (Some 40%nat) 0 32 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 41%nat 0)); YP09.mkChunk 8 (CVal 8 (SOff 42%nat 0));
YP09.mkChunk 16 (CVal 8 (SOff 43%nat 0)); YP09.mkChunk 24 (CVal 8 (SOff 44%nat 0))].
Definition REG0 : smem := [ R_STK; R_B ].
Definition FFO : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + DRSTACK - YFRAME) (kHighMemEnd - YFRAME - 32) 4);
(40%nat, mkAF kHighMemBeg (CEIL_MAX - 8192) 13);
(41%nat, mkAF 0 CEIL_MAX 13);
(42%nat, mkAF 0 (2 ^ 64 - 1) 0);
(43%nat, mkAF 1 kBatchSlots 0);
(44%nat, mkAF 4096 CEIL_MAX 4)    ;
(46%nat, mkAF 1 (2 ^ 40) 0);
(47%nat, mkAF 0 (2 ^ 64 - 1) 0);
(49%nat, mkAF 0 CEIL_MAX 0) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 8%bv (SOff 2%nat YFRAME)) 9%bv (SLit A_ALLOCATOR))
18%bv (SLit (A_ALLOCATOR + 64))) 19%bv (SLit (A_ALLOCATOR + 688))) 21%bv (SLit (2 ^ 37))) 10%bv (SOff 46%nat 0).
Definition SS0 : sstate := mkSS 0x334ac SR0 REG0 None FFO.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x334ac) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_Htp : getr regs0 4 = w64 TFIB_TP;
fh_Hsp : ly_stk_lo ly + DRSTACK <= sp0 + YFRAME /\ sp0 + YFRAME + 32 <= ly_stk_hi ly;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 + YFRAME <= a < sp0 + YFRAME + 32 -> apresent (w_H W) mem0 a;
fh_regs : getr regs0 8 = w64 (sp0 + YFRAME) /\ getr regs0 9 = w64 A_ALLOCATOR /\ getr regs0 18 = w64 (A_ALLOCATOR + 64) /\
getr regs0 19 = w64 (A_ALLOCATOR + 688) /\ getr regs0 21 = w64 (2 ^ 37) /\ getr regs0 10 = w64 sz;
fh_Hb : ly_prim ly <= b /\ b + kBatchBytes <= ly_prim ly + kPrimResvSize /\ b mod 8192 = 0 /\ (forall a, b <= a < b + 32 -> apresent (w_H W) mem0 a);
fh_Hnx : 0 <= nx < ASAN_CEIL /\ nx mod 8192 = 0;
fh_Hbc : 1 <= bc <= kBatchSlots;
fh_Hby : 0 <= bb < 2 ^ 64 /\ 0 <= qb < 2 ^ 64;
fh_Hsz : 1 <= sz < 2 ^ 40;
fh_Hlz : 0 <= lz < ASAN_CEIL;
fh_Hh0 : 4096 <= h0 /\ h0 + 16 <= ASAN_CEIL /\ h0 mod 16 = 0;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x334ac) mem0 (seg_rom tfibsegs)))
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
pose proof (fh_Hb FH) as Hb;
pose proof (fh_Hnx FH) as Hnx;
pose proof (fh_Hbc FH) as Hbc;
pose proof (fh_Hby FH) as Hby;
pose proof (fh_Hsz FH) as Hsz;
pose proof (fh_Hlz FH) as Hlz;
pose proof (fh_Hh0 FH) as Hh0;
pose proof (fh_SEED FH) as SEED.
Lemma LYB :
kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly).
Proof.
open_FH.
pose proof (lo_high ly LY) as HI. unfold owned_extents in HI.
repeat match type of HI with Forall _ (_ :: _) => apply Forall_cons_iff in HI as [? HI] end.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
unfold zdisjoint in PSTK. unfold in_high in *. cbn [fst snd] in *.
repeat split; try lia.
Qed.
Lemma derived_ranges :
kHighMemBeg <= b /\ b + kBatchBytes <= ASAN_CEIL /\ b mod 8192 = 0 /\ 0 <= nx < ASAN_CEIL /\ 1 <= bc <= kBatchSlots /\
0 <= bb < 2 ^ 64 /\ 0 <= qb < 2 ^ 64 /\ True /\ 1 <= sz < 2 ^ 40 /\ 0 <= lz < ASAN_CEIL /\ 4096 <= h0 /\ h0 + 16 <= ASAN_CEIL /\
kHighMemBeg + DRSTACK - YFRAME <= sp0 /\ sp0 + YFRAME + 32 <= kHighMemEnd.
Proof.
open_FH. pose proof LYB as LB. destruct Hb as (B1 & B2 & B3 & _). destruct Hsp as [S1 S2]. destruct Hh0 as (H1 & H2 & _).
clear - LB B1 B2 B3 S1 S2 H1 H2 Hnx Hbc Hby Hsz Hlz. numconst. repeat split; lia.
Qed.
Definition WIN (a : Z) : Prop := sp0 + YFRAME <= a < sp0 + YFRAME + 32.
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
Definition WSK0 : list (option nat * Z * Z) := [(Some 2%nat, YFRAME, YFRAME + 32)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK0.
Proof.
intros E HE t a Hin Hr. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN. unfold aHAVf in *.
destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr. rewrite HE in Hr by (cbv; lia). rewrite E2 in Hr. unfold sp0 in *. lia.
Qed.
Lemma windows_WIN : forall (E : env) SK rs a,
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
intros E SK rs a HSK Hb0 Hw. destruct (in_wrange_windows E rs a Hw) as (b0 & lo & hi & Hin & Hr).
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
Definition SREGS : list (bv 5) := [3; 4; 8; 9; 18; 19; 21; 26; 27]%bv.
Definition LZn : Z := if nx =? 0 then 0 else lz.
Definition at_RC0 (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 A_RChunk) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ getr regs' 1 = w64 0x334f8 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 10 = w64 (sp0 + 8) /\ getr regs' 11 = w64 h0 /\
getr regs' 20 = w64 b /\ getr regs' 22 = w64 bc /\ getr regs' 23 = w64 (b + 152) /\ getr regs' 24 = w64 (bc + 16) /\ getr regs' 25 = w64 16 /\
MEQ mem' /\
(forall a, WIN a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem tfibsegs m (sp0 + YFRAME) 8 (sz - 1) /\ val_mem tfibsegs m (sp0 + YFRAME + 8) 8 nx /\
val_mem tfibsegs m (sp0 + YFRAME + 16) 8 LZn /\ val_mem tfibsegs m (sp0 + YFRAME + 24) 8 (zcanon (qb - bb)).
End d.
End c.
