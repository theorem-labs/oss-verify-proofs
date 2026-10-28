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
Definition rSB : nat := 32.
Definition rM : nat := 33.
Definition rN : nat := 34.
Definition rQ : nat := 35.
Definition GFRAME : Z := 80.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (m n q : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Definition XW : list word := [ w64 SB; w64 m; w64 n; w64 q ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma EqSB : ew E0 32 = w64 SB. Proof. reflexivity. Qed.
Lemma EqM : ew E0 33 = w64 m. Proof. reflexivity. Qed.
Lemma EqN : ew E0 34 = w64 n. Proof. reflexivity. Qed.
Lemma EqQ : ew E0 35 = w64 q. Proof. reflexivity. Qed.
Definition R_STK : YP09.region := YP09.mkRegion (Some 2%nat) (- GFRAME) 0 (- GFRAME) 0 [].
Definition R_MUT : YP09.region :=
YP09.mkRegion None (A_ALLOCATOR + 680) (A_ALLOCATOR + 684) (A_ALLOCATOR + 680) (A_ALLOCATOR + 684) [YP09.mkChunk (A_ALLOCATOR + 680) (CVal 4 (SLit 0))].
Definition REG0 : smem := [ R_STK; R_MUT; fatom8 (A_ALLOCATOR + 32) 32%nat; fatom8 (A_ALLOCATOR + 120) 34%nat; fatom8 (A_ALLOCATOR + 72) 35%nat ].
Definition FFA : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + KSTACK) kHighMemEnd 4);
(32%nat, mkAF kHighMemBeg CEIL_MAX 16);
(33%nat, mkAF 4096 (CEIL_MAX - 16) 4)    ;
(34%nat, mkAF 1 16384 0);
(35%nat, mkAF 4096 CEIL_MAX 12)            ] [] [].
Definition SR0 : list sv := sr_set sr_atoms 11%bv (SOff 33%nat 0).
Definition SS0 : sstate := mkSS A_RChunk SR0 REG0 None FFA.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 A_RChunk) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_regs : getr regs0 11 = w64 m;
fh_Hsp : ly_stk_lo ly + KSTACK <= sp0 /\ sp0 <= ly_stk_hi ly;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 - KSTACK <= a < sp0 -> apresent (w_H W) mem0 a;
fh_Hm : 4096 <= m /\ m + 16 <= ASAN_CEIL /\ m mod 16 = 0 /\ (m < SB \/ SB + 2 ^ 37 <= m);
fh_sb : val_mem tfibsegs m0 (A_ALLOCATOR + 32) 8 SB;
fh_n : val_mem tfibsegs m0 (A_ALLOCATOR + 120) 8 n /\ 1 <= n <= 16384;
fh_q : val_mem tfibsegs m0 (A_ALLOCATOR + 72) 8 q /\ 4096 <= q /\ q + 8 * n <= ASAN_CEIL /\ q mod 4096 = 0;
fh_mut : val_mem tfibsegs m0 (A_ALLOCATOR + 680) 4 0    ;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 A_RChunk) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH :=
pose proof (fh_LY FH) as LY;
pose proof (fh_IMG FH) as IMG;
pose proof (fh_regs FH) as Hregs;
pose proof (fh_Hsp FH) as Hsp;
pose proof (fh_Hsp_al FH) as Hsp_al;
pose proof (fh_pres FH) as Hpres;
pose proof (fh_Hm FH) as Hm;
pose proof (fh_sb FH) as Hsb;
pose proof (fh_n FH) as Hn;
pose proof (fh_q FH) as Hq;
pose proof (fh_mut FH) as Hmut;
pose proof (fh_SEED FH) as SEED.
Lemma LYB :
kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly /\ SB mod 65536 = 0.
Proof.
open_FH.
pose proof (lo_high ly LY) as HI. unfold owned_extents in HI.
repeat match type of HI with Forall _ (_ :: _) => apply Forall_cons_iff in HI as [? HI] end.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in ly LY) as HSPC. pose proof (lo_space_al ly LY) as SAL.
pose proof (lo_stk_ceil ly LY) as CE.
unfold in_high in *. cbn [fst snd] in *. unfold SB. ceil; unfold ASAN_CEIL, kHighMemBeg in *.
repeat split; try lia.
Qed.
Definition WIN (a : Z) : Prop := (sp0 - GFRAME <= a < sp0) \/ (A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684).
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
Definition WSK0 : list (option nat * Z * Z) := [ (Some 2%nat, - GFRAME, 0); (None, A_ALLOCATOR + 680, A_ALLOCATOR + 684) ].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK0.
Proof.
intros E HE t a Hin Hr. unfold WIN. cbn [WSK0 In] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd base_val] in Hr.
- left. rewrite (HE 2%nat ltac:(cbv; lia)), E2 in Hr. unfold sp0. lia.
- right. lia.
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
Definition SREGS : list (bv 5) := [3; 4; 18; 21; 22; 23; 24; 25; 26; 27]%bv.
Let v (r : bv 5) : Z := bv_unsigned (getr regs0 r).
Definition at_L0 (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x3385c) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 2 = w64 (sp0 - GFRAME) /\ getr regs' 1 = w64 0x335e4 /\ getr regs' 8 = w64 (A_ALLOCATOR + 680) /\ getr regs' 9 = w64 m /\
getr regs' 10 = w64 (A_ALLOCATOR + 64) /\ getr regs' 11 = w64 m /\ getr regs' 12 = w64 q /\ getr regs' 13 = w64 0 /\ getr regs' 14 = w64 (q + 8 * n) /\
getr regs' 19 = w64 A_ALLOCATOR /\ getr regs' 20 = w64 (2 ^ 37) /\
MEQ mem' /\
(forall a, sp0 - GFRAME <= a < sp0 -> apresent (w_H W) mem' a) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 8) 8 (v 1%bv) /\ val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 16) 8 (v 8%bv) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 24) 8 (v 9%bv) /\ val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 32) 8 (v 18%bv) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 40) 8 (v 19%bv) /\ val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 48) 8 (v 20%bv) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 56) 8 0x335e4 /\ val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 64) 8 (v 10%bv) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 72) 8 m /\ val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 80) 8 (v 18%bv) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 680) 4 1.
End c.
End b.
