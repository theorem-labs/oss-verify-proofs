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
Definition rP : nat := 32.
Definition rCUR : nat := 33.
Definition rNR : nat := 34.
Definition rLIM : nat := 35.
Definition rH : nat := 36.
Definition nr_step (p nr h : Z) : Z := if (h <=? p) && (nr <? h) then h else nr.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (p cur nr lim h : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Definition XW : list word := [ w64 p; w64 cur; w64 nr; w64 lim; w64 h ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma EqP : ew E0 32 = w64 p. Proof. reflexivity. Qed.
Lemma EqCUR : ew E0 33 = w64 cur. Proof. reflexivity. Qed.
Lemma EqNR : ew E0 34 = w64 nr. Proof. reflexivity. Qed.
Lemma EqLIM : ew E0 35 = w64 lim. Proof. reflexivity. Qed.
Lemma EqH : ew E0 36 = w64 h. Proof. reflexivity. Qed.
Definition R_CUR : YP09.region := YP09.mkRegion (Some 33%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36%nat 0))].
Definition REG0 : smem := [ R_CUR ].
Definition FFL : facts := mkFacts
[ (32%nat, mkAF 4096 CEIL_MAX 4)          ;
(33%nat, mkAF 4096 (CEIL_MAX - 8) 3)    ;
(34%nat, mkAF 0 CEIL_MAX 0);
(35%nat, mkAF 4096 CEIL_MAX 3)          ;
(36%nat, mkAF 4096 CEIL_MAX 12)          ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set (sr_set sr_atoms 11%bv (SOff 32%nat 0)) 12%bv (SOff 33%nat 0)) 13%bv (SOff 34%nat 0)) 14%bv (SOff 35%nat 0).
Definition SS0 : sstate := mkSS 0x3385c SR0 REG0 None FFL.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x3385c) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_regs : getr regs0 11 = w64 p /\ getr regs0 12 = w64 cur /\ getr regs0 13 = w64 nr /\ getr regs0 14 = w64 lim;
fh_Hp : 4096 <= p < ASAN_CEIL /\ p mod 16 = 0;
fh_Hcur : 4096 <= cur /\ cur + 8 <= lim /\ lim <= ASAN_CEIL /\ cur mod 8 = 0 /\ lim mod 8 = 0;
fh_Hnr : 0 <= nr <= p;
fh_Hh : 4096 <= h < ASAN_CEIL /\ h mod 4096 = 0;
fh_cell : val_mem tfibsegs m0 cur 8 h /\ (forall a, cur <= a < cur + 8 -> apresent (w_H W) mem0 a);
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x3385c) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH :=
pose proof (fh_LY FH) as LY;
pose proof (fh_IMG FH) as IMG;
pose proof (fh_regs FH) as Hregs;
pose proof (fh_Hp FH) as Hp;
pose proof (fh_Hcur FH) as Hcur;
pose proof (fh_Hnr FH) as Hnr;
pose proof (fh_Hh FH) as Hh;
pose proof (fh_cell FH) as Hcell;
pose proof (fh_SEED FH) as SEED.
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
Definition SREGS : list (bv 5) := [1; 2; 3; 4; 6; 7; 8; 9; 10; 11; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition at_L (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ cur + 8 < lim /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x3385c) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 12 = w64 (cur + 8) /\ getr regs' 13 = w64 (nr_step p nr h) /\
MEQ mem'.
Definition at_XG (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ cur + 8 = lim /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33888) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 12 = w64 lim /\ getr regs' 13 = w64 (nr_step p nr h) /\
MEQ mem'.
Definition postL : world tfibsegs -> config -> Prop := if cur + 8 <? lim then at_L else at_XG.
End c.
End b.
