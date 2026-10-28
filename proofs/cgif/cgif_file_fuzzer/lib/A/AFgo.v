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
Definition oRI : nat := 32.
Definition oC : nat := 33.
Definition oRG : nat := 34.
Definition oNF : nat := 35.
Definition oJ80 : nat := 36.
Definition oJ88 : nat := 37.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (ri c nf j80 j88 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let m0 := mrestrict (w_H W) mem0.
Definition RGv : Z := ri + 128 * c.
Definition XW : list word := [ w64 ri; w64 c; w64 RGv; w64 nf; w64 j80; w64 j88 ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma EqRI : ew E0 32 = w64 ri. Proof. reflexivity. Qed.
Lemma EqC : ew E0 33 = w64 c. Proof. reflexivity. Qed.
Lemma EqRG : ew E0 34 = w64 RGv. Proof. reflexivity. Qed.
Lemma EqNF : ew E0 35 = w64 nf. Proof. reflexivity. Qed.
Lemma EqJ80 : ew E0 36 = w64 j80. Proof. reflexivity. Qed.
Lemma EqJ88 : ew E0 37 = w64 j88. Proof. reflexivity. Qed.
Definition R_RGO : YP09.region :=
YP09.mkRegion (Some 34%nat) 0 128 0 0
[YP09.mkChunk 16 (CVal 8 (SOff 35%nat 0)); YP09.mkChunk 80 (CVal 8 (SOff 36%nat 0)); YP09.mkChunk 88 (CVal 8 (SOff 37%nat 0))].
Definition REG0 : smem :=
[ YP09.mkRegion (Some 2%nat) (- 80) 0 (- 80) 0 []; R_RGO;
fatom8 (A_ALLOCATOR + 48) 32%nat  ; flit4 (A_ALLOCATOR + 40) 4294967295  ;
flit8 0x9df78 0x135aa0; flit8 0x135aa0 4096   ].
Definition FFO : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + 80) kHighMemEnd 4);
(32%nat, mkAF kHighMemBeg (CEIL_MAX - 4096) 12);
(33%nat, mkAF 1 30 0);
(34%nat, mkAF kHighMemBeg (CEIL_MAX - 128) 7);
(35%nat, mkAF 0 (2 ^ 64 - 1) 0);
(36%nat, mkAF 0 (2 ^ 64 - 1) 0);
(37%nat, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set sr_atoms 10%bv (SLit A_ALLOCATOR)) 12%bv (SOff 33%nat 0)) 13%bv (SLit 0).
Definition SS0 : sstate := mkSS 0x34350 SR0 REG0 None FFO.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x34350) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_Hra : YK0s.ret_ok (getr regs0 1);
fh_Hsp : kHighMemBeg + 80 <= sp0 /\ sp0 <= kHighMemEnd;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 - 80 <= a < sp0 -> apresent (w_H W) mem0 a;
fh_Hc : 1 <= c <= 30;
fh_Hri : kHighMemBeg <= ri /\ ri + 4096 <= ASAN_CEIL /\ ri mod 4096 = 0;
fh_vals : 0 <= nf < 2 ^ 64 /\ 0 <= j80 < 2 ^ 64 /\ 0 <= j88 < 2 ^ 64;
fh_disj : sp0 <= RGv \/ RGv + 128 <= sp0 - 80;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x34350) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH :=
pose proof (fh_Hra FH) as Hra;
pose proof (fh_Hsp FH) as Hsp;
pose proof (fh_Hsp_al FH) as Hsp_al;
pose proof (fh_pres FH) as Hpres;
pose proof (fh_Hc FH) as Hc;
pose proof (fh_Hri FH) as Hri;
pose proof (fh_vals FH) as Hvals;
pose proof (fh_disj FH) as Hdisj;
pose proof (fh_SEED FH) as SEED.
Lemma derived_ranges :
kHighMemBeg + 80 <= sp0 /\ sp0 <= kHighMemEnd /\ kHighMemBeg <= ri /\ ri + 4096 <= ASAN_CEIL /\
RGv = ri + 128 * c /\ ri + 128 <= RGv /\ RGv + 128 <= ri + 4096 /\ 1 <= c <= 30 /\
0 <= nf < 2 ^ 64 /\ 0 <= j80 < 2 ^ 64 /\ 0 <= j88 < 2 ^ 64.
Proof. open_FH. unfold RGv in *. numconst. repeat split; lia. Qed.
Definition WIN (a : Z) : Prop := sp0 - 80 <= a < sp0.
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
Definition WSK0 : list (option nat * Z * Z) := [(Some 2%nat, -80, 0)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN. unfold aHAVf in *.
destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr. rewrite HE in Hr by (cbv; lia). rewrite E2 in Hr. unfold sp0 in *. lia.
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
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> m x = mem0 x.
Lemma MEQ_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQ m -> MEQ m'.
Proof. intros E SK rs m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WIN E SK rs _ HSK Hb Hw). Qed.
Lemma MEQ_0 : MEQ mem0. Proof. intros x _. reflexivity. Qed.
Definition at_RETO : world tfibsegs -> config -> Prop :=
call_post W (mkst regs0 (w64 0x34350) mem0 (seg_rom tfibsegs)) md0 WIN.
End e.
End d.
