(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
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
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD,
A_QUAR, A_ALLOCATOR, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Definition xRA : nat := 32.  Definition xS0 : nat := 33.  Definition xS1 : nat := 34.  Definition xS2 : nat := 35.  Definition xS3 : nat := 36.  Definition xS4 : nat := 37.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (vra vs0 vs1 vs2 vs3 vs4 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let m0 := mrestrict (w_H W) mem0.
Definition XW : list word := [ w64 vra; w64 vs0; w64 vs1; w64 vs2; w64 vs3; w64 vs4 ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma EqRA : ew E0 32 = w64 vra. Proof. reflexivity. Qed.
Lemma EqS0 : ew E0 33 = w64 vs0. Proof. reflexivity. Qed.
Lemma EqS1 : ew E0 34 = w64 vs1. Proof. reflexivity. Qed.
Lemma EqS2 : ew E0 35 = w64 vs2. Proof. reflexivity. Qed.
Lemma EqS3 : ew E0 36 = w64 vs3. Proof. reflexivity. Qed.
Lemma EqS4 : ew E0 37 = w64 vs4. Proof. reflexivity. Qed.
Definition R_STK : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 LFRAME 0 0
[YP09.mkChunk 72 (CVal 8 (SOff 32%nat 0)); YP09.mkChunk 64 (CVal 8 (SOff 33%nat 0)); YP09.mkChunk 56 (CVal 8 (SOff 34%nat 0));
YP09.mkChunk 48 (CVal 8 (SOff 35%nat 0)); YP09.mkChunk 40 (CVal 8 (SOff 36%nat 0)); YP09.mkChunk 32 (CVal 8 (SOff 37%nat 0))].
Definition REG0 : smem := [ R_STK ].
Definition FFX : facts := mkFacts
[ (2%nat, mkAF kHighMemBeg (kHighMemEnd - LFRAME) 4);
(32%nat, mkAF 0 (2 ^ 64 - 1) 0);
(33%nat, mkAF 0 (2 ^ 64 - 1) 0); (34%nat, mkAF 0 (2 ^ 64 - 1) 0); (35%nat, mkAF 0 (2 ^ 64 - 1) 0);
(36%nat, mkAF 0 (2 ^ 64 - 1) 0); (37%nat, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition SR0 : list sv := sr_set sr_atoms 4%bv (SLit TFIB_TP).
Definition SS0 : sstate := mkSS 0x3323c SR0 REG0 None FFX.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x3323c) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_Htp : getr regs0 4 = w64 TFIB_TP;
fh_Hra : YK0s.ret_ok (w64 vra);
fh_Hsp : kHighMemBeg <= sp0 /\ sp0 + LFRAME <= kHighMemEnd;
fh_Hsp_al : sp0 mod 16 = 0;
fh_vals : 0 <= vra < 2 ^ 64 /\ 0 <= vs0 < 2 ^ 64 /\ 0 <= vs1 < 2 ^ 64 /\ 0 <= vs2 < 2 ^ 64 /\ 0 <= vs3 < 2 ^ 64 /\ 0 <= vs4 < 2 ^ 64;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x3323c) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH :=
pose proof (fh_Htp FH) as Htp;
pose proof (fh_Hra FH) as Hra;
pose proof (fh_Hsp FH) as Hsp;
pose proof (fh_Hsp_al FH) as Hsp_al;
pose proof (fh_vals FH) as Hvals;
pose proof (fh_SEED FH) as SEED.
Definition WIN (a : Z) : Prop := False.
Definition win_sub (t w : option nat * Z * Z) : bool :=
obase_eqb (fst (fst t)) (fst (fst w)) && (snd (fst w) <=? snd (fst t)) && (snd t <=? snd w).
Definition WSK0 : list (option nat * Z * Z) := [].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, sk_ok E WSK0.
Proof. intros E t a Hin _. destruct Hin. Qed.
Lemma windows_WIN : forall (E : env) SK rs a,
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
intros E SK rs a HSK Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b0 & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). unfold win_sub in Hsub. exact (HSK t a Hint ltac:(destruct t as [[bt lt] ht]; cbn [fst snd] in *;
apply andb_prop in Hsub as [Hs H3]; apply andb_prop in Hs as [H1 H2]; apply Z.leb_le in H2; apply Z.leb_le in H3;
destruct bt, b0; cbn in H1; try discriminate; [apply Nat.eqb_eq in H1; subst; lia | lia])).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> m x = mem0 x.
Lemma MEQ_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQ m -> MEQ m'.
Proof. intros E SK rs m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WIN E SK rs _ HSK Hb Hw). Qed.
Lemma MEQ_0 : MEQ mem0. Proof. intros x _. reflexivity. Qed.
Lemma MEQ_all : forall m, MEQ m -> forall x, m x = mem0 x.
Proof. intros m HM x. apply HM. intros []. Qed.
Definition SREGS : list (bv 5) := [3; 4; 10; 11; 12; 13; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition at_RETX (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mat,
c' = mkCfg (mkst regs' (w64 vra) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = w64 (sp0 + LFRAME) /\ getr regs' 1 = w64 vra /\
getr regs' 8 = w64 vs0 /\ getr regs' 9 = w64 vs1 /\ getr regs' 18 = w64 vs2 /\ getr regs' 19 = w64 vs3 /\ getr regs' 20 = w64 vs4 /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r).
End c.
End b.
