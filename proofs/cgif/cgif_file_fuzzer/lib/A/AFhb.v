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
Definition YFRAME : Z := 112.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD,
A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax, YFRAME in *.
Definition qSZ : nat := 46.
Definition qRA : nat := 50.  Definition qS0 : nat := 51.  Definition qS1 : nat := 52.  Definition qS2 : nat := 53.  Definition qS3 : nat := 54.
Definition qS4 : nat := 55.  Definition qS5 : nat := 56.  Definition qS6 : nat := 57.  Definition qS7 : nat := 58.  Definition qS8 : nat := 59.
Definition qS9 : nat := 60.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let m0 := mrestrict (w_H W) mem0.
Definition XW : list word :=
[ w64 0; w64 0; w64 0; w64 0; w64 0; w64 0; w64 0; w64 0; w64 0; w64 0; w64 0; w64 0; w64 0; w64 0; w64 sz; w64 0; w64 0; w64 0;
w64 vra; w64 vs0; w64 vs1; w64 vs2; w64 vs3; w64 vs4; w64 vs5; w64 vs6; w64 vs7; w64 vs8; w64 vs9 ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma EqSZ : ew E0 46 = w64 sz. Proof. reflexivity. Qed.
Lemma EqRA : ew E0 50 = w64 vra. Proof. reflexivity. Qed.
Lemma EqS0 : ew E0 51 = w64 vs0. Proof. reflexivity. Qed.
Lemma EqS1 : ew E0 52 = w64 vs1. Proof. reflexivity. Qed.
Lemma EqS2 : ew E0 53 = w64 vs2. Proof. reflexivity. Qed.
Lemma EqS3 : ew E0 54 = w64 vs3. Proof. reflexivity. Qed.
Lemma EqS4 : ew E0 55 = w64 vs4. Proof. reflexivity. Qed.
Lemma EqS5 : ew E0 56 = w64 vs5. Proof. reflexivity. Qed.
Lemma EqS6 : ew E0 57 = w64 vs6. Proof. reflexivity. Qed.
Lemma EqS7 : ew E0 58 = w64 vs7. Proof. reflexivity. Qed.
Lemma EqS8 : ew E0 59 = w64 vs8. Proof. reflexivity. Qed.
Lemma EqS9 : ew E0 60 = w64 vs9. Proof. reflexivity. Qed.
Definition R_STK : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 (YFRAME + 32) 0 0
[YP09.mkChunk 112 (CVal 8 (SOff 46%nat 0));
YP09.mkChunk 104 (CVal 8 (SOff 50%nat 0)); YP09.mkChunk 96 (CVal 8 (SOff 51%nat 0)); YP09.mkChunk 88 (CVal 8 (SOff 52%nat 0));
YP09.mkChunk 80 (CVal 8 (SOff 53%nat 0)); YP09.mkChunk 72 (CVal 8 (SOff 54%nat 0)); YP09.mkChunk 64 (CVal 8 (SOff 55%nat 0));
YP09.mkChunk 56 (CVal 8 (SOff 56%nat 0)); YP09.mkChunk 48 (CVal 8 (SOff 57%nat 0)); YP09.mkChunk 40 (CVal 8 (SOff 58%nat 0));
YP09.mkChunk 32 (CVal 8 (SOff 59%nat 0)); YP09.mkChunk 24 (CVal 8 (SOff 60%nat 0))].
Definition REG0 : smem := [ R_STK ].
Definition FFQ : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + DRSTACK - YFRAME) (kHighMemEnd - YFRAME - 32) 4);
(46%nat, mkAF 0 (2 ^ 40) 0);
(50%nat, mkAF 0 (2 ^ 64 - 1) 0); (51%nat, mkAF 0 (2 ^ 64 - 1) 0); (52%nat, mkAF 0 (2 ^ 64 - 1) 0); (53%nat, mkAF 0 (2 ^ 64 - 1) 0);
(54%nat, mkAF 0 (2 ^ 64 - 1) 0); (55%nat, mkAF 0 (2 ^ 64 - 1) 0); (56%nat, mkAF 0 (2 ^ 64 - 1) 0); (57%nat, mkAF 0 (2 ^ 64 - 1) 0);
(58%nat, mkAF 0 (2 ^ 64 - 1) 0); (59%nat, mkAF 0 (2 ^ 64 - 1) 0); (60%nat, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
4%bv (SLit TFIB_TP)) 8%bv (SOff 2%nat YFRAME)) 9%bv (SLit A_ALLOCATOR)) 18%bv (SLit (A_ALLOCATOR + 64))) 19%bv (SLit (A_ALLOCATOR + 688)))
21%bv (SLit (2 ^ 37)).
Definition SS0 : sstate := mkSS 0x33530 SR0 REG0 None FFQ.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33530) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_Htp : getr regs0 4 = w64 TFIB_TP;
fh_Hsp : ly_stk_lo ly + DRSTACK <= sp0 + YFRAME /\ sp0 + YFRAME + 32 <= ly_stk_hi ly;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 <= a < sp0 + YFRAME + 32 -> apresent (w_H W) mem0 a;
fh_regs : getr regs0 8 = w64 (sp0 + YFRAME) /\ getr regs0 9 = w64 A_ALLOCATOR /\ getr regs0 18 = w64 (A_ALLOCATOR + 64) /\
getr regs0 19 = w64 (A_ALLOCATOR + 688) /\ getr regs0 21 = w64 (2 ^ 37);
fh_Hra : YK0s.ret_ok (w64 vra);
fh_Hsz : 0 <= sz < 2 ^ 40;
fh_vals : 0 <= vra < 2 ^ 64 /\ 0 <= vs0 < 2 ^ 64 /\ 0 <= vs1 < 2 ^ 64 /\ 0 <= vs2 < 2 ^ 64 /\ 0 <= vs3 < 2 ^ 64 /\ 0 <= vs4 < 2 ^ 64 /\
0 <= vs5 < 2 ^ 64 /\ 0 <= vs6 < 2 ^ 64 /\ 0 <= vs7 < 2 ^ 64 /\ 0 <= vs8 < 2 ^ 64 /\ 0 <= vs9 < 2 ^ 64;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x33530) mem0 (seg_rom tfibsegs)))
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
pose proof (fh_Hra FH) as Hra;
pose proof (fh_Hsz FH) as Hsz;
pose proof (fh_vals FH) as Hvals;
pose proof (fh_SEED FH) as SEED.
Lemma LYB : ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly.
Proof.
open_FH. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). split; [exact T4 | exact T7].
Qed.
Lemma derived_ranges : kHighMemBeg + DRSTACK - YFRAME <= sp0 /\ sp0 + YFRAME + 32 <= kHighMemEnd /\ 0 <= sz < 2 ^ 40.
Proof. open_FH. pose proof LYB as LB. destruct Hsp as [S1 S2]. clear - LB S1 S2 Hsz. numconst. repeat split; lia. Qed.
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
Lemma MEQ_all : forall m, MEQ m -> forall x, m x = mem0 x.
Proof. intros m HM x. apply HM. intros []. Qed.
Definition SREGS : list (bv 5) := [3; 4; 8; 9; 18; 19; 21; 26; 27]%bv.
Definition at_O (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ sz <> 0 /\ exists regs' mat,
c' = mkCfg (mkst regs' (w64 0x334ac) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\ getr regs' 10 = w64 sz.
Definition SREGS_X : list (bv 5) := [3; 4; 26; 27]%bv.
Definition at_RETQ (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ sz = 0 /\ exists regs' mat,
c' = mkCfg (mkst regs' (w64 vra) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = w64 (sp0 + YFRAME) /\ getr regs' 1 = w64 vra /\
getr regs' 8 = w64 vs0 /\ getr regs' 9 = w64 vs1 /\ getr regs' 18 = w64 vs2 /\ getr regs' 19 = w64 vs3 /\ getr regs' 20 = w64 vs4 /\
getr regs' 21 = w64 vs5 /\ getr regs' 22 = w64 vs6 /\ getr regs' 23 = w64 vs7 /\ getr regs' 24 = w64 vs8 /\ getr regs' 25 = w64 vs9 /\
(forall r : bv 5, In r SREGS_X -> getr regs' r = getr regs0 r).
Definition postQ : world tfibsegs -> config -> Prop := if sz =? 0 then at_RETQ else at_O.
End c.
End b.
