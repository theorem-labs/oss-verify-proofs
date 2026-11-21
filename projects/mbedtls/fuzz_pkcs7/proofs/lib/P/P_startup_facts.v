(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the D_main facts restated over the process input instead of argv, envp and hwcap; the main_entry facts moved to a new section MEFacts that goes through main_entry_launch; encoded statements and the D_main_cells data decoded to plain text, with the encoding table removed; import of MemSplit). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb StartupTac ArgvEnv Layout MemSplit.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_startup_defs P_startup.
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Definition D_main_cells : list (Z * nat) := [(0x598f8, 8%nat); (0x79c58, 8%nat); (0x79cb8, 8%nat); (0x79c80, 8%nat); (0x79c48, 8%nat); (0x79c40, 8%nat); (0x799f0, 8%nat); (0x79a00, 8%nat); (0x799f8, 8%nat); (0x79c68, 8%nat); (0x79c70, 8%nat); (0x599d8, 8%nat); (0x599c0, 8%nat); (0x59900, 8%nat); (0x79c50, 1%nat); (0x59928, 4%nat); (0x59920, 4%nat); (0x59998, 8%nat); (0x59978, 8%nat); (0x59908, 8%nat); (0x59910, 8%nat); (0x59918, 8%nat); (0x79c30, 4%nat); (0x79c34, 4%nat); (0x79c31, 1%nat); (0x599b8, 8%nat); (0x49820, 1%nat)]%Z.

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x7b000)%Z.

(* [comment removed for export] *)
Definition djw (P : Prop) : Prop := P.

Lemma range_disjoint_djw : forall a n (c : Z * nat), range_disjoint_b a n c = true ->
  djw ((a + Z.of_nat n <= fst c)%Z \/ (fst c + Z.of_nat (snd c) <= a)%Z).
Proof.
  intros a n [c l] H. unfold range_disjoint_b in H. cbn [fst snd] in *.
  apply orb_true_iff in H. unfold djw. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Section Facts.
  Variable inp : ProcInput.
  Variable sp0 : word.
  Variable tid : word.
  Variable rd : EntryDraw.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Let D := D_main sp0 inp rd tid.

  #[using="Hva"] Lemma len_av : (1 <= Z.of_nat (length (in_argv inp)) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma D_main_miss : forall segs a n, D_main_missb a n = true ->
    rdn segs (D_main sp0 inp rd tid) (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
  Proof.
    intros segs a n Hb. pose proof (u64_range tid).
    unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
    repeat match goal with
           | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
           end.
    repeat match goal with
           | H : range_disjoint_b _ _ _ = true |- _ =>
               apply range_disjoint_djw in H; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ] in H
           | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
           | H : true = true |- _ => clear H
           end.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite rdn_wbytes_out by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; imm_norm; unorm;
       lazymatch goal with
       | |- (?A \/ ?B) => match goal with H : djw _ |- _ => exact H end
       | |- _ => lia
       end)).
    reflexivity.
  Qed.

  Ltac hitD :=
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc;
    pose proof len_av;
    peel; first [ apply rdn_wbytes_hit8; unorm; lia
                | match goal with |- rdn _ (wbytes _ ?a ?bs) ?a _ = _ =>
                    rewrite <- (length_N_to_le_bytes 4) at 1; apply rdn_wbytes_hit; rewrite length_N_to_le_bytes; unorm; lia end ].

  (* [comment removed for export] *)
  #[using="Type"] Lemma D_main_tid : forall segs,
    rdn segs D (Z_to_bv 64 0x59920) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0x79c30) 8 = Some (canary_bytes rd).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply guard_read.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva"] Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x79c80) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  #[using="Type"] Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x59900) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x59900)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0x599b8) 8 = Some (word_to_le_bytes 8 (canary_w rd)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  #[using="Hva"] Lemma D_main_hwcap : forall segs,
    rdn segs D (Z_to_bv 64 0x79cb8) 8 = Some (word_to_le_bytes 8 (in_hwcap inp)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  End Facts.

Section MEFacts.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev tid rd regs mem.

  Lemma main_entry_rdn_image : forall segs a n, D_main_missb a n = true ->
    rdn segs mem (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
  Proof using Hlo ME.
    intros segs a n Hb.
    assert (Hr : (0 <= a /\ a + Z.of_nat n <= 0x7b000)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    destruct (main_entry_launch sp0 av ev tid rd regs mem ME) as (inp & mbase & brk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RD).
    rewrite RD by (rewrite stack_max_size_val; unorm; lia).
    eapply D_main_miss. exact Hb.
  Qed.

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x59920) 4 = Some (word_to_le_bytes 4 tid).
  Proof using Hlo ME.
    intros segs.
    destruct (main_entry_launch sp0 av ev tid rd regs mem ME) as (inp & mbase & brk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RD).
    rewrite RD by (rewrite stack_max_size_val; unorm; lia). eapply D_main_tid.
  Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0x79c30) 8 = Some (canary_bytes rd).
  Proof using Hlo ME.
    intros segs.
    destruct (main_entry_launch sp0 av ev tid rd regs mem ME) as (inp & mbase & brk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RD).
    rewrite RD by (rewrite stack_max_size_val; unorm; lia). eapply D_main_guard.
  Qed.
End MEFacts.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
