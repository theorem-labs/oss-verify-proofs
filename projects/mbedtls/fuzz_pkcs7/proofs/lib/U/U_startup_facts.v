(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (D_main_cells, range_disjoint_djw, D_main_miss and D_main_self written out in plain text, the cell table as explicit addresses, and the CDefT table removed; the Facts section restated over one ProcInput, hwcap read from it; main_entry_rdn_image, main_entry_tid and main_entry_guard moved to a new MEFacts section and reproved through main_entry_launch; import of MemSplit). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb StartupTac ArgvEnv Layout MemSplit.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_startup_defs U_startup.
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Definition D_main_cells : list (Z * nat) := [(0x5cff8, 8%nat); (0x7d358, 8%nat); (0x7d3b8, 8%nat); (0x7d380, 8%nat); (0x7d348, 8%nat); (0x7d340, 8%nat); (0x7d0f0, 8%nat); (0x7d100, 8%nat); (0x7d0f8, 8%nat); (0x7d368, 8%nat); (0x7d370, 8%nat); (0x5d0d8, 8%nat); (0x5d0c0, 8%nat); (0x5d000, 8%nat); (0x7d350, 1%nat); (0x5d028, 4%nat); (0x5d020, 4%nat); (0x5d098, 8%nat); (0x5d078, 8%nat); (0x5d008, 8%nat); (0x5d010, 8%nat); (0x5d018, 8%nat); (0x7d330, 4%nat); (0x7d334, 4%nat); (0x7d331, 1%nat); (0x5d0b8, 8%nat); (0x4cf20, 1%nat)]%Z.

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x7e000)%Z.

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
    rdn segs D (Z_to_bv 64 0x5d020) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0x7d330) 8 = Some (canary_bytes rd).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply guard_read.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva"] Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x7d380) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  #[using="Type"] Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x5d000) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5d000)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0x5d0b8) 8 = Some (word_to_le_bytes 8 (canary_w rd)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  #[using="Hva"] Lemma D_main_hwcap : forall segs,
    rdn segs D (Z_to_bv 64 0x7d3b8) 8 = Some (word_to_le_bytes 8 (in_hwcap inp)).
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
    assert (Hr : (0 <= a /\ a + Z.of_nat n <= 0x7e000)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    destruct (main_entry_launch sp0 av ev tid rd regs mem ME) as (inp & mbase & brk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RD).
    rewrite RD by (rewrite stack_max_size_val; unorm; lia).
    eapply D_main_miss. exact Hb.
  Qed.

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x5d020) 4 = Some (word_to_le_bytes 4 tid).
  Proof using Hlo ME.
    intros segs.
    destruct (main_entry_launch sp0 av ev tid rd regs mem ME) as (inp & mbase & brk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RD).
    rewrite RD by (rewrite stack_max_size_val; unorm; lia). eapply D_main_tid.
  Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0x7d330) 8 = Some (canary_bytes rd).
  Proof using Hlo ME.
    intros segs.
    destruct (main_entry_launch sp0 av ev tid rd regs mem ME) as (inp & mbase & brk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RD).
    rewrite RD by (rewrite stack_max_size_val; unorm; lia). eapply D_main_guard.
  Qed.
End MEFacts.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
