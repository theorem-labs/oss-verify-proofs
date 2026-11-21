(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import
  StartupTac ArgvEnv RefLayout DrawDefs S7StartupDefs S7Startup.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RPH := Src_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs.

Definition D_main_cells : list (Z * nat) :=
  [(0x72eb0%Z, 8%nat); (0x93210%Z, 8%nat); (0x93270%Z, 8%nat); (0x93238%Z, 8%nat); (0x93200%Z, 8%nat); (0x931f8%Z, 8%nat); (0x92fa8%Z, 8%nat); (0x92fb8%Z, 8%nat); (0x92fb0%Z, 8%nat); (0x93220%Z, 8%nat); (0x93228%Z, 8%nat); (0x72f90%Z, 8%nat); (0x72f78%Z, 8%nat); (0x72eb8%Z, 8%nat); (0x93208%Z, 1%nat); (0x72ee0%Z, 4%nat); (0x72ed8%Z, 4%nat); (0x72f50%Z, 8%nat); (0x72f30%Z, 8%nat); (0x72ec0%Z, 8%nat); (0x72ec8%Z, 8%nat); (0x72ed0%Z, 8%nat); (0x931e8%Z, 4%nat); (0x931ec%Z, 4%nat); (0x931e9%Z, 1%nat); (0x72f70%Z, 8%nat); (0x22e30%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x94000)%Z.

Definition djw (P : Prop) : Prop := P.

Lemma range_disjoint_djw : forall a n c,
  range_disjoint_b a n c = true ->
  djw (a + Z.of_nat n <= fst c \/ fst c + Z.of_nat (snd c) <= a)%Z.
Proof.
  intros a n [c l] H. unfold range_disjoint_b in H. cbn [fst snd] in *.
  apply orb_true_iff in H. unfold djw. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Section Facts.
  Variable sp0 : word.
  (* the launch input; av / hw are notations of it. *)
  Variable inp : ProcInput.
  Variable mbase : word.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Let D := D_main sp0 inp rdraw tid.

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma D_main_miss : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs (D_main sp0 inp rdraw tid) (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
  Proof.
    intros segs a n Hb. pose proof (u64_range tid). pose proof (u64_range hw).
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

  Lemma D_main_tid : forall segs,
    rdn segs D (Z_to_bv 64 0x72ed8) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0x931e8) 8 = Some (canary_bytes rdraw).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_guard; [reflexivity | reflexivity | lia | lia].
  Qed.

  Lemma D_main_guard_w : forall segs,
    rdn segs D (Z_to_bv 64 0x931e8) 8 = Some (word_to_le_bytes 8 (canary_w rdraw)).
  Proof. intros segs. rewrite w8_canary. apply D_main_guard. Qed.

  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x93238) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.


  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x72eb8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x72eb8)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0x72f70) 8 = Some (word_to_le_bytes 8 (canary_w rdraw)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.


  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs mem.


  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x72ed8) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 inp mbase rdraw tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
