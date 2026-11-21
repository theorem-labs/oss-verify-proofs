(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the run's launch class holds the entry draw, the process input, the entry stack pointer and the mmap base, with the hwcap and the other launch values as notations over them; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef), with a notation for the launch's auxv at a given stack pointer; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/P/Rnd.v, lines 7, 14-29. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import MState Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.

(* The run's launch: the entry draw, the process input, the entry stack
   pointer and the mmap base.  The stack image, the auxv and the zero window
   under [sp] are functions of these ([Run.entry_stack_image],
   [Run.launch_auxv]). *)
Class RunRnd : Type := mkRunRnd { run_draw : EntryDraw ; run_inp : ProcInput ; run_sp : word ; run_mbase : word }.

Notation run_hw := (in_hwcap run_inp).
Notation run_gid := (in_gid run_inp).
Notation run_execfn := (in_execfn run_inp).
Notation run_top := (ed_top run_draw).
Notation run_la := (launch_auxv run_inp run_sp run_mbase).
(* The launch's auxv at a given entry stack pointer: [Run.launch_auxv] reads
   [sp] (AT_SYSINFO_EHDR is the vDSO text base placed below it), and
   [Run.entry_stack_image] lays the block with the auxv at the block's own
   [sp].  A section that has its own stack pointer takes the auxv there. *)
Notation run_la_at sp := (launch_auxv run_inp sp run_mbase).

Definition run_rnd {RN__ : RunRnd} : bv 128 := ed_random run_draw.

Definition rnd_lo (r : bv 128) : word := bv_extract 0 64 r.
Definition rnd_hi (r : bv 128) : word := bv_extract 64 64 r.

Lemma Z_to_le_bytes_of_bytes : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with (2 ^ 8)%Z.
    rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
    destruct (Z.lt_ge_cases i 8).
    + rewrite Z.ones_spec_low by lia. rewrite (Z.testbit_neg_r _ (i - 8)) by lia. rewrite orb_false_r, andb_true_r. reflexivity.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
      symmetry. apply (Z.bits_above_log2 (bv_unsigned b) i); [lia|].
      destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [rewrite E; cbn; lia|].
      assert (Z.log2 (bv_unsigned b) < 8)%Z by (apply Z.log2_lt_pow2; lia). lia.
  - replace (Z.shiftr (Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) 8) with (bytes_le_to_Z bs); [exact IH|].
    apply Z.bits_inj'. intros i Hi.
    rewrite Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec by lia.
    replace (i + 8 - 8)%Z with i by lia.
    rewrite (Z.bits_above_log2 (bv_unsigned b) (i + 8)); [reflexivity|lia|].
    destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [rewrite E; cbn; lia|].
    assert (Z.log2 (bv_unsigned b) < 8)%Z by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma le8_le_bytes_to_word : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bytes_le_to_Z bs)) with ((bytes_le_to_Z bs) mod 2^64)%Z.
  rewrite (Z_to_le_bytes_mod 8 _ 64) by lia. rewrite <- L. apply Z_to_le_bytes_of_bytes.
Qed.

Definition guard_bytes (g : word) : list byte := firstn 1 (le8 g) ++ [Z_to_bv 8 0] ++ skipn 2 (le8 g).
Definition guard_of (g : word) : word := le_bytes_to_word (guard_bytes g).

Lemma guard_bytes_length : forall g, length (guard_bytes g) = 8%nat.
Proof. intros g. unfold guard_bytes. rewrite !app_length, firstn_length, skipn_length, length_le8. reflexivity. Qed.

Lemma le8_guard_of : forall g, le8 (guard_of g) = guard_bytes g.
Proof. intros g. apply le8_le_bytes_to_word, guard_bytes_length. Qed.

Section WithRnd.
  Context {RN__ : RunRnd}.

  Definition rr_guard : word := guard_of (rnd_lo run_rnd).
  Definition rr_secret : word := rnd_hi run_rnd.
End WithRnd.
