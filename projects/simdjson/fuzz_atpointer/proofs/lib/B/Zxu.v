(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q FP ImageA.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa SjTape Zpj Zpk Zp9.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Zpm Zwd Z103 Z104 Zwk Z107 Zwm Zxc Zxd Zxe
  Zxx Zxy Zy0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | s2_load_sown | s2_load_pow | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac g_store_hook ::= s2_note_tape.

Section NumO7.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).
  Notation o s := (e_off E (k s)).

  Lemma seg_numo_slowret : forall (Q : machine_state -> Prop) (s : st) r v,
    (r = 9 \/ r = 0)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q -> (forall vw rw, num_word vw -> numo_fin_k (gapp E [vw; rw] []) Q s) ->
    numo_slowret_k E Q s r v.
  Proof using OK SHZ.
    intros Q s r v HR HW0 HW GLT KX KF. unfold numo_slowret_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    destruct HR as [-> | ->].
    - ngrun_to 0xacd28%Z. nstep. gdec. ngrun_to 0xacc2c%Z. nstep. gdec. nexit KX.
    - ngrun_to 0xacd28%Z. nstep. gdec. n_tape2. s2_kvr_kapply KF. nclose.
  Qed.

  Lemma seg_numo_fbret : forall (Q : machine_state -> Prop) (s : st) r v,
    (r = 0 \/ r = 1)%Z -> exit_k E Q -> numo_write_k E Q s 0 ->
    numo_fbret_k E Q s r v.
  Proof using OK SHZ.
    intros Q s r v HR KX KW. unfold numo_fbret_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    destruct HR as [-> | ->].
    - ngrun_to 0xacfd4%Z. nstep. gdec. ngrun_to 0xacd28%Z. nstep. gdec. ngrun_to 0xacc2c%Z. nstep. gdec. nexit KX.
    - ngrun_to 0xacfd4%Z. nstep. gdec. kapply KW. nclose.
  Qed.
End NumO7.
