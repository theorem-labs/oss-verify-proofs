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
  Zx7 Zx8 Zxa.
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

Section NumA6.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).
  Notation o s := (e_off E (k s)).

  Lemma seg_numa_cmpB : forall (Q : machine_state -> Prop) (s : st) neg,
    numa_write_k E Q s neg -> numa_fbcall_k E Q s ->
    numa_cmpB_k E Q s neg.
  Proof using OK SHZ.
    intros Q s neg KW KFB. unfold numa_cmpB_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    ngexp_f ltac:(fun pc => lazymatch pc with 0xaa280%Z => fail | 0xaa704%Z => fail | _ => idtac end)
            ltac:(idtac; lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                    lazymatch pc with
                    | 0xaa280%Z => ngrun_to 0xaa2e4%Z; kapply KW; nclose
                    | 0xaa704%Z => ngrun_to 0xd7204%Z; kapply KFB; nclose
                    end end)
            ltac:(nkeep ltac:(fun n => idtac)).
  Qed.

  Lemma seg_numa_write : forall (Q : machine_state -> Prop) (s : st) neg,
    (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> (forall v r, num_word v -> numa_fin_k (gapp E [v; r] []) Q s) ->
    numa_write_k E Q s neg.
  Proof using OK SHZ.
    intros Q s neg HW0 HW GLT KF. unfold numa_write_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    ngrun_to 0xaa368%Z. nstep. gdec.
    n_tape2. s2_kvr_kapply KF. nclose.
  Qed.

  Lemma seg_numa_fin : forall (Q : machine_state -> Prop) (s : st),
    exit_k E Q -> arrcont_k E Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s)) ->
    numa_fin_k E Q s.
  Proof using OK SHZ.
    intros Q s KX KC. unfold numa_fin_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    ngexp ltac:(fun pc => lazymatch pc with 0xb6f14%Z => fail | 0xb60c0%Z => fail | _ => idtac end)
          ltac:(idtac; first [ nexit0 KX | (kapply KC; nclose) ]).
  Qed.
End NumA6.
