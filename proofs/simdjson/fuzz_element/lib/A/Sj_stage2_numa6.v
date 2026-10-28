(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit
  Sj_stage2_numkit2 Sj_stage2_numa_defs Sj_stage2_numa_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= lia0.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac g_store_hook ::= s2_note_tape.

Lemma land9_range : forall x, (0 <= Z.land x 9 < 64)%Z.
Proof.
  intros x. assert (E : Z.land (Z.land x 9) (Z.ones 4) = Z.land x 9) by (rewrite <- Z.land_assoc; reflexivity).
  rewrite Z.land_ones in E by lia. pose proof (Z.mod_pos_bound (Z.land x 9) (2 ^ 4) ltac:(lia)). lia.
Qed.

Section NumA6.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).
  Notation o s := (e_off E (k s)).

  Lemma seg_numa_join : forall (Q : machine_state -> Prop) (s : st),
    arrcont_k E Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s)) -> numa_join_k E Q s.
  Proof using OK SHZ.
    intros Q s KC. unfold numa_join_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    ngrun.
    first [ if_true | idtac ].
    ngrun_to 0xcf560%Z.
    kapply KC. cbn [scopes k depth W sb]. nclose.
  Qed.

  Lemma seg_numa_fin : forall (Q : machine_state -> Prop) (s : st) neg r,
    (r = 0 \/ r = 9)%Z -> exit_k E Q -> numa_join_k E Q s -> numa_fin_k E Q s neg r.
  Proof using OK SHZ.
    intros Q s neg r HR KX KJ. unfold numa_fin_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    destruct HR as [-> | ->].
    - ngrun. first [ if_true | idtac ].
      ngrun.
      if_cases K1.
      + kapply KJ. nclose.
      + ngrun_to 0xcb1dc%Z.
        lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
          let v := greg_val R 23%Z in lazymatch v with Z_to_bv 64 ?ev => eapply (KX ev); [s2_errok_code | s2_close_memx] end end.
    - repeat (ngrun_to 0xcb1dc%Z; gdec).
      nexit KX.
  Qed.

  Lemma seg_numa_write : forall (Q : machine_state -> Prop) (s : st) neg,
    (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> (forall v r, num_word v -> numa_fin_k (gapp E [v; r] []) Q s neg 0) -> numa_write_k E Q s neg.
  Proof using OK SHZ.
    intros Q s neg HW0 HW GLT KF. unfold numa_write_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    ngrun_to 0xc73ec%Z.
    n_tape2. s2_kvr_kapply KF. nclose.
  Qed.

End NumA6.
