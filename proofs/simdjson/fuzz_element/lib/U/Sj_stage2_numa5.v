(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit3 Sj_stage2_numa_defs Sj_stage2_numa_defs2 Sj_stage2_numa_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_note_tape; s2_store_done_wr_v2.

Local Ltac nnorm ::=
  s2norm;
  repeat match goal with
  | |- context [Z.land (Z.modulo ?x 18446744073709551616) 255] => rewrite (land255_mod x)
  | |- context [Z.land (B ?bs ?i) 255] => rewrite (land255_small (B bs i)) by lia
  | |- context [Z.land ?x 255] => rewrite (land255_any x)
  end.

Section NumA5.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Notation o s := (e_off E (k s)).

  Ltac n_close := unfold NSL; s2_close_mem0.
  Local Ltac n_closed_branch a b ::= lazymatch a with 0x48e00%Z => if_false | 0x48e58%Z => first [if_true | if_false] end.

  Lemma seg_numa_flt : forall (Q : machine_state -> Prop) (s : st) neg x,
    (0 <= x < 2^64)%Z -> (0 <= neg <= 1)%Z -> (0 <= k s <= e_n E)%Z -> (o s + neg < e_len E)%Z ->
    numa_tail_k E Q s neg 0x4880c -> numa_tailm_k E Q s neg 0x48cbc ->
    numa_flt_k E Q s neg x.
  Proof using OK.
    intros Q s neg x HX HNEG HK HS Kac0 Kf70. unfold numa_flt_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    pose proof (B_range bs (o s + neg) BOK) as HB0.
    assert (HXM : (0 <= x mod 256 < 256)%Z) by (apply Z.mod_pos_bound; lia).
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0.
    - eapply Kac0. n_close.
    - ngrun.
      if_cases K1; zify_cond K1.
      +
        ngrun.
        if_cases K2; zify_cond K2.
        * ngrun_to 0x487e8%Z.
          eapply (numa_L6 E OK Q (S (Z.to_nat (e_len E))) (o s + neg)%Z); [exact BUFRO | lia | lia |].
          intros ya4 yt2 yt0. ngrun. if_cases K9; [eapply Kf70 | eapply Kac0]; n_close.
        * ngrun. if_cases K9; [eapply Kf70 | eapply Kac0]; n_close.
      + ngrun_to 0x487e8%Z.
        eapply (numa_L6 E OK Q (S (Z.to_nat (e_len E))) (o s + neg)%Z); [exact BUFRO | lia | lia |].
        intros ya4 yt2 yt0. ngrun. if_cases K9; [eapply Kf70 | eapply Kac0]; n_close.
  Qed.

  Ltac fin5 sv KX KC :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0x4ed1c%Z => s2_tape2; s2_kvr KC; [s2_num_word|]; cbn [k depth W sb scopes];
                     repeat match goal with H : rw_cells _ _ _ _ |- _ =>
                       progress (replace (e_TAPE E + 8 * W sv + 16)%Z with (e_TAPE E + 8 * (W sv + 2))%Z in H by lia) end;
                     s2_close_mem0
      | 0x4bfd0%Z =>
          eapply KX; [s2_errok_code | s2_close_memx]
      end end.
  Ltac cuts5 pc := lazymatch pc with 0x4ed1c%Z => fail | 0x4bfd0%Z => fail | _ => idtac end.

  Lemma seg_numa_wr34 : forall (Q : machine_state -> Prop) (s : st) neg,
    (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (forall v r, num_word v -> arrcont_k (gapp E [v; r] []) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    numa_tail_k E Q s neg 0x48d80.
  Proof using OK.
    intros Q s neg HW0 HW GLT KX KC. unfold numa_tail_k. intros until m1. intros HM.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    ngexp cuts5 ltac:(idtac; fin5 s KX KC).
  Qed.

  Lemma seg_numa_wr30 : forall (Q : machine_state -> Prop) (s : st) neg,
    (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (forall v r, num_word v -> arrcont_k (gapp E [v; r] []) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    numa_tailm_k E Q s neg 0x48d7c.
  Proof using OK.
    intros Q s neg HW0 HW GLT KX KC. unfold numa_tailm_k. intros until m1. intros HM.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    ngexp cuts5 ltac:(idtac; fin5 s KX KC).
  Qed.
End NumA5.
