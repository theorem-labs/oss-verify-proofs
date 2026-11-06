(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_auto Sj_stage2_auto2
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numa_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_note_tape; s2_store_done_wr_v2.

Section NumA7.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).

  Ltac n_close := unfold NSL; s2_close_mem0.
  Ltac cuts7 pc := lazymatch pc with 0x44e6c%Z => fail | 0x44e70%Z => fail | 0x44f74%Z => fail | 0x404dc%Z => fail | 0x44f8c%Z => fail | _ => idtac end.
  Ltac fin7 sv KX KJ KW KFB :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0x44e6c%Z => eapply KW; n_close
      | 0x44f8c%Z => eapply KFB; n_close
      | 0x44f74%Z => replace (e_TAPE E + 8 * W sv + 16)%Z with (e_TAPE E + 8 * (W sv + 2))%Z by lia; s2_tape2; s2_kvr KJ; [s2_num_word | n_close]
      | 0x404dc%Z => s2_err_exit KX; eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..]
      end end.

  Lemma seg_numa_t114 : forall (Q : machine_state -> Prop) (s : st) neg,
    (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q -> (forall v r, num_word v -> numa_join_k (gapp E [v; r] []) Q s neg) ->
    numa_tail_k E Q s neg 0x44e6c (W s) ->
    (forall e, (-342 <= e <= 308)%Z -> numa_cmp_k E Q s neg e) ->
    numa_tail_k E Q s neg 0x44b18 (W s).
  Proof using OK.
    intros Q s neg HW0 HW GLT KX KJ KW KC. unfold numa_tail_k. intros until m1. intros HM.
    destruct (word_signed_repr xt1) as (e & HE & ->).
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0; zify_cond K0.
    -
      assert (HER : (-342 <= e <= 308)%Z) by lia.
      srun.
      if_cases K1.
      + eapply (KC e HER). n_close.
      + srun.
        if_cases K2; zify_cond K2.
        * eapply (KC e HER). n_close.
        * assert (HE22 : (-22 <= e <= 22)%Z) by lia.
          srun.
          if_cases K3; zify_cond K3.
          --
             srun.
             destruct (pow_tab_read m1 (8 * - e) (Z_to_bv 64 (84368 - (8 * (e mod 18446744073709551616)) mod 18446744073709551616))
                         ltac:(lia) ltac:(lia) ltac:(unfold wa, T_POW; apply wz_eq_mod; lia)) as [w RD].
             nexp cuts7 ltac:(idtac; fin7 s KX KJ KW KX).
          --
             srun.
             destruct (pow_tab_read m1 (8 * e) (Z_to_bv 64 (84368 + 8 * (e mod 18446744073709551616)))
                         ltac:(lia) ltac:(lia) ltac:(unfold wa, T_POW; apply wz_eq_mod; lia)) as [w RD].
             nexp cuts7 ltac:(idtac; fin7 s KX KJ KW KX).
    -
      nexp cuts7 ltac:(idtac; fin7 s KX KJ KW KX).
  Qed.

  Lemma seg_numa_cmp : forall (Q : machine_state -> Prop) (s : st) neg e,
    (-342 <= e <= 308)%Z ->
    numa_tail_k E Q s neg 0x44e6c (W s) -> numa_tail_k E Q s neg 0x44f8c (W s) ->
    numa_cmp_k E Q s neg e.
  Proof using OK.
    intros Q s neg e HE KW KFB. unfold numa_cmp_k. intros until m1. intros HM.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0.
    - nexp cuts7 ltac:(idtac; fin7 s KW KW KW KFB).
    - destruct (pow5_read m1 e 1376 HE ltac:(left; reflexivity)) as [w1 RD1].
      destruct (pow5_read m1 e 1384 HE ltac:(right; reflexivity)) as [w2 RD2].
      nexp_f ltac:(fun pc => lazymatch pc with 0x44c9c%Z => fail | _ => cuts7 pc end)
             ltac:(idtac; lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                     lazymatch pc with 0x44c9c%Z => nexp_f cuts7 ltac:(idtac; fin7 s KW KW KW KFB) ltac:(fun n => idtac) end end)
             ltac:(fun n => lazymatch n with 14%Z => fail | 6%Z => fail | 17%Z => fail | 5%Z => fail | _ => idtac end).
  Qed.
End NumA7.
