(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_auto Sj_stage2_auto2
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numo_defs Sj_stage2_numo_loops.
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

Section NumO5.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Notation o s := (e_off E (k s)).

  Ltac n_close := unfold OSL; s2_close_mem0.
  Local Ltac n_closed_branch a b ::= lazymatch a with 0x44344%Z => if_true end.

  Lemma seg_numo_flt : forall (Q : machine_state -> Prop) (s : st) neg c,
    (0 <= c < 256)%Z -> (0 <= neg <= 1)%Z -> (0 <= k s <= e_n E)%Z -> (o s + neg < e_len E)%Z ->
    numo_tail_k E Q s neg (W s) 0x43e28 -> numo_tail_k E Q s neg (W s) 0x44160 ->
    numo_flt_k E Q s neg (W s) c.
  Proof using OK.
    intros Q s neg c HC HNEG HK HS K114 K438. unfold numo_flt_k. intros until m1. intros HM.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    s2_env OK. unfold OSL in HM.
    s2_open_mem HM.
    pose proof (sown_range c) as HSR.
    srun.
    if_cases K0.
    - eapply K114. n_close.
    - assert (TAIL : forall ya4 yt2 ya5 xa1',
        evt psegs Q (S2R E 0x43e20 xra xt0 xt1 yt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1' xa2 (Z_to_bv 64 (48)) ya4 ya5 (Z_to_bv 64 (46)) xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 (Z_to_bv 64 (sown c)) xs10 xs11 (Z_to_bv 64 (c)) xt4 xt5 xt6 F fc m1)).
      { intros ya4 yt2 ya5 xa1'. srun. if_cases K9; [eapply K438 | eapply K114]; n_close. }
      srun.
      if_cases K1.
      + srun_to 0x43e08%Z.
        replace (neg + o s + e_BUF E + 1)%Z with (e_BUF E + (o s + neg + 1))%Z by lia.
        eapply (numo_L6 E OK Q (S (Z.to_nat (e_len E)))); [exact BUFRO | lia | lia |].
        intros ya4 yt2 ya5. apply TAIL.
      + srun.
        if_cases K2.
        * srun_to 0x43e08%Z.
          replace (neg + o s + e_BUF E + 1)%Z with (e_BUF E + (o s + neg + 1))%Z by lia.
          eapply (numo_L6 E OK Q (S (Z.to_nat (e_len E)))); [exact BUFRO | lia | lia |].
          intros ya4 yt2 ya5. apply TAIL.
        * apply TAIL.
  Qed.

  Lemma seg_numo_wr : forall (Q : machine_state -> Prop) (s : st) neg,
    (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q -> (forall v r, num_word v -> numo_join_k (gapp E [v; r] []) Q s neg (W s + 2)) ->
    numo_wr_k E Q s neg (W s).
  Proof using OK.
    intros Q s neg HW0 HW GLT KX KJ. unfold numo_wr_k. intros until m1. intros HA0 HM.
    s2_env OK. unfold OSL in HM.
    s2_open_mem HM.
    nexp ltac:(fun pc => lazymatch pc with 0x442a4%Z => fail | 0x409cc%Z => fail | _ => idtac end)
         ltac:(idtac; lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                 lazymatch pc with
                 | 0x442a4%Z => replace (e_TAPE E + 8 * W s + 16)%Z with (e_TAPE E + 8 * (W s + 2))%Z in FR by lia; s2_tape2; s2_kvr KJ; [s2_num_word | n_close]
                 | 0x409cc%Z => s2_err_exit9 KX; eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..]
                 end end).
  Qed.

  Lemma seg_numo_wr0 : forall (Q : machine_state -> Prop) (s : st) neg,
    numo_wr_k E Q s neg (W s) -> numo_tail_k E Q s neg (W s) 0x44190.
  Proof using OK.
    intros Q s neg KW. unfold numo_tail_k. intros until m1. intros HM. zstep. eapply (KW 0%Z); [left; reflexivity | exact HM].
  Qed.
End NumO5.
