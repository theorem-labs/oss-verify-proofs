(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_stage2_defs Sj_tables Sj_stage2_auto2 Sj_stage2_entry.
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

Section RootAtom.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).

  Ltac ra_docend KD tw :=
    match goal with TI : tape_img _ _ _ _, NW : bytes_at _ _ _ (le8 _) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      eapply (tape_img_app1 E _ _ m (tword tw 0) _ OK) in TI;
      [ | exact NW | lia | lia | vm_compute; split; [discriminate | reflexivity] ] end;
    eapply KD; cbn [k W];
    eapply (MEMI_forget8 _ _ [_;_;_;_;_;_;_;_] _ [_]); cycle 1; [s2_close_mem0 | reflexivity].
  Ltac ra_exit KX := s2_err_exit KX; eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].

  Ltac ra_intro :=
    intros Q GLT KX KD; unfold rootprim_k;
    intros xra xt0 xt1 xt2 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j1 j2 j3 j4 j5 j9 F fc m1 HM;
    pose proof (ok_bytes _ OK) as BOK;
    pose proof (n_bound E OK) as HN;
    pose proof (off_bound E OK 0 ltac:(lia)) as HO;
    pose proof (off_range _ _ (ok_s1 _ OK) 0 ltac:(lia)) as HOR;
    pose proof (B_range bs (e_off E 0 + 4) BOK) as HB4; pose proof (B_range bs (e_off E 0 + 5) BOK) as HB5;
    s2_env OK;
    s2_open_mem HM;
    lazymatch goal with MIh : mem_inv psegs ?m |- _ =>
      pose proof (sown_read m (B bs (e_off E 0 + 4)) MIh HB4) as RS4; unfold T_SOWN in RS4;
      pose proof (sown_read m (B bs (e_off E 0 + 5)) MIh HB5) as RS5; unfold T_SOWN in RS5 end;
    pose proof (sown_range (B bs (e_off E 0 + 4))) as HS4; pose proof (sown_range (B bs (e_off E 0 + 5))) as HS5.

  Lemma seg_root_null : forall (Q : machine_state -> Prop),
    Z.of_nat (length (e_tws E)) = 1%Z -> exit_k E Q -> docend_k (gapp E [tword t_null 0] []) Q (mkst 1 0 2 0 []) -> rootprim_k E Q 0x3e694.
  Proof using OK.
    ra_intro.
    do 4 sstep.
    if_cases K; zify_cond K.
    - do 3 sstep.
      if_cases K1; zify_cond K1.
      + do 13 sstep.
        if_cases K2; zify_cond K2.
        * do 7 sstep. ra_docend KD t_null.
        * sstep. ra_exit KX.
      + sstep. ra_exit KX.
    - do 19 sstep.
      if_cases K2; zify_cond K2.
      + do 2 sstep. ra_exit KX.
      + do 8 sstep. ra_docend KD t_null.
  Qed.

  Lemma seg_root_true : forall (Q : machine_state -> Prop),
    Z.of_nat (length (e_tws E)) = 1%Z -> exit_k E Q -> docend_k (gapp E [tword t_true 0] []) Q (mkst 1 0 2 0 []) -> rootprim_k E Q 0x3e754.
  Proof using OK.
    ra_intro.
    do 4 sstep.
    if_cases K; zify_cond K.
    - do 3 sstep.
      if_cases K1; zify_cond K1.
      + do 13 sstep.
        if_cases K2; zify_cond K2.
        * do 7 sstep. ra_docend KD t_true.
        * sstep. ra_exit KX.
      + sstep. ra_exit KX.
    - do 19 sstep.
      if_cases K2; zify_cond K2.
      + do 2 sstep. ra_exit KX.
      + do 8 sstep. ra_docend KD t_true.
  Qed.

  Lemma seg_root_false : forall (Q : machine_state -> Prop),
    Z.of_nat (length (e_tws E)) = 1%Z -> exit_k E Q -> docend_k (gapp E [tword t_false 0] []) Q (mkst 1 0 2 0 []) -> rootprim_k E Q 0x3ec9c.
  Proof using OK.
    ra_intro.
    do 4 sstep.
    if_cases K; zify_cond K.
    - do 3 sstep.
      if_cases K1; zify_cond K1.
      + do 13 sstep.
        if_cases K2; zify_cond K2.
        * do 6 sstep. ra_docend KD t_false.
        * sstep. ra_exit KX.
      + sstep. ra_exit KX.
    - do 20 sstep.
      if_cases K2; zify_cond K2.
      + do 2 sstep. ra_exit KX.
      + do 7 sstep. ra_docend KD t_false.
  Qed.
End RootAtom.
