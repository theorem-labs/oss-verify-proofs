(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage2_defs Sj_tables Sj_stage2_auto2 Sj_stage2_objf.
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

Section AtomO.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).

  Lemma seg_atoms_o : forall (Q : machine_state -> Prop) (s : st),
    (0 <= k s <= e_n E)%Z -> (0 <= W s /\ W s + 1 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (forall v, atom_word v -> is_atomstart (e_tok E (k s)) = true -> lab_k (gapp E [v] []) Q 0x4a878 (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s))) ->
    objval_k E Q 0x4a0c0 s.
  Proof using OK.
    intros Q s HK HW GLT KX KC. unfold objval_k.
    intros xra xt0 xt1 xt2 xs1 xa1 xa2 xa4 xa7 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 j0 j1 j2 j3 j4 j6 j8 j9 F fc m1 HM.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (B_range bs (e_off E (k s) + 4) BOK) as HB4. pose proof (B_range bs (e_off E (k s) + 5) BOK) as HB5.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    s2_env OK.
    s2_open_mem HM.
    pose proof (sown_read m1 (B bs (e_off E (k s) + 4)) MI HB4) as RS4. unfold T_SOWN in RS4.
    pose proof (sown_read m1 (B bs (e_off E (k s) + 5)) MI HB5) as RS5. unfold T_SOWN in RS5.
    pose proof (sown_range (B bs (e_off E (k s) + 4))) as HS4. pose proof (sown_range (B bs (e_off E (k s) + 5))) as HS5.
    sstep. sstep. sstep.
    if_cases K; zify_cond K.
    -
      do 20 sstep.
      if_cases K2; zify_cond K2.
      + do 5 sstep.
        replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z by lia.
        s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_false 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
          [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]).
        eapply (KC (tword t_false 0)); [right; left; reflexivity | unfold is_atomstart; rewrite K; reflexivity | cbn [scopes]; eapply MEMJ_of_MEMI; [s2_close_mem0 | reflexivity ..]].
      + do 3 sstep. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
    - sstep. sstep.
      if_cases K1; zify_cond K1.
      +
        do 19 sstep.
        if_cases K2; zify_cond K2.
        * do 6 sstep.
          replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z by lia.
          s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_null 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
          [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]).
        eapply (KC (tword t_null 0)); [right; right; reflexivity | unfold is_atomstart; rewrite K1; reflexivity | cbn [scopes]; eapply MEMJ_of_MEMI; [s2_close_mem0 | reflexivity ..]].
        * do 3 sstep. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
      + sstep. sstep.
        if_cases K3; zify_cond K3.
        *
          do 19 sstep.
          if_cases K2; zify_cond K2.
          -- do 6 sstep.
             replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z by lia.
             s2_cur_mem ltac:(fun m => apply (tape_img_app1 E _ _ m (tword t_true 0) (e_TAPE E + 8 * W s)%Z OK) in TIMG;
          [ | exact NEWCH | lia | lia | vm_compute; split; [discriminate | reflexivity] ]).
        eapply (KC (tword t_true 0)); [left; reflexivity | unfold is_atomstart; rewrite K3; reflexivity | cbn [scopes]; eapply MEMJ_of_MEMI; [s2_close_mem0 | reflexivity ..]].
          -- do 3 sstep. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
        *
          do 3 sstep. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
  Qed.
End AtomO.
