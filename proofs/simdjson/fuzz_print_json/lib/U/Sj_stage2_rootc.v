(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard.
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
Local Ltac g_store_hook ::= s2_note_tape.

Section RootC.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_root_obj : forall (Q : machine_state -> Prop)
      xra xt0 xt1 xt2 xs0 xs1 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    e_tok E 0 = c_lbrace ->
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_SBUF E)); C8 (Z_to_bv 64 (e_THIS E)); CB 8 j72]
         [] fc m1 ->
    Z.of_nat (length (e_tws E)) = 1%Z -> exit_k E Q ->
    (e_tok E 1 <> c_rbrace -> objbegin_k E Q (mkst 1 0 1 0 [])) ->
    (e_tok E 1 = c_rbrace -> docend_k (empty_env E 123 1) Q (mkst 2 0 3 0 [])) ->
    evt usegs Q (S2R E 0x440c8 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (3)) (Z_to_bv 64 (Z.lxor (e_IDX E) 18446744073709551615)) (Z_to_bv 64 (e_n E)) (Z_to_bv 64 (e_off E 0)) xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E 0)) (Z_to_bv 64 (e_IDX E)) xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK.
    intros Q xra xt0 xt1 xt2 xs0 xs1 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 F fc m1 HT0 HM GLT KX KB KE.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    pose proof (ok_bytes _ OK) as BOK.
    assert (HK0 : (0 < e_n E)%Z) by lia.
    pose proof (off_range _ _ (ok_s1 _ OK) (e_n E - 1) ltac:(lia)) as HORL. pose proof (off_bound E OK (e_n E - 1) ltac:(lia)) as HOL.
    pose proof (off_range _ _ (ok_s1 _ OK) 1 ltac:(lia)) as HOR1. pose proof (off_bound E OK 1 ltac:(lia)) as HO1. pose proof (tok_range E OK 1) as HT1.
    s2_open_mem HM.
    pose proof (idx_read E OK m1 (e_n E - 1) IDXA ltac:(lia)) as RDL.
    pose proof (idx_read E OK m1 1 IDXA ltac:(lia)) as RD1.
    replace (e_IDX E + 4 * 1)%Z with (e_IDX E + 4)%Z in RD1 by lia.
    grun.
    fold (tok (e_bs E) (e_idxs E) (e_n E - 1)) in *.
    if_cases KL; zify_cond KL.
    2:{
        grun_to 0x4be14%Z. eapply (KX 3%Z); [s2_errlit|]. s2_close_memx. }
    grun.
    fold (tok (e_bs E) (e_idxs E) 1) in *.
    if_cases K1; zify_cond K1.
    -
      pose proof (ok_tcap _ OK) as HTC.
      grun_to 0x47028%Z.
      replace (e_TAPE E + 24)%Z with (e_TAPE E + 8 * 3)%Z in FR by lia.
      replace (e_IDX E + 8)%Z with (e_IDX E + 4 * 2)%Z in FR by lia.
      s2_tape2. s2_lit_words (cword 123 (1 + 2) 0) (tword (123 + 2) 1). eapply (KE K1). cbn [scopes k depth W sb].
      s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac].
    -
      grun_to 0x45d38%Z.
      replace (e_SBUF E)%Z with (e_SBUF E + 0)%Z at 1 by lia.
      replace (e_IDX E + 4)%Z with (e_IDX E + 4 * 1)%Z by lia.
      replace (e_TAPE E + 8)%Z with (e_TAPE E + 8 * 1)%Z by lia.
      eapply (KB K1). cbn [scopes k depth W sb].
      s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac].
  Qed.

  Lemma seg_root_arr : forall (Q : machine_state -> Prop)
      xra xt0 xt1 xt2 xs0 xs1 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    e_tok E 0 = c_lbrack ->
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_SBUF E)); C8 (Z_to_bv 64 (e_THIS E)); CB 8 j72]
         [] fc m1 ->
    Z.of_nat (length (e_tws E)) = 1%Z -> exit_k E Q ->
    (e_tok E 1 <> c_rbrack -> arrbegin_k E Q (mkst 1 0 1 0 [])) ->
    (e_tok E 1 = c_rbrack -> docend_k (empty_env E 91 1) Q (mkst 2 0 3 0 [])) ->
    evt usegs Q (S2R E 0x44ac0 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (3)) (Z_to_bv 64 (Z.lxor (e_IDX E) 18446744073709551615)) (Z_to_bv 64 (e_n E)) (Z_to_bv 64 (e_off E 0)) xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_BUF E + e_off E 0)) (Z_to_bv 64 (e_IDX E)) xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK.
    intros Q xra xt0 xt1 xt2 xs0 xs1 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 F fc m1 HT0 HM GLT KX KB KE.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    pose proof (ok_bytes _ OK) as BOK.
    assert (HK0 : (0 < e_n E)%Z) by lia.
    pose proof (off_range _ _ (ok_s1 _ OK) (e_n E - 1) ltac:(lia)) as HORL. pose proof (off_bound E OK (e_n E - 1) ltac:(lia)) as HOL.
    pose proof (off_range _ _ (ok_s1 _ OK) 1 ltac:(lia)) as HOR1. pose proof (off_bound E OK 1 ltac:(lia)) as HO1. pose proof (tok_range E OK 1) as HT1.
    s2_open_mem HM.
    pose proof (idx_read E OK m1 (e_n E - 1) IDXA ltac:(lia)) as RDL.
    pose proof (idx_read E OK m1 1 IDXA ltac:(lia)) as RD1.
    replace (e_IDX E + 4 * 1)%Z with (e_IDX E + 4)%Z in RD1 by lia.
    grun.
    fold (tok (e_bs E) (e_idxs E) (e_n E - 1)) in *.
    if_cases KL; zify_cond KL.
    2:{
        grun_to 0x4be14%Z. eapply (KX 3%Z); [s2_errlit|]. s2_close_memx. }
    grun.
    fold (tok (e_bs E) (e_idxs E) 1) in *.
    if_cases K1; zify_cond K1.
    -
      pose proof (ok_tcap _ OK) as HTC.
      grun_to 0x47028%Z.
      replace (e_TAPE E + 24)%Z with (e_TAPE E + 8 * 3)%Z in FR by lia.
      replace (e_IDX E + 8)%Z with (e_IDX E + 4 * 2)%Z in FR by lia.
      s2_tape2. s2_lit_words (cword 91 (1 + 2) 0) (tword (91 + 2) 1). eapply (KE K1). cbn [scopes k depth W sb].
      s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac].
    -
      grun_to 0x46244%Z.
      replace (e_SBUF E)%Z with (e_SBUF E + 0)%Z at 1 by lia.
      replace (e_IDX E + 4)%Z with (e_IDX E + 4 * 1)%Z by lia.
      replace (e_TAPE E + 8)%Z with (e_TAPE E + 8 * 1)%Z by lia.
      eapply (KB K1). cbn [scopes k depth W sb].
      s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac].
  Qed.

End RootC.
