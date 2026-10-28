(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac g_store_hook ::= s2_note_tape.

Section RootC.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_root_obj : forall (Q : machine_state -> Prop)
      xra xt0 xt1 xt2 xa0 xa4 xa5 xa6 xa7 xs4 xs7 xt3 xt5 xt6
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_SBUF E)); C8 (Z_to_bv 64 (3)); CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    e_tok E 0 = c_lbrace ->
    Z.of_nat (length (e_tws E)) = 1%Z -> exit_k E Q ->
    (e_tok E 1 <> c_rbrace -> objbegin_k E Q (mkst 1 0 1 0 [])) ->
    (e_tok E 1 = c_rbrace -> docend_k (empty_env E 123 1) Q (mkst 2 0 3 0 [])) ->
    evt bsegs Q (S2R E 0xb8b74 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (SHA (e_BUF E + e_off E 0))) (Z_to_bv 64 (3)) (Z_to_bv 64 (e_IDX E + 4)) xa4 xa5 xa6 xa7 (Z_to_bv 64 (SHA (e_IDX E))) (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (e_TAPE E)) (Z_to_bv 64 (e_THIS E + 56)) xs7 (Z_to_bv 64 (e_BUF E + e_off E 0)) (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_IDX E)) xt3 (Z_to_bv 64 (SHA (e_THIS E + 56))) xt5 xt6 F fc m1).
  Proof using OK SHZ.
    intros Q xra xt0 xt1 xt2 xa0 xa4 xa5 xa6 xa7 xs4 xs7 xt3 xt5 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j288 j304 F fc m1 HM HT0 GLT KX KB KE.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    pose proof (ok_bytes _ OK) as BOK.
    assert (HK0 : (0 < e_n E)%Z) by lia.
    pose proof (off_range _ _ (ok_s1 _ OK) (e_n E - 1) ltac:(lia)) as HORL. pose proof (off_bound E OK (e_n E - 1) ltac:(lia)) as HOL.
    pose proof (off_range _ _ (ok_s1 _ OK) 1 ltac:(lia)) as HOR1. pose proof (off_bound E OK 1 ltac:(lia)) as HO1. pose proof (tok_range E OK 1) as HT1.
    s2_open_mem HM.
    grun_to 0xb8b78%Z.
    s2_cur_mem ltac:(fun m =>
      pose proof (idx_read E OK m (e_n E - 1) IDXA ltac:(lia)) as RDL;
      pose proof (idx_read E OK m 1 IDXA ltac:(lia)) as RD1;
      pose proof (tok_read E OK m (e_n E - 1) BUFRO ltac:(lia)) as RTL;
      pose proof (tok_read E OK m 1 BUFRO ltac:(lia)) as RT1).
    replace (e_IDX E + 4 * 1)%Z with (e_IDX E + 4)%Z in RD1 by lia.
    grun.
    fold (tok (e_bs E) (e_idxs E) (e_n E - 1)) in *.
    if_cases KL; zify_cond KL.
    2:{
        grun_to 0xcd488%Z. gexit KX. }
    grun.
    fold (tok (e_bs E) (e_idxs E) 1) in *.
    if_cases K1; zify_cond K1.
    -
      pose proof (ok_tcap _ OK) as HTC.
      grun_to 0xbcfe4%Z.
      s2_tape2. s2_root_words. s2_lit_words (cword 123 (1 + 2) 0) (tword (123 + 2) 1). eapply (KE K1). cbn [scopes k depth W sb].
      s2_close_mem; [exact OCL | exact OCR | exact IAL | exact IAR].
    -
      grun_to 0xbb810%Z.
      replace (e_SBUF E)%Z with (e_SBUF E + 0)%Z at 1 by lia.
      replace (e_IDX E + 4)%Z with (e_IDX E + 4 * 1)%Z by lia.
      replace (e_TAPE E + 8)%Z with (e_TAPE E + 8 * 1)%Z by lia.
      eapply (KB K1). cbn [scopes k depth W sb].
      s2_close_mem; [exact OCL | exact OCR | exact IAL | exact IAR].
  Qed.

End RootC.
