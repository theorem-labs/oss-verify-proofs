(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard.
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

Section ArrValueC.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_arrv_arr : forall (Q : machine_state -> Prop) (s : st),
    INV ArrValue s -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q -> e_tok E (k s) = c_lbrack ->
    (e_tok E (k s) = c_lbrack -> e_tok E (k s + 1) = c_rbrack -> arrcont_k (empty_env E 91 (W s)) Q (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_lbrack -> e_tok E (k s + 1) <> c_rbrack -> arrbegin_k E Q (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    forall xra xa0 xa1 xa2 xa3 xa4 xa5 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
           j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j184 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304] (scopes s) fc m1 ->
      evt bsegs Q (S2R E 0xbf7a0 xra (Z_to_bv 64 (e_TAPE E + 8 * W s)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_IDX E + 4 * k s)) (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_IDX E + 4 * k s + 4)) (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    intros Q s HI GLT KX K1 KEA KAB.
    intros xra xa0 xa1 xa2 xa3 xa4 xa5 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
           j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j184 j192 j200 j272 j288 j304 F fc m1 HM.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_depth_range _ _ _ _ HI) as HD.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    unfold c_colon, c_lbrack, c_lbrace, c_rbrack, c_rbrace in *.
    pose proof (n_bound E OK) as HN. s2_env OK.
    s2_open_mem HM.
        assert (HK1 : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK| rewrite K1; lia]).
        pose proof (off_bound E OK (k s + 1) ltac:(lia)) as HO1. pose proof (tok_range E OK (k s + 1)) as HT1.
        s2_cur_mem ltac:(fun m => pose proof (idx_read E OK m (k s + 1) IDXA ltac:(lia)) as RD3;
                                  pose proof (tok_read E OK m (k s + 1) BUFRO ltac:(lia)) as RD4).
        replace (e_IDX E + 4 * (k s + 1))%Z with (e_IDX E + 4 * k s + 4)%Z in RD3 by lia.
        grun.
        if_cases K2; zify_cond K2.
        *
          grun_to 0xbbf84%Z.
          replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
          eapply (KAB K1 K2). cbn [scopes k depth W sb]. s2_close_mem; [exact OCL | exact OCR | exact IAL | exact IAR].
        *
          pose proof (inv_W _ _ _ _ HI) as HW. cbn [slackW] in HW.
          assert (HK2 : (k s + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K2; lia]).
          grun_to 0xcdf58%Z.
          s2_tape2. s2_empty_words 91%Z. eapply (KEA K1 K2). cbn [scopes k depth W sb]. s2_close_mem; [exact OCL | exact OCR | exact IAL | exact IAR].
  Qed.

  Lemma seg_arrv_obj : forall (Q : machine_state -> Prop) (s : st),
    INV ArrValue s -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q -> e_tok E (k s) = c_lbrace ->
    (e_tok E (k s) = c_lbrace -> e_tok E (k s + 1) = c_rbrace -> arrcont_k (empty_env E 123 (W s)) Q (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_lbrace -> e_tok E (k s + 1) <> c_rbrace -> objbegin_k E Q (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    forall xra xa0 xa1 xa2 xa3 xa4 xa5 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
           j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j184 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304] (scopes s) fc m1 ->
      evt bsegs Q (S2R E 0xbf650 xra (Z_to_bv 64 (e_TAPE E + 8 * W s)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_IDX E + 4 * k s)) (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_IDX E + 4 * k s + 4)) (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    intros Q s HI GLT KX K3 KEO KOB.
    intros xra xa0 xa1 xa2 xa3 xa4 xa5 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
           j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j184 j192 j200 j272 j288 j304 F fc m1 HM.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_depth_range _ _ _ _ HI) as HD.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    unfold c_colon, c_lbrack, c_lbrace, c_rbrack, c_rbrace in *.
    pose proof (n_bound E OK) as HN. s2_env OK.
    s2_open_mem HM.
          assert (HK1 : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK| rewrite K3; lia]).
          pose proof (off_bound E OK (k s + 1) ltac:(lia)) as HO1. pose proof (tok_range E OK (k s + 1)) as HT1.
          s2_cur_mem ltac:(fun m => pose proof (idx_read E OK m (k s + 1) IDXA ltac:(lia)) as RD3;
                                    pose proof (tok_read E OK m (k s + 1) BUFRO ltac:(lia)) as RD4).
          replace (e_IDX E + 4 * (k s + 1))%Z with (e_IDX E + 4 * k s + 4)%Z in RD3 by lia.
          grun.
          if_cases K2; zify_cond K2.
          --
             pose proof (inv_W _ _ _ _ HI) as HW. cbn [slackW] in HW.
             assert (HK2 : (k s + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K2; lia]).
             grun_to 0xcdf58%Z.
             s2_tape2. s2_empty_words 123%Z. eapply (KEO K3 K2). cbn [scopes k depth W sb]. s2_close_mem; [exact OCL | exact OCR | exact IAL | exact IAR].
          --
             grun_to 0xbb48c%Z.
             replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
             eapply (KOB K3 K2). cbn [scopes k depth W sb]. s2_close_mem; [exact OCL | exact OCR | exact IAL | exact IAR].
  Qed.

End ArrValueC.
