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

Section ObjField.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_obj_field : forall (Q : machine_state -> Prop) (s : st)
      xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5
      j0 j8 j16 j24 j40 j48 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    INV ObjField s ->
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; C8 (Z_to_bv 64 (depth s)); CB 8 j40; CB 8 j48; CB 8 j56; C8 (Z_to_bv 64 (e_THIS E)); CB 8 j72]
         (scopes s) fc m1 ->
    Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (e_tok E (k s) = c_colon -> e_tok E (k s + 1) = c_quote -> objstr_k E Q (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_colon -> e_tok E (k s + 1) = c_lbrack -> e_tok E (k s + 2) = c_rbrack -> objcont_k (empty_env E 91 (W s)) Q (mkst (k s + 3) (depth s) (W s + 2) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_colon -> e_tok E (k s + 1) = c_lbrace -> e_tok E (k s + 2) = c_rbrace -> objcont_k (empty_env E 123 (W s)) Q (mkst (k s + 3) (depth s) (W s + 2) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_colon -> e_tok E (k s + 1) = c_lbrack -> e_tok E (k s + 2) <> c_rbrack -> arrbegin_k E Q (mkst (k s + 2) (depth s) (W s) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_colon -> e_tok E (k s + 1) = c_lbrace -> e_tok E (k s + 2) <> c_rbrace -> objbegin_k E Q (mkst (k s + 2) (depth s) (W s) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_colon -> e_tok E (k s + 1) <> c_quote -> e_tok E (k s + 1) <> c_lbrack -> e_tok E (k s + 1) <> c_lbrace -> (e_tok E (k s + 1) < 58)%Z -> objnum_k E Q (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_colon -> e_tok E (k s + 1) <> c_quote -> e_tok E (k s + 1) <> c_lbrack -> e_tok E (k s + 1) <> c_lbrace -> (58 <= e_tok E (k s + 1))%Z -> objatom_k E Q (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    evt usegs Q (S2R E 0x4aa5c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_IDX E + 4 * (k s - 1))) xa7 xs2 (Z_to_bv 64 (e_SBUF E + (sb s - 1))) xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 (Z_to_bv 64 (e_TAPE E + 8 * W s)) F fc m1).
  Proof using OK.
    intros Q s xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 j0 j8 j16 j24 j40 j48 j56 j72 F fc m1 HI HM GLT KX KS KEA KEO KAB KOB KN KA.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_sb _ _ _ _ HI) as [HSB0 HSB1].
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (n_bound E OK) as HN. s2_env OK.
    s2_open_mem HM.
    pose proof (idx_read E OK m1 (k s) IDXA ltac:(lia)) as RD1.
    replace (e_IDX E + 4 * k s)%Z with (e_IDX E + 4 * (k s - 1) + 4)%Z in RD1 by lia.
    pose proof (tok_read E OK m1 (k s) BUFRO HK) as RD2.
    grun.
    if_cases KC; zify_cond KC.
    -
      assert (HK1 : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK| rewrite KC; lia]).
      pose proof (off_bound E OK (k s + 1) ltac:(lia)) as HO1. pose proof (tok_range E OK (k s + 1)) as HT1.
      pose proof (idx_read E OK m1 (k s + 1) IDXA ltac:(lia)) as RD3.
      replace (e_IDX E + 4 * (k s + 1))%Z with (e_IDX E + 4 * (k s - 1) + 8)%Z in RD3 by lia.
      pose proof (tok_read E OK m1 (k s + 1) BUFRO ltac:(lia)) as RD4.
      grun.
      replace (e_SBUF E + (sb s - 1) + 1)%Z with (e_SBUF E + sb s)%Z by lia.
      replace (e_IDX E + 4 * (k s - 1) + 12)%Z with (e_IDX E + 4 * (k s + 1 + 1))%Z by lia.
      if_cases K; zify_cond K.
      +
        eapply (KS KC K). cbn [scopes k depth W sb].
        s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac].
      + grun.
        if_cases K1; zify_cond K1.
        *
          assert (HK2 : (k s + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K1; lia]).
          pose proof (off_bound E OK (k s + 2) ltac:(lia)) as HO2. pose proof (tok_range E OK (k s + 2)) as HT2.
          pose proof (idx_read E OK m1 (k s + 2) IDXA ltac:(lia)) as RD5.
          replace (e_IDX E + 4 * (k s + 2))%Z with (e_IDX E + 4 * (k s + 1 + 1))%Z in RD5 by lia.
          pose proof (tok_read E OK m1 (k s + 2) BUFRO ltac:(lia)) as RD6.
          grun.
          if_cases K2; zify_cond K2.
          --
             grun_to 0x46244%Z.
             replace (e_IDX E + 4 * (k s + 1 + 1))%Z with (e_IDX E + 4 * (k s + 2))%Z by lia.
             eapply (KAB KC K1 K2). cbn [scopes k depth W sb].
             s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac].
          --
             pose proof (inv_W _ _ _ _ HI) as HW. cbn [slackW] in HW. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL.
             assert (HK3 : (k s + 2 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K2; lia]).
             grun_to 0x4e4c4%Z.
             replace (e_TAPE E + 8 * W s + 16)%Z with (e_TAPE E + 8 * (W s + 2))%Z in FR by lia.
             replace (e_IDX E + 4 * (k s - 1) + 16)%Z with (e_IDX E + 4 * (k s + 3))%Z by lia.
             s2_tape2. s2_empty_words 91%Z. eapply (KEA KC K1 K2). cbn [scopes k depth W sb].
             s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac].
        * grun.
          if_cases K3; zify_cond K3.
          --
             grun.
             replace (e_IDX E + 4 * (k s + 2))%Z with (e_IDX E + 4 * (k s + 1 + 1))%Z by lia.
             if_cases K4; zify_cond K4.
             ++ eapply (KA KC K K1 K3 ltac:(lia)). cbn [scopes k depth W sb]. s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac].
             ++ eapply (KN KC K K1 K3 ltac:(lia)). cbn [scopes k depth W sb]. s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac].
          --
             assert (HK2 : (k s + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K3; lia]).
             pose proof (off_bound E OK (k s + 2) ltac:(lia)) as HO2. pose proof (tok_range E OK (k s + 2)) as HT2.
             pose proof (idx_read E OK m1 (k s + 2) IDXA ltac:(lia)) as RD5.
             replace (e_IDX E + 4 * (k s + 2))%Z with (e_IDX E + 4 * (k s + 1 + 1))%Z in RD5 by lia.
             pose proof (tok_read E OK m1 (k s + 2) BUFRO ltac:(lia)) as RD6.
             grun.
             if_cases K2; zify_cond K2.
             ++
                grun_to 0x45d38%Z.
                replace (e_IDX E + 4 * (k s + 1 + 1))%Z with (e_IDX E + 4 * (k s + 2))%Z by lia.
                eapply (KOB KC K3 K2). cbn [scopes k depth W sb].
                s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac].
             ++
                pose proof (inv_W _ _ _ _ HI) as HW. cbn [slackW] in HW. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL.
                assert (HK3 : (k s + 2 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K2; lia]).
                grun_to 0x4e4c4%Z.
                replace (e_TAPE E + 8 * W s + 16)%Z with (e_TAPE E + 8 * (W s + 2))%Z in FR by lia.
                replace (e_IDX E + 4 * (k s - 1) + 16)%Z with (e_IDX E + 4 * (k s + 3))%Z by lia.
                s2_tape2. s2_empty_words 123%Z. eapply (KEO KC K3 K2). cbn [scopes k depth W sb].
                s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac].
    -
      grun_to 0x4be14%Z.
      eapply (KX 3%Z); [s2_errlit|]. s2_close_memx.
  Qed.
End ObjField.
