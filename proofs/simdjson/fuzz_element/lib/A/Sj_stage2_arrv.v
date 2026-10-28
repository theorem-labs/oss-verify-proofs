(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard.
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

Section ArrValue.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_arr_value : forall (Q : machine_state -> Prop) (s : st)
      xra xt1 xt2 xa2 xa3 xa4 xa5 xs7 xs9 xt3 xt4 xt5 xt6
      j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j168 j176 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j168; CB 8 j176; CB 8 j208; CB 8 j272]
         (scopes s) fc m1 ->
    INV ArrValue s ->
    Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (e_tok E (k s) = c_quote -> arrstr_k E Q s) ->
    (e_tok E (k s) = c_lbrack -> e_tok E (k s + 1) = c_rbrack -> arrcont_k (empty_env E 91 (W s)) Q (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_lbrace -> e_tok E (k s + 1) = c_rbrace -> arrcont_k (empty_env E 123 (W s)) Q (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_lbrack -> e_tok E (k s + 1) <> c_rbrack -> arrbegin_k E Q (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_lbrace -> e_tok E (k s + 1) <> c_rbrace -> objbegin_k E Q (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    (e_tok E (k s) <> c_quote -> e_tok E (k s) <> c_lbrack -> e_tok E (k s) <> c_lbrace -> (e_tok E (k s) < 58)%Z -> arrnum_k E Q s) ->
    (e_tok E (k s) <> c_quote -> e_tok E (k s) <> c_lbrack -> e_tok E (k s) <> c_lbrace -> (58 <= e_tok E (k s))%Z -> arratom_k E Q s) ->
    evt asegs Q (S2R E 0xc5df0 xra (Z_to_bv 64 (SHA (e_THIS E + 88))) xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_IDX E + 4 * k s)) (Z_to_bv 64 (e_OC E + 8 * depth s + 4)) xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_THIS E + 88)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_SBUF E + sb s)) xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (e_TAPE E + 8 * W s)) xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    intros Q s xra xt1 xt2 xa2 xa3 xa4 xa5 xs7 xs9 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j168 j176 j208 j272 F fc m1 HM.
    intros HI GLT KX KS KEA KEO KAB KOB KN KA.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_depth_range _ _ _ _ HI) as HD.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (n_bound E OK) as HN. s2_env OK.
    s2_open_mem HM.

    pose proof (u32arr_store_ok asegs m1 (e_OC E) ocs (2 * depth s + 1) (wa (e_OC E + 8 * depth s + 4)) OCA ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    pose proof (u32arr_write asegs m1 (e_OC E) ocs (2 * depth s + 1) xa2 OCA ltac:(lia)) as OCA'.
    replace (e_OC E + 4 * (2 * depth s + 1))%Z with (e_OC E + 8 * depth s + 4)%Z in OCA' by lia.
    store_done.
    s2_cur_mem ltac:(fun m => pose proof (idx_read E OK m (k s) IDXA ltac:(lia)) as RD1;
                              pose proof (tok_read E OK m (k s) BUFRO HK) as RD2).
    grun.
    if_cases K; zify_cond K.
    -
      replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
      eapply (KS K). s2_close_auto.
    - grun.
      if_cases K1; zify_cond K1.
      +
        assert (HK1 : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK| rewrite K1; lia]).
        pose proof (off_bound E OK (k s + 1) ltac:(lia)) as HO1. pose proof (tok_range E OK (k s + 1)) as HT1.
        s2_cur_mem ltac:(fun m => pose proof (idx_read E OK m (k s + 1) IDXA ltac:(lia)) as RD3;
                                  pose proof (tok_read E OK m (k s + 1) BUFRO ltac:(lia)) as RD4).
        replace (e_IDX E + 4 * (k s + 1))%Z with (e_IDX E + 4 * k s + 4)%Z in RD3 by lia.
        grun.
        if_cases K2; zify_cond K2.
        *
          grun_to 0xc5cb8%Z.
          replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
          eapply (KAB K1 K2). cbn [scopes k depth W sb]. s2_close_auto.
        *
          pose proof (inv_W _ _ _ _ HI) as HW. cbn [slackW] in HW.
          assert (HK2 : (k s + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K2; lia]).
          grun_to 0xcf560%Z.
          replace (e_TAPE E + 8 * W s + 16)%Z with (e_TAPE E + 8 * (W s + 2))%Z by lia.
          replace (e_IDX E + 4 * k s + 8)%Z with (e_IDX E + 4 * (k s + 2))%Z by lia.
          s2_tape2. s2_empty_words 91%Z. eapply (KEA K1 K2). cbn [scopes k depth W sb]. s2_close_auto.
      + grun.
        if_cases K3; zify_cond K3.
        *
          grun.
          replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
          if_cases K4; zify_cond K4.
          -- eapply (KA K K1 K3 ltac:(lia)). s2_close_auto.
          -- eapply (KN K K1 K3 ltac:(lia)). s2_close_auto.
        *
          assert (HK1 : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK| rewrite K3; lia]).
          pose proof (off_bound E OK (k s + 1) ltac:(lia)) as HO1. pose proof (tok_range E OK (k s + 1)) as HT1.
          s2_cur_mem ltac:(fun m => pose proof (idx_read E OK m (k s + 1) IDXA ltac:(lia)) as RD3;
                                    pose proof (tok_read E OK m (k s + 1) BUFRO ltac:(lia)) as RD4).
          replace (e_IDX E + 4 * (k s + 1))%Z with (e_IDX E + 4 * k s + 4)%Z in RD3 by lia.
          grun.
          if_cases K2; zify_cond K2.
          --
             grun_to 0xc7450%Z. zstep. if_false.
             grun_to 0xbffec%Z.
             replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
             eapply (KOB K3 K2). cbn [scopes k depth W sb]. s2_close_auto.
          --
             pose proof (inv_W _ _ _ _ HI) as HW. cbn [slackW] in HW.
             assert (HK2 : (k s + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K2; lia]).
             grun_to 0xcf560%Z.
             replace (e_TAPE E + 8 * W s + 16)%Z with (e_TAPE E + 8 * (W s + 2))%Z by lia.
             replace (e_IDX E + 4 * k s + 8)%Z with (e_IDX E + 4 * (k s + 2))%Z by lia.
             s2_tape2. s2_empty_words 123%Z. eapply (KEO K3 K2). cbn [scopes k depth W sb]. s2_close_auto.
  Qed.
End ArrValue.
