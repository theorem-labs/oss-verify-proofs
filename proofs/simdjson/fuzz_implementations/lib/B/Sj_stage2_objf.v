(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_stage2_wkit Sj_stage2_fkit Sj_stage2_objfc.
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

Section ObjField.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Definition keyend_k (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)) : Prop :=
    forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs4 xs8 xs11 xt3 xt4 xt5 xt6
           j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (dpt)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * Wv)); CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304] sc fc m1 ->
      evt bsegs Q (S2R E 0xd08e4 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 (e_IDX E + 4 * kk)) (Z_to_bv 64 (e_THIS E)) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

  Lemma seg_key_end : forall (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)),
    let sF := mkst (kk + 1) dpt Wv (sbv + d + 5) sc in
    let sV := mkst (kk + 2) dpt Wv (sbv + d + 5) sc in
    INV ObjField sF -> (0 <= sbv)%Z -> (0 <= d)%Z -> (sbv + d + 5 <= e_scap E)%Z ->
    Z.of_nat (length (e_tws E)) = Wv -> exit_k E Q ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) = c_quote -> objstr_k E Q sV) ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) = c_lbrack -> e_tok E (kk + 3) = c_rbrack ->
       objcont_k (empty_env E 91 Wv) Q (mkst (kk + 4) dpt (Wv + 2) (sbv + d + 5) sc)) ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) = c_lbrace -> e_tok E (kk + 3) = c_rbrace ->
       objcont_k (empty_env E 123 Wv) Q (mkst (kk + 4) dpt (Wv + 2) (sbv + d + 5) sc)) ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) = c_lbrack -> e_tok E (kk + 3) <> c_rbrack ->
       arrbegin_k E Q (mkst (kk + 3) dpt Wv (sbv + d + 5) sc)) ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) = c_lbrace -> e_tok E (kk + 3) <> c_rbrace ->
       objbegin_k E Q (mkst (kk + 3) dpt Wv (sbv + d + 5) sc)) ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) <> c_quote -> e_tok E (kk + 2) <> c_lbrack -> e_tok E (kk + 2) <> c_lbrace ->
       (e_tok E (kk + 2) <= 57)%Z -> objnum_k E Q sV) ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) <> c_quote -> e_tok E (kk + 2) <> c_lbrack -> e_tok E (kk + 2) <> c_lbrace ->
       (57 < e_tok E (kk + 2))%Z -> objatom_k E Q sV) ->
    keyend_k Q kk dpt Wv sbv d sc.
  Proof using OK SHZ.
    intros Q kk dpt Wv sbv d sc sF sV HI HSB HD0 HSC GLT KX KS KEA KEO KAB KOB KN KA. unfold keyend_k. subst sF sV.
    intros xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs4 xs8 xs11 xt3 xt4 xt5 xt6
           j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j192 j200 j272 j288 j304 F fc m1 HM.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_depth_range _ _ _ _ HI) as HD.
    cbn [k depth W sb scopes slackW] in *.
    pose proof (n_bound E OK) as HN. s2_env OK.
    pose proof HM as HMo. s2_open_mem HMo.

    pose proof (off_bound E OK (kk + 1) HK) as HO1. pose proof (tok_range E OK (kk + 1)) as HT1.
    s2_cur_mem ltac:(fun m =>
      pose proof (idx_read E OK m (kk + 1) IDXA ltac:(lia)) as RD1;
      pose proof (tok_read E OK m (kk + 1) BUFRO HK) as RD2).
    replace (e_IDX E + 4 * (kk + 1))%Z with (e_IDX E + 4 * kk + 4)%Z in RD1 by lia.
    wrun_f.
    if_cases K; zify_cond K.
    2:{ wrun_f_to 0xdbc94%Z. gexit KX. }

    assert (HK1 : (kk + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK| rewrite K; lia]).
    pose proof (off_bound E OK (kk + 2) ltac:(lia)) as HO2. pose proof (tok_range E OK (kk + 2)) as HT2.
    s2_cur_mem ltac:(fun m =>
      pose proof (idx_read E OK m (kk + 2) IDXA ltac:(lia)) as RD3;
      pose proof (tok_read E OK m (kk + 2) BUFRO ltac:(lia)) as RD4).
    replace (e_IDX E + 4 * (kk + 2))%Z with (e_IDX E + 4 * kk + 8)%Z in RD3 by lia.
    wrun_f.
    if_cases K0; zify_cond K0.
    -
      replace (e_IDX E + 4 * kk + 12)%Z with (e_IDX E + 4 * (kk + 2 + 1))%Z by lia.
      replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + (sbv + d + 5))%Z by lia.
      replace (e_SBUF E + sbv + 4 + d)%Z with (e_SBUF E + (sbv + d + 5) + -1)%Z by lia.
      eapply (KS K K0). cbn [scopes depth W sb k]. s2_close_auto.
    - wrun_f.
      if_cases K1; zify_cond K1.
      +
        eapply (seg_objf_arr E OK SHZ Q kk dpt Wv sbv d sc HI HSB HD0 HSC GLT KX K K1 HK1 KEA KAB); wk_close.
      + wrun_f.
        if_cases K3; zify_cond K3.
        *
          wrun_f.
          replace (e_IDX E + 4 * kk + 12)%Z with (e_IDX E + 4 * (kk + 2 + 1))%Z in * by lia.
          replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + (sbv + d + 5))%Z in * by lia.
          replace (e_SBUF E + sbv + 4 + d)%Z with (e_SBUF E + (sbv + d + 5) + -1)%Z by lia.
          if_cases K4; zify_cond K4.
          -- eapply (KA K K0 K1 K3 ltac:(lia)). cbn [scopes depth W sb k]. wk_close.
          -- eapply (KN K K0 K1 K3 ltac:(lia)). cbn [scopes depth W sb k]. wk_close.
        *
          eapply (seg_objf_obj E OK SHZ Q kk dpt Wv sbv d sc HI HSB HD0 HSC GLT KX K K3 HK1 KEO KOB); wk_close.
  Qed.
End ObjField.
