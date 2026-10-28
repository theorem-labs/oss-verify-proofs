(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_stage2_wkit Sj_stage2_fkit.
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

Ltac wrun_fn_to A :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with A => fail | _ => idtac end
          | _ => idtac end;
          first [ gguard | (wstep_note; gforget_junk) ]).

Section KeyEnd2.
  Variable E : s2env.

  Definition keyend2_k (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)) : Prop :=
    forall xra xt2 xa4 xs6 xs7 xs9 xt3 xt4 xt5 xt6
           j64 j72 j80 j88 j96 j104 j112 j120 j128 j168 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128;
                         C8 (Z_to_bv 64 (e_SBUF E + sbv + 4)); C8 (Z_to_bv 64 dpt); C8 (Z_to_bv 64 (SHA (e_THIS E + 56)));
                         CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E + 8 * Wv)); C8 (Z_to_bv 64 (e_SBUF E + sbv + 4 + d + 1)); CB 8 j272] sc fc m1 ->
      evt asegs Q (S2R E 0xc1cf4 xra (Z_to_bv 64 (SHA (e_THIS E + 88))) (Z_to_bv 64 (e_SBUF E + sbv)) xt2 (e_sp E) (Z_to_bv 64 (e_spa E))
                       (Z_to_bv 64 (e_IDX E + 4 * kk)) (Z_to_bv 64 (e_IDX E + 4 * kk + 4)) (Z_to_bv 64 0) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d + 1)) xa4
                       (Z_to_bv 64 (SHA (e_SBUF E + sbv + 4 + d))) (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_THIS E + 88))
                       (Z_to_bv 64 2147450880) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 dpt) xs6 xs7 (Z_to_bv 64 (e_BUF E)) xs9
                       (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) xt3 xt4 xt5 xt6 F fc m1).
End KeyEnd2.

Section ObjField.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Definition keyend_k (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)) : Prop :=
    forall xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs9 xt3 xt4 xt5 xt6
           j64 j72 j80 j88 j96 j104 j112 j120 j128 j168 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128;
                         C8 (Z_to_bv 64 (e_SBUF E + sbv + 4)); C8 (Z_to_bv 64 dpt); C8 (Z_to_bv 64 (SHA (e_THIS E + 56)));
                         CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E + 8 * Wv)); C8 (Z_to_bv 64 (e_SBUF E + sbv)); CB 8 j272] sc fc m1 ->
      evt asegs Q (S2R E 0xc1c54 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_IDX E + 4 * kk)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 2147450880) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 xs7 (Z_to_bv 64 (e_BUF E)) xs9
                       (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) xt3 xt4 xt5 xt6 F fc m1).

  Lemma seg_key_end : forall (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)),
    let sF := mkst (kk + 1) dpt Wv (sbv + d + 5) sc in
    INV ObjField sF -> (0 <= sbv)%Z -> (0 <= d < 2^31)%Z -> (sbv + d + 5 <= e_scap E)%Z -> Z.of_nat (length (e_sbs E)) = sbv ->
    (forall cb, Z.of_nat (length cb) = d -> keyend2_k (gapp E [] (srec d cb)) Q kk dpt Wv sbv d sc) ->
    keyend_k Q kk dpt Wv sbv d sc.
  Proof using OK SHZ.
    intros Q kk dpt Wv sbv d sc sF HI HSB HD0 HSC GLS KC. unfold keyend_k. subst sF.
    intros until m1. intros HM.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_depth_range _ _ _ _ HI) as HD.
    cbn [k depth W sb scopes slackW] in *.
    pose proof (n_bound E OK) as HN. s2_env OK.
    pose proof HM as HMo. s2_open_mem HMo.
    wrun_note_to 0xc1cf4%Z.
    s2_str_close d.
    unfold keyend2_k in KC. eapply (KC (map bv_unsigned cb) SRL). wk_close_ghost.
  Qed.

  Lemma seg_key_disp : forall (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)),
    let sF := mkst (kk + 1) dpt Wv (sbv + d + 5) sc in
    let sV := mkst (kk + 2) dpt Wv (sbv + d + 5) sc in
    INV ObjField sF -> (0 <= sbv)%Z -> (0 <= d)%Z -> (sbv + d + 5 <= e_scap E)%Z -> Z.of_nat (length (e_tws E)) = Wv ->
    exit_k E Q ->
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
    keyend2_k E Q kk dpt Wv sbv d sc.
  Proof using OK SHZ.
    intros Q kk dpt Wv sbv d sc sF sV HI HSB HD0 HSC GLT KX KS KEA KEO KAB KOB KN KA. unfold keyend2_k. subst sF sV.
    intros until m1. intros HM.
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
    2:{ wrun_f_to 0xcb1dc%Z. eapply (KX 3%Z); [s2_errlit|]. s2_close_memx. }

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
      replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + (sbv + d + 5))%Z in FR by lia.
      replace (e_SBUF E + sbv + 4 + d)%Z with (e_SBUF E + (sbv + d + 5) + -1)%Z by lia.
      eapply (KS K K0). cbn [scopes depth W sb k]. s2_close_auto.
    - wrun_f.
      if_cases K1; zify_cond K1.
      +
        assert (HK2 : (kk + 2 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K1; lia]).
        pose proof (off_bound E OK (kk + 3) ltac:(lia)) as HO3. pose proof (tok_range E OK (kk + 3)) as HT3.
        s2_cur_mem ltac:(fun m =>
          pose proof (idx_read E OK m (kk + 3) IDXA ltac:(lia)) as RD5;
          pose proof (tok_read E OK m (kk + 3) BUFRO ltac:(lia)) as RD6).
        replace (e_IDX E + 4 * (kk + 3))%Z with (e_IDX E + 4 * kk + 12)%Z in RD5 by lia.
        wrun_f.
        if_cases K2; zify_cond K2.
        *
          assert (HK3 : (kk + 3 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K2; lia]).
          wrun_note_to 0xca8f8%Z.
          replace (e_IDX E + 4 * kk + 16)%Z with (e_IDX E + 4 * (kk + 4))%Z by lia.
          replace (e_TAPE E + 8 * Wv + 16)%Z with (e_TAPE E + 8 * (Wv + 2))%Z by lia.
          replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + (sbv + d + 5))%Z by lia.
          s2_tape2. s2_empty_words 91%Z. eapply (KEA K K1 K2). cbn [scopes depth W sb k]. s2_close_auto.
        *
          wrun_f_to 0xc5cb8%Z.
          replace (e_IDX E + 4 * kk + 12)%Z with (e_IDX E + 4 * (kk + 3))%Z by lia.
          replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + (sbv + d + 5))%Z by lia.
          eapply (KAB K K1 K2). cbn [scopes depth W sb k]. s2_close_auto.
      + wrun_f.
        if_cases K3; zify_cond K3.
        *
          wrun_f.
          replace (e_IDX E + 4 * kk + 12)%Z with (e_IDX E + 4 * (kk + 2 + 1))%Z by lia.
          replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + (sbv + d + 5))%Z in FR by lia.
          replace (e_SBUF E + sbv + 4 + d)%Z with (e_SBUF E + (sbv + d + 5) + -1)%Z by lia.
          if_cases K4; zify_cond K4.
          -- eapply (KA K K0 K1 K3 ltac:(lia)). cbn [scopes depth W sb k]. s2_close_auto.
          -- eapply (KN K K0 K1 K3 ltac:(lia)). cbn [scopes depth W sb k]. s2_close_auto.
        *
          assert (HK2 : (kk + 2 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K3; lia]).
          pose proof (off_bound E OK (kk + 3) ltac:(lia)) as HO3. pose proof (tok_range E OK (kk + 3)) as HT3.
          s2_cur_mem ltac:(fun m =>
            pose proof (idx_read E OK m (kk + 3) IDXA ltac:(lia)) as RD5;
            pose proof (tok_read E OK m (kk + 3) BUFRO ltac:(lia)) as RD6).
          replace (e_IDX E + 4 * (kk + 3))%Z with (e_IDX E + 4 * kk + 12)%Z in RD5 by lia.
          wrun_f.
          if_cases K2; zify_cond K2.
          --
             wrun_f_to 0xc3b2c%Z. zstep. if_false.
             wrun_f_to 0xbffec%Z.
             replace (e_IDX E + 4 * kk + 12)%Z with (e_IDX E + 4 * (kk + 3))%Z by lia.
             replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + (sbv + d + 5))%Z by lia.
             eapply (KOB K K3 K2). cbn [scopes depth W sb k]. s2_close_auto.
          --
             assert (HK3 : (kk + 3 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K2; lia]).
             wrun_note_to 0xca8f8%Z.
             replace (e_IDX E + 4 * kk + 16)%Z with (e_IDX E + 4 * (kk + 4))%Z by lia.
             replace (e_TAPE E + 8 * Wv + 16)%Z with (e_TAPE E + 8 * (Wv + 2))%Z by lia.
             replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + (sbv + d + 5))%Z by lia.
             s2_tape2. s2_empty_words 123%Z. eapply (KEO K K3 K2). cbn [scopes depth W sb k]. s2_close_auto.
  Qed.
End ObjField.
