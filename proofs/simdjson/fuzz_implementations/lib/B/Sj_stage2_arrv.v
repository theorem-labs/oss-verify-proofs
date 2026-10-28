(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_stage2_arrvc.
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
      xra xa2 xa3 xa4 xa5 xa7 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j184 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
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
    evt bsegs Q (S2R E 0xce148 xra (Z_to_bv 64 (e_TAPE E + 8 * W s)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_IDX E + 4 * k s)) (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_OC E + 8 * depth s)) (Z_to_bv 64 (e_OC E)) xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_THIS E)) xa7 (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    intros Q s xra xa2 xa3 xa4 xa5 xa7 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j184 j192 j200 j272 j288 j304 F fc m1
 HM.
    intros HI GLT KX KS KEA KEO KAB KOB KN KA.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_depth_range _ _ _ _ HI) as HD.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (n_bound E OK) as HN. s2_env OK.
    s2_open_mem HM.

    destruct (nth_error_ex ocs (Z.to_nat (2 * depth s + 1)) ltac:(lia)) as [cnt Hcnt].
    pose proof (u32arr_read bsegs m1 (e_OC E) ocs (2 * depth s + 1) cnt (wa (e_OC E + 8 * depth s + 4)) OCA Hcnt ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD0.
    pose proof (u32arr_store_ok bsegs m1 (e_OC E) ocs (2 * depth s + 1) (wa (e_OC E + 8 * depth s + 4)) OCA ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    grun_to 0xce17c%Z.
    zstep.
    pose proof (u32arr_write bsegs m1 (e_OC E) ocs (2 * depth s + 1) (Z_to_bv 64 (bv_unsigned (sx32 cnt) + 1)) OCA ltac:(lia)) as OCA'.
    replace (e_OC E + 4 * (2 * depth s + 1))%Z with (e_OC E + 8 * depth s + 4)%Z in OCA' by lia.
    store_done.
    s2_cur_mem ltac:(fun m => pose proof (idx_read E OK m (k s) IDXA ltac:(lia)) as RD1;
                              pose proof (tok_read E OK m (k s) BUFRO HK) as RD2).
    grun.
    assert (OCL' : length (upd ocs (Z.to_nat (2 * depth s + 1)) (Z_to_bv 64 (bv_unsigned (sx32 cnt) + 1))) = 2048%nat) by (rewrite upd_length; exact OCL).
    assert (OCR' : oc_rel (scopes s) (upd ocs (Z.to_nat (2 * depth s + 1)) (Z_to_bv 64 (bv_unsigned (sx32 cnt) + 1))))
      by (apply oc_rel_upd_other; [exact OCR | intros jj Hjj; lia]).
    if_cases K; zify_cond K.
    -
      replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
      eapply (KS K). s2_close_mem; [exact OCL' | exact OCR' | exact IAL | exact IAR].
    - grun.
      if_cases K1; zify_cond K1.
      +
        eapply (seg_arrv_arr E OK SHZ Q s HI GLT KX K1 KEA KAB). s2_close_mem; [exact OCL' | exact OCR' | exact IAL | exact IAR].
      + grun.
        if_cases K3; zify_cond K3.
        *
          grun.
          replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z in * by lia.
          if_cases K4; zify_cond K4.
          -- eapply (KA K K1 K3 ltac:(lia)). s2_close_mem; [exact OCL' | exact OCR' | exact IAL | exact IAR].
          -- eapply (KN K K1 K3 ltac:(lia)). s2_close_mem; [exact OCL' | exact OCR' | exact IAL | exact IAR].
        *
          eapply (seg_arrv_obj E OK SHZ Q s HI GLT KX K3 KEO KOB). s2_close_mem; [exact OCL' | exact OCR' | exact IAL | exact IAR].
  Qed.
End ArrValue.
