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

Section ArrCont.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_arr_cont : forall (Q : machine_state -> Prop) (s : st)
      xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xs7 xs9 xt4 xt5 xt6
      j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j168 j176 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j168; CB 8 j176; CB 8 j208; CB 8 j272]
         (scopes s) fc m1 ->
    INV ArrCont s ->
    exit_k E Q ->
    (e_tok E (k s) = c_comma -> arrvalue_k E Q (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_rbrack -> scopeend_k E Q 91 (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s))) ->
    evt asegs Q (S2R E 0xcf560 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_THIS E + 88)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_SBUF E + sb s)) xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (e_TAPE E + 8 * W s)) (Z_to_bv 64 (e_IDX E + 4 * k s)) xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    intros Q s xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xs7 xs9 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j168 j176 j208 j272 F fc m1 HM.
    intros HI KX KV KE.
    pose proof (inv_k _ _ _ _ HI) as HK.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (n_bound E OK) as HN. s2_env OK.
    s2_open_mem HM.
    pose proof (idx_read E OK m1 (k s) IDXA ltac:(lia)) as RD1.
    pose proof (tok_read E OK m1 (k s) BUFRO HK) as RD2.
    grun.
    if_cases K; zify_cond K.
    -
      grun_to 0xcf43c%Z.
      replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
      replace (e_TAPE E + 8 * W s)%Z with (e_TAPE E + 8 * (W s + 1 - 1))%Z by lia.
      eapply (KE K); [reflexivity | reflexivity |]. cbn [scopes k depth W sb].
      s2_close_mem; [exact OCL | exact OCR | exact IAL | exact IAR].
    - grun.
      if_cases K2; zify_cond K2.
      +
        grun_to 0xcb1dc%Z.
        eapply (KX 3%Z); [s2_errlit|].
        s2_close_memx.
      +
        pose proof (inv_depth_range _ _ _ _ HI) as HD.
        destruct (nth_error_ex ocs (Z.to_nat (2 * depth s + 1)) ltac:(lia)) as [cnt Hcnt].
        pose proof (u32arr_read asegs m1 (e_OC E) ocs (2 * depth s + 1) cnt (wa (e_OC E + 8 * depth s + 4)) OCA Hcnt ltac:(lia)
                      ltac:(unfold wa; f_equal; lia)) as RD3.
        grun_to 0xc5df0%Z.
        replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
        eapply (KV K2). cbn [scopes k depth W sb].
        s2_close_mem; [exact OCL | exact OCR | exact IAL | exact IAR].
  Qed.
End ArrCont.
