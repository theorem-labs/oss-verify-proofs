(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard.
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

Section ArrCont.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_arr_cont : forall (Q : machine_state -> Prop) (s : st)
      xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs4 xs5 xs7 xs8 xs11 xt3 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j176 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); CB 8 j176; C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * k s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    INV ArrCont s ->
    Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (e_tok E (k s) = c_comma -> arrvalue_k E Q (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    (forall cv ti rest, scopes s = (true, ti) :: rest -> (0 <= cv <= CNT_MAX)%Z -> e_tok E (k s) = c_rbrack ->
       scopeend_k (endc_env E 91 ti (W s) cv) Q (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s))) ->
    evt bsegs Q (S2R E 0xdcae8 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (SHA (e_THIS E + 56))) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) xs7 xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    intros Q s xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs4 xs5 xs7 xs8 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j176 j272 j288 j304 F fc m1
 HM.
    intros HI GLT KX KV KE.
    pose proof (inv_k _ _ _ _ HI) as HK.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (n_bound E OK) as HN. s2_env OK.
    s2_open_mem HM.
    grun_to 0xdcaec%Z.
    s2_cur_mem ltac:(fun m => pose proof (idx_read E OK m (k s) IDXA ltac:(lia)) as RD1;
                              pose proof (tok_read E OK m (k s) BUFRO HK) as RD2).
    grun.
    if_cases K; zify_cond K.
    -
      pose proof (inv_depth_range _ _ _ _ HI) as HD.
      grun_to 0xce148%Z.
      replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
      replace (8 * depth s + e_OC E)%Z with (e_OC E + 8 * depth s)%Z by lia.
      eapply (KV K). cbn [scopes k depth W sb].
      s2_close_auto.
    -
      grun.
      if_cases K2; zify_cond K2.
      +
        grun_to 0xdbc94%Z. gexit KX.
      +
        pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_depth _ _ _ _ HI) as [HD1 HD2].
        pose proof (inv_scopes _ _ _ _ HI) as HSC. pose proof (inv_kind _ _ _ _ HI) as HKD.
        cbn [k depth W sb scopes slackW kind_ok] in *. unfold MAXDEPTH in *.
        pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL.
        assert (HK1 : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK| rewrite K2; lia]).
        destruct HKD as (ti0 & rest & ESC). rewrite ESC in HD1, HSC, OCR, IAR. cbn [length] in HD1.
        inversion HSC as [|? ? HTI HSC']; subst. cbn [snd] in HTI.
        pose proof (oc_rel_top _ _ _ _ OCR) as TOP.
        assert (DEQ : (2 * (length rest + 1))%nat = Z.to_nat (2 * depth s)) by lia.
        rewrite DEQ in TOP.
        s2_cur_mem ltac:(fun m => pose proof (u32arr_read bsegs m (e_OC E) ocs (2 * depth s) (Z_to_bv 64 ti0) (wa (e_OC E + 8 * depth s)) OCA TOP ltac:(lia)
                      ltac:(unfold wa; f_equal; lia)) as RD3).
        grun_to 0xdccc8%Z.
        destruct (nth_error_ex ocs (Z.to_nat (2 * depth s + 1)) ltac:(lia)) as [cnt Hcnt].
        s2_cur_mem ltac:(fun m => pose proof (u32arr_read bsegs m (e_OC E) ocs (2 * depth s + 1) cnt (wa (e_OC E + 8 * depth s + 4)) OCA Hcnt ltac:(lia)
                      ltac:(unfold wa; f_equal; lia)) as RD4).
        grun.
        pose proof (bv_unsigned_in_range 64 (sx32 cnt)) as HCR. unfold bv_modulus in HCR. cbn in HCR.
        if_cases KC; [ zify_cond KC | gstep; gstep; gstep; clear KC ].

        all: grun_to 0xdca68%Z; zstep; gnorm.
        1: pose proof (srliw24_zero _ KC) as HC24; s2_endc_patch_b 91%Z ti0 (bv_unsigned (sx32 cnt)); s2_endc_close 91%Z ti0.
        2: s2_endc_patch_b 91%Z ti0 16777215%Z; s2_endc_close 91%Z ti0.
        all: grun_to 0xdca6c%Z.
        all: replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
        1: eapply (KE (bv_unsigned (sx32 cnt)) ti0 rest ESC ltac:(unfold CNT_MAX; lia) K2).
        2: eapply (KE 16777215%Z ti0 rest ESC ltac:(unfold CNT_MAX; lia) K2).
        all: cbn [scopes k depth W sb]; rewrite ESC; unfold endc_env;
             s2_close_mem; [exact OCL | exact OCR | exact IAL | exact IAR].
  Qed.
End ArrCont.
