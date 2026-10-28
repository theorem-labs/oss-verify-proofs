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

Section ObjCont.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_obj_cont : forall (Q : machine_state -> Prop) (s : st)
      xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6
      j0 j8 j16 j24 j48 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    INV ObjCont s ->
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); CB 8 j48; C8 (Z_to_bv 64 (e_SBUF E + sb s)); C8 (Z_to_bv 64 (e_THIS E)); CB 8 j72]
         (scopes s) fc m1 ->
    Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (e_tok E (k s) = c_comma -> e_tok E (k s + 1) = c_quote -> keyb_k E Q (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    (forall cv ti rest, scopes s = (false, ti) :: rest -> (0 <= cv <= CNT_MAX)%Z -> e_tok E (k s) = c_rbrace ->
       scopeend_k (endc_env E 123 ti (W s) cv) Q (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s))) ->
    evt usegs Q (S2R E 0x4e4c4 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * k s)) xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK.
    intros Q s xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j48 j72 F fc m1 HI HM GLT KX KK KE.
    pose proof (inv_k _ _ _ _ HI) as HK.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (n_bound E OK) as HN. s2_env OK.
    s2_open_mem HM.
    pose proof (idx_read E OK m1 (k s) IDXA ltac:(lia)) as RD1.
    pose proof (tok_read E OK m1 (k s) BUFRO HK) as RD2.
    grun.
    if_cases K; zify_cond K.
    -
      pose proof (inv_depth_range _ _ _ _ HI) as HD.
      assert (HK1 : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK| rewrite K; lia]).
      destruct (nth_error_ex ocs (Z.to_nat (2 * depth s + 1)) ltac:(lia)) as [cnt Hcnt].
      pose proof (u32arr_read usegs m1 (e_OC E) ocs (2 * depth s + 1) cnt (wa (e_OC E + 8 * depth s + 4)) OCA Hcnt ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as RD3.
      pose proof (u32arr_store_ok usegs m1 (e_OC E) ocs (2 * depth s + 1) (wa (e_OC E + 8 * depth s + 4)) OCA ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as SOK.
      grun.
      zstep.
      pose proof (u32arr_write usegs m1 (e_OC E) ocs (2 * depth s + 1) (Z_to_bv 64 (bv_unsigned (sx32 cnt) + 1)) OCA ltac:(lia)) as OCA'.
      replace (e_OC E + 4 * (2 * depth s + 1))%Z with (e_OC E + 8 * depth s + 4)%Z in OCA' by lia.
      store_done.
      s2_cur_mem ltac:(fun m => pose proof (idx_read E OK m (k s + 1) IDXA ltac:(lia)) as RD4;
                                pose proof (tok_read E OK m (k s + 1) BUFRO ltac:(lia)) as RD5).
      replace (e_IDX E + 4 * (k s + 1))%Z with (e_IDX E + 4 * k s + 4)%Z in RD4 by lia.
      pose proof (off_bound E OK (k s + 1) ltac:(lia)) as HO1. pose proof (tok_range E OK (k s + 1)) as HT1.
      grun.
      if_cases KQ; zify_cond KQ.
      +
        grun_to 0x4be14%Z.
        eapply (KX 3%Z); [s2_errlit|].
        s2_close_memx.
      +
        replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
        eapply (KK K KQ). cbn [scopes k depth W sb].
        s2_close_forget; [rewrite upd_length; exact OCL | | exact IAL | exact IAR | forgets_tac].
        apply oc_rel_upd_other; [exact OCR|]. intros jj Hjj. lia.
    -
      grun.
      if_cases K2; zify_cond K2.
      +
        grun_to 0x4be14%Z.
        eapply (KX 3%Z); [s2_errlit|].
        s2_close_memx.
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
        pose proof (u32arr_read usegs m1 (e_OC E) ocs (2 * depth s) (Z_to_bv 64 ti0) (wa (e_OC E + 8 * depth s)) OCA TOP ltac:(lia)
                      ltac:(unfold wa; f_equal; lia)) as RD3.
        grun.
        destruct (nth_error_ex ocs (Z.to_nat (2 * depth s + 1)) ltac:(lia)) as [cnt Hcnt].
        s2_cur_mem ltac:(fun m => pose proof (u32arr_read usegs m (e_OC E) ocs (2 * depth s + 1) cnt (wa (e_OC E + 8 * depth s + 4)) OCA Hcnt ltac:(lia)
                      ltac:(unfold wa; f_equal; lia)) as RD4).
        grun.
        pose proof (bv_unsigned_in_range 64 (sx32 cnt)) as HCR. unfold bv_modulus in HCR. cbn in HCR.
        if_cases KC; [ zify_cond KC | gstep ].

        all: grun_to 0x4e624%Z.
        1: zstep; gnorm; s2_endc_patch 123%Z ti0 (bv_unsigned (sx32 cnt)); s2_endc_close 123%Z ti0.
        2: zstep; gnorm; s2_endc_patch 123%Z ti0 16777215%Z; s2_endc_close 123%Z ti0.
        all: grun_to 0x4eb04%Z.
        all: replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
        all: replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z by lia.
        1: eapply (KE (bv_unsigned (sx32 cnt)) ti0 rest ESC ltac:(unfold CNT_MAX; lia) K2).
        2: eapply (KE 16777215%Z ti0 rest ESC ltac:(unfold CNT_MAX; lia) K2).
        all: cbn [scopes k depth W sb]; rewrite ESC;
             s2_close_forget; [exact OCL | exact OCR | exact IAL | exact IAR | forgets_tac].
  Qed.
End ObjCont.
