(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard.
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

Section ObjBegin.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_obj_begin : forall (Q : machine_state -> Prop) (s : st)
      xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xs2 xs4 xs7 xs8 xs10 xs11 xt3 xt4 xt5
      j0 j8 j16 j24 j32 j40 j48 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    INV ObjBegin s ->
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; C8 (Z_to_bv 64 (e_THIS E)); CB 8 j72]
         (scopes s) fc m1 ->
    exit_k E Q ->
    ((depth s + 1 < 1024)%Z -> e_tok E (k s) = c_quote -> keya_k E Q s) ->
    evt usegs Q (S2R E 0x45ef4 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 (e_THIS E)) xa6 xa7 xs2 (Z_to_bv 64 (depth s)) xs4 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_SBUF E + sb s)) xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * k s)) xs10 xs11 xt3 xt4 xt5 (Z_to_bv 64 (e_TAPE E + 8 * W s)) F fc m1).
  Proof using OK.
    intros Q s xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xs2 xs4 xs7 xs8 xs10 xs11 xt3 xt4 xt5 j0 j8 j16 j24 j32 j40 j48 j56 j72 F fc m1 HI HM KX KK.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_depth _ _ _ _ HI) as [HD1 HD2].
    cbn [slackW] in HW. unfold MAXDEPTH in *.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    s2_open_mem HM.
    grun.
    if_cases K; zify_cond K.
    - s2_cur_mem ltac:(fun m =>
        pose proof (u8arr_store_ok usegs m (e_IA E) ias (depth s + 1) (wa (e_IA E + (depth s + 1))) IAA ltac:(lia) eq_refl) as SOK1).
      grun.
      zstep.
      change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
      s2_old_mem ltac:(fun m =>
        pose proof (u8arr_write usegs m (e_IA E) ias (depth s + 1) (Z_to_bv 8 0) IAA ltac:(lia)) as IAA').
      store_done.
      s2_cur_mem ltac:(fun m =>
        pose proof (u32arr_store_ok usegs m (e_OC E) ocs (2 * (depth s + 1)) (wa (e_OC E + 8 * (depth s + 1))) OCA ltac:(lia)
                      ltac:(unfold wa; f_equal; lia)) as SOK2).
      grun.
      zstep.
      s2_old_mem ltac:(fun m =>
        pose proof (u32arr_write usegs m (e_OC E) ocs (2 * (depth s + 1)) (Z_to_bv 64 (W s)) OCA ltac:(lia)) as OCA').
      replace (e_OC E + 4 * (2 * (depth s + 1)))%Z with (e_OC E + 8 * (depth s + 1))%Z in OCA' by lia.
      store_done.
      s2_cur_mem ltac:(fun m =>
        pose proof (u32arr_store_ok usegs m (e_OC E) _ (2 * (depth s + 1) + 1) (wa (e_OC E + 8 * (depth s + 1) + 4)) OCA' ltac:(rewrite upd_length; lia)
                      ltac:(unfold wa; f_equal; lia)) as SOK3).
      grun.
      zstep.
      s2_old_mem ltac:(fun m =>
        pose proof (u32arr_write usegs m (e_OC E) _ (2 * (depth s + 1) + 1) (Z_to_bv 64 0) OCA' ltac:(rewrite upd_length; lia)) as OCA'').
      replace (e_OC E + 4 * (2 * (depth s + 1) + 1))%Z with (e_OC E + 8 * (depth s + 1) + 4)%Z in OCA'' by lia.
      store_done.
      s2_cur_mem ltac:(fun m => pose proof (idx_read E OK m (k s) IDXA ltac:(lia)) as RD1;
                                pose proof (tok_read E OK m (k s) BUFRO HK) as RD2;
        pose proof (u32arr_store_ok usegs m (e_OC E) _ (2 * (depth s + 1) + 1) (wa (e_OC E + 8 * (depth s + 1) + 4)) OCA'' ltac:(rewrite !upd_length; lia)
                      ltac:(unfold wa; f_equal; lia)) as SOK4).
      grun.
      if_cases KQ; zify_cond KQ.
      +
        grun.
        zstep.
        s2_old_mem ltac:(fun m =>
          pose proof (u32arr_write usegs m (e_OC E) _ (2 * (depth s + 1) + 1) (Z_to_bv 64 1) OCA'' ltac:(rewrite !upd_length; lia)) as OCA3).
        replace (e_OC E + 4 * (2 * (depth s + 1) + 1))%Z with (e_OC E + 8 * (depth s + 1) + 4)%Z in OCA3 by lia.
        store_done.
        grun_to 0x46020%Z.
        replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z by lia.
        eapply (KK K KQ).
        s2_close_forget.
        * rewrite !upd_length. exact OCL.
        * apply oc_rel_upd_other; [apply oc_rel_upd_other|].
          -- replace (Z.to_nat (2 * (depth s + 1))) with (2 * (length (scopes s) + 1))%nat by lia.
             apply oc_rel_push; [exact OCR | lia].
          -- intros jj Hjj. lia.
          -- intros jj Hjj. lia.
        * rewrite upd_length. exact IAL.
        * replace (Z.to_nat (depth s + 1)) with (length (scopes s) + 1)%nat by lia.
          apply (ia_rel_push (scopes s) ias false (W s)); [exact IAR | lia].
        * forgets_tac.
      +
        grun_to 0x4bfd0%Z.
        eapply (KX 3%Z); [s2_errlit|]. s2_close_memx.
    -
      grun_to 0x4bfd0%Z.
      eapply (KX 4%Z); [s2_errlit|]. s2_close_memx.
  Qed.
End ObjBegin.
