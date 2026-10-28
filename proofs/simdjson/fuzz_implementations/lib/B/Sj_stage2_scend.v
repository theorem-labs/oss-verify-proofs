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

Section ScopeEnd.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_scope_end : forall (Q : machine_state -> Prop) (s : st)
      xra xt0 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    INV ScopeEnd s ->
    (forall sc, scopes s = [sc] -> docend_k E Q (mkst (k s) (depth s - 1) (W s) (sb s) [])) ->
    (forall sc ti rest, scopes s = sc :: (true, ti) :: rest -> arrcont_k E Q (mkst (k s) (depth s - 1) (W s) (sb s) ((true, ti) :: rest))) ->
    (forall sc ti rest, scopes s = sc :: (false, ti) :: rest -> objcont_k E Q (mkst (k s) (depth s - 1) (W s) (sb s) ((false, ti) :: rest))) ->
    evt bsegs Q (S2R E 0xdca6c xra xt0 (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_IDX E + 4 * k s)) (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_THIS E)) xa7 (Z_to_bv 64 (e_SBUF E + sb s)) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    intros Q s xra xt0 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j192 j200 j272 j288 j304 F fc m1
 HM.
    intros HI KD KA KO.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_depth _ _ _ _ HI) as [HD1 HD2].
    pose proof (inv_kind _ _ _ _ HI) as HKD.
    cbn [k depth W sb scopes slackW kind_ok] in *. unfold MAXDEPTH in *.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    destruct (scopes s) as [|[b0 ti0] rest] eqn:ESC; [congruence|]. clear HKD.
    cbn [length] in HD1.
    s2_open_mem HM.
    grun.
    if_cases K; zify_cond K.
    -
      assert (ER : rest = []) by (destruct rest; [reflexivity| cbn [length] in HD1; lia]). subst rest.
      grun_to 0xcb7f0%Z.
      eapply (KD _ eq_refl). cbn [k W scopes].
      s2_close_mem; [exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil].
    -
      destruct rest as [|[b1 ti1] rest']; [cbn [length] in HD1; lia|]. cbn [length] in HD1.
      pose proof (ia_rel_top _ _ _ _ (ia_rel_pop _ _ _ IAR)) as TOP.
      grun_to 0xdcacc%Z.
      s2_cur_mem ltac:(fun m => pose proof (u8arr_read bsegs m (e_IA E) ias (depth s - 1) _ (wa (e_IA E + (depth s + -1))) IAA
                  ltac:(replace (Z.to_nat (depth s - 1)) with (length rest' + 1)%nat by lia; exact TOP) ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD3).
      destruct b1; grun.
      +
        if_false.
        replace (depth s + -1)%Z with (depth s - 1)%Z in * by lia.
        eapply (KA _ _ _ eq_refl). cbn [scopes k depth W sb].
        s2_close_mem; [exact OCL | exact (oc_rel_pop _ _ _ OCR) | exact IAL | exact (ia_rel_pop _ _ _ IAR)].
      +
        if_true.
        replace (depth s + -1)%Z with (depth s - 1)%Z in * by lia.
        eapply (KO _ _ _ eq_refl). cbn [scopes k depth W sb].
        s2_close_mem; [exact OCL | exact (oc_rel_pop _ _ _ OCR) | exact IAL | exact (ia_rel_pop _ _ _ IAR)].
  Qed.
End ScopeEnd.
