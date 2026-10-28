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

Section ArrBegin.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_arr_begin : forall (Q : machine_state -> Prop) (s : st)
      xra xt1 xt2 xa1 xa2 xa3 xa4 xa5 xs7 xs9 xt3 xt4 xt5 xt6
      j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j168 j176 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j168; CB 8 j176; CB 8 j208; CB 8 j272]
         (scopes s) fc m1 ->
    INV ArrBegin s ->
    exit_k E Q ->
    ((depth s + 1 < 1024)%Z -> arrvalue_k E Q (mkst (k s) (depth s + 1) (W s + 1) (sb s) ((true, W s) :: scopes s))) ->
    evt asegs Q (S2R E 0xc5cb8 xra (Z_to_bv 64 (SHA (e_THIS E + 88))) xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_IDX E + 4 * k s)) xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_THIS E + 88)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_SBUF E + sb s)) xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (e_TAPE E + 8 * W s)) xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    intros Q s xra xt1 xt2 xa1 xa2 xa3 xa4 xa5 xs7 xs9 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j168 j176 j208 j272 F fc m1 HM.
    intros HI KX KV.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_depth _ _ _ _ HI) as [HD1 HD2].
    cbn [slackW] in HW. unfold MAXDEPTH in *.
    pose proof (n_bound E OK) as HN. s2_env OK.
    s2_open_mem HM.
    grun.
    if_cases K; zify_cond K.
    -
      grun_to 0xcb1dc%Z.
      eapply (KX 4%Z); [s2_errlit|]. s2_close_memx.
    - pose proof (u8arr_store_ok asegs m1 (e_IA E) ias (depth s + 1) (wa (e_IA E + (depth s + 1))) IAA ltac:(lia) eq_refl) as SOK1.
      grun.
      zstep.
      change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1].
      pose proof (u8arr_write asegs m1 (e_IA E) ias (depth s + 1) (Z_to_bv 8 1) IAA ltac:(lia)) as IAA'.
      store_done.
      s2_cur_mem ltac:(fun m =>
        pose proof (u32arr_store_ok asegs m (e_OC E) ocs (2 * (depth s + 1)) (wa (e_OC E + 8 * (depth s + 1))) OCA ltac:(lia)
                      ltac:(unfold wa; f_equal; lia)) as SOK2).
      grun.
      zstep.
      s2_old_mem ltac:(fun m =>
        pose proof (u32arr_write asegs m (e_OC E) ocs (2 * (depth s + 1)) (Z_to_bv 64 (W s)) OCA ltac:(lia)) as OCA').
      replace (e_OC E + 4 * (2 * (depth s + 1)))%Z with (e_OC E + 8 * (depth s + 1))%Z in OCA' by lia.
      store_done.
      grun_to 0xc5df0%Z.
      replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z by lia.
      eapply (KV ltac:(lia)). cbn [scopes k depth W sb].
      s2_close_mem.
      + rewrite !upd_length. exact OCL.
      + replace (Z.to_nat (2 * (depth s + 1))) with (2 * (length (scopes s) + 1))%nat by lia.
        apply oc_rel_push; [exact OCR | lia].
      + rewrite upd_length. exact IAL.
      + replace (Z.to_nat (depth s + 1)) with (length (scopes s) + 1)%nat by lia.
        apply (ia_rel_push (scopes s) ias true (W s)); [exact IAR | lia].
  Qed.
End ArrBegin.
