(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q FP ImageA.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa SjTape Zpj Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Zpm Zwd Z103 Z104 Zwk Z107 Zwm Zxc Zxd Zxe Zxf
  Zyi Zyj Zyk Zyn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Definition cli_got_nothrow (m : mem) : Prop := ro_cells bsegs m 0x1187d8 [C8 (Z_to_bv 64 0x2ca50)].

Section NumR0.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.

  Lemma seg_numr_pro1 : forall (Q : machine_state -> Prop), rpro_new_k E Q ->
    forall xra xt0 xt1 xt2 xa0 xa4 xa5 xa6 xa7 xs4 xs7 xt3 xt5 xt6
            j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    cli_got_nothrow m1 ->
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_SBUF E)); C8 (Z_to_bv 64 (3)); CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xa01b4 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (SHA (e_BUF E + e_off E 0))) (Z_to_bv 64 (3)) (Z_to_bv 64 (e_IDX E + 4)) xa4 xa5 xa6 xa7 (Z_to_bv 64 (SHA (e_IDX E))) (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (e_TAPE E)) (Z_to_bv 64 (e_THIS E + 56)) xs7 (Z_to_bv 64 (e_BUF E + e_off E 0)) (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_IDX E)) xt3 (Z_to_bv 64 (SHA (e_THIS E + 56))) xt5 xt6 F fc m1).
  Proof using OK SHZ.
    intros Q KN. intros until m1. intros GOT HM.
    unfold cli_got_nothrow in GOT.
    pose proof (off_bound E OK 0 ltac:(pose proof (n_bound E OK); lia)) as HO.
    s2_env OK. s2_open_mem HM.
    ngrun_to 0xa01b8%Z.
    s2_cur_mem ltac:(fun m => pose proof (idx_read E OK m 0 IDXA ltac:(pose proof (n_bound E OK); lia)) as RD0).
    replace (e_IDX E + 4 * 0)%Z with (e_IDX E) in RD0 by lia.
    ngrun_to 0xf32c8%Z.
    kapply KN. s2_close_mem0.
  Qed.

  Lemma seg_numr_pro2 : forall (Q : machine_state -> Prop) CP, (0 < CP < 2^47)%Z -> rpro_memcpy_k E Q CP -> rpro_ret1_k E Q CP.
  Proof using OK SHZ.
    intros Q CP HCP KM. unfold rpro_ret1_k. intros until m1. intros HM.
    pose proof (off_bound E OK 0 ltac:(pose proof (n_bound E OK); lia)) as HO.
    s2_env OK. s2_open_mem HM.
    pose proof (idx_read E OK m1 0 IDXA ltac:(pose proof (n_bound E OK); lia)) as RD0.
    replace (e_IDX E + 4 * 0)%Z with (e_IDX E) in RD0 by lia.
    ngrun. if_cases KZ; zify_cond KZ; try (exfalso; lia).
    ngrun_to 0x667bc%Z.
    kapply KM. s2_close_mem0.
  Qed.

  Lemma seg_numr_pro3 : forall (Q : machine_state -> Prop) CP, (0 < CP < 2^47)%Z -> rpro_memset_k E Q CP -> rpro_ret2_k E Q CP.
  Proof using OK SHZ.
    intros Q CP HCP KM. unfold rpro_ret2_k. intros until m1. intros HM.
    pose proof (off_bound E OK 0 ltac:(pose proof (n_bound E OK); lia)) as HO.
    s2_env OK. s2_open_mem HM.
    pose proof (idx_read E OK m1 0 IDXA ltac:(pose proof (n_bound E OK); lia)) as RD0.
    replace (e_IDX E + 4 * 0)%Z with (e_IDX E) in RD0 by lia.
    ngrun_to 0x66c58%Z.
    kapply KM. s2_close_mem0.
  Qed.
End NumR0.
