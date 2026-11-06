(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa SjTape Zpj Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zwd.
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

Section StrEnd.
  Variable E : s2env.
  Hypothesis OK : env_ok E.

  Definition strendo_k (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)) : Prop :=
    forall xra xt0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xs11 xt4 xt5 xt6
           j0 j1 j2 j3 j4 j7 j8 j9 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; C8 (Z_to_bv 64 dpt); C8 (Z_to_bv 64 (e_IDX E + 4 * (kk + 1)));
                         CB 8 j7; CB 8 j8; CB 8 j9] sc fc m1 ->
      evt psegs Q (S2R E 0x3050c xra xt0 (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 (e_TAPE E + 8 * Wv)) (Z_to_bv 64 (e_THIS E)) xs1
                       xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7
                       (Z_to_bv 64 (e_SBUF E + sbv + 4)) xs9 xs10 xs11 (Z_to_bv 64 (e_SBUF E + sbv)) xt4 xt5 xt6 F fc m1).

  Lemma seg_str_end_o : forall (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)),
    (0 <= sbv)%Z -> (0 <= d < 2^31)%Z -> (sbv + d + 5 <= e_scap E)%Z -> Z.of_nat (length (e_sbs E)) = sbv ->
    (forall cb, Z.of_nat (length cb) = d -> lab_k (gapp E [] (srec d cb)) Q 0x30c48 (mkst (kk + 1) dpt Wv (sbv + d + 5) sc)) ->
    strendo_k Q kk dpt Wv sbv d sc.
  Proof using OK.
    intros Q kk dpt Wv sbv d sc HSB HD0 HSC GS KC. unfold strendo_k.
    intros xra xt0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xs11 xt4 xt5 xt6 j0 j1 j2 j3 j4 j7 j8 j9 F fc m1 HM.
    s2_env OK.
    s2_open_mem HM.
    do 4 zstep.
    replace (e_SBUF E + sbv + 4 + d - (e_SBUF E + sbv + 4))%Z with d by lia. rewrite (swrap32_small d) by lia.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    do 5 zstep.
    replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + (sbv + d + 5))%Z by lia.
    s2_cur_mem ltac:(fun m => destruct (timg_sbytes E _ _ m (sbv + 4) d TIMG ltac:(lia) ltac:(lia) ltac:(lia)) as (cb & HCL & HCB);
      eapply (tape_img_app_str E _ _ m d cb _ _ _ _ (e_SBUF E + sbv)%Z) in TIMG;
      [ | lia | exact NEWCH | exact NEWCH0 | exact NEWCH1 | exact NEWCH2
        | replace (e_SBUF E + sbv + 4)%Z with (e_SBUF E + (sbv + 4))%Z by lia; exact HCB | exact HCL | exact NEWCH3
        | rewrite u64_small by lia; reflexivity
        | apply (str_byte_k d 8); lia | apply (str_byte_k d 16); lia | apply (str_byte_k d 24); lia
        | lia | lia | lia ]).
    eapply (KC (map bv_unsigned cb)); [rewrite length_map; exact HCL|]. cbn [scopes].
    eapply MEMJ_of_MEMI; [s2_close_mem0 | reflexivity ..].
  Qed.

  Definition strenda_k (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)) : Prop :=
    forall xra xt0 xt1 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6
           j0 j1 j2 j3 j4 j7 j8 j9 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; C8 (Z_to_bv 64 dpt); C8 (Z_to_bv 64 (e_IDX E + 4 * (kk + 1)));
                         CB 8 j7; CB 8 j8; CB 8 j9] sc fc m1 ->
      evt psegs Q (S2R E 0x316dc xra xt0 xt1 (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 (e_THIS E)) xs1
                       (Z_to_bv 64 (e_SBUF E + sbv + 4)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7
                       xs8 xs9 xs10 xs11 (Z_to_bv 64 (e_TAPE E + 8 * Wv)) (Z_to_bv 64 (e_SBUF E + sbv)) xt5 xt6 F fc m1).

  Lemma seg_str_end_a : forall (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)),
    (0 <= sbv)%Z -> (0 <= d < 2^31)%Z -> (sbv + d + 5 <= e_scap E)%Z -> Z.of_nat (length (e_sbs E)) = sbv ->
    (forall cb, Z.of_nat (length cb) = d -> lab_k (gapp E [] (srec d cb)) Q 0x30fb0 (mkst (kk + 1) dpt Wv (sbv + d + 5) sc)) ->
    strenda_k Q kk dpt Wv sbv d sc.
  Proof using OK.
    intros Q kk dpt Wv sbv d sc HSB HD0 HSC GS KC. unfold strenda_k.
    intros xra xt0 xt1 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 j0 j1 j2 j3 j4 j7 j8 j9 F fc m1 HM.
    s2_env OK.
    s2_open_mem HM.
    do 4 zstep.
    replace (e_SBUF E + sbv + 4 + d - (e_SBUF E + sbv + 4))%Z with d by lia. rewrite (swrap32_small d) by lia.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    do 5 zstep.
    replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + (sbv + d + 5))%Z by lia.
    s2_cur_mem ltac:(fun m => destruct (timg_sbytes E _ _ m (sbv + 4) d TIMG ltac:(lia) ltac:(lia) ltac:(lia)) as (cb & HCL & HCB);
      eapply (tape_img_app_str E _ _ m d cb _ _ _ _ (e_SBUF E + sbv)%Z) in TIMG;
      [ | lia | exact NEWCH | exact NEWCH0 | exact NEWCH1 | exact NEWCH2
        | replace (e_SBUF E + sbv + 4)%Z with (e_SBUF E + (sbv + 4))%Z by lia; exact HCB | exact HCL | exact NEWCH3
        | rewrite u64_small by lia; reflexivity
        | apply (str_byte_k d 8); lia | apply (str_byte_k d 16); lia | apply (str_byte_k d 24); lia
        | lia | lia | lia ]).
    eapply (KC (map bv_unsigned cb)); [rewrite length_map; exact HCL|]. cbn [scopes].
    eapply MEMJ_of_MEMI; [s2_close_mem0 | reflexivity ..].
  Qed.
End StrEnd.
