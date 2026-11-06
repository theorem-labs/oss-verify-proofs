(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_stage2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.

Section KeyEnd2.
  Variable E : s2env.

  Definition keyend2_k (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xs11 xt5 xt6
           j0 j1 j2 j3 j4 j6 j8 j9 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; C8 (Z_to_bv 64 dpt); CB 8 j6;
                         C8 (Z_to_bv 64 (e_TAPE E + 8 * Wv)); CB 8 j8; CB 8 j9] sc fc m1 ->
      evt psegs Q (S2R E 0x43510 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) xs9 xs10 xs11
                       (Z_to_bv 64 (e_IDX E + 4 * kk)) (Z_to_bv 64 (e_SBUF E + sbv)) xt5 xt6 F fc m1).

End KeyEnd2.

Section ObjField.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Definition keyend_k (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xs11 xt5 xt6
           j0 j1 j2 j3 j4 j6 j8 j9 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; C8 (Z_to_bv 64 dpt); CB 8 j6;
                         C8 (Z_to_bv 64 (e_TAPE E + 8 * Wv)); CB 8 j8; CB 8 j9] sc fc m1 ->
      evt psegs Q (S2R E 0x434ec xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 (Z_to_bv 64 (e_SBUF E + sbv + 4)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) xs9 xs10 xs11
                       (Z_to_bv 64 (e_IDX E + 4 * kk)) (Z_to_bv 64 (e_SBUF E + sbv)) xt5 xt6 F fc m1).

  Definition objval_k (Q : machine_state -> Prop) (pc : Z) (s : st) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa1 xa2 xa4 xa7 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6
           j0 j1 j2 j3 j4 j6 j8 j9 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; C8 (Z_to_bv 64 (depth s)); CB 8 j6;
                         C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); CB 8 j8; CB 8 j9] (scopes s) fc m1 ->
      evt psegs Q (S2R E pc xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 (Z_to_bv 64 (e_tok E (k s))) xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4
                       (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xs3
                       (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 (Z_to_bv 64 (e_SBUF E + sb s + -1)) xs9 xs10 (Z_to_bv 64 (e_SBUF E + sb s))
                       xt3 xt4 xt5 xt6 F fc m1).

  Definition objstr_k (Q : machine_state -> Prop) (s : st) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa2 xa4 xa7 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6
           j0 j1 j2 j3 j4 j6 j8 j9 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; C8 (Z_to_bv 64 (depth s)); CB 8 j6;
                         C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); CB 8 j8; CB 8 j9] (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x43610 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 (Z_to_bv 64 (e_tok E (k s))) (Z_to_bv 64 34) xa2 (Z_to_bv 64 (e_off E (k s))) xa4
                       (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xa7 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xs3
                       (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 (Z_to_bv 64 (e_SBUF E + sb s + -1)) xs9 xs10 (Z_to_bv 64 (e_SBUF E + sb s))
                       xt3 xt4 xt5 xt6 F fc m1).

  Lemma objf_empty_tail : forall (Q : machine_state -> Prop) (s : st) (oc a0z a2z a3z : Z) c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
      xra xt0 xt1 xt2 xs1 xa1 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    (oc = 91 \/ oc = 123)%Z -> a0z = tword (oc + 2) (W s) -> a2z = (oc * 2^56)%Z -> a3z = ((W s + 2) * 2^32)%Z ->
    Z.of_nat (length (e_tws E)) = W s -> (W s + 2 < 2^32)%Z ->
    (W s + 2 <= e_tcap E)%Z -> (0 <= W s)%Z ->
    MEMI E (e_nxt0 E) [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] (scopes s) fc m1 ->
    csize c0 = 8%nat -> csize c1 = 8%nat -> csize c2 = 8%nat -> csize c3 = 8%nat -> csize c4 = 8%nat ->
    csize c5 = 8%nat -> csize c6 = 8%nat -> csize c7 = 8%nat -> csize c8 = 8%nat -> csize c9 = 8%nat ->
    lab_k (empty_env E oc (W s)) Q 0x4434c (mkst (k s) (depth s) (W s + 2) (sb s) (scopes s)) ->
    evt psegs Q (S2ML E 0x435f8 xra xt0 xt1 xt2 xs1 (Z_to_bv 64 a0z) xa1 (Z_to_bv 64 a2z) (Z_to_bv 64 a3z) xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6
                      (depth s) (k s) (W s) (sb s) F fc m1).
  Proof using OK.
    intros Q s oc a0z a2z a3z c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 xra xt0 xt1 xt2 xs1 xa1 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 F fc m1
           HOC -> -> -> GL HW32 HW HW0 HM E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 KC.
    s2_env OK.
    pose proof (MEMJ_of_MEMI _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM E0 E1 E2 E3 E4 E5 E6 E7 E8 E9) as HMJ. clear HM.
    s2_open_memj HMJ.
    pose proof (tape_store_ok E m1 (W s) TAPEW ltac:(lia)) as SOK1.
    zstep. zstep. zstep. rewrite (empty_word_machine (W s) oc) by lia. s2_note_store. store_done.
    s2_cur_mem ltac:(fun m => pose proof (tape_store_ok E m (W s + 1) TAPEW ltac:(lia)) as SOK2).
    replace (e_TAPE E + 8 * (W s + 1))%Z with (e_TAPE E + 8 * W s + 8)%Z in SOK2 by lia.
    zstep. s2_note_store. store_done. zstep. zstep.
    replace (e_TAPE E + 8 * W s + 16)%Z with (e_TAPE E + 8 * (W s + 2))%Z by lia.
    s2_cur_mem ltac:(fun m =>
      apply (tape_img_app2 E _ _ m (cword oc (W s + 2) 0) (tword (oc + 2) (W s)) (e_TAPE E + 8 * W s)%Z (e_TAPE E + 8 * W s + 8)%Z OK) in TIMG;
      [ | exact NEWCH | exact NEWCH0 | lia | lia | lia | apply cword_range; lia | apply tword_range; lia ]).
    eapply KC. cbn [scopes]. s2_close_memj0.
  Qed.

  Lemma seg_key_end : forall (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)),
    (0 <= sbv)%Z -> (0 <= d < 2^31)%Z -> (sbv + d + 5 <= e_scap E)%Z -> Z.of_nat (length (e_sbs E)) = sbv ->
    (forall cb, Z.of_nat (length cb) = d -> keyend2_k (gapp E [] (srec d cb)) Q kk dpt Wv sbv d sc) ->
    keyend_k Q kk dpt Wv sbv d sc.
  Proof using OK.
    intros Q kk dpt Wv sbv d sc HSB HD0 HSC GS KC. unfold keyend_k.
    intros xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xs11 xt5 xt6
           j0 j1 j2 j3 j4 j6 j8 j9 F fc m1 HM.
    s2_env OK.
    s2_open_mem HM.
    zstep. zstep. zstep. zstep.
    replace (e_SBUF E + sbv + 4 + d - (e_SBUF E + sbv + 4))%Z with d by lia. rewrite (swrap32_small d) by lia.
    pose proof (sbuf_store_ok_at E m1 sbv (wa (e_SBUF E + sbv)) SBUFW ltac:(lia) eq_refl) as SOK0.
    zstep. s2norm. s2_note_store. store_done.
    s2_cur_mem ltac:(fun m => pose proof (sbuf_store_ok_at E m (sbv + 1) (wa (e_SBUF E + sbv + 1)) SBUFW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK1).
    zstep. s2norm. s2_note_store. store_done.
    s2_cur_mem ltac:(fun m => pose proof (sbuf_store_ok_at E m (sbv + 2) (wa (e_SBUF E + sbv + 2)) SBUFW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK2).
    zstep. s2norm. s2_note_store. store_done.
    s2_cur_mem ltac:(fun m => pose proof (sbuf_store_ok_at E m (sbv + 3) (wa (e_SBUF E + sbv + 3)) SBUFW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK3).
    zstep. s2norm. s2_note_store. store_done.
    s2_cur_mem ltac:(fun m => pose proof (sbuf_store_ok_at E m (sbv + 4 + d) (wa (e_SBUF E + sbv + 4 + d)) SBUFW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK4).
    zstep. s2norm. s2_note_store. store_done.
    s2_cur_mem ltac:(fun m => destruct (timg_sbytes E _ _ m (sbv + 4) d TIMG ltac:(lia) ltac:(lia) ltac:(lia)) as (cb & HCL & HCB);
      eapply (tape_img_app_str E _ _ m d cb _ _ _ _ (e_SBUF E + sbv)%Z) in TIMG;
      [ | lia | exact NEWCH | exact NEWCH0 | exact NEWCH1 | exact NEWCH2
        | replace (e_SBUF E + sbv + 4)%Z with (e_SBUF E + (sbv + 4))%Z by lia; exact HCB | exact HCL | exact NEWCH3
        | rewrite u64_small by lia; reflexivity
        | apply (str_byte_k d 8); lia | apply (str_byte_k d 16); lia | apply (str_byte_k d 24); lia
        | lia | lia | lia ]).
    eapply (KC (map bv_unsigned cb)); [rewrite length_map; exact HCL|]. s2_close_mem0.
  Qed.

  Lemma seg_key_disp : forall (Q : machine_state -> Prop) (kk dpt Wv sbv d : Z) (sc : list (bool * Z)),
    let sF := mkst (kk + 1) dpt Wv (sbv + d + 5) sc in
    let sV := mkst (kk + 2) dpt Wv (sbv + d + 5) sc in
    INV ObjField sF -> (0 <= sbv)%Z -> (0 <= d)%Z -> (sbv + d + 5 <= e_scap E)%Z -> Z.of_nat (length (e_tws E)) = Wv ->
    exit_k E Q ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) = c_quote -> objstr_k Q sV) ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) = c_lbrack -> e_tok E (kk + 3) = c_rbrack ->
       lab_k (empty_env E 91 Wv) Q 0x4434c (mkst (kk + 4) dpt (Wv + 2) (sbv + d + 5) sc)) ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) = c_lbrace -> e_tok E (kk + 3) = c_rbrace ->
       lab_k (empty_env E 123 Wv) Q 0x4434c (mkst (kk + 4) dpt (Wv + 2) (sbv + d + 5) sc)) ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) = c_lbrack -> e_tok E (kk + 3) <> c_rbrack ->
       arrbegin_k E Q (mkst (kk + 3) dpt Wv (sbv + d + 5) sc)) ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) = c_lbrace -> e_tok E (kk + 3) <> c_rbrace ->
       lab_k E Q 0x3f794 (mkst (kk + 3) dpt Wv (sbv + d + 5) sc)) ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) <> c_quote -> e_tok E (kk + 2) <> c_lbrack -> e_tok E (kk + 2) <> c_lbrace ->
       (e_tok E (kk + 2) <= 57)%Z -> objval_k Q 0x43890 sV) ->
    (e_tok E (kk + 1) = c_colon -> e_tok E (kk + 2) <> c_quote -> e_tok E (kk + 2) <> c_lbrack -> e_tok E (kk + 2) <> c_lbrace ->
       (57 < e_tok E (kk + 2))%Z -> objval_k Q 0x43b94 sV) ->
    keyend2_k E Q kk dpt Wv sbv d sc.
  Proof using OK.
    intros Q kk dpt Wv sbv d sc sF sV HI HSB HD0 HSC GL KX KS KEA KEO KAB KOB KN KA. unfold keyend2_k. subst sF sV.
    intros xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xs11 xt5 xt6
           j0 j1 j2 j3 j4 j6 j8 j9 F fc m1 HM.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_depth_range _ _ _ _ HI) as HD.
    cbn [k depth W sb scopes slackW] in *.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    s2_open_mem HM.

    pose proof (off_bound E OK (kk + 1) HK) as HO1. pose proof (tok_range E OK (kk + 1)) as HT1.
    s2_cur_mem ltac:(fun m =>
      pose proof (idx_read E OK m (kk + 1) IDXA ltac:(lia)) as RD1;
      pose proof (tok_read E OK m (kk + 1) BUFRO HK) as RD2).
    replace (e_IDX E + 4 * (kk + 1))%Z with (e_IDX E + 4 * kk + 4)%Z in RD1 by lia.
    zstep. s2norm. zstep. zstep. s2norm. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    2:{ zstep. zstep. zstep. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..]. }

    assert (HK1 : (kk + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK| rewrite K; lia]).
    pose proof (off_bound E OK (kk + 2) ltac:(lia)) as HO2. pose proof (tok_range E OK (kk + 2)) as HT2.
    s2_cur_mem ltac:(fun m =>
      pose proof (idx_read E OK m (kk + 2) IDXA ltac:(lia)) as RD3;
      pose proof (tok_read E OK m (kk + 2) BUFRO ltac:(lia)) as RD4).
    replace (e_IDX E + 4 * (kk + 2))%Z with (e_IDX E + 4 * kk + 8)%Z in RD3 by lia.
    zstep. s2norm. zstep. zstep. s2norm. zstep. zstep. zstep. zstep.
    replace (e_IDX E + 4 * kk + 12)%Z with (e_IDX E + 4 * (kk + 2 + 1))%Z by lia.
    replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + (sbv + d + 5))%Z by lia.
    if_cases K0; zify_cond K0.
    -
      replace (e_SBUF E + sbv + 4 + d)%Z with (e_SBUF E + (sbv + d + 5) + -1)%Z by lia.
      eapply (KS K K0). cbn [scopes depth W]. s2_close_mem0.
    - pose proof (inv_W _ _ _ _ HI) as HW'. cbn [slackW k W] in HW'.
      zstep. zstep.
      if_cases K1; zify_cond K1.
      +
        assert (HK2 : (kk + 2 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K1; lia]).
        pose proof (off_bound E OK (kk + 3) ltac:(lia)) as HO3. pose proof (tok_range E OK (kk + 3)) as HT3.
        s2_cur_mem ltac:(fun m =>
          pose proof (idx_read E OK m (kk + 3) IDXA ltac:(lia)) as RD5;
          pose proof (tok_read E OK m (kk + 3) BUFRO ltac:(lia)) as RD6).
        replace (e_IDX E + 4 * (kk + 3))%Z with (e_IDX E + 4 * (kk + 2 + 1))%Z in RD5 by lia.
        zstep. s2norm. zstep. zstep. s2norm. zstep. zstep.
        if_cases K2; zify_cond K2.
        *
          assert (HK3 : (kk + 3 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K2; lia]).
          do 14 zstep.
          replace (e_IDX E + 4 * kk + 16)%Z with (e_IDX E + 4 * (kk + 4))%Z by lia.
          eapply (objf_empty_tail Q (mkst (kk + 4) dpt Wv (sbv + d + 5) sc) 91); cbn [k depth W sb scopes];
            [left; reflexivity | change 6701356245527298048%Z with (93 * 72057594037927936)%Z; apply close_word_machine; lia | reflexivity | apply next2_machine; lia
             | exact GL | lia | lia | lia | s2_close_mem0 | reflexivity .. | exact (KEA K K1 K2)].
        *
          zstep.
          replace (e_IDX E + 4 * (kk + 2 + 1))%Z with (e_IDX E + 4 * (kk + 3))%Z by lia.
          eapply (KAB K K1 K2). cbn [scopes W].
          eapply (MEMI_forget8 E _ [_; _; _; _; _] _ [_; _; _; _]); cycle 1; [s2_close_mem0 | reflexivity].
      + zstep. zstep.
        if_cases K3; zify_cond K3.
        *
          zstep. zstep.
          replace (e_SBUF E + sbv + 4 + d)%Z with (e_SBUF E + (sbv + d + 5) + -1)%Z by lia.
          replace (e_IDX E + 4 * (kk + 3))%Z with (e_IDX E + 4 * (kk + 2 + 1))%Z by lia.
          if_cases K4; zify_cond K4.
          -- eapply (KA K K0 K1 K3 ltac:(lia)). cbn [scopes depth W]. s2_close_mem0.
          -- eapply (KN K K0 K1 K3 ltac:(lia)). cbn [scopes depth W]. s2_close_mem0.
        *
          assert (HK2 : (kk + 2 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K3; lia]).
          pose proof (off_bound E OK (kk + 3) ltac:(lia)) as HO3. pose proof (tok_range E OK (kk + 3)) as HT3.
          s2_cur_mem ltac:(fun m =>
            pose proof (idx_read E OK m (kk + 3) IDXA ltac:(lia)) as RD5;
            pose proof (tok_read E OK m (kk + 3) BUFRO ltac:(lia)) as RD6).
          replace (e_IDX E + 4 * (kk + 3))%Z with (e_IDX E + 4 * (kk + 2 + 1))%Z in RD5 by lia.
          zstep. s2norm. zstep. zstep. s2norm. zstep. zstep.
          if_cases K2; zify_cond K2.
          --
             replace (e_IDX E + 4 * (kk + 2 + 1))%Z with (e_IDX E + 4 * (kk + 3))%Z by lia.
             do 9 zstep.
             if_false. zstep.
             eapply (KOB K K3 K2). cbn [scopes].
             eapply MEMJ_of_MEMI; [s2_close_mem0 | reflexivity ..].
          --
             assert (HK3 : (kk + 3 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [lia| rewrite K2; lia]).
             do 15 zstep.
             replace (e_IDX E + 4 * kk + 16)%Z with (e_IDX E + 4 * (kk + 4))%Z by lia.
             eapply (objf_empty_tail Q (mkst (kk + 4) dpt Wv (sbv + d + 5) sc) 123); cbn [k depth W sb scopes];
               [right; reflexivity | change 9007199254740992000%Z with (125 * 72057594037927936)%Z; apply close_word_machine; lia | reflexivity | apply next2_machine; lia
                | exact GL | lia | lia | lia | s2_close_mem0 | reflexivity .. | exact (KEO K K3 K2)].
  Qed.
End ObjField.
