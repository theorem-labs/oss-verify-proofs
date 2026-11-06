(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_stage2_defs Sj_tables Sj_stage2_auto Sj_stage2_auto2 Sj_stage2_hex4 Sj_stage2_entry.
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
Local Ltac s2_store_done_wr ::= s2_store_done_wr_v2.

Ltac lstep :=
  zstep;
  match goal with |- context [Z_to_le_bytes 8 ?lit] => change (Z_to_le_bytes 8 lit) with (le8 (Z_to_bv 64 lit)) end;
  mem_after_store_fast.

Section RootStr.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).

  Notation RSH xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 p d F fc m :=
    (S2R E 0x3e910 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
         xs2 (Z_to_bv 64 (e_BUF E + p)) (Z_to_bv 64 56320) (Z_to_bv 64 1) (Z_to_bv 64 23669) (Z_to_bv 64 55296)
         (Z_to_bv 64 (e_SBUF E + 4 + d)) (Z_to_bv 64 92) (Z_to_bv 64 117) (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m).

  Notation RSLOTS j0 j1 j2 j3 j9 :=
    [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; C8 (Z_to_bv 64 (e_SBUF E + 4)); C8 (Z_to_bv 64 18446744073709495296);
     C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 16)); C8 (Z_to_bv 64 (e_SBUF E)); CB 8 j9].

  Definition rootstrend_k (Q : machine_state -> Prop) (d : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
           j0 j1 j2 j3 j9 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSLOTS j0 j1 j2 j3 j9) [] fc m1 ->
      evt psegs Q (S2R E 0x3f4b0 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (e_SBUF E + 4 + d)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Lemma seg_root_str_end : forall (Q : machine_state -> Prop) (d : Z),
    (0 <= d < 2^31)%Z -> (d + 5 <= e_scap E)%Z -> Z.of_nat (length (e_sbs E)) = 0%Z ->
    (forall cb, Z.of_nat (length cb) = d -> docend_k (gapp E [] (srec d cb)) Q (mkst 1 0 2 (d + 5) [])) ->
    rootstrend_k Q d.
  Proof using OK.
    intros Q d HD0 HSC GS KD. unfold rootstrend_k.
    intros xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j1 j2 j3 j9 F fc m1 HM.
    s2_env OK.
    s2_open_mem HM.
    do 6 zstep.
    replace (e_SBUF E + 4 + d - (e_SBUF E + 4))%Z with d by lia. rewrite (swrap32_small d) by lia.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    zstep. s2norm. s2_note_store. s2_store_done_wr.
    zstep.
    s2_cur_mem ltac:(fun m => destruct (timg_sbytes E _ _ m 4 d TIMG ltac:(lia) ltac:(lia) ltac:(lia)) as (cb & HCL & HCB);
      eapply (tape_img_app_str E _ _ m d cb _ _ _ _ (e_SBUF E)%Z) in TIMG;
      [ | lia | exact NEWCH | exact NEWCH0 | exact NEWCH1 | exact NEWCH2
        | exact HCB | exact HCL | exact NEWCH3
        | rewrite u64_small by lia; reflexivity
        | apply (str_byte_k d 8); lia | apply (str_byte_k d 16); lia | apply (str_byte_k d 24); lia
        | lia | lia | lia ]).
    eapply (KD (map bv_unsigned cb)); [rewrite length_map; exact HCL|]. cbn [k W].
    eapply (MEMI_forget8 _ _ [_;_;_;_] _ [_;_;_;_;_]); cycle 1;
      [eapply (MEMI_forget8 _ _ [_;_;_;_;_] _ [_;_;_;_]); cycle 1;
         [eapply (MEMI_forget8 _ _ [_;_;_;_;_;_;_;_] _ [_]); cycle 1; [s2_close_mem0 | reflexivity] | reflexivity]
      | reflexivity].
  Qed.

  Ltac rs_exit KX := s2_err_exit KX; eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].

  Section Loop.
    Variables (Q : machine_state -> Prop) (i j : Z).
    Hypothesis HROOM : ((j - i) + 4 <= e_scap E)%Z.
    Hypothesis HI0 : (0 <= i)%Z.
    Hypothesis HGS : (Z.of_nat (length (e_sbs E)) <= 0)%Z.
    Hypothesis KX : exit_k E Q.
    Hypothesis KE : forall d', (0 <= d' <= j - i - 1)%Z -> rootstrend_k Q d'.

    Lemma rootstr_loop : forall (fuel : nat) p d xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6
        j0 j1 j2 j3 j9 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      PS bs i j p d -> (j - p < Z.of_nat fuel)%Z ->
      MEMI E (e_nxt0 E) (RSLOTS j0 j1 j2 j3 j9) [] fc m1 ->
      evt psegs Q (RSH xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 p d F fc m1).
    Proof using OK HROOM HI0 HGS KX KE.
      induction fuel as [|fuel IH];
        intros p d xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 j0 j1 j2 j3 j9 F fc m1 HPS HF HM.
      { pose proof (PS_measure _ _ _ _ _ HPS). lia. }
      pose proof (PS_read _ _ _ _ _ HPS) as (HP0 & HPJ & HJL & HP11).
      pose proof (PS_store _ _ _ _ _ HPS) as (HD0 & HD4).
      pose proof (ok_bytes _ OK) as BOK.
      pose proof (B_range bs p BOK) as HB0.
      s2_env OK.
      s2_open_mem HM.
      sstep. sstep. sstep.
      if_cases K; zify_cond K.
      -
        pose proof (B_range bs (p + 1) BOK) as HB1.
        sstep. sstep.
        if_cases K1; zify_cond K1.
        +
          s2_cur_mem ltac:(fun m => pose proof (esc_read m (B bs (p + 1)) MI HB1) as RE).
          unfold T_ESC in RE. pose proof (esc_range (B bs (p + 1))) as HER.
          sstep. sstep. sstep. sstep. sstep.
          if_cases K2; zify_cond K2.
          *
            sstep. sstep. sstep. sstep.
            replace (e_SBUF E + 4 + d + 1)%Z with (e_SBUF E + 4 + (d + 1))%Z by lia.
            replace (e_BUF E + p + 2)%Z with (e_BUF E + (p + 2))%Z by lia.
            pose proof (closes_esc_le _ _ _ (ps_closes _ _ _ _ _ HPS) K) as HLE.
            eapply (IH (p + 2)%Z (d + 1)%Z); [apply PS_esc; [exact HPS | exact K] | lia | s2_close_mem0].
          *
            sstep. sstep. rs_exit KX.
        +
          pose proof (B_range bs (p + 2) BOK) as HB2. pose proof (B_range bs (p + 3) BOK) as HB3.
          pose proof (B_range bs (p + 4) BOK) as HB4. pose proof (B_range bs (p + 5) BOK) as HB5.
          sstep. sstep.
          replace (e_BUF E + p + 2)%Z with (e_BUF E + (p + 2))%Z by lia.
          eapply (hex4_call E OK Q 0x3e93c (p + 2)%Z); [left; reflexivity | exact BUFRO | exact MI | lia |].
          intros y11 y12 y13 y14. unfold hex4v.
          replace (p + 2 + 1)%Z with (p + 3)%Z by lia. replace (p + 2 + 2)%Z with (p + 4)%Z by lia. replace (p + 2 + 3)%Z with (p + 5)%Z by lia.
          destruct (or4_cases _ _ _ _ (dig_shape (420 + B bs (p + 3))) (dig_shape (210 + B bs (p + 4)))
                              (dig_shape (630 + B bs (p + 2))) (dig_shape (0 + B bs (p + 5)))) as [EQ | (RV & V3 & V4 & V2 & V5)].
          *
            rewrite EQ. unfold ONES64.
            sstep. sstep. sstep. sstep. if_false.
            sstep. if_true. sstep. sstep. sstep. if_false. sstep. sstep. if_true. sstep. sstep. if_true. sstep. sstep. if_false. sstep.
            rs_exit KX.
          *
            set (v := or4 (dig (420 + B bs (p + 3))) (dig (210 + B bs (p + 4))) (dig (630 + B bs (p + 2))) (dig (0 + B bs (p + 5)))) in *.
            assert (HU : forall t, (2 <= t < 6)%Z -> not_qb (B bs (p + t))).
            { intros t Ht. assert (t = 2 \/ t = 3 \/ t = 4 \/ t = 5)%Z as [-> | [-> | [-> | ->]]] by lia.
              - apply (dig_valid_not_qb 630); [auto | lia].
              - apply (dig_valid_not_qb 420); [auto | lia].
              - apply (dig_valid_not_qb 210); [auto | lia].
              - apply (dig_valid_not_qb 0); [auto | lia]. }
            pose proof (PS_u_store _ _ _ _ _ HPS K HU) as HST.
            pose proof (closes_u_le _ _ _ (ps_closes _ _ _ _ _ HPS) K HU) as HLE.
            sstep. sstep. sstep. sstep.
            if_cases K2; zify_cond K2.
            --
               pose proof (B_range bs (p + 6) BOK) as HB6. pose proof (B_range bs (p + 7) BOK) as HB7.
               sstep. sstep. zstep. zstep. zstep.
               if_cases K8; zify_cond K8.
               ++ rewrite Z.mod_small in K8 by (rewrite Z.shiftl_mul_pow2 by lia; lia).
                  destruct (lor_shl8_bu _ _ HB6 HB7 K8) as [E6 E7].
                  pose proof (B_range bs (p + 8) BOK) as HB8. pose proof (B_range bs (p + 9) BOK) as HB9.
                  pose proof (B_range bs (p + 10) BOK) as HB10. pose proof (B_range bs (p + 11) BOK) as HB11.
                  sstep. sstep.
                  replace (e_BUF E + p + 8)%Z with (e_BUF E + (p + 8))%Z by lia.
                  eapply (hex4_call E OK Q 0x3e9d4 (p + 8)%Z); [right; reflexivity | exact BUFRO | exact MI | lia |].
                  intros z11 z12 z13 z14. unfold hex4v.
                  replace (p + 8 + 1)%Z with (p + 9)%Z by lia. replace (p + 8 + 2)%Z with (p + 10)%Z by lia. replace (p + 8 + 3)%Z with (p + 11)%Z by lia.
                  destruct (or4_cases _ _ _ _ (dig_shape (420 + B bs (p + 9))) (dig_shape (210 + B bs (p + 10)))
                                      (dig_shape (630 + B bs (p + 8))) (dig_shape (0 + B bs (p + 11)))) as [EQ2 | (RV2 & V9 & V10 & V8 & V11)].
                  ** rewrite EQ2. unfold ONES64.
                     sstep. sstep. sstep. sstep. if_false. sstep.
                     rs_exit KX.
                  ** set (v2 := or4 (dig (420 + B bs (p + 9))) (dig (210 + B bs (p + 10))) (dig (630 + B bs (p + 8))) (dig (0 + B bs (p + 11)))) in *.
                     assert (HU2 : forall t, (8 <= t < 12)%Z -> not_qb (B bs (p + t))).
                     { intros t Ht. assert (t = 8 \/ t = 9 \/ t = 10 \/ t = 11)%Z as [-> | [-> | [-> | ->]]] by lia.
                       - apply (dig_valid_not_qb 630); [auto | lia].
                       - apply (dig_valid_not_qb 420); [auto | lia].
                       - apply (dig_valid_not_qb 210); [auto | lia].
                       - apply (dig_valid_not_qb 0); [auto | lia]. }
                     pose proof (PS_uu_store _ _ _ _ _ HPS K HU E6 HU2) as HST2.
                     pose proof (PS_uu bs i j p d 4 HPS K HU E6 HU2 ltac:(lia)) as HPS12.
                     pose proof (PS_read _ _ _ _ _ HPS12) as (_ & HP12J & _ & _).
                     sstep. sstep. sstep. sstep.
                     if_cases K9; zify_cond K9.
                     ---
                         do 22 sstep.
                         replace (e_BUF E + p + 12)%Z with (e_BUF E + (p + 12))%Z by lia.
                         replace (e_SBUF E + 4 + d + 4)%Z with (e_SBUF E + 4 + (d + 4))%Z by lia.
                         eapply (IH (p + 12)%Z (d + 4)%Z); [exact HPS12 | lia | s2_close_mem0].
                     --- sstep. rs_exit KX.
               ++ sstep. rs_exit KX.
            -- sstep.
               if_cases K3; zify_cond K3.
               ++
                  sstep. sstep. sstep.
                  replace (e_BUF E + p + 6)%Z with (e_BUF E + (p + 6))%Z by lia.
                  if_cases K4; zify_cond K4.
                  **
                     sstep. sstep.
                     replace (e_SBUF E + 4 + d + 1)%Z with (e_SBUF E + 4 + (d + 1))%Z by lia.
                     eapply (IH (p + 6)%Z (d + 1)%Z); [apply (PS_u bs i j p d 1 HPS K HU); lia | lia | s2_close_mem0].
                  ** sstep. sstep.
                     if_cases K5; zify_cond K5.
                     ---
                         sstep. sstep.
                         if_cases K6; zify_cond K6.
                         +++
                             sstep. sstep.
                             if_cases K7; zify_cond K7.
                             ***
                                 do 17 sstep.
                                 replace (e_SBUF E + 4 + d + 4)%Z with (e_SBUF E + 4 + (d + 4))%Z by lia.
                                 eapply (IH (p + 6)%Z (d + 4)%Z); [apply (PS_u bs i j p d 4 HPS K HU); lia | lia | s2_close_mem0].
                             *** sstep. rs_exit KX.
                         +++
                             do 13 sstep.
                             replace (e_SBUF E + 4 + d + 3)%Z with (e_SBUF E + 4 + (d + 3))%Z by lia.
                             eapply (IH (p + 6)%Z (d + 3)%Z); [apply (PS_u bs i j p d 3 HPS K HU); lia | lia | s2_close_mem0].
                     ---
                         do 9 sstep.
                         replace (e_SBUF E + 4 + d + 2)%Z with (e_SBUF E + 4 + (d + 2))%Z by lia.
                         eapply (IH (p + 6)%Z (d + 2)%Z); [apply (PS_u bs i j p d 2 HPS K HU); lia | lia | s2_close_mem0].
               ++
                  sstep. rs_exit KX.
      - sstep.
        if_cases K1; zify_cond K1.
        +
          destruct (PS_quote _ _ _ _ _ HPS ltac:(lia)) as [EJ HDJ].
          eapply (KE d HDJ). s2_close_mem0.
        +
          sstep. sstep. sstep.
          replace (e_SBUF E + 4 + d + 1)%Z with (e_SBUF E + 4 + (d + 1))%Z by lia.
          replace (e_BUF E + p + 1)%Z with (e_BUF E + (p + 1))%Z by lia.
          eapply (IH (p + 1)%Z (d + 1)%Z); [apply PS_ord; [exact HPS | lia | lia] | lia | s2_close_mem0].
    Qed.
  End Loop.
End RootStr.
