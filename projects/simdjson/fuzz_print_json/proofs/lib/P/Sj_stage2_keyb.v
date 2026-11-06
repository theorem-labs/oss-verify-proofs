(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_stage2_defs Sj_tables Sj_stage2_auto Sj_stage2_objf.
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

Section KeyB.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).
  Notation bs := (e_bs E).

  Notation KAH xra xs1 xs3 xs5 xs6 xs7 p d sbv kk F fc m :=
    (S2R E 0x47f34 xra (Z_to_bv 64 127) (Z_to_bv 64 1) (Z_to_bv 64 2047) (Z_to_bv 64 (e_THIS E)) xs1
         (Z_to_bv 64 (e_SBUF E + sbv + 4)) (Z_to_bv 64 34) (Z_to_bv 64 (e_BUF E + p)) (Z_to_bv 64 92) (Z_to_bv 64 117) (Z_to_bv 64 1023)
         (Z_to_bv 64 (-56557568)) (Z_to_bv 64 4) (Z_to_bv 64 55296) xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7
         (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 23669) (Z_to_bv 64 56320) (Z_to_bv 64 16)
         (Z_to_bv 64 (e_IDX E + 4 * kk)) (Z_to_bv 64 (e_SBUF E + sbv)) (Z_to_bv 64 (-56320)) (Z_to_bv 64 81364) F fc m).

  Section Loop.
    Variables (Q : machine_state -> Prop) (kk dpt Wv sbv : Z) (sc : list (bool * Z)) (i j : Z).
    Hypothesis HROOM : (0 <= sbv /\ sbv + (j - i) + 4 <= e_scap E)%Z.
    Hypothesis HI0 : (0 <= i)%Z.
    Hypothesis HGS : (Z.of_nat (length (e_sbs E)) <= sbv)%Z.
    Hypothesis KX : exit_k E Q.
    Hypothesis KE : forall d', (0 <= d' <= j - i - 1)%Z -> keyend_k E Q kk dpt Wv sbv d' sc.

    Lemma keyb_loop : forall (fuel : nat) p d xra xs1 xs3 xs5 xs6 xs7 j0 j1 j2 j3 j4 j6 j8 j9 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      PS bs i j p d -> (j - p < Z.of_nat fuel)%Z ->
      MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; C8 (Z_to_bv 64 dpt); CB 8 j6;
                         C8 (Z_to_bv 64 (e_TAPE E + 8 * Wv)); CB 8 j8; CB 8 j9] sc fc m1 ->
      evt psegs Q (KAH xra xs1 xs3 xs5 xs6 xs7 p d sbv kk F fc m1).
    Proof using OK HROOM HI0 HGS KX KE.
      induction fuel as [|fuel IH]; intros p d xra xs1 xs3 xs5 xs6 xs7 j0 j1 j2 j3 j4 j6 j8 j9 F fc m1 HPS HF HM.
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
            replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + sbv + 4 + (d + 1))%Z by lia.
            replace (e_BUF E + p + 2)%Z with (e_BUF E + (p + 2))%Z by lia.
            pose proof (closes_esc_le _ _ _ (ps_closes _ _ _ _ _ HPS) K) as HLE.
            eapply (IH (p + 2)%Z (d + 1)%Z); [apply PS_esc; [exact HPS | exact K] | lia | s2_close_mem0].
          *
            sstep. sstep. s2_err_exit KX.
            eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
        +
          pose proof (B_range bs (p + 2) BOK) as HB2. pose proof (B_range bs (p + 3) BOK) as HB3.
          pose proof (B_range bs (p + 4) BOK) as HB4. pose proof (B_range bs (p + 5) BOK) as HB5.
          do 12 sstep.
          s2_cur_mem ltac:(fun m =>
            pose proof (dig_read m (420 + B bs (p + 3)) (wa (4 * B bs (p + 3) + 81364 + 1680)) MI ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia)) as RD3;
            pose proof (dig_read m (210 + B bs (p + 4)) (wa (4 * B bs (p + 4) + 81364 + 840)) MI ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia)) as RD4;
            pose proof (dig_read m (630 + B bs (p + 2)) (wa (81364 + 4 * (B bs (p + 2) + 630))) MI ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia)) as RD2;
            pose proof (dig_read m (0 + B bs (p + 5)) (wa (81364 + 4 * B bs (p + 5))) MI ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia)) as RD5).
          zstep. zstep. zstep. zstep. zstep.
          zstep. zstep. zstep.
          repeat match goal with |- context [bv_unsigned (sx32 (Z_to_bv 64 (dig ?x)))] =>
            change (bv_unsigned (sx32 (Z_to_bv 64 (dig x)))) with (sxu (dig x)) end.
          match goal with |- context [Z.lor (Z.lor (Z.lor (sxu ?a) (sxu ?b)) (sxu ?c)) (sxu ?e)] =>
            change (Z.lor (Z.lor (Z.lor (sxu a) (sxu b)) (sxu c)) (sxu e)) with (or4 a b c e) end.
          destruct (or4_cases _ _ _ _ (dig_shape (420 + B bs (p + 3))) (dig_shape (210 + B bs (p + 4)))
                              (dig_shape (630 + B bs (p + 2))) (dig_shape (0 + B bs (p + 5)))) as [EQ | (RV & V3 & V4 & V2 & V5)].
          *
            rewrite EQ. unfold ONES64.
            sstep. sstep. sstep. if_false.
            sstep. if_true. sstep. sstep. if_false. sstep. if_true. sstep. sstep. if_true. sstep. if_false. sstep.
            s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
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
            sstep. sstep. sstep.
            if_cases K2; zify_cond K2.
            --
               pose proof (B_range bs (p + 6) BOK) as HB6. pose proof (B_range bs (p + 7) BOK) as HB7.
               sstep. sstep. zstep. zstep. zstep.
               if_cases K8; zify_cond K8.
               ++ rewrite Z.mod_small in K8 by (rewrite Z.shiftl_mul_pow2 by lia; lia).
                  destruct (lor_shl8_bu _ _ HB6 HB7 K8) as [E6 E7].
                  pose proof (B_range bs (p + 8) BOK) as HB8. pose proof (B_range bs (p + 9) BOK) as HB9.
                  pose proof (B_range bs (p + 10) BOK) as HB10. pose proof (B_range bs (p + 11) BOK) as HB11.
                  do 12 sstep.
                  s2_cur_mem ltac:(fun m =>
                    pose proof (dig_read m (420 + B bs (p + 9)) (wa (4 * B bs (p + 9) + 81364 + 1680)) MI ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia)) as RD9;
                    pose proof (dig_read m (210 + B bs (p + 10)) (wa (4 * B bs (p + 10) + 81364 + 840)) MI ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia)) as RD10;
                    pose proof (dig_read m (630 + B bs (p + 8)) (wa (81364 + 4 * (B bs (p + 8) + 630))) MI ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia)) as RD8;
                    pose proof (dig_read m (0 + B bs (p + 11)) (wa (81364 + 4 * B bs (p + 11))) MI ltac:(lia) ltac:(unfold wa, T_DIG; f_equal; lia)) as RD11).
                  zstep. zstep. zstep. zstep. zstep.
                  zstep. zstep. zstep.
                  repeat match goal with |- context [bv_unsigned (sx32 (Z_to_bv 64 (dig ?x)))] =>
                    change (bv_unsigned (sx32 (Z_to_bv 64 (dig x)))) with (sxu (dig x)) end.
                  match goal with |- context [Z.lor (Z.lor (Z.lor (sxu ?a) (sxu ?b)) (sxu ?c)) (sxu ?e)] =>
                    change (Z.lor (Z.lor (Z.lor (sxu a) (sxu b)) (sxu c)) (sxu e)) with (or4 a b c e) end.
                  destruct (or4_cases _ _ _ _ (dig_shape (420 + B bs (p + 9))) (dig_shape (210 + B bs (p + 10)))
                                      (dig_shape (630 + B bs (p + 8))) (dig_shape (0 + B bs (p + 11)))) as [EQ2 | (RV2 & V9 & V10 & V8 & V11)].
                  ** rewrite EQ2. unfold ONES64.
                     sstep. sstep. if_false. sstep.
                     s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
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
                     sstep. sstep.
                     if_cases K9; zify_cond K9.
                     ---
                         do 20 sstep.
                         replace (e_BUF E + p + 12)%Z with (e_BUF E + (p + 12))%Z by lia.
                         replace (e_SBUF E + sbv + 4 + d + 4)%Z with (e_SBUF E + sbv + 4 + (d + 4))%Z by lia.
                         eapply (IH (p + 12)%Z (d + 4)%Z); [exact HPS12 | lia | s2_close_mem0].
                     --- sstep. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
               ++ sstep. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
            -- sstep.
               if_cases K3; zify_cond K3.
               ++
                  sstep. sstep.
                  replace (e_BUF E + p + 6)%Z with (e_BUF E + (p + 6))%Z by lia.
                  if_cases K4; zify_cond K4.
                  **
                     sstep. sstep.
                     replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + sbv + 4 + (d + 1))%Z by lia.
                     eapply (IH (p + 6)%Z (d + 1)%Z); [apply (PS_u bs i j p d 1 HPS K HU); lia | lia | s2_close_mem0].
                  ** sstep.
                     if_cases K5; zify_cond K5.
                     ---
                         sstep. sstep.
                         if_cases K6; zify_cond K6.
                         +++
                             sstep.
                             if_cases K7; zify_cond K7.
                             ***
                                 do 16 sstep.
                                 replace (e_SBUF E + sbv + 4 + d + 4)%Z with (e_SBUF E + sbv + 4 + (d + 4))%Z by lia.
                                 eapply (IH (p + 6)%Z (d + 4)%Z); [apply (PS_u bs i j p d 4 HPS K HU); lia | lia | s2_close_mem0].
                             *** sstep. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
                         +++
                             do 13 sstep.
                             replace (e_SBUF E + sbv + 4 + d + 3)%Z with (e_SBUF E + sbv + 4 + (d + 3))%Z by lia.
                             eapply (IH (p + 6)%Z (d + 3)%Z); [apply (PS_u bs i j p d 3 HPS K HU); lia | lia | s2_close_mem0].
                     ---
                         do 9 sstep.
                         replace (e_SBUF E + sbv + 4 + d + 2)%Z with (e_SBUF E + sbv + 4 + (d + 2))%Z by lia.
                         eapply (IH (p + 6)%Z (d + 2)%Z); [apply (PS_u bs i j p d 2 HPS K HU); lia | lia | s2_close_mem0].
               ++
                  sstep. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
      - sstep.
        if_cases K1; zify_cond K1.
        +
          destruct (PS_quote _ _ _ _ _ HPS ltac:(lia)) as [EJ HDJ].
          eapply (KE d HDJ). s2_close_mem0.
        +
          sstep. sstep. sstep.
          replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + sbv + 4 + (d + 1))%Z by lia.
          replace (e_BUF E + p + 1)%Z with (e_BUF E + (p + 1))%Z by lia.
          eapply (IH (p + 1)%Z (d + 1)%Z); [apply PS_ord; [exact HPS | lia | lia] | lia | s2_close_mem0].
    Qed.
  End Loop.
End KeyB.
