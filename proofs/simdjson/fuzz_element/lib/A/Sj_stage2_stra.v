(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_strkit Sj_stage2_auto Sj_stage2_wkit Sj_stage2_objf Sj_stage2_stram.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_shadow_dig | s2_load_buf | s2_load_esc | s2_load_dig | s2_load_dig2 | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section StrA.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Section Loop.
    Variables (Q : machine_state -> Prop) (dpt t40 i48 sbv r9 : Z) (sc : list (bool * Z)).
    Hypothesis KX : exit_k E Q.
    Hypothesis HGS : (Z.of_nat (length (e_sbs E)) = sbv)%Z.
    Notation headk := (Sj_stage2_stram.headk E Q dpt t40 i48 sbv sc).
    Notation stra_mb0s := (Sj_stage2_stram.stra_mb0s E OK SHZ Q dpt t40 i48 sbv sc KX HGS).
    Notation stra_mb0p := (Sj_stage2_stram.stra_mb0p E OK SHZ Q dpt t40 i48 sbv sc KX HGS).
    Variables (i j : Z) (kk Wv : Z).
    Hypothesis HROOM : (0 <= sbv /\ sbv + (j - i) + 4 <= e_scap E)%Z.
    Hypothesis HI0 : (0 <= i)%Z.
    Hypothesis H40 : t40 = (e_TAPE E + 8 * Wv)%Z.
    Hypothesis H48 : i48 = (e_IDX E + 4 * kk)%Z.
    Hypothesis KE : forall d', (0 <= d' <= j - i - 1)%Z -> keyend_k E Q kk dpt Wv sbv d' sc.

    Lemma stra_loop : forall (fuel : nat) p d, PS bs i j p d -> (j - p < Z.of_nat fuel)%Z -> headk p d.
    Proof using OK SHZ HROOM HI0 KX HGS KE H40 H48.
      induction fuel as [|fuel IH]; intros p d HPS HF; unfold Sj_stage2_stram.headk; intros xt0 xa1 xa2 xa4 xa7 xs6 xt4 j64 j72 j80 j88 j96 j104 j112 j120 j128 j272 F fc m1 HM.
      { pose proof (PS_measure _ _ _ _ _ HPS). lia. }
      pose proof (PS_read _ _ _ _ _ HPS) as (HP0 & HPJ & HJL & HP11).
      pose proof (PS_store _ _ _ _ _ HPS) as (HD0 & HD4).
      pose proof (ok_bytes _ OK) as BOK.
      pose proof (B_range bs p BOK) as HB0.
      s2_env OK.
      pose proof HM as HMo. s2_open_mem HMo.
      wrun.
      if_cases_eq K.
      -
        pose proof (B_range bs (p + 1) BOK) as HB1.
        wrun.
        if_cases_eq K1.
        +
          pose proof (B_range bs (p + 2) BOK) as HB2. pose proof (B_range bs (p + 3) BOK) as HB3.
          pose proof (B_range bs (p + 4) BOK) as HB4. pose proof (B_range bs (p + 5) BOK) as HB5.
          wrun.
          repeat match goal with |- context [bv_unsigned (sx32 (Z_to_bv 64 (dig ?x)))] =>
            change (bv_unsigned (sx32 (Z_to_bv 64 (dig x)))) with (sxu (dig x)) end.
          repeat match goal with |- context [Z.lor (Z.lor (sxu ?a) (sxu ?b)) (Z.lor (sxu ?c) (sxu ?e))] =>
            replace (Z.lor (Z.lor (sxu a) (sxu b)) (Z.lor (sxu c) (sxu e))) with (or4 a b c e) by (unfold or4; rewrite Z.lor_assoc; reflexivity) end.
          destruct (or4_cases _ _ _ _ (dig_shape (420 + B bs (p + 3))) (dig_shape (630 + B bs (p + 2)))
                              (dig_shape (210 + B bs (p + 4))) (dig_shape (0 + B bs (p + 5)))) as [EQ | (RV & V3 & V2 & V4 & V5)].
          *
            rewrite EQ. unfold ONES64.
            grun_dec_to 0xcb1dc%Z.
            eapply (KX 5%Z); [s2_errlit|]. s2_close_memx.
          *
            set (v := or4 (dig (420 + B bs (p + 3))) (dig (630 + B bs (p + 2))) (dig (210 + B bs (p + 4))) (dig (0 + B bs (p + 5)))) in *.
            assert (HU : forall t, (2 <= t < 6)%Z -> not_qb (B bs (p + t))).
            { intros t Ht. assert (t = 2 \/ t = 3 \/ t = 4 \/ t = 5)%Z as [-> | [-> | [-> | ->]]] by lia.
              - apply (dig_valid_not_qb 630); [auto | lia].
              - apply (dig_valid_not_qb 420); [auto | lia].
              - apply (dig_valid_not_qb 210); [auto | lia].
              - apply (dig_valid_not_qb 0); [auto | lia]. }
            pose proof (PS_u_store _ _ _ _ _ HPS K HU) as HST.
            pose proof (closes_u_le _ _ _ (ps_closes _ _ _ _ _ HPS) K HU) as HLE.
            assert (KH6 : forall w, (1 <= w <= 4)%Z -> headk (p + 6) (d + w)).
            { intros w Hw. apply IH; [apply (PS_u bs i j p d w HPS K HU); lia | lia]. }
            if_cases_eq K2.
            --
               pose proof (B_range bs (p + 6) BOK) as HB6. pose proof (B_range bs (p + 7) BOK) as HB7.
               wrun.
               if_cases_eq K8.
               ++ rewrite Z.mod_small in K8 by (rewrite Z.shiftl_mul_pow2 by lia; lia).
                  destruct (lor_shl8_bu _ _ HB6 HB7 K8) as [E6 E7].
                  pose proof (B_range bs (p + 8) BOK) as HB8. pose proof (B_range bs (p + 9) BOK) as HB9.
                  pose proof (B_range bs (p + 10) BOK) as HB10. pose proof (B_range bs (p + 11) BOK) as HB11.
                  wrun.
                  repeat match goal with |- context [bv_unsigned (sx32 (Z_to_bv 64 (dig ?x)))] =>
                    change (bv_unsigned (sx32 (Z_to_bv 64 (dig x)))) with (sxu (dig x)) end.
                  repeat match goal with |- context [Z.lor (Z.lor (sxu ?a) (sxu ?b)) (Z.lor (sxu ?c) (sxu ?e))] =>
                    replace (Z.lor (Z.lor (sxu a) (sxu b)) (Z.lor (sxu c) (sxu e))) with (or4 a b c e) by (unfold or4; rewrite Z.lor_assoc; reflexivity) end.
                  destruct (or4_cases _ _ _ _ (dig_shape (420 + B bs (p + 9))) (dig_shape (630 + B bs (p + 8)))
                                      (dig_shape (210 + B bs (p + 10))) (dig_shape (0 + B bs (p + 11)))) as [EQ2 | (RV2 & V9 & V8 & V10 & V11)].
                  ** rewrite EQ2. unfold ONES64.
                     grun_dec_to 0xcb1dc%Z. eapply (KX 5%Z); [s2_errlit|]. s2_close_memx.
                  ** set (v2 := or4 (dig (420 + B bs (p + 9))) (dig (630 + B bs (p + 8))) (dig (210 + B bs (p + 10))) (dig (0 + B bs (p + 11)))) in *.
                     assert (HU2 : forall t, (8 <= t < 12)%Z -> not_qb (B bs (p + t))).
                     { intros t Ht. assert (t = 8 \/ t = 9 \/ t = 10 \/ t = 11)%Z as [-> | [-> | [-> | ->]]] by lia.
                       - apply (dig_valid_not_qb 630); [auto | lia].
                       - apply (dig_valid_not_qb 420); [auto | lia].
                       - apply (dig_valid_not_qb 210); [auto | lia].
                       - apply (dig_valid_not_qb 0); [auto | lia]. }
                     pose proof (PS_uu_store _ _ _ _ _ HPS K HU E6 HU2) as HST2.
                     pose proof (PS_read _ _ _ _ _ (PS_uu bs i j p d 4 HPS K HU E6 HU2 ltac:(lia))) as (_ & HP12J & _ & _).
                     assert (KH12 : forall w, (1 <= w <= 4)%Z -> headk (p + 12) (d + w)).
                     { intros w Hw. apply IH; [apply (PS_uu bs i j p d w HPS K HU E6 HU2); lia | lia]. }

                     if_cases K9; clear K9;
                     wrun_to2 0xcb1dc%Z 0xc04e4%Z;
                     lazymatch goal with
                     | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                         lazymatch pc with
                         | 0xcb1dc%Z => eapply (KX 5%Z); [s2_errlit|]; s2_close_memx
                         | _ => replace (e_BUF E + p + 12)%Z with (e_BUF E + (p + 12))%Z by lia;
                                eapply (stra_mb0p (p + 12)%Z d); [lia | lia | eassumption | exact KH12]
                         end
                     end.
               ++
                  wrun_to 0xcb1dc%Z. eapply (KX 5%Z); [s2_errlit|]. s2_close_memx.
            -- wrun.
               if_cases_eq K3.
               ++
                  wrun_to 0xcb1dc%Z. eapply (KX 5%Z); [s2_errlit|]. s2_close_memx.
               ++
                  wrun_to 0xc033c%Z.
                  replace (e_BUF E + p + 6)%Z with (e_BUF E + (p + 6))%Z by lia.
                  eapply (stra_mb0s (p + 6)%Z d); [lia | lia | eassumption | exact KH6].
        +
          pose proof (esc_range (B bs (p + 1))) as HER.
          wrun.
          if_cases_eq K2.
          *
            wrun_to 0xcb1dc%Z. eapply (KX 5%Z); [s2_errlit|]. s2_close_memx.
          *
            pose proof (closes_esc_le _ _ _ (ps_closes _ _ _ _ _ HPS) K) as HLE.
            wrun_to 0xc01dc%Z.
            replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + sbv + 4 + (d + 1))%Z by lia.
            replace (e_BUF E + p + 2)%Z with (e_BUF E + (p + 2))%Z by lia.
            eapply (IH (p + 2)%Z (d + 1)%Z); [apply PS_esc; [exact HPS | exact K] | lia | eassumption].
      - wrun.
        if_cases_eq K1.
        +
          destruct (PS_quote _ _ _ _ _ HPS ltac:(lia)) as [EJ HDJ].
          wrun_to 0xc1c54%Z.
          match goal with HMh : MEMI _ _ _ _ _ _ |- _ => rewrite H40 in HMh end.
          rewrite ?H48.
          eapply (KE d HDJ). wk_close.
        +
          wrun_to 0xc01dc%Z.
          replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + sbv + 4 + (d + 1))%Z by lia.
          replace (e_BUF E + p + 1)%Z with (e_BUF E + (p + 1))%Z by lia.
          eapply (IH (p + 1)%Z (d + 1)%Z); [apply PS_ord; [exact HPS | lia | lia] | lia | eassumption].
    Qed.
  End Loop.
End StrA.
