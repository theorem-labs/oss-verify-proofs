(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Zbitwise.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow Od_pstr_defsA Od_pstr_encA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | ps_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ ps_solve_store0 | ps_store_wr ].

Lemma or22_or4 : forall a b c e, Z.lor (Z.lor (sxu a) (sxu b)) (Z.lor (sxu c) (sxu e)) = or4 a b c e.
Proof. intros. unfold or4. rewrite Z.lor_assoc. reflexivity. Qed.

Section U.
  Variable E : psenv.
  Hypothesis OK : psa_ok E.
  Hypothesis SHZ : psa_shz E.
  Local Notation BUF := (q_BUF E) (only parsing).
  Local Notation SB := (q_SB E) (only parsing).
  Local Notation sbo := (q_sbo E) (only parsing).
  Local Notation bs := (q_bs E) (only parsing).

  Lemma psa_u : forall p d xra xa2 xa4 xa5 xt1 xt3 xs8 xs9 mm,
    PS bs (q_i E) (q_j E) p d -> B bs p = 92%Z -> PSAINV E mm ->
    (forall p' d', PS bs (q_i E) (q_j E) p' d' -> (p < p')%Z -> psa_headk E d' p') ->
    evt asegs (psa_post E) (PSA E 0xc4b0c xra (Z_to_bv 64 (SB + sbo + d)) (Z_to_bv 64 (BUF + p)) xa2 xa4 xa5 xt1 xt3 xs8 xs9
                              (Z_to_bv 64 ((SB + sbo + d) / 8 + 2147450880)) mm).
  Proof using OK SHZ.
    intros until mm. intros HPS K INV HK. pose proof INV as INV0. psa_open INV0. pose proof OK as OK0. psa_env OK0. psa_shzp SHZ.
    pose proof (PS_read _ _ _ _ _ HPS) as (HP0 & HPJ & HJL & HP11).
    pose proof (PS_store _ _ _ _ _ HPS) as (HD0 & HD4).
    pose proof (B_range bs (p + 2) BOK) as HB2. pose proof (B_range bs (p + 3) BOK) as HB3.
    pose proof (B_range bs (p + 4) BOK) as HB4. pose proof (B_range bs (p + 5) BOK) as HB5.
    pose proof (adig_read mm (630 + B bs (p + 2)) (wa (146208 + 4 * (B bs (p + 2) + 630))) MI ltac:(lia) ltac:(unfold wa, AT_DIG; f_equal; lia)) as RD2.
    pose proof (adig_read mm (420 + B bs (p + 3)) (wa (4 * B bs (p + 3) + 146208 + 1680)) MI ltac:(lia) ltac:(unfold wa, AT_DIG; f_equal; lia)) as RD3.
    pose proof (adig_read mm (210 + B bs (p + 4)) (wa (4 * B bs (p + 4) + 146208 + 840)) MI ltac:(lia) ltac:(unfold wa, AT_DIG; f_equal; lia)) as RD4.
    pose proof (adig_read mm (0 + B bs (p + 5)) (wa (146208 + 4 * B bs (p + 5))) MI ltac:(lia) ltac:(unfold wa, AT_DIG; f_equal; lia)) as RD5.

    pa. pa. pa. pa. pa. if_false. pa.
    pa. pa. pa.
    pa. pa. pa. pa. if_false.

    pa. pa. pa. pa. pa. pa. if_false.

    pa. pa. pa. pa.
    pa. pa. pa. pa. if_false.

    pa. pa. pa. pa. pa. pa. if_false.

    pa. pa. pa. pa.
    pa. pa. pa. pa. if_false.

    pa. pa. pa. pa. pa. pa. if_false.

    pa. pa. pa.
    pa. pa. pa. pa. if_false.
    pa. pa. pa. pa.
    repeat match goal with |- context [bv_unsigned (sx32 (Z_to_bv 64 (odig ?x)))] =>
      change (bv_unsigned (sx32 (Z_to_bv 64 (odig x)))) with (sxu (odig x)) end.
    rewrite or22_or4.
    destruct (or4_cases _ _ _ _ (odig_dshape (420 + B bs (p + 3))) (odig_dshape (630 + B bs (p + 2)))
                        (odig_dshape (210 + B bs (p + 4))) (odig_dshape (0 + B bs (p + 5)))) as [EQ | (RV & V3 & V2 & V4 & V5)].
    - rewrite EQ. unfold ONES64.

      pa. pa. pa. if_true.
      pa. pa. if_true. pa. if_false. pa. if_false. pa. if_true. pa. if_true.
      pa. pa. if_false. pa. pa. pa. if_true.
      eapply evt_eq; [| eapply (psa_fail E OK)]; [s1_st_eq | exact INV].
    - set (v := or4 (odig (420 + B bs (p + 3))) (odig (630 + B bs (p + 2))) (odig (210 + B bs (p + 4))) (odig (0 + B bs (p + 5)))) in *.
      assert (HU : forall t, (2 <= t < 6)%Z -> not_qb (B bs (p + t))).
      { intros t Ht. assert (t = 2 \/ t = 3 \/ t = 4 \/ t = 5)%Z as [-> | [-> | [-> | ->]]] by lia.
        - apply (odig_valid_not_qb 630); [auto | lia].
        - apply (odig_valid_not_qb 420); [auto | lia].
        - apply (odig_valid_not_qb 210); [auto | lia].
        - apply (odig_valid_not_qb 0); [auto | lia]. }
      pose proof (PS_u_store _ _ _ _ _ HPS K HU) as HST.
      pose proof (closes_u_le _ _ _ (ps_closes _ _ _ _ _ HPS) K HU) as HLE.
      clearbody v.

      pa. pa. pa.
      if_cases K2; zify_cond K2.
      +
        pa. pa.
        if_cases K3; zify_cond K3.
        *
          pa. if_false. pa.
          if_cases K3b; zify_cond K3b; [exfalso; lia|].
          pa.
          if_cases K4; zify_cond K4.
          --
             pa.
             if_cases K5; zify_cond K5.
             ++
                pa. pa.
                if_cases K6; zify_cond K6.
                **
                   eapply evt_eq; [| eapply (psa_enc3 E OK SHZ d (p + 6)%Z)]; [s1_st_eq | exact INV | lia | lia |].
                   apply HK; [apply (PS_u bs (q_i E) (q_j E) p d 3 HPS K HU); lia | lia].
                **
                   pa. pa. pa.
                   if_cases K7; zify_cond K7.
                   --- eapply evt_eq; [| eapply (psa_fail E OK)]; [s1_st_eq | exact INV].
                   ---
                       eapply evt_eq; [| eapply (psa_enc4 E OK SHZ d (p + 6)%Z)]; [s1_st_eq | exact INV | lia | lia |].
                       apply HK; [apply (PS_u bs (q_i E) (q_j E) p d 4 HPS K HU); lia | lia].
             ++
                eapply evt_eq; [| eapply (psa_enc2 E OK SHZ d (p + 6)%Z)]; [s1_st_eq | exact INV | lia | lia |].
                apply HK; [apply (PS_u bs (q_i E) (q_j E) p d 2 HPS K HU); lia | lia].
          --
             eapply evt_eq; [| eapply (psa_enc1 E OK SHZ d (p + 6)%Z)]; [s1_st_eq | exact INV | lia | lia |].
             apply HK; [apply (PS_u bs (q_i E) (q_j E) p d 1 HPS K HU); lia | lia].
        *
          pa. pa. if_false. pa.
          if_cases K3b; zify_cond K3b; [|exfalso; lia].
          eapply evt_eq; [| eapply (psa_fail E OK)]; [s1_st_eq | exact INV].
      +
        pose proof (B_range bs (p + 6) BOK) as HB6. pose proof (B_range bs (p + 7) BOK) as HB7.
        pa. pa. pa. pa. if_false.
        pa. pa. pa. pa. pa. pa. if_false.
        pa. pa. pa. pa.
        if_cases K8; zify_cond K8.
        *
          pa. pa. if_true.
          eapply evt_eq; [| eapply (psa_fail E OK)]; [s1_st_eq | exact INV].
        * rewrite Z.mod_small in K8 by (rewrite Z.shiftl_mul_pow2 by lia; lia).
          destruct (lor_shl8_bu _ _ HB6 HB7 K8) as [E6 E7].
          pose proof (B_range bs (p + 8) BOK) as HB8. pose proof (B_range bs (p + 9) BOK) as HB9.
          pose proof (B_range bs (p + 10) BOK) as HB10. pose proof (B_range bs (p + 11) BOK) as HB11.
          pose proof (adig_read mm (630 + B bs (p + 8)) (wa (146208 + 4 * (B bs (p + 8) + 630))) MI ltac:(lia) ltac:(unfold wa, AT_DIG; f_equal; lia)) as RD8.
          pose proof (adig_read mm (420 + B bs (p + 9)) (wa (4 * B bs (p + 9) + 146208 + 1680)) MI ltac:(lia) ltac:(unfold wa, AT_DIG; f_equal; lia)) as RD9.
          pose proof (adig_read mm (210 + B bs (p + 10)) (wa (4 * B bs (p + 10) + 146208 + 840)) MI ltac:(lia) ltac:(unfold wa, AT_DIG; f_equal; lia)) as RD10.
          pose proof (adig_read mm (0 + B bs (p + 11)) (wa (146208 + 4 * B bs (p + 11))) MI ltac:(lia) ltac:(unfold wa, AT_DIG; f_equal; lia)) as RD11.

          pa. pa. pa. pa. pa. if_false. pa.
          pa. pa. pa.
          pa. pa. pa. pa. if_false.

          pa. pa. pa. pa. pa. pa. if_false.
          pa. pa. pa. pa.
          pa. pa. pa. pa. if_false.

          pa. pa. pa. pa. pa. pa. if_false.
          pa. pa. pa. pa.
          pa. pa. pa. pa. if_false.

          pa. pa. pa. pa. pa. pa. if_false.
          pa. pa. pa.
          pa. pa. pa. pa. if_false.
          pa. pa. pa. pa.
          repeat match goal with |- context [bv_unsigned (sx32 (Z_to_bv 64 (odig ?x)))] =>
            change (bv_unsigned (sx32 (Z_to_bv 64 (odig x)))) with (sxu (odig x)) end.
          rewrite or22_or4.
          destruct (or4_cases _ _ _ _ (odig_dshape (420 + B bs (p + 9))) (odig_dshape (630 + B bs (p + 8)))
                              (odig_dshape (210 + B bs (p + 10))) (odig_dshape (0 + B bs (p + 11)))) as [EQ2 | (RV2 & V9 & V8 & V10 & V11)].
          -- rewrite EQ2. unfold ONES64.

             pa. pa. if_true. pa. pa. if_true.
             eapply evt_eq; [| eapply (psa_fail E OK)]; [s1_st_eq | exact INV].
          -- set (v2 := or4 (odig (420 + B bs (p + 9))) (odig (630 + B bs (p + 8))) (odig (210 + B bs (p + 10))) (odig (0 + B bs (p + 11)))) in *.
             assert (HU2 : forall t, (8 <= t < 12)%Z -> not_qb (B bs (p + t))).
             { intros t Ht. assert (t = 8 \/ t = 9 \/ t = 10 \/ t = 11)%Z as [-> | [-> | [-> | ->]]] by lia.
               - apply (odig_valid_not_qb 630); [auto | lia].
               - apply (odig_valid_not_qb 420); [auto | lia].
               - apply (odig_valid_not_qb 210); [auto | lia].
               - apply (odig_valid_not_qb 0); [auto | lia]. }
             pose proof (PS_uu_store _ _ _ _ _ HPS K HU E6 HU2) as HST2.
             pose proof (PS_uu bs (q_i E) (q_j E) p d 4 HPS K HU E6 HU2 ltac:(lia)) as HPS12.
             clearbody v2.
             pa. pa.
             if_cases K9; zify_cond K9.
             ++ pa. pa. if_true.
                eapply evt_eq; [| eapply (psa_fail E OK)]; [s1_st_eq | exact INV].
             ++
                do 6 pa.
                eapply evt_eq; [| eapply (psa_enc4 E OK SHZ d (p + 12)%Z)]; [s1_st_eq | exact INV | lia | lia |].
                apply HK; [exact HPS12 | lia].
  Qed.
End U.
