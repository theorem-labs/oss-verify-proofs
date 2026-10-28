(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_strkit Sj_stage2_auto Sj_stage2_wkit Sj_stage2_strom.
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

Section StrOp.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Section Loop.
    Variables (Q : machine_state -> Prop) (dpt t40 i48 sbv r9 : Z) (sc : list (bool * Z)).
    Hypothesis KX : exit_k E Q.
    Hypothesis HGS : (Z.of_nat (length (e_sbs E)) = sbv)%Z.
    Notation headk := (Sj_stage2_strom.headk E Q dpt t40 i48 sbv sc).
    Notation stro_mb0s := (Sj_stage2_strom.stro_mb0s E OK SHZ Q dpt t40 i48 sbv sc KX HGS).
    Notation stro_mb0p := (Sj_stage2_strom.stro_mb0p E OK SHZ Q dpt t40 i48 sbv sc KX HGS).
    Variables (i j : Z) (kk Wv : Z).
    Hypothesis HROOM : (0 <= sbv /\ sbv + (j - i) + 4 <= e_scap E)%Z.
    Hypothesis HI0 : (0 <= i)%Z.
    Hypothesis H40 : t40 = (e_TAPE E + 8 * Wv)%Z.
    Hypothesis H48 : i48 = (e_IDX E + 4 * (kk + 1))%Z.
    Notation SLOTS j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j272 j288 j304 := ([CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; C8 (Z_to_bv 64 (e_SBUF E + sbv + 4)); C8 (Z_to_bv 64 (e_SBUF E + sbv + 4)); C8 (Z_to_bv 64 (18446744073709495296)); C8 (Z_to_bv 64 (23669)); C8 (Z_to_bv 64 (56320)); C8 (Z_to_bv 64 (dpt)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (t40)); C8 (Z_to_bv 64 (i48)); C8 (Z_to_bv 64 (e_SBUF E + sbv)); CB 8 j272; CB 8 j288; CB 8 j304]).
    Notation SLOTM j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j272 j288 j304 := ([CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; C8 (Z_to_bv 64 (e_SBUF E + sbv + 4)); C8 (Z_to_bv 64 (e_SBUF E + sbv + 4)); C8 (Z_to_bv 64 (18446744073709495296)); C8 (Z_to_bv 64 (23669)); C8 (Z_to_bv 64 (56320)); C8 (Z_to_bv 64 (dpt)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (t40)); C8 (Z_to_bv 64 (i48)); C8 (Z_to_bv 64 (e_SBUF E + sbv)); CB 8 j272; CB 8 j288; CB 8 j304]).

    Lemma stro_p : forall (fuel : nat) p d v, PS bs i j p d -> B bs p = 92%Z -> (j - p < Z.of_nat (S fuel))%Z ->
      (forall p' d', PS bs i j p' d' -> (j - p' < Z.of_nat fuel)%Z -> headk p' d') ->
      (forall t, (2 <= t < 6)%Z -> not_qb (B bs (p + t))) -> (0 <= v < 65536)%Z ->
      forall xa3 xa4 xa5 xs7 xs8 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
        MEMI E (e_nxt0 E) (SLOTM j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j272 j288 j304) sc fc m1 ->
        evt bsegs Q (S2R E 0xc24d0 (Z_to_bv 64 (146752)) (Z_to_bv 64 (92)) (Z_to_bv 64 (2)) (Z_to_bv 64 (117)) (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 (e_BUF E + p)) (Z_to_bv 64 (e_BUF E + p + 6)) xa3 xa4 xa5 (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 ((-1))) (Z_to_bv 64 (SHA (e_SBUF E + sbv + 4 + d))) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (55296)) (Z_to_bv 64 (18446744073709404863)) (Z_to_bv 64 (e_THIS E + 56)) xs7 xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (v)) (Z_to_bv 64 ((-2))) (Z_to_bv 64 ((-3))) (Z_to_bv 64 ((-4))) (Z_to_bv 64 (34)) F fc m1).
    Proof using OK SHZ HROOM HI0 KX HGS.
      intros fuel p d v HPS K HF IH HU RV xa3 xa4 xa5 xs7 xs8 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j272 j288 j304 F fc m1 HM.
      pose proof (PS_read _ _ _ _ _ HPS) as (HP0 & HPJ & HJL & HP11).
      pose proof (PS_store _ _ _ _ _ HPS) as (HD0 & HD4).
      pose proof (ok_bytes _ OK) as BOK.
      pose proof (B_range bs p BOK) as HB0. pose proof (B_range bs (p + 1) BOK) as HB1.
      pose proof (PS_u_store _ _ _ _ _ HPS K HU) as HST.
      pose proof (closes_u_le _ _ _ (ps_closes _ _ _ _ _ HPS) K HU) as HLE.
      s2_env OK.
      pose proof HM as HMo. s2_open_mem HMo.
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
                     grun_dec_to 0xcd104%Z. gexit KX.
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
                     wrun_to2 0xcd104%Z 0xc26ac%Z;
                     lazymatch goal with
                     | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                         lazymatch pc with
                         | 0xcd104%Z => gexit KX
                         | _ => replace (e_BUF E + p + 12)%Z with (e_BUF E + (p + 12))%Z by lia;
                                eapply (stro_mb0p (p + 12)%Z d); [lia | lia | wk_close | exact KH12]
                         end
                     end.
               ++
                  wrun_to 0xcd104%Z. gexit KX.
    Qed.
  End Loop.
End StrOp.
