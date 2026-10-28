(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_strkit Sj_stage2_auto Sj_stage2_wkit Sj_stage2_strbm Sj_stage2_strbp.
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

Section StrBu.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Section Loop.
    Variables (Q : machine_state -> Prop) (dpt t40 i48 sbv r9 : Z) (sc : list (bool * Z)).
    Hypothesis KX : exit_k E Q.
    Hypothesis HGS : (Z.of_nat (length (e_sbs E)) = sbv)%Z.
    Notation headk := (Sj_stage2_strbm.headk E Q dpt t40 i48 sbv sc).
    Notation strb_mb0s := (Sj_stage2_strbm.strb_mb0s E OK SHZ Q dpt t40 i48 sbv sc KX HGS).
    Notation strb_mb0p := (Sj_stage2_strbm.strb_mb0p E OK SHZ Q dpt t40 i48 sbv sc KX HGS).
    Variables (i j : Z) (kk Wv : Z).
    Hypothesis HROOM : (0 <= sbv /\ sbv + (j - i) + 4 <= e_scap E)%Z.
    Hypothesis HI0 : (0 <= i)%Z.
    Hypothesis H40 : t40 = (e_TAPE E + 8 * Wv)%Z.
    Hypothesis H48 : i48 = (e_IDX E + 4 * kk)%Z.
    Notation strb_p := (Sj_stage2_strbp.strb_p E OK SHZ Q dpt t40 i48 sbv sc KX HGS i j HROOM HI0).
    Notation SLOTS j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j272 j288 j304 := ([CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_SBUF E + sbv + 4)); C8 (Z_to_bv 64 (18446744073709495296)); C8 (Z_to_bv 64 (23669)); C8 (Z_to_bv 64 (56320)); C8 (Z_to_bv 64 (dpt)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (t40)); C8 (Z_to_bv 64 (i48)); C8 (Z_to_bv 64 (e_SBUF E + sbv)); CB 8 j272; CB 8 j288; CB 8 j304]).
    Notation SLOTM j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j288 j304 := ([CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_SBUF E + sbv + 4)); C8 (Z_to_bv 64 (18446744073709495296)); C8 (Z_to_bv 64 (23669)); C8 (Z_to_bv 64 (56320)); C8 (Z_to_bv 64 (dpt)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (t40)); C8 (Z_to_bv 64 (i48)); C8 (Z_to_bv 64 (e_SBUF E + sbv)); C8 (Z_to_bv 64 (5)); CB 8 j288; CB 8 j304]).

    Lemma strb_u : forall (fuel : nat) p d, PS bs i j p d -> B bs p = 92%Z -> (j - p < Z.of_nat (S fuel))%Z ->
      (forall p' d', PS bs i j p' d' -> (j - p' < Z.of_nat fuel)%Z -> headk p' d') ->
      forall xra xa1 xa2 xa3 xa4 xs11 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
        MEMI E (e_nxt0 E) (SLOTS j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j272 j288 j304) sc fc m1 ->
        evt bsegs Q (S2R E 0xcd968 xra (Z_to_bv 64 (2)) (Z_to_bv 64 (117)) (Z_to_bv 64 ((-2))) (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + p)) xa1 xa2 xa3 xa4 (Z_to_bv 64 (18446744073709403551)) (Z_to_bv 64 ((-1))) (Z_to_bv 64 (92)) (Z_to_bv 64 (SHA (e_SBUF E + sbv + 4 + d))) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (148064)) (Z_to_bv 64 (e_SBUF E + sbv + 4 + d)) (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (55296)) (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 (Z_to_bv 64 ((-3))) (Z_to_bv 64 ((-4))) (Z_to_bv 64 (34)) xt6 F fc m1).
    Proof using OK SHZ HROOM HI0 KX HGS.
      intros fuel p d HPS K HF IH xra xa1 xa2 xa3 xa4 xs11 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j272 j288 j304 F fc m1 HM.
      pose proof (PS_read _ _ _ _ _ HPS) as (HP0 & HPJ & HJL & HP11).
      pose proof (PS_store _ _ _ _ _ HPS) as (HD0 & HD4).
      pose proof (ok_bytes _ OK) as BOK.
      pose proof (B_range bs p BOK) as HB0. pose proof (B_range bs (p + 1) BOK) as HB1.
      s2_env OK.
      pose proof HM as HMo. s2_open_mem HMo.
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
            grun_dec_to 0xcd488%Z. gexit KX.
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
               eapply (strb_p fuel p d v HPS K HF IH HU RV); wk_close.
            -- wrun.
               if_cases_eq K3.
               ++
                  wrun_to 0xcd488%Z. gexit KX.
               ++
                  wrun_to 0xcdac4%Z.
                  replace (e_BUF E + p + 6)%Z with (e_BUF E + (p + 6))%Z by lia.
                  eapply (strb_mb0s (p + 6)%Z d); [lia | lia | wk_close | exact KH6].
    Qed.
  End Loop.
End StrBu.
