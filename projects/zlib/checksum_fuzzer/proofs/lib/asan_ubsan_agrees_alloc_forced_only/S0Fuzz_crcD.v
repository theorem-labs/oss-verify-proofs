(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem S0FuzzBase S0Fuzz_code FuzzCrcLib S0Fuzz_crcA S0Fuzz_crcB.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathCrc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque ctab btab crc_byte.
Section FXG. Context {fx : FPState}.

Section CRCD.
  Variables (m rom : word -> option byte) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn RSEGS m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.

  #[local] Abbreviation BA := (byte_at RSEGS m).

  Ltac solve_kb := first [ assumption | apply lkeeps_refl | solve_lkeeps
                         | eapply lkeeps_trans; [eassumption|]; first [assumption | solve_lkeeps | eapply lkeeps_trans; eassumption] ].
  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_kb ].
  Lemma rng32_64 : forall x, 0 <= x < two32 -> 0 <= x < two64.
  Proof. intros. lia. Qed.
  Ltac crc_rng := first [ assumption | apply crc_byte_range; crc_rng | apply crc_bytes_range; crc_rng
                         | apply rng32_64; crc_rng | lia ].

  Ltac lbu_pl F D Hb Eb :=
    chain_step;
    [ reflexivity
    | eapply step_lbu; [exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ =>
          match type of Hb with rdn _ _ (Z_to_bv 64 ?y) _ = _ => replace x with y by lia end end;
        exact Hb ]
    | step_simpl; gres; rewrite Eb ].

  Ltac lwu_ctab F D idx :=
    chain_step;
    [ reflexivity
    | eapply step_lwu with (v := Z_to_bv 64 (ctab idx));
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with (CTAB + 4 * idx) by (unfold CTAB; lia) end;
        apply rd_ctab; [exact Himg | apply land_255_range]
      | apply ctab_bs_v; apply land_255_range ]
    | step_simpl; gres ].


  Lemma al_step : forall regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 13 = Z_to_bv 64 (a + 1) ->
    getr regs 15 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 c ->
    0 <= c < two32 -> adr0 <= a < adr0 + len0 -> 2 <= n < two64 ->
    exists r, msteps RSEGS (mkst regs (0x145d8 : word) m rom) (mkst r (0x14610 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 (a + 1) /\ getr r 13 = Z_to_bv 64 (a + 1 + 1)
      /\ getr r 15 = Z_to_bv 64 1 /\ getr r 12 = Z_to_bv 64 (n - 1) /\ getr r 14 = Z_to_bv 64 (crc_byte c (BA a))
      /\ getr r 16 = Z_to_bv 64 ((a + 1) mod 4)
      /\ lkeeps KB regs r.
  Proof.
    intros regs c a n R10 R11 R13 R15 R12 R14 Hc Ha Hn.
    destruct (rd1 m adr0 len0 Hrd a Ha) as (b & Hb & Eb).
    eexists. split.
    - lbu_pl F_14578 D_14578 Hb Eb.
      stepz F_1457c D_1457c.
      stepz F_14580 D_14580. stepz F_14584 D_14584. stepz F_14588 D_14588. stepz F_1458c D_1458c.
      lwu_ctab F_14590 D_14590 (Z.land (Z.lxor (BA a) c) 255).
      stepz F_14594 D_14594.
      stepi F_14598 D_14598; znorm. rewrite (zv_srli c 8) by crc_rng.
      stepz F_1459c D_1459c.
      stepz F_145a0 D_145a0.
      change (Z.lxor (Z.shiftr c 8) (ctab (Z.land (Z.lxor (BA a) c) 255))) with (crc_byte c (BA a)).
      stepb_ft F_145a4 D_145a4 ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
      stepz F_145a8 D_145a8. rewrite land_3_mod.
      stepz F_145ac D_145ac.
      apply mst_refl.
    - post.
  Qed.

  Lemma al_loop : forall (k : nat) regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 13 = Z_to_bv 64 (a + 1) ->
    getr regs 15 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 c ->
    0 <= c < two32 -> adr0 <= a -> a + Z.of_nat k <= adr0 + len0 -> Z.of_nat k + 1 <= n < two64 ->
    a mod 4 <> 0 -> align4 a = Z.of_nat k ->
    exists r, msteps RSEGS (mkst regs (0x145d8 : word) m rom) (mkst r (0x14614 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 (a + Z.of_nat k)
      /\ getr r 12 = Z_to_bv 64 (n - Z.of_nat k)
      /\ getr r 14 = Z_to_bv 64 (crc_bytes c (bl BA a k))
      /\ lkeeps KB regs r.
  Proof.
    induction k as [|k IH]; intros regs c a n R10 R11 R13 R15 R12 R14 Hc Ha Hak Hn Hmod Hal.
    - exfalso. apply Hmod. apply (proj2 (align4_zero a)). exact Hal.
    - destruct (al_step regs c a n R10 R11 R13 R15 R12 R14 Hc ltac:(lia) ltac:(lia))
        as (r1 & M1 & S10 & S11 & S13 & S15 & S12 & S14 & S16 & K1).
      destruct (align4_cases a Hmod) as [[Ha1 Hz] | (Ha23 & Hnz & Hal')].
      +
        assert (k = 0%nat) by lia. subst k.
        eexists. split; [|split; [|split; [|split; [|split]]]].
        * eapply msteps_trans; [exact M1|].
          stepb_ft F_145b0 D_145b0 ltac:(rwR; rewrite Hz; rewrite zc_eq by lia; reflexivity).
          apply mst_refl.
        * gres. exact S10.
        * gres. rewrite S11. zbv.
        * gres. rewrite S12. zbv.
        * gres. rewrite S14. cbn [bl]. rewrite crc_bytes_cons, crc_bytes_nil. reflexivity.
        * solve_kb.
      + pose proof (Z.mod_pos_bound (a + 1) 4 ltac:(lia)) as Hm4.
        destruct (IH r1 (crc_byte c (BA a)) (a + 1) (n - 1) S10 S11 S13 S15 S12 S14 ltac:(crc_rng)
                    ltac:(lia) ltac:(lia) ltac:(lia) Hnz ltac:(lia)) as (r2 & M2 & T10 & T11 & T12 & T14 & K2).
        exists r2. split; [|split; [|split; [|split; [|split]]]].
        * eapply msteps_trans; [exact M1|].
          stepb_tk F_145b0 D_145b0 ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
          exact M2.
        * exact T10.
        * rewrite T11. zbv.
        * rewrite T12. zbv.
        * rewrite T14. cbn [bl]. rewrite crc_bytes_cons. reflexivity.
        * solve_kb.
  Qed.

  Lemma al_run : forall regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 c ->
    0 <= c < two32 -> adr0 <= a -> a + n <= adr0 + len0 -> 23 <= n < two64 ->
    exists r, msteps RSEGS (mkst regs (0x145c8 : word) m rom) (mkst r (0x14614 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 (a + align4 a)
      /\ getr r 12 = Z_to_bv 64 (n - align4 a)
      /\ getr r 14 = Z_to_bv 64 (crc_bytes c (bl BA a (Z.to_nat (align4 a))))
      /\ lkeeps KB regs r.
  Proof.
    intros regs c a n R10 R11 R12 R14 Hc Ha Han Hn.
    pose proof (align4_range a) as Har. pose proof (Z.mod_pos_bound a 4 ltac:(lia)) as Hm4.
    destruct (Z.eq_dec (a mod 4) 0) as [Hz | Hnz].
    - pose proof (proj1 (align4_zero a) Hz) as Ha0'.
      eexists. split; [|split; [|split; [|split; [|split]]]].
      + stepz F_14568 D_14568. rewrite land_3_mod, Hz.
        stepb_tk F_1456c D_1456c ltac:(rewrite zc_eq by lia; reflexivity).
        apply mst_refl.
      + post.
      + post.
      + post.
      + gres. rewrite R14, Ha0'. cbn [Z.to_nat bl]. rewrite crc_bytes_nil. reflexivity.
      + solve_kb.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x145d8 : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 a /\ getr r 13 = Z_to_bv 64 (a + 1)
                         /\ getr r 15 = Z_to_bv 64 1 /\ getr r 12 = Z_to_bv 64 n /\ getr r 14 = Z_to_bv 64 c
                         /\ lkeeps KB regs r)).
      { eexists. split.
        - stepz F_14568 D_14568. rewrite land_3_mod.
          stepb_ft F_1456c D_1456c ltac:(rewrite zc_eq by lia; apply Z.eqb_neq; lia).
          stepz F_14570 D_14570. stepz F_14574 D_14574.
          apply mst_refl.
        - post. }
      cbv beta. intros r1 (S10 & S11 & S13 & S15 & S12 & S14 & K1).
      destruct (al_loop (Z.to_nat (align4 a)) r1 c a n S10 S11 S13 S15 S12 S14 Hc Ha ltac:(lia) ltac:(lia) Hnz ltac:(lia))
        as (r2 & M2 & T10 & T11 & T12 & T14 & K2).
      exists r2. split; [exact M2|]. rewrite Z2Nat.id in T11, T12 by lia.
      repeat split; try assumption. solve_kb.
  Qed.


  Definition BK (regs r : bvmap 5 word) (c a n : Z) : Prop :=
    getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 a /\ getr r 12 = Z_to_bv 64 n /\ getr r 14 = Z_to_bv 64 c
    /\ getr r 6 = Z_to_bv 64 (n / 20) /\ getr r 13 = Z_to_bv 64 (n / 20 * -20) /\ getr r 16 = Z_to_bv 64 1
    /\ getr r 15 = Z_to_bv 64 (-20) /\ lkeeps KB regs r.

  Lemma blks_calc : forall regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 c -> 0 <= n < two64 ->
    exists r, msteps RSEGS (mkst regs (0x14614 : word) m rom) (mkst r (0x14638 : word) m rom)
      /\ BK regs r c a n.
  Proof.
    intros regs c a n R10 R11 R12 R14 Hn.
    pose proof (mulhu_range n MAGIC20 ltac:(lia) ltac:(unfold MAGIC20; lia)) as Hm.
    eexists. split.
    - stepz F_145b4 D_145b4. stepz F_145b8 D_145b8. stepz F_145bc D_145bc. stepz F_145c0 D_145c0.
      stepz F_145c4 D_145c4.
      replace (Z_to_bv 64 79228162529021732852511591629) with (Z_to_bv 64 14757395258967641293)
        by (apply zv_eq; vm_compute; reflexivity).
      stepi F_145c8 D_145c8; znorm. rewrite (zv_mulhu n 14757395258967641293) by lia.
      stepi F_145cc D_145cc; znorm. change 14757395258967641293 with MAGIC20.
      rewrite (zv_srli (n * MAGIC20 / two64) 4) by exact Hm. rewrite (magic20_div n) by lia.
      stepz F_145d0 D_145d0.
      stepz F_145d4 D_145d4.
      apply mst_refl.
    - unfold BK. post.
  Qed.

  Lemma blks_run2 : forall regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 c -> 0 <= n < two64 -> 2 <= n / 20 ->
    exists r, msteps RSEGS (mkst regs (0x14614 : word) m rom) (mkst r (0x14674 : word) m rom)
      /\ BH r c 0 0 0 0 a
      /\ getr r 6 = Z_to_bv 64 (a + 20 * Z.of_nat (Z.to_nat (n / 20 - 1)))
      /\ getr r 13 = Z_to_bv 64 (n / 20 * -20) /\ getr r 12 = Z_to_bv 64 n /\ getr r 10 = Z_to_bv 64 CTAB
      /\ lkeeps KB regs r.
  Proof.
    intros regs c a n R10 R11 R12 R14 Hn Hb.
    destruct (blks_calc regs c a n R10 R11 R12 R14 Hn) as (r1 & M1 & S10 & S11 & S12 & S14 & S6 & S13 & S16 & S15 & K1).
    pose proof (Z.div_le_upper_bound n 20 n ltac:(lia) ltac:(lia)) as Hq1.
    eexists. split.
    - eapply msteps_trans; [exact M1|].
      stepb_ft F_145d8 D_145d8 ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
      stepz F_145dc D_145dc. stepz F_145e0 D_145e0. stepz F_145e4 D_145e4. stepz F_145e8 D_145e8.
      stepz F_145ec D_145ec.
      stepi F_145f0 D_145f0; gres; match goal with |- context [v_auipc ?p ?i] => wlit_closed (v_auipc p i) end.
      stepz F_145f4 D_145f4. stepz F_145f8 D_145f8.
      stepz F_145fc D_145fc. stepz F_14600 D_14600. stepz F_14604 D_14604. stepz F_14608 D_14608.
      stepz F_1460c D_1460c. stepz F_14610 D_14610.
      apply mst_refl.
    - unfold BH. post.
  Qed.

  Lemma blks_run1 : forall regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 c -> 0 <= n < two64 -> n / 20 = 1 ->
    exists r, msteps RSEGS (mkst regs (0x14614 : word) m rom) (mkst r (0x14840 : word) m rom)
      /\ (getr r 14 = Z_to_bv 64 c /\ getr r 5 = Z_to_bv 64 0 /\ getr r 17 = Z_to_bv 64 0
          /\ getr r 16 = Z_to_bv 64 0 /\ getr r 15 = Z_to_bv 64 0)
      /\ getr r 11 = Z_to_bv 64 a
      /\ getr r 13 = Z_to_bv 64 (n / 20 * -20) /\ getr r 12 = Z_to_bv 64 n /\ getr r 10 = Z_to_bv 64 CTAB
      /\ lkeeps KB regs r.
  Proof.
    intros regs c a n R10 R11 R12 R14 Hn Hb.
    destruct (blks_calc regs c a n R10 R11 R12 R14 Hn) as (r1 & M1 & S10 & S11 & S12 & S14 & S6 & S13 & S16 & S15 & K1).
    eexists. split.
    - eapply msteps_trans; [exact M1|]. rewrite Hb in S6.
      stepb_tk F_145d8 D_145d8 ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_eq; lia).
      stepz F_147d0 D_147d0. stepz F_147d4 D_147d4. stepz F_147d8 D_147d8. stepz F_147dc D_147dc.
      apply mst_refl.
    - post.
  Qed.
End CRCD.
End FXG.
