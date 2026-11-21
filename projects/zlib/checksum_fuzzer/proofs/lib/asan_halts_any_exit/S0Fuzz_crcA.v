(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem S0FuzzBase S0Fuzz_code FuzzCrcLib.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque ctab btab crc_byte.
Section FXG. Context {fx : FPState}.

Definition KB : list reg := [1; 2; 3; 4; 25; 26; 27]%bv.

Section CRC.
  Variables (m rom : word -> option byte) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn RSEGS m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.

  #[local] Abbreviation BA := (byte_at RSEGS m).

  Lemma rd1 : forall a, adr0 <= a < adr0 + len0 ->
    exists b : byte, rdn RSEGS m (Z_to_bv 64 a) 1 = Some [b] /\ Z_to_bv 64 (bv_unsigned b) = Z_to_bv 64 (BA a).
  Proof.
    intros a Ha. destruct (Hrd (a - adr0) ltac:(lia)) as [b Hb].
    replace (adr0 + (a - adr0)) with a in Hb by lia.
    exists b. split; [exact Hb | apply (rdn_byte_at_v RSEGS), Hb].
  Qed.

  Lemma BA_range : forall a, 0 <= BA a < 256.
  Proof. intros. apply byte_at_range. Qed.

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

  Ltac srli8 F D cv := stepi F D; znorm; rewrite (zv_srli cv 8) by crc_rng.

  Ltac fold_crc :=
    match goal with |- context [Z_to_bv 64 (Z.lxor (Z.shiftr ?c 8) (ctab (Z.land (Z.lxor ?b ?c) 255)))] =>
      change (Z.lxor (Z.shiftr c 8) (ctab (Z.land (Z.lxor b c) 255))) with (crc_byte c b) end.


  Lemma t1_body : forall regs (c a : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    0 <= c < two32 -> adr0 <= a < adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14b88 : word) m rom) (mkst r (0x14bb0 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 (a + 1) /\ getr r 16 = Z_to_bv 64 (a + 1)
      /\ getr r 14 = Z_to_bv 64 (crc_byte c (BA a))
      /\ getr r 12 = getr regs 12 /\ getr r 13 = getr regs 13
      /\ lkeeps KB regs r.
  Proof.
    intros regs c a R10 R11 R14 Hc Ha.
    destruct (rd1 a Ha) as (b & Hb & Eb).
    eexists. split.
    - lbu_pl F_14b28 D_14b28 Hb Eb.
      stepz F_14b2c D_14b2c.
      stepz F_14b30 D_14b30.
      stepz F_14b34 D_14b34.
      stepz F_14b38 D_14b38.
      lwu_ctab F_14b3c D_14b3c (Z.land (Z.lxor (BA a) c) 255).
      srli8 F_14b40 D_14b40 c.
      stepz F_14b44 D_14b44.
      stepz F_14b48 D_14b48. fold_crc.
      stepz F_14b4c D_14b4c.
      apply mst_refl.
    - post.
  Qed.

  Lemma t1_loop : forall (k : nat) regs (c a : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 12 = Z_to_bv 64 (a + Z.of_nat (S k)) ->
    0 <= c < two32 -> adr0 <= a -> a + Z.of_nat (S k) <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14b88 : word) m rom) (mkst r (0x14bb4 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (crc_bytes c (bl BA a (S k)))
      /\ getr r 13 = getr regs 13
      /\ lkeeps KB regs r.
  Proof.
    induction k as [|k IH]; intros regs c a R10 R11 R14 R12 Hc Ha Hk.
    - destruct (t1_body regs c a R10 R11 R14 Hc ltac:(lia)) as (r1 & M1 & S10 & S11 & S16 & S14 & S12 & S13 & K1).
      rewrite R12 in S12.
      eexists. split; [|split; [|split]].
      + eapply msteps_trans; [exact M1|].
        stepb_ft F_14b50 D_14b50 ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_eq; lia).
        apply mst_refl.
      + gres. rewrite S14. reflexivity.
      + gres. exact S13.
      + solve_kb.
    - destruct (t1_body regs c a R10 R11 R14 Hc ltac:(lia)) as (r1 & M1 & S10 & S11 & S16 & S14 & S12 & S13 & K1).
      rewrite R12 in S12.
      assert (S12' : getr r1 12 = Z_to_bv 64 (a + 1 + Z.of_nat (S k))) by (rewrite S12; f_equal; lia).
      destruct (IH r1 (crc_byte c (BA a)) (a + 1) S10 S11 S14 S12' ltac:(crc_rng) ltac:(lia) ltac:(lia))
        as (r2 & M2 & T14 & T13 & K2).
      exists r2. split; [|split; [|split]].
      + eapply msteps_trans; [exact M1|].
        stepb_tk F_14b50 D_14b50 ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
        exact M2.
      + exact T14.
      + rewrite T13. exact S13.
      + solve_kb.
  Qed.


  Lemma t8_h1 : forall regs (c a : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    0 <= c < two32 -> adr0 <= a -> a + 8 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14a70 : word) m rom) (mkst r (0x14af0 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 a
      /\ getr r 14 = Z_to_bv 64 (crc_byte (crc_byte (crc_byte (crc_byte c (BA a)) (BA (a + 1))) (BA (a + 2))) (BA (a + 3)))
      /\ getr r 12 = getr regs 12 /\ getr r 13 = getr regs 13 /\ getr r 15 = getr regs 15
      /\ lkeeps KB regs r.
  Proof.
    intros regs c a R10 R11 R14 Hc Ha Ha8.
    destruct (rd1 a ltac:(lia)) as (b0 & Hb0 & Eb0).
    destruct (rd1 (a + 1) ltac:(lia)) as (b1 & Hb1 & Eb1).
    destruct (rd1 (a + 2) ltac:(lia)) as (b2 & Hb2 & Eb2).
    destruct (rd1 (a + 3) ltac:(lia)) as (b3 & Hb3 & Eb3).
    eexists. split.
    - lbu_pl F_14a10 D_14a10 Hb0 Eb0.
      lbu_pl F_14a14 D_14a14 Hb1 Eb1.
      lbu_pl F_14a18 D_14a18 Hb2 Eb2.
      lbu_pl F_14a1c D_14a1c Hb3 Eb3.
      stepz F_14a20 D_14a20. stepz F_14a24 D_14a24. stepz F_14a28 D_14a28. stepz F_14a2c D_14a2c.
      lwu_ctab F_14a30 D_14a30 (Z.land (Z.lxor (BA a) c) 255).
      srli8 F_14a34 D_14a34 c.
      stepz F_14a38 D_14a38. fold_crc.
      stepz F_14a3c D_14a3c. stepz F_14a40 D_14a40. stepz F_14a44 D_14a44. stepz F_14a48 D_14a48.
      lwu_ctab F_14a4c D_14a4c (Z.land (Z.lxor (BA (a + 1)) (crc_byte c (BA a))) 255).
      srli8 F_14a50 D_14a50 (crc_byte c (BA a)).
      stepz F_14a54 D_14a54. fold_crc.
      stepz F_14a58 D_14a58. stepz F_14a5c D_14a5c. stepz F_14a60 D_14a60. stepz F_14a64 D_14a64.
      lwu_ctab F_14a68 D_14a68 (Z.land (Z.lxor (BA (a + 2)) (crc_byte (crc_byte c (BA a)) (BA (a + 1)))) 255).
      srli8 F_14a6c D_14a6c (crc_byte (crc_byte c (BA a)) (BA (a + 1))).
      stepz F_14a70 D_14a70. fold_crc.
      stepz F_14a74 D_14a74. stepz F_14a78 D_14a78. stepz F_14a7c D_14a7c. stepz F_14a80 D_14a80.
      lwu_ctab F_14a84 D_14a84 (Z.land (Z.lxor (BA (a + 3)) (crc_byte (crc_byte (crc_byte c (BA a)) (BA (a + 1))) (BA (a + 2)))) 255).
      srli8 F_14a88 D_14a88 (crc_byte (crc_byte (crc_byte c (BA a)) (BA (a + 1))) (BA (a + 2))).
      stepz F_14a8c D_14a8c. fold_crc.
      apply mst_refl.
    - post.
  Qed.

  Lemma t8_h2 : forall regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 12 = Z_to_bv 64 n ->
    0 <= c < two32 -> adr0 <= a -> a + 8 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14af0 : word) m rom) (mkst r (0x14b78 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 (a + 8) /\ getr r 12 = Z_to_bv 64 (n - 8)
      /\ getr r 14 = Z_to_bv 64 (crc_byte (crc_byte (crc_byte (crc_byte c (BA (a + 4))) (BA (a + 5))) (BA (a + 6))) (BA (a + 7)))
      /\ getr r 13 = getr regs 13 /\ getr r 15 = getr regs 15
      /\ lkeeps KB regs r.
  Proof.
    intros regs c a n R10 R11 R14 R12 Hc Ha Ha8.
    destruct (rd1 (a + 4) ltac:(lia)) as (b0 & Hb0 & Eb0).
    destruct (rd1 (a + 5) ltac:(lia)) as (b1 & Hb1 & Eb1).
    destruct (rd1 (a + 6) ltac:(lia)) as (b2 & Hb2 & Eb2).
    destruct (rd1 (a + 7) ltac:(lia)) as (b3 & Hb3 & Eb3).
    eexists. split.
    - lbu_pl F_14a90 D_14a90 Hb0 Eb0.
      lbu_pl F_14a94 D_14a94 Hb1 Eb1.
      lbu_pl F_14a98 D_14a98 Hb2 Eb2.
      lbu_pl F_14a9c D_14a9c Hb3 Eb3.
      stepz F_14aa0 D_14aa0. stepz F_14aa4 D_14aa4. stepz F_14aa8 D_14aa8. stepz F_14aac D_14aac.
      lwu_ctab F_14ab0 D_14ab0 (Z.land (Z.lxor (BA (a + 4)) c) 255).
      srli8 F_14ab4 D_14ab4 c.
      stepz F_14ab8 D_14ab8. fold_crc.
      stepz F_14abc D_14abc. stepz F_14ac0 D_14ac0. stepz F_14ac4 D_14ac4. stepz F_14ac8 D_14ac8.
      lwu_ctab F_14acc D_14acc (Z.land (Z.lxor (BA (a + 5)) (crc_byte c (BA (a + 4)))) 255).
      srli8 F_14ad0 D_14ad0 (crc_byte c (BA (a + 4))).
      stepz F_14ad4 D_14ad4. fold_crc.
      stepz F_14ad8 D_14ad8. stepz F_14adc D_14adc. stepz F_14ae0 D_14ae0. stepz F_14ae4 D_14ae4.
      lwu_ctab F_14ae8 D_14ae8 (Z.land (Z.lxor (BA (a + 6)) (crc_byte (crc_byte c (BA (a + 4))) (BA (a + 5)))) 255).
      srli8 F_14aec D_14aec (crc_byte (crc_byte c (BA (a + 4))) (BA (a + 5))).
      stepz F_14af0 D_14af0. fold_crc.
      stepz F_14af4 D_14af4. stepz F_14af8 D_14af8. stepz F_14afc D_14afc. stepz F_14b00 D_14b00.
      lwu_ctab F_14b04 D_14b04 (Z.land (Z.lxor (BA (a + 7)) (crc_byte (crc_byte (crc_byte c (BA (a + 4))) (BA (a + 5))) (BA (a + 6)))) 255).
      stepz F_14b08 D_14b08.
      srli8 F_14b0c D_14b0c (crc_byte (crc_byte (crc_byte c (BA (a + 4))) (BA (a + 5))) (BA (a + 6))).
      stepz F_14b10 D_14b10.
      stepz F_14b14 D_14b14. fold_crc.
      apply mst_refl.
    - post.
  Qed.

  Lemma bl8 : forall a, bl BA a 8 = [BA a; BA (a + 1); BA (a + 2); BA (a + 3); BA (a + 4); BA (a + 5); BA (a + 6); BA (a + 7)].
  Proof.
    intros a. cbn [bl].
    repeat match goal with
           | |- (_ :: _) = (_ :: _) => apply (f_equal2 (@cons Z))
           | |- byte_at _ _ _ = byte_at _ _ _ => f_equal; lia
           | |- @nil _ = @nil _ => reflexivity
           end.
  Qed.

  Lemma t8_iter : forall regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 12 = Z_to_bv 64 n ->
    0 <= c < two32 -> adr0 <= a -> a + 8 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14a70 : word) m rom) (mkst r (0x14b78 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 (a + 8) /\ getr r 12 = Z_to_bv 64 (n - 8)
      /\ getr r 14 = Z_to_bv 64 (crc_bytes c (bl BA a 8))
      /\ getr r 13 = getr regs 13 /\ getr r 15 = getr regs 15
      /\ lkeeps KB regs r.
  Proof.
    intros regs c a n R10 R11 R14 R12 Hc Ha Ha8.
    destruct (t8_h1 regs c a R10 R11 R14 Hc Ha Ha8) as (r1 & M1 & S10 & S11 & S14 & S12 & S13 & S15 & K1).
    rewrite R12 in S12.
    destruct (t8_h2 r1 _ a n S10 S11 S14 S12 ltac:(crc_rng) Ha Ha8) as (r2 & M2 & T10 & T11 & T12 & T14 & T13 & T15 & K2).
    exists r2. split; [eapply msteps_trans; [exact M1 | exact M2]|].
    rewrite T13, T15, S13, S15. repeat split; try assumption.
    - rewrite T14, bl8, crc_bytes8. reflexivity.
    - solve_kb.
  Qed.

  Lemma t8_loop : forall (q : nat) regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 15 = Z_to_bv 64 7 ->
    0 <= c < two32 -> adr0 <= a -> a + n <= adr0 + len0 ->
    (1 <= q)%nat -> 8 * Z.of_nat q <= n < 8 * Z.of_nat q + 8 ->
    exists r, msteps RSEGS (mkst regs (0x14a70 : word) m rom) (mkst r (0x14b7c : word) m rom)
      /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 (a + 8 * Z.of_nat q)
      /\ getr r 12 = Z_to_bv 64 (n - 8 * Z.of_nat q)
      /\ getr r 14 = Z_to_bv 64 (crc_bytes c (bl BA a (8 * q)))
      /\ getr r 13 = getr regs 13
      /\ lkeeps KB regs r.
  Proof.
    induction q as [|q IH]; intros regs c a n R10 R11 R14 R12 R15 Hc Ha Han Hq Hn; [lia|].
    destruct (t8_iter regs c a n R10 R11 R14 R12 Hc Ha ltac:(lia)) as (r1 & M1 & S10 & S11 & S12 & S14 & S13 & S15 & K1).
    rewrite R15 in S15.
    destruct (Nat.eq_dec q 0) as [-> | Hq'].
    - eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      + eapply msteps_trans; [exact M1|].
        stepb_ft F_14b18 D_14b18 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_ge; lia).
        apply mst_refl.
      + gres. exact S10.
      + gres. rewrite S11. zbv.
      + gres. rewrite S12. zbv.
      + gres. rewrite S14. change (8 * 1)%nat with 8%nat. reflexivity.
      + gres. exact S13.
      + solve_kb.
    - destruct (IH r1 (crc_bytes c (bl BA a 8)) (a + 8) (n - 8) S10 S11 S14 S12 S15 ltac:(crc_rng) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia)) as (r2 & M2 & T10 & T11 & T12 & T14 & T13 & K2).
      exists r2. split; [|split; [|split; [|split; [|split; [|split]]]]].
      + eapply msteps_trans; [exact M1|].
        stepb_tk F_14b18 D_14b18 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_lt; lia).
        exact M2.
      + exact T10.
      + rewrite T11. zbv.
      + rewrite T12. zbv.
      + rewrite T14. replace (8 * S q)%nat with (8 + 8 * q)%nat by lia.
        rewrite bl_app, crc_bytes_app. change (Z.of_nat 8) with 8. reflexivity.
      + rewrite T13. exact S13.
      + solve_kb.
  Qed.

  Lemma tailB_run : forall regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 (-1) ->
    0 <= c < two32 -> adr0 <= a -> a + n <= adr0 + len0 -> 0 <= n ->
    exists r, msteps RSEGS (mkst regs (0x14b7c : word) m rom) (mkst r (0x14bb4 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (crc_bytes c (bl BA a (Z.to_nat n)))
      /\ getr r 13 = Z_to_bv 64 M32
      /\ lkeeps KB regs r.
  Proof.
    intros regs c a n R10 R11 R14 R12 R13 Hc Ha Han Hn.
    destruct (Z.eq_dec n 0) as [-> | Hnz].
    - eexists. split; [|split; [|split]].
      + stepi F_14b1c D_14b1c; znorm.
        replace (v_srli (Z_to_bv 64 (-1)) 32) with (Z_to_bv 64 M32) by (apply bv_eq; vm_compute; reflexivity).
        stepb_tk F_14b20 D_14b20 ltac:(rwR; rewrite zc_eq by lia; reflexivity).
        apply mst_refl.
      + gres. rewrite R14. change (Z.to_nat 0) with 0%nat. rewrite crc_bytes_nil. reflexivity.
      + gres. reflexivity.
      + solve_kb.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x14b88 : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 a /\ getr r 14 = Z_to_bv 64 c
                         /\ getr r 12 = Z_to_bv 64 (a + Z.of_nat (S (Z.to_nat (n - 1)))) /\ getr r 13 = Z_to_bv 64 M32
                         /\ lkeeps KB regs r)).
      { eexists. split.
        - stepi F_14b1c D_14b1c; znorm.
          replace (v_srli (Z_to_bv 64 (-1)) 32) with (Z_to_bv 64 M32) by (apply bv_eq; vm_compute; reflexivity).
          stepb_ft F_14b20 D_14b20 ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
          stepz F_14b24 D_14b24.
          apply mst_refl.
        - post. }
      cbv beta. intros r1 (S10 & S11 & S14 & S12 & S13 & K1).
      destruct (t1_loop (Z.to_nat (n - 1)) r1 c a S10 S11 S14 S12 Hc Ha ltac:(lia)) as (r2 & M2 & T14 & T13 & K2).
      exists r2. split; [exact M2|]. split; [|split].
      + rewrite T14. replace (S (Z.to_nat (n - 1))) with (Z.to_nat n) by lia. reflexivity.
      + rewrite T13. exact S13.
      + solve_kb.
  Qed.

  Lemma tail_run : forall regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 12 = Z_to_bv 64 n ->
    0 <= c < two32 -> adr0 <= a -> a + n <= adr0 + len0 -> 0 <= n ->
    exists r, msteps RSEGS (mkst regs (0x14a60 : word) m rom) (mkst r (0x14bb4 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (crc_bytes c (bl BA a (Z.to_nat n)))
      /\ getr r 13 = Z_to_bv 64 M32
      /\ lkeeps KB regs r.
  Proof.
    intros regs c a n R10 R11 R14 R12 Hc Ha Han Hn.
    destruct (Z.lt_ge_cases n 8) as [Hs | Hb].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x14b7c : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 a /\ getr r 14 = Z_to_bv 64 c
                         /\ getr r 12 = Z_to_bv 64 n /\ getr r 13 = Z_to_bv 64 (-1) /\ lkeeps KB regs r)).
      { eexists. split.
        - stepz F_14a00 D_14a00. stepz F_14a04 D_14a04.
          stepb_tk F_14a08 D_14a08 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_lt; lia).
          apply mst_refl.
        - post. }
      cbv beta. intros r1 (S10 & S11 & S14 & S12 & S13 & K1).
      destruct (tailB_run r1 c a n S10 S11 S14 S12 S13 Hc Ha Han Hn) as (r2 & M2 & T14 & T13 & K2).
      exists r2. split; [exact M2|]. split; [exact T14|]. split; [exact T13 | solve_kb].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x14a70 : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 a /\ getr r 14 = Z_to_bv 64 c
                         /\ getr r 12 = Z_to_bv 64 n /\ getr r 15 = Z_to_bv 64 7 /\ getr r 13 = Z_to_bv 64 (-1)
                         /\ lkeeps KB regs r)).
      { eexists. split.
        - stepz F_14a00 D_14a00. stepz F_14a04 D_14a04.
          stepb_ft F_14a08 D_14a08 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_ge; lia).
          stepz F_14a0c D_14a0c.
          apply mst_refl.
        - post. }
      cbv beta. intros r1 (S10 & S11 & S14 & S12 & S15 & S13 & K1).
      set (q := Z.to_nat (n / 8)).
      assert (Hq : 8 * Z.of_nat q <= n < 8 * Z.of_nat q + 8).
      { subst q. rewrite Z2Nat.id by (apply Z.div_pos; lia).
        pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia. }
      destruct (t8_loop q r1 c a n S10 S11 S14 S12 S15 Hc Ha Han ltac:(subst q; pose proof (Z.div_le_lower_bound n 8 1 ltac:(lia) ltac:(lia)); lia) Hq)
        as (r2 & M2 & T10 & T11 & T12 & T14 & T13 & K2).
      rewrite S13 in T13.
      destruct (tailB_run r2 _ (a + 8 * Z.of_nat q) (n - 8 * Z.of_nat q) T10 T11 T14 T12 T13 ltac:(crc_rng) ltac:(lia) ltac:(lia) ltac:(lia))
        as (r3 & M3 & U14 & U13 & K3).
      exists r3. split; [eapply msteps_trans; [exact M2 | exact M3]|]. split; [|split; [exact U13 | solve_kb]].
      rewrite U14. replace (Z.to_nat n) with (8 * q + Z.to_nat (n - 8 * Z.of_nat q))%nat by lia.
      rewrite bl_app, crc_bytes_app. replace (Z.of_nat (8 * q)) with (8 * Z.of_nat q) by lia. reflexivity.
  Qed.
End CRC.
End FXG.
