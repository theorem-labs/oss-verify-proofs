(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem U0FuzzBase U0Fuzz_code FuzzCrcLib.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque ctab btab crc_byte.

Definition UKB : list reg := [2; 3; 4]%bv.

Ltac zcond :=
  rwR; rewrite ?zc_ltu_mod, ?zc_eq_mod;
  repeat match goal with
    | |- context [?a mod two64] =>
        lazymatch a with
        | Zneg _ => let v := eval vm_compute in (a mod two64) in change (a mod two64) with v
        | _ => rewrite (mod_small_64 a) by lia
        end
    end;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq | reflexivity ]; lia.

Section CRCA.
Context {RCa1 : RunCtx}.
  Variables (m rom : word -> option byte) (BA : Z -> Z) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hba : forall a, adr0 <= a < adr0 + len0 -> byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m a = BA a.
  Hypothesis BA_rng : forall a, 0 <= BA a < 256.
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.

  Lemma rd1 : forall a, adr0 <= a < adr0 + len0 ->
    exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 a) 1 = Some [b] /\ Z_to_bv 64 (bv_unsigned b) = Z_to_bv 64 (BA a).
  Proof.
    intros a Ha. destruct (Hrd (a - adr0) ltac:(lia)) as [b Hb].
    replace (adr0 + (a - adr0)) with a in Hb by lia.
    exists b. split; [exact Hb |]. rewrite (rdn_byte_at_v (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m a b Hb), Hba by lia. reflexivity.
  Qed.

  Ltac solve_kb := first [ assumption | apply lkeeps_refl | solve_lkeeps
                         | eapply lkeeps_trans; [eassumption | solve_kb] ].
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

  Ltac notrap F D := stepb_ft F D ltac:(zcond).


  Lemma t1u_body : forall regs (c a : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 13 = Z_to_bv 64 (-1) ->
    0 <= c < two32 -> adr0 <= a < adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14c68 : word) m rom) (mkst r (0x14c94 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 (a + 1) /\ getr r 16 = Z_to_bv 64 (a + 1)
      /\ getr r 14 = Z_to_bv 64 (crc_byte c (BA a)) /\ getr r 13 = Z_to_bv 64 (-1)
      /\ getr r 12 = getr regs 12
      /\ lkeeps UKB regs r.
  Proof.
    intros regs c a R10 R11 R14 R13 Hc Ha.
    destruct (rd1 a Ha) as (b & Hb & Eb).
    eexists. split.
    - notrap F_14c08 D_14c08.
      lbu_pl F_14c0c D_14c0c Hb Eb.
      stepz F_14c10 D_14c10. stepz F_14c14 D_14c14. stepz F_14c18 D_14c18. stepz F_14c1c D_14c1c.
      lwu_ctab F_14c20 D_14c20 (Z.land (Z.lxor (BA a) c) 255).
      stepz F_14c24 D_14c24.
      srli8 F_14c28 D_14c28 c.
      stepz F_14c2c D_14c2c. fold_crc.
      stepz F_14c30 D_14c30.
      apply mst_refl.
    - post.
  Qed.

  Lemma t1u_loop : forall (k : nat) regs (c a : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 13 = Z_to_bv 64 (-1) -> getr regs 12 = Z_to_bv 64 (a + Z.of_nat (S k)) ->
    0 <= c < two32 -> adr0 <= a -> a + Z.of_nat (S k) <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14c68 : word) m rom) (mkst r (0x14c98 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (crc_bytes c (bl BA a (S k)))
      /\ lkeeps UKB regs r.
  Proof.
    induction k as [|k IH]; intros regs c a R10 R11 R14 R13 R12 Hc Ha Hk.
    - destruct (t1u_body regs c a R10 R11 R14 R13 Hc ltac:(lia)) as (r1 & M1 & S10 & S11 & S16 & S14 & S13 & S12 & K1).
      rewrite R12 in S12.
      eexists. split; [|split].
      + eapply msteps_trans; [exact M1|].
        stepb_ft F_14c34 D_14c34 ltac:(zcond).
        apply mst_refl.
      + gres. rewrite S14. cbn [bl]. rewrite crc_bytes_cons, crc_bytes_nil. reflexivity.
      + solve_kb.
    - destruct (t1u_body regs c a R10 R11 R14 R13 Hc ltac:(lia)) as (r1 & M1 & S10 & S11 & S16 & S14 & S13 & S12 & K1).
      rewrite R12 in S12.
      assert (S12' : getr r1 12 = Z_to_bv 64 (a + 1 + Z.of_nat (S k))) by (rewrite S12; zbv).
      destruct (IH r1 (crc_byte c (BA a)) (a + 1) S10 S11 S14 S13 S12' ltac:(crc_rng) ltac:(lia) ltac:(lia))
        as (r2 & M2 & T14 & K2).
      exists r2. split; [|split].
      + eapply msteps_trans; [exact M1|].
        stepb_tk F_14c34 D_14c34 ltac:(zcond).
        exact M2.
      + rewrite T14. cbn [bl]. rewrite crc_bytes_cons. reflexivity.
      + solve_kb.
  Qed.


  Lemma t8u_h1 : forall regs (c a : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 13 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 (-2) ->
    0 <= c < two32 -> adr0 <= a -> a + 8 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14afc : word) m rom) (mkst r (0x14bb8 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 (a + 7) /\ getr r 17 = Z_to_bv 64 a
      /\ getr r 14 = Z_to_bv 64 (crc_byte (crc_byte (crc_byte (crc_byte c (BA a)) (BA (a + 1))) (BA (a + 2))) (BA (a + 3)))
      /\ getr r 13 = Z_to_bv 64 (-1) /\ getr r 15 = Z_to_bv 64 (-2)
      /\ getr r 12 = getr regs 12 /\ getr r 16 = getr regs 16
      /\ lkeeps UKB regs r.
  Proof.
    intros regs c a R10 R11 R14 R13 R15 Hc Ha Ha8.
    destruct (rd1 a ltac:(lia)) as (b0 & Hb0 & Eb0).
    destruct (rd1 (a + 1) ltac:(lia)) as (b1 & Hb1 & Eb1).
    destruct (rd1 (a + 2) ltac:(lia)) as (b2 & Hb2 & Eb2).
    destruct (rd1 (a + 3) ltac:(lia)) as (b3 & Hb3 & Eb3).
    eexists. split.
    - notrap F_14a9c D_14a9c.
      stepz F_14aa0 D_14aa0.
      stepz F_14aa4 D_14aa4. notrap F_14aa8 D_14aa8.
      stepz F_14aac D_14aac. notrap F_14ab0 D_14ab0.
      stepz F_14ab4 D_14ab4. notrap F_14ab8 D_14ab8.
      stepz F_14abc D_14abc. notrap F_14ac0 D_14ac0.
      stepz F_14ac4 D_14ac4. notrap F_14ac8 D_14ac8. notrap F_14acc D_14acc.
      stepz F_14ad0 D_14ad0. notrap F_14ad4 D_14ad4.
      lbu_pl F_14ad8 D_14ad8 Hb0 Eb0.
      lbu_pl F_14adc D_14adc Hb1 Eb1.
      lbu_pl F_14ae0 D_14ae0 Hb2 Eb2.
      lbu_pl F_14ae4 D_14ae4 Hb3 Eb3.
      stepz F_14ae8 D_14ae8. stepz F_14aec D_14aec. stepz F_14af0 D_14af0. stepz F_14af4 D_14af4.
      lwu_ctab F_14af8 D_14af8 (Z.land (Z.lxor (BA a) c) 255).
      srli8 F_14afc D_14afc c.
      stepz F_14b00 D_14b00. fold_crc.
      stepz F_14b04 D_14b04. stepz F_14b08 D_14b08. stepz F_14b0c D_14b0c. stepz F_14b10 D_14b10.
      lwu_ctab F_14b14 D_14b14 (Z.land (Z.lxor (BA (a + 1)) (crc_byte c (BA a))) 255).
      srli8 F_14b18 D_14b18 (crc_byte c (BA a)).
      stepz F_14b1c D_14b1c. fold_crc.
      stepz F_14b20 D_14b20. stepz F_14b24 D_14b24. stepz F_14b28 D_14b28. stepz F_14b2c D_14b2c.
      lwu_ctab F_14b30 D_14b30 (Z.land (Z.lxor (BA (a + 2)) (crc_byte (crc_byte c (BA a)) (BA (a + 1)))) 255).
      srli8 F_14b34 D_14b34 (crc_byte (crc_byte c (BA a)) (BA (a + 1))).
      stepz F_14b38 D_14b38. fold_crc.
      stepz F_14b3c D_14b3c. stepz F_14b40 D_14b40. stepz F_14b44 D_14b44. stepz F_14b48 D_14b48.
      lwu_ctab F_14b4c D_14b4c (Z.land (Z.lxor (BA (a + 3)) (crc_byte (crc_byte (crc_byte c (BA a)) (BA (a + 1))) (BA (a + 2)))) 255).
      srli8 F_14b50 D_14b50 (crc_byte (crc_byte (crc_byte c (BA a)) (BA (a + 1))) (BA (a + 2))).
      stepz F_14b54 D_14b54. fold_crc.
      apply mst_refl.
    - post.
  Qed.

  Lemma t8u_h2 : forall regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 (a + 7) -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 12 = Z_to_bv 64 n ->
    0 <= c < two32 -> adr0 <= a -> a + 8 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14bb8 : word) m rom) (mkst r (0x14c40 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 (a + 8) /\ getr r 12 = Z_to_bv 64 (n - 8)
      /\ getr r 14 = Z_to_bv 64 (crc_byte (crc_byte (crc_byte (crc_byte c (BA (a + 4))) (BA (a + 5))) (BA (a + 6))) (BA (a + 7)))
      /\ getr r 13 = getr regs 13 /\ getr r 15 = getr regs 15 /\ getr r 16 = getr regs 16 /\ getr r 17 = getr regs 17
      /\ lkeeps UKB regs r.
  Proof.
    intros regs c a n R10 R11 R14 R12 Hc Ha Ha8.
    destruct (rd1 (a + 4) ltac:(lia)) as (b0 & Hb0 & Eb0).
    destruct (rd1 (a + 5) ltac:(lia)) as (b1 & Hb1 & Eb1).
    destruct (rd1 (a + 6) ltac:(lia)) as (b2 & Hb2 & Eb2).
    destruct (rd1 (a + 7) ltac:(lia)) as (b3 & Hb3 & Eb3).
    eexists. split.
    - lbu_pl F_14b58 D_14b58 Hb0 Eb0.
      lbu_pl F_14b5c D_14b5c Hb1 Eb1.
      lbu_pl F_14b60 D_14b60 Hb2 Eb2.
      lbu_pl F_14b64 D_14b64 Hb3 Eb3.
      stepz F_14b68 D_14b68. stepz F_14b6c D_14b6c. stepz F_14b70 D_14b70. stepz F_14b74 D_14b74.
      lwu_ctab F_14b78 D_14b78 (Z.land (Z.lxor (BA (a + 4)) c) 255).
      srli8 F_14b7c D_14b7c c.
      stepz F_14b80 D_14b80. fold_crc.
      stepz F_14b84 D_14b84. stepz F_14b88 D_14b88. stepz F_14b8c D_14b8c. stepz F_14b90 D_14b90.
      lwu_ctab F_14b94 D_14b94 (Z.land (Z.lxor (BA (a + 5)) (crc_byte c (BA (a + 4)))) 255).
      srli8 F_14b98 D_14b98 (crc_byte c (BA (a + 4))).
      stepz F_14b9c D_14b9c. fold_crc.
      stepz F_14ba0 D_14ba0. stepz F_14ba4 D_14ba4. stepz F_14ba8 D_14ba8. stepz F_14bac D_14bac.
      lwu_ctab F_14bb0 D_14bb0 (Z.land (Z.lxor (BA (a + 6)) (crc_byte (crc_byte c (BA (a + 4))) (BA (a + 5)))) 255).
      srli8 F_14bb4 D_14bb4 (crc_byte (crc_byte c (BA (a + 4))) (BA (a + 5))).
      stepz F_14bb8 D_14bb8. fold_crc.
      stepz F_14bbc D_14bbc. stepz F_14bc0 D_14bc0. stepz F_14bc4 D_14bc4. stepz F_14bc8 D_14bc8.
      lwu_ctab F_14bcc D_14bcc (Z.land (Z.lxor (BA (a + 7)) (crc_byte (crc_byte (crc_byte c (BA (a + 4))) (BA (a + 5))) (BA (a + 6)))) 255).
      stepz F_14bd0 D_14bd0.
      srli8 F_14bd4 D_14bd4 (crc_byte (crc_byte (crc_byte c (BA (a + 4))) (BA (a + 5))) (BA (a + 6))).
      stepz F_14bd8 D_14bd8. fold_crc.
      stepz F_14bdc D_14bdc.
      apply mst_refl.
    - post.
  Qed.

  Lemma bl8 : forall a, bl BA a 8 = [BA a; BA (a + 1); BA (a + 2); BA (a + 3); BA (a + 4); BA (a + 5); BA (a + 6); BA (a + 7)].
  Proof.
    intros a. cbn [bl].
    repeat match goal with
           | |- (_ :: _) = (_ :: _) => apply (f_equal2 (@cons Z))
           | |- BA _ = BA _ => apply (f_equal BA); lia
           | |- @nil _ = @nil _ => reflexivity
           end.
  Qed.

  Lemma t8u_iter : forall regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 (-2) ->
    0 <= c < two32 -> adr0 <= a -> a + 8 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14afc : word) m rom) (mkst r (0x14c40 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 (a + 8) /\ getr r 12 = Z_to_bv 64 (n - 8)
      /\ getr r 14 = Z_to_bv 64 (crc_bytes c (bl BA a 8))
      /\ getr r 13 = Z_to_bv 64 (-1) /\ getr r 15 = Z_to_bv 64 (-2) /\ getr r 16 = getr regs 16
      /\ getr r 17 = Z_to_bv 64 a
      /\ lkeeps UKB regs r.
  Proof.
    intros regs c a n R10 R11 R14 R12 R13 R15 Hc Ha Ha8.
    destruct (t8u_h1 regs c a R10 R11 R14 R13 R15 Hc Ha Ha8) as (r1 & M1 & S10 & S11 & S17 & S14 & S13 & S15 & S12 & S16 & K1).
    rewrite R12 in S12.
    destruct (t8u_h2 r1 _ a n S10 S11 S14 S12 ltac:(crc_rng) Ha Ha8) as (r2 & M2 & T10 & T11 & T12 & T14 & T13 & T15 & T16 & T17 & K2).
    exists r2. split; [eapply msteps_trans; [exact M1 | exact M2]|].
    rewrite T13, T15, T16, T17, S13, S15, S16, S17. repeat split; try assumption; try reflexivity.
    - rewrite T14, bl8, crc_bytes8. reflexivity.
    - solve_kb.
  Qed.

  Lemma t8u_loop : forall (q : nat) regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 (-2) ->
    getr regs 16 = Z_to_bv 64 7 ->
    0 <= c < two32 -> adr0 <= a -> a + n <= adr0 + len0 ->
    (1 <= q)%nat -> 8 * Z.of_nat q <= n < 8 * Z.of_nat q + 8 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14afc : word) m rom) (mkst r (0x14c48 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 (a + 8 * Z.of_nat q)
      /\ getr r 12 = Z_to_bv 64 (n - 8 * Z.of_nat q)
      /\ getr r 14 = Z_to_bv 64 (crc_bytes c (bl BA a (8 * q)))
      /\ lkeeps UKB regs r.
  Proof.
    induction q as [|q IH]; intros regs c a n R10 R11 R14 R12 R13 R15 R16 Hc Ha Han Hq Hn; [lia|].
    destruct (t8u_iter regs c a n R10 R11 R14 R12 R13 R15 Hc Ha ltac:(lia))
      as (r1 & M1 & S10 & S11 & S12 & S14 & S13 & S15 & S16 & S17 & K1).
    rewrite R16 in S16.
    destruct (Nat.eq_dec q 0) as [-> | Hq'].
    - eexists. split; [|split; [|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact M1|].
        stepb_ft F_14be0 D_14be0 ltac:(zcond).
        stepz F_14be4 D_14be4.
        apply mst_refl.
      + post.
      + post.
      + post.
      + gres. rewrite S14. change (8 * 1)%nat with 8%nat. reflexivity.
      + solve_kb.
    - destruct (IH r1 (crc_bytes c (bl BA a 8)) (a + 8) (n - 8) S10 S11 S14 S12 S13 S15 S16 ltac:(crc_rng) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia)) as (r2 & M2 & T10 & T11 & T12 & T14 & K2).
      exists r2. split; [|split; [|split; [|split; [|split]]]].
      + eapply msteps_trans; [exact M1|].
        stepb_tk F_14be0 D_14be0 ltac:(zcond).
        exact M2.
      + exact T10.
      + rewrite T11. zbv.
      + rewrite T12. zbv.
      + rewrite T14. replace (8 * S q)%nat with (8 + 8 * q)%nat by lia.
        rewrite bl_app, crc_bytes_app. change (Z.of_nat 8) with 8. reflexivity.
      + solve_kb.
  Qed.

  Lemma tailBu_run : forall regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 12 = Z_to_bv 64 n ->
    0 <= c < two32 -> adr0 <= a -> a + n <= adr0 + len0 -> 0 <= n ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14c48 : word) m rom) (mkst r (0x14c98 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (crc_bytes c (bl BA a (Z.to_nat n)))
      /\ lkeeps UKB regs r.
  Proof.
    intros regs c a n R10 R11 R14 R12 Hc Ha Han Hn.
    destruct (Z.eq_dec n 0) as [-> | Hnz].
    - eexists. split; [|split].
      + stepb_tk F_14be8 D_14be8 ltac:(zcond).
        apply mst_refl.
      + rewrite R14. change (Z.to_nat 0) with 0%nat. rewrite crc_bytes_nil. reflexivity.
      + solve_kb.
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14c68 : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 a /\ getr r 14 = Z_to_bv 64 c
                         /\ getr r 13 = Z_to_bv 64 (-1)
                         /\ getr r 12 = Z_to_bv 64 (a + Z.of_nat (S (Z.to_nat (n - 1))))
                         /\ lkeeps UKB regs r)).
      { eexists. split.
        - stepb_ft F_14be8 D_14be8 ltac:(zcond).
          stepz F_14bec D_14bec.
          stepz F_14bf0 D_14bf0.
          stepb_ft F_14bf4 D_14bf4 ltac:(rwR; rewrite zc_ltu_mod, lxor_m1_64, mod_small_64 by lia; apply Z.ltb_ge; unfold ONES64; lia).
          stepz F_14bf8 D_14bf8.
          stepz F_14bfc D_14bfc.
          stepz F_14c00 D_14c00.
          stepz F_14c04 D_14c04.
          apply mst_refl.
        - post. }
      cbv beta. intros r1 (S10 & S11 & S14 & S13 & S12 & K1).
      destruct (t1u_loop (Z.to_nat (n - 1)) r1 c a S10 S11 S14 S13 S12 Hc Ha ltac:(lia)) as (r2 & M2 & T14 & K2).
      exists r2. split; [exact M2|]. split; [|solve_kb].
      rewrite T14. replace (S (Z.to_nat (n - 1))) with (Z.to_nat n) by lia. reflexivity.
  Qed.

  Lemma tailu_run : forall regs (c a n : Z),
    getr regs 10 = Z_to_bv 64 CTAB -> getr regs 11 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 c ->
    getr regs 12 = Z_to_bv 64 n ->
    0 <= c < two32 -> adr0 <= a -> a + n <= adr0 + len0 -> 0 <= n ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14ae8 : word) m rom) (mkst r (0x14c98 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (crc_bytes c (bl BA a (Z.to_nat n)))
      /\ lkeeps UKB regs r.
  Proof.
    intros regs c a n R10 R11 R14 R12 Hc Ha Han Hn.
    destruct (Z.lt_ge_cases n 8) as [Hs | Hb].
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14c48 : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 a /\ getr r 14 = Z_to_bv 64 c
                         /\ getr r 12 = Z_to_bv 64 n /\ lkeeps UKB regs r)).
      { eexists. split.
        - stepz F_14a88 D_14a88.
          stepb_tk F_14a8c D_14a8c ltac:(zcond).
          apply mst_refl.
        - post. }
      cbv beta. intros r1 (S10 & S11 & S14 & S12 & K1).
      destruct (tailBu_run r1 c a n S10 S11 S14 S12 Hc Ha Han Hn) as (r2 & M2 & T14 & K2).
      exists r2. split; [exact M2|]. split; [exact T14 | solve_kb].
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14afc : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 a /\ getr r 14 = Z_to_bv 64 c
                         /\ getr r 12 = Z_to_bv 64 n /\ getr r 13 = Z_to_bv 64 (-1) /\ getr r 15 = Z_to_bv 64 (-2)
                         /\ getr r 16 = Z_to_bv 64 7 /\ lkeeps UKB regs r)).
      { eexists. split.
        - stepz F_14a88 D_14a88.
          stepb_ft F_14a8c D_14a8c ltac:(zcond).
          stepz F_14a90 D_14a90. stepz F_14a94 D_14a94. stepz F_14a98 D_14a98.
          apply mst_refl.
        - post. }
      cbv beta. intros r1 (S10 & S11 & S14 & S12 & S13 & S15 & S16 & K1).
      set (q := Z.to_nat (n / 8)).
      assert (Hq : 8 * Z.of_nat q <= n < 8 * Z.of_nat q + 8).
      { subst q. rewrite Z2Nat.id by (apply Z.div_pos; lia).
        pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia. }
      destruct (t8u_loop q r1 c a n S10 S11 S14 S12 S13 S15 S16 Hc Ha Han
                  ltac:(subst q; pose proof (Z.div_le_lower_bound n 8 1 ltac:(lia) ltac:(lia)); lia) Hq)
        as (r2 & M2 & T10 & T11 & T12 & T14 & K2).
      destruct (tailBu_run r2 _ (a + 8 * Z.of_nat q) (n - 8 * Z.of_nat q) T10 T11 T14 T12 ltac:(crc_rng) ltac:(lia) ltac:(lia) ltac:(lia))
        as (r3 & M3 & U14 & K3).
      exists r3. split; [eapply msteps_trans; [exact M2 | exact M3]|]. split; [|solve_kb].
      rewrite U14. replace (Z.to_nat n) with (8 * q + Z.to_nat (n - 8 * Z.of_nat q))%nat by lia.
      rewrite bl_app, crc_bytes_app. replace (Z.of_nat (8 * q)) with (8 * Z.of_nat q) by lia. reflexivity.
  Qed.
End CRCA.
