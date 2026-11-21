(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem U0FuzzBase U0Fuzz_code U0FuzzIface U0FuzzStmt
  U0Fuzz_adler U0Fuzz_adlc U0Fuzz_crc U0FuzzA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkHarness.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation W8 v := (word_to_le_bytes 8 v).

Definition ARH (sp data : word) (n Bv T NX : Z) (r : bvmap 5 word) (off A : Z) : Prop :=
  getr r 2 = Z_to_bv 64 (bv_unsigned sp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 (bv_unsigned data) /\
  getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T /\
  getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX /\
  getr r 22 = Z_to_bv 64 off /\ getr r 10 = Z_to_bv 64 A.

Section PHASE3.
Context {RCa1 : RunCtx}.
  Variables (mem : word -> option byte) (sp data : word) (n : Z) (M0 rom : word -> option byte).
  Hypothesis HU : u0H mem sp data n M0.
  Variable Bv : Z.
  Hypothesis HBv : Bv = hB mem data.

  #[local] Abbreviation usp := (bv_unsigned sp).
  #[local] Abbreviation udata := (bv_unsigned data).
  #[local] Abbreviation D k := (HD mem data k).
  #[local] Abbreviation CH off k := (CHK mem data off k).
  #[local] Abbreviation NX := (ONES64 - bv_unsigned data).

  Lemma Bv_range3 : 1 <= Bv <= 256.
  Proof. rewrite HBv. apply hB_range. Qed.

  Ltac ranges := pose proof (u64_range data); pose proof (u64_range sp);
                 pose proof (Un _ _ _ _ _ HU); pose proof (Unw _ _ _ _ _ HU); pose proof (Udata _ _ _ _ _ HU);
                 pose proof (Usp _ _ _ _ _ HU); pose proof (Uapart _ _ _ _ _ HU); pose proof Bv_range3.

  Ltac post :=
    repeat split; gres; rwR;
    first [ reflexivity | assumption | lia | f_equal; lia | bveq | solve_lkeeps ].
  Ltac retok := apply ret_ok_even; reflexivity.
  Ltac xfer K H H2 :=
    lazymatch type of K with keeps_cs ?ra ?rb =>
      lazymatch type of H with getr _ ?i = ?v =>
        assert (H2 : getr rb i = v) by (rewrite (K i) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact H)
      end
    end.

  Ltac ld0 F D Hrd :=
    chain_step;
    [ reflexivity
    | eapply step_ld with (v := Z_to_bv 64 1);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite zv_addi; rdn_at (Z_to_bv 64 (bv_unsigned sp - 112)); exact Hrd
      | apply bytes_le_to_Z_8 ]
    | step_simpl; vnorm ].

  Lemma adl_body : forall T regs m off A,
    ARH sp data n Bv T NX regs off A -> MINV sp M0 m -> 0 <= off -> off + Bv <= n ->
    A = adler_spec 1 (D off) ->
    exists r m', msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14430 : word) m rom) (mkst r (0x14454 : word) m' rom)
      /\ (getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\
          getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T /\
          getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX /\
          getr r 22 = Z_to_bv 64 (off + Bv) /\ getr r 11 = Z_to_bv 64 (off + Bv + Bv) /\
          getr r 10 = Z_to_bv 64 (adler_spec 1 (D (off + Bv))))
      /\ MINV sp M0 m' /\ lkeeps hk regs r.
  Proof.
    intros T regs m off A (R2 & R8 & R9 & R19 & R20 & R21 & R26 & R27 & R22 & R10) HM Hoff Hin HA.
    ranges.
    assert (HAr : 0 <= A < two32) by (rewrite HA; apply adler_spec_1_range).
    assert (S1 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14430 : word) m rom) (mkst r (0x14f2c : word) m rom)
      /\ getr r 1 = (0x1444c%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 A /\ getr r 11 = Z_to_bv 64 (udata + off) /\ getr r 12 = Z_to_bv 64 Bv
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 19 = Z_to_bv 64 n
      /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
      /\ getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX /\ getr r 22 = Z_to_bv 64 off
      /\ lkeeps hk regs r).
    { eexists. split.
      - stepz F_143d0 D_143d0. stepz F_143d4 D_143d4. rewrite (mod_small_32 off) by lia.
        stepb_ft F_143d8 D_143d8 ltac:(rwR; rewrite zc_ltu by (unfold ONES64; lia); apply Z.ltb_ge; unfold ONES64; lia).
        stepz F_143dc D_143dc.
        stepz F_143e0 D_143e0. rewrite <- (mod32_land A), (mod_small_32 A) by lia.
        stepz F_143e4 D_143e4. stepz F_143e8 D_143e8.
        apply mst_refl.
      - unfold hk. post. }
    destruct S1 as (r1 & M1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A19 & A20 & A21 & A26 & A27 & A22 & K1).
    destruct (u0_adler32_z r1 m rom (0x1444c%bv : word) (usp - 112) A (udata + off) Bv
                A1 ltac:(retok) A2 A10 A11 A12
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(apply (minv_stk_ mem sp data n M0 HU m); [exact HM | lia | change (Z.of_nat 128) with 128; lia])
                ltac:(intros _; lia) ltac:(apply (minv_img_ sp M0); exact HM)
                ltac:(apply (minv_rd_off_ mem sp data n M0 HU m off Bv HM); lia))
      as (r2 & m2 & M2 & V2 & K2 & F2).
    rewrite (minv_bytes_ mem sp data n M0 HU m off Bv HM) in V2 by lia.
    assert (EA : adler32_z_model A (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (udata + off) (Z.to_nat Bv)) = adler_spec 1 (D (off + Bv))).
    { rewrite HA. unfold HD. rewrite (bytes_at_appZ (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem udata off Bv) by lia.
      apply harness_adler_stream; apply bytes_at_range. }
    rewrite EA in V2. set (A' := adler_spec 1 (D (off + Bv))) in V2.
    assert (HM2 : MINV sp M0 m2)
      by (eapply (minv_frame_ mem sp data n M0 HU m m2); [exact HM | exact F2 | lia | lia | lia]).
    xfer K2 A2 B2. xfer K2 A8 B8. xfer K2 A9 B9. xfer K2 A19 B19. xfer K2 A20 B20. xfer K2 A21 B21.
    xfer K2 A22 B22. xfer K2 A26 B26. xfer K2 A27 B27.
    assert (S3 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r2 (0x1444c%bv : word) m2 rom) (mkst r (0x14454 : word) m2 rom)
      /\ (getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\
          getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T /\
          getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX /\
          getr r 22 = Z_to_bv 64 (off + Bv) /\ getr r 11 = Z_to_bv 64 (off + Bv + Bv) /\
          getr r 10 = Z_to_bv 64 A')
      /\ lkeeps hk r2 r).
    { eexists. split.
      - stepz F_143ec D_143ec.
        stepz F_143f0 D_143f0. rewrite (mod_small_32 (Bv + (off + Bv))), (sx32_small (Bv + (off + Bv))) by lia.
        apply mst_refl.
      - unfold hk. post. }
    destruct S3 as (r3 & M3 & Q3 & K3).
    exists r3, m2. split; [|split; [exact Q3 | split; [exact HM2|]]].
    - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2 | exact M3].
    - intros x Hx. rewrite (K3 x Hx). rewrite (K2 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). apply (K1 x Hx).
  Qed.

  Lemma adl_loop : forall T (k : nat) regs m off,
    ARH sp data n Bv T NX regs off (adler_spec 1 (D off)) -> MINV sp M0 m -> 0 <= off ->
    off + Bv + Z.of_nat k * Bv <= n < off + Bv + (Z.of_nat k + 1) * Bv ->
    exists r m', msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14430 : word) m rom) (mkst r (0x14464 : word) m' rom)
      /\ MINV sp M0 m' /\ lkeeps hk regs r
      /\ getr r 11 = Z_to_bv 64 (off + Bv + Z.of_nat k * Bv)
      /\ getr r 10 = Z_to_bv 64 (adler_spec 1 (D (off + Bv + Z.of_nat k * Bv)))
      /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
      /\ getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX.
  Proof.
    intros T. induction k as [|k IH]; intros regs m off HR HM Hoff Hk.
    - change (Z.of_nat 0) with 0 in *. ranges.
      destruct (adl_body T regs m off _ HR HM Hoff ltac:(lia) eq_refl)
        as (r1 & m1 & M1 & (B2 & B8 & B9 & B19 & B20 & B21 & B26 & B27 & B22 & B11 & B10) & HM1 & K1).
      set (A' := adler_spec 1 (D (off + Bv))) in B10.
      assert (S2 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r1 (0x14454 : word) m1 rom) (mkst r (0x14464 : word) m1 rom)
        /\ (getr r 11 = Z_to_bv 64 (off + Bv) /\ getr r 10 = Z_to_bv 64 A'
            /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
            /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
            /\ getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX)
        /\ lkeeps hk r1 r).
      { eexists. split.
        - stepb_ft F_143f4 D_143f4 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_lt; lia).
          stepz F_143f8 D_143f8. stepz F_143fc D_143fc. rewrite (mod_small_32 (off + Bv)) by lia.
          stepb_ft F_14400 D_14400 ltac:(rwR; rewrite zc_ltu by (unfold ONES64; lia); apply Z.ltb_ge; unfold ONES64; lia).
          apply mst_refl.
        - unfold hk. post. }
      destruct S2 as (r2 & M2 & (C11 & C10 & C2 & C8 & C9 & C19 & C20 & C21 & C26 & C27) & K2).
      exists r2, m1. rewrite Z.mul_0_l, Z.add_0_r.
      split; [eapply msteps_trans; [exact M1 | exact M2]|]. split; [exact HM1|].
      split; [eapply lkeeps_trans; [exact K1 | exact K2]|].
      repeat split; assumption.
    - ranges.
      assert (Hk' : off + Bv + Bv + Z.of_nat k * Bv <= n < off + Bv + Bv + (Z.of_nat k + 1) * Bv)
        by (rewrite Nat2Z.inj_succ in Hk; lia).
      destruct (adl_body T regs m off _ HR HM Hoff ltac:(lia) eq_refl)
        as (r1 & m1 & M1 & (B2 & B8 & B9 & B19 & B20 & B21 & B26 & B27 & B22 & B11 & B10) & HM1 & K1).
      assert (S2 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r1 (0x14454 : word) m1 rom) (mkst r (0x14430 : word) m1 rom)
        /\ ARH sp data n Bv T NX r (off + Bv) (adler_spec 1 (D (off + Bv))) /\ lkeeps hk r1 r).
      { eexists. split.
        - stepb_tk F_143f4 D_143f4 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_ge; lia).
          apply mst_refl.
        - unfold ARH, hk. post. }
      destruct S2 as (r2 & M2 & HR2 & K2).
      destruct (IH r2 m1 (off + Bv) HR2 HM1 ltac:(lia) Hk')
        as (r & m' & M & HM' & K & V11 & V10 & V2 & V8 & V9 & V19 & V20 & V21 & V26 & V27).
      exists r, m'. replace (off + Bv + Z.of_nat (S k) * Bv) with (off + Bv + Bv + Z.of_nat k * Bv) by lia.
      split; [eapply msteps_trans; [exact M1 |]; eapply msteps_trans; [exact M2 | exact M]|].
      split; [exact HM'|]. split; [eapply lkeeps_trans; [exact K1 |]; eapply lkeeps_trans; [exact K2 | exact K]|].
      repeat split; assumption.
  Qed.

  Lemma adl_tail : forall regs m offq,
    getr regs 11 = Z_to_bv 64 offq -> getr regs 10 = Z_to_bv 64 (adler_spec 1 (D offq)) ->
    getr regs 2 = Z_to_bv 64 (usp - 112) -> getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 udata ->
    getr regs 19 = Z_to_bv 64 n -> getr regs 21 = Z_to_bv 64 (n - offq) -> getr regs 26 = Z_to_bv 64 4294967295 ->
    MINV sp M0 m -> 0 <= offq <= n -> n - offq < Bv ->
    exists r m', msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14464 : word) m rom) (mkst r (0x144c4 : word) m' rom)
      /\ MINV sp M0 m' /\ lkeeps hk regs r /\ getr r 2 = Z_to_bv 64 (usp - 112).
  Proof.
    intros regs m offq R11 R10 R2 R8 R9 R19 R21 R26 HM Hoff HT.
    ranges.
    set (Aq := adler_spec 1 (D offq)) in R10.
    assert (HAq : 0 <= Aq < two32) by (subst Aq; apply adler_spec_1_range).
    set (T := n - offq) in *.
    assert (S1 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14464 : word) m rom) (mkst r (0x14f2c : word) m rom)
      /\ getr r 1 = (0x14474%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 Aq /\ getr r 11 = Z_to_bv 64 (udata + offq) /\ getr r 12 = Z_to_bv 64 T
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 19 = Z_to_bv 64 n
      /\ getr r 26 = Z_to_bv 64 4294967295
      /\ lkeeps hk regs r).
    { eexists. split.
      - stepz F_14404 D_14404.
        stepz F_14408 D_14408. rewrite <- (mod32_land Aq), (mod_small_32 Aq) by lia.
        stepz F_1440c D_1440c. stepz F_14410 D_14410.
        apply mst_refl.
      - unfold hk. post. }
    destruct S1 as (r1 & M1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A19 & A26 & K1).
    destruct (u0_adler32_z r1 m rom (0x14474%bv : word) (usp - 112) Aq (udata + offq) T
                A1 ltac:(retok) A2 A10 A11 A12
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(apply (minv_stk_ mem sp data n M0 HU m); [exact HM | lia | change (Z.of_nat 128) with 128; lia])
                ltac:(intros _; lia) ltac:(apply (minv_img_ sp M0); exact HM)
                ltac:(apply (minv_rd_off_ mem sp data n M0 HU m offq T HM); lia))
      as (r2 & m2 & M2 & V2 & K2 & F2).
    rewrite (minv_bytes_ mem sp data n M0 HU m offq T HM) in V2 by lia.
    assert (EADL : adler32_z_model Aq (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (udata + offq) (Z.to_nat T)) = adler_spec 1 (D n)).
    { subst Aq. replace (HD mem data n) with (D (offq + T)) by (f_equal; lia).
      unfold HD. rewrite (bytes_at_appZ (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem udata offq T) by lia.
      apply harness_adler_stream; apply bytes_at_range. }
    rewrite EADL in V2. set (ADL := adler_spec 1 (D n)) in V2.
    assert (HADL : 0 <= ADL < two32) by (subst ADL; apply adler_spec_1_range).
    pose proof (sx32_range ADL HADL) as HsxADL.
    assert (HM2 : MINV sp M0 m2)
      by (eapply (minv_frame_ mem sp data n M0 HU m m2); [exact HM | exact F2 | lia | lia | lia]).
    pose proof (minv_ld0_ mem sp data n M0 HU m2 HM2) as L2.
    xfer K2 A2 B2. xfer K2 A8 B8. xfer K2 A9 B9. xfer K2 A19 B19. xfer K2 A26 B26.
    assert (S3 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r2 (0x14474%bv : word) m2 rom) (mkst r (0x1545c : word) m2 rom)
      /\ getr r 1 = (0x14490%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 1 /\ getr r 11 = Z_to_bv 64 udata /\ getr r 12 = Z_to_bv 64 n
      /\ getr r 18 = Z_to_bv 64 (sx32 ADL) /\ getr r 20 = Z_to_bv 64 ADL
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 19 = Z_to_bv 64 n
      /\ getr r 26 = Z_to_bv 64 4294967295
      /\ lkeeps hk r2 r).
    { eexists. split.
      - stepz F_14414 D_14414. stepz F_14418 D_14418. rewrite (mod_small_32 ADL) by lia.
        ld0 F_1441c D_1441c L2.
        stepz F_14420 D_14420.
        stepz F_14424 D_14424. stepz F_14428 D_14428. stepz F_1442c D_1442c.
        apply mst_refl.
      - unfold hk. post. }
    destruct S3 as (r3 & M3 & B1 & B2' & B10 & B11 & B12 & B18 & B20 & B8' & B9' & B19' & B26' & K3).
    destruct (u0_adler32 r3 m2 rom (0x14490%bv : word) (usp - 112) 1 udata n n
                B1 ltac:(retok) B2' B10 B11 B12
                ltac:(lia) ltac:(rewrite Z.mod_small; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(apply (minv_stk_ mem sp data n M0 HU m2); [exact HM2 | lia | change (Z.of_nat 128) with 128; lia])
                ltac:(intros _; lia) ltac:(apply (minv_img_ sp M0); exact HM2)
                (minv_rd_ mem sp data n M0 HU m2 HM2))
      as (r4 & m4 & M4 & V4 & K4 & F4).
    rewrite <- (Z.add_0_r udata) in V4. rewrite (minv_bytes_ mem sp data n M0 HU m2 0 n HM2) in V4 by lia.
    rewrite (Z.add_0_r udata) in V4. change (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem udata (Z.to_nat n)) with (D n) in V4.
    rewrite (adler32_z_model_spec 1 (D n) adler_ok_1 (HD_bytes mem data n)) in V4. fold ADL in V4.
    assert (HM4 : MINV sp M0 m4)
      by (eapply (minv_frame_ mem sp data n M0 HU m2 m4); [exact HM2 | exact F4 | lia | lia | lia]).
    xfer K4 B2' C2. xfer K4 B8' C8. xfer K4 B18 C18. xfer K4 B19' C19. xfer K4 B20 C20. xfer K4 B26' C26.
    assert (S5 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r4 (0x14490%bv : word) m4 rom) (mkst r (0x15468 : word) m4 rom)
      /\ getr r 1 = (0x144ac%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 ADL /\ getr r 11 = Z_to_bv 64 ADL /\ getr r 12 = Z_to_bv 64 n
      /\ getr r 9 = Z_to_bv 64 ADL /\ getr r 8 = Z_to_bv 64 n
      /\ lkeeps hk r4 r).
    { eexists. split.
      - stepz F_14430 D_14430. rewrite (mod_small_32 ADL) by lia.
        stepb_ft F_14434 D_14434 ltac:(rwR; apply c_eq_refl).
        stepz F_14438 D_14438. rewrite <- (mod32_land ADL), (mod_small_32 ADL) by lia.
        stepz F_1443c D_1443c. rewrite <- (mod32_land ADL), (mod_small_32 ADL) by lia.
        stepz F_14440 D_14440. stepz F_14444 D_14444. stepz F_14448 D_14448.
        apply mst_refl.
      - unfold hk. post. }
    destruct S5 as (r5 & M5 & C1 & D2 & D10 & D11 & D12 & D9 & D8 & K5).
    destruct (u0_adler32_combine r5 m4 rom (0x144ac%bv : word) ADL ADL n C1 ltac:(retok) D10 D11 D12
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply (minv_img_ sp M0); exact HM4)) as (r6 & M6 & V6 & K6).
    set (Z1 := adler32_combine_model ADL ADL n) in V6.
    xfer K6 D2 E2. xfer K6 D8 E8. xfer K6 D9 E9.
    assert (S7 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r6 (0x144ac%bv : word) m4 rom) (mkst r (0x15468 : word) m4 rom)
      /\ getr r 1 = (0x144c0%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 ADL /\ getr r 11 = Z_to_bv 64 ADL /\ getr r 12 = Z_to_bv 64 n
      /\ getr r 18 = Z_to_bv 64 Z1
      /\ lkeeps hk r6 r).
    { eexists. split.
      - stepz F_1444c D_1444c. stepz F_14450 D_14450. stepz F_14454 D_14454. stepz F_14458 D_14458.
        stepz F_1445c D_1445c. apply mst_refl.
      - unfold hk. post. }
    destruct S7 as (r7 & M7 & E1 & F2' & F10 & F11 & F12 & F18 & K7).
    destruct (u0_adler32_combine r7 m4 rom (0x144c0%bv : word) ADL ADL n E1 ltac:(retok) F10 F11 F12
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply (minv_img_ sp M0); exact HM4)) as (r8 & M8 & V8 & K8).
    fold Z1 in V8.
    xfer K8 F2' G2. xfer K8 F18 G18.
    assert (S9 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r8 (0x144c0%bv : word) m4 rom) (mkst r (0x144c4 : word) m4 rom)
      /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ lkeeps hk r8 r).
    { eexists. split.
      - stepb_ft F_14460 D_14460 ltac:(rwR; apply c_eq_refl). apply mst_refl.
      - unfold hk. post. }
    destruct S9 as (r9 & M9 & X2 & K9).
    exists r9, m4. split.
    { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
      eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5|]. eapply msteps_trans; [exact M6|].
      eapply msteps_trans; [exact M7|]. eapply msteps_trans; [exact M8|]. exact M9. }
    split; [exact HM4|]. split; [|exact X2].
    intros x Hx.
    rewrite (K9 x Hx). rewrite (K8 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K7 x Hx).
    rewrite (K6 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K5 x Hx).
    rewrite (K4 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K3 x Hx).
    rewrite (K2 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). apply (K1 x Hx).
  Qed.

  Lemma phase3 : forall (K : nat) regs m,
    getr regs 2 = Z_to_bv 64 (usp - 112) -> getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 udata ->
    getr regs 19 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 Bv ->
    getr regs 21 = Z_to_bv 64 (n - Z.of_nat K * Bv) -> getr regs 26 = Z_to_bv 64 4294967295 ->
    getr regs 27 = Z_to_bv 64 NX ->
    MINV sp M0 m -> Z.of_nat K * Bv <= n < (Z.of_nat K + 1) * Bv ->
    exists r m', msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14418 : word) m rom) (mkst r (0x144c4 : word) m' rom)
      /\ MINV sp M0 m' /\ lkeeps hk regs r /\ getr r 2 = Z_to_bv 64 (usp - 112).
  Proof.
    intros K regs m R2 R8 R9 R19 R20 R21 R26 R27 HM HK.
    ranges. pose proof (minv_ld0_ mem sp data n M0 HU m HM) as L0.
    destruct K as [|k].
    -
      change (Z.of_nat 0) with 0 in *. rewrite Z.mul_0_l, Z.sub_0_r in R21.
      assert (S1 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14418 : word) m rom) (mkst r (0x14464 : word) m rom)
        /\ getr r 11 = Z_to_bv 64 0 /\ getr r 10 = Z_to_bv 64 1
        /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
        /\ getr r 19 = Z_to_bv 64 n /\ getr r 21 = Z_to_bv 64 n /\ getr r 26 = Z_to_bv 64 4294967295
        /\ lkeeps hk regs r).
      { eexists. split.
        - stepb_ft F_143b8 D_143b8 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_lt; lia).
          stepz F_143bc D_143bc.
          ld0 F_143c0 D_143c0 L0.
          stepz F_143c4 D_143c4.
          apply mst_refl.
        - unfold hk. post. }
      destruct S1 as (r1 & M1 & A11 & A10 & A2 & A8 & A9 & A19 & A21 & A26 & K1).
      rewrite <- harness_adler_init in A10. change (@nil Z) with (D 0) in A10.
      destruct (adl_tail r1 m 0 A11 A10 A2 A8 A9 A19 ltac:(rewrite Z.sub_0_r; exact A21) A26 HM ltac:(lia) ltac:(lia))
        as (r2 & m2 & M2 & HM2 & K2 & X2).
      exists r2, m2. split; [eapply msteps_trans; [exact M1 | exact M2]|].
      split; [exact HM2|]. split; [eapply lkeeps_trans; [exact K1 | exact K2] | exact X2].
    -
      assert (Hk : 0 + Bv + Z.of_nat k * Bv <= n < 0 + Bv + (Z.of_nat k + 1) * Bv) by (rewrite Nat2Z.inj_succ in HK; lia).
      assert (S1 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14418 : word) m rom) (mkst r (0x14430 : word) m rom)
        /\ ARH sp data n Bv (n - Z.of_nat (S k) * Bv) NX r 0 1 /\ lkeeps hk regs r).
      { eexists. split.
        - stepb_tk F_143b8 D_143b8 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_ge; lia).
          stepz F_143c8 D_143c8.
          ld0 F_143cc D_143cc L0.
          apply mst_refl.
        - unfold ARH, hk. post. }
      destruct S1 as (r1 & M1 & HR1 & K1).
      rewrite <- harness_adler_init in HR1. change (@nil Z) with (D 0) in HR1.
      destruct (adl_loop (n - Z.of_nat (S k) * Bv) k r1 m 0 HR1 HM ltac:(lia) Hk)
        as (r2 & m2 & M2 & HM2 & K2 & V11 & V10 & V2 & V8 & V9 & V19 & V20 & V21 & V26 & V27).
      replace (0 + Bv + Z.of_nat k * Bv) with (Z.of_nat (S k) * Bv) in V11, V10 by lia.
      destruct (adl_tail r2 m2 (Z.of_nat (S k) * Bv) V11 V10 V2 V8 V9 V19 V21 V26 HM2 ltac:(lia) ltac:(lia))
        as (r3 & m3 & M3 & HM3 & K3 & X3).
      exists r3, m3. split; [eapply msteps_trans; [exact M1 |]; eapply msteps_trans; [exact M2 | exact M3]|].
      split; [exact HM3|]. split; [| exact X3].
      eapply lkeeps_trans; [exact K1|]. eapply lkeeps_trans; [exact K2 | exact K3].
  Qed.
End PHASE3.
