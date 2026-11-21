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
  U0Fuzz_crc U0Fuzz_cop U0Fuzz_gen U0Fuzz_comb U0FuzzA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkHarness.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section PHASE2.
Context {RCa1 : RunCtx}.
  Variables (mem : word -> option byte) (sp data : word) (n : Z) (M0 rom : word -> option byte).
  Hypothesis HU : u0H mem sp data n M0.
  Variable Bv : Z.
  Hypothesis HBv : Bv = hB mem data.

  #[local] Abbreviation usp := (bv_unsigned sp).
  #[local] Abbreviation udata := (bv_unsigned data).
  #[local] Abbreviation D k := (HD mem data k).
  #[local] Abbreviation CH off k := (CHK mem data off k).

  Lemma Bv_range2 : 1 <= Bv <= 256.
  Proof. rewrite HBv. apply hB_range. Qed.

  Ltac ranges := pose proof (u64_range data); pose proof (u64_range sp);
                 pose proof (Un _ _ _ _ _ HU); pose proof (Unw _ _ _ _ _ HU); pose proof (Udata _ _ _ _ _ HU);
                 pose proof (Usp _ _ _ _ _ HU); pose proof (Uapart _ _ _ _ _ HU); pose proof Bv_range2.

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

  Lemma phase2 : forall regs m offq,
    getr regs 11 = Z_to_bv 64 offq -> getr regs 18 = Z_to_bv 64 (crc32_spec 0 (D offq)) ->
    getr regs 2 = Z_to_bv 64 (usp - 112) -> getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 udata ->
    getr regs 19 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 Bv ->
    getr regs 22 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 4294967295 ->
    MINV sp M0 m -> 0 <= offq <= n -> n - offq < Bv -> n mod Bv = n - offq ->
    exists r m', msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14350 : word) m rom) (mkst r (0x14418 : word) m' rom)
      /\ MINV sp M0 m' /\ lkeeps hk regs r
      /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv
      /\ getr r 21 = Z_to_bv 64 (n - offq) /\ getr r 26 = Z_to_bv 64 4294967295
      /\ getr r 27 = Z_to_bv 64 (ONES64 - udata).
  Proof.
    intros regs m offq R11 R18 R2 R8 R9 R19 R20 R22 R26 HM Hoff HT Hmod.
    ranges.
    set (C := crc32_spec 0 (D offq)) in R18.
    assert (HCr : 0 <= C < two32) by (subst C; apply crc32_spec_range, HD_bytes).
    set (T := n - offq) in *.
    set (NX := ONES64 - udata).
    assert (S1 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14350 : word) m rom) (mkst r (0x14568 : word) m rom)
      /\ getr r 1 = (0x1436c%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 C /\ getr r 11 = Z_to_bv 64 (udata + offq) /\ getr r 12 = Z_to_bv 64 T
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 C
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
      /\ getr r 22 = Z_to_bv 64 0 /\ getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX
      /\ lkeeps hk regs r).
    { eexists. split.
      - stepi F_142f0 D_142f0; gres; imm_norm; rwR. rewrite zv_not by lia. fold NX.
        stepb_ft F_142f4 D_142f4 ltac:(rwR; rewrite zc_ltu by (unfold NX, ONES64; lia); apply Z.ltb_ge; unfold NX, ONES64; lia).
        stepz F_142f8 D_142f8.
        stepi F_142fc D_142fc. 1: gres; rwR; rewrite u64_lit by lia; lia. znorm.
        zval T ltac:(unfold v_remu; rewrite !u64_lit by lia; rewrite Hmod; reflexivity).
        stepz F_14300 D_14300. stepz F_14304 D_14304. stepz F_14308 D_14308.
        apply mst_refl.
      - unfold hk. post. }
    destruct S1 as (r1 & M1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A26 & A27 & K1).
    destruct (u0_crc32_z r1 m rom (0x1436c%bv : word) (usp - 112) C (udata + offq) T
                A1 ltac:(retok) A2 A10 A11 A12
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(apply (minv_stk_ mem sp data n M0 HU m); [exact HM | lia | change (Z.of_nat 112) with 112; lia])
                ltac:(intros _; lia) ltac:(apply (minv_img_ sp M0); exact HM)
                ltac:(apply (minv_rd_off_ mem sp data n M0 HU m offq T HM); lia))
      as (r2 & m2 & M2 & V2 & K2 & F2).
    rewrite (minv_bytes_ mem sp data n M0 HU m offq T HM) in V2 by lia.
    change (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (udata + offq) (Z.to_nat T)) with (CH offq T) in V2.
    assert (ECRC : crc32_z_model (udata + offq) C (CH offq T) = crc32_spec 0 (D n)).
    { subst C. replace (HD mem data n) with (D (offq + T)) by (f_equal; lia).
      unfold HD, CHK. rewrite (bytes_at_appZ (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem udata offq T) by lia.
      apply harness_crc_stream; apply bytes_at_range. }
    rewrite ECRC in V2. set (CRC := crc32_spec 0 (D n)) in V2.
    assert (HCRC : 0 <= CRC < two32) by (subst CRC; apply crc32_spec_range, HD_bytes).
    pose proof (sx32_range CRC HCRC) as HsxCRC.
    assert (HM2 : MINV sp M0 m2)
      by (eapply (minv_frame_ mem sp data n M0 HU m m2); [exact HM | exact F2 | lia | lia | lia]).
    xfer K2 A2 B2. xfer K2 A8 B8. xfer K2 A9 B9. xfer K2 A19 B19. xfer K2 A20 B20.
    xfer K2 A21 B21. xfer K2 A22 B22. xfer K2 A26 B26. xfer K2 A27 B27.
    assert (S3 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r2 (0x1436c%bv : word) m2 rom) (mkst r (0x14ce4 : word) m2 rom)
      /\ getr r 1 = (0x14384%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = Z_to_bv 64 udata /\ getr r 12 = Z_to_bv 64 n
      /\ getr r 18 = Z_to_bv 64 (sx32 CRC) /\ getr r 23 = Z_to_bv 64 CRC
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
      /\ getr r 22 = Z_to_bv 64 0 /\ getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX
      /\ lkeeps hk r2 r).
    { eexists. split.
      - stepz F_1430c D_1430c. stepz F_14310 D_14310. rewrite (mod_small_32 CRC) by lia.
        stepz F_14314 D_14314. stepz F_14318 D_14318. stepz F_1431c D_1431c. stepz F_14320 D_14320.
        apply mst_refl.
      - unfold hk. post. }
    destruct S3 as (r3 & M3 & B1 & B2' & B10 & B11 & B12 & B18' & B23 & B8' & B9' & B19' & B20' & B21' & B22' & B26' & B27' & K3).
    destruct (u0_crc32 r3 m2 rom (0x14384%bv : word) (usp - 112) 0 udata n n
                B1 ltac:(retok) B2' B10 B11 B12
                ltac:(lia) ltac:(rewrite Z.mod_small; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(apply (minv_stk_ mem sp data n M0 HU m2); [exact HM2 | lia | change (Z.of_nat 112) with 112; lia])
                ltac:(intros _; lia) ltac:(apply (minv_img_ sp M0); exact HM2)
                (minv_rd_ mem sp data n M0 HU m2 HM2))
      as (r4 & m4 & M4 & V4 & K4 & F4).
    rewrite <- (Z.add_0_r udata) in V4. rewrite (minv_bytes_ mem sp data n M0 HU m2 0 n HM2) in V4 by lia.
    rewrite (Z.add_0_r udata) in V4. change (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem udata (Z.to_nat n)) with (D n) in V4.
    rewrite (crc32_z_model_spec udata 0 (D n) (HD_bytes mem data n)) in V4. fold CRC in V4.
    assert (HM4 : MINV sp M0 m4)
      by (eapply (minv_frame_ mem sp data n M0 HU m2 m4); [exact HM2 | exact F4 | lia | lia | lia]).
    xfer K4 B2' C2. xfer K4 B8' C8. xfer K4 B9' C9. xfer K4 B18' C18. xfer K4 B19' C19. xfer K4 B20' C20.
    xfer K4 B21' C21. xfer K4 B22' C22. xfer K4 B23 C23. xfer K4 B26' C26. xfer K4 B27' C27.
    assert (S5 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r4 (0x14384%bv : word) m4 rom) (mkst r (0x14e24 : word) m4 rom)
      /\ getr r 1 = (0x143a4%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 CRC /\ getr r 11 = Z_to_bv 64 CRC /\ getr r 12 = Z_to_bv 64 n
      /\ getr r 22 = Z_to_bv 64 CRC /\ getr r 23 = Z_to_bv 64 CRC
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
      /\ getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX
      /\ lkeeps hk r4 r).
    { eexists. split.
      - stepz F_14324 D_14324. rewrite (mod_small_32 CRC) by lia.
        stepb_ft F_14328 D_14328 ltac:(rwR; apply c_eq_refl).
        stepz F_1432c D_1432c. rewrite <- (mod32_land CRC), (mod_small_32 CRC) by lia.
        stepz F_14330 D_14330. rewrite <- (mod32_land CRC), (mod_small_32 CRC) by lia.
        stepz F_14334 D_14334. stepz F_14338 D_14338. stepz F_1433c D_1433c. stepz F_14340 D_14340.
        apply mst_refl.
      - unfold hk. post. }
    destruct S5 as (r5 & M5 & C1 & D2 & D10 & D11 & D12 & D22 & D23 & D8 & D9 & D19 & D20 & D21 & D26 & D27 & K5).
    destruct (u0_crc32_combine r5 m4 rom (0x143a4%bv : word) CRC CRC n C1 ltac:(retok) D10 D11 D12
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply (minv_img_ sp M0); exact HM4)) as (r6 & M6 & V6 & K6).
    set (X1 := crc32_combine CRC CRC n) in V6.
    assert (HX1 : 0 <= X1 < two32) by (subst X1; apply crc32_combine_range; lia).
    xfer K6 D2 E2. xfer K6 D8 E8. xfer K6 D9 E9. xfer K6 D19 E19. xfer K6 D20 E20.
    xfer K6 D21 E21. xfer K6 D22 E22. xfer K6 D23 E23. xfer K6 D26 E26. xfer K6 D27 E27.
    assert (S7 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r6 (0x143a4%bv : word) m4 rom) (mkst r (0x14e24 : word) m4 rom)
      /\ getr r 1 = (0x143b8%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 CRC /\ getr r 11 = Z_to_bv 64 CRC /\ getr r 12 = Z_to_bv 64 n
      /\ getr r 22 = Z_to_bv 64 CRC /\ getr r 23 = Z_to_bv 64 CRC /\ getr r 24 = Z_to_bv 64 X1
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
      /\ getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX
      /\ lkeeps hk r6 r).
    { eexists. split.
      - stepz F_14344 D_14344. stepz F_14348 D_14348. stepz F_1434c D_1434c. stepz F_14350 D_14350.
        stepz F_14354 D_14354. apply mst_refl.
      - unfold hk. post. }
    destruct S7 as (r7 & M7 & E1 & F2' & F10 & F11 & F12 & F22 & F23 & F24 & F8 & F9 & F19 & F20 & F21 & F26 & F27 & K7).
    destruct (u0_crc32_combine r7 m4 rom (0x143b8%bv : word) CRC CRC n E1 ltac:(retok) F10 F11 F12
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply (minv_img_ sp M0); exact HM4)) as (r8 & M8 & V8 & K8).
    fold X1 in V8.
    xfer K8 F2' G2. xfer K8 F8 G8. xfer K8 F9 G9. xfer K8 F19 G19. xfer K8 F20 G20.
    xfer K8 F21 G21. xfer K8 F22 G22. xfer K8 F23 G23. xfer K8 F24 G24. xfer K8 F26 G26. xfer K8 F27 G27.
    assert (S9 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r8 (0x143b8%bv : word) m4 rom) (mkst r (0x14cf0 : word) m4 rom)
      /\ getr r 1 = (0x143c4%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 n
      /\ getr r 22 = Z_to_bv 64 CRC /\ getr r 23 = Z_to_bv 64 CRC
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
      /\ getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX
      /\ lkeeps hk r8 r).
    { eexists. split.
      - stepb_ft F_14358 D_14358 ltac:(rwR; apply c_eq_refl).
        stepz F_1435c D_1435c. stepz F_14360 D_14360. apply mst_refl.
      - unfold hk. post. }
    destruct S9 as (r9 & M9 & G1 & H2' & H10 & H22 & H23 & H8 & H9 & H19 & H20 & H21 & H26 & H27 & K9).
    destruct (u0_crc32_combine_gen r9 m4 rom (0x143c4%bv : word) n G1 ltac:(retok) H10 ltac:(lia)
                ltac:(apply (minv_img_ sp M0); exact HM4)) as (r10 & M10 & V10 & K10).
    set (OP2 := crc32_combine_gen n) in V10.
    assert (HOP2 : 0 <= OP2 < two32) by (subst OP2; apply crc32_combine_gen_range).
    assert (HOP2nz : OP2 mod two32 <> 0) by (subst OP2; apply crc32_combine_gen_nz; lia).
    xfer K10 H2' I2. xfer K10 H8 I8. xfer K10 H9 I9. xfer K10 H19 I19. xfer K10 H20 I20.
    xfer K10 H21 I21. xfer K10 H22 I22. xfer K10 H23 I23. xfer K10 H26 I26. xfer K10 H27 I27.
    assert (S11 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r10 (0x143c4%bv : word) m4 rom) (mkst r (0x14db0 : word) m4 rom)
      /\ getr r 1 = (0x143d8%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 CRC /\ getr r 11 = Z_to_bv 64 CRC /\ getr r 12 = Z_to_bv 64 OP2
      /\ getr r 22 = Z_to_bv 64 CRC /\ getr r 23 = Z_to_bv 64 CRC /\ getr r 24 = Z_to_bv 64 OP2
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
      /\ getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX
      /\ lkeeps hk r10 r).
    { eexists. split.
      - stepz F_14364 D_14364. rewrite <- (mod32_land OP2), (mod_small_32 OP2) by lia.
        stepz F_14368 D_14368. stepz F_1436c D_1436c. stepz F_14370 D_14370. stepz F_14374 D_14374.
        apply mst_refl.
      - unfold hk. post. }
    destruct S11 as (r11 & M11 & I1 & J2 & J10 & J11 & J12 & J22 & J23 & J24 & J8 & J9 & J19 & J20 & J21 & J26 & J27 & K11).
    destruct (u0_crc32_combine_op r11 m4 rom (0x143d8%bv : word) CRC CRC OP2 I1 ltac:(retok) J10 J11 J12
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(exact HOP2nz)) as (r12 & M12 & V12 & K12).
    set (Y := crc32_combine_op CRC CRC OP2) in V12.
    assert (HY : 0 <= Y < two32) by (subst Y; apply crc32_combine_op_range; lia).
    xfer K12 J2 L2. xfer K12 J8 L8. xfer K12 J9 L9. xfer K12 J19 L19. xfer K12 J20 L20.
    xfer K12 J21 L21. xfer K12 J22 L22. xfer K12 J23 L23. xfer K12 J24 L24. xfer K12 J26 L26. xfer K12 J27 L27.
    assert (S13 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r12 (0x143d8%bv : word) m4 rom) (mkst r (0x14db0 : word) m4 rom)
      /\ getr r 1 = (0x143ec%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 CRC /\ getr r 11 = Z_to_bv 64 CRC /\ getr r 12 = Z_to_bv 64 OP2
      /\ getr r 22 = Z_to_bv 64 CRC /\ getr r 23 = Z_to_bv 64 CRC /\ getr r 24 = Z_to_bv 64 OP2 /\ getr r 25 = Z_to_bv 64 Y
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
      /\ getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX
      /\ lkeeps hk r12 r).
    { eexists. split.
      - stepz F_14378 D_14378. stepz F_1437c D_1437c. stepz F_14380 D_14380. stepz F_14384 D_14384.
        stepz F_14388 D_14388. apply mst_refl.
      - unfold hk. post. }
    destruct S13 as (r13 & M13 & L1 & N2 & N10 & N11 & N12 & N22 & N23 & N24 & N25 & N8 & N9 & N19 & N20 & N21 & N26 & N27 & K13).
    destruct (u0_crc32_combine_op r13 m4 rom (0x143ec%bv : word) CRC CRC OP2 L1 ltac:(retok) N10 N11 N12
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(exact HOP2nz)) as (r14 & M14 & V14 & K14).
    fold Y in V14.
    xfer K14 N2 O2. xfer K14 N8 O8. xfer K14 N9 O9. xfer K14 N19 O19. xfer K14 N20 O20.
    xfer K14 N21 O21. xfer K14 N22 O22. xfer K14 N23 O23. xfer K14 N24 O24. xfer K14 N25 O25. xfer K14 N26 O26. xfer K14 N27 O27.
    assert (S15 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r14 (0x143ec%bv : word) m4 rom) (mkst r (0x14e24 : word) m4 rom)
      /\ getr r 1 = (0x14400%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 CRC /\ getr r 11 = Z_to_bv 64 CRC /\ getr r 12 = Z_to_bv 64 n
      /\ getr r 22 = Z_to_bv 64 CRC /\ getr r 23 = Z_to_bv 64 CRC /\ getr r 24 = Z_to_bv 64 OP2
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
      /\ getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX
      /\ lkeeps hk r14 r).
    { eexists. split.
      - stepb_ft F_1438c D_1438c ltac:(rwR; apply c_eq_refl).
        stepz F_14390 D_14390. stepz F_14394 D_14394. stepz F_14398 D_14398. stepz F_1439c D_1439c.
        apply mst_refl.
      - unfold hk. post. }
    destruct S15 as (r15 & M15 & O1 & P2 & P10 & P11 & P12 & P22 & P23 & P24 & P8 & P9 & P19 & P20 & P21 & P26 & P27 & K15).
    destruct (u0_crc32_combine r15 m4 rom (0x14400%bv : word) CRC CRC n O1 ltac:(retok) P10 P11 P12
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply (minv_img_ sp M0); exact HM4)) as (r16 & M16 & V16 & K16).
    fold X1 in V16.
    xfer K16 P2 Q2. xfer K16 P8 Q8. xfer K16 P9 Q9. xfer K16 P19 Q19. xfer K16 P20 Q20.
    xfer K16 P21 Q21. xfer K16 P22 Q22. xfer K16 P23 Q23. xfer K16 P24 Q24. xfer K16 P26 Q26. xfer K16 P27 Q27.
    assert (S17 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r16 (0x14400%bv : word) m4 rom) (mkst r (0x14db0 : word) m4 rom)
      /\ getr r 1 = (0x14414%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 CRC /\ getr r 11 = Z_to_bv 64 CRC /\ getr r 12 = Z_to_bv 64 OP2
      /\ getr r 25 = Z_to_bv 64 X1
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 T
      /\ getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX
      /\ lkeeps hk r16 r).
    { eexists. split.
      - stepz F_143a0 D_143a0. stepz F_143a4 D_143a4. stepz F_143a8 D_143a8. stepz F_143ac D_143ac.
        stepz F_143b0 D_143b0. apply mst_refl.
      - unfold hk. post. }
    destruct S17 as (r17 & M17 & Q1 & U2 & U10 & U11 & U12 & U25 & U8 & U9 & U19 & U20 & U21 & U26 & U27 & K17).
    destruct (u0_crc32_combine_op r17 m4 rom (0x14414%bv : word) CRC CRC OP2 Q1 ltac:(retok) U10 U11 U12
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(exact HOP2nz)) as (r18 & M18 & V18 & K18).
    fold Y in V18.
    assert (E5 : X1 = Y) by (subst X1 Y OP2; apply harness_assert5; reflexivity).
    xfer K18 U2 W2. xfer K18 U8 W8. xfer K18 U9 W9. xfer K18 U19 W19. xfer K18 U20 W20.
    xfer K18 U21 W21. xfer K18 U25 W25. xfer K18 U26 W26. xfer K18 U27 W27.
    assert (S19 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r18 (0x14414%bv : word) m4 rom) (mkst r (0x14418 : word) m4 rom)
      /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv
      /\ getr r 21 = Z_to_bv 64 T /\ getr r 26 = Z_to_bv 64 4294967295 /\ getr r 27 = Z_to_bv 64 NX
      /\ lkeeps hk r18 r).
    { eexists. split.
      - stepb_ft F_143b4 D_143b4 ltac:(rwR; rewrite E5; apply c_eq_refl). apply mst_refl.
      - unfold hk. post. }
    destruct S19 as (r19 & M19 & X2 & X8 & X9 & X19 & X20 & X21 & X26 & X27 & K19).
    exists r19, m4. split.
    { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
      eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5|]. eapply msteps_trans; [exact M6|].
      eapply msteps_trans; [exact M7|]. eapply msteps_trans; [exact M8|]. eapply msteps_trans; [exact M9|].
      eapply msteps_trans; [exact M10|]. eapply msteps_trans; [exact M11|]. eapply msteps_trans; [exact M12|].
      eapply msteps_trans; [exact M13|]. eapply msteps_trans; [exact M14|]. eapply msteps_trans; [exact M15|].
      eapply msteps_trans; [exact M16|]. eapply msteps_trans; [exact M17|]. eapply msteps_trans; [exact M18|].
      exact M19. }
    split; [exact HM4|]. split.
    { intros x Hx.
      rewrite (K19 x Hx). rewrite (K18 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K17 x Hx).
      rewrite (K16 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K15 x Hx).
      rewrite (K14 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K13 x Hx).
      rewrite (K12 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K11 x Hx).
      rewrite (K10 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K9 x Hx).
      rewrite (K8 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K7 x Hx).
      rewrite (K6 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K5 x Hx).
      rewrite (K4 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K3 x Hx).
      rewrite (K2 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). apply (K1 x Hx). }
    subst NX. repeat split; assumption.
  Qed.
End PHASE2.
