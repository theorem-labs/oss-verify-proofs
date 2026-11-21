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
  FuzzLib FuzzZ FuzzCk FuzzMem U0FuzzBase U0Fuzz_code U0FuzzIface U0FuzzStmt U0Fuzz_crc U0Fuzz_cop U0FuzzA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkHarness.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition CRH (sp data : word) (n Bv OPv : Z) (r : bvmap 5 word) (off C : Z) : Prop :=
  getr r 2 = Z_to_bv 64 (bv_unsigned sp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 (bv_unsigned data) /\
  getr r 18 = Z_to_bv 64 C /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\
  getr r 22 = Z_to_bv 64 0 /\ getr r 24 = Z_to_bv 64 OPv /\ getr r 26 = Z_to_bv 64 4294967295 /\
  getr r 27 = Z_to_bv 64 off.

Section LOOPB.
Context {RCa1 : RunCtx}.
  Variables (mem : word -> option byte) (sp data : word) (n : Z) (M0 rom : word -> option byte).
  Hypothesis HU : u0H mem sp data n M0.
  Variables (Bv OPv : Z).
  Hypothesis HBv : Bv = hB mem data.
  Hypothesis HOPv : OPv = crc32_combine_gen Bv.

  #[local] Abbreviation usp := (bv_unsigned sp).
  #[local] Abbreviation udata := (bv_unsigned data).
  #[local] Abbreviation D k := (HD mem data k).
  #[local] Abbreviation CH off k := (CHK mem data off k).

  Lemma Bv_range : 1 <= Bv <= 256.
  Proof. rewrite HBv. apply hB_range. Qed.
  Lemma OPv_range : 0 <= OPv < two32.
  Proof. rewrite HOPv. apply crc32_combine_gen_range. Qed.
  Lemma OPv_nz : OPv mod two32 <> 0.
  Proof. rewrite HOPv. pose proof Bv_range. apply crc32_combine_gen_nz. lia. Qed.

  Ltac ranges := pose proof (u64_range data); pose proof (u64_range sp);
                 pose proof (Un _ _ _ _ _ HU); pose proof (Unw _ _ _ _ _ HU); pose proof (Udata _ _ _ _ _ HU);
                 pose proof (Usp _ _ _ _ _ HU); pose proof (Uapart _ _ _ _ _ HU); pose proof Bv_range.

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

  Lemma crc_exit : forall regs m off C,
    CRH sp data n Bv OPv regs off C -> 0 <= off <= n -> n < off + Bv -> 0 <= C < two32 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x142cc : word) m rom) (mkst r (0x14350 : word) m rom)
      /\ getr r 11 = Z_to_bv 64 off /\ getr r 18 = Z_to_bv 64 C
      /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv
      /\ getr r 22 = Z_to_bv 64 0 /\ getr r 26 = Z_to_bv 64 4294967295
      /\ lkeeps hk regs r.
  Proof.
    intros regs m off C (R2 & R8 & R9 & R18 & R19 & R20 & R22 & R24 & R26 & R27) Hoff Hexit HC.
    ranges.
    eexists. split.
    - stepz F_1426c D_1426c. stepz F_14270 D_14270.
      rewrite (mod_small_32 (off + Bv)), (sx32_small (off + Bv)) by lia.
      stepz F_14274 D_14274. rewrite (mod_small_32 off) by lia.
      stepb_tk F_14278 D_14278 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_lt; lia).
      apply mst_refl.
    - unfold hk. post.
  Qed.

  Lemma crc_iter : forall regs m off C,
    CRH sp data n Bv OPv regs off C -> MINV sp M0 m -> 0 <= off -> off + Bv <= n -> C = crc32_spec 0 (D off) ->
    exists r m', msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x142cc : word) m rom) (mkst r (0x142cc : word) m' rom)
      /\ CRH sp data n Bv OPv r (off + Bv) (crc32_spec 0 (D (off + Bv))) /\ MINV sp M0 m' /\ lkeeps hk regs r.
  Proof.
    intros regs m off C (R2 & R8 & R9 & R18 & R19 & R20 & R22 & R24 & R26 & R27) HM Hoff Hin HC.
    ranges. pose proof OPv_range as HOP'. pose proof OPv_nz as HOPnz.
    assert (HCr : 0 <= C < two32) by (rewrite HC; apply crc32_spec_range, HD_bytes).
    assert (S1 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x142cc : word) m rom) (mkst r (0x14568 : word) m rom)
      /\ getr r 1 = (0x142f4%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = Z_to_bv 64 (udata + off) /\ getr r 12 = Z_to_bv 64 Bv
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 C
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 22 = Z_to_bv 64 0
      /\ getr r 24 = Z_to_bv 64 OPv /\ getr r 26 = Z_to_bv 64 4294967295
      /\ getr r 27 = Z_to_bv 64 (off + Bv) /\ getr r 25 = Z_to_bv 64 (udata + off)
      /\ lkeeps hk regs r).
    { eexists. split.
      - stepz F_1426c D_1426c. stepz F_14270 D_14270.
        rewrite (mod_small_32 (off + Bv)), (sx32_small (off + Bv)) by lia.
        stepz F_14274 D_14274. rewrite (mod_small_32 off) by lia.
        stepb_ft F_14278 D_14278 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_ge; lia).
        stepz F_1427c D_1427c.
        stepb_ft F_14280 D_14280 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_ge; lia).
        stepz F_14284 D_14284. stepz F_14288 D_14288. stepz F_1428c D_1428c. stepz F_14290 D_14290.
        apply mst_refl.
      - unfold hk. post. }
    destruct S1 as (r1 & M1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A18 & A19 & A20 & A22 & A24 & A26 & A27 & A25 & K1).
    destruct (u0_crc32_z r1 m rom (0x142f4%bv : word) (usp - 112) 0 (udata + off) Bv
                A1 ltac:(retok) A2 A10 A11 A12
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(apply (minv_stk_ mem sp data n M0 HU m); [exact HM | lia | change (Z.of_nat 112) with 112; lia])
                ltac:(intros _; lia) ltac:(apply (minv_img_ sp M0); exact HM)
                ltac:(apply (minv_rd_off_ mem sp data n M0 HU m off Bv HM); lia))
      as (r2 & m2 & M2 & V2 & K2 & F2).
    rewrite (minv_bytes_ mem sp data n M0 HU m off Bv HM) in V2 by lia.
    change (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (udata + off) (Z.to_nat Bv)) with (CH off Bv) in V2.
    set (crc3 := crc32_z_model (udata + off) 0 (CH off Bv)) in V2.
    assert (Hc3 : 0 <= crc3 < two32) by (subst crc3; apply crc32_z_model_range, CHK_bytes).
    assert (HM2 : MINV sp M0 m2)
      by (eapply (minv_frame_ mem sp data n M0 HU m m2); [exact HM | exact F2 | lia | lia | lia]).
    xfer K2 A2 B2. xfer K2 A8 B8. xfer K2 A9 B9. xfer K2 A18 B18. xfer K2 A19 B19. xfer K2 A20 B20.
    xfer K2 A22 B22. xfer K2 A24 B24. xfer K2 A25 B25. xfer K2 A26 B26. xfer K2 A27 B27.
    assert (S3 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r2 (0x142f4%bv : word) m2 rom) (mkst r (0x14db0 : word) m2 rom)
      /\ getr r 1 = (0x14304%bv : word) /\ getr r 10 = Z_to_bv 64 C /\ getr r 11 = Z_to_bv 64 crc3
      /\ getr r 12 = Z_to_bv 64 OPv
      /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 18 = Z_to_bv 64 C /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv
      /\ getr r 22 = Z_to_bv 64 0 /\ getr r 24 = Z_to_bv 64 OPv /\ getr r 26 = Z_to_bv 64 4294967295
      /\ getr r 27 = Z_to_bv 64 (off + Bv) /\ getr r 25 = Z_to_bv 64 (udata + off)
      /\ lkeeps hk r2 r).
    { eexists. split.
      - stepz F_14294 D_14294. rewrite <- (mod32_land crc3), (mod_small_32 crc3) by lia.
        stepz F_14298 D_14298. stepz F_1429c D_1429c. stepz F_142a0 D_142a0.
        apply mst_refl.
      - unfold hk. post. }
    destruct S3 as (r3 & M3 & B1 & B10 & B11 & B12 & B2' & B8' & B9' & B18' & B19' & B20' & B22' & B24' & B26' & B27' & B25' & K3).
    destruct (cop_run m2 rom (0x14304%bv : word) ltac:(retok) r3 C crc3 OPv
                B1 B10 B11 B12 HCr ltac:(lia) ltac:(lia) HOPnz) as (r4 & M4 & V4 & K4).
    set (crc4 := crc32_combine_op C crc3 OPv) in V4.
    assert (Hc4 : 0 <= crc4 < two32) by (subst crc4; apply crc32_combine_op_range; lia).
    xfer K4 B2' C2. xfer K4 B8' C8. xfer K4 B9' C9. xfer K4 B18' C18. xfer K4 B19' C19. xfer K4 B20' C20.
    xfer K4 B22' C22. xfer K4 B24' C24. xfer K4 B25' C25. xfer K4 B26' C26. xfer K4 B27' C27.
    assert (S5 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r4 (0x14304%bv : word) m2 rom) (mkst r (0x14568 : word) m2 rom)
      /\ getr r 1 = (0x14320%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ getr r 10 = Z_to_bv 64 C /\ getr r 11 = Z_to_bv 64 (udata + off) /\ getr r 12 = Z_to_bv 64 Bv
      /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 C
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 22 = Z_to_bv 64 0
      /\ getr r 24 = Z_to_bv 64 OPv /\ getr r 26 = Z_to_bv 64 4294967295
      /\ getr r 27 = Z_to_bv 64 (off + Bv) /\ getr r 23 = Z_to_bv 64 crc4 /\ getr r 25 = Z_to_bv 64 (udata + off)
      /\ lkeeps hk r4 r).
    { eexists. split.
      - stepb_ft F_142a4 D_142a4 ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
        stepz F_142a8 D_142a8. stepz F_142ac D_142ac. rewrite (mod_small_32 crc4) by lia.
        stepz F_142b0 D_142b0. stepz F_142b4 D_142b4. stepz F_142b8 D_142b8. stepz F_142bc D_142bc.
        apply mst_refl.
      - unfold hk. post. }
    destruct S5 as (r5 & M5 & C1 & C2' & C10 & C11 & C12 & C8' & C9' & C18' & C19' & C20' & C22' & C24' & C26' & C27' & C23 & C25' & K5).
    destruct (u0_crc32_z r5 m2 rom (0x14320%bv : word) (usp - 112) C (udata + off) Bv
                C1 ltac:(retok) C2' C10 C11 C12
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(apply (minv_stk_ mem sp data n M0 HU m2); [exact HM2 | lia | change (Z.of_nat 112) with 112; lia])
                ltac:(intros _; lia) ltac:(apply (minv_img_ sp M0); exact HM2)
                ltac:(apply (minv_rd_off_ mem sp data n M0 HU m2 off Bv HM2); lia))
      as (r6 & m6 & M6 & V6 & K6 & F6).
    rewrite (minv_bytes_ mem sp data n M0 HU m2 off Bv HM2) in V6 by lia.
    change (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem (udata + off) (Z.to_nat Bv)) with (CH off Bv) in V6.
    assert (HM6 : MINV sp M0 m6)
      by (eapply (minv_frame_ mem sp data n M0 HU m2 m6); [exact HM2 | exact F6 | lia | lia | lia]).
    assert (E1 : crc32_z_model (udata + off) C (CH off Bv) = crc4).
    { subst crc4 crc3. rewrite HOPv.
      replace (crc32_combine_gen Bv) with (crc32_combine_gen (Zlen (CH off Bv))) by (rewrite CHK_len by lia; reflexivity).
      apply harness_assert1; [apply CHK_bytes | exact HCr | rewrite CHK_len by lia; lia]. }
    rewrite E1 in V6.
    xfer K6 C2' E2. xfer K6 C8' E8. xfer K6 C9' E9. xfer K6 C19' E19. xfer K6 C20' E20.
    xfer K6 C22' E22. xfer K6 C23 E23. xfer K6 C24' E24. xfer K6 C26' E26. xfer K6 C27' E27.
    assert (S7 : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r6 (0x14320%bv : word) m6 rom) (mkst r (0x142cc : word) m6 rom)
      /\ CRH sp data n Bv OPv r (off + Bv) crc4 /\ lkeeps hk r6 r).
    { eexists. split.
      - stepz F_142c0 D_142c0. stepz F_142c4 D_142c4. rewrite (mod_small_32 crc4) by lia.
        stepz F_142c8 D_142c8.
        stepb_tk F_142cc D_142cc ltac:(rwR; apply c_eq_refl).
        apply mst_refl.
      - unfold CRH, hk. post. }
    destruct S7 as (r7 & M7 & H7 & K7).
    exists r7, m6. split; [|split; [|split]].
    - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|].
      eapply msteps_trans; [exact M3|]. eapply msteps_trans; [exact M4|].
      eapply msteps_trans; [exact M5|]. eapply msteps_trans; [exact M6|]. exact M7.
    - replace (crc32_spec 0 (D (off + Bv))) with crc4; [exact H7|].
      subst crc4. rewrite <- E1. rewrite HC. unfold CHK, HD. rewrite (bytes_at_appZ (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) mem udata off Bv) by lia.
      apply harness_crc_stream; [apply bytes_at_range | apply bytes_at_range].
    - exact HM6.
    - intros x Hx. rewrite (K7 x Hx). rewrite (K6 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])).
      rewrite (K5 x Hx). rewrite (K4 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])).
      rewrite (K3 x Hx). rewrite (K2 x) by (revert Hx; unfold hk; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). apply (K1 x Hx).
  Qed.

  Lemma crc_loop : forall (k : nat) regs m off,
    CRH sp data n Bv OPv regs off (crc32_spec 0 (D off)) -> MINV sp M0 m -> 0 <= off ->
    off + Z.of_nat k * Bv <= n < off + (Z.of_nat k + 1) * Bv ->
    exists r m', msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x142cc : word) m rom) (mkst r (0x14350 : word) m' rom)
      /\ MINV sp M0 m' /\ lkeeps hk regs r
      /\ getr r 11 = Z_to_bv 64 (off + Z.of_nat k * Bv)
      /\ getr r 18 = Z_to_bv 64 (crc32_spec 0 (D (off + Z.of_nat k * Bv)))
      /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
      /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv
      /\ getr r 22 = Z_to_bv 64 0 /\ getr r 26 = Z_to_bv 64 4294967295.
  Proof.
    induction k as [|k IH]; intros regs m off HR HM Hoff Hk.
    - change (Z.of_nat 0) with 0 in *. pose proof Bv_range.
      assert (HCr : 0 <= crc32_spec 0 (D off) < two32) by (apply crc32_spec_range, HD_bytes).
      destruct (crc_exit regs m off _ HR ltac:(lia) ltac:(lia) HCr)
        as (r & M & V11 & V18 & V2 & V8 & V9 & V19 & V20 & V22 & V26 & K).
      exists r, m. rewrite Z.mul_0_l, Z.add_0_r.
      split; [exact M|]. split; [exact HM|]. split; [exact K|]. repeat split; assumption.
    - pose proof Bv_range.
      assert (Hk' : off + Bv + Z.of_nat k * Bv <= n < off + Bv + (Z.of_nat k + 1) * Bv) by (rewrite Nat2Z.inj_succ in Hk; lia).
      destruct (crc_iter regs m off _ HR HM Hoff ltac:(lia) eq_refl) as (r1 & m1 & M1 & HR1 & HM1 & K1).
      destruct (IH r1 m1 (off + Bv) HR1 HM1 ltac:(lia) Hk')
        as (r & m' & M & HM' & K & V11 & V18 & V2 & V8 & V9 & V19 & V20 & V22 & V26).
      exists r, m'. replace (off + Z.of_nat (S k) * Bv) with (off + Bv + Z.of_nat k * Bv) by lia.
      split; [eapply msteps_trans; [exact M1 | exact M]|].
      split; [exact HM'|]. split; [eapply lkeeps_trans; [exact K1 | exact K]|].
      repeat split; assumption.
  Qed.
End LOOPB.
