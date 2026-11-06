(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit F_m2s F_mem_is_zero.
Import ListNotations.
Open Scope Z_scope.

Definition A0_rip : Z := 0x5a188.
Definition rip_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 80, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q.

Section Proofs.
  Variables (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo B n : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo q.
  Hypothesis LO : lo <= q - 80.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Hypothesis ES : env_shadow m.
  Hypothesis LAY : env_layout m.
  Hypothesis WIN : rwin B n.
  Hypothesis ACC : accessible m B n.
  Hypothesis NSZ : 8 <= n <= 2^43.

  Notation RPOST := (rip_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  #[using="LO"] Lemma L5 : forall (m2 : mem) junk8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x8 x9 x18 x19 x20 x21 x28 x29 x30 x31,
    rw_cells asegs m2 (q + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs m2 lo (q + -64) ->
    munch [(q + -80, q)] m m2 -> wmono asegs m m2 -> mem_inv asegs m2 ->
    evt asegs RPOST
      (MS (mkR x1 (wz (q + -64)) gp tp x5 x6 x7 x8 x9
               x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x5a300) fc None m2 (seg_rom asegs)).
  Proof.
    intros until x31. intros FR ST2 MU2 WM2 MI2.
    do 11 zstep. release_frame FR ST2 q. finish.
  Qed.

  #[using="KLO Q64 WIN"] Lemma BND : 0 <= B /\ B + n < 2^47 /\ 0 <= lo /\ q <= 2^64.
  Proof. unfold rwin in WIN. lia. Qed.

  Section AfterFrame.
    Variables (m1 : mem) (junk8 : list byte).
    Hypothesis FR : rw_cells asegs m1 (q + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis ST1 : stk asegs m1 lo (q + -64).
    Hypothesis MU1 : munch [(q + -80, q)] m m1.
    Hypothesis WM1 : wmono asegs m m1.
    Hypothesis MI1 : mem_inv asegs m1.
    Hypothesis GOT1 : rw_cells asegs m1 699696 [C8 (Z_to_bv 64 738616)].
    Hypothesis SHB1 : rw_cells asegs m1 738616 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis LG1 : rw_cells asegs m1 699704 [C8 (Z_to_bv 64 741928); C8 (Z_to_bv 64 741936); C8 (Z_to_bv 64 741920)].
    Hypothesis LC1 : rw_cells asegs m1 741920 [C8 (Z_to_bv 64 140737488355327); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
    Hypothesis ACC1 : accessible m1 B n.

    Section Core.
    Variables (AB AE : Z).
    Hypothesis RAB : B <= AB <= B + 7 /\ AB mod 8 = 0.
    Hypothesis RAE : B + n - 7 <= AE <= B + n /\ AE mod 8 = 0.

    #[using="B n LO KLO Q64 WIN NSZ junk8 FR ST1 MU1 WM1 MI1 GOT1 SHB1 LG1 LC1 ACC1 RAB RAE"] Lemma L4 : forall x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x28 x29 x30 x31,
      evt asegs RPOST
        (MS (mkR x1 (wz (q + -64)) gp tp x5 x6 x7 x8 x9 (wz (sh AE)) x11 x12 x13 x14 x15 x16 x17
                 x18 (wz (sh AB)) x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz 0x5a2ec) fc None m1 (seg_rom asegs)).
    Proof.
      intros. pose proof BND as BD.
      assert (SHR : 2147450880 <= sh B /\ sh B <= sh AB /\ 2147450880 <= sh AE /\ sh AE < 17594333495296 /\ sh AB < 17594333495296
                    /\ 8 * (sh AE - SHADOW_OFF) = AE /\ 8 * (sh AB - SHADOW_OFF) = AB)
        by (unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
      zstep. if_cases K8; zify_cond K8.
      {   eapply L5; eassumption. }
      assert (ZR : zrun m1 (sh AB) (sh AB + (sh AE - sh AB))).
      { eapply acc_core_zrun; [exact ACC1| lia| lia]. }
      zstep. zstep. zstep.
      call miz_spec; [exact MI1 | exact ST1 | lia | lia | exact ZR | lia | lia | lia | reflexivity | reflexivity |].
      fold_lits. zstep. if_cases K9; zify_cond K9. { exfalso. clear - K9. cbv in K9. lia. }
      match goal with P : stk asegs _ lo (q + -64) |- _ => eapply L5; [ eassumption | exact P | eassumption | eassumption | eassumption ] end.
    Qed.

    #[using="LO KLO Q64 WIN NSZ junk8 FR ST1 MU1 WM1 MI1 GOT1 SHB1 LG1 LC1 ACC1 RAB RAE"] Lemma L3 : forall x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
      evt asegs RPOST
        (MS (mkR x1 (wz (q + -64)) gp tp x5 x6 x7 x8 x9 (wz (sh AE)) (wz 2147450880) x12 x13 x14 x15 x16 x17
                 (wz (n + B)) (wz (sh AB)) x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz 0x5a298) fc None m1 (seg_rom asegs)).
    Proof.
      intros. pose proof BND as BD.
      do 3 zstep.
      destruct (acc_byte_rd m1 B n (n + B + -1) ACC1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
      unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
      zstep.
      rewrite (sxb_small k2) by lia.
      zstep. if_cases K6; zify_cond K6.
      { apply L4. }
      zstep. zstep. if_cases K7; zify_cond K7.
      2:{ exfalso. zify_granule K7. pose proof (Z.mod_pos_bound (n + B + -1) 8 ltac:(lia)). lia. }
      apply L4.
    Qed.
    End Core.

    #[using="LO KLO Q64 WIN NSZ junk8 FR ST1 MU1 WM1 MI1 GOT1 SHB1 LG1 LC1 ACC1"] Lemma L2 : forall x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31,
      evt asegs RPOST
        (MS (mkR x1 (wz (q + -64)) gp tp x5 x6 x7 (wz B) x9 x10 x11 x12 x13 x14 x15 x16 x17
                 (wz (n + B)) x19 x20 (wz 738616) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz 0x5a25c) fc None m1 (seg_rom asegs)).
    Proof.
      intros. pose proof BND as BD.
      zstep. if_cases K5; zify_cond K5. { exfalso; lia. }
      do 3 zstep.
      change 18446744073709551608 with (2^64 - 2^3). rewrite !land_align_down by lia.
      remember (B + 7 - (B + 7) mod 2 ^ 3) as AB eqn:HAB.
      remember (n + B - (n + B) mod 2 ^ 3) as AE eqn:HAE.
      assert (RAB : B <= AB <= B + 7 /\ AB mod 8 = 0) by (subst AB; Z.div_mod_to_equations; lia).
      assert (RAE : B + n - 7 <= AE <= B + n /\ AE mod 8 = 0) by (subst AE; Z.div_mod_to_equations; lia).
      clear HAB HAE.
      zstep.
      call m2s_spec; [assumption| split; assumption | split; assumption | reflexivity | unfold rwin in WIN; lia |].
      do 3 zstep.
      call m2s_spec; [assumption| split; assumption | split; assumption | reflexivity | unfold rwin in WIN; lia |].
      do 3 zstep.
      destruct (acc_byte_rd m1 B n B ACC1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k1 & RD1 & CK1).
      unfold sh at 1, SHADOW_OFF in RD1. rewrite <- shiftr3_div in RD1.
      zstep. rewrite (sxb_small k1) by lia.
      zstep. if_cases K6; zify_cond K6.
      { eapply L3; eassumption. }
      zstep. zstep. if_cases K7; zify_cond K7.
      { exfalso. zify_granule K7. pose proof (Z.mod_pos_bound B 8 ltac:(lia)). lia. }
      eapply L3; eassumption.
    Qed.

    #[using="LO KLO Q64 WIN NSZ junk8 FR ST1 MU1 WM1 MI1 GOT1 SHB1 LG1 LC1 ACC1"] Lemma L1 : forall x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
      evt asegs RPOST
        (MS (mkR x1 (wz (q + -64)) gp tp x5 x6 x7 (wz B) (wz n) x10 (wz 2147450880) (wz 2147450879) x13 x14 x15 x16 x17
                 x18 x19 x20 (wz 738616) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz 0x5a214) fc None m1 (seg_rom asegs)).
    Proof.
      intros. pose proof BND as BD.
      zstep. zstep. if_cases K1; zify_cond K1.
      - apply L2.
      - do 7 zstep. fold_lits. zsimp. zstep. if_cases K2; zify_cond K2. 2:{ exfalso; lia. }
        do 6 zstep. fold_lits. if_cases K3; zify_cond K3. { exfalso; unfold rwin in WIN; lia. }
        zstep. if_cases K4; zify_cond K4. { exfalso; unfold rwin in WIN; lia. }
        apply L2.
    Qed.
  End AfterFrame.

  #[using="MI ST LO KLO Q64 ES LAY WIN ACC NSZ"] Lemma rip_body : forall a0 a1 a2 a3 a4 a5 a6 a7, a0 = wz B -> a1 = wz n ->
    evt asegs RPOST (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz A0_rip) fc None m (seg_rom asegs)).
  Proof.
    intros a0 a1 a2 a3 a4 a5 a6 a7 -> ->. unfold A0_rip. pose proof BND as BD.
    pose proof (munch_refl [(q - 80, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct ES as (GOT & SHB). destruct LAY as (LG & LC).
    assert (LO' : lo <= q - 64) by lia.
    carve_frame 64%nat ST.
    do 8 zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (ACC1 : accessible m1 B n)
        by (eapply accessible_munch; [exact ACC| exact MU| apply rwin_cwin; [exact WIN| lia] | intros s Hs; cbn [outside]; lia]) end.
    zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
    do 7 zstep. fold_lits. zsimp. do 2 zstep.
    zstep. if_cases K1; zify_cond K1.
    - eapply L1; eassumption.
    - do 7 zstep. fold_lits. zsimp. zstep. if_cases K2; zify_cond K2. 2:{ exfalso; lia. }
      do 6 zstep. fold_lits. if_cases K3; zify_cond K3. { exfalso; unfold rwin in WIN; lia. }
      zstep. if_cases K4; zify_cond K4. { exfalso; unfold rwin in WIN; lia. }
      eapply L1; eassumption.
  Qed.
End Proofs.

Lemma rip_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo B n : Z),
  mem_inv asegs m -> stk asegs m lo q -> lo <= q - 80 -> 0x10007fff8000 <= lo -> q < 2^64 ->
  env_shadow m -> env_layout m ->
  a0 = wz B -> a1 = wz n ->
  rwin B n -> accessible m B n -> 8 <= n <= 2^43 ->
  evt asegs (rip_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_rip) fc None m (seg_rom asegs)).
Proof. intros. eapply rip_body; eassumption. Qed.
