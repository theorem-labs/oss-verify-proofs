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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit.
Import ListNotations.
Open Scope Z_scope.

Definition A0_mem_is_zero : Z := 0x69efc.
Definition miz_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 16, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q.

Section Proofs.
  Variables (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo B n : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo q.
  Hypothesis LO : lo <= q - 16.
  Hypothesis Q64 : q < 2^64.
  Hypothesis ZR : zrun m B (B + n).
  Hypothesis BB : 0 <= B /\ 0 <= n <= 2^40 /\ B + n <= lo.

  Notation ZPOST := (miz_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  Section Loops.
    Variables (m1 : mem) (junk8 : list byte).
    Hypothesis FR : rw_cells asegs m1 (q + -16) [CB 8 junk8; C8 ra].
    Hypothesis ST1 : stk asegs m1 lo (q + -16).
    Hypothesis MU1 : munch [(q + -16, q)] m m1.
    Hypothesis WM1 : wmono asegs m m1.
    Hypothesis MI1 : mem_inv asegs m1.
    Hypothesis ZR1 : zrun m1 B (B + n).
    Variables (AB AE : Z).
    Hypothesis RAB : B <= AB <= B + 7 /\ AB mod 8 = 0.
    Hypothesis RAE : B + n - 7 <= AE <= B + n /\ AE mod 8 = 0.
    Hypothesis LO0 : 0 <= lo.

    Notation AT pc x10 x11 x12 x13 x14 x15 x16 :=
      (MS (mkR ra (wz (q + -16)) gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz pc) fc None m1 (seg_rom asegs)).

    #[using="LO junk8 FR ST1 MU1 WM1 MI1 AB AE"] Lemma L_ret : forall x10 x12 x13 x14 x15 x16,
      evt asegs ZPOST (AT 0x69f88 x10 (wz 0) x12 x13 x14 x15 x16).
    Proof.
      intros.
      zstep. fold_lits. zstep. zstep. zstep. fold_lits.
      release_frame FR ST1 q. finish.
    Qed.

    #[using="LO Q64 BB junk8 FR ST1 MU1 WM1 MI1 ZR1 AB AE RAB RAE"] Lemma L_epi : forall (k : nat) (c : Z) x10 x13 x15 x16,
      Z.to_nat (B + n - c) = k -> B <= c < B + n ->
      evt asegs ZPOST (AT 0x69f74 x10 (wz 0) (wz c) x13 (wz (B + n - c)) x15 x16).
    Proof.
      induction k as [|k IH]; intros c x10 x13 x15 x16 Hk Hc; [exfalso; lia|].
      pose proof (ov_read1_mrd m1 c _ ltac:(lia) ltac:(lia) (ZR1 c Hc)) as RD.
      zstep.
      cbv beta. zsimp. zstep. zstep. fold_lits.
      zstep. zstep.
      if_cases K; zify_cond K.
      - replace (B + n - c + -1) with (B + n - (c + 1)) by lia. apply IH; lia.
      - apply L_ret.
    Qed.

    #[using="LO Q64 BB junk8 FR ST1 MU1 WM1 MI1 ZR1 AB RAB RAE"] Lemma L_tail : forall x10 x13 x15 x16, x10 = wz B ->
      evt asegs ZPOST (AT 0x69f68 x10 (wz 0) (wz AE) x13 (wz (B + n)) x15 x16).
    Proof.
      intros x10 x13 x15 x16 ->.
      zstep. if_cases K1; zify_cond K1. { apply L_ret. }
      zstep. if_cases K2; zify_cond K2. { apply L_ret. }
      zstep.
      apply (L_epi (Z.to_nat (B + n - AE)) AE); lia.
    Qed.

    #[using="LO Q64 BB junk8 FR ST1 MU1 WM1 MI1 ZR1 RAB RAE"] Lemma L_word : forall (k : nat) (c : Z) x13 x16,
      Z.to_nat (AE - c) = k -> AB <= c < AE -> c mod 8 = 0 ->
      evt asegs ZPOST (AT 0x69f58 (wz B) (wz 0) (wz AE) x13 (wz (B + n)) (wz c) x16).
    Proof.
      intros k. induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf). intros c x13 x16 Hk Hc Hal.
      assert (C8 : c + 8 <= AE) by (Z.div_mod_to_equations; lia).
      pose proof (ov_read8_zrun m1 c ltac:(lia) ltac:(lia) (zrun_sub m1 _ _ c (c + 8) ZR1 ltac:(lia) ltac:(lia))) as RD.
      zstep. zstep. zstep. fold_lits. zstep.
      if_cases K; zify_cond K.
      - apply (IH (Z.to_nat (AE - (c + 8)))); try lia; Z.div_mod_to_equations; lia.
      - replace (Z_to_bv 64 (c + 8)) with (Z_to_bv 64 AE) by (f_equal; lia). apply L_tail. reflexivity.
    Qed.

    #[using="LO Q64 BB junk8 FR ST1 MU1 WM1 MI1 ZR1 RAB RAE"] Lemma L_mid : forall x13 x16,
      evt asegs ZPOST (AT 0x69f54 (wz B) (wz 0) (wz AE) x13 (wz (B + n)) (wz AB) x16).
    Proof.
      intros. zstep. if_cases K; zify_cond K. { apply L_tail. reflexivity. }
      apply (L_word (Z.to_nat (AE - AB)) AB); lia.
    Qed.

    #[using="LO Q64 BB junk8 FR ST1 MU1 WM1 MI1 ZR1 RAB RAE"] Lemma L_pro : forall (k : nat) (c : Z) x16,
      Z.to_nat (AB - c) = k -> B <= c < AB -> c < B + n ->
      evt asegs ZPOST (AT 0x69f3c (wz B) (wz 0) (wz AE) (wz (c + 1)) (wz (B + n)) (wz AB) x16).
    Proof.
      induction k as [|k IH]; intros c x16 Hk Hc HcE; [exfalso; lia|].
      pose proof (ov_read1_mrd m1 c _ ltac:(lia) ltac:(lia) (ZR1 c ltac:(lia))) as RD.
      zstep. zstep. cbv beta. zsimp. zstep. fold_lits. zstep.
      if_cases K1; zify_cond K1. { apply L_mid. }
      zstep. zstep.
      if_cases K2; zify_cond K2.
      - replace (c + 2) with ((c + 1) + 1) by lia. apply IH; lia.
      - apply L_mid.
    Qed.
  End Loops.

  #[using="MI ST LO Q64 ZR BB"] Lemma miz_body : forall a0 a1 a2 a3 a4 a5 a6, a0 = wz B -> a1 = wz n ->
    evt asegs ZPOST (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz A0_mem_is_zero) fc None m (seg_rom asegs)).
  Proof.
    intros a0 a1 a2 a3 a4 a5 a6 -> ->. unfold A0_mem_is_zero.
    pose proof (munch_refl [(q - 16, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    carve_frame 16%nat ST.
    zstep. zstep.
    assert (ZR1 : zrun m0 B (B + n)).
    { eapply zrun_munch; [exact ZR| exact MU| lia| lia|]. intros a Ha. cbn [outside]. lia. }
    do 5 zstep.
    if_cases K; zify_cond K. { exfalso. lia. }
    do 5 zstep.
    change 18446744073709551608 with (2^64 - 2^3). rewrite !land_align_down by lia.
    remember (B + 7 - (B + 7) mod 2 ^ 3) as AB eqn:HAB.
    remember (B + n - (B + n) mod 2 ^ 3) as AE eqn:HAE.
    assert (RAB : B <= AB <= B + 7 /\ AB mod 8 = 0) by (subst AB; Z.div_mod_to_equations; lia).
    assert (RAE : B + n - 7 <= AE <= B + n /\ AE mod 8 = 0) by (subst AE; Z.div_mod_to_equations; lia).
    clear HAB HAE.
    zstep. if_cases K1; zify_cond K1.
    { eapply L_mid; eassumption. }
    zstep. if_cases K2; zify_cond K2.
    { eapply L_mid; eassumption. }
    zstep. zstep.
    eapply (L_pro m0) with (c := B); try eassumption; [reflexivity | lia | lia].
  Qed.
End Proofs.

Lemma miz_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo B n : Z),
  mem_inv asegs m -> stk asegs m lo q -> lo <= q - 16 -> q < 2^64 ->
  zrun m B (B + n) -> 0 <= B -> 0 <= n <= 2^40 -> B + n <= lo ->
  a0 = wz B -> a1 = wz n ->
  evt asegs (miz_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_mem_is_zero) fc None m (seg_rom asegs)).
Proof. intros. eapply miz_body; try eassumption. lia. Qed.
