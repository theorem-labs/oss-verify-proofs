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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit IcptKit2 F_rip F_gates F_irt I_printf_front M_sspdefs I_memcmp I_strchr M_twoway_A M_twoway_C.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition A0_strstr_i : Z := 0x4411c.
Definition A0_StrstrCheck : Z := 0x45894.

Definition sck_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q.

Section Check.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (S1 n1 S2 k2 lo : Z).
  Hypothesis LO : lo <= q - 2160 - 80.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Hypothesis WIN1 : cwin S1 n1.
  Hypothesis W21 : S1 + n1 < 2^47.
  Hypothesis NS1 : 1 <= n1 <= 2^43.
  Hypothesis ACC1 : accessible m S1 n1.
  Hypothesis RD1 : sh_readable m S1 n1.
  Hypothesis WIN2 : cwin S2 (k2 + 1).
  Hypothesis W22 : S2 + k2 + 1 < 2^47.
  Hypothesis NS2 : 0 <= k2 /\ k2 + 1 <= 2^43.
  Hypothesis ACC2 : accessible m S2 (k2 + 1).
  Hypothesis RD2 : sh_readable m S2 (k2 + 1).

  Notation APOST := (sck_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  Definition INVX (mc : mem) : Prop :=
    (exists jk, rw_cells asegs mc (q + -2160) [CB 2080 jk; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (q + -2160)
    /\ munch [(lo, q)] m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc.
  Definition INV (mc : mem) : Prop :=
    INVX mc /\ env_shadow mc /\ env_layout mc
    /\ accessible mc S1 n1 /\ sh_readable mc S1 n1 /\ accessible mc S2 (k2 + 1) /\ sh_readable mc S2 (k2 + 1).

  #[using="LO KLO Q64 WIN1 W21 WIN2 W22"] Lemma BL : 0 <= S1 /\ 0 <= S2 /\ S1 + n1 < 2^47 /\ S2 + k2 + 1 < 2^47 /\ 0 <= lo /\ q < 2^64 /\ lo <= q - 2240 /\ 17594333495296 <= lo.
  Proof. destruct WIN1 as [Hn W]. destruct WIN2 as [_ W']. lia. Qed.

  Ltac invx_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1).
  Ltac inv_open H :=
    let IX := fresh "IX" in
    destruct H as (IX & (GOT1 & SHB1) & (LG1 & LC1) & ACCa & RDa & ACCb & RDb); invx_open IX.

  #[using="LO KLO Q64 WIN1 W21 ACC1 RD1 WIN2 W22 ACC2 RD2"] Lemma inv_of : forall mc jk,
    rw_cells asegs mc (q + -2160) [CB 2080 jk; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (q + -2160) -> munch [(lo, q)] m mc -> wmono asegs m mc -> mem_inv asegs mc -> icpt_env mc ->
    INV mc.
  Proof.
    intros mc jk FR ST1 MU1 WM1 MI1 IE1. pose proof BL as BL0.
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia).
    split; [split; [exists jk; exact FR|]; repeat (split; [assumption|]); assumption|].
    split; [exact (ie_shadow _ IE1)|]. split; [exact (ie_layout _ IE1)|].
    split; [eapply accessible_munch; [exact ACC1| exact MU1| exact WIN1| intros s Hs; apply HO; lia]|].
    split; [eapply sh_readable_munch; [exact RD1| exact MU1| exact WIN1| exact HO]|].
    split; [eapply accessible_munch; [exact ACC2| exact MU1| exact WIN2| intros s Hs; apply HO; lia]|].
    eapply sh_readable_munch; [exact RD2| exact MU1| exact WIN2| exact HO].
  Qed.

  Notation KST pc mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 y2 y3 y4 y5 y6 y7 y8 x28 x29 x30 x31 :=
    (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) x9 x10 x11 x12 x13 x14 x15 x16 x17
             y2 y3 y4 y5 y6 y7 y8 s9 s10 s11 x28 x29 x30 x31)
        F (wz pc) fc None mc (seg_rom asegs)) (only parsing).

  #[using="S1 n1 S2 k2 LO KLO Q64 WIN1 W21 WIN2 W22"] Lemma LX : forall mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 y2 y3 y4 y5 y6 y7 y8 x28 x29 x30 x31,
    INVX mc ->
    evt asegs APOST (KST 0x459d0 mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 y2 y3 y4 y5 y6 y7 y8 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. invx_open IV.
    do 13 zstep.
    release_frame FR ST1 q. unfold sck_post. finish.
  Qed.

  #[using="LO KLO Q64 WIN1 W21 ACC1 RD1 WIN2 W22 ACC2 RD2"] Lemma inv_of_cells : forall mc jk,
    rw_cells asegs mc (q + -2160) [CB 2080 jk; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (q + -2160) -> munch [(lo, q)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rw_cells asegs mc 699696 [C8 (Z_to_bv 64 738616)] -> rw_cells asegs mc 738616 [C8 (Z_to_bv 64 2147450880)] ->
    rw_cells asegs mc 699704 [C8 (Z_to_bv 64 741928); C8 (Z_to_bv 64 741936); C8 (Z_to_bv 64 741920)] ->
    rw_cells asegs mc 741920 [C8 (Z_to_bv 64 140737488355327); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    INV mc.
  Proof.
    intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 L1 L2. pose proof BL as BL0.
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia).
    split; [split; [exists jk; exact FR|]; repeat (split; [assumption|]); assumption|].
    split; [split; assumption|]. split; [split; assumption|].
    split; [eapply accessible_munch; [exact ACC1| exact MU1| exact WIN1| intros s Hs; apply HO; lia]|].
    split; [eapply sh_readable_munch; [exact RD1| exact MU1| exact WIN1| exact HO]|].
    split; [eapply accessible_munch; [exact ACC2| exact MU1| exact WIN2| intros s Hs; apply HO; lia]|].
    eapply sh_readable_munch; [exact RD2| exact MU1| exact WIN2| exact HO].
  Qed.

  #[using="LO KLO Q64 WIN1 W21 WIN2 W22"] Lemma LWL2 : forall mc (j : nat) (cur : Z) x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 y4 y5 y6 y7 y8 x28 x29 x30 x31,
    INV mc -> 1 <= k2 + 1 <= 64 ->
    Z.to_nat (sh (S2 + (k2 + 1) - 1) - cur) = j -> sh S2 <= cur < sh (S2 + (k2 + 1) - 1) ->
    evt asegs APOST (KST 0x45bcc mc x1 x5 x6 x7 x9 (wz cur) (wz (2147450880 + Z.shiftr (k2 + S2) 3)) (wz 0) x13 x14 x15 x16 x17 (wz S2) (wz (k2 + S2)) y4 y5 y6 y7 y8 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV N1 Hk Hc. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    revert cur x13 Hk Hc. induction j as [|j IH]; intros cur x13 Hk Hc; [exfalso; lia|].
    assert (SL : sh (S2 + (k2 + 1) - 1) = 2147450880 + Z.shiftr (k2 + S2) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (S2 + (k2 + 1) - 1) with (k2 + S2) by lia; lia).
    pose proof (sh_div8 (S2 + (k2 + 1) - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc S2 (k2 + 1) cur ACCb ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX. exact (proj1 IV0).
  Qed.

  #[using="LO KLO Q64 WIN1 W21 WIN2 W22 NS2"] Lemma LWS2 : forall mc x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 y4 y5 y6 y7 y8 x28 x29 x30 x31,
    INV mc -> 1 <= k2 + 1 <= 64 ->
    evt asegs APOST (KST 0x45bb0 mc x1 x5 x6 x7 x9 (wz (2147450880 + Z.shiftr S2 3)) (wz (2147450880 + Z.shiftr (k2 + S2) 3)) x12 x13 x14 x15 x16 x17 (wz S2) (wz (k2 + S2)) y4 y5 y6 y7 y8 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV N1. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    destruct (acc_byte_rd mc S2 (k2 + 1) (k2 + S2) ACCb ltac:(lia) ltac:(lia) ltac:(lia)) as (kk & RDk & CKk).
    unfold sh, SHADOW_OFF in RDk. rewrite <- shiftr3_div in RDk.
    zstep. rewrite (sxb_small kk) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((k2 + S2) mod 8) kk) by (pose proof (Z.mod_pos_bound (k2 + S2) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX. exact (proj1 IV0).
    - eapply LWL2; [exact IV0 | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (S2 + (k2 + 1) - 1) with (k2 + S2) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= S2 / 8 < 2^44 /\ 0 <= (k2 + S2) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite !Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 WIN1 W21 WIN2 W22 NS2"] Lemma LB2 : forall mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 y4 y5 y6 y7 y8 x28 x29 x30 x31,
    INV mc ->
    evt asegs APOST (KST 0x45984 mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (wz S2) (wz k2) y4 y5 y6 y7 y8 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    zstep. zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
      do 3 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct WIN2 as [_ W]; unfold rwin; lia | exact ACCb | lia |].
      zstep. lit_branch.
      eapply LX. unfold INVX. split; [eexists; eassumption|]. repeat (split; [eassumption|]). assumption.
    - assert (N1 : 1 <= k2 + 1 <= 64) by lia.
      do 10 zstep.
      probe8_regx 12%Z RDb S2 w1 P1. probe8_regx 13%Z RDb (k2 + S2) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS2; eassumption.
      + eapply LX; exact (proj1 IV0).
  Qed.

  #[using="LO KLO Q64 WIN1 W21 WIN2 W22 NS2"] Lemma LWL1 : forall mc (j : nat) (cur : Z) x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 y6 y7 y8 x28 x29 x30 x31,
    INV mc -> 1 <= n1 <= 64 ->
    Z.to_nat (sh (S1 + n1 - 1) - cur) = j -> sh S1 <= cur < sh (S1 + n1 - 1) ->
    evt asegs APOST (KST 0x45b10 mc x1 x5 x6 x7 x9 (wz cur) (wz (2147450880 + Z.shiftr (S1 + n1 + -1) 3)) (wz 0) x13 x14 x15 x16 x17 (wz S2) (wz k2) (wz n1) (wz S1) y6 y7 y8 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV N1 Hk Hc. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    revert cur x13 Hk Hc. induction j as [|j IH]; intros cur x13 Hk Hc; [exfalso; lia|].
    assert (SL : sh (S1 + n1 - 1) = 2147450880 + Z.shiftr (S1 + n1 + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (S1 + n1 + -1) with (S1 + n1 - 1) by lia; lia).
    pose proof (sh_div8 (S1 + n1 - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc S1 n1 cur ACCa ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LB2. exact IV0.
  Qed.

  #[using="LO KLO Q64 WIN1 W21 NS1 WIN2 W22 NS2"] Lemma LWS1 : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 y6 y7 y8 x28 x29 x30 x31,
    INV mc -> 1 <= n1 <= 64 ->
    evt asegs APOST (KST 0x45af4 mc x1 x5 x6 x7 x9 (wz (2147450880 + Z.shiftr S1 3)) (wz (2147450880 + Z.shiftr (S1 + n1 + -1) 3)) (wz (S1 + n1 + -1)) x13 x14 x15 x16 x17 (wz S2) (wz k2) (wz n1) (wz S1) y6 y7 y8 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV N1. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    destruct (acc_byte_rd mc S1 n1 (S1 + n1 + -1) ACCa ltac:(lia) ltac:(lia) ltac:(lia)) as (kk & RDk & CKk).
    unfold sh, SHADOW_OFF in RDk. rewrite <- shiftr3_div in RDk.
    zstep. rewrite (sxb_small kk) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((S1 + n1 + -1) mod 8) kk) by (pose proof (Z.mod_pos_bound (S1 + n1 + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LB2. exact IV0.
    - eapply LWL1; [exact IV0 | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (S1 + n1 - 1) with (S1 + n1 + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= S1 / 8 < 2^44 /\ 0 <= (S1 + n1 + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite !Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 WIN1 W21 NS1 ACC1 RD1 WIN2 W22 NS2 ACC2 RD2"] Lemma LB1 : forall mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 y6 y7 y8 x28 x29 x30 x31,
    INV mc ->
    evt asegs APOST (KST 0x4593c mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (wz S2) (wz k2) (wz n1) (wz S1) y6 y7 y8 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
      assert (N65 : 64 < n1) by (clear - K2 K3 NS1; Z.div_mod_to_equations; lia).
      do 3 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct WIN1 as [_ W]; unfold rwin; lia | exact ACCa | lia |].
      zstep. lit_branch.
      eapply LB2. match goal with P : stk asegs _ lo (q + -2160) |- _ => eapply inv_of_cells; [ eassumption | exact P | eassumption .. ] end.
    - assert (N1 : 1 <= n1 <= 64) by (clear - K2 NS1; Z.div_mod_to_equations; lia).
      do 11 zstep.
      probe8_regx 13%Z RDa S1 w1 P1. probe8_regx 14%Z RDa (S1 + n1 + -1) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS1; eassumption.
      + eapply LB2; exact IV0.
  Qed.
End Check.

Lemma sck_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (H S2 r lo : Z) (hay slack ndl nrest : list byte),
  bytes_at asegs m H (hay ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) hay ->
  bytes_at asegs m S2 (ndl ++ Z_to_bv 8 0 :: nrest) -> ~ In (Z_to_bv 8 0) ndl ->
  (r = 0 \/ (H <= r /\ r + Z.of_nat (length ndl) <= H + Z.of_nat (length hay))) ->
  accessible m H (Z.of_nat (length hay) + 1) -> sh_readable m H (Z.of_nat (length hay) + 1) -> cwin H (Z.of_nat (length hay) + 1) ->
  H + Z.of_nat (length hay) + 1 < 2^47 -> Z.of_nat (length hay) + 1 <= 2^43 ->
  accessible m S2 (Z.of_nat (length ndl) + 1) -> sh_readable m S2 (Z.of_nat (length ndl) + 1) -> cwin S2 (Z.of_nat (length ndl) + 1) ->
  S2 + Z.of_nat (length ndl) + 1 < 2^47 -> Z.of_nat (length ndl) + 1 <= 2^43 -> 1 <= Z.of_nat (length ndl) ->
  icpt_env m -> stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 2240 -> q < 2^64 ->
  (H + Z.of_nat (length hay) + 1 + Z.of_nat (length slack) <= lo \/ q <= H) ->
  (S2 + Z.of_nat (length ndl) + 1 + Z.of_nat (length nrest) <= lo \/ q <= S2) ->
  mem_inv asegs m ->
  evt asegs (sck_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 (wz r) (wz H) (wz S2) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_StrstrCheck) fc None m (seg_rom asegs)).
Proof.
  intros until nrest. intros HAY NONUL NDL NNUL RR ACCH RDH WINH W2H NSH ACCN RDN WINN W2N NSN N1 IE ST KLO LO Q64 SEPH SEPN MI.
  unfold A0_StrstrCheck.
  assert (BL0 : 0 <= H /\ 0 <= S2) by (destruct WINH as [_ W]; destruct WINN as [_ W']; lia).
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 2160%nat ST.
  do 13 zstep. do 5 zstep. zstep.
  lazymatch goal with HAYc : bytes_at asegs ?mm H _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply istrlen_spec with (str := hay) (rest := slack); [ assumption | rewrite unsigned_lit by lia; exact HAYc | apply noz_of_notin; exact NONUL ]
    | post_call asegs mm ] end.
  do 3 zstep.
  lazymatch goal with NDLc : bytes_at asegs ?mm S2 _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply istrlen_spec with (str := ndl) (rest := nrest); [ assumption | rewrite unsigned_lit by lia; exact NDLc | apply noz_of_notin; exact NNUL ]
    | post_call asegs mm ] end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1 end.
  pose proof (ie_cf _ IE1) as CF1. pose proof (ie_flags _ IE1) as FL1. unfold env_cf in CF1. unfold env_flags in FL1.
  do 3 zstep. cbv beta. zsimp. zstep. zstep. if_cases K0; zify_cond K0. 2:{ exfalso. clear - K0. cbv in K0. lia. }
  zstep. if_cases KR; zify_cond KR.
  -
    do 4 zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
    eapply LB1 with (S1 := H) (n1 := Z.of_nat (length hay) + 1) (S2 := S2) (k2 := Z.of_nat (length ndl)) (lo := lo);
      [ lia | exact KLO | exact Q64 | exact WINH | lia | lia | exact ACCH | exact RDH | exact WINN | lia | lia | exact ACCN | exact RDN |].
    eapply inv_of; first [ exact IE1 | eassumption | lia ].
  -
    destruct RR as [R0|[RL RH]]; [exfalso; lia|].
    do 5 zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    assert (SUB : H <= H /\ H + (r - H + Z.of_nat (length ndl)) <= H + (Z.of_nat (length hay) + 1)) by lia.
    eapply LB1 with (S1 := H) (n1 := r - H + Z.of_nat (length ndl)) (S2 := S2) (k2 := Z.of_nat (length ndl)) (lo := lo);
      [ lia | exact KLO | exact Q64 | destruct WINH as [_ WH]; split; lia | lia | lia
      | eapply accessible_sub; [exact ACCH| lia| lia] | eapply sh_readable_sub; [exact RDH| lia| lia| lia]
      | exact WINN | lia | lia | exact ACCN | exact RDN |].
    eapply inv_of; first [ exact IE1 | eassumption | lia
      | destruct WINH as [_ WH]; split; lia | eapply accessible_sub; [exact ACCH| lia| lia] | eapply sh_readable_sub; [exact RDH| lia| lia| lia] ].
Qed.

Lemma chunked_at : forall m, mem_inv asegs m -> bytes_at asegs m NAD chunked_bytes.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold NAD; lia| unfold NAD, chunked_bytes; cbn [length]; lia|].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Definition strstr_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (H : Z) (hay slack : list byte) (canary : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' H (hay ++ Z_to_bv 8 0 :: slack)
    /\ rw_cells asegs m' got_ssp [C8 (wz ssp_guard)]
    /\ rw_cells asegs m' ssp_guard [C8 canary]
    /\ (r = 0 \/ (H <= r /\ r + 7 <= H + Z.of_nat (length hay))).

Lemma strstr_chunked_specZ : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (H : Z) (hay slack : list byte) (canary : word) (lo : Z),
  bytes_at asegs m H (hay ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) hay ->
  (- (H + Z.of_nat (length hay) + 1)) mod 8 <= Z.of_nat (length slack) ->
  rw_cells asegs m got_ssp [C8 (wz ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
  stk asegs m lo q -> lo <= q - 2240 - 2320 ->
  icpt_env m -> 0x10007fff8000 <= lo -> env_real_memcmp m -> env_real_strchr m ->
  accessible m H (Z.of_nat (length hay) + 1) -> sh_readable m H (Z.of_nat (length hay) + 1) -> cwin H (Z.of_nat (length hay) + 1) ->
  H + Z.of_nat (length hay) + 1 < 2^47 -> Z.of_nat (length hay) + 1 <= 2^43 ->
  accessible m NAD 8 -> sh_readable m NAD 8 ->
  (H + Z.of_nat (length hay) + 1 + Z.of_nat (length slack) <= lo \/ q <= H) ->
  0 < H < 2^64 -> 0 <= q < 2^64 -> mem_inv asegs m ->
  evt asegs (strstr_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H hay slack canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz H) (wz NAD) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xa3470) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HAY NONUL PAD GOT GUARD ST LO IE KLO RMC RSC ACCH RDH WINH W2H NSH ACCN RDN SEPH HB QB MI.
  assert (Eh : bv_unsigned (Z_to_bv 64 H) = H) by (apply unsigned_lit; lia).
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply strstr_chunked_spec with (hay := hay) (slack := slack) (canary := canary) (lo := lo);
      rewrite ?Eh, ?Eq; first [ eassumption | reflexivity | apply chunked_at; exact MI | unfold got_ssp, ssp_guard, NAD; lia | lia ]. }
  intros ms' Q. unfold twoway_post in Q. rewrite ?Eh, ?Eq in Q. exact Q.
Qed.

Definition istrstr_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (H : Z) (hay slack : list byte) (canary : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' H (hay ++ Z_to_bv 8 0 :: slack)
    /\ rw_cells asegs m' got_ssp [C8 (wz ssp_guard)]
    /\ rw_cells asegs m' ssp_guard [C8 canary]
    /\ (r = 0 \/ (H <= r /\ r + 7 <= H + Z.of_nat (length hay))).

Lemma strstr_i_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (H : Z) (hay slack : list byte) (canary : word) (lo : Z),
  bytes_at asegs m H (hay ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) hay ->
  (- (H + Z.of_nat (length hay) + 1)) mod 8 <= Z.of_nat (length slack) ->
  rw_cells asegs m got_ssp [C8 (wz ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
  accessible m H (Z.of_nat (length hay) + 1) -> sh_readable m H (Z.of_nat (length hay) + 1) -> cwin H (Z.of_nat (length hay) + 1) ->
  H + Z.of_nat (length hay) + 1 < 2^47 -> Z.of_nat (length hay) + 1 <= 2^43 ->
  accessible m NAD 8 -> sh_readable m NAD 8 ->
  icpt_env m -> env_real_memcmp m -> env_real_strchr m ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 48 - 2240 - 2320 -> q < 2^64 ->
  H + Z.of_nat (length hay) + 1 + Z.of_nat (length slack) <= lo -> 0 < H ->
  mem_inv asegs m -> a0 = wz H -> a1 = wz NAD ->
  evt asegs (istrstr_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H hay slack canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_strstr_i) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HAY NONUL PAD GOT GUARD ACCH RDH WINH W2H NSH ACCN RDN IE RMC RSC ST KLO LO Q64 SEPH HPOS MI -> ->.
  unfold A0_strstr_i. unfold got_ssp, ssp_guard in *.
  pose proof (bytes_at_bound _ _ _ _ HAY) as HB. rewrite length_app in HB. cbn [length] in HB.
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep.
  carve_frame 48%nat ST.
  do 10 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1 end.
  zstep.
  call inited_spec; [assumption | exact (ie_inited _ IE1) |].
  zstep. lit_branch. zstep.
  call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
  clear IE1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
      pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1 end end.
  pose proof (ie_real_lib _ IE1) as (RL1 & _).
  do 6 zstep.
  ihide HAY. ihide GOT. ihide GUARD.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia);
    assert (ACCH1 : accessible mm H (Z.of_nat (length hay) + 1)) by (eapply accessible_munch; [exact ACCH| exact MU| exact WINH| intros s Hs; apply HO; lia]);
    assert (RDH1 : sh_readable mm H (Z.of_nat (length hay) + 1)) by (eapply sh_readable_munch; [exact RDH| exact MU| exact WINH| exact HO]);
    assert (WINN : cwin NAD 8) by (unfold cwin, NAD; lia);
    assert (ACCN1 : accessible mm NAD 8) by (eapply accessible_munch; [exact ACCN| exact MU| exact WINN| intros s Hs; apply HO; unfold NAD in Hs; lia]);
    assert (RDN1 : sh_readable mm NAD 8) by (eapply sh_readable_munch; [exact RDN| exact MU| exact WINN| exact HO]);
    assert (RMC1 : env_real_memcmp mm)
      by (unfold env_real_memcmp in *; eapply env_cell_frame; [exact RMC| exact MU| exact WM| unfold env_band_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]| lia| cbn [cells_size csize Nat.add]; lia]);
    assert (RSC1 : env_real_strchr mm)
      by (unfold env_real_strchr in *; eapply env_cell_frame; [exact RSC| exact MU| exact WM| unfold env_band_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]| lia| cbn [cells_size csize Nat.add]; lia]);
    eapply evt_cut;
    [ eapply strstr_chunked_specZ with (H := H) (hay := hay) (slack := slack) (canary := canary) (lo := lo);
      [ exact HAY | exact NONUL | exact PAD | exact GOT | exact GUARD | eassumption | lia | exact IE1 | exact KLO | exact RMC1 | exact RSC1
      | exact ACCH1 | exact RDH1 | exact WINH | exact W2H | exact NSH | exact ACCN1 | exact RDN1 | left; lia | lia | lia | assumption ]
    | post_call asegs mm ] end.
  clear IE1 ACCH1 RDH1 ACCN1 RDN1 RMC1 RSC1 HAY GOT GUARD RL1.
  unfold got_ssp, ssp_guard in *.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
      pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1 end end.
  pose proof (ie_cf _ IE1) as CF1. pose proof (ie_flags _ IE1) as FL1. unfold env_cf in CF1. unfold env_flags in FL1.
  zstep. zstep.
  lit_branch.
  do 2 zstep. cbv beta. zsimp. zstep. zstep.
  lit_branch.
  do 6 zstep.
  pose proof (chunked_at _ MI) as NEE. unfold chunked_bytes in NEE.
  assert (NNUL : ~ In (Z_to_bv 8 0) [Z_to_bv 8 99; Z_to_bv 8 104; Z_to_bv 8 117; Z_to_bv 8 110; Z_to_bv 8 107; Z_to_bv 8 101; Z_to_bv 8 100]).
  { cbn [In]. intros HIn. repeat (destruct HIn as [E|HIn]; [apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate|]). exact HIn. }
  lazymatch goal with HAYc : bytes_at asegs ?mm H _, MUc : munch [(lo, q)] m ?mm, WMc : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (ACCH1 : accessible mm H (Z.of_nat (length hay) + 1)) by (eapply accessible_munch; [exact ACCH| exact MUc| exact WINH| intros s Hs; apply HO; lia]);
    assert (RDH1 : sh_readable mm H (Z.of_nat (length hay) + 1)) by (eapply sh_readable_munch; [exact RDH| exact MUc| exact WINH| exact HO]);
    assert (ACCN1 : accessible mm NAD 8) by (eapply accessible_munch; [exact ACCN| exact MUc| exact WINN| intros s Hs; apply HO; unfold NAD in Hs; lia]);
    assert (RDN1 : sh_readable mm NAD 8) by (eapply sh_readable_munch; [exact RDN| exact MUc| exact WINN| exact HO]);
    eapply evt_cut;
    [ eapply sck_spec with (H := H) (S2 := NAD) (r := x16) (lo := lo) (hay := hay) (slack := slack)
        (ndl := [Z_to_bv 8 99; Z_to_bv 8 104; Z_to_bv 8 117; Z_to_bv 8 110; Z_to_bv 8 107; Z_to_bv 8 101; Z_to_bv 8 100]) (nrest := []);
      [ exact HAYc | exact NONUL | exact NEE | exact NNUL | cbn [length]; lia
      | exact ACCH1 | exact RDH1 | exact WINH | exact W2H | exact NSH
      | exact ACCN1 | exact RDN1 | exact WINN | unfold NAD; cbn [length]; lia | cbn [length]; lia | cbn [length]; lia
      | exact IE1 | eassumption | exact KLO | lia | lia | left; lia | left; unfold NAD; cbn [length]; lia | assumption ]
    | post_call asegs mm ] end.
  clear IE1 CF1 FL1 ACCH1 RDH1 ACCN1 RDN1.
  do 6 zstep.
  do 9 zstep.
  lazymatch goal with P : stk asegs _ lo (q + -48) |- _ => release_frame FR P q end.
  unfold istrstr_post, got_ssp, ssp_guard. finish.
Qed.
