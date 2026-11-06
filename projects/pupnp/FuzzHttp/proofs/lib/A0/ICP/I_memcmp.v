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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit IcptKit2 F_rip F_gates M_memcmpZ.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition A0_memcmp_i : Z := 0x4413c.
Definition A0_memcmp_common : Z := 0x45fe0.

Definition env_real_memcmp (m : mem) : Prop := rw_cells asegs m 0xabe18 [C8 (wz 0xa1de8)].

Definition imemcmp_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A B : Z) (ls rs : list byte) (v lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' A ls /\ bytes_at asegs m' B rs.

Section Common.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (A B n lo v : Z) (ls rs : list byte).
  Hypothesis LO : lo <= q - 2192 - 80.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Hypothesis MODEL : memcmp_model ls rs (Z.to_nat n) = Some v.
  Hypothesis SEPA : A + Z.of_nat (length ls) <= lo \/ q <= A.
  Hypothesis SEPB : B + Z.of_nat (length rs) <= lo \/ q <= B.
  Hypothesis WINA : cwin A n.
  Hypothesis WINB : cwin B n.
  Hypothesis WIN2 : A + n < 2^47 /\ B + n < 2^47.
  Hypothesis NSZ : n <= 2^43.
  Hypothesis ACCA : accessible m A n.
  Hypothesis RDA : sh_readable m A n.
  Hypothesis ACCB : accessible m B n.
  Hypothesis RDB : sh_readable m B n.

  Notation APOST := (imemcmp_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A B ls rs v lo m).

  Definition INVX (mc : mem) : Prop :=
    (exists jk, rw_cells asegs mc (q + -2192) [CB 2088 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (q + -2192)
    /\ munch [(lo, q)] m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ bytes_at asegs mc A ls /\ bytes_at asegs mc B rs.
  Definition INV (mc : mem) : Prop :=
    INVX mc /\ env_shadow mc /\ env_layout mc
    /\ accessible mc A n /\ sh_readable mc A n /\ accessible mc B n /\ sh_readable mc B n.

  #[using="ls rs LO KLO Q64 WINA WINB WIN2"] Lemma BL : 0 <= A /\ 0 <= B /\ 0 <= n /\ A + n < 2^47 /\ B + n < 2^47 /\ 0 <= lo /\ q < 2^64 /\ lo <= q - 2272 /\ 17594333495296 <= lo.
  Proof. destruct WINA as [Hn W]. destruct WINB as [_ W']. lia. Qed.

  Ltac invx_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & LS1 & RS1).
  Ltac inv_open H :=
    let IX := fresh "IX" in
    destruct H as (IX & (GOT1 & SHB1) & (LG1 & LC1) & ACCA1 & RDA1 & ACCB1 & RDB1); invx_open IX.

  #[using="LO KLO Q64 WINA WINB WIN2 ACCA RDA ACCB RDB"] Lemma inv_of : forall mc jk,
    rw_cells asegs mc (q + -2192) [CB 2088 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (q + -2192) -> munch [(lo, q)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rw_cells asegs mc 696528 [C8 (Z_to_bv 64 735480)] -> rw_cells asegs mc 735480 [C8 (Z_to_bv 64 2147450880)] ->
    rw_cells asegs mc 696536 [C8 (Z_to_bv 64 738792); C8 (Z_to_bv 64 738800); C8 (Z_to_bv 64 738784)] ->
    rw_cells asegs mc 738784 [C8 (Z_to_bv 64 140737488355327); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    bytes_at asegs mc A ls -> bytes_at asegs mc B rs ->
    INV mc.
  Proof.
    intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 L1 L2 LS1 RS1. pose proof BL as BL0.
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia).
    split; [split; [exists jk; exact FR|]; repeat (split; [assumption|]); assumption|].
    split; [split; assumption|]. split; [split; assumption|].
    split; [eapply accessible_munch; [exact ACCA| exact MU1| exact WINA| intros s Hs; apply HO; lia]|].
    split; [eapply sh_readable_munch; [exact RDA| exact MU1| exact WINA| exact HO]|].
    split; [eapply accessible_munch; [exact ACCB| exact MU1| exact WINB| intros s Hs; apply HO; lia]|].
    eapply sh_readable_munch; [exact RDB| exact MU1| exact WINB| exact HO].
  Qed.

  Notation CST pc mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y6 y9 y10 y11 x28 x29 x30 x31 :=
    (MS (mkR x1 (wz (q + -2192)) gp tp x5 x6 x7 (wz q) (wz n) x10 x11 x12 x13 x14 x15 x16 x17
             (wz B) ra (wz A) (wz 0xa1de8) y6 (wz (q + -2176)) (wz 0x145428) y9 y10 y11 x28 x29 x30 x31)
        F (wz pc) fc None mc (seg_rom asegs)) (only parsing).

  #[using="LO KLO Q64 MODEL WINA WINB WIN2 NSZ"] Lemma LX : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y6 y9 y10 y11 x28 x29 x30 x31,
    INVX mc ->
    evt asegs APOST (CST 0x460f0 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y6 y9 y10 y11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. invx_open IV.
    zstep. zstep. zstep. zstep.
    call memcmp_specZ; [ exact LS1 | exact RS1 | exact MODEL | exact MI1 | lia | lia | lia |].
    do 2 zstep. do 5 zstep. zstep. zstep.
    do 16 zstep.
    zstep.
    release_frame FR ST1 q. finish.
  Qed.

  #[using="LO KLO Q64 MODEL WINA WINB WIN2 NSZ"] Lemma LWLb : forall mc (k : nat) (cur : Z) x1 x5 x6 x7 x10 x14 x15 x16 x17 y6 y10 y11 x28 x29 x30 x31,
    INV mc -> 1 <= n <= 64 ->
    Z.to_nat (sh (B + n - 1) - cur) = k -> sh B <= cur < sh (B + n - 1) ->
    evt asegs APOST (CST 0x46568 mc x1 x5 x6 x7 x10 (wz cur) (wz (2147450880 + Z.shiftr (B + n + -1) 3)) (wz 0) x14 x15 x16 x17 y6 (wz (n + -65)) y10 y11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV N1 Hk Hc. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    revert cur x14 Hk Hc. induction k as [|k IH]; intros cur x14 Hk Hc; [exfalso; lia|].
    assert (SL : sh (B + n - 1) = 2147450880 + Z.shiftr (B + n + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (B + n + -1) with (B + n - 1) by lia; lia).
    pose proof (sh_div8 (B + n - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc B n cur ACCB1 ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX. exact (proj1 IV0).
  Qed.

  #[using="LO KLO Q64 MODEL WINA WINB WIN2 NSZ"] Lemma LWSb : forall mc x1 x5 x6 x7 x10 x14 x15 x16 x17 y6 y10 y11 x28 x29 x30 x31,
    INV mc -> 1 <= n <= 64 ->
    evt asegs APOST (CST 0x4654c mc x1 x5 x6 x7 x10 (wz (2147450880 + Z.shiftr B 3)) (wz (2147450880 + Z.shiftr (B + n + -1) 3)) (wz (B + n + -1)) x14 x15 x16 x17 y6 (wz (n + -65)) y10 y11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV N1. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    destruct (acc_byte_rd mc B n (B + n + -1) ACCB1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((B + n + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (B + n + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX. exact (proj1 IV0).
    - eapply LWLb; [exact IV0 | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (B + n - 1) with (B + n + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= B / 8 < 2^44 /\ 0 <= (B + n + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite !Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 MODEL SEPA SEPB WINA WINB WIN2 NSZ"] Lemma LBb : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y6 y10 y11 x28 x29 x30 x31,
    INV mc ->
    evt asegs APOST (CST 0x460a4 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y6 (wz (n + -65)) y10 y11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LX; exact (proj1 IV0). }
      assert (N65 : 64 < n) by (clear - K2 K3 BL0; Z.div_mod_to_equations; lia).
      do 4 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct WINB as [_ W]; unfold rwin; lia | exact ACCB1 | lia |].
      do 2 zstep. lit_branch.
      eapply LX. unfold INVX. split; [eexists; eassumption|]. repeat (split; [eassumption|]). assumption.
    -
      assert (N1 : 1 <= n <= 64) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      probe8_regx 14%Z RDB1 B w1 P1. probe8_regx 15%Z RDB1 (B + n + -1) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWSb; eassumption.
      + eapply LX; exact (proj1 IV0).
  Qed.

  #[using="LO KLO Q64 MODEL SEPA SEPB WINA WINB WIN2 NSZ"] Lemma LWLa : forall mc (k : nat) (cur : Z) x1 x5 x6 x7 x10 x14 x15 x16 x17 y6 y10 y11 x28 x29 x30 x31,
    INV mc -> 1 <= n <= 64 ->
    Z.to_nat (sh (A + n - 1) - cur) = k -> sh A <= cur < sh (A + n - 1) ->
    evt asegs APOST (CST 0x4645c mc x1 x5 x6 x7 x10 (wz cur) (wz (2147450880 + Z.shiftr (A + n + -1) 3)) (wz 0) x14 x15 x16 x17 y6 (wz (n + -65)) y10 y11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV N1 Hk Hc. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    revert cur x14 Hk Hc. induction k as [|k IH]; intros cur x14 Hk Hc; [exfalso; lia|].
    assert (SL : sh (A + n - 1) = 2147450880 + Z.shiftr (A + n + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (A + n + -1) with (A + n - 1) by lia; lia).
    pose proof (sh_div8 (A + n - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc A n cur ACCA1 ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LBb. exact IV0.
  Qed.

  #[using="LO KLO Q64 MODEL SEPA SEPB WINA WINB WIN2 NSZ"] Lemma LWSa : forall mc x1 x5 x6 x7 x10 x14 x15 x16 x17 y6 y10 y11 x28 x29 x30 x31,
    INV mc -> 1 <= n <= 64 ->
    evt asegs APOST (CST 0x46440 mc x1 x5 x6 x7 x10 (wz (2147450880 + Z.shiftr A 3)) (wz (2147450880 + Z.shiftr (A + n + -1) 3)) (wz (A + n + -1)) x14 x15 x16 x17 y6 (wz (n + -65)) y10 y11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV N1. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    destruct (acc_byte_rd mc A n (A + n + -1) ACCA1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((A + n + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (A + n + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LBb. exact IV0.
    - eapply LWLa; [exact IV0 | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (A + n - 1) with (A + n + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= A / 8 < 2^44 /\ 0 <= (A + n + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite !Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 MODEL SEPA SEPB WINA WINB WIN2 NSZ ACCA RDA ACCB RDB"] Lemma LBa : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y6 y9 y10 y11 x28 x29 x30 x31,
    INV mc ->
    evt asegs APOST (CST 0x46054 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y6 y9 y10 y11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LBb; exact IV0. }
      assert (N65 : 64 < n) by (clear - K2 K3 BL0; Z.div_mod_to_equations; lia).
      do 4 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct WINA as [_ W]; unfold rwin; lia | exact ACCA1 | lia |].
      do 3 zstep. lit_branch.
      eapply LBb. match goal with P : stk asegs _ lo (q + -2192) |- _ => eapply inv_of; [ eassumption | exact P | eassumption .. ] end.
    -
      assert (N1 : 1 <= n <= 64) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      probe8_regx 14%Z RDA1 A w1 P1. probe8_regx 15%Z RDA1 (A + n + -1) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWSa; eassumption.
      + eapply LBb; exact IV0.
  Qed.

  #[using="LO KLO Q64 MODEL SEPA SEPB WINA WINB WIN2 NSZ ACCA RDA ACCB RDB"] Lemma common_body : forall t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6,
    mem_inv asegs m -> stk asegs m lo q -> icpt_env m -> bytes_at asegs m A ls -> bytes_at asegs m B rs ->
    evt asegs APOST (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 (wz 0xa1de8) (wz A) (wz B) (wz n) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz A0_memcmp_common) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros MI ST IE LS RS. unfold A0_memcmp_common. pose proof BL as BL0.
    pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO' : lo <= q - 2192) by lia.
    pose proof LS as LS0. ihide LS0. pose proof RS as RS0. ihide RS0. clear LS RS.
    carve_frame 2192%nat ST.
    do 14 zstep. do 7 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1;
      assert (LS1 : bytes_at asegs m1 A ls)
        by (iunhide LS0; eapply bytes_at_transport; [exact LS0| exact MU| cbn [disjoint_from]; lia]);
      assert (RS1 : bytes_at asegs m1 B rs)
        by (iunhide RS0; eapply bytes_at_transport; [exact RS0| exact MU| cbn [disjoint_from]; lia])
    end.
    pose proof (ie_cf _ IE1) as CF1. pose proof (ie_flags _ IE1) as FL1. unfold env_cf in CF1. unfold env_flags in FL1.
    do 3 zstep.
    cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    zstep. cbv beta. zsimp. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1. cbv in K1. lia. }
    eapply LBa.
    eapply inv_of; try eassumption; first [ exact (proj1 (ie_shadow _ IE1)) | exact (proj2 (ie_shadow _ IE1))
        | exact (proj1 (ie_layout _ IE1)) | exact (proj2 (ie_layout _ IE1)) ].
  Qed.
End Common.

Lemma memcmp_i_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A B n lo v : Z) (ls rs : list byte),
  bytes_at asegs m A ls -> bytes_at asegs m B rs -> memcmp_model ls rs (Z.to_nat n) = Some v ->
  accessible m A n -> sh_readable m A n -> accessible m B n -> sh_readable m B n ->
  icpt_env m -> env_real_memcmp m -> cwin A n -> cwin B n -> A + n < 2^47 /\ B + n < 2^47 -> n <= 2^43 ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 2320 -> q < 2^64 ->
  (A + Z.of_nat (length ls) <= lo \/ q <= A) -> (B + Z.of_nat (length rs) <= lo \/ q <= B) ->
  mem_inv asegs m -> a0 = wz A -> a1 = wz B -> a2 = wz n ->
  evt asegs (imemcmp_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A B ls rs v lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_memcmp_i) fc None m (seg_rom asegs)).
Proof.
  intros until rs. intros LS RS MODEL ACCA RDA ACCB RDB IE RMC WINA WINB WIN2 NSZ ST KLO LO Q64 SEPA SEPB MI -> -> ->.
  unfold A0_memcmp_i. unfold env_real_memcmp in RMC.
  assert (BL0 : 0 <= A /\ 0 <= B /\ 0 <= n) by (destruct WINA as [Hn W]; destruct WINB as [_ W']; lia).
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof LS as LS0. ihide LS0. pose proof RS as RS0. ihide RS0. clear LS RS.
  zstep.
  carve_frame 48%nat ST.
  do 8 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1 end.
  zstep.
  call inited_spec; [assumption | exact (ie_inited _ IE1) |].
  zstep. lit_branch. zstep. zstep. zstep. fix_lit_store.
  zstep.
  clear IE1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1 end.
  call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
  clear IE1.
  do 2 zstep. zstep. lit_branch. do 5 zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (icpt_env_stack lo q m mm IE MU WM ltac:(lia)) as IE1;
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia);
    assert (ACCA1 : accessible mm A n) by (eapply accessible_munch; [exact ACCA| exact MU| exact WINA| intros s Hs; apply HO; lia]);
    assert (RDA1 : sh_readable mm A n) by (eapply sh_readable_munch; [exact RDA| exact MU| exact WINA| exact HO]);
    assert (ACCB1 : accessible mm B n) by (eapply accessible_munch; [exact ACCB| exact MU| exact WINB| intros s Hs; apply HO; lia]);
    assert (RDB1 : sh_readable mm B n) by (eapply sh_readable_munch; [exact RDB| exact MU| exact WINB| exact HO]);
    assert (LS1 : bytes_at asegs mm A ls) by (iunhide LS0; eapply bytes_at_transport; [exact LS0| exact MU| cbn [disjoint_from]; lia]);
    assert (RS1 : bytes_at asegs mm B rs) by (iunhide RS0; eapply bytes_at_transport; [exact RS0| exact MU| cbn [disjoint_from]; lia]);
    eapply evt_cut;
    [ eapply common_body with (lo := lo) (A := A) (B := B) (n := n) (v := v) (ls := ls) (rs := rs);
      [ lia | exact KLO | lia | exact MODEL | lia | lia | exact WINA | exact WINB | exact WIN2 | exact NSZ
      | exact ACCA1 | exact RDA1 | exact ACCB1 | exact RDB1 | eassumption | eassumption | exact IE1 | exact LS1 | exact RS1 ]
    | post_call asegs mm ] end.
  do 6 zstep.
  release_frame FR PC q. unfold imemcmp_post. finish.
Qed.
