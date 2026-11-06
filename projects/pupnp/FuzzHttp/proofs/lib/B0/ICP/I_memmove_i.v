(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit F_rip F_imemmove.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition A0_memmove_i : Z := 0x56a8c.

Definition memmove_i_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S n U lo : Z) (us : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + n); (lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ u8arr asegs m' U (upd_bytes us (Z.to_nat (D - U)) (firstn (Z.to_nat n) (skipn (Z.to_nat (S - U)) us))).

Section Proofs.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S n U lo : Z) (us : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo q.
  Hypothesis LO : lo <= q - 2144 - 80.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Hypothesis IE : icpt_env m.
  Hypothesis ARR : u8arr asegs m U us.
  Hypothesis HS : U <= S /\ S + n <= U + Z.of_nat (length us).
  Hypothesis HD : U <= D /\ D + n <= U + Z.of_nat (length us).
  Hypothesis ULO : U + Z.of_nat (length us) <= lo \/ q <= U.
  Hypothesis WIND : cwin D n.
  Hypothesis WINS : cwin S n.
  Hypothesis WIN2 : D + n < 2^47 /\ S + n < 2^47.
  Hypothesis ACCD : accessible m D n.
  Hypothesis RDD : sh_readable m D n.
  Hypothesis ACCS : accessible m S n.
  Hypothesis RDS : sh_readable m S n.
  Hypothesis NSZ : n <= 2^43.

  Notation APOST := (memmove_i_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n U lo us m).

  Definition INVX (mc : mem) : Prop :=
    (exists jk, rw_cells asegs mc (q + -2144) [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (q + -2144)
    /\ munch [(lo, q)] m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ u8arr asegs mc U us.
  Definition INV (mc : mem) : Prop :=
    INVX mc /\ env_shadow mc /\ env_layout mc
    /\ accessible mc D n /\ sh_readable mc D n /\ accessible mc S n /\ sh_readable mc S n.

  #[using="m us LO KLO Q64 ARR HS HD WIND WINS WIN2"] Lemma BL : 0 <= D /\ 0 <= S /\ 0 <= n /\ D + n < 2^47 /\ S + n < 2^47 /\ 0 <= lo /\ q < 2^64 /\ lo <= q - 2224 /\ 17594333495296 <= lo /\ 0 <= U.
  Proof. destruct WIND as [Hn W]. destruct WINS as [_ W']. pose proof (u8arr_bound _ _ _ _ ARR). lia. Qed.

  Ltac invx_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & ARR1).
  Ltac inv_open H :=
    let IX := fresh "IX" in
    destruct H as (IX & (GOT1 & SHB1) & (LG1 & LC1) & ACCD1 & RDD1 & ACCS1 & RDS1); invx_open IX.

  #[using="LO KLO Q64 ARR HS HD WIND WINS WIN2 ACCD RDD ACCS RDS"] Lemma inv_of : forall mc jk,
    rw_cells asegs mc (q + -2144) [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (q + -2144) -> munch [(lo, q)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rw_cells asegs mc 699696 [C8 (Z_to_bv 64 738616)] -> rw_cells asegs mc 738616 [C8 (Z_to_bv 64 2147450880)] ->
    rw_cells asegs mc 699704 [C8 (Z_to_bv 64 741928); C8 (Z_to_bv 64 741936); C8 (Z_to_bv 64 741920)] ->
    rw_cells asegs mc 741920 [C8 (Z_to_bv 64 140737488355327); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    u8arr asegs mc U us ->
    INV mc.
  Proof.
    intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 L1 L2 ARR1. pose proof BL as BL0.
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia).
    split; [split; [exists jk; exact FR|]; repeat (split; [assumption|]); assumption|].
    split; [split; assumption|]. split; [split; assumption|].
    split; [eapply accessible_munch; [exact ACCD| exact MU1| exact WIND| intros s Hs; apply HO; lia]|].
    split; [eapply sh_readable_munch; [exact RDD| exact MU1| exact WIND| exact HO]|].
    split; [eapply accessible_munch; [exact ACCS| exact MU1| exact WINS| intros s Hs; apply HO; lia]|].
    eapply sh_readable_munch; [exact RDS| exact MU1| exact WINS| exact HO].
  Qed.

  #[using="LO KLO Q64 ARR HS HD ULO WIND WINS WIN2 NSZ"] Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INVX mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 (wz D) (wz S) (wz n) x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x578b4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. invx_open IV.
    apply (munch_weaken _ [(D, D + n); (lo, q)]) in MU1; [| unfold sub_fp; cbn [outside]; intros; lia].
    zstep.
    call imemmove_specZ; [ exact ARR1 | exact MI1 | exact HS | exact HD | lia | lia |].
    do 12 zstep.
    release_frame FR ST1 q. finish.
  Qed.

  #[using="LO KLO Q64 ARR HS HD ULO WIND WINS WIN2 NSZ"] Lemma LWLd : forall mc (k : nat) (cur : Z) x1 x5 x6 x7 x9 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc -> 1 <= n <= 64 ->
    Z.to_nat (sh (D + n - 1) - cur) = k -> sh D <= cur < sh (D + n - 1) ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 (wz D) (wz S) (wz n)
               (wz cur) (wz (2147450880 + Z.shiftr (D + n + -1) 3)) (wz 0) x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x57b20) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    revert cur x16 Hk Hc. induction k as [|k IH]; intros cur x16 Hk Hc; [exfalso; lia|].
    assert (SL : sh (D + n - 1) = 2147450880 + Z.shiftr (D + n + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (D + n + -1) with (D + n - 1) by lia; lia).
    pose proof (sh_div8 (D + n - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc D n cur ACCD1 ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX. exact (proj1 IV0).
  Qed.

  #[using="LO KLO Q64 ARR HS HD ULO WIND WINS WIN2 NSZ"] Lemma LWSd : forall mc x1 x5 x6 x7 x9 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc -> 1 <= n <= 64 ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 (wz D) (wz S) (wz n)
               (wz (2147450880 + Z.shiftr D 3)) (wz (2147450880 + Z.shiftr (D + n + -1) 3)) (wz (D + n + -1)) x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x57b04) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    destruct (acc_byte_rd mc D n (D + n + -1) ACCD1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((D + n + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (D + n + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX. exact (proj1 IV0).
    - eapply LWLd; [exact IV0 | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (D + n - 1) with (D + n + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= D / 8 < 2^44 /\ 0 <= (D + n + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite !Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 ARR HS HD ULO WIND WINS WIN2 NSZ"] Lemma LBd : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 (wz D) (wz S) (wz n) x13 x14 x15 x16 x17
               x18 x19 (wz (n + -65)) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x57868) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LX; exact (proj1 IV0). }
      assert (N65 : 64 < n) by (clear - K2 K3 BL0; Z.div_mod_to_equations; lia).
      do 5 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct WIND as [_ W]; unfold rwin; lia | exact ACCD1 | lia |].
      do 5 zstep. lit_branch.
      eapply LX. unfold INVX. split; [eexists; eassumption|]. repeat (split; [eassumption|]). assumption.
    -
      assert (N1 : 1 <= n <= 64) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      probe8_reg 16%Z RDD1 D w1 P1. probe8_reg 17%Z RDD1 (D + n + -1) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWSd; eassumption.
      + eapply LX; exact (proj1 IV0).
  Qed.

  #[using="LO KLO Q64 ARR HS HD ULO WIND WINS WIN2 NSZ"] Lemma LWLs : forall mc (k : nat) (cur : Z) x1 x5 x6 x7 x9 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31,
    INV mc -> 1 <= n <= 64 ->
    Z.to_nat (sh (S + n - 1) - cur) = k -> sh S <= cur < sh (S + n - 1) ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 (wz D) (wz S) (wz n)
               (wz cur) (wz (2147450880 + Z.shiftr (S + n + -1) 3)) (wz 0) x16 x17
               x18 x19 (wz (n + -65)) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x57a20) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    revert cur x16 Hk Hc. induction k as [|k IH]; intros cur x16 Hk Hc; [exfalso; lia|].
    assert (SL : sh (S + n - 1) = 2147450880 + Z.shiftr (S + n + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (S + n + -1) with (S + n - 1) by lia; lia).
    pose proof (sh_div8 (S + n - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc S n cur ACCS1 ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LBd. exact IV0.
  Qed.

  #[using="LO KLO Q64 ARR HS HD ULO WIND WINS WIN2 NSZ"] Lemma LWSs : forall mc x1 x5 x6 x7 x9 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31,
    INV mc -> 1 <= n <= 64 ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 (wz D) (wz S) (wz n)
               (wz (2147450880 + Z.shiftr S 3)) (wz (2147450880 + Z.shiftr (S + n + -1) 3)) (wz (S + n + -1)) x16 x17
               x18 x19 (wz (n + -65)) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x57a04) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    destruct (acc_byte_rd mc S n (S + n + -1) ACCS1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((S + n + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (S + n + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LBd. exact IV0.
    - eapply LWLs; [exact IV0 | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (S + n - 1) with (S + n + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= S / 8 < 2^44 /\ 0 <= (S + n + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite !Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 ARR HS HD ULO WIND WINS WIN2 ACCD RDD ACCS RDS NSZ"] Lemma LBs : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 (wz D) (wz S) (wz n) x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x57820) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LBd; exact IV0. }
      assert (N65 : 64 < n) by (clear - K2 K3 BL0; Z.div_mod_to_equations; lia).
      do 6 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct WINS as [_ W]; unfold rwin; lia | exact ACCS1 | lia |].
      do 5 zstep. lit_branch.
      eapply LBd. match goal with P : stk asegs _ lo (q + -2144) |- _ => eapply inv_of; [ eassumption | exact P | eassumption .. ] end.
    -
      assert (N1 : 1 <= n <= 64) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      probe8_reg 16%Z RDS1 S w1 P1. probe8_reg 17%Z RDS1 (S + n + -1) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWSs; eassumption.
      + eapply LBd; exact IV0.
  Qed.

  #[using="MI ST LO KLO Q64 IE ARR HS HD ULO WIND WINS WIN2 ACCD RDD ACCS RDS NSZ"] Lemma memmove_i_body : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6, a0 = wz D -> a1 = wz S -> a2 = wz n ->
    evt asegs APOST (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz A0_memmove_i) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros -> -> ->. unfold A0_memmove_i. pose proof BL as BL0.
    pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO' : lo <= q - 2144) by lia.
    pose proof ST as ST0. ihide ARR.
    carve_frame 2144%nat ST0.
    zstep. do 12 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1;
      assert (ARR1 : u8arr asegs m1 U us)
        by (iunhide ARR; eapply u8arr_transport; [exact ARR| exact MU| exact WM| cbn [disjoint_from]; lia])
    end.
    pose proof (ie_inited _ IE1) as INI1. pose proof (ie_ric _ IE1) as RIC1. unfold env_inited in INI1. unfold env_ric in RIC1.
    do 3 zstep.
    cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (IV : INV mm) end.
    { eapply inv_of; try eassumption; first [ exact (proj1 (ie_shadow _ IE1)) | exact (proj2 (ie_shadow _ IE1))
        | exact (proj1 (ie_layout _ IE1)) | exact (proj2 (ie_layout _ IE1)) ]. }
    eapply LBs; exact IV.
  Qed.
End Proofs.

Lemma memmove_i_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S n U lo : Z) (us : list byte),
  u8arr asegs m U us -> (U <= S /\ S + n <= U + Z.of_nat (length us)) -> (U <= D /\ D + n <= U + Z.of_nat (length us)) ->
  accessible m D n -> sh_readable m D n -> accessible m S n -> sh_readable m S n ->
  icpt_env m -> cwin D n -> cwin S n -> D + n < 2^47 /\ S + n < 2^47 -> n <= 2^43 ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 2224 -> q < 2^64 ->
  (U + Z.of_nat (length us) <= lo \/ q <= U) ->
  mem_inv asegs m -> a0 = wz D -> a1 = wz S -> a2 = wz n ->
  evt asegs (memmove_i_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n U lo us m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_memmove_i) fc None m (seg_rom asegs)).
Proof. intros. eapply memmove_i_body; try eassumption. lia. Qed.
