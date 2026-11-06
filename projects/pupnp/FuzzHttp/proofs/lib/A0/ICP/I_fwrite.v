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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit F_rip F_gates I_read.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition fwrite_front_post0 (q : Z) (gp tp : word) (p sz nm f : Z) (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk : list byte),
    ms' = MS (mkR (wz 291140) (wz (q - 2128)) gp tp t0 t1 t2 (wz q) (wz sz) (wz p) (wz sz) (wz nm) (wz f) a4 a5 a6 a7
                 (wz p) (wz f) (wz nm) (wz 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 635068) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q - 2128)
    /\ rw_cells asegs m' (q - 2128) [CB 2072 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0].

Lemma fwrite_front_spec : forall (ra0 : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p sz nm f lo : Z),
  icpt_env m -> stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 2128 - 64 -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz p -> a1 = wz sz -> a2 = wz nm -> a3 = wz f ->
  evt asegs (fwrite_front_post0 q gp tp p sz nm f ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_fwrite) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros IE ST KLO LO Q64 MI -> -> -> ->. unfold A0_fwrite.
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO' : lo <= q - 2128) by lia.
  carve_frame 2128%nat ST.
  zstep. do 10 zstep. do 5 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1 end.
  call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
  clear IE1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
      pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1 end end.
  pose proof (ie_real_io _ IE1) as (RIO & _).
  do 8 zstep.
  replace (q + -2128) with (q - 2128) in * by lia.
  finish. exact FR.
Qed.

Section BackX.
  Variables (ra0 s0 s1 s2 s3 s4 s5 : word) (q : Z) (gp tp s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (r lo : Z).
  Hypothesis LO : lo <= q - 2128 - 80.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Notation APOST := (icpt_back_post0 ra0 q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r lo m).

  Definition WINVX (mc : mem) : Prop :=
    (exists jk, rw_cells asegs mc (q + -2128) [CB 2072 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0])
    /\ stk asegs mc lo (q + -2128)
    /\ munch [(lo, q)] m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc.

  #[using="LO"] Lemma WLX : forall mc x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    WINVX mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2128)) gp tp x5 x6 x7 x8 x9 (wz r) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x471a8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros ((jk & FR) & ST1 & MU1 & WM1 & MI1).
    do 10 zstep.
    release_frame FR ST1 q. finish.
  Qed.

  #[using="LO"] Lemma WLX5 : forall mc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    WINVX mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 (wz r) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x47354) fc None mc (seg_rom asegs)).
  Proof. intros until x31. intros IV. zstep. zstep. eapply WLX. exact IV. Qed.
End BackX.

Section BackC.
  Variables (ra0 s0 s1 s2 s3 s4 s5 : word) (q : Z) (gp tp s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (p N r lo : Z).
  Hypothesis LO : lo <= q - 2128 - 80.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Hypothesis POS : 0 < N.
  Hypothesis WIN : cwin p N.
  Hypothesis WIN2 : p + N < 2^47.
  Hypothesis ACC : accessible m p N.
  Hypothesis RDB : sh_readable m p N.
  Hypothesis NSZ : N <= 2^43.

  Notation APOST := (icpt_back_post0 ra0 q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r lo m).
  Notation INVX := (WINVX ra0 s0 s1 s2 s3 s4 s5 q m lo).
  Definition WINV (mc : mem) : Prop :=
    INVX mc /\ env_shadow mc /\ env_layout mc /\ accessible mc p N /\ sh_readable mc p N.

  #[using="LO KLO Q64 POS WIN WIN2"] Lemma BL : 0 <= p /\ 0 < N /\ p + N < 2^47 /\ 0 <= lo /\ q < 2^64 /\ lo <= q - 2208 /\ 17594333495296 <= lo.
  Proof. destruct WIN as [Hn W]. lia. Qed.

  Ltac invx_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1).
  Ltac inv_open H :=
    let IX := fresh "IX" in
    destruct H as (IX & (GOT1 & SHB1) & (LG1 & LC1) & ACC1 & RDB1); invx_open IX.

  #[using="LO KLO Q64 POS WIN WIN2"] Lemma LWL : forall mc (k : nat) (cur : Z) x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    WINV mc -> 1 <= N <= 64 ->
    Z.to_nat (sh (p + N - 1) - cur) = k -> sh p <= cur < sh (p + N - 1) ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2128)) gp tp x5 x6 x7 x8 x9 (wz r) (wz cur) (wz (2147450880 + Z.shiftr (p + N + -1) 3)) (wz 0) x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4726c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    revert cur x14 Hk Hc. induction k as [|k IH]; intros cur x14 Hk Hc; [exfalso; lia|].
    assert (SL : sh (p + N - 1) = 2147450880 + Z.shiftr (p + N + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (p + N + -1) with (p + N - 1) by lia; lia).
    pose proof (sh_div8 (p + N - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc p N cur ACC1 ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply WLX; [exact LO| exact (proj1 IV0)].
  Qed.

  #[using="LO KLO Q64 POS WIN WIN2"] Lemma LWS : forall mc x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    WINV mc -> 1 <= N <= 64 ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2128)) gp tp x5 x6 x7 x8 x9 (wz r) (wz (2147450880 + Z.shiftr p 3)) (wz (2147450880 + Z.shiftr (p + N + -1) 3)) (wz (p + N + -1)) x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x47250) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    destruct (acc_byte_rd mc p N (p + N + -1) ACC1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((p + N + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (p + N + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply WLX; [exact LO| exact (proj1 IV0)].
    - eapply LWL; [exact IV0 | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (p + N - 1) with (p + N + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= p / 8 < 2^44 /\ 0 <= (p + N + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite !Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 POS WIN WIN2 NSZ"] Lemma LB : forall mc x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31,
    WINV mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2128)) gp tp x5 x6 x7 x8 (wz N) (wz r) x11 x12 x13 x14 x15 x16 x17
               (wz p) x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x47160) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
      assert (N65 : 64 < N) by (clear - K2 K3 BL0; Z.div_mod_to_equations; lia).
      do 4 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct WIN as [_ W]; unfold rwin; lia | exact ACC1 | lia |].
      zstep. lit_branch.
      eapply WLX5; [exact LO|]. unfold WINVX. split; [eexists; eassumption|]. repeat (split; [eassumption|]). assumption.
    -
      assert (N1 : 1 <= N <= 64) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      probe8_reg 14%Z RDB1 p w1 P1. probe8_reg 15%Z RDB1 (p + N + -1) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS; eassumption.
      + eapply WLX; [exact LO| exact (proj1 IV0)].
  Qed.
End BackC.

Lemma fwrite_back_spec : forall (ra0 s0 s1 s2 s3 s4 s5 : word) (q : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p sz nm f r lo : Z) (junk : list byte),
  rw_cells asegs m (q - 2128) [CB 2072 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0] ->
  icpt_env m -> stk asegs m lo (q - 2128) -> 0x10007fff8000 <= lo -> lo <= q - 2128 - 80 -> q < 2^64 ->
  0 <= r -> 0 <= sz -> r * sz < 2^40 -> 0 <= p < 2^64 ->
  (0 < r * sz -> accessible m p (r * sz) /\ sh_readable m p (r * sz) /\ cwin p (r * sz) /\ p + r * sz < 2^47) ->
  mem_inv asegs m ->
  evt asegs (icpt_back_post0 ra0 q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r lo m)
    (MS (mkR (wz 291140) (wz (q - 2128)) gp tp t0 t1 t2 (wz q) (wz sz) (wz r) a1 a2 a3 a4 a5 a6 a7
             (wz p) (wz f) (wz nm) (wz 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 291140) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros FRM IE ST KLO LO Q64 Hr Hsz HN Hp CHK MI.
  replace (q - 2128) with (q + -2128) in * by lia.
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (IVX : WINVX ra0 s0 s1 s2 s3 s4 s5 q m lo m).
  { split; [exists junk; exact FRM|]. repeat (split; [assumption|]). assumption. }
  assert (NN : 0 <= r * sz) by (apply Z.mul_nonneg_nonneg; lia).
  zstep. lit_branch. zstep. if_cases K0; zify_cond K0.
  { eapply WLX; [exact LO| exact IVX]. }
  zstep.
  assert (R1 : 1 <= r) by (destruct (Z.eq_dec r 0) as [->|]; [exfalso; apply K0; reflexivity| lia]).
  assert (EN : Z_to_bv 64 (r mod 18446744073709551616 * (sz mod 18446744073709551616)) = Z_to_bv 64 (r * sz)).
  { destruct (Z.eq_dec sz 0) as [->|NZ]; [rewrite Z.mod_0_l by lia; rewrite !Z.mul_0_r; reflexivity|].
    assert (r < 2^40 /\ sz < 2^40) as [B1 B2] by (clear - R1 Hsz NZ HN; nia).
    rewrite !Z.mod_small by lia. reflexivity. }
  rewrite EN. clear EN.
  zstep. rewrite zb_lxor_ones by lia. do 3 zstep. if_cases KO; zify_cond KO. { exfalso. lia. }
  destruct (Z_lt_le_dec 0 (r * sz)) as [POS|NPOS].
  - destruct (CHK POS) as (ACC & RDB & WIN & WIN2).
    eapply (LB ra0 s0 s1 s2 s3 s4 s5 q gp tp s6 s7 s8 s9 s10 s11 F fc m p (r * sz) r lo); try eassumption; try lia.
    split; [exact IVX|]. split; [exact (ie_shadow _ IE)|]. split; [exact (ie_layout _ IE)|]. split; assumption.
  - assert (E0 : r * sz = 0) by lia. rewrite E0.
    zstep. zstep. zstep. lit_branch. zstep. lit_branch. zstep.
    eapply WLX; [exact LO| exact IVX].
Qed.
