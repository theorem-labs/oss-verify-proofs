(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require F_strncmp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit F_rip F_gates.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition istrncmp_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A B : Z) (ls rs : list byte) (v : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz (zsign v)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' A ls /\ bytes_at asegs m' B rs.

Section Proofs.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (A B n lo : Z) (ls rs : list byte) (v : Z).
  Notation NA := (Z.min n (Z.of_nat (length ls))).
  Notation NB := (Z.min n (Z.of_nat (length rs))).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo q.
  Hypothesis LO : lo <= q - 2176 - 80.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Hypothesis IE : icpt_env m.
  Hypothesis LSB : bytes_at asegs m A ls.
  Hypothesis RSB : bytes_at asegs m B rs.
  Hypothesis SEPA : A + Z.of_nat (length ls) <= lo \/ q <= A.
  Hypothesis SEPB : B + Z.of_nat (length rs) <= lo \/ q <= B.
  Hypothesis RN : 0 <= n < 2^63.
  Hypothesis WINA : cwin A NA.   Hypothesis WINA2 : A + NA < 2^47.   Hypothesis NSA : NA <= 2^43.
  Hypothesis WINB : cwin B NB.   Hypothesis WINB2 : B + NB < 2^47.   Hypothesis NSB : NB <= 2^43.
  Hypothesis ACCA : accessible m A NA.   Hypothesis RDA : sh_readable m A NA.
  Hypothesis ACCB : accessible m B NB.   Hypothesis RDB : sh_readable m B NB.

  Notation APOST := (istrncmp_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A B ls rs v lo m).

  Definition INVX (mc : mem) : Prop :=
    (exists jk, rw_cells asegs mc (q + -2176) [CB 2072 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (q + -2176)
    /\ munch [(lo, q)] m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ bytes_at asegs mc A ls /\ bytes_at asegs mc B rs.
  Definition INV (mc : mem) : Prop := INVX mc /\ icpt_env mc.

  #[using="LO KLO Q64 RN WINA WINA2 WINB WINB2"] Lemma BL : 0 <= A /\ 0 <= B /\ 0 <= NA /\ 0 <= NB /\ A + NA < 2^47 /\ B + NB < 2^47 /\ 0 <= lo /\ q < 2^64 /\ lo <= q - 2256 /\ 17594333495296 <= lo.
  Proof. destruct WINA as [HA _]. destruct WINB as [HB _]. destruct WINA as [_ WA]. destruct WINB as [_ WB]. lia. Qed.

  Ltac invx_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & LS1 & RS1).
  Ltac inv_open H :=
    let IX := fresh "IX" in
    destruct H as (IX & IEc); invx_open IX;
    pose proof (ie_shadow _ IEc) as (GOT1 & SHB1); pose proof (ie_layout _ IEc) as (LG1 & LC1).

  #[using="LO KLO Q64 RN WINA WINA2 WINB WINB2 ACCA RDA"] Lemma facts_A : forall mc sz, INVX mc -> 0 <= sz <= NA ->
    accessible mc A sz /\ sh_readable mc A sz /\ cwin A sz.
  Proof.
    intros mc sz IV Hsz. invx_open IV. pose proof BL as BL0.
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia).
    assert (CW : cwin A sz) by (destruct WINA as [_ W]; split; lia).
    split; [| split; [| exact CW]].
    - eapply accessible_munch; [eapply accessible_sub; [exact ACCA| lia| lia] | exact MU1 | exact CW | intros s Hs; apply HO; lia].
    - eapply sh_readable_munch; [eapply sh_readable_sub; [exact RDA| lia| lia| lia] | exact MU1 | exact CW | exact HO].
  Qed.
  #[using="LO KLO Q64 RN WINA WINA2 WINB WINB2 ACCB RDB"] Lemma facts_B : forall mc sz, INVX mc -> 0 <= sz <= NB ->
    accessible mc B sz /\ sh_readable mc B sz /\ cwin B sz.
  Proof.
    intros mc sz IV Hsz. invx_open IV. pose proof BL as BL0.
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia).
    assert (CW : cwin B sz) by (destruct WINB as [_ W]; split; lia).
    split; [| split; [| exact CW]].
    - eapply accessible_munch; [eapply accessible_sub; [exact ACCB| lia| lia] | exact MU1 | exact CW | intros s Hs; apply HO; lia].
    - eapply sh_readable_munch; [eapply sh_readable_sub; [exact RDB| lia| lia| lia] | exact MU1 | exact CW | exact HO].
  Qed.

  Definition resok (c1 c2 : word) : Prop :=
    exists a b, c1 = wz a /\ c2 = wz b /\ 0 <= a < 256 /\ 0 <= b < 256 /\ zsign v = zsign (a - b).

  #[using="n LO KLO Q64 RN WINA WINA2 WINB WINB2"] Lemma LR : forall mc c1 c2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x26 x27 x28 x29 x30 x31,
    INVX mc -> resok c1 c2 ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2176)) gp tp x5 x6 x7 (wz q) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 c1 c2 x26 x27 x28 x29 x30 x31)
          F (wz 0x44e88) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV (a & b & -> & -> & Ra & Rb & EV). pose proof BL as BL0. invx_open IV.
    zstep. zstep. zstep.
    assert (ZS : Z.b2z (b <? a) - Z.b2z (a <? b) = zsign v).
    { rewrite EV. unfold zsign. clear - Ra Rb. destruct (Z.ltb_spec b a), (Z.ltb_spec a b), (Z.ltb_spec (a - b) 0), (Z.ltb_spec 0 (a - b)); cbn; lia. }
    rewrite ZS. clear ZS.
    do 5 zstep.
    zstep. zstep. zstep. zstep.
    do 15 zstep.
    release_frame FR ST1 q. finish.
  Qed.

  #[using="LO KLO Q64 RN WINA WINA2 WINB WINB2 ACCB RDB"] Lemma LWLb : forall mc sz c1 c2 (k : nat) (cur : Z) x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x19 x20 x22 x23 x26 x27 x28 x29 x30 x31,
    INV mc -> resok c1 c2 -> 1 <= sz <= 64 -> sz <= NB ->
    Z.to_nat (sh (B + sz - 1) - cur) = k -> sh B <= cur < sh (B + sz - 1) ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2176)) gp tp x5 x6 x7 (wz q) x9 (wz cur) (wz (2147450880 + Z.shiftr (B + sz + -1) 3)) (wz 0) x13 x14 x15 x16 x17
               (wz B) x19 x20 (wz sz) x22 x23 c1 c2 x26 x27 x28 x29 x30 x31)
          F (wz 0x450ec) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV RES N1 NLE Hk Hc. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts_B mc sz (proj1 IV) ltac:(lia)) as (ACC1 & RDB1 & CW1). inv_open IV.
    revert cur x13 Hk Hc. induction k as [|k IH]; intros cur x13 Hk Hc; [exfalso; lia|].
    assert (SL : sh (B + sz - 1) = 2147450880 + Z.shiftr (B + sz + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (B + sz + -1) with (B + sz - 1) by lia; lia).
    pose proof (sh_div8 (B + sz - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc B sz cur ACC1 ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LR; [exact (proj1 IV0)| exact RES].
  Qed.

  #[using="LO KLO Q64 SEPB RN WINA WINA2 WINB WINB2 ACCB RDB"] Lemma LWSb : forall mc sz c1 c2 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x19 x20 x22 x23 x26 x27 x28 x29 x30 x31,
    INV mc -> resok c1 c2 -> 1 <= sz <= 64 -> sz <= NB ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2176)) gp tp x5 x6 x7 (wz q) x9 (wz (2147450880 + Z.shiftr B 3)) (wz (2147450880 + Z.shiftr (B + sz + -1) 3)) (wz (B + sz + -1)) x13 x14 x15 x16 x17
               (wz B) x19 x20 (wz sz) x22 x23 c1 c2 x26 x27 x28 x29 x30 x31)
          F (wz 0x450d0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV RES N1 NLE. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts_B mc sz (proj1 IV) ltac:(lia)) as (ACC1 & RDB1 & CW1). inv_open IV.
    destruct (acc_byte_rd mc B sz (B + sz + -1) ACC1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((B + sz + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (B + sz + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LR; [exact (proj1 IV0)| exact RES].
    - eapply LWLb; [exact IV0 | exact RES | assumption | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (B + sz - 1) with (B + sz + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= B / 8 < 2^44 /\ 0 <= (B + sz + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite !Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 SEPA SEPB RN WINA WINA2 NSA WINB WINB2 NSB ACCB RDB"] Lemma LBb : forall mc sz c1 c2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x26 x27 x28 x29 x30 x31,
    INV mc -> resok c1 c2 -> 0 <= sz <= NB ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2176)) gp tp x5 x6 x7 (wz q) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (wz B) x19 x20 (wz sz) x22 x23 c1 c2 x26 x27 x28 x29 x30 x31)
          F (wz 0x44e40) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV RES NLE. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts_B mc sz (proj1 IV) ltac:(lia)) as (ACC1 & RDB1 & CW1). inv_open IV.
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LR; [exact (proj1 IV0)| exact RES]. }
      assert (N65 : 64 < sz) by (clear - K2 K3 NLE NSB; Z.div_mod_to_equations; lia).
      do 3 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct CW1 as [_ W]; unfold rwin; lia | exact ACC1 | lia |].
      zstep. lit_branch.
      eapply LR; [| exact RES]. unfold INVX. split; [eexists; eassumption|]. repeat (split; [eassumption|]). assumption.
    -
      assert (N1 : 1 <= sz <= 64) by (clear - K2 NLE NSB; Z.div_mod_to_equations; lia).
      do 11 zstep.
      probe8_reg 13%Z RDB1 B w1 P1. probe8_reg 14%Z RDB1 (B + sz + -1) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWSb; [exact IV0| exact RES| exact N1| lia].
      + eapply LR; [exact (proj1 IV0)| exact RES].
  Qed.

  #[using="LO KLO Q64 SEPA SEPB RN WINA WINA2 NSA WINB WINB2 NSB ACCB RDB"] Lemma LC : forall mc I c1 c2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x26 x28 x29 x30 x31,
    INV mc -> resok c1 c2 -> 0 <= I <= n -> Z.min (I + 1) n <= NB ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2176)) gp tp x5 x6 x7 (wz q) (wz n) x10 x11 x12 x13 x14 x15 x16 x17
               (wz B) x19 x20 x21 x22 x23 c1 c2 x26 (wz I) x28 x29 x30 x31)
          F (wz 0x44e30) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV RES HI HSZ. pose proof BL as BL0.
    zstep. zstep. if_cases KM; zify_cond KM.
    -
      assert (ESZ : Z.min (I + 1) n = n) by lia.
      zstep. zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
      eapply (LBb mc n); [exact IV| exact RES| lia].
    - assert (ESZ : Z.min (I + 1) n = I + 1) by lia.
      zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
      eapply (LBb mc (I + 1)); [exact IV| exact RES| lia].
  Qed.

  #[using="LO KLO Q64 SEPA SEPB RN WINA WINA2 NSA WINB WINB2 NSB ACCA RDA ACCB RDB"] Lemma LWLa : forall mc sz I c1 c2 (k : nat) (cur : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x22 x23 x26 x28 x29 x30 x31,
    INV mc -> resok c1 c2 -> 0 <= I <= n -> sz = Z.min (I + 1) n -> sz <= NA -> sz <= NB -> 1 <= sz <= 64 ->
    Z.to_nat (sh (A + sz - 1) - cur) = k -> sh A <= cur < sh (A + sz - 1) ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2176)) gp tp x5 x6 x7 (wz q) (wz n) (wz cur) (wz (2147450880 + Z.shiftr (A + sz + -1) 3)) (wz 0) x13 x14 x15 x16 x17
               (wz B) (wz A) x20 (wz sz) x22 x23 c1 c2 x26 (wz I) x28 x29 x30 x31)
          F (wz 0x45024) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV RES HI ESZ NLA NLB N1 Hk Hc. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts_A mc sz (proj1 IV) ltac:(lia)) as (ACC1 & RDB1 & CW1). inv_open IV.
    revert cur x13 Hk Hc. induction k as [|k IH]; intros cur x13 Hk Hc; [exfalso; lia|].
    assert (SL : sh (A + sz - 1) = 2147450880 + Z.shiftr (A + sz + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (A + sz + -1) with (A + sz - 1) by lia; lia).
    pose proof (sh_div8 (A + sz - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc A sz cur ACC1 ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LC; [exact IV0| exact RES| exact HI| lia].
  Qed.

  #[using="LO KLO Q64 SEPA SEPB RN WINA WINA2 NSA WINB WINB2 NSB ACCA RDA ACCB RDB"] Lemma LWSa : forall mc sz I c1 c2 x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x22 x23 x26 x28 x29 x30 x31,
    INV mc -> resok c1 c2 -> 0 <= I <= n -> sz = Z.min (I + 1) n -> sz <= NA -> sz <= NB -> 1 <= sz <= 64 ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2176)) gp tp x5 x6 x7 (wz q) (wz n) (wz (2147450880 + Z.shiftr A 3)) (wz (2147450880 + Z.shiftr (A + sz + -1) 3)) (wz (A + sz + -1)) x13 x14 x15 x16 x17
               (wz B) (wz A) x20 (wz sz) x22 x23 c1 c2 x26 (wz I) x28 x29 x30 x31)
          F (wz 0x45008) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV RES HI ESZ NLA NLB N1. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts_A mc sz (proj1 IV) ltac:(lia)) as (ACC1 & RDB1 & CW1). inv_open IV.
    destruct (acc_byte_rd mc A sz (A + sz + -1) ACC1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((A + sz + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (A + sz + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LC; [exact IV0| exact RES| exact HI| lia].
    - eapply LWLa; [exact IV0 | exact RES | exact HI | exact ESZ | assumption | assumption | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (A + sz - 1) with (A + sz + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= A / 8 < 2^44 /\ 0 <= (A + sz + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite !Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 IE SEPA SEPB RN WINA WINA2 NSA WINB WINB2 NSB ACCA RDA ACCB RDB"] Lemma LBa : forall mc sz I c1 c2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x26 x28 x29 x30 x31,
    INV mc -> resok c1 c2 -> 0 <= I <= n -> sz = Z.min (I + 1) n -> sz <= NA -> sz <= NB ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2176)) gp tp x5 x6 x7 (wz q) (wz n) x10 x11 x12 x13 x14 x15 x16 x17
               (wz B) (wz A) x20 (wz sz) x22 x23 c1 c2 x26 (wz I) x28 x29 x30 x31)
          F (wz 0x44de8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV RES HI ESZ NLA NLB. pose proof BL as BL0. pose proof IV as IV0.
    assert (SZ0 : 0 <= sz) by lia.
    destruct (facts_A mc sz (proj1 IV) ltac:(lia)) as (ACC1 & RDB1 & CW1). inv_open IV.
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LC; [exact IV0| exact RES| exact HI| lia]. }
      assert (N65 : 64 < sz) by (clear - K2 K3 SZ0 NLA NSA; Z.div_mod_to_equations; lia).
      do 3 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct CW1 as [_ W]; unfold rwin; lia | exact ACC1 | lia |].
      zstep. lit_branch.
      eapply LC; [| exact RES| exact HI| lia].
      split; [unfold INVX; split; [eexists; eassumption|]; repeat (split; [eassumption|]); assumption
             | eapply icpt_env_stack; [exact IE| eassumption| eassumption| lia]].
    -
      assert (N1 : 1 <= sz <= 64) by (clear - K2 SZ0 NLA NSA; Z.div_mod_to_equations; lia).
      do 11 zstep.
      probe8_reg 13%Z RDB1 A w1 P1. probe8_reg 14%Z RDB1 (A + sz + -1) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWSa; eassumption.
      + eapply LC; [exact IV0| exact RES| exact HI| lia].
  Qed.

  #[using="LO KLO Q64 IE SEPA SEPB RN WINA WINA2 NSA WINB WINB2 NSB ACCA RDA ACCB RDB"] Lemma LE : forall mc I c1 c2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x26 x28 x29 x30 x31,
    INV mc -> resok c1 c2 -> 0 <= I <= n -> Z.min (I + 1) n <= NA -> Z.min (I + 1) n <= NB ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2176)) gp tp x5 x6 x7 (wz q) (wz n) x10 x11 x12 x13 x14 x15 x16 x17
               (wz B) (wz A) x20 x21 x22 x23 c1 c2 x26 (wz I) x28 x29 x30 x31)
          F (wz 0x44cc8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV RES HI HA HB. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    pose proof (ie_cf _ IEc) as CF1. pose proof (ie_flags _ IEc) as FL1. unfold env_cf in CF1. unfold env_flags in FL1.
    zstep. if_cases KI; zify_cond KI.
    -
      zstep. zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
      zstep. zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
      eapply (LBa mc n I); [exact IV0| exact RES| exact HI| lia| lia| lia].
    -
      do 3 zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. lit_branch.
      zstep. zstep. if_cases K2; zify_cond K2.
      +
        zstep. zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
        eapply (LBa mc n I); [exact IV0| exact RES| exact HI| lia| lia| lia].
      + zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
        eapply (LBa mc (I + 1) I); [exact IV0| exact RES| exact HI| lia| lia| lia].
  Qed.

  #[using="LO KLO Q64 IE SEPA SEPB RN WINA WINA2 NSA WINB WINB2 NSB ACCA RDA ACCB RDB"] Lemma LL : forall mc (k : nat) (i : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    INV mc -> 0 <= i < n -> Z.to_nat (n - 1 - i) = k ->
    strncmp_walk (skipn (Z.to_nat i) ls) (skipn (Z.to_nat i) rs) k = Some v ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2176)) gp tp x5 x6 x7 (wz q) (wz n) x10 x11 x12 x13 x14 x15 x16 x17
               (wz B) (wz A) x20 x21 x22 x23 x24 x25 x26 (wz i) x28 x29 x30 x31)
          F (wz 0x44ca0) fc None mc (seg_rom asegs)).
  Proof.
    intros mc k. induction k as [|k IH]; intros until x31; intros IV Hi Hk HW; pose proof BL as BL0; pose proof IV as IV0; inv_open IV;
      destruct (F_strncmp.walk_at ls rs _ _ _ HW) as (a & b & Hna & Hnb & HC);
      pose proof (nth_error_lt _ _ _ Hna) as LA; pose proof (nth_error_lt _ _ _ Hnb) as LB0;
      pose proof (bytes_at_bound _ _ _ _ LS1) as BA; pose proof (bytes_at_bound _ _ _ _ RS1) as BB;
      pose proof (bv_unsigned_in_range 8 a) as Ra; pose proof (bv_unsigned_in_range 8 b) as Rb; unfold bv_modulus in Ra, Rb; cbn in Ra, Rb;
      pose proof (u8ro_read asegs mc A ls i a (wz (A + i)) LS1 Hna ltac:(lia) eq_refl) as RDa;
      pose proof (u8ro_read asegs mc B rs i b (wz (B + i)) RS1 Hnb ltac:(lia) eq_refl) as RDb.
    -
      cbn [Nat.eqb] in HC. rewrite !orb_true_r in HC. cbn [orb] in HC.
      zstep. zstep. zstep. zstep. cbv beta. zstep. if_cases Ka; zify_cond Ka.
      + eapply (LE mc i); [exact IV0| exists (bv_unsigned a), (bv_unsigned b); repeat split; try lia; rewrite HC; reflexivity | lia | lia | lia].
      + zstep. if_cases Kne; zify_cond Kne.
        * eapply (LE mc i); [exact IV0| exists (bv_unsigned a), (bv_unsigned b); repeat split; try lia; rewrite HC; reflexivity | lia | lia | lia].
        * zstep. zstep. if_cases Kn; zify_cond Kn. { exfalso. lia. }
          zstep. zstep.
          replace (Z_to_bv 64 (i + 1)) with (Z_to_bv 64 n) by (f_equal; lia).
          eapply (LE mc n); [exact IV0| exists (bv_unsigned a), (bv_unsigned a); repeat split; try lia; rewrite HC; f_equal; lia | lia | lia | lia].
    - zstep. zstep. zstep. zstep. cbv beta. zstep. if_cases Ka; zify_cond Ka.
      + replace ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb (S k) 0 || negb (bv_unsigned a =? bv_unsigned b))%bool with true in HC
          by (symmetry; rewrite (proj2 (Z.eqb_eq _ _) Ka); reflexivity).
        eapply (LE mc i); [exact IV0| exists (bv_unsigned a), (bv_unsigned b); repeat split; try lia; rewrite HC; reflexivity | lia | lia | lia].
      + zstep. if_cases Kne; zify_cond Kne.
        * replace ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb (S k) 0 || negb (bv_unsigned a =? bv_unsigned b))%bool with true in HC
            by (symmetry; rewrite (proj2 (Z.eqb_neq _ _) Kne); cbn [negb]; rewrite !orb_true_r; reflexivity).
          eapply (LE mc i); [exact IV0| exists (bv_unsigned a), (bv_unsigned b); repeat split; try lia; rewrite HC; reflexivity | lia | lia | lia].
        * replace ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb (S k) 0 || negb (bv_unsigned a =? bv_unsigned b))%bool with false in HC
            by (symmetry; rewrite (proj2 (Z.eqb_neq _ _) Ka); rewrite <- Kne; rewrite (proj2 (Z.eqb_neq _ _) Ka); rewrite Z.eqb_refl; reflexivity).
          destruct HC as (k' & Ek & HW'). injection Ek as <-.
          zstep. zstep. if_cases Kn; zify_cond Kn. 2:{ exfalso. lia. }
          eapply (IH (i + 1)); [exact IV0| lia| lia|].
          replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact HW'.
  Qed.

  Hypothesis MOD : strncmp_model ls rs n = Some v.

  #[using="MI ST LO KLO Q64 IE LSB RSB SEPA SEPB RN WINA WINA2 NSA WINB WINB2 NSB ACCA RDA ACCB RDB MOD"] Lemma istrncmp_body : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6, a0 = wz A -> a1 = wz B -> a2 = wz n ->
    evt asegs APOST (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz A0_strncmp) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros -> -> ->. unfold A0_strncmp. pose proof BL as BL0.
    pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO' : lo <= q - 2176) by lia.
    pose proof ST as ST0. ihide LSB. ihide RSB.
    carve_frame 2176%nat ST0.
    zstep. do 16 zstep. do 5 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1;
      assert (LS1 : bytes_at asegs m1 A ls) by (iunhide LSB; eapply bytes_at_transport; [exact LSB| exact MU| cbn [disjoint_from]; lia]);
      assert (RS1 : bytes_at asegs m1 B rs) by (iunhide RSB; eapply bytes_at_transport; [exact RSB| exact MU| cbn [disjoint_from]; lia])
    end.
    call inited_spec; [assumption | exact (ie_inited _ IE1) |].
    zstep. lit_branch. zstep.
    call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
    clear IE1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
        pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1 end end.
    zstep. lit_branch.
    assert (IV : INV _) by (split; [unfold INVX; split; [eexists; eassumption|]; repeat (split; [eassumption|]); assumption | exact IE1]).
    unfold strncmp_model in MOD.
    zstep. if_cases KN; zify_cond KN.
    -
      replace (n =? 0) with true in MOD by (symmetry; apply Z.eqb_eq; lia). injection MOD as EV0.
      do 4 zstep. zstep. zstep. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
      zstep. zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
      eapply (LBa _ n 0); [exact IV| exists 0, 0; repeat split; try lia; rewrite <- EV0; reflexivity | lia | lia | lia | lia].
    - replace (n =? 0) with false in MOD by (symmetry; apply Z.eqb_neq; lia).
      zstep.
      eapply (LL _ (Z.to_nat (n - 1)) 0); [exact IV| lia| f_equal; lia| exact MOD].
  Qed.
End Proofs.

Lemma strncmp_i_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A B n : Z) (ls rs : list byte) (v : Z) (lo : Z),
  bytes_at asegs m A ls -> bytes_at asegs m B rs ->
  strncmp_model ls rs n = Some v ->
  accessible m A (Z.min n (Z.of_nat (length ls))) -> sh_readable m A (Z.min n (Z.of_nat (length ls))) ->
  accessible m B (Z.min n (Z.of_nat (length rs))) -> sh_readable m B (Z.min n (Z.of_nat (length rs))) ->
  icpt_env m ->
  cwin A (Z.min n (Z.of_nat (length ls))) -> A + Z.min n (Z.of_nat (length ls)) < 2^47 -> Z.min n (Z.of_nat (length ls)) <= 2^43 ->
  cwin B (Z.min n (Z.of_nat (length rs))) -> B + Z.min n (Z.of_nat (length rs)) < 2^47 -> Z.min n (Z.of_nat (length rs)) <= 2^43 ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 2256 -> q < 2^64 ->
  (A + Z.of_nat (length ls) <= lo \/ q <= A) -> (B + Z.of_nat (length rs) <= lo \/ q <= B) ->
  mem_inv asegs m -> a0 = wz A -> a1 = wz B -> a2 = wz n -> 0 <= n < 2^63 ->
  evt asegs (istrncmp_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A B ls rs v lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_strncmp) fc None m (seg_rom asegs)).
Proof. intros. eapply istrncmp_body; try eassumption. lia. Qed.
