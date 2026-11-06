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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit IcptKit2 F_gates F_rip I_strtolfix M_sspdefs M_strtol I_strtol.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition atoi_tpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' S (str ++ [Z_to_bv 8 0]).

Section Tail.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (S lo k : Z) (str : list byte) (jk0 jk1 : list byte).
  Notation LEN := (Z.of_nat (length str)).
  Notation NS := (LEN + 1).
  Notation SAVES := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis MI : mem_inv asegs m.
  Hypothesis FRLO : rw_cells asegs m (q + -2160) [CB 2064 jk0].
  Hypothesis ECM : rw_cells asegs m (q + -96) [C8 (wz (S + k))].
  Hypothesis FRHI : rw_cells asegs m (q + -88) (CB 8 jk1 :: SAVES).
  Hypothesis ST : stk asegs m lo (q + -2160).
  Hypothesis LO : lo <= q - 2160 - 80.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Hypothesis IE : icpt_env m.
  Hypothesis STR : bytes_at asegs m S (str ++ [Z_to_bv 8 0]).
  Hypothesis SEPS : S + NS <= lo \/ q <= S.
  Hypothesis HK : 0 <= k <= LEN.
  Hypothesis WINS : cwin S NS.
  Hypothesis WIN2 : S + NS < 2^47.
  Hypothesis NSZ : NS <= 2^43.
  Hypothesis ACCS : accessible m S NS.
  Hypothesis RDS : sh_readable m S NS.

  Notation TPOST := (atoi_tpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str lo m).

  Definition INVX (mc : mem) : Prop :=
    (exists j0, rw_cells asegs mc (q + -2160) [CB 2064 j0])
    /\ (exists v : word, rw_cells asegs mc (q + -96) [C8 v])
    /\ (exists j1, rw_cells asegs mc (q + -88) (CB 8 j1 :: SAVES))
    /\ stk asegs mc lo (q + -2160)
    /\ munch [(lo, q)] m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ bytes_at asegs mc S (str ++ [Z_to_bv 8 0]).
  Definition INV (mc : mem) : Prop := INVX mc /\ icpt_env mc.

  #[using="LO KLO Q64 WINS WIN2"] Lemma BL : 0 <= S /\ 0 <= LEN /\ S + NS < 2^47 /\ 0 <= lo /\ q < 2^64 /\ lo <= q - 2240 /\ 17594333495296 <= lo.
  Proof. destruct WINS as [_ W]. lia. Qed.

  Ltac invx_open H :=
    let j0 := fresh "j0" in let v := fresh "v" in let j1 := fresh "j1" in
    destruct H as ((j0 & FRL) & (v & EC1) & (j1 & FRH) & ST1 & MU1 & WM1 & MI1 & STR1).
  Ltac inv_open H :=
    let IX := fresh "IX" in
    destruct H as (IX & IEc); invx_open IX;
    pose proof (ie_shadow _ IEc) as (GOT1 & SHB1); pose proof (ie_layout _ IEc) as (LG1 & LC1).

  #[using="k jk0 jk1 MI FRLO ECM FRHI ST IE STR"] Lemma inv0 : INV m.
  Proof.
    split; [| exact IE]. split; [eexists; exact FRLO|]. split; [eexists; exact ECM|]. split; [eexists; exact FRHI|].
    split; [exact ST|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI| exact STR].
  Qed.

  #[using="LO KLO Q64 WINS WIN2 ACCS RDS"] Lemma facts_S : forall mc sz, INVX mc -> 0 <= sz <= NS ->
    accessible mc S sz /\ sh_readable mc S sz /\ cwin S sz.
  Proof.
    intros mc sz IV Hsz. invx_open IV. pose proof BL as BL0.
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia).
    assert (CW : cwin S sz) by (destruct WINS as [_ W]; split; lia).
    split; [| split; [| exact CW]].
    - eapply accessible_munch; [eapply accessible_sub; [exact ACCS| lia| lia] | exact MU1 | exact CW | intros s Hs; apply HO; lia].
    - eapply sh_readable_munch; [eapply sh_readable_sub; [exact RDS| lia| lia| lia] | exact MU1 | exact CW | exact HO].
  Qed.

  #[using="LO KLO Q64 WINS WIN2"] Lemma LX : forall mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    INVX mc ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4c700) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. invx_open IV.
    do 14 zstep.

    destruct (rw_cells_C8_CB _ _ _ _ EC1) as [ej ECB].
    assert (FRJ : rw_cells asegs mc (q + -2160) ([CB 2064 j0] ++ [CB 8 ej] ++ (CB 8 j1 :: SAVES))).
    { apply (proj2 (rw_cells_app asegs mc (q + -2160) [CB 2064 j0] _)). split; [exact FRL|].
      replace (q + -2160 + Z.of_nat (cells_size [CB 2064 j0])) with (q + -96) by (cbn; lia).
      apply (proj2 (rw_cells_app asegs mc (q + -96) [CB 8 ej] _)). split; [exact ECB|].
      replace (q + -96 + Z.of_nat (cells_size [CB 8 ej])) with (q + -88) by (cbn; lia). exact FRH. }
    cbn [app] in FRJ. clear FRL EC1 ECB FRH.
    release_frame FRJ ST1 q. finish.
  Qed.

  #[using="LO KLO Q64 WINS WIN2 ACCS RDS"] Lemma LWL : forall mc off (j : nat) (cur : Z) x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    INV mc -> 0 <= off < 64 -> off <= LEN ->
    Z.to_nat (sh (S + off) - cur) = j -> sh S <= cur < sh (S + off) ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) x9 (wz cur) (wz (2147450880 + Z.shiftr (S + off) 3)) (wz 0) x13 x14 x15 x16 x17
               (wz S) (wz (off + 1)) x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4c7c8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 NLE Hj Hc. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts_S mc (off + 1) (proj1 IV) ltac:(lia)) as (ACC1 & RDS1 & CW1). inv_open IV.
    revert cur x13 Hj Hc. induction j as [|j IH]; intros cur x13 Hj Hc; [exfalso; lia|].
    assert (SL : sh (S + off) = 2147450880 + Z.shiftr (S + off) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; lia).
    pose proof (sh_div8 (S + off)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc S (off + 1) cur ACC1 ltac:(lia) ltac:(replace (S + (off + 1) - 1) with (S + off) by lia; lia))) as RDc.
    assert (SB : 0 <= (S + off) / 8 < 2^44) by (Z.div_mod_to_equations; lia).
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K;
      change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite shiftr3_div in K;
      rewrite !Z.mod_small in K by (unfold sh, SHADOW_OFF in *; lia); rewrite shiftr3_div in SL.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; exact (proj1 IV0).
  Qed.

  #[using="LO KLO Q64 WINS WIN2 ACCS RDS"] Lemma LWS : forall mc off x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    INV mc -> 0 <= off < 64 -> off <= LEN ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) x9 (wz (2147450880 + Z.shiftr S 3)) (wz (2147450880 + Z.shiftr (S + off) 3)) (wz (S + off)) x13 x14 x15 x16 x17
               (wz S) (wz (off + 1)) x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4c7ac) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 NLE. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts_S mc (off + 1) (proj1 IV) ltac:(lia)) as (ACC1 & RDS1 & CW1). inv_open IV.
    destruct (acc_byte_rd mc S (off + 1) (S + off) ACC1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((S + off) mod 8) k2) by (pose proof (Z.mod_pos_bound (S + off) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; exact (proj1 IV0).
    - eapply LWL; [exact IV0 | assumption | assumption | reflexivity |].
      rewrite !shiftr3_div in *. unfold sh, SHADOW_OFF.
      assert (0 <= S / 8 < 2^44 /\ 0 <= (S + off) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      change 18446744073709551615 with (Z.ones 64) in K6; rewrite ?Z.land_ones in K6 by lia.
      rewrite ?Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 SEPS WINS WIN2 NSZ ACCS RDS"] Lemma LB : forall mc off x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    INV mc -> 0 <= off <= LEN ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) x9 (wz off) x11 x12 x13 x14 x15 x16 x17
               (wz S) (wz (off + 1)) x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4c6b0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV NLE. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts_S mc (off + 1) (proj1 IV) ltac:(lia)) as (ACC1 & RDS1 & CW1). inv_open IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
      do 3 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct CW1 as [_ W]; unfold rwin; lia | exact ACC1 | lia |].
      zstep. lit_branch.
      eapply LX. unfold INVX. split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [eexists; eassumption|].
      repeat (split; [eassumption|]). assumption.
    - do 10 zstep. replace (off + S) with (S + off) by lia.
      probe8_regx 13%Z RDS1 S w1 P1. probe8_regx 14%Z RDS1 (S + off) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS; [exact IV0| lia| lia].
      + eapply LX; exact (proj1 IV0).
  Qed.

  #[using="LO KLO Q64 SEPS WINS WIN2 NSZ ACCS RDS"] Lemma L_size : forall mc off x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    INV mc -> 0 <= off <= LEN ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) x9 x10 (wz (S + off)) x12 x13 x14 x15 x16 x17
               (wz S) x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4c68c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV Hoff. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    pose proof (ie_cf _ IEc) as CF1. pose proof (ie_flags _ IEc) as FL1. unfold env_cf in CF1. unfold env_flags in FL1.
    do 3 zstep. cbv beta. zsimp. zstep. lit_branch.
    zstep. zstep.
    replace (S + off - S) with off by lia.
    eapply LB; [exact IV0| lia].
  Qed.

  Notation LL := (str ++ [Z_to_bv 8 0]).
  Ltac nland K := try (change 18446744073709551615 with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia).

  #[using="LO KLO Q64 IE SEPS WINS WIN2 NSZ ACCS RDS"] Lemma L_ws : forall (n i : nat) mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    INV mc -> (i <= length str)%nat -> nblank (skipn i LL) = n -> (nblank LL = i + n)%nat ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) x9 (wz 5) (wz (S + Z.of_nat i)) (wz 32) x13 x14 x15 x16 x17
               (wz S) x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4c664) fc None mc (seg_rom asegs)).
  Proof.
    induction n as [|n IH]; intros until x31; intros IV Hi Hn Hnb; pose proof BL as BL0; pose proof IV as IV0; inv_open IV;
      (destruct (nth_error LL i) as [b|] eqn:Eb; [| exfalso; apply nth_error_None in Eb; rewrite length_app in Eb; cbn in Eb; lia]);
      pose proof (bv_unsigned_in_range 8 b) as Rb; unfold bv_modulus in Rb; cbn in Rb;
      pose proof (bytes_at_bound _ _ _ _ STR1) as BS; rewrite length_app in BS; cbn [length] in BS;
      pose proof (u8ro_read asegs mc S LL (Z.of_nat i) b (wz (S + Z.of_nat i)) STR1 ltac:(rewrite Nat2Z.id; exact Eb) ltac:(lia) eq_refl) as RDb;
      assert (SK : skipn i LL = b :: skipn (Datatypes.S i) LL) by (clear - Eb; revert i Eb; induction LL as [|x l IHl]; intros [|i] E; cbn in *; try discriminate; [injection E as ->; reflexivity | apply IHl; exact E]);
      rewrite SK in Hn; cbn [nblank] in Hn; pose proof (blank_code str _ Rb) as BC.
    -
      destruct (is_blank (bv_unsigned b)) eqn:EB; [discriminate Hn|]. symmetry in BC. apply orb_false_iff in BC. destruct BC as [BC1 BC2].
      apply Z.ltb_ge in BC1. apply Z.eqb_neq in BC2.
      zstep. cbv beta. zstep. zstep. if_cases K1; zify_cond K1; nland K1. { exfalso. lia. }
      zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
      assert (FO : fix_off LL = if ((bv_unsigned b =? 43) || (bv_unsigned b =? 45))%bool then Z.of_nat i + 1 else Z.of_nat i).
      { unfold fix_off. replace (nblank LL) with i by lia. rewrite Eb. reflexivity. }
      pose proof (fix_off_range str) as FR0.
      assert (FIN : forall mc' y1 y5 y6 y7 y9 y10 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31, INV mc' ->
        evt asegs TPOST
          (MS (mkR y1 (wz (q + -2160)) gp tp y5 y6 y7 (wz q) y9 y10 (wz (S + fix_off LL)) y12 y13 y14 y15 y16 y17
                   (wz S) y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
              F (wz 0x4c688) fc None mc' (seg_rom asegs))).
      { intros until y31. intros IV'. pose proof IV' as IV'0. destruct IV' as (IX' & IE').
        destruct IX' as ((j0' & FRL') & (v' & EC') & (j1' & FRH') & ST' & MU' & WM' & MI' & STR').
        zstep.
        eapply L_size; [| lia].
        split; [| eapply icpt_env_stack; [exact IE| eassumption| eassumption| lia]].
        split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [eexists; eassumption|]. repeat (split; [eassumption|]). assumption. }
      zstep. zstep. if_cases K3; zify_cond K3.
      + rewrite (proj2 (Z.eqb_eq _ _) K3) in FO. cbn [orb] in FO.
        zstep. replace (S + Z.of_nat i + 1) with (S + fix_off LL) by lia.
        eapply FIN; exact IV0.
      + zstep. zstep. if_cases K4; zify_cond K4.
        * rewrite (proj2 (Z.eqb_neq _ _) K3), (proj2 (Z.eqb_neq _ _) K4) in FO. cbn [orb] in FO.
          replace (S + Z.of_nat i) with (S + fix_off LL) by lia.
          eapply FIN; exact IV0.
        * rewrite (proj2 (Z.eqb_eq _ _) K4), orb_true_r in FO.
          zstep. replace (S + Z.of_nat i + 1) with (S + fix_off LL) by lia.
          eapply FIN; exact IV0.
    -
      destruct (is_blank (bv_unsigned b)) eqn:EB; [| discriminate Hn]. injection Hn as Hn.
      assert (ILT : (i < length str)%nat).
      { destruct (Nat.eq_dec i (length str)) as [EQ|]; [|lia]. exfalso. rewrite EQ, nth_error_app2, Nat.sub_diag in Eb by lia. cbn in Eb. injection Eb as <-. vm_compute in EB. discriminate. }
      symmetry in BC. apply orb_true_iff in BC.
      zstep. cbv beta. zstep. zstep. if_cases K1; zify_cond K1; nland K1.
      + zstep. replace (S + Z.of_nat i + 1) with (S + Z.of_nat (Datatypes.S i)) by lia.
        eapply IH; [exact IV0| lia| exact Hn| lia].
      + zstep. if_cases K2; zify_cond K2.
        * zstep. replace (S + Z.of_nat i + 1) with (S + Z.of_nat (Datatypes.S i)) by lia.
          eapply IH; [exact IV0| lia| exact Hn| lia].
        * exfalso. destruct BC as [BC|BC]; [apply Z.ltb_lt in BC; lia | apply Z.eqb_eq in BC; lia].
  Qed.

  #[using="k jk0 jk1 MI FRLO ECM FRHI ST LO KLO Q64 IE STR SEPS HK WINS WIN2 NSZ ACCS RDS"] Lemma L_cmp : forall x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2160)) gp tp x5 x6 x7 (wz q) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (wz S) x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x4c5dc) fc None m (seg_rom asegs)).
  Proof.
    intros. pose proof BL as BL0. pose proof inv0 as IV.
    pose proof ECM as EC0.
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    - assert (K0 : k = 0) by lia.
      do 4 zstep.
      pose proof (fun y1 y5 y6 y7 y9 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31 =>
        L_ws (nblank LL) 0%nat m y1 y5 y6 y7 y9 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31 IV ltac:(lia) eq_refl ltac:(lia)) as HW.
      cbn [Z.of_nat] in HW. rewrite Z.add_0_r in HW. eapply HW.
    - zstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
      eapply L_size; [exact IV| exact HK].
  Qed.
End Tail.

Lemma atoi_i_spec : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (S : Z) (str : list byte) (errv canary : word) (lo q : Z),
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) ->
  rw_cells asegs m (bv_unsigned tp - 164) [C4 errv] ->
  rw_cells asegs m got_ssp [C8 (wz ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
  icpt_env m ->
  accessible m S (Z.of_nat (length str) + 1) -> sh_readable m S (Z.of_nat (length str) + 1) -> cwin S (Z.of_nat (length str) + 1) ->
  Z.of_nat (length str) + 1 <= 2^40 ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 2160 - 528 -> q < 2^63 ->
  bv_unsigned tp = 0x5e75b0 ->
  0x609000 <= S -> S + Z.of_nat (length str) + 1 <= lo -> S + Z.of_nat (length str) + 1 < 2^47 ->
  mem_inv asegs m -> a0 = wz S ->
  evt asegs (istrtol0_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_atoi) fc None m (seg_rom asegs)).
Proof.
  intros until q. intros STR ERR GOT CAN IE ACCS RDS WINS NSZ ST KLO LO Q63 TPV S1 S2 S3 MI ->.
  unfold A0_atoi. rewrite TPV in *. unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(lo, q); (6190348, 6190348 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO' : lo <= q - 2160) by lia.
  carve_frame 2160%nat ST.
  zstep. do 14 zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (SAFE : env_band_safe [(lo, q); (6190348, 6190348 + 4)]) by (repeat (constructor; [cbn; lia|]); constructor);
    pose proof (icpt_env_frame _ m m1 IE MU WM SAFE) as IE1 end.
  call ensure_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
  clear IE1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with MU' : munch _ m m1, WM' : wmono asegs m m1 |- _ =>
      pose proof (icpt_env_frame _ m m1 IE MU' WM' SAFE) as IE1 end end.
  pose proof (ie_cf _ IE1) as CF1. pose proof (ie_aflags _ IE1) as AF1. pose proof (ie_real_lib _ IE1) as (_ & _ & _ & RL1).
  unfold env_cf in CF1. unfold env_aflags in AF1.
  do 3 zstep. zstep. lit_branch.
  do 5 zstep. fix_lit_store. do 4 zstep.
  lazymatch type of FR with rw_cells _ ?mm _ (CB 2064 ?j0 :: C8 ?v :: ?rest) =>
    pose proof (proj1 (rw_cells_app asegs mm (q + -2160) [CB 2064 j0] (C8 v :: rest)) FR) as [FRL FR2];
    replace (q + -2160 + Z.of_nat (cells_size [CB 2064 j0])) with (q + -96) in FR2 by (cbn; lia);
    pose proof (proj1 (rw_cells_app asegs mm (q + -96) [C8 v] rest) FR2) as [FRE FRH];
    replace (q + -96 + Z.of_nat (cells_size [C8 v])) with (q + -88) in FRH by (cbn; lia);
    clear FR FR2 end.
  destruct (rw_cells_C8_CB _ _ _ _ FRE) as [ej FREB]. clear FRE.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (strtox_callq strtol_entry strtol_proof) with (lo := lo) (S := S) (str := str) (E := q + -96) (base := 10) (ejunk := ej) (canary := canary);
      rewrite ?TPV; unfold got_ssp, ssp_guard;
      first [ eassumption | lia | idtac ]
    | post_call asegs mm ] end.
  match goal with H : 0 <= ?kk <= Z.of_nat (length str) |- _ => rename kk into k; rename H into HK end.
  clear IE1 CF1 AF1 RL1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU' : munch _ m mm, WM' : wmono asegs m mm |- _ =>
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q); (6190348, 6190348 + 4)] s)
      by (intros s Hs; cbn [outside]; lia);
    pose proof (icpt_env_frame _ m mm IE MU' WM' SAFE) as IE1;
    assert (ACS1 : accessible mm S (Z.of_nat (length str) + 1)) by (eapply accessible_munch; [exact ACCS| exact MU'| exact WINS| intros s Hs; apply HO; lia]);
    assert (RDS1 : sh_readable mm S (Z.of_nat (length str) + 1)) by (eapply sh_readable_munch; [exact RDS| exact MU'| exact WINS| exact HO])
    end end.
  eapply evt_mono.
  { eapply (L_cmp ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc _ S lo k str); try eassumption; lia. }
  intros ms' Q. unfold atoi_tpost in Q. unfold istrtol0_post.
  destruct Q as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & EQ & MU' & WM' & MI' & ST' & STR').
  match goal with H : rw_cells asegs _ (bv_unsigned tp - 164) [C4 ?ev] |- _ =>
    exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m', ev; rewrite TPV in H end.
  split; [exact EQ|].
  split. { rewrite TPV. eapply munch_trans; [eassumption|]. eapply munch_weaken; [| exact MU']. unfold sub_fp; cbn [outside]; intros; lia. }
  split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact STR'|].
  rewrite TPV.
  unfold got_ssp, ssp_guard.
  split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU'| exact WM'| cbn [disjoint_from cells_size csize Nat.add]; lia]).
Qed.
