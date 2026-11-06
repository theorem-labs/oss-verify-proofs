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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit F_rip.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition A0_StrtolFix : Z := 0x565c8.

Definition is_blank (c : Z) : bool := ((9 <=? c) && (c <=? 13)) || (c =? 32).
Fixpoint nblank (l : list byte) : nat :=
  match l with b :: l' => if is_blank (bv_unsigned b) then Datatypes.S (nblank l') else O | [] => O end.
Definition fix_off (l : list byte) : Z :=
  match nth_error l (nblank l) with
  | Some b => if (bv_unsigned b =? 43) || (bv_unsigned b =? 45) then Z.of_nat (nblank l) + 1 else Z.of_nat (nblank l)
  | None => Z.of_nat (nblank l)
  end.
Lemma nblank_nul : forall str, (nblank (str ++ [Z_to_bv 8 0]) <= length str)%nat.
Proof. induction str as [|b str IH]; [vm_compute; lia|]. cbn [app nblank length]. destruct (is_blank (bv_unsigned b)); lia. Qed.
Lemma fix_off_range : forall str, 0 <= fix_off (str ++ [Z_to_bv 8 0]) <= Z.of_nat (length str).
Proof.
  intros str. unfold fix_off. pose proof (nblank_nul str) as H.
  destruct (nth_error (str ++ [Z_to_bv 8 0]) (nblank (str ++ [Z_to_bv 8 0]))) as [b|] eqn:E; [|lia].
  destruct ((bv_unsigned b =? 43) || (bv_unsigned b =? 45))%bool eqn:SG; [|lia].
  destruct (Nat.eq_dec (nblank (str ++ [Z_to_bv 8 0])) (length str)) as [EQ|NE]; [|lia].
  exfalso. rewrite EQ, nth_error_app2, Nat.sub_diag in E by lia. cbn in E. injection E as <-. vm_compute in SG. discriminate.
Qed.

Definition fixed_off (str : list byte) (k : Z) : Z := if k =? 0 then fix_off (str ++ [Z_to_bv 8 0]) else k.
Lemma fixed_off_range : forall str k, 0 <= k <= Z.of_nat (length str) -> 0 <= fixed_off str k <= Z.of_nat (length str).
Proof. intros str k Hk. unfold fixed_off. destruct (k =? 0); [apply fix_off_range| lia]. Qed.

Definition sfix_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str : list byte) (W : list (Z * Z)) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ((lo, q) :: W) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' S (str ++ [Z_to_bv 8 0]).

Definition sfix_tpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' S (str ++ [Z_to_bv 8 0]).

Section Tail.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (S lo k : Z) (str : list byte) (jk0 : list byte).
  Notation LEN := (Z.of_nat (length str)).
  Notation NS := (LEN + 1).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis FRM : rw_cells asegs m (q + -2144) [CB 2072 jk0; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis ST : stk asegs m lo (q + -2144).
  Hypothesis LO : lo <= q - 2144 - 80.
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

  Notation TPOST := (sfix_tpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str lo m).

  Definition INVX (mc : mem) : Prop :=
    (exists jk, rw_cells asegs mc (q + -2144) [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (q + -2144)
    /\ munch [(lo, q)] m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ bytes_at asegs mc S (str ++ [Z_to_bv 8 0]).
  Definition INV (mc : mem) : Prop := INVX mc /\ icpt_env mc.

  #[using="LO KLO Q64 WINS WIN2"] Lemma BL : 0 <= S /\ 0 <= LEN /\ S + NS < 2^47 /\ 0 <= lo /\ q < 2^64 /\ lo <= q - 2224 /\ 17594333495296 <= lo.
  Proof. destruct WINS as [_ W]. lia. Qed.

  Ltac invx_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & STR1).
  Ltac inv_open H :=
    let IX := fresh "IX" in
    destruct H as (IX & IEc); invx_open IX;
    pose proof (ie_shadow _ IEc) as (GOT1 & SHB1); pose proof (ie_layout _ IEc) as (LG1 & LC1).

  #[using="jk0 MI FRM ST IE STR"] Lemma inv0 : INV m.
  Proof. split; [| exact IE]. split; [eexists; exact FRM|]. split; [exact ST|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI| exact STR]. Qed.

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

  #[using="LO KLO Q64 WINS WIN2"] Lemma LX : forall mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INVX mc ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x56748) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. invx_open IV.
    do 12 zstep.
    release_frame FR ST1 q. finish.
  Qed.

  #[using="LO KLO Q64 WINS WIN2 ACCS RDS"] Lemma LWL : forall mc sz (j : nat) (cur : Z) x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc -> 1 <= sz <= 64 -> sz <= NS ->
    Z.to_nat (sh (S + sz - 1) - cur) = j -> sh S <= cur < sh (S + sz - 1) ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 (wz cur) (wz (2147450880 + Z.shiftr (S + sz + -1) 3)) (wz 0) x13 x14 x15 x16 x17
               (wz S) (wz sz) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x56804) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 NLE Hj Hc. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts_S mc sz (proj1 IV) ltac:(lia)) as (ACC1 & RDS1 & CW1). inv_open IV.
    revert cur x13 Hj Hc. induction j as [|j IH]; intros cur x13 Hj Hc; [exfalso; lia|].
    assert (SL : sh (S + sz - 1) = 2147450880 + Z.shiftr (S + sz + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (S + sz + -1) with (S + sz - 1) by lia; lia).
    pose proof (sh_div8 (S + sz - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc S sz cur ACC1 ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; exact (proj1 IV0).
  Qed.

  #[using="k LO KLO Q64 HK WINS WIN2 ACCS RDS"] Lemma LWS : forall mc sz x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc -> 1 <= sz <= 64 -> sz <= NS ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 (wz (2147450880 + Z.shiftr S 3)) (wz (2147450880 + Z.shiftr (S + sz + -1) 3)) (wz (S + sz + -1)) x13 x14 x15 x16 x17
               (wz S) (wz sz) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x567e8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 NLE. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts_S mc sz (proj1 IV) ltac:(lia)) as (ACC1 & RDS1 & CW1). inv_open IV.
    destruct (acc_byte_rd mc S sz (S + sz + -1) ACC1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((S + sz + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (S + sz + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; exact (proj1 IV0).
    - eapply LWL; [exact IV0 | assumption | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (S + sz - 1) with (S + sz + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= S / 8 < 2^44 /\ 0 <= (S + sz + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite ?Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="k LO KLO Q64 SEPS HK WINS WIN2 NSZ ACCS RDS"] Lemma LB : forall mc sz x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc -> 1 <= sz <= NS ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (wz S) (wz sz) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x566f8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV NLE. pose proof BL as BL0. pose proof IV as IV0.
    destruct (facts_S mc sz (proj1 IV) ltac:(lia)) as (ACC1 & RDS1 & CW1). inv_open IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
      assert (N65 : 64 < sz) by (clear - K2 K3 NLE NSZ; Z.div_mod_to_equations; lia).
      do 3 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct CW1 as [_ W]; unfold rwin; lia | exact ACC1 | lia |].
      zstep. lit_branch.
      eapply LX. unfold INVX. split; [eexists; eassumption|]. repeat (split; [eassumption|]). assumption.
    -
      assert (N1 : 1 <= sz <= 64) by (clear - K2 NLE NSZ; Z.div_mod_to_equations; lia).
      do 11 zstep.
      probe8_reg 13%Z RDS1 S w1 P1. probe8_reg 14%Z RDS1 (S + sz + -1) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS; [exact IV0| exact N1| lia].
      + eapply LX; exact (proj1 IV0).
  Qed.

  #[using="k LO KLO Q64 SEPS HK WINS WIN2 NSZ ACCS RDS"] Lemma L_size : forall mc off x1 x5 x6 x7 x9 x11 x12 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc -> 0 <= off <= LEN ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 (wz 1) x11 x12 (wz (S + off)) x14 x15 x16 x17
               (wz S) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x566c8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV Hoff. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    pose proof (ie_cf _ IEc) as CF1. pose proof (ie_flags _ IEc) as FL1. unfold env_cf in CF1. unfold env_flags in FL1.
    do 3 zstep. cbv beta. zsimp. zstep. lit_branch.
    do 4 zstep.
    replace (Z.land 18446744073709551615 (S + off - S + 1)) with (off + 1)
      by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small by lia; lia).
    eapply LB; [exact IV0| lia].
  Qed.

  #[using="str"] Lemma blank_code : forall c, 0 <= c < 256 -> is_blank c = (((c + -9) mod 18446744073709551616 <? 5) || (c =? 32))%bool.
  Proof.
    intros c Hc. unfold is_blank. f_equal.
    destruct (Z.leb_spec 9 c) as [H9|H9]; cbn [andb].
    - rewrite Z.mod_small by lia. destruct (Z.leb_spec c 13), (Z.ltb_spec (c + -9) 5); try reflexivity; lia.
    - replace ((c + -9) mod 18446744073709551616) with (c + -9 + 18446744073709551616) by (apply (Z.mod_unique _ _ (-1)); lia).
      destruct (Z.ltb_spec (c + -9 + 18446744073709551616) 5); [lia| reflexivity].
  Qed.

  Notation LL := (str ++ [Z_to_bv 8 0]).

  #[using="k LO KLO Q64 SEPS HK WINS WIN2 NSZ ACCS RDS"] Lemma L_ws : forall (n i : nat) mc x1 x5 x6 x7 x9 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc -> (i <= length str)%nat -> nblank (skipn i LL) = n -> (nblank LL = i + n)%nat ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 (wz 1) (wz 5) (wz 32) (wz (S + Z.of_nat i)) x14 x15 x16 x17
               (wz S) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x566a4) fc None mc (seg_rom asegs)).
  Proof.
    induction n as [|n IH]; intros until x31; intros IV Hi Hn Hnb; pose proof BL as BL0; pose proof IV as IV0; inv_open IV;
      (destruct (nth_error LL i) as [b|] eqn:Eb; [| exfalso; apply nth_error_None in Eb; rewrite length_app in Eb; cbn in Eb; lia]);
      pose proof (bv_unsigned_in_range 8 b) as Rb; unfold bv_modulus in Rb; cbn in Rb;
      pose proof (bytes_at_bound _ _ _ _ STR1) as BS; rewrite length_app in BS; cbn [length] in BS;
      pose proof (u8ro_read asegs mc S LL (Z.of_nat i) b (wz (S + Z.of_nat i)) STR1 ltac:(rewrite Nat2Z.id; exact Eb) ltac:(lia) eq_refl) as RDb;
      assert (SK : skipn i LL = b :: skipn (Datatypes.S i) LL) by (clear - Eb; revert i Eb; induction LL as [|x l IHl]; intros [|i] E; cbn in *; try discriminate; [injection E as ->; reflexivity | apply IHl; exact E]);
      rewrite SK in Hn; cbn [nblank] in Hn; pose proof (blank_code _ Rb) as BC.
    -
      destruct (is_blank (bv_unsigned b)) eqn:EB; [discriminate Hn|]. symmetry in BC. apply orb_false_iff in BC. destruct BC as [BC1 BC2].
      apply Z.ltb_ge in BC1. apply Z.eqb_neq in BC2.
      zstep. cbv beta. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
      zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
      assert (FO : fix_off LL = if ((bv_unsigned b =? 43) || (bv_unsigned b =? 45))%bool then Z.of_nat i + 1 else Z.of_nat i).
      { unfold fix_off. replace (nblank LL) with i by lia. rewrite Eb. reflexivity. }
      pose proof (fix_off_range str) as FR0.
      zstep. zstep. if_cases K3; zify_cond K3.
      + rewrite (proj2 (Z.eqb_eq _ _) K3) in FO. cbn [orb] in FO.
        zstep. replace (S + Z.of_nat i + 1) with (S + fix_off LL) by lia.
        eapply L_size; [exact IV0| lia].
      + zstep. zstep. if_cases K4; zify_cond K4.
        * rewrite (proj2 (Z.eqb_neq _ _) K3), (proj2 (Z.eqb_neq _ _) K4) in FO. cbn [orb] in FO.
          replace (S + Z.of_nat i) with (S + fix_off LL) by lia.
          eapply L_size; [exact IV0| lia].
        * rewrite (proj2 (Z.eqb_eq _ _) K4), orb_true_r in FO.
          zstep. replace (S + Z.of_nat i + 1) with (S + fix_off LL) by lia.
          eapply L_size; [exact IV0| lia].
    -
      destruct (is_blank (bv_unsigned b)) eqn:EB; [| discriminate Hn]. injection Hn as Hn.
      assert (ILT : (i < length str)%nat).
      { destruct (Nat.eq_dec i (length str)) as [EQ|]; [|lia]. exfalso. rewrite EQ, nth_error_app2, Nat.sub_diag in Eb by lia. cbn in Eb. injection Eb as <-. vm_compute in EB. discriminate. }
      symmetry in BC. apply orb_true_iff in BC.
      zstep. cbv beta. zstep. zstep. if_cases K1; zify_cond K1.
      + zstep. replace (S + Z.of_nat i + 1) with (S + Z.of_nat (Datatypes.S i)) by lia.
        eapply IH; [exact IV0| lia| exact Hn| lia].
      + zstep. if_cases K2; zify_cond K2.
        * zstep. replace (S + Z.of_nat i + 1) with (S + Z.of_nat (Datatypes.S i)) by lia.
          eapply IH; [exact IV0| lia| exact Hn| lia].
        * exfalso. destruct BC as [BC|BC]; [apply Z.ltb_lt in BC; lia | apply Z.eqb_eq in BC; lia].
  Qed.

  #[using="LO KLO Q64 SEPS HK WINS WIN2 NSZ ACCS RDS"] Lemma L_base : forall mc base x1 x5 x6 x7 x9 x10 x11 x12 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc -> (base = 10 \/ base = 16) ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 x10 x11 x12 (wz (S + k)) (wz base) x15 x16 x17
               (wz S) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x56650) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV HB. pose proof BL as BL0.
    assert (CONT : forall y11 y14 : word,
      evt asegs TPOST
        (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 (wz 1) y11 x12 (wz (S + k)) y14 x15 x16 x17
                 (wz S) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz 0x56664) fc None mc (seg_rom asegs))).
    { intros y11 y14. clear HB.
      zstep. if_cases K1; zify_cond K1.
      - assert (K0 : k = 0) by lia.
        do 4 zstep.
        pose proof (fun y1 y5 y6 y7 y9 z14 y15 y16 y17 y19 y20 y21 y22 y23 y28 y29 y30 y31 =>
          L_ws (nblank LL) 0%nat mc y1 y5 y6 y7 y9 z14 y15 y16 y17 y19 y20 y21 y22 y23 y28 y29 y30 y31 IV ltac:(lia) eq_refl ltac:(lia)) as HW.
        cbn [Z.of_nat] in HW. rewrite Z.add_0_r in HW. eapply HW.
      - zstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
        eapply L_size; [exact IV| exact HK]. }
    destruct HB as [-> | ->]; do 4 zstep; zstep; lit_branch; eapply CONT.
  Qed.

  #[using="jk0 MI FRM ST LO KLO Q64 IE STR SEPS HK WINS WIN2 NSZ ACCS RDS"] Lemma sfix_tail : forall base x1 x5 x6 x7 x9 x10 x11 x12 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    (base = 10 \/ base = 16) ->
    evt asegs TPOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 x10 x11 x12 (wz (S + k)) (wz base) x15 x16 x17
               (wz S) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x56650) fc None m (seg_rom asegs)).
  Proof. intros. eapply L_base; [exact inv0 | assumption]. Qed.
End Tail.

Lemma sfix0_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (S k base lo : Z) (str : list byte),
  mem_inv asegs m -> stk asegs m lo q -> lo <= q - 2144 - 80 -> 0x10007fff8000 <= lo -> q < 2^64 -> icpt_env m ->
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) -> (S + (Z.of_nat (length str) + 1) <= lo \/ q <= S) -> 0 <= k <= Z.of_nat (length str) ->
  cwin S (Z.of_nat (length str) + 1) -> S + (Z.of_nat (length str) + 1) < 2^47 -> Z.of_nat (length str) + 1 <= 2^43 ->
  accessible m S (Z.of_nat (length str) + 1) -> sh_readable m S (Z.of_nat (length str) + 1) ->
  (base = 10 \/ base = 16) -> a1 = wz S -> a2 = wz 0 -> a3 = wz (S + k) -> a4 = wz base ->
  evt asegs (sfix_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str [] lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_StrtolFix) fc None m (seg_rom asegs)).
Proof.
  intros until str. intros MI ST LO KLO Q64 IE STR SEPS HK WINS WIN2 NSZ ACCS RDS HB -> -> -> ->. unfold A0_StrtolFix.
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (BS : 0 <= S) by (destruct WINS as [_ W]; lia).
  assert (LO' : lo <= q - 2144) by lia.
  carve_frame 2144%nat ST.
  do 12 zstep. do 4 zstep. zstep. lit_branch.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia);
    pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1;
    assert (ACS1 : accessible m1 S (Z.of_nat (length str) + 1)) by (eapply accessible_munch; [exact ACCS| exact MU| exact WINS| intros s Hs; apply HO; lia]);
    assert (RDS1 : sh_readable m1 S (Z.of_nat (length str) + 1)) by (eapply sh_readable_munch; [exact RDS| exact MU| exact WINS| exact HO])
  end.
  eapply evt_mono.
  { eapply (sfix_tail ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc _ S lo k str); try eassumption; lia. }
  intros ms' Q. unfold sfix_tpost in Q. unfold sfix_post.
  destruct Q as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MU' & WM' & MI' & ST' & STR').
  exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m'.
  split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact ST'| exact STR'].
Qed.

Definition sfixE_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str : list byte) (E k : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q); (E, E + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' S (str ++ [Z_to_bv 8 0])
    /\ rw_cells asegs m' E [C8 (wz (S + k))].

Lemma sfixE_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (S k base lo E : Z) (str ejunk : list byte),
  mem_inv asegs m -> stk asegs m lo q -> lo <= q - 2144 - 80 -> 0x10007fff8000 <= lo -> q < 2^64 -> icpt_env m ->
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) -> (S + (Z.of_nat (length str) + 1) <= lo \/ q <= S) -> 0 <= k <= Z.of_nat (length str) ->
  cwin S (Z.of_nat (length str) + 1) -> S + (Z.of_nat (length str) + 1) < 2^47 -> Z.of_nat (length str) + 1 <= 2^43 ->
  accessible m S (Z.of_nat (length str) + 1) -> sh_readable m S (Z.of_nat (length str) + 1) ->
  rw_cells asegs m E [CB 8 ejunk] -> accessible m E 8 -> sh_readable m E 8 -> cwin E 8 -> E + 8 < 2^47 -> E mod 8 = 0 ->
  0x147000 <= E -> (E + 8 <= lo \/ q <= E) -> (E + 8 <= S \/ S + (Z.of_nat (length str) + 1) <= E) ->
  (base = 10 \/ base = 16) -> a1 = wz S -> a2 = wz E -> a3 = wz (S + k) -> a4 = wz base ->
  evt asegs (sfixE_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str E k lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_StrtolFix) fc None m (seg_rom asegs)).
Proof.
  intros until ejunk. intros MI ST LO KLO Q64 IE STR SEPS HK WINS WIN2 NSZ ACCS RDS EC ACCE RDE WINE WINE2 EAL EBAND SEPE SEPES HB -> -> -> ->.
  unfold A0_StrtolFix.
  pose proof (munch_refl [(lo, q); (E, E + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (BS : 0 <= S) by (destruct WINS as [_ W]; lia).
  assert (LO' : lo <= q - 2144) by lia.
  carve_frame 2144%nat ST.
  do 12 zstep. do 4 zstep. zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
  zstep. zstep.
  zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with MU' : munch _ m m1, WM' : wmono asegs m m1 |- _ =>
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q); (E, E + 8)] s) by (intros s Hs; destruct WINE as [_ WE]; cbn [outside]; lia);
    assert (IE1 : icpt_env m1) by (eapply icpt_env_frame; [exact IE| exact MU'| exact WM'| constructor; [cbn; lia| constructor; [cbn; lia| constructor]]]);
    assert (ACS1 : accessible m1 S (Z.of_nat (length str) + 1)) by (eapply accessible_munch; [exact ACCS| exact MU'| exact WINS| intros s Hs; apply HO; lia]);
    assert (RDS1 : sh_readable m1 S (Z.of_nat (length str) + 1)) by (eapply sh_readable_munch; [exact RDS| exact MU'| exact WINS| exact HO]);
    assert (ACE1 : accessible m1 E 8) by (eapply accessible_munch; [exact ACCE| exact MU'| exact WINE| intros s Hs; apply HO; lia]);
    assert (RDE1 : sh_readable m1 E 8) by (eapply sh_readable_munch; [exact RDE| exact MU'| exact WINE| exact HO])
  end end.
  pose proof (ie_shadow _ IE1) as (GOT1 & SHB1).
  assert (BE : 0 <= E) by (destruct WINE as [_ WE]; lia).
  do 10 zstep.
  probe8_reg 16%Z RDE1 E w1 P1. probe8_reg 17%Z RDE1 (E + 7) w2 P2.
  do 4 zstep.
  assert (TAIL : forall x1 x5 x6 x7 x9 x10 x11 x12 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    evt asegs (sfixE_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str E k lo m)
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 x10 x11 x12 (wz (S + k)) (wz base) x15 x16 x17
               (wz S) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x56650) fc None m1 (seg_rom asegs))).
  { intros.
    eapply evt_mono.
    { eapply (sfix_tail ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 S lo k str); try eassumption; lia. }
    intros ms' Q. unfold sfix_tpost in Q. unfold sfixE_post.
    destruct Q as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & EQ & MU' & WM' & MI' & ST' & STR').
    exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m'.
    split; [exact EQ|].
    split. { eapply munch_trans; [eassumption|]. eapply munch_weaken; [| exact MU']. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact STR'|].
    eapply rw_cells_transport; [exact EC| exact MU'| exact WM'| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  if_cases K5; zify_cond K5; [| eapply TAIL].

  destruct (acc_byte_rd m1 E 8 (E + 7) ACE1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
  unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
  zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
  rewrite land7_mod8. rewrite (aip_zero ((E + 7) mod 8) k2) by (pose proof (Z.mod_pos_bound (E + 7) 8 ltac:(lia)); lia).
  zstep. if_cases K6; zify_cond K6.
  2:{ exfalso. rewrite !shiftr3_div in K6. assert (E / 8 = (E + 7) / 8) by (Z.div_mod_to_equations; lia).
      assert (0 <= E / 8 < 2^44) by (Z.div_mod_to_equations; lia). rewrite ?Z.mod_small in K6 by lia. lia. }
  zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
  eapply TAIL.
Qed.
