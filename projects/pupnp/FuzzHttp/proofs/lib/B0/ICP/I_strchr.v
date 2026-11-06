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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit IcptKit2 F_rip F_gates F_irt I_printf_front M_strchrnul M_strchrZ.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition A0_strchr_i : Z := 0x44120.

Definition env_real_strchr (m : mem) : Prop := rw_cells asegs m 0xaca70 [C8 (wz 0xa2f78)].

Definition istrchr_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S c : Z) (str slack : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack)
    /\ strchr_res S str c r.

Section Proofs.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (S c lo : Z) (str slack : list byte).
  Notation L := (Z.of_nat (length str)).
  Hypothesis LO : lo <= q - 2144 - 80.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : (- (S + L + 1)) mod 8 <= Z.of_nat (length slack).
  Hypothesis SEPS : S + L + 1 + Z.of_nat (length slack) <= lo \/ q <= S.
  Hypothesis WIN : cwin S (L + 1).
  Hypothesis WIN2 : S + L + 1 < 2^47.
  Hypothesis ACC : accessible m S (L + 1).
  Hypothesis RDB : sh_readable m S (L + 1).
  Hypothesis NSZ : L + 1 <= 2^43.
  Hypothesis CR : 0 < c < 256.

  Notation APOST := (istrchr_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S c str slack lo m).

  Definition INVX (mc : mem) : Prop :=
    (exists jk, rw_cells asegs mc (q + -2144) [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (q + -2144)
    /\ munch [(lo, q)] m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ bytes_at asegs mc S (str ++ Z_to_bv 8 0 :: slack).
  Definition INV (mc : mem) : Prop :=
    INVX mc /\ env_shadow mc /\ env_layout mc /\ accessible mc S (L + 1) /\ sh_readable mc S (L + 1).

  #[using="slack LO KLO Q64 WIN WIN2"] Lemma BL : 0 <= S /\ 0 <= L /\ S + L + 1 < 2^47 /\ 0 <= lo /\ q < 2^64 /\ lo <= q - 2224 /\ 17594333495296 <= lo.
  Proof. destruct WIN as [Hn W]. lia. Qed.

  Ltac invx_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & STR1).
  Ltac inv_open H :=
    let IX := fresh "IX" in
    destruct H as (IX & (GOT1 & SHB1) & (LG1 & LC1) & ACC1 & RDB1); invx_open IX.

  #[using="LO KLO Q64 WIN WIN2 ACC RDB"] Lemma inv_of : forall mc jk,
    rw_cells asegs mc (q + -2144) [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (q + -2144) -> munch [(lo, q)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    bytes_at asegs mc S (str ++ Z_to_bv 8 0 :: slack) -> icpt_env mc ->
    INV mc.
  Proof.
    intros mc jk FR ST1 MU1 WM1 MI1 STR1 IE1. pose proof BL as BL0.
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia).
    split; [split; [exists jk; exact FR|]; repeat (split; [assumption|]); assumption|].
    split; [exact (ie_shadow _ IE1)|]. split; [exact (ie_layout _ IE1)|].
    split; [eapply accessible_munch; [exact ACC| exact MU1| exact WIN| intros s Hs; apply HO; lia]|].
    eapply sh_readable_munch; [exact RDB| exact MU1| exact WIN| exact HO].
  Qed.

  Section Range.
  Variables (r k : Z).
  Hypothesis RES : strchr_res S str c r.
  Hypothesis KR : 0 <= k <= L.

  #[using="LO KLO Q64 WIN WIN2 RES"] Lemma LX : forall mc x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INVX mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 x8 x9 (wz r) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x45e08) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. invx_open IV.
    do 12 zstep.
    release_frame FR ST1 q. unfold istrchr_post. finish.
  Qed.

  #[using="q lo str slack LO KLO WIN WIN2 ACC RDB KR"] Lemma SUBR : accessible m S (k + 1) /\ sh_readable m S (k + 1) /\ cwin S (k + 1).
  Proof.
    destruct WIN as [Hn W]. split; [eapply accessible_sub; [exact ACC| lia| lia]|].
    split; [eapply sh_readable_sub; [exact RDB| lia| lia| lia]|]. split; lia.
  Qed.

  #[using="LO KLO Q64 WIN WIN2 RES KR"] Lemma LWL : forall mc (j : nat) (cur : Z) x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc -> 1 <= k + 1 <= 64 ->
    Z.to_nat (sh (S + (k + 1) - 1) - cur) = j -> sh S <= cur < sh (S + (k + 1) - 1) ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 x8 x9 (wz r) (wz cur) (wz (2147450880 + Z.shiftr (k + S) 3)) (wz 0) x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x45ec8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    assert (ACCk : accessible mc S (k + 1)) by (eapply accessible_sub; [exact ACC1| lia| lia]).
    revert cur x14 Hk Hc. induction j as [|j IH]; intros cur x14 Hk Hc; [exfalso; lia|].
    assert (SL : sh (S + (k + 1) - 1) = 2147450880 + Z.shiftr (k + S) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (S + (k + 1) - 1) with (k + S) by lia; lia).
    pose proof (sh_div8 (S + (k + 1) - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc S (k + 1) cur ACCk ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX. exact (proj1 IV0).
  Qed.

  #[using="LO KLO Q64 WIN WIN2 RES KR"] Lemma LWS : forall mc x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc -> 1 <= k + 1 <= 64 ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 x8 x9 (wz r) (wz (2147450880 + Z.shiftr S 3)) (wz (2147450880 + Z.shiftr (k + S) 3)) x13 x14 x15 x16 x17
               x18 (wz (k + S)) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x45eac) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    assert (ACCk : accessible mc S (k + 1)) by (eapply accessible_sub; [exact ACC1| lia| lia]).
    destruct (acc_byte_rd mc S (k + 1) (k + S) ACCk ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((k + S) mod 8) k2) by (pose proof (Z.mod_pos_bound (k + S) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX. exact (proj1 IV0).
    - eapply LWL; [exact IV0 | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (S + (k + 1) - 1) with (k + S) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= S / 8 < 2^44 /\ 0 <= (k + S) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite !Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 SEPS WIN WIN2 NSZ RES KR"] Lemma LB : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2144)) gp tp x5 x6 x7 (wz q) x9 (wz r) x11 x12 x13 x14 x15 x16 x17
               (wz S) (wz k) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x45db4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    assert (ACCk : accessible mc S (k + 1)) by (eapply accessible_sub; [exact ACC1| lia| lia]).
    assert (RDk : sh_readable mc S (k + 1)) by (eapply sh_readable_sub; [exact RDB1| lia| lia| lia]).
    zstep. zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
      do 4 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct WIN as [_ W]; unfold rwin; lia | exact ACCk | lia |].
      do 3 zstep. lit_branch.
      eapply LX. unfold INVX. split; [eexists; eassumption|]. repeat (split; [eassumption|]). assumption.
    -
      assert (N1 : 1 <= k + 1 <= 64) by lia.
      do 10 zstep.
      probe8_regx 13%Z RDk S w1 P1. probe8_regx 14%Z RDk (k + S) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS; eassumption.
      + eapply LX; exact (proj1 IV0).
  Qed.
  End Range.

  #[using="LO KLO Q64 NONUL PAD SEPS WIN WIN2 ACC RDB NSZ CR"] Lemma istrchr_body : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    mem_inv asegs m -> stk asegs m lo q -> icpt_env m -> env_real_strchr m -> bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) ->
    evt asegs APOST (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz A0_strchr_i) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros MI ST IE RSC STR. unfold A0_strchr_i. unfold env_real_strchr in RSC. pose proof BL as BL0.
    pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO' : lo <= q - 2144) by lia.
    pose proof STR as STR0. ihide STR0. clear STR.
    zstep.
    carve_frame 2144%nat ST.
    do 14 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1 end.
    zstep.
    call inited_spec; [assumption | exact (ie_inited _ IE1) |].
    zstep. lit_branch. zstep.
    call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
    clear IE1.
    do 6 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (STR1 : bytes_at asegs mm S (str ++ Z_to_bv 8 0 :: slack))
        by (iunhide STR0; eapply bytes_at_transport; [exact STR0| exact MU| cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]);
      eapply evt_cut;
      [ eapply strchr_specZ with (lo := lo) (S := S) (c := c) (str := str) (slack := slack);
        [ exact STR1 | exact NONUL | exact PAD | eassumption | lia | lia | assumption | lia | lia | exact CR ]
      | post_call asegs mm ] end.
    lazymatch goal with H : strchr_res S str c ?rr |- _ => rename H into RES; rename rr into r end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
        pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1 end end.
    pose proof (ie_cf _ IE1) as CF1. pose proof (ie_flags _ IE1) as FL1. unfold env_cf in CF1. unfold env_flags in FL1.
    zstep. lit_branch. do 3 zstep.
    cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    zstep. cbv beta. zsimp. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1. cbv in K1. lia. }
    assert (RB : r = 0 \/ S <= r < S + L) by (unfold strchr_res in RES; destruct RES as [E|[[E _]|[E _]]]; lia).
    zstep. if_cases K2; zify_cond K2.
    -
      do 3 zstep.
      lazymatch goal with STRc : bytes_at asegs ?mm S _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply istrlen_spec with (str := str) (rest := slack); [ assumption | rewrite unsigned_lit by lia; exact STRc | apply noz_of_notin; exact NONUL ]
        | post_call asegs mm ] end.
      zstep. zstep.
      eapply LB with (r := r) (k := L); [exact RES | lia |].
      match goal with P : stk asegs _ lo (q + -2144) |- _ => eapply inv_of; [ eassumption | exact P | eassumption | eassumption | eassumption | eassumption | exact IE1 ] end.
    -
      zstep. zstep.
      eapply LB with (r := r) (k := r - S); [exact RES | lia |].
      match goal with P : stk asegs _ lo (q + -2144) |- _ => eapply inv_of; [ eassumption | exact P | eassumption | eassumption | eassumption | eassumption | exact IE1 ] end.
  Qed.
End Proofs.

Lemma strchr_i_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (S c : Z) (str slack : list byte) (lo : Z),
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  accessible m S (Z.of_nat (length str) + 1) -> sh_readable m S (Z.of_nat (length str) + 1) ->
  icpt_env m -> env_real_strchr m -> cwin S (Z.of_nat (length str) + 1) -> S + Z.of_nat (length str) + 1 < 2^47 -> Z.of_nat (length str) + 1 <= 2^43 ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 2224 -> q < 2^64 ->
  (S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ q <= S) ->
  mem_inv asegs m -> 0 < c < 256 -> a0 = wz S -> a1 = wz c ->
  evt asegs (istrchr_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S c str slack lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_strchr_i) fc None m (seg_rom asegs)).
Proof. intros. subst a0 a1. eapply istrchr_body; try eassumption. lia. Qed.
