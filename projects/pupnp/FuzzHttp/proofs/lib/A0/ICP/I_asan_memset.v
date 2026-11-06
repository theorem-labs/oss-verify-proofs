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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit F_rip M_memsetZ.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition amemset_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P c n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(P, P + n); (lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ rw_cells asegs m' P [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].

Section Proofs.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (P c n lo : Z) (junk : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo q.
  Hypothesis LO : lo <= q - 2128 - 80.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Hypothesis IE : icpt_env m.
  Hypothesis DST : rw_cells asegs m P [CB (Z.to_nat n) junk].
  Hypothesis SEPD : P + n <= lo \/ q <= P.
  Hypothesis WIN : cwin P n.
  Hypothesis WIN2 : P + n < 2^47.
  Hypothesis ACC : accessible m P n.
  Hypothesis RDB : sh_readable m P n.
  Hypothesis NSZ : n <= 2^43.
  Hypothesis RC : 0 <= c < 256.

  Notation APOST := (amemset_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P c n lo m).

  Definition INVX (mc : mem) : Prop :=
    (exists jk, rw_cells asegs mc (q + -2128) [CB 2072 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (q + -2128)
    /\ munch [(lo, q)] m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ env_real_mem mc
    /\ rw_cells asegs mc P [CB (Z.to_nat n) junk].
  Definition INV (mc : mem) : Prop :=
    INVX mc /\ env_shadow mc /\ env_layout mc /\ accessible mc P n /\ sh_readable mc P n.

  #[using="c LO KLO Q64 WIN WIN2 RC"] Lemma BL : 0 <= P /\ 0 <= n /\ P + n < 2^47 /\ 0 <= lo /\ q < 2^64 /\ lo <= q - 2208 /\ 17594333495296 <= lo.
  Proof. destruct WIN as [Hn W]. lia. Qed.

  Ltac invx_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & REAL1 & DST1); unfold env_real_mem in REAL1.
  Ltac inv_open H :=
    let IX := fresh "IX" in
    destruct H as (IX & (GOT1 & SHB1) & (LG1 & LC1) & ACC1 & RDB1); invx_open IX.

  #[using="LO KLO Q64 SEPD WIN WIN2 NSZ RC"] Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INVX mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2128)) gp tp x5 x6 x7 (wz q) x9 (wz P) (wz c) (wz n) x13 x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x56fd8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. invx_open IV.
    apply (munch_weaken _ [(P, P + n); (lo, q)]) in MU1; [| unfold sub_fp; cbn [outside]; intros; lia].
    zstep. zstep. zstep.
    clear REAL1.
    call memset_specZ; [ exact DST1 | exact MI1 | lia | lia | lia |].
    do 10 zstep.
    release_frame FR ST1 q. finish.
  Qed.

  #[using="LO KLO Q64 SEPD WIN WIN2 NSZ RC"] Lemma LWL : forall mc (k : nat) (cur : Z) x1 x5 x6 x7 x9 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mc -> 1 <= n <= 64 ->
    Z.to_nat (sh (P + n - 1) - cur) = k -> sh P <= cur < sh (P + n - 1) ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2128)) gp tp x5 x6 x7 (wz q) x9 (wz P) (wz c) (wz n)
               (wz cur) (wz (2147450880 + Z.shiftr (P + n + -1) 3)) (wz 0) x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x57104) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    revert cur x16 Hk Hc. induction k as [|k IH]; intros cur x16 Hk Hc; [exfalso; lia|].
    assert (SL : sh (P + n - 1) = 2147450880 + Z.shiftr (P + n + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (P + n + -1) with (P + n - 1) by lia; lia).
    pose proof (sh_div8 (P + n - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc P n cur ACC1 ltac:(lia) ltac:(lia))) as RDc.
    zstep.
    cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX. exact (proj1 IV0).
  Qed.

  #[using="LO KLO Q64 SEPD WIN WIN2 NSZ RC"] Lemma LWS : forall mc x1 x5 x6 x7 x9 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mc -> 1 <= n <= 64 ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2128)) gp tp x5 x6 x7 (wz q) x9 (wz P) (wz c) (wz n)
               (wz (2147450880 + Z.shiftr P 3)) (wz (2147450880 + Z.shiftr (P + n + -1) 3)) (wz (P + n + -1)) x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x570e8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    destruct (acc_byte_rd mc P n (P + n + -1) ACC1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((P + n + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (P + n + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX. exact (proj1 IV0).
    - eapply LWL; [exact IV0 | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (P + n - 1) with (P + n + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= P / 8 < 2^44 /\ 0 <= (P + n + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite !Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 SEPD WIN WIN2 NSZ RC"] Lemma LB : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2128)) gp tp x5 x6 x7 (wz q) x9 (wz P) (wz c) (wz n) x13 x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x56f80) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LX; exact (proj1 IV0). }
      assert (N65 : 64 < n) by (clear - K2 K3 BL0; Z.div_mod_to_equations; lia).
      do 5 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct WIN as [_ W]; unfold rwin; lia | exact ACC1 | lia |].
      do 5 zstep. lit_branch.
      eapply LX. unfold INVX. split; [eexists; eassumption|]. repeat (split; [eassumption|]). assumption.
    -
      assert (N1 : 1 <= n <= 64) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      probe8_reg 16%Z RDB1 P w1 P1. probe8_reg 17%Z RDB1 (P + n + -1) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS; eassumption.
      + eapply LX; exact (proj1 IV0).
  Qed.

  #[using="junk MI ST LO KLO Q64 IE DST SEPD WIN WIN2 ACC RDB NSZ RC"] Lemma amemset_body : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6, a0 = wz P -> a1 = wz c -> a2 = wz n ->
    evt asegs APOST (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz A0_asan_memset) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros -> -> ->. unfold A0_asan_memset. pose proof BL as BL0.
    pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO' : lo <= q - 2128) by lia.
    pose proof ST as ST0. ihide DST.
    carve_frame 2128%nat ST0.
    do 10 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1;
      assert (ACC1 : accessible m1 P n) by (eapply accessible_munch; [exact ACC| exact MU| exact WIN| intros s Hs; cbn [outside]; lia]);
      assert (RDB1 : sh_readable m1 P n) by (eapply sh_readable_munch; [exact RDB| exact MU| exact WIN| intros s Hs; cbn [outside]; lia]);
      assert (DST1 : rw_cells asegs m1 P [CB (Z.to_nat n) junk])
        by (iunhide DST; eapply rw_cells_transport; [exact DST| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia])
    end.
    pose proof (ie_inited _ IE1) as INI1. pose proof (ie_ric _ IE1) as RIC1. unfold env_inited in INI1. unfold env_ric in RIC1.
    do 3 zstep.
    cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    eapply LB. split; [| split; [exact (ie_shadow _ IE1)| split; [exact (ie_layout _ IE1)| split; [exact ACC1| exact RDB1]]]].
    split; [eexists; exact FR|]. split; [exact ST0|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact (ie_real_mem _ IE1)| exact DST1].
  Qed.
End Proofs.

Lemma asan_memset_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (P c n lo : Z) (junk : list byte),
  rw_cells asegs m P [CB (Z.to_nat n) junk] -> accessible m P n -> sh_readable m P n ->
  icpt_env m -> cwin P n -> P + n < 2^47 -> n <= 2^43 ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 2208 -> q < 2^64 ->
  (P + n <= lo \/ q <= P) ->
  mem_inv asegs m -> a0 = wz P -> a1 = wz c -> a2 = wz n -> 0 <= c < 256 ->
  evt asegs (amemset_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P c n lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_asan_memset) fc None m (seg_rom asegs)).
Proof. intros. eapply amemset_body; try eassumption. lia. Qed.
