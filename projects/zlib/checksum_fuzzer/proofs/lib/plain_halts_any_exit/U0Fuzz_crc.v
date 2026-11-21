(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem U0FuzzBase U0Fuzz_code U0FuzzIface FuzzCrcLib FuzzCrcLibU
  U0Fuzz_crcA U0Fuzz_crcB U0Fuzz_crcC U0Fuzz_crcD.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.cks Require Import CkTables CkModel CkMathCrc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque ctab btab crc_byte.

#[local] Abbreviation W8 v := (word_to_le_bytes 8 v).


Section BODY.
Context {RCa1 : RunCtx}.
  Variables (m rom : word -> option byte) (BA : Z -> Z) (adr0 len0 spv : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hba : forall a, adr0 <= a < adr0 + len0 -> byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m a = BA a.
  Hypothesis BA_rng : forall a, 0 <= BA a < 256.
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.
  Hypothesis Hl0 : 0 <= len0.
  Hypothesis Hst : store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 spv) 8 = true.
  Hypothesis Hspv : 0 <= spv /\ spv + 8 <= two64.
  Hypothesis Hro : spv + 8 <= RO_LO \/ RO_HI <= spv.
  Hypothesis Hap : 1 <= len0 -> adr0 + len0 <= spv.

  Ltac solve_kb := first [ assumption | apply lkeeps_refl | solve_lkeeps
                         | eapply lkeeps_trans; [eassumption | solve_kb] ].
  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_kb ].

  Definition MS (q : Z) : word -> option byte := wbytes m (Z_to_bv 64 spv) (W8 (Z_to_bv 64 q)).

  Lemma MS_img : forall q, img_ok (MS q).
  Proof.
    intros q. unfold MS. apply img_ok_wbytes; [exact Himg | |]; rewrite lenW8; change (Z.of_nat 8) with 8%Z; u_norm; lia.
  Qed.

  Lemma MS_rd : forall q i, 0 <= i < len0 -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (MS q) (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Proof. intros q. unfold MS. apply (readable_grows (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m). apply wbytes_grows. exact Hrd. Qed.

  Lemma MS_ba : 1 <= len0 -> forall q a, adr0 <= a < adr0 + len0 -> byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (MS q) a = BA a.
  Proof.
    intros Hl q a Ha. unfold MS. rewrite <- (Hba a Ha). apply byte_at_ext.
    apply wbytes_outside; rewrite lenW8; change (Z.of_nat 8) with 8%Z; [|u_norm; lia].
    unfold in_rng. u_norm. specialize (Hap Hl). lia.
  Qed.

  Lemma MS_ld : forall q, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (MS q) (Z_to_bv 64 spv) 8 = Some (W8 (Z_to_bv 64 q)).
  Proof. intros q. unfold MS. apply rdn_wbytes_hit8. u_norm. lia. Qed.

  Definition crcT (c : Z) : Z :=
    let '(cT, aT, nT) := tail_entry BA adr0 len0 c in crc_bytes cT (bl BA aT (Z.to_nat nT)).


  Lemma ucrcT_model : forall c, Z.lxor (crcT c) M32 = crc32_z_model adr0 c (bl BA adr0 (Z.to_nat len0)).
  Proof.
    intros c. unfold crcT. rewrite (crc32_z_bridge BA BA_rng) by exact Hl0.
    destruct (tail_entry BA adr0 len0 c) as [[cT aT] nT]. reflexivity.
  Qed.

  Lemma ubody_run : forall regs (c : Z),
    getr regs 14 = Z_to_bv 64 (crc_pre c) -> getr regs 10 = Z_to_bv 64 CTAB ->
    getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 len0 -> getr regs 13 = Z_to_bv 64 23 ->
    getr regs 2 = Z_to_bv 64 spv ->
    exists r m', msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x145bc : word) m rom) (mkst r (0x14c98 : word) m' rom)
      /\ getr r 14 = Z_to_bv 64 (crcT c)
      /\ lkeeps UKB regs r
      /\ (m' = m \/ exists q, m' = MS q).
  Proof.
    intros regs c R14 R10 R11 R12 R13 R2.
    pose proof (crc_pre_range32 c) as Hc0. unfold crcT, tail_entry.
    destruct (Z.ltb_spec len0 23) as [Hs | Hb].
    -
      assert (PRE : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x145bc : word) m rom) (mkst r (0x14ae8 : word) m rom)
               /\ (getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 adr0 /\ getr r 14 = Z_to_bv 64 (crc_pre c)
                   /\ getr r 12 = Z_to_bv 64 len0 /\ lkeeps UKB regs r)).
      { eexists. split.
        - stepb_tk F_1455c D_1455c ltac:(zcond).
          apply mst_refl.
        - post. }
      destruct PRE as (r1 & M1 & S10 & S11 & S14 & S12 & K1).
      destruct (tailu_run m rom BA adr0 len0 Himg Hrd Hba Hnw Ha0 r1 (crc_pre c) adr0 len0 S10 S11 S14 S12 Hc0
                  ltac:(lia) ltac:(lia) Hl0) as (r2 & M2 & T14 & K2).
      exists r2, m. split; [eapply msteps_trans; [exact M1 | exact M2]|]. split; [exact T14|]. split; [solve_kb | left; reflexivity].
    -
      pose proof (align4_range adr0) as Hna. set (na := align4 adr0) in *.
      assert (PRE : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x145bc : word) m rom) (mkst r (0x145c0 : word) m rom)
               /\ (getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 adr0 /\ getr r 12 = Z_to_bv 64 len0
                   /\ getr r 14 = Z_to_bv 64 (crc_pre c) /\ getr r 2 = Z_to_bv 64 spv /\ lkeeps UKB regs r)).
      { eexists. split.
        - stepb_ft F_1455c D_1455c ltac:(zcond).
          apply mst_refl.
        - post. }
      destruct PRE as (r1 & M1 & S10 & S11 & S12 & S14 & S2 & K1).
      destruct (ual_run m rom BA adr0 len0 Himg Hrd Hba Hnw Ha0 r1 (crc_pre c) adr0 len0 S10 S11 S12 S14 Hc0
                  ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & M2 & T10 & T11 & T5 & T12 & T14 & K2).
      fold na in T11, T5, T12, T14.
      set (c1 := crc_bytes (crc_pre c) (bl BA adr0 (Z.to_nat na))) in *.
      assert (Hc1 : 0 <= c1 < two32) by (subst c1; apply crc_bytes_range; exact Hc0).
      set (a1 := adr0 + na) in *. set (n1 := len0 - na) in *.
      assert (Hal : a1 mod 4 = 0).
      { subst a1 na. unfold align4. pose proof (Z.mod_pos_bound adr0 4 ltac:(lia)).
        rewrite <- Z.add_mod_idemp_l by lia.
        assert (C : adr0 mod 4 = 0 \/ adr0 mod 4 = 1 \/ adr0 mod 4 = 2 \/ adr0 mod 4 = 3) by lia.
        destruct C as [C|[C|[C|C]]]; rewrite C; reflexivity. }
      set (blks := n1 / 20).
      assert (Hb1 : 1 <= blks) by (subst blks; apply Z.div_le_lower_bound; lia).
      assert (Hb2 : 20 * blks <= n1) by (subst blks; apply Z.mul_div_le; lia).
      assert (T2 : getr r2 2 = Z_to_bv 64 spv) by (rewrite (K2 2%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact S2).
      destruct (ublks_calc m rom r2 c1 a1 n1 spv T10 T11 T5 T12 T14 T2 ltac:(lia) Hst)
        as (r3 & M3 & U10 & U11 & U5 & U12 & U14 & U2 & U13 & U7 & K3).
      fold blks in U13, U7, M3. change (wbytes m (Z_to_bv 64 spv) (W8 (Z_to_bv 64 blks))) with (MS blks) in M3.
      pose proof (MS_img blks) as HMi. pose proof (MS_rd blks) as HMr. pose proof (MS_ba ltac:(lia) blks) as HMb.
      destruct (Z.eq_dec blks 1) as [Hone | Hmany].
      +
        destruct (ublks_init1 (MS blks) rom r3 c1 a1 n1 U10 U11 U5 U12 U14 U7 ltac:(subst blks; exact Hone) Hal)
          as (r4 & M4 & L4 & V11 & V12 & V10 & V2 & K4).
        rewrite U2 in V2.
        destruct (ulast_run (MS blks) rom BA adr0 len0 HMi HMr HMb BA_rng Hnw Ha0 r4 (c1, 0, 0, 0, 0) a1 n1 blks spv
                    L4 V11 V10 V12 V2 (MS_ld blks) ltac:(lia) ltac:(lia)) as (r5 & M5 & W14 & W11 & W10 & W12 & K5).
        destruct (tailu_run (MS blks) rom BA adr0 len0 HMi HMr HMb Hnw Ha0 r5 _ (a1 + 20) (blks * -20 + n1) W10 W11 W14 W12
                    (mlastx_range _ _ _) ltac:(lia) ltac:(lia) ltac:(lia)) as (r6 & M6 & X14 & K6).
        exists r6, (MS blks). split; [|split; [|split]].
        * eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
          eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5 | exact M6].
        * rewrite X14. fold blks. rewrite Hone. change (Z.to_nat (1 - 1)) with 0%nat. cbn [mrun].
          replace (a1 + 20 * (1 - 1)) with a1 by lia. replace (a1 + 20) with (a1 + 20 * (1 - 1) + 20) by lia.
          replace (1 * -20 + n1) with (n1 - 20 * 1) by lia. reflexivity.
        * apply UKC_UKB in K5. solve_kb.
        * right. exists blks. reflexivity.
      +
        destruct (ublks_init2 (MS blks) rom r3 c1 a1 n1 U10 U11 U5 U12 U14 U13 U7 ltac:(lia) ltac:(lia) Hal)
          as (r4 & M4 & HB4 & V7 & V5 & V12 & V10 & V2 & K4).
        rewrite U2 in V2.
        set (k := Z.to_nat (blks - 1)) in *.
        destruct (ubloop (MS blks) rom BA adr0 len0 HMi HMr HMb BA_rng Hnw Ha0 k r4 (c1, 0, 0, 0, 0) a1 HB4
                    ltac:(cbn; lia) V7 ltac:(lia) ltac:(lia) ltac:(lia)) as (r5 & M5 & HB5 & K5).
        destruct (mrun BA k a1 (c1, 0, 0, 0, 0)) as [[[[z0 z1] z2] z3] z4] eqn:Ex.
        destruct HB5 as (W14 & W6 & W17 & W16 & W15 & W11 & _).
        assert (W5 : getr r5 5 = Z_to_bv 64 (a1 + 20 * Z.of_nat k)) by (rewrite (K5 5%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact V5).
        assert (W12 : getr r5 12 = Z_to_bv 64 n1) by (rewrite (K5 12%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact V12).
        assert (W10 : getr r5 10 = Z_to_bv 64 CTAB) by (rewrite (K5 10%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact V10).
        assert (W2 : getr r5 2 = Z_to_bv 64 spv) by (rewrite (K5 2%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact V2).
        destruct (upost_loop (MS blks) rom r5 z0 z1 z2 z3 z4 (a1 + 20 * Z.of_nat k) W14 W6 W17 W16 W15 W5
                    ltac:(apply mod4_add20; exact Hal)) as (r6 & M6 & L6 & X11 & X12 & X10 & X2 & K6).
        rewrite W12 in X12. rewrite W10 in X10. rewrite W2 in X2.
        destruct (ulast_run (MS blks) rom BA adr0 len0 HMi HMr HMb BA_rng Hnw Ha0 r6 (z0, z1, z2, z3, z4)
                    (a1 + 20 * Z.of_nat k) n1 blks spv L6 X11 X10 X12 X2 (MS_ld blks) ltac:(lia) ltac:(lia))
          as (r7 & M7 & Y14 & Y11 & Y10 & Y12 & K7).
        destruct (tailu_run (MS blks) rom BA adr0 len0 HMi HMr HMb Hnw Ha0 r7 _ (a1 + 20 * Z.of_nat k + 20) (blks * -20 + n1)
                    Y10 Y11 Y14 Y12 (mlastx_range _ _ _) ltac:(lia) ltac:(lia) ltac:(lia)) as (r8 & M8 & Q14 & K8).
        exists r8, (MS blks). split; [|split; [|split]].
        * eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
          eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5|]. eapply msteps_trans; [exact M6|].
          eapply msteps_trans; [exact M7 | exact M8].
        * rewrite Q14.
          replace (a1 + 20 * (blks - 1)) with (a1 + 20 * Z.of_nat k) by lia.
          replace (blks * -20 + n1) with (n1 - 20 * blks) by lia. reflexivity.
        * apply UKC_UKB in K7. apply UKBB_UKB in K5. solve_kb.
        * right. exists blks. reflexivity.
  Qed.
End BODY.


Definition m13 (m : word -> option byte) (usp : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (usp - 8)) (W8 (getr regs 1)))
    (Z_to_bv 64 (usp - 16)) (W8 (getr regs 8)))
    (Z_to_bv 64 (usp - 24)) (W8 (getr regs 9)))
    (Z_to_bv 64 (usp - 32)) (W8 (getr regs 18)))
    (Z_to_bv 64 (usp - 40)) (W8 (getr regs 19)))
    (Z_to_bv 64 (usp - 48)) (W8 (getr regs 20)))
    (Z_to_bv 64 (usp - 56)) (W8 (getr regs 21)))
    (Z_to_bv 64 (usp - 64)) (W8 (getr regs 22)))
    (Z_to_bv 64 (usp - 72)) (W8 (getr regs 23)))
    (Z_to_bv 64 (usp - 80)) (W8 (getr regs 24)))
    (Z_to_bv 64 (usp - 88)) (W8 (getr regs 25)))
    (Z_to_bv 64 (usp - 96)) (W8 (getr regs 26)))
    (Z_to_bv 64 (usp - 104)) (W8 (getr regs 27)).

Lemma ustk8 {RCa1 : RunCtx}  : forall (m m' : word -> option byte) (usp z : Z),
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 112)) 112 = true -> 112 <= usp < two64 -> mem_grows m m' ->
  usp - 112 <= z -> z + 8 <= usp -> store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m' (Z_to_bv 64 z) 8 = true.
Proof.
  intros m m' usp z Hstk Husp Hg Hlo Hhi.
  eapply store_ok_mono; [exact Hg|].
  eapply (store_ok_sub (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 112)) _ 112 8);
    [u_norm; lia | exact Hstk | u_norm; lia
    | u_norm; change (Z.of_nat 8) with 8%Z; change (Z.of_nat 112%nat) with 112%Z; lia].
Qed.

Ltac grows := repeat (first [ apply mem_grows_refl | eapply mem_grows_trans; [| apply wbytes_grows] ]).

Lemma m13_grows : forall m usp regs, mem_grows m (m13 m usp regs).
Proof. intros. unfold m13. grows. Qed.

Ltac fm1 := eapply frame_mod_trans_same;
    [| eapply frame_mod_weaken; [| apply frame_mod_wbytes; rewrite lenW8; change (Z.of_nat 8) with 8%Z; u_norm; lia];
       intros a [Ha _]; split; [|exact I]; rewrite lenW8; change (Z.of_nat 8) with 8%Z;
       intros Hin; apply Ha; unfold in_rng in *; revert Hin; u_norm; lia ].

Lemma m13_frame : forall m usp regs, 112 <= usp < two64 ->
  frame_mod m (m13 m usp regs) [(Z_to_bv 64 (usp - 112), 112%Z)].
Proof.
  intros m usp regs Husp. unfold m13. repeat fm1. apply frame_mod_refl.
Qed.

Lemma m13s_frame : forall m usp regs (v : word), 112 <= usp < two64 ->
  frame_mod m (wbytes (m13 m usp regs) (Z_to_bv 64 (usp - 112)) (W8 v)) [(Z_to_bv 64 (usp - 112), 112%Z)].
Proof.
  intros m usp regs v Husp. unfold m13. repeat fm1. apply frame_mod_refl.
Qed.

Lemma frame_ro {RCa1 : RunCtx}  : forall m usp, 112 <= usp < two64 ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 112)) 112 = true -> img_ok m -> RO_HI <= usp - 112 \/ usp <= RO_LO.
Proof.
  intros m usp Husp Hstk Hi.
  pose proof (store_ok_off_ro m (usp - 112) 112%nat Hstk ltac:(lia) ltac:(change (Z.of_nat 112%nat) with 112%Z; lia)
                ltac:(change (Z.of_nat 112%nat) with 112%Z; lia) Hi) as Hro.
  change (Z.of_nat 112%nat) with 112%Z in Hro. lia.
Qed.

Lemma m13_img {RCa1 : RunCtx}  : forall m usp regs, 112 <= usp < two64 ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 112)) 112 = true -> img_ok m -> img_ok (m13 m usp regs).
Proof.
  intros m usp regs Husp Hstk Hi.
  pose proof (frame_ro m usp Husp Hstk Hi) as Hro. unfold RO_LO, RO_HI in Hro.
  unfold m13.
  repeat (apply img_ok_wbytes; [ | rewrite lenW8; change (Z.of_nat 8) with 8%Z; u_norm; unfold RO_LO, RO_HI; lia
                                 | rewrite lenW8; change (Z.of_nat 8) with 8%Z; u_norm; lia ]).
  exact Hi.
Qed.

Section TOP.
Context {RCa1 : RunCtx}.
  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac solve_kb := first [ assumption | apply lkeeps_refl | solve_lkeeps
                         | eapply lkeeps_trans; [eassumption | solve_kb] ].
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_kb ].

  Ltac sdz F D aa oktac :=
    chain_step;
    [ reflexivity
    | eapply step_sd_at with (a := aa);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi; zbv
      | gres; reflexivity
      | oktac ]
    | step_simpl ].

  Ltac ldz F D vv E :=
    chain_step;
    [ reflexivity
    | eapply step_ld with (v := vv);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ =>
          match type of E with rdn _ _ (Z_to_bv 64 ?y) _ = _ => replace x with y by lia end end;
        exact E
      | apply bytes_le_to_Z_8 ]
    | step_simpl; gres ].

  Definition UPK : list reg := [1; 3; 4; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

  Lemma upro_run : forall regs m rom (usp : Z),
    getr regs 2 = Z_to_bv 64 usp ->
    112 <= usp < two64 -> store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 112)) 112 = true ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14568 : word) m rom) (mkst r (0x145a0 : word) (m13 m usp regs) rom)
      /\ getr r 2 = Z_to_bv 64 (usp - 112)
      /\ lkeeps UPK regs r.
  Proof.
    intros regs m rom usp R2 Husp Hstk.
    eexists. split.
    - stepz F_14508 D_14508.
      sdz F_1450c D_1450c (Z_to_bv 64 (usp - 8)) ltac:(apply (ustk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14510 D_14510 (Z_to_bv 64 (usp - 16)) ltac:(apply (ustk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14514 D_14514 (Z_to_bv 64 (usp - 24)) ltac:(apply (ustk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14518 D_14518 (Z_to_bv 64 (usp - 32)) ltac:(apply (ustk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_1451c D_1451c (Z_to_bv 64 (usp - 40)) ltac:(apply (ustk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14520 D_14520 (Z_to_bv 64 (usp - 48)) ltac:(apply (ustk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14524 D_14524 (Z_to_bv 64 (usp - 56)) ltac:(apply (ustk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14528 D_14528 (Z_to_bv 64 (usp - 64)) ltac:(apply (ustk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_1452c D_1452c (Z_to_bv 64 (usp - 72)) ltac:(apply (ustk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14530 D_14530 (Z_to_bv 64 (usp - 80)) ltac:(apply (ustk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14534 D_14534 (Z_to_bv 64 (usp - 88)) ltac:(apply (ustk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14538 D_14538 (Z_to_bv 64 (usp - 96)) ltac:(apply (ustk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_1453c D_1453c (Z_to_bv 64 (usp - 104)) ltac:(apply (ustk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      apply mst_refl.
    - unfold UPK. post.
  Qed.

  Lemma upro2_run : forall regs M rom (c : Z),
    getr regs 10 = Z_to_bv 64 c ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x145a4 : word) M rom) (mkst r (0x145bc : word) M rom)
      /\ getr r 14 = Z_to_bv 64 (crc_pre c) /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 13 = Z_to_bv 64 23
      /\ getr r 11 = getr regs 11 /\ getr r 12 = getr regs 12 /\ getr r 2 = getr regs 2
      /\ lkeeps UKB regs r.
  Proof.
    intros regs M rom c R10.
    eexists. split.
    - stepz F_14544 D_14544.
      stepz F_14548 D_14548.
      stepi F_1454c D_1454c; gres; match goal with |- context [v_auipc ?p ?i] => wlit_closed (v_auipc p i) end.
      stepz F_14550 D_14550.
      stepz F_14554 D_14554. rewrite crc_pre_machine.
      stepz F_14558 D_14558.
      apply mst_refl.
    - post.
  Qed.

  Definition UKE : list reg := [3; 4; 10]%bv.

  Lemma uepi_run : forall regs M rom (retw : word) (usp : Z) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
    v1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 (usp - 112) -> 112 <= usp < two64 ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 8)) 8 = Some (W8 v1) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 16)) 8 = Some (W8 v8) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 24)) 8 = Some (W8 v9) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 32)) 8 = Some (W8 v18) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 40)) 8 = Some (W8 v19) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 48)) 8 = Some (W8 v20) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 56)) 8 = Some (W8 v21) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 64)) 8 = Some (W8 v22) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 72)) 8 = Some (W8 v23) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 80)) 8 = Some (W8 v24) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 88)) 8 = Some (W8 v25) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 96)) 8 = Some (W8 v26) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 104)) 8 = Some (W8 v27) ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14ca4 : word) M rom) (mkst r retw M rom)
      /\ getr r 10 = getr regs 10 /\ getr r 2 = Z_to_bv 64 usp /\ getr r 1 = v1
      /\ getr r 8 = v8 /\ getr r 9 = v9 /\ getr r 18 = v18 /\ getr r 19 = v19 /\ getr r 20 = v20
      /\ getr r 21 = v21 /\ getr r 22 = v22 /\ getr r 23 = v23 /\ getr r 24 = v24
      /\ getr r 25 = v25 /\ getr r 26 = v26 /\ getr r 27 = v27
      /\ lkeeps UKE regs r.
  Proof.
    intros regs M rom retw usp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hv1 Hret R2 Husp
           E1 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27.
    eexists. split.
    - ldz F_14c44 D_14c44 v1 E1.
      ldz F_14c48 D_14c48 v8 E8.
      ldz F_14c4c D_14c4c v9 E9.
      ldz F_14c50 D_14c50 v18 E18.
      ldz F_14c54 D_14c54 v19 E19.
      ldz F_14c58 D_14c58 v20 E20.
      ldz F_14c5c D_14c5c v21 E21.
      ldz F_14c60 D_14c60 v22 E22.
      ldz F_14c64 D_14c64 v23 E23.
      ldz F_14c68 D_14c68 v24 E24.
      ldz F_14c6c D_14c6c v25 E25.
      ldz F_14c70 D_14c70 v26 E26.
      ldz F_14c74 D_14c74 v27 E27.
      stepz F_14c78 D_14c78.
      stepret F_14c7c D_14c7c retw ltac:(rwR; subst v1; reflexivity).
      apply mst_refl.
    - unfold UKE. post.
  Qed.
End TOP.


Ltac kb_chain :=
  repeat match goal with
    | K : lkeeps _ ?a ?b |- getr ?b ?r = _ => rewrite (K r) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto]))
    end.

Ltac solve_kb := first [ assumption | apply lkeeps_refl | solve_lkeeps
                       | eapply lkeeps_trans; [eassumption | solve_kb] ].

Theorem u0_crc32_z {RCa1 : RunCtx}  : U0_crc32_z_stmt.
Proof.
  unfold U0_crc32_z_stmt.
  intros regs m rom retw usp c adr len R1 Hret R2 R10 R11 R12 Hc Hadr Hlen Hnw Husp Hstk Hapart Himg Hrd.
  change (2 ^ 64) with two64 in Hc, Hnw, Husp.
  set (M := m13 m usp regs).
  assert (HMi : img_ok M) by (apply m13_img; [lia | exact Hstk | exact Himg]).
  assert (HMr : forall i, 0 <= i < len -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (adr + i)) 1 = Some [b])
    by (apply (readable_grows (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m M adr len (m13_grows m usp regs) Hrd)).
  assert (Hfm : frame_mod m M [(Z_to_bv 64 (usp - 112), 112%Z)]) by (apply m13_frame; lia).
  assert (HMb : forall a, adr <= a < adr + len -> byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M a = byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m a).
  { intros a Ha. apply byte_at_ext. apply (proj1 Hfm). cbn [outside]. split; [|exact I].
    unfold in_rng. u_norm. specialize (Hapart ltac:(lia)). lia. }
  pose proof (frame_ro m usp Husp Hstk Himg) as Hro. unfold RO_LO, RO_HI in Hro.
  assert (Hst8 : store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 112)) 8 = true)
    by (apply (ustk8 m _ usp); [exact Hstk | lia | apply m13_grows | lia | lia]).
  destruct (upro_run regs m rom usp R2 Husp Hstk) as (r1 & M1 & S2 & K1). fold M in M1.
  assert (S11 : getr r1 11 = Z_to_bv 64 adr) by (kb_chain; exact R11).
  assert (S10 : getr r1 10 = Z_to_bv 64 c) by (kb_chain; exact R10).
  destruct (upro2_run r1 M rom c S10) as (r2 & M2 & T14 & T10 & T13 & T11 & T12 & T2 & K2).
  rewrite S11 in T11. rewrite S2 in T2.
  assert (T12' : getr r2 12 = Z_to_bv 64 len) by (rewrite T12; kb_chain; exact R12).
  destruct (ubody_run M rom (byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m) adr len (usp - 112) HMi HMr HMb (byte_at_range (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m) Hnw
              ltac:(lia) Hlen Hst8 ltac:(lia) ltac:(unfold RO_LO, RO_HI; lia) Hapart
              r2 c T14 T10 T11 T12' T13 T2) as (r3 & m3 & M3 & U14 & K3 & Hm3).
  assert (EPA : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r3 (0x14c98 : word) m3 rom) (mkst r (0x14ca4 : word) m3 rom)
           /\ getr r 10 = Z_to_bv 64 (Z.lxor (crcT (byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m) adr len c) M32)
           /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ lkeeps UKB r3 r).
  { eexists. split.
    - stepz F_14c38 D_14c38.
      stepi F_14c3c D_14c3c; znorm.
      replace (v_srli (Z_to_bv 64 (-1)) 32) with (Z_to_bv 64 M32) by (apply bv_eq; vm_compute; reflexivity).
      stepz F_14c40 D_14c40.
      apply mst_refl.
    - repeat split; gres; rwR; [reflexivity | kb_chain; assumption | solve_lkeeps]. }
  destruct EPA as (r4 & M4 & V10 & V2 & K4).
  assert (Hm3' : m3 = M \/ exists v : word, m3 = wbytes M (Z_to_bv 64 (usp - 112)) (W8 v)).
  { destruct Hm3 as [-> | [q ->]]; [left; reflexivity | right]. eexists. unfold MS. reflexivity. }
  clear Hm3.
  assert (E1 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m3 (Z_to_bv 64 (usp - 8)) 8 = Some (W8 (getr regs 1))) by (destruct Hm3' as [-> | [v ->]]; subst M; unfold m13; rdn_solve).
  assert (E8 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m3 (Z_to_bv 64 (usp - 16)) 8 = Some (W8 (getr regs 8))) by (destruct Hm3' as [-> | [v ->]]; subst M; unfold m13; rdn_solve).
  assert (E9 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m3 (Z_to_bv 64 (usp - 24)) 8 = Some (W8 (getr regs 9))) by (destruct Hm3' as [-> | [v ->]]; subst M; unfold m13; rdn_solve).
  assert (E18 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m3 (Z_to_bv 64 (usp - 32)) 8 = Some (W8 (getr regs 18))) by (destruct Hm3' as [-> | [v ->]]; subst M; unfold m13; rdn_solve).
  assert (E19 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m3 (Z_to_bv 64 (usp - 40)) 8 = Some (W8 (getr regs 19))) by (destruct Hm3' as [-> | [v ->]]; subst M; unfold m13; rdn_solve).
  assert (E20 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m3 (Z_to_bv 64 (usp - 48)) 8 = Some (W8 (getr regs 20))) by (destruct Hm3' as [-> | [v ->]]; subst M; unfold m13; rdn_solve).
  assert (E21 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m3 (Z_to_bv 64 (usp - 56)) 8 = Some (W8 (getr regs 21))) by (destruct Hm3' as [-> | [v ->]]; subst M; unfold m13; rdn_solve).
  assert (E22 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m3 (Z_to_bv 64 (usp - 64)) 8 = Some (W8 (getr regs 22))) by (destruct Hm3' as [-> | [v ->]]; subst M; unfold m13; rdn_solve).
  assert (E23 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m3 (Z_to_bv 64 (usp - 72)) 8 = Some (W8 (getr regs 23))) by (destruct Hm3' as [-> | [v ->]]; subst M; unfold m13; rdn_solve).
  assert (E24 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m3 (Z_to_bv 64 (usp - 80)) 8 = Some (W8 (getr regs 24))) by (destruct Hm3' as [-> | [v ->]]; subst M; unfold m13; rdn_solve).
  assert (E25 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m3 (Z_to_bv 64 (usp - 88)) 8 = Some (W8 (getr regs 25))) by (destruct Hm3' as [-> | [v ->]]; subst M; unfold m13; rdn_solve).
  assert (E26 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m3 (Z_to_bv 64 (usp - 96)) 8 = Some (W8 (getr regs 26))) by (destruct Hm3' as [-> | [v ->]]; subst M; unfold m13; rdn_solve).
  assert (E27 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m3 (Z_to_bv 64 (usp - 104)) 8 = Some (W8 (getr regs 27))) by (destruct Hm3' as [-> | [v ->]]; subst M; unfold m13; rdn_solve).
  assert (Hfm3 : frame_mod m m3 [(Z_to_bv 64 (usp - 112), 112%Z)]).
  { destruct Hm3' as [-> | [v ->]]; [exact Hfm | subst M; apply m13s_frame; lia]. }
  destruct (uepi_run r4 m3 rom retw usp _ _ _ _ _ _ _ _ _ _ _ _ _ R1 Hret V2 Husp
              E1 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27)
    as (r5 & M5 & W10 & W2 & W1 & W8' & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & K5).
  exists r5, m3. split; [|split; [|split]].
  - eapply msteps_trans; [exact M1|].
    stepb_ft F_14540 D_14540 ltac:(rwR; zcond).
    eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|]. eapply msteps_trans; [exact M4 | exact M5].
  - rewrite W10, V10, (ucrcT_model (byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m) adr len (byte_at_range (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m) Hlen c), bl_bytes_at. reflexivity.
  - intros rr Hin. cbv [callee_saved In] in Hin.
    repeat (destruct Hin as [<- | Hin]);
      first [ rewrite W2; symmetry; exact R2
            | rewrite W1; exact R1 || (rewrite W1; reflexivity)
            | kb_chain; first [ reflexivity | assumption ]
            | assumption
            | destruct Hin ].
  - exact Hfm3.
Qed.

Theorem u0_crc32_z_null {RCa1 : RunCtx}  : U0_crc32_z_null_stmt.
Proof.
  unfold U0_crc32_z_null_stmt.
  intros regs m rom retw usp R1 Hret R2 R11 Husp Hstk.
  change (2 ^ 64) with two64 in Husp.
  set (M := m13 m usp regs).
  destruct (upro_run regs m rom usp R2 Husp Hstk) as (r1 & M1 & S2 & K1). fold M in M1.
  assert (S11 : getr r1 11 = Z_to_bv 64 0) by (kb_chain; exact R11).
  assert (PRE : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r1 (0x145a0 : word) M rom) (mkst r (0x14ca4 : word) M rom)
           /\ getr r 10 = Z_to_bv 64 0 /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ lkeeps UKB r1 r).
  { eexists. split.
    - stepb_tk F_14540 D_14540 ltac:(rwR; zcond).
      stepz F_145c4 D_145c4.
      stepj F_145c8 D_145c8.
      apply mst_refl.
    - repeat split; gres; rwR; first [reflexivity | assumption | solve_lkeeps]. }
  destruct PRE as (r2 & M2 & T10 & T2 & K2).
  destruct (uepi_run r2 M rom retw usp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
              (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
              (getr regs 26) (getr regs 27) R1 Hret T2 Husp)
    as (r3 & M3 & W10 & W2 & W1 & W8' & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & K3).
  1-13: subst M; unfold m13; rdn_solve.
  exists r3, M. split; [|split; [|split]].
  - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2 | exact M3].
  - rewrite W10. exact T10.
  - intros rr Hin. cbv [callee_saved In] in Hin.
    repeat (destruct Hin as [<- | Hin]);
      first [ rewrite W2; symmetry; exact R2
            | kb_chain; first [ reflexivity | assumption ]
            | assumption
            | destruct Hin ].
  - subst M. apply m13_frame. lia.
Qed.

Theorem u0_crc32 {RCa1 : RunCtx}  : U0_crc32_stmt.
Proof.
  unfold U0_crc32_stmt.
  intros regs m rom retw usp c adr v len R1 Hret R2 R10 R11 R12 Hv Hvl Hc Hadr Hnw Husp Hstk Hapart Himg Hrd.
  pose proof (mod32_range v) as Hl. change (2 ^ 32) with two32 in Hvl. rewrite Hvl in Hl.
  assert (PRE : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14ce4 : word) m rom) (mkst r (0x14568 : word) m rom)
           /\ (getr r 1 = retw /\ getr r 2 = Z_to_bv 64 usp /\ getr r 10 = Z_to_bv 64 c
               /\ getr r 11 = Z_to_bv 64 adr /\ getr r 12 = Z_to_bv 64 len /\ keeps_cs regs r)).
  { eexists. split.
    - stepz F_14c84 D_14c84. stepz F_14c88 D_14c88. rewrite Hvl.
      stepz F_14c8c D_14c8c.
      apply mst_refl.
    - repeat split; gres; rwR; try reflexivity. apply (proj2 (keeps_cs_lkeeps _ _)). solve_lkeeps. }
  destruct PRE as (r1 & M1 & S1 & S2 & S10 & S11 & S12 & K1).
  destruct (u0_crc32_z r1 m rom retw usp c adr len S1 Hret S2 S10 S11 S12 Hc Hadr ltac:(lia) Hnw Husp Hstk Hapart Himg Hrd)
    as (r2 & m' & M2 & V10 & K2 & F2).
  exists r2, m'. split; [eapply msteps_trans; [exact M1 | exact M2]|]. split; [exact V10|]. split; [| exact F2].
  eapply keeps_cs_trans; [exact K1 | exact K2].
Qed.

Theorem u0_crc32_null {RCa1 : RunCtx}  : U0_crc32_null_stmt.
Proof.
  unfold U0_crc32_null_stmt.
  intros regs m rom retw usp R1 Hret R2 R11 Husp Hstk.
  assert (PRE : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14ce4 : word) m rom) (mkst r (0x14568 : word) m rom)
           /\ (getr r 1 = retw /\ getr r 2 = Z_to_bv 64 usp /\ getr r 11 = Z_to_bv 64 0 /\ lkeeps callee_saved regs r
               /\ (forall k, getr r k = getr regs k \/ k = 12%bv))).
  { eexists. split.
    - stepi F_14c84 D_14c84. stepi F_14c88 D_14c88.
      stepj F_14c8c D_14c8c.
      apply mst_refl.
    - repeat split; gres; rwR; try reflexivity; [solve_lkeeps|].
      intros k. destruct (decide (k = 12%bv)) as [-> | Hk]; [right; reflexivity | left].
      rewrite !getr_other by exact Hk. reflexivity. }
  destruct PRE as (r1 & M1 & S1 & S2 & S11 & K1 & Hsame).
  destruct (u0_crc32_z_null r1 m rom retw usp S1 Hret S2 S11 Husp Hstk) as (r2 & m' & M2 & V10 & K2 & F2).
  exists r2, m'. split; [eapply msteps_trans; [exact M1 | exact M2]|]. split; [exact V10|]. split.
  - eapply keeps_cs_trans; [apply (proj2 (keeps_cs_lkeeps _ _)); exact K1 | exact K2].
  -
    exact F2.
Qed.
