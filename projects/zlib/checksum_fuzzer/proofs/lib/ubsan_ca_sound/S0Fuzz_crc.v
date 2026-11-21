(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem S0FuzzBase S0Fuzz_code S0FuzzIface FuzzCrcLib
  S0Fuzz_crcA S0Fuzz_crcB S0Fuzz_crcC S0Fuzz_crcD.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.cks Require Import CkTables CkModel CkMathCrc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque ctab btab crc_byte.


Section BODY.
Context {RCa1 : RunCtx}.
  Variables (m rom : word -> option byte) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.
  Hypothesis Hl0 : 0 <= len0.

  #[local] Abbreviation BA := (byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m).

  Ltac solve_kb := first [ assumption | apply lkeeps_refl | solve_lkeeps
                         | eapply lkeeps_trans; [eassumption | solve_kb] ].
  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_kb ].

  Definition crcT (c : Z) : Z :=
    let '(cT, aT, nT) := tail_entry BA adr0 len0 c in crc_bytes cT (bl BA aT (Z.to_nat nT)).

  Lemma crcT_model : forall c, Z.lxor (crcT c) M32 = crc32_z_model adr0 c (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m adr0 (Z.to_nat len0)).
  Proof.
    intros c. unfold crcT. rewrite <- bl_bytes_at. rewrite (crc32_z_bridge BA (byte_at_range (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m)) by exact Hl0.
    destruct (tail_entry BA adr0 len0 c) as [[cT aT] nT]. reflexivity.
  Qed.


  Lemma body_run : forall regs (c : Z),
    getr regs 14 = Z_to_bv 64 (crc_pre c) -> getr regs 10 = Z_to_bv 64 CTAB ->
    getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 len0 -> getr regs 13 = Z_to_bv 64 23 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x145c4 : word) m rom) (mkst r (0x14bb4 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (crcT c)
      /\ getr r 13 = Z_to_bv 64 M32
      /\ lkeeps KB regs r.
  Proof.
    intros regs c R14 R10 R11 R12 R13.
    pose proof (crc_pre_range32 c) as Hc0. unfold crcT, tail_entry.
    destruct (Z.ltb_spec len0 23) as [Hs | Hb].
    -
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14a60 : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 adr0 /\ getr r 14 = Z_to_bv 64 (crc_pre c)
                         /\ getr r 12 = Z_to_bv 64 len0 /\ lkeeps KB regs r)).
      { eexists. split.
        - stepb_tk F_14564 D_14564 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_lt; lia).
          apply mst_refl.
        - post. }
      cbv beta. intros r1 (S10 & S11 & S14 & S12 & K1).
      destruct (tail_run m rom adr0 len0 Himg Hrd Hnw Ha0 r1 (crc_pre c) adr0 len0 S10 S11 S14 S12 Hc0
                  ltac:(lia) ltac:(lia) Hl0) as (r2 & M2 & T14 & T13 & K2).
      exists r2. split; [exact M2|]. split; [exact T14|]. split; [exact T13 | solve_kb].
    -
      pose proof (align4_range adr0) as Hna. set (na := align4 adr0) in *.
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x145c8 : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 CTAB /\ getr r 11 = Z_to_bv 64 adr0 /\ getr r 12 = Z_to_bv 64 len0
                         /\ getr r 14 = Z_to_bv 64 (crc_pre c) /\ lkeeps KB regs r)).
      { eexists. split.
        - stepb_ft F_14564 D_14564 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_ge; lia).
          apply mst_refl.
        - post. }
      cbv beta. intros r1 (S10 & S11 & S12 & S14 & K1).
      destruct (al_run m rom adr0 len0 Himg Hrd Ha0 r1 (crc_pre c) adr0 len0 S10 S11 S12 S14 Hc0
                  ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & M2 & T10 & T11 & T12 & T14 & K2).
      fold na in T11, T12, T14.
      set (c1 := crc_bytes (crc_pre c) (bl BA adr0 (Z.to_nat na))) in *.
      assert (Hc1 : 0 <= c1 < two32) by (subst c1; apply crc_bytes_range; exact Hc0).
      set (a1 := adr0 + na) in *. set (n1 := len0 - na) in *.
      set (blks := n1 / 20).
      assert (Hb1 : 1 <= blks) by (subst blks; apply Z.div_le_lower_bound; lia).
      assert (Hb2 : 20 * blks <= n1) by (subst blks; apply Z.mul_div_le; lia).
      destruct (Z.eq_dec blks 1) as [Hone | Hmany].
      +
        destruct (blks_run1 m rom r2 c1 a1 n1 T10 T11 T12 T14 ltac:(lia) ltac:(subst blks; exact Hone))
          as (r3 & M3 & L3 & U11 & U13 & U12 & U10 & K3).
        destruct (last_run m rom adr0 len0 Himg Hrd Hnw Ha0 r3 (c1, 0, 0, 0, 0) a1 n1 (n1 / 20 * -20)
                    L3 U11 U10 U12 U13 ltac:(lia) ltac:(lia)) as (r4 & M4 & V14 & V11 & V10 & V12 & K4).
        destruct (tail_run m rom adr0 len0 Himg Hrd Hnw Ha0 r4 _ (a1 + 20) (n1 / 20 * -20 + n1) V10 V11 V14 V12
                    (mlastx_range _ _ _) ltac:(lia) ltac:(lia) ltac:(lia)) as (r5 & M5 & W14 & W13 & K5).
        exists r5. split; [|split; [|split]].
        * eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
          eapply msteps_trans; [exact M4 | exact M5].
        * rewrite W14. rewrite Hone. change (Z.to_nat (1 - 1)) with 0%nat. cbn [mrun].
          replace (a1 + 20 * (1 - 1)) with a1 by lia. replace (a1 + 20) with (a1 + 20 * (1 - 1) + 20) by lia.
          replace (n1 / 20 * -20 + n1) with (n1 - 20 * 1) by lia. reflexivity.
        * exact W13.
        * apply KBC_KB in K4. solve_kb.
      +
        destruct (blks_run2 m rom r2 c1 a1 n1 T10 T11 T12 T14 ltac:(lia) ltac:(lia))
          as (r3 & M3 & HB3 & U6 & U13 & U12 & U10 & K3).
        fold blks in U6, U13.
        set (k := Z.to_nat (blks - 1)) in *.
        destruct (bloop m rom adr0 len0 Himg Hrd Hnw Ha0 k r3 (c1, 0, 0, 0, 0) a1 HB3
                    ltac:(cbn; lia) U6 ltac:(lia) ltac:(lia) ltac:(lia)) as (r4 & M4 & HB4 & K4).
        destruct (mrun BA k a1 (c1, 0, 0, 0, 0)) as [[[[z0 z1] z2] z3] z4] eqn:Ex.
        destruct HB4 as (V14 & V5 & V17 & V16 & V15 & V11 & _).
        assert (V6 : getr r4 6 = Z_to_bv 64 (a1 + 20 * Z.of_nat k)) by (rewrite (K4 6%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact U6).
        assert (V13 : getr r4 13 = Z_to_bv 64 (blks * -20)) by (rewrite (K4 13%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact U13).
        assert (V12 : getr r4 12 = Z_to_bv 64 n1) by (rewrite (K4 12%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact U12).
        assert (V10 : getr r4 10 = Z_to_bv 64 CTAB) by (rewrite (K4 10%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact U10).
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14840 : word) m rom)
                 (fun r => (getr r 14 = Z_to_bv 64 z0 /\ getr r 5 = Z_to_bv 64 z1 /\ getr r 17 = Z_to_bv 64 z2
                            /\ getr r 16 = Z_to_bv 64 z3 /\ getr r 15 = Z_to_bv 64 z4)
                           /\ getr r 11 = Z_to_bv 64 (a1 + 20 * Z.of_nat k) /\ getr r 10 = Z_to_bv 64 CTAB
                           /\ getr r 12 = Z_to_bv 64 n1 /\ getr r 13 = Z_to_bv 64 (blks * -20)
                           /\ lkeeps KB regs r)).
        { eexists. split.
          - eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|]. eapply msteps_trans; [exact M4|].
            stepz F_147c0 D_147c0.
            stepz F_147c4 D_147c4.
            apply mst_refl.
          - apply KBB_KB in K4. post. }
        cbv beta. intros r5 (L5 & W11 & W10 & W12 & W13 & K5).
        destruct (last_run m rom adr0 len0 Himg Hrd Hnw Ha0 r5 (z0, z1, z2, z3, z4) (a1 + 20 * Z.of_nat k) n1 (blks * -20)
                    L5 W11 W10 W12 W13 ltac:(lia) ltac:(lia)) as (r6 & M6 & X14 & X11 & X10 & X12 & K6).
        destruct (tail_run m rom adr0 len0 Himg Hrd Hnw Ha0 r6 _ (a1 + 20 * Z.of_nat k + 20) (blks * -20 + n1) X10 X11 X14 X12
                    (mlastx_range _ _ _) ltac:(lia) ltac:(lia) ltac:(lia)) as (r7 & M7 & Y14 & Y13 & K7).
        exists r7. split; [|split; [|split]].
        * eapply msteps_trans; [exact M6 | exact M7].
        * rewrite Y14.
          replace (a1 + 20 * (blks - 1)) with (a1 + 20 * Z.of_nat k) by lia.
          replace (blks * -20 + n1) with (n1 - 20 * blks) by lia. reflexivity.
        * exact Y13.
        * apply KBC_KB in K6. solve_kb.
  Qed.
End BODY.


#[local] Abbreviation W8 v := (word_to_le_bytes 8 v).

Definition m9 (m : word -> option byte) (usp : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (usp - 8)) (W8 (getr regs 8)))
    (Z_to_bv 64 (usp - 16)) (W8 (getr regs 9)))
    (Z_to_bv 64 (usp - 24)) (W8 (getr regs 18)))
    (Z_to_bv 64 (usp - 32)) (W8 (getr regs 19)))
    (Z_to_bv 64 (usp - 40)) (W8 (getr regs 20)))
    (Z_to_bv 64 (usp - 48)) (W8 (getr regs 21)))
    (Z_to_bv 64 (usp - 56)) (W8 (getr regs 22)))
    (Z_to_bv 64 (usp - 64)) (W8 (getr regs 23)))
    (Z_to_bv 64 (usp - 72)) (W8 (getr regs 24)).

Lemma stk8 {RCa1 : RunCtx}  : forall (m m' : word -> option byte) (usp z : Z),
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 80)) 80 = true -> 80 <= usp < two64 -> mem_grows m m' ->
  usp - 80 <= z -> z + 8 <= usp -> store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m' (Z_to_bv 64 z) 8 = true.
Proof.
  intros m m' usp z Hstk Husp Hg Hlo Hhi.
  eapply store_ok_mono; [exact Hg|].
  eapply (store_ok_sub (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 80)) _ 80 8);
    [u_norm; lia | exact Hstk | u_norm; lia
    | u_norm; change (Z.of_nat 8) with 8%Z; change (Z.of_nat 80%nat) with 80%Z; lia].
Qed.

Ltac grows := repeat (first [ apply mem_grows_refl | eapply mem_grows_trans; [| apply wbytes_grows] ]).

Lemma m9_grows : forall m usp regs, mem_grows m (m9 m usp regs).
Proof. intros. unfold m9. grows. Qed.

Lemma m9_frame : forall m usp regs, 80 <= usp < two64 ->
  frame_mod m (m9 m usp regs) [(Z_to_bv 64 (usp - 80), 80%Z)].
Proof.
  intros m usp regs Husp. unfold m9.
  repeat (eapply frame_mod_trans_same;
    [| eapply frame_mod_weaken; [| apply frame_mod_wbytes; rewrite lenW8; change (Z.of_nat 8) with 8%Z; u_norm; lia];
       intros a [Ha _]; split; [|exact I]; rewrite lenW8; change (Z.of_nat 8) with 8%Z;
       intros Hin; apply Ha; unfold in_rng in *; revert Hin; u_norm; lia ]).
  apply frame_mod_refl.
Qed.

Lemma m9_img {RCa1 : RunCtx}  : forall m usp regs, 80 <= usp < two64 ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 80)) 80 = true -> img_ok m -> img_ok (m9 m usp regs).
Proof.
  intros m usp regs Husp Hstk Hi.
  pose proof (store_ok_off_ro m (usp - 80) 80%nat Hstk ltac:(lia) ltac:(change (Z.of_nat 80%nat) with 80%Z; lia)
                ltac:(change (Z.of_nat 80%nat) with 80%Z; lia) Hi) as Hro.
  change (Z.of_nat 80%nat) with 80%Z in Hro. unfold RO_LO, RO_HI in Hro.
  unfold m9.
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

  Definition PK : list reg := [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

  Lemma pro_run : forall regs m rom (usp c adr len : Z),
    getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 c ->
    getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 len ->
    80 <= usp < two64 -> store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 80)) 80 = true ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x14584 : word) m rom) (mkst r (0x145c4 : word) (m9 m usp regs) rom)
      /\ getr r 2 = Z_to_bv 64 (usp - 80) /\ getr r 14 = Z_to_bv 64 (crc_pre c) /\ getr r 10 = Z_to_bv 64 CTAB
      /\ getr r 11 = Z_to_bv 64 adr /\ getr r 12 = Z_to_bv 64 len /\ getr r 13 = Z_to_bv 64 23
      /\ lkeeps PK regs r.
  Proof.
    intros regs m rom usp c adr len R2 R10 R11 R12 Husp Hstk.
    eexists. split.
    - stepz F_14524 D_14524.
      sdz F_14528 D_14528 (Z_to_bv 64 (usp - 8)) ltac:(apply (stk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_1452c D_1452c (Z_to_bv 64 (usp - 16)) ltac:(apply (stk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14530 D_14530 (Z_to_bv 64 (usp - 24)) ltac:(apply (stk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14534 D_14534 (Z_to_bv 64 (usp - 32)) ltac:(apply (stk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14538 D_14538 (Z_to_bv 64 (usp - 40)) ltac:(apply (stk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_1453c D_1453c (Z_to_bv 64 (usp - 48)) ltac:(apply (stk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14540 D_14540 (Z_to_bv 64 (usp - 56)) ltac:(apply (stk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14544 D_14544 (Z_to_bv 64 (usp - 64)) ltac:(apply (stk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_14548 D_14548 (Z_to_bv 64 (usp - 72)) ltac:(apply (stk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      stepz F_1454c D_1454c.
      stepz F_14550 D_14550.
      stepi F_14554 D_14554; gres; match goal with |- context [v_auipc ?p ?i] => wlit_closed (v_auipc p i) end.
      stepz F_14558 D_14558.
      stepz F_1455c D_1455c. rewrite crc_pre_machine.
      stepz F_14560 D_14560.
      apply mst_refl.
    - unfold PK. post.
  Qed.

  Definition EK : list reg := [1; 3; 4; 25; 26; 27]%bv.

  Lemma epi_run : forall regs M rom (retw : word) (usp x : Z) (v8 v9 v18 v19 v20 v21 v22 v23 v24 : word),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 (usp - 80) ->
    getr regs 14 = Z_to_bv 64 x -> getr regs 13 = Z_to_bv 64 M32 -> 80 <= usp < two64 ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 8)) 8 = Some (W8 v8) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 16)) 8 = Some (W8 v9) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 24)) 8 = Some (W8 v18) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 32)) 8 = Some (W8 v19) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 40)) 8 = Some (W8 v20) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 48)) 8 = Some (W8 v21) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 56)) 8 = Some (W8 v22) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 64)) 8 = Some (W8 v23) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 72)) 8 = Some (W8 v24) ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x14bb4 : word) M rom) (mkst r retw M rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lxor x M32) /\ getr r 2 = Z_to_bv 64 usp
      /\ getr r 8 = v8 /\ getr r 9 = v9 /\ getr r 18 = v18 /\ getr r 19 = v19 /\ getr r 20 = v20
      /\ getr r 21 = v21 /\ getr r 22 = v22 /\ getr r 23 = v23 /\ getr r 24 = v24
      /\ lkeeps EK regs r.
  Proof.
    intros regs M rom retw usp x v8 v9 v18 v19 v20 v21 v22 v23 v24 R1 Hret R2 R14 R13 Husp E8 E9 E18 E19 E20 E21 E22 E23 E24.
    eexists. split.
    - stepz F_14b54 D_14b54.
      ldz F_14b58 D_14b58 v8 E8.
      ldz F_14b5c D_14b5c v9 E9.
      ldz F_14b60 D_14b60 v18 E18.
      ldz F_14b64 D_14b64 v19 E19.
      ldz F_14b68 D_14b68 v20 E20.
      ldz F_14b6c D_14b6c v21 E21.
      ldz F_14b70 D_14b70 v22 E22.
      ldz F_14b74 D_14b74 v23 E23.
      ldz F_14b78 D_14b78 v24 E24.
      stepz F_14b7c D_14b7c.
      stepret F_14b80 D_14b80 retw ltac:(rwR; reflexivity).
      apply mst_refl.
    - unfold EK. post.
  Qed.
End TOP.


Ltac kb_chain :=
  repeat match goal with
    | K : lkeeps _ ?a ?b |- getr ?b ?r = _ => rewrite (K r) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto]))
    end.

Theorem s0_crc32_z {RCa1 : RunCtx}  : S0_crc32_z_stmt.
Proof.
  unfold S0_crc32_z_stmt.
  intros regs m rom retw usp c adr len R1 Hret R2 R10 R11 R12 Hc Hadr Hlen Hnw Husp Hstk Hapart Himg Hrd.
  change (2 ^ 64) with two64 in Hc, Hnw, Husp.
  set (M := m9 m usp regs).
  assert (HMi : img_ok M) by (apply m9_img; [lia | exact Hstk | exact Himg]).
  assert (HMr : forall i, 0 <= i < len -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (adr + i)) 1 = Some [b])
    by (apply (readable_grows (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m M adr len (m9_grows m usp regs) Hrd)).
  assert (Hfm : frame_mod m M [(Z_to_bv 64 (usp - 80), 80%Z)]) by (apply m9_frame; lia).
  destruct (pro_run regs m rom usp c adr len R2 R10 R11 R12 Husp Hstk) as (r1 & M1 & S2 & S14 & S10 & S11 & S12 & S13 & K1).
  fold M in M1.
  destruct (body_run M rom adr len HMi HMr Hnw ltac:(lia) Hlen r1 c S14 S10 S11 S12 S13) as (r2 & M2 & T14 & T13 & K2).
  assert (T1 : getr r2 1 = retw) by (kb_chain; exact R1).
  assert (T2 : getr r2 2 = Z_to_bv 64 (usp - 80)) by (kb_chain; exact S2).
  assert (E8 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 8)) 8 = Some (W8 (getr regs 8))) by (subst M; unfold m9; rdn_solve).
  assert (E9 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 16)) 8 = Some (W8 (getr regs 9))) by (subst M; unfold m9; rdn_solve).
  assert (E18 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 24)) 8 = Some (W8 (getr regs 18))) by (subst M; unfold m9; rdn_solve).
  assert (E19 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 32)) 8 = Some (W8 (getr regs 19))) by (subst M; unfold m9; rdn_solve).
  assert (E20 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 40)) 8 = Some (W8 (getr regs 20))) by (subst M; unfold m9; rdn_solve).
  assert (E21 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 48)) 8 = Some (W8 (getr regs 21))) by (subst M; unfold m9; rdn_solve).
  assert (E22 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 56)) 8 = Some (W8 (getr regs 22))) by (subst M; unfold m9; rdn_solve).
  assert (E23 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 64)) 8 = Some (W8 (getr regs 23))) by (subst M; unfold m9; rdn_solve).
  assert (E24 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 72)) 8 = Some (W8 (getr regs 24))) by (subst M; unfold m9; rdn_solve).
  destruct (epi_run r2 M rom retw usp _ _ _ _ _ _ _ _ _ _ T1 Hret T2 T14 T13 Husp E8 E9 E18 E19 E20 E21 E22 E23 E24)
    as (r3 & M3 & U10 & U2 & U8 & U9 & U18 & U19 & U20 & U21 & U22 & U23 & U24 & K3).
  exists r3, M. split; [|split; [|split]].
  - stepb_ft F_14520 D_14520 ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
    eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2 | exact M3].
  - rewrite U10, (crcT_model M adr len Hlen c).
    destruct (Z.eq_dec len 0) as [-> | Hnz]; [reflexivity|].
    rewrite (bytes_at_frame1 (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m M (Z.to_nat len) adr (usp - 80) 80 Hfm) by lia. reflexivity.
  - intros rr Hin. cbv [callee_saved In] in Hin.
    repeat (destruct Hin as [<- | Hin]);
      first [ rewrite U2; symmetry; exact R2
            | kb_chain; first [ reflexivity | assumption ]
            | assumption
            | destruct Hin ].
  - exact Hfm.
Qed.


Theorem s0_crc32 {RCa1 : RunCtx}  : S0_crc32_stmt.
Proof.
  unfold S0_crc32_stmt.
  intros regs m rom retw usp c adr v len R1 Hret R2 R10 R11 R12 Hv Hvl Hc Hadr Hnw Husp Hstk Hapart Himg Hrd.
  pose proof (mod32_range v) as Hl. change (2 ^ 32) with two32 in Hvl. rewrite Hvl in Hl.
  assert (PRE : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x14be4 : word) m rom) (mkst r (0x14580 : word) m rom)
           /\ (getr r 1 = retw /\ getr r 2 = Z_to_bv 64 usp /\ getr r 10 = Z_to_bv 64 c
               /\ getr r 11 = Z_to_bv 64 adr /\ getr r 12 = Z_to_bv 64 len /\ keeps_cs regs r)).
  { eexists. split.
    - stepz F_14b84 D_14b84. stepz F_14b88 D_14b88. rewrite Hvl.
      stepz F_14b8c D_14b8c.
      apply mst_refl.
    - repeat split; gres; rwR; try reflexivity. apply (proj2 (keeps_cs_lkeeps _ _)). solve_lkeeps. }
  destruct PRE as (r1 & M1 & S1 & S2 & S10 & S11 & S12 & K1).
  destruct (s0_crc32_z r1 m rom retw usp c adr len S1 Hret S2 S10 S11 S12 Hc Hadr ltac:(lia) Hnw Husp Hstk Hapart Himg Hrd)
    as (r2 & m' & M2 & V10 & K2 & F2).
  exists r2, m'. split; [eapply msteps_trans; [exact M1 | exact M2]|]. split; [exact V10|]. split; [| exact F2].
  eapply keeps_cs_trans; [exact K1 | exact K2].
Qed.

Theorem s0_crc32_null {RCa1 : RunCtx}  : S0_crc32_null_stmt.
Proof.
  unfold S0_crc32_null_stmt.
  intros regs m rom retw R1 Hret R11.
  eexists. split; [|split].
  - stepi F_14b84 D_14b84. stepi F_14b88 D_14b88.
    stepj F_14b8c D_14b8c.
    stepb_tk F_14520 D_14520 ltac:(rwR; rewrite zc_eq by lia; reflexivity).
    stepz F_147c8 D_147c8.
    stepret F_147cc D_147cc retw ltac:(rwR; reflexivity).
    apply mst_refl.
  - gres. reflexivity.
  - apply (proj2 (keeps_cs_lkeeps _ _)). solve_lkeeps.
Qed.
