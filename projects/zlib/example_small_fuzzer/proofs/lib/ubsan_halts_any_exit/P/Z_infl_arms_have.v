(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_defs2.

Module Z_infl_a_lit.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_TERM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_TERM.RefInflateA_LIT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma arm_LIT_spec : forall X w x8 x12 ms,
  ILOOP X w PC_LIT x8 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LIT ->
  evt psegs (fun ms' => IPOST X (arm_LIT w) ms' /\ PATI X (wof (arm_LIT w))) ms.
Proof.
  intros X [s c r] x8 x12 ms HL XO HW HP HM. iarm_open HL. rewrite arm_LIT_eq.
  destruct HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & RHB & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & [POB POW]). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LIT.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB.
  open_IST ST. open_isA GA. ifine m.
  zstep. br_cases K.
  -
    assert (Kl : ir_left r <> 0) by lia. replace (ir_left r =? 0) with false by (symmetry; apply Z.eqb_neq; exact Kl).
    rd_sub GA 108%nat 0%nat 1%nat. zs. clear RD. zs.
    assert (RLEN : 0 <= is_length s < 2^32) by (destruct HCORE as (_&_&_&_&_&_&_&_&_&_&_&_&_&H); exact H).
    pose proof (u8arr_store_ok psegs _ _ _ (ir_put r) (wa (il_NO (ix_L X) + ir_put r)) OUT ltac:(rewrite LOB; lia) eq_refl) as SOK.
    zs. rewrite le1_zx8_wz by lia.
    pose proof (u8arr_write psegs _ _ _ (ir_put r) (Z_to_bv 8 (wrap8 (is_length s))) OUT ltac:(rewrite LOB; lia)) as OUT2. clear OUT LOB.
    store_done.
    rewrite iout_bytes_store in OUT2 by lia.
    pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) (wrap8 (is_length s)))) (ir_put r + 1) ltac:(lia)) as LOB.
    apply (f_equal Z.of_nat) in LOB.
    do 8 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eexists. eapply ILOOP_intro; ired; try ireg.
      apply IMEM_intro; ired.
      * exists jf. exact FRM.
      * exact STK.
      * exact ZS.
      * constructor; ired; [unfold isA, isA_cells; ired; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
      * exact IN.
      * unfold iout. exact OUT2.
      * eassumption.
      * exact MU.
      * exact WM.
    + cbn [wof]. destruct POW as (POW & POL & _ & PHW). unfold PATI, OBYT. ired. rewrite arr_len_set.
      destruct Pfl as [Pf|(Pf & [E|E] & _)]; [|rewrite HM in E; discriminate E ..].
      repeat (split; [first [assumption | left; assumption | unfold LEN, FLAGS, HCRC; lia]|]).
      split; [|split; [exact POW|split; [rewrite wrap32_id by lia; lia| split; [reflexivity| exact PHW]]]]. intros i Hi. destruct (Z.eq_dec i (ir_put r)) as [->|NE].
      * rewrite arr_get_set_same by lia. pose proof (wrap8_range (is_length s)) as H8. change (2^8) with 256 in H8. exact H8.
      * rewrite arr_get_set_other by lia. apply POB. lia.
  -
    assert (Kl : ir_left r = 0) by lia. replace (ir_left r =? 0) with true by (symmetry; apply Z.eqb_eq; exact Kl).
    do 2 zs.
    apply evt_done. split; [|exact HP].
    cbn [IPOST]. eapply ILEAVE_intro; ired; try ireg.
    apply IMEML_intro; ired.
    + exists (wz (ir_ret r)), jf. exact FRM.
    + exact STK.
    + exact ZS.
    + constructor; [exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + exact OUT.
    + exact MI.
    + exact MU.
    + exact WM.
Qed.

Lemma arm_LIT_ok : forall flush, arm_stmt flush LIT PC_LIT arm_LIT.
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (arm_LIT_spec X w _ x12 ms HL XO HW HP HM). Qed.
End Z_infl_a_lit.


Module Z_infl_a_term.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma arm_DONE_eq : forall s c r, arm_DONE (mkW s c r) = ALeave (mkW s c (irset_ret r Z_STREAM_END)).
Proof. reflexivity. Qed.
Lemma arm_BAD_eq : forall s c r, arm_BAD (mkW s c r) = ALeave (mkW s c (irset_ret r Z_DATA_ERROR)).
Proof. reflexivity. Qed.
Lemma arm_MEM_eq : forall s c r, arm_MEM (mkW s c r) = ARet Z_MEM_ERROR (mkW s c r).
Proof. reflexivity. Qed.

Lemma arm_DONE_ok : forall flush, arm_stmt flush DONE PC_DONE arm_DONE.
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. rewrite arm_DONE_eq.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  unfold PC_DONE. do 2 zs.
  apply evt_done. split; [|exact HP].
  cbn [IPOST]. eapply ILEAVE_intro; ired; try ireg.
  eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma arm_BAD_ok : forall flush, arm_stmt flush BAD PC_BAD arm_BAD.
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. rewrite arm_BAD_eq.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  apply evt_done. split; [|exact HP].
  cbn [IPOST]. eapply ILEAVE_intro; ired; try ireg.
  eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma arm_MEM_ok : forall flush, arm_stmt flush MEM PC_MEM arm_MEM.
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. rewrite arm_MEM_eq.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  unfold PC_MEM. do 2 zs.
  apply evt_done. split; [|exact HP].
  cbn [IPOST]. eapply IRET_intro; ired; try ireg.
  - eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
  - intros E; discriminate E.
Qed.
End Z_infl_a_term.


Module Z_infl_a_type.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_pure Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_TERM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_TERM.RefInflateA_TYPE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_TYPEDO_NB : Z := 0x1d3b4.
Definition PC_TYPEDO_J : Z := 0x1d3e4.

Lemma typedo_nb3 : forall X s c r x8 x12 ms,
  ILOOP X (mkW s c r) PC_TYPEDO_NB x8 x12 ms -> ix_ok X -> REGS c r -> PATI X (mkW s c r) -> ir_bits r < 8 ->
  evt psegs (NBJ X s c r 3 PC_TYPEDO_J x8 (wz (il_NI (ix_L X) + ir_next r))) ms.
Proof.
  intros X s c r x8 x12 ms HL XO HREGS HP MFB.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  unfold PC_TYPEDO_NB. ix_open XO.
  do 2 zs. br_cases K.
  -
    zs. apply evt_done. left. exists r, (wz 2). split; [|split].
    + rewrite NEEDBITS3_eq by lia. replace (ir_bits r <? 3) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    + left. split; [reflexivity| lia].
    + eapply ILOOP27_intro; ired; [ireg .. |]. exact HMEM.
  - zs. br_cases K2.
    +
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 6 zs. rewrite <- Pin. rewrite !pull_shift by lia. rewrite lor8_small by lia.
      apply evt_done. left. eexists (pullr c r), _. split; [|split].
      * rewrite NEEDBITS3_eq by lia. replace (ir_bits r <? 3) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (ir_have r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      * right. split; [reflexivity| lia].
      * eapply ILOOP27_intro; pullr_rw c r; ired; [ireg .. |].
        eapply IMEM_regs; [exact HMEM| reflexivity..].
    +
      do 2 zs.
      apply evt_done. right. exists r. split; [|split].
      * rewrite NEEDBITS3_eq by lia. replace (ir_bits r <? 3) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (ir_have r =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Local Ltac close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma typedo_core : forall flush X w x8 x12 ms,
  ix_flush X = flush -> 0 <= flush <= 4 ->
  ILOOP X w PC_TYPEDO x8 x12 ms -> ix_ok X -> WINV w -> PATI X w -> (is_mode (w_s w) = TYPE \/ is_mode (w_s w) = TYPEDO) ->
  evt psegs (fun ms' => IPOST X (arm_TYPEDO ivar_ref flush w) ms' /\ PATI X (wof (arm_TYPEDO ivar_ref flush w))) ms.
Proof.
  intros flush X [s c r] x8 x12 ms EF RF HL XO HW HP HM.
  destruct HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  assert (MFB : ir_bits r < 8).
  { destruct HM as [E|E]; rewrite E in HMF; unfold MF in HMF; cbn in HMF; destruct HMF as [_ H]; exact H. }
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0).
  { destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; destruct HM as [E'|E']; rewrite E' in E; discriminate E. }
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HISR : ISR s) by (split; assumption).
  destruct (Z.eq_dec (is_last s) 0) as [L0|L1].
  2:{
      rewrite (arm_TYPEDO_last flush s c r L1).
      assert (L1' : is_last s = 1) by (destruct PL; [contradiction| assumption]).
      clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HM HREGS.
      iarm_open HL. ix_open XO.
      pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
      pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
      open_IST ST. open_isA GA. open_izs ZS. ifineS m.
      unfold PC_TYPEDO. zs. rewrite L1'. zs. br_true.
      do 8 zs. rewrite (land63_small (Z.land (ir_bits r) 7)) by (pose proof (land7_range (ir_bits r)); lia).
      rewrite land_m8_u64 by lia. pose proof (land7_le (ir_bits r) ltac:(lia)) as L7.
      itr_groups MUf WMf.
      apply evt_done. split.
      - cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      - cbn [wof]. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold CHECK, FLAGS, HCRC; cbn; lia| reflexivity..|].
        exact HISR. }

  eapply evt_cut.
  { destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
    pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
    unfold PC_TYPEDO. zs. rewrite L0. zs. br_false.
    eapply (typedo_nb3 X s c r x8); [eapply ILOOP_intro; ired; [ireg .. | exact HMEM] | exact XO | exact HREGS | exact HP | exact MFB]. }
  intros ms1 [(r1 & x12' & EN & HR1 & HJ)|(r1 & EN & HR1 & HLV)].
  2:{
      rewrite (arm_TYPEDO_leave flush s c r _ L0 EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
  pose proof (Rin (ir_next r)) as RBy.
  assert (R1 : 3 <= ir_bits r1 < 64 /\ 0 <= ir_hold r1 < 2 ^ ir_bits r1 /\ ir_put r1 = ir_put r /\ ir_out r1 = ir_out r /\ ir_left r1 = ir_left r).
  { destruct HR1 as [[-> H3]|(-> & H1 & H2)]; [split; [lia|]; split; [exact RH|]; repeat split; reflexivity|].
    pullr_rw c r. pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r)) (ir_bits r) (ir_hold r) RBy ltac:(lia) RH) as PR.
    split; [lia|]. split; [exact PR|]. repeat split; reflexivity. }
  destruct R1 as (RB1 & RH1 & EP1 & EO1 & EL1).
  rewrite (arm_TYPEDO_run flush s c r s c r1 L0 EN RB1 RH1). unfold typedo_B. cbn [w_s w_c w_r].
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HP| assumption..]).
  assert (RH164 : 0 <= ir_hold r1 < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH1)|]. apply Z.pow_le_mono_r; lia. }
  assert (Rv : 0 <= ir_hold r1 mod 2 ^ 1 < 2) by (apply Z.mod_pos_bound; lia).
  assert (Rt : 0 <= (ir_hold r1 / 2 ^ 1) mod 2 ^ 2 < 4) by (apply Z.mod_pos_bound; lia).
  remember (ir_hold r1 mod 2 ^ 1) as v eqn:Ev. remember ((ir_hold r1 / 2 ^ 1) mod 2 ^ 2) as t eqn:Et.
  assert (HISR' : forall M, ISR (iset_mode (iset_last s v) M)) by (intros M; destruct HISR as [_ H2]; split; [ired; lia| exact H2]).
  assert (HISRf : ISR (iset_mode (fixedtables (iset_last s v)) LEN_)) by (destruct HISR as [_ H2]; split; [cbn; lia| exact H2]).
  clear HL RH RH1 HCORE HMF HWF HWB Rin Pfl PL PHD HR1 HM HISR EN RBy HREGS.
  iarm_open27 HJ. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r1) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_TYPEDO_J. do 3 zs. rewrite land1_mod, type_bits by lia. rewrite <- Ev, <- Et.
  do 3 zs. br_cases K; rewrite ?signed_wz in K by lia.
  -
    do 2 zs. br_cases K2.
    +
      replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (t =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (t =? 2) with false by (symmetry; apply Z.eqb_neq; lia).
      do 5 zs. do 6 zs. rewrite (Z.shiftr_div_pow2 (ir_hold r1) 3) by lia.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..|]. apply HISR'.
    +
      replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (t =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (t =? 2) with true by (symmetry; apply Z.eqb_eq; lia).
      do 3 zs. do 6 zs. rewrite (Z.shiftr_div_pow2 (ir_hold r1) 3) by lia.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TABLE, FLAGS, HCRC; cbn; lia| reflexivity..|]. apply HISR'.
  - zs. br_cases K2.
    +
      replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (t =? 1) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (flush =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia).
      (* 1.4: the fixed tables come from a CALL to inflate_fixed (0x1f818), walked inline: mv a0,s0; mv s1,ra; jal;
         7 instructions forming lenfix / distfix / (5 << 32 | 9); sd lencode (120); sd distcode (128); then the one
         8-byte store of lenbits | distbits at 136 (through the recast, as at 1.3.1), ret; isA cells at the 1.4 layout *)
      do 12 zs.

      destruct (le8_of_bytes (le4 (wz (is_lenbits s)) ++ le4 (wz (is_distbits s))) ltac:(rewrite length_app, !length_le4; reflexivity)) as (zz & _ & Hzz).
      eapply (rw_cells_recast _ _ _
        [C8 (wz (il_S (ix_L X))); C4 (wz (is_mode s)); C4 (wz v); C4 (wz (is_wrap s)); C4 (wz 5); C4 (wz (is_havedict s)); C4 (wz (is_flags s)); C4 (wz (is_dmax s)); C4 (wz 0);
         C8 (wz (is_check s)); C8 (wz (is_total s)); C8 (wz (is_head s)); C4 (wz 15); C4 (wz (is_wbits s)); C4 (wz (is_wsize s)); C4 (wz (is_whave s)); C4 (wz (is_wnext s)); C4 (wz 0);
         C8 (wz (win_addr (ix_L X) (is_window_blk s))); C8 (wz (is_hold s)); C4 (wz (is_bits s)); C4 (wz (is_length s)); C4 (wz (is_offset s)); C4 (wz (is_extra s));
         C8 (wz 75390); C8 (wz 77438); C8 (wz zz);
         C4 (wz (is_ncode s)); C4 (wz (is_nlen s)); C4 (wz (is_ndist s)); C4 (wz (is_have s)); C8 (wz (il_As (ix_L X) + 1384 + 4 * is_next s))]) in GA.
      2:{ cbn [cells_wf cell_wf]; repeat split. }
      2:{ cbn [cells_bytes cbytes]; rewrite Hzz, <- !app_assoc; reflexivity. }
      zs.
      eapply (rw_cells_recast _ _ _
        [C8 (wz (il_S (ix_L X))); C4 (wz (is_mode s)); C4 (wz v); C4 (wz (is_wrap s)); C4 (wz 5); C4 (wz (is_havedict s)); C4 (wz (is_flags s)); C4 (wz (is_dmax s)); C4 (wz 0);
         C8 (wz (is_check s)); C8 (wz (is_total s)); C8 (wz (is_head s)); C4 (wz 15); C4 (wz (is_wbits s)); C4 (wz (is_wsize s)); C4 (wz (is_whave s)); C4 (wz (is_wnext s)); C4 (wz 0);
         C8 (wz (win_addr (ix_L X) (is_window_blk s))); C8 (wz (is_hold s)); C4 (wz (is_bits s)); C4 (wz (is_length s)); C4 (wz (is_offset s)); C4 (wz (is_extra s));
         C8 (wz 75390); C8 (wz 77438); C4 (wz 9); C4 (wz 5);
         C4 (wz (is_ncode s)); C4 (wz (is_nlen s)); C4 (wz (is_ndist s)); C4 (wz (is_have s)); C8 (wz (il_As (ix_L X) + 1384 + 4 * is_next s))]) in GA.
      2:{ cbn [cells_wf cell_wf]; repeat split. }
      2:{ cbn [cells_bytes cbytes]; rewrite le8_fixed_bits; rewrite <- !app_assoc; reflexivity. }
      (* ret; li t4,30; ld t6,88(sp); mv ra,s1; ld a1,104(sp); ld a0,96(sp); add a2,s4,-10; li a3,6; sw a2,8(s0); bne a1,a3 *)
      do 10 zs. br_true. do 5 zs. rewrite (Z.shiftr_div_pow2 (ir_hold r1) 3) by lia.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold LEN_, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact HISRf.
    +
      replace (t =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      do 3 zs. do 6 zs. rewrite (Z.shiftr_div_pow2 (ir_hold r1) 3) by lia.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold STORED, FLAGS, HCRC; cbn; lia| reflexivity..|]. apply HISR'.
Qed.

Lemma arm_TYPEDO_ok : forall flush, 0 <= flush <= 4 -> arm_stmt flush TYPEDO PC_TYPEDO (arm_TYPEDO ivar_ref flush).
Proof. intros flush RF X w x12 ms EF HL XO HW _ HP HM. exact (typedo_core flush X w _ x12 ms EF RF HL XO HW HP (or_intror HM)). Qed.

Lemma type_core : forall flush X w x8 x12 ms,
  ix_flush X = flush -> 0 <= flush <= 4 ->
  ILOOP X w PC_TYPE x8 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = TYPE ->
  evt psegs (fun ms' => IPOST X (arm_TYPE ivar_ref flush w) ms' /\ PATI X (wof (arm_TYPE ivar_ref flush w))) ms.
Proof.
  intros flush X w x8 x12 ms EF RF HL XO HW HP HM.
  assert (EA : arm_TYPE ivar_ref flush w = arm_TYPEDO ivar_ref flush w).
  { unfold arm_TYPE. cbn [iv_flush_exits ivar_ref andb].
    replace (flush =? Z_BLOCK) with false by (symmetry; apply Z.eqb_neq; unfold Z_BLOCK; lia).
    replace (flush =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia). reflexivity. }
  rewrite EA.
  eapply (evt_cut psegs (ILOOP X w PC_TYPEDO x8 (wz 2))); [| intros ms1 H1; exact (typedo_core flush X w _ _ ms1 EF RF H1 XO HW HP (or_introl HM))].
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM).
  pose proof HMEM as ((jf & FRM) & _). unfold iframe_cells in FRM.
  unfold PC_TYPE. do 3 zs. rewrite EF. if_cases K; zify_cond K; rewrite land_ones64_neg in K by lia; [clear K| exfalso; lia].
  apply evt_done. eapply ILOOP_intro; try reflexivity; [rewrite EF; reflexivity| exact HMEM].
Qed.

Lemma arm_TYPE_ok : forall flush, 0 <= flush <= 4 -> arm_stmt flush TYPE PC_TYPE (arm_TYPE ivar_ref flush).
Proof. intros flush RF X w x12 ms EF HL XO HW _ HP HM. exact (type_core flush X w _ x12 ms EF RF HL XO HW HP HM). Qed.
End Z_infl_a_type.


Module Z_infl_a_dict.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_pure Z_adler32.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_adler32 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_type.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface AdlerModel InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.AdlerModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma arm_DICT_eq : forall flush s c r,
  arm_DICT ivar_ref flush (mkW s c r)
  = if is_havedict s =? 0 then
      (* zlib 1.4 (zl14infl-r2's DICT row): total_in += in - avail_in before Z_NEED_DICT *)
      ARet Z_NEED_DICT (let w := RESTORE (mkW s c r) in
                        mkW (w_s w) (icset_total_in (w_c w) (wrap64 (ic_total_in (w_c w) + wrap32 (ir_in r - ic_avail_in (w_c w))))) (w_r w))
    else arm_TYPE ivar_ref flush (mkW (iset_mode (iset_check s iadler32_init) TYPE) (icset_adler c iadler32_init) r).
Proof.
  intros flush s c r. unfold arm_DICT, abind, gs. cbn [w_s]. destruct (is_havedict s =? 0); reflexivity.
Qed.

(* the need-dict exit's total_in update, as the machine computes it *)
Lemma dict_total_in_eq : forall t X h,
  wz (t + Z.land (Z.land (bv_swrap 32 (Z.land X 18446744073709551615 - h)) 18446744073709551615) 4294967295)
  = wz (wrap64 (t + wrap32 (X - h))).
Proof.
  intros t X h. apply Z_to_bv_eqm. rewrite wrap64_mod, wrap32_mod.
  change 18446744073709551615 with (Z.ones 64). change 4294967295 with (Z.ones 32).
  rewrite !Z.land_ones by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.div]. change (4294967296 / 2) with 2147483648.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma arm_DICT_ok : forall flush, 0 <= flush <= 4 -> arm_stmt flush DICT PC_DICT (arm_DICT ivar_ref flush).
Proof.
  intros flush RF X [s c r] x12 ms EF HL XO HW _ HP HM. rewrite arm_DICT_eq.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HAV : ir_have r <= 1 /\ ir_left r <= 1) by (rewrite Pin in Rnh; lia).
  assert (HISR : ISR s) by (split; assumption).
  destruct (Z.eq_dec (is_havedict s) 0) as [D0|D1].
  -
    replace (is_havedict s =? 0) with true by (symmetry; apply Z.eqb_eq; exact D0). cbv zeta. rewrite RESTORE_eq. cbn [w_s w_c w_r].
    assert (HPUT0 : ir_put r = 0) by (apply (NOPUTb_false _ _ (PATI_noput _ _ _ _ HP)); right; left; exact HM).
    clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW.
    iarm_open HL. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. open_izs ZS. ifineS m.
    unfold PC_DICT. zs. rewrite D0. zs. br_false.
    (* j to the need-dict block; RESTORE's six stores plus total_in += in -
       avail_in (ld, ld, subw, zext, add, sd); li s5,2; j *)
    do 16 zs.
    itr_groups MUf WMf.
    apply evt_done. split; [| cbn [wof]; eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| exact Pgz| first [reflexivity | exact (PATI_noput _ _ _ _ HP)]..|]; exact HISR].
    cbn [IPOST]. eapply IRET_intro; inorm; [ireg .. | | intros _; unfold RST; cbn [w_c w_r]; ired; repeat split; exact HPUT0].
    apply IMEML_intro; inorm.
    + exists (wz (ir_ret r)), jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app]. inorm. close_cells ZS.
      all: apply dict_total_in_eq.
    + constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
  -
    replace (is_havedict s =? 0) with false by (symmetry; apply Z.eqb_neq; exact D1).
    assert (D1' : is_havedict s = 1) by (destruct PHD; [contradiction| assumption]).
    set (w1 := mkW (iset_mode (iset_check s iadler32_init) TYPE) (icset_adler c iadler32_init) r).
    assert (HW1 : WINV w1).
    { unfold WINV, w1. cbn [w_s w_c w_r]. split; [exact HCORE|]. split; [exact HREGS|].
      rewrite HM in HMF, HWF. unfold MF, WF in *. cbn in HMF, HWF |- *. destruct HMF as [HMF1 HMF2].
      split; [split; [split; [exact HMF1| intros _; exact adler_canon_1]| exact HMF2]|]. split; [exact HWF| exact HWB]. }
    assert (HP1 : PATI X w1).
    { unfold w1. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact HISR. }
    eapply (evt_cut psegs (fun ms' => exists x8' x12', ILOOP X w1 PC_TYPE x8' x12' ms')).
    2:{ intros ms1 (x8' & x12' & H1). exact (type_core flush X w1 x8' x12' ms1 EF RF H1 XO HW1 HP1 eq_refl). }
    clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW HW1 HP1. subst w1.
    iarm_open HL. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. open_izs ZS. ifineS m.
    unfold PC_DICT. zs. rewrite D1'. zs. br_true.
    do 5 zs.
    call (adler32_null_spec).
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ eassumption. }
    do 10 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; inorm; [ireg .. |].
    apply IMEM_intro; inorm.
    + exists jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE, iadler32_init. cbn [app]. inorm. close_cells ZS.
    + constructor; inorm; [unfold isA, isA_cells, iadler32_init; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
Qed.
End Z_infl_a_dict.


Module Z_infl_a_check.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Z_adler32 Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface AdlerModel InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CHECK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CHECK DeflateLz RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.AdlerModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CHECK.RefInflateA_LENGTH OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CHECK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_CHECK_T : Z := 0x1deb8.


Lemma arm_LENGTH_ok : forall flush, arm_stmt flush LENGTH PC_LENGTH arm_LENGTH.
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  rewrite (arm_LENGTH_skip s c r (or_intror Pf0)). unfold done_w.
  destruct HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (HISR : ISR s) by (split; assumption).
  clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS.
  iarm_open HL. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  unfold PC_LENGTH. do 2 zs. rewrite Pw. zs. br_false. zs. rewrite Pf0. zs. br_true.
  do 7 zs.
  itr_groups MUf WMf.
  apply evt_done. split; [| cbn [wof]; eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold DONE, FLAGS, HCRC; cbn; lia| reflexivity..|]; exact HISR].
  cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
  apply IMEML_intro; inorm.
  + exists (wz (ir_ret r)), jf. exact FRM.
  + exact STK.
  + exact ZS.
  + constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
  + exact IN.
  + unfold iout. exact OUT.
  + eassumption.
  + exact MU.
  + exact WM.
Qed.


Definition PC_CHECK_NB : Z := 0x1d2a4.
Definition PC_CHECK_J : Z := 0x1da80.

Lemma check_nb32 : forall X s c r q v13 ms,
  ILOOPg X (mkW s c r) PC_CHECK_NB q ms -> sc26 q = wz (il_NI (ix_L X) + ir_next r) -> sc13 q = v13 ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) ->
  evt psegs (NBJg X s c r 32 PC_CHECK_J (fun r1 q1 => sc13 q1 = v13
               /\ sc26 q1 = wz (il_NI (ix_L X) + ir_next r1) /\ sc27 q1 = wz (il_NI (ix_L X) + ir_next r1))) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] v13 ms HL E26 E13 XO HREGS HP.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x26 v13.
  pose proof HMEM as ((jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  unfold PC_CHECK_NB. ix_open XO.
  do 2 zs. br_cases K.
  -
    do 1 zs. apply evt_done. left. eexists r, _. split; [|split; [|split]].
    + apply nb_enough. lia.
    + left. split; [reflexivity| lia].
    + eapply ILOOPg_intro; ired; [ireg .. |]. exact HMEM.
    + cbn [sc13 sc26 sc27]. repeat split; reflexivity.
  - do 2 zs. br_cases K2.
    +
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      do 3 zs. clear RD. do 8 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      br_cases K3.
      *
        zs. br_false. do 2 zs.
        apply evt_done. right. exists (pullr c r). split; [|split].
        -- apply nb_pull_dry; lia.
        -- right. reflexivity.
        -- eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
      * zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
        -- apply nb_pull_ok; lia.
        -- right. split; [reflexivity| lia].
        -- eapply ILOOPg_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| reflexivity..].
        -- cbn [sc13 sc26 sc27]. pullr_rw c r. repeat split; ireg.
    +
      do 2 zs.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.



Definition chk_ov (s : inflate_state) (c : icall) (r : iregs) : option Z :=
  if chk_out r =? 0 then None
  else Some (UPDATE_CHECK_bytes s (is_check s) (arr_slice (ic_outbuf c) (ir_put r - chk_out r) (chk_out r))).

Lemma check_mid : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_CHECK_J q ms -> sc13 q = wz 5 ->
  sc27 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) -> is_flags s = 0 -> adler_canon (is_check s) -> ir_out r = arr_len (ic_outbuf c) ->
  evt psegs (fun ms' => exists q', ILOOPg X (mkW (chk_s3 s r (chk_ov s c r)) (chk_c3 c r (chk_ov s c r)) r) PC_CHECK_T q' ms'
                                   /\ sc13 q' = wz 5 /\ sc14 q' = wz 4 /\ sc27 q' = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E13 E27 XO HREGS HP Pf0 HCK HOUT.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & [POB POW]). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  destruct HCK as (CK1 & CK2 & CK3).
  assert (ECO : chk_out r = ir_put r).
  { unfold chk_out. rewrite HOUT, <- Rpl. replace (ir_put r + ir_left r - ir_left r) with (ir_put r) by lia. rewrite wrap32_id by lia. reflexivity. }
  assert (RPUT : ir_put r = 0 \/ ir_put r = 1) by lia.
  clear RH Rin Pfl PL PHD HREGS.
  iarm_openg HL. subst x13 x27. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_CHECK_J. do 6 zs. replace (ir_out r - ir_left r) with (ir_put r) by lia. rewrite land_u32_small by lia.
  do 6 zs. br_false. zs. br_cases K.
  -
    assert (EP : ir_put r = 0) by lia.
    assert (EOV : chk_ov s c r = None) by (unfold chk_ov; rewrite ECO, EP; reflexivity).
    rewrite EOV. unfold chk_s3, chk_c3, chk_s2, chk_c2. rewrite ECO.
    itr_groups MUf WMf.
    apply evt_done. eexists. split.
    { eapply ILOOPg_intro; ired; [ireg .. |].
      apply IMEM_intro; inorm.
      + exists jf. exact FRM.
      + exact STK.
      + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm. rewrite wz_wrap64. close_cells ZS.
      + constructor; inorm; [unfold isA, isA_cells; inorm; rewrite wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
      + exact IN.
      + unfold iout. exact OUT.
      + eassumption.
      + exact MU.
      + exact WM. }
    cbn [sc13 sc14 sc27]. repeat split; reflexivity.
  -
    assert (EP : ir_put r = 1) by lia.
    pose proof (POB 0 ltac:(lia)) as RBY.
    assert (EOV : chk_ov s c r = Some (adler32_len1 (is_check s) (arr_get (ic_outbuf c) 0))).
    { unfold chk_ov. rewrite ECO, EP. change (1 =? 0) with false. cbv iota. f_equal. unfold UPDATE_CHECK_bytes. rewrite Pf0. cbn [Z.eqb negb].
      change (arr_slice (ic_outbuf c) (1 - 1) 1) with [arr_get (ic_outbuf c) 0]. unfold iadler32_upd.
      apply adler32_model_len1; [exact (conj CK1 (conj CK2 CK3))| exact RBY]. }
    pose proof (iout_byte_at _ _ _ _ _ 0 OUT ltac:(lia) ltac:(lia)) as BY. rewrite Z.add_0_r in BY.
    rewrite EOV. unfold chk_s3, chk_c3, chk_s2, chk_c2. rewrite ECO. rewrite EP in *.
    zs. zs. rewrite Pf0. do 3 zs. br_true. replace (il_NO (ix_L X) + 1 + - (1)) with (il_NO (ix_L X)) by lia. zs.
    call (adler32_len1_spec).
    1:{ lia. } 1:{ lia. } 1:{ exact RBY. } 1:{ exact BY. } 1:{ eassumption. }
    zs. zs. rewrite Pw. do 8 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists. split.
    { eapply ILOOPg_intro; ired; [ireg .. |].
      apply IMEM_intro; inorm.
      + exists jf. exact FRM.
      + exact STK.
      + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm. rewrite wz_wrap64. close_cells ZS.
      + constructor; inorm; [unfold isA, isA_cells; inorm; rewrite wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
      + exact IN.
      + unfold iout. rewrite (iout_bytes_ext _ _ c) by reflexivity. rewrite EP. exact OUT.
      + eassumption.
      + exact MU.
      + exact WM. }
    cbn [sc13 sc14 sc27]. repeat split; reflexivity.
Qed.



Local Ltac close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma check_tail : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_CHECK_T q ms -> sc13 q = wz 5 -> sc14 q = wz 4 -> sc27 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) -> is_flags s = 0 -> adler_canon (is_check s) ->
  evt psegs (fun ms' => IPOST X (chk_tail s c r 5 (ZSWAP32 (ir_hold r))) ms' /\ PATI X (wof (chk_tail s c r 5 (ZSWAP32 (ir_hold r))))) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E13 E14 E27 XO HREGS HP Pf0 HCK.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HISR : ISR s) by (split; assumption).
  destruct HCK as (CK1 & _).
  clear RH Rin Pfl PL PHD HREGS.
  iarm_openg HL. subst x13 x14 x27. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_CHECK_T. zs. br_false. zs. rewrite Pf0. do 2 zs. br_false.
  do 14 zs. rewrite zswap_clang by lia.
  pose proof (ZSWAP32_range (ir_hold r)) as RZ.
  zs. br_cases K.
  -
    unfold chk_tail. change (Z.land 5 4 =? 0) with false. replace (ZSWAP32 (ir_hold r) =? is_check s) with false by (symmetry; apply Z.eqb_neq; exact K).
    cbn [negb andb]. unfold chk_r3.
    do 8 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
      close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + cbn [wof]. eapply PATI_step_out; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| ired; lia| reflexivity|]. exact HISR.
  -
    unfold chk_tail. change (Z.land 5 4 =? 0) with false. replace (ZSWAP32 (ir_hold r) =? is_check s) with true by (symmetry; apply Z.eqb_eq; exact K).
    cbn [negb andb]. rewrite (arm_LENGTH_skip (iset_mode s LENGTH) c _ (or_intror Pf0)). unfold done_w, chk_r3.
    do 6 zs. zs. br_false. zs. rewrite Pf0. zs. br_true. do 7 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
      apply IMEML_intro; inorm.
      * eexists _, jf. exact FRM.
      * exact STK.
      * eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS.
      * constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
      * exact IN.
      * unfold iout. exact OUT.
      * eassumption.
      * exact MU.
      * exact WM.
    + cbn [wof]. eapply PATI_step_out; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold DONE, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| ired; lia| reflexivity|]. exact HISR.
Qed.


Lemma arm_CHECK_run : forall s c r r1,
  is_wrap s = 5 -> is_flags s = 0 -> NEEDBITS 32 (mkW s c r) = ARun tt (mkW s c r1) ->
  arm_CHECK (mkW s c r) = chk_tail (chk_s3 s r1 (chk_ov s c r1)) (chk_c3 c r1 (chk_ov s c r1)) r1 5 (ZSWAP32 (ir_hold r1)).
Proof.
  intros s c r r1 Hw Hf HN. unfold chk_ov.
  assert (EV : chk_v s r1 = ZSWAP32 (ir_hold r1)) by (unfold chk_v; rewrite Hf; reflexivity).
  destruct (Z.eqb_spec (chk_out r1) 0) as [E0|NE0].
  - rewrite (arm_CHECK_run_noupd s c r r1 ltac:(lia) HN (or_intror E0)). rewrite Hw, EV. reflexivity.
  - rewrite (arm_CHECK_run_upd s c r r1 ltac:(lia) HN ltac:(rewrite Hw; discriminate) NE0). rewrite Hw, EV. reflexivity.
Qed.

Lemma arm_CHECK_ok : forall flush, arm_stmt flush CHECK PC_CHECK arm_CHECK.
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HISR : ISR s) by (split; assumption).
  rewrite HM in HMF, HWF. unfold MF, WF in HMF, HWF. cbn in HMF, HWF. destruct HMF as [_ HCK]. specialize (HCK Pf0).
  eapply (evt_cut psegs (NBJg X s c r 32 PC_CHECK_J (fun r1 q1 => sc13 q1 = wz 5
               /\ sc26 q1 = wz (il_NI (ix_L X) + ir_next r1) /\ sc27 q1 = wz (il_NI (ix_L X) + ir_next r1)))).
  { destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
    pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
    unfold PC_CHECK. zs. rewrite Pw. zs. br_false.
    eapply (check_nb32 X s c r (mkSC x5 x6 x7 (wz (-3)) x12 (wz 5) x14 x15 x16 x17 (wz (il_NI (ix_L X) + ir_next r)) x27 x28 x30));
      [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM] | reflexivity | reflexivity | exact XO | exact HREGS | exact HP]. }
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & E13 & E26 & E27)|(r1 & EN & HR1 & HLV)].
  2:{
      rewrite (arm_CHECK_dry s c r _ ltac:(lia) EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
  rewrite (arm_CHECK_run s c r r1 Pw Pf0 EN).
  destruct (NEEDBITS_spec c 32 s r HREGS ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & _ & EOUT & _).
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HP| assumption..]).
  assert (HOUT1 : ir_out r1 = arr_len (ic_outbuf c)) by (rewrite EOUT; exact HWF).
  eapply evt_cut; [exact (check_mid X s c r1 q1 ms1 HJ E13 E27 XO HREGS1 HP1 Pf0 HCK HOUT1)|].
  intros ms2 (q2 & HJ2 & E13' & E14' & E27').
  destruct (chk_c3_facts c r1 (chk_ov s c r1)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
  destruct (chk_s3_eq s r1 (chk_ov s c r1)) as (t & ck & ES3 & Rt & Eck).
  apply (check_tail X _ _ r1 q2 ms2 HJ2 E13' E14' E27' XO).
  - unfold REGS in *. rewrite F5, F6. exact HREGS1.
  - rewrite ES3. eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| cbn; rewrite HM; unfold CHECK, FLAGS, HCRC; lia| reflexivity| exact F5| exact F6| reflexivity| reflexivity| reflexivity| reflexivity| cbn [is_mode iset_check iset_total]; rewrite HM; reflexivity|]. exact HISR.
  - rewrite ES3. exact Pf0.
  - rewrite ES3. cbn [is_check iset_check]. rewrite Eck. unfold chk_ov. destruct (chk_out r1 =? 0); [exact HCK|].
    unfold UPDATE_CHECK_bytes. rewrite Pf0. cbn [Z.eqb negb]. apply adler32_model_canon.
Qed.
End Z_infl_a_check.


Module Z_infl_a_dictid.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Z_adler32 Zh_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_adler32 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_type OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_dict.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface AdlerModel InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateA_DICT DeflateLz RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.AdlerModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DICT OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ILOOP11 (X : ictx) (w : iw) (pc : Z) (x8 x11 x12 : word) : machine_state -> Prop :=
  fun ms => exists x5 x6 x7 x13 x14 x15 x16 x17 x27 x28 x30 m,
    ms = MS (mkR (wz (ir_left (w_r w))) (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) x5 x6 x7 (wz (il_As (ix_L X)))
                 x8 (wz (il_S (ix_L X))) x11 x12 x13 x14 x15 x16 x17
                 (wz (ir_have (w_r w))) (wz (il_NO (ix_L X) + ir_put (w_r w))) (wz 16209) (wz (-2))
                 (wz (il_As (ix_L X) + 168)) (wz (ir_hold (w_r w))) (wz (ir_bits (w_r w))) (wz 74976)
                 x27 (wz (il_NI (ix_L X) + ir_next (w_r w))) x28 (wz 30) x30 (wz (-16180)))
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom psegs)
    /\ IMEM X w m.

Lemma ILOOP11_intro : forall X w pc x8 x11 x12 x1 x2 x3 x4 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x1 = wz (ir_left (w_r w)) -> x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X ->
  x9 = wz (ir_have (w_r w)) -> x10 = wz (il_S (ix_L X)) ->
  x18 = wz (il_NO (ix_L X) + ir_put (w_r w)) -> x19 = wz 16209 -> x20 = wz (-2) -> x21 = wz (il_As (ix_L X) + 168) ->
  x22 = wz (ir_hold (w_r w)) -> x23 = wz (ir_bits (w_r w)) -> x24 = wz 74976 -> x25 = wz (il_As (ix_L X)) ->
  x26 = wz (il_NI (ix_L X) + ir_next (w_r w)) -> x29 = wz 30 -> x31 = wz (-16180) -> F = ix_F X -> fc = ix_fc X ->
  IMEM X w m ->
  ILOOP11 X w pc x8 x11 x12 (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
                          F (wz pc) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold ILOOP11. do 12 eexists. split; [reflexivity| assumption]. Qed.

Lemma dict_core11 : forall flush X w x8 x11 x12 ms,
  ix_flush X = flush -> 0 <= flush <= 4 -> ILOOP11 X w PC_DICT x8 x11 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = DICT ->
  evt psegs (fun ms' => IPOST X (arm_DICT ivar_ref flush w) ms' /\ PATI X (wof (arm_DICT ivar_ref flush w))) ms.
Proof.
  intros flush X [s c r] x8 x11 x12 ms EF RF HL XO HW HP HM. rewrite arm_DICT_eq.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HAV : ir_have r <= 1 /\ ir_left r <= 1) by (rewrite Pin in Rnh; lia).
  assert (HISR : ISR s) by (split; assumption).
  destruct (Z.eq_dec (is_havedict s) 0) as [D0|D1].
  -
    replace (is_havedict s =? 0) with true by (symmetry; apply Z.eqb_eq; exact D0). cbv zeta. rewrite RESTORE_eq. cbn [w_s w_c w_r].
    assert (HPUT0 : ir_put r = 0) by (apply (NOPUTb_false _ _ (PATI_noput _ _ _ _ HP)); right; left; exact HM).
    clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW.
    iarm_open HL. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. open_izs ZS. ifineS m.
    unfold PC_DICT. zs. rewrite D0. zs. br_false.
    (* j to the need-dict block; RESTORE's six stores plus total_in += in -
       avail_in (ld, ld, subw, zext, add, sd); li s5,2; j *)
    do 16 zs.
    itr_groups MUf WMf.
    apply evt_done. split; [| cbn [wof]; eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| exact Pgz| first [reflexivity | exact (PATI_noput _ _ _ _ HP)]..|]; exact HISR].
    cbn [IPOST]. eapply IRET_intro; inorm; [ireg .. | | intros _; unfold RST; cbn [w_c w_r]; ired; repeat split; exact HPUT0].
    apply IMEML_intro; inorm.
    + exists (wz (ir_ret r)), jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app]. inorm. close_cells ZS.
      all: apply dict_total_in_eq.
    + constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
  -
    replace (is_havedict s =? 0) with false by (symmetry; apply Z.eqb_neq; exact D1).
    assert (D1' : is_havedict s = 1) by (destruct PHD; [contradiction| assumption]).
    set (w1 := mkW (iset_mode (iset_check s iadler32_init) TYPE) (icset_adler c iadler32_init) r).
    assert (HW1 : WINV w1).
    { unfold WINV, w1. cbn [w_s w_c w_r]. split; [exact HCORE|]. split; [exact HREGS|].
      rewrite HM in HMF, HWF. unfold MF, WF in *. cbn in HMF, HWF |- *. destruct HMF as [HMF1 HMF2].
      split; [split; [split; [exact HMF1| intros _; exact adler_canon_1]| exact HMF2]|]. split; [exact HWF| exact HWB]. }
    assert (HP1 : PATI X w1).
    { unfold w1. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact HISR. }
    eapply (evt_cut psegs (fun ms' => exists x8' x12', ILOOP X w1 PC_TYPE x8' x12' ms')).
    2:{ intros ms1 (x8' & x12' & H1). exact (type_core flush X w1 x8' x12' ms1 EF RF H1 XO HW1 HP1 eq_refl). }
    clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW HW1 HP1. subst w1.
    iarm_open HL. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. open_izs ZS. ifineS m.
    unfold PC_DICT. zs. rewrite D1'. zs. br_true.
    do 5 zs.
    call (adler32_null_spec).
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ eassumption. }
    do 10 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; inorm; [ireg .. |].
    apply IMEM_intro; inorm.
    + exists jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE, iadler32_init. cbn [app]. inorm. close_cells ZS.
    + constructor; inorm; [unfold isA, isA_cells, iadler32_init; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
Qed.

Definition PC_DICTID_J : Z := 0x1d304.

Lemma dictid_nb32 : forall X s c r x12 ms,
  ILOOP X (mkW s c r) PC_DICTID (wz (-3)) x12 ms ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) ->
  evt psegs (NBJg X s c r 32 PC_DICTID_J (fun r1 q1 => sc8 q1 = wz (-3) /\ sc12 q1 = wz (il_NI (ix_L X) + ir_next r1))) ms.
Proof.
  intros X s c r x12 ms HL XO HREGS HP.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  unfold PC_DICTID. ix_open XO.
  do 2 zs. br_cases K.
  -
    do 1 zs. apply evt_done. left. eexists r, _. split; [|split; [|split]].
    + apply nb_enough. lia.
    + left. split; [reflexivity| lia].
    + eapply ILOOPg_intro; ired; [ireg .. |]. exact HMEM.
    + cbn [sc8 sc12]. split; reflexivity.
  - do 2 zs. br_cases K2.
    +
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      do 3 zs. clear RD. do 8 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      br_cases K3.
      *
        zs. br_false. do 2 zs.
        apply evt_done. right. exists (pullr c r). split; [|split].
        -- apply nb_pull_dry; lia.
        -- right. reflexivity.
        -- eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
      * zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
        -- apply nb_pull_ok; lia.
        -- right. split; [reflexivity| lia].
        -- eapply ILOOPg_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| reflexivity..].
        -- cbn [sc8 sc12]. pullr_rw c r. split; ireg.
    +
      do 2 zs.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Local Ltac close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma dictid_core : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_DICTID_J q ms -> sc8 q = wz (-3) -> sc12 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) ->
  evt psegs (fun ms' => exists x11' x12', ILOOP11 X (mkW (iset_mode (iset_check s (ZSWAP32 (ir_hold r))) DICT) (icset_adler c (ZSWAP32 (ir_hold r))) (irset_bits (irset_hold r 0) 0))
                                              PC_DICT (wz (-3)) x11' x12' ms') ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E8 E12 XO HREGS HP.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  clear RH Rin Pfl PL PHD HREGS.
  iarm_openg HL. subst x8 x12. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_DICTID_J. do 15 zs. rewrite zswap_clang by lia.
  pose proof (ZSWAP32_range (ir_hold r)) as RZ.
  do 5 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists _, _. eapply ILOOP11_intro; ired; [ireg .. |].
  close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma arm_DICTID_ok : forall flush, 0 <= flush <= 4 -> arm_stmt flush DICTID PC_DICTID (arm_DICTID ivar_ref flush).
Proof.
  intros flush RF X [s c r] x12 ms EF HL XO HW _ HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HISR : ISR s) by (split; assumption).
  assert (HPUT0 : ir_put r = 0) by (apply (NOPUTb_false _ _ (PATI_noput _ _ _ _ HP)); left; exact HM).
  rewrite HM in HMF, HWF. unfold MF, WF in HMF, HWF. cbn in HMF, HWF. destruct HMF as [HWB0 HCK].
  eapply evt_cut; [exact (dictid_nb32 X s c r x12 ms HL XO HREGS HP)|].
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & E8 & E12)|(r1 & EN & HR1 & HLV)].
  2:{ rewrite (arm_DICTID_dry flush s c r _ EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
  rewrite (arm_DICTID_run flush s c r r1 EN).
  destruct (NEEDBITS_spec c 32 s r HREGS ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & _ & EOUT & _).
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HP| assumption..]).
  eapply evt_cut; [exact (dictid_core X s c r1 q1 ms1 HJ E8 E12 XO HREGS1 HP1)|].
  intros ms2 (x11' & x12' & H2).
  apply (dict_core11 flush X _ _ x11' x12' ms2 EF RF H2 XO).
  -
    unfold WINV. cbn [w_s w_c w_r]. split; [exact HCORE|]. split.
    { destruct HREGS1 as (Rn & Rh & Rnh & Rp & Rl & Rpl & _ & Rin & Rli & Rlo). unfold REGS, HB. ired. change (2 ^ 0) with 1.
      split; [exact Rn|]. split; [exact Rh|]. split; [exact Rnh|]. split; [exact Rp|]. split; [exact Rl|]. split; [exact Rpl|]. split; [lia|]. split; [exact Rin|]. split; [exact Rli| exact Rlo]. }
    ired. unfold MF, WF. cbn. split; [split; [exact HWB0| lia]|]. split; [rewrite EOUT; exact HWF| intros E; rewrite EPUT; exact HPUT0].
  - eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold DICT, FLAGS, HCRC; cbn; lia| reflexivity..| |exact HISR].
    ired. rewrite EPUT, HPUT0. reflexivity.
  - reflexivity.
Qed.
End Z_infl_a_dictid.


Module Z_infl_a_head.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Z_infl_pure3 Z_adler32 Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface AdlerModel InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_HEAD DeflateLz RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.AdlerModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HDR OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_HEAD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_HEAD_NB : Z := 0x1d06c.
Definition PC_HEAD_J : Z := 0x1da08.

Lemma head_nb16 : forall X s c r q v12 ms,
  ILOOPg X (mkW s c r) PC_HEAD_NB q ms -> sc26 q = wz (il_NI (ix_L X) + ir_next r) -> sc12 q = v12 ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) ->
  evt psegs (NBJg X s c r 16 PC_HEAD_J (fun r1 q1 => sc12 q1 = v12
               /\ sc26 q1 = wz (il_NI (ix_L X) + ir_next r1) /\ sc27 q1 = wz (il_NI (ix_L X) + ir_next r1))) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] v12 ms HL E26 E12 XO HREGS HP.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x26 v12.
  pose proof HMEM as ((jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  unfold PC_HEAD_NB. ix_open XO.
  do 2 zs. br_cases K.
  -
    do 1 zs. apply evt_done. left. eexists r, _. split; [|split; [|split]].
    + apply nb_enough. lia.
    + left. split; [reflexivity| lia].
    + eapply ILOOPg_intro; ired; [ireg .. |]. exact HMEM.
    + cbn [sc12 sc26 sc27]. repeat split; reflexivity.
  - do 2 zs. br_cases K2.
    +
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      do 3 zs. clear RD. do 8 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      br_cases K3.
      *
        zs. br_false. do 2 zs.
        apply evt_done. right. exists (pullr c r). split; [|split].
        -- apply nb_pull_dry; lia.
        -- right. reflexivity.
        -- eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
      * zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
        -- apply nb_pull_ok; lia.
        -- right. split; [reflexivity| lia].
        -- eapply ILOOPg_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| reflexivity..].
        -- cbn [sc12 sc26 sc27]. pullr_rw c r. repeat split; ireg.
    +
      do 2 zs.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma PATI_step_bad : forall X s c r s' c' r', PATI X (mkW s c r) -> is_mode s = HEAD ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = is_flags s ->
  is_mode s' = BAD -> is_window_blk s' = is_window_blk s ->
  ic_input c' = ic_input c -> ic_outbuf c' = ic_outbuf c -> ir_put r' = ir_put r -> is_window s' = is_window s ->
  ir_out r' = ir_out r -> ir_left r' = ir_left r -> ISR s' -> PATI X (mkW s' c' r').
Proof.
  intros X s c r s' c' r' (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _ & (P12 & P13 & P14 & P15 & P16)) HM E1 E2 E3 E4 EM E6 E7 E8 E9 E10 E11 E12 HI.
  unfold PATI, OBYT in *. cbn [w_s w_c w_r] in *. rewrite E1, E2, E3, E4, E6, E7, E8, E9, E10, E11, E12, EM.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split. { destruct P4 as [F0|(F1 & _ & F3 & F4)]; [left; exact F0| right; split; [exact F1|]; split; [right; reflexivity|]; split; assumption]. }
  split; [unfold BAD, FLAGS, HCRC; lia|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|]. split; [exact P10|].
  split; [exact HI|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [reflexivity| exact P16].
Qed.

Local Ltac close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma head_core : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_HEAD_J q ms -> sc12 q = wz 5 -> sc26 q = wz (il_NI (ix_L X) + ir_next r) -> sc27 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) -> is_mode s = HEAD -> 16 <= ir_bits r -> ir_put r = 0 ->
  evt psegs (fun ms' => IPOST X (hd_zres s c r) ms' /\ PATI X (wof (hd_zres s c r))) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E12 E26 E27 XO HREGS HP HM HB16 HPUT0.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HISR : ISR s) by (split; assumption).
  unfold hd_zres. cbv zeta. rewrite Pw. change (Z.land 5 1 =? 0) with false. cbn [orb].
  rewrite (hd_x_spec (ir_hold r) RH64).
  clear RH Rin Pfl PL PHD HREGS.
  iarm_openg HL. subst x12 x26 x27. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_HEAD_J. do 2 zs. br_true. zs. rewrite Phd. zs. br_true. do 2 zs. br_false.
  do 12 zs. br_cases K; rewrite hd_x_clang in K by lia; change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by lia.
  2:{
      assert (E31 : (hd_x (ir_hold r) mod 31 =? 0) = false) by (apply Z.eqb_neq; intros E0; apply (proj2 (mod31_clang _ (hd_x_range _ RH64))) in E0; lia).
      rewrite E31. cbn [negb].
      do 8 zs.
      itr_groups MUf WMf.
      apply evt_done. split.
      + cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      + cbn [wof]. eapply PATI_step_bad; [exact HP| exact HM| reflexivity ..| exact HISR]. }
  assert (E31 : (hd_x (ir_hold r) mod 31 =? 0) = true) by (apply Z.eqb_eq; apply (proj1 (mod31_clang _ (hd_x_range _ RH64))); exact K).
  rewrite E31. cbn [negb]. clear K E31.
  assert (EB4 : forall h, 0 <= h -> BITSv h 4 = Z.land h 15) by (intros h Hh; rewrite BITSv_mod by lia; change 15 with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
  rewrite (EB4 _ (proj1 RH64)). unfold Z_DEFLATED.
  do 4 zs. br_cases K.
  -
    replace (Z.land (ir_hold r) 15 =? 8) with false by (symmetry; apply Z.eqb_neq; exact K). cbn [negb].
    do 14 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
      close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + cbn [wof]. eapply PATI_step_bad; [exact HP| exact HM| reflexivity ..| exact HISR].
  - replace (Z.land (ir_hold r) 15 =? 8) with true by (symmetry; apply Z.eqb_eq; exact K). cbn [negb].
    rewrite Pwb. do 4 zs.
    assert (RL4 : 0 <= Z.land (Z.shiftr (ir_hold r) 4) (Z.ones 4) <= 15).
    { rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (Z.shiftr (ir_hold r) 4) (2 ^ 4) ltac:(lia)) as Q. change (2 ^ 4) with 16 in Q. lia. }
    change (Z.ones 4) with 15 in RL4.
    assert (RS4 : 0 <= Z.shiftr (ir_hold r) 4) by (apply Z.shiftr_nonneg; lia).
    change (ir_hold (drop4 r)) with (Z.shiftr (ir_hold r) 4). rewrite (EB4 _ RS4).
    set (l4 := Z.land (Z.shiftr (ir_hold r) 4) 15) in *.
    br_cases K2.
    +
      replace (15 <? l4 + 8) with true by (symmetry; apply Z.ltb_lt; lia). cbn [orb].
      do 16 zs.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists. unfold drop4. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATI_step_bad; [exact HP| exact HM| reflexivity ..| exact HISR].
    + replace (15 <? l4 + 8) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
      zs. rewrite ?Pwb. do 2 zs. br_false. zs. br_true. zs. br_true.
      do 8 zs.
      call (adler32_null_spec).
      1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ eassumption. }
      do 5 zs. zs. br_cases K3.
      *
        replace (Z.land (Z.shiftr (ir_hold r) 4) 512 =? 0) with true by (symmetry; apply Z.eqb_eq; apply (fdict_clang _ RH64); exact K3). cbn [negb].
        do 14 zs.
        itr_groups MUf WMf. rewrite dmax_clang in GA by lia.
        apply evt_done. split.
        -- cbn [IPOST]. eexists. unfold hd_ok_s, r00, iadler32_init. eapply ILOOP_intro; ired; [ireg .. |].
           close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
        -- cbn [wof]. unfold hd_ok_s, r00. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| reflexivity| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact HISR.
      *
        replace (Z.land (Z.shiftr (ir_hold r) 4) 512 =? 0) with false by (symmetry; apply Z.eqb_neq; intros E0; apply (fdict_clang _ RH64) in E0; lia). cbn [negb].
        do 15 zs.
        itr_groups MUf WMf. rewrite dmax_clang in GA by lia.
        apply evt_done. split.
        -- cbn [IPOST]. eexists. unfold hd_ok_s, r00, iadler32_init. eapply ILOOP_intro; ired; [ireg .. |].
           close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
        -- cbn [wof]. unfold hd_ok_s, r00. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| reflexivity| unfold DICTID, FLAGS, HCRC; cbn; lia| reflexivity..| |exact HISR].
           ired. rewrite HPUT0. reflexivity.
Qed.


Lemma arm_HEAD_ok : forall flush, arm_stmt flush HEAD PC_HEAD (arm_HEAD ivar_ref).
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  rewrite HM in HWF. unfold WF in HWF. cbn in HWF. destruct HWF as [HOUT HPUT0].
  rewrite (arm_HEAD_eq s c r ltac:(rewrite Pwb; discriminate)). rewrite Pw. change (5 =? 0) with false. cbv iota.
  eapply (evt_cut psegs (NBJg X s c r 16 PC_HEAD_J (fun r1 q1 => sc12 q1 = wz 5
               /\ sc26 q1 = wz (il_NI (ix_L X) + ir_next r1) /\ sc27 q1 = wz (il_NI (ix_L X) + ir_next r1)))).
  { destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
    pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
    unfold PC_HEAD. zs. rewrite Pw. zs. br_false.
    eapply (head_nb16 X s c r (mkSC x5 x6 x7 (wz (-3)) (wz 5) x13 x14 x15 x16 x17 (wz (il_NI (ix_L X) + ir_next r)) x27 x28 x30));
      [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM] | reflexivity | reflexivity | exact XO | exact HREGS | exact HP]. }
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & E12 & E26 & E27)|(r1 & EN & HR1 & HLV)].
  2:{ rewrite EN. apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
  rewrite EN. unfold hd_res. rewrite Pw. change (negb (Z.land 5 2 =? 0)) with false. cbn [andb].
  destruct (NEEDBITS_spec c 16 s r HREGS ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & HB16 & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & _ & EOUT & _).
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HP| assumption..]).
  exact (head_core X s c r1 q1 ms1 HJ E12 E26 E27 XO HREGS1 HP1 HM HB16 ltac:(rewrite EPUT; exact HPUT0)).
Qed.
End Z_infl_a_head.


Module Z_infl_a_copy.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Z_infl_pure3 Z_updwin_pure Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_STORED OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST.RefInflateA_COPY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma sx32_u : forall L, 0 <= L < 2 ^ 32 -> bv_unsigned (sx32 (wz L)) = if L <? 2 ^ 31 then L else L + 18446744069414584320.
Proof.
  intros L HL. unfold sx32. rewrite (unsigned_lit L) by lia.
  destruct (Z.ltb_spec L (2 ^ 31)) as [H|H].
  - rewrite bv_swrap32_id by lia. apply unsigned_lit. lia.
  - replace (bv_swrap 32 L) with (L - 4294967296).
    + apply Z_to_bv_unsigned_neg64 || (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; change (2 ^ 64) with 18446744073709551616; change (2 ^ 31) with 2147483648 in H; change (2 ^ 32) with 4294967296 in HL; Z.div_mod_to_equations; lia).
    + unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change (4294967296 / 2) with 2147483648.
      change (2 ^ 31) with 2147483648 in H. change (2 ^ 32) with 4294967296 in HL. Z.div_mod_to_equations. lia.
Qed.

Lemma len_dec_cell : forall L, 0 < L < 2 ^ 32 ->
  le4 (wz (bv_swrap 32 (bv_unsigned (sx32 (wz L)) - 1))) = le4 (wz (wrap32 (L - 1))).
Proof.
  intros L HL. apply le4_wz_mod. rewrite sx32_u by lia. rewrite wrap32_id by lia.
  rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2 ^ 32) with 4294967296 in *. change (2 ^ 31) with 2147483648.
  destruct (Z.ltb_spec L 2147483648); Z.div_mod_to_equations; lia.
Qed.

Lemma av8_1 : forall a, av8 a 1 = [Z_to_bv 8 (arr_get a 0)].
Proof.
  intros a. apply list_ext_nth; [rewrite av8_length; reflexivity|].
  intros k Hk. rewrite av8_length in Hk. assert (k = 0%nat) as -> by lia. exact (av8_nth a 1 0 ltac:(lia)).
Qed.

Lemma iout_copy1 : forall rest0 c (inp : arr), length rest0 = 1%nat -> arr_len (ic_outbuf c) = 1 ->
  iout_bytes rest0 (icset_outbuf c (arr_blit (ic_outbuf c) 0 inp 0 1)) (0 + 1) = av8 inp 1.
Proof.
  intros rest0 c inp HL HO. rewrite blit1. rewrite <- (iout_bytes_store rest0 c 0 (arr_get inp 0)) by lia.
  rewrite iout_bytes_0. destruct rest0 as [|b [|b2 rest]]; try discriminate HL. cbn [upd Z.to_nat]. rewrite av8_1. reflexivity.
Qed.

Lemma copy_core : forall X w x8 x12 ms,
  ILOOP X w PC_COPY x8 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = COPY ->
  evt psegs (fun ms' => IPOST X (arm_COPY w) ms' /\ PATI X (wof (arm_COPY w))) ms.
Proof.
  intros X [s c r] x8 x12 ms HL XO HW HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HAV : ir_have r <= 1 /\ ir_left r <= 1) by (rewrite Pin in Rnh; lia).
  assert (HISR : ISR s) by (split; assumption).
  assert (RLEN : 0 <= is_length s < 2^32) by (destruct HCORE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H); exact H).
  assert (RMODE : 0 <= is_mode s < 2 ^ 31) by (rewrite HM; unfold COPY; lia).
  rewrite HM in HWF. unfold WF in HWF. cbn in HWF.
  clear RH HCORE HMF HWB Pfl PL PHD HREGS HW.
  iarm_open HL. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  pose proof (sx32_u _ RLEN) as ESX.
  unfold PC_COPY. do 2 zs. br_cases K0; rewrite ESX in K0.
  -
    assert (EL0 : is_length s = 0) by (destruct (Z.ltb_spec (is_length s) (2 ^ 31)); lia).
    rewrite (arm_COPY_zero s c r EL0).
    do 7 zs.
    itr_groups MUf WMf.
    apply evt_done. split; [| cbn [wof]; eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity..|]; exact HISR].
    cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    apply IMEM_intro; inorm.
    + exists jf. exact FRM.
    + exact STK.
    + exact ZS.
    + constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
  - assert (NL0 : is_length s <> 0) by (destruct (Z.ltb_spec (is_length s) (2 ^ 31)); lia).
    zs. br_cases K1; rewrite ?ESX in K1; [exfalso; destruct (Z.ltb_spec (is_length s) (2 ^ 31)); lia|].
    do 2 zs. br_cases K2.
    +
      do 2 zs. br_cases K3.
      *
        rewrite Pin in Rnh. rewrite Pout in Rpl.
        assert (EL1 : ir_left r = 1) by lia. assert (EH1 : ir_have r = 1) by lia.
        assert (EP0 : ir_put r = 0) by lia. assert (EN0 : ir_next r = 0) by lia.
        assert (ELI : arr_len (ix_input X) = 1) by lia.
        assert (ELR : length (ix_rest0 X) = 1%nat) by lia.
        assert (ECN : cpy_n s r = 1) by (unfold cpy_n; cbv zeta; destruct (Z.ltb_spec (ir_have r) (is_length s)); destruct (Z.ltb_spec (ir_left r) (ir_have r)); destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
        rewrite (arm_COPY_run s c r NL0 ltac:(rewrite ECN; discriminate)), ECN. unfold cpy_c, cpy_r.
        assert (HP' : PATI X (mkW (iset_length s (wrap32 (is_length s - 1))) (icset_outbuf c (arr_blit (ic_outbuf c) (ir_put r) (ic_input c) (ir_next r) 1))
                                  (irset_put (irset_left (irset_next (irset_have r (wrap32 (ir_have r - 1))) (ir_next r + 1)) (wrap32 (ir_left r - 1))) (ir_put r + 1)))).
        { destruct POB as (POB & POW & POL & _ & PHW). unfold PATI, OBYT. ired. rewrite arr_len_blit, HM.
          split; [exact Pw|]. split; [exact Pwb|]. split; [exact Phd|]. split; [left; exact Pf0|]. split; [unfold COPY, FLAGS, HCRC; lia|].
          split; [exact Pwin|]. split; [exact Pin|]. split; [exact Pin1|]. split; [exact Pout|]. split; [exact Pout1|]. split; [exact HISR|].
          split. { intros i Hi. rewrite blit1. destruct (Z.eq_dec i (ir_put r)) as [->|NE].
                   - rewrite arr_get_set_same by lia. apply Rin.
                   - rewrite arr_get_set_other by lia. apply POB. lia. }
          split; [exact POW|]. split; [rewrite EL1, EP0, HWF, Pout, ELR; change (wrap32 (1 - 1)) with 0; lia|]. split; [reflexivity| exact PHW]. }
        rewrite EL1, EH1, EP0, EN0 in *. rewrite iout_bytes_0 in OUT.
        apply rw_cells_of_u8arr in OUT. rewrite ELR in OUT.
        do 7 zs.
        rewrite ?Z.add_0_r in *.
        eapply evt_cut.
        { eapply (memcpy_Z (il_NO (ix_L X)) (il_NI (ix_L X)) 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (av8 (ix_input X) (arr_len (ix_input X))) (ix_rest0 X));
            [exact IN| rewrite av8_length, ELI; reflexivity| exact OUT| pose proof (xo_io _ XO) as SEPIO; unfold apart in SEPIO; rewrite ELI, ELR in SEPIO; lia| exact MI| lia| lia| lia]. }
        intros ms' PO. destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & PC & SRC').
        clear OUT SRC'.
        itr_groups MUc WMc.
        clear MUf WMf.
        transport_after_call psegs m m' MUc WMc. clear MUc WMc. ifine m'.
        replace (ret_pc (wz 119984)) with (wz 119984) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        do 17 zs.
        itr_groups MUf WMf.
        apply evt_done. split; [|exact HP'].
        cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
        apply IMEM_intro; inorm.
        -- exists jf. exact FRM.
        -- exact STK.
        -- exact ZS.
        -- constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA; apply len_dec_cell; lia| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
        -- exact IN.
        -- unfold iout. rewrite Pin. rewrite (iout_copy1 (ix_rest0 X) c (ix_input X) ELR ltac:(lia)). rewrite <- ELI. apply (u8arr_of_rw_cells psegs _ _ _ _ PC).
        -- eassumption.
        -- exact MU.
        -- exact WM.
      *
        assert (ECN : cpy_n s r = 0) by (unfold cpy_n; cbv zeta; destruct (Z.ltb_spec (ir_have r) (is_length s)); destruct (Z.ltb_spec (ir_left r) (ir_have r)); destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
        rewrite (arm_COPY_leave s c r NL0 ECN).
        do 2 zs.
        apply evt_done. split; [|exact HP].
        cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
        apply IMEML_intro; inorm.
        -- exists (wz (ir_ret r)), jf. exact FRM.
        -- exact STK.
        -- exact ZS.
        -- constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
        -- exact IN.
        -- unfold iout. exact OUT.
        -- eassumption.
        -- exact MU.
        -- exact WM.
    +
      zs. br_false.
      assert (ECN : cpy_n s r = 0) by (unfold cpy_n; cbv zeta; destruct (Z.ltb_spec (ir_have r) (is_length s)); destruct (Z.ltb_spec (ir_left r) (ir_have r)); destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
      rewrite (arm_COPY_leave s c r NL0 ECN).
      do 2 zs.
      apply evt_done. split; [|exact HP].
      cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
      apply IMEML_intro; inorm.
      * exists (wz (ir_ret r)), jf. exact FRM.
      * exact STK.
      * exact ZS.
      * constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
      * exact IN.
      * unfold iout. exact OUT.
      * eassumption.
      * exact MU.
      * exact WM.
Qed.

Lemma arm_COPY_ok : forall flush, arm_stmt flush COPY PC_COPY arm_COPY.
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (copy_core X w _ x12 ms HL XO HW HP HM). Qed.

Lemma arm_COPY__eq : forall s c r, arm_COPY_ (mkW s c r) = arm_COPY (mkW (iset_mode s COPY) c r).
Proof. intros s c r. unfold arm_COPY_. rewrite abind_run, set_mode_eq. reflexivity. Qed.

Lemma copy__core : forall X w x8 x12 ms,
  ILOOP X w PC_COPY_ x8 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = COPY_ ->
  evt psegs (fun ms' => IPOST X (arm_COPY_ w) ms' /\ PATI X (wof (arm_COPY_ w))) ms.
Proof.
  intros X [s c r] x8 x12 ms HL XO HW HP HM. rewrite arm_COPY__eq.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HISR : ISR s) by (split; assumption).
  set (w1 := mkW (iset_mode s COPY) c r).
  assert (HW1 : WINV w1).
  { unfold WINV, w1. cbn [w_s w_c w_r]. split; [exact HCORE|]. split; [exact HREGS|].
    rewrite HM in HMF, HWF. unfold MF, WF in *. cbn in HMF, HWF |- *. split; [exact HMF|]. split; [exact HWF| exact HWB]. }
  assert (HP1 : PATI X w1).
  { unfold w1. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold COPY, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact HISR. }
  eapply (evt_cut psegs (fun ms' => exists x12', ILOOP X w1 PC_COPY x8 x12' ms')).
  2:{ intros ms1 (x12' & H1). exact (copy_core X w1 x8 x12' ms1 H1 XO HW1 HP1 eq_refl). }
  clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW HW1 HP1. subst w1.
  iarm_open HL. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  unfold PC_COPY_. do 2 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. eapply ILOOP_intro; inorm; [ireg .. |].
  apply IMEM_intro; inorm.
  + exists jf. exact FRM.
  + exact STK.
  + exact ZS.
  + constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
  + exact IN.
  + unfold iout. exact OUT.
  + eassumption.
  + exact MU.
  + exact WM.
Qed.

Lemma arm_COPY__ok : forall flush, arm_stmt flush COPY_ PC_COPY_ arm_COPY_.
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (copy__core X w _ x12 ms HL XO HW HP HM). Qed.
End Z_infl_a_copy.


Module Z_infl_a_stored.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Z_infl_pure3 Z_updwin_pure Zh_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_updwin_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_copy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HDR OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_STORED OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST.RefInflateA_COPY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Lemma land24 : forall b, 0 <= b < 32 -> Z.land b 24 = b - Z.land b 7.
Proof.
  intros b Hb. destruct b as [|p|p]; [reflexivity| |lia].
  do 5 (destruct p as [p|p|]; try lia; try reflexivity).
Qed.

Lemma lxor_swap_eq : forall a b m, Z.lxor b a = m <-> a = Z.lxor b m.
Proof.
  intros a b m. split; intros H.
  - rewrite <- H. rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. reflexivity.
  - rewrite H. rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. reflexivity.
Qed.
Lemma lxor_lt_pow2 : forall a b n, 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= n -> 0 <= Z.lxor a b < 2 ^ n.
Proof.
  intros a b n Ha Hb Hn. assert (NN : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia). split; [exact NN|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|NZ]; [rewrite E; apply Z.pow_pos_nonneg; lia|].
  assert (LA : Z.log2 a < n). { destruct (Z.eq_dec a 0) as [->|Na]; [|apply Z.log2_lt_pow2; lia]. cbn. destruct (Z.eq_dec n 0) as [->|]; [|lia]. exfalso. change (2 ^ 0) with 1 in *. assert (b = 0) by lia. subst. apply NZ. reflexivity. }
  assert (LB : Z.log2 b < n). { destruct (Z.eq_dec b 0) as [->|Nb]; [|apply Z.log2_lt_pow2; lia]. cbn. destruct (Z.eq_dec n 0) as [->|]; [|lia]. exfalso. change (2 ^ 0) with 1 in *. assert (a = 0) by lia. subst. apply NZ. reflexivity. }
  apply Z.log2_lt_pow2; [lia|]. eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|]. apply Z.max_lub_lt; assumption.
Qed.

Definition PC_STORED_NB : Z := 0x1d188.
Definition PC_STORED_J : Z := 0x1d424.

Lemma stored_nb32 : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_STORED_NB q ms -> sc26 q = wz (il_NI (ix_L X) + ir_next r) -> sc8 q = wz (-3) ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) -> ir_bits r <= 31 ->
  evt psegs (NBJg X s c r 32 PC_STORED_J (fun r1 q1 => sc8 q1 = wz (-3) /\ sc26 q1 = wz (il_NI (ix_L X) + ir_next r1))) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E26 E8 XO HREGS HP HB31.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x26 x8.
  pose proof HMEM as ((jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  unfold PC_STORED_NB. ix_open XO.
  do 3 zs. br_cases K2.
  -
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    do 3 zs. clear RD. do 8 zs. rewrite <- Pin. rewrite !pull_shift by lia.
    br_cases K3.
    +
      zs. br_false. do 4 zs.
      apply evt_done. right. exists (pullr c r). split; [|split].
      * apply nb_pull_dry; lia.
      * right. reflexivity.
      * eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
    + zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
      * apply nb_pull_ok; lia.
      * right. split; [reflexivity| lia].
      * eapply ILOOPg_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| reflexivity..].
      * cbn [sc8 sc26]. pullr_rw c r. split; ireg.
  -
    do 4 zs.
    apply evt_done. right. exists r. split; [|split].
    + apply nb_dry; lia.
    + left. reflexivity.
    + eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma stored_tail : forall flush X s c r q ms,
  ILOOPg X (mkW s c r) PC_STORED_J q ms -> sc8 q = wz (-3) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_flush X = flush -> 0 <= flush <= 4 -> ix_ok X -> WINV (mkW s c r) -> PATI X (mkW s c r) -> is_mode s = STORED ->
  evt psegs (fun ms' => IPOST X (st_tail flush s c r) ms' /\ PATI X (wof (st_tail flush s c r))) ms.
Proof.
  intros flush X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E8 E26 EF RF XO HW HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HISR : ISR s) by (split; assumption).
  unfold st_tail.
  destruct (Z.eqb_spec (Z.land (ir_hold r) 65535) (Z.lxor (Z.shiftr (ir_hold r) 16) 65535)) as [EQ|NEQ]; cbn [negb].
  -
    replace (flush =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia).
    set (w2 := mkW (iset_mode (iset_length s (Z.land (wrap32 (ir_hold r)) 65535)) COPY_) c (irset_bits (irset_hold r 0) 0)).
    assert (RL16 : 0 <= Z.land (wrap32 (ir_hold r)) 65535 < 2 ^ 32).
    { rewrite land16_wrap32 by lia. pose proof (Z.mod_pos_bound (ir_hold r) (2 ^ 16) ltac:(lia)) as Q. change (2 ^ 16) with 65536 in Q. lia. }
    assert (HW2 : WINV w2).
    { unfold WINV, w2. cbn [w_s w_c w_r]. split.
      { destruct HCORE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14). unfold CORE. ired. repeat (split; [assumption|]). exact RL16. }
      split. { unfold REGS, HB. ired. change (2 ^ 0) with 1.
               split; [exact Rn|]. split; [exact Rh|]. split; [exact Rnh|]. split; [exact Rp|]. split; [exact Rl|]. split; [exact Rpl|]. split; [lia|]. split; [exact Rin|]. split; [exact Rli| exact Rlo]. }
      rewrite HM in HMF, HWF. unfold MF, WF in *. cbn in HMF, HWF |- *. split; [split; [exact HMF| lia]|]. split; [exact HWF| exact HWB]. }
    assert (HP2 : PATI X w2).
    { unfold w2. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold COPY_, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact HISR. }
    eapply (evt_cut psegs (fun ms' => exists x12', ILOOP X w2 PC_COPY_ (wz (-3)) x12' ms')).
    2:{ intros ms1 (x12' & H1). exact (copy__core X w2 _ x12' ms1 H1 XO HW2 HP2 eq_refl). }
    clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW HW2 HP2. subst w2.
    iarm_openg HL. subst x8 x26. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. ifine m.
    assert (RX : 0 <= Z.lxor (Z.shiftr (ir_hold r) 16) (Z.land (ir_hold r) 65535) < 2 ^ 64).
    { rewrite (proj2 (lxor_swap_eq _ _ 65535) EQ). lia. }
    unfold PC_STORED_J. do 6 zs. zs. if_cases K; br_norm K; [exfalso; apply K; apply lxor_swap_eq; exact EQ|]. clear K.
    do 7 zs. br_true.
    itr_groups MUf WMf.
    assert (E16 : Z.land (ir_hold r) 65535 = Z.land (wrap32 (ir_hold r)) 65535).
    { rewrite land16_wrap32 by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. }
    rewrite E16 in GA.
    apply evt_done. eexists. eapply ILOOP_intro; inorm; [ireg .. |].
    apply IMEM_intro; inorm.
    + exists jf. exact FRM.
    + exact STK.
    + exact ZS.
    + constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
  -
    clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW.
    iarm_openg HL. subst x8 x26. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. open_izs ZS. ifineS m.
    assert (RX : 0 <= Z.lxor (Z.shiftr (ir_hold r) 16) (Z.land (ir_hold r) 65535) < 2 ^ 64).
    { apply lxor_lt_pow2; [| |lia].
      - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. change (2 ^ 64) with 18446744073709551616 in *. Z.to_euclidean_division_equations. lia.
      - change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (ir_hold r) (2 ^ 16) ltac:(lia)) as Q. change (2 ^ 16) with 65536 in Q. change (2 ^ 64) with 18446744073709551616. lia. }
    unfold PC_STORED_J. do 6 zs. zs. if_cases K; br_norm K; [|exfalso; apply NEQ; apply lxor_swap_eq; exact K]. clear K.
    do 9 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
      close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + cbn [wof]. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact HISR.
Qed.

Lemma arm_STORED_ok : forall flush, 0 <= flush <= 4 -> arm_stmt flush STORED PC_STORED (arm_STORED ivar_ref flush).
Proof.
  intros flush RF X [s c r] x12 ms EF HL XO HW _ HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  destruct (bb_r_facts r ltac:(lia) RH) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11).
  pose proof (land7_le (ir_bits r) ltac:(lia)) as R7.
  assert (HREGSb : REGS c (bb_r r)).
  { unfold REGS, HB. rewrite B1, B2, B3, B4. split; [exact Rn|]. split; [exact Rh|]. split; [exact Rnh|]. split; [exact Rp|]. split; [exact Rl|]. split; [exact Rpl|].
    split; [split; [rewrite B8; lia| exact B11]|]. split; [exact Rin|]. split; [exact Rli| exact Rlo]. }
  assert (HPb : PATI X (mkW s c (bb_r r))) by (eapply PATI_regs; [exact HP| assumption..]).
  eapply (evt_cut psegs (NBJg X s c (bb_r r) 32 PC_STORED_J (fun r1 q1 => sc8 q1 = wz (-3) /\ sc26 q1 = wz (il_NI (ix_L X) + ir_next r1)))).
  { destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
    assert (HMEMb : IMEM X (mkW s c (bb_r r)) m) by (eapply IMEM_regs; [exact HMEM| assumption..]).
    unfold PC_STORED. do 4 zs. rewrite (land63_small (Z.land (ir_bits r) 7)) by lia. br_cases K.
    -
      zs. rewrite land_m8_u64 by lia.
      apply evt_done. left. eexists (bb_r r), _. split; [|split; [|split]].
      + apply nb_enough. rewrite B8. lia.
      + left. split; [reflexivity|]. rewrite B8. lia.
      + eapply ILOOPg_intro; [..| exact HMEMb]; rewrite ?B1, ?B2, ?B3, ?B4, ?B8, ?B9; ired; ireg.
      + cbn [sc8 sc26]. rewrite B1. split; reflexivity.
    -
      zs. rewrite land24 by lia.
      eapply (stored_nb32 X s c (bb_r r) (mkSC x5 x6 x7 (wz (-3)) _ _ x14 x15 x16 x17 (wz (il_NI (ix_L X) + ir_next r)) x27 x28 x30));
        [eapply ILOOPg_intro; [..| exact HMEMb]; rewrite ?B1, ?B2, ?B3, ?B4, ?B8, ?B9; ired; ireg | cbn [sc26]; rewrite B1; reflexivity | reflexivity | exact XO | exact HREGSb | exact HPb | rewrite B8; lia]. }
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & E8 & E26)|(r1 & EN & HR1 & HLV)].
  2:{ rewrite (arm_STORED_dry flush s c r _ EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HPb| eapply PATI_regs; [exact HPb| reflexivity..]]. }
  rewrite (arm_STORED_run flush s c r r1 EN).
  destruct (NEEDBITS_spec c 32 s (bb_r r) HREGSb ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & _ & EOUT & _).
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HPb| assumption..]).
  assert (HW1 : WINV (mkW s c r1)).
  { unfold WINV. cbn [w_s w_c w_r]. split; [exact HCORE|]. split; [exact HREGS1|].
    rewrite HM in HMF, HWF |- *. unfold MF, WF in *. cbn in HMF, HWF |- *. split; [exact HMF|]. split; [rewrite EOUT, B6; exact HWF| intros E; rewrite EPUT, B3; exact (HWB E)]. }
  exact (stored_tail flush X s c r1 q1 ms1 HJ E8 E26 EF RF XO HW1 HP1 HM).
Qed.
End Z_infl_a_stored.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.

Module Z_infl_a_lenext.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_match OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_distext OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST.RefInflateA_LENEXT OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_LENEXT_NB : Z := 0x1d0d8.
Definition PC_LENEXT_OFF : Z := 0x1e55c.
Definition PC_LENEXT_J : Z := 0x1d96c.

Lemma lenext_nb : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_LENEXT_NB q ms -> sc13 q = wz (is_extra s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) -> 1 <= is_extra s <= 15 ->
  evt psegs (NBJh X s c r (is_extra s) PC_LENEXT_J) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E13 E26 XO HREGS HP REX.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x13 x26.
  pose proof HMEM as ((jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  unfold PC_LENEXT_NB. ix_open XO.
  zs. br_cases K.
  -
    do 3 zs. apply evt_done. left. eexists r, _. split; [|split; [|split]].
    + apply nb_enough. lia.
    + left. split; [reflexivity| lia].
    + eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
    + cbn [h12 h13 h14 h15 h22 h29 h31]. repeat split; reflexivity.
  - do 4 zs. br_cases K2.
    +
      assert (H1 : ir_have r = 1) by lia.
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 7 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      br_cases K3.
      *
        zs. br_false. do 9 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r). split; [|split].
        -- apply nb_pull_dry; lia.
        -- right. reflexivity.
        -- unfold hide in RH. eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
      * zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
        -- apply nb_pull_ok; lia.
        -- right. split; [reflexivity| lia].
        -- eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
        -- unfold hide in RH. cbn [h12 h13 h14 h15 h22 h29 h31]. pullr_rw c r. repeat split; ireg.
    +
      assert (H0 : ir_have r = 0) by lia.
      do 9 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite !Z.add_0_r.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma lenext_fin : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_LENEXT_J q ms ->
  h12 q = wz (ir_have r1) -> h13 q = wz (is_extra s) -> h14 q = wz (ir_bits r1) -> h15 q = wz (il_NI (ix_L X) + ir_next r1) ->
  h22 q = wz (ir_hold r1) -> h29 q = wz 30 -> h31 q = wz (-16180) ->
  ix_ok X -> PATI X (mkW s c r) ->
  ir_in r1 = ir_in r -> ir_out r1 = ir_out r -> ir_ret r1 = ir_ret r -> ir_put r1 = ir_put r -> ir_left r1 = ir_left r ->
  1 <= is_extra s <= 15 -> 1 <= is_length s < 2^16 -> is_extra s <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2^64 ->
  0 <= ir_have r1 < 2^32 -> 0 <= ir_next r1 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists x8 x12, ILOOP X (mkW (lx_fin (lx_s s (ir_hold r1))) c (ddrop r1 (is_extra s))) PC_DIST x8 x12 ms') ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL E12 E13 E14 E15 E22 E29 E31 XO HP
         EI EO ER EP EL REX RLEN RB1 RH1 RHV1 RN1 RPUT.
  apply (ILOOPh_regs X s c r r1) in HL; [|assumption..].
  iarm_openh HL. subst x12 x13 x14 x15 x22 x29 x31.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LENEXT_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r1) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl psegs m) as WMf.
  pose proof (bv_swrap32_range (is_back s)) as RBK. pose proof (sx32_wz_u (is_back s)) as EBK. set (bk := bv_swrap 32 (is_back s)) in *.
  do 4 zs. rewrite EBK. do 4 zs. rewrite clang_mask32 by lia.
  pose proof (land_ones_rng (ir_hold r1) (is_extra s) ltac:(lia)) as RV. set (v := Z.land (ir_hold r1) (Z.ones (is_extra s))) in *.
  assert (RV' : 0 <= v < 32768) by (split; [lia|]; eapply Z.lt_le_trans; [exact (proj2 RV)|]; change 32768 with (2^15); apply Z.pow_le_mono_r; lia).
  clear RV.
  assert (EV : BITSv (ir_hold r1) (is_extra s) = v) by (unfold v; apply BITSv_land; lia).
  do 11 zs. rewrite (land63_small (is_extra s)) by lia.
  itr_groups MUf WMf.
  apply evt_done. eexists _, _. eapply ILOOP_intro; unfold lx_fin, lx_s, ddrop; ired; [ireg .. |].
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; rewrite EV, (wrap32_id (is_length s + v)) by lia; close_cells GA
                        | unfold isT, isT_cells; exists padT; inorm; rewrite EV, (wrap32_id (is_length s + v)) by lia; close_cells GT; unfold bk; apply le4_back_add
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.

Lemma lenext_off : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_LENEXT_OFF q ms -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> PATI X (mkW s c r) -> 1 <= is_length s < 2^16 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists x8 x12, ILOOP X (mkW (lx_fin s) c r) PC_DIST x8 x12 ms') ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E26 XO HP RLEN RPUT.
  iarm_openg HL. subst x26.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LENEXT_OFF.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl psegs m) as WMf.
  do 5 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists _, _. eapply ILOOP_intro; unfold lx_fin; ired; [ireg .. |].
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA | unfold isT, isT_cells; exists padT; inorm; close_cells GT
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.

Lemma lenext_core_on : forall X w q ms,
  ILOOPg X w PC_LENEXT_NB q ms -> sc13 q = wz (is_extra (w_s w)) -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LENEXT -> is_extra (w_s w) <> 0 ->
  evt psegs (fun ms' => IPOST X (arm_LENEXT ivar_ref w) ms' /\ PATI X (wof (arm_LENEXT ivar_ref w))) ms.
Proof.
  intros X [s c r] q ms HL E13 E26 XO HW HP HM NE0. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & REX & RLEN).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  rewrite (arm_LENEXT_on s c r NE0).
  eapply evt_cut; [exact (lenext_nb X s c r q ms HL E13 E26 XO HREGS HP ltac:(lia))|].
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & E12 & E13' & E14 & E15 & E22 & E29 & E31)|(r1 & EN & HR1 & HLV)].
  2:{ rewrite EN. apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
  rewrite EN.
  assert (HN : lenext_next (mkW s c r) = Some (mkW (lx_fin (lx_s s (ir_hold r1))) c (ddrop r1 (is_extra s)))).
  { unfold lenext_next. cbn [w_s w_c w_r]. replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE0). rewrite EN. reflexivity. }
  destruct (lenext_next_WINV _ _ HW HM HN) as [HW2 HM2].
  destruct (nb_r1_facts c r r1 (is_extra s) HREGS ltac:(rewrite Pin; exact Pin1) ltac:(lia) HR1) as (EI & EO & ER & EP & EL & RB1 & RH1 & RHV1 & RN1).
  assert (HP2 : PATI X (mkW (lx_fin (lx_s s (ir_hold r1))) c (ddrop r1 (is_extra s)))).
  { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold lx_fin; cbn [is_mode iset_mode]; unfold DIST, FLAGS, HCRC; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity|]. exact Pisr. }
  eapply evt_cut.
  { destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
    exact (lenext_fin X s c r r1 q1 ms1 HJ E12 E13' E14 E15 E22 E29 E31 XO HP EI EO ER EP EL ltac:(lia) RLEN RB1 RH1 RHV1 RN1 ltac:(lia)). }
  intros ms2 (x8' & x12' & H2). exact (dist_core X _ x8' x12' ms2 H2 XO HW2 HP2 HM2).
Qed.

Lemma lenext_core_off : forall X w q ms,
  ILOOPg X w PC_LENEXT_OFF q ms -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LENEXT -> is_extra (w_s w) = 0 ->
  evt psegs (fun ms' => IPOST X (arm_LENEXT ivar_ref w) ms' /\ PATI X (wof (arm_LENEXT ivar_ref w))) ms.
Proof.
  intros X [s c r] q ms HL E26 XO HW HP HM E0. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & REX & RLEN).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  rewrite (arm_LENEXT_off s c r E0).
  assert (HN : lenext_next (mkW s c r) = Some (mkW (lx_fin s) c r)).
  { unfold lenext_next. cbn [w_s w_c w_r]. rewrite E0. reflexivity. }
  destruct (lenext_next_WINV _ _ HW HM HN) as [HW2 HM2].
  assert (HP2 : PATI X (mkW (lx_fin s) c r)).
  { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold lx_fin; cbn [is_mode iset_mode]; unfold DIST, FLAGS, HCRC; lia| reflexivity..|]. exact Pisr. }
  eapply evt_cut.
  { destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _). exact (lenext_off X s c r q ms HL E26 XO HP RLEN ltac:(lia)). }
  intros ms2 (x8' & x12' & H2). exact (dist_core X _ x8' x12' ms2 H2 XO HW2 HP2 HM2).
Qed.

Lemma arm_LENEXT_ok : forall flush, arm_stmt flush LENEXT PC_LENEXT (arm_LENEXT ivar_ref).
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. cbn [w_s] in HM.
  pose proof HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in HMF. rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & REX & _).
  destruct (Z.eq_dec (is_extra s) 0) as [E0|NE0].
  - eapply (evt_cut psegs (fun ms1 => exists q, ILOOPg X (mkW s c r) PC_LENEXT_OFF q ms1 /\ sc26 q = wz (il_NI (ix_L X) + ir_next r))).
    2:{ intros ms1 (q & H1 & E26). exact (lenext_core_off X _ q ms1 H1 E26 XO HW HP HM E0). }
    destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
    pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
    unfold PC_LENEXT. zs. rewrite E0. zs. br_false. zs.
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|]. reflexivity.
  - eapply (evt_cut psegs (fun ms1 => exists q, ILOOPg X (mkW s c r) PC_LENEXT_NB q ms1 /\ sc13 q = wz (is_extra s) /\ sc26 q = wz (il_NI (ix_L X) + ir_next r))).
    2:{ intros ms1 (q & H1 & E13 & E26). exact (lenext_core_on X _ q ms1 H1 E13 E26 XO HW HP HM NE0). }
    destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
    pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
    unfold PC_LENEXT. do 2 zs. br_true.
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|]. cbn [sc13 sc26]. split; reflexivity.
Qed.
End Z_infl_a_lenext.


Module Z_infl_a_len1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_DIST2 RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_LEN.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST2.RefInflateA_LEN1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LEN OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_LEN_D : Z := 0x1e3b0.
Definition PC_LEN_J1 : Z := 0x1e428.

Lemma len_pre : forall X s c r x8 x12 ms,
  ILOOP X (mkW s c r) PC_LEN x8 x12 ms -> ix_ok X -> REGS c r -> PATI X (mkW s c r) -> 0 <= is_lenbits s <= 15 ->
  evt psegs (fun ms' => exists q, ILOOPg X (mkW (iset_back s 0) c r) PC_LEN_D q ms' /\ sc12 q = wz (is_lenbits s)
                                  /\ sc15 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ sc26 q = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros X s c r x8 x12 ms HL XO HREGS HP RN. iarm_open HL.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  clear RH Rin. ix_open XO. unfold PC_LEN.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl psegs m) as WMf.
  do 2 zs. br_true. do 4 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. |]| cbn [sc12 sc15 sc26]; repeat split; reflexivity].
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA | unfold isT, isT_cells; exists padT; inorm; close_cells GT
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.

Definition len_Q1 (X : ictx) (s : inflate_state) (r1 : iregs) (q : iscrh) : Prop :=
  h12 q = wz (ir_have r1) /\ h13 q = wz (ir_bits r1) /\ h27 q = wz (il_NI (ix_L X) + ir_next r1) /\ h22 q = wz (ir_hold r1)
  /\ h14 q = wz (code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))))
  /\ h17 q = wz (cp_addr (ix_L X) (is_lencode s) + 4 * dec_idx1 (is_lenbits s) (ir_hold r1))
  /\ h15 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ h29 q = wz 30 /\ h31 q = wz (-16180).

Lemma len_lvl1 : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_LEN_D q ms -> sc12 q = wz (is_lenbits s) -> sc15 q = wz (cp_addr (ix_L X) (is_lencode s)) ->
  sc26 q = wz (il_NI (ix_L X) + ir_next r) -> ix_ok X -> REGS c r -> PATI X (mkW s c r) ->
  0 <= is_lenbits s <= 15 -> cp_ofs_ok (is_lencode s) ->
  dlvl c s (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits r ->
  evt psegs (DECJ X s c r r (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits PC_LEN_J1 (len_Q1 X s)) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E12 E15 E26 XO HREGS HP RN CPO DL.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x12 x15 x26.
  pose proof HMEM as ((jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST. open_isA GA.
  unfold PC_LEN_D. ix_open XO.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *.
  pose proof (dec_idx1_land n (ir_hold r) ltac:(lia) RN) as EI0. pose proof (dec_idx1_range n (ir_hold r) ltac:(lia) RN) as RI0'.
  pose proof (dl_i0 _ _ _ _ _ _ DL) as RI0. pose proof (dl_n0 _ _ _ _ _ _ DL) as RN0. pose proof (ones_range15 n RN) as RMK.
  do 3 zs. rewrite clang_mask32 by lia. zs. rewrite EI0.
  set (i0 := dec_idx1 n (ir_hold r)) in *. set (e0 := code_at s p i0) in *.
  pose proof (code_bits_range e0) as RB0.
  do 2 zs.
  pose proof (code_rd_bits m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2 + 1)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. cbv beta. rewrite (bv8_small (code_bits e0)) by exact RB0. clear RD.
  zs. br_cases K.
  -
    destruct (dl_found0 _ _ _ _ _ _ DL ltac:(fold i0; fold e0; lia)) as [ED EC].
    do 3 zs. apply evt_done. left. eexists r, _. split; [exact ED|]. split; [exact EC|]. split; [fold i0; fold e0; lia|]. split; [exact RI0|].
    split; [left; reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold len_Q1. cbn [h12 h13 h14 h15 h17 h22 h27 h29 h31]. fold p. fold n. fold i0. fold e0. repeat split; try reflexivity.
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. lia.
  - assert (K' : ir_bits r < code_bits (code_at s p (dec_idx1 n (ir_hold r)))) by (fold i0; fold e0; exact K).
    do 5 zs. br_cases K2.
    +
      assert (H0 : ir_have r = 0) by lia.
      pose proof (dl_dry0 _ _ _ _ _ _ DL K' H0) as ED.
      do 9 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite !Z.add_0_r.
      apply evt_done. right. exists r. split; [exact ED|]. split; [left; reflexivity|].
      eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
    +
      assert (H1 : ir_have r = 1) by lia.
      destruct (dl_i1 _ _ _ _ _ _ DL K' H1) as [RI1 RN1].
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      assert (EH1 : arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r + ir_hold r = ir_hold (pullr c r)).
      { unfold hide in RH. rewrite pullr_hold by (first [assumption | lia]). lia. }
      pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r)) (ir_bits r) (ir_hold r) RBy ltac:(lia) RH) as PR.
      assert (RH1 : 0 <= ir_hold (pullr c r) < 2^64).
      { rewrite <- EH1. split; [lia|]. eapply Z.lt_le_trans; [rewrite Z.add_comm; exact (proj2 PR)|]. apply Z.pow_le_mono_r; lia. }
      rewrite EH1. clear PR EH1.
      pose proof (dec_idx1_land n (ir_hold (pullr c r)) ltac:(lia) RN) as EI1. pose proof (dec_idx1_range n (ir_hold (pullr c r)) ltac:(lia) RN) as RI1'.
      set (h1 := ir_hold (pullr c r)) in *.
      zs. rewrite EI1. set (i1 := dec_idx1 n h1) in *. set (e1 := code_at s p i1) in *. pose proof (code_bits_range e1) as RB1.
      do 2 zs.
      pose proof (code_rd_bits m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2 + 1)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e1 in RD. zs. cbv beta. rewrite (bv8_small (code_bits e1)) by exact RB1. clear RD.
      do 6 zs. br_cases K3.
      *
        assert (K3' : ir_bits (pullr c r) < code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r))))) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; exact K3).
        pose proof (dl_dry1 _ _ _ _ _ _ DL K' H1 K3') as ED.
        zs. br_true. do 9 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r). split; [exact ED|]. split; [right; split; [reflexivity| split; [exact H1| lia]]|].
        unfold hide in RH. subst e1 i1 h1. eapply ILEAVE_intro; ired; [ .. | eapply IMEML_of_IMEM; [exact HMEM| reflexivity..]]; pullr_rw c r; ireg.
      * assert (K3' : code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r)))) <= ir_bits (pullr c r)) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; lia).
        destruct (dl_found1 _ _ _ _ _ _ DL K' H1 K3') as [ED EC].
        zs. apply evt_done. left. eexists (pullr c r), _. split; [exact ED|]. split; [exact EC|]. split; [exact K3'|]. split; [exact RI1|].
        split; [right; split; [reflexivity| split; [exact H1| lia]]|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
        unfold hide in RH. unfold len_Q1. cbn [h12 h13 h14 h15 h17 h22 h27 h29 h31]. fold p. fold n. fold h1. fold i1. fold e1.
        repeat split; try reflexivity; try (pullr_rw c r; ireg).
        f_equal. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Definition PC_LEN_T : Z := 0x1e514.
Definition len_QT (X : ictx) (here : Z) (rt : iregs) (Bv : Z) (q : iscrh) : Prop :=
  h7 q = wz (code_op here) /\ h17 q = wz (code_val here) /\ h14 q = wz (code_bits here) /\ h16 q = wz Bv
  /\ h13 q = wz (ir_bits rt) /\ h22 q = wz (ir_hold rt) /\ h12 q = wz (ir_have rt) /\ h27 q = wz (il_NI (ix_L X) + ir_next rt)
  /\ h26 q = wz (il_As (ix_L X) + 7160) /\ h29 q = wz 30 /\ h31 q = wz (-16180).

Lemma len_two_cases : forall op, 0 <= op < 256 -> len_two op = false -> op = 0 \/ 16 <= op.
Proof.
  intros op Hop H. unfold len_two in H. destruct (Z.eqb_spec op 0) as [E|NE]; [left; exact E| right].
  cbn [negb andb] in H. rewrite (land240_le15 _ Hop) in H. apply Z.leb_gt in H. lia.
Qed.
Lemma len_two_true : forall op, 0 <= op < 256 -> len_two op = true -> 1 <= op <= 15.
Proof.
  intros op Hop H. unfold len_two in H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite (land240_le15 _ Hop) in H2. apply Z.leb_le in H2. apply negb_true_iff in H1. apply Z.eqb_neq in H1. lia.
Qed.

Lemma len_direct : forall X s c r0 r1 q ms,
  ILOOPh X (mkW s c r0) PC_LEN_J1 q ms -> len_Q1 X s r1 q -> ix_ok X ->
  0 <= dec_idx1 (is_lenbits s) (ir_hold r1) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) ->
  len_two (code_op (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)))) = false ->
  evt psegs (fun ms' => exists q', ILOOPh X (mkW s c r0) PC_LEN_T q' ms'
                                   /\ len_QT X (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) r1 0 q') ms.
Proof.
  intros X s c r0 r1 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO RI CPO TWO.
  destruct HQ as (E12 & E13 & E27 & E22 & E14 & E17 & E15 & E29 & E31).
  cbn [h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst x12 x13 x27 x22 x14 x17 x15 x29 x31.
  iarm_openh_keep HL HMEM.
  set (p := is_lencode s) in *. set (i := dec_idx1 (is_lenbits s) (ir_hold r1)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_val_range e) as RVAL. pose proof (code_bits_range e) as RBITS.
  open_IST ST. ix_open XO. unfold PC_LEN_J1.
  zs.
  pose proof (code_rd_op m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i)) MI Gc CPO RI eq_refl) as RD.
  fold e in RD. zs. cbv beta. rewrite (bv8_small (code_op e)) by exact ROP. clear RD.
  pose proof (code_rd_val m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i + 2)) MI Gc CPO RI eq_refl) as RD.
  fold e in RD. zs. rewrite (zx16_small (code_val e)) by exact RVAL. clear RD.
  destruct (len_two_cases _ ROP TWO) as [E0|K16].
  - rewrite E0. do 4 zs. if_cases K; br_norm K; [clear K| exfalso; cbn in K; lia].
    do 2 zs.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold len_QT. cbn [h7 h12 h13 h14 h16 h17 h22 h26 h27 h29 h31]. rewrite E0. repeat split; reflexivity.
  - do 4 zs. br_true. do 2 zs.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold len_QT. cbn [h7 h12 h13 h14 h16 h17 h22 h26 h27 h29 h31]. repeat split; reflexivity.
Qed.

Definition PC_LEN_J2 : Z := 0x1e4f0.
Definition len_Q2 (X : ictx) (s : inflate_state) (last : Z) (r2 : iregs) (q : iscrh) : Prop :=
  h5 q = wz (ir_have r2) /\ h6 q = wz (ir_bits r2) /\ h31 q = wz (il_NI (ix_L X) + ir_next r2) /\ h22 q = wz (ir_hold r2)
  /\ h28 q = wz (code_bits (code_at s (is_lencode s) (dec_idx2 last (ir_hold r2))))
  /\ h30 q = wz (cp_addr (ix_L X) (is_lencode s) + 4 * dec_idx2 last (ir_hold r2))
  /\ h14 q = wz (code_bits last) /\ h16 q = wz (code_bits last) /\ h26 q = wz (il_As (ix_L X) + 7160).

Lemma len_lvl2 : forall X s c r0 r1 q ms,
  ILOOPh X (mkW s c r0) PC_LEN_J1 q ms -> len_Q1 X s r1 q -> ix_ok X -> PATI X (mkW s c r0) ->
  ir_in r1 = ir_in r0 -> ir_out r1 = ir_out r0 -> ir_put r1 = ir_put r0 -> ir_left r1 = ir_left r0 -> ir_ret r1 = ir_ret r0 ->
  0 <= ir_have r1 <= 1 -> 0 <= ir_next r1 -> ir_next r1 + ir_have r1 = arr_len (ic_input c) -> 0 <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2 ^ ir_bits r1 ->
  (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  0 <= dec_idx1 (is_lenbits s) (ir_hold r1) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) ->
  forall last, last = code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) ->
  len_two (code_op last) = true -> code_bits last <= ir_bits r1 -> code_bits last + code_op last <= 31 ->
  dlvl c s (is_lencode s) (dec_idx2 last) (dec_need2 last) r1 ->
  evt psegs (DECJ X s c r0 r1 (is_lencode s) (dec_idx2 last) (dec_need2 last) PC_LEN_J2 (len_Q2 X s last)) ms.
Proof.
  intros X s c r0 r1 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO HP EI EO EP EL ER
         RHV RNX RNH RB RH Rin RI CPO last ELAST TWO KB K31 DL.
  destruct HQ as (E12 & E13 & E27 & E22 & E14 & E16 & E15 & E29 & E31).
  cbn [h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst x12 x13 x27 x22 x14 x17 x15 x29 x31.
  iarm_openh_keep HL HMEM.
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  set (p := is_lencode s) in *. set (i := dec_idx1 (is_lenbits s) (ir_hold r1)) in *. rewrite <- ELAST in *.
  pose proof (code_op_range last) as ROP. pose proof (code_val_range last) as RVAL. pose proof (code_bits_range last) as RBITS.
  pose proof (len_two_true _ ROP TWO) as K15.
  assert (RH64 : 0 <= ir_hold r1 < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  pose proof (Rin (ir_next r1)) as RBy. apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST. ix_open XO. unfold PC_LEN_J1.
  zs.
  pose proof (code_rd_op m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i)) MI Gc CPO RI eq_refl) as RD.
  rewrite <- ELAST in RD. zs. cbv beta. rewrite (bv8_small (code_op last)) by exact ROP. clear RD.
  pose proof (code_rd_val m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i + 2)) MI Gc CPO RI eq_refl) as RD.
  rewrite <- ELAST in RD. zs. rewrite (zx16_small (code_val last)) by exact RVAL. clear RD.
  do 4 zs. br_false.
  pose proof (ones_range31 (code_bits last + code_op last) ltac:(lia)) as RMK2.
  pose proof (land_ones_le (ir_hold r1) (code_bits last + code_op last) ltac:(lia)) as RHM.
  do 4 zs. rewrite clang_mask32 by lia. set (mk2 := Z.ones (code_bits last + code_op last)) in *.
  zs. set (hm := Z.land (ir_hold r1) mk2) in *.
  pose proof (shiftr_le hm (code_bits last) ltac:(lia) ltac:(lia)) as RSH.
  zs. rewrite (srlw_small hm (code_bits last)) by lia. set (sh := hm ≫ code_bits last) in *.
  do 3 zs. rewrite (zext32_x4 (sh + code_val last)) by lia.
  assert (EI2 : sh + code_val last = dec_idx2 last (ir_hold r1)) by (rewrite dec_idx2_clang by lia; reflexivity).
  rewrite EI2. pose proof (dl_i0 _ _ _ _ _ _ DL) as RI2. pose proof (dl_n0 _ _ _ _ _ _ DL) as RN2.
  set (i2 := dec_idx2 last (ir_hold r1)) in *. set (e2 := code_at s p i2) in *. pose proof (code_bits_range e2) as RB2.
  assert (EN2 : dec_need2 last e2 = code_bits last + code_bits e2) by (unfold dec_need2; rewrite wrap32_id by lia; reflexivity).
  rewrite EN2 in *.
  zs.
  pose proof (code_rd_bits m (ix_L X) s p i2 (wa (cp_addr (ix_L X) p + 4 * i2 + 1)) MI Gc CPO ltac:(lia) eq_refl) as RD.
  fold e2 in RD. zs. cbv beta. rewrite (bv8_small (code_bits e2)) by exact RB2. clear RD.
  do 2 zs. br_cases K.
  -
    destruct (dl_found0 _ _ _ _ _ _ DL ltac:(fold i2; fold e2; rewrite EN2; lia)) as [ED EC].
    do 3 zs. apply evt_done. left. eexists r1, _. split; [exact ED|]. split; [exact EC|]. split; [fold i2; fold e2; rewrite EN2; lia|]. split; [exact RI2|].
    split; [left; reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold len_Q2. cbn [h5 h6 h14 h16 h22 h26 h28 h30 h31]. fold p. fold i2. fold e2. repeat split; reflexivity.
  - assert (K' : ir_bits r1 < dec_need2 last (code_at s p (dec_idx2 last (ir_hold r1)))) by (fold i2; fold e2; rewrite EN2; exact K).
    do 5 zs. br_cases K2.
    +
      assert (H0 : ir_have r1 = 0) by lia.
      pose proof (dl_dry0 _ _ _ _ _ _ DL K' H0) as ED.
      do 8 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite ?Z.add_0_r, ?Z.add_0_l.
      apply evt_done. right. exists r1. split; [exact ED|]. split; [left; reflexivity|].
      eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| assumption..].
    +
      assert (H1 : ir_have r1 = 1) by lia.
      destruct (dl_i1 _ _ _ _ _ _ DL K' H1) as [RI3 RN3].
      assert (NXT : 0 <= ir_next r1 < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read psegs _ _ _ (ir_next r1) _ (wa (il_NI (ix_L X) + ir_next r1)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      assert (EH2 : arr_get (ic_input c) (ir_next r1) * 2 ^ ir_bits r1 + ir_hold r1 = ir_hold (pullr c r1)).
      { unfold hide in RH. rewrite pullr_hold by (first [assumption | lia]). lia. }
      pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r1)) (ir_bits r1) (ir_hold r1) RBy ltac:(lia) RH) as PR.
      assert (RH2 : 0 <= ir_hold (pullr c r1) < 2^64).
      { rewrite <- EH2. split; [lia|]. eapply Z.lt_le_trans; [rewrite Z.add_comm; exact (proj2 PR)|]. apply Z.pow_le_mono_r; lia. }
      rewrite EH2. clear PR EH2.
      pose proof (land_ones_le (ir_hold (pullr c r1)) (code_bits last + code_op last) ltac:(lia)) as RHM3. fold mk2 in RHM3.
      assert (EI3 : (Z.land (ir_hold (pullr c r1)) mk2 ≫ code_bits last) + code_val last = dec_idx2 last (ir_hold (pullr c r1))) by (rewrite dec_idx2_clang by lia; reflexivity).
      set (h2 := ir_hold (pullr c r1)) in *.
      zs. set (hm3 := Z.land h2 mk2) in *.
      pose proof (shiftr_le hm3 (code_bits last) ltac:(lia) ltac:(lia)) as RSH3.
      zs. rewrite (srlw_small hm3 (code_bits last)) by lia. set (sh3 := hm3 ≫ code_bits last) in *.
      do 3 zs. rewrite (zext32_x4 (sh3 + code_val last)) by lia. rewrite EI3.
      set (i3 := dec_idx2 last h2) in *. set (e3 := code_at s p i3) in *. pose proof (code_bits_range e3) as RB3.
      assert (EN3 : dec_need2 last e3 = code_bits last + code_bits e3) by (unfold dec_need2; rewrite wrap32_id by lia; reflexivity).
      rewrite EN3 in *.
      zs.
      pose proof (code_rd_bits m (ix_L X) s p i3 (wa (cp_addr (ix_L X) p + 4 * i3 + 1)) MI Gc CPO ltac:(lia) eq_refl) as RD.
      fold e3 in RD. zs. cbv beta. rewrite (bv8_small (code_bits e3)) by exact RB3. clear RD.
      do 7 zs. br_cases K3.
      *
        assert (K3' : ir_bits (pullr c r1) < dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r1))))) by (fold h2; fold i3; fold e3; rewrite EN3; rewrite pullr_bits by lia; exact K3).
        pose proof (dl_dry1 _ _ _ _ _ _ DL K' H1 K3') as ED.
        zs. br_true. do 8 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r1). split; [exact ED|]. split; [right; split; [reflexivity| split; [exact H1| lia]]|].
        unfold hide in RH. subst e3 i3 sh3 hm3 h2. eapply ILEAVE_intro; ired; [ .. | eapply IMEML_of_IMEM; [exact HMEM| assumption..]]; pullr_rw c r1; ireg.
      * assert (K3' : dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r1)))) <= ir_bits (pullr c r1)) by (fold h2; fold i3; fold e3; rewrite EN3; rewrite pullr_bits by lia; lia).
        destruct (dl_found1 _ _ _ _ _ _ DL K' H1 K3') as [ED EC].
        zs. apply evt_done. left. eexists (pullr c r1), _. split; [exact ED|]. split; [exact EC|]. split; [exact K3'|]. split; [exact RI3|].
        split; [right; split; [reflexivity| split; [exact H1| lia]]|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
        unfold hide in RH. unfold len_Q2. cbn [h5 h6 h14 h16 h22 h26 h28 h30 h31]. fold p. fold h2. fold i3. fold e3.
        repeat split; try reflexivity; try (pullr_rw c r1; ireg).
Qed.

Lemma len_j2 : forall X s c r0 r2 last q ms,
  ILOOPh X (mkW s c r0) PC_LEN_J2 q ms -> len_Q2 X s last r2 q -> ix_ok X ->
  0 <= dec_idx2 last (ir_hold r2) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) ->
  code_bits last <= ir_bits r2 <= 63 -> 0 <= ir_hold r2 < 2^64 ->
  evt psegs (fun ms' => exists q', ILOOPh X (mkW s c r0) PC_LEN_T q' ms'
                                   /\ len_QT X (code_at s (is_lencode s) (dec_idx2 last (ir_hold r2))) (ddrop r2 (code_bits last)) (code_bits last) q') ms.
Proof.
  intros X s c r0 r2 last [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO RI CPO RB RH.
  destruct HQ as (E5 & E6 & E31 & E22 & E28 & E30 & E14 & E16 & E26).
  cbn [h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst x5 x6 x31 x22 x28 x30 x14 x16 x26.
  iarm_openh_keep HL HMEM.
  set (p := is_lencode s) in *. set (i := dec_idx2 last (ir_hold r2)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_val_range e) as RVAL. pose proof (code_bits_range e) as RBITS.
  pose proof (code_bits_range last) as RLB.
  open_IST ST. ix_open XO. unfold PC_LEN_J2.
  pose proof (code_rd_op m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i)) MI Gc CPO RI eq_refl) as RD.
  fold e in RD. zs. cbv beta. rewrite (bv8_small (code_op e)) by exact ROP. clear RD.
  pose proof (code_rd_val m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i + 2)) MI Gc CPO RI eq_refl) as RD.
  fold e in RD. zs. rewrite (zx16_small (code_val e)) by exact RVAL. clear RD.
  do 7 zs. rewrite (land63_small (code_bits last)) by lia.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
  unfold len_QT, ddrop. cbn [h7 h12 h13 h14 h16 h17 h22 h26 h27 h29 h31 ir_bits ir_hold ir_have ir_next irset_bits irset_hold].
  repeat split; try reflexivity; ireg.
Qed.
End Z_infl_a_len1.

Module Z_infl_a_len.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_lenext OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_len1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_DIST2 RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_LEN.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST2.RefInflateA_LEN1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LEN OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition lt_s1 (s : inflate_state) (here Bv : Z) : inflate_state := iset_length (iset_back s (Bv + code_bits here)) (code_val here).
Definition lt_lx (s : inflate_state) (c : icall) (here : Z) (rt : iregs) (Bv : Z) : iw :=
  mkW (iset_mode (iset_extra (lt_s1 s here Bv) (Z.land (code_op here) 15)) LENEXT) c (ddrop rt (code_bits here)).

Local Ltac close_all jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| unfold isT, isT_cells; exists padT; inorm; close_cells GT
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma len_tail_walk : forall X s c r0 rt here Bv q ms,
  ILOOPh X (mkW s c r0) PC_LEN_T q ms -> len_QT X here rt Bv q -> ix_ok X -> PATI X (mkW s c r0) ->
  ir_in rt = ir_in r0 -> ir_out rt = ir_out r0 -> ir_ret rt = ir_ret r0 -> ir_put rt = ir_put r0 -> ir_left rt = ir_left r0 ->
  0 <= Bv < 256 ->
  code_bits here <= ir_bits rt <= 63 -> 0 <= ir_hold rt < 2^64 -> 0 <= ir_have rt < 2^32 -> 0 <= ir_next rt ->
  0 <= ir_put r0 <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
     if code_op here =? 0 then exists x8, ILOOP X (mkW (iset_mode (lt_s1 s here Bv) LIT) c (ddrop rt (code_bits here))) PC_DISPATCH x8 (wz LIT) ms'
     else if negb (Z.land (code_op here) 32 =? 0)
     then exists x8, ILOOP X (mkW (iset_mode (iset_back (lt_s1 s here Bv) (-1)) TYPE) c (ddrop rt (code_bits here))) PC_DISPATCH x8 (wz TYPE) ms'
     else if negb (Z.land (code_op here) 64 =? 0)
     then exists x8, ILOOP X (mkW (iset_mode (lt_s1 s here Bv) BAD) (icset_msg c MSG_invalid_literal_length_code) (ddrop rt (code_bits here))) PC_DISPATCH x8 (wz BAD) ms'
     else if Z.land (code_op here) 15 =? 0
     then exists q', ILOOPg X (lt_lx s c here rt Bv) PC_LENEXT_OFF q' ms' /\ sc26 q' = wz (il_NI (ix_L X) + ir_next rt)
     else exists q', ILOOPg X (lt_lx s c here rt Bv) PC_LENEXT_NB q' ms' /\ sc13 q' = wz (Z.land (code_op here) 15)
                     /\ sc26 q' = wz (il_NI (ix_L X) + ir_next rt)) ms.
Proof.
  intros X s c r0 rt here Bv [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO HP
         EI EO ER EP EL RBv RB RH RHV RNX RPUT.
  destruct HQ as (E7 & E17 & E14 & E16 & E13 & E22 & E12 & E27 & E26 & E29 & E31).
  cbn [h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst x7 x17 x14 x16 x13 x22 x12 x27 x26 x29 x31.
  apply (ILOOPh_regs X s c r0 rt) in HL; [|assumption..].
  iarm_openh HL.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  pose proof (code_op_range here) as ROP. pose proof (code_val_range here) as RVAL. pose proof (code_bits_range here) as RBITS.
  pose proof (land32_cases (code_op here) ROP) as R32. pose proof (land64_cases (code_op here) ROP) as R64. pose proof (land15_range (code_op here)) as R15.
  ix_open XO. unfold PC_LEN_T.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put rt) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT. open_izs ZS.
  pose proof (munch_refl [(il_S (ix_L X), il_S (ix_L X) + 112); (ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168);
                          (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl psegs m) as WMf.
  do 3 zs. rewrite (land63_small (code_bits here)) by lia. do 3 zs. br_cases K0.
  -
    replace (code_op here =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    do 6 zs. itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; unfold lt_s1, ddrop; ired; [ireg .. |].
    close_all jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  - replace (code_op here =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    do 2 zs. br_cases K32.
    +
      replace (Z.land (code_op here) 32 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      do 8 zs. itr_groups MUf WMf.
      apply evt_done. eexists. eapply ILOOP_intro; unfold lt_s1, ddrop; ired; [ireg .. |].
      close_all jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + replace (Z.land (code_op here) 32 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
      do 2 zs. br_cases K64.
      *
        replace (Z.land (code_op here) 64 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
        do 9 zs. itr_groups MUf WMf.
        apply evt_done. eexists. eapply ILOOP_intro; unfold lt_s1, ddrop; ired; [ireg .. |].
        close_all jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * replace (Z.land (code_op here) 64 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
        do 7 zs. br_cases K15.
        -- replace (Z.land (code_op here) 15 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
           itr_groups MUf WMf.
           apply evt_done. eexists. split; [eapply ILOOPg_intro; unfold lt_lx, lt_s1, ddrop; ired; [ireg .. |]| reflexivity].
           close_all jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
        -- replace (Z.land (code_op here) 15 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
           zs. itr_groups MUf WMf.
           apply evt_done. eexists. split; [eapply ILOOPg_intro; unfold lt_lx, lt_s1, ddrop; ired; [ireg .. |]| cbn [sc13 sc26]; split; reflexivity].
           close_all jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma len_fin : forall X s0 c r rt here sb Bv q ms,
  ILOOPh X (mkW s0 c r) PC_LEN_T q ms -> len_QT X here rt Bv q -> ix_ok X -> PATI X (mkW s0 c r) -> is_flags s0 = 0 ->
  ir_in rt = ir_in r -> ir_out rt = ir_out r -> ir_ret rt = ir_ret r -> ir_put rt = ir_put r -> ir_left rt = ir_left r ->
  addback sb (code_bits here) = iset_back s0 (Bv + code_bits here) -> 0 <= Bv < 256 ->
  code_bits here <= ir_bits rt <= 63 -> 0 <= ir_hold rt < 2^64 -> 0 <= ir_have rt < 2^32 -> 0 <= ir_next rt ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  (forall w2, len_tailnext c here rt sb = Some w2 -> WINV w2 /\ is_mode (w_s w2) = LENEXT) ->
  evt psegs (fun ms' => IPOST X (len_tail c here rt sb) ms' /\ PATI X (wof (len_tail c here rt sb))) ms.
Proof.
  intros X s0 c r rt here sb Bv q ms HL HQ XO HP Pf0 EI EO ER EP EL ESB RBv RB RH RHV RNX RPUT HWN.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  eapply evt_cut; [exact (len_tail_walk X s0 c r rt here Bv q ms HL HQ XO HP EI EO ER EP EL RBv RB RH RHV RNX RPUT)|].
  intros ms1 H1. unfold len_tail. unfold len_tailnext in HWN. cbv zeta. rewrite ESB. rewrite ESB in HWN. unfold lt_lx, lt_s1 in H1.
  destruct (code_op here =? 0).
  { destruct H1 as (x8' & H1). apply evt_done. split; [cbn [IPOST]; exists x8'; exact H1|]. cbn [wof].
    eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold LIT, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity|]. exact Pisr. }
  destruct (negb (Z.land (code_op here) 32 =? 0)).
  { destruct H1 as (x8' & H1). apply evt_done. split; [cbn [IPOST]; exists x8'; exact H1|]. cbn [wof].
    eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity|]. exact Pisr. }
  destruct (negb (Z.land (code_op here) 64 =? 0)).
  { destruct H1 as (x8' & H1). apply evt_done. split; [cbn [IPOST]; exists x8'; exact H1|]. cbn [wof].
    eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity|]. exact Pisr. }
  cbn [orb] in HWN. destruct (HWN _ eq_refl) as [HW3 HM3].
  assert (HP3 : PATI X (mkW (iset_mode (iset_extra (iset_length (iset_back s0 (Bv + code_bits here)) (code_val here)) (Z.land (code_op here) 15)) LENEXT) c (ddrop rt (code_bits here)))).
  { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold LENEXT, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity|]. exact Pisr. }
  destruct (Z.eqb_spec (Z.land (code_op here) 15) 0) as [E0|NE0].
  - destruct H1 as (q' & H1 & E26). exact (lenext_core_off X _ q' ms1 H1 E26 XO HW3 HP3 HM3 E0).
  - destruct H1 as (q' & H1 & E13 & E26). exact (lenext_core_on X _ q' ms1 H1 E13 E26 XO HW3 HP3 HM3 NE0).
Qed.

Lemma len_core : forall X w x8 x12 ms,
  ILOOP X w PC_LEN x8 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LEN ->
  evt psegs (fun ms' => IPOST X (arm_LEN ivar_ref w) ms' /\ PATI X (wof (arm_LEN ivar_ref w))) ms.
Proof.
  intros X [s c r] x8 x12 ms HL XO HW HP HM. cbn [w_s] in HM.
  pose proof (WINV_len_okb _ HW HM) as OKB. unfold len_okb in OKB. cbn [w_s w_c w_r] in OKB.
  pose proof HW as (HCORE & HREGS & HMF & _). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & [TL _]).
  pose proof (cpok_ofs_ok _ _ _ _ TL) as CPO.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HIN1 : arr_len (ic_input c) <= 1) by (rewrite Pin; exact Pin1).
  pose proof (DREGS_of_REGS c r HREGS HIN1) as DR.
  assert (Rin : forall i, 0 <= arr_get (ic_input c) i < 256) by (destruct HREGS as (_&_&_&_&_&_&_&H&_); exact H).
  assert (RPUT : 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X))) by (destruct HREGS as (_&_&_&Rp&Rl&Rpl&_); lia).
  (* 1.4 (zl14infl-r1 LEN row): the fast entry also needs bits < 8; here have <= 1, so the first test fails *)
  assert (HSLOW : ir_have r < 6 \/ ir_left r < 258 \/ 8 <= ir_bits r) by (left; destruct DR as (_&H&_); lia).
  replace ((6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8)) with false in OKB
    by (symmetry; apply andb_false_iff; left; apply andb_false_iff; left; apply Z.leb_gt; destruct DR as (_&H&_); lia).
  apply andb_prop in OKB. destruct OKB as [OKB OKD]. apply andb_prop in OKB. destruct OKB as [OKB _]. apply andb_prop in OKB. destruct OKB as [OKB _].
  apply andb_prop in OKB. destruct OKB as [RN1 RN2]. apply Z.leb_le in RN1, RN2.
  rewrite (arm_LEN_slow s c r HSLOW). cbv zeta.
  set (s0 := iset_back s 0) in *.
  assert (OKD0 : decode_okb len_two s0 c r (is_lencode s0) (is_lenbits s0) = true) by exact OKD.
  change (is_lencode s) with (is_lencode s0). change (is_lenbits s) with (is_lenbits s0).
  assert (HP0 : PATI X (mkW s0 c r)).
  { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| cbn; rewrite HM; unfold LEN, FLAGS, HCRC; lia| reflexivity..| |exact Pisr].
    cbn [is_mode s0 iset_back]. rewrite HM. reflexivity. }
  destruct (decode_okb_lvl1 _ _ _ _ _ _ OKD0) as [RN D1].
  pose proof (dlvl_of_dchk c s0 _ _ _ r D1 ltac:(destruct DR as (_&H&_); exact H) ltac:(destruct DR as (_&_&_&H&_); lia)) as DL1.
  change (DECODE1 (is_lencode s0) (is_lenbits s0)) with (DECODE_k 8 (is_lencode s0) (dec_idx1 (is_lenbits s0)) code_bits).
  eapply evt_cut; [exact (len_pre X s c r x8 x12 ms HL XO HREGS HP ltac:(lia))|].
  intros ms0 (q0 & HL0 & E12 & E15 & E26).
  eapply evt_cut; [exact (len_lvl1 X s0 c r q0 ms0 HL0 E12 E15 E26 XO HREGS HP0 RN CPO DL1)|].
  intros ms1 [(r1 & q1 & ED1 & EC1 & KB1 & RI1 & HR1 & HJ1 & HQ1)|(r1 & ED1 & HR1 & HLV)].
  2:{ rewrite ED1. apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct (dec_r1_facts c r r1 DR Rin HR1) as (_ & _ & EO1 & _ & EP1 & EL1). eapply PATI_regs; [exact HP0| assumption..]. }
  rewrite ED1.
  destruct (dec_r1_facts c r r1 DR Rin HR1) as (DR1 & EI1 & EO1 & ER1 & EP1 & EL1).
  assert (HN0 : len_next (mkW s c r) =
                if len_two (code_op (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1)))) then
                  match DECODE_k 8 (is_lencode s0) (dec_idx2 (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1))))
                                 (dec_need2 (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1)))) (mkW s0 c r1) with
                  | ARun here (mkW _ _ r2) => len_tailnext c here (ddrop r2 (code_bits (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1)))))
                                                (addback s0 (code_bits (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1)))))
                  | _ => None
                  end
                else len_tailnext c (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1))) r1 s0).
  { unfold len_next. cbn [w_s w_c w_r]. cbv zeta.
    replace ((6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8)) with false
      by (symmetry; apply andb_false_iff; left; apply andb_false_iff; left; apply Z.leb_gt; destruct DR as (_&H&_); lia).
    fold s0. change (is_lencode s) with (is_lencode s0). change (is_lenbits s) with (is_lenbits s0).
    change (DECODE1 (is_lencode s0) (is_lenbits s0)) with (DECODE_k 8 (is_lencode s0) (dec_idx1 (is_lenbits s0)) code_bits).
    rewrite ED1. reflexivity. }
  set (last := code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1))) in *.
  pose proof (code_bits_range last) as RLB.
  pose proof (DREGS_hold64 c r1 DR1) as RH1. destruct DR1 as (RNX1 & RHV1 & RNH1 & RB1 & RHB1).
  change (negb (code_op last =? 0) && (Z.land (code_op last) 240 =? 0)) with (len_two (code_op last)).
  change (DECODE2 (is_lencode s0) last) with (DECODE_k 8 (is_lencode s0) (dec_idx2 last) (dec_need2 last)).
  assert (HWN : forall sbx herex rtx, len_next (mkW s c r) = len_tailnext c herex rtx sbx ->
                forall w2, len_tailnext c herex rtx sbx = Some w2 -> WINV w2 /\ is_mode (w_s w2) = LENEXT).
  { intros sbx herex rtx E w2 E2. rewrite <- E in E2. exact (len_next_WINV _ _ HW HM E2). }
  destruct (len_two (code_op last)) eqn:TWO.
  -
    destruct (decode_okb_lvl2 _ _ _ _ _ _ r1 OKD0 EC1 KB1 TWO) as [K31 D2]. fold last in K31, D2.
    pose proof (dlvl_of_dchk c s0 _ _ _ r1 D2 RHV1 ltac:(lia)) as DL2.
    eapply evt_cut; [exact (len_lvl2 X s0 c r r1 q1 ms1 HJ1 HQ1 XO HP0 EI1 EO1 EP1 EL1 ER1 RHV1 RNX1 RNH1 RB1 RHB1 Rin RI1 CPO last eq_refl TWO KB1 K31 DL2)|].
    intros ms2 [(r2 & q2 & ED2 & EC2 & KB2 & RI2 & HR2 & HJ2 & HQ2)|(r2 & ED2 & HR2 & HLV)].
    2:{ rewrite ED2. apply evt_done. split; [exact HLV|]. cbn [wof].
        destruct (dec_r1_facts c r1 r2 (conj RNX1 (conj RHV1 (conj RNH1 (conj RB1 RHB1)))) Rin HR2) as (_ & _ & EO2 & _ & EP2 & EL2).
        eapply PATI_regs; [exact HP0| congruence..]. }
    rewrite ED2. rewrite ED2 in HN0.
    destruct (dec_r1_facts c r1 r2 (conj RNX1 (conj RHV1 (conj RNH1 (conj RB1 RHB1)))) Rin HR2) as (DR2 & EI2 & EO2 & ER2 & EP2 & EL2).
    pose proof (DREGS_hold64 c r2 DR2) as RH2. destruct DR2 as (RNX2 & RHV2 & RNH2 & RB2 & RHB2).
    set (e2 := code_at s0 (is_lencode s0) (dec_idx2 last (ir_hold r2))) in *. pose proof (code_bits_range e2) as RHB.
    assert (KB2' : code_bits last + code_bits e2 <= ir_bits r2) by (unfold dec_need2 in KB2; rewrite wrap32_id in KB2 by lia; exact KB2).
    eapply evt_cut; [exact (len_j2 X s0 c r r2 last q2 ms2 HJ2 HQ2 XO RI2 CPO ltac:(lia) RH2)|].
    intros ms3 (q3 & HJ3 & HQ3). fold e2 in HQ3.
    destruct (ddrop_facts' r2 (code_bits last) ltac:(lia) ltac:(lia) RH2) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    refine (len_fin X s0 c r (ddrop r2 (code_bits last)) e2 (addback s0 (code_bits last)) (code_bits last) q3 ms3 HJ3 HQ3 XO HP0 Pf0 _ _ _ _ _ _ RLB _ F7 _ _ RPUT (HWN _ _ _ HN0));
      try congruence; try lia.
    rewrite (addback00 s0 (code_bits last) (code_bits e2) eq_refl RLB RHB). f_equal. lia.
  -
    eapply evt_cut; [exact (len_direct X s0 c r r1 q1 ms1 HJ1 HQ1 XO RI1 CPO TWO)|].
    intros ms3 (q3 & HJ3 & HQ3). fold last in HQ3.
    refine (len_fin X s0 c r r1 last s0 0 q3 ms3 HJ3 HQ3 XO HP0 Pf0 EI1 EO1 ER1 EP1 EL1 _ ltac:(lia) _ RH1 _ _ RPUT (HWN _ _ _ HN0)); try lia.
    rewrite (addback0 s0 (code_bits last) eq_refl RLB). reflexivity.
Qed.

Lemma arm_LEN_ok : forall flush, arm_stmt flush LEN PC_LEN (arm_LEN ivar_ref).
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (len_core X w _ x12 ms HL XO HW HP HM). Qed.

Lemma len__core : forall X w x8 x12 ms,
  ILOOP X w PC_LEN_ x8 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LEN_ ->
  evt psegs (fun ms' => IPOST X (arm_LEN_ ivar_ref w) ms' /\ PATI X (wof (arm_LEN_ ivar_ref w))) ms.
Proof.
  intros X [s c r] x8 x12 ms HL XO HW HP HM. cbn [w_s] in HM.
  rewrite arm_LEN__eq.
  pose proof (WINV_LEN_ s c r HW HM) as HW2.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HP2 : PATI X (mkW (iset_mode s LEN) c r)).
  { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold LEN, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact Pisr. }
  eapply (evt_cut psegs (fun ms1 => exists x8' x12', ILOOP X (mkW (iset_mode s LEN) c r) PC_LEN x8' x12' ms1)).
  2:{ intros ms1 (x8' & x12' & H1). exact (len_core X _ x8' x12' ms1 H1 XO HW2 HP2 eq_refl). }
  pose proof HW as (_ & HREGS & _). cbn [w_s w_c w_r] in HREGS. destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
  clear HW HW2 HP HP2 Pfl Pgz Pisr POBY.
  iarm_open HL. ix_open XO. unfold PC_LEN_.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  do 2 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.

Lemma arm_LEN__ok : forall flush, arm_stmt flush LEN_ PC_LEN_ (arm_LEN_ ivar_ref).
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (len__core X w _ x12 ms HL XO HW HP HM). Qed.
End Z_infl_a_len.


Module Z_infl_a_table.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_t_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 RefInflateSafeOK3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_TABLE OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma tb_f1 : forall h, Z.land h 31 = h mod 2^5.
Proof. intros h. change 31 with (Z.ones 5). apply Z.land_ones. lia. Qed.
Lemma tb_f2 : forall h, 0 <= h < 2^64 -> Z.land (h ≪ 54) 18446744073709551615 ≫ 59 = h mod 2^10 / 2^5.
Proof.
  intros h H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^64) with 18446744073709551616 in *. change (2^54) with 18014398509481984. change (2^59) with 576460752303423488.
  change (2^10) with 1024. change (2^5) with 32. Z.div_mod_to_equations. lia.
Qed.
Lemma tb_f3 : forall h, 0 <= h < 2^64 -> Z.land (h ≪ 50) 18446744073709551615 ≫ 60 = h mod 2^14 / 2^10.
Proof.
  intros h H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^64) with 18446744073709551616 in *. change (2^50) with 1125899906842624. change (2^60) with 1152921504606846976.
  change (2^14) with 16384. change (2^10) with 1024. Z.div_mod_to_equations. lia.
Qed.
Lemma tb_ranges : forall h, 0 <= h mod 2^5 < 32 /\ 0 <= h mod 2^10 / 2^5 < 32 /\ 0 <= h mod 2^14 / 2^10 < 16.
Proof. intros h. change (2^5) with 32. change (2^10) with 1024. change (2^14) with 16384. Z.div_mod_to_equations. lia. Qed.

Definition PC_TABLE_J : Z := 0x1d4f0.

Lemma table_nb14 : forall X s c r x8 x12 ms,
  ILOOP X (mkW s c r) PC_TABLE x8 x12 ms -> ix_ok X -> REGS c r -> PATI X (mkW s c r) -> ir_bits r < 14 ->
  evt psegs (NBJg X s c r 14 PC_TABLE_J (fun r1 q => sc27 q = wz (il_NI (ix_L X) + ir_next r1))) ms.
Proof.
  intros X s c r x8 x12 ms HL XO HREGS HP MFB.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  unfold PC_TABLE. ix_open XO.
  do 2 zs. br_false. do 2 zs. br_cases K.
  -
    assert (H1 : ir_have r = 1) by lia.
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    do 2 zs.
    pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    zs. clear RD. do 8 zs. rewrite <- Pin. rewrite !pull_shift by lia. br_cases K3.
    +
      zs. br_false. do 2 zs.
      apply evt_done. right. exists (pullr c r). split; [|split].
      * apply nb_pull_dry; lia.
      * right. reflexivity.
      * unfold hide in RH. eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
    + zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
      * apply nb_pull_ok; lia.
      * right. split; [reflexivity| lia].
      * unfold hide in RH. eapply ILOOPg_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| reflexivity..].
      * cbn [sc27]. pullr_rw c r. ireg.
  -
    do 2 zs.
    apply evt_done. right. exists r. split; [|split].
    + apply nb_dry; lia.
    + left. reflexivity.
    + eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Local Ltac close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma table_fin : forall flush X s c r q ms,
  ix_flush X = flush ->
  ILOOPg X (mkW s c r) PC_TABLE_J q ms -> sc27 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> PATI X (mkW s c r) -> 14 <= ir_bits r <= 63 -> 0 <= ir_hold r < 2^64 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
     if (286 <? is_nlen (tb_s s (ir_hold r))) || (30 <? is_ndist (tb_s s (ir_hold r)))
     then exists x8, ILOOP X (mkW (iset_mode (tb_s s (ir_hold r)) BAD) (icset_msg c MSG_too_many_length_or_distance_symbols) (tb_r r)) PC_DISPATCH x8 (wz BAD) ms'
     else exists q', ILOOPg X (mkW (tb_s2 s (ir_hold r)) c (tb_r r)) PC_LENLENS_E q' ms' /\ sc12 q' = wz (is_ncode (tb_s2 s (ir_hold r)))
                     /\ sc15 q' = wz 0 /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros flush X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms EF HL E27 XO HP RB RH RPUT.
  iarm_openg HL. subst x27.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_TABLE_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  do 7 zs. rewrite tb_f1, (tb_f2 (ir_hold r) RH), (tb_f3 (ir_hold r) RH).
  destruct (tb_ranges (ir_hold r)) as (Ra & Rb & Rc).
  unfold tb_s2, tb_s, tb_r. cbn [is_nlen is_ndist is_ncode iset_ncode iset_ndist iset_nlen iset_have iset_mode].
  set (fa := ir_hold r mod 2^5) in *. set (fb := ir_hold r mod 2^10 / 2^5) in *. set (fc := ir_hold r mod 2^14 / 2^10) in *.
  do 8 zs. br_cases K1.
  {
    replace (286 <? fa + 257) with true by (symmetry; apply Z.ltb_lt; lia). cbn [orb].
    do 8 zs. itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM. }
  replace (286 <? fa + 257) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  do 2 zs. br_cases K2.
  {
    replace (30 <? fb + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    do 8 zs. itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM. }
  replace (30 <? fb + 1) with false by (symmetry; apply Z.ltb_ge; lia).
  do 5 zs. itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. |]| cbn [sc12 sc15 sc26]; repeat split; reflexivity].
  close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Section Table.
Variable flush : Z.
Hypothesis LENLENS_CORE : lenlens_core_stmt flush.

Lemma table_core : forall X w x8 x12 ms,
  ix_flush X = flush -> ILOOP X w PC_TABLE x8 x12 ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w -> is_mode (w_s w) = TABLE ->
  evt psegs (fun ms' => IPOST X (arm_TABLE ivar_ref flush w) ms' /\ PATI X (wof (arm_TABLE ivar_ref flush w))) ms.
Proof.
  intros X [s c r] x8 x12 ms EF HL XO HW HA HP HM. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & MFB).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  eapply evt_cut; [exact (table_nb14 X s c r x8 x12 ms HL XO HREGS HP MFB)|].
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & E27)|(r1 & EN & HR1 & HLV)].
  2:{ rewrite (arm_TABLE_leave flush _ _ EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
  destruct (nb_r1_facts c r r1 14 HREGS ltac:(rewrite Pin; exact Pin1) ltac:(lia) HR1) as (EI & EO & ER & EP & EL & RB1 & RH1 & RHV1 & RN1).
  rewrite (arm_TABLE_eq flush s c r s c r1 EN ltac:(lia) ltac:(lia)).
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HP| assumption..]).
  eapply evt_cut.
  { destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
    exact (table_fin flush X s c r1 q1 ms1 EF HJ E27 XO HP1 ltac:(lia) RH1 ltac:(rewrite EP; lia)). }
  intros ms2 H2. unfold tb_res. cbv zeta.
  assert (HN : table_next (mkW s c r) = if (286 <? is_nlen (tb_s s (ir_hold r1))) || (30 <? is_ndist (tb_s s (ir_hold r1))) then None
                                        else Some (mkW (tb_s2 s (ir_hold r1)) c (tb_r r1))).
  { unfold table_next. rewrite EN. reflexivity. }
  destruct ((286 <? is_nlen (tb_s s (ir_hold r1))) || (30 <? is_ndist (tb_s s (ir_hold r1)))).
  - destruct H2 as (x8' & H2). apply evt_done. split; [cbn [IPOST]; exists x8'; exact H2|]. cbn [wof].
    eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact Pisr.
  - destruct H2 as (q2 & H2 & E12 & E15 & E26).
    destruct (table_next_WINV _ _ HW HM HN) as [HW2 HM2].
    pose proof (table_next_ATY (mkW s c r) _ HA HN) as HA2.
    refine (LENLENS_CORE X _ q2 ms2 EF H2 E12 E15 E26 XO HW2 HA2 _ HM2).
    eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold tb_s2; cbn [is_mode iset_mode]; unfold LENLENS, FLAGS, HCRC; lia| reflexivity..|]. exact Pisr.
Qed.

Lemma arm_TABLE_of : arm_stmt flush TABLE PC_TABLE (arm_TABLE ivar_ref flush).
Proof. intros X w x12 ms EF HL XO HW HA HP HM. exact (table_core X w _ x12 ms EF HL XO HW HA HP HM). Qed.
End Table.
End Z_infl_a_table.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.

Module Z_infl_a_codelens1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_iface Z_infl_c_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_t_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_lenlens1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_len.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate Inftrees ItableModel InffastMem RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 RefInflateSafeOK3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LENLENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.

Definition PC_CL_B : Z := 0x1d6c0.
Definition PC_CL_J : Z := 0x1d734.
Definition PC_CL_T : Z := 0x1d8dc.
Definition PC_CL_X : Z := 0x1d8e8.

Definition CLK (X : ictx) (s : inflate_state) (q : iscr) : Prop :=
  sc12 q = wz (is_nlen s) /\ sc14 q = wz (is_nlen s + is_ndist s) /\ sc15 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ sc16 q = wz (Z.ones (is_lenbits s)).

Lemma cl_entry : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_CODELENS_E q ms -> sc13 q = wz (is_have s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  0 <= is_have s <= 320 -> 257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 -> 0 <= is_lenbits s <= 15 -> cp_ofs_ok (is_lencode s) ->
  evt psegs (fun ms' => exists q',
     if is_have s <? is_nlen s + is_ndist s
     then ILOOPg X (mkW s c r) PC_CL_B q' ms' /\ CLK X s q' /\ sc13 q' = wz (is_have s) /\ sc6 q' = wz (ir_have r)
          /\ sc7 q' = wz (il_NI (ix_L X) + ir_next r) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r)
     else ILOOPg X (mkW s c r) PC_CL_X q' ms' /\ sc12 q' = wz (is_nlen s) /\ sc13 q' = wz (is_have s) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E13 E26 Rh Rnl Rnd Rlb CPO.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x13 x26.
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s w_c w_r] in *.
  unfold PC_CODELENS_E.
  do 4 zs. br_cases K.
  - replace (is_have s <? is_nlen s + is_ndist s) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|]. cbn [sc12 sc13 sc26]. repeat split; ireg.
  - replace (is_have s <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; lia).
    rd_sub GA 136%nat 0%nat 4%nat. do 7 zs. rewrite clang_mask32 by lia.
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|].
    unfold CLK. cbn [sc6 sc7 sc12 sc13 sc14 sc15 sc16 sc26]. repeat split; ireg.
Qed.

Definition cl_QJ (X : ictx) (s : inflate_state) (r r1 : iregs) (q : iscrh) : Prop :=
  h28 q = wz (dec_idx1 (is_lenbits s) (ir_hold r1)) /\ h5 q = wz (code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))))
  /\ h17 q = wz (ir_bits r1) /\ h9 q = wz (ir_have r1) /\ h22 q = wz (ir_hold r1) /\ h26 q = wz (il_NI (ix_L X) + ir_next r1)
  /\ h23 q = wz (ir_bits r) /\ h29 q = wz 30 /\ h31 q = wz (-16180)
  /\ h12 q = wz (is_nlen s) /\ h13 q = wz (is_have s) /\ h14 q = wz (is_nlen s + is_ndist s)
  /\ h15 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ h16 q = wz (Z.ones (is_lenbits s)).

Lemma cl_dec : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_CL_B q ms -> CLK X s q -> sc13 q = wz (is_have s) -> sc6 q = wz (ir_have r) ->
  sc7 q = wz (il_NI (ix_L X) + ir_next r) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> DREGS c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) -> PATI X (mkW s c r) ->
  0 <= is_lenbits s <= 15 -> cp_ofs_ok (is_lencode s) ->
  dlvl c s (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits r ->
  evt psegs (DECJ X s c r r (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits PC_CL_J (cl_QJ X s r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL (E12 & E14 & E15 & E16) E13 E6 E7 E26 XO DR Rin HP RN CPO DL.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *.
  subst x12 x13 x14 x15 x16 x6 x7 x26.
  pose proof HMEM as ((jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  destruct DR as (Rn & Rh & Rnh & RB & RH).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST.
  unfold PC_CL_B. ix_open XO.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *.
  pose proof (dec_idx1_land n (ir_hold r) ltac:(lia) RN) as EI0. pose proof (dec_idx1_range n (ir_hold r) ltac:(lia) RN) as RI0'.
  pose proof (dl_i0 _ _ _ _ _ _ DL) as RI0. pose proof (dl_n0 _ _ _ _ _ _ DL) as RN0. pose proof (ones_range15 n RN) as RMK.
  zs. rewrite EI0.
  set (i0 := dec_idx1 n (ir_hold r)) in *. set (e0 := code_at s p i0) in *.
  pose proof (code_bits_range e0) as RB0.
  do 2 zs.
  pose proof (code_rd_bits m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2 + 1)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. cbv beta. rewrite (bv8_small (code_bits e0)) by exact RB0. clear RD.
  zs. br_cases K.
  -
    destruct (dl_found0 _ _ _ _ _ _ DL ltac:(fold i0; fold e0; lia)) as [ED EC].
    do 3 zs. apply evt_done. left. eexists r, _. split; [exact ED|]. split; [exact EC|]. split; [fold i0; fold e0; lia|]. split; [exact RI0|].
    split; [left; reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold cl_QJ. cbn [h5 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h28 h29 h31]. fold p. fold n. fold i0. fold e0. repeat split; reflexivity.
  - assert (K' : ir_bits r < code_bits (code_at s p (dec_idx1 n (ir_hold r)))) by (fold i0; fold e0; exact K).
    do 5 zs. br_cases K2.
    +
      assert (H1 : ir_have r = 1) by lia.
      destruct (dl_i1 _ _ _ _ _ _ DL K' H1) as [RI1 RN1].
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      assert (EH1 : arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r + ir_hold r = ir_hold (pullr c r)).
      { unfold hide in RH. rewrite pullr_hold by (first [assumption | lia]). lia. }
      pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r)) (ir_bits r) (ir_hold r) RBy ltac:(lia) RH) as PR.
      assert (RH1 : 0 <= ir_hold (pullr c r) < 2^64).
      { rewrite <- EH1. split; [lia|]. eapply Z.lt_le_trans; [rewrite Z.add_comm; exact (proj2 PR)|]. apply Z.pow_le_mono_r; lia. }
      rewrite EH1. clear PR EH1.
      pose proof (dec_idx1_land n (ir_hold (pullr c r)) ltac:(lia) RN) as EI1. pose proof (dec_idx1_range n (ir_hold (pullr c r)) ltac:(lia) RN) as RI1'.
      set (h1 := ir_hold (pullr c r)) in *.
      zs. rewrite EI1. set (i1 := dec_idx1 n h1) in *. set (e1 := code_at s p i1) in *. pose proof (code_bits_range e1) as RB1.
      do 2 zs.
      pose proof (code_rd_bits m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2 + 1)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e1 in RD. zs. cbv beta. rewrite (bv8_small (code_bits e1)) by exact RB1. clear RD.
      do 6 zs. br_cases K3.
      *
        assert (K3' : ir_bits (pullr c r) < code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r))))) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; exact K3).
        pose proof (dl_dry1 _ _ _ _ _ _ DL K' H1 K3') as ED.
        zs. br_false. do 8 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1. change (1 ≪ 32) with 4294967296.
        apply evt_done. right. exists (pullr c r). split; [exact ED|]. split; [right; split; [reflexivity| split; [exact H1| lia]]|].
        unfold hide in RH. subst e1 i1 h1. eapply ILEAVE_intro; ired; [ .. | eapply IMEML_of_IMEM; [exact HMEM| reflexivity..]]; pullr_rw c r; ireg.
      * assert (K3' : code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r)))) <= ir_bits (pullr c r)) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; lia).
        destruct (dl_found1 _ _ _ _ _ _ DL K' H1 K3') as [ED EC].
        do 2 zs. apply evt_done. left. eexists (pullr c r), _. split; [exact ED|]. split; [exact EC|]. split; [exact K3'|]. split; [exact RI1|].
        split; [right; split; [reflexivity| split; [exact H1| lia]]|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
        unfold hide in RH. unfold cl_QJ. cbn [h5 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h28 h29 h31]. fold p. fold n. fold h1. fold i1. fold e1.
        repeat split; try reflexivity; pullr_rw c r; ireg.
    +
      assert (H0 : ir_have r = 0) by lia.
      pose proof (dl_dry0 _ _ _ _ _ _ DL K' H0) as ED.
      do 8 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite !Z.add_0_r.
      apply evt_done. right. exists r. split; [exact ED|]. split; [left; reflexivity|].
      eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Local Ltac close_lit jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV EP :=
  apply IMEM_intro; inorm;
  [ exists jf; unfold iframe_cells; inorm; close_cells FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| unfold ilens, u16arr; inorm; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; rewrite ?EP; exact OUT | eassumption | exact MU | exact WM ].

Lemma cl_litw : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_CL_J q ms -> cl_QJ X s r r1 q -> ix_ok X -> PATI X (mkW s c r) ->
  ir_in r1 = ir_in r -> ir_out r1 = ir_out r -> ir_ret r1 = ir_ret r -> ir_put r1 = ir_put r -> ir_left r1 = ir_left r ->
  code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2^64 ->
  0 <= dec_idx1 (is_lenbits s) (ir_hold r1) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) -> 0 <= is_lenbits s <= 15 ->
  code_val (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) < 16 ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s < 320 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists q',
     ILOOPg X (mkW (cl_lit s (code_val (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))))) c
                 (ddrop r1 (code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)))))) PC_CL_T q' ms'
     /\ CLK X s q' /\ sc13 q' = wz (is_have s + 1) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r1)) ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO HP EI EO ER EP EL RB RH RI CPO RN RV LL Rh RPUT.
  destruct HQ as (E28 & E5 & E17 & E9 & E22 & E26 & E23 & E29 & E31 & E12 & E13 & E14 & E15 & E16).
  iarm_openh HL. subst.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *. set (i1 := dec_idx1 n (ir_hold r1)) in *. set (e1 := code_at s p i1) in *.
  pose proof (code_bits_range e1) as RB1. pose proof (code_val_range e1) as RV1. pose proof (dec_idx1_range n (ir_hold r1) ltac:(lia) RN) as RI1'. fold i1 in RI1'.
  do 2 zs.
  pose proof (code_rd_val m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2 + 2)) MI Gc CPO RI ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e1 in RD. zs. rewrite (zx16_small (code_val e1)) by lia. clear RD.
  do 2 zs. br_false.
  zs. rewrite land63_small by lia. do 4 zs. itr_groups MUf WMf. clear MUf WMf.
  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  lazymatch goal with MI' : mem_inv psegs ?m1 |- _ =>
    pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m1) as MUf;
    pose proof (wmono_refl psegs m1) as WMf end.
  do 2 zs. rewrite zext32_x2 by lia.
  assert (EV : wrap16 (code_val e1) = code_val e1) by (apply wrap16_id; lia).
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) (is_have s) (wrap16 (code_val e1)) ltac:(rewrite EV; reflexivity).
  zs. itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPg_intro; unfold cl_lit, ddrop; ired; [ireg .. |]|].
  - close_lit jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV EP.
  - unfold CLK, cl_lit. cbn [sc12 sc13 sc14 sc15 sc16 sc26]. ired. fold p n. repeat split; ireg.
Qed.

Definition cl_pce (val : Z) : Z := if val =? 16 then 0x1d7b8 else if val =? 17 then 0x1d77c else 0x1d7f4.
Definition cl_pcx (val : Z) : Z := if val =? 16 then 0x1d858 else if val =? 17 then 0x1d834 else 0x1d894.

Definition cl_QN (X : ictx) (s : inflate_state) (r r1 r2 : iregs) (q : iscrh) : Prop :=
  h5 q = wz (code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))))
  /\ h17 q = wz (ir_bits r2) /\ h9 q = wz (ir_have r2) /\ h22 q = wz (ir_hold r2)
  /\ h26 q = wz (il_NI (ix_L X) + ir_next r2) /\ h27 q = wz (il_NI (ix_L X) + ir_next r2)
  /\ h23 q = wz (ir_bits r) /\ h29 q = wz 30 /\ h31 q = wz (-16180)
  /\ h12 q = wz (is_nlen s) /\ h13 q = wz (is_have s) /\ h14 q = wz (is_nlen s + is_ndist s)
  /\ h15 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ h16 q = wz (Z.ones (is_lenbits s)).

Definition NBJc (X : ictx) (s : inflate_state) (c : icall) (r r1 : iregs) (n pcx : Z) : machine_state -> Prop :=
  fun ms' =>
    (exists r2 q', NEEDBITS n (mkW s c r1) = ARun tt (mkW s c r2)
                   /\ ((r2 = r1 /\ n <= ir_bits r1) \/ (r2 = pullr c r1 /\ 0 < ir_have r1 /\ ir_bits r1 < n <= ir_bits r1 + 8))
                   /\ ILOOPh X (mkW s c r) pcx q' ms' /\ cl_QN X s r r1 r2 q')
    \/ (exists r2, NEEDBITS n (mkW s c r1) = ALeave (mkW s c r2) /\ (r2 = r1 \/ r2 = pullr c r1) /\ ILEAVE X (mkW s c r2) ms').

Local Ltac nb_site_tac X c r1 Pin IN HMEM RH EI EO EP :=
  let K := fresh "K" in let K2 := fresh "K" in let K3 := fresh "K" in
  do 2 zs; br_cases K;
  [
    zs; apply evt_done; left; eexists r1, _; split; [apply nb_enough; lia|]; split; [left; split; [reflexivity| lia]|];
    split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|];
    unfold cl_QN; cbn [h5 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h29 h31]; repeat split; reflexivity
  | do 2 zs; br_cases K2;
    [
      let H1 := fresh "H1" in let NXT := fresh "NXT" in let RD := fresh "RD" in
      assert (H1 : ir_have r1 = 1) by lia;
      assert (NXT : 0 <= ir_next r1 < arr_len (ix_input X)) by (rewrite <- Pin; lia);
      pose proof (u8ro_read psegs _ _ _ (ir_next r1) _ (wa (il_NI (ix_L X) + ir_next r1)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD;
      zs; clear RD; do 8 zs; rewrite <- Pin; rewrite !pull_shift by lia; br_cases K3;
      [
        zs; br_false; do 4 zs; rewrite H1; change (Z.land 1 4294967295) with 1;
        apply evt_done; right; exists (pullr c r1); split; [apply nb_pull_dry; lia|]; split; [right; reflexivity|];
        unfold hide in RH; eapply ILEAVE_intro; pullr_rw c r1; ired; [ireg .. |]; eapply IMEML_of_IMEM; [exact HMEM| rewrite ?pullr_in, ?pullr_out, ?pullr_put; assumption ..]
      | zs; apply evt_done; left; eexists (pullr c r1), _; split; [apply nb_pull_ok; lia|]; split; [right; split; [reflexivity| lia]|];
        split; [unfold hide in RH; eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|];
        unfold hide in RH; unfold cl_QN; cbn [h5 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h29 h31]; pullr_rw c r1;
        rewrite H1; change (Z.land 1 4294967295) with 1; repeat split; ireg ]
    |
      let H0 := fresh "H0" in assert (H0 : ir_have r1 = 0) by lia;
      do 4 zs; apply evt_done; right; exists r1; split; [apply nb_dry; lia|]; split; [left; reflexivity|];
      eapply ILEAVE_intro; ired; [ireg .. |]; eapply IMEML_of_IMEM; [exact HMEM| assumption ..] ] ].

Lemma cl_need : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_CL_J q ms -> cl_QJ X s r r1 q -> ix_ok X -> DREGS c r1 -> (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  PATI X (mkW s c r) ->
  ir_in r1 = ir_in r -> ir_out r1 = ir_out r -> ir_ret r1 = ir_ret r -> ir_put r1 = ir_put r -> ir_left r1 = ir_left r ->
  code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) <= ir_bits r1 ->
  code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) <= 32 ->
  0 <= dec_idx1 (is_lenbits s) (ir_hold r1) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) -> 0 <= is_lenbits s <= 15 ->
  16 <= code_val (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) ->
  let here := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  evt psegs (NBJc X s c r r1 (code_bits here + cl_nb (code_val here)) (cl_pcx (code_val here))) ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO DR Rin HP EI EO ER EP EL RB RB32 RI CPO RN RV.
  destruct HQ as (E28 & E5 & E17 & E9 & E22 & E26 & E23 & E29 & E31 & E12 & E13 & E14 & E15 & E16).
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst.
  pose proof HMEM as ((jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  destruct DR as (Rn & Rh & Rnh & RB1 & RH).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r1)) as RBy.
  assert (RH64 : 0 <= ir_hold r1 < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST. ix_open XO. unfold PC_CL_J.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *. set (i1 := dec_idx1 n (ir_hold r1)) in *. set (e1 := code_at s p i1) in *.
  pose proof (code_bits_range e1) as RBe. pose proof (code_val_range e1) as RVe. pose proof (dec_idx1_range n (ir_hold r1) ltac:(lia) RN) as RI1'. fold i1 in RI1'.
  cbv zeta.
  do 2 zs.
  pose proof (code_rd_val m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2 + 2)) MI Gc CPO RI ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e1 in RD. zs. rewrite (zx16_small (code_val e1)) by lia. clear RD.
  do 2 zs. br_true.
  do 2 zs. br_cases K16.
  { unfold cl_nb, cl_pcx. replace (code_val e1 =? 16) with true by (symmetry; apply Z.eqb_eq; lia).
    nb_site_tac X c r1 Pin IN HMEM RH EI EO EP. }
  do 2 zs. br_cases K17.
  { unfold cl_nb, cl_pcx. replace (code_val e1 =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (code_val e1 =? 17) with false by (symmetry; apply Z.eqb_neq; lia).
    nb_site_tac X c r1 Pin IN HMEM RH EI EO EP. }
  unfold cl_nb, cl_pcx. replace (code_val e1 =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (code_val e1 =? 17) with true by (symmetry; apply Z.eqb_eq; lia).
  nb_site_tac X c r1 Pin IN HMEM RH EI EO EP.
Qed.

Definition PC_CL_R : Z := 0x1d8bc.
Definition PC_CL_RX : Z := 0x1d8d4.

Local Ltac close_keep jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP :=
  apply IMEM_intro; inorm;
  [ exists jf; unfold iframe_cells; inorm; close_cells FRM | exact STK | first [exact ZS | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS]
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; rewrite ?EP; exact OUT | eassumption | exact MU | exact WM ].

Lemma cl_rep_hd : forall X s c r r1 r2 q ms,
  let here := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  let val := code_val here in let nb := cl_nb val in
  let r3 := ddrop r2 (code_bits here) in
  let len := (if val =? 16 then arr_get (is_lens s) (is_have s - 1) else 0) in
  let copy := cl_base val + BITSv (ir_hold r3) nb in
  let r4 := ddrop r3 nb in
  ILOOPh X (mkW s c r) (cl_pcx val) q ms -> cl_QN X s r r1 r2 q -> ix_ok X -> PATI X (mkW s c r) ->
  ir_in r2 = ir_in r -> ir_out r2 = ir_out r -> ir_ret r2 = ir_ret r -> ir_put r2 = ir_put r -> ir_left r2 = ir_left r ->
  code_bits here + nb <= ir_bits r2 <= 63 -> 0 <= ir_hold r2 < 2^64 -> 0 <= ir_have r2 -> 16 <= val ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s <= is_nlen s + is_ndist s -> is_nlen s + is_ndist s <= 320 ->
  (forall i, 0 <= i < is_have s -> 0 <= arr_get (is_lens s) i <= 15) ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
    if (val =? 16) && (is_have s =? 0) then exists x8, ILOOP X (cl_bad s c r3) PC_DISPATCH x8 (wz BAD) ms'
    else if is_nlen s + is_ndist s <? is_have s + copy then exists x8, ILOOP X (cl_bad s c r4) PC_DISPATCH x8 (wz BAD) ms'
    else exists q', ILOOPg X (mkW s c r4) PC_CL_R q' ms' /\ CLK X s q' /\ sc13 q' = wz (is_have s) /\ sc17 q' = wz (is_have s + copy)
                    /\ sc6 q' = wz len /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r2) /\ sc27 q' = wz (il_NI (ix_L X) + ir_next r2)) ms.
Proof.
  intros X s c r r1 r2 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms.
  intros here val nb r3 len copy r4 HL HQ XO HP EI EO ER EP EL RB RH RHV RV LL Rh Rnd HLs RPUT.
  destruct HQ as (E5 & E17 & E9 & E22 & E26 & E27 & E23 & E29 & E31 & E12 & E13 & E14 & E15 & E16).
  iarm_openh HL. subst x5 x17 x9 x22 x26 x27 x23 x29 x31 x12 x13 x14 x15 x16.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  fold here. set (cb := code_bits here) in *. pose proof (code_bits_range here) as RCB. fold cb in RCB.
  assert (Rnb : 2 <= nb <= 7) by (subst nb; unfold cl_nb; destruct (val =? 16); [lia|]; destruct (val =? 17); lia).
  pose proof (shiftr_le (ir_hold r2) cb ltac:(lia) ltac:(lia)) as RH3.
  assert (EH3 : ir_hold r3 = ir_hold r2 ≫ cb) by reflexivity.
  pose proof (BITSv_land (ir_hold r3) nb ltac:(rewrite EH3; lia) ltac:(lia)) as EBV. pose proof (land_ones_rng (ir_hold r3) nb ltac:(lia)) as RBV. rewrite <- EBV in RBV.
  assert (Rcp : 3 <= copy <= 138).
  { subst copy. assert (P7 : 2 ^ nb <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia). change (2 ^ 7) with 128 in P7.
    unfold cl_base. destruct (val =? 16); [lia|]. destruct (val =? 17); lia. }
  unfold cl_pcx.
  destruct (Z.eqb_spec val 16) as [V16|NV16].
  -
    assert (Enb : nb = 2) by (subst nb; unfold cl_nb; rewrite V16; reflexivity).
    assert (Ecp : copy = 3 + Z.land (ir_hold r3) 3) by (subst copy; rewrite EBV, Enb; unfold cl_base; rewrite V16; reflexivity).
    do 2 zs. rewrite land63_small by lia. zs. br_cases K0.
    + replace (is_have s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
      pose proof (HLs (is_have s - 1) ltac:(lia)) as RLEN.
      do 4 zs. rewrite zext32_x2 by lia.
      pose proof Gl as Gl'. unfold ilens, u16arr in Gl'. ld16 Gl' (is_lens s) 320 (il_As (ix_L X) + 168) (is_have s - 1) ltac:(lia). clear Gl'.
      pose proof (land_ones_rng (ir_hold r2 ≫ cb) 2 ltac:(lia)) as R3. change (Z.ones 2) with 3 in R3. change (2 ^ 2) with 4 in R3.
      rewrite EH3 in Ecp.
      do 5 zs. do 2 zs. br_cases K1.
      *
        replace (is_nlen s + is_ndist s <? is_have s + copy) with false by (symmetry; apply Z.ltb_ge; lia).
        apply evt_done. eexists. split; [eapply ILOOPg_intro; subst r4 r3; unfold ddrop; ired; rewrite ?Enb; [ireg .. |]|].
        { apply IMEM_intro; inorm; [ exists jf; unfold iframe_cells; inorm; close_cells FRM | exact STK | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
          | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin | unfold iarrs in *; inorm; exact ARRS| exact LAY]
          | exact IN | unfold iout; rewrite ?EP; exact OUT | eassumption | exact MU | exact WM ]. }
        unfold CLK. cbn [sc6 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27]. repeat split; ireg.
      *
        replace (is_nlen s + is_ndist s <? is_have s + copy) with true by (symmetry; apply Z.ltb_lt; lia).
        do 4 zs. do 3 zs. do 2 zs. itr_groups MUf WMf.
        apply evt_done. eexists. unfold cl_bad. subst r4 r3. unfold ddrop. eapply ILOOP_intro; ired; rewrite ?Enb; [ireg .. |].
        apply IMEM_intro; inorm; [ exists jf; unfold iframe_cells; inorm; close_cells FRM | exact STK | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
          | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin | unfold iarrs in *; inorm; exact ARRS| exact LAY]
          | exact IN | unfold iout; rewrite ?EP; exact OUT | eassumption | exact MU | exact WM ].
    +
      replace (is_have s =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb].
      do 4 zs. do 3 zs. do 2 zs. itr_groups MUf WMf.
      apply evt_done. eexists. unfold cl_bad. subst r3. unfold ddrop. eapply ILOOP_intro; ired; [ireg .. |].
      close_keep jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
  -
    cbn [andb].
    destruct (Z.eqb_spec val 17) as [V17|NV17].
    + assert (Enb : nb = 3) by (subst nb; unfold cl_nb; rewrite V17; reflexivity).
      assert (Ecp : copy = 3 + Z.land (ir_hold r3) 7) by (subst copy; rewrite EBV, Enb; unfold cl_base; rewrite V17; reflexivity).
      pose proof (land_ones_rng (ir_hold r2 ≫ cb) 3 ltac:(lia)) as R3. change (Z.ones 3) with 7 in R3. change (2 ^ 3) with 8 in R3.
      rewrite EH3 in Ecp.
      do 2 zs. rewrite land63_small by lia. do 6 zs.
      do 2 zs. br_cases K1.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with false by (symmetry; apply Z.ltb_ge; lia).
        apply evt_done. eexists. split; [eapply ILOOPg_intro; subst r4 r3; unfold ddrop; ired; rewrite ?Enb; [ireg .. |]|].
        { close_keep jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP. }
        unfold CLK. cbn [sc6 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27]. repeat split; ireg.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with true by (symmetry; apply Z.ltb_lt; lia).
        do 4 zs. do 3 zs. do 2 zs. itr_groups MUf WMf.
        apply evt_done. eexists. unfold cl_bad. subst r4 r3. unfold ddrop. eapply ILOOP_intro; ired; rewrite ?Enb; [ireg .. |].
        close_keep jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
    + assert (Enb : nb = 7).
      { subst nb; unfold cl_nb. replace (val =? 16) with false by (symmetry; apply Z.eqb_neq; exact NV16).
        replace (val =? 17) with false by (symmetry; apply Z.eqb_neq; exact NV17). reflexivity. }
      assert (Ecp : copy = 11 + Z.land (ir_hold r3) 127).
      { subst copy; rewrite EBV, Enb; unfold cl_base. replace (val =? 16) with false by (symmetry; apply Z.eqb_neq; exact NV16).
        replace (val =? 17) with false by (symmetry; apply Z.eqb_neq; exact NV17). reflexivity. }
      pose proof (land_ones_rng (ir_hold r2 ≫ cb) 7 ltac:(lia)) as R3. change (Z.ones 7) with 127 in R3. change (2 ^ 7) with 128 in R3.
      rewrite EH3 in Ecp.
      do 2 zs. rewrite land63_small by lia. do 5 zs.
      do 2 zs. br_cases K1.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with false by (symmetry; apply Z.ltb_ge; lia).
        apply evt_done. eexists. split; [eapply ILOOPg_intro; subst r4 r3; unfold ddrop; ired; rewrite ?Enb; [ireg .. |]|].
        { close_keep jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP. }
        unfold CLK. cbn [sc6 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27]. repeat split; ireg.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with true by (symmetry; apply Z.ltb_lt; lia).
        do 4 zs. do 3 zs. do 2 zs. itr_groups MUf WMf.
        apply evt_done. eexists. unfold cl_bad. subst r4 r3. unfold ddrop. eapply ILOOP_intro; ired; rewrite ?Enb; [ireg .. |].
        close_keep jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
Qed.
End Z_infl_a_codelens1.

Module Z_infl_a_codelens2.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_iface Z_infl_c_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_t_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_lenlens1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_len OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_codelens1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate Inftrees ItableModel InffastMem RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 RefInflateSafeOK3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LENLENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.



Local Ltac close_l jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [exact GA| exact GT| unfold ilens, u16arr; inorm; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma cl_rep_body : forall X s c r i t v q ms,
  ILOOPg X (mkW s c r) PC_CL_R q ms -> sc13 q = wz i -> sc17 q = wz t -> sc6 q = wz v ->
  ix_ok X -> PATI X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i < t -> t <= 320 -> 0 <= v < 16 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists q',
     (if i + 1 =? t then ILOOPg X (mkW (iset_lens s (arr_set (is_lens s) i v)) c r) PC_CL_RX q' ms'
      else ILOOPg X (mkW (iset_lens s (arr_set (is_lens s) i v)) c r) PC_CL_R q' ms')
     /\ sc13 q' = wz (i + 1) /\ sc17 q' = sc17 q /\ sc6 q' = sc6 q /\ sc12 q' = sc12 q /\ sc14 q' = sc14 q /\ sc15 q' = sc15 q
     /\ sc16 q' = sc16 q /\ sc26 q' = sc26 q /\ sc27 q' = sc27 q) ms.
Proof.
  intros X s c r i t v [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E13 E17 E6 XO HP LL Ri Rt Rv RPUT.
  iarm_openg HL. subst x13 x17 x6.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_R.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST.
  pose proof (munch_refl [(il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m) as MUf. pose proof (wmono_refl psegs m) as WMf.
  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  do 4 zs. rewrite zext32_x2 by lia.
  assert (EV : wrap16 v = v) by (apply wrap16_id; lia).
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) i v ltac:(reflexivity).
  zs. itr_groups MUf WMf. br_cases K.
  - replace (i + 1 =? t) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. |]|].
    + close_l jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + cbn [sc6 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27]. repeat split; ireg.
  - replace (i + 1 =? t) with true by (symmetry; apply Z.eqb_eq; lia).
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. |]|].
    + close_l jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + cbn [sc6 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27]. repeat split; ireg.
Qed.

Lemma fill_S' : forall n a i v, fill (S n) a i v = fill n (arr_set a i v) (i + 1) v.
Proof. intros. reflexivity. Qed.

Lemma cl_rep_loop : forall n X s c r i t v q ms,
  ILOOPg X (mkW s c r) PC_CL_R q ms -> sc13 q = wz i -> sc17 q = wz t -> sc6 q = wz v ->
  ix_ok X -> PATI X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i -> t = i + Z.of_nat n -> (0 < n)%nat -> t <= 320 -> 0 <= v < 16 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists q', ILOOPg X (mkW (iset_lens s (fill n (is_lens s) i v)) c r) PC_CL_RX q' ms'
     /\ sc13 q' = wz t /\ sc12 q' = sc12 q /\ sc14 q' = sc14 q /\ sc15 q' = sc15 q /\ sc16 q' = sc16 q /\ sc26 q' = sc26 q /\ sc27 q' = sc27 q) ms.
Proof.
  induction n as [|n IH]; intros X s c r i t v q ms HL E13 E17 E6 XO HP LL Ri Et Hn Rt Rv RPUT; [lia|].
  rewrite fill_S'.
  eapply evt_cut; [exact (cl_rep_body X s c r i t v q ms HL E13 E17 E6 XO HP LL ltac:(lia) Rt Rv RPUT)|].
  intros ms1 (q1 & H1 & E13' & E17' & E6' & E12' & E14' & E15' & E16' & E26' & E27').
  destruct (Z.eqb_spec (i + 1) t) as [E|NE].
  - assert (n = 0)%nat as -> by lia. cbn [fill]. apply evt_done. exists q1. rewrite <- E. repeat split; assumption.
  - refine (_ (IH X (iset_lens s (arr_set (is_lens s) i v)) c r (i + 1) t v q1 ms1 H1 E13' ltac:(congruence) ltac:(congruence) XO _ _ _ _ _ Rt Rv RPUT)).
    + intros H. eapply evt_mono; [exact H|]. cbv beta. intros ms2 (q2 & H2 & F2). exists q2. split; [exact H2|].
      rewrite E12', E14', E15', E16', E26', E27' in F2. exact F2.
    + exact HP.
    + cbn [is_lens iset_lens]. rewrite arr_len_set. exact LL.
    + lia.
    + lia.
    + lia.
Qed.

Local Ltac close_gA jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma cl_rep_tl : forall X s c r t q ms,
  ILOOPg X (mkW s c r) PC_CL_RX q ms -> sc13 q = wz t -> sc27 q = wz (il_NI (ix_L X) + ir_next r) -> ix_ok X -> PATI X (mkW s c r) ->
  0 <= t <= 320 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists q', ILOOPg X (mkW (iset_have s t) c r) PC_CL_T q' ms' /\ sc13 q' = wz t /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r)
     /\ sc12 q' = sc12 q /\ sc14 q' = sc14 q /\ sc15 q' = sc15 q /\ sc16 q' = sc16 q) ms.
Proof.
  intros X s c r t [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E13 E27 XO HP Rt RPUT.
  iarm_openg HL. subst x13 x27.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_RX.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  do 2 zs. itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. |]| cbn [sc12 sc13 sc14 sc15 sc16 sc26]; repeat split; reflexivity].
  close_gA jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma cl_test : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_CL_T q ms -> CLK X s q -> sc13 q = wz (is_have s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  0 <= is_have s <= 320 -> 257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 ->
  evt psegs (fun ms' => exists q',
     if is_have s <? is_nlen s + is_ndist s
     then ILOOPg X (mkW s c r) PC_CL_B q' ms' /\ CLK X s q' /\ sc13 q' = wz (is_have s) /\ sc6 q' = wz (ir_have r)
          /\ sc7 q' = wz (il_NI (ix_L X) + ir_next r) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r)
     else ILOOPg X (mkW s c r) PC_CL_X q' ms' /\ sc12 q' = wz (is_nlen s) /\ sc13 q' = wz (is_have s) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL (E12 & E14 & E15 & E16) E13 E26 Rh Rnl Rnd.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst.
  unfold PC_CL_T.
  do 3 zs. br_cases K.
  - replace (is_have s <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; lia).
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|].
    unfold CLK. cbn [sc6 sc7 sc12 sc13 sc14 sc15 sc16 sc26]. repeat split; reflexivity.
  - replace (is_have s <? is_nlen s + is_ndist s) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|]. cbn [sc12 sc13 sc26]. repeat split; reflexivity.
Qed.

Lemma cl_rep_run : forall X s c r copy len q ms,
  ILOOPg X (mkW s c r) PC_CL_R q ms -> CLK X s q -> sc13 q = wz (is_have s) -> sc17 q = wz (is_have s + copy) -> sc6 q = wz len ->
  sc27 q = wz (il_NI (ix_L X) + ir_next r) -> ix_ok X -> PATI X (mkW s c r) ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s -> 3 <= copy -> is_have s + copy <= 320 -> 0 <= len < 16 ->
  is_mode s = CODELENS -> is_flags s = 0 -> ISR s -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
    (exists q', ILOOPg X (mkW (cl_rep s copy len) c r) PC_CL_T q' ms' /\ CLK X (cl_rep s copy len) q'
                /\ sc13 q' = wz (is_have (cl_rep s copy len)) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r))
    /\ PATI X (mkW (cl_rep s copy len) c r)) ms.
Proof.
  intros X s c r copy len q ms HL HK E13 E17 E6 E27 XO HP LL Rh Rc Rhc Rlen HM Pf0 Pisr RPUT.
  rewrite (cl_rep_fill s copy len) by lia. rewrite (wrap16_id len) by lia.
  eapply evt_cut.
  { exact (cl_rep_loop (Z.to_nat copy) X s c r (is_have s) (is_have s + copy) len q ms HL E13 E17 E6 XO HP LL Rh ltac:(lia) ltac:(lia) Rhc Rlen RPUT). }
  intros ms1 (q1 & H1 & E13' & E12' & E14' & E15' & E16' & E26' & E27').
  eapply evt_cut.
  { exact (cl_rep_tl X _ c r (is_have s + copy) q1 ms1 H1 E13' ltac:(rewrite E27'; exact E27) XO HP ltac:(lia) RPUT). }
  intros ms2 (q2 & H2 & E13'' & E26'' & E12'' & E14'' & E15'' & E16''). apply evt_done. split.
  - exists q2. split; [exact H2|]. destruct HK as (K12 & K14 & K15 & K16).
    unfold CLK. cbn [is_nlen is_ndist is_lencode is_lenbits is_have iset_have iset_lens]. repeat split; try congruence.
  - eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0
      | cbn [is_mode iset_have iset_lens]; rewrite HM; unfold CODELENS, FLAGS, HCRC; lia| try reflexivity ..]; [|exact Pisr].
    cbn [is_mode iset_have iset_lens]. rewrite HM. reflexivity.
Qed.

Lemma cl_r2_facts : forall c r r1 n, DREGS c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) -> n <= 48 ->
  ((r1 = r /\ n <= ir_bits r) \/ (r1 = pullr c r /\ 0 < ir_have r /\ ir_bits r < n <= ir_bits r + 8)) ->
  DREGS c r1 /\ n <= ir_bits r1 /\ ir_in r1 = ir_in r /\ ir_out r1 = ir_out r /\ ir_ret r1 = ir_ret r /\ ir_put r1 = ir_put r /\ ir_left r1 = ir_left r.
Proof.
  intros c r r1 n DR Rin Hn [[-> H]|(-> & H1 & H2)]; [split; [exact DR| repeat split; try reflexivity; lia]|].
  pose proof DR as (Rn & Rh & Rnh & RB & RH). assert (A1 : ir_have r = 1) by lia.
  pose proof (Rin (ir_next r)) as RBy.
  pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r)) (ir_bits r) (ir_hold r) RBy ltac:(lia) RH) as PR.
  unfold DREGS. pullr_rw c r. repeat split; try reflexivity; lia.
Qed.

Definition CLBPOST (X : ictx) (res : ares bool) : machine_state -> Prop :=
  match res with
  | ARun true w1 => fun ms' => (exists q, ILOOPg X w1 PC_CL_T q ms' /\ CLK X (w_s w1) q /\ sc13 q = wz (is_have (w_s w1))
                                           /\ sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w1))) /\ PATI X w1
  | ARun false w1 => fun ms' => (exists x8, ILOOP X w1 PC_DISPATCH x8 (wz BAD) ms') /\ PATI X w1
  | ALeave w' => fun ms' => ILEAVE X w' ms' /\ PATI X w'
  | ARet _ _ => fun _ => False
  end.

Lemma cl_body : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_CL_B q ms -> CLK X s q -> sc13 q = wz (is_have s) -> sc6 q = wz (ir_have r) ->
  sc7 q = wz (il_NI (ix_L X) + ir_next r) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> CL s c r -> PATI X (mkW s c r) -> is_have s < is_nlen s + is_ndist s ->
  decode_okb cl_two s c r (is_lencode s) (is_lenbits s) = true ->
  evt psegs (CLBPOST X (codelens_body (mkW s c r))) ms.
Proof.
  intros X s c r q ms HL HK E13 E6 E7 E26 XO HCL HP LT OKD.
  pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E'|E'] & _)]; [exact Pf| |]; rewrite E in E'; discriminate E').
  clear Pfl.
  pose proof HR as (Rn & Rh & Rnh & Rp & Rl & Rpl & _ & Rin & _).
  assert (HIN1 : arr_len (ic_input c) <= 1) by (rewrite Pin; exact Pin1).
  pose proof (DREGS_of_REGS c r HR HIN1) as DR.
  assert (LL : arr_len (is_lens s) = 320) by (destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  pose proof (cpok_ofs_ok _ _ _ _ HT) as CPO.
  assert (RPUT : 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X))) by (rewrite <- Pout; lia).
  destruct (decode_okb_lvl1 _ _ _ _ _ _ OKD) as [RN D1].
  pose proof (dlvl_of_dchk c s _ _ _ r D1 ltac:(destruct DR as (_&H&_); exact H) ltac:(destruct DR as (_&_&_&H&_); lia)) as DL.
  rewrite codelens_body_eq. change (DECODE1 (is_lencode s) (is_lenbits s)) with (DECODE_k 8 (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits).
  eapply evt_cut; [exact (cl_dec X s c r q ms HL HK E13 E6 E7 E26 XO DR Rin HP RN CPO DL)|].
  intros ms1 [(r1 & q1 & ED & EC & KB & RI & HR1 & HJ & HQ)|(r1 & ED & HR1 & HLV)].
  2:{ rewrite ED. cbn [CLBPOST]. apply evt_done. split; [exact HLV|].
      destruct (dec_r1_facts c r r1 DR Rin HR1) as (_ & _ & EO1 & _ & EP1 & EL1). eapply PATI_regs; [exact HP| assumption..]. }
  rewrite ED.
  destruct (dec_r1_facts c r r1 DR Rin HR1) as (DR1 & EI1 & EO1 & ER1 & EP1 & EL1).
  pose proof (dchk_sound 8 s c _ _ _ r r1 EC) as SND. cbv zeta in SND. destruct SND as (_ & RN32 & _).
  set (here := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) in *.
  pose proof (code_bits_range here) as RCB. pose proof (code_val_range here) as RCV.
  pose proof (DREGS_hold64 c r1 DR1) as RH1. pose proof DR1 as (Rn1 & Rh1 & Rnh1 & RB1 & RHB1).
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HP| assumption..]).
  destruct (Z.ltb_spec (code_val here) 16) as [V|V].
  -
    eapply evt_cut; [exact (cl_litw X s c r r1 q1 ms1 HJ HQ XO HP EI1 EO1 ER1 EP1 EL1 (conj KB (proj2 RB1)) RH1 RI CPO RN V LL ltac:(lia) RPUT)|].
    intros ms2 (q2 & H2 & HK2 & E13' & E26'). cbn [CLBPOST w_s w_r]. apply evt_done. split.
    + exists q2. split; [exact H2|]. split; [exact HK2|].
      split; [rewrite E13'; unfold cl_lit; cbn [is_have iset_have iset_lens]; rewrite wrap32_id by lia; reflexivity| exact E26'].
    + destruct (ddrop_facts' r1 (code_bits here) ltac:(lia) ltac:(lia) RH1) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
      unfold cl_lit. eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0
        | cbn [is_mode iset_have iset_lens]; rewrite E; unfold CODELENS, FLAGS, HCRC; lia| try reflexivity ..].
      * cbn [is_mode iset_have iset_lens]. rewrite E. reflexivity.
      * exact Pisr.
  -
    eapply evt_cut; [exact (cl_need X s c r r1 q1 ms1 HJ HQ XO DR1 Rin HP EI1 EO1 ER1 EP1 EL1 KB (proj2 RN32) RI CPO RN V)|].
    intros ms2 [(r2 & q2 & EN & HR2 & HJ2 & HQ2)|(r2 & EN & HR2 & HLV)].
    2:{ fold here in EN. rewrite EN. cbn [CLBPOST]. apply evt_done. split; [exact HLV|].
        destruct HR2 as [-> | ->]; [exact HP1| eapply PATI_regs; [exact HP1| reflexivity..]]. }
    fold here in EN. rewrite EN.
    destruct (cl_r2_facts c r1 r2 (code_bits here + cl_nb (code_val here)) DR1 Rin ltac:(unfold cl_nb; destruct (code_val here =? 16); [lia|]; destruct (code_val here =? 17); lia) HR2)
      as (DR2 & KB2 & EI2 & EO2 & ER2 & EP2 & EL2).
    pose proof (DREGS_hold64 c r2 DR2) as RH2. pose proof DR2 as (Rn2 & Rh2 & Rnh2 & RB2 & RHB2).
    assert (HP2 : PATI X (mkW s c r2)) by (eapply PATI_regs; [exact HP1| assumption..]).
    fold here in HJ2.
    assert (EIr : ir_in r2 = ir_in r) by congruence. assert (EOr : ir_out r2 = ir_out r) by congruence.
    assert (ERr : ir_ret r2 = ir_ret r) by congruence. assert (EPr : ir_put r2 = ir_put r) by congruence. assert (ELr : ir_left r2 = ir_left r) by congruence.
    unfold cl_after. cbv zeta. fold here.
    eapply evt_cut; [exact (cl_rep_hd X s c r r1 r2 q2 ms2 HJ2 HQ2 XO HP EIr EOr ERr EPr ELr (conj KB2 (proj2 RB2)) RH2 (proj1 Rh2) V LL
                             ltac:(lia) ltac:(lia) HLs RPUT)|].
    intros ms3 H3. cbv zeta in H3. fold here in H3.
    set (cb := code_bits here) in *. set (nb := cl_nb (code_val here)) in *.
    set (r3 := ddrop r2 cb) in *. set (copy := cl_base (code_val here) + BITSv (ir_hold r3) nb) in *. set (r4 := ddrop r3 nb) in *.
    assert (Rnb : 2 <= nb <= 7) by (subst nb; unfold cl_nb; destruct (code_val here =? 16); [lia|]; destruct (code_val here =? 17); lia).
    destruct (ddrop_facts' r2 cb ltac:(lia) ltac:(lia) RH2) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9). fold r3 in F1, F2, F3, F4, F5, F6, F7, F8, F9.
    destruct (ddrop_facts' r3 nb ltac:(lia) ltac:(lia) F7) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). fold r4 in G1, G2, G3, G4, G5, G6, G7, G8, G9.
    pose proof (BITSv_range (ir_hold r3) nb ltac:(lia) ltac:(lia)) as RBV.
    assert (P7 : 2 ^ nb <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia). change (2 ^ 7) with 128 in P7.
    assert (Rcp : 3 <= copy <= 138) by (subst copy; unfold cl_base; destruct (code_val here =? 16); [lia|]; destruct (code_val here =? 17); lia).
    assert (HP3 : PATI X (mkW s c r3)) by (eapply PATI_regs; [exact HP2| assumption..]).
    assert (HP4 : PATI X (mkW s c r4)) by (eapply PATI_regs; [exact HP3| assumption..]).
    assert (BADP : forall rr, PATI X (mkW s c rr) -> PATI X (cl_bad s c rr)).
    { intros rr HPr. unfold cl_bad. eapply PATI_step; [exact HPr| reflexivity| reflexivity| reflexivity| exact Pf0
        | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| try reflexivity ..]. exact Pisr. }
    revert H3. destruct (Z.eqb_spec (code_val here) 16) as [V16|NV16]; [destruct (Z.eqb_spec (is_have s) 0) as [H0|H0]|]; cbn [andb]; intros H3.
    1:{ cbn [CLBPOST]. apply evt_done. split; [exact H3| apply BADP; exact HP3]. }
    all: revert H3; destruct (Z.ltb_spec (is_nlen s + is_ndist s) (is_have s + copy)) as [OV|OV]; intros H3.
    1,3: cbn [CLBPOST]; apply evt_done; split; [exact H3| apply BADP; exact HP4].
    all: destruct H3 as (q3 & HL3 & HK3 & E13c & E17c & E6c & E26c & E27c); cbn [CLBPOST w_s w_r].
    all: rewrite <- F9, <- G9 in E27c.
    + pose proof (HLs (is_have s - 1) ltac:(lia)) as RL.
      exact (cl_rep_run X s c r4 copy _ q3 ms3 HL3 HK3 E13c E17c E6c E27c XO HP4 LL ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E Pf0 Pisr ltac:(lia)).
    + exact (cl_rep_run X s c r4 copy _ q3 ms3 HL3 HK3 E13c E17c E6c E27c XO HP4 LL ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv iota; lia) E Pf0 Pisr ltac:(lia)).
Qed.

Definition CLPOST (X : ictx) (res : ares unit) : machine_state -> Prop :=
  match res with
  | ARun _ w1 => fun ms' =>
      (if is_mode (w_s w1) =? BAD then exists x8, ILOOP X w1 PC_DISPATCH x8 (wz BAD) ms'
       else exists q, ILOOPg X w1 PC_CL_X q ms' /\ sc12 q = wz (is_nlen (w_s w1)) /\ sc13 q = wz (is_have (w_s w1))
                      /\ sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w1)))
      /\ PATI X w1
  | ALeave w' => fun ms' => ILEAVE X w' ms' /\ PATI X w'
  | ARet _ _ => fun _ => False
  end.

Lemma cl_loop : forall k X s c r q ms,
  ILOOPg X (mkW s c r) PC_CL_B q ms -> CLK X s q -> sc13 q = wz (is_have s) -> sc6 q = wz (ir_have r) ->
  sc7 q = wz (il_NI (ix_L X) + ir_next r) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> CL s c r -> PATI X (mkW s c r) -> is_have s < is_nlen s + is_ndist s -> clw_chk k s c r = true ->
  is_nlen s + is_ndist s - is_have s <= Z.of_nat k ->
  evt psegs (CLPOST X (codelens_while k (mkW s c r))) ms.
Proof.
  induction k as [|k IH]; intros X s c r q ms HL HK E13 E6 E7 E26 XO HCL HP LT CHK RK; [cbn [Z.of_nat] in RK; lia|].
  rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.codelens_while_S. cbn [clw_chk] in CHK.
  replace (is_have s <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (is_have s <? is_nlen s + is_ndist s) with true in CHK by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in CHK. destruct CHK as [OKD CHK].
  pose proof (codelens_body_spec c s r HCL LT) as BS.
  eapply evt_cut; [exact (cl_body X s c r q ms HL HK E13 E6 E7 E26 XO HCL HP LT OKD)|]. intros ms1 H1.
  destruct (codelens_body (mkW s c r)) as [[|] [s1 c1 r1] | w' | rc w']; cbn [CLBPOST w_s w_r] in H1.
  - destruct BS as (-> & HCL1 & Hlt1 & Hb1 & En1 & Ed1 & _ & Ep1). destruct H1 as ((q1 & HL1 & HK1 & E13' & E26') & HP1).
    pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & Hbx1 & Hnl1 & Hnd1 & Hh1 & _).
    eapply evt_cut; [exact (cl_test X s1 c r1 q1 ms1 HL1 HK1 E13' E26' ltac:(lia) Hnl1 Hnd1)|]. intros ms2 (q2 & H2).
    destruct (Z.ltb_spec (is_have s1) (is_nlen s1 + is_ndist s1)) as [LT1|GE1].
    + destruct H2 as (HL2 & HK2 & E13'' & E6'' & E7'' & E26'').
      exact (IH X s1 c r1 q2 ms2 HL2 HK2 E13'' E6'' E7'' E26'' XO HCL1 HP1 LT1 CHK ltac:(rewrite Nat2Z.inj_succ in RK; lia)).
    + destruct H2 as (HL2 & E12'' & E13'' & E26'').
      rewrite codelens_while_stop by lia. cbn [CLPOST w_s w_r]. rewrite E1. change (CODELENS =? BAD) with false.
      apply evt_done. split; [exists q2; repeat split; assumption| exact HP1].
  - destruct BS as (HM1 & _). cbn [CLPOST w_s w_r]. rewrite HM1. change (BAD =? BAD) with true. apply evt_done. exact H1.
  - apply evt_done. cbn [CLPOST]. exact H1.
  - destruct BS.
Qed.

Lemma cl_while : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_CODELENS_E q ms -> sc13 q = wz (is_have s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> WINV (mkW s c r) -> ATY s -> PATI X (mkW s c r) -> is_mode s = CODELENS ->
  evt psegs (CLPOST X (codelens_while 321 (mkW s c r))) ms.
Proof.
  intros X s c r q ms HL E13 E26 XO HW HA HP HM.
  pose proof (codelens_facts s c r HW HA HM) as (HCL & Hlt & _).
  pose proof (WINV_codelens_okb s c r HW HA HM) as OKB. unfold codelens_okb in OKB. cbn [w_s w_c w_r] in OKB.
  apply andb_prop in OKB. destruct OKB as [OKB _]. apply andb_prop in OKB. destruct OKB as [Rnd CHK]. apply Z.leb_le in Rnd.
  pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & _).
  destruct (decode_okb_lvl1 _ _ _ _ _ _ ltac:(cbn [clw_chk] in CHK; replace (is_have s <? is_nlen s + is_ndist s) with true in CHK by (symmetry; apply Z.ltb_lt; lia); apply andb_prop in CHK; exact (proj1 CHK))) as [RN _].
  eapply evt_cut; [exact (cl_entry X s c r q ms HL E13 E26 ltac:(lia) Hnl Hnd RN (cpok_ofs_ok _ _ _ _ HT))|]. intros ms1 (q1 & H1).
  replace (is_have s <? is_nlen s + is_ndist s) with true in H1 by (symmetry; apply Z.ltb_lt; lia).
  destruct H1 as (HL1 & HK1 & E13' & E6' & E7' & E26').
  exact (cl_loop 321 X s c r q1 ms1 HL1 HK1 E13' E6' E7' E26' XO HCL HP Hlt CHK ltac:(cbn; lia)).
Qed.
End Z_infl_a_codelens2.

Module Z_infl_a_codelens.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_iface Z_infl_c_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_a_lenlens.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_t_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_lenlens1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_len OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_codelens1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_codelens2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate Inftrees ItableModel InffastMem RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 RefInflateSafeOK3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LENLENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.



Definition PC_CL_C1 : Z := 0x1d8f0.
Definition PC_CL_RET1 : Z := 0x1d920.
Definition PC_CL_C2 : Z := 0x1db30.
Definition PC_CL_RET2 : Z := 0x1db64.

Local Ltac close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; unfold iframe_cells; inorm; close_cells FRM | exact STK
  | first [exact ZS | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS]
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma cl_x256 : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_CL_X q ms -> sc12 q = wz (is_nlen s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) -> ix_ok X -> PATI X (mkW s c r) ->
  arr_len (is_lens s) = 320 -> ty16 (is_lens s) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
    if arr_get (is_lens s) 256 =? 0
    then exists x8, ILOOP X (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_code_missing_end_of_block) r) PC_DISPATCH x8 (wz BAD) ms'
    else exists q', ILOOPg X (mkW s c r) PC_CL_C1 q' ms' /\ sc12 q' = wz (is_nlen s) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E12 E26 XO HP LL TY RPUT.
  iarm_openg HL. subst x12 x26.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_X.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  pose proof (TY 256) as R256.
  pose proof Gl as Gl'. unfold ilens, u16arr in Gl'. ld16 Gl' (is_lens s) 320 (il_As (ix_L X) + 168) 256 ltac:(lia). clear Gl'.
  zs. br_cases K.
  - replace (arr_get (is_lens s) 256 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    do 3 zs. do 3 zs. do 3 zs. itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  - replace (arr_get (is_lens s) 256 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. |]| cbn [sc12 sc26]; split; reflexivity].
    close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma cl_after2 : forall X s4 c r k ms ret,
  ILOOPk X (mkW s4 c r) PC_CL_RET2 k ms -> k10 k = wz (ret mod 2 ^ 64) -> k27 k = wz 6 -> (ret = 0 \/ ret = 1 \/ ret = -1) -> ix_ok X ->
  0 <= ix_flush X <= 4 ->
  (is_window_blk s4 <> None -> ix_hasw X = true) -> ic_input c = ix_input X -> arr_len (ix_input X) <= 1 ->
  arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
    if negb (ret =? 0)
    then exists x8, ILOOP X (mkW (iset_mode s4 BAD) (icset_msg c MSG_invalid_distances_set) (irset_ret r ret)) PC_DISPATCH x8 (wz BAD) ms'
    else exists x8 x12, ILOOP X (mkW (iset_mode s4 LEN_) c (irset_ret r ret)) PC_LEN_ x8 x12 ms') ms.
Proof.
  intros X s4 c r [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms ret HL E10 E27 RRET XO RF Pwin Pin Pin1 Pout RPUT.
  iarm_openk HL. subst x10 x27.
  ix_open XO. unfold PC_CL_RET2.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  assert (RM : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  do 2 zs. br_cases K.
  -
    assert (R0 : ret = 0) by (destruct RRET as [R|[R|R]]; rewrite R in K; [exact R| |]; exfalso; revert K; vm_compute; discriminate).
    clear RRET K RM. subst ret. cbn [Z.eqb negb].
    do 9 zs. br_false. itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
    close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  -
    assert (R1 : (ret =? 0) = false) by (apply Z.eqb_neq; intros R; rewrite R in K; apply K; reflexivity). rewrite R1. cbn [negb].
    clear RRET K.
    do 2 zs. do 5 zs. do 5 zs. do 2 zs. itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Section CLcalls.
Variable flush : Z.
Hypothesis ITABLE : inflate_table_stmt.

Lemma cl_call2 : forall X s3 c r k ms ret tbl nxt db wk,
  ILOOPk X (mkW s3 c r) PC_CL_C2 k ms -> ix_ok X -> 0 <= ix_flush X <= 4 ->
  (is_window_blk s3 <> None -> ix_hasw X = true) -> ic_input c = ix_input X -> arr_len (ix_input X) <= 1 ->
  arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  inflate_table DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = (ret, tbl, nxt, db, wk) ->
  it_safe DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = true ->
  ATY s3 -> (forall i, 0 <= i < is_ndist s3 -> arr_get (is_lens s3) (is_nlen s3 + i) <= 15) ->
  257 <= is_nlen s3 <= 286 -> 1 <= is_ndist s3 <= 30 -> 0 <= is_next s3 <= 1444 -> iarrs s3 ->
  evt psegs (fun ms' =>
    if negb (ret =? 0)
    then exists x8, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl nxt db wk) BAD) (icset_msg c MSG_invalid_distances_set) (irset_ret r ret)) PC_DISPATCH x8 (wz BAD) ms'
    else exists x8 x12, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl nxt db wk) LEN_) c (irset_ret r ret)) PC_LEN_ x8 x12 ms') ms.
Proof.
  intros X s3 c r [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms ret tbl nxt db wk HL XO RF Pwin Pin Pin1 Pout RPUT EIT SAFE HA HL15 Rnl Rnd Rnx HARR.
  iarm_openk HL.
  ix_open XO. unfold PC_CL_C2.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  rd_sub GA 148%nat 0%nat 4%nat. do 13 zs. itr_groups MUf WMf. clear MUf WMf.
  set (spre := iset_distbits (iset_distcode s3 (CDyn (is_next s3))) 6).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
  assert (ST' : IST m1 (ix_L X) spre);
  [ subst spre; constructor; inorm;
    [ unfold isA, isA_cells; inorm; unfold cp_addr at 2; close_cells GA | exact GT | exact Gl | exact Gw | exact Gc | exact Gwin
    | unfold iarrs in *; inorm; exact HARR | exact LAY ]
  | clear GA GT Gl Gw Gc Gwin ] end.
  pose proof (inflate_table_ret _ _ _ _ _ _ _ _ _ _ _ _ _ EIT) as RRET.
  eapply evt_cut.
  { eapply (ITABLE (ix_L X) spre DISTS true (is_nlen s3) (is_ndist s3) (ix_lo X));
      [ exact ST' | eassumption | rewrite unsigned_lit by lia; exact STK | rewrite unsigned_lit by lia; unfold Z_ITABLE_STACK; lia | lia
      | intros NE; subst spre; cbn in NE; pose proof (xo_win _ XO (Pwin NE)); lia
      | lia | lia | lia | subst spre; cbn; lia | subst spre; cbn; lia
      | subst spre; cbn [it_bits_get is_lens is_codes is_next is_work is_distbits iset_distcode iset_distbits]; exact SAFE
      | exact HA
      | subst spre; cbn [is_lens is_nlen iset_distcode iset_distbits]; exact HL15
      | exact I
      | reflexivity | f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STKc & EA0 & STc).
  rewrite unsigned_lit in MUc, STKc by lia.
  assert (ER : it_result DISTS true (is_nlen s3) (is_ndist s3) spre = (ret, cl_tab2 s3 tbl nxt db wk)).
  { unfold it_result. subst spre. cbn [it_bits_get it_bits_set is_lens is_codes is_next is_work is_distbits iset_distcode iset_distbits].
    rewrite EIT.
    unfold cl_tab2, it_bits_set. cbv [iset_work iset_distbits iset_next iset_distcode iset_codes
      is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk
      is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next
      is_lens is_work is_codes is_sane is_back is_was is_self_blk]. reflexivity. }
  rewrite ER in EA0, STc. cbn [fst snd] in EA0, STc. subst a0'. clear ER ST' spre.
  lazymatch type of WMc with wmono _ ?ma _ => itr_groups MUc WMc; transport_after_call psegs ma m' MUc WMc end. clear MUc WMc MI HARR LAY.
  replace (ret_pc (wz 121700)) with (wz 121700) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply (cl_after2 X (cl_tab2 s3 tbl nxt db wk) c r _ _ ret); [ | | | exact RRET | exact XO | exact RF | exact Pwin | exact Pin | exact Pin1 | exact Pout | exact RPUT].
  { eapply ILOOPk_intro; ired; [ireg .. |].
    apply IMEM_intro; [ exists jf; exact FRM | exact STKc | exact ZS | exact STc | exact IN | exact OUT | exact MIc | exact MU | exact WM ]. }
  all: reflexivity.
Qed.

Lemma cl_after1 : forall X s3 c r k ms ret ret2 tbl2 nxt2 db wk2,
  ILOOPk X (mkW s3 c r) PC_CL_RET1 k ms -> k10 k = wz (ret mod 2 ^ 64) -> (ret = 0 \/ ret = 1 \/ ret = -1) -> ix_ok X -> 0 <= ix_flush X <= 4 ->
  (is_window_blk s3 <> None -> ix_hasw X = true) -> ic_input c = ix_input X -> arr_len (ix_input X) <= 1 ->
  arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  (ret = 0 -> inflate_table DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = (ret2, tbl2, nxt2, db, wk2)) ->
  (ret = 0 -> it_safe DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = true) ->
  (ret = 0 -> ATY s3) -> (ret = 0 -> forall i, 0 <= i < is_ndist s3 -> arr_get (is_lens s3) (is_nlen s3 + i) <= 15) ->
  257 <= is_nlen s3 <= 286 -> 1 <= is_ndist s3 <= 30 -> (ret = 0 -> 0 <= is_next s3 <= 1444) ->
  evt psegs (fun ms' =>
    if negb (ret =? 0)
    then exists x8, ILOOP X (mkW (iset_mode s3 BAD) (icset_msg c MSG_invalid_literal_lengths_set) (irset_ret r ret)) PC_DISPATCH x8 (wz BAD) ms'
    else if negb (ret2 =? 0)
    then exists x8, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl2 nxt2 db wk2) BAD) (icset_msg c MSG_invalid_distances_set) (irset_ret r ret2)) PC_DISPATCH x8 (wz BAD) ms'
    else exists x8 x12, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl2 nxt2 db wk2) LEN_) c (irset_ret r ret2)) PC_LEN_ x8 x12 ms') ms.
Proof.
  intros X s3 c r [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms ret ret2 tbl2 nxt2 db wk2 HL E10 RRET XO RF Pwin Pin Pin1 Pout RPUT
         EIT2 SAFE2 HA3 HL15 Rnl Rnd Rnx.
  pose proof HL as HL0. iarm_openk HL. subst x10.
  ix_open XO. unfold PC_CL_RET1.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  assert (RM : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  zs. br_cases K.
  -
    assert (R0 : ret = 0) by (destruct RRET as [R|[R|R]]; rewrite R in K; [exact R| |]; exfalso; revert K; vm_compute; discriminate).
    clear RRET K RM. subst ret. cbn [Z.eqb negb].
    eapply (cl_call2 X s3 c r _ _ ret2 tbl2 nxt2 db wk2); [| exact XO | exact RF | exact Pwin | exact Pin | exact Pin1 | exact Pout | exact RPUT
      | exact (EIT2 eq_refl) | exact (SAFE2 eq_refl) | exact (HA3 eq_refl) | exact (HL15 eq_refl) | exact Rnl | exact Rnd | exact (Rnx eq_refl) | exact ARRS ].
    eapply ILOOPk_intro; ired; [ireg .. |].
    close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  -
    assert (R1 : (ret =? 0) = false) by (apply Z.eqb_neq; intros R; rewrite R in K; apply K; reflexivity). rewrite R1. cbn [negb].
    clear RRET K.
    do 4 zs. do 5 zs. do 5 zs. do 2 zs. itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_gen jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma cl_call1 : forall X s c r q ms ret tbl nxt lb wk ret2 tbl2 nxt2 db wk2,
  let s3 := cl_tab1 s tbl nxt lb wk in
  ILOOPg X (mkW s c r) PC_CL_C1 q ms -> sc12 q = wz (is_nlen s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> 0 <= ix_flush X <= 4 -> PATI X (mkW s c r) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  inflate_table LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s) = (ret, tbl, nxt, lb, wk) ->
  it_safe LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s) = true ->
  ATY s -> (forall i, 0 <= i < is_nlen s -> arr_get (is_lens s) (0 + i) <= 15) ->
  257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 ->
  (ret = 0 -> inflate_table DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = (ret2, tbl2, nxt2, db, wk2)) ->
  (ret = 0 -> it_safe DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = true) ->
  (ret = 0 -> ATY s3) -> (ret = 0 -> forall i, 0 <= i < is_ndist s3 -> arr_get (is_lens s3) (is_nlen s3 + i) <= 15) ->
  (ret = 0 -> 0 <= is_next s3 <= 1444) ->
  evt psegs (fun ms' =>
    if negb (ret =? 0)
    then exists x8, ILOOP X (mkW (iset_mode s3 BAD) (icset_msg c MSG_invalid_literal_lengths_set) (irset_ret r ret)) PC_DISPATCH x8 (wz BAD) ms'
    else if negb (ret2 =? 0)
    then exists x8, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl2 nxt2 db wk2) BAD) (icset_msg c MSG_invalid_distances_set) (irset_ret r ret2)) PC_DISPATCH x8 (wz BAD) ms'
    else exists x8 x12, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl2 nxt2 db wk2) LEN_) c (irset_ret r ret2)) PC_LEN_ x8 x12 ms') ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms ret tbl nxt lb wk ret2 tbl2 nxt2 db wk2 s3 HL E12 E26 XO RF HP RPUT
         EIT SAFE HA HL15 Rnl Rnd EIT2 SAFE2 HA3 HL15' Rnx.
  iarm_openg HL. subst x12 x26.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_C1.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  do 12 zs. itr_groups MUf WMf. clear MUf WMf.
  set (spre := iset_lencode (iset_next (iset_lenbits s 9) 0) (CDyn 0)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
  assert (ST' : IST m1 (ix_L X) spre);
  [ subst spre; constructor; inorm;
    [ unfold isA, isA_cells; inorm; unfold cp_addr at 1; close_cells GA | exact GT | exact Gl | exact Gw | exact Gc | exact Gwin
    | unfold iarrs in *; inorm; exact ARRS | exact LAY ]
  | clear GA GT Gl Gw Gc Gwin ] end.
  pose proof (inflate_table_ret _ _ _ _ _ _ _ _ _ _ _ _ _ EIT) as RRET.
  eapply evt_cut.
  { eapply (ITABLE (ix_L X) spre LENS false 0 (is_nlen s) (ix_lo X));
      [ exact ST' | eassumption | rewrite unsigned_lit by lia; exact STK | rewrite unsigned_lit by lia; unfold Z_ITABLE_STACK; lia | lia
      | intros NE; subst spre; cbn in NE; pose proof (xo_win _ XO (Pwin NE)); lia
      | lia | lia | lia | subst spre; cbn; lia | subst spre; cbn; lia
      | subst spre; cbn [it_bits_get is_lens is_codes is_next is_work is_lenbits iset_lencode iset_next iset_lenbits]; exact SAFE
      | exact HA
      | subst spre; cbn [is_lens iset_lencode iset_next iset_lenbits]; exact HL15
      | cbn [it_codes_ok]; lia
      | reflexivity | f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STKc & EA0 & STc).
  rewrite unsigned_lit in MUc, STKc by lia.
  assert (ER : it_result LENS false 0 (is_nlen s) spre = (ret, s3)).
  { unfold it_result. subst spre s3. cbn [it_bits_get it_bits_set is_lens is_codes is_next is_work is_lenbits iset_lencode iset_next iset_lenbits].
    rewrite EIT.
    unfold cl_tab1, it_bits_set. cbv [iset_work iset_lenbits iset_next iset_lencode iset_codes
      is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk
      is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next
      is_lens is_work is_codes is_sane is_back is_was is_self_blk]. reflexivity. }
  rewrite ER in EA0, STc. cbn [fst snd] in EA0, STc. subst a0'. clear ER ST' spre.
  lazymatch type of WMc with wmono _ ?ma _ => itr_groups MUc WMc; transport_after_call psegs ma m' MUc WMc end. clear MUc WMc MI ARRS LAY.
  replace (ret_pc (wz 121120)) with (wz 121120) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (Pwin3 : is_window_blk s3 <> None -> ix_hasw X = true) by exact Pwin.
  eapply (cl_after1 X s3 c r _ _ ret ret2 tbl2 nxt2 db wk2);
    [ | | exact RRET | exact XO | exact RF | exact Pwin3 | exact Pin | exact Pin1 | exact Pout | exact RPUT
    | exact EIT2 | exact SAFE2 | exact HA3 | exact HL15' | exact Rnl | exact Rnd | exact Rnx ].
  { eapply ILOOPk_intro; ired; [ireg .. |].
    apply IMEM_intro; [ exists jf; exact FRM | exact STKc | exact ZS | exact STc | exact IN | exact OUT | exact MIc | exact MU | exact WM ]. }
  reflexivity.
Qed.
End CLcalls.

Lemma irset_ret_twice : forall r a b, irset_ret (irset_ret r a) b = irset_ret r b.
Proof. intros [n h p l ho b' i o rt] a b. reflexivity. Qed.

Section CLcore.
Variable flush : Z.
Hypothesis ITABLE : inflate_table_stmt.
Hypothesis RF : 0 <= flush <= 4.

Lemma codelens_core : codelens_core_stmt flush.
Proof.
  intros X [s c r] q ms EF HL E13 E26 XO HW HA HP HM. cbn [w_s w_c w_r] in *.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (RFX : 0 <= ix_flush X <= 4) by (rewrite EF; exact RF).
  rewrite arm_CODELENS_eq.
  pose proof (codelens_facts s c r HW HA HM) as (HCL & Hlt & F).
  pose proof (WINV_codelens_okb s c r HW HA HM) as OKB. unfold codelens_okb in OKB. cbn [w_s w_c w_r] in OKB.
  apply andb_prop in OKB. destruct OKB as [_ OKB].
  pose proof (codelens_next_WINV flush s c r HW HA HM) as NXW. unfold codelens_next in NXW.
  eapply evt_cut; [exact (cl_while X s c r q ms HL E13 E26 XO HW HA HP HM)|]. intros ms1 H1.
  destruct (codelens_while 321 (mkW s c r)) as [[] [s1 c1 r1] | w' | rc w']; cbn [CLPOST w_s w_r] in H1.
  2:{ apply evt_done. cbn [IPOST wof]. exact H1. }
  2:{ destruct H1. }
  destruct (Z.eqb_spec (is_mode s1) BAD) as [EB|NB].
  { destruct H1 as [H1 HP1]. apply evt_done. split; [cbn [IPOST w_s]; rewrite EB; exact H1| exact HP1]. }
  destruct F as [EB|(-> & HCL1 & Hh1 & Hb1 & HA1)]; [contradiction|].
  destruct H1 as [(q1 & HL1 & E12' & E13' & E26') HP1].
  pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & Hbx1 & Hnl1 & Hnd1 & Hh1' & HLs1 & HT1 & HWF1 & HWB1).
  assert (LL1 : arr_len (is_lens s1) = 320) by (destruct HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  pose proof HR1 as (Rn1 & Rh1 & Rnh1 & Rp1 & Rl1 & Rpl1 & _).
  pose proof HP1 as (_ & _ & _ & Pfl1 & _ & _ & _ & _ & _ & _ & Pisr1 & _). cbn [w_s w_c w_r] in Pfl1, Pisr1.
  assert (Pf1 : is_flags s1 = 0) by (destruct Pfl1 as [Pf|(Pf & [E'|E'] & _)]; [exact Pf| |]; rewrite E1 in E'; discriminate E').
  assert (RPUT1 : 0 <= ir_put r1 <= Z.of_nat (length (ix_rest0 X))) by (rewrite <- Pout; lia).
  pose proof HA1 as (TY1 & TYw1 & TYc1).
  unfold cl_post_ok in OKB. unfold cl_post.
  eapply evt_cut; [exact (cl_x256 X s1 c r1 q1 ms1 HL1 E12' E26' XO HP1 LL1 TY1 RPUT1)|]. intros ms2 H2.
  revert OKB NXW H2. destruct (Z.eqb_spec (arr_get (is_lens s1) 256) 0) as [Z0|NZ]; intros OKB NXW H2.
  {
    apply evt_done. split; [cbn [IPOST w_s]; exact H2|]. cbn [wof].
    eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| try reflexivity ..]. exact Pisr1. }
  destruct H2 as (q2 & HL2 & E12'' & E26'').
  revert OKB NXW. destruct (inflate_table LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)) as [[[[ret tbl] nxt] lb] wk] eqn:EIT1.
  cbv zeta. intros OKB NXW.
  apply andb_prop in OKB. destruct OKB as [OKB REST]. apply andb_prop in OKB. destruct OKB as [L15 SAFE1].
  apply andb_prop in REST. destruct REST as [LPO1 REST].
  pose proof (lens15b_sound _ _ _ L15 ltac:(lia) ltac:(lia)) as HL15. rewrite Z.sub_0_r in HL15.
  destruct (ll_post_ok_sound _ _ _ _ LPO1) as (Ltbl & Lwk & Rnxt & Rlb & Ttbl & Twk).
  pose proof (inflate_table_typed LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1) TYc1 TYw1) as TT. rewrite EIT1 in TT. destruct TT as [TT1 TT2].
  set (s3 := cl_tab1 s1 tbl nxt lb wk) in *.
  assert (HA3 : ATY s3) by (split; [exact TY1| split; [exact TT2| exact TT1]]).
  revert REST NXW. destruct (inflate_table DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3)) as [[[[ret2 tbl2] nxt2] db] wk2] eqn:EIT2.
  intros REST NXW.
  assert (C2 : ret = 0 -> (forall i, 0 <= i < is_ndist s3 -> arr_get (is_lens s3) (is_nlen s3 + i) <= 15)
                         /\ it_safe DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = true).
  { intros R0. rewrite R0 in REST. cbn [Z.eqb] in REST. apply andb_prop in REST. destruct REST as [REST _]. apply andb_prop in REST. destruct REST as [L15' SAFE2].
    split; [|exact SAFE2]. pose proof (lens15b_sound _ _ _ L15' ltac:(cbn; lia) ltac:(cbn; lia)) as H. intros i Hi. apply H. lia. }
  eapply evt_cut.
  { exact (cl_call1 ITABLE X s1 c r1 q2 ms2 ret tbl nxt lb wk ret2 tbl2 nxt2 db wk2 HL2 E12'' E26'' XO RFX HP1 RPUT1 EIT1 SAFE1 HA1 HL15 Hnl1 Hnd1
             (fun _ => EIT2) (fun R0 => proj2 (C2 R0)) (fun _ => HA3) (fun R0 => proj1 (C2 R0)) (fun _ => Rnxt)). }
  intros ms3 H3. cbv zeta in H3. fold s3 in H3.
  revert H3 NXW. destruct (Z.eqb_spec ret 0) as [R0|R1]; cbn [negb]; intros H3 NXW.
  2:{
      apply evt_done. split; [cbn [IPOST w_s]; exact H3|]. cbn [wof]. subst s3. unfold cl_tab1.
      eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| try reflexivity ..]. exact Pisr1. }
  rewrite irset_ret_twice. rewrite irset_ret_twice in NXW.
  revert H3 NXW. destruct (Z.eqb_spec ret2 0) as [R0'|R1']; cbn [negb]; intros H3 NXW.
  2:{
      apply evt_done. split; [cbn [IPOST w_s]; exact H3|]. cbn [wof]. subst s3. unfold cl_tab1, cl_tab2.
      eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| try reflexivity ..]. exact Pisr1. }
  replace (flush =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia).
  replace (flush =? Z_TREES) with false in NXW by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia).
  destruct H3 as (x8' & x12' & HL3).
  destruct (NXW _ eq_refl) as [HW2 HM2].
  refine (len__core X _ x8' x12' ms3 HL3 XO HW2 _ HM2).
  subst s3. unfold cl_tab1, cl_tab2.
  eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold LEN_, FLAGS, HCRC; lia| try reflexivity ..]. exact Pisr1.
Qed.

Lemma arm_CODELENS_of : arm_stmt flush CODELENS PC_CODELENS (arm_CODELENS ivar_ref flush).
Proof.
  intros X [s c r] x12 ms EF HL XO HW HA HP HM.
  assert (H0 : evt psegs (fun ms' => exists q, ILOOPg X (mkW s c r) PC_CODELENS_E q ms' /\ sc13 q = wz (is_have s) /\ sc26 q = wz (il_NI (ix_L X) + ir_next r)) ms).
  { pose proof HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in HMF, HM. rewrite HM in HMF. unfold MF in HMF. cbn in HMF.
    destruct HMF as (_ & _ & Hnl & Hnd & Hh & _).
    destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM).
    pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s w_c w_r] in *.
    unfold PC_CODELENS. do 2 zs.
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]| cbn [sc13 sc26]; split; reflexivity]. }
  eapply evt_cut; [exact H0|]. intros ms1 (q1 & H1 & E13 & E26).
  exact (codelens_core X (mkW s c r) q1 ms1 EF H1 E13 E26 XO HW HA HP HM).
Qed.
End CLcore.
End Z_infl_a_codelens.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_t_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2.Z_infl_arms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_lit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_term OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_type OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_dict OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_check OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_dictid OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_head OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_copy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_stored OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_match OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_distext OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_lenext OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_len OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_table OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_arms_have.Z_infl_a_codelens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Open.
  Hypothesis ITABLE : inflate_table_stmt.

  Lemma arms_ok_0 : arms_ok 0.
  Proof.
    pose proof (codelens_core 0 ITABLE ltac:(lia)) as CLC.
    pose proof (lenlens_core 0 CLC ITABLE) as LLC.
    constructor.
    - exact (arm_HEAD_ok 0).
    - exact (arm_DICTID_ok 0 ltac:(lia)).
    - exact (arm_DICT_ok 0 ltac:(lia)).
    - exact (arm_TYPE_ok 0 ltac:(lia)).
    - exact (arm_TYPEDO_ok 0 ltac:(lia)).
    - exact (arm_STORED_ok 0 ltac:(lia)).
    - exact (arm_COPY__ok 0).
    - exact (arm_COPY_ok 0).
    - exact (arm_TABLE_of 0 LLC).
    - exact (arm_LENLENS_of 0 CLC ITABLE).
    - exact (arm_CODELENS_of 0 ITABLE ltac:(lia)).
    - exact (arm_LEN__ok 0).
    - exact (arm_LEN_ok 0).
    - exact (arm_LENEXT_ok 0).
    - exact (arm_DIST_ok 0).
    - exact (arm_DISTEXT_ok 0).
    - exact (arm_MATCH_ok 0).
    - exact (arm_LIT_ok 0).
    - exact (arm_CHECK_ok 0).
    - exact (arm_LENGTH_ok 0).
    - exact (arm_DONE_ok 0).
    - exact (arm_BAD_ok 0).
    - exact (arm_MEM_ok 0).
  Qed.
End Open.
