(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_itab_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_a_codelens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_arms.

Module Z_infl_a_lit.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_ukit.
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

Lemma arm_LIT_spec : forall X w x26 x12 ms,
  ILOOP X w PC_LIT x26 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LIT ->
  evt usegs (fun ms' => IPOST X (arm_LIT w) ms' /\ PATI X (wof (arm_LIT w))) ms.
Proof.
  intros X [s c r] x26 x12 ms HL XO HW HP HM. iarm_open HL. rewrite arm_LIT_eq.
  destruct HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & RHB & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & [POB POW] & PBK). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LIT.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB.
  open_IST ST. open_isA GA. ifine m.
  zs. zstep. br_cases K.
  -
    assert (Kl : ir_left r <> 0) by lia. replace (ir_left r =? 0) with false by (symmetry; apply Z.eqb_neq; exact Kl).
    do 2 zs. gT.
    rd_sub GA 108%nat 0%nat 1%nat. zs. clear RD.  (* 1.4: length moved +16 *)
    do 3 zs.
    assert (RLEN : 0 <= is_length s < 2^32) by (destruct HCORE as (_&_&_&_&_&_&_&_&_&_&_&_&_&H); exact H).
    pose proof (u8arr_store_ok usegs _ _ _ (ir_put r) (wa (il_NO (ix_L X) + ir_put r)) OUT ltac:(rewrite LOB; lia) eq_refl) as SOK.
    zs. rewrite le1_zx8_wz by lia.
    pose proof (u8arr_write usegs _ _ _ (ir_put r) (Z_to_bv 8 (wrap8 (is_length s))) OUT ltac:(rewrite LOB; lia)) as OUT2. clear OUT LOB.
    store_done.
    rewrite iout_bytes_store in OUT2 by lia.
    pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) (wrap8 (is_length s)))) (ir_put r + 1) ltac:(lia)) as LOB.
    apply (f_equal Z.of_nat) in LOB.
    do 7 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; try ireg.
      apply IMEM_intro; ired.
      * exists j0, jf. replace (ir_left r + -1) with (wrap32 (ir_left r - 1)) in FRM by (rewrite wrap32_id by lia; lia). exact FRM.
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
      split; [| revert PBK; bk_keep].
      split; [|split; [exact POW|split; [rewrite wrap32_id by lia; lia| split; [reflexivity| exact PHW]]]]. intros i Hi. destruct (Z.eq_dec i (ir_put r)) as [->|NE].
      * rewrite arr_get_set_same by lia. pose proof (wrap8_range (is_length s)) as H8. change (2^8) with 256 in H8. exact H8.
      * rewrite arr_get_set_other by lia. apply POB. lia.
  -
    assert (Kl : ir_left r = 0) by lia. replace (ir_left r =? 0) with true by (symmetry; apply Z.eqb_eq; exact Kl).
    do 5 zs.
    itr_groups MUf WMf.
    apply evt_done. split; [|exact HP].
    cbn [IPOST]. eapply ILEAVE_intro; ired; try ireg.
    apply IMEML_intro; ired.
    + exists (wz (ir_ret r)), j0, jf. unfold iframe_cells. rewrite Kl. exact FRM.
    + exact STK.
    + exact ZS.
    + constructor; [exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + exact OUT.
    + eassumption.
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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs.
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
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  unfold PC_DONE. do 2 zs.
  apply evt_done. split; [|exact HP].
  cbn [IPOST]. eapply ILEAVE_intro; ired; try ireg.
  eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma arm_BAD_ok : forall flush, arm_stmt flush BAD PC_BAD arm_BAD.
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. rewrite arm_BAD_eq.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  apply evt_done. split; [|exact HP].
  cbn [IPOST]. eapply ILEAVE_intro; ired; try ireg.
  eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma arm_MEM_ok : forall flush, arm_stmt flush MEM PC_MEM arm_MEM.
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. rewrite arm_MEM_eq.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_infl_pure Zh_kit Z_ukit.
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

Definition PC_TYPEDO_NB : Z := 0x1f458.
Definition PC_TYPEDO_J : Z := 0x1f498.

Lemma typedo_nb3 : forall X s c r x26 x12 ms,
  ILOOP X (mkW s c r) PC_TYPEDO_NB x26 x12 ms -> ix_ok X -> REGS c r -> PATI X (mkW s c r) -> ir_bits r < 8 ->
  evt usegs (NBJ X s c r 3 PC_TYPEDO_J x26) ms.
Proof.
  intros X s c r x26 x12 ms HL XO HREGS HP MFB.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  unfold PC_TYPEDO_NB. ix_open XO.
  do 2 zs. br_cases K.
  -
    apply evt_done. left. exists r, (wz 2). split; [|split].
    + rewrite NEEDBITS3_eq by lia. replace (ir_bits r <? 3) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    + left. split; [reflexivity| lia].
    + eapply ILOOP_intro; ired; [ireg .. |]. exact HMEM.
  - zs. br_cases K2.
    +
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      do 2 zs. gT.
      zs. clear RD. do 7 zs. rewrite <- Pin. rewrite !pull_shift by lia. rewrite lor8_small by lia.
      apply evt_done. left. eexists (pullr c r), _. split; [|split].
      * rewrite NEEDBITS3_eq by lia. replace (ir_bits r <? 3) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (ir_have r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      * right. split; [reflexivity| lia].
      * eapply ILOOP_intro; pullr_rw c r; ired; [ireg .. |].
        eapply IMEM_regs; [exact HMEM| reflexivity..].
    +
      do 4 zs.
      apply evt_done. right. exists r. split; [|split].
      * rewrite NEEDBITS3_eq by lia. replace (ir_bits r <? 3) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (ir_have r =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Local Ltac close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma typedo_core : forall flush X w x26 x12 ms,
  ix_flush X = flush -> 0 <= flush <= 4 ->
  ILOOP X w PC_TYPEDO x26 x12 ms -> ix_ok X -> WINV w -> PATI X w -> (is_mode (w_s w) = TYPE \/ is_mode (w_s w) = TYPEDO) ->
  evt usegs (fun ms' => IPOST X (arm_TYPEDO ivar_ref flush w) ms' /\ PATI X (wof (arm_TYPEDO ivar_ref flush w))) ms.
Proof.
  intros flush X [s c r] x26 x12 ms EF RF HL XO HW HP HM.
  destruct HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  assert (MFB : ir_bits r < 8).
  { destruct HM as [E|E]; rewrite E in HMF; unfold MF in HMF; cbn in HMF; destruct HMF as [_ H]; exact H. }
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
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
      unfold PC_TYPEDO. zs. rewrite L1'. zs. br_false.
      do 6 zs. rewrite (land63_small (Z.land (ir_bits r) 7)) by (pose proof (land7_range (ir_bits r)); lia).
      rewrite land_m8_u64 by lia. pose proof (land7_le (ir_bits r) ltac:(lia)) as L7.
      itr_groups MUf WMf.
      apply evt_done. split.
      - cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      - cbn [wof]. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold CHECK, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep].
        exact HISR. }
  eapply evt_cut.
  { destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
    pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
    unfold PC_TYPEDO. zs. rewrite L0. zs. br_true.
    eapply (typedo_nb3 X s c r x26); [eapply ILOOP_intro; ired; [ireg .. | exact HMEM] | exact XO | exact HREGS | exact HP | exact MFB]. }
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
  iarm_open HJ. ix_open XO.
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
      do 9 zs. rewrite (Z.shiftr_div_pow2 (ir_hold r1) 3) by lia.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. apply HISR'.
    +
      replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (t =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (t =? 2) with true by (symmetry; apply Z.eqb_eq; lia).
      do 7 zs. rewrite (Z.shiftr_div_pow2 (ir_hold r1) 3) by lia.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TABLE, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. apply HISR'.
  - zs. br_cases K2.
    +
      replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (t =? 1) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (flush =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia).
      (* 1.4 UBSan: the fixed tables come from a CALL to inflate_fixed (0x2219c): mv a0,s0; jal; its null and
         alignment checks (trap 0x221d4); 7 instructions forming lenfix / distfix / (5 << 32 | 9); sd lencode (120);
         sd distcode (128); then the one 8-byte store of lenbits | distbits at 136 (through the recast, as at 1.3.1);
         ret. The isA cells are at the 1.4 layout. *)
      zs. zs. ustep 0x22234. ustep 0x22234. ustep 0x22234. do 9 zs.
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
      (* ret; ld ra,80(sp) (the 16209 cell); li a0,-2; ld a1,136(sp); mv a3,s2; add a2,ra,-10; li a4,6; sw a2,8(s0); bne a1,a4 *)
      do 9 zs. br_true. do 3 zs. rewrite (Z.shiftr_div_pow2 (ir_hold r1) 3) by lia.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold LEN_, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. exact HISRf.
    +
      replace (t =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      do 7 zs. rewrite (Z.shiftr_div_pow2 (ir_hold r1) 3) by lia.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold STORED, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. apply HISR'.
Qed.

Lemma arm_TYPEDO_ok : forall flush, 0 <= flush <= 4 -> arm_stmt flush TYPEDO PC_TYPEDO (arm_TYPEDO ivar_ref flush).
Proof. intros flush RF X w x12 ms EF HL XO HW _ HP HM. exact (typedo_core flush X w _ x12 ms EF RF HL XO HW HP (or_intror HM)). Qed.

Lemma type_core : forall flush X w x26 x12 ms,
  ix_flush X = flush -> 0 <= flush <= 4 ->
  ILOOP X w PC_TYPE x26 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = TYPE ->
  evt usegs (fun ms' => IPOST X (arm_TYPE ivar_ref flush w) ms' /\ PATI X (wof (arm_TYPE ivar_ref flush w))) ms.
Proof.
  intros flush X w x26 x12 ms EF RF HL XO HW HP HM.
  assert (EA : arm_TYPE ivar_ref flush w = arm_TYPEDO ivar_ref flush w).
  { unfold arm_TYPE. cbn [iv_flush_exits ivar_ref andb].
    replace (flush =? Z_BLOCK) with false by (symmetry; apply Z.eqb_neq; unfold Z_BLOCK; lia).
    replace (flush =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia). reflexivity. }
  rewrite EA.
  eapply (evt_cut usegs (ILOOP X w PC_TYPEDO x26 (wz 2))); [| intros ms1 H1; exact (typedo_core flush X w _ _ ms1 EF RF H1 XO HW HP (or_introl HM))].
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM).
  pose proof HMEM as ((j0 & jf & FRM) & _). unfold iframe_cells in FRM. cbn [w_s w_c w_r] in FRM. ix_open XO.
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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs Z_infl_pure Z_adler32.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_adler32 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_type OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
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
      (* total_in += in - avail_in before Z_NEED_DICT *)
      ARet Z_NEED_DICT (let w := RESTORE (mkW s c r) in
                        mkW (w_s w) (icset_total_in (w_c w) (wrap64 (ic_total_in (w_c w) + wrap32 (ir_in r - ic_avail_in (w_c w))))) (w_r w))
    else arm_TYPE ivar_ref flush (mkW (iset_mode (iset_check s iadler32_init) TYPE) (icset_adler c iadler32_init) r).
Proof.
  intros flush s c r. unfold arm_DICT, abind, gs. cbn [w_s]. destruct (is_havedict s =? 0); reflexivity.
Qed.

(* the need-dict exit's total_in update *)
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
(* the UBSan build zero-extends with sll 32 / srl 32 *)
Lemma dict_total_in_eq_u : forall t X h,
  wz (t + Z.land (Z.land (bv_swrap 32 (Z.land X 18446744073709551615 - h)) 18446744073709551615 ≪ 32) 18446744073709551615 ≫ 32)
  = wz (wrap64 (t + wrap32 (X - h))).
Proof.
  intros t X h. rewrite <- dict_total_in_eq. f_equal. f_equal.
  change 18446744073709551615 with (Z.ones 64). change 4294967295 with (Z.ones 32).
  set (y := Z.land (bv_swrap 32 (Z.land X (Z.ones 64) - h)) (Z.ones 64)).
  assert (Ry : 0 <= y < 2 ^ 64) by (subst y; rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z.land_ones by lia.
  change (2 ^ 64) with 18446744073709551616 in *. change (2 ^ 32) with 4294967296.
  Z.div_mod_to_equations. nia.
Qed.

Definition DQ (X : ictx) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h13 q = wz (il_S (ix_L X)) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
  /\ h24 q = wz (ir_have r) /\ h25 q = wz (il_NI (ix_L X) + ir_next r).

Lemma dict_core11 : forall flush X w q ms,
  ix_flush X = flush -> 0 <= flush <= 4 -> ILOOPh X w PC_DICT q ms -> DQ X (w_r w) q ->
  ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = DICT ->
  evt usegs (fun ms' => IPOST X (arm_DICT ivar_ref flush w) ms' /\ PATI X (wof (arm_DICT ivar_ref flush w))) ms.
Proof.
  intros flush X [s c r] [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms EF RF HL HQ XO HW HP HM.
  unfold DQ in HQ. hred_in HQ. cbn [w_r] in HQ. destruct HQ as (-> & -> & -> & -> & -> & ->).
  rewrite arm_DICT_eq.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
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
    iarm_openh HL. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. open_izs ZS. ifineS m.
    unfold PC_DICT. zs. rewrite D0. zs. br_false.
    (* 1.4 UBSan: j to the need-dict block; RESTORE's stores plus total_in += in - avail_in (ld, ld, subw, sll, srl,
       add, sd); li a0,2; j *)
    do 17 zs.
    itr_groups MUf WMf.
    apply evt_done. split; [| cbn [wof]; eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| exact Pgz| first [reflexivity | exact (PATI_noput _ _ _ _ HP)]..| | bk_keep]; exact HISR].
    cbn [IPOST]. eapply IRET_intro; inorm; [ireg .. | | intros _; unfold RST; cbn [w_c w_r]; ired; repeat split; exact HPUT0].
    apply IMEML_intro; inorm.
    + exists (wz (ir_ret r)), j0, jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app]. inorm. close_cells ZS.
      all: first [apply dict_total_in_eq_u | apply dict_total_in_eq].
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
    { unfold w1. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. exact HISR. }
    eapply (evt_cut usegs (fun ms' => exists x26' x12', ILOOP X w1 PC_TYPE x26' x12' ms')).
    2:{ intros ms1 (x26' & x12' & H1). exact (type_core flush X w1 x26' x12' ms1 EF RF H1 XO HW1 HP1 eq_refl). }
    clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW HW1 HP1. subst w1.
    iarm_openh HL. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. open_izs ZS. ifineS m.
    unfold PC_DICT. zs. rewrite D1'. zs. br_true.
    do 4 zs.
    remember (wz (bv_unsigned (ix_sp X) + -256)) as spw eqn:Espw.
    assert (ESP : bv_unsigned spw = bv_unsigned (ix_sp X) + -256) by (rewrite Espw; apply unsigned_lit; lia).
    call (adler32_null_spec (ix_lo X)).
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ eassumption. }
    1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold ADLER32_FRAME. lia. }
    lazymatch goal with H : stk usegs _ _ (bv_unsigned spw) |- _ => rewrite ESP in H; rename H into STK end.
    subst spw.
    do 8 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; inorm; [ireg .. |].
    apply IMEM_intro; inorm.
    + exists j0, jf. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE, iadler32_init. cbn [app]. inorm. close_cells ZS.
    + constructor; inorm; [unfold isA, isA_cells, iadler32_init; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
Qed.

Lemma arm_DICT_ok : forall flush, 0 <= flush <= 4 -> arm_stmt flush DICT PC_DICT (arm_DICT ivar_ref flush).
Proof.
  intros flush RF X w x12 ms EF HL XO HW _ HP HM.
  destruct (ILOOPh_of_ILOOP _ _ _ _ _ _ HL) as (q & HL' & _ & _ & HH).
  apply (dict_core11 flush X w q ms EF RF HL'); [|assumption ..].
  unfold hhome in HH. unfold DQ. destruct HH as (E9 & _ & _ & E13 & E18 & E22 & E24 & E25). repeat split; assumption.
Qed.
End Z_infl_a_dict.


Module Z_infl_a_check.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Z_adler32 Zh_kit Z_ukit.
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

Definition PC_CHECK_J : Z := 0x1fdf4.
Definition PC_CHECK_T : Z := 0x203f8.

Definition CHKQ (X : ictx) (r r1 : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h13 q = wz (il_S (ix_L X)) /\ h14 q = wz 5
  /\ h19 q = wz (il_NI (ix_L X) + ir_next r1) /\ h26 q = wz (ir_have r1) /\ h20 q = wz (ir_bits r1) /\ h22 q = wz (ir_hold r1).

Lemma check_nb32 : forall X s c r x26 x12 ms,
  ILOOP X (mkW s c r) PC_CHECK x26 x12 ms -> ix_ok X -> REGS c r -> PATI X (mkW s c r) -> is_wrap s = 5 ->
  evt usegs (NBJq X s c r 32 PC_CHECK_J (CHKQ X r)) ms.
Proof.
  intros X s c r x26 x12 ms HL XO HREGS HP Pw.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  open_IST ST. open_isA GA. cbn [w_s] in GA.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  unfold PC_CHECK. ix_open XO.
  zs. rewrite Pw. zs. br_false.
  do 2 zs. br_cases K.
  -
    do 3 zs. apply evt_done. left. eexists r, _. split; [|split; [|split]].
    + apply nb_enough. lia.
    + left. split; [reflexivity| lia].
    + eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
    + unfold CHKQ. hred. repeat split; reflexivity.
  - do 5 zs. zs. br_cases K2.
    +
      assert (EH1 : ir_have r = 1) by lia. rewrite EH1 in *.
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      do 2 zs. gT. do 2 zs. zs. clear RD. do 8 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      zs. br_cases K3.
      *
        zs. br_false. do 10 zs.
        apply evt_done. right. exists (pullr c r). split; [|split].
        -- apply nb_pull_dry; lia.
        -- right. reflexivity.
        -- eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
      * zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
        -- apply nb_pull_ok; lia.
        -- right. split; [reflexivity| lia].
        -- eapply ILOOPh_intro; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| reflexivity..].
        -- unfold CHKQ. hred. pullr_rw c r. repeat split; ireg.
    +
      assert (EH0 : ir_have r = 0) by lia. rewrite EH0 in *.
      do 10 zs.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.


Definition CHKT (X : ictx) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X))
  /\ h19 q = wz (il_NI (ix_L X) + ir_next r) /\ h26 q = wz (ir_have r) /\ h20 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r).

Definition chk_ov (s : inflate_state) (c : icall) (r : iregs) : option Z :=
  if chk_out r =? 0 then None
  else Some (UPDATE_CHECK_bytes s (is_check s) (arr_slice (ic_outbuf c) (ir_put r - chk_out r) (chk_out r))).

Lemma check_mid : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_CHECK_J q ms -> CHKQ X r r q ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) -> is_flags s = 0 -> adler_canon (is_check s) -> ir_out r = arr_len (ic_outbuf c) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (chk_s3 s r (chk_ov s c r)) (chk_c3 c r (chk_ov s c r)) r) PC_CHECK_T q' ms' /\ CHKT X r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HP Pf0 HCK HOUT.
  unfold CHKQ in HQ. hred_in HQ. destruct HQ as (-> & -> & -> & -> & -> & -> & -> & ->).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & [POB POW] & PBK). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  destruct HCK as (CK1 & CK2 & CK3).
  assert (ECO : chk_out r = ir_put r).
  { unfold chk_out. rewrite HOUT, <- Rpl. replace (ir_put r + ir_left r - ir_left r) with (ir_put r) by lia. rewrite wrap32_id by lia. reflexivity. }
  assert (RPUT : ir_put r = 0 \/ ir_put r = 1) by lia.
  clear RH Rin Pfl PL PHD HREGS.
  iarm_openh HL. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_CHECK_J. do 3 zs. replace (ir_out r - ir_left r) with (ir_put r) by lia.
  do 4 zs. rewrite !land_u32_small by lia.
  do 5 zs. change (Z.land 5 4) with 4. zs. br_false. zs. br_cases K.
  -
    assert (EP : ir_put r = 0) by lia.
    assert (EOV : chk_ov s c r = None) by (unfold chk_ov; rewrite ECO, EP; reflexivity).
    rewrite EOV. unfold chk_s3, chk_c3, chk_s2, chk_c2. rewrite ECO.
    zs. zs. br_true.
    itr_groups MUf WMf.
    apply evt_done. eexists. split.
    { eapply ILOOPh_intro; ired; [ireg .. |].
      apply IMEM_intro; inorm.
      + exists j0, jf. exact FRM.
      + exact STK.
      + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm. rewrite wz_wrap64. close_cells ZS.
      + constructor; inorm; [unfold isA, isA_cells; inorm; rewrite wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
      + exact IN.
      + unfold iout. exact OUT.
      + eassumption.
      + exact MU.
      + exact WM. }
    unfold CHKT. hred. repeat split; first [reflexivity | ireg].
  -
    assert (EP : ir_put r = 1) by lia.
    pose proof (POB 0 ltac:(lia)) as RBY.
    assert (EOV : chk_ov s c r = Some (adler32_len1 (is_check s) (arr_get (ic_outbuf c) 0))).
    { unfold chk_ov. rewrite ECO, EP. change (1 =? 0) with false. cbv iota. f_equal. unfold UPDATE_CHECK_bytes. rewrite Pf0. cbn [Z.eqb negb].
      change (arr_slice (ic_outbuf c) (1 - 1) 1) with [arr_get (ic_outbuf c) 0]. unfold iadler32_upd.
      apply adler32_model_len1; [exact (conj CK1 (conj CK2 CK3))| exact RBY]. }
    pose proof (iout_byte_at _ _ _ _ _ 0 OUT ltac:(lia) ltac:(lia)) as BY. rewrite Z.add_0_r in BY.
    rewrite EOV. unfold chk_s3, chk_c3, chk_s2, chk_c2. rewrite ECO. rewrite EP in *.
    zs. rewrite Pf0. do 7 zs.
    replace (il_NO (ix_L X) + 1 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite xor_guard_sub by lia. cbn [Z.b2z]. change (Z.land (Z.lxor 0 18446744073709551615) 1) with 1.
    gT. gT.
    do 2 zs. replace (il_NO (ix_L X) + 1 + - (1)) with (il_NO (ix_L X)) by lia. zs.
    remember (wz (bv_unsigned (ix_sp X) + -256)) as spw eqn:Espw.
    assert (ESP : bv_unsigned spw = bv_unsigned (ix_sp X) + -256) by (rewrite Espw; apply unsigned_lit; lia).
    call (adler32_len1_spec (ix_lo X)).
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RBY. } 1:{ exact BY. } 1:{ eassumption. }
    1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold ADLER32_FRAME. lia. }
    lazymatch goal with H : stk usegs _ _ (bv_unsigned spw) |- _ => rewrite ESP in H; rename H into STK end.
    subst spw.
    do 2 zs. rd_sub GA 16%nat 0%nat 1%nat. zs. clear RD. rewrite Pw. zs. change (Z.land (bv_unsigned (zx8 (wz 5))) 4) with 4.
    do 4 zs. zs. br_false.
    itr_groups MUf WMf.
    apply evt_done. eexists. split.
    { eapply ILOOPh_intro; ired; [ireg .. |].
      apply IMEM_intro; inorm.
      + exists j0, jf. exact FRM.
      + exact STK.
      + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm. rewrite wz_wrap64. close_cells ZS.
      + constructor; inorm; [unfold isA, isA_cells; inorm; rewrite wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
      + exact IN.
      + unfold iout. rewrite (iout_bytes_ext _ _ c) by reflexivity. rewrite EP. exact OUT.
      + eassumption.
      + exact MU.
      + exact WM. }
    unfold CHKT. hred. repeat split; first [reflexivity | ireg].
Qed.


Local Ltac close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma check_tail : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_CHECK_T q ms -> CHKT X r q ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) -> is_flags s = 0 -> adler_canon (is_check s) ->
  evt usegs (fun ms' => IPOST X (chk_tail s c r 5 (ZSWAP32 (ir_hold r))) ms' /\ PATI X (wof (chk_tail s c r 5 (ZSWAP32 (ir_hold r))))) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HP Pf0 HCK.
  unfold CHKT in HQ. hred_in HQ. destruct HQ as (-> & -> & -> & -> & -> & -> & -> & ->).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HISR : ISR s) by (split; assumption).
  destruct HCK as (CK1 & _).
  clear RH Rin Pfl PL PHD HREGS.
  iarm_openh HL. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_CHECK_T. zs. rewrite Pf0. zs. zs. br_false.
  do 14 zs. rewrite zswap_clang by lia.
  pose proof (ZSWAP32_range (ir_hold r)) as RZ.
  zs. br_cases K.
  -
    unfold chk_tail. change (Z.land 5 4 =? 0) with false. replace (ZSWAP32 (ir_hold r) =? is_check s) with false by (symmetry; apply Z.eqb_neq; exact K).
    cbn [negb andb]. unfold chk_r3.
    do 10 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
      close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + cbn [wof]. eapply PATI_step_out; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| ired; lia| reflexivity| | bk_keep]. exact HISR.
  -
    unfold chk_tail. change (Z.land 5 4 =? 0) with false. replace (ZSWAP32 (ir_hold r) =? is_check s) with true by (symmetry; apply Z.eqb_eq; exact K).
    cbn [negb andb]. rewrite (arm_LENGTH_skip (iset_mode s LENGTH) c _ (or_intror Pf0)). unfold done_w, chk_r3.
    do 8 zs. zs. rewrite Pw. zs. br_false. zs. rewrite Pf0. zs. br_true. do 9 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
      apply IMEML_intro; inorm.
      * eexists _, j0, jf. exact FRM.
      * exact STK.
      * eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS.
      * constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
      * exact IN.
      * unfold iout. exact OUT.
      * eassumption.
      * exact MU.
      * exact WM.
    + cbn [wof]. eapply PATI_step_out; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold DONE, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| ired; lia| reflexivity| | bk_keep]. exact HISR.
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
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HISR : ISR s) by (split; assumption).
  rewrite HM in HMF, HWF. unfold MF, WF in HMF, HWF. cbn in HMF, HWF. destruct HMF as [_ HCK]. specialize (HCK Pf0).
  eapply evt_cut; [exact (check_nb32 X s c r _ x12 ms HL XO HREGS HP Pw)|].
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & HQ)|(r1 & EN & HR1 & HLV)].
  2:{
      rewrite (arm_CHECK_dry s c r _ ltac:(lia) EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
  rewrite (arm_CHECK_run s c r r1 Pw Pf0 EN).
  destruct (NEEDBITS_spec c 32 s r HREGS ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & EIN & EOUT & ERET).
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HP| assumption..]).
  assert (HOUT1 : ir_out r1 = arr_len (ic_outbuf c)) by (rewrite EOUT; exact HWF).
  assert (HJ1 : ILOOPh X (mkW s c r1) PC_CHECK_J q1 ms1) by (eapply ILOOPh_regs; [exact HJ| assumption ..]).
  assert (HQ1 : CHKQ X r1 r1 q1) by (unfold CHKQ in *; rewrite EPUT; exact HQ).
  eapply evt_cut; [exact (check_mid X s c r1 q1 ms1 HJ1 HQ1 XO HREGS1 HP1 Pf0 HCK HOUT1)|].
  intros ms2 (q2 & HJ2 & HQ2).
  destruct (chk_c3_facts c r1 (chk_ov s c r1)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
  destruct (chk_s3_eq s r1 (chk_ov s c r1)) as (t & ck & ES3 & Rt & Eck).
  apply (check_tail X _ _ r1 q2 ms2 HJ2 HQ2 XO).
  - unfold REGS in *. rewrite F5, F6. exact HREGS1.
  - rewrite ES3. eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| cbn; rewrite HM; unfold CHECK, FLAGS, HCRC; lia| reflexivity| exact F5| exact F6| reflexivity| reflexivity| reflexivity| reflexivity| cbn [is_mode iset_check iset_total]; rewrite HM; reflexivity| | bk_keep]. exact HISR.
  - rewrite ES3. exact Pf0.
  - rewrite ES3. cbn [is_check iset_check]. rewrite Eck. unfold chk_ov. destruct (chk_out r1 =? 0); [exact HCK|].
    unfold UPDATE_CHECK_bytes. rewrite Pf0. cbn [Z.eqb negb]. apply adler32_model_canon.
Qed.

Lemma arm_LENGTH_ok : forall flush, arm_stmt flush LENGTH PC_LENGTH arm_LENGTH.
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
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
  unfold PC_LENGTH. zs. rewrite Pw. zs. br_false. zs. rewrite Pf0. zs. br_true.
  do 9 zs.
  itr_groups MUf WMf.
  apply evt_done. split; [| cbn [wof]; eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold DONE, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]; exact HISR].
  cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
  apply IMEML_intro; inorm.
  + exists (wz (ir_ret r)), j0, jf. exact FRM.
  + exact STK.
  + exact ZS.
  + constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
  + exact IN.
  + unfold iout. exact OUT.
  + eassumption.
  + exact MU.
  + exact WM.
Qed.
End Z_infl_a_check.


Module Z_infl_a_dictid.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Z_adler32 Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_adler32 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_type OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_dict OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface AdlerModel InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateA_DICT DeflateLz RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.AdlerModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DICT OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_DICTID_J : Z := 0x1f398.

Definition DIQ (X : ictx) (r r1 : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X))
  /\ h12 q = wz (il_NI (ix_L X) + ir_next r1) /\ h10 q = wz (ir_have r1) /\ h22 q = wz (ir_hold r1).

Lemma dictid_nb32 : forall X s c r x26 x12 ms,
  ILOOP X (mkW s c r) PC_DICTID x26 x12 ms ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) ->
  evt usegs (NBJq X s c r 32 PC_DICTID_J (DIQ X r)) ms.
Proof.
  intros X s c r x26 x12 ms HL XO HREGS HP.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  unfold PC_DICTID. ix_open XO.
  do 2 zs. br_cases K.
  -
    do 2 zs. apply evt_done. left. eexists r, _. split; [|split; [|split]].
    + apply nb_enough. lia.
    + left. split; [reflexivity| lia].
    + eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
    + unfold DIQ. hred. repeat split; reflexivity.
  - do 4 zs. zs. br_cases K2.
    +
      assert (EH1 : ir_have r = 1) by lia. rewrite EH1 in *.
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      do 2 zs. gT. zs. zs. clear RD. do 9 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      zs. br_cases K3.
      *
        zs. br_false. do 10 zs.
        apply evt_done. right. exists (pullr c r). split; [|split].
        -- apply nb_pull_dry; lia.
        -- right. reflexivity.
        -- eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
      * zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
        -- apply nb_pull_ok; lia.
        -- right. split; [reflexivity| lia].
        -- eapply ILOOPh_intro; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| reflexivity..].
        -- unfold DIQ. hred. pullr_rw c r. repeat split; ireg.
    +
      assert (EH0 : ir_have r = 0) by lia. rewrite EH0 in *.
      do 10 zs.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Local Ltac close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma dictid_core : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_DICTID_J q ms -> DIQ X r r q ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (iset_mode (iset_check s (ZSWAP32 (ir_hold r))) DICT) (icset_adler c (ZSWAP32 (ir_hold r))) (irset_bits (irset_hold r 0) 0))
                                              PC_DICT q' ms' /\ DQ X (irset_bits (irset_hold r 0) 0) q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HP.
  unfold DIQ in HQ. hred_in HQ. destruct HQ as (-> & -> & -> & -> & -> & ->).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  clear RH Rin Pfl PL PHD HREGS.
  iarm_openh HL. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_DICTID_J. do 15 zs. rewrite zswap_clang by lia.
  pose proof (ZSWAP32_range (ir_hold r)) as RZ.
  do 6 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. split.
  { eapply ILOOPh_intro; ired; [ireg .. |].
    close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM. }
  unfold DQ. hred. ired. repeat split; ireg.
Qed.

Lemma arm_DICTID_ok : forall flush, 0 <= flush <= 4 -> arm_stmt flush DICTID PC_DICTID (arm_DICTID ivar_ref flush).
Proof.
  intros flush RF X [s c r] x12 ms EF HL XO HW _ HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HISR : ISR s) by (split; assumption).
  assert (HPUT0 : ir_put r = 0) by (apply (NOPUTb_false _ _ (PATI_noput _ _ _ _ HP)); left; exact HM).
  rewrite HM in HMF, HWF. unfold MF, WF in HMF, HWF. cbn in HMF, HWF. destruct HMF as [HWB0 HCK].
  eapply evt_cut; [exact (dictid_nb32 X s c r _ x12 ms HL XO HREGS HP)|].
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & HQ)|(r1 & EN & HR1 & HLV)].
  2:{ rewrite (arm_DICTID_dry flush s c r _ EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
  rewrite (arm_DICTID_run flush s c r r1 EN).
  destruct (NEEDBITS_spec c 32 s r HREGS ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & EIN & EOUT & ERET).
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HP| assumption..]).
  assert (HJ1 : ILOOPh X (mkW s c r1) PC_DICTID_J q1 ms1) by (eapply ILOOPh_regs; [exact HJ| assumption ..]).
  assert (HQ1 : DIQ X r1 r1 q1) by (unfold DIQ in *; rewrite EPUT; exact HQ).
  eapply evt_cut; [exact (dictid_core X s c r1 q1 ms1 HJ1 HQ1 XO HREGS1 HP1)|].
  intros ms2 (q2 & H2 & HQ2).
  apply (dict_core11 flush X _ q2 ms2 EF RF H2 HQ2 XO).
  -
    unfold WINV. cbn [w_s w_c w_r]. split; [exact HCORE|]. split.
    { destruct HREGS1 as (Rn & Rh & Rnh & Rp & Rl & Rpl & _ & Rin & Rli & Rlo). unfold REGS, HB. ired. change (2 ^ 0) with 1.
      split; [exact Rn|]. split; [exact Rh|]. split; [exact Rnh|]. split; [exact Rp|]. split; [exact Rl|]. split; [exact Rpl|]. split; [lia|]. split; [exact Rin|]. split; [exact Rli| exact Rlo]. }
    ired. unfold MF, WF. cbn. split; [split; [exact HWB0| lia]|]. split; [rewrite EOUT; exact HWF| intros E; rewrite EPUT; exact HPUT0].
  - eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold DICT, FLAGS, HCRC; cbn; lia| reflexivity..| |exact HISR| bk_keep].
    ired. rewrite EPUT, HPUT0. reflexivity.
  - reflexivity.
Qed.
End Z_infl_a_dictid.


Module Z_infl_a_head.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Z_infl_pure3 Z_adler32 Zh_kit Z_ukit.
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

Definition PC_HEAD_J : Z := 0x1fd58.

Definition HDQ (X : ictx) (r r1 : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h14 q = wz 5
  /\ h19 q = wz (il_NI (ix_L X) + ir_next r1) /\ h26 q = wz (ir_have r1) /\ h12 q = wz (ir_bits r1) /\ h22 q = wz (ir_hold r1).

Lemma head_nb16 : forall X s c r x26 x12 ms,
  ILOOP X (mkW s c r) PC_HEAD x26 x12 ms -> ix_ok X -> REGS c r -> PATI X (mkW s c r) -> is_wrap s = 5 ->
  evt usegs (NBJq X s c r 16 PC_HEAD_J (HDQ X r)) ms.
Proof.
  intros X s c r x26 x12 ms HL XO HREGS HP Pw.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  open_IST ST. open_isA GA. cbn [w_s] in GA.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  unfold PC_HEAD. ix_open XO.
  zs. rewrite Pw. zs. br_false.
  do 2 zs. br_cases K.
  -
    do 3 zs. apply evt_done. left. eexists r, _. split; [|split; [|split]].
    + apply nb_enough. lia.
    + left. split; [reflexivity| lia].
    + eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
    + unfold HDQ. hred. repeat split; reflexivity.
  - do 5 zs. zs. br_cases K2.
    +
      assert (EH1 : ir_have r = 1) by lia. rewrite EH1 in *.
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      do 3 zs. gT. zs. zs. clear RD. do 7 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      zs. br_cases K3.
      *
        zs. br_false. do 12 zs.
        apply evt_done. right. exists (pullr c r). split; [|split].
        -- apply nb_pull_dry; lia.
        -- right. reflexivity.
        -- eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
      * zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
        -- apply nb_pull_ok; lia.
        -- right. split; [reflexivity| lia].
        -- eapply ILOOPh_intro; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| reflexivity..].
        -- unfold HDQ. hred. pullr_rw c r. repeat split; ireg.
    +
      assert (EH0 : ir_have r = 0) by lia. rewrite EH0 in *.
      do 12 zs.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma PATI_step_bad : forall X s c r s' c' r', PATI X (mkW s c r) -> is_mode s = HEAD ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = is_flags s ->
  is_mode s' = BAD -> is_window_blk s' = is_window_blk s ->
  ic_input c' = ic_input c -> ic_outbuf c' = ic_outbuf c -> ir_put r' = ir_put r -> is_window s' = is_window s ->
  ir_out r' = ir_out r -> ir_left r' = ir_left r -> ISR s' -> (bk_ok s -> bk_ok s') -> PATI X (mkW s' c' r').
Proof.
  intros X s c r s' c' r' (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _ & (P12 & P13 & P14 & P15 & P16) & P17) HM E1 E2 E3 E4 EM E6 E7 E8 E9 E10 E11 E12 HI HBK.
  specialize (HBK P17).
  unfold PATI, OBYT in *. cbn [w_s w_c w_r] in *. rewrite E1, E2, E3, E4, E6, E7, E8, E9, E10, E11, E12, EM.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split. { destruct P4 as [F0|(F1 & _ & F3 & F4)]; [left; exact F0| right; split; [exact F1|]; split; [right; reflexivity|]; split; assumption]. }
  split; [unfold BAD, FLAGS, HCRC; lia|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|]. split; [exact P10|].
  split; [exact HI|]. split; [|exact HBK]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [reflexivity| exact P16].
Qed.

Local Ltac close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma head_core : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_HEAD_J q ms -> HDQ X r r q ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) -> is_mode s = HEAD -> 16 <= ir_bits r -> ir_put r = 0 ->
  evt usegs (fun ms' => IPOST X (hd_zres s c r) ms' /\ PATI X (wof (hd_zres s c r))) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HP HM HB16 HPUT0.
  unfold HDQ in HQ. hred_in HQ. destruct HQ as (-> & -> & -> & -> & -> & -> & ->).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HISR : ISR s) by (split; assumption).
  unfold hd_zres. cbv zeta. rewrite Pw. change (Z.land 5 1 =? 0) with false. cbn [orb].
  rewrite (hd_x_spec (ir_hold r) RH64).
  clear RH Rin Pfl PL PHD HREGS.
  iarm_openh HL. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_HEAD_J. do 2 zs. br_true. zs. rewrite Phd. zs. br_true. do 4 zs. br_false.
  do 12 zs. br_cases K; rewrite hd_x_clang in K by lia; change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by lia.
  1:{
      assert (E31 : (hd_x (ir_hold r) mod 31 =? 0) = false) by (apply Z.eqb_neq; intros E0; apply (proj2 (mod31_clang _ (hd_x_range _ RH64))) in E0; lia).
      rewrite E31. cbn [negb].
      do 8 zs.
      itr_groups MUf WMf.
      apply evt_done. split.
      + cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      + cbn [wof]. eapply PATI_step_bad; [exact HP| exact HM| reflexivity ..| exact HISR| bk_keep]. }
  assert (E31 : (hd_x (ir_hold r) mod 31 =? 0) = true) by (apply Z.eqb_eq; apply (proj1 (mod31_clang _ (hd_x_range _ RH64))); lia).
  rewrite E31. cbn [negb]. clear K E31.
  assert (EB4 : forall h, 0 <= h -> BITSv h 4 = Z.land h 15) by (intros h Hh; rewrite BITSv_mod by lia; change 15 with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
  rewrite (EB4 _ (proj1 RH64)). unfold Z_DEFLATED.
  do 4 zs. br_cases K.
  -
    replace (Z.land (ir_hold r) 15 =? 8) with false by (symmetry; apply Z.eqb_neq; exact K). cbn [negb].
    do 13 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
      close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + cbn [wof]. eapply PATI_step_bad; [exact HP| exact HM| reflexivity ..| exact HISR| bk_keep].
  - replace (Z.land (ir_hold r) 15 =? 8) with true by (symmetry; apply Z.eqb_eq; exact K). cbn [negb].
    (* 1.4 UBSan: the window size is checked before wbits is read: srl; and; li 7; bltu (bad); then on the good path
       lw wbits; add; beqz; bgeu (wbits >= len); bnez (keep wbits) *)
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
      do 14 zs.
      itr_groups MUf WMf.
      apply evt_done. split.
      * cbn [IPOST]. eexists _, _. unfold drop4. eapply ILOOP_intro; ired; [ireg .. |].
        close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * cbn [wof]. eapply PATI_step_bad; [exact HP| exact HM| reflexivity ..| exact HISR| bk_keep].
    + replace (15 <? l4 + 8) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
      zs. rewrite ?Pwb. zs. zs. br_false. zs. br_true. zs. br_true.
      do 8 zs.
      remember (wz (bv_unsigned (ix_sp X) + -256)) as spw eqn:Espw.
      assert (ESP : bv_unsigned spw = bv_unsigned (ix_sp X) + -256) by (rewrite Espw; apply unsigned_lit; lia).
      call (adler32_null_spec (ix_lo X)).
      1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ eassumption. }
      1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold ADLER32_FRAME. lia. }
      lazymatch goal with H : stk usegs _ _ (bv_unsigned spw) |- _ => rewrite ESP in H; rename H into STK end.
      subst spw.
      do 4 zs. zs. br_cases K3.
      *
        replace (Z.land (Z.shiftr (ir_hold r) 4) 512 =? 0) with true by (symmetry; apply Z.eqb_eq; apply (fdict_clang _ RH64); exact K3). cbn [negb].
        do 11 zs.
        itr_groups MUf WMf. rewrite dmax_clang in GA by lia.
        apply evt_done. split.
        -- cbn [IPOST]. eexists _, _. unfold hd_ok_s, r00, iadler32_init. eapply ILOOP_intro; ired; [ireg .. |].
           close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
        -- cbn [wof]. unfold hd_ok_s, r00. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| reflexivity| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. exact HISR.
      *
        replace (Z.land (Z.shiftr (ir_hold r) 4) 512 =? 0) with false by (symmetry; apply Z.eqb_neq; intros E0; apply (fdict_clang _ RH64) in E0; lia). cbn [negb].
        do 12 zs.
        itr_groups MUf WMf. rewrite dmax_clang in GA by lia.
        apply evt_done. split.
        -- cbn [IPOST]. eexists _, _. unfold hd_ok_s, r00, iadler32_init. eapply ILOOP_intro; ired; [ireg .. |].
           close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
        -- cbn [wof]. unfold hd_ok_s, r00. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| reflexivity| unfold DICTID, FLAGS, HCRC; cbn; lia| reflexivity..| |exact HISR| bk_keep].
           ired. rewrite HPUT0. reflexivity.
Qed.


Lemma arm_HEAD_ok : forall flush, arm_stmt flush HEAD PC_HEAD (arm_HEAD ivar_ref).
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  rewrite HM in HWF. unfold WF in HWF. cbn in HWF. destruct HWF as [HOUT HPUT0].
  rewrite (arm_HEAD_eq s c r ltac:(rewrite Pwb; discriminate)). rewrite Pw. change (5 =? 0) with false. cbv iota.
  eapply evt_cut; [exact (head_nb16 X s c r _ x12 ms HL XO HREGS HP Pw)|].
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & HQ)|(r1 & EN & HR1 & HLV)].
  2:{ rewrite EN. apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
  rewrite EN. unfold hd_res. rewrite Pw. change (negb (Z.land 5 2 =? 0)) with false. cbn [andb].
  destruct (NEEDBITS_spec c 16 s r HREGS ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & HB16 & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & EIN & EOUT & ERET).
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HP| assumption..]).
  assert (HJ1 : ILOOPh X (mkW s c r1) PC_HEAD_J q1 ms1) by (eapply ILOOPh_regs; [exact HJ| assumption ..]).
  assert (HQ1 : HDQ X r1 r1 q1) by (unfold HDQ in *; rewrite EPUT; exact HQ).
  exact (head_core X s c r1 q1 ms1 HJ1 HQ1 XO HREGS1 HP1 HM HB16 ltac:(rewrite EPUT; exact HPUT0)).
Qed.
End Z_infl_a_head.


Module Z_infl_a_copy.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_pure Z_infl_pure2 Z_infl_pure3 Z_updwin_pure Zh_kit Z_ukit Z_infl_defs.
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

Local Ltac close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
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

Lemma copy_core : forall X w x26 x12 ms,
  ILOOP X w PC_COPY x26 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = COPY ->
  evt usegs (fun ms' => IPOST X (arm_COPY w) ms' /\ PATI X (wof (arm_COPY w))) ms.
Proof.
  intros X [s c r] x26 x12 ms HL XO HW HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
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
    do 3 zs.
    itr_groups MUf WMf.
    apply evt_done. split; [| cbn [wof]; eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]; exact HISR].
    cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
    apply IMEM_intro; inorm.
    + exists j0, jf. exact FRM.
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
    do 3 zs. br_cases K2.
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
          split; [| revert PBK; unfold bk_ok; cbn [is_back is_mode iset_length]; rewrite HM; intros HBK; exact HBK].
          split. { intros i Hi. rewrite blit1. destruct (Z.eq_dec i (ir_put r)) as [->|NE].
                   - rewrite arr_get_set_same by lia. apply Rin.
                   - rewrite arr_get_set_other by lia. apply POB. lia. }
          split; [exact POW|]. split; [rewrite EL1, EP0, HWF, Pout, ELR; change (wrap32 (1 - 1)) with 0; lia|]. split; [reflexivity| exact PHW]. }
        rewrite EL1, EH1, EP0, EN0 in *. rewrite iout_bytes_0 in OUT.
        apply rw_cells_of_u8arr in OUT. rewrite ELR in OUT.
        do 6 zs.
        rewrite ?Z.add_0_r in *.
        eapply evt_cut.
        { eapply (memcpy_Z (il_NO (ix_L X)) (il_NI (ix_L X)) 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (av8 (ix_input X) (arr_len (ix_input X))) (ix_rest0 X));
            [exact IN| rewrite av8_length, ELI; reflexivity| exact OUT| pose proof (xo_io _ XO) as SEPIO; unfold apart in SEPIO; rewrite ELI, ELR in SEPIO; lia| exact MI| lia| lia| lia]. }
        intros ms' PO. destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & PC & SRC').
        clear OUT SRC'.
        itr_groups MUc WMc.
        clear MUf WMf.
        transport_after_call usegs m m' MUc WMc. clear MUc WMc. ifine m'.
        replace (ret_pc (wz 128376)) with (wz 128376) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        do 3 zs. gT. gT. gT. zs. gT. gT. gT. do 12 zs.
        itr_groups MUf WMf.
        apply evt_done. split; [|exact HP'].
        cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
        apply IMEM_intro; inorm.
        -- exists j0, jf. exact FRM.
        -- exact STK.
        -- exact ZS.
        -- constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA; apply len_dec_cell; lia| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
        -- exact IN.
        -- unfold iout. rewrite Pin. rewrite (iout_copy1 (ix_rest0 X) c (ix_input X) ELR ltac:(lia)). rewrite <- ELI. apply (u8arr_of_rw_cells usegs _ _ _ _ PC).
        -- eassumption.
        -- exact MU.
        -- exact WM.
      *
        assert (ECN : cpy_n s r = 0) by (unfold cpy_n; cbv zeta; destruct (Z.ltb_spec (ir_have r) (is_length s)); destruct (Z.ltb_spec (ir_left r) (ir_have r)); destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
        rewrite (arm_COPY_leave s c r NL0 ECN).
        do 3 zs.
        apply evt_done. split; [|exact HP].
        cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
        apply IMEML_intro; inorm.
        -- exists (wz (ir_ret r)), j0, jf. exact FRM.
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
      do 3 zs.
      apply evt_done. split; [|exact HP].
      cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
      apply IMEML_intro; inorm.
      * exists (wz (ir_ret r)), j0, jf. exact FRM.
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

Lemma copy__core : forall X w x26 x12 ms,
  ILOOP X w PC_COPY_ x26 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = COPY_ ->
  evt usegs (fun ms' => IPOST X (arm_COPY_ w) ms' /\ PATI X (wof (arm_COPY_ w))) ms.
Proof.
  intros X [s c r] x26 x12 ms HL XO HW HP HM. rewrite arm_COPY__eq.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HISR : ISR s) by (split; assumption).
  set (w1 := mkW (iset_mode s COPY) c r).
  assert (HW1 : WINV w1).
  { unfold WINV, w1. cbn [w_s w_c w_r]. split; [exact HCORE|]. split; [exact HREGS|].
    rewrite HM in HMF, HWF. unfold MF, WF in *. cbn in HMF, HWF |- *. split; [exact HMF|]. split; [exact HWF| exact HWB]. }
  assert (HP1 : PATI X w1).
  { unfold w1. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold COPY, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. exact HISR. }
  eapply (evt_cut usegs (fun ms' => exists x12', ILOOP X w1 PC_COPY x26 x12' ms')).
  2:{ intros ms1 (x12' & H1). exact (copy_core X w1 x26 x12' ms1 H1 XO HW1 HP1 eq_refl). }
  clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW HW1 HP1. subst w1.
  iarm_open HL. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  unfold PC_COPY_. do 2 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. eapply ILOOP_intro; inorm; [ireg .. |].
  apply IMEM_intro; inorm.
  + exists j0, jf. exact FRM.
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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_pure Z_infl_pure2 Z_infl_pure3 Z_updwin_pure Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit Z_infl_defs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_updwin_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_copy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs.
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

Local Ltac close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
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


Definition PC_STORED_NB : Z := 0x1f1c8.
Definition PC_STORED_J : Z := 0x1f4e0.

Definition SNQ (X : ictx) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X))
  /\ h25 q = wz (il_NI (ix_L X) + ir_next r) /\ h24 q = wz (ir_have r) /\ h15 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r).
Definition STQ (X : ictx) (r r1 : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X))
  /\ h14 q = wz (il_NI (ix_L X) + ir_next r1) /\ h12 q = wz (ir_have r1) /\ h18 q = wz (ir_bits r1) /\ h22 q = wz (ir_hold r1).

Lemma stored_nb32 : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_STORED_NB q ms -> SNQ X r q ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) -> ir_bits r <= 31 ->
  evt usegs (NBJq X s c r 32 PC_STORED_J (STQ X r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HP HB31.
  unfold SNQ in HQ. hred_in HQ. destruct HQ as (-> & -> & -> & -> & -> & -> & -> & ->).
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r] in *. hred.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  unfold PC_STORED_NB. ix_open XO.
  do 5 zs. zs. br_cases K2.
  -
    assert (EH1 : ir_have r = 1) by lia. rewrite EH1 in *.
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    do 2 zs. gT. do 2 zs. zs. clear RD. do 9 zs. rewrite <- Pin. rewrite !pull_shift by lia.
    zs. br_cases K3.
    +
      zs. br_false. do 9 zs.
      apply evt_done. right. exists (pullr c r). split; [|split].
      * apply nb_pull_dry; lia.
      * right. reflexivity.
      * eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
    + zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
      * apply nb_pull_ok; lia.
      * right. split; [reflexivity| lia].
      * eapply ILOOPh_intro; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| reflexivity..].
      * unfold STQ. hred. pullr_rw c r. repeat split; ireg.
  -
    assert (EH0 : ir_have r = 0) by lia. rewrite EH0 in *.
    do 9 zs.
    apply evt_done. right. exists r. split; [|split].
    + apply nb_dry; lia.
    + left. reflexivity.
    + eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma stored_tail : forall flush X s c r q ms,
  ILOOPh X (mkW s c r) PC_STORED_J q ms -> STQ X r r q ->
  ix_flush X = flush -> 0 <= flush <= 4 -> ix_ok X -> WINV (mkW s c r) -> PATI X (mkW s c r) -> is_mode s = STORED ->
  evt usegs (fun ms' => IPOST X (st_tail flush s c r) ms' /\ PATI X (wof (st_tail flush s c r))) ms.
Proof.
  intros flush X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ EF RF XO HW HP HM.
  unfold STQ in HQ. hred_in HQ. destruct HQ as (-> & -> & -> & -> & -> & -> & -> & ->).
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
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
    { unfold w2. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold COPY_, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. exact HISR. }
    eapply (evt_cut usegs (fun ms' => exists x12', ILOOP X w2 PC_COPY_ x26 x12' ms')).
    2:{ intros ms1 (x12' & H1). exact (copy__core X w2 _ x12' ms1 H1 XO HW2 HP2 eq_refl). }
    clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW HW2 HP2. subst w2.
    iarm_openh HL. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. ifine m.
    assert (RX : 0 <= Z.lxor (Z.shiftr (ir_hold r) 16) (Z.land (ir_hold r) 65535) < 2 ^ 64).
    { rewrite (proj2 (lxor_swap_eq _ _ 65535) EQ). lia. }
    unfold PC_STORED_J. do 6 zs. zs. if_cases K; br_norm K; [exfalso; apply K; apply lxor_swap_eq; exact EQ|]. clear K.
    do 8 zs. zs. br_true.
    itr_groups MUf WMf.
    assert (E16 : Z.land (ir_hold r) 65535 = Z.land (wrap32 (ir_hold r)) 65535).
    { rewrite land16_wrap32 by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. }
    rewrite E16 in GA.
    apply evt_done. eexists. eapply ILOOP_intro; inorm; [ireg .. |].
    apply IMEM_intro; inorm.
    + exists j0, jf. exact FRM.
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
    iarm_openh HL. ix_open XO.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. open_izs ZS. ifineS m.
    assert (RX : 0 <= Z.lxor (Z.shiftr (ir_hold r) 16) (Z.land (ir_hold r) 65535) < 2 ^ 64).
    { apply lxor_lt_pow2; [| |lia].
      - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. change (2 ^ 64) with 18446744073709551616 in *. Z.to_euclidean_division_equations. lia.
      - change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (ir_hold r) (2 ^ 16) ltac:(lia)) as Q. change (2 ^ 16) with 65536 in Q. change (2 ^ 64) with 18446744073709551616. lia. }
    unfold PC_STORED_J. do 6 zs. zs. if_cases K; br_norm K; [|exfalso; apply NEQ; apply lxor_swap_eq; exact K]. clear K.
    do 8 zs.
    itr_groups MUf WMf.
    apply evt_done. split.
    + cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
      close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + cbn [wof]. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. exact HISR.
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
  eapply (evt_cut usegs (NBJq X s c (bb_r r) 32 PC_STORED_J (STQ X (bb_r r)))).
  { destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
    assert (HMEMb : IMEM X (mkW s c (bb_r r)) m) by (eapply IMEM_regs; [exact HMEM| assumption..]).
    ix_open XO.
    unfold PC_STORED. do 4 zs. rewrite (land63_small (Z.land (ir_bits r) 7)) by lia. br_cases K.
    -
      zs. rewrite land_m8_u64 by lia. do 2 zs.
      apply evt_done. left. eexists (bb_r r), _. split; [|split; [|split]].
      + apply nb_enough. rewrite B8. lia.
      + left. split; [reflexivity|]. rewrite B8. lia.
      + eapply ILOOPh_intro; [..| exact HMEMb]; ired; ireg.
      + unfold STQ. hred. rewrite ?B1, ?B2, ?B3, ?B4, ?B8, ?B9. repeat split; ireg.
    -
      zs. rewrite land24 by lia.
      eapply (stored_nb32 X s c (bb_r r));
        [eapply ILOOPh_intro; [..| exact HMEMb]; ired; ireg | unfold SNQ; hred; rewrite ?B1, ?B2, ?B3, ?B4, ?B8, ?B9; repeat split; ireg | exact XO | exact HREGSb | exact HPb | rewrite B8; lia]. }
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & HQ)|(r1 & EN & HR1 & HLV)].
  2:{ rewrite (arm_STORED_dry flush s c r _ EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HPb| eapply PATI_regs; [exact HPb| reflexivity..]]. }
  rewrite (arm_STORED_run flush s c r r1 EN).
  destruct (NEEDBITS_spec c 32 s (bb_r r) HREGSb ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & EIN & EOUT & ERET).
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HPb| assumption..]).
  assert (HW1 : WINV (mkW s c r1)).
  { unfold WINV. cbn [w_s w_c w_r]. split; [exact HCORE|]. split; [exact HREGS1|].
    rewrite HM in HMF, HWF |- *. unfold MF, WF in *. cbn in HMF, HWF |- *. split; [exact HMF|]. split; [rewrite EOUT, B6; exact HWF| intros E; rewrite EPUT, B3; exact (HWB E)]. }
  assert (HJ1 : ILOOPh X (mkW s c r1) PC_STORED_J q1 ms1) by (eapply ILOOPh_regs; [exact HJ| assumption ..]).
  assert (HQ1 : STQ X r1 r1 q1) by (unfold STQ in *; rewrite EPUT, B3; exact HQ).
  exact (stored_tail flush X s c r1 q1 ms1 HJ1 HQ1 EF RF XO HW1 HP1 HM).
Qed.
End Z_infl_a_stored.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_a_codelens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_a_codelens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_a_codelens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_a_codelens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_a_codelens.

Module Z_infl_a_table.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs Z_infl_pure Zh_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_a_codelens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_a_codelens.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_t_iface.
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

Lemma land_ones32 : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x H. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. change (2^32) with 4294967296. lia. Qed.
Lemma shl3 : forall x, x ≪ 3 = 8 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. lia. Qed.

Definition PC_TABLE_J : Z := 0x1f638.
Definition PC_TABLE_DRY : Z := 0x21284.

Definition TBQ (X : ictx) (x26 : word) (r1 : iregs) (q : iscrh) : Prop :=
  h11 q = wz (ir_bits r1) /\ h14 q = wz (il_NI (ix_L X) + ir_next r1) /\ h12 q = wz (ir_have r1) /\ h22 q = wz (ir_hold r1)
  /\ h13 q = wz (il_S (ix_L X)) /\ h9 q = wz (il_NO (ix_L X) + ir_put r1) /\ h10 q = wz (-2) /\ h26 q = x26.

Lemma table_nb14 : forall X s c r x26 x12 ms,
  ILOOP X (mkW s c r) PC_TABLE x26 x12 ms -> ix_ok X -> REGS c r -> PATI X (mkW s c r) -> ir_bits r < 14 ->
  evt usegs (NBJq X s c r 14 PC_TABLE_J (TBQ X x26)) ms.
Proof.
  intros X s c r x26 x12 ms HL XO HREGS HP MFB.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  unfold PC_TABLE. ix_open XO.
  zs. zs. br_cases K0; [exfalso; lia|]. do 5 zs. zs. br_cases K.
  -
    assert (H1 : ir_have r = 1) by lia.
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    zs. zs. zs. br_cases KG; [| exfalso; lia].
    zs. zs. zs. clear RD. zs. zs. zs. zs. rewrite <- Pin. rewrite !pull_shift by lia. zs. zs. zs. zs. zs. br_cases K3.
    +
      zs. br_cases K4; [exfalso; lia|]. do 10 zs. rewrite land_ones32, shl3 by lia.
      apply evt_done. right. exists (pullr c r). split; [|split].
      * apply nb_pull_dry; lia.
      * right. reflexivity.
      * eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
    + zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
      * apply nb_pull_ok; lia.
      * right. split; [reflexivity| lia].
      * eapply ILOOPh_intro; try reflexivity. eapply IMEM_regs; [exact HMEM| reflexivity..].
      * unfold TBQ. hred. pullr_rw c r. repeat split; ireg.
  -
    do 10 zs. rewrite land_ones32, shl3 by lia.
    apply evt_done. right. exists r. split; [|split].
    + apply nb_dry; lia.
    + left. reflexivity.
    + eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

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

Local Ltac close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma table_fin : forall flush X s c r q x26 ms,
  ix_flush X = flush ->
  ILOOPh X (mkW s c r) PC_TABLE_J q ms -> TBQ X x26 r q ->
  ix_ok X -> PATI X (mkW s c r) -> 14 <= ir_bits r <= 63 -> 0 <= ir_hold r < 2^64 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_have r ->
  evt usegs (fun ms' =>
     if (286 <? is_nlen (tb_s s (ir_hold r))) || (30 <? is_ndist (tb_s s (ir_hold r)))
     then exists x26' x12', ILOOP X (mkW (iset_mode (tb_s s (ir_hold r)) BAD) (icset_msg c MSG_too_many_length_or_distance_symbols) (tb_r r)) PC_DISPATCH x26' x12' ms'
     else exists q', ILOOPh X (mkW (tb_s2 s (ir_hold r)) c (tb_r r)) PC_LENLENS_E q' ms' /\ h17 q' = wz 0 /\ h14 q' = wz (il_NI (ix_L X) + ir_next r)
                     /\ h12 q' = wz (ir_have r) /\ h9 q' = wz (il_NO (ix_L X) + ir_put r) /\ h11 q' = wz (ix_flush X) /\ h13 q' = wz (il_S (ix_L X))
                     /\ h18 q' = wz (ir_bits r - 14) /\ h22 q' = wz (Z.shiftr (ir_hold r) 14)) ms.
Proof.
  intros flush X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26' x28 x29 x30 x31] x26 ms EF HL HQ XO HP RB RH RPUT RHV.
  unfold TBQ in HQ. iarm_openh HL. destruct HQ as (E11 & E14 & E12 & E22 & E13 & E9 & E10 & E26). subst x11 x14 x12 x22 x13 x9 x10 x26'.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_TABLE_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  do 7 zs. rewrite tb_f1, (tb_f2 (ir_hold r) RH), (tb_f3 (ir_hold r) RH).
  destruct (tb_ranges (ir_hold r)) as (Ra & Rb & Rc).
  unfold tb_s2, tb_s, tb_r. cbn [is_nlen is_ndist is_ncode iset_ncode iset_ndist iset_nlen iset_have iset_mode].
  set (fa := ir_hold r mod 2^5) in *. set (fb := ir_hold r mod 2^10 / 2^5) in *. set (fc := ir_hold r mod 2^14 / 2^10) in *.
  do 8 zs. zs. br_cases K1.
  {
    replace (286 <? fa + 257) with true by (symmetry; apply Z.ltb_lt; lia). cbn [orb].
    do 7 zs. itr_groups MUf WMf.
    apply evt_done. do 2 eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM. }
  replace (286 <? fa + 257) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  zs. zs. br_cases K2.
  {
    replace (30 <? fb + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    do 7 zs. itr_groups MUf WMf.
    apply evt_done. do 2 eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM. }
  replace (30 <? fb + 1) with false by (symmetry; apply Z.ltb_ge; lia).
  do 4 zs. itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; try reflexivity| hred; repeat split; try reflexivity; ireg].
  close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Section Table.
Variable flush : Z.
Hypothesis LENLENS_CORE : lenlens_core_stmt flush.

Lemma table_core : forall X w x26 x12 ms,
  ix_flush X = flush -> ILOOP X w PC_TABLE x26 x12 ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w -> is_mode (w_s w) = TABLE ->
  evt usegs (fun ms' => IPOST X (arm_TABLE ivar_ref flush w) ms' /\ PATI X (wof (arm_TABLE ivar_ref flush w))) ms.
Proof.
  intros X [s c r] x26 x12 ms EF HL XO HW HA HP HM. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & MFB).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  eapply evt_cut; [exact (table_nb14 X s c r x26 x12 ms HL XO HREGS HP MFB)|].
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & HQ1)|(r1 & EN & HR1 & HLV)].
  2:{ rewrite (arm_TABLE_leave flush _ _ EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
  destruct (nb_r1_facts c r r1 14 HREGS ltac:(rewrite Pin; exact Pin1) ltac:(lia) HR1) as (EI & EO & ER & EP & EL & RB1 & RH1 & RHV1 & RN1).
  rewrite (arm_TABLE_eq flush s c r s c r1 EN ltac:(lia) ltac:(lia)).
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HP| assumption..]).
  eapply evt_cut.
  { destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
    exact (table_fin flush X s c r1 q1 x26 ms1 EF (ILOOPh_regs X s c r r1 _ q1 ms1 HJ EI EO ER EP EL) HQ1 XO HP1 ltac:(lia) RH1 ltac:(rewrite EP; lia) ltac:(lia)). }
  intros ms2 H2. unfold tb_res. cbv zeta.
  assert (HN : table_next (mkW s c r) = if (286 <? is_nlen (tb_s s (ir_hold r1))) || (30 <? is_ndist (tb_s s (ir_hold r1))) then None
                                        else Some (mkW (tb_s2 s (ir_hold r1)) c (tb_r r1))).
  { unfold table_next. rewrite EN. reflexivity. }
  destruct ((286 <? is_nlen (tb_s s (ir_hold r1))) || (30 <? is_ndist (tb_s s (ir_hold r1)))).
  - destruct H2 as (x26' & x12' & H2). apply evt_done. split; [cbn [IPOST]; exists x26', x12'; exact H2|]. cbn [wof].
    eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..| exact Pisr| bk_keep].
  - destruct H2 as (q2 & H2 & E17 & E14 & E12 & E9 & E11 & E13 & E18 & E22).
    destruct (table_next_WINV _ _ HW HM HN) as [HW2 HM2].
    pose proof (table_next_ATY (mkW s c r) _ HA HN) as HA2.
    refine (LENLENS_CORE X _ q2 ms2 EF H2 E17 E14 E12 E9 E11 E13 E18 E22 XO HW2 HA2 _ HM2).
    eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold tb_s2; cbn [is_mode iset_mode]; unfold LENLENS, FLAGS, HCRC; lia| reflexivity..| exact Pisr| bk_keep].
Qed.

Lemma arm_TABLE_of : arm_stmt flush TABLE PC_TABLE (arm_TABLE ivar_ref flush).
Proof. intros X w x12 ms EF HL XO HW HA HP HM. exact (table_core X w _ x12 ms EF HL XO HW HA HP HM). Qed.
End Table.
End Z_infl_a_table.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_a_codelens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_a_codelens.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_itab_kit.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_t_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_lit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_term OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_type OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_dict OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_check OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_dictid OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_head OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_copy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_stored OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_match OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_distext OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_lenext OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_len OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms_have.Z_infl_a_table OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_lenlens OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.
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
