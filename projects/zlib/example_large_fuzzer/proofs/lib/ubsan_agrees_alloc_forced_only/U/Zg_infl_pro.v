From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_infl_defs Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface InflateState InflateArms Inflate RefInflate_runA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma inflate_prologueG : forall (X : ictx) (s : inflate_state) (zc : ZCall)
         (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
  ix_m0 X = m -> ix_ok X ->
  izs m (ix_L X) (icall_of_zcall zc) -> IST m (ix_L X) s -> iin m X -> iout m (ix_L X) (ix_rest0 X) (icall_of_zcall zc) 0 ->
  stk usegs m (ix_lo X) (bv_unsigned (ix_sp X)) -> mem_inv usegs m ->
  (is_window_blk s <> None -> ix_hasw X = true) ->
  HEAD <= is_mode s <= SYNC -> 0 <= is_bits s < 64 -> 0 <= is_hold s < 2^64 ->
  0 <= zlength (zc_input zc) < 2^31 -> 0 <= zc_avail_out zc < 2^31 -> 0 <= ix_flush X <= 4 ->
  0 < il_NI (ix_L X) < 2^63 -> 0 < il_NO (ix_L X) < 2^63 ->
  evt usegs (fun ms' => exists x26 x12, ILOOP X (W0 s zc) PC_DISPATCH x26 x12 ms')
      (MS (mkR (ix_ra X) (ix_sp X) (ix_gp X) (ix_tp X) t0 t1 t2 (ix_s0 X) (ix_s1 X) (wz (il_S (ix_L X))) (wz (ix_flush X)) a2 a3 a4 a5 a6 a7
               (ix_s2 X) (ix_s3 X) (ix_s4 X) (ix_s5 X) (ix_s6 X) (ix_s7 X) (ix_s8 X) (ix_s9 X) (ix_s10 X) (ix_s11 X) t3 t4 t5 t6)
          (ix_F X) (wz Z_INFLATE) (ix_fc X) None m (seg_rom usegs)).
Proof.
  intros X s zc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m EM0 XO ZS ST IN OUT STK MI HWIN RM RB RH RAI RAO RF RNI RNO.
  unfold Z_INFLATE, HEAD, SYNC in *. ix_open XO.
  pose proof (munch_refl (ix_W X) m) as MU. unfold ix_W in MU. pose proof (wmono_refl usegs m) as WM.
  unfold iin in IN. unfold iout in OUT.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) (icall_of_zcall zc) 0 ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_izs ZS. cbn [icall_of_zcall ic_next_in ic_avail_in ic_total_in ic_next_out ic_avail_out ic_total_out ic_msg ic_adler] in ZS.
  open_IST ST. open_isA GA.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  carve_frame 256%nat STK.
  do 17 zs. br_true.
  zs. al8 (il_S (ix_L X)). gT.
  do 2 zs. br_true. do 2 zs. br_true. do 2 zs. br_true.
  zs. al8 (il_As (ix_L X)). gT.
  do 2 zs. br_true.
  do 6 zs. rewrite (swrap32_sub _ 16180) by (try reflexivity; lia).
  br_true. do 2 zs. br_true. do 2 zs. br_true.
  do 6 zs.
  br_cases KT.
  -
    do 35 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _.
    assert (ES : s_entry s = s) by (unfold s_entry; replace (is_mode s =? TYPE) with false by (symmetry; apply Z.eqb_neq; unfold TYPE; lia); reflexivity).
    unfold W0. rewrite ES. cbn [w_s].
    eapply ILOOP_intro; ired; [ireg .. |].
    apply IMEM_intro; ired.
    + eexists _, _. unfold iframe_cells. ired. exact FR.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app icall_of_zcall]. ired. exact ZS.
    + constructor; [unfold isA, isA_cells; exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + rewrite EM0. exact MU.
    + rewrite EM0. exact WM.
  -
    do 2 zs. do 35 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _.
    assert (ES : s_entry s = iset_mode s TYPEDO) by (unfold s_entry; replace (is_mode s =? TYPE) with true by (symmetry; apply Z.eqb_eq; unfold TYPE; lia); reflexivity).
    unfold W0. rewrite ES. cbn [w_s].
    eapply ILOOP_intro; ired; [ireg .. |].
    apply IMEM_intro; ired.
    + eexists _, _. unfold iframe_cells. ired. exact FR.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app icall_of_zcall]. ired. exact ZS.
    + constructor; ired; [unfold isA, isA_cells; ired; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + rewrite EM0. exact MU.
    + rewrite EM0. exact WM.
Qed.
