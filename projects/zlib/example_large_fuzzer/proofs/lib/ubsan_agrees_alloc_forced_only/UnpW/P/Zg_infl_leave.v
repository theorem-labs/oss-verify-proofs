(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Zg_infl_pure Z_adler32 Zh_kit Zg_infl_iface Z_infl_leave.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface ZChkAdl AdlerModel InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib RefInflateArms RefInflateSafeS2 RefInflateSafeOK3 RefInflate_runA. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma iout_slice_bytes : forall m L rest0 c put a k, iout m L rest0 c put -> 0 <= a -> 0 <= k -> a + k <= put -> put <= Z.of_nat (length rest0) ->
  bytes_at psegs m (il_NO L + a) (map (Z_to_bv 8) (arr_slice (ic_outbuf c) a k)).
Proof.
  intros m L rest0 c put a k H Ha Hk Hak Hp.
  pose proof (iout_prefix_bytes m L rest0 c put H ltac:(lia)) as HB.
  rewrite <- (av8_sub (ic_outbuf c) put a k) by lia.
  rewrite <- (firstn_skipn (Z.to_nat a) (av8 (ic_outbuf c) put)) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn, av8_length, Nat.min_l in HB by lia.
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn _ _)) in HB. apply bytes_at_app in HB. destruct HB as [HB _].
  replace (il_NO L + a) with (il_NO L + Z.of_nat (Z.to_nat a)) by lia. exact HB.
Qed.

Lemma bZ_map8 : forall l, (forall k, (k < length l)%nat -> 0 <= nth k l 0 < 256) -> bZ (map (Z_to_bv 8) l) = l.
Proof.
  intros l. induction l as [|x l IH]; intros H; [reflexivity|].
  cbn [map bZ]. unfold bZ in IH |- *. cbn [map]. f_equal.
  - apply bv8_small. apply (H 0%nat). cbn. lia.
  - apply IH. intros k Hk. apply (H (S k)). cbn. lia.
Qed.

Lemma bZ_slice : forall a so n, 0 <= so -> 0 <= n -> (forall i, so <= i < so + n -> 0 <= arr_get a i < 256) ->
  bZ (map (Z_to_bv 8) (arr_slice a so n)) = arr_slice a so n.
Proof.
  intros a so n Hso Hn Hb. apply bZ_map8. intros k Hk. unfold arr_slice in *. rewrite arr_slice_nat_length in Hk.
  rewrite arr_slice_nat_nth by exact Hk. apply Hb. lia.
Qed.

Section Leave.
Hypothesis ADLER32 : adler32_stmt.

Lemma adler32_callG : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (adler B len lo : Z) (d : list byte),
  0 <= adler < 2^64 -> 0 < B -> B + Z.of_nat (length d) < 2^63 -> Z.of_nat (length d) < 2^32 ->
  bytes_at psegs m B d -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp < 2^63 -> (B + Z.of_nat (length d) <= lo \/ bv_unsigned sp <= B) ->
  len = Z.of_nat (length d) ->
  evt psegs (adler32_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (adler32_z_spec adler B d) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz B) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_ADLER32) fc None m (seg_rom psegs)).
Proof. intros. subst. apply ADLER32; assumption. Qed.

Lemma leave_preG : forall X w ms,
  ILEAVE X w ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w ->
  ir_in (w_r w) = arr_len (ic_input (w_c w)) ->
  evt psegs (fun ms' => exists x15, ILVT (ix_W X) X (mkW (s_rest (w_s w) (w_r w)) (c_rest (w_c w) (w_r w)) (w_r w)) PC_LV_WIN
                  (wz (il_S (ix_L X))) (wz (is_wsize (w_s w))) x15 (wz (il_NO (ix_L X) + ir_put (w_r w))) (wz (il_As (ix_L X))) ms') ms.
Proof.
  intros X [s c r] ms HL XO HW HA HP EIN. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & (POB & POW & POL & PNP & PHW)). cbn [w_s w_c w_r] in *.
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (RWS : 0 <= is_wsize s <= 32768).
  { destruct HCORE as (_ & _ & C3 & _ & _ & _ & C7 & _). destruct (Z.eq_dec (is_wsize s) 0) as [E|NE]; [lia|].
    rewrite (C3 NE), Pwb. change (shl32 1 15) with 32768. lia. }
  destruct HL as (x1 & x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x21 & x27 & x28 & x29 & x30 & x31 & m & -> & (retw & jf0 & jf1 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  unfold PC_LEAVE. do 7 zs. rewrite ?sx32_wz by lia.
  itr_groups MUf WMf.
  apply evt_done. exists x15. unfold s_rest, c_rest. eapply ILVT_intro; ired; [ireg .. |].
  { apply IMEMLW_of_IMEML. apply IMEML_intro; inorm.
       - exists retw, jf0, jf1, jf. exact FRM.
       - exact STK.
       - eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm. close_cells ZS.
       - constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
       - exact IN.
       - unfold iout. rewrite (iout_bytes_ext _ _ c) by reflexivity. exact OUT.
       - eassumption.
       - exact MU.
       - exact WM. }
Qed.
End Leave.
