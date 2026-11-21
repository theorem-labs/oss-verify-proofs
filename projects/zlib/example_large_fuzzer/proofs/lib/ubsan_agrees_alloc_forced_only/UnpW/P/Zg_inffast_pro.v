(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_c_pure Z_infl_c_tab Zg_infl_iface Zg_inffast_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate InflateFast InffastModel InffastCtx InffastSafe InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ff_pro_post (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (sv : ffsave) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x1 x7 x21 x25 x26 x27 m',
    ms' = FFL X s c r (ff0_of s c) PC_FF_LOOP x1 x7 x21 x25 x26 x27 m'
    /\ munch [(ff_sp X, ff_sp X + 112)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ FFM X s c sv (ff0_of s c) m'
    /\ iframe X r m' /\ stk psegs m' (ix_lo X) (ff_sp X) /\ ilens m' (ix_L X) s /\ iwork m' (ix_L X) s.

Lemma ff_prologue : forall (X : ictx) s c r (ra x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) m,
  IMEM X (mkW s c r) m -> ix_ok X -> ff_restored s c r -> ff_typed X s c r ->
  evt psegs (ff_pro_post X s c r (mkFS ra x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27) m)
    (MS (mkR ra (wz (bv_unsigned (ix_sp X) + -240)) (ix_gp X) (ix_tp X) x5 x6 x7 x8 x9 (wz (il_S (ix_L X))) (wz (ir_out r)) x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (ix_F X) (wz Z_INFFAST) (ix_fc X) None m (seg_rom psegs)).
Proof.
  intros X s c r ra x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m HMEM XO HRS HT.
  pose proof HMEM as ((jf0 & jf1 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  destruct HRS as (E1 & E2 & E3 & E4 & E5 & E6).
  destruct HT as (Pin & Pout & Rn & Rh & Rnh & Rin31 & Rp & Rl & Rpl & Rout31 & Rout & Rbeg & Bin & Bout & Bwin & Rb & Rhold
               & Rlb & Rdb & CPL & CPD & Rws & Rwh & Rwn & Rsane & Wnone & Wz & Whas).
  rewrite <- E1, <- E2, <- E3, <- E4 in *. clear E1 E2 E3 E4.
  ix_open XO. unfold Z_INFFAST.
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 Rhold)|]. apply Z.pow_le_mono_r; lia. }
  rewrite <- E5, <- E6 in *. clear E5 E6.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ic_next_out c) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT. open_izs ZS.
  pose proof (munch_refl [(bv_unsigned (ix_sp X) + -352, bv_unsigned (ix_sp X) + -352 + 112)] m) as MUf.
  pose proof (wmono_refl psegs m) as WMf.
  carve_frame 112%nat STK.
  do 14 zs. do 15 zs. do 15 zs. do 14 zs.
  rewrite !clang_mask32 by lia. rewrite <- !(zmask_ones (is_lenbits s)) by lia. rewrite <- !(zmask_ones (is_distbits s)) by lia.
  itr_groups MUf WMf.
  apply evt_done. eexists _, _, _, _, _, _, _. split.
  { eapply FFL_intro; unfold ff_sp; cbn [ffx_of x_last x_end x_beg x_lmask x_dmask ff0_of f_hold f_in f_out f_bits]; ffreg. }
  split; [exact MUf|]. split; [exact WMf|]. split; [assumption|].
  split.
  { unfold FFM, FFMg. cbn [ff0_of f_ob f_out].
    split; [unfold ff_sp, ff_frame_cells; cbn [fs_ra fs_x8 fs_x9 fs_x18 fs_x19 fs_x20 fs_x21 fs_x22 fs_x23 fs_x24 fs_x25 fs_x26 fs_x27]; exact FR|].
    split; [unfold isA, isA_cells; exact GA|].
    split; [exists padT; exact GT|].
    split; [eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; exact ZS|].
    split; [exact Gc|]. split; [exact Gwin|]. split; [unfold iin; exact IN|].
    split; [unfold iout; rewrite (iout_bytes_ext _ (icset_outbuf c (ic_outbuf c)) c) by reflexivity; exact OUT|].
    split; [assumption|]. split; [exact ARRS| exact LAY]. }
  split; [exists jf0, jf1, jf; unfold iframe_cells; exact FRM|].
  split; [unfold ff_sp; exact STK|].
  split; [exact Gl| exact Gw].
Qed.
