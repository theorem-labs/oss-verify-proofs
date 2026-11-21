(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_updwin_pure Z_updwin Z_infl_leave Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefUpdWin1 RefInflate_runA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition PC_LV_CALL : Z := 0x219b8.
Definition PC_LV_BACK : Z := 0x219c8.
Definition lv_condv (flush mode wsize o : Z) : bool :=
  negb (wsize =? 0) || (negb (o =? 0) && (mode <? BAD) && ((mode <? CHECK) || negb (flush =? Z_FINISH))).
Definition WFACTS (s : inflate_state) : Prop :=
  is_wbits s = 15 /\ (is_wsize s <> 0 -> is_wsize s = 32768) /\ 0 <= uw_wnext0 s < 32768 /\ 0 <= uw_whave0 s <= 32768
  /\ (is_window_blk s <> None -> arr_len (is_window s) = 32768).
Definition ILVM (W : list ivl) (X : ictx) (w : iw) (pc : Z) (a0v : word) (Pm : mem -> Prop) : machine_state -> Prop :=
  fun ms => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18c x20 x21 x22 x23 x25 t3 t4 t5 t6 fj m,
    ms = MS (mkR (wz PC_UW_RET) (wz (bv_unsigned (ix_sp X) + -320)) (ix_gp X) (ix_tp X) t0 t1 t2
                 (wz (il_NO (ix_L X) + ir_put (w_r w))) (wz (ir_out (w_r w) - ir_left (w_r w))) a0v a1 a2 a3 a4 a5 a6 a7
                 (wz 1) (wz (il_As (ix_L X))) (wz (ir_out (w_r w) - ir_left (w_r w))) x20 x21 (wz (ir_have (w_r w))) x23 x22 x25 (wz (ir_ret (w_r w))) t3 t4 t5 t6)
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom usegs)
    /\ rw_cells usegs m (bv_unsigned (ix_sp X) + -320)
          [CB 8 fj; C8 x20; C8 (wz (ir_out (w_r w) - ir_left (w_r w))); C8 x18c; C8 (wz (il_S (ix_L X)));
           C8 (wz (il_NO (ix_L X) + ir_put (w_r w))); C8 (wz (il_As (ix_L X))); C8 (wz PC_LV_BACK)]
    /\ iframeL X (w_r w) m
    /\ stk usegs m (ix_lo X) (bv_unsigned (ix_sp X) + -320)
    /\ IREP m (ix_L X) (w_s w) (w_c w) /\ iin m X /\ iout m (ix_L X) (ix_rest0 X) (w_c w) (ir_put (w_r w))
    /\ mem_inv usegs m /\ munch W (ix_m0 X) m /\ wmono usegs (ix_m0 X) m /\ Pm m.
Lemma leave_call_to_malloc : forall X w x10 x12 x14 ms,
  ILVT (ix_W X) X w PC_LV_CALL x10 x12 (wz (il_S (ix_L X))) x14 (wz (ir_out (w_r w) - ir_left (w_r w))) ms ->
  ix_ok X -> is_window_blk (w_s w) = None -> is_wbits (w_s w) = 15 -> ic_next_out (w_c w) = ir_put (w_r w) ->
  0 <= ir_put (w_r w) -> ir_put (w_r w) <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (ILVM (ix_W X) X w PC_MALLOC (wz 32768) (fun _ => True)) ms.
Proof.
  intros X [s c r] x10 x12 x14 ms HL XO HB Hwb ENO RP RPL. cbn [w_s w_c w_r] in *.
  destruct HL as (x1 & x5 & x6 & x7 & x15 & x16 & x17 & x18 & x20 & x21 & x22 & x23 & x25 & x28 & x29 & x30 & x31 & m & -> & (retw & j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  unfold iout in OUT.
  open_IST ST. pose proof ZS as ZS0. open_izs ZS.
  assert (E256 : bv_unsigned (wz (bv_unsigned (ix_sp X) + -256)) = bv_unsigned (ix_sp X) + -256) by (apply unsigned_lit; lia).
  unfold PC_LV_CALL. do 4 zs. rewrite ENO.
  eapply evt_cut.
  { eapply (updwin_to_malloc (ix_L X) s c (ir_out r - ir_left r) (il_NO (ix_L X) + ir_put r) (ix_lo X)); rewrite ?E256;
      [ exact STK | exact ZS0 | exact GA | exact HB | exact Hwb | lia | lia | lia | lia | lia | lia | exact MI | lia | exact XAl ]. }
  intros ms' PO. unfold uw_at_malloc in PO.
  destruct PO as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & fj & -> & FRU & STK' & MUc & WMc & MIc).
  rewrite E256 in *. replace (bv_unsigned (ix_sp X) + -256 + -64) with (bv_unsigned (ix_sp X) + -320) in * by lia.
  clear STK ZS Gwin.
  itr_groups MUc WMc.
  transport_after_call usegs m m' MUc WMc.
  apply evt_done. unfold ILVM. cbn [w_s w_c w_r]. do 22 eexists. split; [reflexivity|].
  split; [exact FRU|]. split; [eexists _, j0, jf; unfold iframe_cells; exact FRM|]. split; [exact STK'|].
  split; [split; [exact ZS0| constructor; try assumption; unfold iwin; rewrite HB; exact I]|].
  split; [unfold iin; exact IN|]. split; [unfold iout; exact OUT|]. split; [exact MIc|]. split; [unfold ix_W; exact MU|]. split; [exact WM| exact I].
Qed.
Lemma leave_from_malloc_null : forall X w Pm ms,
  ILVM (ix_W X) X w PC_UW_RET (wz 0) Pm ms ->
  ix_ok X -> is_window_blk (w_s w) = None -> 0 <= ir_put (w_r w) <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (IFIN (ix_W X) X Z_MEM_ERROR (mkW (iset_mode (w_s w) MEM) (w_c w) (w_r w))) ms.
Proof.
  intros X [s c r] Pm ms HL XO HB RP. cbn [w_s w_c w_r] in *.
  eapply evt_cut; [| intros ms1 H1; exact (epilogue_gen _ X _ _ ms1 H1 XO)].
  destruct HL as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x18c & x20 & x21 & x22 & x23 & x25 & t3 & t4 & t5 & t6 & fj & m & -> & FRU & (retw & j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM & _).
  unfold iframe_cells in FRM; unfold iin in IN; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  unfold iout in OUT.
  open_IST ST.
  assert (E256 : bv_unsigned (wz (bv_unsigned (ix_sp X) + -256)) = bv_unsigned (ix_sp X) + -256) by (apply unsigned_lit; lia).
  replace (wz (bv_unsigned (ix_sp X) + -320)) with (wz (bv_unsigned (wz (bv_unsigned (ix_sp X) + -256)) + -64)) by (rewrite E256; f_equal; lia).
  eapply evt_cut.
  { eapply (updwin_ret_null fj (ix_L X) s (ir_out r - ir_left r) (il_NO (ix_L X) + ir_put r) (ix_lo X) (wz PC_LV_BACK) (wz (bv_unsigned (ix_sp X) + -256))); rewrite ?E256;
      [ replace (bv_unsigned (ix_sp X) + -256 + -64) with (bv_unsigned (ix_sp X) + -320) by lia; exact FRU
      | replace (bv_unsigned (ix_sp X) + -256 + -64) with (bv_unsigned (ix_sp X) + -320) by lia; exact STK
      | exact GA | exact HB | lia | lia | lia | lia | lia | exact MI ]. }
  intros ms' PO. unfold updwin_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STK' & GA' & GW').
  rewrite E256 in *.
  clear GA Gwin STK FRU.
  itr_groups MUc WMc.
  transport_after_call usegs m m' MUc WMc.
  replace (ret_pc (wz PC_LV_BACK)) with (wz PC_LV_BACK) by (symmetry; apply ret_pc_even; [unfold PC_LV_BACK; lia| reflexivity]).
  open_isA GA'. unfold PC_LV_BACK.
  pose proof (munch_refl [(il_As (ix_L X), il_As (ix_L X) + 168)] m') as MUf. pose proof (wmono_refl usegs m') as WMf.
  do 2 zs. zs. br_false. do 4 zs.
  itr_groups MUf WMf.
  apply evt_done. eapply IRETW_intro; try reflexivity.
  unfold IMEMLW. cbn [w_s w_c w_r].
  split; [eexists _, j0, jf; unfold iframe_cells; exact FRM|]. split; [exact STK'|].
  split. { split; [exact ZS|]. constructor; ired; [unfold isA, isA_cells; ired; close_cells GA'| exact GT| exact Gl| exact Gw| exact Gc| unfold iwin; ired; rewrite HB; exact I| exact ARRS| exact LAY]. }
  split; [unfold iin; exact IN|]. split; [unfold iout; exact OUT|]. split; [eassumption|]. split; [unfold ix_W; exact MU| exact WM].
Qed.
Lemma il_setw_id : forall L, il_setw L (il_Aw L) = L.
Proof. intros [a b c d e]. reflexivity. Qed.
