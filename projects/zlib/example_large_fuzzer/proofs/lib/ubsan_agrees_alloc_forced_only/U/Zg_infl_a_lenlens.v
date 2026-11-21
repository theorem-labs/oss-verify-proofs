(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_ukit Z_infl_iface Z_infl_c_pure Z_infl_c_tab Z_infl_t_iface Zg_infl_t_iface Zg_infl_c_kit Z_itab_kit Zg_infl_a_lenlens1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate Inftrees ItableModel RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_LENLENS1 RefInflateA_LENLENS2 RefInflateSafeOK RefInflateSafeOK2 RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.
Definition PC_LL2_B : Z := 0x1fba4.
Definition PC_LL2_X : Z := 0x1fbe4.
Definition PC_LL_CALL : Z := 0x1fbec.
Definition PC_LL_RET : Z := 0x1fc20.
Definition HC (X : ictx) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
  /\ h24 q = wz (ir_have r) /\ h25 q = wz (il_NI (ix_L X) + ir_next r).
Definition L2B (X : ictx) (r : iregs) (i : Z) (q : iscrh) : Prop :=
  h10 q = wz Z_ORDER /\ h11 q = wz (2 * i) /\ h12 q = wz (Z_ORDER + 2 * i) /\ HC X r q.
Lemma ll2_pre : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LL2 q ms -> LL2Q X s r q -> 0 <= is_have s <= 19 ->
  evt usegs (fun ms' => exists q',
     if is_have s <? 19 then ILOOPh X (mkW s c r) PC_LL2_B q' ms' /\ L2B X r (is_have s) q'
     else ILOOPh X (mkW s c r) PC_LL_CALL q' ms' /\ HC X r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ RH.
  unfold LL2Q in HQ. hred_in HQ. destruct HQ as (E17 & E14 & E12 & E10 & E9 & E18 & E22).
  destruct HL as (m & -> & HMEM). hred. subst x17 x14 x12 x10 x9 x18 x22.
  unfold PC_LL2, Z_ORDER.
  do 4 zs. br_cases K.
  - replace (is_have s <? 19) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; try reflexivity; exact HMEM|]. unfold HC. hred. repeat split; reflexivity.
  - replace (is_have s <? 19) with true by (symmetry; apply Z.ltb_lt; lia).
    do 3 zs.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; try reflexivity; exact HMEM|].
    unfold L2B, HC. hred. unfold Z_ORDER. repeat split; ireg.
Qed.
Local Ltac close_k j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [exact GA| exact GT| unfold ilens, u16arr; inorm; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Lemma ll2_body : forall X s c r i q ms,
  ILOOPh X (mkW s c r) PC_LL2_B q ms -> L2B X r i q ->
  ix_ok X -> PATG X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i < 19 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q',
     if i + 1 =? 19
     then ILOOPh X (mkW (iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)) c r) PC_LL2_X q' ms' /\ HC X r q'
     else ILOOPh X (mkW (iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)) c r) PC_LL2_B q' ms' /\ L2B X r (i + 1) q') ms.
Proof.
  intros X s c r i [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP LL Ri RPUT.
  unfold L2B, HC in HQ. hred_in HQ. destruct HQ as (E10 & E11 & E12 & E9 & E18 & E22 & E24 & E25).
  iarm_openh HL. subst x10 x11 x12 x9 x18 x22 x24 x25.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL2_B, Z_ORDER.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST.
  pose proof (munch_refl [(il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  pose proof (order_lt19 i ltac:(lia)) as ROR. set (od := arr_get order_a i) in *.
  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  pose proof (order_rd m i (wa (Z_ORDER + 2 * i)) MI ltac:(lia) eq_refl) as RD. fold od in RD. unfold Z_ORDER in RD.
  zs. change (Z.lxor 75196 18446744073709551615) with 18446744073709476419. gT.
  zs. rewrite (zx16_small od) by lia. clear RD.
  zs. replace (od ≪ 1) with (2 * od) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zs. zstep. rewrite (zb_lxor_ones (il_As (ix_L X) + 168)) by lia. br_true.
  do 4 zs.
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) od 0 ltac:(reflexivity).
  do 2 zs. itr_groups MUf WMf.
  destruct (Z.eqb_spec (i + 1) 19) as [E|NE].
  - replace (2 * i + 2) with 38 by lia. zstep. br_false.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; try reflexivity| unfold HC; hred; repeat split; reflexivity].
    close_k j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  - zstep. br_true.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; try reflexivity|].
    + close_k j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + unfold L2B, HC. hred. unfold Z_ORDER. repeat split; ireg.
Qed.
Lemma zlens_19 : forall n a, zlens n a 19 = a.
Proof. intros [|n] a; reflexivity. Qed.
Lemma ll2_loop : forall n X s c r i q ms,
  ILOOPh X (mkW s c r) PC_LL2_B q ms -> L2B X r i q ->
  ix_ok X -> PATG X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i < 19 -> 19 - i <= Z.of_nat n ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (iset_lens s (zlens n (is_lens s) i)) c r) PC_LL2_X q' ms' /\ HC X r q') ms.
Proof.
  induction n as [|n IH]; intros X s c r i q ms HL HQ XO HP LL Ri Rn RPUT; [cbn [Z.of_nat] in Rn; lia|].
  cbn [zlens]. replace (i <? 19) with true by (symmetry; apply Z.ltb_lt; lia).
  eapply evt_cut; [exact (ll2_body X s c r i q ms HL HQ XO HP LL Ri RPUT)|].
  intros ms1 (q1 & H1).
  destruct (Z.eqb_spec (i + 1) 19) as [E|NE].
  - rewrite E, zlens_19. apply evt_done. exists q1. exact H1.
  - destruct H1 as (H1 & HQ1).
    refine (IH X (iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)) c r (i + 1) q1 ms1 H1 HQ1 XO _ _ _ _ RPUT).
    + exact HP.
    + cbn [is_lens iset_lens]. rewrite arr_len_set. exact LL.
    + lia.
    + rewrite Nat2Z.inj_succ in Rn. lia.
Qed.
Local Ltac close_kA j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Lemma ll2_exit : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LL2_X q ms -> HC X r q -> ix_ok X -> PATG X (mkW s c r) ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (iset_have s 19) c r) PC_LL_CALL q' ms' /\ HC X r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP RPUT.
  unfold HC in HQ. hred_in HQ. destruct HQ as (E9 & E18 & E22 & E24 & E25).
  iarm_openh HL. subst x9 x18 x22 x24 x25.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL2_X.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  zs. zs. itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; try reflexivity| unfold HC; hred; repeat split; reflexivity].
  close_kA j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.
Lemma ll2_walk : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LL2 q ms -> LL2Q X s r q ->
  ix_ok X -> PATG X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= is_have s <= 19 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (ll2 19 s) c r) PC_LL_CALL q' ms' /\ HC X r q') ms.
Proof.
  intros X s c r q ms HL HQ XO HP LL RH RPUT.
  eapply evt_cut; [exact (ll2_pre X s c r q ms HL HQ RH)|]. intros ms1 (q1 & H1).
  destruct (Z.ltb_spec (is_have s) 19) as [LT|GE].
  - destruct H1 as (H1 & HQ1).
    rewrite (ll2_zlens 19 s) by (cbn; lia).
    eapply evt_cut; [exact (ll2_loop 19 X s c r (is_have s) q1 ms1 H1 HQ1 XO HP LL ltac:(lia) ltac:(cbn; lia) RPUT)|].
    intros ms2 (q2 & H2 & HQ2).
    exact (ll2_exit X _ c r q2 ms2 H2 HQ2 XO HP RPUT).
  - rewrite ll2_stop by lia. apply evt_done. exists q1. exact H1.
Qed.
Definition ILOOPc (X : ictx) (w : iw) (pc : Z) (x1 : word) (q : iscrh) : machine_state -> Prop :=
  fun ms => exists m,
    ms = MS (mkR x1 (wz (bv_unsigned (ix_sp X) + -256)) (ix_gp X) (ix_tp X) (h5 q) (h6 q) (h7 q) (wz (il_As (ix_L X))) (h9 q) (h10 q) (h11 q) (h12 q) (h13 q) (h14 q) (h15 q) (h16 q) (h17 q) (wz (il_S (ix_L X))) (h18 q) (h19 q) (h20 q) (h21 q) (h24 q) (h23 q) (h22 q) (h25 q) (h26 q) (h28 q) (h29 q) (h30 q) (h31 q))
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom usegs)
    /\ IMEM X w m.
Lemma ILOOPc_intro : forall X w pc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (bv_unsigned (ix_sp X) + -256) -> x3 = ix_gp X -> x4 = ix_tp X ->
  x8 = wz (il_S (ix_L X)) -> x27 = wz (il_As (ix_L X)) -> F = ix_F X -> fc = ix_fc X ->
  IMEM X w m ->
  ILOOPc X w pc x1 (mkSH x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31)
         (MS (mkR x1 x2 x3 x4 x5 x6 x7 x27 x9 x10 x11 x12 x13 x14 x15 x16 x17 x8 x18 x19 x20 x21 x24 x23 x22 x25 x26 x28 x29 x30 x31)
             F (wz pc) fc None m (seg_rom usegs)).
Proof. intros. subst. unfold ILOOPc. eexists. split; [reflexivity| assumption]. Qed.
Local Ltac close_A j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; unfold iframe_cells; inorm; close_cells FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Definition HCC (X : ictx) (r : iregs) (q : iscrh) : Prop := HC X r q /\ h10 q = wz (-2).
Lemma ll_after : forall X s3 c r x1 q ms ret,
  ILOOPc X (mkW s3 c r) PC_LL_RET x1 q ms -> h10 q = wz (ret mod 2 ^ 64) -> HC X r q -> (ret = 0 \/ ret = 1 \/ ret = -1) -> ix_ok X ->
  (is_window_blk s3 <> None -> ix_hasw X = true) -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 ->
  arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' =>
    if negb (ret =? 0)
    then exists x26 x12, ILOOP X (mkW (iset_mode s3 BAD) (icset_msg c MSG_invalid_code_lengths_set) (irset_ret r ret)) PC_DISPATCH x26 x12 ms'
    else exists q', ILOOPh X (mkW (iset_mode (iset_have s3 0) CODELENS) c (irset_ret r ret)) PC_CODELENS_E q' ms' /\ HCC X r q') ms.
Proof.
  intros X s3 c r x1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms ret HL E10 HQ RRET XO Pwin Pin Pin1 Pout RPUT.
  unfold HC in HQ. hred_in HQ. hred_in E10. destruct HQ as (E9 & E18 & E22 & E24 & E25).
  destruct HL as (m & -> & (j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU. hred. cbn [w_s w_c w_r] in *.
  subst x10 x9 x18 x22 x24 x25.
  ix_open XO. unfold PC_LL_RET.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  assert (RM : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  zs. br_cases K.
  -
    assert (R0 : ret = 0) by (destruct RRET as [R|[R|R]]; rewrite R in K; [exact R| |]; exfalso; revert K; vm_compute; discriminate).
    clear RRET K RM. subst ret. cbn [Z.eqb negb].
    do 6 zs. itr_groups MUf WMf.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; try reflexivity| unfold HCC, HC; hred; repeat split; reflexivity].
    close_A j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  -
    assert (R1 : (ret =? 0) = false) by (apply Z.eqb_neq; intros R; rewrite R in K; apply K; reflexivity). rewrite R1. cbn [negb].
    clear RRET K.
    do 4 zs. do 7 zs. itr_groups MUf WMf.
    apply evt_done. do 2 eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_A j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.
Section LLcall.
Variable flush : Z.
Hypothesis CODELENS_CORE : codelens_core_stmt flush.
Hypothesis ITABLE : inflate_table_stmt.
Lemma ll_call : forall X s c r q ms ret tbl nxt lb wk,
  ILOOPh X (mkW s c r) PC_LL_CALL q ms -> HC X r q -> ix_ok X -> PATG X (mkW s c r) ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  inflate_table CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s) = (ret, tbl, nxt, lb, wk) ->
  it_safe CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s) = true ->
  ATY s -> (forall i, 0 <= i < 19 -> arr_get (is_lens s) i <= 15) ->
  evt usegs (fun ms' =>
    if negb (ret =? 0)
    then exists x26 x12, ILOOP X (mkW (iset_mode (ll_tab s tbl nxt lb wk) BAD) (icset_msg c MSG_invalid_code_lengths_set) (irset_ret r ret)) PC_DISPATCH x26 x12 ms'
    else exists q', ILOOPh X (mkW (ll_s2 (ll_tab s tbl nxt lb wk)) c (irset_ret r ret)) PC_CODELENS_E q' ms' /\ HCC X r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms ret tbl nxt lb wk HL HQ XO HP RPUT EIT SAFE HA HL15.
  unfold HC in HQ. hred_in HQ. destruct HQ as (E9 & E18 & E22 & E24 & E25).
  iarm_openh HL. subst x9 x18 x22 x24 x25.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL_CALL.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  do 13 zs. itr_groups MUf WMf. clear MUf WMf.
  set (spre := iset_distcode (iset_lencode (iset_next (iset_lenbits s 7) 0) (CDyn 0)) (CDyn 0)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
  assert (ST' : IST m1 (ix_L X) spre);
  [ subst spre; constructor; inorm;
    [ unfold isA, isA_cells; inorm; unfold cp_addr; close_cells GA | exact GT | exact Gl | exact Gw | exact Gc | exact Gwin
    | unfold iarrs in *; inorm; exact ARRS | exact LAY ]
  | clear GA GT Gl Gw Gc Gwin ] end.
  pose proof (inflate_table_ret _ _ _ _ _ _ _ _ _ _ _ _ _ EIT) as RRET.
  eapply evt_cut.
  { eapply (ITABLE (ix_L X) spre CODES false 0 19 (ix_lo X));
      [ exact ST' | eassumption | rewrite unsigned_lit by lia; exact STK | rewrite unsigned_lit by lia; unfold Z_ITABLE_STACK; lia | lia
      | intros NE; subst spre; cbn in NE; pose proof (xo_win _ XO (Pwin NE)); lia
      | lia | lia | lia | subst spre; cbn; lia | subst spre; cbn; lia
      | subst spre; cbn [it_bits_get is_lens is_codes is_next is_work is_lenbits iset_distcode iset_lencode iset_next iset_lenbits]; exact SAFE
      | exact HA
      | subst spre; cbn [is_lens iset_distcode iset_lencode iset_next iset_lenbits]; intros i Hi; rewrite Z.add_0_l; exact (HL15 i Hi)
      | cbn [it_codes_ok]; first [exact I | lia]
      | reflexivity | f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STKc & EA0 & STc).
  rewrite unsigned_lit in MUc, STKc by lia.
  assert (ER : it_result CODES false 0 19 spre = (ret, ll_tab s tbl nxt lb wk)).
  { unfold it_result. subst spre. cbn [it_bits_get it_bits_set is_lens is_codes is_next is_work is_lenbits iset_distcode iset_lencode iset_next iset_lenbits].
    rewrite EIT.
    unfold ll_tab, it_bits_set. cbv [iset_work iset_lenbits iset_next iset_lencode iset_codes
      is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk
      is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next
      is_lens is_work is_codes is_sane is_back is_was is_self_blk]. reflexivity. }
  rewrite ER in EA0, STc. cbn [fst snd] in EA0, STc. subst a0'. clear ER ST' spre.
  lazymatch type of WMc with wmono _ ?ma _ => itr_groups MUc WMc; transport_after_call usegs ma m' MUc WMc end. clear MUc WMc MI ARRS LAY.
  replace (ret_pc (wz 130080)) with (wz 130080) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  unfold ll_s2.
  eapply (ll_after X (ll_tab s tbl nxt lb wk) c r _ _ _ ret); [ | | | exact RRET | exact XO | exact Pwin | exact Pin | exact Pin1 | exact Pout | exact RPUT].
  { eapply ILOOPc_intro; ired; [ireg .. |].
    apply IMEM_intro; [ exists j0, jf; exact FRM | exact STKc | exact ZS | exact STc | exact IN | exact OUT | exact MIc | exact MU | exact WM ]. }
  { hred. reflexivity. }
  { unfold HC. hred. repeat split; reflexivity. }
Qed.
Lemma lenlens_core : lenlens_core_stmt flush.
Proof.
  intros X [s c r] q ms EF HL E17 E14 E12 E9 E11 E13 E18 E22 XO HW HA HP HM. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _ & Rin & _).
  assert (LL : arr_len (is_lens s) = 320) by (destruct HCORE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  assert (HIN1 : arr_len (ic_input c) < 2^31) by (rewrite Pin; exact Pin1).
  pose proof (DREGSg_of_REGS c r HREGS HIN1) as DR.
  rewrite arm_LENLENS_eq.
  eapply evt_cut; [exact (ll_entry X s c r q ms HL E17 E14 E12 E9 E18 E22 Hh (proj2 Hnc))|]. intros ms1 (q1 & H1 & HQ1).
  eapply evt_cut; [exact (ll1_loop 19 X s c r q1 ms1 H1 HQ1 XO DR Rin HP HM LL Hh (proj2 Hnc) ltac:(cbn; lia) ltac:(lia))|]. intros ms2 H2.
  pose proof (lenlens_facts s c r HW HA HM) as [_ F].
  pose proof (WINV_lenlens_okb s c r HW HA HM) as OKB. unfold lenlens_okb in OKB. cbn [w_s] in OKB.
  pose proof (lenlens_next_WINV s c r HW HA HM) as NXW. unfold lenlens_next in NXW.
  destruct (lenlens_while1 19 (mkW s c r)) as [[] [s1 c1 r1] | w' | rc w']; cbn [LL1POST w_s w_r] in H2.
  2:{ apply evt_done. cbn [IPOST wof]. exact H2. }
  2:{ destruct H2. }
  destruct H2 as ((q2 & HL2 & HQ2) & HP1 & Hh1 & HM1).
  destruct F as (-> & lens19 & EL2 & HL19 & HLs19 & HT19 & HC1 & HR1 & HCm1 & Hb1 & Hnl1 & Hnd1 & HWF1 & HWB1 & HA1).
  apply andb_prop in OKB. destruct OKB as [_ OKB]. apply ll_call_ok_sound in OKB. destruct OKB as (CL15 & SAFE & _).
  assert (LL1 : arr_len (is_lens s1) = 320) by (destruct HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  pose proof HR1 as (Rn1 & Rh1 & Rnh1 & Rp1 & Rl1 & Rpl1 & _).
  pose proof HP1 as (_ & _ & _ & _ & _ & Pwin1 & Pin' & _ & Pout' & _ & Pisr1 & _). cbn [w_s w_c w_r] in *.
  assert (RPUT1 : 0 <= ir_put r1 <= Z.of_nat (length (ix_rest0 X))) by (rewrite <- Pout; lia).
  eapply evt_cut; [exact (ll2_walk X s1 c r1 q2 ms2 HL2 HQ2 XO HP1 LL1 Hh1 RPUT1)|]. intros ms3 (q3 & H3 & HQ3).
  unfold ll_fin. rewrite EL2 in H3, CL15, SAFE, NXW |- *. cbv zeta in NXW.
  cbn [is_lens is_codes is_work iset_have iset_lens] in CL15, SAFE, NXW |- *.
  destruct (inflate_table CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)) as [[[[ret tbl] nxt] lb] wk] eqn:EIT. cbv zeta.
  assert (Pf1 : is_flags s1 = 0).
  { destruct HP1 as (_ & _ & _ & Pfl1 & _). cbn [w_s w_r] in Pfl1. destruct Pfl1 as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM1 in E; discriminate E. }
  assert (HPA : PATG X (mkW (iset_have (iset_lens s1 lens19) 19) c r1)).
  { eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_have iset_lens]; rewrite HM1; unfold LENLENS, FLAGS, HCRC; lia| reflexivity..| |exact Pisr1| bk_keep].
    cbn [is_mode iset_have iset_lens]. rewrite HM1. reflexivity. }
  assert (HAA : ATY (iset_have (iset_lens s1 lens19) 19)).
  { unfold ATY. cbn [is_lens is_work is_codes iset_have iset_lens]. split; [exact HT19| destruct HA1 as [_ H]; exact H]. }
  eapply evt_cut.
  { eapply (ll_call X (iset_have (iset_lens s1 lens19) 19) c r1 q3 ms3 ret tbl nxt lb wk H3 HQ3 XO HPA RPUT1);
      cbn [is_lens is_codes is_work iset_have iset_lens]; [exact EIT | exact SAFE | exact HAA | exact CL15]. }
  intros ms4 H4.
  destruct (Z.eqb_spec ret 0) as [R0|R1]; cbn [negb] in H4 |- *.
  -
    destruct H4 as (q4 & HL4 & (E9' & E18' & E22' & E24' & E25') & E10').
    specialize (NXW _ eq_refl). destruct NXW as (HW2 & HA2 & HM2).
    refine (CODELENS_CORE X _ q4 ms4 EF HL4 _ _ _ _ _ _ XO HW2 HA2 _ HM2); cbn [w_s w_c w_r]; ired; try assumption.
    unfold ll_s2, ll_tab. eapply PATG_step; [exact HPA| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode iset_have]; unfold CODELENS, FLAGS, HCRC; lia| reflexivity..| exact Pisr1| bk_keep].
  -
    destruct H4 as (x26' & x12' & HL4).
    apply evt_done. split; [cbn [IPOST]; exists x26', x12'; exact HL4|]. cbn [wof].
    unfold ll_tab. eapply PATG_step; [exact HPA| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| reflexivity..| exact Pisr1| bk_keep].
Qed.
Lemma arm_LENLENS_of : arm_stmtg flush LENLENS PC_LENLENS (arm_LENLENS ivar_ref flush).
Proof.
  intros X [s c r] x12 ms EF HL XO HW HA HP HM.
  pose proof HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in HMF. rewrite HM in HMF. unfold MF in HMF. cbn in HMF.
  destruct HMF as (_ & _ & Hnc & _ & _ & Hh & _).
  eapply evt_cut; [exact (ll_arm_entry X s c r _ x12 ms HL ltac:(lia))|]. intros ms1 (q1 & H1 & E17 & E14 & E12 & E9 & E11 & E13 & E18 & E22).
  exact (lenlens_core X (mkW s c r) q1 ms1 EF H1 E17 E14 E12 E9 E11 E13 E18 E22 XO HW HA HP HM).
Qed.
End LLcall.
