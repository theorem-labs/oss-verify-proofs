(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_iface Z_infl_c_defs Z_infl_c_pure Z_infl_c_tab Z_infl_a_dist1 Z_infl_a_dist Zg_infl_t_iface Zg_infl_a_lenlens1 Zg_infl_c_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate Inftrees ItableModel RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_LENLENS1 RefInflateA_LENLENS2 RefInflateSafeOK RefInflateSafeOK2 RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.

Record iscrk : Type := mkSK {
  k1 : word; k5 : word; k6 : word; k7 : word; k10 : word; k11 : word; k12 : word; k13 : word; k14 : word; k15 : word;
  k16 : word; k17 : word; k27 : word; k28 : word; k29 : word; k30 : word; k31 : word }.

Definition ILOOPk (X : ictx) (w : iw) (pc : Z) (q : iscrk) : machine_state -> Prop :=
  fun ms => exists m,
    ms = MS (mkR (k1 q) (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) (k5 q) (k6 q) (k7 q) (wz (il_As (ix_L X)))
                 (wz (ir_left (w_r w))) (k10 q) (k11 q) (k12 q) (k13 q) (k14 q) (k15 q) (k16 q) (k17 q)
                 (wz (ir_have (w_r w))) (wz (il_NO (ix_L X) + ir_put (w_r w))) (wz 16209) (wz (-2))
                 (wz (il_As (ix_L X) + 168)) (wz (ir_hold (w_r w))) (wz (ir_bits (w_r w))) (wz 75072)
                 (k27 q) (wz (il_NI (ix_L X) + ir_next (w_r w))) (k28 q) (k29 q) (k30 q) (k31 q))
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom psegs)
    /\ IMEM X w m.

Lemma ILOOPk_intro : forall X w pc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X -> x8 = wz (ir_left (w_r w)) ->
  x9 = wz (ir_have (w_r w)) ->
  x18 = wz (il_NO (ix_L X) + ir_put (w_r w)) -> x19 = wz 16209 -> x20 = wz (-2) -> x21 = wz (il_As (ix_L X) + 168) ->
  x22 = wz (ir_hold (w_r w)) -> x23 = wz (ir_bits (w_r w)) -> x24 = wz 75072 -> x25 = wz (il_As (ix_L X)) ->
  x26 = wz (il_NI (ix_L X) + ir_next (w_r w)) -> F = ix_F X -> fc = ix_fc X ->
  IMEM X w m ->
  ILOOPk X w pc (mkSK x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31)
         (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
             F (wz pc) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold ILOOPk. eexists. split; [reflexivity| assumption]. Qed.

Ltac iarm_openk HL :=
  let m := fresh "m" in let jf := fresh "jf" in
  let FRM := fresh "FRM" in let STK := fresh "STK" in let ZS := fresh "ZS" in let ST := fresh "ST" in let IN := fresh "IN" in
  let OUT := fresh "OUT" in let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in
  destruct HL as (m & -> & (jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM);
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU;
  cbn [w_s w_c w_r k1 k5 k6 k7 k10 k11 k12 k13 k14 k15 k16 k17 k27 k28 k29 k30 k31] in *.

Lemma zext32_x2 : forall x, 0 <= x < 4294967296 -> Z.land (x ≪ 32) 18446744073709551615 ≫ 31 = 2 * x.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^32) with 4294967296. change (2^64) with 18446744073709551616. change (2^31) with 2147483648. Z.div_mod_to_equations. lia.
Qed.

Lemma ll_entry : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_LENLENS_E q ms ->
  sc12 q = wz (is_ncode s) -> sc15 q = wz (is_have s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  0 <= is_have s < is_ncode s -> is_ncode s <= 19 ->
  evt psegs (fun ms' => exists q', ILOOPg X (mkW s c r) PC_LL1_H q' ms' /\ ll1_Q X s r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E12 E15 E26 RH RN.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x12 x15 x26.
  unfold PC_LENLENS_E.
  do 11 zs. rewrite zext32_x2 by lia. rewrite !land_u32_small by lia.
  apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|].
  unfold ll1_Q. cbn [sc12 sc13 sc14 sc15 sc26]. unfold Z_ORDER. repeat split; ireg.
Qed.

Lemma ll_arm_entry : forall X s c r x8 x12 ms,
  ILOOP X (mkW s c r) PC_LENLENS x8 x12 ms -> 0 <= is_have s < is_ncode s -> is_ncode s <= 19 ->
  evt psegs (fun ms' => exists q, ILOOPg X (mkW s c r) PC_LENLENS_E q ms' /\ sc12 q = wz (is_ncode s) /\ sc15 q = wz (is_have s)
                                  /\ sc26 q = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros X s c r x8 x12 ms HL RH RN.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM).
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s w_c w_r] in *.
  unfold PC_LENLENS.
  do 3 zs. br_true.
  apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|].
  cbn [sc12 sc15 sc26]. repeat split; reflexivity.
Qed.

Definition PC_LL2_B : Z := 0x1d97c.
Definition PC_LL2_X : Z := 0x1d9a0.
Definition PC_LL_CALL : Z := 0x1d9a4.

Lemma ll2_pre : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_LL2 q ms -> sc15 q = wz (is_have s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) -> 0 <= is_have s <= 19 ->
  evt psegs (fun ms' => exists k,
     if is_have s <? 19
     then ILOOPk X (mkW s c r) PC_LL2_B k ms' /\ k10 k = wz 4294967295 /\ k11 k = wz (Z_ORDER + 2 * is_have s) /\ k15 k = wz (is_have s + 1)
     else ILOOPk X (mkW s c r) PC_LL_CALL k ms') ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E15 E26 RH.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x15 x26.
  unfold PC_LL2.
  do 3 zs. br_cases K.
  - replace (is_have s <? 19) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. eexists. eapply ILOOPk_intro; ired; [ireg .. | exact HMEM].
  - replace (is_have s <? 19) with true by (symmetry; apply Z.ltb_lt; lia).
    do 7 zs.
    apply evt_done. eexists. split; [eapply ILOOPk_intro; ired; [ireg .. | exact HMEM]|].
    cbn [k10 k11 k15]. unfold Z_ORDER. repeat split; ireg.
Qed.

Local Ltac close_k jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [exact GA| exact GT| unfold ilens, u16arr; inorm; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma ll2_body : forall X s c r i k ms,
  ILOOPk X (mkW s c r) PC_LL2_B k ms -> k10 k = wz 4294967295 -> k11 k = wz (Z_ORDER + 2 * i) -> k15 k = wz (i + 1) ->
  ix_ok X -> PATG X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i < 19 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists k',
     if i + 1 =? 19
     then ILOOPk X (mkW (iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)) c r) PC_LL2_X k' ms' /\ k12 k' = wz 19
     else ILOOPk X (mkW (iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)) c r) PC_LL2_B k' ms'
          /\ k10 k' = wz 4294967295 /\ k11 k' = wz (Z_ORDER + 2 * (i + 1)) /\ k15 k' = wz (i + 1 + 1)) ms.
Proof.
  intros X s c r i [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms HL E10 E11 E15 XO HP LL Ri RPUT.
  iarm_openk HL. subst x10 x11 x15.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL2_B.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST.
  pose proof (munch_refl [(il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m) as MUf. pose proof (wmono_refl psegs m) as WMf.
  pose proof (order_lt19 i ltac:(lia)) as ROR. set (od := arr_get order_a i) in *.

  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  pose proof (order_rd m i (wa (Z_ORDER + 2 * i)) MI ltac:(lia) eq_refl) as RD.
  fold od in RD. zs. rewrite (zx16_small od) by lia. clear RD.
  do 4 zs. replace (od ≪ 1) with (2 * od) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite (land_u32_small (i + 1)) by lia.
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) od 0 ltac:(reflexivity).
  do 3 zs. itr_groups MUf WMf. br_cases K.
  - replace (i + 1 =? 19) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done. eexists. split; [eapply ILOOPk_intro; ired; [ireg .. |]|].
    + close_k jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + cbn [k10 k11 k15]. repeat split; ireg.
  - replace (i + 1 =? 19) with true by (symmetry; apply Z.eqb_eq; lia).
    apply evt_done. eexists. split; [eapply ILOOPk_intro; ired; [ireg .. |]| cbn [k12]; reflexivity].
    close_k jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma zlens_19 : forall n a, zlens n a 19 = a.
Proof. intros [|n] a; reflexivity. Qed.

Lemma ll2_loop : forall n X s c r i k ms,
  ILOOPk X (mkW s c r) PC_LL2_B k ms -> k10 k = wz 4294967295 -> k11 k = wz (Z_ORDER + 2 * i) -> k15 k = wz (i + 1) ->
  ix_ok X -> PATG X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i < 19 -> 19 - i <= Z.of_nat n ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists k', ILOOPk X (mkW (iset_lens s (zlens n (is_lens s) i)) c r) PC_LL2_X k' ms' /\ k12 k' = wz 19) ms.
Proof.
  induction n as [|n IH]; intros X s c r i k ms HL E10 E11 E15 XO HP LL Ri Rn RPUT; [cbn [Z.of_nat] in Rn; lia|].
  cbn [zlens]. replace (i <? 19) with true by (symmetry; apply Z.ltb_lt; lia).
  eapply evt_cut; [exact (ll2_body X s c r i k ms HL E10 E11 E15 XO HP LL Ri RPUT)|].
  intros ms1 (k1 & H1).
  destruct (Z.eqb_spec (i + 1) 19) as [E|NE].
  - rewrite E, zlens_19. apply evt_done. exists k1. exact H1.
  - destruct H1 as (H1 & E10' & E11' & E15').
    refine (IH X (iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)) c r (i + 1) k1 ms1 H1 E10' E11' E15' XO _ _ _ _ RPUT).
    + exact HP.
    + cbn [is_lens iset_lens]. rewrite arr_len_set. exact LL.
    + lia.
    + rewrite Nat2Z.inj_succ in Rn. lia.
Qed.

Local Ltac close_kA jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma ll2_exit : forall X s c r k ms,
  ILOOPk X (mkW s c r) PC_LL2_X k ms -> k12 k = wz 19 -> ix_ok X -> PATG X (mkW s c r) ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists k', ILOOPk X (mkW (iset_have s 19) c r) PC_LL_CALL k' ms') ms.
Proof.
  intros X s c r [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms HL E12 XO HP RPUT.
  iarm_openk HL. subst x12.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL2_X.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  zs. itr_groups MUf WMf.
  apply evt_done. eexists. eapply ILOOPk_intro; ired; [ireg .. |].
  close_kA jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma ll2_walk : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_LL2 q ms -> sc15 q = wz (is_have s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> PATG X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= is_have s <= 19 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists k, ILOOPk X (mkW (ll2 19 s) c r) PC_LL_CALL k ms') ms.
Proof.
  intros X s c r q ms HL E15 E26 XO HP LL RH RPUT.
  eapply evt_cut; [exact (ll2_pre X s c r q ms HL E15 E26 RH)|]. intros ms1 (k1 & H1).
  destruct (Z.ltb_spec (is_have s) 19) as [LT|GE].
  - destruct H1 as (H1 & E10 & E11 & E15').
    rewrite (ll2_zlens 19 s) by (cbn; lia).
    eapply evt_cut; [exact (ll2_loop 19 X s c r (is_have s) k1 ms1 H1 E10 E11 E15' XO HP LL ltac:(lia) ltac:(cbn; lia) RPUT)|].
    intros ms2 (k2 & H2 & E12).
    exact (ll2_exit X _ c r k2 ms2 H2 E12 XO HP RPUT).
  - rewrite ll2_stop by lia. apply evt_done. exists k1. exact H1.
Qed.

Definition PC_LL_RET : Z := 0x1d9d8.

Local Ltac close_A jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; unfold iframe_cells; inorm; close_cells FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma ll_after : forall X s3 c r k ms ret,
  ILOOPk X (mkW s3 c r) PC_LL_RET k ms -> k10 k = wz (ret mod 2 ^ 64) -> (ret = 0 \/ ret = 1 \/ ret = -1) -> ix_ok X ->
  (is_window_blk s3 <> None -> ix_hasw X = true) -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 ->
  arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
    if negb (ret =? 0)
    then exists x8, ILOOP X (mkW (iset_mode s3 BAD) (icset_msg c MSG_invalid_code_lengths_set) (irset_ret r ret)) PC_DISPATCH x8 (wz BAD) ms'
    else exists q, ILOOPg X (mkW (iset_mode (iset_have s3 0) CODELENS) c (irset_ret r ret)) PC_CODELENS_E q ms'
                   /\ sc13 q = wz 0 /\ sc26 q = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros X s3 c r [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms ret HL E10 RRET XO Pwin Pin Pin1 Pout RPUT.
  iarm_openk HL. subst x10.
  ix_open XO. unfold PC_LL_RET.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  assert (RM : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  zs. br_cases K.
  -
    assert (R0 : ret = 0) by (destruct RRET as [R|[R|R]]; rewrite R in K; [exact R| |]; exfalso; revert K; vm_compute; discriminate).
    clear RRET K RM. subst ret. cbn [Z.eqb negb].
    do 10 zs. itr_groups MUf WMf.
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. |]| cbn [sc13 sc26]; split; reflexivity].
    close_A jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  -
    assert (R1 : (ret =? 0) = false) by (apply Z.eqb_neq; intros R; rewrite R in K; apply K; reflexivity). rewrite R1. cbn [negb].
    clear RRET K.
    do 4 zs. do 5 zs. do 5 zs. do 2 zs. itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_A jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Section LLcall.
Variable flush : Z.
Hypothesis CODELENS_CORE : codelens_core_stmt flush.
Hypothesis ITABLE : inflate_table_stmt.

Lemma ll_call : forall X s c r k ms ret tbl nxt lb wk,
  ILOOPk X (mkW s c r) PC_LL_CALL k ms -> ix_ok X -> PATG X (mkW s c r) ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  inflate_table CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s) = (ret, tbl, nxt, lb, wk) ->
  it_safe CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s) = true ->
  ATY s -> (forall i, 0 <= i < 19 -> arr_get (is_lens s) i <= 15) ->
  evt psegs (fun ms' =>
    if negb (ret =? 0)
    then exists x8, ILOOP X (mkW (iset_mode (ll_tab s tbl nxt lb wk) BAD) (icset_msg c MSG_invalid_code_lengths_set) (irset_ret r ret)) PC_DISPATCH x8 (wz BAD) ms'
    else exists q, ILOOPg X (mkW (ll_s2 (ll_tab s tbl nxt lb wk)) c (irset_ret r ret)) PC_CODELENS_E q ms'
                   /\ sc13 q = wz 0 /\ sc26 q = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros X s c r [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms ret tbl nxt lb wk HL XO HP RPUT EIT SAFE HA HL15.
  iarm_openk HL.
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
      | cbn [it_codes_ok]; lia
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
  lazymatch type of WMc with wmono _ ?ma _ => itr_groups MUc WMc; transport_after_call psegs ma m' MUc WMc end. clear MUc WMc MI ARRS LAY.
  replace (ret_pc (wz 121304)) with (wz 121304) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  unfold ll_s2.
  eapply (ll_after X (ll_tab s tbl nxt lb wk) c r _ _ ret); [ | | exact RRET | exact XO | exact Pwin | exact Pin | exact Pin1 | exact Pout | exact RPUT].
  { eapply ILOOPk_intro; ired; [ireg .. |].
    apply IMEM_intro; [ exists jf; exact FRM | exact STKc | exact ZS | exact STc | exact IN | exact OUT | exact MIc | exact MU | exact WM ]. }
  reflexivity.
Qed.

Lemma lenlens_core : lenlens_core_stmt flush.
Proof.
  intros X [s c r] q ms EF HL E12 E15 E26 XO HW HA HP HM. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _ & Rin & _).
  assert (LL : arr_len (is_lens s) = 320) by (destruct HCORE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  assert (HIN1 : arr_len (ic_input c) < 2^31) by (rewrite Pin; exact Pin1).
  pose proof (DREGSg_of_REGS c r HREGS HIN1) as DR.
  rewrite arm_LENLENS_eq.
  eapply evt_cut; [exact (ll_entry X s c r q ms HL E12 E15 E26 Hh (proj2 Hnc))|]. intros ms1 (q1 & H1 & HQ1).
  eapply evt_cut; [exact (ll1_loop 19 X s c r q1 ms1 H1 HQ1 XO DR Rin HP HM LL Hh (proj2 Hnc) ltac:(cbn; lia) ltac:(lia))|]. intros ms2 H2.
  pose proof (lenlens_facts s c r HW HA HM) as [_ F].
  pose proof (WINV_lenlens_okb s c r HW HA HM) as OKB. unfold lenlens_okb in OKB. cbn [w_s] in OKB.
  pose proof (lenlens_next_WINV s c r HW HA HM) as NXW. unfold lenlens_next in NXW.
  destruct (lenlens_while1 19 (mkW s c r)) as [[] [s1 c1 r1] | w' | rc w']; cbn [LL1POST w_s w_r] in H2.
  2:{ apply evt_done. cbn [IPOST wof]. exact H2. }
  2:{ destruct H2. }
  destruct H2 as ((q2 & HL2 & E15' & E26') & HP1 & Hh1 & HM1).
  destruct F as (-> & lens19 & EL2 & HL19 & HLs19 & HT19 & HC1 & HR1 & HCm1 & Hb1 & Hnl1 & Hnd1 & HWF1 & HWB1 & HA1).
  apply andb_prop in OKB. destruct OKB as [_ OKB]. apply ll_call_ok_sound in OKB. destruct OKB as (CL15 & SAFE & _).
  assert (LL1 : arr_len (is_lens s1) = 320) by (destruct HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  pose proof HR1 as (Rn1 & Rh1 & Rnh1 & Rp1 & Rl1 & Rpl1 & _).
  pose proof HP1 as (_ & _ & _ & _ & _ & Pwin1 & Pin' & _ & Pout' & _ & Pisr1 & _). cbn [w_s w_c w_r] in *.
  assert (RPUT1 : 0 <= ir_put r1 <= Z.of_nat (length (ix_rest0 X))) by (rewrite <- Pout; lia).
  eapply evt_cut; [exact (ll2_walk X s1 c r1 q2 ms2 HL2 E15' E26' XO HP1 LL1 Hh1 RPUT1)|]. intros ms3 (k3 & H3).
  unfold ll_fin. rewrite EL2 in H3, CL15, SAFE, NXW |- *. cbv zeta in NXW.
  cbn [is_lens is_codes is_work iset_have iset_lens] in CL15, SAFE, NXW |- *.
  destruct (inflate_table CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)) as [[[[ret tbl] nxt] lb] wk] eqn:EIT. cbv zeta.
  assert (Pf1 : is_flags s1 = 0).
  { destruct HP1 as (_ & _ & _ & Pfl1 & _). cbn [w_s w_r] in Pfl1. destruct Pfl1 as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM1 in E; discriminate E. }
  assert (HPA : PATG X (mkW (iset_have (iset_lens s1 lens19) 19) c r1)).
  { eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_have iset_lens]; rewrite HM1; unfold LENLENS, FLAGS, HCRC; lia| reflexivity..| |exact Pisr1].
    cbn [is_mode iset_have iset_lens]. rewrite HM1. reflexivity. }
  assert (HAA : ATY (iset_have (iset_lens s1 lens19) 19)).
  { unfold ATY. cbn [is_lens is_work is_codes iset_have iset_lens]. split; [exact HT19| destruct HA1 as [_ H]; exact H]. }
  eapply evt_cut.
  { eapply (ll_call X (iset_have (iset_lens s1 lens19) 19) c r1 k3 ms3 ret tbl nxt lb wk H3 XO HPA RPUT1);
      cbn [is_lens is_codes is_work iset_have iset_lens]; [exact EIT | exact SAFE | exact HAA | exact CL15]. }
  intros ms4 H4.
  destruct (Z.eqb_spec ret 0) as [R0|R1]; cbn [negb] in H4 |- *.
  -
    destruct H4 as (q4 & HL4 & E13 & E26'').
    specialize (NXW _ eq_refl). destruct NXW as (HW2 & HA2 & HM2).
    refine (CODELENS_CORE X _ q4 ms4 EF HL4 E13 E26'' XO HW2 HA2 _ HM2).
    unfold ll_s2, ll_tab. eapply PATG_step; [exact HPA| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode iset_have]; unfold CODELENS, FLAGS, HCRC; lia| reflexivity..|].
    exact Pisr1.
  -
    destruct H4 as (x8' & HL4).
    apply evt_done. split; [cbn [IPOST]; exists x8'; exact HL4|]. cbn [wof].
    unfold ll_tab. eapply PATG_step; [exact HPA| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| reflexivity..|].
    exact Pisr1.
Qed.

Lemma arm_LENLENS_of : arm_stmtg flush LENLENS PC_LENLENS (arm_LENLENS ivar_ref flush).
Proof.
  intros X [s c r] x12 ms EF HL XO HW HA HP HM.
  pose proof HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in HMF. rewrite HM in HMF. unfold MF in HMF. cbn in HMF.
  destruct HMF as (_ & _ & Hnc & _ & _ & Hh & _).
  eapply evt_cut; [exact (ll_arm_entry X s c r _ x12 ms HL Hh (proj2 Hnc))|]. intros ms1 (q1 & H1 & E12 & E15 & E26).
  exact (lenlens_core X (mkW s c r) q1 ms1 EF H1 E12 E15 E26 XO HW HA HP HM).
Qed.
End LLcall.
