(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_iface Z_infl_c_defs Z_infl_c_pure Z_infl_c_tab Z_infl_a_dist1 Z_infl_a_dist Zg_infl_t_iface Zg_infl_c_kit Zg_infl_a_lenlens1 Zg_infl_a_lenlens Zg_infl_a_codelens1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate Inftrees ItableModel InffastMem RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_LENLENS1 RefInflateA_CODELENS1 RefInflateA_CODELENS11 RefInflateSafeA5 RefInflateSafeOK RefInflateSafeOK2 RefInflateSafeOK3 RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.
Local Notation pullr := RefInflateArmLib.pullr.

Local Ltac close_l jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [exact GA| exact GT| unfold ilens, u16arr; inorm; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma cl_rep_body : forall X s c r i t v q ms,
  ILOOPg X (mkW s c r) PC_CL_R q ms -> sc13 q = wz i -> sc17 q = wz t -> sc6 q = wz v ->
  ix_ok X -> PATG X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i < t -> t <= 320 -> 0 <= v < 16 ->
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
  ix_ok X -> PATG X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i -> t = i + Z.of_nat n -> (0 < n)%nat -> t <= 320 -> 0 <= v < 16 ->
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
  ILOOPg X (mkW s c r) PC_CL_RX q ms -> sc13 q = wz t -> sc27 q = wz (il_NI (ix_L X) + ir_next r) -> ix_ok X -> PATG X (mkW s c r) ->
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
  sc27 q = wz (il_NI (ix_L X) + ir_next r) -> ix_ok X -> PATG X (mkW s c r) ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s -> 3 <= copy -> is_have s + copy <= 320 -> 0 <= len < 16 ->
  is_mode s = CODELENS -> is_flags s = 0 -> ISR s -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
    (exists q', ILOOPg X (mkW (cl_rep s copy len) c r) PC_CL_T q' ms' /\ CLK X (cl_rep s copy len) q'
                /\ sc13 q' = wz (is_have (cl_rep s copy len)) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r))
    /\ PATG X (mkW (cl_rep s copy len) c r)) ms.
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
  - eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0
      | cbn [is_mode iset_have iset_lens]; rewrite HM; unfold CODELENS, FLAGS, HCRC; lia| try reflexivity ..]; [|exact Pisr].
    cbn [is_mode iset_have iset_lens]. rewrite HM. reflexivity.
Qed.

Definition CLBPOST (X : ictx) (res : ares bool) : machine_state -> Prop :=
  match res with
  | ARun true w1 => fun ms' => (exists q, ILOOPg X w1 PC_CL_T q ms' /\ CLK X (w_s w1) q /\ sc13 q = wz (is_have (w_s w1))
                                           /\ sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w1))) /\ PATG X w1
  | ARun false w1 => fun ms' => (exists x8, ILOOP X w1 PC_DISPATCH x8 (wz BAD) ms') /\ PATG X w1
  | ALeave w' => fun ms' => ILEAVE X w' ms' /\ PATG X w'
  | ARet _ _ => fun _ => False
  end.

Lemma cl_body : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_CL_B q ms -> CLK X s q -> sc13 q = wz (is_have s) -> sc6 q = wz (ir_have r) ->
  sc7 q = wz (il_NI (ix_L X) + ir_next r) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> CL s c r -> PATG X (mkW s c r) -> is_have s < is_nlen s + is_ndist s ->
  decode_okb cl_two s c r (is_lencode s) (is_lenbits s) = true ->
  evt psegs (CLBPOST X (codelens_body (mkW s c r))) ms.
Proof.
  intros X s c r q ms HL HK E13 E6 E7 E26 XO HCL HP LT OKD.
  pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E'|E'] & _)]; [exact Pf| |]; rewrite E in E'; discriminate E').
  clear Pfl.
  pose proof HR as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB0 RH0] & Rin & _).
  assert (LL : arr_len (is_lens s) = 320) by (destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  pose proof (cpok_ofs_ok _ _ _ _ HT) as CPO.
  assert (RPUT : 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X))) by (rewrite <- Pout; lia).
  destruct (decode_okb_lvl1 _ _ _ _ _ _ OKD) as [RN D1].
  destruct (dchk 8 c (dec_idx1 (is_lenbits s)) code_bits (ctab_size (is_lencode s)) (code_at s (is_lencode s)) r) as [rf|] eqn:HD1; [clear D1| contradiction].
  rewrite codelens_body_eq. change (DECODE1 (is_lencode s) (is_lenbits s)) with (DECODE_k 8 (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits).
  eapply evt_cut; [exact (cl_dec X s c r rf q ms HL HK E13 E6 E7 E26 XO HR HP RN CPO HD1)|].
  intros ms1 [(r1 & q1 & ED & -> & KB & RI & HR1 & HPL1 & HJ & HQ)|(r1 & ED & HPL1 & HLV)].
  2:{ rewrite ED. cbn [CLBPOST]. apply evt_done. split; [exact HLV|]. eapply PATG_pulled; [exact HP| exact HPL1]. }
  rewrite ED.
  destruct (decG_r1_facts c r r1 HR1 HPL1) as ((RNX1 & RHV1 & RNH1 & RB1 & RHB1) & EI1 & EO1 & ER1 & EP1 & EL1).
  pose proof (dchk_sound 8 s c _ _ _ r r1 HD1) as SND. cbv zeta in SND. destruct SND as (_ & RN32 & _).
  set (here := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) in *.
  pose proof (code_bits_range here) as RCB. pose proof (code_val_range here) as RCV.
  pose proof (REGS_hold64 c r1 HR1) as RH1.
  assert (HP1 : PATG X (mkW s c r1)) by (eapply PATG_pulled; [exact HP| exact HPL1]).
  destruct (Z.ltb_spec (code_val here) 16) as [V|V].
  -
    eapply evt_cut; [exact (cl_litw X s c r r1 q1 ms1 HJ HQ XO HP EI1 EO1 ER1 EP1 EL1 (conj KB (proj2 RB1)) RH1 RI CPO RN V LL ltac:(lia) RPUT)|].
    intros ms2 (q2 & H2 & HK2 & E13' & E26'). cbn [CLBPOST w_s w_r]. apply evt_done. split.
    + exists q2. split; [exact H2|]. split; [exact HK2|].
      split; [rewrite E13'; unfold cl_lit; cbn [is_have iset_have iset_lens]; rewrite wrap32_id by lia; reflexivity| exact E26'].
    + destruct (ddrop_facts' r1 (code_bits here) ltac:(lia) ltac:(lia) RH1) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
      unfold cl_lit. eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0
        | cbn [is_mode iset_have iset_lens]; rewrite E; unfold CODELENS, FLAGS, HCRC; lia| try reflexivity ..].
      * cbn [is_mode iset_have iset_lens]. rewrite E. reflexivity.
      * exact Pisr.
  -
    assert (Rnb : 2 <= cl_nb (code_val here) <= 7) by (unfold cl_nb; destruct (code_val here =? 16); [lia|]; destruct (code_val here =? 17); lia).
    eapply evt_cut; [exact (cl_need X s c r r1 q1 ms1 HJ HQ XO HR1 HPL1 (proj1 RB0) HP KB (proj2 RN32) RI CPO RN V)|].
    intros ms2 [(r2 & q2 & EN & HJ2 & HQ2)|(r2 & EN & HLV)].
    2:{ fold here in EN. rewrite EN. cbn [CLBPOST]. apply evt_done. split; [exact HLV|].
        destruct (NBG_leave_facts c (code_bits here + cl_nb (code_val here)) s r1 r2 HR1 ltac:(lia) EN) as (_ & HPL2 & _). eapply PATG_pulled; [exact HP1| exact HPL2]. }
    fold here in EN. rewrite EN.
    destruct (NBG_run_facts c (code_bits here + cl_nb (code_val here)) s r1 r2 HR1 ltac:(lia) EN) as (HR2 & HPL2 & KB2 & _).
    destruct (nbG_r1_facts c r1 r2 (code_bits here + cl_nb (code_val here)) HR2 HPL2 KB2) as (EI2 & EO2 & ER2 & EP2 & EL2 & RB2 & RH2 & RHV2 & RN2).
    assert (HP2 : PATG X (mkW s c r2)) by (eapply PATG_pulled; [exact HP1| exact HPL2]).
    fold here in HJ2.
    assert (EIr : ir_in r2 = ir_in r) by congruence. assert (EOr : ir_out r2 = ir_out r) by congruence.
    assert (ERr : ir_ret r2 = ir_ret r) by congruence. assert (EPr : ir_put r2 = ir_put r) by congruence. assert (ELr : ir_left r2 = ir_left r) by congruence.
    unfold cl_after. cbv zeta. fold here.
    eapply evt_cut; [exact (cl_rep_hd X s c r r1 r2 q2 ms2 HJ2 HQ2 XO HP EIr EOr ERr EPr ELr RB2 RH2 (proj1 RHV2) V LL
                             ltac:(lia) ltac:(lia) HLs RPUT)|].
    intros ms3 H3. cbv zeta in H3. fold here in H3.
    set (cb := code_bits here) in *. set (nb := cl_nb (code_val here)) in *.
    set (r3 := ddrop r2 cb) in *. set (copy := cl_base (code_val here) + BITSv (ir_hold r3) nb) in *. set (r4 := ddrop r3 nb) in *.
    destruct (ddrop_facts' r2 cb ltac:(lia) ltac:(lia) RH2) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9). fold r3 in F1, F2, F3, F4, F5, F6, F7, F8, F9.
    destruct (ddrop_facts' r3 nb ltac:(lia) ltac:(lia) F7) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). fold r4 in G1, G2, G3, G4, G5, G6, G7, G8, G9.
    pose proof (BITSv_range (ir_hold r3) nb ltac:(lia) ltac:(lia)) as RBV.
    assert (P7 : 2 ^ nb <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia). change (2 ^ 7) with 128 in P7.
    assert (Rcp : 3 <= copy <= 138) by (subst copy; unfold cl_base; destruct (code_val here =? 16); [lia|]; destruct (code_val here =? 17); lia).
    assert (HP3 : PATG X (mkW s c r3)) by (eapply PATG_regs; [exact HP2| assumption..]).
    assert (HP4 : PATG X (mkW s c r4)) by (eapply PATG_regs; [exact HP3| assumption..]).
    assert (BADP : forall rr, PATG X (mkW s c rr) -> PATG X (cl_bad s c rr)).
    { intros rr HPr. unfold cl_bad. eapply PATG_step; [exact HPr| reflexivity| reflexivity| reflexivity| exact Pf0
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
      /\ PATG X w1
  | ALeave w' => fun ms' => ILEAVE X w' ms' /\ PATG X w'
  | ARet _ _ => fun _ => False
  end.

Lemma cl_loop : forall k X s c r q ms,
  ILOOPg X (mkW s c r) PC_CL_B q ms -> CLK X s q -> sc13 q = wz (is_have s) -> sc6 q = wz (ir_have r) ->
  sc7 q = wz (il_NI (ix_L X) + ir_next r) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> CL s c r -> PATG X (mkW s c r) -> is_have s < is_nlen s + is_ndist s -> clw_chk k s c r = true ->
  is_nlen s + is_ndist s - is_have s <= Z.of_nat k ->
  evt psegs (CLPOST X (codelens_while k (mkW s c r))) ms.
Proof.
  induction k as [|k IH]; intros X s c r q ms HL HK E13 E6 E7 E26 XO HCL HP LT CHK RK; [cbn [Z.of_nat] in RK; lia|].
  rewrite RefInflateA_CODELENS1.codelens_while_S. cbn [clw_chk] in CHK.
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
  ix_ok X -> WINV (mkW s c r) -> ATY s -> PATG X (mkW s c r) -> is_mode s = CODELENS ->
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
