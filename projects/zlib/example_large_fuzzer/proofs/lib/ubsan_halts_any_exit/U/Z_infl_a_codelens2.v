From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_ukit Z_infl_iface Z_infl_c_pure Z_infl_c_tab Z_infl_t_iface Z_itab_kit Z_infl_a_dist1 Z_infl_a_dist Z_infl_a_lenlens1 Z_infl_a_lenlens Z_infl_a_codelens1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate Inftrees ItableModel InffastMem RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_LENLENS1 RefInflateA_CODELENS1 RefInflateA_CODELENS11 RefInflateSafeA5 RefInflateSafeOK RefInflateSafeOK2 RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.
Local Ltac close_l j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [exact GA| exact GT| unfold ilens, u16arr; inorm; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Lemma cl_rep_body : forall X s c r i cnt v q ms,
  ILOOPh X (mkW s c r) PC_CL_R q ms -> CLR X s r i cnt v q ->
  ix_ok X -> PATI X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i -> 1 <= cnt -> i + cnt <= 320 -> 0 <= v < 16 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q',
     (if cnt - 1 =? 0 then ILOOPh X (mkW (iset_lens s (arr_set (is_lens s) i v)) c r) PC_CL_RX q' ms'
      else ILOOPh X (mkW (iset_lens s (arr_set (is_lens s) i v)) c r) PC_CL_R q' ms')
     /\ CLR X (iset_lens s (arr_set (is_lens s) i v)) r (i + 1) (cnt - 1) v q') ms.
Proof.
  intros X s c r i cnt v [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP LL Ri Rc Ric Rv RPUT.
  unfold CLR, CLK in HQ. hred_in HQ.
  destruct HQ as (E16 & E5 & E6 & E7 & E17 & (E11 & E12 & E13 & E14 & E15) & E9 & E10 & E18 & E22 & E24).
  iarm_openh HL. subst.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_R.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST.
  pose proof (munch_refl [(il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  zstep. br_true.
  zs. replace (i ≪ 1) with (2 * i) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zs. zstep. rewrite (zb_lxor_ones (il_As (ix_L X) + 168)) by lia. br_true.
  zs. zs. zs.
  assert (EV : wrap16 v = v) by (apply wrap16_id; lia).
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) i v ltac:(reflexivity).
  zs. itr_groups MUf WMf. zstep. br_cases K.
  - replace (cnt - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |]|].
    + close_l j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + unfold CLR, CLK. hred. ired. repeat split; ireg.
  - replace (cnt - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |]|].
    + close_l j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + unfold CLR, CLK. hred. ired. repeat split; ireg.
Qed.
Lemma fill_S' : forall n a i v, fill (S n) a i v = fill n (arr_set a i v) (i + 1) v.
Proof. intros. reflexivity. Qed.
Lemma cl_rep_loop : forall n X s c r i cnt v q ms,
  ILOOPh X (mkW s c r) PC_CL_R q ms -> CLR X s r i cnt v q ->
  ix_ok X -> PATI X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i -> cnt = Z.of_nat n -> (0 < n)%nat -> i + cnt <= 320 -> 0 <= v < 16 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (iset_lens s (fill n (is_lens s) i v)) c r) PC_CL_RX q' ms'
     /\ CLR X (iset_lens s (fill n (is_lens s) i v)) r (i + cnt) 0 v q') ms.
Proof.
  induction n as [|n IH]; intros X s c r i cnt v q ms HL HQ XO HP LL Ri Ec Hn Ric Rv RPUT; [lia|].
  rewrite fill_S'.
  eapply evt_cut; [exact (cl_rep_body X s c r i cnt v q ms HL HQ XO HP LL Ri ltac:(lia) Ric Rv RPUT)|].
  intros ms1 (q1 & H1 & HQ1).
  destruct (Z.eqb_spec (cnt - 1) 0) as [E|NE].
  - assert (n = 0)%nat as -> by lia. cbn [fill]. apply evt_done. exists q1. replace (i + cnt) with (i + 1) by lia. replace 0 with (cnt - 1) by lia.
    split; assumption.
  - replace (i + cnt) with (i + 1 + (cnt - 1)) by lia.
    refine (IH X (iset_lens s (arr_set (is_lens s) i v)) c r (i + 1) (cnt - 1) v q1 ms1 H1 HQ1 XO _ _ _ _ _ _ Rv RPUT).
    + exact HP.
    + cbn [is_lens iset_lens]. rewrite arr_len_set. exact LL.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.
Local Ltac close_gA j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Lemma cl_rep_tl : forall X s c r t v q ms,
  ILOOPh X (mkW s c r) PC_CL_RX q ms -> CLR X s r t 0 v q -> ix_ok X -> PATI X (mkW s c r) ->
  0 <= t <= 320 -> 257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q',
     if t <? is_nlen s + is_ndist s
     then ILOOPh X (mkW (iset_have s t) c r) PC_CL_B q' ms' /\ CLB X (iset_have s t) r t q'
     else ILOOPh X (mkW (iset_have s t) c r) PC_CL_X q' ms' /\ CLX X (iset_have s t) r q') ms.
Proof.
  intros X s c r t v [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP Rt Rnl Rnd RPUT.
  unfold CLR, CLK in HQ. hred_in HQ.
  destruct HQ as (E16 & E5 & E6 & E7 & E17 & (E11 & E12 & E13 & E14 & E15) & E9 & E10 & E18 & E22 & E24).
  iarm_openh HL. subst.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_RX.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  zs. itr_groups MUf WMf. do 2 zs.
  zstep. br_cases K.
  - replace (t <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |]| unfold CLB, CLK, HCC, HC; hred; ired; repeat split; ireg].
    close_gA j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  - replace (t <? is_nlen s + is_ndist s) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |]| unfold CLX, HCC, HC; hred; ired; repeat split; ireg].
    close_gA j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.
Definition CLBPOST (X : ictx) (res : ares bool) : machine_state -> Prop :=
  match res with
  | ARun true w1 => fun ms' =>
      (exists q, if is_have (w_s w1) <? is_nlen (w_s w1) + is_ndist (w_s w1)
                 then ILOOPh X w1 PC_CL_B q ms' /\ CLB X (w_s w1) (w_r w1) (is_have (w_s w1)) q
                 else ILOOPh X w1 PC_CL_X q ms' /\ CLX X (w_s w1) (w_r w1) q)
      /\ PATI X w1
  | ARun false w1 => fun ms' => (exists x26 x12, ILOOP X w1 PC_DISPATCH x26 x12 ms') /\ PATI X w1
  | ALeave w' => fun ms' => ILEAVE X w' ms' /\ PATI X w'
  | ARet _ _ => fun _ => False
  end.
Lemma cl_rep_run : forall X s c r copy len q ms,
  ILOOPh X (mkW s c r) PC_CL_R q ms -> CLR X s r (is_have s) copy len q -> ix_ok X -> PATI X (mkW s c r) ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s -> 3 <= copy -> is_have s + copy <= 320 -> 0 <= len < 16 ->
  is_mode s = CODELENS -> is_flags s = 0 -> ISR s -> 257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (CLBPOST X (ARun true (mkW (cl_rep s copy len) c r))) ms.
Proof.
  intros X s c r copy len q ms HL HQ XO HP LL Rh Rc Rhc Rlen HM Pf0 Pisr Rnl Rnd RPUT. cbn [CLBPOST w_s w_r].
  rewrite (cl_rep_fill s copy len) by lia. rewrite (wrap16_id len) by lia.
  eapply evt_cut.
  { exact (cl_rep_loop (Z.to_nat copy) X s c r (is_have s) copy len q ms HL HQ XO HP LL Rh ltac:(lia) ltac:(lia) Rhc Rlen RPUT). }
  intros ms1 (q1 & H1 & HQ1).
  eapply evt_cut.
  { exact (cl_rep_tl X _ c r (is_have s + copy) len q1 ms1 H1 HQ1 XO HP ltac:(lia) Rnl Rnd RPUT). }
  intros ms2 (q2 & H2). apply evt_done. split.
  - exists q2. cbn [is_have is_nlen is_ndist iset_have iset_lens] in *. exact H2.
  - eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0
      | cbn [is_mode iset_have iset_lens]; rewrite HM; unfold CODELENS, FLAGS, HCRC; lia| reflexivity ..| | exact Pisr| bk_keep].
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
Lemma cl_body : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_CL_B q ms -> CLB X s r (is_have s) q ->
  ix_ok X -> CL s c r -> PATI X (mkW s c r) -> is_have s < is_nlen s + is_ndist s ->
  decode_okb cl_two s c r (is_lencode s) (is_lenbits s) = true ->
  evt usegs (CLBPOST X (codelens_body (mkW s c r))) ms.
Proof.
  intros X s c r q ms HL HQ XO HCL HP LT OKD.
  pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
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
  eapply evt_cut; [exact (cl_dec X s c r q ms HL HQ XO DR Rin HP RN CPO DL)|].
  intros ms1 [(r1 & q1 & ED & EC & KB & RI & HR1 & HJ & HQJ)|(r1 & ED & HR1 & HLV)].
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
    eapply evt_cut; [exact (cl_litw X s c r r1 q1 ms1 HJ HQJ XO HP EI1 EO1 ER1 EP1 EL1 (conj KB (proj2 RB1)) RH1 RI CPO RN V LL ltac:(lia) Hnl Hnd RPUT (proj1 Rh1) Rn1)|].
    intros ms2 (q2 & H2). cbv zeta in H2. fold here in H2. cbn [CLBPOST w_s w_r]. apply evt_done. split.
    + exists q2. unfold cl_lit in *. cbn [is_have is_nlen is_ndist iset_have iset_lens] in *. rewrite (wrap32_id (is_have s + 1)) in * by lia. exact H2.
    + destruct (ddrop_facts' r1 (code_bits here) ltac:(lia) ltac:(lia) RH1) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
      unfold cl_lit. eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0
        | cbn [is_mode iset_have iset_lens]; rewrite E; unfold CODELENS, FLAGS, HCRC; lia| try reflexivity ..]; [| exact Pisr| bk_keep].
      cbn [is_mode iset_have iset_lens]. rewrite E. reflexivity.
  -
    eapply evt_cut; [exact (cl_need X s c r r1 q1 ms1 HJ HQJ XO DR1 Rin HP EI1 EO1 ER1 EP1 EL1 KB (proj2 RN32) RI CPO RN V)|].
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
                             ltac:(lia) ltac:(lia) HLs RPUT Rn2)|].
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
        | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| try reflexivity ..]; [exact Pisr| bk_keep]. }
    revert H3. destruct (Z.eqb_spec (code_val here) 16) as [V16|NV16]; [destruct (Z.eqb_spec (is_have s) 0) as [H0|H0]|]; cbn [andb]; intros H3.
    1:{ cbn [CLBPOST]. apply evt_done. split; [exact H3| apply BADP; exact HP3]. }
    all: revert H3; destruct (Z.ltb_spec (is_nlen s + is_ndist s) (is_have s + copy)) as [OV|OV]; intros H3.
    1,3: cbn [CLBPOST]; apply evt_done; split; [exact H3| apply BADP; exact HP4].
    all: destruct H3 as (q3 & HL3 & HQ3).
    + pose proof (HLs (is_have s - 1) ltac:(lia)) as RL.
      exact (cl_rep_run X s c r4 copy _ q3 ms3 HL3 HQ3 XO HP4 LL ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E Pf0 Pisr Hnl Hnd ltac:(lia)).
    + exact (cl_rep_run X s c r4 copy _ q3 ms3 HL3 HQ3 XO HP4 LL ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv iota; lia) E Pf0 Pisr Hnl Hnd ltac:(lia)).
Qed.
Definition CLPOST (X : ictx) (res : ares unit) : machine_state -> Prop :=
  match res with
  | ARun _ w1 => fun ms' =>
      (if is_mode (w_s w1) =? BAD then exists x26 x12, ILOOP X w1 PC_DISPATCH x26 x12 ms'
       else exists q, ILOOPh X w1 PC_CL_X q ms' /\ CLX X (w_s w1) (w_r w1) q)
      /\ PATI X w1
  | ALeave w' => fun ms' => ILEAVE X w' ms' /\ PATI X w'
  | ARet _ _ => fun _ => False
  end.
Lemma cl_loop : forall k X s c r q ms,
  ILOOPh X (mkW s c r) PC_CL_B q ms -> CLB X s r (is_have s) q ->
  ix_ok X -> CL s c r -> PATI X (mkW s c r) -> is_have s < is_nlen s + is_ndist s -> clw_chk k s c r = true ->
  is_nlen s + is_ndist s - is_have s <= Z.of_nat k ->
  evt usegs (CLPOST X (codelens_while k (mkW s c r))) ms.
Proof.
  induction k as [|k IH]; intros X s c r q ms HL HQ XO HCL HP LT CHK RK; [cbn [Z.of_nat] in RK; lia|].
  rewrite RefInflateA_CODELENS1.codelens_while_S. cbn [clw_chk] in CHK.
  replace (is_have s <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (is_have s <? is_nlen s + is_ndist s) with true in CHK by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in CHK. destruct CHK as [OKD CHK].
  pose proof (codelens_body_spec c s r HCL LT) as BS.
  eapply evt_cut; [exact (cl_body X s c r q ms HL HQ XO HCL HP LT OKD)|]. intros ms1 H1.
  destruct (codelens_body (mkW s c r)) as [[|] [s1 c1 r1] | w' | rc w']; cbn [CLBPOST w_s w_r] in H1.
  - destruct BS as (-> & HCL1 & Hlt1 & Hb1 & En1 & Ed1 & _ & Ep1). destruct H1 as ((q1 & H1') & HP1).
    pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & Hbx1 & Hnl1 & Hnd1 & Hh1 & _).
    destruct (Z.ltb_spec (is_have s1) (is_nlen s1 + is_ndist s1)) as [LT1|GE1].
    + destruct H1' as (HL1 & HQ1).
      exact (IH X s1 c r1 q1 ms1 HL1 HQ1 XO HCL1 HP1 LT1 CHK ltac:(rewrite Nat2Z.inj_succ in RK; lia)).
    + destruct H1' as (HL1 & HQ1).
      rewrite codelens_while_stop by lia. cbn [CLPOST w_s w_r]. rewrite E1. change (CODELENS =? BAD) with false.
      apply evt_done. split; [exists q1; split; assumption| exact HP1].
  - destruct BS as (HM1 & _). cbn [CLPOST w_s w_r]. rewrite HM1. change (BAD =? BAD) with true. apply evt_done. exact H1.
  - apply evt_done. cbn [CLPOST]. exact H1.
  - destruct BS.
Qed.
Lemma cl_while : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_CODELENS_E q ms -> HCC X r q ->
  ix_ok X -> WINV (mkW s c r) -> ATY s -> PATI X (mkW s c r) -> is_mode s = CODELENS ->
  evt usegs (CLPOST X (codelens_while 321 (mkW s c r))) ms.
Proof.
  intros X s c r q ms HL HQ XO HW HA HP HM.
  pose proof (codelens_facts s c r HW HA HM) as (HCL & Hlt & _).
  pose proof (WINV_codelens_okb s c r HW HA HM) as OKB. unfold codelens_okb in OKB. cbn [w_s w_c w_r] in OKB.
  apply andb_prop in OKB. destruct OKB as [OKB _]. apply andb_prop in OKB. destruct OKB as [Rnd CHK]. apply Z.leb_le in Rnd.
  pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd' & Hh & HLs & HT & _).
  destruct (decode_okb_lvl1 _ _ _ _ _ _ ltac:(cbn [clw_chk] in CHK; replace (is_have s <? is_nlen s + is_ndist s) with true in CHK by (symmetry; apply Z.ltb_lt; lia); apply andb_prop in CHK; exact (proj1 CHK))) as [RN _].
  eapply evt_cut; [exact (cl_entry X s c r q ms HL HQ ltac:(lia) Hnl Hnd' RN (cpok_ofs_ok _ _ _ _ HT))|]. intros ms1 (q1 & H1).
  replace (is_have s <? is_nlen s + is_ndist s) with true in H1 by (symmetry; apply Z.ltb_lt; lia).
  destruct H1 as (HL1 & HQ1).
  exact (cl_loop 321 X s c r q1 ms1 HL1 HQ1 XO HCL HP Hlt CHK ltac:(cbn; lia)).
Qed.
