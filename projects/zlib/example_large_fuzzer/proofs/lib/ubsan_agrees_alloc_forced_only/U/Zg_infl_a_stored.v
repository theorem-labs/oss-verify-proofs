(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_infl_pure Z_infl_pure2 Z_infl_pure3 Z_updwin_pure Zh_kit Zg_infl_t_iface Z_ukit Z_infl_defs Zg_infl_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateA_HDR RefInflateA_STORED RefInflateA_COPY DeflateLz RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
(* [comment removed for export] *)
Lemma land24 : forall b, 0 <= b < 32 -> Z.land b 24 = b - Z.land b 7.
Proof.
  intros b Hb. destruct b as [|p|p]; [reflexivity| |lia].
  do 5 (destruct p as [p|p|]; try lia; try reflexivity).
Qed.

(* [comment removed for export] *)
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


Definition PC_STORED_NB : Z := 0x1f5ec.   (* [comment removed for export] *)
Definition PC_STORED_J : Z := 0x1f904.    (* [comment removed for export] *)

Definition SNQ (X : ictx) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X))
  /\ h25 q = wz (il_NI (ix_L X) + ir_next r) /\ h24 q = wz (ir_have r) /\ h15 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r).
Definition STQ (X : ictx) (r r1 : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X))
  /\ h14 q = wz (il_NI (ix_L X) + ir_next r1) /\ h12 q = wz (ir_have r1) /\ h18 q = wz (ir_bits r1) /\ h22 q = wz (ir_hold r1).

Definition PC_STORED_L : Z := 0x1f600.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STL (X : ictx) (r0 r : iregs) (q : iscrh) : Prop :=
  h12 q = wz (ir_have r) /\ h16 q = wz (il_NI (ix_L X) + ir_next r) /\ h6 q = wz (il_NI (ix_L X) + ir_next r)
  /\ h18 q = wz (ir_bits r) /\ h5 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
  /\ h24 q = wz (ir_have r0) /\ h25 q = wz (il_NI (ix_L X) + ir_next r0) /\ h15 q = wz (ir_bits r0)
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r0) /\ h10 q = wz (-2) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X)).

(* [comment removed for export] *)
Lemma stored_loop : forall f X s c r0 r q ms,
  ILOOPh X (mkW s c r) PC_STORED_L q ms -> STL X r0 r q ->
  ix_ok X -> REGS c r -> pulled r0 r -> 0 <= ir_have r0 < 2^31 -> 0 <= ir_bits r0 ->
  ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 -> ir_bits r < 32 -> 32 <= ir_bits r + 8 * Z.of_nat f ->
  evt usegs (NBGq X s c (NEEDBITS_k f 32 (mkW s c r)) PC_STORED_J (STQ X r0)) ms.
Proof.
  induction f as [|f IH]; intros X s c r0 r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HPL0 HAV0 HB0 Pin Pin1 HB Hf.
  { exfalso. cbn [Z.of_nat] in Hf. lia. }
  destruct HL as (m & -> & HMEM). unfold STL in HQ. hred_in HQ. cbn [w_s w_c w_r] in HMEM.
  destruct HQ as (E12 & E16 & E6 & E18 & E5 & E22 & E24 & E25 & E15 & E9 & E10 & E11 & E13). subst. hred.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  pose proof (pulled_cursor r0 r HPL0) as (PC1 & PC2 & PC3 & PC4 & PC5).
  pose proof (pulled_eqs r0 r HPL0) as (PE1 & PE2 & PE3 & PE4 & PE5).
  assert (HAV : ir_have r < 2^31) by lia.
  unfold PC_STORED_L. ix_open XO.
  zs. br_cases K.
  - (* [comment removed for export] *)
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r r HREGS (proj1 RB) (pulled_refl r Rh (conj RB RH)) ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5 & E6 & E3 & E4 & E7 & E8 & E9 & RH1).
    pose proof (pulled_trans r0 r (RefInflateArmLib.pullr c r) HB0 HPL0 HPL1) as HPL01.
    pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    do 2 zs. gT. do 2 zs. zs. clear RD. do 9 zs. rewrite <- Pin. rewrite !pull_shift by lia.
    zs. br_cases K3.
    + (* [comment removed for export] *)
      rewrite (NB_pull f 32 s c r) by lia.
      eapply IH; [ eapply ILOOPh_intro; try reflexivity
                 | unfold STL; hred; rewrite ?E1, ?E2, ?E5, ?E6; repeat split; ireg
                 | exact XO | exact HREGS1 | exact HPL01 | exact HAV0 | exact HB0 | exact Pin | exact Pin1 | rewrite E6; lia | rewrite E6; rewrite Nat2Z.inj_succ in Hf; lia ].
      eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
    + (* [comment removed for export] *)
      rewrite (NB_pull f 32 s c r) by lia. rewrite (NB_done f 32 s c (RefInflateArmLib.pullr c r)) by (rewrite E6; lia).
      zs. apply evt_done. left. eexists (RefInflateArmLib.pullr c r), _. split; [reflexivity|]. split.
      * eapply ILOOPh_intro; try reflexivity. eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
      * unfold STQ. hred. rewrite ?E1, ?E2, ?E5, ?E6. repeat split; ireg.
  - (* [comment removed for export] *)
    rewrite (NB_dry f 32 s c r) by lia.
    do 9 zs. rewrite land_ones32, shl3 by lia.
    apply evt_done. right. exists r. split; [reflexivity|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

(* [comment removed for export] *)
Lemma stored_nb32 : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_STORED_NB q ms -> SNQ X r q ->
  ix_ok X -> REGS c r -> PATG X (mkW s c r) -> ir_bits r <= 31 ->
  evt usegs (NBGq X s c (NEEDBITS 32 (mkW s c r)) PC_STORED_J (STQ X r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HP HB31.
  unfold SNQ in HQ. hred_in HQ. destruct HQ as (-> & -> & -> & -> & -> & -> & -> & ->).
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r] in *. hred.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  unfold PC_STORED_NB. ix_open XO. rewrite NB_top.
  do 5 zs.
  eapply (stored_loop 8%nat X s c r r);
    [ eapply ILOOPh_intro; try reflexivity; exact HMEM | unfold STL; hred; repeat split; ireg | exact XO
    | exact HREGS | exact (pulled_refl r Rh (conj RB RH)) | lia | lia | exact Pin | exact Pin1 | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Qed.

Section Stored.
Hypothesis COPY__CORE : copy__core_stmt.

(* [comment removed for export] *)
Lemma stored_tail : forall flush X s c r q ms,
  ILOOPh X (mkW s c r) PC_STORED_J q ms -> STQ X r r q ->
  ix_flush X = flush -> 0 <= flush <= 4 -> ix_ok X -> WINV (mkW s c r) -> PATG X (mkW s c r) -> is_mode s = STORED ->
  evt usegs (fun ms' => IPOST X (st_tail flush s c r) ms' /\ PATG X (wof (st_tail flush s c r))) ms.
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
  - (* [comment removed for export] *)
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
    assert (HP2 : PATG X w2).
    { unfold w2. eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold COPY_, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. exact HISR. }
    eapply (evt_cut usegs (fun ms' => exists x12', ILOOP X w2 PC_COPY_ x26 x12' ms')).
    2:{ intros ms1 (x12' & H1). exact (COPY__CORE X w2 _ x12' ms1 H1 XO HW2 HP2 eq_refl). }
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
  - (* [comment removed for export] *)
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
    + cbn [wof]. eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..| | bk_keep]. exact HISR.
Qed.

Lemma arm_STORED_of : forall flush, 0 <= flush <= 4 -> arm_stmtg flush STORED PC_STORED (arm_STORED ivar_ref flush).
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
  assert (HPb : PATG X (mkW s c (bb_r r))) by (eapply PATG_regs; [exact HP| assumption..]).
  (* [comment removed for export] *)
  eapply (evt_cut usegs (NBGq X s c (NEEDBITS 32 (mkW s c (bb_r r))) PC_STORED_J (STQ X (bb_r r)))).
  { destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
    assert (HMEMb : IMEM X (mkW s c (bb_r r)) m) by (eapply IMEM_regs; [exact HMEM| assumption..]).
    ix_open XO.
    unfold PC_STORED. do 4 zs. rewrite (land63_small (Z.land (ir_bits r) 7)) by lia. br_cases K.
    - (* [comment removed for export] *)
      zs. rewrite land_m8_u64 by lia. do 2 zs.
      apply evt_done. left. eexists (bb_r r), _. split; [|split].
      + apply nb_enough. rewrite B8. lia.
      + eapply ILOOPh_intro; [..| exact HMEMb]; ired; ireg.
      + unfold STQ. hred. rewrite ?B1, ?B2, ?B3, ?B4, ?B8, ?B9. repeat split; ireg.
    - (* [comment removed for export] *)
      zs. rewrite land24 by lia.
      eapply (stored_nb32 X s c (bb_r r));
        [eapply ILOOPh_intro; [..| exact HMEMb]; ired; ireg | unfold SNQ; hred; rewrite ?B1, ?B2, ?B3, ?B4, ?B8, ?B9; repeat split; ireg | exact XO | exact HREGSb | exact HPb | rewrite B8; lia]. }
  intros ms1 [(r1 & q1 & EN & HJ & HQ)|(r1 & EN & HLV)].
  2:{ rewrite (arm_STORED_dry flush s c r _ EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct (NBG_leave_facts c 32 s (bb_r r) r1 HREGSb ltac:(lia) EN) as (_ & HPL' & _). eapply PATG_pulled; [exact HPb| exact HPL']. }
  rewrite (arm_STORED_run flush s c r r1 EN).
  destruct (NEEDBITS_spec c 32 s (bb_r r) HREGSb ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & EIN & EOUT & ERET).
  assert (HP1 : PATG X (mkW s c r1)) by (eapply PATG_regs; [exact HPb| assumption..]).
  assert (HW1 : WINV (mkW s c r1)).
  { unfold WINV. cbn [w_s w_c w_r]. split; [exact HCORE|]. split; [exact HREGS1|].
    rewrite HM in HMF, HWF |- *. unfold MF, WF in *. cbn in HMF, HWF |- *. split; [exact HMF|]. split; [rewrite EOUT, B6; exact HWF| intros E; rewrite EPUT, B3; exact (HWB E)]. }
  assert (HQ1 : STQ X r1 r1 q1) by (unfold STQ in *; rewrite EPUT, B3; exact HQ).
  exact (stored_tail flush X s c r1 q1 ms1 HJ HQ1 EF RF XO HW1 HP1 HM).
Qed.
End Stored.
