(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_infl_pure Z_infl_pure2 Z_adler32 Zh_kit Zg_infl_a_type Zg_infl_a_dict Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH ZIface AdlerModel InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateA_DICT DeflateLz RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_DICTID_J : Z := 0x1f7bc.    (* [comment removed for export] *)

Definition DIQ (X : ictx) (r r1 : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X))
  /\ h12 q = wz (il_NI (ix_L X) + ir_next r1) /\ h10 q = wz (ir_have r1) /\ h22 q = wz (ir_hold r1).

Definition PC_DICTID_L : Z := 0x1f578.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition DIL (X : ictx) (r0 r : iregs) (q : iscrh) : Prop :=
  h10 q = wz (ir_have r) /\ h14 q = wz (il_NI (ix_L X) + ir_next r) /\ h16 q = wz (il_NI (ix_L X) + ir_next r)
  /\ h17 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
  /\ h24 q = wz (ir_have r0) /\ h25 q = wz (il_NI (ix_L X) + ir_next r0) /\ h18 q = wz (ir_bits r0)
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r0) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X)).

(* [comment removed for export] *)
Lemma dictid_loop : forall f X s c r0 r q ms,
  ILOOPh X (mkW s c r) PC_DICTID_L q ms -> DIL X r0 r q ->
  ix_ok X -> REGS c r -> pulled r0 r -> 0 <= ir_have r0 < 2^31 -> 0 <= ir_bits r0 ->
  ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 -> ir_bits r < 32 -> 32 <= ir_bits r + 8 * Z.of_nat f ->
  evt usegs (NBGq X s c (NEEDBITS_k f 32 (mkW s c r)) PC_DICTID_J (DIQ X r0)) ms.
Proof.
  induction f as [|f IH]; intros X s c r0 r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HREGS HPL0 HAV0 HB0 Pin Pin1 HB Hf.
  { exfalso. cbn [Z.of_nat] in Hf. lia. }
  destruct HL as (m & -> & HMEM). unfold DIL in HQ. hred_in HQ. cbn [w_s w_c w_r] in HMEM.
  destruct HQ as (E10 & E14 & E16 & E17 & E22 & E24 & E25 & E18 & E9 & E11 & E13). subst. hred.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  pose proof (pulled_cursor r0 r HPL0) as (PC1 & PC2 & PC3 & PC4 & PC5).
  pose proof (pulled_eqs r0 r HPL0) as (PE1 & PE2 & PE3 & PE4 & PE5).
  assert (HAV : ir_have r < 2^31) by lia.
  unfold PC_DICTID_L. ix_open XO.
  zs. br_cases K.
  - (* [comment removed for export] *)
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r r HREGS (proj1 RB) (pulled_refl r Rh (conj RB RH)) ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5 & E6 & E3 & E4 & E7 & E8 & E9 & RH1).
    pose proof (pulled_trans r0 r (RefInflateArmLib.pullr c r) HB0 HPL0 HPL1) as HPL01.
    pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    do 2 zs. gT. zs. zs. clear RD. do 9 zs. rewrite <- Pin. rewrite !pull_shift by lia.
    zs. br_cases K3.
    + (* [comment removed for export] *)
      rewrite (NB_pull f 32 s c r) by lia.
      eapply IH; [ eapply ILOOPh_intro; try reflexivity
                 | unfold DIL; hred; rewrite E1, E2, E5, E6; repeat split; ireg
                 | exact XO | exact HREGS1 | exact HPL01 | exact HAV0 | exact HB0 | exact Pin | exact Pin1 | rewrite E6; lia | rewrite E6; rewrite Nat2Z.inj_succ in Hf; lia ].
      eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
    + (* [comment removed for export] *)
      rewrite (NB_pull f 32 s c r) by lia. rewrite (NB_done f 32 s c (RefInflateArmLib.pullr c r)) by (rewrite E6; lia).
      zs. apply evt_done. left. eexists (RefInflateArmLib.pullr c r), _. split; [reflexivity|]. split.
      * eapply ILOOPh_intro; try reflexivity. eapply IMEM_regs; [exact HMEM| symmetry; assumption..].
      * unfold DIQ. hred. rewrite ?E1, ?E2, ?E5, ?E6. repeat split; ireg.
  - (* [comment removed for export] *)
    rewrite (NB_dry f 32 s c r) by lia.
    do 10 zs. rewrite land_ones32, shl3 by lia.
    apply evt_done. right. exists r. split; [reflexivity|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

(* [comment removed for export] *)
Lemma dictid_nb32 : forall X s c r x26 x12 ms,
  ILOOP X (mkW s c r) PC_DICTID x26 x12 ms ->
  ix_ok X -> REGS c r -> PATG X (mkW s c r) ->
  evt usegs (NBGq X s c (NEEDBITS 32 (mkW s c r)) PC_DICTID_J (DIQ X r)) ms.
Proof.
  intros X s c r x26 x12 ms HL XO HREGS HP.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  pose proof (REGS_hold64 c r HREGS) as RH64.
  unfold PC_DICTID. ix_open XO. rewrite NB_top.
  do 2 zs. br_cases K.
  - (* [comment removed for export] *)
    rewrite (NB_done 8 32 s c r) by lia.
    do 2 zs. apply evt_done. left. eexists r, _. split; [reflexivity|]. split.
    + eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
    + unfold DIQ. hred. repeat split; reflexivity.
  - do 4 zs.
    eapply (dictid_loop 8%nat X s c r r);
      [ eapply ILOOPh_intro; try reflexivity; exact HMEM | unfold DIL; hred; repeat split; ireg | exact XO
      | exact HREGS | exact (pulled_refl r Rh (conj RB RH)) | lia | lia | exact Pin | exact Pin1 | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Qed.

Local Ltac close_mem j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

(* [comment removed for export] *)
Lemma dictid_core : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_DICTID_J q ms -> DIQ X r r q ->
  ix_ok X -> REGS c r -> PATG X (mkW s c r) ->
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

Lemma arm_DICTID_ok : forall flush, 0 <= flush <= 4 -> arm_stmtg flush DICTID PC_DICTID (arm_DICTID ivar_ref flush).
Proof.
  intros flush RF X [s c r] x12 ms EF HL XO HW _ HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HISR : ISR s) by (split; assumption).
  assert (HPUT0 : ir_put r = 0) by (apply (NOPUTb_false _ _ (PATG_noput _ _ _ _ HP)); left; exact HM).
  rewrite HM in HMF, HWF. unfold MF, WF in HMF, HWF. cbn in HMF, HWF. destruct HMF as [HWB0 HCK].
  (* [comment removed for export] *)
  eapply evt_cut; [exact (dictid_nb32 X s c r _ x12 ms HL XO HREGS HP)|].
  intros ms1 [(r1 & q1 & EN & HJ & HQ)|(r1 & EN & HLV)].
  2:{ rewrite (arm_DICTID_dry flush s c r _ EN). apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct (NBG_leave_facts c 32 s r r1 HREGS ltac:(lia) EN) as (_ & HPL' & _). eapply PATG_pulled; [exact HP| exact HPL']. }
  rewrite (arm_DICTID_run flush s c r r1 EN).
  destruct (NEEDBITS_spec c 32 s r HREGS ltac:(lia)) as [(r' & EN' & HREGS1 & HPL & _)|(r' & EN' & _)]; [|rewrite EN in EN'; discriminate EN'].
  rewrite EN in EN'. injection EN' as <-.
  destruct HPL as (k & _ & _ & _ & _ & _ & _ & _ & EPUT & ELEFT & EIN & EOUT & ERET).
  assert (HP1 : PATG X (mkW s c r1)) by (eapply PATG_regs; [exact HP| assumption..]).
  assert (HQ1 : DIQ X r1 r1 q1) by (unfold DIQ in *; rewrite EPUT; exact HQ).
  eapply evt_cut; [exact (dictid_core X s c r1 q1 ms1 HJ HQ1 XO HREGS1 HP1)|].
  intros ms2 (q2 & H2 & HQ2).
  apply (dict_core11 flush X _ q2 ms2 EF RF H2 HQ2 XO).
  - (* [comment removed for export] *)
    unfold WINV. cbn [w_s w_c w_r]. split; [exact HCORE|]. split.
    { destruct HREGS1 as (Rn & Rh & Rnh & Rp & Rl & Rpl & _ & Rin & Rli & Rlo). unfold REGS, HB. ired. change (2 ^ 0) with 1.
      split; [exact Rn|]. split; [exact Rh|]. split; [exact Rnh|]. split; [exact Rp|]. split; [exact Rl|]. split; [exact Rpl|]. split; [lia|]. split; [exact Rin|]. split; [exact Rli| exact Rlo]. }
    ired. unfold MF, WF. cbn. split; [split; [exact HWB0| lia]|]. split; [rewrite EOUT; exact HWF| intros E; rewrite EPUT; exact HPUT0].
  - eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold DICT, FLAGS, HCRC; cbn; lia| reflexivity..| |exact HISR| bk_keep].
    ired. rewrite EPUT, HPUT0. reflexivity.
  - reflexivity.
Qed.
