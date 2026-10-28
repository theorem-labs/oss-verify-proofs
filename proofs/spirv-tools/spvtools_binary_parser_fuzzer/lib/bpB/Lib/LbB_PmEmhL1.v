From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem LbB_RwStm.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_Own LbB_HEmpStmt LbB_DStat.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmEmhW.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmEmh LbB_PmEmhF LbB_PmEmhI.

Section EmhL1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.

  Lemma emh_to_B_fw : forall m a w, fldw asegs m a 8 w -> fldA m a 8 (bv_unsigned w).
  Proof. intros m a w Hf. unfold fldw, fldA, fld in *. rewrite Z_to_bv_bv_unsigned. exact Hf. Qed.

  Lemma emh_to_B_fm8 : forall W m m' a v, fldA m a 8 v -> munch W m m' ->
    Forall (fun iv : Z * Z => a + 8 <= fst iv \/ snd iv <= a) W -> 0 <= a -> a + 8 < 2 ^ 64 -> fldA m' a 8 v.
  Proof.
    intros W m m' a v F MU D H0 H1.
    eapply fld_agree; [exact H0 | change (Z.of_nat 8) with 8; lia | exact F |].
    intros x Hx. unfold zwin in Hx. change (Z.of_nat 8) with 8 in Hx. apply MU. rewrite unsigned_lit by lia.
    eapply disjoint_outside; [exact (emh_keep_dj W a 8 D) | lia].
  Qed.

  Lemma emh_to_B_rd8 : forall m A cs (k : nat) z, rw_cells asegs m A cs -> cell_at cs k = Some (C8 (Z_to_bv 64 z)) ->
    fldA m (A + Z.of_nat k) 8 z.
  Proof.
    intros m A cs k z Hc Hk. unfold fldA, fld.
    pose proof (rw_cells_read asegs m A cs k _ Hc Hk) as RD. rewrite <- rdn_of_ov. exact RD.
  Qed.

  Lemma emh_to_B_rd4 : forall m A cs (k : nat) z, rw_cells asegs m A cs -> cell_at cs k = Some (C4 (Z_to_bv 64 z)) ->
    fldA m (A + Z.of_nat k) 4 z.
  Proof.
    intros m A cs k z Hc Hk. unfold fldA, fld.
    pose proof (rw_cells_read asegs m A cs k _ Hc Hk) as RD. rewrite <- rdn_of_ov. exact RD.
  Qed.

  Lemma emh_to_B_stk : forall m m' lo hi, stk asegs m lo hi -> wmono asegs m m' -> AIMG_TOP <= lo -> stk asegs m' lo hi.
  Proof.
    intros m m' lo hi (S0 & S1 & S) WM Hlo. split; [lia|]. split; [lia|]. intros a Ha.
    destruct (S a Ha) as [W _]. pose proof (WM _ W) as W'. split; [exact W'|].
    rewrite BakeStackRep.wview_high in W' by (unfold wa; rewrite unsigned_lit by (unfold AIMG_TOP in *; lia); lia).
    destruct (m' (wa a)) as [b|] eqn:E; [exists b; unfold mrd; rewrite E; reflexivity | congruence].
  Qed.

  Lemma emh_to_B_acc : forall m ff, fldA m (sh ff + 4) 1 0 -> 0 <= ff -> ff mod 64 = 0 -> ff + 40 <= AAPP_HI ->
    accessible m (ff + 32) 8.
  Proof.
    intros m ff F H0 H64 HA. pose proof (emh_release_flag0 m _ F) as R.
    split; [lia|]. split; [lia|]. intros x Hx. exists 0. split; [lia|]. split; [|left; reflexivity].
    replace (sh x) with (sh ff + 4); [exact R|]. unfold sh. Z.div_mod_to_equations. lia.
  Qed.

  Lemma emh_to_B_in : forall spz ff fp l h,
    (aceil <= l /\ h <= spz) \/ (as_FSB H <= l /\ h <= as_FSB H + AFS_FLAGS) \/ (fp <= l /\ h <= fp + 1)
    \/ (ff <= l /\ h <= ff + 128) \/ (sh ff <= l /\ h <= sh ff + 16) -> emh_in H spz ff fp (l, h).
  Proof.
    intros spz ff fp l h K. unfold emh_in, emh_W.
    destruct K as [K|[K|[K|[K|K]]]];
      [exists (aceil, spz) | exists (as_FSB H, as_FSB H + AFS_FLAGS) | exists (fp, fp + 1) | exists (ff, ff + fsz 1)
      | exists (sh ff, sh ff + fshn 1)];
      change (fsz 1) with 128; change (fshn 1) with 16; cbn [fst snd In];
      (split; [repeat (first [left; reflexivity | right]) | lia]).
  Qed.

  Lemma emh_to_B_blk : forall (Q : config -> Prop) s msF mo R F pc fc m ro R1 pc1 M1,
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F pc fc None m ro -> rfull R ->
    CatSim.msteps asegs (MS R F pc fc None m ro) (MS R1 F pc1 fc None M1 ro) ->
    (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> rfull R1 ->
       as_VIS H s msF' = MS R1 F pc1 fc None M1 ro -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHbp.
    intros Q s msF mo R F pc fc m ro R1 pc1 M1 KR VIS HF Hms K.
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    eapply (ah_lift H (rt_bp_base H HHbp) (fun ms => ms = MS R1 F pc1 fc None M1 ro)); [exact KR | exact VIS | |].
    - eapply evt_of_msteps_done; [exact Hms | reflexivity].
    - intros msF' mo' KR' MP' HP. exact (K msF' mo' KR' MP' HF1 HP).
  Qed.

  Lemma emh_to_B : forall I, emh_entry I mod 2 = 0 -> 0 <= emh_entry I < 2 ^ 32 -> emh_A I -> emh_B I -> emh_toB_stmt H I.
  Proof using HHbp.
    intros I EV ER EA EB. unfold emh_toB_stmt.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc msF m mo s LB LB0 LBm LF obj bl bc keyp key ents lo B shi errv.
    intros VIS0 FZ0 HA0 HA1 UM0 US0 PLB PLBm AD0 WR0 MLF OC OD KF0 KA0 SRC0 KLF KM KR ZL BCL
           RH0 KREL0 AL0 SMALL CNT LG ICMf TR RX0 SPB BB SP16 STK0 CEIL LO ERR0 MI0 TP RA0 AC0 RFS0 LFN RL0 S00 SPH OWN0.
    subst a0 a1.
    pose proof (rt_bp_base H HHbp) as HB.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    pose proof aceil_range as ACR.
    pose proof S00 as (g & G1 & G2 & G3 & G4).
    assert (S47 : bv_unsigned sp <= 2 ^ 47) by (unfold AAPP_HI in G2; lia).
    assert (LOE : lo <= bv_unsigned sp - 8544) by (unfold AEMH_STACK, AEMP_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia).
    assert (SPL : aceil + 8544 <= bv_unsigned sp) by lia.
    assert (LO0 : 0 <= lo) by (destruct STK0 as (K & _); exact K).
    assert (TOP : AIMG_TOP <= aceil) by (unfold AIMG_TOP; lia).
    assert (SQF : bv_unsigned sp - 80 <= emh_sq (bv_unsigned sp) /\ emh_sq (bv_unsigned sp) <= bv_unsigned sp - 64
                  /\ emh_sq (bv_unsigned sp) mod 32 = 0) by (unfold emh_sq; clear - SP16 SPL ACR; Z.div_mod_to_equations; lia).
    destruct SQF as (Q1 & Q2 & Q3).
    assert (UAR : fldA m AUAR_CELL 4 1).
    { pose proof (ACONST_uar m AC0) as [_ CU].
      pose proof (emh_to_B_rd4 m AUAR_CELL _ 0 1 CU eq_refl) as X. replace (AUAR_CELL + Z.of_nat 0) with AUAR_CELL in X by lia.
      exact X. }
    assert (WRA : wr_at asegs m (bv_unsigned sp - 64) 64).
    { assert (X0 : lo <= bv_unsigned sp - 64 <= bv_unsigned sp) by lia.
      destruct (stk_split asegs m lo (bv_unsigned sp - 64) (bv_unsigned sp) STK0 X0) as [_ X].
      pose proof (wr_at_of_stk asegs m _ _ X) as W. replace (bv_unsigned sp - (bv_unsigned sp - 64)) with 64 in W by lia.
      exact W. }
    destruct (EA (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 obj) (Z_to_bv 64 keyp) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6) F fc m obj (bv_unsigned sp) keyp (eq_sym (Z_to_bv_bv_unsigned sp)) eq_refl eq_refl AC0 UAR WRA
                 ltac:(lia) SP16)
      as (R1 & M1 & MS1 & MU1 & WM1 & FW20 & FW19 & FW18 & FW9 & FW8 & FW1 & A1 & A2 & A8 & A9 & A10 & A18 & A19 & A20 & AK).
    eapply emh_to_B_blk; [exact KREL0 | exact VIS0 | apply rfull_mkR | exact MS1 |].
    intros msF1 mo1 KR1 MP1 FR1 VIS1. rewrite (MS_full_eq _ _ _ _ _ _ FR1) in VIS1.
    assert (RF1 : as_RFS H LF M1).
    { apply (emh_rfs H HHbp LF m M1 _ (bv_unsigned sp) 0 0 RFS0 MU1 WM1 S47). intros iv [<-|[]]. left. cbn [fst snd]. lia. }
    assert (RH1 : as_RHEAP H s LB M1).
    { eapply (ah_RHEAP_frame H HB); [exact RH0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst]; lia | apply Forall_nil]. }
    pose proof (ah_thr H HB s LB M1 RH1) as THR1.
    assert (AC1 : ACONST M1).
    { apply (ACONST_frame _ m M1 AC0 MU1 WM1). apply Forall_cons; [apply emh_keep_achi; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ MS1 MI0).
    assert (US1 : bv_unsigned (getr R1 2) = emh_sq (bv_unsigned sp)) by (rewrite A2; apply wz_unsigned; lia).
    assert (STK1 : stk asegs M1 lo (bv_unsigned (getr R1 2))).
    { rewrite US1. destruct (stk_split asegs m lo (emh_sq (bv_unsigned sp)) (bv_unsigned sp) STK0 ltac:(lia)) as [X _].
      exact (emh_to_B_stk m M1 lo _ X WM1 ltac:(lia)). }
    assert (TP1 : getr R1 4 = Z_to_bv 64 ATP).
    { rewrite (AK 4%bv ltac:(unfold EMH_KEPT; cbn [In]; right; left; reflexivity)). exact TP. }
    assert (SM1 : stack_malloc_stmt_bp H 1 AFS_MALLOC_1) by (apply stack_malloc_bp_of_donor; exact (ah_fs1 H HB)).
    unfold stack_malloc_stmt_bp in SM1. cbn [Z.eqb Pos.eqb] in SM1.
    eapply (ah_lift H HB _ _ s msF1 _ mo1 KR1 VIS1).
    { apply (SM1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc M1 LF lo RF1 LFN STK1 CEIL);
        [rewrite US1; unfold AFS_STACK; lia | exact MI1 | exact TP1 | exact AC1 | exact THR1]. }
    intros msF2 mo2 KR2 MP2 P2.
    destruct P2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & ff & fp & junk1 & junk2
                    & E2 & MU2 & WM2 & MI2 & ST2 & RF2 & FRC & SHF & FLG & AC2).
    change (getr R1 1 = Z_to_bv 64 (emh_entry I + 88)) in A1.
    rewrite A1 in E2. rewrite ret_pc_even in E2 by (clear - EV ER; Z.div_mod_to_equations; lia).
    rewrite fsz_1, fshn_1 in MU2. rewrite US1 in MU2, ST2.
    pose proof (emh_fresh H HHbp LF m2 ff fp RF2) as FRESH.
    assert (A128 : aceil + 128 <= bv_unsigned sp) by lia.
    destruct (emh_place H HHbp LF m LB0 obj (bv_unsigned sp) ff fp RFS0 FRESH MLF A128 S47 SP16)
      as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & _).
    pose proof FRESH as ((K0 & K1 & K2 & (K3 & _) & K5 & K6) & (F0 & F1 & F2 & _) & _).
    change (fsz 1) with 128 in K2.
    assert (FF0 : 0 <= ff) by (unfold AIMG_TOP in P1; lia).
    assert (FSBB : as_FSB H + AFS_FLAGS <= aceil /\ ff + 128 <= aceil /\ 0 <= as_FSB H)
      by (unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in *; lia).
    assert (SHB : sh ff + 16 <= aceil /\ (sh ff + 16 <= ff \/ ff + 128 <= sh ff)).
    { unfold sh. rewrite ASHADOW_BASE_val. clear - P1 P3 P4 FSBB ACR. unfold AIMG_TOP in P1. Z.div_mod_to_equations. lia. }
    pose proof (munch_app _ _ _ _ _ MU1 MU2) as MUW1.
    pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WMW1.
    lazymatch type of MUW1 with munch ?W _ _ => assert (EIN1 : Forall (emh_in H (bv_unsigned sp) ff fp) W) end.
    { cbn [app]. repeat (apply Forall_cons; [apply emh_to_B_in; unfold AFS_STACK; lia|]). apply Forall_nil. }
    destruct (emh_keep H HHbp s LB LB0 LBm LF obj bl bc keyp key ents B lo shi (bv_unsigned sp) ff fp errv tp m m m2 _
                FRESH RFS0 MLF KLF RH0 PLB PLBm OC CEIL S47 TP MUW1 WMW1 EIN1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RLF2 & _).
    assert (WSQ : wr_at asegs m2 (emh_sq (bv_unsigned sp) + 8) 8).
    { assert (X0 : lo <= emh_sq (bv_unsigned sp) + 8 <= bv_unsigned sp) by lia.
      destruct (stk_split asegs m lo _ (bv_unsigned sp) STK0 X0) as [_ X].
      assert (X1 : emh_sq (bv_unsigned sp) + 8 <= emh_sq (bv_unsigned sp) + 16 <= bv_unsigned sp) by lia.
      destruct (stk_split asegs m _ (emh_sq (bv_unsigned sp) + 16) _ X X1) as [Y _].
      pose proof (wr_at_of_stk asegs m _ _ Y) as W.
      replace (emh_sq (bv_unsigned sp) + 16 - (emh_sq (bv_unsigned sp) + 8)) with 8 in W by lia.
      exact (wr_at_transport asegs m m2 _ _ W WMW1). }
    assert (WFF : wr_at asegs m2 ff 128) by (apply (rw_cells_wr_at asegs m2 ff _ 128 FRC); vm_compute; congruence).
    assert (WSH : wr_at asegs m2 (sh ff) 16) by (destruct SHF as (_ & _ & _ & WS); exact WS).
    assert (SQA : 2 ^ 46 <= emh_sq (bv_unsigned sp)) by lia.
    assert (SQB : emh_sq (bv_unsigned sp) + 16 <= 2 ^ 47) by lia.
    lazymatch type of E2 with _ = MS ?RR _ _ _ _ _ _ => set (R2 := RR) in E2 end.
    destruct (EB R2 F fc m2 ff (emh_sq (bv_unsigned sp)) keyp obj (bv_unsigned sp) eq_refl A2 A9 A18 A20 A8 A19 eq_refl
                 (RLF2 RL0) WSQ WFF WSH P1 P2 P3 P4 SQA SQB Q3)
      as (R3 & M3 & MS3 & MU3 & WM3 & KP3 & SH3 & B1 & B2 & B8 & B9 & B10 & B11 & B13 & B18 & B19 & B20 & BK).
    eapply emh_to_B_blk; [exact KR2 | exact E2 | unfold R2; apply rfull_mkR | exact MS3 |].
    intros msF3 mo3 KR3 MP3 FR3 VIS3. rewrite (MS_full_eq _ _ _ _ _ _ FR3) in VIS3.
    assert (KEPT : forall r, In r EMH_KEPT -> getr R3 r = getr (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 obj) (Z_to_bv 64 keyp)
                     a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) r).
    { intros r Hr. rewrite (BK r Hr), <- (AK r Hr). unfold EMH_KEPT in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; reflexivity. }
    assert (E8 : getr R3 8 = sp) by (rewrite B8; exact (Z_to_bv_bv_unsigned sp)).
    rewrite B1, B2, E8, B9, B10, B11, B13, B18, B19, B20 in VIS3.
    rewrite (KEPT 3%bv ltac:(unfold EMH_KEPT; cbn [In]; repeat (first [left; reflexivity | right]))) in VIS3.
    rewrite (KEPT 4%bv ltac:(unfold EMH_KEPT; cbn [In]; repeat (first [left; reflexivity | right]))) in VIS3.
    rewrite (KEPT 21%bv ltac:(unfold EMH_KEPT; cbn [In]; repeat (first [left; reflexivity | right]))) in VIS3.
    rewrite (KEPT 22%bv ltac:(unfold EMH_KEPT; cbn [In]; repeat (first [left; reflexivity | right]))) in VIS3.
    rewrite (KEPT 23%bv ltac:(unfold EMH_KEPT; cbn [In]; repeat (first [left; reflexivity | right]))) in VIS3.
    rewrite (KEPT 24%bv ltac:(unfold EMH_KEPT; cbn [In]; repeat (first [left; reflexivity | right]))) in VIS3.
    rewrite (KEPT 25%bv ltac:(unfold EMH_KEPT; cbn [In]; repeat (first [left; reflexivity | right]))) in VIS3.
    rewrite (KEPT 26%bv ltac:(unfold EMH_KEPT; cbn [In]; repeat (first [left; reflexivity | right]))) in VIS3.
    rewrite (KEPT 27%bv ltac:(unfold EMH_KEPT; cbn [In]; repeat (first [left; reflexivity | right]))) in VIS3.
    pose proof (munch_app _ _ _ _ _ MUW1 MU3) as MUW2.
    pose proof (wmono_trans asegs _ _ _ WMW1 WM3) as WMW2.
    assert (EIN2 : Forall (emh_in H (bv_unsigned sp) ff fp)
                     (([(bv_unsigned sp - 64, bv_unsigned sp)] ++ [(emh_sq (bv_unsigned sp) - AFS_STACK, emh_sq (bv_unsigned sp));
                       (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 128); (sh ff, sh ff + 16)])
                      ++ [(emh_sq (bv_unsigned sp) + 8, emh_sq (bv_unsigned sp) + 16); (ff, ff + 40); (sh ff, sh ff + 16)])).
    { apply Forall_app. split; [exact EIN1|].
      repeat (apply Forall_cons; [apply emh_to_B_in; lia|]). apply Forall_nil. }
    destruct (emh_keep H HHbp s LB LB0 LBm LF obj bl bc keyp key ents B lo shi (bv_unsigned sp) ff fp errv tp m m M3 _
                FRESH RFS0 MLF KLF RH0 PLB PLBm OC CEIL S47 TP MUW2 WMW2 EIN2)
      as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & _ & X12).
    assert (RF3 : as_RFS H ((1, ff, fp) :: LF) M3).
    { apply (emh_rfs H HHbp _ m2 M3 _ (bv_unsigned sp) ff fp RF2 MU3 WM3 S47).
      intros iv Hi. cbn [In] in Hi. change (fsz 1) with 128. change (fshn 1) with 16.
      destruct Hi as [<-|[<-|[<-|[]]]]; cbn [fst snd];
        [left; lia | right; split; [left; reflexivity | left; lia] | right; split; [left; reflexivity | right; lia]]. }
    pose proof (munch_app _ _ _ _ _ MU2 MU3) as MU23.
    assert (SVD : forall a, bv_unsigned sp - 48 <= a -> Forall (fun iv : Z * Z => a + 8 <= fst iv \/ snd iv <= a)
                    ([(emh_sq (bv_unsigned sp) - AFS_STACK, emh_sq (bv_unsigned sp)); (as_FSB H, as_FSB H + AFS_FLAGS);
                      (fp, fp + 1); (ff, ff + 128); (sh ff, sh ff + 16)]
                     ++ [(emh_sq (bv_unsigned sp) + 8, emh_sq (bv_unsigned sp) + 16); (ff, ff + 40); (sh ff, sh ff + 16)])).
    { intros a Ha. cbn [app]. repeat (apply Forall_cons; [cbn [fst snd]; unfold AFS_STACK; lia|]). apply Forall_nil. }
    assert (FP2 : fldA m2 (ff + 120) 8 fp) by exact (emh_to_B_rd8 m2 ff _ 120 fp FRC eq_refl).
    assert (FP3 : fldA M3 (ff + 120) 8 fp).
    { apply (emh_to_B_fm8 _ m2 M3 _ _ FP2 MU3); [| lia | lia].
      repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    apply (ah_done H HB). unfold emh_SB.
    exists (getr R3 5), (getr R3 6), (getr R3 7), (getr R3 12), (getr R3 14), (getr R3 15), (getr R3 16), (getr R3 17),
      (getr R3 28), (getr R3 29), (getr R3 30), (getr R3 31), M3, errv, ff, fp.
    split; [cbn [cfg_ms]; exact VIS3|].
    split; [exact FZ0|]. split; [exact KR3|].
    split; [cbn [cfg_model]; exact (ah_mpres_trans H HB _ _ _ (ah_mpres_trans H HB _ _ _ MP1 MP2) MP3)|].
    split; [exact FRESH|]. split; [exact RF3|].
    split; [exact (X1 UM0)|]. split; [exact (X2 US0)|]. split; [exact (X3 AD0)|].
    split; [exact (wr_at_transport asegs m M3 obj 40 WR0 WMW2)|].
    split; [exact (X4 KF0)|]. split; [exact (X5 KA0)|].
    split; [exact KP3|].
    split; [apply (emh_to_B_acc M3 ff SH3); [unfold AIMG_TOP in P1; lia | exact P3 | unfold AAPP_HI; lia]|].
    split; [exact X6|].
    split; [exact (Forall_impl _ (fun b Hb => wr_at_transport asegs m M3 _ _ Hb WMW2) OWN0)|].
    split; [exact (X7 RX0)|].
    split; [exact (emh_to_B_stk m M3 lo _ STK0 WMW2 ltac:(lia))|].
    split; [exact (X8 ERR0)|].
    split; [exact (msteps_mem_inv asegs _ _ MS3 MI2)|].
    split; [exact (X9 AC0)|]. split; [exact (X10 S00)|].
    split; [apply (emh_to_B_fm8 _ M1 M3 _ _ (emh_to_B_fw M1 _ _ FW1) MU23 (SVD (bv_unsigned sp - 8) ltac:(lia))); lia|].
    split; [apply (emh_to_B_fm8 _ M1 M3 _ _ (emh_to_B_fw M1 _ _ FW8) MU23 (SVD (bv_unsigned sp - 16) ltac:(lia))); lia|].
    split; [apply (emh_to_B_fm8 _ M1 M3 _ _ (emh_to_B_fw M1 _ _ FW9) MU23 (SVD (bv_unsigned sp - 24) ltac:(lia))); lia|].
    split; [apply (emh_to_B_fm8 _ M1 M3 _ _ (emh_to_B_fw M1 _ _ FW18) MU23 (SVD (bv_unsigned sp - 32) ltac:(lia))); lia|].
    split; [apply (emh_to_B_fm8 _ M1 M3 _ _ (emh_to_B_fw M1 _ _ FW19) MU23 (SVD (bv_unsigned sp - 40) ltac:(lia))); lia|].
    split; [apply (emh_to_B_fm8 _ M1 M3 _ _ (emh_to_B_fw M1 _ _ FW20) MU23 (SVD (bv_unsigned sp - 48) ltac:(lia))); lia|].
    split; [exact FP3|].
    split; [exact (wr_at_transport asegs m2 M3 fp 1 (rw_cells_wr_at asegs m2 fp _ 1 FLG ltac:(vm_compute; congruence)) WM3)|].
    split; [exact (wr_at_transport asegs m2 M3 ff 128 WFF WM3)|].
    split; [exact (wr_at_transport asegs m2 M3 (sh ff) 16 WSH WM3)|].
    exact X12.
  Qed.
End EmhL1.
