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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmEmh LbB_PmEmhF LbB_PmEmhI LbB_HEmpStmt.

Section EmhL2b.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.

  Lemma emh_rpc : forall z, z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
  Proof.
    intros z E.
    assert (Ez : Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64)).
    { apply bv_eq. rewrite !unsigned_lit_wrap. symmetry. apply Z.mod_mod. lia. }
    rewrite Ez. apply ret_pc_even; [apply Z.mod_pos_bound; lia|].
    Z.div_mod_to_equations. lia.
  Qed.

  Lemma emh_xwr : forall LB SP X m m' A n, xpres H LB SP X m m' -> xclient_range H LB SP X A n ->
    wr_at asegs m A n -> wr_at asegs m' A n.
  Proof.
    intros LB SP X m m' A n XP XR (W0 & W1 & W). split; [exact W0|]. split; [exact W1|].
    intros i Hi.
    exact (proj2 (XP (A + i) ltac:(lia) (xclient_range_addr H LB SP X A n (A + i) XR ltac:(lia))) (W i Hi)).
  Qed.

  Lemma emh_xfld : forall LB SP X m m' a k n v, xpres H LB SP X m m' -> xclient_range H LB SP X a n ->
    Z.of_nat k = n -> 0 <= a -> a + n < 2 ^ 64 -> fldA m a k v -> fldA m' a k v.
  Proof.
    intros LB SP X m m' a k n v XP XR E A0 A1 Fk. subst n. unfold fldA in *.
    eapply CRep.fld_agree; [exact A0 | exact A1 | exact Fk |].
    intros x Hx. unfold zwin in Hx.
    exact (emh_keep_ag H LB SP X m m' a (Z.of_nat k) XP XR A0 ltac:(lia) x ltac:(lia)).
  Qed.

  Lemma emh_xstk : forall LB SP X m m' lo hi, xpres H LB SP X m m' -> xclient_range H LB SP X lo (hi - lo) ->
    stk asegs m lo hi -> stk asegs m' lo hi.
  Proof.
    intros LB SP X m m' lo hi XP XR (S0 & S1 & S). split; [exact S0|]. split; [exact S1|].
    intros a Ha. destruct (S a Ha) as [W [b Hb]].
    destruct (XP a ltac:(lia) (xclient_range_addr H LB SP X lo (hi - lo) a XR ltac:(lia))) as [E WV].
    split; [exact (WV W)|]. exists b. unfold mrd in *. rewrite E. exact Hb.
  Qed.

  Lemma emh_xr_stk : forall LB SP obj A n, SP <= A -> obj + 40 <= A -> xclient_range H LB SP [(obj, obj + 40)] A n.
  Proof.
    intros LB SP obj A n L1 L2. unfold xclient_range, aclient_range. split; [left; exact L1|].
    apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
  Qed.

  Lemma emh_xr_fs : forall LB SP obj A n, as_FSB H <= A -> A + n <= as_FSB H + AFS_SIZE -> (A + n <= obj \/ obj + 40 <= A) ->
    xclient_range H LB SP [(obj, obj + 40)] A n.
  Proof.
    intros LB SP obj A n L1 L2 L3. unfold xclient_range, aclient_range. split; [do 4 right; left; lia|].
    apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
  Qed.

  Lemma emh_xr_sh : forall LB SP obj A n, sh (as_FSB H) <= A -> A + n <= sh (as_FSB H + AFS_SIZE) ->
    (A + n <= obj \/ obj + 40 <= A) -> xclient_range H LB SP [(obj, obj + 40)] A n.
  Proof.
    intros LB SP obj A n L1 L2 L3. unfold xclient_range, aclient_range. split; [do 5 right; left; lia|].
    apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
  Qed.

  Lemma emh_run_ret : forall I (Q : config -> Prop) s msF mo R F pc fc m R1 M1,
    emh_ret I -> as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F pc fc None m (seg_rom asegs) -> rfull R ->
    CatSim.msteps asegs (MS R F pc fc None m (seg_rom asegs)) (MS R1 F (Z_to_bv 64 (emh_entry I + 500)) fc None M1 (seg_rom asegs)) ->
    (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       as_VIS H s msF' = MS (mkR (getr R1 1) (getr R1 2) (getr R1 3) (getr R1 4) (getr R1 5) (getr R1 6) (getr R1 7) (getr R1 8)
                                 (getr R1 9) (getr R1 10) (getr R1 11) (getr R1 12) (getr R1 13) (getr R1 14) (getr R1 15) (getr R1 16)
                                 (getr R1 17) (getr R1 18) (getr R1 19) (getr R1 20) (getr R1 21) (getr R1 22) (getr R1 23) (getr R1 24)
                                 (getr R1 25) (getr R1 26) (getr R1 27) (getr R1 28) (getr R1 29) (getr R1 30) (getr R1 31))
                            F (ret_pc (getr R1 1)) fc None M1 (seg_rom asegs) ->
       Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHbp.
    intros I Q s msF mo R F pc fc m R1 M1 RT KR VIS HF HMS K.
    pose proof (msteps_full asegs _ _ HMS HF) as HF1. cbn [ms_regs] in HF1.
    eapply (ahh_evt H (rt_bp_base H HHbp)
      (fun ms => ms = MS (mkR (getr R1 1) (getr R1 2) (getr R1 3) (getr R1 4) (getr R1 5) (getr R1 6) (getr R1 7) (getr R1 8)
                              (getr R1 9) (getr R1 10) (getr R1 11) (getr R1 12) (getr R1 13) (getr R1 14) (getr R1 15) (getr R1 16)
                              (getr R1 17) (getr R1 18) (getr R1 19) (getr R1 20) (getr R1 21) (getr R1 22) (getr R1 23) (getr R1 24)
                              (getr R1 25) (getr R1 26) (getr R1 27) (getr R1 28) (getr R1 29) (getr R1 30) (getr R1 31))
                         F (ret_pc (getr R1 1)) fc None M1 (seg_rom asegs))); [exact KR | exact VIS | | exact K].
    eapply evt_of_msteps; [exact HMS|]. rewrite (MS_full_eq _ _ _ _ _ _ HF1). unfold emh_ret in RT. apply RT. reflexivity.
  Qed.

  Ltac emh_kp := unfold EMH_KEPT; cbn [In]; repeat (first [left; reflexivity | right]).

  Lemma emh_C_to_post : forall I, emh_entry I mod 2 = 0 -> emh_C I -> emh_ret I -> emh_Cpost_stmt H I.
  Proof using HHbp.
    intros I EV HC HRET. unfold emh_Cpost_stmt.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc msF m mo s LB LB0 LBm LF obj bl bc keyp key ents lo B shi errv.
    intros VIS0 FZ0 HA0 HA1 UM0 US0 PLB PLBm AD0 WR0 MLF OC OD KF0 KA0 SRC0 KLF KM KR ZL BCL
           RH0 KREL0 AL0 SM CNT LG ICMf TR RX0 SPB BB SP16 STK0 CEIL LO ERR0 MI0 TP RA0 AC0 RFS0 LFN RL0 S00 SPH OWN0.
    intros cf SC. destruct cf as [msF1 mo1]. unfold emh_SC in SC.
    destruct SC as (m1 & ff & fp & FR1 & STK1 & R1 & R2 & R3 & R4 & R5 & R6 & FP1 & WFP1 & WFF1 & WSH1 & XP1 & EP).
    destruct EP as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & s2' & LB2 & LBm2
      & F2 & fc2 & p & v & bl2 & bc2 & ents2 & ins & reh & VIS2 & FZ2 & KR2 & MP2 & MI2 & STK2 & ERR2 & RX2 & UM2 & US2 & AD2
      & WR2 & IN2 & INF2 & INT2 & RHF2 & RHT2 & RH2 & PLB2 & PLBm2 & OWN2 & XP2 & RFS2 & AC2 & S02 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, MP2.
    pose proof (rt_bp_base H HHbp) as HHb.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    pose proof aceil_range as ACR.
    assert (LO0 : 0 <= lo) by (destruct STK0 as (K & _); exact K).
    unfold AEMH_STACK, AEMP_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    assert (A128 : aceil + 128 <= bv_unsigned sp) by lia.
    assert (QS : bv_unsigned sp - 80 <= emh_sq (bv_unsigned sp) <= bv_unsigned sp - 64)
      by (clear - SP16; unfold emh_sq; Z.div_mod_to_equations; lia).
    assert (SQ : bv_unsigned (Z_to_bv 64 (emh_sq (bv_unsigned sp))) = emh_sq (bv_unsigned sp)) by (apply wz_unsigned; lia).
    rewrite SQ in STK2, XP2.
    pose proof S00 as (g & G1 & G2 & G3 & G4).
    assert (S47 : bv_unsigned sp <= 2 ^ 47) by (unfold AAPP_HI in G2; lia).
    destruct (emh_place H HHbp LF m LB0 obj (bv_unsigned sp) ff fp RFS0 FR1 MLF A128 S47 SP16)
      as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & _).
    pose proof (fresh_frame_facts H LF 1 ff fp FR1) as (_ & _ & FA & _ & FM8 & _ & _ & FL1 & FL2 & FF1 & FF2 & _ & FSA & FAP).
    change (fsz 1) with 128 in FA, FF2.
    pose proof (aapp_bounds (as_FSB H) AFS_SIZE FAP ltac:(unfold AFS_SIZE; lia)) as (_ & _ & FB & FB0 & _).
    assert (CK : 0 <= AFS_FLAGS /\ AFS_FLAGS <= AFS_HDR <= AFS_SIZE) by (unfold AFS_FLAGS, AFS_HDR, AFS_SIZE; lia).
    destruct (emh_keep_fo H HHbp LF m obj 40 RFS0 ltac:(lia) MLF) as (_ & O1 & O2 & _).
    assert (FD : ff + 128 <= obj \/ obj + 40 <= ff).
    { destruct MLF as (f & Hf & L1 & L2). pose proof FR1 as (_ & _ & FDJ). destruct (FDJ f Hf) as [D _].
      change (fsz 1) with 128 in D. lia. }
    pose proof (sh_add8 ff 16) as SA16.
    pose proof (sh_below_aceil (ff + 8 * 16) ltac:(lia)) as SBA.
    pose proof (sh_mono (as_FSB H) ff ltac:(lia)) as SM1.
    pose proof (sh_mono (ff + 8 * 16) (as_FSB H + AFS_SIZE) ltac:(lia)) as SM2.
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE ff 128 FAP ltac:(lia) ltac:(lia) ltac:(lia)) as SDJ.
    change (nsh 128) with 16 in SDJ.
    assert (WSH2 : wr_at asegs m2 (sh ff) 16) by (eapply emh_xwr; [exact XP2 | apply emh_xr_sh; lia | exact WSH1]).
    assert (WFF2 : wr_at asegs m2 ff 8).
    { assert (W : wr_at asegs m2 ff 128) by (eapply emh_xwr; [exact XP2 | apply emh_xr_fs; lia | exact WFF1]).
      destruct W as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi. apply W. lia. }
    assert (WFP2 : wr_at asegs m2 fp 1) by (eapply emh_xwr; [exact XP2 | apply emh_xr_fs; lia | exact WFP1]).
    assert (FP2 : fldA m2 (ff + 120) 8 fp)
      by (apply (emh_xfld LB0 _ _ m1 m2 _ 8%nat 8 _ XP2); [apply emh_xr_fs; lia | reflexivity | lia | lia | exact FP1]).
    assert (R1' : fldA m2 (bv_unsigned sp - 8) 8 (bv_unsigned ra))
      by (apply (emh_xfld LB0 _ _ m1 m2 _ 8%nat 8 _ XP2); [apply emh_xr_stk; lia | reflexivity | lia | lia | exact R1]).
    assert (R2' : fldA m2 (bv_unsigned sp - 16) 8 (bv_unsigned s0))
      by (apply (emh_xfld LB0 _ _ m1 m2 _ 8%nat 8 _ XP2); [apply emh_xr_stk; lia | reflexivity | lia | lia | exact R2]).
    assert (R3' : fldA m2 (bv_unsigned sp - 24) 8 (bv_unsigned s1))
      by (apply (emh_xfld LB0 _ _ m1 m2 _ 8%nat 8 _ XP2); [apply emh_xr_stk; lia | reflexivity | lia | lia | exact R3]).
    assert (R4' : fldA m2 (bv_unsigned sp - 32) 8 (bv_unsigned s2))
      by (apply (emh_xfld LB0 _ _ m1 m2 _ 8%nat 8 _ XP2); [apply emh_xr_stk; lia | reflexivity | lia | lia | exact R4]).
    assert (R5' : fldA m2 (bv_unsigned sp - 40) 8 (bv_unsigned s3))
      by (apply (emh_xfld LB0 _ _ m1 m2 _ 8%nat 8 _ XP2); [apply emh_xr_stk; lia | reflexivity | lia | lia | exact R5]).
    assert (R6' : fldA m2 (bv_unsigned sp - 48) 8 (bv_unsigned s4))
      by (apply (emh_xfld LB0 _ _ m1 m2 _ 8%nat 8 _ XP2); [apply emh_xr_stk; lia | reflexivity | lia | lia | exact R6]).
    assert (STKb : stk asegs m2 (emh_sq (bv_unsigned sp)) (bv_unsigned sp)).
    { eapply emh_xstk; [exact XP2 | apply emh_xr_stk; lia |].
      destruct STK1 as (K1 & K2 & K3). split; [lia|]. split; [lia|]. intros x Hx. apply K3. lia. }
    assert (STKa : stk asegs m2 lo (bv_unsigned sp)).
    { eapply stk_merge; [exact STK2 | exact STKb |]. split; lia. }
    assert (INB : In (p, 24) (lbl LBm2)).
    { apply (Permutation_in _ (Permutation_sym PLBm2)). unfold umap_blocks. apply in_or_app. right. apply in_map_iff.
      exists (p, (key, v)). split; [reflexivity | exact IN2]. }
    assert (SUB2 : forall b, In b LBm2 -> In b LB2)
      by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PLB2 | apply in_or_app; right; exact Hb]).
    destruct (emh_keep_blk H HHbp s2' LB2 LBm2 m2 p 24 RH2 SUB2 INB) as ((B0 & B1 & _ & _ & _ & _ & B6) & _).
    pose proof (aapp_bounds p 24 B6 ltac:(lia)) as (_ & _ & PB & _).
    unfold AAPP_HI in PB.
    assert (PM : p mod 8 = 0) by (clear - B1; Z.div_mod_to_equations; lia).
    rewrite (emh_rpc (emh_entry I + 296) ltac:(clear - EV; Z.div_mod_to_equations; lia)) in VIS2.
    lazymatch type of VIS2 with _ = MS ?RR _ _ _ _ _ _ => set (R := RR) in VIS2 end.
    destruct (HC R F2 fc2 m2 p (emh_sq (bv_unsigned sp)) (bv_unsigned sp) ff fp (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1)
                (bv_unsigned s2) (bv_unsigned s3) (bv_unsigned s4)
                eq_refl eq_refl eq_refl ltac:(unfold R, wz; rewrite Z_to_bv_bv_unsigned; reflexivity) eq_refl eq_refl eq_refl eq_refl
                WSH2 WFF2 FP2 WFP2 R1' R2' R3' R4' R5' R6' ltac:(lia) ltac:(lia) PM
                P1 P2 P3 P4 P5 P6 P7 ltac:(lia) S47 SP16 ltac:(lia) ltac:(lia))
      as (R' & M' & HMS & MU & WM & FL & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & KP).
    eapply (emh_run_ret I _ s2' msF1 mo1 R F2 _ fc2 m2 R' M' HRET KR2 VIS2 ltac:(unfold R; apply rfull_mkR) HMS).
    intros msF' mo' KR' MP' VIS'.
    assert (FW : Forall (emh_in H (bv_unsigned sp) ff fp) [(sh ff, sh ff + 16); (ff, ff + 8); (fp, fp + 1)]).
    { unfold emh_in, emh_W. repeat apply Forall_cons; try apply Forall_nil; hnf.
      - exists (sh ff, sh ff + fshn 1).
        split; [cbn [In]; do 4 right; left; reflexivity | cbn [fst snd]; change (fshn 1) with 16; lia].
      - exists (ff, ff + fsz 1). split; [cbn [In]; do 3 right; left; reflexivity | cbn [fst snd]; change (fsz 1) with 128; lia].
      - exists (fp, fp + 1). split; [cbn [In]; do 2 right; left; reflexivity | cbn [fst snd]; lia]. }
    destruct (emh_keep H HHbp s2' LB2 LB0 LBm2 LF obj bl2 bc2 keyp key ents2 B lo shi (bv_unsigned sp) ff fp errv2 tp m m2 M' _
                FR1 RFS0 MLF KLF RH2 PLB2 PLBm2 OC CEIL S47 TP MU WM FW)
      as (UMk & USk & ADk & _ & _ & RHk & RXk & ERk & ACk & S0k & _ & XPk).
    unfold emh_post.
    exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14), (getr R' 15),
      (getr R' 16), (getr R' 17), (getr R' 28), (getr R' 29), (getr R' 30), (getr R' 31), M', errv2, s2', LB2, LBm2, F2, fc2,
      p, v, bl2, bc2, ents2, ins, reh, [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)].
    cbn [cfg_ms cfg_model].
    split.
    { rewrite VIS', E1, E2, E8, E9, E10, E18, E19, E20.
      rewrite (KP 3%bv ltac:(emh_kp)), (KP 4%bv ltac:(emh_kp)), (KP 21%bv ltac:(emh_kp)), (KP 22%bv ltac:(emh_kp)),
        (KP 23%bv ltac:(emh_kp)), (KP 24%bv ltac:(emh_kp)), (KP 25%bv ltac:(emh_kp)), (KP 26%bv ltac:(emh_kp)),
        (KP 27%bv ltac:(emh_kp)).
      unfold wz. rewrite !Z_to_bv_bv_unsigned. reflexivity. }
    split; [exact FZ2|]. split; [exact KR'|].
    split; [exact (ah_mpres_trans H HHb _ _ _ MP2 MP')|].
    split; [exact (msteps_mem_inv asegs _ _ HMS MI2)|].
    split.
    { eapply stk_transport_disjoint; [exact STKa | exact MU | exact WM |]. apply emh_keep_dj.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
    split; [exact (ERk ERR2)|]. split; [exact (RXk RX2)|].
    split; [exact (UMk UM2)|]. split; [exact (USk US2)|]. split; [exact (ADk AD2)|].
    split; [exact (wr_at_wmono _ _ _ _ WR2 WM)|].
    split; [exact IN2|]. split; [exact INF2|]. split; [exact INT2|]. split; [exact RHF2|]. split; [exact RHT2|].
    split; [exact RHk|]. split; [exact PLB2|]. split; [exact PLBm2|].
    split; [exact (lb_own_wmono _ _ _ OWN2 WM)|].
    split.
    { repeat apply Forall_cons; try apply Forall_nil; unfold fs_scratch.
      - left. reflexivity.
      - right. exists 1, ff, fp. split; [exact FR1 | right; left; reflexivity].
      - right. exists 1, ff, fp. split; [exact FR1 | left; reflexivity].
      - right. exists 1, ff, fp. split; [exact FR1 | right; right; reflexivity]. }
    split.
    { apply (xpres_trans H _ _ _ m m1 M'); [| apply (xpres_trans H _ _ _ m1 m2 M')].
      - eapply xpres_weaken; [exact XP1 | lia | intros b K; exact K | intros a K; exact (or_intror K)].
      - eapply xpres_weaken; [exact XP2 | lia | intros b K; exact K | intros a [K|[]]; exact (or_introl K)].
      - eapply xpres_weaken; [exact XPk | lia | intros b K; exact K | intros a K; exact (or_intror K)]. }
    split; [exact (emh_release H HHbp LF m2 M' ff fp RFS2 MU WM FL)|].
    split; [exact (ACk AC2)|]. split; [exact (S0k S02)|]. exact AL2.
  Qed.
End EmhL2b.
