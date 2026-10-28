(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface RtB_IMemset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DPdK LbB_PmXp.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_WoGen LbB_ExDefs LbB_ExKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Notation PD_SHB := LbB_DPdK.PD_SHB (only parsing).

Definition kst_ex : list kentry :=
  [ KImg 0x17e000 0x186000; KWord (SA (ELit 0) SHCELL) 8 (ELit SHBASE); KWord (SA (ELit 0) AUAR_CELL) 4 (ELit 1);
    KWr (SA (EVar 58) (-8192)) (ELit 8216); KRange (EVar 58) (2 ^ 45) (2 ^ 47);
    KWr (SA (EVar 52) 0) (ELit 504); KRange (EVar 52) 0x6e8000 (2 ^ 47 - 512);
    KWr (SA PD_SHB SHBASE) (ELit 64);
    KDisj (SA (EVar 52) 0) (ELit 504) (SA (EVar 58) (-8192)) (ELit 8216);
    KDisj (SA PD_SHB SHBASE) (ELit 64) (SA (EVar 58) (-8192)) (ELit 8216);
    KDisj (SA PD_SHB SHBASE) (ELit 64) (SA (EVar 52) 0) (ELit 512) ].

Lemma ftbl_xpres {HCEIL : HeapCeil} : forall (H : asr) LB SP X W B m m' tbl,
  ftbl W B m tbl -> xpres H LB SP X m m' ->
  (forall k w, In (k, w) (fkeys tbl) -> xclient_range H LB SP X (B + k) (Z.of_nat w)) ->
  ftbl W B m' tbl.
Proof.
  intros H LB SP X W B m m' tbl FT XP XR. unfold ftbl in *. apply Forall_forall. intros [[k w] e] Hi.
  pose proof (proj1 (Forall_forall _ _) FT (k, w, e) Hi) as R. cbn beta iota in R |- *.
  eapply xpres_rw_cells; [exact XP | exact R |].
  cbn [cells_size csize]. rewrite Nat.add_0_r. exact (XR k w (fkeys_In tbl k w e Hi)).
Qed.

Section XT.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable e : xent H.
  Variables (ff fp : Z).

  Variables (p1 n1 p2 n2 : Z).
  Hypothesis HP : xpre H e.
  Hypothesis FF : fresh_frame H (x_LF e) 3 ff fp.

  Hypothesis THI : obj_inframe (x_LF e) (x_this e) 288.
  Hypothesis PCI : obj_inframe (x_LF e) (x_pcons e) 48.

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.
  Notation SP := (xSP e) (only parsing).
  Notation this := (x_this e) (only parsing).
  Notation pcons := (x_pcons e) (only parsing).

  Definition Wx : list word :=
    [Z_to_bv 64 this; x_sp e; x_ra e; Z_to_bv 64 (x_ioff e); Z_to_bv 64 (x_opc e); Z_to_bv 64 (x_ty e);
     x_s0 e; x_s1 e; x_s2 e; x_s3 e; x_s4 e; x_s5 e; x_s6 e; x_s7 e; x_s8 e; x_s9 e; x_s10 e; x_s11 e; x_gp e; x_tp e;
     Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 pcons; Z_to_bv 64 (x_icount e); Z_to_bv 64 (x_nwords e); Z_to_bv 64 (x_widx e);
     Z_to_bv 64 (xS1 e); Z_to_bv 64 p1; Z_to_bv 64 n1; Z_to_bv 64 p2; Z_to_bv 64 n2].

  Definition Px (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (m : mem) : Prop := xinv H e ff fp XSc sk LBk m.

  Lemma ex_ranges :
    0 <= SP < 2 ^ 64 /\ aceil + AEX_STACK <= SP /\ SP <= AAPP_HI
    /\ as_FSB H + AFS_HDR <= ff /\ ff + 512 <= as_FSB H + AFS_SIZE /\ ff mod 64 = 0
    /\ as_FSB H + AFS_FLAGS <= fp < as_FSB H + AFS_HDR
    /\ AIMG_TOP <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ as_FSB H mod 4096 = 0
    /\ (as_FSB H + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= as_FSB H)
    /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000.
Proof using HP FF.
    pose proof (xframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & _).
    pose proof (xpre_geo H e HP) as (CE & LO & SH1 & SH2 & _ & _).
    pose proof FF as (_ & (A1 & A2 & A3 & A4) & _).
    pose proof aceil_facts as ACF.
    assert (AP : as_FSB H + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= as_FSB H) by (destruct F10 as [[_ X]|[X _]]; [left | right]; lia).
    clear F10 A4.
    unfold AEX_STACK, ADS_STACK, AAPP_HI, AFS_HDR, AFS_FLAGS, AIMG_TOP in *.
    repeat split; try assumption; lia.
Qed.

  Lemma ex_vals : 0 <= ff < 2 ^ 64 /\ 0 <= fp < 2 ^ 64 /\ 0 < this /\ this + 288 <= 2 ^ 47 /\ this mod 8 = 0
    /\ 0 < pcons /\ pcons + 48 <= 2 ^ 47.
Proof using HP FF.
    pose proof (xframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
    pose proof aceil_facts as ACF.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & THO & _ & _ & _ & _ & _ & _ & _ & PCO & _).
    destruct THO as (_ & T8 & _ & T0 & T1 & _). destruct PCO as (_ & _ & _ & P0 & P1 & _).
    clear - F1 F2 F4 F5 F6 F8 ACF T8 T0 T1 P0 P1. repeat split; try assumption; lia.
Qed.
  Lemma ex_wins : ff + 512 <= xS1 e - 8192 /\ ff / 8 + SHBASE + 64 <= xS1 e - 8192
    /\ (ff + 512 <= ff / 8 + SHBASE \/ ff / 8 + SHBASE + 64 <= ff) /\ 0 <= ff / 8 /\ x_lo e <= xS1 e - 8192
    /\ xS1 e + 24 <= SP - 104 /\ 2 ^ 45 <= xS1 e /\ xS1 e + 24 <= 2 ^ 47.
Proof using HP FF.
    pose proof (xframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (xS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof aceil_facts as ACF.
    assert (E : ff / 8 + SHBASE = sh ff) by (unfold sh, SHBASE; rewrite ASHADOW_BASE_val; lia).
    assert (Q : 0 <= ff / 8) by (apply Z.div_pos; lia).
    rewrite E. clear - F2 F6 F7 F15 F16 S1SP S1L SPH LOS1 CE ACF Q.
    split; [lia|]. split; [lia|]. split; [destruct F16; [right | left]; lia|]. split; [exact Q|]. lia.
Qed.

  Lemma xobj_range : forall XSc O n, obj_inframe (x_LF e) O n -> 0 <= n -> O mod 8 = 0 ->
    Forall (fs_scratch H (x_LF e)) XSc ->
    xclient_range H (x_LB e) SP ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XE H ff fp ++ XSc) O n
    /\ xclient_range H (x_LB e) SP ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XE H ff fp ++ XSc) (sh O) (nsh n).
Proof using HHbp HP FF.
    intros XSc O n OI Hn O8 FS.
    pose proof (rt_bp_base H HHbp) as HB.
    pose proof (xframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RF0 & _).
    pose proof OI as (f & IN & D1 & D2).
    pose proof (proj2 (ah_RFS_range H HB _ _ RF0) f IN) as (K' & Q1 & Q2 & Q3 & Q4).
    pose proof (fsz_pos (ff_class f) ltac:(lia)) as FZ.
    pose proof FF as (_ & (A1 & A2 & A3 & A4) & _).
    assert (OB : fsobj H (x_LF e) O n) by (right; exists f; auto).
    unfold AFS_HDR in Q1.
    assert (R1 : as_FSB H + 0x9000 <= O /\ O + n <= as_FSB H + AFS_SIZE) by lia.
    assert (R0 : 0 <= O /\ O + n <= AAPP_HI) by (unfold AIMG_TOP, AAPP_HI in *; lia).
    assert (AO : aapp O n) by (eapply aapp_sub; [exact A4 | lia | lia]).
    assert (FA : as_FSB H + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= as_FSB H) by (destruct A4 as [[_ X]|[X _]]; [left | right]; lia).
    destruct (fsobj_windows H HB (x_LF e) O n 3 ff fp (x_m e) RF0 OB FF ltac:(lia) Hn ltac:(lia)) as (W1 & W2 & W3 & W4).
    change (fsz 3) with 512 in W1. change (fshn 3) with 64 in W2.
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE O n A4 ltac:(lia) ltac:(lia) Hn) as SD.
    assert (S1 : sh (as_FSB H) <= sh O) by (apply sh_mono; lia).
    assert (S2 : sh O + nsh n <= sh (as_FSB H + AFS_SIZE)).
    { clear - O8 A3 R1 Hn. unfold sh, nsh, AFS_SIZE in *. Z.div_mod_to_equations. lia. }
    assert (S0 : 0x7fff8000 <= sh O) by (unfold sh; rewrite ASHADOW_BASE_val; pose proof (Z.div_pos O 8 ltac:(lia) ltac:(lia)); lia).
    assert (XS1 : Forall (fun iv : Z * Z => O + n <= fst iv \/ snd iv <= O) XSc).
    { apply Forall_forall. intros iv Hiv.
      exact (fsobj_scratch H HB (x_LF e) O n (x_m e) iv RF0 OB ltac:(lia) Hn ltac:(lia) AO (proj1 (Forall_forall _ _) FS iv Hiv)). }
    assert (XS2 : Forall (fun iv : Z * Z => sh O + nsh n <= fst iv \/ snd iv <= sh O) XSc).
    { apply Forall_forall. intros iv Hiv.
      exact (fsobj_scratch_sh H HB (x_LF e) O n (x_m e) iv RF0 OB ltac:(lia) Hn ltac:(lia) (proj1 (Forall_forall _ _) FS iv Hiv)). }
    clear F10 F11 F12 F13 Q3 Q4 A4 AO FS.
    unfold XE. change (fsz 3) with 512. change (fshn 3) with 64.
    split; split.
    - unfold aclient_range. right; right; right; right; left. lia.
    - apply Forall_cons; [cbn [fst snd]; unfold RtB_Td.ATDLOC, AFS_HDR, AIMG_TOP in *; lia|].
      apply Forall_app. split; [|exact XS1].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AFS_HDR, AFS_FLAGS, AIMG_TOP, ALOWSH_LO, AHI_LO in *; lia.
    - unfold aclient_range. right; right; right; right; right; left. lia.
    - apply Forall_cons; [cbn [fst snd]; unfold RtB_Td.ATDLOC in *; lia|].
      apply Forall_app. split; [|exact XS2].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *; lia.
Qed.

  Lemma ex_keepT : forall XSc sk LBk m, Px XSc sk LBk m ->
    addressable m this 288
    /\ rw_cells asegs m (this + 8) [C8 (Z_to_bv 64 pcons)] /\ rw_cells asegs m (this + 56) [C8 (Z_to_bv 64 (x_nwords e))]
    /\ rw_cells asegs m (this + 72) [C8 (Z_to_bv 64 (x_widx e))] /\ rw_cells asegs m (this + 80) [C8 (Z_to_bv 64 (x_icount e))]
    /\ addressable m pcons 48 /\ rw_cells asegs m (pcons + 32) [C8 (Z_to_bv 64 0)].
Proof using HHbp HP FF THI PCI.
    intros XSc sk LBk m HPX.
    pose proof ex_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
    pose proof HPX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XP & FS & _).
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & THO & TC1 & TC2 & TC3 & TC4 & _ & _ & _ & PCO & PCC & _).
    destruct THO as (THA & _). destruct PCO as (PCA & PC8 & _).
    destruct (xobj_range XSc (x_this e) 288 THI ltac:(lia) V5 FS) as [XT1 XT2].
    destruct (xobj_range XSc (x_pcons e) 48 PCI ltac:(lia) PC8 FS) as [XQ1 XQ2].
    assert (SUB : forall X A n A' n', xclient_range H (x_LB e) SP X A n -> A <= A' -> A' + n' <= A + n -> xclient_range H (x_LB e) SP X A' n').
    { intros X0 A n A' n' [HR HX] Q1 Q2. split; [eapply aclient_range_sub; [exact HR | exact Q1 | exact Q2]|].
      eapply Forall_impl; [| exact HX]. intros iv Hiv. cbv beta in *. lia. }
    assert (ADP : forall O n, 0 < O -> 0 <= n -> O + n <= 2 ^ 47 -> addressable (x_m e) O n ->
              xclient_range H (x_LB e) SP ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XE H ff fp ++ XSc) (sh O) (nsh n) -> addressable m O n).
    { intros O n Q1 Q2 Q3 AD XR. pose proof (sh_nsh_high O n ltac:(lia) Q2 ltac:(unfold AAPP_HI; lia)) as Q4.
      assert (Q5 : 0 <= sh O) by (unfold sh; rewrite ASHADOW_BASE_val; pose proof (Z.div_pos O 8 ltac:(lia) ltac:(lia)); lia).
      unfold AHI_LO in Q4.
      eapply addressable_pteq; [exact AD|]. intros x Hx.
      exact (proj1 (XP x ltac:(lia) ltac:(eapply xclient_range_addr; [exact XR | exact Hx]))). }
    split; [exact (ADP (x_this e) 288 ltac:(lia) ltac:(lia) ltac:(lia) THA XT2)|].
    split; [eapply xpres_rw_cells; [exact XP | exact TC1 | cbn [cells_size csize]; apply (SUB _ (x_this e) 288); [exact XT1 | lia | lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact TC2 | cbn [cells_size csize]; apply (SUB _ (x_this e) 288); [exact XT1 | lia | lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact TC3 | cbn [cells_size csize]; apply (SUB _ (x_this e) 288); [exact XT1 | lia | lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact TC4 | cbn [cells_size csize]; apply (SUB _ (x_this e) 288); [exact XT1 | lia | lia]]|].
    split; [exact (ADP (x_pcons e) 48 ltac:(lia) ltac:(lia) ltac:(lia) PCA XQ2)|].
    eapply xpres_rw_cells; [exact XP | exact PCC | cbn [cells_size csize]; apply (SUB _ (x_pcons e) 48); [exact XQ1 | lia | lia]].
Qed.

  Lemma ex_keep : forall XSc sk LBk m, Px XSc sk LBk m ->
    ACONST m /\ LINV_P5 m /\ mem_inv asegs m /\ stk asegs m (x_lo e) SP /\ wr_at asegs m ff 504 /\ wr_at asegs m (sh ff) 64
    /\ as_RFS H ((3, ff, fp) :: x_LF e) m.
Proof using HHbp HP FF.
    intros XSc sk LBk m HPX.
    pose proof (rt_bp_base H HHbp) as HB.
    destruct HPX as (RF & _ & _ & AC & MI & _ & _ & _ & ST & _ & _ & WF & _ & _ & _ & LV).
    pose proof (xframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & _).
    pose proof (ah_frm_shvis H HB _ m (3, ff, fp) RF (or_introl eq_refl)) as SV.
    unfold shvis in SV. cbn [ff_addr ff_class fst snd] in SV. change (fsz 3) with 512 in SV.
    pose proof (wr_at_of_stk asegs m _ _ SV) as W.
    pose proof (hull_lo_le ff ltac:(lia)) as (HL1 & _). pose proof (hull_hi_ge (ff + 512) ltac:(lia)) as (HH1 & _).
    pose proof (sh_mono _ _ HL1) as M1. pose proof (sh_mono _ _ HH1) as M2.
    refine (conj AC (conj LV (conj MI (conj ST (conj WF (conj _ RF)))))).
    eapply wr_at_sub; [exact W | lia | lia | lia].
Qed.

  Lemma evWx : forall R X (k : nat), (k < 31)%nat ->
    ev (HLib.Eseed R (Wx ++ X)) (32 + N.of_nat k) = nth k Wx (Z_to_bv 64 0).
Proof using.
    intros R X k Hk. unfold HLib.Eseed, reg_ev. cbn [ev].
    destruct (N.ltb_spec (32 + N.of_nat k) 32); [lia|]. rewrite app_nth1 by (cbn [length Wx]; lia). f_equal. lia.
Qed.

  Ltac evwx := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wx;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Lemma kst_ex_ok : forall R X XSc sk LBk m, Px XSc sk LBk m -> know_ok asegs (HLib.Eseed R (Wx ++ X)) m kst_ex.
Proof using HHbp HP FF.
    intros R X XSc sk LBk m HPX.
    destruct (ex_keep XSc sk LBk m HPX) as (AC & LV & MI & ST & FW & SW & RF).
    pose proof ex_vals as (V1 & V2 & _).
    pose proof ex_wins as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    pose proof (xframe_facts H _ _ _ FF) as (F1 & F2 & _).
    pose proof aceil_facts as ACF.
    assert (SHF : edenot (HLib.Eseed R (Wx ++ X)) (EVar 52) = Z_to_bv 64 ff) by reflexivity.
    assert (ESH : estart (HLib.Eseed R (Wx ++ X)) (SA PD_SHB SHBASE) = ff / 8 + SHBASE).
    { unfold LbB_DPdK.PD_SHB. apply estart_sh; [exact SHF | lia]. }
    assert (E0 : ff / 8 + SHBASE = sh ff) by (unfold sh, SHBASE; rewrite ASHADOW_BASE_val; lia).
    rewrite <- E0 in SW.
    pose proof (ACONST_shbase m AC) as [_ CS]. pose proof (ACONST_uar m AC) as [_ CU].
    unfold know_ok, kst_ex. repeat apply Forall_cons; try apply Forall_nil.
    - apply kimg_relro. exact (proj1 LV).
    - eapply (kword_of_rw_cells asegs _ m ASHBASE_CELL _ 0%nat (C8 (wz 0x7fff8000))); [exact CS | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off edenot]; rewrite unsigned_lit by lia; reflexivity
        | unfold ASHBASE_CELL; cbn; lia | unfold ASHBASE_CELL; cbn; lia | reflexivity].
    - eapply (kword_of_rw_cells asegs _ m AUAR_CELL _ 0%nat (C4 (wz 1))); [exact CU | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off edenot]; rewrite unsigned_lit by lia; reflexivity
        | unfold AUAR_CELL; cbn; lia | unfold AUAR_CELL; cbn; lia | reflexivity].
    - eapply kwr_of_stk; [exact ST | | |]; evwx; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwx. rewrite unsigned_lit by lia. lia.
    - eapply kwr_of_wr_at; [exact FW | | |]; evwx; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwx. rewrite unsigned_lit by lia. lia.
    - eapply kwr_of_wr_at; [exact SW | rewrite ESH; lia | rewrite ESH; unfold elenZ; cbn [edenot]; rewrite unsigned_lit by lia; lia
                           | unfold elenZ; cbn [edenot]; rewrite unsigned_lit by lia; lia].
    - cbn [kentry_ok]. evwx. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. rewrite ESH. evwx. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. rewrite ESH. evwx. rewrite !unsigned_lit by lia. lia.
Qed.

  Definition shT (k : Z) : saddr := SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit k)) (ELit 3)) SHBASE.
  Definition kT (k : Z) (v : expr) : list kentry :=
    [KWord (shT k) 1 (ELit 0); KDisj (shT k) (ELit 1) (SA PD_SHB SHBASE) (ELit 64);
     KDisj (shT k) (ELit 1) (SA (EVar 58) (-8192)) (ELit 8216); KDisj (shT k) (ELit 1) (SA (EVar 52) 0) (ELit 504);
     KWord (SA (EVar 32) k) 8 v;
     KDisj (SA (EVar 32) 0) (ELit 288) (SA (EVar 58) (-8192)) (ELit 8216);
     KDisj (SA (EVar 32) 0) (ELit 288) (SA (EVar 52) 0) (ELit 504);
     KDisj (SA (EVar 32) 0) (ELit 288) (SA PD_SHB SHBASE) (ELit 64)].

  Lemma evT : forall R X k, 0 <= k <= 288 ->
    edenot (HLib.Eseed R (Wx ++ X)) (EAlu ALU_ADD (EVar 32) (ELit k)) = Z_to_bv 64 (this + k).
Proof using HP FF.
    intros R X k Hk. pose proof ex_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
    cbn [edenot]. change (ev (HLib.Eseed R (Wx ++ X)) 32) with (Z_to_bv 64 this).
    apply w_add; lia.
Qed.

  Lemma shT_start : forall R X k, 0 <= k < 288 -> estart (HLib.Eseed R (Wx ++ X)) (shT k) = (this + k) / 8 + SHBASE.
Proof using HP FF.
    intros R X k Hk. pose proof ex_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7). unfold shT.
    apply estart_sh; [apply evT; lia | lia].
Qed.

  Lemma shT_apart : forall k, 0 <= k < 288 ->
    (this + k) / 8 + SHBASE + 1 <= ff / 8 + SHBASE \/ ff / 8 + SHBASE + 64 <= (this + k) / 8 + SHBASE.
Proof using HHbp HP FF THI.
    intros k Hk.
    pose proof ex_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
    assert (D : this + 288 <= ff \/ ff + 512 <= this).
    { pose proof THI as (f & IN & D1 & D2). pose proof FF as (_ & _ & FD). destruct (FD f IN) as [DJ _].
      change (fsz 3) with 512 in DJ. lia. }
    pose proof (xframe_facts H _ _ _ FF) as (_ & _ & F3 & _).
    assert (EF : ff = ff / 8 * 8) by (clear - F3; Z.div_mod_to_equations; lia).
    assert (ET : this = this / 8 * 8) by (clear - V5; Z.div_mod_to_equations; lia).
    clear - Hk D EF ET. set (f8 := ff / 8) in *. set (t8 := this / 8) in *.
    assert (E2 : (this + k) / 8 = t8 + k / 8) by (rewrite ET; rewrite Z.add_comm, Z.div_add by lia; lia).
    rewrite E2. assert (0 <= k / 8 < 36) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    destruct D as [A|A]; [left | right]; lia.
Qed.

  Lemma shb_eq0 : ff / 8 + SHBASE = sh ff.
Proof using.
    unfold sh, SHBASE. rewrite ASHADOW_BASE_val. lia.
Qed.

  Lemma this_apart :
       x_this e + 288 <= xS1 e - 8192
    /\ (x_this e + 288 <= ff \/ ff + 512 <= x_this e)
    /\ (x_this e + 288 <= sh ff \/ sh ff + 64 <= x_this e)
    /\ (forall k, 0 <= k < 288 -> (x_this e + k) / 8 + SHBASE + 1 <= xS1 e - 8192
                                 /\ ((x_this e + k) / 8 + SHBASE + 1 <= ff \/ ff + 512 <= (x_this e + k) / 8 + SHBASE)).
Proof using HHbp HP FF THI.
    pose proof (rt_bp_base H HHbp) as HB.
    pose proof ex_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
    pose proof (xframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (xS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof aceil_facts as ACF.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RF0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & THO & _).
    destruct THO as (_ & _ & _ & _ & _ & _ & (A1 & A2 & A3)).
    pose proof THI as (f & IN & D1 & D2).
    pose proof (proj2 (ah_RFS_range H HB _ _ RF0) f IN) as (K' & Q1 & Q2 & Q3 & Q4).
    pose proof FF as (_ & _ & FD). destruct (FD f IN) as [DJ _]. change (fsz 3) with 512 in DJ.
    assert (FA : ff + 512 <= ALOWSH_LO \/ AHI_LO <= ff) by (destruct F10 as [[_ X]|[X _]]; [left | right]; lia).
    clear F10 F11 F12 F13 F16 Q3 Q4 RF0 FD.
    unfold AFS_HDR, AFS_FLAGS, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, SHBASE in *.
    split; [lia|]. split; [lia|]. split; [lia|].
    intros k Hk.
    assert (Q0 : 0 <= (x_this e + k) / 8) by (apply Z.div_pos; lia).
    assert (QH : (x_this e + k) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
    split; lia.
Qed.

  Lemma kT_ok : forall R X XSc sk LBk m k v (ve : expr), Px XSc sk LBk m -> 0 <= k -> k + 8 <= 288 -> k mod 8 = 0 ->
    rw_cells asegs m (this + k) [C8 (Z_to_bv 64 v)] -> edenot (HLib.Eseed R (Wx ++ X)) ve = Z_to_bv 64 v ->
    know_ok asegs (HLib.Eseed R (Wx ++ X)) m (kT k ve).
Proof using HHbp HP FF THI PCI.
    intros R X XSc sk LBk m k v ve HPX Hk0 Hk8 Hkm RW Hve.
    destruct (ex_keepT XSc sk LBk m HPX) as (THAm & _).
    pose proof ex_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
    pose proof ex_wins as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    pose proof this_apart as (TA1 & TA2 & TA3 & TA4).
    pose proof shb_eq0 as E0.
    assert (ESH : estart (HLib.Eseed R (Wx ++ X)) (SA PD_SHB SHBASE) = ff / 8 + SHBASE).
    { unfold LbB_DPdK.PD_SHB. apply estart_sh; [reflexivity | lia]. }
    assert (ETH : estart (HLib.Eseed R (Wx ++ X)) (SA (EVar 32) 0) = x_this e).
    { unfold estart; cbn [a_base a_off edenot]. change (ev (HLib.Eseed R (Wx ++ X)) 32) with (Z_to_bv 64 (x_this e)).
      rewrite unsigned_lit by lia. lia. }
    assert (Hk : 0 <= k < 288) by lia.
    unfold know_ok, kT. repeat apply Forall_cons; try apply Forall_nil.
    - unfold shT. apply (kshadow0 _ m (EAlu ALU_ADD (EVar 32) (ELit k)) (x_this e + k)); [apply evT; lia | lia |].
      eapply (sh0_of_addressable m (x_this e) 288 (x_this e + k)); [exact THAm | change (8 * (288 / 8)) with 288; lia].
    - cbn [kentry_ok]. rewrite shT_start by exact Hk. rewrite ESH. unfold elenZ. cbn [edenot]. rewrite !unsigned_lit by lia.
      pose proof (shT_apart k Hk) as A. lia.
    - cbn [kentry_ok]. rewrite shT_start by exact Hk. evwx. rewrite !unsigned_lit by lia. destruct (TA4 k Hk) as [A _]. lia.
    - cbn [kentry_ok]. rewrite shT_start by exact Hk. evwx. rewrite !unsigned_lit by lia. destruct (TA4 k Hk) as [_ A]. lia.
    - eapply (kword_of_rw_cells asegs _ m (x_this e + k) _ 0%nat (C8 (Z_to_bv 64 v))); [exact RW | reflexivity | reflexivity | lia | | lia | lia |].
      + unfold estart; cbn [a_base a_off edenot]. change (ev (HLib.Eseed R (Wx ++ X)) 32) with (Z_to_bv 64 (x_this e)).
        rewrite unsigned_lit by lia. lia.
      + rewrite Hve. reflexivity.
    - cbn [kentry_ok]. rewrite ETH. evwx. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. rewrite ETH. evwx. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. rewrite ETH, ESH. unfold elenZ. cbn [edenot]. rewrite !unsigned_lit by lia. lia.
Qed.

  Lemma scT_flat : forall R X k, 0 <= k < 288 -> flat (HLib.Eseed R (Wx ++ X)) (shT k) 1.
Proof using HP FF.
    intros R X k Hk. pose proof ex_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7). unfold flat. rewrite shT_start by exact Hk.
    assert (Q : 0 <= (this + k) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    clear - Q. unfold SHBASE. lia.
Qed.

  Lemma scP_flat : forall R X k n, 0 <= k -> 0 <= n -> k + n <= 288 -> flat (HLib.Eseed R (Wx ++ X)) (SA (EVar 32) k) n.
Proof using HP FF.
    intros R X k n Hk Hn Hkn. pose proof ex_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
    unfold flat, estart. cbn [a_base a_off edenot].
    change (ev (HLib.Eseed R (Wx ++ X)) 32) with (Z_to_bv 64 this).
    rewrite unsigned_lit by lia. lia.
Qed.

  Definition tS (T : list fent) (ks : list (Z * nat)) : tab := (EVar 58, xS1 e, -8192, 24, T, ks).

  Definition tFw (hF : Z) (T : list fent) (ks : list (Z * nat)) : tab := (EVar 52, ff, 0, hF, T, ks).
  Definition tHw (hH : Z) (T : list fent) (ks : list (Z * nat)) : tab := (PD_SHB, ff / 8, SHBASE, SHBASE + hH, T, ks).
  Definition tF (T : list fent) (ks : list (Z * nat)) : tab := tFw 504 T ks.
  Definition tH (T : list fent) (ks : list (Z * nat)) : tab := tHw 64 T ks.
  Definition wok (hF hH : Z) : bool := ((0 <=? hF) && (hF <=? 504) && (0 <=? hH) && (hH <=? 64))%bool.
  Lemma wok_facts : forall hF hH, wok hF hH = true -> 0 <= hF <= 504 /\ 0 <= hH <= 64.
Proof using.
    intros hF hH W. unfold wok in W.
    apply andb_true_iff in W as [W W4]. apply andb_true_iff in W as [W W3]. apply andb_true_iff in W as [W1 W2].
    apply Z.leb_le in W1, W2, W3, W4. lia.
Qed.

  Lemma tab_vals : bv_unsigned (edenot (wenv Wx) (EVar 58)) = xS1 e /\ bv_unsigned (edenot (wenv Wx) (EVar 52)) = ff
    /\ bv_unsigned (edenot (wenv Wx) PD_SHB) = ff / 8.
Proof using HP FF.
    pose proof ex_vals as (V1 & V2 & _). pose proof ex_wins as (_ & _ & _ & _ & _ & _ & W7 & W8).
    split; [change (edenot (wenv Wx) (EVar 58)) with (Z_to_bv 64 (xS1 e)); apply unsigned_lit; lia|].
    split; [change (edenot (wenv Wx) (EVar 52)) with (Z_to_bv 64 ff); apply unsigned_lit; lia|].
    unfold LbB_DPdK.PD_SHB. apply (srl3_val (wenv Wx) (EVar 52) ff); [reflexivity | lia].
Qed.

  Lemma tabs_wf3w : forall hF hH SF FT HT ks1 ks2 ks3, wok hF hH = true ->
    fwcl (wbound Wx) SF = true -> fwcl (wbound Wx) FT = true -> fwcl (wbound Wx) HT = true ->
    fin (-8192) 24 (fkeys SF ++ ks1) = true -> fin 0 hF (fkeys FT ++ ks2) = true -> fin SHBASE (SHBASE + hH) (fkeys HT ++ ks3) = true ->
    tabs_wf Wx [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3].
Proof using HP FF.
    intros hF hH SF FT HT ks1 ks2 ks3 WK C1 C2 C3 F1 F2 F3.
    destruct (wok_facts hF hH WK) as [K1 K2].
    pose proof ex_wins as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8). pose proof tab_vals as (T1 & T2 & T3).
    pose proof ex_vals as (V1 & V2 & _).
    split.
    - repeat apply Forall_cons; try apply Forall_nil; cbn [tb tB tlo thi ttbl tks tS tFw tHw]; unfold SHBASE in *;
        (split; [reflexivity|]); (split; [assumption|]); (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; assumption).
    - intros t1 t2 I1 I2 Hb. cbn [In] in I1, I2.
      destruct I1 as [<-|[<-|[<-|[]]]]; destruct I2 as [<-|[<-|[<-|[]]]]; cbn [tb tB tlo thi tS tFw tHw] in *;
        try (vm_compute in Hb; discriminate Hb); unfold SHBASE in *; lia.
Qed.
  Lemma tabs_wf3 : forall SF FT HT ks1 ks2 ks3,
    fwcl (wbound Wx) SF = true -> fwcl (wbound Wx) FT = true -> fwcl (wbound Wx) HT = true ->
    fin (-8192) 24 (fkeys SF ++ ks1) = true -> fin 0 504 (fkeys FT ++ ks2) = true -> fin SHBASE (SHBASE + 64) (fkeys HT ++ ks3) = true ->
    tabs_wf Wx [tS SF ks1; tF FT ks2; tH HT ks3].
Proof using HP FF.
    intros SF FT HT ks1 ks2 ks3 C1 C2 C3 F1 F2 F3.
    exact (tabs_wf3w 504 64 SF FT HT ks1 ks2 ks3 eq_refl C1 C2 C3 F1 F2 F3).
Qed.

  Lemma wk_stk : forall m (ks : list (Z * nat)), stk asegs m (x_lo e) SP -> fin (-8192) 24 ks = true ->
    forall k w, In (k, w) ks -> wr_at asegs m (xS1 e + k) (Z.of_nat w).
Proof using HP FF.
    intros m ks ST Hf k w Hi. destruct (fin_In _ _ _ k w Hf Hi) as (K1 & K2 & K3).
    pose proof (xS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof (wr_at_of_stk asegs m (x_lo e) SP ST) as W. eapply wr_at_sub; [exact W | lia | lia | lia].
Qed.
  Lemma wk_win : forall m A n (ks : list (Z * nat)) B lo0, wr_at asegs m A n -> A = B + lo0 ->
    fin lo0 (lo0 + n) ks = true -> forall k w, In (k, w) ks -> wr_at asegs m (B + k) (Z.of_nat w).
Proof using.
    intros m A n ks B lo0 W -> Hf k w Hi. destruct (fin_In _ _ _ k w Hf Hi) as (H1 & H2 & H3).
    eapply wr_at_sub; [exact W | lia | lia | lia].
Qed.
  Lemma shb_eq : ff / 8 + SHBASE = sh ff.
Proof using.
    exact shb_eq0.
Qed.

  Lemma fin_wider : forall lo hi hi' ks, fin lo hi ks = true -> hi <= hi' -> fin lo hi' ks = true.
Proof using.
    intros lo hi hi' ks F Hh. unfold fin. apply forallb_forall. intros [k w] Hi.
    destruct (fin_In _ _ _ k w F Hi) as (K1 & K2 & K3). cbn [fst snd].
    apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split|]|].
    - apply Z.leb_le; lia.
    - apply Z.leb_le; lia.
    - apply Nat.leb_le; lia.
    - apply Nat.leb_le; lia.
Qed.
  Lemma tabs_ok3w : forall hF hH XSc sk LBk m SF FT HT ks1 ks2 ks3, wok hF hH = true -> Px XSc sk LBk m ->
    ftbl Wx (xS1 e) m SF -> ftbl Wx ff m FT -> ftbl Wx (ff / 8) m HT ->
    fin (-8192) 24 ks1 = true -> fin 0 hF ks2 = true -> fin SHBASE (SHBASE + hH) ks3 = true ->
    tabs_ok Wx m [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3].
Proof using HHbp HP FF.
    intros hF hH XSc sk LBk m SF FT HT ks1 ks2 ks3 WK HPX T1 T2 T3 F1 F2 F3.
    destruct (wok_facts hF hH WK) as [K1 K2].
    destruct (ex_keep XSc sk LBk m HPX) as (_ & _ & _ & ST & FW & SW & _).
    apply Forall_cons; [split; [exact T1 | exact (wk_stk m ks1 ST F1)]|].
    apply Forall_cons; [split; [exact T2 | exact (wk_win m ff 504 ks2 ff 0 FW ltac:(lia) (fin_wider 0 hF (0 + 504) ks2 F2 ltac:(lia)))]|].
    apply Forall_cons; [split; [exact T3 | exact (wk_win m (sh ff) 64 ks3 (ff / 8) SHBASE SW (eq_sym shb_eq) (fin_wider SHBASE (SHBASE + hH) (SHBASE + 64) ks3 F3 ltac:(lia)))]|].
    apply Forall_nil.
Qed.
  Lemma tabs_ok3 : forall XSc sk LBk m SF FT HT ks1 ks2 ks3, Px XSc sk LBk m ->
    ftbl Wx (xS1 e) m SF -> ftbl Wx ff m FT -> ftbl Wx (ff / 8) m HT ->
    fin (-8192) 24 ks1 = true -> fin 0 504 ks2 = true -> fin SHBASE (SHBASE + 64) ks3 = true ->
    tabs_ok Wx m [tS SF ks1; tF FT ks2; tH HT ks3].
Proof using HHbp HP FF.
    intros XSc sk LBk m SF FT HT ks1 ks2 ks3 HPX T1 T2 T3 F1 F2 F3.
    exact (tabs_ok3w 504 64 XSc sk LBk m SF FT HT ks1 ks2 ks3 eq_refl HPX T1 T2 T3 F1 F2 F3).
Qed.

  Lemma Px_step3w : forall hF hH XSc sk LBk SF FT HT ks1 ks2 ks3 m m', wok hF hH = true -> Px XSc sk LBk m ->
    munch (winsT [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3]) m m' -> wmono asegs m m' -> mem_inv asegs m' -> Px XSc sk LBk m'.
Proof using HHbp HP FF.
    intros hF hH XSc sk LBk SF FT HT ks1 ks2 ks3 m m' WK HPX MU WM MI.
    pose proof (rt_bp_base H HHbp) as HB.
    destruct (wok_facts hF hH WK) as [K1 K2].
    pose proof ex_wins as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    pose proof (xS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof aceil_facts as ACF.
    pose proof shb_eq0 as E0.
    unfold Px in *.
    pose proof HPX as (_ & _ & _ & _ & _ & _ & _ & _ & ST & _).
    eapply (xinv_munch H HB e ff fp XSc sk LBk m m' _ HP HPX MU WM MI).
    - eapply stk_wmono; [exact ST | exact WM | lia].
    - unfold winsT. cbn [map tB tlo thi tS tFw tHw].
      repeat apply Forall_cons; try apply Forall_nil; unfold xwin, EX_SAVED, EX_FLAGP; cbn [fst snd].
      + left. lia.
      + right; left. lia.
      + right; right. lia.
Qed.
  Lemma Px_step3 : forall XSc sk LBk SF FT HT ks1 ks2 ks3 m m', Px XSc sk LBk m ->
    munch (winsT [tS SF ks1; tF FT ks2; tH HT ks3]) m m' -> wmono asegs m m' -> mem_inv asegs m' -> Px XSc sk LBk m'.
Proof using HHbp HP FF.
    intros XSc sk LBk SF FT HT ks1 ks2 ks3 m m' HPX MU WM MI.
    exact (Px_step3w 504 64 XSc sk LBk SF FT HT ks1 ks2 ks3 m m' eq_refl HPX MU WM MI).
Qed.

  Ltac tnormp H :=
    lazymatch type of H with
    | ftbl ?W ?B ?m ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    | rtbl ?W ?R ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    end.

  Ltac exrun3w hF hH HRT HSF HFT HHT HPX HMI fuel stops kx :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HPX with Px ?XSc ?sk ?LBk _ =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tFw hF FT []; tHw hH HT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) ((kst_ex ++ kx) ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] (((kst_ex ++ kx) ++ kf) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wx) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 58) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wx [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3]
                    (tabs_wf3w hF hH SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    (Px XSc sk LBk) (fun m0 m0' => Px_step3w hF hH XSc sk LBk SF FT HT ks1 ks2 ks3 m0 m0' eq_refl)
                    Q R F pc fc m ro RT [] ((kst_ex ++ kx) ++ kf) fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply (tabs_ok3w hF hH XSc sk LBk); [vm_compute; reflexivity | exact HPX | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HPX | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply Forall_app; split; [apply (kst_ex_ok _ _ XSc sk LBk); exact HPX | ] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end
    end.

  Ltac exrun3wd dirs hF hH HRT HSF HFT HHT HPX HMI fuel stops kx :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HPX with Px ?XSc ?sk ?LBk _ =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tFw hF FT []; tHw hH HT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) ((kst_ex ++ kx) ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR dirs [] []) (SS pc (HLib.srs sr_id RT) [] (((kst_ex ++ kx) ++ kf) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wx) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 58) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wx [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3]
                    (tabs_wf3w hF hH SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    (Px XSc sk LBk) (fun m0 m0' => Px_step3w hF hH XSc sk LBk SF FT HT ks1 ks2 ks3 m0 m0' eq_refl)
                    Q R F pc fc m ro RT [] ((kst_ex ++ kx) ++ kf) fuel stops (SCR dirs [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply (tabs_ok3w hF hH XSc sk LBk); [vm_compute; reflexivity | exact HPX | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HPX | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply Forall_app; split; [apply (kst_ex_ok _ _ XSc sk LBk); exact HPX | ] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end
    end.

  Ltac exrun3 HRT HSF HFT HHT HPX HMI fuel stops kx := exrun3w 504 64 HRT HSF HFT HHT HPX HMI fuel stops kx.

  Ltac tsplit HTS H1 H2 H3 :=
    lazymatch type of HTS with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in HTS; clear E end;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS]; apply Forall_cons_iff in HTS as [H3 _];
    cbn [fst snd] in H1, H2, H3.

  Ltac rgetx HRT r H :=
    lazymatch type of HRT with rtbl _ ?R ?RT =>
      let e0 := eval vm_compute in (match find (fun p : reg * expr => bv_eqb (fst p) r) RT with Some p => snd p | None => ELit 0 end) in
      assert (H : PropExec.getr R r = edenot (wenv Wx) e0)
        by (apply (rtbl_In Wx R RT r e0 HRT); apply LbB_DCtorK.inb_In'; vm_compute; reflexivity);
      unfold wenv in H; cbn [edenot] in H; unfold HLib.Eseed, reg_ev, Wx in H;
      lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
            Init.Nat.add Nat.sub nth app] in H;
      rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z in H by (pose proof ex_vals; pose proof ex_wins; lia)
    end.

End XT.

Lemma rtbl_sw : forall W W' k R RT, (forall n, (32 <= n < k)%N -> ev (wenv W) n = ev (wenv W') n) ->
  forallb (fun re : reg * expr => wcl k (snd re)) RT = true -> rtbl W R RT -> rtbl W' R RT.
Proof.
  intros W W' k R RT HE C HT. unfold rtbl in *. apply Forall_forall. intros [r e] Hi.
  pose proof (proj1 (Forall_forall _ _) HT (r, e) Hi) as K. cbn [fst snd] in K |- *.
  pose proof (proj1 (forallb_forall _ _) C (r, e) Hi) as Ce. cbn [snd] in Ce.
  rewrite (edenot_wcl (wenv W') (wenv W) k e Ce (fun n Hn => eq_sym (HE n Hn))). exact K.
Qed.
Lemma ftbl_sw : forall W W' k B m tbl, (forall n, (32 <= n < k)%N -> ev (wenv W) n = ev (wenv W') n) ->
  fwcl k tbl = true -> ftbl W B m tbl -> ftbl W' B m tbl.
Proof.
  intros W W' k B m tbl HE C HT. unfold ftbl in *. apply Forall_forall. intros [[k0 w] e] Hi.
  pose proof (proj1 (Forall_forall _ _) HT (k0, w, e) Hi) as R. cbn beta iota in R |- *.
  pose proof (proj1 (forallb_forall _ _) C (k0, w, e) Hi) as Ce. cbn beta iota in Ce.
  rewrite (edenot_wcl (wenv W') (wenv W) k e Ce (fun n Hn => eq_sym (HE n Hn))). exact R.
Qed.
Lemma Wx_sw1 {HCEIL : HeapCeil} : forall (H : asr) (e : xent H) ff fp p1 n1 p2 n2 q2 m2 n, (32 <= n < 61)%N ->
  ev (wenv (Wx H e ff fp p1 n1 p2 n2)) n = ev (wenv (Wx H e ff fp p1 n1 q2 m2)) n.
Proof.
  intros H e ff fp p1 n1 p2 n2 q2 m2 n Hn. unfold wenv, HLib.Eseed, reg_ev. cbn [ev].
  destruct (N.ltb_spec n 32); [lia|]. unfold Wx.
  assert (Hj : (N.to_nat n - 32 < 29)%nat) by lia. set (j := (N.to_nat n - 32)%nat) in *. clearbody j.
  do 29 (destruct j as [|j]; [reflexivity|]). lia.
Qed.
Lemma Wx_sw {HCEIL : HeapCeil} : forall (H : asr) (e : xent H) ff fp p1 n1 p2 n2 q1 m1 q2 m2 n, (32 <= n < 59)%N ->
  ev (wenv (Wx H e ff fp p1 n1 p2 n2)) n = ev (wenv (Wx H e ff fp q1 m1 q2 m2)) n.
Proof.
  intros H e ff fp p1 n1 p2 n2 q1 m1 q2 m2 n Hn. unfold wenv, HLib.Eseed, reg_ev. cbn [ev].
  destruct (N.ltb_spec n 32); [lia|]. unfold Wx.
  assert (Hj : (N.to_nat n - 32 < 27)%nat) by lia. set (j := (N.to_nat n - 32)%nat) in *. clearbody j.
  do 27 (destruct j as [|j]; [reflexivity|]). lia.
Qed.
