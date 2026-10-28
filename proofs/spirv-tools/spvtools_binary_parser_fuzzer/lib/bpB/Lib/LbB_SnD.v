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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtor LbB_DPdK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_TablStmt LbB_SnStmt LbB_SnV.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnK LbB_SnW LbB_SnFind LbB_SnTA LbB_SnTB LbB_SnA LbB_SnF LbB_SnAb LbB_SnFb LbB_SnQ LbB_Sn.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_SnXD LbB_SnXK LbB_SnXI.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnXT LbB_SnB.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnXO1 LbB_SnXO2 LbB_SnXQ1 LbB_SnXQ2 LbB_SnXC1 LbB_SnXC2 LbB_SnXS1 LbB_SnXS2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnXP1 LbB_SnXP2 LbB_SnXR1 LbB_SnXR2 LbB_SnXE1 LbB_SnXE2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SnD.

  Local Notation kst_p1 := LbB_SnQ.kst_p1 (only parsing).
  Local Notation pd_mul32 := LbB_SnQ.pd_mul32 (only parsing).
  Local Notation disjoint_of_outside := LbB_SnQ.disjoint_of_outside (only parsing).
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 aw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (this po tid pcons icount lo : Z) (LF : list fframe).
  Variables (bl bc : Z) (LB : list block) (ents : list (Z * (Z * (Z * Z * Z)))).
  Hypothesis Ha0 : a0 = Z_to_bv 64 this.
  Hypothesis Ha1 : a1 = Z_to_bv 64 po.
  Hypothesis Ha2 : a2 = Z_to_bv 64 (sx32A tid).
  Hypothesis TIDR : 0 <= tid < 2 ^ 32.

  Hypothesis DSA : addressable m0 po 20.
  Hypothesis DSW : wr_at asegs m0 po 20.
  Hypothesis DSO : app_obj po 20.
  Hypothesis DS8 : po mod 8 = 0.
  Hypothesis DSV : shvis m0 po (po + 20).
  Hypothesis DSin : obj_inframe LF po 20.

  Hypothesis PCA : addressable m0 pcons 48.
  Hypothesis PCO : app_obj pcons 48.
  Hypothesis PC8 : pcons mod 8 = 0.
  Hypothesis PCC : rw_cells asegs m0 (pcons + 32) [C8 (Z_to_bv 64 0)].
  Hypothesis PCfs : fsobj H LF pcons 48.
  Hypothesis DISJ : forall a, po <= a < po + 20 -> ~ (pcons <= a < pcons + 48).
  Hypothesis ICN : 0 <= icount < 2 ^ 63.

  Hypothesis THA : addressable m0 this 288.
  Hypothesis THO : app_obj this 288.
  Hypothesis TH8 : this mod 8 = 0.
  Hypothesis THfs : fsobj H LF this 288.
  Hypothesis THC1 : rw_cells asegs m0 (this + 8) [C8 (Z_to_bv 64 pcons)].
  Hypothesis THC2 : rw_cells asegs m0 (this + 80) [C8 (Z_to_bv 64 icount)].

  Hypothesis UM0 : umapx MI_A 32 (nval32 ASEGS) (lbl LB) m0 (this + 136) bl bc ents.
  Hypothesis USH : umap_sh m0 32 (bl, bc, ents).
  Hypothesis UBL : forall A n, In (A, n) (lbl LB) -> ablock_range H A n.
  Hypothesis KOK : sn_kinds_ok ents.

  Hypothesis STK : stk asegs m0 lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ADS_STACK.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPHI : bv_unsigned sp <= AAPP_HI.
  Hypothesis SPOBJ : forall O n, O = po /\ n = 20 \/ O = pcons /\ n = 48 \/ O = this /\ n = 288 ->
                     O + n <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= O.

  Hypothesis MI0 : mem_inv asegs m0.
  Hypothesis AC0 : ACONST m0.
  Hypothesis LV0 : LINV_P5 m0.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis RFS0 : as_RFS H LF m0.
  Hypothesis LFn : (length LF < AFS_MAXLIVE_BP)%nat.
  Hypothesis THR : athr_cells m0.

  Local Notation Wp0 := (@LbB_SnQ.Wp0 ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 this po tid) (only parsing).
  Local Notation P1w := (@LbB_SnQ.P1w sp m0) (only parsing).
  Local Notation p1_ranges := (@LbB_SnQ.p1_ranges HCEIL sp this po tid pcons icount lo LF TIDR ICN CEIL LO LFn) (only parsing).
  Local Notation p1_keep := (@LbB_SnQ.p1_keep HCEIL sp m0 this po tid pcons icount lo LF TIDR ICN STK CEIL LO AC0 LV0 LFn) (only parsing).
  Local Notation kst_p1_ok := (@LbB_SnQ.kst_p1_ok HCEIL ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 this po tid pcons icount lo LF TIDR ICN STK CEIL LO SPHI AC0 LV0 LFn) (only parsing).
  Local Notation tS0 := (@LbB_SnQ.tS0 sp) (only parsing).
  Local Notation tabs_wf1 := (@LbB_SnQ.tabs_wf1 HCEIL ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 this po tid pcons icount lo LF TIDR ICN CEIL LO LFn) (only parsing).
  Local Notation P1w_step := (@LbB_SnQ.P1w_step sp m0 this po tid pcons icount LF TIDR ICN LFn) (only parsing).
  Local Notation tabs_ok1 := (@LbB_SnQ.tabs_ok1 HCEIL ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 this po tid pcons icount lo LF TIDR ICN STK CEIL LO AC0 LV0 LFn) (only parsing).
  Local Notation HHb := (@LbB_SnQ.HHb HCEIL H HHbp) (only parsing).
  Local Notation SM4 := (@LbB_SnQ.SM4 HCEIL H HHbp) (only parsing).
  Local Notation po_this := (@LbB_SnQ.po_this m0 this po DSA DS8 THA TH8) (only parsing).
  Local Notation W1 := (@LbB_SnQ.W1 H sp) (only parsing).
  Local Notation new_frame := (@LbB_SnQ.new_frame HCEIL H HHbp this po pcons LF DSin PCfs THfs) (only parsing).
  Local Notation quiet := (@LbB_SnQ.quiet this LB) (only parsing).
  Local Notation quiet_foot := (@LbB_SnQ.quiet_foot m0 this bl bc LB ents UM0) (only parsing).
  Local Notation UW := (@LbB_SnQ.UW H sp po) (only parsing).
  Local Notation out_obj := (@LbB_SnQ.out_obj HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR DSO DSin ICN CEIL LO RFS0 LFn) (only parsing).
  Local Notation quiet_out := (@LbB_SnQ.quiet_out HCEIL H HHbp sp m0 this po tid pcons icount lo LF LB TIDR DSA DSO DS8 DSin ICN THA THO TH8 THfs UBL CEIL LO SPOBJ RFS0 LFn) (only parsing).
  Local Notation W1_sub := (@LbB_SnQ.W1_sub H sp po) (only parsing).
  Local Notation quiet_keep := (@LbB_SnQ.quiet_keep HCEIL H HHbp sp m0 this po tid pcons icount lo LF bl bc LB ents TIDR DSA DSO DS8 DSin ICN THA THO TH8 THfs THC1 THC2 UM0 USH UBL CEIL LO SPOBJ RFS0 LFn) (only parsing).
  Local Notation W1_keep := (@LbB_SnQ.W1_keep HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR DSA DSW DSO DS8 DSV PCA PCO PC8 PCC PCfs ICN THA THO TH8 STK CEIL LO SPHI SPOBJ LV0 RFS0 LFn) (only parsing).
  Local Notation athr_keep := (@LbB_SnQ.athr_keep HCEIL sp this po tid pcons icount LF TIDR ICN LFn) (only parsing).
  Local Notation TW := (@LbB_SnQ.TW H sp po) (only parsing).
  Local Notation tw_munch := (@LbB_SnQ.tw_munch H sp m0 po) (only parsing).
  Local Notation tw_place := (@LbB_SnQ.tw_place HCEIL H LF) (only parsing).
  Local Notation tw_laws := (@LbB_SnQ.tw_laws HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR DSO DSin ICN CEIL LO RFS0 LFn) (only parsing).
  Local Notation tw_out_img := (@LbB_SnQ.tw_out_img HCEIL H sp this po tid pcons icount lo LF TIDR DSO ICN CEIL LO LFn) (only parsing).
  Local Notation tw_keep := (@LbB_SnQ.tw_keep HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR DSW DSO DSin ICN STK CEIL LO AC0 LV0 RFS0 LFn) (only parsing).
  Local Notation tw_xpres := (@LbB_SnQ.tw_xpres HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR ICN CEIL LO LFn) (only parsing).
  Local Notation TW0 := (@LbB_SnQ.TW0 H sp) (only parsing).
  Local Notation tw0_munch := (@LbB_SnQ.tw0_munch H sp m0) (only parsing).
  Local Notation tw0_tw := (@LbB_SnQ.tw0_tw H sp po) (only parsing).
  Local Notation tw0_laws := (@LbB_SnQ.tw0_laws HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR DSO DSin ICN CEIL LO RFS0 LFn) (only parsing).
  Local Notation tw0_xpres := (@LbB_SnQ.tw0_xpres HCEIL H HHbp sp m0 this po tid pcons icount lo LF TIDR ICN CEIL LO LFn) (only parsing).

  Notation spz := (bv_unsigned sp) (only parsing).

  Ltac evw0 := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wp0;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Ltac dkrun1 HRT HSF HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS0 SF []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] (kst_p1 ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp0) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          eapply (dk_runN Wp0 [tS0 SF ks1] (tabs_wf1 SF ks1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    P1w (P1w_step SF ks1) Q R F pc fc m ro RT [] kst_p1 fuel stops (SCR [] [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok1; [exact HP | exact HMI | exact HSF | vm_compute; reflexivity]
          | exact HP | exact HMI | apply kst_p1_ok; [exact HP | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end
    end.

  Variables (s : as_St H) (mo : Model) (CH : list (Z * Z)) (B shi : Z).
  Notation E0 := (LbB_SnB.sn_e H ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 this po tid pcons icount lo LF bl bc LB
                                s mo CH B shi) (only parsing).
  Hypothesis XP : xpre H E0.
  Hypothesis THI : obj_inframe LF this 288.
  Hypothesis PCI : obj_inframe LF pcons 48.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV_P5 ds_repA0.
  Hypothesis HU32 : put_u32_stmtA H LINV_P5 ds_repA0.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV_P5 ds_repA0.
  Hypothesis HPDIAG : pdiag0_stmtA H LINV_P5 ds_repA0.

  Notation SNPOST :=
    (sn_post H LINV_P5 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF (sn_XT po) lo B shi m0 mo
             (sn_res LB po tid ents)) (only parsing).

  Lemma sn_diag1A : bv_unsigned sp mod 32 = 0 -> FPSteps.frm_zero fc ->
    forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> LbB_Sn.sn_d1A H ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 this po tid pcons icount LF bl bc (as_VIS H s msF') ->
    as_SR H SNPOST (mkCfg msF' mo').
  Proof using All.
    intros C32 FZ msF' mo' KR' MP' HD.
    destruct (LbB_SnB.sn_bridgeA H HHbp ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 this po tid pcons icount lo LF bl bc LB
                TIDR DSW DSO DSin ICN STK CEIL LO AC0 LV0 TP RFS0 LFn s mo CH B shi XP C32 _ _ HD)
      as (ff & fp & R & m & E & RF & FRESH & HPX & MI & HRT & HSF & HFT & HHT).
    eapply (ahh_evt_then H HHb _ _ s msF' _ mo' KR' E).
    { exact (LbB_SnXP1.sx_ph1 H HHbp E0 ff fp 0 0 0 0 XP FRESH THI PCI R F fc m [] s LB RF HRT HSF HFT HHT HPX MI). }
    intros msF2 mo2 KR2 MP2 CUT.
    eapply (LbB_SnXR1.sx_ph2 H HHbp E0 ff fp 0 0 0 0 XP FRESH THI PCI HPDIAG HCSEQ HU32 HDTOR SNPOST (mkCfg msF2 mo2)).
    { exists s, F, fc, []. split; [exact KR2|]. split; [exact (ah_mpres_trans H HHb mo mo' mo2 MP' MP2)|].
      split; [exact FZ|]. split; [exact CUT | unfold LbB_SnB.sn_e; cbn [x_s]; clear; lia]. }
    intros c' X3. exact (LbB_SnXE1.sx_end H HHbp E0 ff fp 0 0 0 0 XP FRESH ents c' X3).
  Qed.

  Lemma sn_diag2A : bv_unsigned sp mod 32 = 0 -> FPSteps.frm_zero fc ->
    forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> LbB_Sn.sn_d2A H ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 this po tid pcons icount LF bl bc (as_VIS H s msF') ->
    as_SR H SNPOST (mkCfg msF' mo').
  Proof using All.
    intros C32 FZ msF' mo' KR' MP' HD.
    destruct (LbB_SnB.sn_bridgeA H HHbp ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 this po tid pcons icount lo LF bl bc LB
                TIDR DSW DSO DSin ICN STK CEIL LO AC0 LV0 TP RFS0 LFn s mo CH B shi XP C32 _ _ HD)
      as (ff & fp & R & m & E & RF & FRESH & HPX & MI & HRT & HSF & HFT & HHT).
    eapply (ahh_evt_then H HHb _ _ s msF' _ mo' KR' E).
    { exact (LbB_SnXP2.sx_ph1 H HHbp E0 ff fp 0 0 0 0 XP FRESH THI PCI R F fc m [] s LB RF HRT HSF HFT HHT HPX MI). }
    intros msF2 mo2 KR2 MP2 CUT.
    eapply (LbB_SnXR2.sx_ph2 H HHbp E0 ff fp 0 0 0 0 XP FRESH THI PCI HPDIAG HCSEQ HU32 HDTOR SNPOST (mkCfg msF2 mo2)).
    { exists s, F, fc, []. split; [exact KR2|]. split; [exact (ah_mpres_trans H HHb mo mo' mo2 MP' MP2)|].
      split; [exact FZ|]. split; [exact CUT | unfold LbB_SnB.sn_e; cbn [x_s]; clear; lia]. }
    intros c' X3. exact (LbB_SnXE2.sx_end H HHbp E0 ff fp 0 0 0 0 XP FRESH ents c' X3).
  Qed.

  Lemma sn_diag1B : bv_unsigned sp mod 32 = 16 -> FPSteps.frm_zero fc ->
    forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> LbB_Sn.sn_d1B H ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 this po tid pcons icount LF bl bc (as_VIS H s msF') ->
    as_SR H SNPOST (mkCfg msF' mo').
  Proof using All.
    intros C32 FZ msF' mo' KR' MP' HD.
    destruct (LbB_SnB.sn_bridgeB H HHbp ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 this po tid pcons icount lo LF bl bc LB
                TIDR DSW DSO DSin ICN STK CEIL LO AC0 LV0 TP RFS0 LFn s mo CH B shi XP C32 _ _ HD)
      as (ff & fp & R & m & E & RF & FRESH & HPX & MI & HRT & HSF & HFT & HHT).
    eapply (ahh_evt_then H HHb _ _ s msF' _ mo' KR' E).
    { exact (LbB_SnXP1.sx_ph1 H HHbp E0 ff fp 0 0 0 0 XP FRESH THI PCI R F fc m [] s LB RF HRT HSF HFT HHT HPX MI). }
    intros msF2 mo2 KR2 MP2 CUT.
    eapply (LbB_SnXR1.sx_ph2 H HHbp E0 ff fp 0 0 0 0 XP FRESH THI PCI HPDIAG HCSEQ HU32 HDTOR SNPOST (mkCfg msF2 mo2)).
    { exists s, F, fc, []. split; [exact KR2|]. split; [exact (ah_mpres_trans H HHb mo mo' mo2 MP' MP2)|].
      split; [exact FZ|]. split; [exact CUT | unfold LbB_SnB.sn_e; cbn [x_s]; clear; lia]. }
    intros c' X3. exact (LbB_SnXE1.sx_end H HHbp E0 ff fp 0 0 0 0 XP FRESH ents c' X3).
  Qed.

  Lemma sn_diag2B : bv_unsigned sp mod 32 = 16 -> FPSteps.frm_zero fc ->
    forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> LbB_Sn.sn_d2B H ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 this po tid pcons icount LF bl bc (as_VIS H s msF') ->
    as_SR H SNPOST (mkCfg msF' mo').
  Proof using All.
    intros C32 FZ msF' mo' KR' MP' HD.
    destruct (LbB_SnB.sn_bridgeB H HHbp ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 this po tid pcons icount lo LF bl bc LB
                TIDR DSW DSO DSin ICN STK CEIL LO AC0 LV0 TP RFS0 LFn s mo CH B shi XP C32 _ _ HD)
      as (ff & fp & R & m & E & RF & FRESH & HPX & MI & HRT & HSF & HFT & HHT).
    eapply (ahh_evt_then H HHb _ _ s msF' _ mo' KR' E).
    { exact (LbB_SnXP2.sx_ph1 H HHbp E0 ff fp 0 0 0 0 XP FRESH THI PCI R F fc m [] s LB RF HRT HSF HFT HHT HPX MI). }
    intros msF2 mo2 KR2 MP2 CUT.
    eapply (LbB_SnXR2.sx_ph2 H HHbp E0 ff fp 0 0 0 0 XP FRESH THI PCI HPDIAG HCSEQ HU32 HDTOR SNPOST (mkCfg msF2 mo2)).
    { exists s, F, fc, []. split; [exact KR2|]. split; [exact (ah_mpres_trans H HHb mo mo' mo2 MP' MP2)|].
      split; [exact FZ|]. split; [exact CUT | unfold LbB_SnB.sn_e; cbn [x_s]; clear; lia]. }
    intros c' X3. exact (LbB_SnXE2.sx_end H HHbp E0 ff fp 0 0 0 0 XP FRESH ents c' X3).
  Qed.

  Lemma sn_all : forall msF errv,
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 aw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 ASN_ENTRY) fc None m0 (seg_rom asegs) ->
    FPSteps.frm_zero fc -> as_RHEAP H s LB m0 -> as_AKREL H s (mkCfg msF mo) -> as_rauxv_ok H m0 B ->
    rw_cells asegs m0 (errno_addr tp) [C4 errv] -> stack0 m0 lo shi ->
    as_SR H SNPOST (mkCfg msF mo).
  Proof using All.
    intros msF errv VIS FZ RH KR RAUX ERRN S0.
    assert (C32 : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16) by (clear - SP16; Z.div_mod_to_equations; lia).
    destruct C32 as [C32|C32].
    - exact (LbB_Sn.sn_srA H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 aw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0
               this po tid pcons icount lo LF bl bc LB ents Ha0 Ha1 Ha2 TIDR DSA DSW DSO DS8 DSV DSin PCA PCO PC8 PCC PCfs DISJ ICN
               THA THO TH8 THfs THC1 THC2 UM0 USH UBL KOK STK CEIL LO SP16 SPHI SPOBJ MI0 AC0 LV0 TP RFS0 LFn THR
               C32 s msF mo B shi errv (sn_diag1A C32 FZ) (sn_diag2A C32 FZ) VIS FZ RH KR RAUX ERRN S0).
    - exact (LbB_Sn.sn_srB H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 aw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0
               this po tid pcons icount lo LF bl bc LB ents Ha0 Ha1 Ha2 TIDR DSA DSW DSO DS8 DSV DSin PCA PCO PC8 PCC PCfs DISJ ICN
               THA THO TH8 THfs THC1 THC2 UM0 USH UBL KOK STK CEIL LO SP16 SPHI SPOBJ MI0 AC0 LV0 TP RFS0 LFn THR
               C32 s msF mo B shi errv (sn_diag1B C32 FZ) (sn_diag2B C32 FZ) VIS FZ RH KR RAUX ERRN S0).
  Qed.
End SnD.
