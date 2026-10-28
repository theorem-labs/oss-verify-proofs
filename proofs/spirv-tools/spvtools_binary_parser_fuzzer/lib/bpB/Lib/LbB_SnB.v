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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnXT.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SnB.

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

  Definition sn_e : xent H :=
    XEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo s LB LF CH this pcons icount po tid aw bl bc lo B shi.
  Hypothesis XP : xpre H sn_e.

  Notation WpK ff fp :=
    (LbB_SnK.Wp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc 0 0 0 0) (only parsing).
  Notation WX ff fp := (LbB_SnXT.Wx H sn_e ff fp 0 0 0 0) (only parsing).

  Lemma wx_agree : forall ff fp, LbB_SnW.wagree 58 (WpK ff fp) (WX ff fp).
  Proof.
    intros ff fp.
    exact (LbB_SnW.wagree_prefix
             (Wp0 ++ [Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 pcons; Z_to_bv 64 icount; Z_to_bv 64 bl; Z_to_bv 64 bc])
             [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]
             [Z_to_bv 64 (xS1 sn_e); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]).
  Qed.

  Lemma xs1_A : bv_unsigned sp mod 32 = 0 -> xS1 sn_e = spz - 96.
  Proof. intros C32. unfold xS1, xSP, SX_FRAME. cbn [x_sp sn_e]. rewrite C32. clear; lia. Qed.

#[local] Definition HTLbASnB_0 : list expr := [EVar 45; EVar 44; EVar 43; EVar 42; EVar 41; EVar 40; EVar 39; EVar 38; EVar 34].
  Lemma sn_bridgeA : bv_unsigned sp mod 32 = 0 -> forall pc ms,
    LbB_Sn.sn_dF H ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 this po tid pcons icount LF bl bc pc
                 LbB_SnTA.RTK4 LbB_SnTA.SF4 LbB_SnTA.FT4 LbB_SnTA.HT4 ms ->
    exists ff fp R m, ms = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) /\ rfull R
      /\ fresh_frame H LF 4 ff fp
      /\ LbB_SnXT.Px H sn_e ff fp [] s LB m /\ mem_inv asegs m
      /\ rtbl (WX ff fp) R SNX_RT /\ ftbl (WX ff fp) (xS1 sn_e) m SNX_SF
      /\ ftbl (WX ff fp) ff m SNX_FT /\ ftbl (WX ff fp) (ff / 8) m SNX_HT.
  Proof.
    intros C32 pc ms (ff & fp & m2 & R & m & FRESH & MUW & WMW & MU3 & WM3 & E & RF & HRT & HSF & HFT & HHT & FW & PW1 & MI & RFS).
    pose proof (xs1_A C32) as ES1.
    pose proof (tw0_munch ff fp m2 m MUW MU3) as MUT.
    assert (WMT : wmono asegs m0 m) by (eapply wmono_trans; [exact WMW | exact WM3]).
    destruct (tw0_laws LB ff fp FRESH) as (W1' & W2' & W3').
    destruct (tw_keep ff fp m FRESH (tw0_tw ff fp m0 m MUT) WMT) as (ST' & LV' & AC' & DW').
    destruct (tw_place ff fp FRESH) as (K2 & K3 & K4 & K6 & B1 & B2 & B3 & B4 & AP & S1 & S2 & S3 & S4).
    pose proof p1_ranges as (R1 & R2 & R3). pose proof DSO as (O1 & _).
    pose proof (xpre_RH0 H sn_e XP) as RH0. cbn [x_s x_LB x_m sn_e] in RH0.
    pose proof XP as (_ & _ & _ & _ & _ & RAUX & _ & _ & _ & _ & _ & _ & (errv & ERRN) & _ & _ & _ & _ & _ & _ & _ & S0 & _).
    cbn [x_m x_B x_tp x_lo x_shi sn_e] in RAUX, ERRN, S0.
    pose proof (wx_agree ff fp) as WA.
    pose proof (LbB_SnW.rtbl_wch 58 _ _ R LbB_SnTA.RTK4 WA ltac:(vm_compute; reflexivity) HRT) as HRTx.
    pose proof (LbB_SnW.ftbl_wch 58 _ _ spz m LbB_SnTA.SF4 WA ltac:(vm_compute; reflexivity) HSF) as HSFx.
    pose proof (LbB_SnW.ftbl_wch 58 _ _ ff m LbB_SnTA.FT4 WA ltac:(vm_compute; reflexivity) HFT) as HFTx.
    pose proof (LbB_SnW.ftbl_wch 58 _ _ (ff / 8) m LbB_SnTA.HT4 WA ltac:(vm_compute; reflexivity) HHT) as HHTx.
    exists ff, fp, R, m. split; [exact E|]. split; [exact RF|]. split; [exact FRESH|].
    split.
    {
      unfold LbB_SnXT.Px, xinv. cbn [x_LF x_lo x_shi x_B x_tp x_LB x_m sn_e]. unfold xSP. cbn [x_sp sn_e].
      split; [exact RFS|]. split; [exact FRESH|].
      split; [eapply (ah_RHEAP_frame H HHb); [exact RH0 | exact MUT | exact WMT | exact W1']|].
      split; [exact AC'|]. split; [exact MI|].
      split; [eapply stack0_transport; [exact S0 | exact MUT | exact WMT | exact W2']|].
      split; [eapply (ah_rauxv_frame H HHb); [exact RAUX | exact MUT | exact WMT | exact W1']|].
      split.
      { exists errv. eapply rw_cells_transport; [exact ERRN | exact MUT | exact WMT |].
        unfold TW0. cbn [disjoint_from cells_size csize]. rewrite TP, unsigned_lit by (clear; unfold ATP; lia).
        clear - R1 R2 R3 B1 K2 K6 S3 O1. unfold ATP, AIMG_TOP, AFS_HDR, AFS_FLAGS, ADS_STACK in *. cbn. lia. }
      split; [exact ST'|].
      split.
      {
        unfold SX_SAVED, xsaved. cbn [x_s8 x_s7 x_s6 x_s5 x_s4 x_s3 x_s2 x_s1 x_s0 x_ra sn_e].
        replace (spz - 80) with (spz + -80) by (clear; lia).
        exact (rw_C8s_of_ftbl (WX ff fp) spz m LbB_SnTA.SF4
                 HTLbASnB_0
                 (EVar 46) (-80)
                 ltac:(intros i e Hi; do 10 (destruct i as [|i]; [injection Hi as <-; vm_compute; reflexivity|]); destruct i; discriminate Hi)
                 HSFx). }
      split.
      { unfold SX_FLAGP. apply rw_C8_of_CB.
        exact (ftbl_In (WX ff fp) ff m LbB_SnTA.FT4 1016 8%nat (EVar 53) HFTx ltac:(apply fent_in_In; vm_compute; reflexivity)). }
      split; [unfold SX_FLAGP; eapply wr_at_sub; [exact FW | clear; lia | clear; lia | clear; lia]|].
      split; [exact PW1|].
      split.
      { rewrite app_nil_r. exact (tw0_xpres s LB m ff fp RH0 MUT WMT). }
      split; [apply Forall_nil | exact LV']. }
    split; [exact MI|].
    split.
    {
      assert (G58 : edenot (wenv (WX ff fp)) (EVar 58) = Z_to_bv 64 (spz - 96)) by (cbn [edenot]; rewrite <- ES1; reflexivity).
      assert (GX : forall r, PropExec.getr R r = edenot (wenv (WX ff fp)) (EAlu ALU_ADD (EVar 33) (ELit (-96))) ->
                   PropExec.getr R r = edenot (wenv (WX ff fp)) (EVar 58)).
      { intros r G. rewrite G, G58. cbn [edenot]. change (ev (wenv (WX ff fp)) 33) with sp.
        rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite w_addm by (clear - R1 R2 R3; unfold ADS_STACK in *; lia).
        first [reflexivity | f_equal; clear; lia]. }
      pose proof (fun r e (Hi : In (r, e) LbB_SnTA.RTK4) => rtbl_In (WX ff fp) R LbB_SnTA.RTK4 r e HRTx Hi) as Y.
      unfold SNX_RT, rtbl.
      repeat (apply Forall_cons; [cbn [fst snd];
                first [ apply Y; apply LbB_DCtorK.inb_In'; vm_compute; reflexivity
                      | apply GX; apply Y; apply LbB_DCtorK.inb_In'; vm_compute; reflexivity ] |]).
      apply Forall_nil. }
    split.
    {
      unfold SNX_SF. apply Forall_cons; [| apply Forall_nil]. cbn beta iota.
      replace (xS1 sn_e + 8) with (spz + -88) by (rewrite ES1; clear; lia).
      exact (ftbl_In (WX ff fp) spz m LbB_SnTA.SF4 (-88) 8%nat (EVar 52) HSFx ltac:(apply fent_in_In; vm_compute; reflexivity)). }
    split.
    { apply (ftbl_sub (WX ff fp) ff m LbB_SnTA.FT4 SNX_FT HFTx). vm_compute. reflexivity. }
    apply (ftbl_sub (WX ff fp) (ff / 8) m LbB_SnTA.HT4 SNX_HT HHTx). vm_compute. reflexivity.
  Qed.

  Lemma xs1_B : bv_unsigned sp mod 32 = 16 -> xS1 sn_e = spz - 112.
  Proof. intros C32. unfold xS1, xSP, SX_FRAME. cbn [x_sp sn_e]. rewrite C32. clear; lia. Qed.

  Lemma sn_bridgeB : bv_unsigned sp mod 32 = 16 -> forall pc ms,
    LbB_Sn.sn_dF H ra sp gp tp s0 s1 aw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 this po tid pcons icount LF bl bc pc
                 LbB_SnTB.RTK4 LbB_SnTB.SF4 LbB_SnTB.FT4 LbB_SnTB.HT4 ms ->
    exists ff fp R m, ms = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) /\ rfull R
      /\ fresh_frame H LF 4 ff fp
      /\ LbB_SnXT.Px H sn_e ff fp [] s LB m /\ mem_inv asegs m
      /\ rtbl (WX ff fp) R SNX_RT /\ ftbl (WX ff fp) (xS1 sn_e) m SNX_SF
      /\ ftbl (WX ff fp) ff m SNX_FT /\ ftbl (WX ff fp) (ff / 8) m SNX_HT.
  Proof.
    intros C32 pc ms (ff & fp & m2 & R & m & FRESH & MUW & WMW & MU3 & WM3 & E & RF & HRT & HSF & HFT & HHT & FW & PW1 & MI & RFS).
    pose proof (xs1_B C32) as ES1.
    pose proof (tw0_munch ff fp m2 m MUW MU3) as MUT.
    assert (WMT : wmono asegs m0 m) by (eapply wmono_trans; [exact WMW | exact WM3]).
    destruct (tw0_laws LB ff fp FRESH) as (W1' & W2' & W3').
    destruct (tw_keep ff fp m FRESH (tw0_tw ff fp m0 m MUT) WMT) as (ST' & LV' & AC' & DW').
    destruct (tw_place ff fp FRESH) as (K2 & K3 & K4 & K6 & B1 & B2 & B3 & B4 & AP & S1 & S2 & S3 & S4).
    pose proof p1_ranges as (R1 & R2 & R3). pose proof DSO as (O1 & _).
    pose proof (xpre_RH0 H sn_e XP) as RH0. cbn [x_s x_LB x_m sn_e] in RH0.
    pose proof XP as (_ & _ & _ & _ & _ & RAUX & _ & _ & _ & _ & _ & _ & (errv & ERRN) & _ & _ & _ & _ & _ & _ & _ & S0 & _).
    cbn [x_m x_B x_tp x_lo x_shi sn_e] in RAUX, ERRN, S0.
    pose proof (wx_agree ff fp) as WA.
    pose proof (LbB_SnW.rtbl_wch 58 _ _ R LbB_SnTB.RTK4 WA ltac:(vm_compute; reflexivity) HRT) as HRTx.
    pose proof (LbB_SnW.ftbl_wch 58 _ _ spz m LbB_SnTB.SF4 WA ltac:(vm_compute; reflexivity) HSF) as HSFx.
    pose proof (LbB_SnW.ftbl_wch 58 _ _ ff m LbB_SnTB.FT4 WA ltac:(vm_compute; reflexivity) HFT) as HFTx.
    pose proof (LbB_SnW.ftbl_wch 58 _ _ (ff / 8) m LbB_SnTB.HT4 WA ltac:(vm_compute; reflexivity) HHT) as HHTx.
    exists ff, fp, R, m. split; [exact E|]. split; [exact RF|]. split; [exact FRESH|].
    split.
    {
      unfold LbB_SnXT.Px, xinv. cbn [x_LF x_lo x_shi x_B x_tp x_LB x_m sn_e]. unfold xSP. cbn [x_sp sn_e].
      split; [exact RFS|]. split; [exact FRESH|].
      split; [eapply (ah_RHEAP_frame H HHb); [exact RH0 | exact MUT | exact WMT | exact W1']|].
      split; [exact AC'|]. split; [exact MI|].
      split; [eapply stack0_transport; [exact S0 | exact MUT | exact WMT | exact W2']|].
      split; [eapply (ah_rauxv_frame H HHb); [exact RAUX | exact MUT | exact WMT | exact W1']|].
      split.
      { exists errv. eapply rw_cells_transport; [exact ERRN | exact MUT | exact WMT |].
        unfold TW0. cbn [disjoint_from cells_size csize]. rewrite TP, unsigned_lit by (clear; unfold ATP; lia).
        clear - R1 R2 R3 B1 K2 K6 S3 O1. unfold ATP, AIMG_TOP, AFS_HDR, AFS_FLAGS, ADS_STACK in *. cbn. lia. }
      split; [exact ST'|].
      split.
      {
        unfold SX_SAVED, xsaved. cbn [x_s8 x_s7 x_s6 x_s5 x_s4 x_s3 x_s2 x_s1 x_s0 x_ra sn_e].
        replace (spz - 80) with (spz + -80) by (clear; lia).
        exact (rw_C8s_of_ftbl (WX ff fp) spz m LbB_SnTB.SF4
                 HTLbASnB_0
                 (EVar 46) (-80)
                 ltac:(intros i e Hi; do 10 (destruct i as [|i]; [injection Hi as <-; vm_compute; reflexivity|]); destruct i; discriminate Hi)
                 HSFx). }
      split.
      { unfold SX_FLAGP. apply rw_C8_of_CB.
        exact (ftbl_In (WX ff fp) ff m LbB_SnTB.FT4 1016 8%nat (EVar 53) HFTx ltac:(apply fent_in_In; vm_compute; reflexivity)). }
      split; [unfold SX_FLAGP; eapply wr_at_sub; [exact FW | clear; lia | clear; lia | clear; lia]|].
      split; [exact PW1|].
      split.
      { rewrite app_nil_r. exact (tw0_xpres s LB m ff fp RH0 MUT WMT). }
      split; [apply Forall_nil | exact LV']. }
    split; [exact MI|].
    split.
    {
      assert (G58 : edenot (wenv (WX ff fp)) (EVar 58) = Z_to_bv 64 (spz - 112)) by (cbn [edenot]; rewrite <- ES1; reflexivity).
      assert (GX : forall r, PropExec.getr R r = edenot (wenv (WX ff fp)) (EAlu ALU_ADD (EVar 33) (ELit (-112))) ->
                   PropExec.getr R r = edenot (wenv (WX ff fp)) (EVar 58)).
      { intros r G. rewrite G, G58. cbn [edenot]. change (ev (wenv (WX ff fp)) 33) with sp.
        rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite w_addm by (clear - R1 R2 R3; unfold ADS_STACK in *; lia).
        first [reflexivity | f_equal; clear; lia]. }
      pose proof (fun r e (Hi : In (r, e) LbB_SnTB.RTK4) => rtbl_In (WX ff fp) R LbB_SnTB.RTK4 r e HRTx Hi) as Y.
      unfold SNX_RT, rtbl.
      repeat (apply Forall_cons; [cbn [fst snd];
                first [ apply Y; apply LbB_DCtorK.inb_In'; vm_compute; reflexivity
                      | apply GX; apply Y; apply LbB_DCtorK.inb_In'; vm_compute; reflexivity ] |]).
      apply Forall_nil. }
    split.
    {
      unfold SNX_SF. apply Forall_cons; [| apply Forall_nil]. cbn beta iota.
      replace (xS1 sn_e + 8) with (spz + -104) by (rewrite ES1; clear; lia).
      exact (ftbl_In (WX ff fp) spz m LbB_SnTB.SF4 (-104) 8%nat (EVar 52) HSFx ltac:(apply fent_in_In; vm_compute; reflexivity)). }
    split.
    { apply (ftbl_sub (WX ff fp) ff m LbB_SnTB.FT4 SNX_FT HFTx). vm_compute. reflexivity. }
    apply (ftbl_sub (WX ff fp) (ff / 8) m LbB_SnTB.HT4 SNX_HT HHTx). vm_compute. reflexivity.
  Qed.

End SnB.
