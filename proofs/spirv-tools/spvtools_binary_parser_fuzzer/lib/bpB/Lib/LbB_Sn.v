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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnK LbB_SnW LbB_SnFind LbB_SnTA LbB_SnTB LbB_SnA LbB_SnF LbB_SnAb LbB_SnFb LbB_SnQ.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Sn.

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

  Notation WpK ff fp nd nk bw enc :=
    (LbB_SnK.Wp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc) (only parsing).

  Definition sn_okF : machine_state -> Prop := fun ms =>
    exists ff fp m2 nd nk bw enc, fresh_frame H LF 4 ff fp /\ munch (W1 ff fp) m0 m2 /\ wmono asegs m0 m2
      /\ In (nd, (tid, (nk, bw, enc))) ents /\ nk <> 0 /\ 0 <= nk < 2 ^ 32 /\ 0 <= bw < 2 ^ 32 /\ 0 <= enc < 2 ^ 32
      /\ LbB_SnK.sn_Pok H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 po ff fp LF nk bw enc ms.

  Definition sn_dF (pc : Z) (RTK : list (reg * expr)) (SF FT HT : list fent) : machine_state -> Prop := fun ms =>
    exists ff fp m2 R m, fresh_frame H LF 4 ff fp /\ munch (W1 ff fp) m0 m2 /\ wmono asegs m0 m2
      /\ munch (LbB_SnK.W3 sp ff) m2 m /\ wmono asegs m2 m
      /\ ms = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) /\ rfull R
      /\ rtbl (WpK ff fp 0 0 0 0) R RTK /\ ftbl (WpK ff fp 0 0 0 0) spz m SF /\ ftbl (WpK ff fp 0 0 0 0) ff m FT
      /\ ftbl (WpK ff fp 0 0 0 0) (ff / 8) m HT
      /\ wr_at asegs m ff 1024 /\ wr_at asegs m fp 1
      /\ mem_inv asegs m /\ as_RFS H ((4, ff, fp) :: LF) m.
  Definition SN_D1 : Z := 0xf98d0.
  Definition SN_D2 : Z := 0xf9bf8.
  Definition sn_d1A := sn_dF SN_D1 LbB_SnTA.RTK4 LbB_SnTA.SF4 LbB_SnTA.FT4 LbB_SnTA.HT4.
  Definition sn_d2A := sn_dF SN_D2 LbB_SnTA.RTK4 LbB_SnTA.SF4 LbB_SnTA.FT4 LbB_SnTA.HT4.
  Definition sn_d1B := sn_dF SN_D1 LbB_SnTB.RTK4 LbB_SnTB.SF4 LbB_SnTB.FT4 LbB_SnTB.HT4.
  Definition sn_d2B := sn_dF SN_D2 LbB_SnTB.RTK4 LbB_SnTB.SF4 LbB_SnTB.FT4 LbB_SnTB.HT4.

  Definition sn_midA : machine_state -> Prop := fun ms => sn_okF ms \/ sn_d1A ms \/ sn_d2A ms.
  Lemma sn_mid_okA : forall ms, sn_okF ms -> sn_midA ms. Proof. intros ms X. left. exact X. Qed.
  Lemma sn_mid_d1A : forall ms, sn_d1A ms -> sn_midA ms. Proof. intros ms X. right; left. exact X. Qed.
  Lemma sn_mid_d2A : forall ms, sn_d2A ms -> sn_midA ms. Proof. intros ms X. right; right. exact X. Qed.

#[local] Definition HTLbASn_0 : list (reg * expr) := [(1%bv, EVar 34); (2%bv, EVar 33); (3%bv, EVar 50); (4%bv, EVar 51); (8%bv, EVar 38); (9%bv, EVar 39); (18%bv, EVar 40); (19%bv, EVar 41); (20%bv, EVar 42); (21%bv, EVar 43); (22%bv, EVar 44); (23%bv, EVar 45); (24%bv, EVar 46); (25%bv, EVar 47); (26%bv, EVar 48); (27%bv, EVar 49); (10%bv, EVar 32); (11%bv, EVar 35); (12%bv, EVar 36); (13%bv, EVar 37)].
  Lemma sn_fullA : bv_unsigned sp mod 32 = 0 ->
    evt asegs sn_midA (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 aw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 ASN_ENTRY) fc None m0 (seg_rom asegs)).
  Proof using All.
    intros C32. pose proof p1_ranges as (R1' & R2' & R3').
    assert (RF0 : rfull (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 aw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
      by apply rfull_mkR.
    assert (HRT : rtbl Wp0 (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 aw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  HTLbASn_0).
    { unfold rtbl. repeat constructor; cbn [fst snd]; [exact Ha0 | exact Ha1 | exact Ha2]. }
    assert (HSF : ftbl Wp0 spz m0 []) by constructor.
    assert (HP : P1w m0) by (split; [apply munch_refl | apply wmono_refl]).
    unfold ASN_ENTRY.

    dkrun1 HRT HSF HP MI0 600%nat [AFS_MALLOC_4].
    { constructor. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
    lazymatch type of HTS1 with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS1; clear E end.
    apply Forall_cons_iff in HTS1 as [HSF1 _]. cbn [fst snd] in HSF1.
    cbn [s_pc].
    destruct (p1_keep m1 HP1 HMI1) as (AC1 & LV1 & ST1).

    assert (K1 : PropExec.getr R1 1 = Z_to_bv 64 0xf943c).
    { apply (rtbl_In Wp0 R1 _ 1%bv (ELit 0xf943c) HRT1). apply LbB_DCtorK.inb_In'. vm_compute. reflexivity. }
    assert (K4 : PropExec.getr R1 4 = tp).
    { apply (rtbl_In Wp0 R1 _ 4%bv (EVar 51) HRT1). apply LbB_DCtorK.inb_In'. vm_compute. reflexivity. }
    assert (K2e : PropExec.getr R1 2 = Z_to_bv 64 ((spz - 96) - (spz - 96) mod 32)).
    { rewrite (rtbl_In Wp0 R1 _ 2%bv (EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-96))) (ELit 5))) HRT1
                ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)). cbn [edenot].
      change (ev (wenv Wp0) 33) with sp.
      assert (EA : alu64 ALU_ADD sp (Z_to_bv 64 (-96)) = Z_to_bv 64 (spz - 96)).
      { rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite w_addm by (clear - R1' R2' R3'; unfold ADS_STACK in *; lia).
        f_equal; clear; lia. }
      rewrite EA. rewrite pd_mul32 by (clear - R1' R2' R3'; unfold ADS_STACK in *; lia). reflexivity. }

    lazymatch type of HRT1 with rtbl _ _ ?T1 =>
      let Tk := eval vm_compute in (keptk T1) in
      assert (HKR1 : rtbl Wp0 R1 Tk) by (apply (rtbl_sub Wp0 R1 T1 Tk HRT1); vm_compute; reflexivity)
    end.
    unfold winsT in MU1. cbn [map tB tlo thi tS0] in MU1.
    destruct (ah_RFS_range H HHb LF m0 RFS0) as [FO0 _]. pose proof FO0 as (B1 & B2 & B3 & B4).
    assert (RFS1 : as_RFS H LF m1).
    { eapply (ah_RFS_frame H HHb); [exact RFS0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd].
      clear - R1' R2' R3' B2. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, ADS_STACK, AFS_SIZE in *. lia. }
    assert (THR1 : athr_cells m1).
    { eapply (athr_keep m0 m1 (spz + -8192) (spz + 0)); [exact THR | exact MU1 | exact WM1 | clear - R2'; unfold ADS_STACK in *; lia]. }
    assert (K2 : PropExec.getr R1 2 = Z_to_bv 64 (spz - 96)).
    { rewrite K2e. f_equal. clear - C32. Z.div_mod_to_equations. lia. }
    assert (Us : bv_unsigned (PropExec.getr R1 2) = spz - 96).
    { rewrite K2. apply unsigned_lit. clear - R1' R2' R3'. unfold ADS_STACK in *. lia. }
    pose proof LO as LO'. unfold ADS_STACK in LO'.
    rewrite (MS_full_eq R1 F _ fc m1 _ RF1).
    eapply evt_cut.
    { apply (@LbB_SnQ.SM4 HCEIL H HHbp (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) (PropExec.getr R1 5)
               (PropExec.getr R1 6) (PropExec.getr R1 7) (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10)
               (PropExec.getr R1 11) (PropExec.getr R1 12) (PropExec.getr R1 13) (PropExec.getr R1 14) (PropExec.getr R1 15)
               (PropExec.getr R1 16) (PropExec.getr R1 17) (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20)
               (PropExec.getr R1 21) (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25)
               (PropExec.getr R1 26) (PropExec.getr R1 27) (PropExec.getr R1 28) (PropExec.getr R1 29) (PropExec.getr R1 30)
               (PropExec.getr R1 31) F fc m1 LF lo RFS1 ltac:(clear - LFn; unfold AFS_MAXLIVE, AFS_MAXLIVE_BP in *; lia)).
      - rewrite Us. destruct (stk_split asegs m1 lo (spz - 96) spz ST1 ltac:(clear - LO'; lia)) as [S _]. exact S.
      - exact CEIL.
      - rewrite Us. clear - LO'. unfold AFS_STACK in *. lia.
      - exact HMI1.
      - rewrite K4. exact TP.
      - exact AC1.
      - exact THR1. }
    intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & ff & fp & junk1 & junk2
                & E2 & MU2 & WM2 & MI2 & ST2 & RF2 & FRC & SHF & FLG & AC2).
    subst ms2. rewrite K1, ret_pc_even; [| clear; lia | reflexivity].
    lazymatch goal with |- evt _ _ (MS ?RR _ _ _ _ _ _) => remember RR as R2 eqn:ER2 end.
    assert (RF2' : rfull R2) by (rewrite ER2; apply rfull_mkR).
    assert (KP : forall r, In r KEPT -> PropExec.getr R2 r = PropExec.getr R1 r).
    { intros r Hr. rewrite ER2. apply (getr_mkR_keptR R1); [exact (eq_sym K1) | exact Hr]. }
    destruct (new_frame m2 ff fp RF2) as (FRESH & FFDS & FFPC & FPPC & FPDS & HULL & DSM & DSH & THF & THP).
    pose proof FRESH as (FFR & FSB_OK & _).
    pose proof FFR as (K1' & K2' & K3' & (K4' & K5') & K6'). unfold fsz in K3'. change (64 * 2 ^ 4) with 1024 in K3'.
    assert (MUW : munch (W1 ff fp) m0 m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; apply sub_fp_of.
      - apply Forall_cons; [| apply Forall_nil]. exists (spz - 8192, spz). split; [left; reflexivity | cbn; clear; lia].
      - rewrite Us. unfold W1.
        apply Forall_cons;
          [exists (spz - 8192, spz); split; [left; reflexivity | cbn; clear; unfold AFS_STACK in *; lia]|].
        apply Forall_cons; [exists (as_FSB H, as_FSB H + AFS_FLAGS); split; [right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (fp, fp + 1); split; [right; right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons;
          [exists (ff, ff + 1024); split; [right; right; right; left; reflexivity | cbn; unfold fsz; cbn; clear; lia]|].
        apply Forall_cons;
          [exists (sh ff, sh ff + 128); split; [right; right; right; right; left; reflexivity | cbn; unfold fshn; cbn; clear; lia]|].
        apply Forall_nil. }
    assert (WMW : wmono asegs m0 m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
    destruct (W1_keep m2 ff fp MUW WMW FSB_OK FFR FFDS FFPC FPPC FPDS HULL DSM THF THP)
      as (DSA2 & DSW2 & DSV2 & PCA2 & PCC2 & LV2 & ST2' & THA2).
    assert (NE1 : Forall (fun iv : Z * Z => fst iv < snd iv) (W1 ff fp)).
    { unfold W1. repeat (apply Forall_cons; [cbn [fst snd]; clear; unfold AFS_FLAGS; lia|]). apply Forall_nil. }
    destruct (quiet_keep ff fp (W1 ff fp) m2 FRESH THF THP (W1_sub ff fp) NE1 MUW WMW) as (THC1' & THC2' & UM2 & UG1' & UG2' & UG3').
    assert (FRW2 : wr_at asegs m2 ff 1024) by (destruct FRC as [_ W]; exact W).
    assert (FSV2 : shvis m2 ff (ff + 1024)) by exact (ah_frm_shvis H HHb _ m2 (4, ff, fp) RF2 (or_introl eq_refl)).
    assert (FSW2 : wr_at asegs m2 (sh ff) 128) by (destruct SHF as (_ & _ & _ & W); exact W).
    assert (FLW2 : wr_at asegs m2 fp 1) by (destruct FLG as [_ W]; exact W).

    assert (SPOBJk : forall O n, O = po /\ n = LbB_SnK.PO_SIZE \/ O = pcons /\ n = 48 ->
                     O + n <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= O).
    { intros O n [[-> ->] | [-> ->]]; [exact (SPOBJ po 20 ltac:(clear; tauto)) | exact (SPOBJ pcons 48 ltac:(clear; tauto))]. }
    assert (THSk : LbB_SnK.dj2 (this + 288) (bv_unsigned sp - ADS_STACK) (bv_unsigned sp) this)
      by exact (SPOBJ this 288 ltac:(clear; tauto)).
    assert (THFk : LbB_SnK.dj2 (ff + 1024) this (this + 288) ff) by exact THF.
    assert (THPk : LbB_SnK.dj2 (fp + 1) this (this + 288) fp) by exact THP.
    assert (THDk : LbB_SnK.dj2 (this + 272) po (po + LbB_SnK.PO_SIZE) this) by exact po_this.
    assert (TIDk : LbB_SnK.rg 0 tid (2 ^ 32)) by exact TIDR.
    assert (UFOk : forall a, umap_foot 32 (this + 136) bl bc ents a ->
              outside [(bv_unsigned sp - 16384, bv_unsigned sp); (po, po + LbB_SnK.PO_SIZE); (ff, ff + 1024); (sh ff, sh ff + 128); (fp, fp + 1)] a
              /\ outside [(bv_unsigned sp - 16384, bv_unsigned sp); (po, po + LbB_SnK.PO_SIZE); (ff, ff + 1024); (sh ff, sh ff + 128); (fp, fp + 1)] (a / 8 + SHBASE)
              /\ 0 <= a < 2 ^ 47).
    { assert (SUBk : sub_fp [(bv_unsigned sp - 16384, bv_unsigned sp); (po, po + LbB_SnK.PO_SIZE); (ff, ff + 1024); (sh ff, sh ff + 128); (fp, fp + 1)]
                            (UW ff fp)).
      { apply sub_fp_of. unfold UW, LbB_SnK.PO_SIZE.
        apply Forall_cons; [sfp_in (spz - 16384, spz)|]. apply Forall_cons; [sfp_in (po, po + 20)|].
        apply Forall_cons; [sfp_in (ff, ff + 1024)|]. apply Forall_cons; [sfp_in (sh ff, sh ff + 128)|].
        apply Forall_cons; [sfp_in (fp, fp + 1)|]. apply Forall_nil. }
      intros a Ha. destruct (quiet_out ff fp a FRESH THF THP (quiet_foot a Ha)) as (O1 & O2 & Ra).
      split; [exact (SUBk a O1)|]. split; [exact (SUBk _ O2) | exact Ra]. }

    assert (HSF2 : ftbl (WpK ff fp 0 0 0 0) spz m2 LbB_SnA.SF2).
    { change (WpK ff fp 0 0 0 0)
        with (Wp0 ++ [Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 pcons; Z_to_bv 64 icount; Z_to_bv 64 bl; Z_to_bv 64 bc;
                      Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]).
      apply ftbl_wext; [vm_compute; reflexivity|].
      eapply (ftbl_munch Wp0 spz m1 m2 _ _ (-96) 0);
        [ apply (ftbl_sub _ _ _ _ _ HSF1); vm_compute; reflexivity | exact MU2 | exact WM2 | vm_compute; reflexivity |].
      rewrite Us. cbn [disjoint_from].
      pose proof aceil_facts as ((A1 & A2) & _).
      assert (SHF0 : sh ff + 128 <= spz - 8192).
      { clear - K3' B2 A1 R2' R3'. unfold sh, ASHADOW_BASE, AFS_SIZE, ADS_STACK in *. Z.div_mod_to_equations. lia. }
      clear - K2' K3' K6' B2 SHF0 R2' R3' A1. unfold AFS_STACK, ADS_STACK, AFS_SIZE, AFS_HDR, AFS_FLAGS, fsz, fshn in *.
      cbn in *. lia. }
    assert (HFT2 : ftbl (WpK ff fp 0 0 0 0) ff m2 LbB_SnA.FT2).
    { apply (ftbl_of_C8 _ ff m2 1016 (EVar 53)).
      apply (proj1 (rw_cells_app asegs m2 ff [CB 24 junk1; C8 (PropExec.getr R1 2); CB (Z.to_nat (fsz 4 - 40)) junk2]
                                 [C8 (Z_to_bv 64 fp)])) in FRC.
      destruct FRC as [_ FRC2]. exact FRC2. }
    assert (HHT2 : ftbl (WpK ff fp 0 0 0 0) (ff / 8) m2 []) by constructor.

    lazymatch type of HKR1 with rtbl _ _ ?Tk =>
      assert (HKW : rtbl (WpK ff fp 0 0 0 0) R2 Tk)
    end.
    { change (WpK ff fp 0 0 0 0)
        with (Wp0 ++ [Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 pcons; Z_to_bv 64 icount; Z_to_bv 64 bl; Z_to_bv 64 bc;
                      Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]).
      apply rtbl_wext; [vm_compute; reflexivity|].
      apply (rtbl_keep Wp0 R1 R2 _ KEPT HKR1); [vm_compute; reflexivity | exact KP]. }
    assert (EAd : forall d, 0 <= spz + d < 2 ^ 64 -> - 2 ^ 63 < d < 0 ->
              edenot (wenv (WpK ff fp 0 0 0 0)) (EAlu ALU_ADD (EVar 33) (ELit d)) = Z_to_bv 64 (spz + d)).
    { intros d Hd1 Hd2. cbn [edenot]. change (ev (wenv (WpK ff fp 0 0 0 0)) 33) with sp.
      rewrite <- (Z_to_bv_bv_unsigned sp) at 1. apply w_addm; clear - Hd1 Hd2 R1'; lia. }
    assert (E10 : PropExec.getr R2 10 = Z_to_bv 64 ff) by (rewrite ER2; reflexivity).
    assert (E2' : PropExec.getr R2 2 = Z_to_bv 64 (spz - 96)) by (rewrite (KP 2%bv ltac:(inkept)); exact K2).
    assert (E9' : PropExec.getr R2 9 = Z_to_bv 64 (spz - 96)).
    { rewrite (KP 9%bv ltac:(inkept)).
      rewrite (rtbl_In Wp0 R1 _ 9%bv (EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-96))) (ELit 5))) HRT1
                ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)).
      rewrite <- (rtbl_In Wp0 R1 _ 2%bv (EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-96))) (ELit 5))) HRT1
                ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)). exact K2. }
    assert (HPW : LbB_SnK.Pw sp m2 po ff fp m2) by (split; [apply munch_refl | apply wmono_refl]).
    assert (HRT2 : rtbl (WpK ff fp 0 0 0 0) R2 LbB_SnA.RT2).
    { lazymatch type of HKW with rtbl _ _ ?Tk =>
        apply (rtbl_sub _ R2 ([(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-96))); (9%bv, EAlu ALU_ADD (EVar 33) (ELit (-96)));
                                (10%bv, EVar 52)] ++ Tk)); [| vm_compute; reflexivity] end.
      apply rtbl_app; [| exact HKW].
      unfold rtbl. apply Forall_cons.
      { cbn [fst snd]. rewrite E2', EAd by (clear - R1' R2' R3'; unfold ADS_STACK in *; lia). f_equal; clear; lia. }
      apply Forall_cons.
      { cbn [fst snd]. rewrite E9', EAd by (clear - R1' R2' R3'; unfold ADS_STACK in *; lia). f_equal; clear; lia. }
      apply Forall_cons; [cbn [fst snd]; exact E10 | apply Forall_nil]. }
    assert (NDk0 : LbB_SnK.rg 0 0 (2 ^ 64) /\ LbB_SnK.rg 0 0 (2 ^ 32) /\ LbB_SnK.rg 0 0 (2 ^ 32) /\ LbB_SnK.rg 0 0 (2 ^ 32))
      by (unfold LbB_SnK.rg; clear; lia).
    pose proof PCO as PCOk. pose proof DSO as DSOk. pose proof THO as THOk.
    eapply LbB_SnA.sn_pre with (H := H) (ra := ra) (sp := sp) (gp := gp) (tp := tp) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3)
      (s4 := s4) (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) (s10 := s10) (s11 := s11) (aw := aw)
      (m1 := m2) (this := this) (po := po) (tid := tid) (pcons := pcons) (icount := icount) (lo := lo) (ff := ff) (fp := fp)
      (LF := LF) (bl := bl) (bc := bc) (nd := 0) (nk := 0) (bw := 0) (enc := 0) (LBl := lbl LB) (ents := ents);
      try eassumption.
    -
      intros R' m' p v RF' Hin G10 HRT' HSF' HFT' HHT' HP' HMI' HRF' MU'. destruct v as [[nk bw] enc].
      destruct (u_node UM2 p tid (nk, bw, enc) Hin) as (_ & Np0 & Np1 & _ & _ & _ & _ & NV & _).
      cbn in NV. destruct NV as ((Rnk & _) & (Rbw & _) & (Renc & _)).
      change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rnk, Rbw, Renc.
      assert (WA : LbB_SnW.wagree 58 (WpK ff fp 0 0 0 0) (WpK ff fp p nk bw enc)).
      { exact (LbB_SnW.wagree_prefix
                 (Wp0 ++ [Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 pcons; Z_to_bv 64 icount; Z_to_bv 64 bl; Z_to_bv 64 bc])
                 [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]
                 [Z_to_bv 64 p; Z_to_bv 64 nk; Z_to_bv 64 bw; Z_to_bv 64 enc]). }
      pose proof (LbB_SnW.rtbl_wch 58 _ _ R' LbB_SnTA.RTK4 WA ltac:(vm_compute; reflexivity) HRT') as HRTn.
      pose proof (LbB_SnW.ftbl_wch 58 _ _ spz m' LbB_SnTA.SF4 WA ltac:(vm_compute; reflexivity) HSF') as HSFn.
      pose proof (LbB_SnW.ftbl_wch 58 _ _ ff m' LbB_SnTA.FT4 WA ltac:(vm_compute; reflexivity) HFT') as HFTn.
      pose proof (LbB_SnW.ftbl_wch 58 _ _ (ff / 8) m' LbB_SnTA.HT4 WA ltac:(vm_compute; reflexivity) HHT') as HHTn.
      assert (HRT5 : rtbl (WpK ff fp p nk bw enc) R' ((10%bv, EVar 58) :: LbB_SnTA.RTK4)).
      { apply Forall_cons; [cbn [fst snd]; exact G10 | exact HRTn]. }
      clear HRT' HSF' HFT' HHT' HRTn.
      destruct (Z.eq_dec nk 0) as [E0|NZ].
      + assert (NDk : LbB_SnK.rg 0 p (2 ^ 64) /\ LbB_SnK.rg 0 nk (2 ^ 32) /\ LbB_SnK.rg 0 bw (2 ^ 32) /\ LbB_SnK.rg 0 enc (2 ^ 32))
          by (unfold LbB_SnK.rg; clear - Np0 Np1 Rnk Rbw Renc; lia).
        clear NDk0.
        eapply LbB_SnF.sn_found0 with (H := H) (ra := ra) (sp := sp) (gp := gp) (tp := tp) (s0 := s0) (s1 := s1) (s2 := s2)
            (s3 := s3) (s4 := s4) (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) (s10 := s10) (s11 := s11) (aw := aw)
            (m1 := m2) (this := this) (po := po) (tid := tid) (pcons := pcons) (icount := icount) (lo := lo) (ff := ff) (fp := fp)
            (LF := LF) (bl := bl) (bc := bc) (nd := p) (nk := nk) (bw := bw) (enc := enc) (LBl := lbl LB) (ents := ents);
            try eassumption.
        intros R'' m'' RF'' HRT'' HSF'' HFT'' HHT'' HP'' HMI'' HRF'' MU''.
        pose proof (LbB_SnW.wagree_sym _ _ _ WA) as WA'.
        pose proof (LbB_SnW.rtbl_wch 58 _ _ R'' LbB_SnTA.RTK4 WA' ltac:(vm_compute; reflexivity) HRT'') as HRTd.
        pose proof (LbB_SnW.ftbl_wch 58 _ _ spz m'' LbB_SnTA.SF4 WA' ltac:(vm_compute; reflexivity) HSF'') as HSFd.
        pose proof (LbB_SnW.ftbl_wch 58 _ _ ff m'' LbB_SnTA.FT4 WA' ltac:(vm_compute; reflexivity) HFT'') as HFTd.
        pose proof (LbB_SnW.ftbl_wch 58 _ _ (ff / 8) m'' LbB_SnTA.HT4 WA' ltac:(vm_compute; reflexivity) HHT'') as HHTd.
        apply evt_done. apply sn_mid_d2A. exists ff, fp, m2, R'', m''.
        split; [exact FRESH|]. split; [exact MUW|]. split; [exact WMW|].
        split; [exact (munch_trans _ _ _ _ MU' MU'')|]. split; [exact (proj2 HP'')|].
        split; [reflexivity|]. split; [exact RF''|]. split; [exact HRTd|]. split; [exact HSFd|]. split; [exact HFTd|].
        split; [exact HHTd|].
        split; [eapply wr_at_transport; [exact FRW2 | exact (proj2 HP'')]|].
        split; [eapply wr_at_transport; [exact FLW2 | exact (proj2 HP'')]|].
        split; [exact HMI'' | exact HRF''].
      + assert (NDk : LbB_SnK.rg 0 p (2 ^ 64) /\ LbB_SnK.rg 0 nk (2 ^ 32) /\ LbB_SnK.rg 0 bw (2 ^ 32) /\ LbB_SnK.rg 0 enc (2 ^ 32))
          by (unfold LbB_SnK.rg; clear - Np0 Np1 Rnk Rbw Renc; lia).
        clear NDk0.
        pose proof (proj1 (Forall_forall _ _) KOK _ Hin) as KH. cbn [fst snd t3a t3c] in KH.
        assert (NK4 : nk < 4) by (clear - KH; lia). assert (EN16 : enc < 16) by (clear - KH; lia).
        eapply evt_mono.
        { eapply LbB_SnF.sn_found with (H := H) (ra := ra) (sp := sp) (gp := gp) (tp := tp) (s0 := s0) (s1 := s1) (s2 := s2)
            (s3 := s3) (s4 := s4) (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) (s10 := s10) (s11 := s11) (aw := aw)
            (m1 := m2) (this := this) (po := po) (tid := tid) (pcons := pcons) (icount := icount) (lo := lo) (ff := ff) (fp := fp)
            (LF := LF) (bl := bl) (bc := bc) (nd := p) (nk := nk) (bw := bw) (enc := enc) (LBl := lbl LB) (ents := ents);
            try eassumption. }
        intros ms HPok. apply sn_mid_okA. exists ff, fp, m2, p, nk, bw, enc.
        split; [exact FRESH|]. split; [exact MUW|]. split; [exact WMW|]. split; [exact Hin|]. split; [exact NZ|].
        split; [exact Rnk|]. split; [exact Rbw|]. split; [exact Renc | exact HPok].
    -
      intros R' m' RF' HRT' HSF' HFT' HHT' HP' HMI' HRF' MU'. apply evt_done. apply sn_mid_d1A. exists ff, fp, m2, R', m'.
      split; [exact FRESH|]. split; [exact MUW|]. split; [exact WMW|]. split; [exact MU'|]. split; [exact (proj2 HP')|].
      split; [reflexivity|]. split; [exact RF'|].
      split; [exact HRT'|]. split; [exact HSF'|]. split; [exact HFT'|]. split; [exact HHT'|].
      split; [eapply wr_at_transport; [exact FRW2 | exact (proj2 HP')]|].
      split; [eapply wr_at_transport; [exact FLW2 | exact (proj2 HP')]|].
      split; [exact HMI' | exact HRF'].
  Qed.
  Definition sn_midB : machine_state -> Prop := fun ms => sn_okF ms \/ sn_d1B ms \/ sn_d2B ms.
  Lemma sn_mid_okB : forall ms, sn_okF ms -> sn_midB ms. Proof. intros ms X. left. exact X. Qed.
  Lemma sn_mid_d1B : forall ms, sn_d1B ms -> sn_midB ms. Proof. intros ms X. right; left. exact X. Qed.
  Lemma sn_mid_d2B : forall ms, sn_d2B ms -> sn_midB ms. Proof. intros ms X. right; right. exact X. Qed.

  Lemma sn_fullB : bv_unsigned sp mod 32 = 16 ->
    evt asegs sn_midB (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 aw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 ASN_ENTRY) fc None m0 (seg_rom asegs)).
  Proof using All.
    intros C32. pose proof p1_ranges as (R1' & R2' & R3').
    assert (RF0 : rfull (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 aw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
      by apply rfull_mkR.
    assert (HRT : rtbl Wp0 (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 aw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  HTLbASn_0).
    { unfold rtbl. repeat constructor; cbn [fst snd]; [exact Ha0 | exact Ha1 | exact Ha2]. }
    assert (HSF : ftbl Wp0 spz m0 []) by constructor.
    assert (HP : P1w m0) by (split; [apply munch_refl | apply wmono_refl]).
    unfold ASN_ENTRY.

    dkrun1 HRT HSF HP MI0 600%nat [AFS_MALLOC_4].
    { constructor. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
    lazymatch type of HTS1 with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS1; clear E end.
    apply Forall_cons_iff in HTS1 as [HSF1 _]. cbn [fst snd] in HSF1.
    cbn [s_pc].
    destruct (p1_keep m1 HP1 HMI1) as (AC1 & LV1 & ST1).

    assert (K1 : PropExec.getr R1 1 = Z_to_bv 64 0xf943c).
    { apply (rtbl_In Wp0 R1 _ 1%bv (ELit 0xf943c) HRT1). apply LbB_DCtorK.inb_In'. vm_compute. reflexivity. }
    assert (K4 : PropExec.getr R1 4 = tp).
    { apply (rtbl_In Wp0 R1 _ 4%bv (EVar 51) HRT1). apply LbB_DCtorK.inb_In'. vm_compute. reflexivity. }
    assert (K2e : PropExec.getr R1 2 = Z_to_bv 64 ((spz - 96) - (spz - 96) mod 32)).
    { rewrite (rtbl_In Wp0 R1 _ 2%bv (EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-96))) (ELit 5))) HRT1
                ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)). cbn [edenot].
      change (ev (wenv Wp0) 33) with sp.
      assert (EA : alu64 ALU_ADD sp (Z_to_bv 64 (-96)) = Z_to_bv 64 (spz - 96)).
      { rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite w_addm by (clear - R1' R2' R3'; unfold ADS_STACK in *; lia).
        f_equal; clear; lia. }
      rewrite EA. rewrite pd_mul32 by (clear - R1' R2' R3'; unfold ADS_STACK in *; lia). reflexivity. }

    lazymatch type of HRT1 with rtbl _ _ ?T1 =>
      let Tk := eval vm_compute in (keptk T1) in
      assert (HKR1 : rtbl Wp0 R1 Tk) by (apply (rtbl_sub Wp0 R1 T1 Tk HRT1); vm_compute; reflexivity)
    end.
    unfold winsT in MU1. cbn [map tB tlo thi tS0] in MU1.
    destruct (ah_RFS_range H HHb LF m0 RFS0) as [FO0 _]. pose proof FO0 as (B1 & B2 & B3 & B4).
    assert (RFS1 : as_RFS H LF m1).
    { eapply (ah_RFS_frame H HHb); [exact RFS0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd].
      clear - R1' R2' R3' B2. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, ADS_STACK, AFS_SIZE in *. lia. }
    assert (THR1 : athr_cells m1).
    { eapply (athr_keep m0 m1 (spz + -8192) (spz + 0)); [exact THR | exact MU1 | exact WM1 | clear - R2'; unfold ADS_STACK in *; lia]. }
    assert (K2 : PropExec.getr R1 2 = Z_to_bv 64 (spz - 112)).
    { rewrite K2e. f_equal. clear - C32. Z.div_mod_to_equations. lia. }
    assert (Us : bv_unsigned (PropExec.getr R1 2) = spz - 112).
    { rewrite K2. apply unsigned_lit. clear - R1' R2' R3'. unfold ADS_STACK in *. lia. }
    pose proof LO as LO'. unfold ADS_STACK in LO'.
    rewrite (MS_full_eq R1 F _ fc m1 _ RF1).
    eapply evt_cut.
    { apply (@LbB_SnQ.SM4 HCEIL H HHbp (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) (PropExec.getr R1 5)
               (PropExec.getr R1 6) (PropExec.getr R1 7) (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10)
               (PropExec.getr R1 11) (PropExec.getr R1 12) (PropExec.getr R1 13) (PropExec.getr R1 14) (PropExec.getr R1 15)
               (PropExec.getr R1 16) (PropExec.getr R1 17) (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20)
               (PropExec.getr R1 21) (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25)
               (PropExec.getr R1 26) (PropExec.getr R1 27) (PropExec.getr R1 28) (PropExec.getr R1 29) (PropExec.getr R1 30)
               (PropExec.getr R1 31) F fc m1 LF lo RFS1 ltac:(clear - LFn; unfold AFS_MAXLIVE, AFS_MAXLIVE_BP in *; lia)).
      - rewrite Us. destruct (stk_split asegs m1 lo (spz - 112) spz ST1 ltac:(clear - LO'; lia)) as [S _]. exact S.
      - exact CEIL.
      - rewrite Us. clear - LO'. unfold AFS_STACK in *. lia.
      - exact HMI1.
      - rewrite K4. exact TP.
      - exact AC1.
      - exact THR1. }
    intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & ff & fp & junk1 & junk2
                & E2 & MU2 & WM2 & MI2 & ST2 & RF2 & FRC & SHF & FLG & AC2).
    subst ms2. rewrite K1, ret_pc_even; [| clear; lia | reflexivity].
    lazymatch goal with |- evt _ _ (MS ?RR _ _ _ _ _ _) => remember RR as R2 eqn:ER2 end.
    assert (RF2' : rfull R2) by (rewrite ER2; apply rfull_mkR).
    assert (KP : forall r, In r KEPT -> PropExec.getr R2 r = PropExec.getr R1 r).
    { intros r Hr. rewrite ER2. apply (getr_mkR_keptR R1); [exact (eq_sym K1) | exact Hr]. }
    destruct (new_frame m2 ff fp RF2) as (FRESH & FFDS & FFPC & FPPC & FPDS & HULL & DSM & DSH & THF & THP).
    pose proof FRESH as (FFR & FSB_OK & _).
    pose proof FFR as (K1' & K2' & K3' & (K4' & K5') & K6'). unfold fsz in K3'. change (64 * 2 ^ 4) with 1024 in K3'.
    assert (MUW : munch (W1 ff fp) m0 m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; apply sub_fp_of.
      - apply Forall_cons; [| apply Forall_nil]. exists (spz - 8192, spz). split; [left; reflexivity | cbn; clear; lia].
      - rewrite Us. unfold W1.
        apply Forall_cons;
          [exists (spz - 8192, spz); split; [left; reflexivity | cbn; clear; unfold AFS_STACK in *; lia]|].
        apply Forall_cons; [exists (as_FSB H, as_FSB H + AFS_FLAGS); split; [right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (fp, fp + 1); split; [right; right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons;
          [exists (ff, ff + 1024); split; [right; right; right; left; reflexivity | cbn; unfold fsz; cbn; clear; lia]|].
        apply Forall_cons;
          [exists (sh ff, sh ff + 128); split; [right; right; right; right; left; reflexivity | cbn; unfold fshn; cbn; clear; lia]|].
        apply Forall_nil. }
    assert (WMW : wmono asegs m0 m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
    destruct (W1_keep m2 ff fp MUW WMW FSB_OK FFR FFDS FFPC FPPC FPDS HULL DSM THF THP)
      as (DSA2 & DSW2 & DSV2 & PCA2 & PCC2 & LV2 & ST2' & THA2).
    assert (NE1 : Forall (fun iv : Z * Z => fst iv < snd iv) (W1 ff fp)).
    { unfold W1. repeat (apply Forall_cons; [cbn [fst snd]; clear; unfold AFS_FLAGS; lia|]). apply Forall_nil. }
    destruct (quiet_keep ff fp (W1 ff fp) m2 FRESH THF THP (W1_sub ff fp) NE1 MUW WMW) as (THC1' & THC2' & UM2 & UG1' & UG2' & UG3').
    assert (FRW2 : wr_at asegs m2 ff 1024) by (destruct FRC as [_ W]; exact W).
    assert (FSV2 : shvis m2 ff (ff + 1024)) by exact (ah_frm_shvis H HHb _ m2 (4, ff, fp) RF2 (or_introl eq_refl)).
    assert (FSW2 : wr_at asegs m2 (sh ff) 128) by (destruct SHF as (_ & _ & _ & W); exact W).
    assert (FLW2 : wr_at asegs m2 fp 1) by (destruct FLG as [_ W]; exact W).

    assert (SPOBJk : forall O n, O = po /\ n = LbB_SnK.PO_SIZE \/ O = pcons /\ n = 48 ->
                     O + n <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= O).
    { intros O n [[-> ->] | [-> ->]]; [exact (SPOBJ po 20 ltac:(clear; tauto)) | exact (SPOBJ pcons 48 ltac:(clear; tauto))]. }
    assert (THSk : LbB_SnK.dj2 (this + 288) (bv_unsigned sp - ADS_STACK) (bv_unsigned sp) this)
      by exact (SPOBJ this 288 ltac:(clear; tauto)).
    assert (THFk : LbB_SnK.dj2 (ff + 1024) this (this + 288) ff) by exact THF.
    assert (THPk : LbB_SnK.dj2 (fp + 1) this (this + 288) fp) by exact THP.
    assert (THDk : LbB_SnK.dj2 (this + 272) po (po + LbB_SnK.PO_SIZE) this) by exact po_this.
    assert (TIDk : LbB_SnK.rg 0 tid (2 ^ 32)) by exact TIDR.
    assert (UFOk : forall a, umap_foot 32 (this + 136) bl bc ents a ->
              outside [(bv_unsigned sp - 16384, bv_unsigned sp); (po, po + LbB_SnK.PO_SIZE); (ff, ff + 1024); (sh ff, sh ff + 128); (fp, fp + 1)] a
              /\ outside [(bv_unsigned sp - 16384, bv_unsigned sp); (po, po + LbB_SnK.PO_SIZE); (ff, ff + 1024); (sh ff, sh ff + 128); (fp, fp + 1)] (a / 8 + SHBASE)
              /\ 0 <= a < 2 ^ 47).
    { assert (SUBk : sub_fp [(bv_unsigned sp - 16384, bv_unsigned sp); (po, po + LbB_SnK.PO_SIZE); (ff, ff + 1024); (sh ff, sh ff + 128); (fp, fp + 1)]
                            (UW ff fp)).
      { apply sub_fp_of. unfold UW, LbB_SnK.PO_SIZE.
        apply Forall_cons; [sfp_in (spz - 16384, spz)|]. apply Forall_cons; [sfp_in (po, po + 20)|].
        apply Forall_cons; [sfp_in (ff, ff + 1024)|]. apply Forall_cons; [sfp_in (sh ff, sh ff + 128)|].
        apply Forall_cons; [sfp_in (fp, fp + 1)|]. apply Forall_nil. }
      intros a Ha. destruct (quiet_out ff fp a FRESH THF THP (quiet_foot a Ha)) as (O1 & O2 & Ra).
      split; [exact (SUBk a O1)|]. split; [exact (SUBk _ O2) | exact Ra]. }

    assert (HSF2 : ftbl (WpK ff fp 0 0 0 0) spz m2 LbB_SnAb.SF2).
    { change (WpK ff fp 0 0 0 0)
        with (Wp0 ++ [Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 pcons; Z_to_bv 64 icount; Z_to_bv 64 bl; Z_to_bv 64 bc;
                      Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]).
      apply ftbl_wext; [vm_compute; reflexivity|].
      eapply (ftbl_munch Wp0 spz m1 m2 _ _ (-96) 0);
        [ apply (ftbl_sub _ _ _ _ _ HSF1); vm_compute; reflexivity | exact MU2 | exact WM2 | vm_compute; reflexivity |].
      rewrite Us. cbn [disjoint_from].
      pose proof aceil_facts as ((A1 & A2) & _).
      assert (SHF0 : sh ff + 128 <= spz - 8192).
      { clear - K3' B2 A1 R2' R3'. unfold sh, ASHADOW_BASE, AFS_SIZE, ADS_STACK in *. Z.div_mod_to_equations. lia. }
      clear - K2' K3' K6' B2 SHF0 R2' R3' A1. unfold AFS_STACK, ADS_STACK, AFS_SIZE, AFS_HDR, AFS_FLAGS, fsz, fshn in *.
      cbn in *. lia. }
    assert (HFT2 : ftbl (WpK ff fp 0 0 0 0) ff m2 LbB_SnAb.FT2).
    { apply (ftbl_of_C8 _ ff m2 1016 (EVar 53)).
      apply (proj1 (rw_cells_app asegs m2 ff [CB 24 junk1; C8 (PropExec.getr R1 2); CB (Z.to_nat (fsz 4 - 40)) junk2]
                                 [C8 (Z_to_bv 64 fp)])) in FRC.
      destruct FRC as [_ FRC2]. exact FRC2. }
    assert (HHT2 : ftbl (WpK ff fp 0 0 0 0) (ff / 8) m2 []) by constructor.

    lazymatch type of HKR1 with rtbl _ _ ?Tk =>
      assert (HKW : rtbl (WpK ff fp 0 0 0 0) R2 Tk)
    end.
    { change (WpK ff fp 0 0 0 0)
        with (Wp0 ++ [Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 pcons; Z_to_bv 64 icount; Z_to_bv 64 bl; Z_to_bv 64 bc;
                      Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]).
      apply rtbl_wext; [vm_compute; reflexivity|].
      apply (rtbl_keep Wp0 R1 R2 _ KEPT HKR1); [vm_compute; reflexivity | exact KP]. }
    assert (EAd : forall d, 0 <= spz + d < 2 ^ 64 -> - 2 ^ 63 < d < 0 ->
              edenot (wenv (WpK ff fp 0 0 0 0)) (EAlu ALU_ADD (EVar 33) (ELit d)) = Z_to_bv 64 (spz + d)).
    { intros d Hd1 Hd2. cbn [edenot]. change (ev (wenv (WpK ff fp 0 0 0 0)) 33) with sp.
      rewrite <- (Z_to_bv_bv_unsigned sp) at 1. apply w_addm; clear - Hd1 Hd2 R1'; lia. }
    assert (E10 : PropExec.getr R2 10 = Z_to_bv 64 ff) by (rewrite ER2; reflexivity).
    assert (E2' : PropExec.getr R2 2 = Z_to_bv 64 (spz - 112)) by (rewrite (KP 2%bv ltac:(inkept)); exact K2).
    assert (E9' : PropExec.getr R2 9 = Z_to_bv 64 (spz - 112)).
    { rewrite (KP 9%bv ltac:(inkept)).
      rewrite (rtbl_In Wp0 R1 _ 9%bv (EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-96))) (ELit 5))) HRT1
                ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)).
      rewrite <- (rtbl_In Wp0 R1 _ 2%bv (EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-96))) (ELit 5))) HRT1
                ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)). exact K2. }
    assert (HPW : LbB_SnK.Pw sp m2 po ff fp m2) by (split; [apply munch_refl | apply wmono_refl]).
    assert (HRT2 : rtbl (WpK ff fp 0 0 0 0) R2 LbB_SnAb.RT2).
    { lazymatch type of HKW with rtbl _ _ ?Tk =>
        apply (rtbl_sub _ R2 ([(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-112))); (9%bv, EAlu ALU_ADD (EVar 33) (ELit (-112)));
                                (10%bv, EVar 52)] ++ Tk)); [| vm_compute; reflexivity] end.
      apply rtbl_app; [| exact HKW].
      unfold rtbl. apply Forall_cons.
      { cbn [fst snd]. rewrite E2', EAd by (clear - R1' R2' R3'; unfold ADS_STACK in *; lia). f_equal; clear; lia. }
      apply Forall_cons.
      { cbn [fst snd]. rewrite E9', EAd by (clear - R1' R2' R3'; unfold ADS_STACK in *; lia). f_equal; clear; lia. }
      apply Forall_cons; [cbn [fst snd]; exact E10 | apply Forall_nil]. }
    assert (NDk0 : LbB_SnK.rg 0 0 (2 ^ 64) /\ LbB_SnK.rg 0 0 (2 ^ 32) /\ LbB_SnK.rg 0 0 (2 ^ 32) /\ LbB_SnK.rg 0 0 (2 ^ 32))
      by (unfold LbB_SnK.rg; clear; lia).
    pose proof PCO as PCOk. pose proof DSO as DSOk. pose proof THO as THOk.
    eapply LbB_SnAb.sn_pre with (H := H) (ra := ra) (sp := sp) (gp := gp) (tp := tp) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3)
      (s4 := s4) (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) (s10 := s10) (s11 := s11) (aw := aw)
      (m1 := m2) (this := this) (po := po) (tid := tid) (pcons := pcons) (icount := icount) (lo := lo) (ff := ff) (fp := fp)
      (LF := LF) (bl := bl) (bc := bc) (nd := 0) (nk := 0) (bw := 0) (enc := 0) (LBl := lbl LB) (ents := ents);
      try eassumption.
    -
      intros R' m' p v RF' Hin G10 HRT' HSF' HFT' HHT' HP' HMI' HRF' MU'. destruct v as [[nk bw] enc].
      destruct (u_node UM2 p tid (nk, bw, enc) Hin) as (_ & Np0 & Np1 & _ & _ & _ & _ & NV & _).
      cbn in NV. destruct NV as ((Rnk & _) & (Rbw & _) & (Renc & _)).
      change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rnk, Rbw, Renc.
      assert (WA : LbB_SnW.wagree 58 (WpK ff fp 0 0 0 0) (WpK ff fp p nk bw enc)).
      { exact (LbB_SnW.wagree_prefix
                 (Wp0 ++ [Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 pcons; Z_to_bv 64 icount; Z_to_bv 64 bl; Z_to_bv 64 bc])
                 [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]
                 [Z_to_bv 64 p; Z_to_bv 64 nk; Z_to_bv 64 bw; Z_to_bv 64 enc]). }
      pose proof (LbB_SnW.rtbl_wch 58 _ _ R' LbB_SnTB.RTK4 WA ltac:(vm_compute; reflexivity) HRT') as HRTn.
      pose proof (LbB_SnW.ftbl_wch 58 _ _ spz m' LbB_SnTB.SF4 WA ltac:(vm_compute; reflexivity) HSF') as HSFn.
      pose proof (LbB_SnW.ftbl_wch 58 _ _ ff m' LbB_SnTB.FT4 WA ltac:(vm_compute; reflexivity) HFT') as HFTn.
      pose proof (LbB_SnW.ftbl_wch 58 _ _ (ff / 8) m' LbB_SnTB.HT4 WA ltac:(vm_compute; reflexivity) HHT') as HHTn.
      assert (HRT5 : rtbl (WpK ff fp p nk bw enc) R' ((10%bv, EVar 58) :: LbB_SnTB.RTK4)).
      { apply Forall_cons; [cbn [fst snd]; exact G10 | exact HRTn]. }
      clear HRT' HSF' HFT' HHT' HRTn.
      destruct (Z.eq_dec nk 0) as [E0|NZ].
      + assert (NDk : LbB_SnK.rg 0 p (2 ^ 64) /\ LbB_SnK.rg 0 nk (2 ^ 32) /\ LbB_SnK.rg 0 bw (2 ^ 32) /\ LbB_SnK.rg 0 enc (2 ^ 32))
          by (unfold LbB_SnK.rg; clear - Np0 Np1 Rnk Rbw Renc; lia).
        clear NDk0.
        eapply LbB_SnFb.sn_found0 with (H := H) (ra := ra) (sp := sp) (gp := gp) (tp := tp) (s0 := s0) (s1 := s1) (s2 := s2)
            (s3 := s3) (s4 := s4) (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) (s10 := s10) (s11 := s11) (aw := aw)
            (m1 := m2) (this := this) (po := po) (tid := tid) (pcons := pcons) (icount := icount) (lo := lo) (ff := ff) (fp := fp)
            (LF := LF) (bl := bl) (bc := bc) (nd := p) (nk := nk) (bw := bw) (enc := enc) (LBl := lbl LB) (ents := ents);
            try eassumption.
        intros R'' m'' RF'' HRT'' HSF'' HFT'' HHT'' HP'' HMI'' HRF'' MU''.
        pose proof (LbB_SnW.wagree_sym _ _ _ WA) as WA'.
        pose proof (LbB_SnW.rtbl_wch 58 _ _ R'' LbB_SnTB.RTK4 WA' ltac:(vm_compute; reflexivity) HRT'') as HRTd.
        pose proof (LbB_SnW.ftbl_wch 58 _ _ spz m'' LbB_SnTB.SF4 WA' ltac:(vm_compute; reflexivity) HSF'') as HSFd.
        pose proof (LbB_SnW.ftbl_wch 58 _ _ ff m'' LbB_SnTB.FT4 WA' ltac:(vm_compute; reflexivity) HFT'') as HFTd.
        pose proof (LbB_SnW.ftbl_wch 58 _ _ (ff / 8) m'' LbB_SnTB.HT4 WA' ltac:(vm_compute; reflexivity) HHT'') as HHTd.
        apply evt_done. apply sn_mid_d2B. exists ff, fp, m2, R'', m''.
        split; [exact FRESH|]. split; [exact MUW|]. split; [exact WMW|].
        split; [exact (munch_trans _ _ _ _ MU' MU'')|]. split; [exact (proj2 HP'')|].
        split; [reflexivity|]. split; [exact RF''|]. split; [exact HRTd|]. split; [exact HSFd|]. split; [exact HFTd|].
        split; [exact HHTd|].
        split; [eapply wr_at_transport; [exact FRW2 | exact (proj2 HP'')]|].
        split; [eapply wr_at_transport; [exact FLW2 | exact (proj2 HP'')]|].
        split; [exact HMI'' | exact HRF''].
      + assert (NDk : LbB_SnK.rg 0 p (2 ^ 64) /\ LbB_SnK.rg 0 nk (2 ^ 32) /\ LbB_SnK.rg 0 bw (2 ^ 32) /\ LbB_SnK.rg 0 enc (2 ^ 32))
          by (unfold LbB_SnK.rg; clear - Np0 Np1 Rnk Rbw Renc; lia).
        clear NDk0.
        pose proof (proj1 (Forall_forall _ _) KOK _ Hin) as KH. cbn [fst snd t3a t3c] in KH.
        assert (NK4 : nk < 4) by (clear - KH; lia). assert (EN16 : enc < 16) by (clear - KH; lia).
        eapply evt_mono.
        { eapply LbB_SnFb.sn_found with (H := H) (ra := ra) (sp := sp) (gp := gp) (tp := tp) (s0 := s0) (s1 := s1) (s2 := s2)
            (s3 := s3) (s4 := s4) (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) (s10 := s10) (s11 := s11) (aw := aw)
            (m1 := m2) (this := this) (po := po) (tid := tid) (pcons := pcons) (icount := icount) (lo := lo) (ff := ff) (fp := fp)
            (LF := LF) (bl := bl) (bc := bc) (nd := p) (nk := nk) (bw := bw) (enc := enc) (LBl := lbl LB) (ents := ents);
            try eassumption. }
        intros ms HPok. apply sn_mid_okB. exists ff, fp, m2, p, nk, bw, enc.
        split; [exact FRESH|]. split; [exact MUW|]. split; [exact WMW|]. split; [exact Hin|]. split; [exact NZ|].
        split; [exact Rnk|]. split; [exact Rbw|]. split; [exact Renc | exact HPok].
    -
      intros R' m' RF' HRT' HSF' HFT' HHT' HP' HMI' HRF' MU'. apply evt_done. apply sn_mid_d1B. exists ff, fp, m2, R', m'.
      split; [exact FRESH|]. split; [exact MUW|]. split; [exact WMW|]. split; [exact MU'|]. split; [exact (proj2 HP')|].
      split; [reflexivity|]. split; [exact RF'|].
      split; [exact HRT'|]. split; [exact HSF'|]. split; [exact HFT'|]. split; [exact HHT'|].
      split; [eapply wr_at_transport; [exact FRW2 | exact (proj2 HP')]|].
      split; [eapply wr_at_transport; [exact FLW2 | exact (proj2 HP')]|].
      split; [exact HMI' | exact HRF'].
  Qed.

  Notation SNPOST s mo B shi :=
    (sn_post H LINV_P5 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF (sn_XT po) lo B shi m0 mo
             (sn_res LB po tid ents)) (only parsing).

  Lemma sn_ok_post : forall s msF' mo mo' B shi errv,
    sn_okF (as_VIS H s msF') ->
    FPSteps.frm_zero fc -> as_RHEAP H s LB m0 -> as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> as_rauxv_ok H m0 B ->
    rw_cells asegs m0 (errno_addr tp) [C4 errv] -> stack0 m0 lo shi ->
    SNPOST s mo B shi (mkCfg msF' mo').
  Proof using All.
    intros s msF' mo mo' B shi errv HOK FZ RH KR' MP' RAUX ERRN S0.
    destruct HOK as (ff & fp & m2 & nd & nk & bw & enc & FRESH & MUW & WMW & Hin & NZ & Rnk & Rbw & Renc & HPP).
    destruct HPP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E' & MI' & PW'
                     & RFS' & C1 & C2 & C3 & C4).
    destruct PW' as (MUP & WMP).
    pose proof (tw_munch ff fp m2 m' MUW MUP) as MUT.
    assert (WMT : wmono asegs m0 m') by (eapply wmono_trans; [exact WMW | exact WMP]).
    destruct (tw_laws LB ff fp FRESH) as (W1' & W2' & W3').
    destruct (tw_keep ff fp m' FRESH MUT WMT) as (ST' & LV' & AC' & DW').
    destruct (tw_place ff fp FRESH) as (K2 & K3 & K4 & K6 & B1 & B2 & B3 & B4 & AP & S1 & S2 & S3 & S4).
    pose proof p1_ranges as (R1 & R2 & R3). pose proof DSO as (O1 & _).
    unfold sn_post. cbn [cfg_ms cfg_model].
    exists t0', t1', t2', (Z_to_bv 64 0), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv, s, LB,
           [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 4); (sh ff, sh ff + fshn 4)], F, fc, 0.
    split; [exact E'|]. split; [exact FZ|]. split; [reflexivity|].
    split; [exact KR'|]. split; [exact MP'|]. split; [exact MI'|]. split; [exact ST'|].
    split.
    { eapply rw_cells_transport; [exact ERRN | exact MUT | exact WMT |].
      unfold TW. cbn [disjoint_from cells_size csize]. rewrite TP, unsigned_lit by (clear; unfold ATP; lia).
      clear - R1 R2 R3 B1 K2 K6 S3 O1. unfold ATP, AIMG_TOP, AFS_HDR, AFS_FLAGS, ADS_STACK in *. cbn. lia. }
    split; [eapply (ah_rauxv_frame H HHb); [exact RAUX | exact MUT | exact WMT | exact W1']|].
    split; [eapply (ah_RHEAP_frame H HHb); [exact RH | exact MUT | exact WMT | exact W1']|].
    split.
    { unfold sn_res. split; [apply Permutation_refl|]. split; [exact DW'|]. right.
      split; [reflexivity|]. split; [reflexivity|]. exists nd, nk, bw, enc.
      split; [exact Hin|]. split; [exact NZ|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
      split; [exact Rnk|]. split; [exact Rbw | exact Renc]. }
    split; [exact (fs_scratch_of_fresh H LF 4 ff fp FRESH)|].
    split; [exact (tw_xpres s LB m' ff fp RH MUT WMT)|].
    split; [exact RFS'|]. split; [exact AC'|].
    split; [eapply stack0_transport; [exact S0 | exact MUT | exact WMT | exact W2']|].
    split; [exact LV'|]. cbn. clear; lia.
  Qed.

  Lemma sn_srA : bv_unsigned sp mod 32 = 0 -> forall s msF mo B shi errv,
    (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> sn_d1A (as_VIS H s msF') ->
       as_SR H (SNPOST s mo B shi) (mkCfg msF' mo')) ->
    (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> sn_d2A (as_VIS H s msF') ->
       as_SR H (SNPOST s mo B shi) (mkCfg msF' mo')) ->
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 aw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 ASN_ENTRY) fc None m0 (seg_rom asegs) ->
    FPSteps.frm_zero fc -> as_RHEAP H s LB m0 -> as_AKREL H s (mkCfg msF mo) -> as_rauxv_ok H m0 B ->
    rw_cells asegs m0 (errno_addr tp) [C4 errv] -> stack0 m0 lo shi ->
    as_SR H (SNPOST s mo B shi) (mkCfg msF mo).
  Proof using All.
    intros C32 s msF mo B shi errv HD1 HD2 VIS FZ RH KR RAUX ERRN S0.
    eapply (ahh_evt_then H HHb sn_midA _ s msF _ mo KR VIS (sn_fullA C32)).
    intros msF' mo' KR' MP' [HOK | [HX | HX]].
    - apply (ah_done H HHb). exact (sn_ok_post s msF' mo mo' B shi errv HOK FZ RH KR' MP' RAUX ERRN S0).
    - exact (HD1 msF' mo' KR' MP' HX).
    - exact (HD2 msF' mo' KR' MP' HX).
  Qed.

  Lemma sn_srB : bv_unsigned sp mod 32 = 16 -> forall s msF mo B shi errv,
    (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> sn_d1B (as_VIS H s msF') ->
       as_SR H (SNPOST s mo B shi) (mkCfg msF' mo')) ->
    (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> sn_d2B (as_VIS H s msF') ->
       as_SR H (SNPOST s mo B shi) (mkCfg msF' mo')) ->
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 aw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 ASN_ENTRY) fc None m0 (seg_rom asegs) ->
    FPSteps.frm_zero fc -> as_RHEAP H s LB m0 -> as_AKREL H s (mkCfg msF mo) -> as_rauxv_ok H m0 B ->
    rw_cells asegs m0 (errno_addr tp) [C4 errv] -> stack0 m0 lo shi ->
    as_SR H (SNPOST s mo B shi) (mkCfg msF mo).
  Proof using All.
    intros C32 s msF mo B shi errv HD1 HD2 VIS FZ RH KR RAUX ERRN S0.
    eapply (ahh_evt_then H HHb sn_midB _ s msF _ mo KR VIS (sn_fullB C32)).
    intros msF' mo' KR' MP' [HOK | [HX | HX]].
    - apply (ah_done H HHb). exact (sn_ok_post s msF' mo mo' B shi errv HOK FZ RH KR' MP' RAUX ERRN S0).
    - exact (HD1 msF' mo' KR' MP' HX).
    - exact (HD2 msF' mo' KR' MP' HX).
  Qed.

End Sn.
