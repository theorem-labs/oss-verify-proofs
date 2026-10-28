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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td LbB_TdKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtorR1 LbB_DPdK LbB_PmXp LbB_PmSL.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_TablStmt LbB_SnStmt LbB_WoGen LbB_SnXD LbB_SnXK LbB_SnXT LbB_SnXO2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnXC2 LbB_SnXS2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_SnXI LbB_SnXQ2 LbB_SnXZ.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmGlue LbB_PcOvf.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SnXE.
  Local Notation PD_SHB := LbB_DPdK.PD_SHB (only parsing).

  Local Notation kst_ex := LbB_SnXT.kst_ex (only parsing).
  Local Notation shT := LbB_SnXT.shT (only parsing).
  Local Notation kT := LbB_SnXT.kT (only parsing).
  Local Notation wok := LbB_SnXT.wok (only parsing).
  Local Notation wok_facts := LbB_SnXT.wok_facts (only parsing).
  Local Notation wk_win := LbB_SnXT.wk_win (only parsing).
  Local Notation fin_wider := LbB_SnXT.fin_wider (only parsing).
  Local Notation rtbl_sw := LbB_SnXT.rtbl_sw (only parsing).
  Local Notation ftbl_sw := LbB_SnXT.ftbl_sw (only parsing).
  Local Notation ds_cost_le := LbB_SnXS2.ds_cost_le (only parsing).
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable e : xent H.
  Variables (ff fp : Z).

  Variables (p1 n1 p2 n2 : Z).
  Hypothesis HP : xpre H e.
  Hypothesis FF : fresh_frame H (x_LF e) 4 ff fp.

  Hypothesis THI : obj_inframe (x_LF e) (x_this e) 288.
  Hypothesis PCI : obj_inframe (x_LF e) (x_pcons e) 48.

  Local Notation ftbl_xpres := (@LbB_SnXT.ftbl_xpres HCEIL H) (only parsing).
  Local Notation Wx := (@LbB_SnXT.Wx H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation Px := (@LbB_SnXT.Px HCEIL H e ff fp) (only parsing).
  Local Notation ex_ranges := (@LbB_SnXT.ex_ranges HCEIL H e ff fp HP FF) (only parsing).
  Local Notation ex_vals := (@LbB_SnXT.ex_vals HCEIL H e ff fp HP FF) (only parsing).
  Local Notation ex_wins := (@LbB_SnXT.ex_wins HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xobj_range := (@LbB_SnXT.xobj_range HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation ex_keepT := (@LbB_SnXT.ex_keepT HCEIL H HHbp e ff fp HP FF THI PCI) (only parsing).
  Local Notation ex_keep := (@LbB_SnXT.ex_keep HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation evWx := (@LbB_SnXT.evWx H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation kst_ex_ok := (@LbB_SnXT.kst_ex_ok HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation evT := (@LbB_SnXT.evT HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation shT_start := (@LbB_SnXT.shT_start HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation shT_apart := (@LbB_SnXT.shT_apart HCEIL H HHbp e ff fp HP FF THI) (only parsing).
  Local Notation shb_eq0 := (@LbB_SnXT.shb_eq0 ff) (only parsing).
  Local Notation this_apart := (@LbB_SnXT.this_apart HCEIL H HHbp e ff fp HP FF THI) (only parsing).
  Local Notation kT_ok := (@LbB_SnXT.kT_ok HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF THI PCI) (only parsing).
  Local Notation scT_flat := (@LbB_SnXT.scT_flat HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation scP_flat := (@LbB_SnXT.scP_flat HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tS := (@LbB_SnXT.tS H e) (only parsing).
  Local Notation tFw := (@LbB_SnXT.tFw ff) (only parsing).
  Local Notation tHw := (@LbB_SnXT.tHw ff) (only parsing).
  Local Notation tF := (@LbB_SnXT.tF ff) (only parsing).
  Local Notation tH := (@LbB_SnXT.tH ff) (only parsing).
  Local Notation tab_vals := (@LbB_SnXT.tab_vals HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_wf3w := (@LbB_SnXT.tabs_wf3w HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_wf3 := (@LbB_SnXT.tabs_wf3 HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation wk_stk := (@LbB_SnXT.wk_stk HCEIL H e ff fp HP FF) (only parsing).
  Local Notation shb_eq := (@LbB_SnXT.shb_eq ff) (only parsing).
  Local Notation tabs_ok3w := (@LbB_SnXT.tabs_ok3w HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_ok3 := (@LbB_SnXT.tabs_ok3 HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation Px_step3w := (@LbB_SnXT.Px_step3w HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation Px_step3 := (@LbB_SnXT.Px_step3 HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation Wx_sw1 := (@LbB_SnXT.Wx_sw1 HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation Wx_sw := (@LbB_SnXT.Wx_sw HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation ex_shvis := (@LbB_SnXC2.ex_shvis HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation fr_app := (@LbB_SnXC2.fr_app HCEIL H e ff fp HP FF) (only parsing).
  Local Notation fr_addr := (@LbB_SnXC2.fr_addr HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation xwin_stk := (@LbB_SnXC2.xwin_stk HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xwin_fr := (@LbB_SnXC2.xwin_fr H e ff) (only parsing).
  Local Notation Px_win := (@LbB_SnXC2.Px_win HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation obj_apart := (@LbB_SnXC2.obj_apart HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation blk_apart := (@LbB_SnXC2.blk_apart HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xds_run := (@LbB_SnXC2.xds_run HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xcut := (@LbB_SnXC2.xcut HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation xchain_call := (@LbB_SnXS2.xchain_call HCEIL H HHbp e ff fp HP) (only parsing).
  Local Notation xsess := (@LbB_SnXS2.xsess H e ff) (only parsing).
  Local Notation xsess_facts := (@LbB_SnXS2.xsess_facts HCEIL H e ff HP) (only parsing).
  Local Notation x_ds_pre := (@LbB_SnXS2.x_ds_pre HCEIL H HHbp e ff fp HP) (only parsing).
  Local Notation sf_xpres := (@LbB_SnXS2.sf_xpres HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation x_ds_back := (@LbB_SnXS2.x_ds_back HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation xsr := (@LbB_SnXS2.xsr HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation rcall := (@LbB_SnXS2.rcall H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation x_ds_obj := (@LbB_SnXS2.x_ds_obj HCEIL H e ff fp HP FF) (only parsing).
  Local Notation x_cseq := (@LbB_SnXS2.x_cseq HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation rcall1 := (@LbB_SnXS2.rcall1 H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation rcall0 := (@LbB_SnXS2.rcall0 H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation x_u64 := (@LbB_SnXS2.x_u64 HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation x_u32 := (@LbB_SnXS2.x_u32 HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation xsr3 := (@LbB_SnXS2.xsr3 HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation x_dtor := (@LbB_SnXS2.x_dtor HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation x_run := (@LbB_SnXS2.x_run HCEIL H HHbp e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation xsess_win := (@LbB_SnXS2.xsess_win HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation x_stk_back := (@LbB_SnXS2.x_stk_back HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation x_strlen := (@LbB_SnXS2.x_strlen HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation xsess_run := (@LbB_SnXS2.xsess_run HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation xsr_mono := (@LbB_SnXS2.xsr_mono HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Notation SP := (xSP e) (only parsing).
  Notation this := (x_this e) (only parsing).
  Notation pcons := (x_pcons e) (only parsing).

  Ltac evwx := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wx;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

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

  Ltac exrun3 HRT HSF HFT HHT HPX HMI fuel stops kx := exrun3w 1016 128 HRT HSF HFT HHT HPX HMI fuel stops kx.

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

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Local Notation ds := (ff + SX_DS_OFF) (only parsing).

  Ltac scT := unfold scs_denot; repeat (apply Forall_cons; [cbn [sc_denot]; unfold elenZ; cbn [edenot]; rewrite ?unsigned_lit by (clear; lia);
                                           first [apply scT_flat; clear; lia | apply scP_flat; clear; lia] |]); apply Forall_nil.

  Definition sx_post (ents : list (Z * (Z * (Z * Z * Z)))) : config -> Prop :=
    sn_post H LINV_P5 (x_ra e) (x_sp e) (x_gp e) (x_tp e) (x_s0 e) (x_s1 e) (x_s2 e) (x_s3 e) (x_s4 e) (x_s5 e) (x_s6 e)
      (x_s7 e) (x_s8 e) (x_s9 e) (x_s10 e) (x_s11 e) (x_F e) (x_fc e) (x_s e) (x_LB e) (x_LF e) (sn_XT (x_po e))
      (x_lo e) (x_B e) (x_shi e) (x_m e) (x_mo e) (sn_res (x_LB e) (x_po e) (x_tid e) ents).

  Lemma x_po_wr : forall XSc sk LBk m, Px XSc sk LBk m -> wr_at asegs m (x_po e) 20.
Proof using HHbp HP FF.
    intros XSc sk LBk m HI.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & _ & _ & _ & _ & _ & _ & _ & (_ & P8 & _) & POI & POW).
    destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XP & FS & _).
    pose proof (xobj_range XSc (x_po e) 20 POI ltac:(lia) P8 FS) as (XR & _).
    eapply xpres_wr_at; [exact XP | exact POW | exact XR].
  Qed.

  Lemma sx_end : forall ents c, xsr3 SN_DTOR_RA2 SX_RT9 SX_SF7 98304 c -> as_SR H (sx_post ents) c.
Proof using HHbp HP FF.
    intros ents [msF mo] (s & F & fc & XSc & LBc & KR & MP & FZ & CUT & AL).
    cbn [cfg_ms cfg_model] in *.
    destruct CUT as (R & m & VIS & RF & HRT & HSF & HI & MI & (PL & _)).
    pose proof (rt_bp_base H HHbp) as HB.
    pose proof ex_ranges as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
    pose proof (xS1_facts H e HP) as (S0' & (S1 & S2) & S3 & S4 & S5 & S6).
    pose proof (xpre_geo H e HP) as (CE & LO & SH1 & SH2 & SP16 & TP).
    pose proof FF as (_ & (_ & _ & _ & FAPP) & _).
    assert (FFB : 0 <= ff /\ ff + 1024 <= 2 ^ 47) by (unfold AIMG_TOP, AFS_HDR, AAPP_HI in *; lia).
    assert (FPB : 0 <= fp /\ fp + 1 <= 2 ^ 47) by (unfold AIMG_TOP, AFS_FLAGS, AFS_HDR, AFS_SIZE, AAPP_HI in *; lia).
    assert (SPB : 2 ^ 45 <= xSP e - 96 /\ xSP e <= 2 ^ 47) by lia.
    assert (FPS : fp + 1 <= xSP e - 80 \/ xSP e <= fp) by (left; unfold AFS_HDR, AFS_SIZE in *; lia).
    eapply (ahh_evt_then H HB (fun ms => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m3 m4,
              ms = MS (mkR (x_ra e) (x_sp e) (x_gp e) (x_tp e) t0 t1 t2 (x_s0 e) (x_s1 e) (Z_to_bv 64 SN_ERR) a1 a2 a3 a4 a5 a6 a7
                           (x_s2 e) (x_s3 e) (x_s4 e) (x_s5 e) (x_s6 e) (x_s7 e) (x_s8 e) (x_s9 e) (x_s10 e) (x_s11 e) t3 t4 t5 t6)
                      F (ret_pc (x_ra e)) fc None m4 (seg_rom asegs)
              /\ Px XSc s LBc m3 /\ munch [(fp, fp + 1)] m3 m4 /\ wmono asegs m3 m4 /\ mem_inv asegs m4
              /\ stk asegs m4 (x_lo e) (xSP e) /\ mrd asegs m4 (wa fp) = Some (b8 0))
              (sx_post ents) s msF _ mo KR VIS).
    - assert (HFT : ftbl Wx ff m []) by apply ftbl_nil.
      assert (HHT : ftbl Wx (ff / 8) m []) by apply ftbl_nil.
      exrun3 HRT HSF HFT HHT HI MI 400%nat [ASET_SHADOW_F5] (@nil kentry).
      + apply Forall_nil.
      + apply Forall_nil.
      + scT.
      + intros R2 m2 RF2 HRT2 HTS2 HPm2 HMI2 MU2 WM2.
        tsplit HTS2 HSF2 HFT2 HHT2. cbn [s_pc].
        destruct (ex_keep XSc s LBc m2 HPm2) as (AC2 & _ & _ & ST2 & _ & SW2 & _).
        rgetx HRT2 (1%bv : reg) A1. rgetx HRT2 (3%bv : reg) A3. rgetx HRT2 (4%bv : reg) A4. rgetx HRT2 (8%bv : reg) A8.
        rgetx HRT2 (10%bv : reg) A10r. rgetx HRT2 (11%bv : reg) A11. rgetx HRT2 (18%bv : reg) A18. rgetx HRT2 (20%bv : reg) A20.
        rgetx HRT2 (25%bv : reg) A25. rgetx HRT2 (26%bv : reg) A26. rgetx HRT2 (27%bv : reg) A27.
        assert (SHW : alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 ff) (Z_to_bv 64 3)) (Z_to_bv 64 SHBASE) = Z_to_bv 64 (sh ff)).
        { assert (E1 : bv_unsigned (alu64 ALU_SRL (Z_to_bv 64 ff) (Z_to_bv 64 3)) = ff / 8).
          { cbn [alu64 alu]. rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite (Z.mod_small ff) by lia.
            replace (bv_unsigned (bv_and (Z_to_bv 64 3) (Z_to_bv 64 63))) with 3 by (vm_compute; reflexivity).
            rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
          rewrite <- (Z_to_bv_bv_unsigned (alu64 ALU_SRL (Z_to_bv 64 ff) (Z_to_bv 64 3))), E1.
          assert (D8 : 0 <= ff / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
          rewrite w_add by (unfold SHBASE; lia). unfold sh, SHBASE, ASHADOW_BASE. f_equal. lia. }
        assert (A10 : PropExec.getr R2 10 = Z_to_bv 64 (sh ff)) by (rewrite A10r; exact SHW).
        assert (A1' : PropExec.getr R2 1 = Z_to_bv 64 LbB_SnXZ.SX_SF_RA) by exact A1.
        assert (A8' : PropExec.getr R2 8 = Z_to_bv 64 (xSP e)) by (rewrite A8; symmetry; apply Z_to_bv_bv_unsigned).
        assert (A20' : PropExec.getr R2 20 = Z_to_bv 64 SN_ERR) by (rewrite A20; reflexivity).
        rewrite (MS_full_eq R2 F _ fc m2 _ RF2).
        destruct (rw_cells_of_wr_hi m2 (sh ff) 128 SW2
                    ltac:(clear - FFB; unfold sh, AIMG_TOP, ASHADOW_BASE; Z.div_mod_to_equations; lia) ltac:(clear; lia))
          as (junk & CSH).
        eapply evt_cut.
        { eapply (ah_setf5 H HB) with (sa := sh ff) (n := 128); [exact A10 | exact A11 | clear; lia | exact CSH | exact HMI2 | exact AC2]. }
        intros ms3 (v0 & v1 & v2 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m3 & EQ3 & MU3 & WM3 & MI3 & SH3).
        subst ms3.
        rewrite A1', (ret_pc_even LbB_SnXZ.SX_SF_RA ltac:(unfold LbB_SnXZ.SX_SF_RA; lia) eq_refl), A8', A18, A20'.
        assert (HI3 : Px XSc s LBc m3).
        { eapply (xinv_munch H HB e ff fp XSc s LBc m2 m3 [(sh ff, sh ff + 128)] HP HPm2 MU3 WM3 MI3).
          - eapply stk_wmono; [exact ST2 | exact WM3 | lia].
          - apply Forall_cons; [right; right; cbn [fst snd]; lia | apply Forall_nil]. }
        pose proof HI3 as (RF3 & _ & _ & _ & _ & _ & _ & _ & ST3 & SV3 & SF3 & _ & WP3 & _).
        unfold xsaved, SX_SAVED in SV3. unfold SX_FLAGP in SF3.
        destruct (LbB_SnXZ.sn_xe2 (Z_to_bv 64 LbB_SnXZ.SX_SF_RA) (PropExec.getr R2 2) v0 v1 v2 (PropExec.getr R2 9)
                    v10 v11 v12 v13 v14 v15 v16 v17 (PropExec.getr R2 19) (PropExec.getr R2 21) (PropExec.getr R2 22)
                    (PropExec.getr R2 23) (PropExec.getr R2 24) (PropExec.getr R2 25) (PropExec.getr R2 26) (PropExec.getr R2 27)
                    v28 v29 v30 v31 (PropExec.getr R2 3) (PropExec.getr R2 4) (x_ra e) (x_s0 e) (x_s1 e) (x_s2 e) (x_s3 e)
                    (x_s4 e) (x_s5 e) (x_s6 e) (x_s7 e) (x_s8 e) F fc m3 (seg_rom asegs) ff fp (xSP e) SN_ERR
                    (proj1 FFB) (proj2 FFB) (proj1 FPB) (proj2 FPB) (proj1 SPB) (proj2 SPB) FPS SV3 SF3 WP3 MI3)
          as (R4 & m4 & RUN4 & HR4 & MU4 & WM4 & MI4 & ST4 & FL4).
        eapply evt_of_msteps; [exact RUN4|]. subst R4.
        rewrite A3, A4, A25, A26, A27.
        assert (ESP : Z_to_bv 64 (xSP e) = x_sp e) by (apply Z_to_bv_bv_unsigned). rewrite ESP.
        unfold LbB_SnXZ.SX_RET. step. apply evt_done.
        exists v0, v1, v2, v11, v12, v13, v14, v15, v16, v17, v28, v29, v30, v31, m3, m4.
        split; [reflexivity|]. split; [exact HI3|]. split; [exact MU4|]. split; [exact WM4|]. split; [exact MI4|].
        split; [exact (ST4 _ _ ST3) | exact FL4].
    - intros msF' mo' KR' MP' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m3 & m4 & VIS' & HI3 & MU & WM
                               & MI4 & ST4 & FL4).
      apply (ah_done H HB). unfold sx_post, sn_post.
      pose proof HI3 as (RF3 & _ & RH3 & AC3 & _ & S03 & RA3 & (errv & ER3) & _ & _ & _ & _ & _ & XP3 & FS3 & LV3).
      assert (K1 : forall LB0, Forall (aclient_write_ok H LB0) [(fp, fp + 1)]).
      { intros LB0. apply Forall_cons; [| apply Forall_nil]. right; right; right; right; left. cbn [fst snd].
        unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. lia. }
      assert (K2 : Forall aconst_ok [(fp, fp + 1)]).
      { apply Forall_cons; [| apply Forall_nil].
        eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact FAPP | unfold AFS_FLAGS in *; lia | unfold AFS_HDR, AFS_SIZE in *; lia]. }
      assert (K3 : Forall stack0_ok [(fp, fp + 1)]).
      { apply Forall_cons; [| apply Forall_nil].
        eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact FAPP | unfold AFS_FLAGS in *; lia | unfold AFS_HDR, AFS_SIZE in *; lia]. }
      assert (K4 : Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) [(fp, fp + 1)]).
      { apply Forall_cons; [| apply Forall_nil]. cbn [fst]. unfold AFS_FLAGS in *. lia. }
      exists t0, t1, t2, (Z_to_bv 64 SN_ERR), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m4, errv, s, LBc, (XE H ff fp ++ XSc), F, fc,
        SN_ERR.
      cbn [cfg_ms cfg_model].
      split; [exact VIS'|]. split; [exact FZ|]. split; [reflexivity|]. split; [exact KR'|].
      split; [exact (ah_mpres_trans H HB _ _ _ MP MP')|].
      split; [exact MI4|]. split; [exact ST4|].
      split; [eapply rw_cells_transport; [exact ER3 | exact MU | exact WM |]; rewrite (xerrno_ATP H e TP); cbn;
              unfold ATP, AIMG_TOP, AFS_FLAGS in *; lia|].
      split; [eapply (ah_rauxv_frame H HB); [exact RA3 | exact MU | exact WM | exact (K1 LBc)]|].
      split; [eapply (ah_RHEAP_frame H HB); [exact RH3 | exact MU | exact WM | exact (K1 LBc)]|].
      split; [split; [exact PL | split; [exact (wr_at_wmono _ _ _ _ (x_po_wr XSc s LBc m3 HI3) WM) | left; reflexivity]]|].
      split; [apply Forall_app; split; [exact (fs_scratch_of_fresh H (x_LF e) 4 ff fp FF) | exact FS3]|].
      split.
      { eapply xpres_weaken; [eapply xpres_trans; [exact XP3|] | unfold xSP; lia | intros b Hb; exact Hb |].
        - eapply (xpres_of_munch H (x_s e) (x_LB e) (xSP e) _ [(fp, fp + 1)] (x_m e));
            [exact HB | exact (xpre_RH0 H e HP) | exact MU | exact WM |].
          apply Forall_cons; [| apply Forall_nil]. right. intros a Ha. cbn [fst snd] in Ha. cbn [rin_ivs]. right.
          apply rin_ivs_app. left. cbn. right. left. lia.
        - intros a Ha. apply rin_ivs_app. cbn [rin_ivs fst snd] in Ha. destruct Ha as [Ha|Ha]; [left | right; exact Ha].
          unfold sn_XT, sn_X. cbn. right. right. left. lia. }
      split.
      { pose proof (ah_release H HB ((4, ff, fp) :: x_LF e) m3 m4 [(fp, fp + 1)] 4 ff fp RF3 (or_introl eq_refl) MU WM) as K.
        rewrite lf_remove_head in K. apply K; [| exact FL4]. apply Forall_cons; [right; split; reflexivity | apply Forall_nil]. }
      split; [exact (ACONST_frame _ _ _ AC3 MU WM K2)|].
      split; [exact (stack0_transport _ _ _ _ _ S03 MU WM K3)|].
      split; [exact (LbB_TdKit.LINV_P5_munch_hi _ _ _ LV3 MU K4)|].
      replace (SN_ERR =? 0) with false by reflexivity. unfold SN_COST. lia.
  Qed.
End SnXE.
