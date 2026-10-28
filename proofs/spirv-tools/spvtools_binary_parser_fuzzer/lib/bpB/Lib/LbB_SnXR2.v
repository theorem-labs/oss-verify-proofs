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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_SnXI LbB_SnXQ2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SnXR.
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
  Local Notation xsr0 := (@LbB_SnXS2.xsr0 HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation x_pdiag := (@LbB_SnXS2.x_pdiag HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF THI PCI) (only parsing).
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

  Hypothesis HPDIAG : pdiag0_stmtA H LINV_P5 ds_repA0.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV_P5 ds_repA0.
  Hypothesis HU32 : put_u32_stmtA H LINV_P5 ds_repA0.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV_P5 ds_repA0.

  Ltac lit_acc p gsz grz :=
    let M' := fresh "M'" in let ACM' := fresh "ACM'" in
    intros M' ACM'; eapply (addressable_accessible M' p gsz); [| lia | lia | unfold AAPP_HI; lia];
    eapply (ACONST_global_addressable M' p gsz grz ACM'); [| lia]; unfold aglobals; repeat (first [left; reflexivity | right]).
  Ltac lit_bytes p n :=
    let r := eval vm_compute in (PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 p) n) in
    lazymatch r with Some ?bs => exists bs; split; [reflexivity |
      let M' := fresh "M'" in let MIM' := fresh "MIM'" in let B' := fresh "B'" in
      intros M' MIM'; edestruct (LbB_PmGlue.img_lit M' p n bs MIM') as [B' _]; [lia | cbn; lia | vm_compute; reflexivity | exact B']] end.

  Ltac rc3 := let R := fresh "R" in let HRT := fresh "HRT" in intros R HRT;
    let G1 := fresh in let G2 := fresh in let G8 := fresh in let G4 := fresh in let G10 := fresh in let G11 := fresh in let G12 := fresh in
    rgetx HRT (1%bv : reg) G1; rgetx HRT (2%bv : reg) G2; rgetx HRT (8%bv : reg) G8; rgetx HRT (4%bv : reg) G4;
    rgetx HRT (10%bv : reg) G10; rgetx HRT (11%bv : reg) G11; rgetx HRT (12%bv : reg) G12;
    exact (conj G1 (conj G2 (conj (eq_trans G8 (eq_sym (Z_to_bv_bv_unsigned (x_sp e)))) (conj G4 (conj G10 (conj G11 G12)))))).
  Ltac rc0 := let R := fresh "R" in let HRT := fresh "HRT" in intros R HRT;
    let G1 := fresh in let G2 := fresh in let G8 := fresh in let G4 := fresh in let G10 := fresh in
    rgetx HRT (1%bv : reg) G1; rgetx HRT (2%bv : reg) G2; rgetx HRT (8%bv : reg) G8; rgetx HRT (4%bv : reg) G4;
    rgetx HRT (10%bv : reg) G10;
    exact (conj G1 (conj G2 (conj (eq_trans G8 (eq_sym (Z_to_bv_bv_unsigned (x_sp e)))) (conj G4 G10)))).

  Ltac xn X :=
    lazymatch type of X with
    | (xsr ?pc ?rt ?sf ?l ?sp ?c) =>
        let rt' := eval vm_compute in rt in
        tryif constr_eq rt rt' then idtac else
          (let E := fresh "E" in assert (E : rt = rt') by (vm_cast_no_check (@eq_refl _ rt')); rewrite E in X; clear E)
    end.

  Ltac xseg0 dirs stops kx :=
    let R := fresh "R" in let F := fresh "F" in let fc := fresh "fc" in let m := fresh "m" in let XSc := fresh "XSc" in
    let s := fresh "s" in let LBc := fresh "LBc" in let DB := fresh "DB" in
    let RFx := fresh "RFx" in let HRTx := fresh "HRTx" in let HSFx := fresh "HSFx" in let HIx := fresh "HIx" in
    let MIx := fresh "MIx" in let SSx := fresh "SSx" in let HFTx := fresh "HFTx" in let HHTx := fresh "HHTx" in
    intros R F fc m XSc s LBc DB RFx HRTx HSFx HIx MIx SSx;
    assert (HFTx : ftbl Wx ff m []) by apply ftbl_nil; assert (HHTx : ftbl Wx (ff / 8) m []) by apply ftbl_nil;
    exrun3wd dirs 0 0 HRTx HSFx HFTx HHTx HIx MIx 1000%nat stops kx.
  Ltac xseg_done :=
    let R' := fresh "R'" in let m' := fresh "m'" in
    let RFy := fresh "RFy" in let HRTy := fresh "HRTy" in let HTSy := fresh "HTSy" in let HPy := fresh "HPy" in
    let HMIy := fresh "HMIy" in let MUy := fresh "MUy" in let WMy := fresh "WMy" in
    let HSFy := fresh "HSFy" in let HFTy := fresh "HFTy" in let HHTy := fresh "HHTy" in
    intros R' m' RFy HRTy HTSy HPy HMIy MUy WMy; tsplit HTSy HSFy HFTy HHTy; cbn [s_pc];
    apply evt_done; exists R', m'; split; [reflexivity|]; split; [exact RFy|]; split; [exact HRTy|]; split; [exact HSFy|];
    split; [exact HPy|]; split; [exact HMIy|];
    lazymatch goal with HIx : Px _ ?s ?LBc ?m, SSx : xsess ?LBc ?len ?DB ?m |- _ =>
      eapply (xsess_run s LBc len DB m m' 0 0 _ _ _ _ _ _ eq_refl ltac:(clear; lia) ltac:(clear; lia));
        [let RHx := fresh "RHx" in destruct HIx as (_ & _ & RHx & _); exact RHx | exact SSx | exact MUy | exact WMy] end.

  Lemma sx32_eq : forall x, sx32A x = LbB_DiagStmt.sx32 x.
Proof.
  intros x. unfold sx32A, PrsGrammar.sx32, LbB_DiagStmt.sx32. destruct (x <? 2 ^ 31); lia.
Qed.

  Ltac rc1 := let R := fresh "R" in let HRT := fresh "HRT" in intros R HRT;
    let G1 := fresh in let G2 := fresh in let G8 := fresh in let G4 := fresh in let G10 := fresh in let G11 := fresh in
    rgetx HRT (1%bv : reg) G1; rgetx HRT (2%bv : reg) G2; rgetx HRT (8%bv : reg) G8; rgetx HRT (4%bv : reg) G4;
    rgetx HRT (10%bv : reg) G10; rgetx HRT (11%bv : reg) G11; rewrite sx32_eq in G11;
    exact (conj G1 (conj G2 (conj (eq_trans G8 (eq_sym (Z_to_bv_bv_unsigned (x_sp e)))) (conj G4 (conj G10 G11))))).
  Ltac kw_err :=
    lazymatch goal with SS : xsess _ _ _ ?m |- Forall (kentry_ok _ _ ?m) _ =>
      let ERR := fresh "ERR" in let D1 := fresh "D1" in let D2 := fresh "D2" in
      apply Forall_cons; [| apply Forall_nil];
      pose proof (dla_err _ _ (ds_laws_A LINV_P5 (fun m0 h => h)) _ _ _ _ _ _ (proj1 SS)) as ERR;
      pose proof (dla_def _ _ (ds_laws_A LINV_P5 (fun m0 h => h)) _ _ _ _ _ _ (proj1 SS)) as (_ & D1 & _ & D2 & _);
      unfold DS_SIZE in D2;
      eapply (kword_of_rw_cells _ _ _ _ _ 0 _ _ _ 4 ERR);
        [ reflexivity | reflexivity | lia
        | evwx; rewrite unsigned_lit by (pose proof ex_vals; lia); unfold SX_DS_OFF, DS_ERR_OFF; lia
        | unfold DS_ERR_OFF; lia | unfold DS_ERR_OFF; lia | vm_compute; reflexivity ]
    end.

  Lemma sx_ph2 : forall (Q : config -> Prop) c,
    xsr0 APDIAG SX_RT8 SX_SF7 c ->
    (forall c', xsr3 SN_DTOR_RA2 SX_RT9 SX_SF7 98304 c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof using HHbp HP FF THI PCI HPDIAG HCSEQ HU32 HDTOR.
    intros Q c X0 K.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & _ & TID & _).
    eapply (x_pdiag HPDIAG Q SX_RT8 SX_SF7 0xf9cd4 c X0); [vm_compute; reflexivity | rc3 | reflexivity | lia |].
    intros c1 X1. xn X1.
    eapply (x_run Q _ _ _ _ _ APUT_CSEQ _ SX_SF7 _ X1).
    { xseg0 (@nil bool) [APUT_CSEQ] (@nil kentry); [apply Forall_nil | apply Forall_nil | scT | xseg_done]. }
    intros c2 X2.
    eapply (x_cseq HCSEQ Q _ _ _ _ 0xf9ce8 0x24dc0 8 c2 X2);
      [ vm_compute; reflexivity | rc3 | reflexivity | lia | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | lit_acc 0x24dc0 9 32 | lit_bytes 0x24dc0 8%nat | lia | unfold SX_COST, SN_COST; lia |].
    intros c3 X3. xn X3.
    eapply (x_run Q _ _ _ _ _ APUT_U32 _ SX_SF7 _ X3).
    { xseg0 (@nil bool) [APUT_U32] (@nil kentry); [apply Forall_nil | apply Forall_nil | scT | xseg_done]. }
    intros c4 X4.
    eapply (x_u32 HU32 Q _ _ _ _ 0xf9cf4 (x_tid e) c4 X4);
      [vm_compute; reflexivity | rc1 | reflexivity | lia | exact TID | lia | unfold SX_COST, SN_COST; lia |].
    intros c5 X5. xn X5.
    eapply (x_run Q _ _ _ _ _ APUT_CSEQ _ SX_SF7 _ X5).
    { xseg0 (@nil bool) [APUT_CSEQ] (@nil kentry); [apply Forall_nil | apply Forall_nil | scT | xseg_done]. }
    intros c6 X6.
    eapply (x_cseq HCSEQ Q _ _ _ _ 0xf9d08 0x24e00 29 c6 X6);
      [ vm_compute; reflexivity | rc3 | reflexivity | lia | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | lit_acc 0x24e00 30 64 | lit_bytes 0x24e00 29%nat | lia | unfold SX_COST, SN_COST; lia |].
    intros c7 X7. xn X7.
    eapply (x_run Q _ _ _ _ _ ADS_DTOR _ SX_SF7 _ X7).
    { xseg0 (@nil bool) [ADS_DTOR] [KWord (SA (EVar 52) 856) 4 (ELit 4294967292)];
        [kw_err | apply Forall_nil | scT | xseg_done]. }
    intros c8 X8.
    eapply (x_dtor HDTOR Q _ _ _ _ c8 X8); [vm_compute; reflexivity | rc0 | unfold SX_COST, SN_COST; lia |].
    intros c9 X9. apply K.
    lazymatch type of X9 with xsr3 _ ?rt _ _ _ => replace SX_RT9 with rt by (vm_compute; reflexivity) end.
    exact X9.
  Qed.
End SnXR.
