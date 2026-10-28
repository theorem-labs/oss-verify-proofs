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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtorR1 LbB_DPdK LbB_PmXp.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_WoGen LbB_ExDefs LbB_ExKit LbB_ExT LbB_ExR1 LbB_ExE0.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_ExC.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition EX_PD_RA : Z := 0xf8dfc.

Definition EX_RT8 : list (reg * expr) :=
  [(1%bv, ELit EX_PD_RA); (2%bv, EVar 58); (3%bv, EVar 50); (4%bv, EVar 51); (8%bv, EVar 33); (9%bv, EVar 58);
   (10%bv, EAlu ALU_ADD (EVar 52) (ELit 32)); (11%bv, EVar 32); (12%bv, ELit (2 ^ 64 - 4)); (18%bv, EVar 52);
   (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit 2147450880)); (20%bv, EVar 35);
   (21%bv, EAlu ALU_ADD (EVar 52) (ELit 32)); (22%bv, EVar 37); (23%bv, EVar 32); (24%bv, EVar 36); (25%bv, EVar 52);
   (26%bv, ELit 2147450880); (27%bv, EVar 49)].

Definition EX_RT7 : list (reg * expr) :=
  [(1%bv, ELit 1019408); (2%bv, EVar 58); (3%bv, EVar 50); (4%bv, EVar 51); (8%bv, EVar 33); (9%bv, EVar 58);
   (10%bv, EAlu ALU_ADD (EVar 52) (ELit 32)); (11%bv, ELit 148672); (12%bv, ELit 38); (18%bv, EVar 52);
   (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit 2147450880)); (20%bv, EVar 35);
   (21%bv, EAlu ALU_ADD (EVar 52) (ELit 32)); (22%bv, EVar 37); (23%bv, EVar 32); (24%bv, EVar 36); (25%bv, EVar 52);
   (26%bv, ELit 2147450880); (27%bv, EVar 49)].

Definition EX_SF : list fent := [(16, 8%nat, EVar 52)].

Section ExA.
  Local Notation PD_SHB := LbB_DPdK.PD_SHB (only parsing).

  Local Notation kst_ex := LbB_ExT.kst_ex (only parsing).
  Local Notation shT := LbB_ExT.shT (only parsing).
  Local Notation kT := LbB_ExT.kT (only parsing).
  Local Notation wok := LbB_ExT.wok (only parsing).
  Local Notation wok_facts := LbB_ExT.wok_facts (only parsing).
  Local Notation wk_win := LbB_ExT.wk_win (only parsing).
  Local Notation fin_wider := LbB_ExT.fin_wider (only parsing).
  Local Notation rtbl_sw := LbB_ExT.rtbl_sw (only parsing).
  Local Notation ftbl_sw := LbB_ExT.ftbl_sw (only parsing).
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

  Local Notation ftbl_xpres := (@LbB_ExT.ftbl_xpres HCEIL H) (only parsing).
  Local Notation Wx := (@LbB_ExT.Wx H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation Px := (@LbB_ExT.Px HCEIL H e ff fp) (only parsing).
  Local Notation ex_ranges := (@LbB_ExT.ex_ranges HCEIL H e ff fp HP FF) (only parsing).
  Local Notation ex_vals := (@LbB_ExT.ex_vals HCEIL H e ff fp HP FF) (only parsing).
  Local Notation ex_wins := (@LbB_ExT.ex_wins HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xobj_range := (@LbB_ExT.xobj_range HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation ex_keepT := (@LbB_ExT.ex_keepT HCEIL H HHbp e ff fp HP FF THI PCI) (only parsing).
  Local Notation ex_keep := (@LbB_ExT.ex_keep HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation evWx := (@LbB_ExT.evWx H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation kst_ex_ok := (@LbB_ExT.kst_ex_ok HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation evT := (@LbB_ExT.evT HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation shT_start := (@LbB_ExT.shT_start HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation shT_apart := (@LbB_ExT.shT_apart HCEIL H HHbp e ff fp HP FF THI) (only parsing).
  Local Notation shb_eq0 := (@LbB_ExT.shb_eq0 ff) (only parsing).
  Local Notation this_apart := (@LbB_ExT.this_apart HCEIL H HHbp e ff fp HP FF THI) (only parsing).
  Local Notation kT_ok := (@LbB_ExT.kT_ok HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF THI PCI) (only parsing).
  Local Notation scT_flat := (@LbB_ExT.scT_flat HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation scP_flat := (@LbB_ExT.scP_flat HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tS := (@LbB_ExT.tS H e) (only parsing).
  Local Notation tFw := (@LbB_ExT.tFw ff) (only parsing).
  Local Notation tHw := (@LbB_ExT.tHw ff) (only parsing).
  Local Notation tF := (@LbB_ExT.tF ff) (only parsing).
  Local Notation tH := (@LbB_ExT.tH ff) (only parsing).
  Local Notation tab_vals := (@LbB_ExT.tab_vals HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_wf3w := (@LbB_ExT.tabs_wf3w HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_wf3 := (@LbB_ExT.tabs_wf3 HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation wk_stk := (@LbB_ExT.wk_stk HCEIL H e ff fp HP FF) (only parsing).
  Local Notation shb_eq := (@LbB_ExT.shb_eq ff) (only parsing).
  Local Notation tabs_ok3w := (@LbB_ExT.tabs_ok3w HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_ok3 := (@LbB_ExT.tabs_ok3 HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation Px_step3w := (@LbB_ExT.Px_step3w HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation Px_step3 := (@LbB_ExT.Px_step3 HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation Wx_sw1 := (@LbB_ExT.Wx_sw1 HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation Wx_sw := (@LbB_ExT.Wx_sw HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation ex_shvis := (@LbB_ExC.ex_shvis HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation fr_app := (@LbB_ExC.fr_app HCEIL H e ff fp HP FF) (only parsing).
  Local Notation fr_addr := (@LbB_ExC.fr_addr HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation fr_str := (@LbB_ExC.fr_str HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation xwin_stk := (@LbB_ExC.xwin_stk HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xwin_fr := (@LbB_ExC.xwin_fr H e ff) (only parsing).
  Local Notation Px_win := (@LbB_ExC.Px_win HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation obj_apart := (@LbB_ExC.obj_apart HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation blk_apart := (@LbB_ExC.blk_apart HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xds_run := (@LbB_ExC.xds_run HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xcut := (@LbB_ExC.xcut HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
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

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Ltac scT := unfold scs_denot; repeat (apply Forall_cons; [cbn [sc_denot]; unfold elenZ; cbn [edenot]; rewrite ?unsigned_lit by (clear; lia);
                                           first [apply scT_flat; clear; lia | apply scP_flat; clear; lia] |]); apply Forall_nil.

  Ltac tnormc H :=
    lazymatch type of H with ftbl ?W ?B ?m ?t => let l := eval vm_compute in t in change t with l in H end.

  Ltac tsplitx HTS H1 H2 H3 :=
    unfold tupd in HTS; cbn [map] in HTS;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS]; apply Forall_cons_iff in HTS as [H3 _];
    unfold LbB_ExT.tS, LbB_ExT.tFw, LbB_ExT.tHw in H1, H2, H3; cbn [fst snd tB tb ttbl tks] in H1, H2, H3;
    tnormc H1; tnormc H2; tnormc H3.

  Lemma ex_ph1 : forall R m XSc sk LBk, rfull R -> rtbl Wx R EX_RT2 -> Px XSc sk LBk m -> mem_inv asegs m ->
    evt asegs (xcut APDIAG (x_F e) (x_fc e) EX_RT8 EX_SF XSc sk LBk (fun m' => addressable m' (ff + EX_DS_OFF) DS_SIZE))
        (MS R (x_F e) (Z_to_bv 64 EX_SM_RA) (x_fc e) None m (seg_rom asegs)).
  Proof using HHbp HP FF THI PCI.
    intros R m XSc sk LBk RF HRT HPX MI.
    assert (HSF : ftbl Wx (xS1 e) m []) by apply Forall_nil.
    assert (HFT : ftbl Wx ff m []) by apply Forall_nil.
    assert (HHT : ftbl Wx (ff / 8) m []) by apply Forall_nil.
    unfold EX_SM_RA.
    exrun3 HRT HSF HFT HHT HPX MI 400%nat [APDIAG] (@nil kentry).
    1: apply Forall_nil.
    1: apply Forall_nil.
    1: scT.
    intros R' m' RF' HRT' HTS HP' MI' _ _.
    tsplitx HTS HS1 HS2 HS3.
    apply evt_done. exists R', m'.
    split; [reflexivity|]. split; [exact RF'|].
    split; [eapply rtbl_sub; [exact HRT' | vm_compute; reflexivity]|].
    split; [eapply ftbl_sub; [exact HS1 | vm_compute; reflexivity]|].
    split; [exact HP'|]. split; [exact MI'|].
    unfold EX_DS_OFF, DS_SIZE.
    exact (fr_addr m' _ 32 392 HS3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl).
  Qed.

  Lemma ex_ph2m : forall (S : mem -> Prop) R F fc m XSc sk LBk, rfull R -> rtbl Wx R (keptk EX_RT8) ->
    ftbl Wx (xS1 e) m EX_SF -> Px XSc sk LBk m -> mem_inv asegs m ->
    (forall m', munch (winsT [tS EX_SF []; tFw 0 [] []; tHw 0 [] []]) m m' -> wmono asegs m m' -> S m') ->
    evt asegs (xcut APUT_CSEQ F fc EX_RT7 EX_SF XSc sk LBk S) (MS R F (Z_to_bv 64 EX_PD_RA) fc None m (seg_rom asegs)).
  Proof using HHbp HP FF.
    intros S R F fc m XSc sk LBk RF HRT HSF HPX MI KS.
    assert (HFT : ftbl Wx ff m []) by apply Forall_nil.
    assert (HHT : ftbl Wx (ff / 8) m []) by apply Forall_nil.
    unfold EX_PD_RA.
    exrun3w 0 0 HRT HSF HFT HHT HPX MI 50%nat [APUT_CSEQ] (@nil kentry).
    1: apply Forall_nil.
    1: apply Forall_nil.
    1: scT.
    intros R' m' RF' HRT' HTS HP' MI' MU WM.
    tsplitx HTS HS1 HS2 HS3.
    apply evt_done. exists R', m'.
    split; [reflexivity|]. split; [exact RF'|].
    split; [eapply rtbl_sub; [exact HRT' | vm_compute; reflexivity]|].
    split; [eapply ftbl_sub; [exact HS1 | vm_compute; reflexivity]|].
    split; [exact HP'|]. split; [exact MI'|].
    exact (KS m' MU WM).
  Qed.
End ExA.
