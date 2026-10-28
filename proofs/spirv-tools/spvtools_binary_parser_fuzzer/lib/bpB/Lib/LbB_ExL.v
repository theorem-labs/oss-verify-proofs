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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_WoGen LbB_ExDefs LbB_ExKit LbB_ExT LbB_ExR1 LbB_ExE0.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_ExC LbB_ExS.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma disj_of_forall : forall (W : list (Z * Z)) A n, Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) W -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros A n FW; [exact I|]. cbn [disjoint_from].
  split; [exact (Forall_inv FW) | exact (IH A n (Forall_inv_tail FW))].
Qed.

Section ExL.
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
  Local Notation ds_cost_le := LbB_ExS.ds_cost_le (only parsing).
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
  Local Notation xchain_call := (@LbB_ExS.xchain_call HCEIL H HHbp e ff fp HP) (only parsing).
  Local Notation xsess := (@LbB_ExS.xsess H e ff) (only parsing).
  Local Notation xsess_facts := (@LbB_ExS.xsess_facts HCEIL H e ff HP) (only parsing).
  Local Notation x_ds_pre := (@LbB_ExS.x_ds_pre HCEIL H HHbp e ff fp HP) (only parsing).
  Local Notation sf_xpres := (@LbB_ExS.sf_xpres HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation x_ds_back := (@LbB_ExS.x_ds_back HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation xsr := (@LbB_ExS.xsr HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation rcall := (@LbB_ExS.rcall H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation x_ds_obj := (@LbB_ExS.x_ds_obj HCEIL H e ff fp HP FF) (only parsing).
  Local Notation x_cseq := (@LbB_ExS.x_cseq HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation rcall1 := (@LbB_ExS.rcall1 H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation rcall0 := (@LbB_ExS.rcall0 H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation x_u64 := (@LbB_ExS.x_u64 HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation xsr3 := (@LbB_ExS.xsr3 HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation x_dtor := (@LbB_ExS.x_dtor HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation x_run := (@LbB_ExS.x_run HCEIL H HHbp e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation xsess_win := (@LbB_ExS.xsess_win HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation x_stk_back := (@LbB_ExS.x_stk_back HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation x_strlen := (@LbB_ExS.x_strlen HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation xsess_run := (@LbB_ExS.xsess_run HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation xsr_mono := (@LbB_ExS.xsr_mono HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
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

  Local Notation ds := (ff + EX_DS_OFF) (only parsing).
  Local Notation LFx := ((3, ff, fp) :: x_LF e) (only parsing).

  Lemma x_ts : operand_type_str_stmtA ->
    forall (Q : config -> Prop) RT SF len spent (ret : Z) c,
    xsr AT_OPERAND_TYPE_STR RT SF len spent c -> fin 0 24 (fkeys SF) = true ->
    rcall0 RT ret (Z_to_bv 64 (x_ty e)) -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    forallb (fun re : reg * expr => wcl 61 (snd re)) (keptk RT) = true -> fwcl 61 SF = true ->
    (forall P L c', cstrA P L ->
       (@LbB_ExS.xsr HCEIL H e ff fp p1 n1 P L) ret (keptk RT ++ [(10%bv, EVar 61)]) SF len spent c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof.
    intros HTS Q RT SF len spent ret [msF mo] (s & F & fc & XSc & LBc & DB & KR & MP & FZ & CUT & AL) Hf RC Hr2 Hr CL1 CL2 K.
    cbn [cfg_ms cfg_model] in *.
    destruct CUT as (R & m & VIS & RF & HRT & HSF & HI & MI & SS).
    destruct (RC R HRT) as (G1 & G2 & G8 & G4 & G10).
    pose proof (xpre_geo H e HP) as (CE & LO & _). pose proof (xS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    destruct (ex_keep XSc s LBc m HI) as (AC & (RL & _) & _ & ST & _).
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & _ & _ & TYR & _).
    assert (Us1 : bv_unsigned (PropExec.getr R 2) = xS1 e) by (rewrite G2; apply unsigned_lit; lia).
    rewrite (MS_full_eq R F _ fc m _ RF) in VIS.
    eapply (ahh_evt_then H HH _ _ s msF _ mo KR VIS).
    { eapply (HTS (x_ty e)); rewrite ?Us1.
      - exact (proj1 (stk_split asegs m (x_lo e) (xS1 e) (xSP e) ST ltac:(lia))).
      - exact CE.
      - unfold TL_STACK. lia.
      - clear - S32. Z.div_mod_to_equations. lia.
      - lia.
      - exact MI.
      - exact AC.
      - split; [exact TYR|]. split; [exact G10 | exact RL]. }
    intros msF' mo' KR' MP' POST.
    destruct POST as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & EQ & MU & WM & MI' & ST' & AC' & (P & L & CS & RES & _)).
    rewrite Us1 in MU. rewrite G1, (ret_pc_even ret Hr Hr2) in EQ.
    lazymatch type of EQ with _ = MS ?R1 _ _ _ _ _ _ => set (R1' := R1) in * end.
    eapply (x_stk_back (as_SR H Q (mkCfg msF' mo')) XSc s LBc len DB m m' R R1' RT SF TL_STACK HI SS HRT HSF Hf
              ltac:(unfold TL_STACK; lia) MU WM MI').
    { intros r Hr0. cbn [In KEPT] in Hr0. subst R1'.
      repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | exact (eq_sym G1)]|]). destruct Hr0. }
    intros HI' SS' HRT' HSF'.
    apply (K P L _ CS). exists s, F, fc, XSc, LBc, DB.
    split; [exact KR'|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP')|]. split; [exact FZ|]. split; [| exact AL].
    exists R1', m'. split; [exact EQ|]. split; [apply rfull_mkR|].
    split.
    { apply rtbl_app.
      - eapply (rtbl_sw _ _ 61 _ _ (Wx_sw1 P L) CL1). exact HRT'.
      - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. exact RES. }
    split; [exact (ftbl_sw _ _ 61 _ _ _ (Wx_sw1 P L) CL2 HSF')|].
    split; [exact HI'|]. split; [exact MI' | exact SS'].
  Qed.

  Lemma x_os : opcode_string_stmtA H ->
    forall (Q : config -> Prop) RT SF len spent (ret : Z) c,
    xsr AT_OPCODE_STRING RT SF len spent c -> fin 0 24 (fkeys SF) = true ->
    rcall0 RT ret (Z_to_bv 64 (x_opc e)) -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    forallb (fun re : reg * expr => wcl 59 (snd re)) (keptk RT) = true -> fwcl 59 SF = true ->
    (forall P L c', cstrA P L ->
       (@LbB_ExS.xsr HCEIL H e ff fp P L p2 n2) ret (keptk RT ++ [(10%bv, EVar 59)]) SF len spent c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof.
    intros HOS Q RT SF len spent ret [msF mo] (s & F & fc & XSc & LBc & DB & KR & MP & FZ & CUT & AL) Hf RC Hr2 Hr CL1 CL2 K.
    cbn [cfg_ms cfg_model] in *.
    destruct CUT as (R & m & VIS & RF & HRT & HSF & HI & MI & SS).
    destruct (RC R HRT) as (G1 & G2 & G8 & G4 & G10).
    pose proof (xpre_geo H e HP) as (CE & LO & _ & _ & _ & TP). pose proof (xS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    destruct (ex_keep XSc s LBc m HI) as (AC & (RL & _) & _ & ST & _ & _ & RFS).
    pose proof HI as (_ & _ & RH & _).
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LFL & _ & _ & _ & _ & _ & _ & _
                      & _ & OPR & _).
    assert (Us1 : bv_unsigned (PropExec.getr R 2) = xS1 e) by (rewrite G2; apply unsigned_lit; lia).
    rewrite (MS_full_eq R F _ fc m _ RF) in VIS.
    eapply (ahh_evt_then H HH _ _ s msF _ mo KR VIS).
    { eapply (HOS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s LBc LFx (x_opc e) (x_lo e)); rewrite ?Us1.
      - exact G10.
      - lia.
      - exact (proj1 (stk_split asegs m (x_lo e) (xS1 e) (xSP e) ST ltac:(lia))).
      - exact CE.
      - unfold OS_STACK, AFS_STACK, TL_STACK. lia.
      - clear - S32. Z.div_mod_to_equations. lia.
      - lia.
      - exact RFS.
      - cbn [length]. unfold EX_FRAMES, DS_FRAMES in *. lia.
      - exact RH.
      - exact MI.
      - rewrite G4. exact TP.
      - exact AC.
      - exact RL. }
    intros msF' mo' KR' MP' POST.
    destruct POST as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & XS & P & L & EQ & RES & CS & FXS & MU & WM & MI' & ST' & RF' & AC' & RH').
    rewrite Us1 in MU, ST'. rewrite G1, (ret_pc_even ret Hr Hr2) in EQ.
    lazymatch type of EQ with _ = MS ?R1 _ _ _ _ _ _ => set (R1' := R1) in * end.
    assert (FW : Forall (fun iv : Z * Z => (x_lo e <= fst iv /\ snd iv <= xS1 e) \/ In iv XS) ((xS1 e - OS_STACK, xS1 e) :: XS)).
    { apply Forall_cons; [left; cbn [fst snd]; unfold OS_STACK, AFS_STACK, TL_STACK; lia|]. apply Forall_forall. intros iv Hiv. right. exact Hiv. }
    assert (HI' : Px (XSc ++ XS) s LBc m').
    { eapply (xinv_callee H HH e ff fp XSc XS s LBc s LBc m m' _ HP HI MU WM MI' ST' RF' AC' RH' FXS).
      eapply Forall_impl; [| exact FW]. intros iv [K0|K0]; [left; exact K0 | right; right; right; exact K0]. }
    assert (SS' : xsess LBc len DB m').
    { eapply (xsess_win s LBc len DB m m' _ RH RF' SS MU WM). eapply Forall_impl; [| exact FW].
      intros iv [K0|K0]; [left; exact K0 | right; exact (proj1 (Forall_forall _ _) FXS iv K0)]. }
    assert (HSF' : ftbl Wx (xS1 e) m' SF).
    { eapply (ftbl_munch Wx (xS1 e) m m' SF _ 0 24); [exact HSF | exact MU | exact WM | exact Hf |].
      apply disj_of_forall. eapply Forall_impl; [| exact FW]. intros iv [K0|K0]; right; [lia|].
      destruct (xfsw_ok H HH e ff fp m' iv RF' FF CE (proj1 (Forall_forall _ _) FXS iv K0)) as (_ & _ & _ & _ & _ & _ & B7 & _). lia. }
    assert (HRT' : rtbl Wx R1' (keptk RT)).
    { eapply rtbl_keep; [exact (rtbl_keptk Wx R RT HRT) | apply rsub_keptk |].
      intros r Hr0. cbn [In KEPT] in Hr0. subst R1'.
      repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | exact (eq_sym G1)]|]). destruct Hr0. }
    apply (K P L _ CS). exists s, F, fc, (XSc ++ XS), LBc, DB.
    split; [exact KR'|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP')|]. split; [exact FZ|]. split; [| exact AL].
    exists R1', m'. split; [exact EQ|]. split; [apply rfull_mkR|].
    split.
    { apply rtbl_app.
      - eapply (rtbl_sw _ _ 59 _ _ (Wx_sw P L p2 n2) CL1). exact HRT'.
      - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. exact RES. }
    split; [exact (ftbl_sw _ _ 59 _ _ _ (Wx_sw P L p2 n2) CL2 HSF')|].
    split; [exact HI'|]. split; [exact MI' | exact SS'].
  Qed.
End ExL.
