(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts S1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HCommon HLib HConstsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBase PmHyps PmCoreS1 PmStepS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2S1 PmLoopS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Plain.M.loaded_segments.

Module Ly := S1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_callees SEGS Ly.L MI ST G tcS1 dcS1 nfcS1 HConstsS1.hc ccS1 kcS1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBase.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cl_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_exit := (PmCoreS1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepS1.pmx_ds_room CL).
  #[local] Notation pm_tail_68410 := (PmStepS1.pm_tail_68410 CL).
  #[local] Notation cregs_kept := (PmStepS1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepS1.pm_put_cstr CL).
  #[local] Notation pm_put_num := (PmStepS1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepS1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepS1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepS1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepS1.pm_put_int CL).
  #[local] Notation pm_ctor := (PmStepS1.pm_ctor CL).
  #[local] Notation pm_pdiag := (PmStepS1.pm_pdiag CL).
  #[local] Notation pm_pdiag0 := (PmStepS1.pm_pdiag0 CL).
  #[local] Notation pm_pdiagE := (PmStepS1.pm_pdiagE CL).
  #[local] Notation pm_dtor := (PmStepS1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepS1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepS1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepS1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepS1.pm_binend CL).
  #[local] Notation pm_ecw_pb := (PmStep2S1.pm_ecw_pb CL).
  #[local] Notation pm_opcode_split := (PmStep2S1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2S1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2S1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2S1.pm_lookup_ext CL).

  Ltac stin ::= repeat (first [ match goal with |- stores_in _ ?a ?b => constr_eq a b; apply stores_in_refl end
                             | eapply stores_in_wbytes_more; [ | lia | w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                                              | w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zwin; intros; lia ] ]).

  Lemma pm_tail_66bbc : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (err len : Z) (B : list (Z * Z)),
    PMS w c0 K -> PMX w A M model c -> c_tr c = B -> pm_bud (w_n w) c ->
    ds_rep A M (w_sp w + 272) err len B -> - 2 ^ 31 <= err < 0 ->
    frm_zero (@fp_csr fx) ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    srealizes SEGS (cfg fx R 0x66c60 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R err len B PS X Htr BUD DS Herr FZ Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME in *.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M (w_sp w + 272 + 360) (err mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound err (2 ^ 32)); cbn; lia | exact Herrc]. }
    pose (E := Eseed R [Z_to_bv 64 (w_sp w); sxw (err mod 2 ^ 32)]).
    seedHR HR E [(2%bv, EVar 32)] R.
    assert (HK : know_ok SEGS E M [KRange (EVar 32) (2 ^ 24) (2 ^ 47)]).
    { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [] [EVar 33] []) 50%N.
    { split_scs. sc_rd_sx Cerr. }
    name_run HRn R1. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (10%bv) G10. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A M model c R1 err len _ B []);
      [exact PS | exact X | rewrite Htr, app_nil_r; reflexivity | exact BUD | rewrite Zlength_nil; lia | exact DS | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros A' R' M' model' X' BUD' KEPT AG.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G26 Qs10.
    pose proof (Z.mod_pos_bound err (2 ^ 32) ltac:(lia)) as Hm.
    assert (Hnz : err mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add err 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    eapply (pm_latch_err w c0 K fx A' M' model' (set_tr c []) R' (err mod 2 ^ 32) PS X' eq_refl BUD' FZ Qsp' Qgp' Qtp' Qs10 ltac:(lia)).
  Qed.

  Lemma cellw_frame : forall M M' a (wd : N) v,
    cellw SEGS M a wd v -> 0 <= a -> a + Z.of_N wd < 2 ^ 64 -> CRep.agree_on (zwin a (a + Z.of_N wd)) M M' -> cellw SEGS M' a wd v.
  Proof using.
    intros M M' a wd v [Hv Hr] Ha Hw AG. split; [exact Hv|]. rewrite (rdn_agree_win SEGS M M' a (N.to_nat wd)); [exact Hr | lia | rewrite N_nat_Z; lia |].
    rewrite N_nat_Z. exact AG.
  Qed.
  Lemma loop_mem_frame : forall (w : pmw MI ST) M M',
    loop_mem w M -> 0 <= w_sp w -> w_sp w + 144 < 2 ^ 64 -> CRep.agree_on (zwin (w_sp w + 16) (w_sp w + 144)) M M' -> loop_mem w M'.
  Proof using AC MI ST.
    intros w M M' LM Hlo Hhi AG. unfold loop_mem, hdr_consts in *.
    repeat match goal with |- Forall _ (_ :: _) => apply Forall_cons; [| ] | |- Forall _ [] => apply Forall_nil end;
    match goal with |- fld _ _ (w_sp w + fst ?oc) 8 _ =>
      pose proof (proj1 (Forall_forall _ _) LM oc ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])) as F; cbn [fst snd] in F |- *;
      eapply fld_agree; [lia | cbn; lia | exact F | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]] end.
  Qed.
  Definition SREGS : list reg := [18; 19; 20; 21; 22; 24]%bv.
  Lemma loop_regs_glue : forall (w : pmw MI ST) R R1,
    loop_regs w R -> (forall r, In r SREGS -> getr R1 r = getr R r) ->
    getr R1 2%bv = Z_to_bv 64 (w_sp w) -> getr R1 3%bv = getr R 3%bv -> getr R1 4%bv = getr R 4%bv -> getr R1 8%bv = Z_to_bv 64 (w_p w) ->
    (getr R1 9%bv = getr R 9%bv \/ getr R1 9%bv = Z_to_bv 64 (w_p w + 240)) ->
    loop_regs w R1.
  Proof using AC MI ST.
    intros w R R1 LR GS G2 G3 G4 G8 G9. destruct LR as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs6 & Qs8).
    assert (G9' : getr R1 9%bv = Z_to_bv 64 (w_p w + 240)) by (destruct G9 as [G9|G9]; [rewrite G9; exact Qs1 | exact G9]).
    unfold loop_regs. rewrite G2, G3, G4, G8, G9', Qgp, Qtp. rewrite !GS by (unfold SREGS; (first [solve [clear; cbn; tauto] | cbn; tauto])).
    rewrite Qs2, Qs3, Qs4, Qs5, Qs6, Qs8. repeat split; reflexivity.
  Qed.
  Lemma loop_regs_kept : forall (w : pmw MI ST) R R', loop_regs w R -> kept R R' -> loop_regs w R'.
  Proof using AC MI ST.
    intros w R R' LR KP. destruct LR as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs6 & Qs8). unfold loop_regs.
    rewrite !KP by (first [solve [clear; cbv; tauto] | cbv; tauto]). repeat split; assumption.
  Qed.
  Lemma loop_mem_cell : forall (w : pmw MI ST) M o v,
    loop_mem w M -> In (o, v) (hdr_consts w) -> 0 <= v < 2 ^ 64 -> cellw SEGS M (w_sp w + o) 8 v.
  Proof using AC MI ST. intros w M o v LM Hin Hv. split; [cbn; lia|]. exact (proj1 (Forall_forall _ _) LM (o, v) Hin). Qed.

  Lemma ext_val_zx2 : forall v, 0 <= v < 2 ^ 16 -> ext_val false 0 2 (Z_to_bv 64 v) = Z_to_bv 64 v.
  Proof using. intros v Hv. apply ext_val_zx_id. rewrite u64_of_Z by lia. cbn. lia. Qed.

  Lemma pm_D5 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (iwc : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> loop_mem w M ->
    cellw SEGS M (w_sp w + 218) 2 iwc -> c_icount c < 2 ^ 62 ->
    frm_zero (@fp_csr fx) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    srealizes SEGS (cfg fx R 0x66d54 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R iwc PS X Htr BUD LM Ciwc Hic FZ Qs0 Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (proj1 Ciwc) as Riwc. cbn in Riwc.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13. rreg HRn (14%bv) G14. rreg HRn (15%bv) G15.
    rewrite w_add in G10, G11, G13, G15 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (Mw0 := m) end.
    assert (STw : stores_in (fun a => zwin (w_sp w + 160) (w_sp w + 160 + 24) a \/ zwin (w_sp w + 752) (w_sp w + 752 + 2) a \/ zwin (w_sp w + 728) (w_sp w + 728 + 2) a) M Mw0) by (unfold Mw0; stin).
    assert (Xw : PMX w A Mw0 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact STw | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (cellw_frame _ Mw0) in Ciwc; [| lia | cbn; lia | eapply stores_in_agree; [exact STw | unfold zwin; cbn; intros; lia]].
    eapply (loop_mem_frame w _ Mw0) in LM; [| lia | lia | eapply stores_in_agree; [exact STw | unfold zwin; intros; lia]].
    clear STw.
    eapply (pm_ctor w c0 K fx A Mw0 model c R1 (-4) (w_sp w + 160) (w_sp w + 752) (w_sp w + 728) _ []);
      [exact PS | exact Xw | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact G13 | exact G14 | exact G15 | lia
      | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia
      | unfold Mw0; rdback | unfold Mw0; rdback |].
    clear Xw.
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M1) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    assert (C728 : cellw SEGS M1 (w_sp w + 728) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 728) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    assert (C752 : cellw SEGS M1 (w_sp w + 752) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 752) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    clear AG. clearbody Mw0.
    pm_seed R1c w (set_tr c (B1 ++ [])) [Z_to_bv 64 0].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    apply (know_more E M1 [KWord (SA (EVar 32) 728) (N.to_nat 1) (EVar 39); KWord (SA (EVar 32) 752) (N.to_nat 1) (EVar 39); KRange (EVar 39) 0 0; KWord (SA (EVar 32) 128) (N.to_nat 8) (ELit 82108)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact C728 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact C752 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kword_var; [eapply (loop_mem_cell w _ 128 82108 LM); [(first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [true; true] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    clear C728 C752.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x140bc 32 32 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M2) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M2) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 iwc].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 218) (N.to_nat 2) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u16 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-4) _ (iwc) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; rewrite ext_val_zx2 by lia; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M3) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M3) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    eapply (pm_tail_66bbc w c0 K fx A3 M3 model3 _ R3c (-4) _ B3);
      [exact PS | exact X3 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD3 | exact DS3 | lia | exact FZ | exact Qsp | exact Qgp | exact Qtp].
  Qed.

  Lemma pm_D6 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (op : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    cellw SEGS M (w_sp w + 234) 2 op -> c_icount c < 2 ^ 62 ->
    frm_zero (@fp_csr fx) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    srealizes SEGS (cfg fx R 0x66dc4 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R op PS X Htr BUD Cop Hic FZ Qs0 Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (proj1 Cop) as Rop. cbn in Rop.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13. rreg HRn (14%bv) G14. rreg HRn (15%bv) G15.
    rewrite w_add in G10, G11, G13, G15 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (Mw0 := m) end.
    assert (STw : stores_in (fun a => zwin (w_sp w + 160) (w_sp w + 160 + 24) a \/ zwin (w_sp w + 752) (w_sp w + 752 + 2) a \/ zwin (w_sp w + 728) (w_sp w + 728 + 2) a) M Mw0) by (unfold Mw0; stin).
    assert (Xw : PMX w A Mw0 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact STw | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (cellw_frame _ Mw0) in Cop; [| lia | cbn; lia | eapply stores_in_agree; [exact STw | unfold zwin; cbn; intros; lia]].
    clear STw.
    eapply (pm_ctor w c0 K fx A Mw0 model c R1 (-4) (w_sp w + 160) (w_sp w + 752) (w_sp w + 728) _ []);
      [exact PS | exact Xw | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact G13 | exact G14 | exact G15 | lia
      | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia
      | unfold Mw0; rdback | unfold Mw0; rdback |].
    clear Xw.
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in Cop; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    assert (C728 : cellw SEGS M1 (w_sp w + 728) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 728) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    assert (C752 : cellw SEGS M1 (w_sp w + 752) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 752) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    clear AG. clearbody Mw0.
    pm_seed R1c w (set_tr c (B1 ++ [])) [Z_to_bv 64 0].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    apply (know_more E M1 [KWord (SA (EVar 32) 728) (N.to_nat 1) (EVar 39); KWord (SA (EVar 32) 752) (N.to_nat 1) (EVar 39); KRange (EVar 39) 0 0]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact C728 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact C752 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [true; true] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    clear C728 C752.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x13548 16 16 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M2) in Cop; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 op].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 234) (N.to_nat 2) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cop | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u16 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-4) _ (op) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; rewrite ext_val_zx2 by lia; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M3) in Cop; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    eapply (pm_tail_66bbc w c0 K fx A3 M3 model3 _ R3c (-4) _ B3);
      [exact PS | exact X3 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD3 | exact DS3 | lia | exact FZ | exact Qsp | exact Qgp | exact Qtp].
  Qed.

  Lemma kword_expr : forall E M (base : expr) (b off : Z) (w : N) (v : Z) (e : expr),
    cellw SEGS M (b + off) w v -> (w <= 8)%N ->
    edenot E base = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 -> 0 <= b + off < 2 ^ 64 -> b + off + Z.of_N w <= 2 ^ 64 ->
    edenot E e = Z_to_bv 64 v ->
    kentry_ok SEGS E M (KWord (SA base off) (N.to_nat w) e).
  Proof using.
    intros E M base b off w v e [Hv Hr] Hw Hn Hb Hbo Hbow He. cbn [kentry_ok]. rewrite !N_nat_Z.
    split; [lia|]. split.
    - unfold flat, estart. cbn [a_base a_off]. rewrite Hn, u64_of_Z by lia. lia.
    - unfold adenot. cbn [a_base a_off]. rewrite Hn, He, v_addi_Z by lia. exact Hr.
  Qed.
  Lemma kdisj_expr : forall E M (e1 e2 : expr) (b1 b2 o1 o2 l1 l2 : Z),
    edenot E e1 = Z_to_bv 64 b1 -> edenot E e2 = Z_to_bv 64 b2 -> 0 <= b1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 ->
    0 <= l1 < 2 ^ 64 -> 0 <= l2 < 2 ^ 64 ->
    (b1 + o1 + l1 <= b2 + o2 \/ b2 + o2 + l2 <= b1 + o1) ->
    kentry_ok SEGS E M (KDisj (SA e1 o1) (ELit l1) (SA e2 o2) (ELit l2)).
  Proof using.
    intros E M e1 e2 b1 b2 o1 o2 l1 l2 H1 H2 Hb1 Hb2 Hl1 Hl2 H. cbn [kentry_ok].
    unfold estart, elenZ. cbn [a_base a_off]. rewrite H1, H2. cbn [edenot]. rewrite !u64_of_Z by lia. exact H.
  Qed.

  Lemma w2lb4_sx32 : forall v, 0 <= v < 2 ^ 32 -> word_to_le_bytes 4 (Z_to_bv 64 (PrsNeeds.sx32 v)) = word_to_le_bytes 4 (Z_to_bv 64 v).
  Proof using. intros v Hv. rewrite <- (sxw_sx32 v Hv). unfold sxw. change 32%N with (8 * 4)%N. apply (word_to_le_bytes_swrap 4). cbn; lia. Qed.

  Definition WIX : expr := EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 38)).
  Lemma wix_val : forall E words widx, ev E 34 = Z_to_bv 64 words -> ev E 38 = Z_to_bv 64 widx ->
    0 <= words -> 0 <= widx -> words + 4 * widx < 2 ^ 64 -> edenot E WIX = Z_to_bv 64 (words + 4 * widx).
  Proof using.
    intros E words widx H34 H38 Hw Hi Hhi. cbn [edenot WIX]. rewrite H34, H38. rewrite w_mul by lia. rewrite w_add by lia. reflexivity.
  Qed.

  Ltac rdbackz := unfold CRep.fld; repeat (rewrite rdn_wbytes_out_Z by (w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia));
                  first [ apply rdn_wbytes_self; w2blen; rewrite u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                        | rewrite rdn_wbytes_prefix; [ reflexivity | w2blen; rewrite u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | w2blen; lia ]
                        | change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (zeros 8); rewrite rdn_wbytes_zeros_in;
                          [ reflexivity | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite !u64_of_Z by lia; lia | rewrite !u64_of_Z by lia; lia
                          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite !u64_of_Z by lia; lia ] ].

  Definition izero (w : pmw MI ST) (M : mem) : Prop :=
    cellw SEGS M (w_sp w + 224) 8 0 /\ cellw SEGS M (w_sp w + 232) 2 0 /\ cellw SEGS M (w_sp w + 236) 4 0 /\
    cellw SEGS M (w_sp w + 240) 4 0 /\ cellw SEGS M (w_sp w + 244) 4 0 /\ cellw SEGS M (w_sp w + 248) 8 0 /\ cellw SEGS M (w_sp w + 256) 8 0.
  Lemma izero_agree : forall (w : pmw MI ST) M M', izero w M -> 0 <= w_sp w -> w_sp w + 264 < 2 ^ 64 ->
    CRep.agree_on (fun a => zwin (w_sp w + 224) (w_sp w + 264) a /\ ~ zwin (w_sp w + 234) (w_sp w + 236) a) M M' -> izero w M'.
  Proof using AC MI ST.
    intros w M M' IZ Hlo Hhi AG. destruct IZ as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold izero.
    repeat match goal with |- _ /\ _ => split end;
      (eapply (cellw_frame M M'); [eassumption | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]]).
  Qed.

  Definition ictx (w : pmw MI ST) (M : mem) (io fw iwc op d : Z) : Prop :=
    cellw SEGS M (w_sp w + 200) 8 io /\ cellw SEGS M (w_sp w + 220) 4 fw /\ cellw SEGS M (w_sp w + 218) 2 iwc /\
    cellw SEGS M (w_sp w + 234) 2 op /\ fld SEGS M (w_sp w + 208) 8 d.
  Lemma ictx_agree : forall (w : pmw MI ST) M M' io fw iwc op d, ictx w M io fw iwc op d -> 0 <= w_sp w -> w_sp w + 264 < 2 ^ 64 ->
    CRep.agree_on (fun a => zwin (w_sp w + 200) (w_sp w + 224) a \/ zwin (w_sp w + 234) (w_sp w + 236) a) M M' -> ictx w M' io fw iwc op d.
  Proof using AC MI ST.
    intros w M M' io fw iwc op d IC Hlo Hhi AG. destruct IC as (C1 & C2 & C3 & C4 & C5). unfold ictx.
    repeat match goal with |- _ /\ _ => split end;
      [ eapply (cellw_frame M M'); [eassumption | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]] .. |].
    eapply fld_agree; [lia | cbn; lia | exact C5 | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]].
  Qed.
  Lemma hi16_range : forall v, 0 <= v < 2 ^ 32 -> 0 <= v / 2 ^ 16 < 2 ^ 16.
  Proof using. intros v Hv. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
  Lemma lo16_range : forall v, 0 <= v mod 2 ^ 16 < 2 ^ 16.
  Proof using. intros v. apply Z.mod_pos_bound. lia. Qed.

  Lemma pm_B1 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> LI w A M model c R -> c_widx c < w_n w -> getr R 10%bv = Z_to_bv 64 (c_widx c) ->
    (forall A' M' model' c' R' (fw iwc op d : Z),
        PMX w A' M' model' c' -> c_tr c' = [] -> pm_bud (w_n w) c' -> loop_regs w R' -> loop_mem w M' -> izero w M' ->
        ictx w M' (c_widx c) fw iwc op d -> iwc = fw / 2 ^ 16 -> op = fw mod 2 ^ 16 -> iwc <> 0 -> 0 <= fw < 2 ^ 32 ->
        (exists l, g_op G op = Some l) -> idesc d op ->
        c_widx c' = c_widx c + 1 -> c_icount c' = c_icount c + 1 -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c ->
        t3b (c_v1 c') = 0 -> t3b (c_v2 c') = [fw] ->
        c_m1 c' = c_m1 c -> c_m2 c' = c_m2 c -> c_m3 c' = c_m3 c -> c_v3 c' = c_v3 c -> t3c (c_v1 c') = t3c (c_v1 c) ->
        srealizes SEGS (cfg fx R' 0x66e4c M' model') K) ->
    srealizes SEGS (cfg fx R 0x66c88 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS FZ HLI Hlt Qa0 B2K.
    destruct HLI as (X & Htr & BUD & LR & LM & Hw5 & He2 & Hw & ACC & MACC).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof LR as LR'. destruct LR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs6 & Qs8).
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5).

    destruct (mdef_cell4 M (w_words w + 4 * c_widx c) ltac:(eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (fw & Cfw).
    pose proof (proj1 Cfw) as Rfw. cbn in Rfw.
    pose proof (fld_cellw M _ 4 _ (x_endian X) ltac:(lia)) as Ce. unfold O_ENDIAN in Ce.
    pm_seed R w c [Z_to_bv 64 (c_endian c); Z_to_bv 64 fw].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 38)] R. seedHK HK w A M model c E X.
    assert (AW : edenot E WIX = Z_to_bv 64 (w_words w + 4 * c_widx c)) by (apply wix_val; [evs; reflexivity | evs; reflexivity | lia | lia | lia]).
    apply (know_more E M [KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 39); KWord (SA WIX 0) (N.to_nat 4) (EVar 40);
                           KDisj (SA WIX 0) (ELit 4) (SA (EVar 32) 0) (ELit 880); KDisj (SA WIX 0) (ELit 4) (SA (EVar 33) 0) (ELit 288)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_expr; [rewrite Z.add_0_r; exact Cfw | cbn; lia | exact AW | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
           destruct (W5 (w_words w + 4 * c_widx c) ltac:(unfold zwin; lia)) as [Hnw _].
           destruct (W5 (w_words w + 4 * c_widx c + 3) ltac:(unfold zwin; lia)) as [Hnw' _]. unfold zwin in Hnw, Hnw'. lia.
         - eapply kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
           destruct (W5 (w_words w + 4 * c_widx c) ltac:(unfold zwin; lia)) as [_ Hnp].
           destruct (W5 (w_words w + 4 * c_widx c + 3) ltac:(unfold zwin; lia)) as [_ Hnp']. lia. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1. all: eapply sc_flat; [exact AW | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof (syms_id_sound _ _ _ _ SREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs. pose proof (loop_regs_glue w R R1 LR GS G2 G3 G4 G8 (or_introl G9)) as LR1. clear GS G9. rewrite Qgp in G3. rewrite Qtp in G4.
    rewrite ext_val_sx4 in G10 by lia. rewrite ext_val_sx4, sx32_small in G11 by lia. rewrite w_add by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) end.
    assert (ST1 : stores_in (fun a => zwin (w_p w + 80) (w_p w + 88) a \/ zwin (w_sp w + 224) (w_sp w + 264) a) M M1) by (unfold M1; stin).
    set (c1 := set_scal c (c_widx c) (c_icount c + 1) (c_endian c) (c_reqconv c)).
    assert (X1 : PMX w A M1 model c1).
    { eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img);
        [exact X | exact ST1 | intros a [Ha|Ha]; unfold scal_win, zwin, O_WIDX, O_FLAGS, w_sp0, PM_FRAME in *; [right; lia | left; lia]
        | eapply fld_keep; [exact ST1 | exact (x_widx X) | unfold O_WIDX; lia | unfold O_WIDX; cbn; lia | unfold O_WIDX, zwin; cbn; intros; lia]
        | unfold M1, O_ICOUNT; rdback
        | eapply fld_keep; [exact ST1 | exact (x_endian X) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST1 | exact (x_flags X) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | unfold O_FLAGS, zwin; cbn; intros; lia]
        | lia | lia | lia | exact Sc4]. }
    eapply (loop_mem_frame w _ M1) in LM; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
    assert (IZ : izero w M1) by (unfold izero, M1; repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | rdbackz])).
    clear ST1 X. clearbody M1. pose proof (x_ms X1) as MS1. assert (He32 : 0 <= c_endian c < 2 ^ 32) by lia.

    eapply (pm_fixword w A M1 model c1 fx R1 _ K X1 (ex_intro _ fw (ex_intro _ (c_endian c) (conj Rfw (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 KEPT (r1 & Rr1 & Hr1). rewrite TablStmts.sx32_prs in Hr1.
    keptQ KEPT G2 Qsp'. keptQ KEPT G8 Qs0'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. clear G1 G2 G3 G4 G8 G10 G11 Qa0.
    pose proof (loop_regs_kept w R1 R2 LR1 KEPT) as LR2. clear LR1 KEPT.
    rename Qsp' into Qsp2. rename Qs0' into Qs02. rename Qgp' into Qgp2. rename Qtp' into Qtp2.

    pose proof (x_v2 X1) as V2. cbn [c1 c_v2 set_scal] in V2. destruct V2 as (_ & _ & _ & V2len & V2blk & V2f0 & _).
    assert (Qs12 : getr R2 9%bv = Z_to_bv 64 (w_p w + 240)) by (destruct LR2 as (_ & _ & _ & _ & Q & _); exact Q).
    pm_seed R2 w c1 [Z_to_bv 64 (PrsNeeds.sx32 r1); Z_to_bv 64 (t3a (c_v2 c)); Z_to_bv 64 (w_p w + 240)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (9%bv, EVar 41)] R2. seedHK HK w A M1 model c1 E X1.
    apply (know_more E M1 [KWord (SA (EVar 33) 240) (N.to_nat 8) (EVar 40)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [eapply fld_cellw; [unfold O_V2 in V2f0; exact V2f0 | cbn; destruct V2blk as [[Hb0 Hc0]|(Hb1 & ? & ? & Hb2 & ?)]; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof (syms_id_sound _ _ _ _ SREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs. pose proof (loop_regs_glue w R2 R3 LR2 GS G2 G3 G4 G8 (or_intror G9)) as LR3. clear GS G9. rewrite Qgp2 in G3. rewrite Qtp2 in G4.
    rewrite w_add in G11 by lia.
    rewrite (w2lb4_sx32 r1) by lia.
    assert (ST2 : stores_in (zwin (w_sp w + 220) (w_sp w + 224)) M1 (wbytes M1 (Z_to_bv 64 (w_sp w + 220)) (word_to_le_bytes 4 (Z_to_bv 64 r1)))) by stin.
    assert (X2a : PMX w A (wbytes M1 (Z_to_bv 64 (w_sp w + 220)) (word_to_le_bytes 4 (Z_to_bv 64 r1))) model c1).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M1 _ model c1 (zwin (w_sp w + 220) (w_sp w + 224)));
        [exact X1 | exact ST2 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (loop_mem_frame w M1) in LM; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
    eapply (izero_agree w M1) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]]. clear ST2.
    pose proof (pm_v2_clear w A _ model c1 (t3a (c_v2 c)) X2a eq_refl) as X2. clear X2a X1 MS1.
    set (c2 := set_v2 c1 (t3a (c_v2 c), [], t3c (c_v2 c1))) in X2.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M2 := m) in * end.
    assert (ST3 : stores_in (zwin (w_p w + 248) (w_p w + 256)) (wbytes M1 (Z_to_bv 64 (w_sp w + 220)) (word_to_le_bytes 4 (Z_to_bv 64 r1))) M2) by (unfold M2; stin).
    eapply (loop_mem_frame w _ M2) in LM; [| lia | lia | eapply stores_in_agree; [exact ST3 | unfold zwin; intros; lia]].
    eapply (izero_agree w _ M2) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST3 | unfold zwin; intros; lia]]. clear ST3.
    pose proof (x_ms X2) as MS2.
    eapply (pm_ecw_pb (kv_ecw_pb ccS1) (cl_ecw_pb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) eq_refl w c0 K fx A M2 model c2 R3 (w_sp w + 220) r1 _ PS X2 Htr);
      [exact BUD | cregs_tac G1 G2 G3 G4 | unfold O_V2; exact G10 | exact G11 | unfold M2; rdback | lia | lia | unfold w_sp0, PM_FRAME; lia
      | cbn [c2 c1 c_v2 set_v2 set_scal t3b t3c fst snd]; intros H0; unfold vgrow, Zlen in H0 |- *; cbn in H0; lia |].
    intros A3 R4 M3 model3 b2' cap2' X3 BUD3 KEPT AG.
    pose proof (loop_regs_kept w R3 R4 LR3 KEPT) as LR4.
    keptQ KEPT G2 Qsp4. keptQ KEPT G8 Qs04. keptQ KEPT G3 Qgp4. keptQ KEPT G4 Qtp4. clear G1 G2 G3 G4 G8 G10 G11 KEPT LR3 Qsp2 Qs02 Qgp2 Qtp2 Qs12.
    eapply (loop_mem_frame w M2) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
    eapply (izero_agree w M2) in IZ; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
    assert (Cfw1 : cellw SEGS M3 (w_sp w + 220) 4 r1).
    { eapply (cellw_frame M2 M3); [split; [cbn; lia | unfold M2; change (N.to_nat 4) with 4%nat; rdback] | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]]. }
    clear AG X2 MS2 V2f0 V2len V2blk. clearbody M2. clear M2 M1. pose proof (x_ms X3) as MS3.
    cbn [c2 c1 set_v2 set_scal c_v2 t3b fst snd app] in X3, BUD3.
    set (c3 := set_v2 c2 (b2', [r1], cap2')) in *.

    pose proof (x_v1 X3) as V1. cbn [c3 c2 c1 c_v1 c_v2 set_v2 set_scal t3a t3b t3c fst snd] in V1. destruct V1 as (_ & _ & _ & V1len & V1blk & V1f0 & _).
    assert (Qs34 : getr R4 19%bv = Z_to_bv 64 (w_sp w + 234)) by (destruct LR4 as (_ & _ & _ & _ & _ & _ & Q & _); exact Q).
    pm_seed R4 w c3 [Z_to_bv 64 (t3a (c_v1 c)); Z_to_bv 64 r1; Z_to_bv 64 (w_sp w + 234)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R4. seedHK HK w A3 M3 model3 c3 E X3.
    apply (know_more E M3 [KWord (SA (EVar 33) 216) (N.to_nat 8) (EVar 39); KWord (SA (EVar 32) 220) (N.to_nat 4) (EVar 40)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [unfold O_V1 in V1f0; exact V1f0 | cbn; destruct V1blk as [[Hb0 Hc0]|(Hb1 & ? & ? & Hb2 & ?)]; unfold OPND_SZ in *; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cfw1 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }

    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }

    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    pose proof (syms_id_sound _ _ _ _ SREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs. pose proof (loop_regs_glue w R4 R5 LR4 GS G2 G3 G4 G8 (or_introl G9)) as LR5. clear GS G9.
    rewrite Qgp4 in G3. rewrite Qtp4 in G4.
    replace (Z_to_bv 5 (Z.of_N 19)) with (19%bv : reg) in G12 by (apply bv_eq; reflexivity). rewrite Qs34 in G12.
    rewrite ext_val_sx4 in G10 by lia. rewrite w_add in G11 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M4 := m) in * end.
    assert (ST4 : stores_in (fun a => zwin (w_p w + 224) (w_p w + 232) a \/ zwin (w_sp w + 218) (w_sp w + 220) a) M3 M4) by (unfold M4; stin).
    pose proof (pm_v1_clear w A3 M3 model3 c3 (t3a (c_v1 c)) X3 eq_refl) as X4a.
    assert (X4 : PMX w A3 M4 model3 (set_v1 c3 (t3a (c_v1 c), 0, t3c (c_v1 c3)))).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A3 _ _ model3 _ (zwin (w_sp w + 218) (w_sp w + 220)));
        [exact X4a | unfold M4; stin | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (loop_mem_frame w M3 M4) in LM; [| lia | lia | eapply stores_in_agree; [exact ST4 | unfold zwin; intros; lia]].
    eapply (izero_agree w M3 M4) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST4 | unfold zwin; intros; lia]].
    assert (Cfw4 : cellw SEGS M4 (w_sp w + 220) 4 r1).
    { eapply (cellw_frame M3 M4); [exact Cfw1 | lia | cbn; lia | eapply stores_in_agree; [exact ST4 | unfold zwin; cbn; intros; lia]]. }
    clear ST4 X4a X3 MS3 Cfw1 V1f0 V1len V1blk. clearbody M4. pose proof (x_ms X4) as MS4.
    set (c4 := set_v1 c3 (t3a (c_v1 c), 0, t3c (c_v1 c3))) in *.

    eapply (pm_opcode_split w A3 M4 model3 c4 fx R5 r1 (w_sp w + 218) (w_sp w + 234) _ K X4 G10 G11 G12);
      [lia | lia | unfold w_sp0, PM_FRAME; lia | lia | unfold w_sp0, PM_FRAME; lia
      | apply mod16_2; [exact Gsp16 | reflexivity] | apply mod16_2; [exact Gsp16 | reflexivity] | exact G1 | apply bv_eq; vm_compute; reflexivity |].
    intros R6 KEPT M5 X5.
    pose proof (loop_regs_kept w R5 R6 LR5 KEPT) as LR6.
    keptQ KEPT G2 Qsp6. keptQ KEPT G8 Qs06. keptQ KEPT G3 Qgp6. keptQ KEPT G4 Qtp6. clear G1 G2 G3 G4 G8 G10 G11 G12 KEPT LR5 LR4 Qsp4 Qs04 Qgp4 Qtp4 Qs34.
    assert (ST5 : stores_in (fun a => zwin (w_sp w + 218) (w_sp w + 220) a \/ zwin (w_sp w + 234) (w_sp w + 236) a) M4 M5) by (unfold M5; stin).
    eapply (loop_mem_frame w M4 M5) in LM; [| lia | lia | eapply stores_in_agree; [exact ST5 | unfold zwin; intros; lia]].
    eapply (izero_agree w M4 M5) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST5 | unfold zwin; intros; lia]].
    eapply (cellw_frame M4 M5) in Cfw4; [| lia | cbn; lia | eapply stores_in_agree; [exact ST5 | unfold zwin; cbn; intros; lia]].
    pose proof (hi16_range r1 Rr1) as Riwc. pose proof (lo16_range r1) as Rop.
    set (iwc := r1 / 2 ^ 16) in *. set (op := r1 mod 2 ^ 16) in *.
    assert (Ciwc : cellw SEGS M5 (w_sp w + 218) 2 iwc) by (split; [cbn; lia | unfold M5; rdback]).
    assert (Cop : cellw SEGS M5 (w_sp w + 234) 2 op) by (split; [cbn; lia | unfold M5; rdback]).
    clear ST5. clearbody M5. clear X4 MS4 M4. pose proof (x_ms X5) as MS5.
    assert (Hic : c_icount c4 < 2 ^ 62) by (cbn [c4 c3 c2 c1 set_v1 set_v2 set_scal c_icount]; lia).

    destruct (Z.eq_dec iwc 0) as [Hz0|Hnz].
    { pm_seed R6 w c4 (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6. seedHK HK w A3 M5 model3 c4 E X5.
      apply (know_more E M5 [KWord (SA (EVar 32) 218) (N.to_nat 2) (ELit 0)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           eapply kword_var; [rewrite Hz0 in Ciwc; exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
      xruns HR HK 100%nat (0x66d54 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R7. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
      clear HRn HR HK. fixregs. rewrite Qgp6 in G3. rewrite Qtp6 in G4.
      eapply (pm_D5 w c0 K fx A3 M5 model3 c4 R7 iwc PS X5 Htr BUD3 LM Ciwc Hic FZ G8 G2 G3 G4). }

    pm_seed R6 w c4 [Z_to_bv 64 iwc; Z_to_bv 64 op].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6. seedHK HK w A3 M5 model3 c4 E X5.
    apply (know_more E M5 [KWord (SA (EVar 32) 218) (N.to_nat 2) (EVar 39); KWord (SA (EVar 32) 234) (N.to_nat 2) (EVar 40); KRange (EVar 39) 1 (2 ^ 16)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cop | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }

    xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N. { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ext_val_zx2 by lia; rewrite br_eq by lia; bool_lia. }

    postrun. name_run HRn R7.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof (syms_id_sound _ _ _ _ SREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs. pose proof (loop_regs_glue w R6 R7 LR6 GS G2 G3 G4 G8 (or_introl G9)) as LR7. clear GS G9.
    rewrite Qgp6 in G3. rewrite Qtp6 in G4. rewrite ext_val_zx2 in G10 by lia. rewrite w_add in G11 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M6 := m) in * end.
    assert (ST6 : stores_in (zwin (w_sp w + 208) (w_sp w + 216)) M5 M6) by (unfold M6; stin).
    assert (X6 : PMX w A3 M6 model3 c4).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A3 M5 M6 model3 c4 (zwin (w_sp w + 208) (w_sp w + 216)));
        [exact X5 | exact ST6 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (loop_mem_frame w M5 M6) in LM; [| lia | lia | eapply stores_in_agree; [exact ST6 | unfold zwin; intros; lia]].
    eapply (izero_agree w M5 M6) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST6 | unfold zwin; intros; lia]].
    eapply (cellw_frame M5 M6) in Cfw4; [| lia | cbn; lia | eapply stores_in_agree; [exact ST6 | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame M5 M6) in Ciwc; [| lia | cbn; lia | eapply stores_in_agree; [exact ST6 | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame M5 M6) in Cop; [| lia | cbn; lia | eapply stores_in_agree; [exact ST6 | unfold zwin; cbn; intros; lia]].
    clear ST6 X5 MS5. clearbody M6. clear M5. pose proof (x_ms X6) as MS6.

    eapply (pm_lookup_opcode w A3 M6 model3 c4 fx R7 op 0 (w_sp w + 208) _ K X6 G10);
      [lia | intros _; exact G11 | intros Hn; discriminate Hn | exact G2 | lia | unfold w_sp0, PM_FRAME; lia
      | apply mod16_8; [exact Gsp16 | reflexivity] | exact G1 | apply bv_eq; vm_compute; reflexivity |].
    intros R8 M7 r d KEPT Hr Rr Fd Hfound Hdesc X7 AG.
    pose proof (loop_regs_kept w R7 R8 LR7 KEPT) as LR8.
    keptQ KEPT G2 Qsp8. keptQ KEPT G8 Qs08. keptQ KEPT G3 Qgp8. keptQ KEPT G4 Qtp8. clear G1 G2 G3 G4 G8 G10 G11 KEPT LR7 LR6 Qsp6 Qs06 Qgp6 Qtp6.
    eapply (loop_mem_frame w M6 M7) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
    eapply (izero_agree w M6 M7) in IZ; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
    eapply (cellw_frame M6 M7) in Cfw4; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    eapply (cellw_frame M6 M7) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    eapply (cellw_frame M6 M7) in Cop; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    clear AG X6 MS6 M6. pose proof (x_ms X7) as MS7.

    destruct (Z.eq_dec r 0) as [Hr0|Hrn].
    2: { pm_seed R8 w c4 [Z_to_bv 64 r].
         seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R8. seedHK HK w A3 M7 model3 c4 E X7.
         apply (know_more E M7 [KWord (SA (EVar 33) 40) (N.to_nat 1) (ELit 0); KRange (EVar 39) 1 (2 ^ 64 - 1)]) in HK.
         2: { repeat apply Forall_cons; try apply Forall_nil.
              - eapply kword_var; [eapply fld_cellw; [exact (x_hunk X7) | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity].
              - eapply krange_var; [evs; reflexivity | lia | lia]. }

         xruns HR HK 100%nat (0x66dc4 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
         postrun. name_run HRn R9. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
         clear HRn HR HK. fixregs. rewrite Qgp8 in G3. rewrite Qtp8 in G4.
         eapply (pm_D6 w c0 K fx A3 M7 model3 c4 R9 op PS X7 Htr BUD3 Cop Hic FZ G8 G2 G3 G4). }

    rewrite Hr0 in Hr.
    pose proof (fld_cellw M7 _ 8 _ (x_widx X7) ltac:(cbn [c4 c3 c2 c1 set_v1 set_v2 set_scal c_widx]; lia)) as Cwi. unfold O_WIDX in Cwi.
    pm_seed R8 w c4 (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0)] R8. seedHK HK w A3 M7 model3 c4 E X7.
    apply (know_more E M7 [KWord (SA (EVar 33) 72) (N.to_nat 8) (EVar 38)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [exact Cwi | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }

    xruns HR HK 100%nat (0x66e4c :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }

    postrun. name_run HRn R9.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    pose proof (syms_id_sound _ _ _ _ SREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs. pose proof (loop_regs_glue w R8 R9 LR8 GS G2 G3 G4 G8 (or_introl G9)) as LR9. clear GS G9.
    rewrite w_add by (cbn [c4 c3 c2 c1 set_v1 set_v2 set_scal c_widx]; lia).
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M8 := m) in * end.
    assert (ST8 : stores_in (fun a => zwin (w_sp w + 160) (w_sp w + 208) a \/ zwin (w_p w + 72) (w_p w + 80) a) M7 M8) by (unfold M8; stin).
    set (c8 := set_scal c4 (c_widx c + 1) (c_icount c4) (c_endian c4) (c_reqconv c4)).
    pose proof (x_scal X7) as (Sc1' & Sc2' & Sc3' & Sc4'). cbn [c4 c3 c2 c1 set_v1 set_v2 set_scal c_widx c_icount c_endian c_reqconv] in Sc1', Sc2', Sc3', Sc4'.
    assert (X8 : PMX w A3 M8 model3 c8).
    { eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img);
        [exact X7 | exact ST8 | intros a [Ha|Ha]; unfold scal_win, zwin, O_WIDX, O_FLAGS, w_sp0, PM_FRAME in *; [left; lia | right; lia]
        | unfold M8, O_WIDX; rdback
        | eapply fld_keep; [exact ST8 | exact (x_icount X7) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | unfold O_ICOUNT, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST8 | exact (x_endian X7) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST8 | exact (x_flags X7) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | unfold O_FLAGS, zwin; cbn; intros; lia]
        | cbn [c4 c3 c2 c1 set_v1 set_v2 set_scal c_widx]; lia | cbn [c4 c3 c2 c1 set_v1 set_v2 set_scal c_widx c_icount]; lia
        | cbn [c4 c3 c2 c1 set_v1 set_v2 set_scal c_endian]; lia | cbn [c4 c3 c2 c1 set_v1 set_v2 set_scal c_reqconv]; exact Sc4]. }
    eapply (loop_mem_frame w M7 M8) in LM; [| lia | lia | eapply stores_in_agree; [exact ST8 | unfold zwin; intros; lia]].
    eapply (izero_agree w M7 M8) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST8 | unfold zwin; intros; lia]].
    eapply (cellw_frame M7 M8) in Cfw4; [| lia | cbn; lia | eapply stores_in_agree; [exact ST8 | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame M7 M8) in Ciwc; [| lia | cbn; lia | eapply stores_in_agree; [exact ST8 | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame M7 M8) in Cop; [| lia | cbn; lia | eapply stores_in_agree; [exact ST8 | unfold zwin; cbn; intros; lia]].
    assert (Fd8 : fld SEGS M8 (w_sp w + 208) 8 d).
    { eapply fld_keep; [exact ST8 | exact Fd | lia | cbn; lia | unfold zwin; cbn; intros; lia]. }
    assert (Cio : cellw SEGS M8 (w_sp w + 200) 8 (c_widx c)) by (split; [cbn; lia | unfold M8; rdback]).

    eapply (B2K A3 M8 model3 c8 R9 r1 iwc op d X8 Htr BUD3 LR9 LM IZ);
      [split; [exact Cio | split; [exact Cfw4 | split; [exact Ciwc | split; [exact Cop | exact Fd8]]]]
      | reflexivity | reflexivity | exact Hnz | exact Rr1 | apply (proj1 Hfound); exact Hr0 | exact (Hdesc Hr0)
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
  Qed.
End PM.
