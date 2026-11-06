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
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2S1 PmLoopS1 PmBody1S1 PmStep3S1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
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
  #[local] Notation pm_idesc_operands := (PmStep3S1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3S1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3S1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3S1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3S1.pm_take_first CL).

  #[local] Notation izero := (PmBody1S1.izero).
  #[local] Notation ictx := (PmBody1S1.ictx).
  #[local] Notation GOK := (cl_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MAXLEN := (cl_maxlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma fld_mod64 : forall M a d, fld SEGS M a 8 d -> fld SEGS M a 8 (d mod 2 ^ 64).
  Proof using. intros M a d F. unfold CRep.fld in *. rewrite <- (LibMaskBits.Z_to_bv_mod64 d). exact F. Qed.

  Lemma op_list_range : forall op l, g_op G op = Some l -> Forall (fun t => 0 <= t < 2 ^ 31) l.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros op l Hg. apply Forall_forall. intros t Ht. eapply (go_range G GOK l t); [left; exists op; exact Hg | exact Ht].
  Qed.

  Lemma pm_B2 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (io fw iwc op d : Z) (l : list Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> loop_regs w R -> loop_mem w M -> izero w M ->
    ictx w M io fw iwc op d -> g_op G op = Some l -> idesc d op ->
    (forall A' M' model' R' (b' cap' : Z),
        PMX w A' M' model' (set_v3 c (b', push_types l [], cap')) -> pm_bud (w_n w) (set_v3 c (b', push_types l [], cap')) ->
        loop_regs w R' -> loop_mem w M' -> izero w M' -> ictx w M' io fw iwc op d ->
        srealizes SEGS (cfg fx R' 0x66e94 M' model') K) ->
    srealizes SEGS (cfg fx R 0x66e4c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R io fw iwc op d l PS X Htr BUD LR LM IZ IC Hg Hdesc HEADK.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof LR as LR'. destruct LR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs6 & Qs8).
    pose proof IC as IC'. destruct IC' as (Cio & Cfw & Ciwc & Cop & Fd).
    pose proof (x_v3 X) as V3. destruct V3 as (_ & _ & _ & V3len & V3blk & V3f0 & _).
    pose proof (Z.mod_pos_bound d (2 ^ 64) ltac:(lia)) as Hdm.

    pm_seed R w c [Z_to_bv 64 (t3a (c_v3 c)); Z_to_bv 64 (d mod 2 ^ 64)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 33) 264) (N.to_nat 8) (EVar 39); KWord (SA (EVar 32) 208) (N.to_nat 8) (EVar 40)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [unfold O_V3 in V3f0; exact V3f0 | cbn; destruct V3blk as [[Hb0 Hc0]|(Hb1 & ? & ? & Hb2 & ?)]; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [eapply fld_cellw; [apply fld_mod64; exact Fd | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10.
    pose proof (syms_id_sound _ _ _ _ PmBody1S1.SREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs. pose proof (PmBody1S1.loop_regs_glue w R R1 LR GS G2 G3 G4 G8 (or_introl G9)) as LR1. clear GS G9.
    rewrite Qgp in G3. rewrite Qtp in G4. rewrite <- (LibMaskBits.Z_to_bv_mod64 d) in G10.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_p w + 272) (w_p w + 280)) M M1) by (unfold M1; stin).
    pose proof (pm_v3_clear w A M model c (t3a (c_v3 c)) X eq_refl) as X1. change (PMX w A M1 model (set_v3 c (t3a (c_v3 c), [], t3c (c_v3 c)))) in X1.
    set (c1 := set_v3 c (t3a (c_v3 c), [], t3c (c_v3 c))) in *.
    eapply (PmBody1S1.loop_mem_frame w M M1) in LM; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
    eapply (PmBody1S1.izero_agree w M M1) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
    eapply (PmBody1S1.ictx_agree w M M1) in IC; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
    clear ST1 X MS. clearbody M1. pose proof (x_ms X1) as MS1.

    eapply (pm_idesc_operands w A M1 model c1 fx R1 _ K X1 (ex_intro _ d (ex_intro _ op (conj Hdesc G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 KEPT POST. destruct (POST d op Hdesc G10) as (p & l' & Hg' & RS & Hp4 & Qa0 & Qa1).
    rewrite Hg in Hg'. injection Hg'. intros El. subst l'.
    keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2. clear G1 G2 G3 G4 G8 G10.
    pose proof (PmBody1S1.loop_regs_kept w R1 R2 LR1 KEPT) as LR2. clear LR1 KEPT POST.
    assert (Qs42 : getr R2 20%bv = Z_to_bv 64 (w_p w + 264)) by (destruct LR2 as (_ & _ & _ & _ & _ & _ & _ & Q & _); exact Q).
    pose proof RS as RS'. destruct RS' as (Rp0 & Rp1 & _).
    pose proof (go_len_op G GOK op l Hg) as Hll. unfold HRep.Zlength in Hll. change (Zlen l <= g_maxlen G) in Hll. pose proof MAXLEN as Hml. assert (Hl0 : 0 <= Zlen l) by (unfold Zlen; lia).

    pm_seed R2 w c1 [Z_to_bv 64 p; Z_to_bv 64 (Zlen l)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (11%bv, EVar 40)] R2. seedHK HK w A M1 model c1 E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof (syms_id_sound _ _ _ _ PmBody1S1.SREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs. pose proof (PmBody1S1.loop_regs_glue w R2 R3 LR2 GS G2 G3 G4 G8 (or_introl G9)) as LR3. clear GS G9.
    rewrite Qgp2 in G3. rewrite Qtp2 in G4. rewrite w_add in G10 by lia.
    replace (Z_to_bv 5 (Z.of_N 20)) with (20%bv : reg) in G11 by (apply bv_eq; reflexivity). rewrite Qs42 in G11.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M2 := m) in * end.
    assert (ST2 : stores_in (zwin (w_sp w + 272) (w_sp w + 288)) M1 M2) by (unfold M2; stin).
    assert (X2 : PMX w A M2 model c1).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M1 M2 model c1 (zwin (w_sp w + 272) (w_sp w + 288)));
        [exact X1 | exact ST2 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (PmBody1S1.loop_mem_frame w M1 M2) in LM; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
    eapply (PmBody1S1.izero_agree w M1 M2) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
    eapply (PmBody1S1.ictx_agree w M1 M2) in IC; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
    assert (Fp : fld SEGS M2 (w_sp w + 272) 8 p) by (unfold M2; rdback).
    assert (Fl : fld SEGS M2 (w_sp w + 272 + 8) 8 (Zlen l)) by (unfold M2; replace (w_sp w + 272 + 8) with (w_sp w + 280) by lia; rdback).
    clear ST2 X1 MS1. clearbody M2. clear M1. pose proof (x_ms X2) as MS2.
    eapply (pm_push_types w c0 K fx A M2 model c1 R3 (w_sp w + 272) p _ l PS X2 Htr BUD ltac:(cregs_tac G1 G2 G3 G4) G10);
      [unfold O_V3; exact G11 | exact Fp | exact Fl | exact RS | exact Hp4 | lia | exact (op_list_range op l Hg)
      | lia | unfold w_sp0, PM_FRAME; lia | cbn [c1 set_v3 c_v3 t3b fst snd]; unfold V3MAX, Zlen in *; cbn [length Z.of_nat]; lia |].
    intros A3 R4 M3 model3 b' cap' X3 BUD3 KEPT AG.
    pose proof (PmBody1S1.loop_regs_kept w R3 R4 LR3 KEPT) as LR4.
    keptQ KEPT G2 Qsp4. keptQ KEPT G8 Qs04. keptQ KEPT G3 Qgp4. keptQ KEPT G4 Qtp4. clear G1 G2 G3 G4 G8 G10 G11 KEPT LR3 LR2 Qsp2 Qs02 Qgp2 Qtp2 Qs42.
    eapply (PmBody1S1.loop_mem_frame w M2 M3) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
    eapply (PmBody1S1.izero_agree w M2 M3) in IZ; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
    eapply (PmBody1S1.ictx_agree w M2 M3) in IC; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    clear AG X2 MS2 M2 Fp Fl. pose proof (x_ms X3) as MS3.
    set (c3 := set_v3 c1 (b', push_types l [], cap')) in *.

    pm_seed R4 w c3 (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R4. seedHK HK w A3 M3 model3 c3 E X3.

    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    pose proof (syms_id_sound _ _ _ _ PmBody1S1.SREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs. pose proof (PmBody1S1.loop_regs_glue w R4 R5 LR4 GS G2 G3 G4 G8 (or_introl G9)) as LR5. clear GS G9.
    eapply (HEADK A3 M3 model3 R5 b' cap' X3 BUD3 LR5 LM IZ IC).
  Qed.
End PM.
