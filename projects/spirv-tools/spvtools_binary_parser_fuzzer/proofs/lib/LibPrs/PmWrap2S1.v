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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts3 S1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HCommon HLib HConstsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBase PmHyps PmCoreS1 PmStepS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2S1 PmLoopS1 PmBody1S1 PmStep3S1 PmODefsS1 PmBody2S1 PmZw PmOLoopS1 PmStep4S1 PmStep5S1 PmExitDiagS1 PmOHeadS1 PmExitS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.PmHdrDiagS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.PmHdrS1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmDispatchS1 PmArm_RidS1 PmArm_StrLibS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.S1_code_69b20_69b24. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.S1_code_69b5c_69b60. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmWrapS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmWrapS1.S1_code_66400_66404. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmSetNumS1 PmArm_TylS1 PmArm_StrS1 PmBodyS1 PmArm_MaskS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.PmArm_IdS1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmArm_SpecS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.PmArm_ExtS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.PmArm_LitS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.PmArm_TyScDfS1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmArm_EnumS1 PmWrapS1.
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
  #[local] Notation pm_X1 := (PmOLoopS1.pm_X1 CL).
  #[local] Notation pm_opnd_pb := (PmOLoopS1.pm_opnd_pb CL).
  #[local] Notation pm_copy_loop := (PmOLoopS1.pm_copy_loop CL).
  #[local] Notation pm_push_tail := (PmOLoopS1.pm_push_tail CL).
  #[local] Notation pm_v3_pb := (PmStep4S1.pm_v3_pb CL).
  #[local] Notation pm_oty_pb := (PmStep4S1.pm_oty_pb CL).
  #[local] Notation pm_find_m1 := (PmStep4S1.pm_find_m1 CL).
  #[local] Notation pm_find_m3 := (PmStep4S1.pm_find_m3 CL).
  #[local] Notation pm_spec_lookup := (PmStep4S1.pm_spec_lookup CL).
  #[local] Notation pm_B2 := (PmBody2S1.pm_B2 CL).
  #[local] Notation pm_B1 := (PmBody1S1.pm_B1 CL).
  #[local] Notation pm_h5 := (PmStep5S1.pm_h5 CL).
  #[local] Notation pm_D7 := (PmExitDiagS1.pm_D7 CL).
  #[local] Notation pm_D8 := (PmExitDiagS1.pm_D8 CL).
  #[local] Notation pm_D9 := (PmExitDiagS1.pm_D9 CL).
  #[local] Notation pm_oloop := (PmOHeadS1.pm_oloop CL).
  #[local] Notation pm_xexit := (PmExitS1.pm_xexit CL).
  #[local] Notation pm_main := (PmLoopS1.pm_main CL).
  #[local] Notation pm_loop := (PmLoopS1.pm_loop CL).
  #[local] Notation pmx_room_ms := (PmArm_StrLibS1.pmx_room_ms CL).
  #[local] Notation pm_makestring := (PmArm_StrLibS1.pm_makestring CL).
  #[local] Notation pm_del_tr := (PmArm_StrLibS1.pm_del_tr CL).
  #[local] Notation pm_import := (PmArm_StrLibS1.pm_import CL).
  #[local] Notation pm_put_string := (PmArm_StrLibS1.pm_put_string CL).
  #[local] Notation pm_emplace_m3 := (PmArm_StrLibS1.pm_emplace_m3 CL).
  #[local] Notation ls_pdiag0x := (PmArm_StrLibS1.ls_pdiag0x CL).
  #[local] Notation ls_put_cstrx := (PmArm_StrLibS1.ls_put_cstrx CL).
  #[local] Notation ls_sdtor := (PmArm_StrLibS1.ls_sdtor CL).
  #[local] Notation ls_etail := (PmArm_StrLibS1.ls_etail CL).
  #[local] Notation ls_exh := (PmArm_StrLibS1.ls_exh CL).
  #[local] Notation ls_toolong := (PmArm_StrLibS1.ls_toolong CL).
  #[local] Notation ls_badimport := (PmArm_StrLibS1.ls_badimport CL).
  #[local] Notation pm_ctor_at := (PmSetNumS1.pm_ctor_at CL).
  #[local] Notation pm_put_cstr_at := (PmSetNumS1.pm_put_cstr_at CL).
  #[local] Notation pm_put_num_at := (PmSetNumS1.pm_put_num_at CL).
  #[local] Notation pm_put_u32_at := (PmSetNumS1.pm_put_u32_at CL).
  #[local] Notation pm_dtor_at := (PmSetNumS1.pm_dtor_at CL).
  #[local] Notation pm_nt_find := (PmSetNumS1.pm_nt_find CL).
  #[local] Notation sn_tail := (PmSetNumS1.sn_tail CL).
  #[local] Notation sn_diag := (PmSetNumS1.sn_diag CL).
  #[local] Notation pm_set_numeric := (PmSetNumS1.pm_set_numeric CL).

  Variable PO : @PmWrapS1.po_callees AC MI ST.
  #[local] Notation po_tail := (PmWrapS1.po_tail CL PO).
  #[local] Notation ws_new := (PmWrapS1.ws_new CL).

  #[local] Ltac cellq := lazymatch goal with
    | |- cellw ?S ?M (?b + ?k) ?w ?v =>
        let k' := eval vm_compute in k in
        match goal with H : cellw S M (b + k') w v |- _ => exact H end
    | |- vtrip ?b ?k ?p ?sz ?M =>
        let k' := eval vm_compute in k in
        match goal with H : vtrip b k' p sz M |- _ => exact H end
    end.

  Lemma po_core : forall (fx : FPState) A (s : LibIface.SX ST) R M model (sp ret ctx env words n : Z) (K : TSet),
    callB MI ST A s R M model sp ret 17072 -> ro_clear Ly.L M -> frm_zero (@fp_csr fx) ->
    getr R 10%bv = Z_to_bv 64 ctx -> getr R 11%bv = Z_to_bv 64 0 -> getr R 12%bv = Z_to_bv 64 words ->
    getr R 13%bv = Z_to_bv 64 n -> getr R 14%bv = Z_to_bv 64 0 -> getr R 15%bv = Z_to_bv 64 0 ->
    getr R 16%bv = Z_to_bv 64 0 -> getr R 17%bv = Z_to_bv 64 0 ->
    CRep.ctx_rep MI A M ctx env -> (forall a, zwin ctx (ctx + CTX_SZ) a -> ~ zwin (sp - 17072) sp a) ->
    (words <> 0 -> words_ok (live MI A) sp M words n) ->
    (forall a, zwin words (words + 4 * n) a -> ~ zwin (sp - 17072) sp a) ->
    pm_budget SEGS Ly.L MI A n ->
    (forall (fx' : FPState) A' R' M' model' (r : Z),
        retB MI ST A' s R R' M' model model' -> frm_zero (@fp_csr fx') ->
        getr R' 10%bv = Z_to_bv 64 r ->
        Permutation (live MI A') (live MI A) ->
        eff MI A A' M M' (sp - 17072, sp) (junk SEGS Ly.L MI A) ->
        srealizes SEGS (cfg fx' R' ret M' model') K) ->
    srealizes SEGS (cfg fx R 0x66100 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL PO.
    intros fx A s R M model sp ret ctx env words n K CB ROC FZ Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7 CTX CWIN WOK WWIN BUD POST.
    pose proof ac_bounds_lit as Hcv.
    assert (Rwords : 0 <= words < 2 ^ 64) by (destruct (Z.eq_dec words 0) as [->|Hw]; [lia | destruct (WOK Hw) as (W1 & W2 & W3 & W4 & _); lia]).
    destruct CB as [AI MS IRC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx]. destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    destruct CTX as (Cq0 & Cqal & Cq63 & CqIn & Cenv & Cf0). unfold CRep.fld in Cenv, Cf0.
    destruct (ai_live_block MI A M model ctx CTX_SZ AI CqIn) as (_ & _ & _ & Cqc & Cqpay). unfold CTX_SZ in *.
    pose proof BUD as BUD'. destruct BUD' as (Bcaps & Bbig & Bnmax & Bn & _).
    assert (HWD : mdef M (sp - 17072) 17072).
    { eapply store_ok_mdef_offimg; [exact HROOM | lia | lia | lia |]. intros x Hx. apply ly_noseg. lia. }
    set (w := {| v_sp0 := sp; v_ret := ret; v_ctx := ctx; v_env := env; v_words := words; v_n := n;
                 v_R0 := R; v_A0 := A; v_M0 := M; v_model0 := model; v_s := s |}).
    assert (Esp : v_sp w = sp - 672) by reflexivity. assert (Esp0 : v_sp0 w = sp) by reflexivity.

    pose (E := Eseed R [Z_to_bv 64 sp]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) (-17072)) (ELit 17072)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_stack; [evs; reflexivity | reflexivity | lia | lia | exact HROOM]. }
    xruns HR HK 100%nat (0x6612c :: WSTOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (2%bv) G2. pose proof (syms_id_sound _ _ _ _ [1; 3; 4; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS1.
    clear HRn HR HK. fixregsN. rewrite w_addm in G2 by lia. rewrite Hra.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M1 := mm) in * end.
    assert (ST1 : stores_in (zwin (sp - 80) sp) M M1) by (unfold M1; stin).
    assert (WS1 : WS w [] A M1 model).
    { subst w. constructor; cbn [v_sp0 v_ret v_ctx v_env v_words v_n v_R0 v_A0 v_M0 v_model0 v_s]; unfold PO_STK, PO_FRAME.
      - eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST1 | intros a Ha; eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | unfold zwin in Ha; lia]].
      - exact MS. - reflexivity. - reflexivity.
      - eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST1 |]. intros a Ha. split; [apply (proj2 (Hwin a ltac:(unfold zwin in *; lia))) | intros Hr; pose proof (ly_img_low _ (ly_relro_img _ Hr)); unfold zwin in Ha; lia].
      - exact SXH.
      - eapply (ro_clear_frame Ly.L); [exact ROC | eapply stores_in_frame_eq; [exact ST1 | intros a Ha; exact Ha] |]. intros a (Hi & _ & _) Hw. pose proof (ly_img_low _ Hi). unfold zwin in Hw. lia.
      - apply (eff_store MI A M M1 _ (junk SEGS Ly.L MI A)); [| exact (proj2 ST1)]. intros a HF HWn. apply (proj1 ST1). intros Hw. apply HWn. unfold W_of, zwin in *. cbn. lia.
      - exact Hown_sx. - exact Herr_sx.
      - intros a Ha. apply (proj2 (Hwin a Ha)).
      - split; reflexivity.
      - split; [exact Hsp16 | lia].
      - eapply stores_in_mdef; [exact ST1 | eapply mdef_sub; [exact HWD | lia | lia]].
      - eapply stores_in_mdef; [exact ST1 | eapply mdef_sub; [exact HWD | lia | lia]].
      - eapply stores_in_mdef; [exact ST1 | eapply mdef_sub; [exact HWD | lia | lia]].
      - intros k Hk. unfold PO_SLOTS.
        assert (Hk' : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
        destruct Hk' as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; cbn [Z.to_nat Z.sub nth Pos.to_nat Z.mul Pos.mul]; unfold M1; rdback.
      - rewrite app_nil_r. reflexivity. }
    assert (AGc : CRep.agree_on (zwin ctx (ctx + 64)) M M1) by (eapply stores_in_agree; [exact ST1 | intros a Ha; unfold zwin in *; lia]).
    assert (Cenv1 : rdn SEGS M1 (Z_to_bv 64 ctx) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 env))).
    { rewrite (rdn_agree_win SEGS M M1 ctx 4); [exact Cenv | lia | cbn; lia | eapply agree_on_weaken; [exact AGc | unfold zwin; cbn; intros; lia]]. }
    assert (Cf1 : cellw SEGS M1 (ctx + 48) 8 0).
    { split; [cbn; lia|]. change (N.to_nat 8) with 8%nat. rewrite (rdn_agree_win SEGS M M1 (ctx + 48) 8); [exact Cf0 | lia | cbn; lia | eapply agree_on_weaken; [exact AGc | unfold zwin; cbn; intros; lia]]. }
    clearbody M1. clear ST1 HWD HROOM IRC AGc.

    set (venv := Z_to_bv 64 (extz true 4 (lez (word_to_le_bytes 4 (Z_to_bv 64 env))))).
    pose (E2 := Eseed R1 [Z_to_bv 64 (sp - 672); Z_to_bv 64 ctx; Z_to_bv 64 words; Z_to_bv 64 n; venv]).
    assert (HR2 : regs_ok E2 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (11%bv, ELit 0); (12%bv, EVar 34); (13%bv, EVar 35); (14%bv, ELit 0); (15%bv, ELit 0); (16%bv, ELit 0); (17%bv, ELit 0)]) R1).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs;
        first [exact G2 | rewrite (GS1 _) by (clear; in_regs); assumption]. }
    assert (HK2 : know_ok SEGS E2 M1 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KRange (EVar 33) 1 (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 592);
                                     KWord (SA (EVar 33) 48) (N.to_nat 8) (ELit 0); KDisj (SA (EVar 33) 0) (ELit 64) (SA (EVar 32) 0) (ELit 672)]).
    { pose proof (s_fdef _ _ _ _ _ WS1) as FD1. rewrite Esp0 in FD1. unfold PO_FRAME in FD1.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD1 | lia | lia] | lia | lia | lia | lia].
      - eapply kword_var; [exact Cf1 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
      - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia]. }
    xruns HR2 HK2 100%nat WSTOPS (SCR [] [EVar 36] []) 60%N.
    { split_scs; try sc_auto1. all: cbn [sc_denot]; exists (word_to_le_bytes 4 (Z_to_bv 64 env)); split; [rewrite (adenot_Z E2 _ ctx); [cbn [a_off]; rewrite Z.add_0_r; exact Cenv1 | evs; reflexivity | lia] | evs; reflexivity]. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) H2. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10.
    rreg HRn (18%bv) G18. rreg HRn (19%bv) G19. rreg HRn (20%bv) G20. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23. rreg HRn (24%bv) G24.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 25; 26; 27]%bv HRn eq_refl) as GS2.
    clear HRn HR2 HK2. fixregsN. rewrite ?w_add in G8, G9 |- * by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M2 := mm) in * end.
    assert (ST2 : stores_in (zwin (sp - 672) (sp - 672 + 344)) M1 M2) by (unfold M2; stin).
    assert (WS2 : WS w [] A M2 model) by (eapply (ws_stores w [] A M1 M2 model _ WS1 ST2); rewrite Esp, Esp0; unfold zwin; intros; lia).
    assert (PI2 : pinit (sp - 672) M2).
    { unfold pinit. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M2; rdback]). }
    pose proof (s_ms _ _ _ _ _ WS2) as MS2. clearbody M2. clear ST2 WS1 Cenv1 Cf1.
    pose proof (cl_classes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HCL. pose proof (x_caps) as XC || idtac.
    assert (HNM : 500 <= NMAX MI) by (unfold LIB_NMAX in Bnmax; lia).

    eapply (ws_new w [] A M2 model fx R2 500 0x6621c K WS2); [split; [exact G1 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2 | split; [rewrite (GS2 3%bv) by (clear; in_regs); rewrite (GS1 3%bv) by (clear; in_regs); exact Hgp | rewrite (GS2 4%bv) by (clear; in_regs); rewrite (GS1 4%bv) by (clear; in_regs); exact Htp]]]]]
      | exact G10 | lia | eapply (roomL_room_for SEGS Ly.L MI); [exact (s_ai _ _ _ _ _ WS2) | lia | eapply (ws_room w [] A M2 model 500 WS2 BUD); [rewrite Zlength_nil; lia | lia]] | exact HNM |].
    intros A3 R3 M3 model3 p3 WS3 KEPT3 G10_3 Hp3a Hp3c Hp3al Hp3d Hp3f AG3 AH3. cbn [app] in WS3.
    assert (Qgp3 : getr R3 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT3 3%bv) by (clear; in_regs); rewrite (GS2 3%bv) by (clear; in_regs); rewrite (GS1 3%bv) by (clear; in_regs); exact Hgp).
    assert (Qtp3 : getr R3 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT3 4%bv) by (clear; in_regs); rewrite (GS2 4%bv) by (clear; in_regs); rewrite (GS1 4%bv) by (clear; in_regs); exact Htp).
    keptQ KEPT3 H2 H2_3.
    assert (PI3 : pinit (sp - 672) M3) by (eapply (pinit_agree _ M2 M3 PI2); [lia | lia | eapply agree_on_weaken; [exact AG3 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    clear AG3 PI2 MS2.

    pose (E3 := Eseed R3 [Z_to_bv 64 (sp - 672); Z_to_bv 64 p3]).
    assert (HR3 : regs_ok E3 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33)]) R3).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK3 : know_ok SEGS E3 M3 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 592)]).
    { pose proof (s_fdef _ _ _ _ _ WS3) as FD. rewrite Esp0 in FD. unfold PO_FRAME in FD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD | lia | lia] | lia | lia | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS3) as MS3.
    xruns HR3 HK3 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3'.
    rreg HRn (1%bv) G1_3. rreg HRn (2%bv) H2_3'. rreg HRn (10%bv) G10_3'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS3'.
    clear HRn HR3 HK3. fixregsN. rewrite ?w_add by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M3' := mm) in * end.
    assert (ST3 : stores_in (zwin (sp - 672 + 216) (sp - 672 + 240)) M3 M3') by (unfold M3'; stin).
    assert (WS3' : WS w [(p3, 500)] A3 M3' model3) by (eapply (ws_stores w _ A3 M3 M3' model3 _ WS3 ST3); rewrite Esp, Esp0; unfold zwin; intros; lia).
    assert (V3 : cell8 SEGS M3' (sp - 672 + 216) p3 /\ cell8 SEGS M3' (sp - 672 + 224) p3 /\ cell8 SEGS M3' (sp - 672 + 232) (p3 + 500)).
    { unfold cell8. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M3'; rdback]). }
    assert (AG3s : CRep.agree_on (fun a => sp - 672 <= a < sp /\ ~ zwin (sp - 672 + 216) (sp - 672 + 240) a) M3 M3') by (eapply stores_in_agree; [exact ST3 | intros b Hb; unfold zwin in *; lia]).
    assert (PI3' : pinit (sp - 672) M3') by (eapply (pinit_agree _ M3 M3' PI3); [lia | lia | eapply agree_on_weaken; [exact AG3s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (VT3 : vtrip (sp - 672) 216 p3 500 M3') by (unfold vtrip; replace (sp - 672 + 216 + 8) with (sp - 672 + 224) by lia; replace (sp - 672 + 216 + 16) with (sp - 672 + 232) by lia; exact V3).
    pose proof (s_ms _ _ _ _ _ WS3') as MS3'. clearbody M3'. clear ST3.
    eapply (ws_new w _ A3 M3' model3 fx R3' 100 0x66234 K WS3');
      [ split; [exact G1_3 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_3' | split; [rewrite (GS3' 3%bv) by (clear; in_regs); exact Qgp3 | rewrite (GS3' 4%bv) by (clear; in_regs); exact Qtp3]]]]]
      | exact G10_3' | lia
      | eapply (roomL_room_for SEGS Ly.L MI); [exact (s_ai _ _ _ _ _ WS3') | lia | eapply (ws_room w _ A3 M3' model3 100 WS3' BUD); [unfold Zlength; cbn; lia | lia]]
      | exact HNM |].
    intros A4 R4 M4 model4 p4 WS4 KEPT4 G10_4 Hp4a Hp4c Hp4al Hp4d Hp4f AG4 AH4. cbn [app] in WS4.
    assert (Qgp4 : getr R4 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT4 3%bv) by (clear; in_regs); rewrite (GS3' 3%bv) by (clear; in_regs); exact Qgp3).
    assert (Qtp4 : getr R4 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT4 4%bv) by (clear; in_regs); rewrite (GS3' 4%bv) by (clear; in_regs); exact Qtp3).
    keptQ KEPT4 H2_3' H2_4.
    assert (PI4 : pinit (sp - 672) M4) by (eapply (pinit_agree _ M3' M4 PI3'); [lia | lia | eapply agree_on_weaken; [exact AG4 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W3_4 : vtrip (sp - 672) 216 p3 500 M4) by (eapply (vtrip_agree _ _ _ _ M3' M4 VT3); [lia | lia | eapply agree_on_weaken; [exact AG4 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    clear AG3s AG4 PI3 PI3' VT3 V3 MS3'.

    pose (E4 := Eseed R4 [Z_to_bv 64 (sp - 672); Z_to_bv 64 p4]).
    assert (HR4 : regs_ok E4 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33)]) R4).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK4 : know_ok SEGS E4 M4 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 592)]).
    { pose proof (s_fdef _ _ _ _ _ WS4) as FD. rewrite Esp0 in FD. unfold PO_FRAME in FD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD | lia | lia] | lia | lia | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS4) as MS4.
    xruns HR4 HK4 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4'.
    rreg HRn (1%bv) G1_4. rreg HRn (2%bv) H2_4'. rreg HRn (10%bv) G10_4'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS4'.
    clear HRn HR4 HK4. fixregsN. rewrite ?w_add by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M4' := mm) in * end.
    assert (ST4 : stores_in (zwin (sp - 672 + 240) (sp - 672 + 264)) M4 M4') by (unfold M4'; stin).
    assert (WS4' : WS w [(p3, 500); (p4, 100)] A4 M4' model4) by (eapply (ws_stores w _ A4 M4 M4' model4 _ WS4 ST4); rewrite Esp, Esp0; unfold zwin; intros; lia).
    assert (V4 : cell8 SEGS M4' (sp - 672 + 240) p4 /\ cell8 SEGS M4' (sp - 672 + 248) p4 /\ cell8 SEGS M4' (sp - 672 + 256) (p4 + 100)).
    { unfold cell8. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M4'; rdback]). }
    assert (AG4s : CRep.agree_on (fun a => sp - 672 <= a < sp /\ ~ zwin (sp - 672 + 240) (sp - 672 + 264) a) M4 M4') by (eapply stores_in_agree; [exact ST4 | intros b Hb; unfold zwin in *; lia]).
    assert (PI4' : pinit (sp - 672) M4') by (eapply (pinit_agree _ M4 M4' PI4); [lia | lia | eapply agree_on_weaken; [exact AG4s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W3_4' : vtrip (sp - 672) 216 p3 500 M4') by (eapply (vtrip_agree _ _ _ _ M4 M4' W3_4); [lia | lia | eapply agree_on_weaken; [exact AG4s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (VT4 : vtrip (sp - 672) 240 p4 100 M4') by (unfold vtrip; replace (sp - 672 + 240 + 8) with (sp - 672 + 248) by lia; replace (sp - 672 + 240 + 16) with (sp - 672 + 256) by lia; exact V4).
    pose proof (s_ms _ _ _ _ _ WS4') as MS4'. clearbody M4'. clear ST4.
    eapply (ws_new w _ A4 M4' model4 fx R4' 100 0x6624c K WS4');
      [ split; [exact G1_4 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_4' | split; [rewrite (GS4' 3%bv) by (clear; in_regs); exact Qgp4 | rewrite (GS4' 4%bv) by (clear; in_regs); exact Qtp4]]]]]
      | exact G10_4' | lia
      | eapply (roomL_room_for SEGS Ly.L MI); [exact (s_ai _ _ _ _ _ WS4') | lia | eapply (ws_room w _ A4 M4' model4 100 WS4' BUD); [unfold Zlength; cbn; lia | lia]]
      | exact HNM |].
    intros A5 R5 M5 model5 p5 WS5 KEPT5 G10_5 Hp5a Hp5c Hp5al Hp5d Hp5f AG5 AH5. cbn [app] in WS5.
    assert (Qgp5 : getr R5 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT5 3%bv) by (clear; in_regs); rewrite (GS4' 3%bv) by (clear; in_regs); exact Qgp4).
    assert (Qtp5 : getr R5 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT5 4%bv) by (clear; in_regs); rewrite (GS4' 4%bv) by (clear; in_regs); exact Qtp4).
    keptQ KEPT5 H2_4' H2_5.
    assert (PI5 : pinit (sp - 672) M5) by (eapply (pinit_agree _ M4' M5 PI4'); [lia | lia | eapply agree_on_weaken; [exact AG5 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W3_5 : vtrip (sp - 672) 216 p3 500 M5) by (eapply (vtrip_agree _ _ _ _ M4' M5 W3_4'); [lia | lia | eapply agree_on_weaken; [exact AG5 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W4_5 : vtrip (sp - 672) 240 p4 100 M5) by (eapply (vtrip_agree _ _ _ _ M4' M5 VT4); [lia | lia | eapply agree_on_weaken; [exact AG5 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    clear AG4s AG5 PI4 PI4' VT4 V4 MS4' W3_4 W3_4'.
    assert (S18_5 : getr R5 18%bv = getr R2 18%bv) by (rewrite (KEPT5 18%bv) by (clear; in_regs); rewrite (GS4' 18%bv) by (clear; in_regs); rewrite (KEPT4 18%bv) by (clear; in_regs); rewrite (GS3' 18%bv) by (clear; in_regs); rewrite (KEPT3 18%bv) by (clear; in_regs); exact eq_refl).
    assert (S19_5 : getr R5 19%bv = getr R2 19%bv) by (rewrite (KEPT5 19%bv) by (clear; in_regs); rewrite (GS4' 19%bv) by (clear; in_regs); rewrite (KEPT4 19%bv) by (clear; in_regs); rewrite (GS3' 19%bv) by (clear; in_regs); rewrite (KEPT3 19%bv) by (clear; in_regs); exact eq_refl).
    assert (S20_5 : getr R5 20%bv = getr R2 20%bv) by (rewrite (KEPT5 20%bv) by (clear; in_regs); rewrite (GS4' 20%bv) by (clear; in_regs); rewrite (KEPT4 20%bv) by (clear; in_regs); rewrite (GS3' 20%bv) by (clear; in_regs); rewrite (KEPT3 20%bv) by (clear; in_regs); exact eq_refl).
    assert (S21_5 : getr R5 21%bv = getr R2 21%bv) by (rewrite (KEPT5 21%bv) by (clear; in_regs); rewrite (GS4' 21%bv) by (clear; in_regs); rewrite (KEPT4 21%bv) by (clear; in_regs); rewrite (GS3' 21%bv) by (clear; in_regs); rewrite (KEPT3 21%bv) by (clear; in_regs); exact eq_refl).
    assert (S24_5 : getr R5 24%bv = getr R2 24%bv) by (rewrite (KEPT5 24%bv) by (clear; in_regs); rewrite (GS4' 24%bv) by (clear; in_regs); rewrite (KEPT4 24%bv) by (clear; in_regs); rewrite (GS3' 24%bv) by (clear; in_regs); rewrite (KEPT3 24%bv) by (clear; in_regs); exact eq_refl).
    assert (S8_5 : getr R5 8%bv = getr R2 8%bv) by (rewrite (KEPT5 8%bv) by (clear; in_regs); rewrite (GS4' 8%bv) by (clear; in_regs); rewrite (KEPT4 8%bv) by (clear; in_regs); rewrite (GS3' 8%bv) by (clear; in_regs); rewrite (KEPT3 8%bv) by (clear; in_regs); exact eq_refl).
    assert (S9_5 : getr R5 9%bv = getr R2 9%bv) by (rewrite (KEPT5 9%bv) by (clear; in_regs); rewrite (GS4' 9%bv) by (clear; in_regs); rewrite (KEPT4 9%bv) by (clear; in_regs); rewrite (GS3' 9%bv) by (clear; in_regs); rewrite (KEPT3 9%bv) by (clear; in_regs); exact eq_refl).
    rewrite G18 in S18_5. rewrite G19 in S19_5. rewrite G20 in S20_5. rewrite G21 in S21_5. rewrite G24 in S24_5. rewrite G8 in S8_5. rewrite G9 in S9_5.

    pose (E5 := Eseed R5 [Z_to_bv 64 (sp - 672); Z_to_bv 64 p5; Z_to_bv 64 words; Z_to_bv 64 n]).
    assert (HR5 : regs_ok E5 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (18%bv, ELit 0); (19%bv, EVar 35); (20%bv, EVar 34); (21%bv, ELit 0); (24%bv, ELit 1065353216)]) R5).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK5 : know_ok SEGS E5 M5 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 592)]).
    { pose proof (s_fdef _ _ _ _ _ WS5) as FD. rewrite Esp0 in FD. unfold PO_FRAME in FD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD | lia | lia] | lia | lia | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS5) as MS5.
    xruns HR5 HK5 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5'.
    rreg HRn (1%bv) G1_5. rreg HRn (2%bv) H2_5'. rreg HRn (10%bv) G10_5'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 22; 23; 25; 26; 27]%bv HRn eq_refl) as GS5'.
    rreg HRn (18%bv) T18. rreg HRn (19%bv) T19. rreg HRn (20%bv) T20. rreg HRn (21%bv) T21. rreg HRn (24%bv) T24.
    clear HRn HR5 HK5. fixregsN. rewrite ?w_add by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M5' := mm) in * end.
    assert (ST5 : stores_in (fun a => zwin (sp - 672 + 264) (sp - 672 + 288) a \/ zwin (sp - 672 + 352) (sp - 672 + 592) a) M5 M5') by (unfold M5'; stin).
    assert (WS5' : WS w [(p3, 500); (p4, 100); (p5, 100)] A5 M5' model5) by (eapply (ws_stores w _ A5 M5 M5' model5 _ WS5 ST5); rewrite Esp, Esp0; unfold zwin; intros; lia).
    assert (V5 : cell8 SEGS M5' (sp - 672 + 264) p5 /\ cell8 SEGS M5' (sp - 672 + 272) p5 /\ cell8 SEGS M5' (sp - 672 + 280) (p5 + 100)).
    { unfold cell8. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M5'; rdback]). }
    assert (TI5 : tinit (sp - 672) words n M5').
    { unfold tinit. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M5'; rdback]). }
    assert (AG5s : CRep.agree_on (fun a => sp - 672 <= a < sp /\ ~ (zwin (sp - 672 + 264) (sp - 672 + 288) a \/ zwin (sp - 672 + 352) (sp - 672 + 592) a)) M5 M5') by (eapply stores_in_agree; [exact ST5 | intros b Hb; unfold zwin in *; lia]).
    assert (PI5' : pinit (sp - 672) M5') by (eapply (pinit_agree _ M5 M5' PI5); [lia | lia | eapply agree_on_weaken; [exact AG5s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W3_5' : vtrip (sp - 672) 216 p3 500 M5') by (eapply (vtrip_agree _ _ _ _ M5 M5' W3_5); [lia | lia | eapply agree_on_weaken; [exact AG5s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W4_5' : vtrip (sp - 672) 240 p4 100 M5') by (eapply (vtrip_agree _ _ _ _ M5 M5' W4_5); [lia | lia | eapply agree_on_weaken; [exact AG5s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (VT5 : vtrip (sp - 672) 264 p5 100 M5') by (unfold vtrip; replace (sp - 672 + 264 + 8) with (sp - 672 + 272) by lia; replace (sp - 672 + 264 + 16) with (sp - 672 + 280) by lia; exact V5).
    pose proof (s_ms _ _ _ _ _ WS5') as MS5'. clearbody M5'. clear ST5.
    eapply (ws_new w _ A5 M5' model5 fx R5' 500 0x662cc K WS5');
      [ split; [exact G1_5 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_5' | split; [rewrite (GS5' 3%bv) by (clear; in_regs); exact Qgp5 | rewrite (GS5' 4%bv) by (clear; in_regs); exact Qtp5]]]]]
      | exact G10_5' | lia
      | eapply (roomL_room_for SEGS Ly.L MI); [exact (s_ai _ _ _ _ _ WS5') | lia | eapply (ws_room w _ A5 M5' model5 500 WS5' BUD); [unfold Zlength; cbn; lia | lia]]
      | exact HNM |].
    intros A6 R6 M6 model6 p6 WS6 KEPT6 G10_6 Hp6a Hp6c Hp6al Hp6d Hp6f AG6 AH6. cbn [app] in WS6.
    assert (Qgp6 : getr R6 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT6 3%bv) by (clear; in_regs); rewrite (GS5' 3%bv) by (clear; in_regs); exact Qgp5).
    assert (Qtp6 : getr R6 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT6 4%bv) by (clear; in_regs); rewrite (GS5' 4%bv) by (clear; in_regs); exact Qtp5).
    keptQ KEPT6 H2_5' H2_6.
    assert (PI6 : pinit (sp - 672) M6) by (eapply (pinit_agree _ M5' M6 PI5'); [lia | lia | eapply agree_on_weaken; [exact AG6 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W3_6 : vtrip (sp - 672) 216 p3 500 M6) by (eapply (vtrip_agree _ _ _ _ M5' M6 W3_5'); [lia | lia | eapply agree_on_weaken; [exact AG6 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W4_6 : vtrip (sp - 672) 240 p4 100 M6) by (eapply (vtrip_agree _ _ _ _ M5' M6 W4_5'); [lia | lia | eapply agree_on_weaken; [exact AG6 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W5_6 : vtrip (sp - 672) 264 p5 100 M6) by (eapply (vtrip_agree _ _ _ _ M5' M6 VT5); [lia | lia | eapply agree_on_weaken; [exact AG6 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (TI6 : tinit (sp - 672) words n M6) by (eapply (tinit_agree _ _ _ M5' M6 TI5); [lia | lia | eapply agree_on_weaken; [exact AG6 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    clear AG5s AG6 PI5 PI5' VT5 V5 MS5' W3_5 W3_5' W4_5 W4_5' TI5.

    pose (E6 := Eseed R6 [Z_to_bv 64 (sp - 672); Z_to_bv 64 p6]).
    assert (HR6 : regs_ok E6 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33)]) R6).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK6 : know_ok SEGS E6 M6 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 592)]).
    { pose proof (s_fdef _ _ _ _ _ WS6) as FD. rewrite Esp0 in FD. unfold PO_FRAME in FD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD | lia | lia] | lia | lia | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS6) as MS6.
    xruns HR6 HK6 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6'.
    rreg HRn (1%bv) G1_6. rreg HRn (2%bv) H2_6'. rreg HRn (10%bv) G10_6'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS6'.
    clear HRn HR6 HK6. fixregsN. rewrite ?w_add by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M6' := mm) in * end.
    assert (ST6 : stores_in (zwin (sp - 672 + 520) (sp - 672 + 544)) M6 M6') by (unfold M6'; stin).
    assert (WS6' : WS w [(p3, 500); (p4, 100); (p5, 100); (p6, 500)] A6 M6' model6) by (eapply (ws_stores w _ A6 M6 M6' model6 _ WS6 ST6); rewrite Esp, Esp0; unfold zwin; intros; lia).
    assert (V6 : cell8 SEGS M6' (sp - 672 + 520) p6 /\ cell8 SEGS M6' (sp - 672 + 528) p6 /\ cell8 SEGS M6' (sp - 672 + 536) (p6 + 500)).
    { unfold cell8. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M6'; rdback]). }
    assert (AG6s : CRep.agree_on (fun a => sp - 672 <= a < sp /\ ~ zwin (sp - 672 + 520) (sp - 672 + 544) a) M6 M6') by (eapply stores_in_agree; [exact ST6 | intros b Hb; unfold zwin in *; lia]).
    assert (PI6' : pinit (sp - 672) M6') by (eapply (pinit_agree _ M6 M6' PI6); [lia | lia | eapply agree_on_weaken; [exact AG6s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W3_6' : vtrip (sp - 672) 216 p3 500 M6') by (eapply (vtrip_agree _ _ _ _ M6 M6' W3_6); [lia | lia | eapply agree_on_weaken; [exact AG6s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W4_6' : vtrip (sp - 672) 240 p4 100 M6') by (eapply (vtrip_agree _ _ _ _ M6 M6' W4_6); [lia | lia | eapply agree_on_weaken; [exact AG6s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W5_6' : vtrip (sp - 672) 264 p5 100 M6') by (eapply (vtrip_agree _ _ _ _ M6 M6' W5_6); [lia | lia | eapply agree_on_weaken; [exact AG6s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (TI6' : tinit (sp - 672) words n M6') by (eapply (tinit_agree _ _ _ M6 M6' TI6); [lia | lia | eapply agree_on_weaken; [exact AG6s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (VT6 : vtrip (sp - 672) 520 p6 500 M6') by (unfold vtrip; replace (sp - 672 + 520 + 8) with (sp - 672 + 528) by lia; replace (sp - 672 + 520 + 16) with (sp - 672 + 536) by lia; exact V6).
    pose proof (s_ms _ _ _ _ _ WS6') as MS6'. clearbody M6'. clear ST6.
    eapply (ws_new w _ A6 M6' model6 fx R6' 100 0x662e4 K WS6');
      [ split; [exact G1_6 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_6' | split; [rewrite (GS6' 3%bv) by (clear; in_regs); exact Qgp6 | rewrite (GS6' 4%bv) by (clear; in_regs); exact Qtp6]]]]]
      | exact G10_6' | lia
      | eapply (roomL_room_for SEGS Ly.L MI); [exact (s_ai _ _ _ _ _ WS6') | lia | eapply (ws_room w _ A6 M6' model6 100 WS6' BUD); [unfold Zlength; cbn; lia | lia]]
      | exact HNM |].
    intros A7 R7 M7 model7 p7 WS7 KEPT7 G10_7 Hp7a Hp7c Hp7al Hp7d Hp7f AG7 AH7. cbn [app] in WS7.
    assert (Qgp7 : getr R7 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT7 3%bv) by (clear; in_regs); rewrite (GS6' 3%bv) by (clear; in_regs); exact Qgp6).
    assert (Qtp7 : getr R7 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT7 4%bv) by (clear; in_regs); rewrite (GS6' 4%bv) by (clear; in_regs); exact Qtp6).
    keptQ KEPT7 H2_6' H2_7.
    assert (PI7 : pinit (sp - 672) M7) by (eapply (pinit_agree _ M6' M7 PI6'); [lia | lia | eapply agree_on_weaken; [exact AG7 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W3_7 : vtrip (sp - 672) 216 p3 500 M7) by (eapply (vtrip_agree _ _ _ _ M6' M7 W3_6'); [lia | lia | eapply agree_on_weaken; [exact AG7 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W4_7 : vtrip (sp - 672) 240 p4 100 M7) by (eapply (vtrip_agree _ _ _ _ M6' M7 W4_6'); [lia | lia | eapply agree_on_weaken; [exact AG7 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W5_7 : vtrip (sp - 672) 264 p5 100 M7) by (eapply (vtrip_agree _ _ _ _ M6' M7 W5_6'); [lia | lia | eapply agree_on_weaken; [exact AG7 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W6_7 : vtrip (sp - 672) 520 p6 500 M7) by (eapply (vtrip_agree _ _ _ _ M6' M7 VT6); [lia | lia | eapply agree_on_weaken; [exact AG7 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (TI7 : tinit (sp - 672) words n M7) by (eapply (tinit_agree _ _ _ M6' M7 TI6'); [lia | lia | eapply agree_on_weaken; [exact AG7 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    clear AG6s AG7 PI6 PI6' VT6 V6 MS6' W3_6 W3_6' W4_6 W4_6' W5_6 W5_6' TI6 TI6'.

    pose (E7 := Eseed R7 [Z_to_bv 64 (sp - 672); Z_to_bv 64 p7]).
    assert (HR7 : regs_ok E7 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33)]) R7).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK7 : know_ok SEGS E7 M7 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 592)]).
    { pose proof (s_fdef _ _ _ _ _ WS7) as FD. rewrite Esp0 in FD. unfold PO_FRAME in FD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD | lia | lia] | lia | lia | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS7) as MS7.
    xruns HR7 HK7 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R7'.
    rreg HRn (1%bv) G1_7. rreg HRn (2%bv) H2_7'. rreg HRn (10%bv) G10_7'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS7'.
    clear HRn HR7 HK7. fixregsN. rewrite ?w_add by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M7' := mm) in * end.
    assert (ST7 : stores_in (zwin (sp - 672 + 544) (sp - 672 + 568)) M7 M7') by (unfold M7'; stin).
    assert (WS7' : WS w [(p3, 500); (p4, 100); (p5, 100); (p6, 500); (p7, 100)] A7 M7' model7) by (eapply (ws_stores w _ A7 M7 M7' model7 _ WS7 ST7); rewrite Esp, Esp0; unfold zwin; intros; lia).
    assert (V7 : cell8 SEGS M7' (sp - 672 + 544) p7 /\ cell8 SEGS M7' (sp - 672 + 552) p7 /\ cell8 SEGS M7' (sp - 672 + 560) (p7 + 100)).
    { unfold cell8. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M7'; rdback]). }
    assert (AG7s : CRep.agree_on (fun a => sp - 672 <= a < sp /\ ~ zwin (sp - 672 + 544) (sp - 672 + 568) a) M7 M7') by (eapply stores_in_agree; [exact ST7 | intros b Hb; unfold zwin in *; lia]).
    assert (PI7' : pinit (sp - 672) M7') by (eapply (pinit_agree _ M7 M7' PI7); [lia | lia | eapply agree_on_weaken; [exact AG7s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W3_7' : vtrip (sp - 672) 216 p3 500 M7') by (eapply (vtrip_agree _ _ _ _ M7 M7' W3_7); [lia | lia | eapply agree_on_weaken; [exact AG7s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W4_7' : vtrip (sp - 672) 240 p4 100 M7') by (eapply (vtrip_agree _ _ _ _ M7 M7' W4_7); [lia | lia | eapply agree_on_weaken; [exact AG7s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W5_7' : vtrip (sp - 672) 264 p5 100 M7') by (eapply (vtrip_agree _ _ _ _ M7 M7' W5_7); [lia | lia | eapply agree_on_weaken; [exact AG7s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W6_7' : vtrip (sp - 672) 520 p6 500 M7') by (eapply (vtrip_agree _ _ _ _ M7 M7' W6_7); [lia | lia | eapply agree_on_weaken; [exact AG7s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (TI7' : tinit (sp - 672) words n M7') by (eapply (tinit_agree _ _ _ M7 M7' TI7); [lia | lia | eapply agree_on_weaken; [exact AG7s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (VT7 : vtrip (sp - 672) 544 p7 100 M7') by (unfold vtrip; replace (sp - 672 + 544 + 8) with (sp - 672 + 552) by lia; replace (sp - 672 + 544 + 16) with (sp - 672 + 560) by lia; exact V7).
    pose proof (s_ms _ _ _ _ _ WS7') as MS7'. clearbody M7'. clear ST7.
    eapply (ws_new w _ A7 M7' model7 fx R7' 100 0x662fc K WS7');
      [ split; [exact G1_7 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_7' | split; [rewrite (GS7' 3%bv) by (clear; in_regs); exact Qgp7 | rewrite (GS7' 4%bv) by (clear; in_regs); exact Qtp7]]]]]
      | exact G10_7' | lia
      | eapply (roomL_room_for SEGS Ly.L MI); [exact (s_ai _ _ _ _ _ WS7') | lia | eapply (ws_room w _ A7 M7' model7 100 WS7' BUD); [unfold Zlength; cbn; lia | lia]]
      | exact HNM |].
    intros A8 R8 M8 model8 p8 WS8 KEPT8 G10_8 Hp8a Hp8c Hp8al Hp8d Hp8f AG8 AH8. cbn [app] in WS8.
    assert (Qgp8 : getr R8 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT8 3%bv) by (clear; in_regs); rewrite (GS7' 3%bv) by (clear; in_regs); exact Qgp7).
    assert (Qtp8 : getr R8 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT8 4%bv) by (clear; in_regs); rewrite (GS7' 4%bv) by (clear; in_regs); exact Qtp7).
    keptQ KEPT8 H2_7' H2_8.
    assert (PI8 : pinit (sp - 672) M8) by (eapply (pinit_agree _ M7' M8 PI7'); [lia | lia | eapply agree_on_weaken; [exact AG8 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W3_8 : vtrip (sp - 672) 216 p3 500 M8) by (eapply (vtrip_agree _ _ _ _ M7' M8 W3_7'); [lia | lia | eapply agree_on_weaken; [exact AG8 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W4_8 : vtrip (sp - 672) 240 p4 100 M8) by (eapply (vtrip_agree _ _ _ _ M7' M8 W4_7'); [lia | lia | eapply agree_on_weaken; [exact AG8 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W5_8 : vtrip (sp - 672) 264 p5 100 M8) by (eapply (vtrip_agree _ _ _ _ M7' M8 W5_7'); [lia | lia | eapply agree_on_weaken; [exact AG8 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W6_8 : vtrip (sp - 672) 520 p6 500 M8) by (eapply (vtrip_agree _ _ _ _ M7' M8 W6_7'); [lia | lia | eapply agree_on_weaken; [exact AG8 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W7_8 : vtrip (sp - 672) 544 p7 100 M8) by (eapply (vtrip_agree _ _ _ _ M7' M8 VT7); [lia | lia | eapply agree_on_weaken; [exact AG8 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (TI8 : tinit (sp - 672) words n M8) by (eapply (tinit_agree _ _ _ M7' M8 TI7'); [lia | lia | eapply agree_on_weaken; [exact AG8 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    clear AG7s AG8 PI7 PI7' VT7 V7 MS7' W3_7 W3_7' W4_7 W4_7' W5_7 W5_7' W6_7 W6_7' TI7 TI7'.

    assert (S9_8 : getr R8 9%bv = getr R2 9%bv) by (rewrite (KEPT8 9%bv) by (clear; in_regs); rewrite (GS7' 9%bv) by (clear; in_regs); rewrite (KEPT7 9%bv) by (clear; in_regs); rewrite (GS6' 9%bv) by (clear; in_regs); rewrite (KEPT6 9%bv) by (clear; in_regs); rewrite (GS5' 9%bv) by (clear; in_regs); rewrite (KEPT5 9%bv) by (clear; in_regs); rewrite (GS4' 9%bv) by (clear; in_regs); rewrite (KEPT4 9%bv) by (clear; in_regs); rewrite (GS3' 9%bv) by (clear; in_regs); rewrite (KEPT3 9%bv) by (clear; in_regs); exact eq_refl). rewrite G9 in S9_8.
    assert (S9_8' : getr R8 9%bv = alu64 ALU_ADD (Z_to_bv 64 (sp - 672)) (Z_to_bv 64 48)) by (rewrite w_add by lia; exact S9_8).
    pose (E8 := Eseed R8 [Z_to_bv 64 (sp - 672); Z_to_bv 64 p8]).
    assert (HR8 : regs_ok E8 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 48))]) R8).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK8 : know_ok SEGS E8 M8 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 592)]).
    { pose proof (s_fdef _ _ _ _ _ WS8) as FD. rewrite Esp0 in FD. unfold PO_FRAME in FD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD | lia | lia] | lia | lia | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS8) as MS8.
    xruns HR8 HK8 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R8'.
    rreg HRn (1%bv) G1_8. rreg HRn (2%bv) H2_8'. rreg HRn (10%bv) G10_8'. rreg HRn (11%bv) G11_8'. rreg HRn (9%bv) G9_8'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS8'.
    clear HRn HR8 HK8. fixregsN. rewrite ?w_add in G10_8', G11_8' |- * by lia. rewrite w_add in G9_8' by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M8' := mm) in * end.
    assert (ST8 : stores_in (zwin (sp - 672 + 568) (sp - 672 + 592)) M8 M8') by (unfold M8'; stin).
    assert (WS8' : WS w [(p3, 500); (p4, 100); (p5, 100); (p6, 500); (p7, 100); (p8, 100)] A8 M8' model8) by (eapply (ws_stores w _ A8 M8 M8' model8 _ WS8 ST8); rewrite Esp, Esp0; unfold zwin; intros; lia).
    assert (V8 : cell8 SEGS M8' (sp - 672 + 568) p8 /\ cell8 SEGS M8' (sp - 672 + 576) p8 /\ cell8 SEGS M8' (sp - 672 + 584) (p8 + 100)).
    { unfold cell8. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M8'; rdback]). }
    assert (AG8s : CRep.agree_on (fun a => sp - 672 <= a < sp /\ ~ zwin (sp - 672 + 568) (sp - 672 + 592) a) M8 M8') by (eapply stores_in_agree; [exact ST8 | intros b Hb; unfold zwin in *; lia]).
    assert (PI8' : pinit (sp - 672) M8') by (eapply (pinit_agree _ M8 M8' PI8); [lia | lia | eapply agree_on_weaken; [exact AG8s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W3_8' : vtrip (sp - 672) 216 p3 500 M8') by (eapply (vtrip_agree _ _ _ _ M8 M8' W3_8); [lia | lia | eapply agree_on_weaken; [exact AG8s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W4_8' : vtrip (sp - 672) 240 p4 100 M8') by (eapply (vtrip_agree _ _ _ _ M8 M8' W4_8); [lia | lia | eapply agree_on_weaken; [exact AG8s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W5_8' : vtrip (sp - 672) 264 p5 100 M8') by (eapply (vtrip_agree _ _ _ _ M8 M8' W5_8); [lia | lia | eapply agree_on_weaken; [exact AG8s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W6_8' : vtrip (sp - 672) 520 p6 500 M8') by (eapply (vtrip_agree _ _ _ _ M8 M8' W6_8); [lia | lia | eapply agree_on_weaken; [exact AG8s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W7_8' : vtrip (sp - 672) 544 p7 100 M8') by (eapply (vtrip_agree _ _ _ _ M8 M8' W7_8); [lia | lia | eapply agree_on_weaken; [exact AG8s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (TI8' : tinit (sp - 672) words n M8') by (eapply (tinit_agree _ _ _ M8 M8' TI8); [lia | lia | eapply agree_on_weaken; [exact AG8s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (VT8 : vtrip (sp - 672) 568 p8 100 M8') by (unfold vtrip; replace (sp - 672 + 568 + 8) with (sp - 672 + 576) by lia; replace (sp - 672 + 568 + 16) with (sp - 672 + 584) by lia; exact V8).
    pose proof (s_ms _ _ _ _ _ WS8') as MS8'. clearbody M8'. clear ST8 AG8s PI8 W3_8 W4_8 W5_8 W6_8 W7_8 TI8 V8 MS8.

    pose proof (ws_X_nodup w _ A8 M8' model8 WS8') as NDX. cbn [map fst] in NDX.
    pose proof PI8' as PIc. unfold pinit in PIc.
    destruct PIc as (Q8 & Q16 & Q24 & Q32 & Q40 & Q48 & Q56 & Q64 & Q72 & Q80 & Q88 & Q92 & Q96 & Q104 & Q112 & Q120 & Q128 & Q136 & Q144 & Q152 & Q160 & Q168 & Q176 & Q184 & Q192 & Q200 & Q208 & Q336).
    pose proof TI8' as TIc. unfold tinit in TIc.
    destruct TIc as (U352 & U360 & U368 & U376 & U384 & U392 & U396 & U400 & U408 & U416 & U424 & U432 & U440 & U448 & U456 & U464 & U472 & U480 & U488 & U496 & U504 & U512).
    pose proof (s_fdef _ _ _ _ _ WS8') as FD8. rewrite Esp0 in FD8. unfold PO_FRAME in FD8.
    assert (SR1 : state_rep MI A8 M8' (sp - 672 + 48) (mkfresh 0 0 p3 p4 p5)).
    { eapply (st_rep_fresh A8 M8' model8 (sp - 672) 48 0 0 p3 p4 p5 (s_ai _ _ _ _ _ WS8')); try cellq.
      - eapply mdef_sub; [exact FD8 | lia | lia].
      - apply PmSetNumS1.mod16_mod8. replace (sp - 672 + 48) with (sp + (-39) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
      - lia. - lia.
      - eapply (ws_X_live w _ A8 M8' model8 _ WS8'). (first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]).
      - eapply (ws_X_live w _ A8 M8' model8 _ WS8'). (first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]).
      - eapply (ws_X_live w _ A8 M8' model8 _ WS8'). (first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]).
      - exact (proj1 (nodup_split6 _ _ _ _ _ _ NDX)). }
    assert (SR2 : state_rep MI A8 M8' (sp - 672 + 352) (mkfresh words n p6 p7 p8)).
    { eapply (st_rep_fresh A8 M8' model8 (sp - 672) 352 words n p6 p7 p8 (s_ai _ _ _ _ _ WS8')); try cellq.
      - eapply mdef_sub; [exact FD8 | lia | lia].
      - apply PmSetNumS1.mod16_mod8. replace (sp - 672 + 352) with (sp + (-20) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
      - lia. - lia.
      - eapply (ws_X_live w _ A8 M8' model8 _ WS8'). (first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]).
      - eapply (ws_X_live w _ A8 M8' model8 _ WS8'). (first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]).
      - eapply (ws_X_live w _ A8 M8' model8 _ WS8'). (first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]).
      - exact (proj2 (nodup_split6 _ _ _ _ _ _ NDX)). }

    assert (F8 : getr R8' 8%bv = Z_to_bv 64 (sp - 672 + 304)) by (rewrite (GS8' 8%bv) by (clear; in_regs); rewrite (KEPT8 8%bv) by (clear; in_regs); rewrite (GS7' 8%bv) by (clear; in_regs); rewrite (KEPT7 8%bv) by (clear; in_regs); rewrite (GS6' 8%bv) by (clear; in_regs); rewrite (KEPT6 8%bv) by (clear; in_regs); rewrite (GS5' 8%bv) by (clear; in_regs); exact S8_5).
    assert (F24 : getr R8' 24%bv = Z_to_bv 64 0x3f800000) by (rewrite (GS8' 24%bv) by (clear; in_regs); rewrite (KEPT8 24%bv) by (clear; in_regs); rewrite (GS7' 24%bv) by (clear; in_regs); rewrite (KEPT7 24%bv) by (clear; in_regs); rewrite (GS6' 24%bv) by (clear; in_regs); rewrite (KEPT6 24%bv) by (clear; in_regs); exact T24).
    assert (F25 : getr R8' 25%bv = getr (v_R0 w) 25%bv) by (rewrite (GS8' 25%bv) by (clear; in_regs); rewrite (KEPT8 25%bv) by (clear; in_regs); rewrite (GS7' 25%bv) by (clear; in_regs); rewrite (KEPT7 25%bv) by (clear; in_regs); rewrite (GS6' 25%bv) by (clear; in_regs); rewrite (KEPT6 25%bv) by (clear; in_regs); rewrite (GS5' 25%bv) by (clear; in_regs); rewrite (KEPT5 25%bv) by (clear; in_regs); rewrite (GS4' 25%bv) by (clear; in_regs); rewrite (KEPT4 25%bv) by (clear; in_regs); rewrite (GS3' 25%bv) by (clear; in_regs); rewrite (KEPT3 25%bv) by (clear; in_regs); rewrite (GS2 25%bv) by (clear; in_regs); rewrite (GS1 25%bv) by (clear; in_regs); reflexivity).
    assert (F26 : getr R8' 26%bv = getr (v_R0 w) 26%bv) by (rewrite (GS8' 26%bv) by (clear; in_regs); rewrite (KEPT8 26%bv) by (clear; in_regs); rewrite (GS7' 26%bv) by (clear; in_regs); rewrite (KEPT7 26%bv) by (clear; in_regs); rewrite (GS6' 26%bv) by (clear; in_regs); rewrite (KEPT6 26%bv) by (clear; in_regs); rewrite (GS5' 26%bv) by (clear; in_regs); rewrite (KEPT5 26%bv) by (clear; in_regs); rewrite (GS4' 26%bv) by (clear; in_regs); rewrite (KEPT4 26%bv) by (clear; in_regs); rewrite (GS3' 26%bv) by (clear; in_regs); rewrite (KEPT3 26%bv) by (clear; in_regs); rewrite (GS2 26%bv) by (clear; in_regs); rewrite (GS1 26%bv) by (clear; in_regs); reflexivity).
    assert (F27 : getr R8' 27%bv = getr (v_R0 w) 27%bv) by (rewrite (GS8' 27%bv) by (clear; in_regs); rewrite (KEPT8 27%bv) by (clear; in_regs); rewrite (GS7' 27%bv) by (clear; in_regs); rewrite (KEPT7 27%bv) by (clear; in_regs); rewrite (GS6' 27%bv) by (clear; in_regs); rewrite (KEPT6 27%bv) by (clear; in_regs); rewrite (GS5' 27%bv) by (clear; in_regs); rewrite (KEPT5 27%bv) by (clear; in_regs); rewrite (GS4' 27%bv) by (clear; in_regs); rewrite (KEPT4 27%bv) by (clear; in_regs); rewrite (GS3' 27%bv) by (clear; in_regs); rewrite (KEPT3 27%bv) by (clear; in_regs); rewrite (GS2 27%bv) by (clear; in_regs); rewrite (GS1 27%bv) by (clear; in_regs); reflexivity).
    eapply (po_tail w K fx A8 M8' model8 R8' p3 p4 p5 p6 p7 p8);
      [ exact POST | unfold POW; cbn [v_ret v_R0 v_sp0]; repeat (split; [first [exact Hret | lia | assumption] |]); exact Htp
      | exact BUD | exact HNM | exact AI | exact WOK | exact WWIN | exact FZ | exact WS8' | exact SR1 | exact SR2
      | apply phdr_of_pinit; exact PI8' | lia | lia | lia | lia | lia | lia
      | exact G1_8 | exact H2_8' | rewrite (GS8' 3%bv) by (clear; in_regs); exact Qgp8 | rewrite (GS8' 4%bv) by (clear; in_regs); exact Qtp8
      | exact G10_8' | exact G11_8' | exact F8 | exact G9_8' | exact F24 | exact F25 | exact F26 | exact F27 ].
  Qed.

  Theorem binary_parse_S1 : binary_parse_stmt SEGS Ly.L MI ST kcS1.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL PO.
    unfold binary_parse_stmt, parse_opts_stmt. cbn [kc_po_stack kc_parse kcS1].
    intros fx A s R M model sp ret ctx env words n K CB ROC FZ Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 _ CTX CWIN Henv WOK WWIN BUD POST.
    pose proof ac_bounds_lit as Hcv.
    pose proof CB as CB0. destruct CB0 as [AI MS IRC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx]. destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    pose (E := Eseed R (@nil word)).
    assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
    assert (HK : know_ok SEGS E M []) by (apply Forall_nil).
    xruns HR HK 10%nat [0x66100] (SCR [] [] []) 10%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (17%bv) G17.
    pose proof (syms_id_sound _ _ _ _ [1; 2; 3; 4; 8; 9; 10; 11; 12; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS.
    clear HRn HR HK. fixregsN.
    eapply (po_core fx A s R1 M model sp ret ctx env words n K); try eassumption.
    - constructor; try assumption. constructor; rewrite ?(GS 1%bv), ?(GS 2%bv), ?(GS 3%bv), ?(GS 4%bv) by (clear; in_regs); assumption.
    - rewrite (GS 10%bv) by (clear; in_regs); exact Ha0.
    - rewrite (GS 11%bv) by (clear; in_regs); exact Ha1.
    - rewrite (GS 12%bv) by (clear; in_regs); exact Ha2.
    - rewrite (GS 13%bv) by (clear; in_regs); exact Ha3.
    - rewrite (GS 14%bv) by (clear; in_regs); exact Ha4.
    - rewrite (GS 15%bv) by (clear; in_regs); exact Ha5.
    - rewrite (GS 16%bv) by (clear; in_regs); exact Ha6.
    - intros fx' A' R' M' model' r RB FZ' Hr PERM EF. eapply (POST fx' A' R' M' model' r); try assumption.
      destruct RB as [AI' MS' FS' FDS' SX' KEPT]. constructor; try assumption.
      intros rr Hrr. rewrite (KEPT rr Hrr). apply GS. revert Hrr. clear. unfold callee_saved. intros Hrr.
      repeat (destruct Hrr as [<-|Hrr]; [in_regs|]). destruct Hrr.
  Qed.
End PM.
