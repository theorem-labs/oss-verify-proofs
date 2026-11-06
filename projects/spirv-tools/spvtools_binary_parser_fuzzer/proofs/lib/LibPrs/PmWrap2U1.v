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
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts2 U1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HFpu HConstsU1 HStateDtorU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1 PmInstU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmWrapU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmWrapU1.U1_code_66cd0_66cd4. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmWrapU1 PmWrapBU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.
Module Ly := U1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_calleesU1 SEGS Ly.L MI ST G tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  Variable PM : parse_module_stmt SEGS Ly.L MI ST kcU1.

  Variable PO : @PmWrapU1.po_callees AC MI ST.
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation po_core2 := (PmWrapBU1.po_core2 CL PM PO).
  #[local] Notation ws_new := (PmWrapU1.ws_new CL).

  Lemma po_core : forall (fx : FPState) A (s : LibIface.SX ST) R M model (sp ret ctx env words n : Z) (K : TSet),
    callB MI ST A s R M model sp ret 17056 -> ro_clear Ly.L M -> frm_zero (@fp_csr fx) ->
    getr R 10%bv = Z_to_bv 64 ctx -> getr R 11%bv = Z_to_bv 64 0 -> getr R 12%bv = Z_to_bv 64 words ->
    getr R 13%bv = Z_to_bv 64 n -> getr R 14%bv = Z_to_bv 64 0 -> getr R 15%bv = Z_to_bv 64 0 ->
    getr R 16%bv = Z_to_bv 64 0 -> getr R 17%bv = Z_to_bv 64 0 ->
    CRep.ctx_rep MI A M ctx env -> (forall a, zwin ctx (ctx + CTX_SZ) a -> ~ zwin (sp - 17056) sp a) ->
    0 <= env < 32 ->
    (words <> 0 -> words_ok (live MI A) sp M words n) ->
    (forall a, zwin words (words + 4 * n) a -> ~ zwin (sp - 17056) sp a) ->
    pm_budget SEGS Ly.L MI A n ->
    (forall (fx' : FPState) A' R' M' model' (r : Z),
        retB MI ST A' s R R' M' model model' -> frm_zero (@fp_csr fx') ->
        getr R' 10%bv = Z_to_bv 64 r ->
        Permutation (live MI A') (live MI A) ->
        eff MI A A' M M' (sp - 17056, sp) (junk SEGS Ly.L MI A) ->
        srealizes SEGS (cfg fx' R' ret M' model') K) ->
    srealizes SEGS (cfg fx R 0x6694c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL PM PO.
    intros fx A s R M model sp ret ctx env words n K CB ROC FZ Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7 CTX CWIN Henv WOK WWIN BUD POST.
    pose proof ac_bounds_lit as Hcv.
    assert (Rwords : 0 <= words < 2 ^ 64) by (destruct (Z.eq_dec words 0) as [->|Hw]; [lia | destruct (WOK Hw) as (W1 & W2 & W3 & W4 & _); lia]).
    destruct CB as [AI MS IRC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx]. destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    destruct CTX as (Cq0 & Cqal & Cq63 & CqIn & Cenv & Cf0). unfold CRep.fld in Cenv, Cf0.
    destruct (ai_live_block MI A M model ctx CTX_SZ AI CqIn) as (_ & _ & _ & Cqc & Cqpay). unfold CTX_SZ in *.
    pose proof BUD as BUD'. destruct BUD' as (Bcaps & Bbig & Bnmax & Bn & _).
    assert (HWD : mdef M (sp - 17056) 17056).
    { eapply store_ok_mdef_offimg; [exact HROOM | lia | lia | lia |]. intros x Hx. apply ly_noseg. lia. }
    set (w := {| v_sp0 := sp; v_ret := ret; v_ctx := ctx; v_env := env; v_words := words; v_n := n;
                 v_R0 := R; v_A0 := A; v_M0 := M; v_model0 := model; v_s := s |}).
    assert (Esp : v_sp w = sp - 672) by reflexivity. assert (Esp0 : v_sp0 w = sp) by reflexivity.

    pose (E := Eseed R [Z_to_bv 64 sp]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) (-17056)) (ELit 17056)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_stack; [evs; reflexivity | reflexivity | lia | lia | exact HROOM]. }
    xruns HR HK 100%nat (0x66974 :: WSTOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (2%bv) G2. pose proof (syms_id_sound _ _ _ _ [1; 3; 4; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS1.
    clear HRn HR HK. fixregsN. rewrite w_addm in G2 by lia. rewrite Hra.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M1 := mm) in * end.
    assert (ST1 : stores_in (zwin (sp - 72) sp) M M1) by (unfold M1; stin).
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
        assert (Hk' : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9) by lia.
        destruct Hk' as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]; cbn [Z.to_nat Z.sub nth Pos.to_nat Z.mul Pos.mul]; unfold M1; rdback.
      - rewrite app_nil_r. reflexivity. }
    assert (AGc : CRep.agree_on (zwin ctx (ctx + 64)) M M1) by (eapply stores_in_agree; [exact ST1 | intros a Ha; unfold zwin in *; lia]).
    assert (Cenv1 : rdn SEGS M1 (Z_to_bv 64 ctx) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 env))).
    { rewrite (rdn_agree_win SEGS M M1 ctx 4); [exact Cenv | lia | cbn; lia | eapply agree_on_weaken; [exact AGc | unfold zwin; cbn; intros; lia]]. }
    assert (Cf1 : cellw SEGS M1 (ctx + 48) 8 0).
    { split; [cbn; lia|]. change (N.to_nat 8) with 8%nat. rewrite (rdn_agree_win SEGS M M1 (ctx + 48) 8); [exact Cf0 | lia | cbn; lia | eapply agree_on_weaken; [exact AGc | unfold zwin; cbn; intros; lia]]. }
    clearbody M1. clear ST1 HWD HROOM IRC AGc.

    pose (E2 := Eseed R1 [Z_to_bv 64 (sp - 672); Z_to_bv 64 ctx; Z_to_bv 64 words; Z_to_bv 64 n; Z_to_bv 64 env]).
    assert (HR2 : regs_ok E2 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (11%bv, ELit 0); (12%bv, EVar 34); (13%bv, EVar 35); (14%bv, ELit 0); (15%bv, ELit 0); (16%bv, ELit 0); (17%bv, ELit 0)]) R1).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs;
        first [exact G2 | rewrite (GS1 _) by (clear; in_regs); assumption]. }
    assert (HK2 : know_ok SEGS E2 M1 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KRange (EVar 33) 1 (2 ^ 47); KAlign (EVar 33) 16; KWr (SA (EVar 32) 0) (ELit 600);
                                     KWord (SA (EVar 33) 48) (N.to_nat 8) (ELit 0); KDisj (SA (EVar 33) 0) (ELit 64) (SA (EVar 32) 0) (ELit 672);
                                     KRange (EVar 36) 0 31]).
    { pose proof (s_fdef _ _ _ _ _ WS1) as FD1. rewrite Esp0 in FD1. unfold PO_FRAME in FD1.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kalign_var; [evs; reflexivity | lia | lia | exact Cqal].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD1 | lia | lia] | lia | lia | lia | lia].
      - eapply kword_var; [exact Cf1 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
      - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR2 HK2 100%nat WSTOPS (SCR [] [EVar 36] []) 60%N.
    { split_scs; try sc_auto1. all: cbn [sc_denot]; exists (word_to_le_bytes 4 (Z_to_bv 64 env)); split; [rewrite (adenot_Z E2 _ ctx); [cbn [a_off]; rewrite Z.add_0_r; exact Cenv1 | evs; reflexivity | lia] | evs; unfold extz; rewrite ContLib.lez_w4 by lia; rewrite bv_swrap32_cases by lia; destruct (Z.ltb_spec env (2 ^ 31)); [reflexivity | lia]]. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) H2. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10.
    rreg HRn (18%bv) G18. rreg HRn (19%bv) G19. rreg HRn (20%bv) G20. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 24; 25; 26; 27]%bv HRn eq_refl) as GS2.
    clear HRn HR2 HK2. fixregsN. rewrite ?w_add in G8 |- * by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M2 := mm) in * end.
    assert (ST2 : stores_in (zwin (sp - 672) (sp - 672 + 344)) M1 M2) by (unfold M2; stin).
    assert (WS2 : WS w [] A M2 model) by (eapply (ws_stores w [] A M1 M2 model _ WS1 ST2); rewrite Esp, Esp0; unfold zwin; intros; lia).
    assert (PI2 : pinit (sp - 672) M2).
    { unfold pinit. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M2; rdback]). }
    pose proof (s_ms _ _ _ _ _ WS2) as MS2. clearbody M2. clear ST2 WS1 Cenv1 Cf1.
    pose proof (cu_classes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HCL.
    assert (HNM : 500 <= NMAX MI) by (unfold LIB_NMAX in Bnmax; lia).

    eapply (ws_new w [] A M2 model fx R2 500 0x66aa0 K WS2); [split; [exact G1 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2 | split; [rewrite (GS2 3%bv) by (clear; in_regs); rewrite (GS1 3%bv) by (clear; in_regs); exact Hgp | rewrite (GS2 4%bv) by (clear; in_regs); rewrite (GS1 4%bv) by (clear; in_regs); exact Htp]]]]]
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
    assert (HK3 : know_ok SEGS E3 M3 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 600); KRange (EVar 33) 1 (2 ^ 47)]).
    { pose proof (s_fdef _ _ _ _ _ WS3) as FD. rewrite Esp0 in FD. unfold PO_FRAME in FD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD | lia | lia] | lia | lia | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia]. }
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
    eapply (ws_new w _ A3 M3' model3 fx R3' 100 0x66ac0 K WS3');
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
    assert (HK4 : know_ok SEGS E4 M4 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 600); KRange (EVar 33) 1 (2 ^ 47)]).
    { pose proof (s_fdef _ _ _ _ _ WS4) as FD. rewrite Esp0 in FD. unfold PO_FRAME in FD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD | lia | lia] | lia | lia | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS4) as MS4.
    xruns HR4 HK4 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4'.
    rreg HRn (1%bv) G1_4. rreg HRn (2%bv) H2_4'. rreg HRn (10%bv) G10_4'. rreg HRn (21%bv) G21_4'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS4'.
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
    eapply (ws_new w _ A4 M4' model4 fx R4' 100 0x66ae0 K WS4');
      [ split; [exact G1_4 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_4' | split; [rewrite (GS4' 3%bv) by (clear; in_regs); exact Qgp4 | rewrite (GS4' 4%bv) by (clear; in_regs); exact Qtp4]]]]]
      | exact G10_4' | lia
      | eapply (roomL_room_for SEGS Ly.L MI); [exact (s_ai _ _ _ _ _ WS4') | lia | eapply (ws_room w _ A4 M4' model4 100 WS4' BUD); [unfold Zlength; cbn; lia | lia]]
      | exact HNM |].
    intros A5 R5 M5 model5 p5 WS5 KEPT5 G10_5 Hp5a Hp5c Hp5al Hp5d Hp5f AG5 AH5. cbn [app] in WS5.
    assert (Qgp5 : getr R5 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT5 3%bv) by (clear; in_regs); rewrite (GS4' 3%bv) by (clear; in_regs); exact Qgp4).
    assert (Qtp5 : getr R5 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT5 4%bv) by (clear; in_regs); rewrite (GS4' 4%bv) by (clear; in_regs); exact Qtp4).
    keptQ KEPT5 H2_4' H2_5.
    keptQ KEPT5 G21_4' G21_5.
    assert (PI5 : pinit (sp - 672) M5) by (eapply (pinit_agree _ M4' M5 PI4'); [lia | lia | eapply agree_on_weaken; [exact AG5 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W3_5 : vtrip (sp - 672) 216 p3 500 M5) by (eapply (vtrip_agree _ _ _ _ M4' M5 W3_4'); [lia | lia | eapply agree_on_weaken; [exact AG5 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    assert (W4_5 : vtrip (sp - 672) 240 p4 100 M5) by (eapply (vtrip_agree _ _ _ _ M4' M5 VT4); [lia | lia | eapply agree_on_weaken; [exact AG5 | cbn beta; rewrite Esp, Esp0; unfold zwin; cbn; intros; lia]]).
    clear AG4s AG5 PI4 PI4' VT4 V4 MS4' W3_4 W3_4'.
    assert (S18_5 : getr R5 18%bv = getr R2 18%bv) by (rewrite (KEPT5 18%bv) by (clear; in_regs); rewrite (GS4' 18%bv) by (clear; in_regs); rewrite (KEPT4 18%bv) by (clear; in_regs); rewrite (GS3' 18%bv) by (clear; in_regs); rewrite (KEPT3 18%bv) by (clear; in_regs); exact eq_refl).
    assert (S19_5 : getr R5 19%bv = getr R2 19%bv) by (rewrite (KEPT5 19%bv) by (clear; in_regs); rewrite (GS4' 19%bv) by (clear; in_regs); rewrite (KEPT4 19%bv) by (clear; in_regs); rewrite (GS3' 19%bv) by (clear; in_regs); rewrite (KEPT3 19%bv) by (clear; in_regs); exact eq_refl).
    assert (S20_5 : getr R5 20%bv = getr R2 20%bv) by (rewrite (KEPT5 20%bv) by (clear; in_regs); rewrite (GS4' 20%bv) by (clear; in_regs); rewrite (KEPT4 20%bv) by (clear; in_regs); rewrite (GS3' 20%bv) by (clear; in_regs); rewrite (KEPT3 20%bv) by (clear; in_regs); exact eq_refl).
    assert (S8_5 : getr R5 8%bv = getr R2 8%bv) by (rewrite (KEPT5 8%bv) by (clear; in_regs); rewrite (GS4' 8%bv) by (clear; in_regs); rewrite (KEPT4 8%bv) by (clear; in_regs); rewrite (GS3' 8%bv) by (clear; in_regs); rewrite (KEPT3 8%bv) by (clear; in_regs); exact eq_refl).
    assert (S9_5 : getr R5 9%bv = getr R2 9%bv) by (rewrite (KEPT5 9%bv) by (clear; in_regs); rewrite (GS4' 9%bv) by (clear; in_regs); rewrite (KEPT4 9%bv) by (clear; in_regs); rewrite (GS3' 9%bv) by (clear; in_regs); rewrite (KEPT3 9%bv) by (clear; in_regs); exact eq_refl).
    rewrite G18 in S18_5. rewrite G19 in S19_5. rewrite G20 in S20_5. rewrite G8 in S8_5. rewrite G9 in S9_5.

    pose (E5 := Eseed R5 [Z_to_bv 64 (sp - 672); Z_to_bv 64 p5; Z_to_bv 64 words; Z_to_bv 64 n; Z_to_bv 64 (2 ^ 64 - 100)]).
    assert (HR5 : regs_ok E5 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (9%bv, ELit 0); (18%bv, EVar 35); (19%bv, EVar 34); (20%bv, ELit 0); (21%bv, EVar 36)]) R5).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; try assumption.
      all: rewrite G21_5; apply bv_eq; vm_compute; reflexivity. }
    assert (HK5 : know_ok SEGS E5 M5 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 600); KRange (EVar 33) 1 (2 ^ 47); KRange (EVar 36) (2 ^ 64 - 100) (2 ^ 64 - 100)]).
    { pose proof (s_fdef _ _ _ _ _ WS5) as FD. rewrite Esp0 in FD. unfold PO_FRAME in FD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD | lia | lia] | lia | lia | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS5) as MS5.
    xruns HR5 HK5 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5'.
    rreg HRn (1%bv) G1_5. rreg HRn (2%bv) H2_5'. rreg HRn (10%bv) G10_5'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS5'.
    clear HRn HR5 HK5. fixregsN. rewrite ?w_add by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M5' := mm) in * end.
    assert (ST5 : stores_in (fun a => zwin (sp - 672 + 264) (sp - 672 + 288) a \/ zwin (sp - 672 + 360) (sp - 672 + 600) a) M5 M5') by (unfold M5'; stin).
    assert (WS5' : WS w [(p3, 500); (p4, 100); (p5, 100)] A5 M5' model5) by (eapply (ws_stores w _ A5 M5 M5' model5 _ WS5 ST5); rewrite Esp, Esp0; unfold zwin; intros; lia).
    assert (V5 : cell8 SEGS M5' (sp - 672 + 264) p5 /\ cell8 SEGS M5' (sp - 672 + 272) p5 /\ cell8 SEGS M5' (sp - 672 + 280) (p5 + 100)).
    { unfold cell8. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M5'; rdback]). }
    assert (TI5 : tinit (sp - 672) words n M5').
    { unfold tinit. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M5'; rdback]). }
    assert (AG5s : CRep.agree_on (fun a => sp - 672 <= a < sp /\ ~ (zwin (sp - 672 + 264) (sp - 672 + 288) a \/ zwin (sp - 672 + 360) (sp - 672 + 600) a)) M5 M5') by (eapply stores_in_agree; [exact ST5 | intros b Hb; unfold zwin in *; lia]).
    assert (PI5' : pinit (sp - 672) M5') by (eapply (pinit_agree _ M5 M5' PI5); [lia | lia | eapply agree_on_weaken; [exact AG5s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W3_5' : vtrip (sp - 672) 216 p3 500 M5') by (eapply (vtrip_agree _ _ _ _ M5 M5' W3_5); [lia | lia | eapply agree_on_weaken; [exact AG5s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W4_5' : vtrip (sp - 672) 240 p4 100 M5') by (eapply (vtrip_agree _ _ _ _ M5 M5' W4_5); [lia | lia | eapply agree_on_weaken; [exact AG5s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (VT5 : vtrip (sp - 672) 264 p5 100 M5') by (unfold vtrip; replace (sp - 672 + 264 + 8) with (sp - 672 + 272) by lia; replace (sp - 672 + 264 + 16) with (sp - 672 + 280) by lia; exact V5).
    pose proof (s_ms _ _ _ _ _ WS5') as MS5'. clearbody M5'. clear ST5.
    eapply (ws_new w _ A5 M5' model5 fx R5' 500 0x66b68 K WS5');
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

    assert (F8_6 : getr R6 8%bv = Z_to_bv 64 (sp - 672 + 304)) by (rewrite (KEPT6 8%bv) by (clear; in_regs); rewrite (GS5' 8%bv) by (clear; in_regs); exact S8_5).
    assert (F24_6 : getr R6 24%bv = getr (v_R0 w) 24%bv) by (rewrite (KEPT6 24%bv) by (clear; in_regs); rewrite (GS5' 24%bv) by (clear; in_regs); rewrite (KEPT5 24%bv) by (clear; in_regs); rewrite (GS4' 24%bv) by (clear; in_regs); rewrite (KEPT4 24%bv) by (clear; in_regs); rewrite (GS3' 24%bv) by (clear; in_regs); rewrite (KEPT3 24%bv) by (clear; in_regs); rewrite (GS2 24%bv) by (clear; in_regs); rewrite (GS1 24%bv) by (clear; in_regs); reflexivity).
    assert (F25_6 : getr R6 25%bv = getr (v_R0 w) 25%bv) by (rewrite (KEPT6 25%bv) by (clear; in_regs); rewrite (GS5' 25%bv) by (clear; in_regs); rewrite (KEPT5 25%bv) by (clear; in_regs); rewrite (GS4' 25%bv) by (clear; in_regs); rewrite (KEPT4 25%bv) by (clear; in_regs); rewrite (GS3' 25%bv) by (clear; in_regs); rewrite (KEPT3 25%bv) by (clear; in_regs); rewrite (GS2 25%bv) by (clear; in_regs); rewrite (GS1 25%bv) by (clear; in_regs); reflexivity).
    assert (F26_6 : getr R6 26%bv = getr (v_R0 w) 26%bv) by (rewrite (KEPT6 26%bv) by (clear; in_regs); rewrite (GS5' 26%bv) by (clear; in_regs); rewrite (KEPT5 26%bv) by (clear; in_regs); rewrite (GS4' 26%bv) by (clear; in_regs); rewrite (KEPT4 26%bv) by (clear; in_regs); rewrite (GS3' 26%bv) by (clear; in_regs); rewrite (KEPT3 26%bv) by (clear; in_regs); rewrite (GS2 26%bv) by (clear; in_regs); rewrite (GS1 26%bv) by (clear; in_regs); reflexivity).
    assert (F27_6 : getr R6 27%bv = getr (v_R0 w) 27%bv) by (rewrite (KEPT6 27%bv) by (clear; in_regs); rewrite (GS5' 27%bv) by (clear; in_regs); rewrite (KEPT5 27%bv) by (clear; in_regs); rewrite (GS4' 27%bv) by (clear; in_regs); rewrite (KEPT4 27%bv) by (clear; in_regs); rewrite (GS3' 27%bv) by (clear; in_regs); rewrite (KEPT3 27%bv) by (clear; in_regs); rewrite (GS2 27%bv) by (clear; in_regs); rewrite (GS1 27%bv) by (clear; in_regs); reflexivity).
    eapply (po_core2 w K fx A6 M6 model6 R6 p3 p4 p5 p6);
      [ exact POST | unfold POW; cbn [v_ret v_R0 v_sp0]; repeat (split; [first [exact Hret | lia | assumption] |]); exact Htp
      | exact BUD | exact HNM | exact AI | exact WOK | exact WWIN | exact FZ | exact WS6
      | exact PI6 | exact W3_6 | exact W4_6 | exact W5_6 | exact TI6 | lia | lia | lia | lia | lia
      | exact H2_6 | exact Qgp6 | exact Qtp6 | exact G10_6 | exact F8_6 | exact F24_6 | exact F25_6 | exact F26_6 | exact F27_6 ].
  Qed.

  Theorem binary_parse_U1 : binary_parse_stmt SEGS Ly.L MI ST kcU1.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL PM PO.
    unfold binary_parse_stmt, parse_opts_stmt. cbn [kc_po_stack kc_parse kcU1].
    intros fx A s R M model sp ret ctx env words n K CB ROC FZ Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 _ CTX CWIN Henv WOK WWIN BUD POST.
    pose proof ac_bounds_lit as Hcv.
    pose proof CB as CB0. destruct CB0 as [AI MS IRC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx]. destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    pose (E := Eseed R (@nil word)).
    assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
    assert (HK : know_ok SEGS E M []) by (apply Forall_nil).
    xruns HR HK 10%nat [0x6694c] (SCR [] [] []) 10%N. { split_scs; try sc_auto1. }
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
