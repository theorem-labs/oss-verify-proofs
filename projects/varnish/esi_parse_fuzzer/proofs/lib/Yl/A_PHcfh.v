(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac AIcpm9j AIcpghc AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Vsb A_World A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PMark.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.

Module A_PHdsh.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac AIcpm9j AIcpghc AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Vsb A_World A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PMark.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@VEPlo; @Hk; @TAG; @Dlo; @WL; @DLEN; @FRB; @G2; @LQ; @ACV; @EE; @NN; @VERP; @Ha; @KS; @PLT; @SZ; @SR; @VEPhi; @DJ_VD; @DJfV; @DJfD; @H; @OUT; @H2; @H3; @PLT0; @PLEc; @ACV__; @K1; @Kb; @K0])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_NotMyTag : handler_stmt S_NotMyTag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    pose proof PLT as PLT0.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + 1) by (unfold phi, rank; rewrite ST; reflexivity).
    destruct (data_shadow A m md _ _ AINV DATA) as [SHD D16]. fold_cl_segs. fold_aview.
    pose proof (shpat_sh_boundL (Clg:=Clg) (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(lia) ltac:(lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
    (* [comment removed for export] *)
    assert (TAIL : forall (xc : pst) (mc : mem) (mdc : Model) (ra' a0' a1' a2' a3' a4' a5' a6' s2' s5' s11' t4' t5' t6' : word),
      pinv E xc A (aview A mc) -> ainv A mc mdc -> amd_frame (pe_md0 E) mdc ->
      (x_st xc = S_NotMyTag \/ x_st xc = S_NxtTag) -> (x_p xc < pe_e E -> phi E xc < phi E x) ->
      srealizes rsegs (mkCfg (loop_ms E 0x8bf44 (x_p xc) (S8 E) ra' a0' a1' a2' a3' a4' a5' a6' s2' s5' s11' t4' t5' t6' mc) mdc) T).
    { intros until t6'. intros PIc AINVc MDFc STc PHIc.
      clear - HMC PE KL PIc AINVc MDFc STc PHIc; try pose proof alloc_ceiling_val as ACV__.
      assert (NMB : x_st xc <> S_MatchBuf) by (destruct STc as [X|X]; rewrite X; discriminate).
      pose proof PIc as PIc0. pose proof (pi_pe _ _ _ _ PIc) as PLEc.
      world_open PE PIc AINVc. unfold loop_ms. rewrite EFP in *.
      hide_neqs.
      ago AINVc. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        astop0 AINVc.
        eapply (KL xc A _ _); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]|].
        intros H. split; [exact (PHIc H)| exact NMB]. }
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0.
      zstep. destruct B_rm as [RM|RM]; rewrite RM, sx32_small by (clear; lia).
      2:{ (* [comment removed for export] *)
          zstep. if_cases K1; zify_cond K1. 2:{ exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val as ACV__; rewrite ?unsigned_lit in K1 by (clear; lia); lia. } clear K1.
          astop0 AINVc.
          eapply (KL xc A _ _); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]|].
          intros H. exfalso. try (generalize alloc_ceiling_val); clear - H K0; try pose proof alloc_ceiling_val as ACV__. lia. }
      zstep. if_cases K1; zify_cond K1. { exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val as ACV__; rewrite ?unsigned_lit in K1 by (clear; lia); lia. } clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      astop0 AINVc.
      eapply (mark_call HMC E xc A _ _ T (x_p xc) (x_p xc) 0 0x8bf78);
        [ exact PE | exact PIc0 | assumption | eapply amd_frame_sbm_r; [exact MDFc | exact SBM]
        | clear; lia | exact PLEc | left; reflexivity | clear; lia | reflexivity
        | intros [X|X]; destruct STc as [Y|Y]; rewrite Y in X; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (ST1 : x_st x1 = x_st xc) by (rewrite EX1; reflexivity).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      assert (EPc : x_p x1 = pe_e E) by (rewrite EP1; exact K0).
      assert (NMB1 : x_st x1 <> S_MatchBuf) by (rewrite ST1; exact NMB).
      clear - HMC PE KL PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EP1 EPc NMB1; try pose proof alloc_ceiling_val as ACV__.
      world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *. rewrite <- EP1.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      hide_neqs.
      ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      astop AINV1 MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x1) (x_st x1) (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
        all: rewrite ?ST1; try assumption.
        + exact (conj DELIM1 DELIM2).
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
      - psimp. rewrite EPc. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val as ACV__. lia. }
    (* [comment removed for export] *)
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 1 0.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (rw_cells_read_sub rsegs mx _ _ 4 1 VEPC ltac:(clear; lia) ltac:(cbn; clear; lia)) as RDF end.
    match type of RDF with _ = Some ?r => change r with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x Fflags)))] in RDF end.
    remember (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x Fflags)))) as fb eqn:Efb in RDF.
    set (RWv := rw_cells rsegs _ (pe_VEP E)) in VEPC.
    zstep. subst RWv. clear RDF. cbv beta.
    zstep. zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      zstep. vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
      astop AINV MU WM CFP. fold_cl_segs.
      set (xa := PST (x_p x + 1) S_NxtTag (fupd (x_v x) Fstate (vi_st VIA S_NxtTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIa : pinv E xa A (aview A mr)) end.
      { subst xa. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__. lia.
        + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val as ACV__. lia.
        + (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
      eapply (TAIL xa); [exact PIa| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| right; reflexivity|].
      subst xa. intros _. rewrite PHI. unfold phi, rank; psimp. clear. lia.
    - (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0. zstep. zstep.
      lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mc _) =>
      assert (LOOP : forall (k : nat) (q : Z) (ra' a1' a2' a3' a4' a5' a6' s2' s5' s11' t4' t5' t6' : word),
                q + Z.of_nat k = pe_e E -> x_p x <= q -> q <= pe_e E ->
                evt rsegs P (loop_ms E 0x8bc84 q (S8 E) ra' (Z_to_bv 64 q) a1' a2' a3' a4' a5' a6' s2' s5' s11' t4' t5' t6' mc))
      end.
      { induction k as [|k IH]; intros until t6'; intros Hk LQ QE; unfold loop_ms, S8.
        - (* [comment removed for export] *)
          zstep. if_cases Kb; zify_cond Kb. 2:{ exfalso. try (generalize alloc_ceiling_val); clear - Kb Hk; try pose proof alloc_ceiling_val as ACV__. lia. }
          astop AINV MU WM CFP. fold_cl_segs.
          set (xq := PST q S_NotMyTag (fupd (x_v x) Ftag_i 0) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
          lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIq : pinv E xq A (aview A mr)) end.
          { subst xq. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
            + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ; try pose proof alloc_ceiling_val as ACV__. lia.
            + (* [comment removed for export] *) clear. lia.
            + (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
            + (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
            + (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
            + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
          eapply (TAIL xq); [exact PIq| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| left; reflexivity|].
          subst xq. cbn [x_p]. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H Hk; try pose proof alloc_ceiling_val as ACV__. lia.
        - zstep. if_cases Kb; zify_cond Kb. { exfalso. try (generalize alloc_ceiling_val); clear - Kb Hk; try pose proof alloc_ceiling_val as ACV__. lia. } clear Kb.
          (* [comment removed for export] *)
          shadow_chk SHD 1 12.
          (* [comment removed for export] *)
          destruct (payload_read rsegs E _ q DBY ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia)) as (b & Hnth & RDP).
          pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
          zstep. clear RDP. cbv beta.
          zstep. zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
          + (* [comment removed for export] *)
            eapply (IH (q + 1)); [try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia].
          + (* [comment removed for export] *)
            zstep. vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
            astop AINV MU WM CFP. fold_cl_segs.
            set (xg := PST (q + 1) S_NxtTag (fupd (fupd (x_v x) Ftag_i 0) Fstate (vi_st VIA S_NxtTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
            lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIg : pinv E xg A (aview A mr)) end.
            { subst xg. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
              * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ; try pose proof alloc_ceiling_val as ACV__. lia.
              * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__. lia.
              * (* [comment removed for export] *) clear. lia.
              * (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
              * (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
              * (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
              * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
            eapply (TAIL xg); [exact PIg| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| right; reflexivity|].
            subst xg. intros _. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__. lia. }
      eapply (LOOP (Z.to_nat (pe_e E - x_p x)) (x_p x)); [try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val as ACV__; rewrite Z2Nat.id by lia; lia| clear; lia| try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val as ACV__; lia].
  Qed.
End S.
End A_PHdsh.

Module A_PHklh.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac AIcpm9j AIcpghc AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Vsb A_World A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PMark.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Ltac icall_consts_in H ::= unfold vep_error_post, VEPERR_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HVE : vep_error_stmt.

  #[using="HVE"] Lemma PH_SkipAttribute : handler_stmt S_SkipAttribute.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_sp E - 304 - 64, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_sp E - 304 - 64, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_sp E - 304 - 64, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    assert (WZh : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                          [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    pose proof (cenv_intro A m md AINV) as CE. fold_aview.
    (first [ dand4 HENV as _ GLOB HOBJ HSH | destruct HENV as (_ & GLOB & HOBJ & HSH) ]).
    assert (SHVD : shadowed LPA (aview A m) (pe_VEP E) 312).
    { exists (pe_VEP E), 312. split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|].
      split; [try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia|]. try (generalize alloc_ceiling_val); clear - VEPlo VEPhi; try pose proof alloc_ceiling_val. lia. }
    assert (KHV : kHighMemBeg <= pe_VEP E) by (unfold kHighMemBeg; try (generalize alloc_ceiling_val); clear - VEPlo; try pose proof alloc_ceiling_val; lia).
    assert (M8V : pe_VEP E mod 8 = 0) by (try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia).
    assert (DJV : h_ff (pe_H E) + HFSIZE <= pe_VEP E \/ pe_VEP E + 312 <= h_ff (pe_H E)) by (unhide_djf; unfold HFSIZE; try (generalize alloc_ceiling_val); clear - DJfV; try pose proof alloc_ceiling_val; lia).
    assert (EVSC : h_vsc (pe_H E) = h_ff (pe_H E) + 32) by reflexivity. unfold kHighMemBeg in G2. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) (h_ff (pe_H E)) 8192 ltac:(try (generalize alloc_ceiling_val); clear -G2; try pose proof alloc_ceiling_val; lia) ltac:(clear; lia) G3) as SHFB. rewrite SHMAX_val in SHFB.
    destruct (data_shadow A m md _ _ AINV DATA) as [SHD D16]. fold_cl_segs. fold_aview.
    pose proof (shpat_sh_boundL (Clg:=Clg) (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(lia) ltac:(lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
    pose proof (got_vct_cell _ (consts_hold_ainv LPA A m md AINV)) as GOTV. pose proof (vct_shadowA _ (consts_hold_ainv LPA A m md AINV)) as VSH. fold_cl_segs. fold_aview.
    unfold GOTA_vct, VCT_TYPTABA in GOTV. unfold VCT_TYPTABA in VSH.
    assert (VSHB : 0 <= sh 148832 /\ sh 148832 + Z.of_nat (length (repeat (Z_to_bv 8 0) 64)) <= 17594064011264).
    { unfold sh. rewrite kShadowOffset_val. change (148832 / 8) with 18604. change (Z.of_nat (length (repeat (Z_to_bv 8 0) 64))) with 64. clear; lia. }
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ ?P _ =>
    assert (INTAG : forall (q' : Z) (b : byte) (ra' a0' a1' a2' a3' a4' a5' a6' t4' t5' t6' : word),
      x_p x <= q' -> q' < pe_e E -> nth_error (pe_inp E) (Z.to_nat (q' - pe_DATA E)) = Some b -> vct_xmlname (bv_unsigned b) = false ->
      evt rsegs P (loop_ms E 0x8d3bc q' (S8 E) ra' a0' a1' a2' a3' a4' a5' a6' (Z_to_bv 64 (vi_st VIA S_NxtTag)) (Z_to_bv 64 (vi_st VIA S_TagError))
                          (Z_to_bv 64 (vi_st VIA S_InTag)) t4' t5' t6' (aview A m)));
    [| assert (EXIT_T : forall (q' : Z) (b : byte) (ra' a0' a3' a4' a5' a6' t4' t5' t6' : word),
      x_p x <= q' -> q' < pe_e E -> nth_error (pe_inp E) (Z.to_nat (q' - pe_DATA E)) = Some b -> vct_xmlname (bv_unsigned b) = false ->
      evt rsegs P (loop_ms E 0x8ce40 q' (S8 E) ra' a0' (Z_to_bv 64 (vct (bv_unsigned b))) (Z_to_bv 64 (bv_unsigned b)) a3' a4' a5' a6'
                          (Z_to_bv 64 (vi_st VIA S_NxtTag)) (Z_to_bv 64 (vi_st VIA S_TagError)) (Z_to_bv 64 (vi_st VIA S_InTag)) t4' t5' t6' (aview A m)));
       [| assert (LOOP : forall (k : nat) (q : Z) (ra' a1' a2' a3' a4' a5' a6' t4' t5' t6' : word),
      q + Z.of_nat k = pe_e E -> x_p x <= q -> q < pe_e E ->
      evt rsegs P (loop_ms E 0x8cac4 q (S8 E) ra' (Z_to_bv 64 q) a1' a2' a3' a4' a5' a6'
                          (Z_to_bv 64 (vi_st VIA S_NxtTag)) (Z_to_bv 64 (vi_st VIA S_TagError)) (Z_to_bv 64 (vi_st VIA S_InTag)) t4' t5' t6' (aview A m))) ]]
    end.
    { intros until t6'. intros LQ QE Hnth NX. unfold loop_ms, S8. rewrite EFP. cbn [vi_st VIA stA].
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MUh. pose proof (wmono_refl rsegs (aview A m)) as WMh.
      zstep. zstep.
      astop AINV MU WM CFP. fold_cl_segs.
      eapply (KL (PST q' S_InTag (fupd (x_v x) Fstate (vi_st VIA S_InTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ; try pose proof alloc_ceiling_val. lia.
      + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - QE; try pose proof alloc_ceiling_val. lia.
      + (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
      + (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
      + (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) eapply (henv_stores _ _ _ _ _ _ _ PE0 AINV HFR MUh WMh WZh); [intros a__ Ha__; cbn [outside]; unhide_djf; unfold h_vsc, pe_fp, PARSE_FRAME in *; first [clear - Ha__ DJfV DJfS DJfB DJfD; lia | lia]| split; [exact HFR| split; [exact GLOB| split; [exact HOBJ| exact HSH]]]].
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
      - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST.
        destruct (Z.eq_dec q' (x_p x)) as [EQ|NE].
        * unfold look. rewrite <- EQ, Hnth, NX. try (generalize alloc_ceiling_val); clear - EQ; try pose proof alloc_ceiling_val. lia.
        * destruct (vct_xmlname (look E x)); try (generalize alloc_ceiling_val); clear - NE LQ QE; try pose proof alloc_ceiling_val; lia.
 }
    { intros until t6'. intros LQ QE Hnth NX. unfold loop_ms, S8. rewrite EFP. cbn [vi_st VIA stA].
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      pose proof (vct_range (bv_unsigned b)) as VR.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1.
      { vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. eapply (INTAG q' b); [exact LQ| exact QE| exact Hnth| exact NX]. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases K2; zify_cond K2.
      { vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. eapply (INTAG q' b); [exact LQ| exact QE| exact Hnth| exact NX]. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases K3; zify_cond K3.
      - (* [comment removed for export] *)
        zstep. zstep. if_cases K4; zify_cond K4.
        { vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. eapply (INTAG q' b); [exact LQ| exact QE| exact Hnth| exact NX]. }
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        unhide DJfV.
        try clear VSH. try clear DBY. icall (HVE (pe_VEP E) (fupd (x_v x) Fstate (stA (x_st x))) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by
          (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - FRB; try pose proof alloc_ceiling_val; lia);
           first [ reflexivity | exact VEPC | exact TAG | exact PADS | exact (proj1 BASE) | exact GLOB | exact HOBJ | exact HSH | exact HG
                 | exact CE | exact SHVD | exact KHV | exact M8V | exact VEPhi | exact DJV | exact STK | exact CEIL | exact MI
                 | unfold VEPERR_STACK; try (generalize alloc_ceiling_val); clear - LOP; try pose proof alloc_ceiling_val; lia ]).
        hide DJfV.
        lazymatch goal with X : glob_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into GLOB1 end.
        lazymatch goal with X : hobj_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into HOBJ1 end.
        lazymatch goal with X : stk _ ?v _ _ |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into STK end.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
          assert (HENV1 : henv_ok LPA VIA (pe_H E) A v)
            by (split; [exact HFR| split; [exact GLOB1| split; [exact HOBJ1|]]];
                eapply hshadow_munch; [exact HSH| exact MU| exact HG|];
                intros a__ Ha__; unfold HFSIZE in Ha__; change (8192 / 8) with 1024 in Ha__; cbn [outside]; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo LOP CEIL ACV EVSC G2; try pose proof alloc_ceiling_val; lia);
          pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] v) as MU2; pose proof (wmono_refl rsegs v) as WM2
        end.
        (* [comment removed for export] *)
        vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
          assert (HENV2 : henv_ok LPA VIA (pe_H E) A v)
            by (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
                intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
                cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi ACV EVSC G2 DJfV; try pose proof alloc_ceiling_val; lia)
        end.
        clear HENV1.
        astop AINV MU WM CFP. fold_cl_segs.
        eapply (KL (PST q' S_TagError (fupd (x_v x) Fstate (vi_st VIA S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
        + apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ; try pose proof alloc_ceiling_val. lia.
        * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - QE; try pose proof alloc_ceiling_val. lia.
        * (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
        * (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
        * (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
          * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
        + assumption.
        + eapply amd_frame_sbm_r; [exact MDF | exact SBM].
        + (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST.
          destruct (Z.eq_dec q' (x_p x)) as [EQ|NE].
          -- unfold look. rewrite <- EQ, Hnth, NX. try (generalize alloc_ceiling_val); clear - EQ; try pose proof alloc_ceiling_val. lia.
          -- destruct (vct_xmlname (look E x)); try (generalize alloc_ceiling_val); clear - NE LQ QE; try pose proof alloc_ceiling_val; lia.
      - (* [comment removed for export] *)
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MUh. pose proof (wmono_refl rsegs (aview A m)) as WMh.
        vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep.
        astop AINV MU WM CFP. fold_cl_segs.
        eapply (KL (PST (q' + 1) S_AttrDelim (fupd (x_v x) Fstate (vi_st VIA S_AttrDelim)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
        + apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ; try pose proof alloc_ceiling_val. lia.
        * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - QE; try pose proof alloc_ceiling_val. lia.
        * (* [comment removed for export] *)
          intros _ [X|X]; [discriminate X|]. exfalso; apply X. revert VA AVSB; clear; destruct (x_va x); [| reflexivity].
          intros VA AVSB. exfalso. exact (AVSB (proj1 VA)).
        * (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
        * (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
        * (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
          * (* [comment removed for export] *) eapply (henv_stores _ _ _ _ _ _ _ PE0 AINV HFR MUh WMh WZh); [intros a__ Ha__; cbn [outside]; unhide_djf; unfold h_vsc, pe_fp, PARSE_FRAME in *; first [clear - Ha__ DJfV DJfS DJfB DJfD; lia | lia]| split; [exact HFR| split; [exact GLOB| split; [exact HOBJ| exact HSH]]]].
          * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
        + assumption.
        + eapply amd_frame_sbm_r; [exact MDF | exact SBM].
        + (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST.
          destruct (vct_xmlname (look E x)); try (generalize alloc_ceiling_val); clear - LQ QE; try pose proof alloc_ceiling_val; lia.
 }
    { induction k as [|k IH]; intros until t6'; intros Hk LQ QE.
      { exfalso. try (generalize alloc_ceiling_val); clear - Hk QE; try pose proof alloc_ceiling_val. lia. }
      unfold loop_ms, S8. rewrite EFP. cbn [vi_st VIA stA].
      (* [comment removed for export] *)
      shadow_chk SHD 1 12.
      (* [comment removed for export] *)
      (first [ pose proof ((payload_read rsegs E _ q DBY ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val; lia) QE)) as dR_2; dex1 dR_2 as b; destruct dR_2 as [Hnth RDP] | pose proof ((payload_read rsegs E _ q DBY ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val; lia) QE)) as dR_2; dand3 dR_2 as b Hnth RDP | destruct (payload_read rsegs E _ q DBY ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val; lia) QE) as (b & Hnth & RDP) ]).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
      (* [comment removed for export] *)
      zstep. zstep. shadow_addr VSH 2. zstep. lit0. chk_branch.
      (* [comment removed for export] *)
      pose proof (vct_readA _ (bv_unsigned b) _ MI BR eq_refl) as RDV. unfold wa, VCT_TYPTABA in RDV.
      zstep. clear RDV. cbv beta. rewrite zx16_vct.
      pose proof (vct_range (bv_unsigned b)) as VR.
      zstep. zstep. if_cases K1; zify_cond K1.
      { eapply (EXIT_T q b); [exact LQ| exact QE| exact Hnth| unfold vct_xmlname; rewrite K1; reflexivity]. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      - eapply (IH (q + 1)); [try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - K2 Hk QE; try pose proof alloc_ceiling_val; lia].
      - (* [comment removed for export] *)
        zstep. zstep. zstep.
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MUh. pose proof (wmono_refl rsegs (aview A m)) as WMh.
        assert (PIe : pinv E (PST (pe_e E) S_SkipAttribute (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A (aview A m)).
        { apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUh WMh WZh.
          * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP PLT; try pose proof alloc_ceiling_val. lia.
          * (* [comment removed for export] *) revert OUT PLT. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
          * (* [comment removed for export] *) revert VA PLT. clear. cbn [x_va x_v x_p x_vv]. destruct (x_va x); [| intros X _; exact X]. ((first [ intro dR_3; dand5 dR_3 as H1 H2 H3 H4 H5 | intros (H1 & H2 & H3 & H4 & H5) ]); intros PLT). refine (conj H1 (conj H2 (conj H3 (conj _ H5)))). lia.
          * (* [comment removed for export] *) revert VI PLT. clear. cbn [x_vi x_va x_v x_p x_vv]. destruct (x_vi x); [| intros X _; exact X]. ((first [ intro dR_4; dand7 dR_4 as H1 H2 H3 H4 H5 H6 H7 | intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) ]); intros PLT). refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ (conj H6 H7)))))). lia.
          * (* [comment removed for export] *) split; [exact HFR| split; [exact GLOB| split; [exact HOBJ| exact HSH]]]. }
        astop0 AINV.
        eapply (KL (PST (pe_e E) S_SkipAttribute (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _);
          [exact PIe| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| psimp; intros H; exfalso; try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val; lia]. }
    (* [comment removed for export] *)
    zstep; if_cases K0; zify_cond K0; try (exfalso; try (generalize alloc_ceiling_val); clear - K0 PLT; try pose proof alloc_ceiling_val; lia); [].
    zstep.
    eapply (LOOP (Z.to_nat (pe_e E - x_p x)) (x_p x)); [try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val; rewrite Z2Nat.id by lia; lia| clear; lia| exact PLT].
  Qed.
End S.
End A_PHklh.

Module A_PHucc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac AIcpm9j AIcpghc AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Vsb A_World A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PMark.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot_lia_prev := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)



(* [comment removed for export] *)
Definition until_byte (U j : Z) : Z :=
  if U =? LIT_arrow then (if j =? 0 then 45 else if j =? 1 then 45 else if j =? 2 then 62 else 0)
  else (if j =? 0 then 93 else if j =? 1 then 93 else if j =? 2 then 62 else 0).

Lemma until_read : forall m U j, mem_inv rsegs m -> (U = LIT_arrow \/ U = LIT_cdata_end) -> 0 <= j <= 3 ->
  ov_read_bytes rsegs m (wa (U + j)) 1 = Some [Z_to_bv 8 (until_byte U j)].
Proof.
  intros m U j MI HU Hj.
  assert (B : bytes_at rsegs m U [Z_to_bv 8 (until_byte U 0); Z_to_bv 8 (until_byte U 1); Z_to_bv 8 (until_byte U 2); Z_to_bv 8 (until_byte U 3)]).
  { apply (ro_bytes_at rsegs m); [exact MI| | |].
    - destruct HU as [-> | ->]; unfold LIT_arrow, LIT_cdata_end; cbn; lia.
    - cbn [length]. destruct HU as [-> | ->]; unfold LIT_arrow, LIT_cdata_end; cbn; lia.
    - apply ro_bytes_b_sound. destruct HU as [-> | ->]; vm_compute; reflexivity. }
  eapply (u8ro_read rsegs m U _ j); [exact B| | lia| reflexivity].
  assert (X : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
  destruct X as [-> |[-> |[-> | ->]]]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma until_byte_3 : forall U, until_byte U 3 = 0.
Proof. intros U. unfold until_byte. destruct (U =? LIT_arrow); reflexivity. Qed.
Lemma until_byte_range : forall U j, 0 <= until_byte U j < 256.
Proof.
  intros U j. unfold until_byte.
  destruct (U =? LIT_arrow); destruct (j =? 0); destruct (j =? 1); destruct (j =? 2); lia.
Qed.
Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma until_shadow : forall v U, consts_hold LPA v -> (U = LIT_arrow \/ U = LIT_cdata_end) ->
  bytes_at rsegs v (sh U) (shpat 4) /\ U mod 8 = 0 /\ 0x23040 <= U <= 0x23120 /\ (0 <= sh U /\ sh U + Z.of_nat (length (shpat 4)) <= 17594064011264).
Proof.
  intros v U CH HU. destruct HU as [-> | ->]; unfold LIT_arrow, LIT_cdata_end; cbn [vi_arrow vi_cdata_end VIA].
  - split; [apply (global_shadow_pat v 0x23040 4 32 CH); gdesc_in|]. split; [reflexivity|]. split; [lia| change (Z.of_nat (length (shpat 4))) with 1; unfold sh; rewrite kShadowOffset_val; change (0x23040 / 8) with 17928; lia].
  - split; [apply (global_shadow_pat v 0x23120 4 32 CH); gdesc_in|]. split; [reflexivity|]. split; [lia| change (Z.of_nat (length (shpat 4))) with 1; unfold sh; rewrite kShadowOffset_val; change (0x23120 / 8) with 17956; lia].
Qed.

End CEIL.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_Until : handler_stmt S_Until.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    pose proof PLT as PLT0.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + 1) by (unfold phi, rank; rewrite ST; reflexivity).
    destruct (UNTL eq_refl) as (HU & UP & US).
    destruct (data_shadow A m md _ _ AINV DATA) as [SHD D16]. fold_cl_segs. fold_aview.
    pose proof (shpat_sh_boundL (Clg:=Clg) (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(lia) ltac:(lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
    destruct (until_shadow _ (x_v x Funtil) (consts_hold_ainv LPA A m md AINV) HU) as (SHU & U8 & UB & SHUB). fold_cl_segs. fold_aview.
    (* [comment removed for export] *)
    assert (TAIL : forall (xc : pst) (mc : mem) (mdc : Model) (ra' a0' a1' a2' a3' a4' a5' a6' s2' s5' s11' t4' t5' t6' : word),
      pinv E xc A (aview A mc) -> ainv A mc mdc -> amd_frame (pe_md0 E) mdc ->
      (x_st xc = S_Until \/ x_st xc = S_NxtTag) -> (x_p xc < pe_e E -> phi E xc < phi E x) ->
      srealizes rsegs (mkCfg (loop_ms E 0x8d3f8 (x_p xc) (S8 E) ra' a0' a1' a2' a3' a4' a5' a6' s2' s5' s11' t4' t5' t6' mc) mdc) T).
    { intros until t6'. intros PIc AINVc MDFc STc PHIc.
      clear - HMC PE KL PIc AINVc MDFc STc PHIc; try pose proof alloc_ceiling_val as ACV__.
      assert (NMB : x_st xc <> S_MatchBuf) by (destruct STc as [X|X]; rewrite X; discriminate).
      pose proof PIc as PIc0. pose proof (pi_pe _ _ _ _ PIc) as PLEc.
      world_open PE PIc AINVc. unfold loop_ms. rewrite EFP in *.
      hide_neqs.
      ago AINVc. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0.
      { astop0 AINVc.
        eapply (KL xc A _ _); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]|].
        intros H. split; [exact (PHIc H)| exact NMB]. }
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0.
      zstep. destruct B_rm as [RM|RM]; rewrite RM, sx32_small by (clear; lia).
      all: zstep; if_cases K1; zify_cond K1; try (exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val as ACV__; rewrite ?unsigned_lit in K1 by (clear; lia); lia); clear K1.
      2:{ (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep. zstep. zstep.
          astop0 AINVc.
          eapply (KL xc A _ _); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]|].
          intros H. exfalso. try (generalize alloc_ceiling_val); clear - H K0; try pose proof alloc_ceiling_val as ACV__. lia. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      astop0 AINVc.
      eapply (mark_call HMC E xc A _ _ T (x_p xc) (x_p xc) 0 0x8d42c);
        [ exact PE | exact PIc0 | assumption | eapply amd_frame_sbm_r; [exact MDFc | exact SBM]
        | clear; lia | exact PLEc | left; reflexivity | clear; lia | reflexivity
        | intros [X|X]; destruct STc as [Y|Y]; rewrite Y in X; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (ST1 : x_st x1 = x_st xc) by (rewrite EX1; reflexivity).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      assert (EPc : x_p x1 = pe_e E) by (rewrite EP1; exact K0).
      assert (NMB1 : x_st x1 <> S_MatchBuf) by (rewrite ST1; exact NMB).
      clear - HMC PE KL PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EP1 EPc NMB1; try pose proof alloc_ceiling_val as ACV__.
      world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *. rewrite <- EP1.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      hide_neqs.
      ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      astop AINV1 MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x1) (x_st x1) (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
        all: rewrite ?ST1; try assumption.
        + exact (conj DELIM1 DELIM2).
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
      - psimp. rewrite EPc. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val as ACV__. lia. }
    (* [comment removed for export] *)
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ _ _) _) _ => idtac end.
    hide_neqs.
    ago AINV. fold_cl_segs.
    lazymatch goal with |- evt _ ?P _ =>
    assert (ULOOP : forall (k : nat) (q u : Z) (ra' a2' a4' a5' a6' s2' s5' s11' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312)] (aview A m) mc -> wmono rsegs (aview A m) mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (fupd (fupd (x_v x) Funtil_p u) Fstate (stA (x_st x))) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E - 304) (pframe E j0 j8) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) -> stk rsegs mc (pe_lo E) (pe_sp E - 304) ->
      bytes_at rsegs mc (sh (pe_VEP E)) zsV -> bytes_at rsegs mc (sh (pe_DATA E)) (shpat (Z.of_nat (length (pe_inp E)))) ->
      bytes_at rsegs mc (sh (x_v x Funtil)) (shpat 4) ->
      q + Z.of_nat k = pe_e E -> x_p x <= q -> q < pe_e E -> x_v x Funtil <= u <= x_v x Funtil + 2 ->
      evt rsegs P (loop_ms E 0x8b9e8 (q + 1) (S8 E) ra' (Z_to_bv 64 q) (Z_to_bv 64 u) a2'
                          (Z_to_bv 64 ((pe_VEP E + 176) / 8 + 2147450880)) a4' a5' a6' s2' s5' s11' t4' t5' t6' mc))
    end.
    { induction k as [|k IH]; intros until mc; intros MUc WMc MIc VEPCc FRc DBYc STKc SHVc SHDc SHUc Hk LQ QE HUR.
      { exfalso. try (generalize alloc_ceiling_val); clear - Hk QE; try pose proof alloc_ceiling_val as ACV__. lia. }
      unfold loop_ms, S8. rewrite EFP.
      clear VEPC FR DBY STK MI SHV0 SHD SHU MU WM.
      unfold vep_cells in VEPCc. psimp_in VEPCc. unfold pframe in FRc. cbv zeta in FRc.
      (* [comment removed for export] *)
      shadow_chk SHDc 1 14.
      (* [comment removed for export] *)
      vrechk SHVc EzsV (pe_VEP E + 176) 8 0.
      (* [comment removed for export] *)
      destruct (payload_read rsegs E _ q DBYc ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val as ACV__; lia) QE) as (b & Hnth & RDP).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      rewrite (shr3_div8 u). shadow_rechk SHUc u 1 16.
      (* [comment removed for export] *)
      lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
        pose proof (until_read mcur (x_v x Funtil) (u - x_v x Funtil) MIx HU ltac:(try (generalize alloc_ceiling_val); clear - HUR; try pose proof alloc_ceiling_val as ACV__; lia)) as RDU end.
      replace (wa (x_v x Funtil + (u - x_v x Funtil))) with (Z_to_bv 64 u) in RDU by (unfold wa; f_equal; clear; lia).
      pose proof (until_byte_range (x_v x Funtil) (u - x_v x Funtil)) as UBR.
      remember (until_byte (x_v x Funtil) (u - x_v x Funtil)) as ub eqn:Eub in RDU, UBR.
      zstep. clear RDU. cbv beta. rewrite (unsigned_lit8 ub UBR).
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      - (* [comment removed for export] *)
        vchk SHVc EzsV 8 0. vrechk SHVc EzsV (pe_VEP E + 176) 8 0. zstep. zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3.
        + replace (q + 1 + 1) with (q + 1 + 1) by reflexivity. try replace (q + 2) with (q + 1 + 1) by (clear; lia).
          lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
            eapply (IH (q + 1) (x_v x Funtil)); [exact MUc| exact WMc| exact MIx| unfold vep_cells; psimp; exact VEPCc| exact FRc| exact DBYc| exact STKc
                                  | exact SHVc| exact SHDc| exact SHUc| try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - K3 Hk QE; try pose proof alloc_ceiling_val as ACV__; lia| clear; lia] end.
        + (* [comment removed for export] *)
          zstep. zstep. zstep.
          astop AINV MUc WMc CFP. fold_cl_segs.
          set (xc := PST (pe_e E) S_Until (fupd (x_v x) Funtil_p (x_v x Funtil)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
          lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIc : pinv E xc A (aview A mr)) end.
          { subst xc. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUc WMc WZ.
            + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ QE; try pose proof alloc_ceiling_val as ACV__. lia.
            + (* [comment removed for export] *) intros _. refine (conj HU (conj _ US)). first [try (generalize alloc_ceiling_val); clear - HUR'; try pose proof alloc_ceiling_val as ACV__; lia | try (generalize alloc_ceiling_val); clear - HUR; try pose proof alloc_ceiling_val as ACV__; lia].
            + (* [comment removed for export] *) revert OUT LQ QE. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
            + (* [comment removed for export] *) world_close PE0 AINV HFR MUc WMc WZ.
            + (* [comment removed for export] *) world_close PE0 AINV HFR MUc WMc WZ.
            + (* [comment removed for export] *) cf_stores CF MUc PE0 STKc FRc. left; left. unfold blk. lia. }
          eapply (TAIL xc); [exact PIc| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| left; reflexivity|].
          subst xc. cbn [x_p]. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val as ACV__. lia.
      - (* [comment removed for export] *)
        shadow_chk SHUc 1 14.
        lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
          pose proof (until_read mcur (x_v x Funtil) (u + 1 - x_v x Funtil) MIx HU ltac:(try (generalize alloc_ceiling_val); clear - HUR; try pose proof alloc_ceiling_val as ACV__; lia)) as RDU2 end.
        replace (wa (x_v x Funtil + (u + 1 - x_v x Funtil))) with (Z_to_bv 64 (u + 1)) in RDU2 by (unfold wa; f_equal; clear; lia).
        pose proof (until_byte_range (x_v x Funtil) (u + 1 - x_v x Funtil)) as UBR2.
        remember (until_byte (x_v x Funtil) (u + 1 - x_v x Funtil)) as ub2 eqn:Eub2 in RDU2, UBR2.
        zstep. clear RDU2. cbv beta. rewrite (unsigned_lit8 ub2 UBR2).
        zstep. if_cases K2; zify_cond K2.
        + (* [comment removed for export] *)
          assert (HUR' : x_v x Funtil <= u + 1 <= x_v x Funtil + 2).
          { destruct (Z.eq_dec (u + 1 - x_v x Funtil) 3) as [EQ3|NEQ3]; [| try (generalize alloc_ceiling_val); clear - HUR NEQ3; try pose proof alloc_ceiling_val as ACV__; lia].
            exfalso. apply K2. rewrite Eub2, EQ3. apply until_byte_3. }
          zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3.
          * try replace (q + 2) with (q + 1 + 1) by (clear; lia).
            lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
              eapply (IH (q + 1) (u + 1)); [exact MUc| exact WMc| exact MIx| unfold vep_cells; psimp; exact VEPCc| exact FRc| exact DBYc| exact STKc
                                          | exact SHVc| exact SHDc| exact SHUc| try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - K3 Hk QE; try pose proof alloc_ceiling_val as ACV__; lia| exact HUR'] end.
          * (* [comment removed for export] *)
            zstep. zstep. zstep.
            astop AINV MUc WMc CFP. fold_cl_segs.
            set (xc := PST (pe_e E) S_Until (fupd (x_v x) Funtil_p (u + 1)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
            lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIc : pinv E xc A (aview A mr)) end.
            { subst xc. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUc WMc WZ.
              + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ QE; try pose proof alloc_ceiling_val as ACV__. lia.
              + (* [comment removed for export] *) intros _. refine (conj HU (conj _ US)). first [try (generalize alloc_ceiling_val); clear - HUR'; try pose proof alloc_ceiling_val as ACV__; lia | try (generalize alloc_ceiling_val); clear - HUR; try pose proof alloc_ceiling_val as ACV__; lia].
              + (* [comment removed for export] *) revert OUT LQ QE. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
              + (* [comment removed for export] *) world_close PE0 AINV HFR MUc WMc WZ.
              + (* [comment removed for export] *) world_close PE0 AINV HFR MUc WMc WZ.
              + (* [comment removed for export] *) cf_stores CF MUc PE0 STKc FRc. left; left. unfold blk. lia. }
            eapply (TAIL xc); [exact PIc| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| left; reflexivity|].
            subst xc. cbn [x_p]. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val as ACV__. lia.
        + (* [comment removed for export] *)
          zstep. vchk SHVc EzsV 8 0. vrechk SHVc EzsV (pe_VEP E + 64) 8 0.
          zstep. zstep. rewrite US. zstep. zstep. zstep. zstep. zstep.
          astop AINV MUc WMc CFP. fold_cl_segs.
          set (xg := PST (q + 1) S_NxtTag (fupd (fupd (x_v x) Funtil_p (u + 1)) Fstate (vi_st VIA S_NxtTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
          lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIg : pinv E xg A (aview A mr)) end.
          { subst xg. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUc WMc WZ.
            -- (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ; try pose proof alloc_ceiling_val as ACV__. lia.
            -- (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - QE; try pose proof alloc_ceiling_val as ACV__. lia.
            -- (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
            -- (* [comment removed for export] *) world_close PE0 AINV HFR MUc WMc WZ.
            -- (* [comment removed for export] *) world_close PE0 AINV HFR MUc WMc WZ.
            -- (* [comment removed for export] *) cf_stores CF MUc PE0 STKc FRc. left; left. unfold blk. lia. }
          eapply (TAIL xg); [exact PIg| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| right; reflexivity|].
          subst xg. intros _. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__. lia. }
    (* [comment removed for export] *)
    zstep; if_cases K0; zify_cond K0; try (exfalso; try (generalize alloc_ceiling_val); clear - K0 PLT; try pose proof alloc_ceiling_val as ACV__; lia); [].
    vchk SHV0 EzsV 8 0.
    zstep. zstep. zstep.
    eapply (ULOOP (Z.to_nat (pe_e E - x_p x)) (x_p x) (x_v x Funtil_p));
      [exact MU| exact WM| exact MI| unfold vep_cells; psimp; exact VEPC| exact FR| exact DBY| exact STK
      | exact SHV0| exact SHD| exact SHU
      | try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val as ACV__; rewrite Z2Nat.id by lia; lia| clear; lia| exact PLT| exact UP].
  Qed.
End S.
End A_PHucc.

   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold memset_esicmt_post, ASAN_MEMSET_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@VEPlo; @TAG; @WL; @Hk; @Dlo; @DLEN; @FRB; @G2; @KS; @SZ; @SR; @VERP; @Ha; @PLTc; @NN; @EE; @ACV; @UB; @VEPhi; @ACV__; @DJ_VD; @DJfV; @DJfD; @LOP; @HJ; @H; @CEIL; @K1; @LQ; @OUT; @H2; @H3; @LAR; @UBR; @EPd; @LAR0; @SPH; @EP2; @Hj; @E1; @Kb; @G3; @VEPlo_l; @EP0; @PLT; @E0; @E2; @R; @Hz; @NJ3; @HJ1; @EPlo; @EPhi; @Kn; @EP1])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
Ltac show_left := match goal with |- ?G => idtac "LEFTOVER:" G end.

(* [comment removed for export] *)
Definition arrow_byte (j : Z) : Z := if j =? 0 then 45 else if j =? 1 then 45 else if j =? 2 then 62 else 0.

Lemma arrow_read : forall m j, mem_inv rsegs m -> 0 <= j <= 3 ->
  ov_read_bytes rsegs m (wa (LIT_arrow + j)) 1 = Some [Z_to_bv 8 (arrow_byte j)].
Proof.
  intros m j MI Hj.
  assert (B : bytes_at rsegs m LIT_arrow [Z_to_bv 8 45; Z_to_bv 8 45; Z_to_bv 8 62; Z_to_bv 8 0]).
  { apply (ro_bytes_at rsegs m); [exact MI| | |].
    - unfold LIT_arrow; cbn; lia.
    - cbn [length]. unfold LIT_arrow; cbn; lia.
    - apply ro_bytes_b_sound. vm_compute; reflexivity. }
  eapply (u8ro_read rsegs m LIT_arrow _ j); [exact B| | lia| reflexivity].
  assert (X : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
  destruct X as [-> |[-> |[-> | ->]]]; reflexivity.
Qed.
Lemma arrow_byte_3 : forall j, arrow_byte j = 0 -> 0 <= j <= 3 -> j = 3.
Proof. intros j H R. unfold arrow_byte in H. destruct (j =? 0) eqn:E0; [cbn in H; lia|]. destruct (j =? 1) eqn:E1; [cbn in H; lia|]. destruct (j =? 2) eqn:E2; [cbn in H; lia|]. apply Z.eqb_neq in E0. apply Z.eqb_neq in E1. apply Z.eqb_neq in E2. lia. Qed.
Lemma arrow_byte_range : forall j, 0 <= arrow_byte j < 256.
Proof. intros j. unfold arrow_byte. destruct (j =? 0); destruct (j =? 1); destruct (j =? 2); lia. Qed.
Lemma unsigned_b8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma arrow_shadow : forall v, consts_hold LPA v ->
  bytes_at rsegs v (sh LIT_arrow) (shpat 4) /\ LIT_arrow mod 8 = 0 /\ LIT_arrow = 0x23040 /\ (0 <= sh LIT_arrow /\ sh LIT_arrow + Z.of_nat (length (shpat 4)) <= 17594064011264).
Proof.
  intros v CH. unfold LIT_arrow; cbn [vi_arrow VIA].
  split; [apply (global_shadow_pat v 0x23040 4 32 CH); gdesc_in|]. split; [reflexivity|]. split; [reflexivity|].
  change (Z.of_nat (length (shpat 4))) with 1; unfold sh; rewrite kShadowOffset_val; change (0x23040 / 8) with 17928; lia.
Qed.

End CEIL.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_NxtTag : handler_stmt S_NxtTag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    pose proof PLT as PLT0.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + 1) by (unfold phi, rank; rewrite ST; reflexivity).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (TAIL : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model) (ra' a0' a1' a2' a3' a4' a5' a6' s2' t4' t5' t6' : word),
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      x_st xc = S_NxtTag -> x_p xc = pe_e E ->
      srealizes rsegs (mkCfg (loop_ms E 0x8bf9c (x_p xc) (S8 E) ra' a0' a1' a2' a3' a4' a5' a6' s2'
                                 (Z_to_bv 64 ((pe_VEP E + 208) / 8)) (Z_to_bv 64 ((pe_VEP E + 200) / 8)) t4' t5' t6' mc) mdc) T).
    { intros until t6'. intros PIc AINVc MDFc STc EPc.
      clear - HMC PE KL PIc AINVc MDFc STc EPc; try pose proof alloc_ceiling_val as ACV__.
      pose proof PIc as PIc0. pose proof (pi_pe _ _ _ _ PIc) as PLEc.
      world_open PE PIc AINVc. unfold loop_ms, S8. rewrite EFP in *.
      assert (R200 : 0 <= x_v xc Fesicmt < 2^64) by (destruct ESIC as [[E1 _]|[E1 _]]; rewrite E1; unfold LIT_arrow; cbn; clear; lia).
      assert (R208 : 0 <= x_v xc Fesicmt_p < 2^64) by (destruct ESIC as [[_ E1]|[_ E1]]; [rewrite E1| revert E1; unfold LIT_arrow; cbn]; clear; intros; lia).
      hide_neqs.
      ago AINVc. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vrechk SHV0 EzsV (pe_VEP E + 208) 8 0.
      zstep. vrechk SHV0 EzsV (pe_VEP E + 200) 8 0.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        astop0 AINVc.
        eapply (KL xc Ac _ _); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]|].
        rewrite EPc. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val as ACV__. lia. }
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0.
      zstep. destruct B_rm as [RM|RM]; rewrite RM, sx32_small by (clear; lia).
      all: zstep; if_cases K1; zify_cond K1; try (exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val as ACV__; rewrite ?unsigned_lit in K1 by (clear; lia); lia); clear K1.
      2:{ (* [comment removed for export] *)
          astop0 AINVc.
          eapply (KL xc Ac _ _); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]|].
          rewrite EPc. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val as ACV__. lia. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      astop0 AINVc.
      eapply (mark_call HMC E xc Ac _ _ T (x_p xc) (x_p xc) 0 0x8bffc);
        [ exact PE | exact PIc0 | assumption | eapply amd_frame_sbm_r; [exact MDFc | exact SBM]
        | clear; lia | exact PLEc | left; reflexivity | clear; lia | reflexivity
        | intros [X|X]; rewrite STc in X; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (ST1 : x_st x1 = S_NxtTag) by (rewrite EX1; exact STc).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      assert (EPe : x_p x1 = pe_e E) by (rewrite EP1; exact EPc).
      clear - HMC PE KL PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EP1 EPe; try pose proof alloc_ceiling_val as ACV__.
      world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *. rewrite <- EP1.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      hide_neqs.
      ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      astop AINV1 MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x1) (x_st x1) (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
        all: rewrite ?ST1; try assumption.
        + exact (conj DELIM1 DELIM2).
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
      - psimp. rewrite EPe. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val as ACV__. lia. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (FOUND : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model) (ra' a0' a1' a2' a3' a4' a5' a6' t4' t5' t6' : word),
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      x_st xc = S_NxtTag -> x_v xc Fattr = 0 -> x_p x <= x_p xc -> x_p xc < pe_e E -> look E xc = 60 ->
      srealizes rsegs (mkCfg (loop_ms E 0x8c260 (x_p xc) (S8 E) ra' a0' a1' a2' a3' a4' a5' a6' (Z_to_bv 64 (x_p xc / 8 + 2147450880))
                                 (Z_to_bv 64 ((pe_VEP E + 208) / 8)) (Z_to_bv 64 ((pe_VEP E + 200) / 8)) t4' t5' t6' mc) mdc) T).
    { intros until t6'. intros PIc AINVc MDFc STc AT0 LQ PLTc LK.
      clear - HMC PE KL PHI PIc AINVc MDFc STc AT0 LQ PLTc LK; try pose proof alloc_ceiling_val as ACV__.
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms, S8. rewrite EFP in *.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview Ac mc)) as MU. pose proof (wmono_refl rsegs (aview Ac mc)) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA Ac (aview Ac mc) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      hide_neqs.
      ago AINVc. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0.
      zstep. destruct B_rm as [RM|RM]; rewrite RM, sx32_small by (clear; lia).
      all: zstep; if_cases K1; zify_cond K1; try (exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val as ACV__; rewrite ?unsigned_lit in K1 by (clear; lia); lia); clear K1.
      2:{ (* [comment removed for export] *)
          vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep.
          astop AINVc MU WM CFP. fold_cl_segs.
          eapply (KL (PST (x_p xc + 1) S_StartTag (fupd (x_v xc) Fstate (vi_st VIA S_StartTag)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) Ac _ _).
          - apply Build_pinv; psimp; pinv_close PE0 AINVc HFR MU WM WZ.
            + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__. lia.
            + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__. lia.
            + (* [comment removed for export] *) left. exact AT0.
            + (* [comment removed for export] *) world_close PE0 AINVc HFR MU WM WZ.
            + (* [comment removed for export] *) world_close PE0 AINVc HFR MU WM WZ.
            + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
          - assumption.
          - eapply amd_frame_sbm_r; [exact MDFc | exact SBM].
          - psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__. lia. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      astop0 AINVc.
      eapply (mark_call HMC E xc Ac _ _ T (x_p xc) (x_p xc) 0 0x8c290);
        [ exact PE | exact PIc0 | assumption | eapply amd_frame_sbm_r; [exact MDFc | exact SBM]
        | clear; lia | try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia | left; reflexivity | clear; lia | reflexivity
        | intros [X|X]; rewrite STc in X; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (ST1 : x_st x1 = S_NxtTag) by (rewrite EX1; exact STc).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      assert (AT1 : x_v x1 Fattr = 0) by (rewrite EX1; cbn [x_v after_mark]; vk_norm VK; exact AT0).
      assert (LK1 : look E x1 = 60) by (unfold look; rewrite EP1; exact LK).
      clear - HMC PE KL PHI PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EP1 AT1 LK1 LQ PLTc; try pose proof alloc_ceiling_val as ACV__.
      world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *. rewrite <- EP1. rewrite <- EP1 in LQ, PLTc.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      destruct (data_shadow A1 m2 md1 _ _ AINV1 DATA) as [SHD1 D16]. fold_cl_segs. fold_aview.
      pose proof (shpat_sh_boundL (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(try (generalize alloc_ceiling_val); clear - Dlo; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(clear; lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
      hide_neqs.
      ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0. zstep. zstep. zstep.
      (* [comment removed for export] *)
      prechk SHD1 (x_p x1) 1 11.
      (* [comment removed for export] *)
      destruct (look_read (Clg:=Clg) rsegs E x1 _ DBY ltac:(try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__; lia) PLTc) as (c & Hnthc & Hlookc & RDP).
      pose proof (bv_unsigned_in_range _ c) as CR. change (bv_modulus 8) with 256 in CR.
      zstep. clear RDP. cbv beta. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      2:{ exfalso. apply K2. rewrite Hlookc. exact LK1. }
      clear K2.
      (* [comment removed for export] *)
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep.
      astop AINV1 MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x1 + 1) S_StartTag
                      (fupd (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1)) Fstate (vi_st VIA S_StartTag))
                      (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
        + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__. lia.
        + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__. unfold pe_e, pe_N in *. lia.
        + (* [comment removed for export] *) left. exact AT1.
        + (* [comment removed for export] *) world_close PE0 AINV1 HFR MU WM WZ.
        + (* [comment removed for export] *) world_close PE0 AINV1 HFR MU WM WZ.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
      - psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__. lia. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (NLOOP : forall (k : nat) (xc : pst) (Ac : AS) (mc : mem) (mdc : Model) (ra' a0' a1' a2' a3' a4' a5' a6' s2' t4' t5' t6' : word),
      pe_e E - x_p xc = Z.of_nat k ->
      pinv E xc Ac (aview Ac mc) -> ainv Ac mc mdc -> amd_frame (pe_md0 E) mdc ->
      x_st xc = S_NxtTag -> x_v xc Fattr = 0 -> x_p x <= x_p xc -> x_p xc <= pe_e E ->
      srealizes rsegs (mkCfg (loop_ms E 0x8bd10 (x_p xc) (S8 E) ra' a0' a1' a2' a3' a4' a5' a6' s2'
                                 (Z_to_bv 64 ((pe_VEP E + 208) / 8)) (Z_to_bv 64 ((pe_VEP E + 200) / 8)) t4' t5' t6' mc) mdc) T).
    { induction k as [|k IH]; intros until t6'; intros Hk PIc AINVc MDFc STc AT0 LQ LEc.
      - (* [comment removed for export] *)
        clear - HMC PE TAIL Hk PIc AINVc MDFc STc; try pose proof alloc_ceiling_val as ACV__.
        pose proof PIc as PIc0.
        world_open PE PIc AINVc. unfold loop_ms, S8. rewrite EFP in *.
        hide_neqs.
        ago AINVc. fold_cl_segs.
        zstep. if_cases Kb; zify_cond Kb. 2:{ exfalso. unsign Kb. try (generalize alloc_ceiling_val); clear - Kb Hk; try pose proof alloc_ceiling_val as ACV__. lia. }
        astop0 AINVc.
        eapply (TAIL xc Ac); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]| exact STc| try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia].
      - (* [comment removed for export] *)
        assert (GB60 : forall (j : Z) (xd : pst) (Ad : AS) (mdd : mem) (mdm : Model) (ra_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ t4_ t5_ t6_ : word),
          pinv E xd Ad (aview Ad mdd) -> ainv Ad mdd mdm -> amd_frame (pe_md0 E) mdm ->
          x_st xd = S_NxtTag -> x_v xd Fattr = 0 -> x_p xd = x_p xc -> x_p xc < pe_e E ->
          x_v xd Fesicmt = LIT_arrow -> x_v xd Fesicmt_p = LIT_arrow + j -> 0 <= j <= 2 ->
          srealizes rsegs (mkCfg (loop_ms E 0x8bddc (x_p xd) (S8 E) ra_ a0_ a1_ a2_ a3_ a4_ a5_ a6_
                                     (Z_to_bv 64 ((pe_VEP E + 208) / 8 + 2147450880))
                                     (Z_to_bv 64 ((pe_VEP E + 208) / 8)) (Z_to_bv 64 ((pe_VEP E + 200) / 8)) t4_ t5_ t6_ mdd) mdm) T).
        { intros until t6_. intros PId AINVd MDFd STd ATd EPd PLTc EC EPJ HJ.
          clear - HMC PE IH Hk PId AINVd MDFd STd ATd EPd PLTc EC EPJ HJ LQ; try pose proof alloc_ceiling_val as ACV__.
          pose proof PId as PId0.
          world_open PE PId AINVd. unfold loop_ms, S8. rewrite EFP in *. rewrite EPd. rewrite EPd in PLE, VERP, OUT, VA, VI.
          pose proof (munch_refl [(pe_sp E - 304 - 2208, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312)] (aview Ad mdd)) as MU.
          pose proof (wmono_refl rsegs (aview Ad mdd)) as WM.
          assert (WZ : wzone E Ad [pe_S E; vb_buf (x_vv xd); pe_DATA E; x_v xd Fattr_vsb; oabuf xd; x_v xd Finclude_src; oibuf xd]
                               [(pe_sp E - 304 - 2208, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
          assert (CFP : client_fp LPA Ad (aview Ad mdd) [(pe_sp E - 304 - 2208, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312)])
            by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
          pose proof (asan_memset_cells_of_consts _ (consts_hold_ainv LPA Ad mdd mdm AINVd)) as AMC. fold_aview.
          pose proof (live_range_ok (Clg:=Clg) Ad mdd mdm (pe_VEP E) 312 (pe_VEP E + 200) 16 AINVd LVEP ltac:(lia) ltac:(lia) ltac:(lia)) as RNG16.
          destruct (arrow_shadow _ (consts_hold_ainv LPA Ad mdd mdm AINVd)) as (SHU & U8 & UB & SHUB). fold_cl_segs. fold_aview.
          assert (LAR : 0 <= LIT_arrow + j + 1 < 2^64) by (rewrite UB; try (generalize alloc_ceiling_val); clear - HJ; try pose proof alloc_ceiling_val as ACV__; lia).
          rewrite EPJ in VEPC.
          hide_neqs.
          ago AINVd. fold_cl_segs.
          (* [comment removed for export] *)
          vrechk SHV0 EzsV (pe_VEP E + 208) 8 0.
          (* [comment removed for export] *)
          zstep. zstep. zstep.
          (* [comment removed for export] *)
          shadow_chk SHU 1 12.
          (* [comment removed for export] *)
          lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
            pose proof (arrow_read mcur (j + 1) MIx ltac:(try (generalize alloc_ceiling_val); clear - HJ; try pose proof alloc_ceiling_val as ACV__; lia)) as RU end.
          replace (wa (LIT_arrow + (j + 1))) with (Z_to_bv 64 (LIT_arrow + j + 1)) in RU by (unfold wa; f_equal; clear; lia).
          pose proof (arrow_byte_range (j + 1)) as UBR.
          zstep. clear RU. cbv beta. rewrite (unsigned_b8 _ UBR).
          (* [comment removed for export] *)
          zstep. zstep. if_cases Kz; zify_cond Kz.
          + (* [comment removed for export] *)
            assert (HJ1 : j + 1 <= 2).
            { destruct (Z.eq_dec (j + 1) 3) as [J3|NJ3]; [| try (generalize alloc_ceiling_val); clear - HJ NJ3; try pose proof alloc_ceiling_val as ACV__; lia].
              exfalso. apply Kz. rewrite J3. reflexivity. }
            astop AINVd MU WM CFP. fold_cl_segs.
            set (xg := PST (x_p xc + 1) S_NxtTag (fupd (x_v xd) Fesicmt_p (LIT_arrow + j + 1)) (x_tag xd) (x_q xd) (x_vv xd) (x_va xd) (x_vi xd)).
            lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIg : pinv E xg Ad (aview Ad mr)) end.
            { subst xg. apply Build_pinv; psimp; pinv_close PE0 AINVd HFR MU WM WZ.
              * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__. lia.
              * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__. unfold pe_e, pe_N in *. lia.
              * (* [comment removed for export] *) right. split; [exact EC| try (generalize alloc_ceiling_val); clear - HJ HJ1; try pose proof alloc_ceiling_val as ACV__; lia].
              * (* [comment removed for export] *) world_close PE0 AINVd HFR MU WM WZ.
              * (* [comment removed for export] *) world_close PE0 AINVd HFR MU WM WZ.
              * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
            eapply (IH xg Ad); [subst xg; cbn [x_p]; try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia| exact PIg| assumption| eapply amd_frame_sbm_r; [exact MDFd | exact SBM]
              | reflexivity| subst xg; psimp; exact ATd| subst xg; cbn [x_p]; try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia| subst xg; cbn [x_p]; try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia].
          + (* [comment removed for export] *)
            assert (J2 : j = 2) by (pose proof (arrow_byte_3 (j + 1) Kz ltac:(try (generalize alloc_ceiling_val); clear - HJ; try pose proof alloc_ceiling_val as ACV__; lia)); try (generalize alloc_ceiling_val); clear - H HJ; try pose proof alloc_ceiling_val as ACV__; lia).
            (* [comment removed for export] *)
            zstep. vchk SHV0 EzsV 4 0. zstep. zstep.
            (* [comment removed for export] *)
            zstep. zstep. zstep. zstep.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
              pose proof (asan_memset_cells_of_consts _ (consts_hold_munch _ _ mx (consts_hold_ainv LPA Ad mdd mdm AINVd) MU
                            ltac:(apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold const_free_ivl, CONSTS_TOP; cbn [fst snd]; left; try (generalize alloc_ceiling_val); clear - VEPlo LOP CEIL ACV; try pose proof alloc_ceiling_val as ACV__; lia))) as AMC1;
              pose proof (range_ok_high_munch (Clg:=Clg) _ _ mx _ _ RNG16 MU ltac:(try (generalize alloc_ceiling_val); clear -VEPlo; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(clear; lia) ltac:(try (generalize alloc_ceiling_val); clear -VEPhi; try pose proof alloc_ceiling_val as ACV__; lia)
                            ltac:(apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst]; rewrite SHMAX_val; try (generalize alloc_ceiling_val); clear - VEPlo LOP CEIL ACV; try pose proof alloc_ceiling_val as ACV__; lia)) as RNG1
            end.
            clear AMC RNG16.
            icall (memset_esicmt_spec (pe_VEP E) (fupd (fupd (fupd (x_v xd) Fstate (stA (x_st xd))) Fesicmt_p (LIT_arrow + j + 1)) Fesi_found 1) (x_tag xd) (x_q xd)) by
              (rewrite ?unsigned_lit by lia;
               first [ exact VEPC | exact TAG | exact PADS | exact MI | exact AMC1 | exact STK | exact CEIL | exact RNG1 | unfold ASAN_MEMSET_STACK; lia | lia ]).
            lazymatch goal with X : rw_cells _ ?mx (pe_VEP E) (vep_cells _ _ _) |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into VEPC end.
            lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into STK end.
            unfold vep_cells in VEPC. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vi_st VIA stA] in VEPC.
            (* [comment removed for export] *)
            zstep. zstep. zstep. zstep.
            astop AINVd MU WM CFP. fold_cl_segs.
            set (xe := PST (x_p xc) S_NxtTag (fupd (fupd (fupd (fupd (x_v xd) Fesicmt_p (LIT_arrow + j + 1)) Fesi_found 1) Fesicmt 0) Fesicmt_p 0)
                           (x_tag xd) (x_q xd) (x_vv xd) (x_va xd) (x_vi xd)).
            lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIe : pinv E xe Ad (aview Ad mr)) end.
            { subst xe. apply Build_pinv; psimp; pinv_close PE0 AINVd HFR MU WM WZ.
              * (* [comment removed for export] *) left. split; reflexivity.
              * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
            eapply (mark_call HMC E xe Ad _ _ T (x_p xc + 1) (x_p xc + 1) 1 0x8be4c);
              [ exact PE | exact PIe | assumption | eapply amd_frame_sbm_r; [exact MDFd | exact SBM]
              | subst xe; cbn [x_p]; clear; lia | try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia | right; reflexivity | clear; lia | reflexivity
              | subst xe; cbn [x_st]; intros [X|X]; discriminate X | ].
            intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A2 m3 md2 v2 vv2 xk EX2 PI2 AINV2 MDF2 VK2 VERP2 LM2 OP2 CRC2 CRCP2.
            assert (ST2 : x_st xk = S_NxtTag) by (rewrite EX2; reflexivity).
            assert (EV2 : x_v xk = v2) by (rewrite EX2; reflexivity).
            assert (EP2 : x_p xk = x_p xc + 1) by (rewrite EX2; reflexivity).
            assert (AT2 : x_v xk Fattr = 0) by (rewrite EX2; cbn [x_v after_mark]; vk_norm VK2; subst xe; psimp; exact ATd).
            clear - HMC PE IH Hk PI2 AINV2 MDF2 VK2 VERP2 LM2 OP2 ST2 EV2 EP2 AT2 LQ PLTc; try pose proof alloc_ceiling_val as ACV__.
            world_open PE PI2 AINV2. unfold call_ms. cbv zeta. rewrite EFP in *. rewrite <- EP2.
            pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A2 m3)) as MU. pose proof (wmono_refl rsegs (aview A2 m3)) as WM.
            assert (WZ : wzone E A2 [pe_S E; vb_buf (x_vv xk); pe_DATA E; x_v xk Fattr_vsb; oabuf xk; x_v xk Finclude_src; oibuf xk]
                                 [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
            assert (CFP : client_fp LPA A2 (aview A2 m3) [(pe_VEP E, pe_VEP E + 312)])
              by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
            hide_neqs.
            ago AINV2. fold_cl_segs.
            (* [comment removed for export] *)
            zstep. vchk SHV0 EzsV 4 0.
            zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
            astop AINV2 MU WM CFP. fold_cl_segs.
            set (xs := PST (x_p xk) S_NxtTag (fupd (x_v xk) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v xk Fnm_skip))) + 1)) (x_tag xk) (x_q xk) (x_vv xk) (x_va xk) (x_vi xk)).
            lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIs : pinv E xs A2 (aview A2 mr)) end.
            { subst xs. apply Build_pinv; psimp; pinv_close PE0 AINV2 HFR MU WM WZ.
              (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
            eapply (IH xs A2); [subst xs; cbn [x_p]; try (generalize alloc_ceiling_val); clear - Hk EP2; try pose proof alloc_ceiling_val as ACV__; lia| exact PIs| assumption| eapply amd_frame_sbm_r; [exact MDF2 | exact SBM]
              | reflexivity| subst xs; psimp; exact AT2| subst xs; cbn [x_p]; try (generalize alloc_ceiling_val); clear - LQ EP2; try pose proof alloc_ceiling_val as ACV__; lia| subst xs; cbn [x_p]; try (generalize alloc_ceiling_val); clear - PLTc EP2; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia]. }
        (* [comment removed for export] *)
        assert (PLTc : x_p xc < pe_e E) by (try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia). clear LEc.
        clear - HMC PE IH TAIL FOUND GB60 Hk PIc AINVc MDFc STc AT0 LQ PLTc; try pose proof alloc_ceiling_val as ACV__.
        pose proof PIc as PIc0.
        world_open PE PIc AINVc. unfold loop_ms, S8. rewrite EFP in *.
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview Ac mc)) as MU. pose proof (wmono_refl rsegs (aview Ac mc)) as WM.
        assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                             [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
        assert (CFP : client_fp LPA Ac (aview Ac mc) [(pe_VEP E, pe_VEP E + 312)])
          by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
        destruct (data_shadow Ac mc mdc _ _ AINVc DATA) as [SHD D16]. fold_cl_segs. fold_aview.
        pose proof (shpat_sh_boundL (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(try (generalize alloc_ceiling_val); clear - Dlo; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(clear; lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
        destruct (arrow_shadow _ (consts_hold_ainv LPA Ac mc mdc AINVc)) as (SHU & U8 & UB & SHUB). fold_cl_segs. fold_aview.
        hide_neqs.
        ago AINVc. fold_cl_segs.
        (* [comment removed for export] *)
        zstep. if_cases Kb; zify_cond Kb. { exfalso. unsign Kb. try (generalize alloc_ceiling_val); clear - Kb PLTc VERP Dlo Dhi EE ACV; try pose proof alloc_ceiling_val as ACV__. unfold pe_e, pe_N in *. lia. } clear Kb.
        (* [comment removed for export] *)
        shadow_chk SHD 1 11.
        (* [comment removed for export] *)
        destruct (look_read (Clg:=Clg) rsegs E xc _ DBY ltac:(try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__; lia) PLTc) as (b & Hnth & Hlook & RD).
        pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
        zstep. clear RD. cbv beta. zstep. zstep. if_cases Kf; zify_cond Kf.
        { (* [comment removed for export] *)
          astop0 AINVc.
          eapply (FOUND xc Ac); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]| exact STc| exact AT0| exact LQ| exact PLTc
            | rewrite <- Hlook; exact Kf]. }
        (* [comment removed for export] *)
        zstep. vrechk SHV0 EzsV (pe_VEP E + 208) 8 0.
        (* [comment removed for export] *)
        zstep.
        destruct ESIC as [[EC0 EP0]|[EC1 [EPlo EPhi]]].
        + (* [comment removed for export] *)
          zstep. if_cases Kn; zify_cond Kn. 2:{ exfalso. apply Kn. rewrite EP0. reflexivity. } clear Kn.
          zstep. zstep.
          set (xn := PST (x_p xc + 1) S_NxtTag (x_v xc) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mr _) => assert (PIn : pinv E xn Ac mr) end.
          { subst xn. apply Build_pinv; psimp; pinv_close PE0 AINVc HFR MU WM WZ.
            * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__. lia.
            * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__. unfold pe_e, pe_N in *. lia.
            * (* [comment removed for export] *) left. exact (conj EC0 EP0).
            * (* [comment removed for export] *) world_close PE0 AINVc HFR MU WM WZ.
            * (* [comment removed for export] *) world_close PE0 AINVc HFR MU WM WZ. }
          astop0 AINVc.
          eapply (IH xn Ac); [subst xn; cbn [x_p]; try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia| exact PIn| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]
            | reflexivity| exact AT0| subst xn; cbn [x_p]; try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia| subst xn; cbn [x_p]; try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia].
        + (* [comment removed for export] *)
          assert (HJ : 0 <= x_v xc Fesicmt_p - LIT_arrow <= 2) by (try (generalize alloc_ceiling_val); clear - EPlo EPhi; try pose proof alloc_ceiling_val as ACV__; lia).
          set (j := x_v xc Fesicmt_p - LIT_arrow) in HJ.
          assert (EPJ : x_v xc Fesicmt_p = LIT_arrow + j) by (subst j; clear; lia). clearbody j.
          rewrite EPJ in VEPC |- *. clear EPlo EPhi.
          assert (LAR0 : 0 <= LIT_arrow + j < 2^64) by (rewrite UB; try (generalize alloc_ceiling_val); clear - HJ; try pose proof alloc_ceiling_val as ACV__; lia).
          zstep. if_cases Kn; zify_cond Kn. { exfalso. revert Kn HJ UB. clear. intros. rewrite ?unsigned_lit in Kn by lia. lia. } clear Kn.
          (* [comment removed for export] *)
          shadow_chk SHU 1 13.
          (* [comment removed for export] *)
          lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
            pose proof (arrow_read mcur j MIx ltac:(try (generalize alloc_ceiling_val); clear - HJ; try pose proof alloc_ceiling_val as ACV__; lia)) as RU end.
          unfold wa in RU.
          pose proof (arrow_byte_range j) as UBR.
          zstep. clear RU. cbv beta. rewrite (unsigned_b8 _ UBR).
          (* [comment removed for export] *)
          zstep. if_cases Km; zify_cond Km.
          * (* [comment removed for export] *)
            zstep. vrechk SHV0 EzsV (pe_VEP E + 200) 8 0.
            vrechk SHV0 EzsV (pe_VEP E + 208) 8 0.
            zstep. zstep. zstep. zstep. zstep.
            astop AINVc MU WM CFP. fold_cl_segs.
            set (xr := PST (x_p xc + 1) S_NxtTag (fupd (x_v xc) Fesicmt_p (x_v xc Fesicmt)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
            lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIr : pinv E xr Ac (aview Ac mr)) end.
            { subst xr. apply Build_pinv; psimp; pinv_close PE0 AINVc HFR MU WM WZ.
              -- (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__. lia.
              -- (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__. unfold pe_e, pe_N in *. lia.
              -- (* [comment removed for export] *) right. rewrite EC1. split; [reflexivity| clear; lia].
              -- (* [comment removed for export] *) world_close PE0 AINVc HFR MU WM WZ.
              -- (* [comment removed for export] *) world_close PE0 AINVc HFR MU WM WZ.
              -- (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
            eapply (IH xr Ac); [subst xr; cbn [x_p]; try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia| exact PIr| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]
              | reflexivity| subst xr; psimp; exact AT0| subst xr; cbn [x_p]; try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia| subst xr; cbn [x_p]; try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia].
          * (* [comment removed for export] *)
            zstep. vchk SHV0 EzsV 4 0.
            zstep. destruct B_rm as [RM|RM]; rewrite RM, sx32_small by (clear; lia).
            all: zstep; if_cases K1; zify_cond K1; try (exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val as ACV__; rewrite ?unsigned_lit in K1 by (clear; lia); lia); clear K1.
            2:{ (* [comment removed for export] *)
                astop0 AINVc.
                eapply (GB60 j xc Ac); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]| exact STc| exact AT0| reflexivity| exact PLTc| exact EC1| exact EPJ| exact HJ]. }
            (* [comment removed for export] *)
            zstep. vrechk SHV0 EzsV (pe_VEP E + 200) 8 0.
            zstep. zstep. rewrite EC1. zstep. if_cases Ke; zify_cond Ke.
            { (* [comment removed for export] *)
              astop0 AINVc.
              eapply (GB60 j xc Ac); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]| exact STc| exact AT0| reflexivity| exact PLTc| exact EC1| exact EPJ| exact HJ]. }
            (* [comment removed for export] *)
            zstep. zstep. zstep. zstep.
            astop0 AINVc.
            eapply (mark_call HMC E xc Ac _ _ T (x_p xc) (x_p xc) 0 0x8bda8);
              [ exact PE | exact PIc0 | assumption | eapply amd_frame_sbm_r; [exact MDFc | exact SBM]
              | clear; lia | try (generalize alloc_ceiling_val); clear - PLTc; try pose proof alloc_ceiling_val as ACV__; unfold pe_e, pe_N in *; lia | left; reflexivity | clear; lia | reflexivity
              | intros [X|X]; rewrite STc in X; discriminate X | ].
            intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
            assert (ST1 : x_st x1 = S_NxtTag) by (rewrite EX1; exact STc).
            assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
            assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
            assert (AT1 : x_v x1 Fattr = 0) by (rewrite EX1; cbn [x_v after_mark]; vk_norm VK; exact AT0).
            assert (ECx : x_v x1 Fesicmt = LIT_arrow) by (rewrite EX1; cbn [x_v after_mark]; vk_norm VK; exact EC1).
            assert (EPx : x_v x1 Fesicmt_p = LIT_arrow + j) by (rewrite EX1; cbn [x_v after_mark]; vk_norm VK; exact EPJ).
            clear - HMC PE GB60 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EP1 AT1 ECx EPx HJ PLTc; try pose proof alloc_ceiling_val as ACV__.
            world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *. rewrite <- EP1.
            pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
            assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                                 [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
            assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
              by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
            hide_neqs.
            ago AINV1. fold_cl_segs.
            (* [comment removed for export] *)
            zstep. vchk SHV0 EzsV 4 0.
            zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
            astop AINV1 MU WM CFP. fold_cl_segs.
            set (xm := PST (x_p x1) S_NxtTag (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)).
            lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIm : pinv E xm A1 (aview A1 mr)) end.
            { subst xm. apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
              (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
            eapply (GB60 j xm A1); [exact PIm| assumption| eapply amd_frame_sbm_r; [exact MDF1 | exact SBM]
              | reflexivity| subst xm; psimp; exact AT1| subst xm; cbn [x_p]; exact EP1| exact PLTc| subst xm; psimp; exact ECx| subst xm; psimp; exact EPx| exact HJ]. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 4 0. zstep.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep.
    astop AINV MU WM CFP. fold_cl_segs.
    set (x0 := PST (x_p x) S_NxtTag (fupd (fupd (fupd (x_v x) Femptytag 0) Fattr 0) Fdostuff 0) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PI0' : pinv E x0 A (aview A mr)) end.
    { subst x0. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      - (* [comment removed for export] *) left; reflexivity.
      - (* [comment removed for export] *) left; reflexivity.
      - (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
    rewrite (shr3_div8 (pe_VEP E + 208)), (shr3_div8 (pe_VEP E + 200)).
    eapply (NLOOP (Z.to_nat (pe_e E - x_p x)) x0 A); [subst x0; cbn [x_p]; try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val as ACV__; rewrite Z2Nat.id by lia; reflexivity| exact PI0'| assumption
      | eapply amd_frame_sbm_r; [exact MDF | exact SBM]| reflexivity| subst x0; psimp; reflexivity| subst x0; cbn [x_p]; clear; lia| subst x0; cbn [x_p]; try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val as ACV__; lia].
  Qed.
End S.
