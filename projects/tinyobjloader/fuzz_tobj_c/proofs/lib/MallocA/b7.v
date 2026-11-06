(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok ba.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.

(* [comment removed for export] *)
Module F0A_minit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "Pre_freeI"; "KcA"; "ulink"; "Kc_ok"; "ustop"; "J_free_preT"; "UStopLeOrPc"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Init.Datatypes"; "list"; "bool"; "prod"; "true"; "cons"; "nil"; "false"; "option"; "pair"; "Some"; "nat"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "rm"; "sobj"; "swf"; "sprop"; "SLit"; "SVar"; "agree_below"; "eval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit"; "N_pg"; "N_i0"; "N_i1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates"; "sa_i"; "MIDx"; "Pre_mid"; "RT_i"; "fi_cutpcs"; "sb_i"; "sc_i"; "P0i"; "fi_cuts"; "fi_vcuts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "@Corelib.Lists.ListDef"; "map"; "nth"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit"; "N_rest"; "K_iaw0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "set_inited"; "ia_zone"; "geom_ok"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "check_cfgA"; "check_ecfgA"; "mkVNA"; "withGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull"; "rt_zone2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit.MI"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_in_view"; "rd_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit"; "O_iaw"; "O_iaw_done"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM"; "rt_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue"; "coverb"; "spec_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition N_pg : list carve_spec := ltac2:(tb__ "0|0|
S15SfS45SfUdS47S48A4S15SfS45SfUeS47S48A4S16SfA1A3A3").
Definition N_i0 : list carve_spec := K_iaw0 :: N_pg.
Definition N_i1 : list carve_spec := K_iaw_done :: N_pg.
Lemma N_pg_ok : ltac2:(tb__ "0|0|
S0S11S21A1S44SfS21S10S32A4S3cA3"). Proof. reflexivity. Qed.
Lemma N_i0_ok : ltac2:(tb__ "0|1|
S0S11S21A1S44SfS21S10S33A4S15S21S63Z0M0G0A2S3cA3A3"). Proof. reflexivity. Qed.
Lemma N_i1_ok : ltac2:(tb__ "0|0|
S0S11S21A1S44SfS21S10S34A4S15S21S64S3cA3A3"). Proof. reflexivity. Qed.
Lemma N_pg_rest : ltac2:(tb__ "0|0|
SfS4eSfR1S32A3S4eSfR2S47A3F_;Fk;").
Proof. intros k [<-|[<-|[]]]; unfold N_rest, N_fn; cbn [tl nth]; cbn; tauto. Qed.

Section MI.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
ScVAInv;VW;Vst;VA;VKc;A5").

Lemma fi_instantiate : ltac2:(tb__ "0|5|
S1bSbS2eS8S1eS11S2bQ40A1A1S35S4S4S4S49SeRbA1S11S9A1M0S0SbRbSdA3S0G0R2S16S9A1A3F_;S68R2RcA2S0S12S30RcA1S17A3S0S12S22S39R4ReA2A1S14A3S0S18S13S11S13S1fS1fA2M1A1M2S11S23A1M3A2M4A1S53S5aS7S6R5RfA3A1S39R5RfA2A2S1aG4S19G2G3S15G1S19S1fS1fS25P18A1S24S5cA1A4S16G1A1A3S16S23A1A4A2A3S0S12S22S3eR6R10A2A1S14A3S0S12S22S3fR7R11A2A1S14A3S28Vsegs;VJ;R8R12R11R10A4S7S6R8R12A3RfReRdA6S28Vsegs;VJ;R9R13R12R11A4S40R9R13A2S4aR12R10RdRcRbRaA6RfReA6F_;F_;F_;F_;F_;F_;F_;F_;TW;Fjv;Ft;Fn;Fp;Fw;Ftp;Frho0;FKc;FA;Fst;FnW;").
Proof.
  intros nW st A Kc rho0 tp w p0 n0 t jv W HW HUS Hii Wa Da Wb Wc H0.
  set (rho := rhoF_of A rho0 p0 n0 t jv).
  assert (H : SPA segs (J W st A Kc) (Pre_freeI AE_A W st) rho tp w).
  { eapply SPA_agree; [| |exact H0]; [eapply agree_below_le; [|exact (rhoF_agree A rho0 p0 n0 t jv)]; cbv; discriminate
                                     | apply (JFr_agree nW st true A Kc rho0 rho); [exact HUS | exact (rhoF_agree A rho0 p0 n0 t jv)]]. }
  clear H0.
  pose proof H as [HsmA HJ]. destruct HJ as (HA & HU & HL & HK & Htp & HB & Htop).
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. destruct HG' as (_ & _ & _ & G4 & _).
  pose proof (topG_range (aa_geom A)) as TR. set (TOP := topG (aa_geom A)) in *.
  set (p := bv_unsigned (rw rho 12%positive)) in *. set (n := bv_unsigned (rw rho 13%positive)) in *.
  destruct HRest as (Hsep & _ & _ & _ & _ & _ & HIA & _).
  destruct (Hsep p n HL) as (S1 & S2 & S3 & _). unfold IMG_HI in S2. fold TOP in S3.
  unfold ia_inv in HIA. rewrite Hii in HIA. destruct HIA as (IA9 & IAa & IAb & IA8 & IAF).
  assert (MV : forall z, z < 0x646000 -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = view segs (rm rho) z).
  { intros z Hz. apply maskv_out. apply fs_footb_img; [exact HG0 | exact Hz]. }
  rewrite MV in IA9, IAa, IAb, IA8 by lia.
  assert (IAF' : forall z, IA_BEG <= z < IA_END -> view segs (rm rho) z = Some (Z_to_bv 8 0)).
  { intros z Hz. rewrite <- MV by (unfold IA_BEG, IA_END in Hz; lia). exact (IAF z Hz). }
  assert (TOPlo : TOP <= fst (obj_range rho stack_win)) by exact Htop.

  assert (H2 : SPA segs (J W st A Kc) (mkAX (sa_i W st) [] base_sv) rho tp w).
  { change (mkAX (sa_i W st) [] base_sv) with (ax_setS (Pre_freeI AE_A W st) (sa_i W st)).
    eapply SPA_restate; [exact Wa | exact Da | reflexivity | | constructor | exact H].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    rewrite Htp, G4. reflexivity. }
  clear H HsmA.
  pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
  assert (Hhigh : holds rho F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn [ss_facts sa_i]; unfold FACTSi; apply in_or_app; right; cbn; tauto).
  destruct (stack_win_range _ rho _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
  assert (LNK : Forall (fun o => TOP + 16 <= bv_unsigned (eval rho (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { unfold unwind_objs. destruct W as [|l W'] eqn:EW; [constructor|].
    destruct st; [|discriminate (HW eq_refl)].
    assert (HC : Forall (holds rho) (chain_pre (l :: W'))).
    { apply Forall_forall. intros pp Hp. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts sa_i]. unfold FACTSi. apply in_or_app. left. apply chain_pre_in. exact Hp. }
    unfold chain_pre in HC. cbn [app] in HC.
    pose proof (Forall_inv HC) as C0. pose proof (Forall_inv (Forall_inv_tail HC)) as C1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as C2. do 3 apply Forall_inv_tail in HC.
    cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
    pose proof (urange (rw rho 10%positive)). rewrite Z.mod_small in C1 by lia.
    eapply Forall_impl; [|apply (chain_facts_bases rho (SVar 28) (l :: W') HC); cbn [eval]; lia].
    intros o (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia. }
  pose proof (urange (rw rho 12%positive)) as U12. pose proof (urange (rw rho 13%positive)) as U13. fold p in U12. fold n in U13.

  assert (RBLK : obj_range rho O_blkP = (p, p + n)).
  { unfold O_blkP, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia.
    unfold soff. cbn [eval]. fold p. rewrite bv_signed_U. unfold Zsigned, H63v, M64v. fold n.
    destruct (Z.ltb_spec n 9223372036854775808); [f_equal; lia | exfalso; lia]. }

  assert (H3 : SPA segs (J W st A Kc) (mkAX (sb_i W st) [] base_sv) rho tp w).
  { change (mkAX (sb_i W st) [] base_sv) with
      (ax_setS (mkAX (sa_i W st) [] base_sv) (let S := ax_S (mkAX (sa_i W st) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ map carve_obj N_i0) (ss_facts S) NW2 (ss_lenient S))).
    eapply SPA_carve_list; [exact H2 | exact Wb | cbv; discriminate | | |].
    - unfold N_i0, N_pg, N_rest, N_fn, K_iaw0. cbn [tl nth].
      repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?u64_lit by lia.
      all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
      all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      all: split; [|split; [|apply xwords_clear_nil]].
      all: match goal with
           | |- cells_in_view _ _ 0 [(0x180e88, _, _); _; _; _] =>
               unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj; replace j with 0%nat by lia;
               cbn [Z.of_nat]; rewrite ?Z.add_0_r, ?Z.add_0_l; rewrite <- view_in by lia; rewrite nth0_enc1_zero;
               first [exact IA8 | exact IA9 | exact IAa | exact IAb]
           | |- cells_in_view _ _ _ _ => unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; civ_any2 HR
           | _ => idtac end.
      all: try match goal with
           | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
           end.
      all: fail "fi_instantiate: carve obligation left".
    - unfold N_i0, N_pg, N_rest, N_fn, K_iaw0. cbn [tl nth map carve_obj ss_objs ax_S sa_i]. unfold PREOBJSi, carved.
      unfold A_globals. unfold O_got, O_rtc. unfold GOT_LO, GOT_HI, RTC_LO, RTC_HI.
      repeat (apply Forall_cons;
        [ apply Forall_cons;
          [ unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia;
            destruct (obj_range rho stack_win) as [lo' hi']; cbn [fst snd] in *; lia
          | apply Forall_app; split;
            [ eapply Forall_impl; [|exact LNK]; intros [ob olo ohi ocs od] (B & L & Hh); cbn [ob_base ob_lo ob_hi] in B, L, Hh; subst olo ohi;
              unfold ranges_disjoint; rewrite !obj_range_mk by lia; cbn [fst snd eval]; cbn [eval] in B; rewrite ?u64_lit by lia; lia
            | apply Forall_cons; [unfold ranges_disjoint; rewrite RBLK; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia|];
              repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint;
              rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia ] ]
        | ]).
      apply Forall_nil.
    - unfold N_i0, N_pg, N_rest, N_fn, K_iaw0. cbn [tl nth map carve_obj pairwise_disjoint]. unfold carved.
      repeat split; repeat apply Forall_cons; try apply Forall_nil; try exact I; unfold ranges_disjoint;
        rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia. }
  clear H2.

  destruct w as [tr [ms md]].
  change (P0i W st) with
      (ax_setS (mkAX (sb_i W st) [] base_sv) (let S := ax_S (mkAX (sb_i W st) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [mkObj (SLit 0) (SLit IA_LO) (SLit IA_HI) [] DZero]) (ss_facts S) NW2 (ss_lenient S))).
  apply (SPA_carve_zero_rd segs (J W st A Kc) rho (mkAX (sb_i W st) [] base_sv) tp tr ms md (SLit 0) IA_LO IA_HI NW2 H3 Wc);
    cbn [ax_S ss_next sb_i ax_X ss_objs eval]; rewrite ?u64_lit by lia; unfold IA_LO, IA_HI; try lia.
  - apply Forall_app. split.
    + unfold PREOBJSi. apply Forall_cons; [unfold ranges_disjoint; destruct (obj_range rho stack_win) as [lo' hi']; cbn [fst snd] in *; lia|].
      apply Forall_app. split.
      * eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
        unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia.
      * apply Forall_cons; [unfold ranges_disjoint; rewrite RBLK; cbn [fst snd]; lia|].
        unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia.
    + unfold RT_i, O_iaw, O_pga, O_pgb. unfold carved.
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; unfold PG; lia.
  - intros a Ha. split; [apply wok_of_imageA; lia|]. rewrite <- view_in by lia. apply IAF'. unfold IA_BEG, IA_END. lia.
  - intros rr y j [].
Qed.

Lemma N_pg_small : Forall spec_small N_pg.
Proof. apply Forall_forall. intros k Hk. exact (proj1 (Forall_forall _ _) N_rest_small k (N_pg_rest k Hk)). Qed.
Lemma N_i1_small : Forall spec_small N_i1.
Proof. apply Forall_cons; [exact (Forall_inv N_fni1_small) | exact N_pg_small]. Qed.
Lemma N_pg_coverb : ltac2:(tb__ "0|0|
S0S12S4fSfS66S32A3S14A3").
Proof. apply forallb_forall. intros k Hk. exact (proj1 (forallb_forall _ _) N_rest_coverb k (N_pg_rest k Hk)). Qed.
Lemma fi_civ : ltac2:(tb__ "0|4|
S2eS1eS11S2bQ40M0A1A1S60VAInv;R4R3R2R1A4S46SfSfS13S13S13S1fS4A2M1S4A2M2S11S13S13S4S1bA2S1fA2A1M3A2OLk;R1G2G3G2OLp;R2G1S4G1OLp0;R2S1fS4S61RbS62Vsegs;S20RbA1A2S2dG0S27RbR2A2A2R5A4Llo;Lbase;X13x1Lhi;Lp0;X13x1Lcs;Lp;X13x1Lk;S32A3F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA. pose proof HA as (HG & HR & _).
  unfold N_pg, N_rest, N_fn. cbn [tl nth].
  repeat apply Forall_cons; try apply Forall_nil; lazy beta iota zeta; cbn [eval]; rewrite ?u64_lit by lia.
  all: unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn [eval].
  all: civ_any2 HR.
Qed.
Lemma N_pg_zone : ltac2:(tb__ "0|1|
S2eS1eSfS4S4dS2fR4A1A1S4eSfR3S32A3S1S50S1cS4S4S67R5R4A2M0A3R3A2S51R3S1dS4S4G0A3A2A2S65S2fR7A1R4A2F_;F_;F_;Fa;Fk;Frho;FA;").
Proof.
  intros A rho k a HG Hk Ha.
  pose proof (proj1 (forallb_forall _ _) N_rest_img_zone1 k (N_pg_rest k Hk)) as IZ.
  unfold N_pg, N_rest, N_fn in Hk. cbn [tl nth In] in Hk. unfold rt_zone.
  repeat (destruct Hk as [E|Hk];
    [subst k; cbn [spec_range fst snd eval] in Ha; rewrite ?u64_lit in Ha by lia;
     left; split; [unfold IMG_HI; lia|]; unfold img_zone_okb in IZ;
     eapply (forall_rangeZ_ok (fun a0 => cells_footb (rtc_cells_img RTC_A G0) a0)); [exact IZ | lia]
    |]).
  destruct Hk.
Qed.

Lemma fi_reabstract : ltac2:(tb__ "0|3|
S11S9A1S2eS8S1eS11S2bQ40M0A1A1S35S1eS0S12S30R6A1S17A3S28Vsegs;S59S1eS26S31R6R1A3Lr;VJ;R8S5R7R6A4A2S3aR8S5A2R2R4R3A6S3S1eS1eS1S28Vsegs;VJ;RaS5S4bR9A1R8A4S3bRaS5A2R1R6R5A6S1S54S31R7R1A3S1S4S2S4cR1A1A1S0S18S2bQ8A1A1M1S43Vsegs;S20R3A1R2A3S43Vsegs;S20R9A1R2A3A3F_;Fz;S4S1S50Z0R1A2S51R1S52Z2Z40A2A2A2S2S5dS2fRbA1R2A2A1S0G1S20R4S2cG0R3A2M2A2S20RaG2A2A3F_;F_;Fa;A2A2A2Lrho2;A2F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;FW;").
Proof.
  intros W A Kc rho tp w rhoE Hii H.
  destruct w as [tr [ms md]]. destruct H as [HsmA [Hag HJ]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct HJ as (HA & HU & HL & HK & Htp & HB & Htop).
  destruct Hag as (Hagw & Hagl & Hagm).
  assert (Erm : rm rhoE = rm rho).
  { apply functional_extensionality. intros a. rewrite <- Hagm. reflexivity. }
  pose proof HA as (HG & HR & HF & HRest & HM). pose proof (proj1 HRest) as Hsep.
  pose proof (topG_range (aa_geom A)) as TG.

  assert (Ha : SPA segs (fun _ _ t m => Kc t m) (MIDx W UStopLe) rhoE tp (tr, mkCfg ms md)) by (split; [exact HsmA | exact HK]).
  pose proof (SPA_unobj segs (fun _ _ t m => Kc t m) rhoE (MIDx W UStopLe) (PREOBJSi W stack_win_mid ++ (O_iaw_done :: RT_i)) [O_inst inst_cells] tp tr ms md eq_refl Ha (fun k => k)) as Hb1.
  cbn zeta in Hb1. set (rho2 := rho_absorb rhoE [O_inst inst_cells] (vms md tp ms)) in *.
  change (ax_setS (MIDx W UStopLe) (set_objs (ax_S (MIDx W UStopLe)) (PREOBJSi W stack_win_mid ++ (O_iaw_done :: RT_i)))) with (mkAX (stJ_i W UStopLe) [] base_sv) in Hb1.
  pose proof (proj1 (proj1 Ha)) as HsmE. unfold virt in HsmE. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in HsmE.

  pose proof (SPA_unobj segs (fun _ _ t m => Kc t m) rho2 (mkAX (stJ_i W UStopLe) [] base_sv) (PREOBJSi W stack_win_mid) (O_iaw_done :: RT_i) tp tr ms md eq_refl Hb1 (fun k => k)) as Hb.
  cbn zeta in Hb. set (rho3 := rho_absorb rho2 (O_iaw_done :: RT_i) (vms md tp ms)) in *.
  change (ax_setS (mkAX (stJ_i W UStopLe) [] base_sv) (set_objs (ax_S (mkAX (stJ_i W UStopLe) [] base_sv)) (PREOBJSi W stack_win_mid))) with (Pre_mid W UStopLe) in Hb.
  pose proof (proj1 (proj1 Hb1)) as Hsm2. unfold virt in Hsm2. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm2.
  assert (EV2 : forall e, eval rho2 e = eval rhoE e) by (intros e; unfold rho2; apply eval_absorb).
  pose proof (fi_civ A rhoE tp md HA) as CIV.
  assert (RNG1 : forall z o, In o (O_iaw_done :: RT_i) -> fst (obj_range rho2 o) <= z < snd (obj_range rho2 o) ->
                 (0x180e88 <= z < 0x180e8c) \/ exists k, In k N_pg /\ fst (spec_range rhoE k) <= z < snd (spec_range rhoE k)).
  { intros z o Hin Hr. rewrite <- N_i1_ok in Hin. apply in_map_iff in Hin as (k & <- & Hk).
    pose proof (proj1 (Forall_forall _ _) N_i1_small k Hk) as Sk.
    destruct Hk as [<-|Hk].
    - left. cbn [carve_obj K_iaw_done] in Hr. unfold carved in Hr. rewrite obj_range_mk in Hr by lia. cbn [fst snd] in Hr. rewrite EV2 in Hr. cbn [eval] in Hr. rewrite u64_lit in Hr by lia. lia.
    - right. exists k. split; [exact Hk|]. destruct k as [[[base lo] hi] cs]. cbn [carve_obj] in Hr.
      destruct Sk as (S1 & S2 & S3 & _). unfold carved in Hr. rewrite obj_range_mk in Hr by lia. cbn [fst snd ob_base spec_range] in Hr |- *.
      rewrite EV2 in Hr. exact Hr. }
  assert (VEQ : forall z, ~ ia_zone z -> view segs (rm rho3) z = view segs (rm rhoE) z).
  { intros z Hz. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    2,3: rewrite !view_out by lia; reflexivity.
    rewrite !view_in by lia. destruct (in_ranges_dec rho2 (O_iaw_done :: RT_i) (Z_to_bv 64 z)) as [Hri|Hrn].
    - destruct Hri as (o & Hin & Hr). rewrite u64_lit in Hr by lia.
      destruct (RNG1 z o Hin Hr) as [Zi|(k & Hk & Hzk)]; [exfalso; apply Hz; unfold ia_zone; lia|].
      unfold rho3. eapply (absorb_specs_view rho2 (stJ_i W UStopLe) tr (vms md tp ms) (vmd md) (PREOBJSi W stack_win_mid) (O_iaw_done :: RT_i) N_pg (rd_of segs (rm rhoE)) Hsm2 eq_refl); [| exact Hk |].
      + intros k' Hk'. split; [rewrite <- N_i1_ok; apply in_map; right; exact Hk'|]. split; [exact (proj1 (Forall_forall _ _) N_pg_small k' Hk')|].
        split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_pg_coverb k' Hk')|].
        pose proof (proj1 (Forall_forall _ _) CIV k' Hk') as C'. destruct k' as [[[base lo] hi] cs]. cbn [spec_range fst snd].
        cbn zeta in C'. rewrite EV2. replace (bv_unsigned (eval rhoE base) + lo - lo) with (bv_unsigned (eval rhoE base)) by lia.
        unfold cells_in_view in C' |- *. apply Forall_forall. intros [[o1 n1] e1] Hin' j Hj. rewrite EV2. exact (proj1 (Forall_forall _ _) C' _ Hin' j Hj).
      + destruct k as [[[base lo] hi] cs]. cbn [spec_range fst snd] in Hzk |- *. rewrite EV2. exact Hzk.
    - unfold rho3, rd_of. rewrite rm_absorb_out by exact Hrn.
      destruct (in_ranges_dec rhoE [O_inst inst_cells] (Z_to_bv 64 z)) as [Hri2|Hrn2].
      + exfalso. destruct Hri2 as (o & [<-|[]] & Hr). unfold O_inst in Hr. rewrite obj_range_mk in Hr by (unfold IA_LO, IA_HI; lia).
        cbn [fst snd eval] in Hr. rewrite !u64_lit in Hr by lia. apply Hz. unfold ia_zone, IA_BEG, IA_END. unfold IA_LO, IA_HI in Hr. lia.
      + unfold rho2. rewrite rm_absorb_out by exact Hrn2. reflexivity. }
  assert (Hrom2 : rom_ok segs (vms md tp ms)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm2))))).
  assert (IAZ : forall z, IA_MAP1 <= z < IA_MAP1 + IA_MAP1_SZ -> view segs (rm rho3) z = Some (Z_to_bv 8 0)).
  { intros z Hz. unfold IA_MAP1, IA_MAP1_SZ in Hz. rewrite view_in by lia.
    assert (Hrn : ~ in_ranges rho2 (O_iaw_done :: RT_i) (Z_to_bv 64 z)).
    { intros (o & Hin & Hr). rewrite u64_lit in Hr by lia. destruct (RNG1 z o Hin Hr) as [Zi|(k & Hk & Hzk)]; [lia|].
      destruct (rt_zone_not_ia _ z HG (N_pg_zone A rhoE k z HG Hk Hzk)) as [X _]. unfold IA_BEG, IA_END in X. lia. }
    pose proof (absorb_zero_dflt segs rhoE (ax_S (MIDx W UStopLe)) tr (vms md tp ms) (vmd md) _ [O_inst inst_cells] (SLit 0) IA_LO IA_HI inst_cells
                  HsmE eq_refl ltac:(left; reflexivity) ltac:(unfold IA_LO; lia) ltac:(unfold IA_LO, IA_HI; lia) ltac:(unfold IA_HI; lia)) as ZD.
    cbn zeta in ZD. cbn [eval] in ZD. rewrite u64_lit in ZD by lia. fold rho2 in ZD.
    unfold rho3, rd_of. rewrite rm_absorb_out by exact Hrn.
    change (rd_of segs (rm rho2) (Z_to_bv 64 z) = Some (Z_to_bv 8 0)). rewrite <- (Z.add_0_l z).
    apply ZD; [unfold IA_LO, IA_HI; lia|].
    unfold inst_cells. intros Hcov. unfold covered in Hcov. apply Exists_exists in Hcov as (c & Hc & Hic).
    destruct Hc as [<-|[<-|[]]]; unfold in_cell in Hic; cbn [c_off c_width] in Hic; rewrite soff_lit_small in Hic by lia; lia. }
  assert (IAW : view segs (rm rho3) 0x180e89 = Some (Z_to_bv 8 0) /\ view segs (rm rho3) 0x180e8a = Some (Z_to_bv 8 0)
                /\ view segs (rm rho3) 0x180e8b = Some (Z_to_bv 8 0) /\ view segs (rm rho3) 0x180e88 = Some (Z_to_bv 8 1)).
  { destruct (absorb_carved_cells segs rho2 (stJ_i W UStopLe) tr (vms md tp ms) (vmd md) (PREOBJSi W stack_win_mid) (O_iaw_done :: RT_i)
                (SLit 0) 0x180e88 0x180e8c [(0x180e89, 1%nat, SLit 0); (0x180e88, 1%nat, SLit 1); (0x180e8a, 2%nat, SLit 0)]
                Hsm2 eq_refl ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)) as [C _].
    fold rho3 in C. unfold cells_in_view in C. rewrite EV2 in C. cbn [eval] in C. rewrite u64_lit in C by lia.
    pose proof (Forall_inv C) as C9. pose proof (Forall_inv (Forall_inv_tail C)) as C8. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail C))) as Ca.
    cbn zeta in C9, C8, Ca.
    rewrite !view_in by lia.
    split; [specialize (C9 0%nat ltac:(lia)); replace (0 + 0x180e89 + Z.of_nat 0) with 0x180e89 in C9 by lia; change (eval rho3 (SLit 0)) with (Z_to_bv 64 0) in C9; rewrite nth0_enc1_zero' in C9; exact C9|].
    split; [pose proof (Ca 0%nat ltac:(lia)) as Ca0; replace (0 + 0x180e8a + Z.of_nat 0) with 0x180e8a in Ca0 by lia; change (eval rho3 (SLit 0)) with (Z_to_bv 64 0) in Ca0; rewrite (nth_enc2_zero' 0%nat ltac:(lia)) in Ca0; exact Ca0|].
    split; [pose proof (Ca 1%nat ltac:(lia)) as Ca1; replace (0 + 0x180e8a + Z.of_nat 1) with 0x180e8b in Ca1 by lia; change (eval rho3 (SLit 0)) with (Z_to_bv 64 0) in Ca1; rewrite (nth_enc2_zero' 1%nat ltac:(lia)) in Ca1; exact Ca1|].
    specialize (C8 0%nat ltac:(lia)). replace (0 + 0x180e88 + Z.of_nat 0) with 0x180e88 in C8 by lia. change (eval rho3 (SLit 1)) with (Z_to_bv 64 1) in C8. rewrite nth0_enc1_one' in C8. exact C8. }
  destruct IAW as (V9 & Va & Vb & V8).
  assert (HA3 : AInv (set_inited A) rho3 tp md).
  { apply (AInvA_ia_update segs A rhoE rho3 tp md HA VEQ). unfold ia_inv. cbn [aa_internal_inited set_inited].
    split; [exact V9|]. split; [exact Va|]. split; [exact Vb|]. split; [exact V8|]. intros z Hz. exact (IAZ z Hz). }
  assert (E3w : forall k, rw rho3 k = rw rhoE k) by (intros k; unfold rho3, rho2; cbn [rho_absorb rw]; reflexivity).
  exists rho3. split; [|split; [|split]].
  - split; [exact (proj1 Hb)|]. cbn [w_tr w_cfg cfg_model fst snd].
    split; [exact HA3|]. split; [destruct W; exact I|].
    split; [rewrite !E3w; exact HL|]. split; [exact HK|].
    split; [unfold tp_ok in *; rewrite E3w; exact Htp|]. split; [exact HB|].
    unfold top_high in *. rewrite !E3w. exact Htop.
  - split; [intros k Hk; rewrite E3w; apply Hagw; exact Hk|].
    intros l. unfold rho3, rho2. cbn [rl rho_absorb]. apply Hagl.
  - intros z Hz. rewrite <- Erm. exact (VEQ z Hz).
  - intros a Ba Hz. rewrite <- Erm. unfold rho3. rewrite rm_absorb_out.
    + unfold rho2. apply rm_absorb_out. intros (o & [<-|[]] & Hr). apply Hz. unfold O_inst in Hr. rewrite obj_range_mk in Hr by (unfold IA_LO, IA_HI; lia).
      cbn [fst snd eval] in Hr. rewrite !u64_lit in Hr by lia. unfold rt_zone2, IA_BEG, IA_END. unfold IA_LO, IA_HI in Hr. right. left. lia.
    + intros (o & Hin & Hr). rewrite u64_lit in Hr by lia. apply Hz. destruct (RNG1 a o Hin Hr) as [Zi|(k & Hk & Hzk)]; [unfold rt_zone2; right; right; exact Zi|].
      left. exact (N_pg_zone A rhoE k a HG Hk Hzk).
Qed.

Definition mid_link (A : AA) (rho rho2 : valuation) : Prop := ltac2:(tb__ "0|2|
S1S54S31Vrho;Vrho2;A3S1S4S2S4cR1A1A1S0S18S2bQ8A1A1M0S43Vsegs;S20Vrho2;A1R2A3S43Vsegs;S20Vrho;A1R2A3A3F_;Fz;S4S1S50Z0R1A2S51R1S52Z2Z40A2A2A2S2S5dS2fVA;A1R2A2A1S0G0S20Vrho2;S2cQ40R3A2M1A2S20Vrho;G1A2A3F_;F_;Fa;A2A2").

Section PerN.
Variable n : nat.
Let W : list ulink := Wcan n.
Hypothesis Wa : ltac2:(tb__ "0|0|
S0S12S22S39VW;S5A2A1S14A3").
Hypothesis Da : ltac2:(tb__ "0|4|
S0S18S13S11S13S1fS1fA2M0A1M1S11S23A1M2A2M3A1S53S5aS7S6VW;S5A3A1S39VW;S5A2A2S1aG3S19G1G2S15G0S19S1fS1fS25P18A1S24S5cA1A4S16G0A1A3S16S23A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S0S12S22S3eVW;S5A2A1S14A3").
Hypothesis Wc : ltac2:(tb__ "0|0|
S0S12S22S3fVW;S5A2A1S14A3").

Hypothesis Cert : ltac2:(tb__ "0|0|
S0S12S56S5fUbb8S3dS31S41Vn;S5A2S15S5bS3aVW;S5A2S16S5bA1A3A6S14A3").
Hypothesis ECert : ltac2:(tb__ "0|1|
S0S12S57S5fUbb8S3dS31S42Vn;S5A2S15S55S58S3aVW;S5A2Z0M0S24G0A1A3S16S55A1A3A6S14A3").

Theorem fi_prefix : ltac2:(tb__ "0|0|
S35OF_;S2eS8S1eS11S2bQ40A1A1S38S4S4S4S49S0S12S30R9A1S17A3SaR9A1S2aVsegs;RcS29RaA1A3S1eS5eRdS4aRdRbR8R7R6R5A6R1A3S37Vsegs;RfS28Vsegs;VJ;VW;S5S4bReA1RdA4S3bVW;S5A2R2RbA5RaA4F_;Frho2;S37Vsegs;ReS28Vsegs;VJ;VW;S5RdRcA4S7S6VW;S5A3RbRaA5R9A4F_;F_;F_;F_;Fjv;Ft;Fn0;Fp0;FQ;Ftp;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 tp Q p0 n0 t jv Hii HKc Hokf HC. set (rho := rhoF_of A rho0 p0 n0 t jv) in *.
  eapply triple_conseq; [intros w Hw; exact (fi_instantiate n UStopLe A Kc rho0 tp w p0 n0 t jv ltac:(intros E; discriminate E) (stopJ_stable_le _) Hii Wa Da Wb Wc Hw) | intros w Hw; exact Hw |]. fold rho.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs _ GW (P0i W UStopLe) rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 3000%nat fi_cutpcs GW (fi_cuts n UStopLe) [MIDx W UStopLe] (JF n UStopLe true A Kc rho) ok Q tp).
  - apply JF_okf. exact Hokf.
  - apply JF_stable; [apply stopJ_stable_le | exact HKc].
  - exact Cert.
  - intros E rhoE [<-|[]]. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    intros k Hg w Hw. destruct (fi_reabstract W A Kc rho tp w rhoE Hii Hw) as (rho2 & Hw2 & AG & VQ & RMO).
    exact (HC rho2 (conj AG (conj VQ RMO)) k Hg w Hw2).
  - left. reflexivity.
Qed.
Theorem efi_prefix : ltac2:(tb__ "0|0|
S2eS8S1eS11S2bQ40A1A1S35OF_;S4S4S4S49S0S12S30R9A1S17A3SaR9A1S1eS5eRcS4aRcRaR7R6R5R4A6R1A3S36Vsegs;S28Vsegs;VJ;VW;S5S4bRdA1RcA4S3bVW;S5A2R2RaA5R9A3F_;Frho2;S36Vsegs;S28Vsegs;VJ;VW;S5RcRbA4S7S6VW;S5A3RaR9A5R8A3F_;F_;F_;Fjv;Ft;Fn0;Fp0;FQ;Ftp;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 tp Q p0 n0 t jv Hii HKc HC. set (rho := rhoF_of A rho0 p0 n0 t jv) in *.
  eapply etriple_conseq; [intros w Hw; exact (fi_instantiate n UStopLe A Kc rho0 tp w p0 n0 t jv ltac:(intros E; discriminate E) (stopJ_stable_le _) Hii Wa Da Wb Wc Hw) | intros w Hw; exact Hw |]. fold rho.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs _ GW (P0i W UStopLe) rho tp w Hw) | intros w Hw; exact Hw |].
  change (P0i W UStopLe) with (vna_state (mkVNA (P0i W UStopLe) 5 (SLit 0))).
  apply (cfg_complete_autoA segs 3000%nat fi_cutpcs GW (fi_vcuts n UStopLe) [mkVNA (MIDx W UStopLe) 0 (SLit 0)] (JF n UStopLe true A Kc rho) Q tp).
  - apply JF_stable; [apply stopJ_stable_le | exact HKc].
  - intros m Hm. cbn [fi_vcuts In] in Hm.
    repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm.
  - exact ECert.
  - intros E rhoE [<-|[]]. cbn [vna_state]. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    intros w Hw. destruct (fi_reabstract W A Kc rho tp w rhoE Hii Hw) as (rho2 & Hw2 & AG & VQ & RMO).
    exact (HC rho2 (conj AG (conj VQ RMO)) w Hw2).
  - left. reflexivity.
Qed.
End PerN.
End MI.
End F0A_minit.

(* [comment removed for export] *)
Module SpineCallocR7.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "entailsA"; "sym_runA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SAlu"; "ss_next"; "eval"; "SVar"; "ss_facts"; "swf"; "valuation"; "SPNot"; "holds"; "ss_lenient"; "SPBranch"; "SPUle"; "rw"; "SMd"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "list"; "nil"; "pair"; "prod"; "Some"; "option"; "andb"; "false"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "cP2"; "GR"; "vMU"; "HINT_map"; "cPa"; "cPb"; "req_e"; "vAU"; "vK"; "vNF"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "of_nat"; "mul"; "sub"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SRL"; "BC_LTU"; "ALU_SRA"; "ALU_XOR"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "V_CLS"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7"; "F_mu0"; "F_hi"; "size_e_hi"; "size_e_lo"; "x19_e0"; "x19_e1"; "popfacts"; "total_e"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_free_array"; "cs_allocated_user"; "cs_mapped_user"; "AA"; "class_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "JR"; "entryR"; "ph0"; "gh_nf"; "ghosts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "tab1_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "rigids"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv InvLaws PrimCredit PrimCreditLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RefillModelP RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.PrimRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition size_e_hi : sv := ltac2:(tb__ "0|4|
SbS37SbS38SbS3cSbS39SeS40A1M0SaZ3fA1M1A3G1A3SbS3aSbS39SaZ200A1SbS3aSbS37G0SaN10A1A3SaZ1A1M2A3A3M3G2A3A3G3A3").
Definition size_e_lo : sv := ltac2:(tb__ "0|0|
SbS39SeS40A1SaZ5A1A3").
Definition tabS_okb : bool := ltac2:(tb__ "0|0|
S22S22S22S5eS40S45S51Z11UeA5S61S40S45A2A2S5eS40S46S51Z1U10A5A2S61S40S46A2A2").
Lemma tabS_ok : tabS_okb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Definition F_hi : sprop := ltac2:(tb__ "0|0|
S15S3bSaZ10A1SeS40A1A3").

Definition total_e : sv := ltac2:(tb__ "0|0|
SbS37S2dS18S3eSeS41A1S2cA3A3").
Definition x19_e0 : sv := ltac2:(tb__ "0|0|
SbS37SbS38SbS37S4aSaN1A1A3SaZfffffffffffc0000A1A3SaZ40000A1A3").
Definition x19_e1 : sv := ltac2:(tb__ "0|0|
SbS37SbS38SbS37S4aSbS3dS28SaZffffffffffffffffA1A3A3SaZfffffffffffc0000A1A3SaZ40000A1A3").
Definition F_mu0 : sprop := SPBranch BC_EQ vMU (SLit 0).

Definition popfacts (A : AA) (rb : valuation) : Prop := ltac2:(tb__ "0|1|
S4eQ40S17Vrb;PcA2A2S25S5fR1A1S25S60VA;R2A2S57S6S31S33S24S25S53R1A1A2A1S52R2A1A2S6S30S32S55R1A1Z40000A2S65R2A1M0A2S30G0Ze0000000A2A2A2Tcs;Tc;Tnv;").

Lemma entry_popfacts : ltac2:(tb__ "0|1|
S56S11S1cS4dQ40M0A1A1S62S1cS63A1S64S11S5aR7R6R5R4R3R2R1A7S31S5cR8R7A2S52S5fS4eG0S17R7PcA2A2A1A1A2S49R9R8A2F_;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho HE HNP. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _) & _ & _ & (_ & _ & Hc0) & _).
  destruct HE as (_ & HA & _). unfold popfacts. cbn zeta. unfold gh_nf in HNP. split; [exact HNP|].
  pose proof (populate_room segs A rb tp0 md0 _ HA C1 Hc0 ltac:(unfold cst_of in HNP; lia)) as [R1 R2].
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize in *. unfold cst_of. split; [exact R1 | exact R2].
Qed.

Section VALS.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis PF : popfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S66VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S5dVA;Vrb;Vr;A3").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.

Lemma size_hi_val : ltac2:(tb__ "0|0|
S13Vr;S44A2S5S4dQ40A1SdVr;S45A2SdVr;SeS41A1A2A3F_;").
Proof.
  intros HF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _).
  destruct RG as (_ & E148 & _ & _ & _ & _ & _ & E158). fold nv c in E148, E158.
  unfold F_hi in HF. cbn [holds eval] in HF. unfold branch_taken, bv_ltu in HF. apply Z.ltb_lt in HF. unfold V_CLS in HF. rewrite E158 in HF. rewrite !u64_lit in HF by (clear -C1; lia).
  pose proof tabS_ok as T. unfold tabS_okb in T. apply andb_prop in T as [T _]. apply andb_prop in T as [T _]. apply andb_prop in T as [T1 T2].
  cbn [eval]. unfold V_SIZE. rewrite E148. exact (tab1_ok_sound V_CLS size_e_hi Size 17 14 r c T1 T2 E158 ltac:(clear -C1 HF; lia)).
Qed.
Lemma size_lo_val : ltac2:(tb__ "0|0|
S7S13Vr;S44A2A1S5S4dQ40A1SdVr;S46A2SdVr;SeS41A1A2A3F_;").
Proof.
  intros HF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _).
  destruct RG as (_ & E148 & _ & _ & _ & _ & _ & E158). fold nv c in E148, E158.
  unfold F_hi in HF. cbn [holds eval] in HF. unfold branch_taken, bv_ltu in HF. unfold V_CLS in HF. rewrite E158 in HF. rewrite !u64_lit in HF by (clear -C1; lia).
  assert (C16 : c <= 16) by (destruct (Z.ltb_spec 16 c) as [X|X]; [exfalso; apply HF; reflexivity | exact X]).
  pose proof tabS_ok as T. unfold tabS_okb in T. apply andb_prop in T as [T T4]. apply andb_prop in T as [T T3].
  cbn [eval]. unfold V_SIZE. rewrite E148. exact (tab1_ok_sound V_CLS size_e_lo Size 1 16 r c T3 T4 E158 ltac:(clear -C1 C16; lia)).
Qed.

Lemma pop_nums : ltac2:(tb__ "0|4|
S51Vc;A1S25S52Vc;A1S25S33S24S25S53Vcs;A1A2A1S25S54Vcs;A1S25S55Vcs;A1S25S6S6S30Z20R5A2S30R5Z10000M0A2A2S6S6S30Z1R4A2S30R4Z8A2A2S6S6S30Z0M1R3A2S31R3R4A2A2S6S6S30G1R2A2S30R2R1A2A2S6S30R1Zdffc0000A2S6S31R1S32R2R5A2A2S6S6S31G1S34R5S35R4R3A2A2M2A2S30G2G0A2A2S6S31R1S32R2G2A2M3A2S30G3S32R1G0A2A2A2A2A2A2A2A2A2A2Tmu;Tau;Tnf;Tk;TS;").
Proof.
  intros S k nf au mu.
  unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. fold S k nf au mu in CF.
  destruct CF as ((_ & _ & S1 & _) & (K1 & _ & K3) & (_ & AU0 & _ & _ & TI0) & _).
  destruct PF as (NP & RM & RC). fold nv c cs in NP, RM, RC. fold k nf mu in NP, RM.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. fold nf in NF0.
  clear -S1 K1 K3 AU0 TI0 NP RM RC NF0.
  assert (B1 : 0 < S * (k - nf)) by nia. assert (B2 : S * (k - nf) <= S * k) by nia. assert (B3 : S <= S * (k - nf)) by nia. lia.
Qed.

Lemma total_val : ltac2:(tb__ "0|0|
S5S25S4eQ40SdVr;S4aA2A2S32S54Vcs;A1S34S51Vc;A1S35S52Vc;A1S33S24S25S53Vcs;A1A2A1A2A2A2A3").
Proof.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct RG as (_ & E148 & _). fold nv c in E148.
  destruct GH as (_ & Q221 & _ & Q223 & _ & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q227.
  unfold total_e, req_e, vAU, vK, vNF, V_SIZE. cbn [eval]. rewrite add_val, mul_val, sub_val, E148, Q221, Q223, Q227.
  rewrite !u64_lit by (clear -N1 N2 N3 N4 N5; lia).
  rewrite (Z.mod_small (kchunks c - _)) by (clear -N2 N3; lia). rewrite (Z.mod_small (Size c * _)) by (clear -N7; lia).
  rewrite Z.mod_small by (clear -N4 N5 N7; lia). reflexivity.
Qed.

Lemma F_pop_hold : Forall (holds r) F_pop.
Proof.
  pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & Q221 & _ & Q223 & Q224 & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q224, Q227.
  unfold F_pop. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. unfold branch_taken, bv_ltu, vNF, vK. cbn [eval]. rewrite Q221, Q227. rewrite !u64_lit by (clear -N2 N3; lia). apply Z.ltb_lt. exact (proj2 N3).
  - unfold HINT_map. cbn [holds]. unfold branch_taken, bv_ltu. fold total_e. rewrite TV. unfold vMU. cbn [eval]. rewrite Q224. rewrite u64_lit by (clear -N4 N5; lia).
    apply Z.ltb_lt. exact (proj1 N8).
  - cbn [holds]. unfold vMU. cbn [eval]. rewrite Q224. rewrite !u64_lit by (clear -N4 N5; lia). exact N5.
Qed.

Lemma x19_val1 : ltac2:(tb__ "0|0|
S5S4dQ40A1SdVr;S48A2SdVr;SaZ40000A1A2A3").
Proof.
  pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & _ & _ & _ & Q224 & _). fold nv c cs in Q224.
  set (tot := cs_allocated_user cs + Size c * (kchunks c - Z.of_nat (length (cs_free_array cs)))) in *.
  unfold x19_e1. cbn [eval]. apply bv_eq. rewrite add_val, and_val, add_val, xor_val. fold total_e. rewrite TV. unfold vMU. cbn [eval]. rewrite Q224.
  rewrite !u64_lit by (clear -N4 N5; lia).
  rewrite lxor_ones64 by (clear -N4 N5; lia).
  replace ((tot + (18446744073709551615 - cs_mapped_user cs)) mod 2 ^ 64) with (tot - cs_mapped_user cs - 1).
  2: { apply (Z.mod_unique_pos _ _ 1); clear -N4 N5 N8; lia. }
  rewrite land_m18_small by (clear -N8; lia). rewrite Z.mod_small by (clear; lia). reflexivity.
Qed.
Lemma x19_val0 : ltac2:(tb__ "0|1|
S13Vr;S43A2S6S5S4dQ40A1M0SdVr;S47A2SdVr;SaZ40000A1A2A3S5G0SdVr;SaZ0A1A2SdVr;S28A2A3A2F_;").
Proof.
  intros HF. pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & _ & _ & _ & Q224 & _). fold nv c cs in Q224.
  unfold F_mu0 in HF. cbn [holds] in HF. unfold branch_taken, bv_eqb, vMU in HF. cbn [eval] in HF. rewrite Q224 in HF. rewrite !u64_lit in HF by (clear -N4 N5; lia). apply Z.eqb_eq in HF.
  set (tot := cs_allocated_user cs + Size c * (kchunks c - Z.of_nat (length (cs_free_array cs)))) in *.
  split.
  - unfold x19_e0. cbn [eval]. apply bv_eq. rewrite add_val, and_val, add_val. fold total_e. rewrite TV.
    replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615 by reflexivity. rewrite !u64_lit by (clear; lia).
    replace ((tot + 18446744073709551615) mod 2 ^ 64) with (tot - 1).
    2: { apply (Z.mod_unique_pos _ _ 1); clear -N4 N8 HF; lia. }
    rewrite land_m18_small by (clear -N4 N8 HF; lia). rewrite Z.mod_small by (clear; lia). reflexivity.
  - unfold vMU. cbn [eval]. rewrite Q224, HF. reflexivity.
Qed.
End VALS.

Section POP1.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S5aVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).

Variable F : nat.
Variables (E3 : axst) (LP : axst) (La Lb La0 La1 Lb0 Lb1 : leafA) (CP2C : axst) (sa0 sa1 sb0 sb1 : wsub).
Let FR : list sprop := factsR E3.
Let CPA : axst := ltac2:(tb__ "0|0|
S2aVFR;S1VLa;A1A2").
Let CPB : axst := ltac2:(tb__ "0|0|
S2bVFR;S1VLb;A1A2").
Hypothesis FP_in : ltac2:(tb__ "0|0|
S36S9S15S3bS2fS2eA3SfS0VLP;A1A1A3").
Hypothesis R_p1 : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z415c0S1bS25Z41600S1dS25A1A3A3VLP;S1aA5S20G0S1bS2VLa;S1bS2VLb;S1dS2A1A3A3A2A3").
Hypothesis LN_p : ltac2:(tb__ "0|0|
S5S19S14S0VLP;A1A1S23A3").
Hypothesis NX_p : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VLP;A1A1A2S1aA3").
Hypothesis Fa_in : ltac2:(tb__ "0|0|
S36S9S44SfS0S1VLa;A1A1A1A3").
Hypothesis Fb_in : ltac2:(tb__ "0|0|
S36S9S12S44A1SfS0S1VLb;A1A1A1A3").
Hypothesis W_pa : ltac2:(tb__ "0|0|
S5S19S10S0VCPA;A1A1S1aA3").
Hypothesis D_pa : ltac2:(tb__ "0|4|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa;A1A1S0VCPA;A1A2S20G3S1eG1G2S1bG0S1eS8S8S45SeS41A1A4S1dG0A1A3S1bS9S29S1bS9S16S28SaZdffc0000A1A2S1dS9A1A3A3A4A2A3").
Hypothesis NX_pa : ltac2:(tb__ "0|0|
S5S19S4bScS0VCPA;A1A1ScS0S1VLa;A1A1A1A2S1aA3").
Hypothesis W_pb : ltac2:(tb__ "0|0|
S5S19S10S0VCPB;A1A1S1aA3").
Hypothesis D_pb : ltac2:(tb__ "0|4|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb;A1A1S0VCPB;A1A2S20G3S1eG1G2S1bG0S1eS8S8S46SeS41A1A4S1dG0A1A3S1bS9S29S1bS9S16S28SaZdffc0000A1A2S1dS9A1A3A3A4A2A3").
Hypothesis NX_pb : ltac2:(tb__ "0|0|
S5S19S4bScS0VCPB;A1A1ScS0S1VLb;A1A1A1A2S1aA3").
Hypothesis R_p2a : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z41630S1dS25A1A3VCPA;S1aA5S20G0S1bS2VLa0;S1bS2VLa1;S1dS2A1A3A3A2A3").
Hypothesis LN_pa : ltac2:(tb__ "0|0|
S5S19S14S0VCPA;A1A1S23A3").
Hypothesis NXr_pa : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VCPA;A1A1A2S1aA3").
Hypothesis R_p2b : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z41630S1dS25A1A3VCPB;S1aA5S20G0S1bS2VLb0;S1bS2VLb1;S1dS2A1A3A3A2A3").
Hypothesis LN_pb : ltac2:(tb__ "0|0|
S5S19S14S0VCPB;A1A1S23A3").
Hypothesis NXr_pb : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VCPB;A1A1A2S1aA3").

Section LEAF.
Variables (L : leafA) (s : wsub) (mu0 : bool).
Let C2 : axst := ltac2:(tb__ "0|0|
S26VFR;S1VL;A1A2").
Hypothesis F_in : ltac2:(tb__ "0|0|
S36S9S19S9Lmu0;Vmu0;S43S12S43A1X19x2SfS0S1VL;A1A1A1A3").
Hypothesis W_2 : ltac2:(tb__ "0|0|
S5S19S10S0VC2;A1A1S1aA3").
Hypothesis D_2 : ltac2:(tb__ "0|6|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VL;A1A1S0VC2;A1A2S20G3S1eG1G2S19G1Lmu0;Vmu0;S1bG0S1eS8S8S47SaZ40000A1M4A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1M5A3A3S1bG0S1eS8S8S48G4A4G5A3X19x2S1dS9A1A4A2A3").
Hypothesis NX_2 : ltac2:(tb__ "0|0|
S5S19S4bScS0VC2;A1A1ScS0S1VL;A1A1A1A2S1aA3").
Hypothesis ENT_2 : ltac2:(tb__ "0|0|
S5S19S3VC2;VCP2C;Vs;A3S1aA3").
Hypothesis SID_2 : ltac2:(tb__ "0|0|
S5S19S4fVs;S27A2S1aA3").

Lemma join_leaf : ltac2:(tb__ "0|1|
S11S1cS4dQ40A1A1S58S49VA;Vrb;A2S11VTR;S50S42S59VA;VKc;Vrb;Vtp0;Vmd0;S5bA6M0VCP2C;R1R4A5R3A2Fr';VTR;S50S42G0S1VL;A1R5R4A5R3A2F_;F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q PF HC.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state L) (ax_S C2) _ _ ph0 r tp Q W_2 D_2 NX_2).
  { intros tr md (HFz & HGh & _) HF. split; [|constructor].
    pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    pose proof (proj1 (Forall_forall _ _) HF _ F_in) as HB.
    unfold diffs_ok. destruct mu0.
    - destruct (x19_val0 A rb r CF PF RG HGh HB) as [X1 X2]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; assumption.
    - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. exact (x19_val1 A rb r CF PF RG HGh). }
  change (ax_setS (la_state L) (ax_S C2)) with C2.
  apply (tr_pre Kc TR KIT (SPA segs (JRp ph0) CP2C (rho_sub r s) tp)); [|exact (HC _)].
  intros w Hw. apply (SPA_entails_J (JRp ph0) (JRp ph0) C2 CP2C s r tp w ENT_2); [|exact Hw].
  intros HJ. eapply (JR_stable A Kc rb tp0 md0 ph0 GR HKc ltac:(lia)); [exact (rho_sub_agree s GR r SID_2) | apply mat_equiv_refl | exact HJ].
Qed.
End LEAF.

Hypothesis Fa0_in : ltac2:(tb__ "0|0|
S36S9S43SfS0S1VLa0;A1A1A1A3").
Hypothesis Fa1_in : ltac2:(tb__ "0|0|
S36S9S12S43A1SfS0S1VLa1;A1A1A1A3").
Hypothesis Fb0_in : ltac2:(tb__ "0|0|
S36S9S43SfS0S1VLb0;A1A1A1A3").
Hypothesis Fb1_in : ltac2:(tb__ "0|0|
S36S9S12S43A1SfS0S1VLb1;A1A1A1A3").
Hypothesis W_a0 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLa0;A1A2A1A1S1aA3").
Hypothesis W_a1 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLa1;A1A2A1A1S1aA3").
Hypothesis W_b0 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLb0;A1A2A1A1S1aA3").
Hypothesis W_b1 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLb1;A1A2A1A1S1aA3").
Hypothesis D_a0 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa0;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S47SaZ40000A1A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1A3A3S1dS9A1A4A2A3").
Hypothesis D_a1 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa1;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S48SaZ40000A1A4S1dG0A1A3S1dS9A1A4A2A3").
Hypothesis D_b0 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb0;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S47SaZ40000A1A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1A3A3S1dS9A1A4A2A3").
Hypothesis D_b1 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb1;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S48SaZ40000A1A4S1dG0A1A3S1dS9A1A4A2A3").
Hypothesis NX_a0 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLa0;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_a1 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLa1;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_b0 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLb0;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_b1 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLb1;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis ENT_a0 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLa0;A1A2VCP2C;Vsa0;A3S1aA3").
Hypothesis ENT_a1 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLa1;A1A2VCP2C;Vsa1;A3S1aA3").
Hypothesis ENT_b0 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLb0;A1A2VCP2C;Vsb0;A3S1aA3").
Hypothesis ENT_b1 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLb1;A1A2VCP2C;Vsb1;A3S1aA3").
Hypothesis SID_a0 : ltac2:(tb__ "0|0|
S5S19S4fVsa0;S27A2S1aA3").
Hypothesis SID_a1 : ltac2:(tb__ "0|0|
S5S19S4fVsa1;S27A2S1aA3").
Hypothesis SID_b0 : ltac2:(tb__ "0|0|
S5S19S4fVsb0;S27A2S1aA3").
Hypothesis SID_b1 : ltac2:(tb__ "0|0|
S5S19S4fVsb1;S27A2S1aA3").

Theorem populate_head : ltac2:(tb__ "0|1|
S11S1cS4dQ40A1A1S58S49VA;Vrb;A2S11VTR;S50S42S59VA;VKc;Vrb;Vtp0;Vmd0;S5bA6M0VCP2C;R1R4A5R3A2Fr';F_;VTR;S50S42G0VLP;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.

  apply (tr_facts Kc TR KIT). intros HF0. pose proof (proj1 (Forall_forall _ _) HF0 _ FP_in) as BF. cbn [holds] in BF.
  apply (tr_pure Kc TR KIT (popfacts A rb)).
  { intros w [_ (HFz & HGh & _)]. apply (entry_popfacts _ _ _ _ _ _ _ HE).
    destruct HGh as (_ & Q221 & _ & _ & _ & _ & _ & Q227 & _).
    unfold cfacts in CF. cbn zeta in CF. destruct CF as (_ & (K1 & _) & _ & (_ & MF0) & _).
    unfold branch_taken, bv_ltu, vNF, vK in BF. cbn [eval] in BF. rewrite Q221, Q227 in BF. unfold gh_nf in *.
    rewrite !u64_lit in BF by lia. apply Z.ltb_lt in BF. exact BF. }
  intros PF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x415c0; 0x41600] LP [La; Lb] ph0 r tp Q R_p1 LN_p NX_p).
  intros L r1 [<-|[<-|[]]] _.
  -
    apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state La) (ax_S CPA) _ _ ph0 r1 tp Q W_pa D_pa NX_pa).
    { intros tr md (HFz & HGh & _) HF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
      split.
      - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        exact (size_hi_val A rb r1 CF RG (proj1 (Forall_forall _ _) HF _ Fa_in)).
      - pose proof (F_pop_hold A rb r1 CF PF RG HGh) as FPH. unfold F_pop in FPH. inversion FPH as [|? ? _ FPH']; subst. exact FPH'. }
    change (ax_setS (la_state La) (ax_S CPA)) with CPA.
    apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41630] CPA [La0; La1] ph0 r1 tp Q R_p2a LN_pa NXr_pa).
    intros L r2 [<-|[<-|[]]] _.
    + exact (join_leaf La0 sa0 true Fa0_in W_a0 D_a0 NX_a0 ENT_a0 SID_a0 r2 tp Q PF (HC PF)).
    + exact (join_leaf La1 sa1 false Fa1_in W_a1 D_a1 NX_a1 ENT_a1 SID_a1 r2 tp Q PF (HC PF)).
  -
    apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state Lb) (ax_S CPB) _ _ ph0 r1 tp Q W_pb D_pb NX_pb).
    { intros tr md (HFz & HGh & _) HF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
      split.
      - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        exact (size_lo_val A rb r1 CF RG (proj1 (Forall_forall _ _) HF _ Fb_in)).
      - pose proof (F_pop_hold A rb r1 CF PF RG HGh) as FPH. unfold F_pop in FPH. inversion FPH as [|? ? _ FPH']; subst. exact FPH'. }
    change (ax_setS (la_state Lb) (ax_S CPB)) with CPB.
    apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41630] CPB [Lb0; Lb1] ph0 r1 tp Q R_p2b LN_pb NXr_pb).
    intros L r2 [<-|[<-|[]]] _.
    + exact (join_leaf Lb0 sb0 true Fb0_in W_b0 D_b0 NX_b0 ENT_b0 SID_b0 r2 tp Q PF (HC PF)).
    + exact (join_leaf Lb1 sb1 false Fb1_in W_b1 D_b1 NX_b1 ENT_b1 SID_b1 r2 tp Q PF (HC PF)).
Qed.
End POP1.
End SpineCallocR7.

(* [comment removed for export] *)
Module SegQ3D_qc.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "app"; "prod"; "list"; "bool"; "true"; "length"; "option"; "Some"; "fst"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "valuation"; "SVar"; "rm"; "SLit"; "rw"; "ss_facts"; "SPAlign"; "obj_range"; "rl"; "ss_next"; "DUnknown"; "SAlu"; "SMd"; "cell"; "holds"; "mkObj"; "mkSS"; "ranges_disjoint"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_objs"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "of_nat"; "add"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "aa_geom"; "cs_cache"; "aa_cache_inited"; "aa_q_global"; "aa_q_thread"; "ag_thread"; "mkQB"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "DQCs"; "clsB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "cell_ok"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc"; "DQC1"; "entC"; "fixed_ok2"; "DQC2"; "N_qc"; "idxP"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "O_sb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs"; "Cqc"; "factsC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel"; "FRM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "cbC"; "DEPTH_R"; "O_gmax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "QFP"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "sv_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Size"; "max_count"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "pre_facts"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue"; "notin_vars"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "O_mtx00"; "STK"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition entC : sv := ltac2:(tb__ "0|0|
S5aS60S24S66S4aS1bZ50A1A3A2").
Definition N_qc : list carve_spec := ltac2:(tb__ "0|d|
S2S7S7S7S17S0A2M0S0A2M1S8S7S7S0S4A2M2S17A2M3A1M4A2M5S3G1G4S3G0S0S3S17S0S4fZ0M6A4Z10M7A4S2G3S3G2S17S3S0S4G6U4M8A4S19PceA1M9A4S2G3S3G2S17S3S0S4Z4G8A4S19PcfA1A4S2G3S3G2S17S3S0S4Z8U8MaA4S19Pc9A1A4S5G3A1MbA3A3A3A4S2G5S3G1G4S3G0S0S3S17S0S5aS4fS23S65G9S1bZ2A1A3A2G7A4Z14A4GbA4S2G5S3G1G4S3G0S0S3S17S0S60Za10McA4Za18A4S2G3S3G2S17S3S0S4GcGaA4S19Pd1A1A4GbA3A4S5G5A1A3A3A3").
Definition SQ1 : sstate := ltac2:(tb__ "0|0|
S3cS49A1S32S28S2fR1A1S30R1A1S2cR1A1S2bR1A1S31R1A1S6S15S2eR1A1S55S70S15S6fS52A4A3S1dR1A1S21R1A1S2dR1A1A9TS;").
Definition DQC1 : axst := ax_setS DQCs SQ1.
Definition DQC2 : axst := ltac2:(tb__ "0|0|
S6aS4eS6S16S1dS3cS4eA1A1S6S16S5eS2S16S1eP97ZcA2S5S16A1A3A3A3A2").
Definition idxP : list nat := ltac2:(tb__ "0|0|
S2S4U0S2S4U9S2S4UaS2S4UbS2S4U8S2S4U6S2S4U7S2S4U1S2S4U2S2S4U3S2S4U4S2S4U5S5S4A1A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma DQC1_swf : swf SQ1 = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DQC2_below : ltac2:(tb__ "0|1|
S10S9S78S16S2aS21S3cS4eA1M0A1A1S6S16S1dG0A1S6S16S5eS2S16S1eP97ZcA2S5S16A1A3A3A3A3SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cqc_eq : ltac2:(tb__ "0|0|
S10ScS3dA1S59S51S2S57S58S53A1S5S57A1A3A2SdS3dS5dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DQCs_vars : ltac2:(tb__ "0|1|
S11S10S9S68S74S2S1PceS2S1PcfS2S1Pc9S2S1Pd1S5S1A1A3A3A3A3A1M0S3cS49A1A2SaA3S10S9S69G0S3eS49A1A2SaA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition fixed_ok2 (rho : valuation) (T : Z) (o : sobj) : Prop := ltac2:(tb__ "0|2|
S13S11S33Ze4000SeS0S0S1fVrho;Vo;A2M0A3M1A2S33SfS0S0G0A3Z646000A2A2S33VT;G1A2A2").
Lemma OBD_fixed2 : ltac2:(tb__ "0|2|
S40S18S8S25A1M0G0S73R4R3A2S54S16S26R4A1S72S61A1A3S54S15S50R5S48S41R6A1A1A2S6S15S6S15S77R4S27S19PaA1S1bNa8A1S1bZ0A1R3S22A5A2S2S15S76S2S15S62S5S15A1M1A3A3A3S6S15S71S2S15S5bG1A3A3A3A3F_;F_;Fswc;Fcb;Frho;FA;").
Proof.
  intros A rho cb swc HT HF. destruct (stk_facts A rho HT HF) as (HD & HTOP & Hsp). pose proof (topG_range (aa_geom A)) as TG.
  destruct (stk_ranges rho _ _ cb swc eq_refl eq_refl ltac:(lia) HD) as (R1 & R2 & R3 & R4).
  unfold STK. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; unfold fixed_ok2.
  - right. rewrite R1. cbn [fst]. lia.
  - right. rewrite R2. cbn [fst]. lia.
  - right. rewrite R3. cbn [fst]. lia.
  - right. rewrite R4. cbn [fst]. lia.
  - left. unfold O_mtx00, carved. rewrite obj_range_mk by (unfold QG; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold QG. lia.
  - left. unfold O_gmax, carved. rewrite obj_range_mk by (unfold QG; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold QG. lia.
  - left. unfold O_got. rewrite obj_range_mk by (unfold GOT_LO, GOT_HI; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold GOT_LO, GOT_HI. lia.
  - left. unfold O_rtc. rewrite obj_range_mk by (unfold RTC_LO, RTC_HI; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold RTC_LO, RTC_HI. lia.
  - left. unfold O_sb, carved. rewrite obj_range_mk by lia. cbn [fst snd eval]. rewrite u64_lit by lia. lia.
Qed.
Lemma fixed_clear2 : ltac2:(tb__ "0|0|
S18S0S15S0S0S50R5R4R3A3S13S33R2Z10000A2S33Z646000R3A2A2S33R3R6A2S29S1fR8R6A2S3S0S0R5R4A4A2F_;F_;F_;Fhi;Flo;Fo;FT;Frho;").
Proof. intros rho T o lo hi [[H1 H2]|H] HZ HT; unfold ranges_disjoint; destruct (obj_range rho o) as [x y]; cbn [fst snd] in *; lia. Qed.

Section QCPre.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).

Lemma qc_pre : ltac2:(tb__ "0|7|
S40S0S0S0S4S8S3fA1M0G0S18S8S3aQ40M1A1M2A1S67S10G0S45RaA1S5S3fA1A3S10S9S43RbA1SaA3S10G0S44RcA1S2S3fS47RbS5S7S0S0A2A1M3RaA3S6S3fR7R6A3A3A3S34S35SbS0S42S63RdZ18M4A2A1A2A1S6eG4A1M5A2S56S38S5cVK;VA0;Vrho0;ReRdRbRaG3R9R8AaS49R7R6R5A6S10G2S1cR8Pa6A2S39G1ReA2A3S14S0S0S11S11S33Z0R1A2S34R1S37Z2Z40A2A2A2S11S4cS4bS38S1aRaA1A2S4dS36S46S41R11A1A1Zae0A2U8R1A3A2S56S38S5cVK;VA0;Vrho0;R11R10ReRdG3RcRbAaS5dS75RaS2S7S1G2A2M6S3S1G2PceS39G1S35SbS0S42S63R11G4A2A1A2A1A2A4S2G6S3S1G2PcfS39G1G5A2A4S2G6S3S1G2Pc9S39G1S6dG4A1A2A4S2G6S3S1G2Pd1S39G1R1A2A4S5G6A1A3A3A3A3A2R9R8A6A2A2Lst;A2F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd tmp' rest rho tp w HTH HCI HGL HNF H E166. destruct w as [tr [ms md]].
  pose proof (proj1 (proj2 H)) as HK. cbn [w_tr w_cfg cfg_model fst snd] in HK.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  destruct HRIG as (E151 & E152 & E155 & E156). pose proof (HCLS HCI 24 ltac:(lia)) as CV.
  pose proof (cv_count _ _ _ _ _ CV) as C_cnt. pose proof (cv_max _ _ _ _ _ CV) as C_max. pose proof (cv_size _ _ _ _ _ CV) as C_sz. pose proof (cv_pc_present _ _ _ _ _ CV) as P_pc.
  pose proof (cv_len _ _ _ _ _ CV) as K_le. unfold pc_entry in C_cnt, C_max, C_sz, P_pc. change (max_count 24) with 2 in *. change (Size 24) with 8192 in *.
  set (T := ag_thread (aa_geom A)) in *. set (k := Z.of_nat (length (cs_cache (cls_of A 24)))) in *.
  pose proof (geom_old _ HG) as HG'. destruct HG' as (_ & _ & _ & _ & G5 & G6 & G7 & _). fold T in G5, G6, G7.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. fold T in TI. pose proof (topG_range (aa_geom A)) as TG.
  assert (PST : present (view segsA (rm rho)) (T + 2784) (T + 2784 + 8)) by (intros z Hz; apply HST; fold T; lia).
  destruct (present_cell8q _ _ PST) as (st & Hst & C_st). exists st. split; [exact Hst|]. split; [exact C_st|].

  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE.
  destruct (batch_sb_facts K HL A (mkQB a [] s) rho tp tr md HTH HCI HK ltac:(rewrite HGL; left; reflexivity)) as (_ & SB0 & SB1 & SB2 & SB3). cbn [qb_addr] in SB2, SB3.
  destruct BE as [_ _ HQP HAU _ _ _].
  destruct (batch_slot A HQP HAU HG (mkQB a [] s) ltac:(rewrite (qall_A1 A HTH), HGL; left; reflexivity)) as (y & Ey & Y0 & _ & Y1 & _). cbn [qb_addr] in Ey. rewrite kUserSpaceSize_val in Y1.
  set (rho2 := rho_sets rho [(206%positive, Z_to_bv 64 k); (207%positive, Z_to_bv 64 2); (201%positive, Z_to_bv 64 8192); (209%positive, Z_to_bv 64 st)]).
  pose proof (JRI_stable K HL A0 rho0 A a n0 nd [] tmp' rest) as HSTB.
  assert (H1 : SPA segsA (JRI K A0 rho0 A a n0 nd [] tmp' rest) DQCs rho2 tp (tr, mkCfg ms md)).
  { apply (SPA_bindV segsA _ NPRE DQCs rho tp _ _ eq_refl HSTB); [| exact (proj1 DQCs_vars) | exact (proj2 DQCs_vars) | exact H].
    intros v Hv. cbn in Hv. destruct Hv as [<-|[<-|[<-|[<-|[]]]]]; unfold NPRE, Pos.le; cbn; discriminate. }
  assert (OTH : forall i, i <> 206%positive -> i <> 207%positive -> i <> 201%positive -> i <> 209%positive -> rw rho2 i = rw rho i).
  { intros i N1 N2 N3 N4. unfold rho2. apply rho_sets_other. cbn. intros [X|[X|[X|[X|[]]]]]; congruence. }
  assert (ERM : rm rho2 = rm rho) by (unfold rho2; apply rm_rho_sets).
  assert (E206 : rw rho2 206%positive = Z_to_bv 64 k) by reflexivity. assert (E207 : rw rho2 207%positive = Z_to_bv 64 2) by reflexivity.
  assert (E201 : rw rho2 201%positive = Z_to_bv 64 8192) by reflexivity. assert (E209 : rw rho2 209%positive = Z_to_bv 64 st) by reflexivity.
  assert (EC : eval rho2 clsB = Z_to_bv 64 24).
  { apply (clsB_val rho2 (ag_spacebeg (aa_geom A)) a y); try lia; rewrite OTH by discriminate; assumption. }
  assert (EcbC : eval rho2 cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply (eval_add_lit A); try lia; unfold vT; cbn [eval]; rewrite OTH by discriminate; exact E151).
  assert (Eent : bv_unsigned (eval rho2 entC) = T + 2128).
  { unfold entC, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC, EC. change (eval rho2 (SLit 80)) with (Z_to_bv 64 80). rewrite !u64_lit by lia. unfold M64v.
    rewrite (Z.mod_small (24 * 80)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Eslot : bv_unsigned (eval rho2 (add entC (SAlu ALU_SLL (SVar 206) (SLit 2)))) = T + 2128 + 4 * k).
  { unfold add at 1. rewrite U_add, U_sll_lit, Eent. cbn [eval]. rewrite E206, u64_lit by lia. change (2 mod 64) with 2. unfold M64v. rewrite (Z.mod_small (k * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. lia. }
  pose proof (D_pre_facts DQCs _ eq_refl rho2 (SPA_facts_hold segsA _ rho2 DQCs tp _ H1)) as HFpre.
  assert (HTOP2 : top_high A rho2) by (unfold top_high in *; rewrite !OTH by (unfold V_DEPTH; discriminate); exact HKTOP).
  assert (TBLK : forall lo hi, T <= lo -> hi <= T + 4096 -> (hi <= 0x10000 \/ 0x646000 <= lo)) by (intros lo hi B1 B2; clear -TI B1 B2; lia).
  assert (H2 : SPA segsA (JRI K A0 rho0 A a n0 nd [] tmp' rest) DQC1 rho2 tp (tr, mkCfg ms md)).
  { pose proof (SPA_carve_list segsA _ rho2 DQCs tp _ N_qc (ss_next (ax_S DQCs)) H1) as X. cbn zeta in X. apply X; clear X.
    - exact DQC1_swf.
    - apply Pos.le_refl.
    - unfold N_qc. repeat apply Forall_cons; try apply Forall_nil.
      + rewrite Eent. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split; [|split].
        * intros off Hoff. rewrite ERM. destruct (Z_lt_dec off 4); [|destruct (Z_lt_dec off 8)].
          -- eapply (cell_wok_rd2 _ _ _ _ _ C_cnt); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
          -- eapply (cell_wok_rd2 _ _ _ _ _ C_max); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
          -- eapply (cell_wok_rd2 _ _ _ _ _ C_sz); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
        * unfold cells_in_view. rewrite ERM. repeat apply Forall_cons; try apply Forall_nil.
          -- eapply (civ_cell rho2 (rm rho) (T + 2128) 0); [replace (T + 2128 + 0) with (T + 208 + 80 * 24) by lia; exact C_cnt | cbn [eval]; exact E206 | lia | lia].
          -- eapply (civ_cell rho2 (rm rho) (T + 2128) 4); [replace (T + 2128 + 4) with (T + 208 + 80 * 24 + 4) by lia; exact C_max | cbn [eval]; exact E207 | lia | lia].
          -- eapply (civ_cell rho2 (rm rho) (T + 2128) 8); [replace (T + 2128 + 8) with (T + 208 + 80 * 24 + 8) by lia; exact C_sz | cbn [eval]; exact E201 | lia | lia].
        * intros rr yy j Hin. destruct Hin.
      + rewrite Eslot. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [unfold cells_inside; apply Forall_nil|]. split; [|split].
        * intros off Hoff. rewrite ERM. destruct (P_pc (T + 2128 + 4 * k + off) ltac:(lia)) as [bb Hbb]. rewrite view_in in Hbb by lia.
          eapply wok_rd_off_image2; [lia | | exact Hbb]. destruct (TBLK (T + 2128 + 4 * k + off) (T + 2128 + 4 * k + off + 1) ltac:(lia) ltac:(lia)); lia.
        * unfold cells_in_view. apply Forall_nil.
        * intros rr yy j Hin. destruct Hin.
      + rewrite EcbC, u64_lit by lia. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split; [|split].
        * intros off Hoff. rewrite ERM. eapply (cell_wok_rd2 _ _ _ _ _ C_st); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
        * unfold cells_in_view. rewrite ERM. repeat apply Forall_cons; try apply Forall_nil.
          eapply (civ_cell rho2 (rm rho) (T + 208) 2576); [replace (T + 208 + 2576) with (T + 2784) by lia; exact C_st | cbn [eval]; exact E209 | lia | lia].
        * intros rr yy j Hin. destruct Hin.
    - pose proof (OBD_fixed2 A rho2 cb_cells (ob_cells (SWD vXK vXF vXL vXS)) HTOP2 HFpre) as FX.
      assert (R1 : obj_range rho2 (carve_obj (entC, 0, 16, [(0, 4%nat, SVar 206); (4, 4%nat, SVar 207); (8, 8%nat, SVar 201)])) = (T + 2128 + 0, T + 2128 + 16)) by (unfold carve_obj, carved; rewrite obj_range_mk by lia; rewrite Eent; reflexivity).
      assert (R2 : obj_range rho2 (carve_obj (add entC (SAlu ALU_SLL (SVar 206) (SLit 2)), 16, 20, [])) = (T + 2128 + 4 * k + 16, T + 2128 + 4 * k + 20)) by (unfold carve_obj, carved; rewrite obj_range_mk by lia; rewrite Eslot; reflexivity).
      assert (R3 : obj_range rho2 (carve_obj (cbC, 2576, 2584, [(2576, 8%nat, SVar 209)])) = (T + 208 + 2576, T + 208 + 2584)) by (unfold carve_obj, carved; rewrite obj_range_mk by lia; rewrite EcbC, u64_lit by lia; reflexivity).
      unfold N_qc. cbn [map]. apply Forall_cons; [rewrite R1 | apply Forall_cons; [rewrite R2 | apply Forall_cons; [rewrite R3 | apply Forall_nil]]];
        (eapply Forall_impl; [|exact FX]); intros o Ho; apply (fixed_clear2 rho2 (topG (aa_geom A)) o _ _ Ho); try lia; try (apply TBLK; lia).
    - unfold N_qc. cbn [map pairwise_disjoint].
      assert (R1 : obj_range rho2 (carve_obj (entC, 0, 16, [(0, 4%nat, SVar 206); (4, 4%nat, SVar 207); (8, 8%nat, SVar 201)])) = (T + 2128 + 0, T + 2128 + 16)) by (unfold carve_obj, carved; rewrite obj_range_mk by lia; rewrite Eent; reflexivity).
      assert (R2 : obj_range rho2 (carve_obj (add entC (SAlu ALU_SLL (SVar 206) (SLit 2)), 16, 20, [])) = (T + 2128 + 4 * k + 16, T + 2128 + 4 * k + 20)) by (unfold carve_obj, carved; rewrite obj_range_mk by lia; rewrite Eslot; reflexivity).
      assert (R3 : obj_range rho2 (carve_obj (cbC, 2576, 2584, [(2576, 8%nat, SVar 209)])) = (T + 208 + 2576, T + 208 + 2584)) by (unfold carve_obj, carved; rewrite obj_range_mk by lia; rewrite EcbC, u64_lit by lia; reflexivity).
      repeat split; repeat apply Forall_cons; try apply Forall_nil; try exact I; unfold ranges_disjoint; rewrite ?R1, ?R2, ?R3; cbn [fst snd]; lia. }
  assert (H3 : SPA segsA (JRI K A0 rho0 A a n0 nd [] tmp' rest) DQC2 rho2 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact DQC2_below |]. intros HF. apply Forall_app. split; [exact HF|]. rewrite factsC_eq. apply Forall_app. split; [apply Forall_app; split|].
    - exact (stk_facts_hold A rho2 HTOP2 HFpre).
    - exact (qc_it_facts rho2 k EC E206 E207 ltac:(change (max_count 24) with 2; lia)).
    - apply Forall_cons; [|apply Forall_nil]. cbn [holds]. split; [lia|]. rewrite OTH by discriminate. rewrite E151, u64_lit by lia. change (2 ^ 12) with 4096. unfold PG in G7. exact G7. }
  exact (SPA_axforms segsA _ _ rho2 _ _ tp _ Cqc_eq H3).
Qed.
End QCPre.

Lemma FRM_absorb_QFP : ltac2:(tb__ "0|5|
S40S18S18S18S0OF_;S0S13R2R1A1M0S12G0A1A2Fz;S1S10S3aQ40M1A1M2S1cR4R1A2S1cR5R1A2A3Fi;S1S10S8S3aQ8A1M3A1S20R5R1A2S20R6R1A2A3Fl;S0R5R1A1S11S64RaR2A2S12S11S33S6cR2A2S34R2S6bA2A2A1A2F_;Fz;S0S12R6R1A1A1S10ScG3A1M4S4bS38S1aR8A1R2A3S4bS38S1aR9A1R2A3A3F_;Fz;G2S12R7S3bG1R1A2A1A1S10G4S1aR9R2A2S1aRaR2A2A3F_;Fa;S5fRbRaR9A3S5fRcRbR9A3F_;F_;F_;F_;F_;F_;F_;FP;Frho3;Frho;Frho0;FA0;").
Proof.
  intros A0 rho0 rho rho3 P PD Hrw Hrl HP FR FRrm ((F1 & F1') & F2 & F3 & F4).
  split; [split; [intros i Hi; rewrite Hrw; exact (F1 i Hi) | intros l; rewrite Hrl; exact (F1' l)]|]. split; [|split].
  - intros a NQ. rewrite FRrm; [exact (F2 a NQ)|]. intros Hp. apply NQ. left. exact (proj1 (HP _ Hp)).
  - intros z NQ. rewrite <- (F3 z NQ). apply FR. intros Hp. exact (NQ (proj1 (HP _ Hp))).
  - intros a HB Hdef. rewrite FRrm; [exact (F4 a HB Hdef)|]. intros Hp. exact (proj2 (HP _ Hp) HB).
Qed.
End SegQ3D_qc.

(* [comment removed for export] *)
Module SegQ3D_qip.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "prod"; "bool"; "list"; "nil"; "app"; "true"; "option"; "Some"; "snd"; "fst"; "length"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "mul"; "div"; "modulo"; "sub"; "opp"; "of_nat"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "SVar"; "rm"; "eval"; "sprop"; "valuation"; "ss_objs"; "SAlu"; "ss_facts"; "rw"; "ss_next"; "SPAlign"; "SPUle"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "swf"; "DUnknown"; "SMd"; "cell"; "holds"; "mkObj"; "obj_range"; "soff"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "in_zone"; "zcheck"; "zdisjb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "ax_X"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "aa_geom"; "aa_cache_inited"; "aa_q_global"; "aa_q_thread"; "mkQB"; "cs_cache"; "topG"; "ag_spacebeg"; "ag_thread"; "cs_allocated_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "DQI0"; "zhiQ"; "zloQ"; "qienv"; "entQ"; "O_ishQ"; "ZD_fix"; "ZD_itm"; "ZD_rti"; "zbQ"; "DQI1"; "DQI2"; "N_itm"; "SQI2"; "ZUQ"; "carve_okq"; "rieQ"; "shQ"; "BLQ"; "DQI3"; "N_qi"; "N_rti"; "SQI1"; "idxQ"; "@Stdlib.Lists.List"; "In"; "forallb"; "Forall2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "xwords_clear"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "O_sb"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "cells_in_view"; "cells_inside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "DQIs"; "vIT"; "O_it"; "vB"; "vS7"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "max_count"; "HIGH_SHADOW_END"; "is_primary"; "rz"; "K_HIGH_MEM_END"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRI"; "CURB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "QG"; "DEPTH_R"; "O_gmax"; "cbC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "it_cls"; "it_ab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QW"; "cls_of"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "ALU_SRL"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vCTX"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs"; "Cqi"; "factsQ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "vRIS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "pre_facts"; "top_high"; "A_globals"; "GOT_HI"; "GOT_LO"; "RTC_HI"; "RTC_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith"; "vb_of"; "QIV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel"; "HVI"; "HVS"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "sv_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue"; "notin_vars"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "O_mtx00"; "STK"; "SWD"; "cb_cells"; "vXF"; "vXK"; "vXL"; "vXS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states"; "kAllocBegMagic"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition DQI0 : axst := dropl (dropl DQIs).
Definition rieQ : sv := ltac2:(tb__ "0|0|
S7bSacS28S9dS22Pc8A1S21Z7A1A3A2").
Definition entQ : sv := ltac2:(tb__ "0|0|
S7bS98S38S9fS22Pc8A1S21Z50A1A3A2").
Definition shQ : sv := ltac2:(tb__ "0|0|
S7bS28S9eS7bS85S21Z10A1A2S21Z3A1A3S21Z7fff8000A1A2").
Definition N_rti : list carve_spec := ltac2:(tb__ "0|17|
S2S5S5S5S1fS0A2M0S0A2M1S7S5S5S0S3A2M2S1fA2M3A1M4A2M5S4G1G4S4G0S0S4S1fS0S21Z0A1M6Zeddb8M7A4Zeddc4A4S2G3S4G2S1fS4S0S3G7U8M8A4S7dA4S2G3S4G2S1fS4S0S3Zeddc0U4M9A4S21ZffffffffA1A4S8G3A1MaA3A3A4S2G5S4G1G4S4G0S0S4S1fS0G6Zeddc8MbA4Zeddd1A4S2G3S4G2S1fS4S0S3GbG8A4SacA4S2G3S4G2S1fS4S0S3Zeddd0U1McA4G6A4GaA3A3A4S2G5S4G1G4S4G0S0S4S1fS0G6Ze9af0MdA4Ze9af8A4S2G3S4G2S1fS4S0S3GdG8A4S21Zde378A1A4GaA3A4S2G5S4G1G4S4G0S0S4S1fS0G6Zf0c5cMeA4Zf0c5dA4S2G3S4G2S1fS4S0S3GeGcA4S21Z1A1MfA4GaA3A4S2G5S4G1G4S4G0S0S4S1fS0G6Zf0c60M10A4Zf0c61A4S2G3S4G2S1fS4S0S3G10GcA4GfA4GaA3A4S2G5S4G1G4S4G0S0S4S1fS0G6Zf0c64M11A4Zf0c68A4S2G3S4G2S1fS4S0S3G11G9A4G6A4GaA3A4S2G5S4G1G4S4G0S0S4S1fS0G6Z624560M12A4Z624568A4S2G3S4G2S1fS4S0S3G12G8A4S21Z645960M13A1A4GaA3A4S2G5S4G1G4S4G0S0S4S1fS0G6G13A4Z645968A4S2G3S4G2S1fS4S0S3G13G8A4Sa0A4GaA3A4S2G5S4G1G4S4G0S0S4S1fS0Sa0Z98M14A4Za0A4S2G3S4G2S1fS4S0S3G14G8A4Sa1A4GaA3A4S2G5S4G1G4S4G0S0S4S1fS0G6Zf20d8M15A4Zf20daA4S2G3S4G2S1fS4S0S3G15GcA4GfA4S2G3S4G2S1fS4S0S3Zf20d9GcA4GfA4GaA3A3A4S2G5S4G1G4S4G0S0S4S1fS0G6Zf20e0M16A4Zf20f8A4S2G3S4G2S1fS4S0S3G16G8A4S21S91A1A4S2G3S4G2S1fS4S0S3Zf20e8G8A4G6A4S2G3S4G2S1fS4S0S3Zf20f0G8A4G6A4GaA3A3A3A4S8G5A1A3A3A3A3A3A3A3A3A3A3A3").
Definition N_itm (vb : bool) : list carve_spec := ltac2:(tb__ "0|12|
S9S5S5S5S1fS0A2M0S0A2M1S7S5S5S0S3A2M2S1fA2M3A1M4A2M5S2G5S4G1G4S4G0S0S4S1fS0S68Z30M6A4Z38A4S2G3S4G2S1fS4S0S3G6U8M7A4S22PcaA1A4S8G3A1M8A3A4S2G5S4G1G4S4G0S0S4S1fS0S85Z0M9A4Z8MaA4S2G3S4G2S1fS4S0S3G9U4MbA4McS22PcbA1A4S2G3S4G2S1fS4S0S3Z4GbA4MdS22PccA1A4G8A3A3A4S2G5S4G1G4S4G0S0S4S1fS0S5cG9A4Z10MeA4S2G3S4G2S1fGcS22PceA1MfA4S2G3S4G2S1fGdS22PcfA1A4S2G3S4G2S1fS4S0S3GaG7A4M10S22Pc9A1A4G8A3A3A3A4S2G5S4G1G4S4G0S0S4S1fS0S7bS5cS28S9dGfS21Z2A1A3A2GeA4Z14A4G8A4S2G5S4G1G4S4G0S0S4S1fS0Sa1Zad0A4Zc60A4S2G3S4G2S1fS4S0S3Zae0G7A4S22Pd1A1A4G8A3A4S8G5A1M11A3A3A3A3A3S6S7G5A1Lvb;Vvb;S2G5S4G1G4S4G0S0S4S1fS0S22Pd2A1G9A4GeA4S2G3S4G2S1fS4S0S3G9G7A4S21Sc8A1A4S2G3S4G2S1fG10S85A4G8A3A3A4G11A3G11X6x2A3").
Definition N_qi (vb : bool) : list carve_spec := N_rti ++ N_itm vb.
Definition O_ishQ : sobj := ltac2:(tb__ "0|0|
S3bS69S21Z0A1S28S9eS22PcdA1S21Z3A1A3S8S39A1S37A5").
Definition SQI1 (vb : bool) : sstate := ltac2:(tb__ "0|0|
S47S58A1S35S2eS32R1A1S33R1A1S30R1A1S2fR1A1S34R1A1S9S20S27R1A1S8aS78S20S79S6cVvb;A1A4A3S29R1A1S2bR1A1S31R1A1A9TS;").
Definition DQI1 (vb : bool) : axst := ax_setS DQI0 (SQI1 vb).
Definition SQI2 (vb : bool) : sstate := ltac2:(tb__ "0|0|
S47S62Vvb;A1A1S35S2eS32R1A1S33R1A1S30R1A1S2fR1A1S34R1A1S9S20S27R1A1S2S20S5dS8S20A1A3A3S29R1A1S2bR1A1S31R1A1A9TS;").
Definition DQI2 (vb : bool) : axst := ltac2:(tb__ "0|0|
S49S62Vvb;A1S65Vvb;A1A2").
Definition DQI3 (vb : bool) : axst := ltac2:(tb__ "0|1|
SbdS63Vvb;A1M0S9S25S29S47G0A1A1Sa3Vvb;A1A3A2").
Definition idxQ (vb : bool) : list nat := ltac2:(tb__ "0|b|
S6S7S3A1Lvb;Vvb;S9S3S2S3U0S2S3U6S2S3U7S8S3A1M0A3A3A3M1S9S3S8bU8UbA2M2S2S3U2M3S2S3U13M4S2S3U14M5S2S3U19S2S3U15M6S2S3U16M7S2S3U17M8S2S3U18M9S2S3U1S2S3U3S2S3U4S2S3U5G0A3A3A3A3MaA3A3A3A3A3A3A3A3A3A3S9S3G1S9S3G2S2S3G3S2S3G4S2S3G5S2S3G9S2S3G6S2S3G7S2S3G8GaA3A3A3A3A3A3A3A3A3X6x2").
Lemma DQI1_swf : ltac2:(tb__ "0|0|
S6S1bS6S36S6eR1A1A1SaA3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DQI2_swf : ltac2:(tb__ "0|0|
S6S1bS6S36S65R1A1A1SaA3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DQI3_below : ltac2:(tb__ "0|1|
S6S1bS6S71S25S3eS2bS47S63R1A1A1M0A1A1S9S25S29G0A1Sa3R1A1A3A3SaA3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cqi_eq : ltac2:(tb__ "0|0|
S6S1bSbS48A1SabS6bR1A1S2Sa9SaaS6fR1A1A1S8Sa9A1A3A2ScS48Sa2R1A1A2A3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DQI0_vars : ltac2:(tb__ "0|1|
S1aS1bS6SbbSbfS2S1Pc8S2S1Pc9S2S1PcaS2S1PcbS2S1PccS2S1PcdS2S1PceS2S1PcfS2S1Pd1S2S1Pd2S8S1A1A3A3A3A3A3A3A3A3A3A3A1M0S47S58A1A2SaA3S1bS6SbcG0S4bS58A1A2SaA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma DQIs_objs2 : ltac2:(tb__ "0|0|
S1bS7S20A1S27S47S84A1A1S9S20S27S47S58A1A1S2S20S7cS2S20S86S8S20A1A3A3A3A3"). Proof. reflexivity. Qed.
Lemma DQI0_eq : ltac2:(tb__ "0|0|
S1bS48S49S84SbaS47S84A1S27S47S58A1A1A2A2S58A3"). Proof. reflexivity. Qed.
Lemma DQI0_objs : ltac2:(tb__ "0|0|
S1bS7S20A1S27S47S58A1A1S9S20S9S20Sc1Sc3Sc2Sc5Sc4Sc6Sc7A4A2S2S20Sc0S2S20S97S8S20A1A3A3A3SafA3A3"). Proof. reflexivity. Qed.
Lemma DQI0_facts : ltac2:(tb__ "0|0|
S1bS7S25A1S29S47S58A1A1S9S25SadS96A1S2S25S2dS21S8eA1S87A2S2S25S2cPa6Z4A2S2S25S2dS21S11S8eZ98A2A1S88A2S2S25S2cPa3Z3A2S8S25A1A3A3A3A3A3A3").
Proof. reflexivity. Qed.

Lemma hdr_word_cell : ltac2:(tb__ "0|8|
S74S0S0S0S0S1aS10Z0R3A2M0S13R3Z100M1A2A2M2G2S1aG0S13R3Z10000M3A2A2S1bSbS40Q8M4A1M5A1M6R8R7A1ScG5S41G4R6A2A2M7A3S1bG6R9S11R8Z1A2A1G7A3S75RaS76S11R9Z2A2U2R6A3A2S75RbS76RaU4S11S11R9S14G1R8A2A2S14G3R7A2A2A3A2F_;F_;F_;F_;F_;F_;Fq;Ft;Fs;Fa;Fm;").
Proof.
  intros m a s t q Hs Ht Hq H0 H1 H2 k Hk. cbn [c_addr c_w RtCells.c_val] in Hk |- *. rewrite nth_enc_bytes by lia.
  assert (LB : forall j, le_byte (s + 256 * t + 65536 * q) 4 j = nth j [s; t; q mod 256; q / 256] 0 \/ (4 <= j)%nat).
  { intros j. unfold le_byte. rewrite (Z.mod_small (s + 256 * t + 65536 * q)) by (change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia).
    destruct j as [|[|[|[|j]]]]; [left|left|left|left|right; lia]; cbn [nth Z.of_nat Z.mul Pos.mul]; rewrite Z.shiftr_div_pow2 by lia.
    - rewrite Z.pow_0_r, Z.div_1_r. replace (s + 256 * t + 65536 * q) with (s + (t + 256 * q) * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
    - change (2 ^ 8) with 256. replace (s + 256 * t + 65536 * q) with (s + (t + 256 * q) * 256) by lia. rewrite Z.div_add by lia. rewrite (Z.div_small s) by lia.
      rewrite Z.add_0_l. replace (t + 256 * q) with (t + q * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
    - change (2 ^ 16) with 65536. replace (s + 256 * t + 65536 * q) with ((s + 256 * t) + q * 65536) by lia. rewrite Z.div_add by lia.
      rewrite (Z.div_small (s + 256 * t)) by lia. rewrite Z.add_0_l. reflexivity.
    - change (2 ^ 24) with (65536 * 256). rewrite <- (Z.div_div _ 65536 256) by lia. replace (s + 256 * t + 65536 * q) with ((s + 256 * t) + q * 65536) by lia.
      rewrite Z.div_add by lia. rewrite (Z.div_small (s + 256 * t)) by lia. rewrite Z.add_0_l. apply Z.mod_small.
      split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  destruct (LB 0%nat) as [L0|L0]; [|lia]. destruct (LB 1%nat) as [L1|L1]; [|lia]. destruct (LB 2%nat) as [L2|L2]; [|lia]. destruct (LB 3%nat) as [L3|L3]; [|lia].
  cbn [nth] in L0, L1, L2, L3. destruct k as [|[|[|[|k]]]]; [| | | |lia].
  - rewrite L0. replace (a + Z.of_nat 0) with a by lia. exact H0.
  - rewrite L1. replace (a + Z.of_nat 1) with (a + 1) by lia. exact H1.
  - rewrite L2. pose proof (H2 0%nat ltac:(cbn; lia)) as X. cbn [c_addr c_w RtCells.c_val] in X.
    replace (a + Z.of_nat 2) with (a + 2 + Z.of_nat 0) by lia. rewrite X. rewrite nth_enc_bytes by lia. f_equal. apply Z_to_bv8_eq.
    unfold le_byte. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 16) with 65536. rewrite (Z.mod_small q 65536) by lia. reflexivity.
  - rewrite L3. pose proof (H2 1%nat ltac:(cbn; lia)) as X. cbn [c_addr c_w RtCells.c_val] in X.
    replace (a + Z.of_nat 3) with (a + 2 + Z.of_nat 1) by lia. rewrite X. rewrite nth_enc_bytes by lia. f_equal. apply Z_to_bv8_eq.
    unfold le_byte. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 1) with 8. change (2 ^ 16) with 65536. rewrite (Z.mod_small q 65536) by lia.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma max_count_le16q : ltac2:(tb__ "0|0|
S0S1aS10Z1R1A2S10R1Z1eA2A2S10S8dR2A1Z10A2F_;Fc;").
Proof.
  assert (H : forallb (fun c => max_count c <=? 16) (zseq 1 30) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  intros c Hc. pose proof (range_check _ 1 30 H c ltac:(lia)) as X. apply Z.leb_le in X. exact X.
Qed.
Lemma present_byte : ltac2:(tb__ "0|2|
S74S0S77R2R1S11R1Z1A2A3S1dS0S0S1aS1aS10Z0R1A2S13R1Z100A2A2S1bSbS40Q8M0A1M1A1R4R3A1ScG1S41G0R1A2A2A3A2Lt;A2F_;Fa;Fm;").
Proof.
  intros m a Hp. destruct (Hp a ltac:(lia)) as [b Hb]. exists (bv_unsigned b). split.
  - pose proof (bv_unsigned_in_range _ b) as R. change (bv_modulus 8) with 256 in R. exact R.
  - rewrite Z_to_bv_bv_unsigned. exact Hb.
Qed.
Lemma wr_present : ltac2:(tb__ "0|3|
S40Q40M0A1SbS40Q8A1M1A1M2F_;S0S0S0S77S73S3fR4A2R3R2A3S1aS10R4R2A2S13R2R3A2A2S10Z0R5A2S10R5S12Z2Z40A2A2S1cS10R6Z10000A2S10Z646000R7A2A2S1aS1bS6S81S3fR9S41G0R6A2A3SaA3S1dG1G1S1bG2S80S3fRaS41G0R7A2A3ScG1R1A2A3Ly;A2A2F_;F_;F_;F_;F_;Fz;Fhi;Flo;Fmm;").
Proof.
  intros mm lo hi z Hp Hz Hlo Hhi Ho. destruct (Hp z Hz) as [b Hb]. rewrite view_in in Hb by lia.
  eapply wok_rd_off_image2; [lia | lia | exact Hb].
Qed.
Lemma ev_add_lit : ltac2:(tb__ "0|7|
S26S1fS0S0S1bS40Q40M0A1M1S24R4R3A2S41G0R2A2A3S1aS10Z0M2R3A2S13R3S12Z2M3Z40A2M4A2A2S1aS10S18S12G3Z3fA2M5A1R3A2S13R3G5A2A2S1aS10G2S11R5R4A2M6A2S13G6G4A2A2S1bG1S24R8S7bR7S21R5A1A2A2S41G0S11R6R5A2A2A3F_;F_;F_;F_;Fk;Fx;Fa;Frho;").
Proof.
  intros rho a x k Ea Hx Hk Hs. apply bv_eq. unfold add. cbn [eval]. rewrite add_val, Ea, (u64_lit x), (u64_lit (x + k)) by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.

Definition carve_okq (rho : valuation) (k : carve_spec) : Prop := ltac2:(tb__ "0|8|
S5S5S5S1fS0A2M0S0A2M1S7S5S5S0S3A2S1fA2A1M2A2OLk;Vk;G1G2G1OLp;R2G0S0G0OLp0;R2S1fS0S42Q40M3S24Vrho;R2A2A2S0S1aS10S18S12Z2M4Z3eA2M5A1R2A2S1aS10R2R4A2S1aS13R4G5A2S1aS10Z0S11R1R2A2A2S1aS10S11R1R4A2S12G4Z40A2A2S1aS83R2R4R6A3S1aS0S1aS10R3R1A2S13R1R5A2A2S1aS1bS6S81S3fS23Vrho;A1M6S41G3S11R3R2A2A2A3SaA3S1dS40Q8A1M7G7S1bSbG7A1S80S3fG6S41G3S11R4R3A2A2A3ScG7R1A2A3Lx;A2A2F_;Foff;S82Vrho;S80S3fG6A2R1R6A4A2A2A2A2A2A2A2Tb;Llo;Lbase;X5x1Lhi;Lp0;X5x1Lcs;Lp;X5x1").
Lemma carve_okq_list : ltac2:(tb__ "0|a|
S26S48S7S78A1S1bS7S5S1fS1fA2M0A1S4aR2A1S8G0A1A3S89S78S67R4A1R2A3S89S78S78S5S5S5S1fS0A2M1S0A2M2S7S5S5S0S3A2S1fA2A1M3A2OLk;R1G2G3G2OLp;R2G1S0G1OLp0;R2S1fS0S42Q40M4S24RcR2A2A2S0S1aS10S18S12Z2M5Z3eA2M6A1R2A2S1aS10R2R4A2S1aS13R4G6A2S1aS10Z0S11R1R2A2M7A2S1aS10S11R1R4A2M8S12G5Z40A2A2S1aS83R2R4R6A3S1aS0S1aS10R3R1A2S13R1R5A2A2S1aS1bS6S81S3fS23RfA1S41G4S11R3R2A2A2A3SaA3S1dS40Q8A1M9G9S1bSbG9A1S80S3fS23R10A1S41G4S11R4R3A2A2A3ScG9R1A2A3Lx;A2A2F_;Foff;S1aS82RdS80S3fS23RdA1A2R1R6A4S7aRdRcG7G8A4A2A2A2A2A2A2A2A2Tb;Llo;Lbase;X5x1Lhi;Lp0;X5x1Lcs;Lp;X5x1Lk;R3A3F_;F_;FN;FX;Frho;").
Proof.
  intros rho X N HX HN. eapply Forall_impl; [|exact HN]. intros [[[base lo] hi] cs] Hk. unfold carve_okq in Hk. lazy beta iota zeta in Hk |- *.
  destruct Hk as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8). repeat (split; [assumption|]). intros rr y j Hin. rewrite HX in Hin. destruct Hin.
Qed.

Definition zloQ (z : nat) : Z := match z with 0%nat => 0xe4000 | 1%nat => 2768 | 2%nat => 0x98 | 3%nat => -16 | 8%nat => 16 | _ => 0 end.
Definition zhiQ (z : nat) : Z :=
  match z with 0%nat => 0x646000 | 1%nat => 3168 | 2%nat => 0xa0 | 3%nat => -8 | 4%nat => 8065 | 5%nat => 4096 | 6%nat => 2 ^ 64 | 7%nat => 16 | 8%nat => 20 | _ => 16 end.
Definition ZUQ (vb : bool) : list nat := ltac2:(tb__ "0|1|
S9S3S2S3U0S2S3U1S2S3U2S2S3U3S2S3U4S2S3U5S2S3U6S2S3U7S2S3U8S8S3A1M0A3A3A3A3A3A3A3A3A3S6S7S3A1Lvb;Vvb;S2S3U9G0A3G0X6x2A3").
Definition ZD_rti : list zdesc := ltac2:(tb__ "0|3|
S2S5S5S3S0A2M0S0A2M1S4G0S0S4S3S0U0M2Zeddb8A4Zeddc4A4S2G1S4G0S0S4S3S0G2Zeddc8A4Zeddd1A4S2G1S4G0S0S4S3S0G2Ze9af0A4Ze9af8A4S2G1S4G0S0S4S3S0G2Zf0c5cA4Zf0c5dA4S2G1S4G0S0S4S3S0G2Zf0c60A4Zf0c61A4S2G1S4G0S0S4S3S0G2Zf0c64A4Zf0c68A4S2G1S4G0S0S4S3S0G2Z624560A4Z624568A4S2G1S4G0S0S4S3S0G2Z645960A4Z645968A4S2G1S4G0S0S4S3S0U2Z98A4Za0A4S2G1S4G0S0S4S3S0G2Zf20d8A4Zf20daA4S2G1S4G0S0S4S3S0G2Zf20e0A4Zf20f8A4S8G1A1A3A3A3A3A3A3A3A3A3A3A3").
Definition ZD_itm (vb : bool) : list zdesc := ltac2:(tb__ "0|5|
S9S5S5S3S0A2M0S0A2M1S2G1S4G0S0S4S3S0U5Z0M2A4Z1000A4S2G1S4G0S0S4S3S0U3N10A4N8A4S2G1S4G0S0S4S3S0U7G2A4Z10M3A4S2G1S4G0S0S4S3S0U8G3A4Z14A4S2G1S4G0S0S4S3S0U1Zad0A4Zc60A4S8G1A1M4A3A3A3A3A3S6S7G1A1Lvb;Vvb;S2G1S4G0S0S4S3S0U9G2A4G3A4G4A3G4X6x2A3").
Definition ZD_fix : list zdesc := ltac2:(tb__ "0|5|
S2S5S5S3S0A2M0S0A2M1S4G0S0S4S3S0U6Z0A4S12Z2Z40M2A2A4M3S2G1G3S2G1G3S2G1G3S2G1S4G0S0S4S3S0U0M4S11S95Z98A2A4S11S95Z9cA2A4S2G1S4G0S0S4S3S0G4S11S95G2A2A4S11S95Z50A2A4S2G1S4G0S0S4S3S0G4Sb1A4Sb0A4S2G1S4G0S0S4S3S0G4Sb3A4Sb2A4S8G1A1A3A3A3A3A3A3A3A3").
Lemma ZDq_chk : ltac2:(tb__ "0|4|
S6S1aS1bS6S45S9S43S60S5fR1A1A3M0A1SaA3S1aS1bS6S71S43S43S71S43S46R1A1M1S5eA3Ld;G0A3SaA3S1bS6S71S43S43S71S43G1S9S43S5eS9S43S60S5fR2A1A3A3A3Ld;S2S5S5S3S0A2M2S0A2M3S4G2S0S4S3S0U4Z0A4Z1f81A4S8G3A1A3A3SaA3A2A2Fvb;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition zbQ (T CTX SB u ab TOP E SLOT SHU : Z) (z : nat) : Z := ltac2:(tb__ "0|0|
S3S0Lz;Vz;Z0S3S3S0Ln;R1VT;S3S3S0Ln0;R1VCTX;S3S3S0Ln1;R1Vu;S3S3S0Ln2;R1VSHU;S3S3S0Ln3;R1S11VSB;S12Z2Z25A2A2S3S3S0Ln4;R1VTOP;S3S3S0Ln5;R1VE;S3S3S0Ln6;R1VSLOT;S3Vab;Ln7;X3x2Ln6;X3x2Ln5;X3x2Ln4;X3x2Ln3;X3x2Ln2;X3x2Ln1;X3x2Ln0;X3x2Ln;X3x2").

Lemma zsepQ : ltac2:(tb__ "0|a|
S0S0S0S0S0S0S0S0S0S10Z1000M0R9A2S10S11RaG0A2R5A2S10G0RaA2S10S11RbG0A2R7A2S10Z10007fff8000M1RbA2S10S11S11RcS12Z2Z25A2M2A2G0A2R9A2S10RdRbA2S10S11RcZ10M3A2RdA2S10ReS11RfG2A2A2S10Z7fff8000RaA2S10S11RbZ1f81A2G1A2S10S11R14Z120A2ReA2S10S11RfZ50M4A2S11R15Zad0A2A2S10R10RfA2S10S11R10Z14A2S11R11G4A2A2S1cS10S11R18G0A2Z10000A2S10Z646000R18A2A2M5G5S1cS10S11R1aG0A2Z7fff7000A2S10G1R1aA2A2M6G6S1cS10S11R1cG0A2R1bA2S10S11R1bG0A2R1cA2A2S1cS10S11R1dG0A2M7R1bA2S10S11S11R1bG2A2G0A2R1dA2A2S1cS10G7R1cA2S10S11S11R1cG2A2G0A2R1dA2A2S6S1bS6R1SaA3S10S11R1dG3A2S17R1eG3A2A2F_;S3S3S70S3R2S66R4A1A3S70S3R2S66R5A1A3S1eS1bS3R4R3A3A1S1cS10S11S61R26R25R24R23R22R21R20R1fR1eR5AaM8S59R5A1A2S11S61R26R25R24R23R22R21R20R1fR1eR4AaM9S5aR4A1A2A2S10S11G9S59R4A1A2S11G8S5aR5A1A2A2A2F_;F_;F_;Fz';Fz;F_;Fvb;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FSHU;FSLOT;FE;FTOP;Fab;Fu;FSB;FCTX;FT;").
Proof.
  intros T CTX SB u ab TOP E SLOT SHU HT0 HT1 HC0 HC1 HSB HST HAB HU HUS HSH0 HSH1 HE0 HE1 HS0 HS1 HTI HCI HTB HCB HTC HTS HCS vb HM.
  assert (HR : forall y, In y (ZUQ vb) -> (y <= 8)%nat \/ (y = 9%nat /\ vb = true)).
  { clear. intros y Hy. destruct vb; cbn in Hy.
    - destruct (Nat.eq_dec y 9) as [->|NE9]; [right; split; reflexivity | left; lia].
    - left. lia. }
  intros z z' Hz Hz' NE.
  assert (HM9 : (z = 9%nat \/ z' = 9%nat) -> ab + 16 <= u - 16).
  { intros [EQ9|EQ9]; subst; [destruct (HR 9%nat Hz) as [L|[_ V]] | destruct (HR 9%nat Hz') as [L|[_ V]]]; first [exfalso; lia | exact (HM V)]. }
  assert (LZ : (z <= 9)%nat /\ (z' <= 9)%nat) by (destruct (HR z Hz) as [L|[-> _]]; destruct (HR z' Hz') as [L'|[-> _]]; lia).
  destruct LZ as [LZ LZ']. clear HR Hz Hz' HM.

  destruct z as [|[|[|[|[|[|[|[|[|[|z]]]]]]]]]]; [| | | | | | | | | | exfalso; lia];
    (destruct z' as [|[|[|[|[|[|[|[|[|[|z']]]]]]]]]]; [| | | | | | | | | | exfalso; lia]);
    try (exfalso; apply NE; reflexivity); cbn [zbQ zloQ zhiQ];
    (first [pose proof (HM9 (or_introl eq_refl)) as HM9' | pose proof (HM9 (or_intror eq_refl)) as HM9' | pose proof I as HM9']); clear HM9 NE LZ LZ';
    first [ solve [clear - HT0 HT1 HC0 HC1 HSB HST HAB HU HUS HSH0 HSH1 HE0 HE1 HS0 HS1 HM9'; lia]
          | solve [clear - HT0 HT1 HC0 HC1 HSB HST HAB HU HUS HSH0 HSH1 HE0 HE1 HS0 HS1 HM9' HTI; lia]
          | solve [clear - HT0 HT1 HC0 HC1 HSB HST HAB HU HUS HSH0 HSH1 HE0 HE1 HS0 HS1 HM9' HCI; lia]
          | solve [clear - HT0 HT1 HC0 HC1 HSB HST HAB HU HUS HSH0 HSH1 HE0 HE1 HS0 HS1 HM9' HTB; lia]
          | solve [clear - HT0 HT1 HC0 HC1 HSB HST HAB HU HUS HSH0 HSH1 HE0 HE1 HS0 HS1 HM9' HCB; lia]
          | solve [clear - HT0 HT1 HC0 HC1 HSB HST HAB HU HUS HSH0 HSH1 HE0 HE1 HS0 HS1 HM9' HTC; lia]
          | solve [clear - HT0 HT1 HC0 HC1 HSB HST HAB HU HUS HSH0 HSH1 HE0 HE1 HS0 HS1 HM9' HTS; lia]
          | solve [clear - HT0 HT1 HC0 HC1 HSB HST HAB HU HUS HSH0 HSH1 HE0 HE1 HS0 HS1 HM9' HCS; lia] ].
Qed.

Definition qgeo (A : AA) (it : Z * Z) : Prop := ltac2:(tb__ "0|12|
S1aS1aS10Z1M0S99Vit;A1M1A2S10G1Z1eA2A2S1aS1aS10Z10M2S92G1A1M3A2S10G3Z10000A2A2S1aS1bS0S16G3G2A2Z0M4A3S1aS1aS10G2S90SdS0S0Vit;A3M5A1M6A2S10G6Z800A2A2S1aS1bS0S16G6G2A2G4A3S1aS1bS0SeS0S0Vit;A3M7S11S9aVit;A1M8G6A2A3S1aS1aS10G0G5A2S10G5Zfc00M9A2A2S1aS10S11S55S4eVA;A1A1MaS14G1S12Z2MbZ20A2A2A2McG8A2S1aS1bS0S16S17G8GcA2MdG3A2G4A3S1aS10S11GdG3A2S57S9cVA;G1A2A1A2S1aS1bS0S16G8G2A2G4A3S1aS10S11G7S14S15S11G5Z7A2Z8MeA2GeA2MfA2S11G8G3A2M10A2S1aS10G10S11GaS12GbZ25A2A2M11A2S1aS1bS0S16GaS12GbG2A2A2G4A3S1aS10Z10007fff8000GaA2S1aS10S11G11Z1000A2Z7fffff800000A2S1aS1aS10GeGfA2S10GfG9A2A2S1bS0S16GfGeA2G4A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").

Record qienv (A : AA) (it : Z * Z) (rho : valuation) (t st : Z) : Prop := mkQE {
  qe_hg : geom_ok (aa_geom A);
  qe_hsep3 : sep_geom3 (aa_geom A);
  qe_hrtc : rtc_inv (view segsA (rm rho)) (aa_geom A);
  qe_hrig : rw rho 151%positive = Z_to_bv 64 (ag_thread (aa_geom A)) /\ rw rho 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))
            /\ rw rho 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A)) /\ rw rho 156%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize);
  qe_hgeo : qgeo A it;
  qe_hv : QIV rho it (cls_of A (it_cls it)) t st;
  qe_hcv : cls_view (view segsA (rm rho)) (aa_geom A) (aa_live A) (it_cls it) (cls_of A (it_cls it));
  qe_him : item_mem (view segsA (rm rho)) it;
  qe_hstat : present (view segsA (rm rho)) (ag_thread (aa_geom A) + 2768) (ag_thread (aa_geom A) + 3168);
  qe_ht : 0 <= t < 256 /\ view segsA (rm rho) (fst it - 15) = Some (Z_to_bv 8 t);
  qe_hst : 0 <= st < 2 ^ 64 /\ cell_ok (view segsA (rm rho)) (mkACell (ag_thread (aa_geom A) + 2784) 8 st);
  qe_hnf : Z.of_nat (length (cs_cache (cls_of A (it_cls it)))) < max_count (it_cls it);
  qe_hqp : q_pure A;
  qe_hau : forall c', 1 <= c' <= 30 -> 0 <= cs_allocated_user (cls_of A c') <= kUserSpaceSize;
  qe_hin : In it (qitems (qall A));
  qe_hpr : is_primary (snd it) = true;
  qe_hmu : cs_allocated_user (cls_of A (it_cls it)) <= cs_mapped_user (cls_of A (it_cls it)) <= kUserSpaceSize
}.

Lemma qienv_agree : ltac2:(tb__ "0|1|
S4dS5S0S0A2S26S26S0S0S5bR6R5R4R2R1A5S1Sc9R1Pd8A2S1bS40Q40A1M0S2aR6R2A2S2aR7R2A2A3F_;Fi;S1bG0SbS40Q8A1A1F_;S23R5A1S23R6A1A3S5bR9R8R6R5R4A5F_;F_;F_;Fst;Ft;Fr';Fr;Fit;FA;").
Proof.
  intros A it r r' t st [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17] HRW HRM.
  constructor; rewrite ?HRM; try assumption.
  - destruct Q4 as (E151 & E152 & E155 & E156). repeat split; rewrite HRW by lia; assumption.
  - unfold QIV in *. cbv zeta in *. destruct Q6 as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
    repeat split; rewrite HRW by lia; assumption.
Qed.

Section QIEnv.
Variables (A : AA) (it : Z * Z) (rho : valuation) (t st : Z).
Hypothesis QE : ltac2:(tb__ "0|0|
S5bVA;Vit;Vrho;Vt;Vst;A5").
Let u : Z := fst it.
Let n : Z := snd it.
Let c : Z := it_cls it.
Let cs : class_state := cls_of A c.
Let ab : Z := it_ab it.
Let T : Z := ag_thread (aa_geom A).
Let CTX : Z := ag_ctx (aa_geom A).
Let SB : Z := ag_spacebeg (aa_geom A).
Let k : Z := Z.of_nat (length (cs_cache cs)).
Let N8 : Z := ltac2:(tb__ "0|1|
S14S15S11Vn;Z7A2Z8M0A2G0A2").
Let m : bview := ltac2:(tb__ "0|0|
S73S3fS23Vrho;A1A2").

Ltac qe_open := pose proof QE as [HG HSEP3 HRTC HRIG HGEO HV HCV HIM HSTAT Ht Hst HNF HQP HAU HIN HPR HMU]; unfold qgeo in HGEO.
Ltac qe_unf := unfold k, N8, m, cs, c, ab, u, n, T, CTX, SB in *.

Lemma qe_nums : ltac2:(tb__ "0|2|
S1aS10Z1000M0VT;A2S1aS10S11VT;G0A2S54S4eVA;A1A1M1A2S1aS10G0VCTX;A2S1aS10S11VCTX;G0A2G1A2S1aS10S11S11VSB;S12Z2Z25A2A2G0A2G1A2S1aS1aS10Z7fff7f800000G1A2S10G1Z7fffff800000A2A2S1aS10Z0Vk;A2S13Vk;Z10A2A2A2A2A2A2A2A2").
Proof.
  qe_open. pose proof (geom_old _ HG) as HG'. rewrite kSpaceSize_val in HG'. destruct HG' as (_ & _ & _ & _ & G5 & G6 & _ & G8 & G9 & _ & _ & _ & _ & G14 & _).
  pose proof (topG_range (aa_geom A)) as TG. destruct HGEO as (C1 & _). pose proof (max_count_le16q _ C1) as MC.
  qe_unf. repeat split; lia.
Qed.
Lemma qe_wins : ltac2:(tb__ "0|8|
S1aS1cS10S11VT;Z1000M0A2M1Z10000M2A2S10Z646000M3VT;A2A2S1aS1cS10S11VCTX;G0A2M4G2A2S10G3VCTX;A2A2S1aS1cS10G1Z7fff7000M5A2S10Z10007fff8000M6VT;A2A2S1aS1cS10G4G5A2S10G6VCTX;A2A2S1aS1cS10G1VCTX;A2S10G4VT;A2A2S1aS1cS10G1VSB;A2S10S11S11VSB;S12Z2Z25A2A2G0A2M7VT;A2A2S1cS10G4VSB;A2S10G7VCTX;A2A2A2A2A2A2A2A2").
Proof.
  qe_open. pose proof (geom_bands _ HG) as (_ & TB & CB & _ & TI & CI & _). pose proof (geom_seps _ HG) as (_ & _ & _ & _ & Q5 & _).
  destruct HSEP3 as (S1 & S2 & _). rewrite kSpaceSize_val in S1, S2.
  unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. qe_unf.
  split; [exact TI|]. split; [exact CI|]. split; [exact TB|]. split; [exact CB|]. split; [exact Q5|]. split; [exact S1 | exact S2].
Qed.
Lemma qe_Sh : ltac2:(tb__ "0|3|
S1aS10Z7fff8000S8cVu;A1M0A2S1aS10S11G0Z1f81A2Z10007fff8000A2S1aS1aS10Z0S15VN8;Z8M1A2M2A2S10G2Z1f80A2A2S1bS0G2S15S11Vn;Z7A2G1A2A3A2A2A2").
Proof.
  qe_open. destruct HGEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  qe_unf. unfold Sh, SHADOW_OFF.
  pose proof (Z.div_pos (fst it) 8 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_lt_upper_bound (fst it) 8 (2 ^ 44 - 2 ^ 20) ltac:(lia) ltac:(lia)) as D1.
  pose proof (Z.div_pos ((snd it + 7) / 8 * 8) 8 ltac:(lia) ltac:(lia)) as D2.
  pose proof (Z.div_le_upper_bound ((snd it + 7) / 8 * 8) 8 8064 ltac:(lia) ltac:(lia)) as D3.
  split; [lia|]. split; [lia|]. split; [lia|]. apply Z.div_mul. lia.
Qed.

Lemma qe_E : ltac2:(tb__ "0|3|
S1aS1bS0S42Q40M0S24Vrho;Sa1A2A2VT;A3S1aS1bS0S42G0S24Vrho;Sa0A2A2VCTX;A3S1aS1bS0S42G0S24Vrho;S85A2A2S17Vu;Z10A2A3S1aS1bS0S42G0S24Vrho;S68A2A2S11S11VSB;S12Z2M1Z25A2A2S14Z80Vc;A2A2A3S1aS1bS0S42G0S24Vrho;S5cA2A2S11S11VT;Zd0A2S14Z50Vc;A2A2M2A3S1aS1bS0S42G0S24Vrho;S7bS5cS28S9dS22PceA1S21G1A1A3A2A2A2S11G2S14Z4Vk;A2A2A3S1aS1bS0S42G0S24Vrho;S69A2A2S8cVu;A1A3S1aS1bS0S3dVrho;S28S9eS22PcdA1S21Z3A1A3A2S15VN8;Z8A2A3S1bS0S42G0S24Vrho;S22Pd2A1A2A2Vab;A3A2A2A2A2A2A2A2A2").
Proof.
  qe_open. pose proof qe_nums as (T0 & T1 & C0 & C1' & S14 & TG & K16). pose proof qe_Sh as (SH0 & SH1 & L0 & _).
  destruct HRIG as (E151 & E152 & E155 & E156). rewrite kSpaceSize_val in E156.
  destruct HV as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
  destruct HGEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  qe_unf.
  assert (EcbC : eval rho cbC = Z_to_bv 64 (ag_thread (aa_geom A) + 208)) by (unfold cbC; apply ev_add_lit; [unfold vT; cbn [eval]; exact E151 | lia | lia | lia]).
  assert (Eent : bv_unsigned (eval rho entQ) = ag_thread (aa_geom A) + 208 + 80 * it_cls it).
  { unfold entQ, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC. cbn [eval]. rewrite E200, !u64_lit by lia. unfold M64v.
    rewrite (Z.mod_small (it_cls it * 80)) by lia. rewrite Z.mod_small by lia. lia. }
  split; [unfold vT; cbn [eval]; rewrite E151; apply u64_lit; lia|].
  split; [unfold vCTX; cbn [eval]; rewrite E152; apply u64_lit; lia|].
  split; [unfold vIT; cbn [eval]; rewrite E165; apply u64_lit; unfold it_ab in *; lia|].
  split.
  { unfold rieQ, add. rewrite U_add, U_sll_lit. unfold vRIS. cbn [eval]. rewrite E156, E200, !u64_lit by lia. change (7 mod 64) with 7. unfold M64v.
    rewrite (Z.mod_small (it_cls it * 2 ^ 7)) by lia. rewrite Z.mod_small by lia. lia. }
  split; [exact Eent|].
  split.
  { unfold add at 1. rewrite U_add, U_sll_lit, Eent. cbn [eval]. rewrite E206, u64_lit by lia. change (2 mod 64) with 2. unfold M64v.
    rewrite (Z.mod_small (Z.of_nat (length (cs_cache (cls_of A (it_cls it)))) * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. lia. }
  split.
  { unfold shQ, add. rewrite U_add, U_srl_lit, U_add, !U_lit. unfold vIT. cbn [eval]. rewrite E165, u64_lit by (unfold it_ab in *; lia). change (3 mod 64) with 3. unfold M64v.
    rewrite (Z.mod_small 16) by lia. rewrite (Z.mod_small 2147450880) by lia. replace (fst it - 16 + 16) with (fst it) by lia. rewrite (Z.mod_small (fst it)) by (unfold it_ab in *; lia).
    change (2 ^ 3) with 8. unfold Sh, SHADOW_OFF in *. rewrite Z.mod_small by lia. reflexivity. }
  split.
  { unfold soff. rewrite signed_of_unsigned, U_srl_lit. cbn [eval]. rewrite E205, u64_lit by lia. change (3 mod 64) with 3. change (2 ^ 3) with 8. apply snorm_small. lia. }
  cbn [eval]. rewrite E210. apply u64_lit. unfold it_ab in *. lia.
Qed.

Lemma carve_rti : Forall (carve_okq rho) N_rti.
Proof.
  qe_open. pose proof qe_nums as (T0 & T1 & C0 & C1' & S14 & TG & K16). pose proof qe_wins as (_ & CI & _).
  destruct HRIG as (E151 & E152 & E155 & E156).
  assert (HR : cells_ok (view segsA (rm rho)) (rtc_cells RTC_A (aa_geom A))) by exact HRTC.
  qe_unf. clear HGEO HSEP3 HV HCV HIM HSTAT Ht Hst HNF HQP HAU HIN HPR HMU.
  unfold N_rti, vSB, vRIS, vCTX, vT. repeat apply Forall_cons; try apply Forall_nil; unfold carve_okq; lazy beta iota zeta; cbn [eval]; rewrite ?E152, ?u64_lit by lia.
  all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
  all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  all: split.
  all: try match goal with
       | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
       | |- forall off, _ -> wok_of _ _ _ = true /\ _ => intros off Hoff; wr_any2 HR ltac:(clear -CI; lia)
       end.
  all: unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?E155, ?E156; civ_any2 HR.
Qed.

Lemma carve_itm : ltac2:(tb__ "0|0|
S6S1bS6R1SaA3S1eS1bS0S90Vn;A1Z10A3A1F_;S89S78S67Vrho;A1S64R2A1A3F_;Fvb;").
Proof.
  intros vb HVB. qe_open.
  pose proof qe_nums as (T0 & T1 & C0 & C1' & S14 & TG & K16). pose proof qe_wins as (TI & _).
  pose proof qe_E as (EvT & EvC & EvIT & Erie & Eent & Eslot & Esh & Elen & E210u).
  destruct HV as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
  destruct HGEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  destruct HIM as (IM1 & IM2 & IM3 & IM4 & IM5 & IM6 & IM7). destruct Ht as [Ht1 Ht2]. destruct Hst as [Hst1 Hst2].
  pose proof (cv_ri_mu _ _ _ _ _ HCV) as C_mu. pose proof (cv_count _ _ _ _ _ HCV) as C_cnt. pose proof (cv_max _ _ _ _ _ HCV) as C_max.
  pose proof (cv_size _ _ _ _ _ HCV) as C_sz. pose proof (cv_pc_present _ _ _ _ _ HCV) as P_pc.
  unfold pc_entry, region_info, RI_mapped_user, kRegionInfoStride in C_mu, C_cnt, C_max, C_sz, P_pc. rewrite kSpaceSize_val in C_mu.
  qe_unf. unfold it_ab in *.
  assert (Q0 : 0 <= snd it / 2 ^ 32 < 65536) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (C_hw : cell_ok (view segsA (rm rho)) (mkACell (fst it - 16) 4 (3 + 256 * t + 65536 * (snd it / 2 ^ 32)))).
  { apply (hdr_word_cell (view segsA (rm rho)) (fst it - 16) 3 t (snd it / 2 ^ 32)); [lia | exact Ht1 | exact Q0 | exact IM1
      | replace (fst it - 16 + 1) with (fst it - 15) by lia; exact Ht2 | replace (fst it - 16 + 2) with (fst it - 14) by lia; exact IM3]. }
  assert (TBLK : forall lo hi, ag_thread (aa_geom A) <= lo -> hi <= ag_thread (aa_geom A) + 4096 -> (hi <= 0x10000 \/ 0x646000 <= lo))
    by (intros lo hi B1 B2; clear -TI B1 B2; lia).
  clear TI HSEP3 HQP HAU HIN HPR.
  unfold N_itm. apply Forall_app. split.
  - repeat apply Forall_cons; try apply Forall_nil; unfold carve_okq; lazy beta iota zeta.
    +
      rewrite Erie. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
      * intros off Hoff. eapply (cell_wok_rd _ _ _ _ _ C_mu); cbn [Z.of_nat]; lia.
      * unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        eapply (civ_cell rho (rm rho) (ag_spacebeg (aa_geom A) + 2 ^ 37 + 128 * it_cls it) 48);
          [replace (ag_spacebeg (aa_geom A) + 2 ^ 37 + 128 * it_cls it + 48) with (ag_spacebeg (aa_geom A) + 2 ^ 37 + it_cls it * 128 + 48) by lia; exact C_mu
          | cbn [eval]; exact E202 | lia | lia].
    +
      rewrite EvIT. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
      * intros off Hoff. destruct (Z_lt_dec off 4); [eapply (cell_wok_rd _ _ _ _ _ C_hw); cbn [Z.of_nat]; lia | eapply (cell_wok_rd _ _ _ _ _ IM4); cbn [Z.of_nat]; lia].
      * unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        -- eapply (civ_cell rho (rm rho) (fst it - 16) 0); [replace (fst it - 16 + 0) with (fst it - 16) by lia; exact C_hw | cbn [eval]; exact E203 | lia | lia].
        -- eapply (civ_cell rho (rm rho) (fst it - 16) 4); [replace (fst it - 16 + 4) with (fst it - 12) by lia; exact IM4 | cbn [eval]; exact E204 | lia | lia].
    +
      rewrite Eent. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
      * intros off Hoff. destruct (Z_lt_dec off 4); [|destruct (Z_lt_dec off 8)].
        -- eapply (cell_wok_rd2 _ _ _ _ _ C_cnt); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
        -- eapply (cell_wok_rd2 _ _ _ _ _ C_max); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
        -- eapply (cell_wok_rd2 _ _ _ _ _ C_sz); cbn [Z.of_nat]; try lia; try (apply TBLK; lia).
      * unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        -- eapply (civ_cell rho (rm rho) (ag_thread (aa_geom A) + 208 + 80 * it_cls it) 0);
             [replace (ag_thread (aa_geom A) + 208 + 80 * it_cls it + 0) with (ag_thread (aa_geom A) + 208 + 80 * it_cls it) by lia; exact C_cnt | cbn [eval]; exact E206 | lia | lia].
        -- eapply (civ_cell rho (rm rho) (ag_thread (aa_geom A) + 208 + 80 * it_cls it) 4); [exact C_max | cbn [eval]; exact E207 | lia | lia].
        -- eapply (civ_cell rho (rm rho) (ag_thread (aa_geom A) + 208 + 80 * it_cls it) 8); [exact C_sz | cbn [eval]; exact E201 | lia | lia].
    +
      rewrite Eslot. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold cells_inside; apply Forall_nil|]. split.
      * intros off Hoff. apply (wr_present (rm rho) _ _ _ P_pc); try lia. apply TBLK; lia.
      * unfold cells_in_view. apply Forall_nil.
    +
      rewrite EvT. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
      * intros off Hoff. apply (wr_present (rm rho) _ _ _ HSTAT); try lia. apply TBLK; lia.
      * unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        eapply (civ_cell rho (rm rho) (ag_thread (aa_geom A)) 2784); [exact Hst2 | cbn [eval]; exact E209 | lia | lia].
  - destruct vb; [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil]. specialize (HVB eq_refl).
    destruct IM6 as [X|[MG1 MG2]]; [exfalso; exact (HVB X)|].
    unfold carve_okq; lazy beta iota zeta. rewrite E210u. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
    + intros off Hoff. destruct (Z_lt_dec off 8); [eapply (cell_wok_rd _ _ _ _ _ MG1); cbn [Z.of_nat]; lia | eapply (cell_wok_rd _ _ _ _ _ MG2); cbn [Z.of_nat]; lia].
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      * eapply (civ_cell rho (rm rho) (fst it - rz (snd it)) 0); [replace (fst it - rz (snd it) + 0) with (fst it - rz (snd it)) by lia; exact MG1 | reflexivity | lia | lia].
      * eapply (civ_cell rho (rm rho) (fst it - rz (snd it)) 8); [exact MG2 | unfold vIT; cbn [eval]; exact E165 | lia | lia].
Qed.

Let zb : nat -> Z := ltac2:(tb__ "0|1|
S61VT;VCTX;VSB;Vu;Vab;S54S4eVA;A1A1S11S11VT;Zd0A2S14Z50Vc;A2A2M0S11G0S14Z4Vk;A2A2S8cVu;A1A9").

Lemma inz_fix : ltac2:(tb__ "0|0|
S7S3A1S70S3U0R1A3S70S3U6R2A3SaeVA;Vrho;A2S89S25S3aVrho;A1SadS96A1A3S72S20S43S44Vrho;Vzb;S5aS59R5A5S27S47S58A1A1S5eA5F_;F_;F_;F_;Fzused;").
Proof.
  intros zused U0 U6 HT HF. destruct (stk_facts A rho HT HF) as (HD & HTOP & Hsp). pose proof (topG_range (aa_geom A)) as TG.
  destruct (stk_ranges rho _ _ cb_cells (ob_cells (SWD vXK vXF vXL vXS)) eq_refl eq_refl ltac:(lia) HD) as (R1 & R2 & R3 & R4).
  assert (R4' : obj_range rho (SWD vXK vXF vXL vXS) = (bv_unsigned (rw rho 10%positive) - 168, bv_unsigned (rw rho 10%positive))) by exact R4.
  rewrite DQI0_objs. unfold STK, A_globals, ZD_fix. cbn [app].
  repeat apply Forall2_cons; try apply Forall2_nil; unfold in_zone.
  - split; [exact U6|]. split; [cbn; lia|]. split; [cbn; lia|]. right. rewrite R1. unfold zb. cbn [fst snd zbQ]. lia.
  - split; [exact U6|]. split; [cbn; lia|]. split; [cbn; lia|]. right. rewrite R2. unfold zb. cbn [fst snd zbQ]. lia.
  - split; [exact U6|]. split; [cbn; lia|]. split; [cbn; lia|]. right. rewrite R3. unfold zb. cbn [fst snd zbQ]. lia.
  - split; [exact U6|]. split; [cbn; lia|]. split; [cbn; lia|]. right. rewrite R4'. unfold zb. cbn [fst snd zbQ]. lia.
  - split; [exact U0|]. split; [unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG; cbn; lia|]. split; [unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG; cbn; lia|]. right.
    unfold O_mtx00, carved. rewrite obj_range_mk by (unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG; lia). unfold zb. cbn [fst snd eval zbQ]. rewrite u64_lit by lia. unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG. lia.
  - split; [exact U0|]. split; [unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG; cbn; lia|]. split; [unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG; cbn; lia|]. right.
    unfold O_gmax, carved. rewrite obj_range_mk by (unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG; lia). unfold zb. cbn [fst snd eval zbQ]. rewrite u64_lit by lia. unfold Inv.QG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG. lia.
  - split; [exact U0|]. split; [unfold GOT_LO, GOT_HI; cbn; lia|]. split; [unfold GOT_LO, GOT_HI; cbn; lia|]. right.
    unfold O_got. rewrite obj_range_mk by (unfold GOT_LO, GOT_HI; lia). unfold zb. cbn [fst snd eval zbQ]. rewrite u64_lit by lia. unfold GOT_LO, GOT_HI. lia.
  - split; [exact U0|]. split; [unfold RTC_LO, RTC_HI; cbn; lia|]. split; [unfold RTC_LO, RTC_HI; cbn; lia|]. right.
    unfold O_rtc. rewrite obj_range_mk by (unfold RTC_LO, RTC_HI; lia). unfold zb. cbn [fst snd eval zbQ]. rewrite u64_lit by lia. unfold RTC_LO, RTC_HI. lia.
Qed.

Lemma inz_rti : ltac2:(tb__ "0|0|
S7S3A1S70S3U0R1A3S70S3U2R2A3S72S20S43S44Vrho;Vzb;S5aS59R3A5S8aS78S20S79S6dA4S60A5F_;F_;Fzused;").
Proof.
  intros zused U0 U2. qe_open. pose proof qe_nums as (T0 & T1 & C0 & C1' & S14 & TG & K16). destruct HRIG as (E151 & E152 & E155 & E156).
  qe_unf. clear HGEO HSEP3 HV HCV HIM HSTAT Ht Hst HNF HQP HAU HIN HPR HMU HRTC.
  unfold N_rti, ZD_rti. cbn [map carve_obj]. unfold vCTX.
  repeat apply Forall2_cons; try apply Forall2_nil.
  all: unfold in_zone; split; [assumption | split; [cbn; lia | split; [cbn; lia | right]]].
  all: unfold carved; rewrite obj_range_mk by lia; unfold zb; cbn [fst snd eval zbQ]; rewrite ?E152, ?u64_lit by lia; lia.
Qed.

Lemma inz_itm : ltac2:(tb__ "0|0|
S6S7S3A1S3S70S3R1S2S3U1S2S3U3S2S3U5S2S3U7S2S3U8S8S3A1A3A3A3A3A3A3S70S3R2R3A3F_;Fz;S1bS6R3SaA3S70S3U9R3A3F_;S72S20S43S44Vrho;Vzb;S5aS59R3A5S8aS78S20S79S64R4A1A4S5fR4A1A5F_;F_;Fzused;Fvb;").
Proof.
  intros vb zused HU HU9. qe_open. pose proof qe_nums as (T0 & T1 & C0 & C1' & S14 & TG & K16).
  pose proof qe_E as (EvT & EvC & EvIT & Erie & Eent & Eslot & Esh & Elen & E210u).
  destruct HGEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  clear HSEP3 HV HCV HIM HSTAT Ht Hst HQP HAU HIN HPR HMU HRTC HRIG.
  unfold N_itm, ZD_itm. rewrite map_app. apply Forall2_app.
  - cbn [map carve_obj]. repeat apply Forall2_cons; try apply Forall2_nil.
    all: unfold in_zone; split; [apply HU; cbn; tauto | split; [cbn; lia | split; [cbn; lia | right]]].
    all: unfold carved; rewrite obj_range_mk by lia; unfold zb; cbn [fst snd zbQ]; rewrite ?EvT, ?EvIT, ?Erie, ?Eent, ?Eslot; qe_unf; lia.
  - destruct vb; cbn [map carve_obj]; [|apply Forall2_nil]. apply Forall2_cons; [|apply Forall2_nil].
    unfold in_zone. split; [exact (HU9 eq_refl)|]. split; [cbn; lia|]. split; [cbn; lia|]. right.
    unfold carved. rewrite obj_range_mk by lia. unfold zb. cbn [fst snd zbQ]. rewrite E210u. lia.
Qed.

Lemma ish_range : ltac2:(tb__ "0|1|
S1bS5S0S0A2S3cVrho;S5dA2S4S0S0S11S8cVu;A1M0Z0A2S11G0S15VN8;Z8A2A2A4A3").
Proof.
  pose proof qe_E as (_ & _ & _ & _ & _ & _ & Esh & Elen & _).
  unfold O_ishQ, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by lia. rewrite Elen, Esh. reflexivity.
Qed.
Lemma inz_ish : ltac2:(tb__ "0|3|
S7S3A1S70S3U4M0R1A3S72S20S43S44Vrho;Vzb;S5aS59R2A5S2S20S5dS8S20A1A3S2S5S5S3S0A2M1S0A2M2S4G1S0S4S3S0G0Z0A4Z1f81A4S8G2A1A3A5F_;Fzused;").
Proof.
  intros zused U4. pose proof qe_Sh as (_ & _ & L0 & _).
  apply Forall2_cons; [|apply Forall2_nil]. unfold in_zone. split; [exact U4|]. split; [cbn; lia|]. split; [cbn; lia|]. right.
  rewrite ish_range. unfold zb. cbn [fst snd zbQ]. lia.
Qed.

Lemma qi_carve : ltac2:(tb__ "0|0|
S7fS7S40Q40A1A1Sa8SaeVA;Vrho;A2S7eS3fR4S58Vrho;R3R2A6S7eS3fR5Sa2Sb4Vit;A1A1Vrho;R4R3A6F_;F_;Fw;Ftp;FJ;").
Proof.
  intros J tp w HTOPH H0. remember (vb_of it) as vb eqn:EVB. qe_open.
  assert (HVB : vb = true -> rz n <> 16) by (rewrite EVB; unfold vb_of; intros X; apply negb_true_iff in X; apply Z.eqb_neq in X; exact X).
  pose proof (D_pre_facts DQI0 _ DQI0_facts rho (SPA_facts_hold segsA _ rho DQI0 tp _ H0)) as HFpre.
  pose proof qe_nums as (T0 & T1 & C0 & C1' & S14 & TG & K16). pose proof qe_Sh as (SH0 & SH1 & L0 & L1).
  pose proof qe_E as (EvT & EvC & EvIT & Erie & Eent & Eslot & Esh & Elen & E210u).
  pose proof qe_wins as (WTI & WCI & WTB & WCB & WTC & WTS & WCS).
  assert (HM : vb = true -> ab + 16 <= u - 16).
  { intros X. specialize (HVB X). destruct HGEO as (_ & _ & _ & RZ & RZ16 & EU & _). unfold u, n, ab in *. clear - HVB RZ RZ16 EU. unfold it_ab in *.
    pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)) as D. rewrite RZ16 in D. lia. }
  assert (HSEPZ : forall z z', In z (ZUQ vb) -> In z' (ZUQ vb) -> z <> z' -> zb z + zhiQ z <= zb z' + zloQ z' \/ zb z' + zhiQ z' <= zb z + zloQ z).
  { unfold zb. destruct HGEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
    intros z z' Hz Hz' NE.
    apply (zsepQ T CTX SB u ab (topG (aa_geom A)) (T + 208 + 80 * c) (T + 208 + 80 * c + 4 * k) (Sh u)) with (vb := vb); try assumption;
      clear WTI WCI WTB WCB WTC WTS WCS HM HVB; unfold k, N8, cs, c, ab, u, n, T, CTX, SB in *; lia. }
  assert (U_all : forall z, (z <= 8)%nat -> In z (ZUQ vb)) by (intros z Hz; unfold ZUQ; apply in_or_app; left; cbn; lia).
  assert (U9 : vb = true -> In 9%nat (ZUQ vb)) by (intros X; rewrite X; first [ repeat match goal with H : _ |- _ => clear H end; cbn; tauto | cbn; tauto ]).
  assert (INZN : Forall2 (in_zone rho zb zloQ zhiQ (ZUQ vb)) (map carve_obj (N_qi vb)) (ZD_rti ++ ZD_itm vb)).
  { unfold N_qi. rewrite map_app. apply Forall2_app; [apply inz_rti; apply U_all; lia | apply inz_itm; [|exact U9]].
    intros z Hz. apply U_all. cbn in Hz. first [ clear - Hz; lia | lia ]. }
  assert (INZF : Forall2 (in_zone rho zb zloQ zhiQ (ZUQ vb)) (ss_objs (ax_S DQI0)) ZD_fix) by (apply inz_fix; [apply U_all; lia | apply U_all; lia | exact HTOPH | exact HFpre]).

  assert (H1 : SPA segsA J (DQI1 vb) rho tp w).
  { pose proof (SPA_carve_list segsA J rho DQI0 tp w (N_qi vb) (ss_next (ax_S DQI0)) H0) as X. cbn zeta in X. apply X; clear X.
    - exact (DQI1_swf vb).
    - apply Pos.le_refl.
    - unfold N_qi. apply carve_okq_list; [reflexivity|]. apply Forall_app. split; [exact carve_rti | exact (carve_itm vb HVB)].
    - exact (zones_cross rho zb zloQ zhiQ (ZUQ vb) HSEPZ _ _ _ _ INZN INZF (proj1 (proj2 (ZDq_chk vb)))).
    - exact (zones_pd rho zb zloQ zhiQ (ZUQ vb) HSEPZ _ _ INZN (proj1 (ZDq_chk vb))). }

  assert (H2 : SPA segsA J (DQI2 vb) rho tp w).
  { pose proof (SPA_carve_unk segsA J rho (DQI1 vb) tp w shQ (SLit 0) (SAlu ALU_SRL (SVar 205) (SLit 3)) (ss_next (ax_S (DQI1 vb))) H1) as X. cbn zeta in X.
    rewrite Esh, Elen, (soff_lit_small rho 0) in X by lia. apply X; clear X.
    - exact (DQI2_swf vb).
    - apply Pos.le_refl.
    - lia.
    - lia.
    - lia.
    - lia.
    - pose proof (zones_cross rho zb zloQ zhiQ (ZUQ vb) HSEPZ [O_ishQ] [(4%nat, 0, 8065)] (ss_objs (ax_S DQI0) ++ map carve_obj (N_qi vb)) (ZD_fix ++ ZD_rti ++ ZD_itm vb)
                   (inz_ish _ (U_all 4%nat ltac:(lia))) (Forall2_app INZF INZN) (proj2 (proj2 (ZDq_chk vb)))) as ZC.
      pose proof (Forall_inv ZC) as ZC1. cbv beta in ZC1. rewrite ish_range in ZC1. exact ZC1.
    - intros a0 Ha. destruct HIM as (_ & _ & _ & _ & _ & _ & IM7).
      assert (IM7' : present (view segsA (rm rho)) (Sh u) (Sh u + N8 / 8)) by (rewrite L1; exact IM7).
      apply (wr_present (rm rho) (Sh u) (Sh u + N8 / 8) a0 IM7'); lia.
    - intros rr y j Hin. destruct Hin. }
  assert (H3 : SPA segsA J (DQI3 vb) rho tp w).
  { apply SPA_refacts; [exact H2 | exact (DQI3_below vb) |]. intros HF. apply Forall_app. split; [exact HF|]. rewrite factsQ_eq.
    destruct Ht as [Ht1 Ht2].
    apply Forall_app. split; [exact (stk_facts_hold A rho HTOPH HFpre)|].
    apply Forall_app. split; [eapply (qi_geo_facts A); eassumption|].
    apply Forall_app. split; [eapply (qi_it_facts A); eassumption|].
    destruct vb; [assert (EVB' : vb_of it = true) by (symmetry; exact EVB); eapply (qi_mag_facts A); eassumption | apply Forall_nil]. }
  exact (SPA_axforms segsA _ _ rho _ _ tp _ (Cqi_eq vb) H3).
Qed.
End QIEnv.

Definition BLQ : list positive := ltac2:(tb__ "0|0|
S2S1Pc8S2S1Pc9S2S1PcaS2S1PcbS2S1PccS2S1PcdS2S1PceS2S1PcfS2S1Pd1S2S1Pd2S8S1A1A3A3A3A3A3A3A3A3A3A3").

Section QIPre.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).

Lemma qi_unobj : ltac2:(tb__ "0|3|
S4dS0S0S0S3S7S5S0S0A2M0A1S7S4cA1M1G1G0S26S7S40Q40A1A1S7Sa7A1M2Sb8Sa6S1bG1S51ReA1S8S4cA1A3S1bS6S4fRfA1SaA3S0S9bR11R1A2S9bVA0;R2A2F_;Fz;S1bG1S50R11A1S2S4cS52R10S2G0R9RcA3RfA3S9S4cRbRaA3A3A3S7eS3fS93VK;VA0;Vrho0;R12R11RfReS2G0RaRdA3RcRbAaS84R9R8S4G2Sa4R7Sa5R6R5A2A4A6Sb6RaR12R10RfRbA5Sb7RbR13R10RcA4Sb9RcS2S20S7cS2S20S86S8S20A1A3A3SbeR8RbR9A3A3S26S1aS7eS3fS93VK;VA0;Vrho0;R16R15R13R12S2G0ReR11A3R10RfAaS58R1RcS4G2Sa4RbSa5RaR9A2A4A6S1bS74S73S3fS23R1A1A2S73S3fS23RdA1A2A3A2Trho3;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fit;Frest;Ftmp';Fits;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd its tmp' rest it rho tp tr ms md HTH HCI HQW HGL H (E162 & E163 & E164 & E165 & E166) HS rho3.
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  destruct HRIG as (E151 & E152 & E155 & E156).
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE.
  assert (INB : In (mkQB a (it :: its) s) (aa_q_global A)) by (rewrite HGL; left; reflexivity).
  destruct (batch_addr_facts A HTH rho _ BE INB) as (BA1 & BA2 & BA3 & BA4 & BA5). cbn [qb_addr] in BA1, BA2, BA3, BA4, BA5. unfold HIGH_SHADOW_END in BA4.
  pose proof HCB as (_ & HN0 & HN1 & _). unfold kQuarantineBatchCount in HN1. cbn [length] in HN0.
  set (B := a + 152 + 8 * Z.of_nat nd) in *.
  set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.
  assert (EB : bv_unsigned (eval rho vS7) = B) by (unfold vS7; cbn [eval]; rewrite E163, u64_lit by (unfold B; lia); reflexivity).
  assert (HSB : cell_ok v (mkACell 0xeddb8 8 (ag_spacebeg (aa_geom A)))) by (unfold rtc_inv, rtc_cells in HRTC; exact (cells_ok_nth _ _ 3 _ HRTC eq_refl)).
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) _ [O_sb; O_it] (SLit 0) 0xeddb8 0xeddc0 _ Hsm DQIs_objs2 ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) _ [O_sb; O_it] vS7 (-128) (-120) [(-128, 8%nat, vIT)] Hsm DQIs_objs2 ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                ltac:(rewrite EB; unfold B; lia) ltac:(rewrite EB; unfold B; lia)) as [AV2 PR2].
  fold rho3 v3 in AV1, PR1, AV2, PR2. cbn [eval] in AV1, PR1. rewrite u64_lit in AV1, PR1 by lia. rewrite EB in AV2, PR2.
  assert (C_sb : cell_ok v3 (mkACell 0xeddb8 8 (ag_spacebeg (aa_geom A)))) by (replace 0xeddb8 with (0 + 0xeddb8) by lia; exact (av_cell v3 0 0xeddb8 8 _ _ rho (fun j => AV1 _ _ _ j (or_introl eq_refl)) E155)).
  assert (C0 : cell_ok v3 (mkACell (B + -128) 8 (fst it - 16))) by exact (av_cell v3 B (-128) 8 _ _ rho (fun j => AV2 _ _ _ j (or_introl eq_refl)) E165).
  clear AV1 AV2. unfold HVS in HS. fold v in HS. replace (a + 24 + 8 * Z.of_nat nd) with (B + -128) in HS by (unfold B; lia).
  set (P := fun z : Z => (0xeddb8 <= z < 0xeddc0) \/ (B - 128 <= z < B - 120)).
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).
  assert (INRG : forall x, in_ranges rho [O_sb; O_it] x -> P (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold P. destruct Ho as [<-|[<-|[]]].
    - left. unfold O_sb, carved in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd eval] in Hz. rewrite u64_lit in Hz by lia. lia.
    - right. unfold O_it in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz. rewrite EB in Hz. lia. }
  destruct (absorb_out rho [O_sb; O_it] (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (EV : v3 = v).
  { apply functional_extensionality. intros z. destruct (PD z) as [[Hz|Hz]|Np]; [| |exact (FR z Np)].
    - apply (cell_ok_same v v3 _ HSB C_sb); cbn [c_addr c_w]; lia.
    - apply (cell_ok_same v v3 _ HS C0); cbn [c_addr c_w]; lia. }
  destruct (K_FRM_absorb2 K HL A0 rho0 A HQW rho rho3 tp tr md P PD ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)) as [HK3 HF3]; try assumption.
  { intros z Hz. destruct Hz as [Hz|Hz].
    - split; [unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; lia|]. right. split; [right; unfold qrtc_zone; lia|].
      fold v3 v. rewrite EV. reflexivity.
    - destruct (batch_in_QW A HTH rho _ z BE INB ltac:(cbn [qb_addr]; unfold B in Hz; lia)) as [Q1 Q2]. split; [exact Q2 | left; exact Q1]. }
  { intros z Hz. fold v3. destruct Hz as [Hz|Hz]; [destruct (PR1 z ltac:(lia)) as [x Hx] | destruct (PR2 z ltac:(lia)) as [x Hx]]; rewrite Hx; discriminate. }
  split; [|exact EV].
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ DQIs rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho DQIs _ [O_sb; O_it] tp tr ms md DQIs_objs2 HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU. rewrite DQI0_eq in HU.
  split; [exact (proj1 HU)|]. split; [exact HK3|]. fold v3. rewrite EV. split; [exact HCB|]. split; [exact HRM | exact HF3].
Qed.

Lemma qienv_of_K : ltac2:(tb__ "0|6|
S4dS0S0S0S3S5S0S0A2M0S7G0A1S7S4cA1M1G1S26S7S40Q40A1A1S7Sa7A1Sa6S0S0S1bG1S51RfA1S8S4cA1A3S1bS6S4fR10A1SaA3S1bG1S50R11A1S2S4cS52R10S2G0RcRbA3RfA3S9S4cRaR9A3A3A3S1bS6S8fSdS0S0RdA3A1SaA3S13S19SfS0S53S9cR13S99ReA1M2A2A1A2A1S8dG2A1A2VK;R14RbRaR9R8A5S94S73S3fS23RcA1A2R14R12R11S2G0R10RfA3A5Sb5RdR11S9cR16S99R11A1A2R9R8A5S1aS10Z0M3RaA2S13RaZ100A2A2S1bSbS40Q8M4A1M5A1S73S3fS23RfA1S17SeS0S0R13A3ZfA2A3ScG5S41G4RbA2A2A3S1aS10G3RbA2S13RbS12Z2Z40A2A2A2S75S73S3fS23R11A1A2S76S11S56S4eR1aA1A1Zae0A2U8RcA3A2S5bR1bR16R12ReRdA5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fst;Ft;Fmd;Ftr;Ftp;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it its tmp' rest rho tp tr md t st HTH HCI HGL HPR HNF HK HCB HQV Ht1 Ht2 Hst1 Hst2.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE. destruct BE as [_ _ HQP HAU _ _ _].
  assert (HIN : In it (qitems (qall A))) by (rewrite (qall_A1 A HTH), HGL; unfold qitems; cbn [flat_map qb_items app]; left; reflexivity).
  pose proof (item_slot A HQP HAU HG it HIN HPR) as IS. cbv zeta in IS. destruct IS as (C1 & _).
  pose proof (HCLS HCI (it_cls it) C1) as CV.
  pose proof (cv_bounds _ _ _ _ _ CV) as (_ & B2 & B3 & _).
  assert (HMU : cs_allocated_user (cls_of A (it_cls it)) <= cs_mapped_user (cls_of A (it_cls it)) <= kUserSpaceSize) by lia.
  pose proof (qi_geom A HG HQP HAU rho it t HIN HPR Ht1 HRIG) as GEO. cbv zeta in GEO.
  destruct HCB as (_ & _ & _ & _ & HITM). destruct (HITM 0%nat it eq_refl) as [_ IM].
  constructor; try assumption; split; assumption.
Qed.

Lemma qi_pre : ltac2:(tb__ "0|4|
S4dS0S0S0S3S5S0S0A2M0S7G0A1S7S4cA1M1G1S26S7S40Q40A1M2A1Sa8S1bG1S51RcA1S8S4cA1A3S1bS6S4fRdA1SaA3S0S9bRfR1A2S9bVA0;R2A2F_;Fz;S1bG1S50RfA1S2S4cS52ReS2G0RaR9A3RdA3S9S4cR8R7A3A3A3S1bS6S8fSdS0S0RbA3A1SaA3S13S19SfS0S53S9cR11S99RcA1M3A2A1A2A1S8dG3A1A2S7eS3fS93VK;VA0;Vrho0;R12R11RfReS2G0RdRcA3RbRaAaS84R9R8R7A6Sb6RaR12R10RfReA5Sb7RbR13R10RfA4S1dS26S26S1dS0S0S1dS0S0S1aS7eS3fS93VK;VA0;Vrho0;R18R17R15R14S2G0R13R12A3R11R10AaSa2Sb4R13A1A1R3ReRdA6S1aS5bR18R13R3R2R1A5S1aS1S1eS70S1R1S6aA3A1S1bG2S2aR5R2A2S2aR11R2A2A3F_;Fi;S1bS74S73S3fS23R3A1A2S73S3fS23RfA1A2A3A2A2A2Lst;A2Lt;A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it its tmp' rest rho tp w HTH HCI HQW HGL HPR HNF H HVi HVs. destruct w as [tr [ms md]].
  pose proof (qi_unobj A a s n0 nd its tmp' rest it rho tp tr ms md HTH HCI HQW HGL H HVi HVs) as X. cbn zeta in X. destruct X as [H0 EV0].
  set (rho3 := rho_absorb rho [O_sb; O_it] (vms md tp ms)) in *.
  destruct (proj2 H0) as (HK & HCB & _). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB.
  destruct (kq_facts segsA K HL A rho3 tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof HCB as (_ & _ & _ & _ & HITM). destruct (HITM 0%nat it eq_refl) as [_ IM].
  pose proof IM as (_ & IM2 & _). replace (fst it - 14) with (fst it - 15 + 1) in IM2 by lia. destruct (present_byte _ _ IM2) as (t & Ht1 & Ht2).
  assert (PST : present (view segsA (rm rho3)) (ag_thread (aa_geom A) + 2784) (ag_thread (aa_geom A) + 2784 + 8)) by (intros z Hz; apply HST; lia).
  destruct (present_cell8q _ _ PST) as (st & Hst1 & Hst2).
  set (c := it_cls it) in *. set (cs := cls_of A c) in *.
  set (rho2 := rho_sets rho3 [(200%positive, Z_to_bv 64 c); (201%positive, Z_to_bv 64 (Size c)); (202%positive, Z_to_bv 64 (cs_mapped_user cs));
                              (203%positive, Z_to_bv 64 (3 + 256 * t + 65536 * (snd it / 2 ^ 32))); (204%positive, Z_to_bv 64 (snd it mod 2 ^ 32));
                              (205%positive, Z_to_bv 64 ((snd it + 7) / 8 * 8)); (206%positive, Z_to_bv 64 (Z.of_nat (length (cs_cache cs))));
                              (207%positive, Z_to_bv 64 (max_count c)); (209%positive, Z_to_bv 64 st); (210%positive, Z_to_bv 64 (it_ab it))]).
  pose proof (JRI_stable K HL A0 rho0 A a n0 nd (it :: its) tmp' rest) as HSTB.
  assert (H1 : SPA segsA (JRI K A0 rho0 A a n0 nd (it :: its) tmp' rest) DQI0 rho2 tp (tr, mkCfg ms md)).
  { apply (SPA_bindV segsA _ NPRE DQI0 rho3 tp _ _ eq_refl HSTB); [| exact (proj1 DQI0_vars) | exact (proj2 DQI0_vars) | exact H0].
    intros v Hv. cbn in Hv. repeat (destruct Hv as [<-|Hv]; [unfold NPRE, Pos.le; cbn; discriminate|]). destruct Hv. }
  assert (OTH : forall i, ~ In i BLQ -> rw rho2 i = rw rho i) by (intros i Hi; unfold rho2; rewrite rho_sets_other by exact Hi; reflexivity).
  assert (ERM : rm rho2 = rm rho3) by (unfold rho2; apply rm_rho_sets).
  assert (NB : forall i, (i < 200)%positive -> ~ In i BLQ) by (intros i Hi X; unfold BLQ in X; cbn in X; lia).
  assert (HQV : QIV rho2 it cs t st).
  { destruct HVi as (_ & _ & _ & E165 & _). unfold QIV. cbv zeta. fold c.
    split; [rewrite (OTH 165%positive (NB 165%positive ltac:(lia))); exact E165|]. repeat split; reflexivity. }
  destruct (proj2 H1) as (HK2 & HCB2 & _). cbn [w_tr w_cfg cfg_model fst snd] in HK2, HCB2.
  assert (QE : qienv A it rho2 t st).
  { apply (qienv_of_K A a s n0 nd it its tmp' rest rho2 tp tr md t st HTH HCI HGL HPR HNF HK2 HCB2 HQV Ht1); [rewrite ERM; exact Ht2 | exact Hst1 | rewrite ERM; exact Hst2]. }
  exists rho2, t, st. split; [|split; [exact QE | split; [exact OTH | rewrite ERM; exact EV0]]].
  apply (qi_carve A it rho2 t st QE); [|exact H1].
  destruct (kq_facts segsA K HL A rho2 tp _ _ HK2) as [_ _ _ _ _ _ _ _ _ _ _ HKTOP2 _]. exact HKTOP2.
Qed.
End QIPre.
End SegQ3D_qip.

(* [comment removed for export] *)
Module SpineMallocS5i.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "prod"; "list"; "pair"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "swf"; "SVar"; "ss_facts"; "SLit"; "ss_next"; "SPUle"; "SPBranch"; "SPNot"; "ss_objs"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E3p"; "E5s1"; "E5s2"; "C5b"; "C5c"; "E5f"; "C3"; "E5n"; "sreg1"; "sreg2"; "C6"; "V_CLS"; "C2p"; "C2r"; "C5"; "E3r"; "E4d"; "V_SIZE"; "F_gen"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "V_CNT"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "E5s1'"; "E5s2'"; "tab1_ok"; "clsp_e"; "clsp_e31"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4"; "Y7"; "Y1"; "Y2"; "Y3"; "Y4"; "Y5"; "Y6"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineMallocS5i.INST"; "s1_0"; "s2_0"; "s3_0"; "s6n_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S28VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C2p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C2p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C2p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E3p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E3p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E3p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S22VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C3 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C3] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C3]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S29VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C2r W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C2r] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C2r]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S2bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E3r W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E3r] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E3r]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S2cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E4d W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E4d] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E4d]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S2aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S23VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5n W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5n] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5n]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S21VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5f W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5f] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5f]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_9 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S26VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C6]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_10 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1fVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_11 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1dVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5s1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_12 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1eVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5s2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_13 : ltac2:(tb__ "0|0|
S1bSfSfS4SfS24VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (sreg1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [sreg1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [sreg1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_14 : ltac2:(tb__ "0|0|
S1bSfSfS4SfS25VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (sreg2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [sreg2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [sreg2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_15 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S38U0Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s1' 0%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5s1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_16 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S39U0Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s2' 0%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5s2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_17 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S20VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5c W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5c] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5c]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma Cert3p_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z40cc4S5S34Z3c480S8S34A1A3A3S36S5S0S28VW;Vst;Vtmax;A3S8S0A1M0A3S5S0S1cVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C2p W st tmax) memo_0. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SKY_0 : ltac2:(tb__ "0|1|
S4SaS9S9SfSfA2SfA2M0A1S4bS11G0S4fS1aS1S1cVW;Vst;Vtmax;A3A1A1A4S4bS11G0S4fScS11ScS11S5S11S56ScS11S5bVW;A1S57A3A3S55A3S5S11S2fS5S11S31S5S11S30S5S11S32S8S11A1A3A3A3A3A3A4A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma YX_0 : ltac2:(tb__ "0|1|
S4SaS9SfSfA2M0A1S3S1cVW;Vst;Vtmax;A3A1S8G0A1A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma YF_0 : ltac2:(tb__ "0|0|
S3eS10ScS10ScS10ScS10S5aVW;Vst;A2S59S58A1A3S54A3S2eA3S14S1S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma YP_0 : ltac2:(tb__ "0|0|
S3dS10S17S15Z1A1S13S33A1A2S14S1S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY1_0 : ltac2:(tb__ "0|0|
S4S6S12S1S45S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY2_0 : ltac2:(tb__ "0|0|
S4S6S12S1S46S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY3_0 : ltac2:(tb__ "0|0|
S4S6S12S1S47S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY4_0 : ltac2:(tb__ "0|0|
S4S6S12S1S48S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY5_0 : ltac2:(tb__ "0|0|
S4S6S12S1S49S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY6_0 : ltac2:(tb__ "0|0|
S4S6S12S1S4aS1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY7_0 : ltac2:(tb__ "0|0|
S4S6S12S1S44S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s3_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S44S1cVW;Vst;Vtmax;A3A1A1S1S22VW;Vst;Vtmax;A3A1A3").
Lemma ENT3_0 : ltac2:(tb__ "0|0|
S4S6S2S44S1cVW;Vst;Vtmax;A3A1S22VW;Vst;Vtmax;A3S52A3S7A3").
Proof. unfold s3_0. memo_rw (E3p W st tmax) memo_1. memo_rw (C3 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID3_0 : ltac2:(tb__ "0|0|
S4S6S42S52S36A2S7A3").
Proof. unfold s3_0. memo_rw (C3 W st tmax) memo_2. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert3r_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z40cc4S5S34Z3c480S8S34A1A3A3S36S5S0S29VW;Vst;Vtmax;A3S8S0A1M0A3S5S0S2bVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C2r W st tmax) memo_3. memo_rw (E3r W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert4_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z7e850S8S34A1A3S36S5S0S22VW;Vst;Vtmax;A3S8S0A1M0A3S5S0S2cVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C3 W st tmax) memo_2. memo_rw (E4d W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert5_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z3c5e0S5S34Z3c678S8S34A1A3A3S36S5S0S2aVW;Vst;Vtmax;A3S8S0A1M0A3S5S0S23VW;Vst;Vtmax;A3S5S0S21VW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. memo_rw (C5 W st tmax) memo_6. memo_rw (E5n W st tmax) memo_7. memo_rw (E5f W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s6n_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S23VW;Vst;Vtmax;A3A1S1S26VW;Vst;Vtmax;A3A1A3").
Lemma ENT6n_0 : ltac2:(tb__ "0|0|
S4S6S2S23VW;Vst;Vtmax;A3S26VW;Vst;Vtmax;A3S53A3S7A3").
Proof. unfold s6n_0. memo_rw (E5n W st tmax) memo_7. memo_rw (C6 W st tmax) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID6n_0 : ltac2:(tb__ "0|0|
S4S6S42S53S36A2S7A3").
Proof. unfold s6n_0. memo_rw (C6 W st tmax) memo_9. memo_rw (E5n W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W5b_0 : ltac2:(tb__ "0|0|
S4S6S12S1S1fVW;Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (C5b W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D5b_0 : ltac2:(tb__ "0|5|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S43S1S21VW;Vst;Vtmax;A3A1S1S1fVW;Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS3cS13S27A1M4A4S5G0SbSfSfS3bG4A4S8G0A1A3A3S8S10A1A4A2A3").
Proof. memo_rw (E5f W st tmax) memo_8. memo_rw (C5b W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX5b_0 : ltac2:(tb__ "0|0|
S4S35S16S1S1fVW;Vst;Vtmax;A3A1A1S16S1S21VW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (C5b W st tmax) memo_10. memo_rw (E5f W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F5f64_0 : ltac2:(tb__ "0|0|
S3dS10S17S13PcA1S15Zfc00A1A2S14S1S21VW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5f W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert5b_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z3c64cS8S34A1A3S36S5S0S1fVW;Vst;Vtmax;A3S8S0A1M0A3S5S0S1dVW;Vst;Vtmax;A3S5S0S1eVW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. memo_rw (C5b W st tmax) memo_10. memo_rw (E5s1 W st tmax) memo_11. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OV1_0 : ltac2:(tb__ "0|0|
S4S6S4eP9eS24VW;Vst;Vtmax;A3A2S7A3").
Proof. memo_rw (sreg1 W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OV2_0 : ltac2:(tb__ "0|0|
S4S6S4eP9eS25VW;Vst;Vtmax;A3A2S7A3").
Proof. memo_rw (sreg2 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TAB1_0 : ltac2:(tb__ "0|0|
S4S6S3aP9eS24VW;Vst;Vtmax;A3S4dZ11UeA5S7A3").
Proof. memo_rw (sreg1 W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TAB2_0 : ltac2:(tb__ "0|0|
S4S6S3aP9eS25VW;Vst;Vtmax;A3S4dZ1U10A5S7A3").
Proof. memo_rw (sreg2 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1'_0 : ltac2:(tb__ "0|0|
S4S6S12S1S38U0Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (E5s1' 0%nat st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W2'_0 : ltac2:(tb__ "0|0|
S4S6S12S1S39U0Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (E5s2' 0%nat st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D1'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S43S1S1dVW;Vst;Vtmax;A3A1S1S38U0Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS24VW;Vst;Vtmax;A3S13S2dA1A4S8G0A1A3S8S10A1A4A2A3").
Proof. memo_rw (E5s1 W st tmax) memo_11. memo_rw (E5s1' 0%nat st tmax) memo_15. memo_rw (sreg1 W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D2'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S43S1S1eVW;Vst;Vtmax;A3A1S1S39U0Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS25VW;Vst;Vtmax;A3S13S2dA1A4S8G0A1A3S8S10A1A4A2A3").
Proof. memo_rw (E5s2 W st tmax) memo_12. memo_rw (E5s2' 0%nat st tmax) memo_16. memo_rw (sreg2 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1'_0 : ltac2:(tb__ "0|0|
S4S35S16S1S38U0Vst;Vtmax;A3A1A1S16S1S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E5s1' 0%nat st tmax) memo_15. memo_rw (E5s1 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX2'_0 : ltac2:(tb__ "0|0|
S4S35S16S1S39U0Vst;Vtmax;A3A1A1S16S1S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E5s2' 0%nat st tmax) memo_16. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F1gt_0 : ltac2:(tb__ "0|0|
S3dS10S18S4cS15Z10A1S13S27A1A3S14S1S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s1 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2le_0 : ltac2:(tb__ "0|0|
S3dS10S19S18S4cS15Z10A1S13S27A1A3A1S14S1S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F1_64_0 : ltac2:(tb__ "0|0|
S3dS10S17S13PcA1S15Zfc00A1A2S14S1S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s1 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2_64_0 : ltac2:(tb__ "0|0|
S3dS10S17S13PcA1S15Zfc00A1A2S14S1S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s1_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S38U0Vst;Vtmax;A3A1S1S20VW;Vst;Vtmax;A3A1A3").
Definition s2_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S39U0Vst;Vtmax;A3A1S1S20VW;Vst;Vtmax;A3A1A3").
Lemma ENT1_0 : ltac2:(tb__ "0|0|
S4S6S2S38U0Vst;Vtmax;A3S20VW;Vst;Vtmax;A3S50A3S7A3").
Proof. unfold s1_0. memo_rw (E5s1' 0%nat st tmax) memo_15. memo_rw (C5c W st tmax) memo_17. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT2_0 : ltac2:(tb__ "0|0|
S4S6S2S39U0Vst;Vtmax;A3S20VW;Vst;Vtmax;A3S51A3S7A3").
Proof. unfold s2_0. memo_rw (E5s2' 0%nat st tmax) memo_16. memo_rw (C5c W st tmax) memo_17. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID1_0 : ltac2:(tb__ "0|0|
S4S6S42S50S36A2S7A3").
Proof. unfold s1_0. memo_rw (C5c W st tmax) memo_17. memo_rw (E5s1' 0%nat st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID2_0 : ltac2:(tb__ "0|0|
S4S6S42S51S36A2S7A3").
Proof. unfold s2_0. memo_rw (C5c W st tmax) memo_17. memo_rw (E5s2' 0%nat st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS5i.

(* [comment removed for export] *)
Module SpineMallocS5iW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "prod"; "list"; "pair"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "swf"; "SVar"; "ss_facts"; "SLit"; "ss_next"; "SPUle"; "SPBranch"; "SPNot"; "ss_objs"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E3p"; "E5s1"; "E5s2"; "C5b"; "C5c"; "E5f"; "C3"; "E5n"; "sreg1"; "sreg2"; "C6"; "V_CLS"; "C2p"; "C2r"; "C5"; "E3r"; "E4d"; "V_SIZE"; "F_gen"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "V_CNT"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "E5s1'"; "E5s2'"; "tab1_ok"; "clsp_e"; "clsp_e31"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4"; "Y7"; "Y1"; "Y2"; "Y3"; "Y4"; "Y5"; "Y6"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineMallocS5iW2.INST"; "s1_0"; "s2_0"; "s3_0"; "s6n_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S28VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C2p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C2p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C2p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E3p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E3p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E3p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S22VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C3 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C3] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C3]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S29VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C2r W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C2r] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C2r]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S2bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E3r W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E3r] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E3r]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S2cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E4d W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E4d] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E4d]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S2aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S23VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5n W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5n] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5n]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S21VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5f W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5f] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5f]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_9 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S26VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C6]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_10 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1fVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_11 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1dVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5s1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_12 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1eVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5s2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_13 : ltac2:(tb__ "0|0|
S1bSfSfS4SfS24VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (sreg1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [sreg1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [sreg1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_14 : ltac2:(tb__ "0|0|
S1bSfSfS4SfS25VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (sreg2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [sreg2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [sreg2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_15 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S38U2Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s1' 2%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5s1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_16 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S39U2Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s2' 2%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5s2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_17 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S20VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5c W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5c] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5c]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma Cert3p_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z40cc4S5S34Z3c480S8S34A1A3A3S36S5S0S28VW;Vst;Vtmax;A3S8S0A1M0A3S5S0S1cVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C2p W st tmax) memo_0. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SKY_0 : ltac2:(tb__ "0|1|
S4SaS9S9SfSfA2SfA2M0A1S4bS11G0S4fS1aS1S1cVW;Vst;Vtmax;A3A1A1A4S4bS11G0S4fScS11ScS11S5S11S56ScS11S5bVW;A1S57A3A3S55A3S5S11S2fS5S11S31S5S11S30S5S11S32S8S11A1A3A3A3A3A3A4A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma YX_0 : ltac2:(tb__ "0|1|
S4SaS9SfSfA2M0A1S3S1cVW;Vst;Vtmax;A3A1S8G0A1A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma YF_0 : ltac2:(tb__ "0|0|
S3eS10ScS10ScS10ScS10S5aVW;Vst;A2S59S58A1A3S54A3S2eA3S14S1S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma YP_0 : ltac2:(tb__ "0|0|
S3dS10S17S15Z1A1S13S33A1A2S14S1S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY1_0 : ltac2:(tb__ "0|0|
S4S6S12S1S45S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY2_0 : ltac2:(tb__ "0|0|
S4S6S12S1S46S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY3_0 : ltac2:(tb__ "0|0|
S4S6S12S1S47S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY4_0 : ltac2:(tb__ "0|0|
S4S6S12S1S48S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY5_0 : ltac2:(tb__ "0|0|
S4S6S12S1S49S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY6_0 : ltac2:(tb__ "0|0|
S4S6S12S1S4aS1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY7_0 : ltac2:(tb__ "0|0|
S4S6S12S1S44S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s3_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S44S1cVW;Vst;Vtmax;A3A1A1S1S22VW;Vst;Vtmax;A3A1A3").
Lemma ENT3_0 : ltac2:(tb__ "0|0|
S4S6S2S44S1cVW;Vst;Vtmax;A3A1S22VW;Vst;Vtmax;A3S52A3S7A3").
Proof. unfold s3_0. memo_rw (E3p W st tmax) memo_1. memo_rw (C3 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID3_0 : ltac2:(tb__ "0|0|
S4S6S42S52S36A2S7A3").
Proof. unfold s3_0. memo_rw (C3 W st tmax) memo_2. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert3r_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z40cc4S5S34Z3c480S8S34A1A3A3S36S5S0S29VW;Vst;Vtmax;A3S8S0A1M0A3S5S0S2bVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C2r W st tmax) memo_3. memo_rw (E3r W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert4_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z7e850S8S34A1A3S36S5S0S22VW;Vst;Vtmax;A3S8S0A1M0A3S5S0S2cVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C3 W st tmax) memo_2. memo_rw (E4d W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert5_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z3c5e0S5S34Z3c678S8S34A1A3A3S36S5S0S2aVW;Vst;Vtmax;A3S8S0A1M0A3S5S0S23VW;Vst;Vtmax;A3S5S0S21VW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. memo_rw (C5 W st tmax) memo_6. memo_rw (E5n W st tmax) memo_7. memo_rw (E5f W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s6n_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S23VW;Vst;Vtmax;A3A1S1S26VW;Vst;Vtmax;A3A1A3").
Lemma ENT6n_0 : ltac2:(tb__ "0|0|
S4S6S2S23VW;Vst;Vtmax;A3S26VW;Vst;Vtmax;A3S53A3S7A3").
Proof. unfold s6n_0. memo_rw (E5n W st tmax) memo_7. memo_rw (C6 W st tmax) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID6n_0 : ltac2:(tb__ "0|0|
S4S6S42S53S36A2S7A3").
Proof. unfold s6n_0. memo_rw (C6 W st tmax) memo_9. memo_rw (E5n W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W5b_0 : ltac2:(tb__ "0|0|
S4S6S12S1S1fVW;Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (C5b W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D5b_0 : ltac2:(tb__ "0|5|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S43S1S21VW;Vst;Vtmax;A3A1S1S1fVW;Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS3cS13S27A1M4A4S5G0SbSfSfS3bG4A4S8G0A1A3A3S8S10A1A4A2A3").
Proof. memo_rw (E5f W st tmax) memo_8. memo_rw (C5b W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX5b_0 : ltac2:(tb__ "0|0|
S4S35S16S1S1fVW;Vst;Vtmax;A3A1A1S16S1S21VW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (C5b W st tmax) memo_10. memo_rw (E5f W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F5f64_0 : ltac2:(tb__ "0|0|
S3dS10S17S13PcA1S15Zfc00A1A2S14S1S21VW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5f W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert5b_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z3c64cS8S34A1A3S36S5S0S1fVW;Vst;Vtmax;A3S8S0A1M0A3S5S0S1dVW;Vst;Vtmax;A3S5S0S1eVW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. memo_rw (C5b W st tmax) memo_10. memo_rw (E5s1 W st tmax) memo_11. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OV1_0 : ltac2:(tb__ "0|0|
S4S6S4eP9eS24VW;Vst;Vtmax;A3A2S7A3").
Proof. memo_rw (sreg1 W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OV2_0 : ltac2:(tb__ "0|0|
S4S6S4eP9eS25VW;Vst;Vtmax;A3A2S7A3").
Proof. memo_rw (sreg2 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TAB1_0 : ltac2:(tb__ "0|0|
S4S6S3aP9eS24VW;Vst;Vtmax;A3S4dZ11UeA5S7A3").
Proof. memo_rw (sreg1 W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TAB2_0 : ltac2:(tb__ "0|0|
S4S6S3aP9eS25VW;Vst;Vtmax;A3S4dZ1U10A5S7A3").
Proof. memo_rw (sreg2 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1'_0 : ltac2:(tb__ "0|0|
S4S6S12S1S38U2Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (E5s1' 2%nat st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W2'_0 : ltac2:(tb__ "0|0|
S4S6S12S1S39U2Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (E5s2' 2%nat st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D1'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S43S1S1dVW;Vst;Vtmax;A3A1S1S38U2Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS24VW;Vst;Vtmax;A3S13S2dA1A4S8G0A1A3S8S10A1A4A2A3").
Proof. memo_rw (E5s1 W st tmax) memo_11. memo_rw (E5s1' 2%nat st tmax) memo_15. memo_rw (sreg1 W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D2'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S43S1S1eVW;Vst;Vtmax;A3A1S1S39U2Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS25VW;Vst;Vtmax;A3S13S2dA1A4S8G0A1A3S8S10A1A4A2A3").
Proof. memo_rw (E5s2 W st tmax) memo_12. memo_rw (E5s2' 2%nat st tmax) memo_16. memo_rw (sreg2 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1'_0 : ltac2:(tb__ "0|0|
S4S35S16S1S38U2Vst;Vtmax;A3A1A1S16S1S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E5s1' 2%nat st tmax) memo_15. memo_rw (E5s1 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX2'_0 : ltac2:(tb__ "0|0|
S4S35S16S1S39U2Vst;Vtmax;A3A1A1S16S1S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E5s2' 2%nat st tmax) memo_16. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F1gt_0 : ltac2:(tb__ "0|0|
S3dS10S18S4cS15Z10A1S13S27A1A3S14S1S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s1 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2le_0 : ltac2:(tb__ "0|0|
S3dS10S19S18S4cS15Z10A1S13S27A1A3A1S14S1S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F1_64_0 : ltac2:(tb__ "0|0|
S3dS10S17S13PcA1S15Zfc00A1A2S14S1S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s1 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2_64_0 : ltac2:(tb__ "0|0|
S3dS10S17S13PcA1S15Zfc00A1A2S14S1S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s1_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S38U2Vst;Vtmax;A3A1S1S20VW;Vst;Vtmax;A3A1A3").
Definition s2_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S39U2Vst;Vtmax;A3A1S1S20VW;Vst;Vtmax;A3A1A3").
Lemma ENT1_0 : ltac2:(tb__ "0|0|
S4S6S2S38U2Vst;Vtmax;A3S20VW;Vst;Vtmax;A3S50A3S7A3").
Proof. unfold s1_0. memo_rw (E5s1' 2%nat st tmax) memo_15. memo_rw (C5c W st tmax) memo_17. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT2_0 : ltac2:(tb__ "0|0|
S4S6S2S39U2Vst;Vtmax;A3S20VW;Vst;Vtmax;A3S51A3S7A3").
Proof. unfold s2_0. memo_rw (E5s2' 2%nat st tmax) memo_16. memo_rw (C5c W st tmax) memo_17. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID1_0 : ltac2:(tb__ "0|0|
S4S6S42S50S36A2S7A3").
Proof. unfold s1_0. memo_rw (C5c W st tmax) memo_17. memo_rw (E5s1' 2%nat st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID2_0 : ltac2:(tb__ "0|0|
S4S6S42S51S36A2S7A3").
Proof. unfold s2_0. memo_rw (C5c W st tmax) memo_17. memo_rw (E5s2' 2%nat st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS5iW2.

