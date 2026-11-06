(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay F0A_instG.
From Stdlib Require Permutation.
From stdpp Require list.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1 RebuildRZ F0A_instok.

(* [comment removed for export] *)
Module F0A_minstG.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "FcsrFrm0"; "mkSS"; "swf"; "SVar"; "sprop"; "valuation"; "DUnknown"; "SLit"; "agree_below"; "cell"; "mkObj"; "sprop_below"; "@Corelib.Init.Datatypes"; "app"; "nil"; "cons"; "true"; "None"; "bool"; "false"; "list"; "prod"; "Some"; "length"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates"; "MIDPC"; "regs_mid"; "stack_win_mid"; "Pre_mid"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "NRT"; "O_pad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG"; "FACTSg"; "XIg"; "instG_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "O_sh"; "RT_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "mkA"; "ulink"; "unwind_objs"; "J_free_preT"; "KcA"; "UStopLeOrPc"; "free_depth"; "pre_facts"; "unwind_factsS"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG.StatesMG"; "sd_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "@Stdlib.Lists.List"; "forallb"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section StatesMG.
Variable khi : bool.
Variables (W : list ulink) (st : ustop) (NVl : list carve_spec) (VF : list sprop).
Let PREOBJS : list sobj := ltac2:(tb__ "0|0|
S10S0S23SeS0S37VW;A1SeS0S10S0ScS5PcA1S9Z0A1S5PdA1SfSbA1S8A5SfS0A1A3S34A3A3A3").
Let PREFACTS : list sprop := ltac2:(tb__ "0|0|
SeS6S3dVW;Vst;A2S3cS3bA1A3").
Definition sb_mg : sstate := ltac2:(tb__ "0|0|
S3S21S22S20S2S12S1A1SeS0VPREOBJS;S1fS1aS0S1bSeS1aS26VNVl;A3A4A3VPREFACTS;S1eS14A9").
Definition sc_mg : sstate := ltac2:(tb__ "0|0|
S3S21S22S20S2S12S1A1SeS0SeS0VPREOBJS;S1fS1aS0S1bSeS1aS26VNVl;A3A4A3S10S0S32SfS0A1A3A3VPREFACTS;S1eS14A9").
Definition sd_mg : sstate := ltac2:(tb__ "0|1|
S3S21S22S20S2S12S1A1SeS0SeS0SeS0VPREOBJS;S1fS1aS0S1bSeS1aS26VNVl;A3A4A3S10S0S32SfS0A1M0A3A3S10S0S27G0A3A3VPREFACTS;S1eS14A9").
Definition se_mg : axst := ltac2:(tb__ "0|0|
S35S40S42S28Vkhi;VW;Vst;VVF;A4A2SfS16S1S1A2A1A2").
End StatesMG.

Definition PMID_g (khi : bool) (W : list ulink) (st : ustop) (VOBJl : list sobj) (VF : list sprop) : axst := ltac2:(tb__ "0|0|
S35S3S21S22S20S2S12S1A1SeS0SeS0S10S0S23SeS0S37VW;A1S34A3A3S33A3VVOBJl;A3S28Vkhi;VW;Vst;VVF;A4S1eS14A9SfS16S1S1A2A1A2").

Section INSTMG.
Let segs : list Segment := segsA.
Variable khi : bool.
Variable nW : nat. Variable st : ustop. Variable NVl : list carve_spec. Variable VF : list sprop.
Let W : list ulink := Wcan nW.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S38VAInv;VW;Vst;VA;VKc;A5").

Hypothesis Wb : ltac2:(tb__ "0|0|
S1cS13S4S2eVW;Vst;VNVl;A3A1S11A3").
Hypothesis Wc : ltac2:(tb__ "0|0|
S1cS13S4S2fVW;Vst;VNVl;A3A1S11A3").
Hypothesis Wd : ltac2:(tb__ "0|0|
S1cS13S4S30VW;Vst;VNVl;A3A1S11A3").
Hypothesis Fe : ltac2:(tb__ "0|0|
S1cS13S49S6SdS1eA1S28Vkhi;VW;Vst;VVF;A4A3S11A3").
Hypothesis AXI : ltac2:(tb__ "0|0|
S1cS19S2cA1S41S31Vkhi;VW;Vst;VNVl;VVF;A5S29VnW;S18S1aVNVl;A2A2A2S17S2cS2dVkhi;VW;Vst;S1fS1aS0S1bVNVl;A4VVF;A5A2A3").

Theorem g_instantiate_mid : ltac2:(tb__ "0|0|
S45S39S7S7S15S4aQ40A1A1S3fS25S25S25S1cS3eVst;S3aA3S1cS15S36A1VW;SfS36A1A3F_;S48VW;Vst;A2SaS1eR9R8A3S2aVkhi;VW;Vst;VNVl;VVF;R9R6R5R4S47S46RcA1A1AaS2bVsegs;VJ;RdRcA2S24VW;Vst;A2RbR9R8A6S1dS44RcRbA2S2bVsegs;S43VnW;Vst;S11ReRdRbA6S2dVkhi;VW;Vst;S1fS1aS0S1bVNVl;A4VVF;A5RbRaR9A6A2F_;F_;F_;F_;F_;Fn8;Fn;Fp;Fw;Ftp;Frho1;Frho;FKc;FA;").
Proof.
  intros A Kc rho rho1 tp w p n n8 HW HUS Hag2 IFF H.
  assert (Hag : agree_below NF rho rho1) by (eapply agree_below_le; [|exact Hag2]; cbv; discriminate).
  destruct IFF as [E12 E13 E105 E106 Hpn Hcarve Hzone Hpd Hsh Hpadm Hfacts Hrig].
  split; [exact (Hrig rho (agree_below_vals _ _ _ Hag))|]. unfold blk_geo, IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in Hpn.
  pose proof H as [HsmA HJ]. destruct HJ as (HA & HU & HL & HK & Htp & HB & Htop).
  pose proof HA as (HG & _).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & _).
  pose proof (topG_range (aa_geom A)) as TR. set (TOP := topG (aa_geom A)) in *.

  assert (H1 : SPA segs (J A Kc) (Pre_mid W st) rho1 tp w).
  { eapply SPA_agree; [| |exact H]; [eapply agree_below_le; [|exact Hag2]; cbv; discriminate | apply (JFr_agree nW st true A Kc rho rho1); [exact HUS | exact Hag]]. }
  clear H HsmA.
  assert (E24 : rw rho1 24%positive = rw rho 24%positive) by (symmetry; apply (proj1 Hag); unfold NF; lia).

  pose proof (proj2 H1) as (_ & _ & _ & _ & _ & _ & Htop1).
  assert (TOPlo : TOP <= fst (obj_range rho1 stack_win)) by exact Htop1.

  assert (H2 : SPA segs (J A Kc) (mkAX (sa_m W st) [] base_sv) rho1 tp w) by exact H1.
  clear H1.

  pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
  assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn [ss_facts sa_m]; apply in_or_app; right; cbn; tauto).
  destruct (stack_winm_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
  assert (LNK : Forall (fun o => TOP + 16 <= bv_unsigned (eval rho1 (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { unfold unwind_objs. destruct W as [|l W'] eqn:EW; [constructor|].
    destruct st; [|discriminate (HW eq_refl)].
    assert (HC : Forall (holds rho1) (chain_pre (l :: W'))).
    { apply Forall_forall. intros pp Hp. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts sa_m]. apply in_or_app. left. apply chain_pre_in. exact Hp. }
    unfold chain_pre in HC. cbn [app] in HC.
    pose proof (Forall_inv HC) as C0. pose proof (Forall_inv (Forall_inv_tail HC)) as C1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as C2. do 3 apply Forall_inv_tail in HC.
    cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
    pose proof (urange (rw rho1 10%positive)). rewrite Z.mod_small in C1 by lia.
    eapply Forall_impl; [|apply (chain_facts_bases rho1 (SVar 28) (l :: W') HC); cbn [eval]; lia].
    intros o (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia. }

  pose proof (urange (rw rho1 12%positive)) as U12. pose proof (urange (rw rho1 13%positive)) as U13.
  assert (Ep : bv_unsigned (rw rho1 12%positive) = p) by (rewrite E12; apply u64_lit; lia).
  assert (En : bv_unsigned (rw rho1 13%positive) = n) by (rewrite E13; apply u64_lit; lia).

  assert (H3 : SPA segs (J A Kc) (mkAX (sb_mg W st NVl) [] base_sv) rho1 tp w).
  { change (mkAX (sb_mg W st NVl) [] base_sv) with
      (ax_setS (mkAX (sa_m W st) [] base_sv) (let S := ax_S (mkAX (sa_m W st) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ map carve_obj (NRT ++ NVl)) (ss_facts S) NW2 (ss_lenient S))).
    eapply SPA_carve_list; [exact H2 | exact Wb | cbv; discriminate | | |].
    -
      apply Forall_forall. intros k Hk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as C.
      destruct k as [[[base lo] hi] cs]. unfold carve_ok in C. cbn zeta in C |- *.
      destruct C as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
      refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 _)))))))). apply xwords_clear_nil.
    -
      apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk).
      pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
      destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
      destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. rewrite obj_range_mk by lia.
      set (b := bv_unsigned (eval rho1 base)) in *.
      cbn [ss_objs ax_S sa_m]. unfold A_globals, O_got, O_rtc. unfold GOT_LO, GOT_HI, RTC_LO, RTC_HI, IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
      apply Forall_cons.
      { unfold ranges_disjoint. change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win). destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *; lia. }
      apply Forall_app. split.
      { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
        unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia. }
      apply Forall_cons.
      { unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia.
        rewrite (soff_var rho1 13%positive n E13) by lia. cbn [eval]. rewrite Ep. lia. }
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia.
    - exact Hpd. }
  clear H2.

  assert (Hshb : bv_unsigned (eval rho1 shb) = Sh p).
  { unfold shb. rewrite U_add, U_srl_lit, U_lit. cbn [eval]. rewrite Ep. change (3 mod 64) with 3. change (2 ^ 3) with 8.
    unfold Sh, SHADOW_OFF, M64v. change (2147450880 mod 18446744073709551616) with 2147450880.
    pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound p 8 (2 ^ 47 / 8) ltac:(lia) ltac:(lia)).
    rewrite Z.mod_small; [reflexivity | lia]. }
  assert (SH1 : 2147450880 <= Sh p) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)); lia).
  assert (SH2 : Sh p + n8 / 8 <= 17594332446720).
  { unfold Sh, SHADOW_OFF. pose proof (div8_sum_le p n8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (p + n8) 140737479966720 8 ltac:(lia) ltac:(lia)) as M. change (140737479966720 / 8) with 17592184995840 in M. lia. }
  assert (SH3 : 0 <= n8 / 8) by (apply Z.div_pos; lia).
  assert (H4 : SPA segs (J A Kc) (mkAX (sc_mg W st NVl) [] base_sv) rho1 tp w).
  { change (mkAX (sc_mg W st NVl) [] base_sv) with
      (ax_setS (mkAX (sb_mg W st NVl) [] base_sv) (let S := ax_S (mkAX (sb_mg W st NVl) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [mkObj shb (SLit 0) vN8g [] DUnknown]) (ss_facts S) NW2 (ss_lenient S))).
    assert (Elo : soff rho1 (SLit 0) = 0) by (apply soff_lit_small; lia).
    assert (Ehi : soff rho1 vN8g = n8 / 8).
    { unfold vN8g. apply (soff_var rho1 106%positive (n8 / 8) E106). split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    eapply (SPA_carve_unk segs (J A Kc) rho1 _ tp w shb (SLit 0) vN8g NW2 H3 Wc (Pos.le_refl _)); rewrite ?Elo, ?Ehi, ?Hshb; try lia.
    -
      cbn [ss_objs ax_S sb_f]. apply Forall_app. split.
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. apply Forall_cons.
        { unfold ranges_disjoint. change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win). destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *. lia. }
        apply Forall_app. split.
        { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
          unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia. }
        apply Forall_cons.
        { unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia.
          rewrite (soff_var rho1 13%positive n E13) by lia. cbn [eval]. rewrite Ep. lia. }
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia.
      + apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk).
        pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
        destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
        destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. unfold ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd].
        unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
    - intros a Ha. destruct (Hsh a ltac:(lia)) as [x Hx]. split; [|exists x; exact Hx].
      pose proof (rd_off_image (rm rho1) a x ltac:(lia) Hx) as M. unfold wok_of. rewrite M. reflexivity.
    - apply xwords_clear_nil. }
  clear H3.

  assert (H5 : SPA segs (J A Kc) (mkAX (sd_mg W st NVl) [] base_sv) rho1 tp w).
  { change (mkAX (sd_mg W st NVl) [] base_sv) with
      (ax_setS (mkAX (sc_mg W st NVl) [] base_sv) (let S := ax_S (mkAX (sc_mg W st NVl) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [mkObj (SVar 12) (SVar 13) vN8 [] DUnknown]) (ss_facts S) NW2 (ss_lenient S))).
    assert (Elo : soff rho1 (SVar 13) = n) by (apply (soff_var rho1 13%positive n E13); lia).
    assert (Ehi : soff rho1 vN8 = n8) by (unfold vN8; apply (soff_var rho1 105%positive n8 E105); lia).
    assert (Eb : bv_unsigned (eval rho1 (SVar 12)) = p) by (cbn [eval]; exact Ep).
    eapply (SPA_carve_unk segs (J A Kc) rho1 _ tp w (SVar 12) (SVar 13) vN8 NW2 H4 Wd (Pos.le_refl _)); rewrite ?Elo, ?Ehi, ?Eb; try lia.
    -
      cbn [ss_objs ax_S sc_f sb_f]. apply Forall_app. split; [apply Forall_app; split|].
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. apply Forall_cons.
        { unfold ranges_disjoint. change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win). destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *. lia. }
        apply Forall_app. split.
        { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
          unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia. }
        apply Forall_cons.
        { unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia. rewrite Elo. cbn [eval]. rewrite Ep. lia. }
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; unfold HIGH_SHADOW_END in *; lia.
      + apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk).
        pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
        destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
        destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. unfold ranges_disjoint. rewrite obj_range_mk by lia. cbn [fst snd].
        unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
      + apply Forall_cons; [|apply Forall_nil]. unfold ranges_disjoint, O_sh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
        rewrite Hshb, soff_lit_small by lia. unfold vN8g. rewrite (soff_var rho1 106%positive (n8 / 8) E106) by (split; [lia | apply Z.div_lt_upper_bound; lia]). lia.
    - intros a Ha. destruct (Hpadm a ltac:(lia)) as [x Hx]. split; [|exists x; exact Hx].
      pose proof (rd_off_image (rm rho1) a x ltac:(unfold HIGH_SHADOW_END in *; lia) Hx) as M. unfold wok_of. rewrite M. reflexivity.
    - apply xwords_clear_nil. }
  clear H4.

  assert (H6 : SPA segs (J A Kc) (se_mg khi W st NVl VF) rho1 tp w).
  { unfold se_mg. change (mkA (with_facts (sd_mg W st NVl) (FACTSg khi W st VF)) []) with (ax_with_facts (mkAX (sd_mg W st NVl) [] base_sv) (FACTSg khi W st VF)).
    eapply SPA_refacts; [exact H5 | exact Fe |].
    intros Hold. unfold FACTSc.
    assert (HP : Forall (holds rho1) (unwind_factsS W st ++ pre_facts free_depth)).
    { apply Forall_forall. intros pp Hp. apply (proj1 (Forall_forall _ _) Hold). cbn [ss_facts ax_S sd_mg]. exact Hp. }
    assert (HD : holds rho1 (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))).
    { apply (proj1 (Forall_forall _ _) HP). apply in_or_app. right. unfold pre_facts, F_depth. cbn. tauto. }
    apply Forall_app in Hfacts as [HFg Hrest]. apply Forall_app in Hrest as [HFp Hrest]. apply Forall_app in Hrest as [HFc HFv].
    apply Forall_app; split; [|exact HFv]. apply Forall_app; split; [|exact HFc]. apply Forall_app; split; [apply Forall_app; split; [exact HP | exact HFg]|].
    assert (HFp' : holds rho1 (SPUle (SLit (atop_lo + 4096)) (SVar 10)) -> Forall (holds rho1) (F_pc khi)).
    { intros H0. clear -H0 HFp. destruct khi; (apply Forall_cons; [exact H0 | exact HFp]). }
    apply HFp'. clear HFp'.

    apply (proj2 (holds_ule rho1 _ _)). rewrite U_lit. cbn [eval]. change ((140735332483072 + 4096) mod M64v) with (140735332483072 + 4096).
    apply (proj1 (holds_bge rho1 _ _)) in HD. rewrite U_lit in HD. cbn [eval] in HD. change (Zsigned ((- free_depth) mod M64v)) with (-4096) in HD.
    unfold obj_range, obj_lo_of, stack_win in SW1. cbn [ob_base ob_lo fst] in SW1. unfold soff in SW1. cbn [eval] in SW1. rewrite bv_signed_U in SW1.
    unfold V_DEPTH in *. lia. }
  clear H5.

  pose proof (SPA_axforms segs (J A Kc) (XIg nW (length NVl)) rho1 (se_mg khi W st NVl VF) (PMID_g khi W st (map carve_obj NVl) VF) tp w AXI H6) as H7.

  exact (SPA_withG_intro segs (J A Kc) GW (PMID_g khi W st (map carve_obj NVl) VF) rho1 tp w H7).
Qed.
End INSTMG.
End F0A_minstG.

(* [comment removed for export] *)
Module InvQ5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qsize"; "fs_footb"; "AInvA"; "QG"; "q_foot"; "quarantine_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Corelib.Init.Datatypes"; "bool"; "false"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineCacheMax"; "kQuarantineMax"; "Sh"; "kQuarantineMin"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_q_global"; "aa_q_thread"; "ag_fsb"; "cs_allocated_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "q_mem"; "cls_of"; "q_pure"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "top_high"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "AInvQ"; "K0"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull SMGlue RebuildM SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma qrepr_of_split : ltac2:(tb__ "0|0|
S24S16S1eR1A1S1cR3R2A2S25R4S26S1SaZ48A2U8S14A3A2S0S7S19R4A1A1S11A2S0S7S18R5A1A1S12A2ScR7R6A2F_;F_;F_;F_;F_;FA;Fm;").
Proof.
  intros m A [QP QN] (QB & QL1 & QL2 & QH1 & QH2 & QMX) HMIN HB1 HB2. unfold quarantine_repr. fold (qall A).
  split; [|exact (conj QL1 (conj QL2 (conj QH1 (conj QH2 (conj QMX (conj HMIN (conj HB1 (conj HB2 QN))))))))].
  apply Forall_forall. intros b Hb.
  pose proof (proj1 (Forall_forall _ _) QP b Hb) as (P1 & P2 & (y & E & Y0 & YM & Y1) & P4).
  pose proof (proj1 (Forall_forall _ _) QB b Hb) as (M1 & M2 & M3 & M4 & M5).
  unfold batch_repr. split; [unfold HIGH_SHADOW_END, IMG_HI in *; lia|]. split; [exact M1|]. split; [exact M2|]. split; [exact P2|]. split; [exact M3|]. split; [exact M4|].
  split; [|exists y; exact (conj E (conj Y0 (conj YM Y1)))].
  intros i it Hi. destruct (M5 i it Hi) as [C IM]. split; [exact C|].
  pose proof (proj1 (Forall_forall _ _) P4 it (nth_error_In _ _ Hi)) as (I1 & I2 & I3 & I4).
  destruct IM as (X1 & X2 & X3 & X4 & X5 & X6 & X7). unfold q_item_ok. cbn zeta. unfold cls_of in I3.
  exact (conj I1 (conj I2 (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj I3 (conj I4 X7)))))))))).
Qed.

Section Back.
Variable A : AA.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HI3 : inv3 A.
Hypothesis HQP : q_pure A.
Hypothesis HAU : ltac2:(tb__ "0|1|
S3S4S0Z1R1A2S0R1Z1eA2A2S4S0Z0S1bS1dVA;R2A2A1M0A2S0G0S15A2A2F_;Fc;").
Variable mq : bview.
Hypothesis HSR : secondary_repr mq A.
Local Abbreviation Gq := (aa_geom A).
Local Abbreviation SBq := (ag_spacebeg (aa_geom A)).
Local Abbreviation Fq := (ag_fsb (aa_geom A)).

Lemma fs_out : ltac2:(tb__ "0|2|
S3S3S3S4S0R3R1A2S2R1R2A2A2S6S0R3S1aS17VA;A1M0A1M1A2S0S1G1Zb09000A2R4A2A2S6S0R4Z7fff7000A2S0Z10007fff8000R5A2A2S5SeS8G0R4A2SfA3F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hz OF OB. pose proof HI3 as (H3 & _).
  pose proof (geoQ2 A HG H3) as ((F1 & FT & FS & FB) & _). pose proof (geoQ A HG H3) as (_ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (geom_numsS _ HG) as (_ & _ & F2 & _).
  assert (B1 : 2147450880 <= Sh (Fq + FS_frames_off)).
  { unfold Sh, SHADOW_OFF. rewrite ?FS_frames_off_val. pose proof (Z.div_pos (Fq + FS_frames_off) 8) as D. rewrite ?FS_frames_off_val in D. lia. }
  pose proof (SpineMallocS4.Sh_lt_HSE (Fq + FS_total) ltac:(rewrite FS_total_val; clear -F2 TG; lia)) as B2. unfold HIGH_SHADOW_END in B2.
  apply fs_footb_false_intro; rewrite ?FS_total_val in *; unfold FS_kFlagsOffset; clear -Hz OF OB B1 B2; lia.
Qed.
Lemma fs_sh_out : ltac2:(tb__ "0|2|
S3S3S3S4S0S13R3A1R1A2S2R1S13R2A1A2A2S0Z0R4A2S0R4Z7fffff800000A2S6S0R5S1aS17VA;A1M0A1M1A2S0S1G1Zb09000A2R6A2A2S5SeS8G0R5A2SfA3F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hz L0 HT OF. pose proof HI3 as (H3 & _).
  pose proof (geoQ2 A HG H3) as ((F1 & FT & FS & FB) & _).
  assert (B1 : 2147450880 <= Sh lo) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos lo 8 L0 ltac:(lia)); lia).
  assert (B2 : Sh hi <= 17594332446720).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_le_mono hi 140737479966720 8 ltac:(lia) HT) as M. change (140737479966720 / 8) with 17592184995840 in M. lia. }
  assert (M3 : z < Sh (Fq + FS_frames_off) \/ Sh (Fq + FS_total) <= z).
  { rewrite FS_total_val. destruct OF as [O|O].
    - left. pose proof (Geometry.Sh_mono hi Fq O). pose proof (Geometry.Sh_mono Fq (Fq + FS_frames_off) ltac:(rewrite ?FS_frames_off_val; lia)). lia.
    - right. pose proof (Geometry.Sh_mono (Fq + 11571200) lo O). lia. }
  apply fs_footb_false_intro; [| | exact M3]; rewrite ?FS_total_val; unfold FS_kFlagsOffset; clear -Hz FB B1 B2; lia.
Qed.

Lemma QF_fs : ltac2:(tb__ "0|0|
S3SbVA;R1A2S5SeS8S17VA;A1R2A2SfA3F_;Fz;").
Proof.
  intros z Hz. pose proof HI3 as (H3 & _ & SEC3 & _). pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  unfold q_foot in Hz. fold (qall A) in Hz. apply Exists_exists in Hz as (b & Hb & Hz).
  assert (PRIM : qzone A z -> fs_footb Gq z = false).
  { intros QZ. exact (QT_fs A HG H3 HQP HAU z (or_introl (or_introl QZ))). }
  destruct Hz as [Hz|Hz].
  - apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | left; exact Hz].
  - apply Exists_exists in Hz as (it & Hit & Hz). destruct (is_primary (snd it)) eqn:EP.
    + apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | right]. apply Exists_exists. exists it. split; [exact Hit|]. split; [exact EP | exact Hz].
    + destruct HQP as [QP _]. pose proof (proj1 (Forall_forall _ _) QP b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
      destruct (IP4 EP) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [i Hi].
      destruct HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      destruct (SEC3 i ch Hi) as (_ & _ & _ & X4 & _). rewrite FS_total_val in X4.
      destruct D10 as (E1 & E2 & E3 & E4 & E5). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in E5.
      pose proof (rz_sec (snd it) IP2 EP) as RZ. pose proof (round_up_ge8 (snd it)) as R8. unfold PG in *.
      destruct Hz as [Hz|Hz].
      * apply (fs_out (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); [clear -Hz RZ Eu Esz D8 R8 IP2; lia | exact X4 | exact E5].
      * apply (fs_sh_out (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); [| clear -E1; lia | clear -E3 TG; lia | exact X4].
        assert (B8 : fst it mod 8 = 0).
        { destruct (proj1 (Z.mod_divide (sc_map_beg ch) 4096 ltac:(lia)) D6) as [k0 Hk0]. apply Z.mod_divide; [lia|]. exists (k0 * 512 + 768). lia. }
        pose proof (Sh_SB (fst it) (8 * ((snd it + 7) / 8)) B8) as E8. rewrite (Z.mul_comm 8), Z.div_mul in E8 by lia.
        pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)) as MB.
        pose proof (Geometry.Sh_mono (sc_map_beg ch) (fst it) ltac:(clear -Eu; lia)) as M1.
        pose proof (Geometry.Sh_mono (fst it + (snd it + 7) / 8 * 8) (sc_map_beg ch + sc_map_size ch) ltac:(clear -Eu Esz D8 R8 DM MB; lia)) as M2.
        clear -Hz E8 M1 M2. lia.
Qed.
End Back.

Theorem AInvQ_back : ltac2:(tb__ "0|0|
S16S22S10S27Q40A1A1S1fS2bR4R3R2R1A4S1cS23SdS21R4A1A2R5A2S0S7S19R6A1A1S11A2S0S7S18R7A1A1S12A2S9SdR8R7R6R5A5F_;F_;F_;F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB) HQM HB1 HB2. cbn zeta in *.
  destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
  set (m := view segsA (rm rho)) in *.
  assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A c) <= kUserSpaceSize).
  { intros c Hc. destruct R3 as (_ & _ & _ & P4). pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold cls_of, kUserMapSize in *. lia. }
  assert (HMINp : cell_ok m (mkACell (QG + 72) 8 kQuarantineMin)).
  { apply (cell_tr A m); [|exact R5m]. cbn [c_addr c_w]. intros k Hk. apply (MI A m HG). unfold QG. lia. }
  pose proof (qrepr_of_split m A R5 HQM HMINp HB1 HB2) as QR.
  unfold AInvA. cbn zeta. fold m.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [|exact (conj HM (conj HI3 HB))].
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [|exact (conj R6 (conj R7 (conj R8 R9)))].
  apply (quarantine_repr_agree_gen m (maskv (fs_footb (aa_geom A)) m) A A eq_refl eq_refl eq_refl eq_refl); [| | | exact R1 | | | | | exact QR].
  - intros c. reflexivity.
  - intros c. reflexivity.
  - intros c x H. exact H.
  - apply Forall_forall. intros qb _. apply Forall_forall. intros it _. pose proof (rz_bound (snd it)). lia.
  - intros z Hz. apply maskv_out. exact (QF_fs A HG HI3 R5 HAU _ R4 z Hz).
  - intros z Hz. apply maskv_out. apply fs_footb_T; [exact HG | lia].
  - intros z Hz. apply maskv_out. apply fs_footb_img; [exact HG | unfold QG in Hz; lia].
Qed.

Theorem K0_back : ltac2:(tb__ "0|0|
S28S16S22S10S27Q40A1A1S10S20A1S1fS2cR6R5R4R3R2R1A6S1cS23SdS21R5A1A2R6A2S0S7S19R7A1A1S11A2S0S7S18R8A1A1S12A2S4S9SdR9R8R7R5A5S4RaR6R5A2S4S2aR9R8A2S29R9R8A2A2A2A2F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho;FA;FKc;").
Proof.
  intros Kc A rho tp tr md (HA & HK & Htp & Htop & _) HQM HB1 HB2.
  exact (conj (AInvQ_back A rho tp md HA HQM HB1 HB2) (conj HK (conj Htp Htop))).
Qed.
End InvQ5.

(* [comment removed for export] *)
Module InvQ6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Datatypes"; "list"; "option"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "AInvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull SMGlue RebuildM SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem AInvQ_frame_top : ltac2:(tb__ "0|0|
SfS1S1S6S5Q40A1A1SbSdR5R4R2R1A4S9S12R1S11S10R7A1A1A2S8S7S5Q8A1A1S4S3S0R6A1R2A3S4S3S0R7A1R2A3A3F_;Fz;SdR7R5R4R3A4F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp md HX AV. unfold AInvQ in HX |- *. cbn zeta in HX |- *.
  set (G := aa_geom A) in *. set (m := view segsA (rm rho)) in *. set (m' := view segsA (rm rho')) in *.
  destruct HX as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
  pose proof (geom_old _ HG) as (_ & F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & _ & S1 & S2 & _). fold G in F1, F2, T1, T2, C1, C2, D1, D2, S1, S2.
  pose proof (topG_range G) as TG.
  assert (HPAB : dyn_ok (topG G) (ag_pab G) kPtrArrayReserve) by (destruct R4 as (_ & _ & _ & _ & S4 & _); exact S4).

  set (mk := maskv (fs_footb G) m) in *. set (mk' := maskv (fs_footb G) m').
  assert (MK : forall z, m' z = m z -> mk' z = mk z) by (intros z E; unfold mk, mk', maskv; rewrite E; reflexivity).
  assert (Zimg : forall z, IMG_LO <= z < IMG_HI -> ~ dstatw z -> m' z = m z) by (intros z Hz _; apply AV; unfold IMG_HI in Hz; clear -Hz TG; lia).
  assert (Zimg' : forall z, IMG_LO <= z < IMG_HI -> m' z = m z) by (intros z Hz; apply AV; unfold IMG_HI in Hz; clear -Hz TG; lia).
  assert (Zsp : forall z, ag_spacebeg G <= z < ag_spacebeg G + kSpaceSize + 4096 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz S2; lia).
  assert (Zth : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz T2; lia).
  assert (Zctx : forall z, ag_ctx G <= z < ag_ctx G + 0x1000 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz C2; lia).
  assert (Zdtls : forall z, ag_dtls G <= z < ag_dtls G + 0x1000 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz D2; lia).
  assert (Zfs : forall z, ag_fsb G <= z < ag_fsb G + FS_total -> m' z = m z) by (intros z Hz; apply AV; clear -Hz F2; lia).
  assert (Zpab : forall z, ag_pab G <= z < ag_pab G + kPtrArrayReserve -> m' z = m z).
  { intros z Hz. apply AV. destruct HPAB as [_ (_ & _ & P3 & _)]. clear -Hz P3. lia. }
  assert (Zsec : forall ch z, In ch (aa_sec A) -> sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch -> m' z = m z).
  { intros ch z Hch Hz. apply AV. destruct (In_nth_error _ _ Hch) as [i Hi]. destruct R4 as [S1' _].
    destruct (S1' i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D12 & _). fold G in D12. clear -Hz D12. lia. }
  assert (Zband : forall z, SHADOW_BAND_LO <= z < SHADOW_BAND_HI -> m' z = m z).
  { intros z Hz. apply AV. unfold SHADOW_BAND_HI, HIGH_SHADOW_END in Hz. clear -Hz TG. lia. }
  split; [exact HG|].
  split.
  { eapply (rtc_inv_z G m m'); first [ eassumption | intros; first [ apply Zimg; assumption | apply Zth; assumption | apply Zctx; assumption | apply Zdtls; assumption | apply Zfs; assumption ] ]. }
  split.
  { replace (restrictv (fs_footb G) m') with (restrictv (fs_footb G) m); [exact HF|].
    apply functional_extensionality. intros z. unfold restrictv. destruct (fs_footb G z) eqn:E; [|reflexivity].
    symmetry. apply AV. unfold fs_footb in E. cbn zeta in E.
    pose proof (SpineMallocS4.Sh_lt_HSE (ag_fsb G + FS_total) ltac:(clear -F2 TG; lia)) as SL. unfold HIGH_SHADOW_END in SL.
    apply orb_prop in E as [E|E]; [apply orb_prop in E as [E|E]|]; apply andb_prop in E as [_ E]; apply Z.ltb_lt in E; rewrite ?FS_total_val in *; clear -E F2 SL TG; lia. }
  split; [|split; [exact HM | split; [exact HI3 | eapply bandtp_agree; [exact Zband | exact HB]]]].
  split; [exact R1|].
  Ltac zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband :=
    first [ eassumption | reflexivity
          | intros; apply MK; first [ apply Zsp; assumption | apply Zth; assumption | apply Zctx; assumption | apply Zdtls; assumption
                                    | apply Zfs; assumption | apply Zpab; assumption | apply Zband; assumption
                                    | eapply Zsec; eassumption | apply Zimg; assumption ] ].
  split; [eapply (live_block_repr_z G (aa_sec A) mk mk'); zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (primary_repr_z G mk mk'); zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (secondary_repr_z G (aa_sec A) mk mk'); zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split.
  { split; [exact R5|]. eapply cell_ok_agree; [|exact R5m]. cbn [c_addr c_w]. intros k Hk. apply MK. apply Zimg'. unfold QG, IMG_LO, IMG_HI. clear -Hk. lia. }
  split.
  { destruct HI3 as (_ & _ & _ & _ & DEP3 & _). unfold depot_wf in *. eapply depot_mem_frame; [|exact R6]. intros a Ha. apply MK.
    destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
    - apply Zimg'. exact (dstat_img a Hs).
    - apply AV. destruct (DEP3 (bb, NBSZ)) as ((_ & _ & W3 & _) & _); [unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb]|].
      cbn [fst snd] in W3. fold G in W3. clear -Hab W3. lia.
    - apply AV. destruct (DEP3 (bb, FBSZ)) as ((_ & _ & W3 & _) & _); [unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb]|].
      cbn [fst snd] in W3. fold G in W3. clear -Hab W3. lia. }
  split; [eapply (ia_inv_z mk mk'); zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (thread_inv_z G mk mk'); zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  eapply (misc_inv_z mk mk'); zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband.
Qed.

Theorem K0_frame_top : ltac2:(tb__ "0|1|
S13SfS1S1S6S5Q40A1M0A1S6ScA1SbSaS8G0S2R5R1A2S2R6R1A2A3Fi;S9S12R1S11S10R8A1A1A2S8S7S5Q8A1A1S4S3S0R7A1R2A3S4S3S0R8A1R2A3A3F_;Fz;SeR9R8R7R5R4R3A6SeRaR9R7R6R5R4A6F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FA;FKc;").
Proof.
  intros Kc A rho rho' tp tr md Hw AV (HA & HK & Htp & Htop & HRG).
  split; [exact (AInvQ_frame_top A rho rho' tp md HA AV)|]. split; [exact HK|]. split; [|split].
  - unfold tp_ok in *. rewrite (Hw 24%positive). exact Htp.
  - unfold top_high in *. rewrite (Hw 10%positive), (Hw V_DEPTH). exact Htop.
  - destruct HRG as (E1 & E2 & E3 & E4). unfold rigidQ. rewrite !Hw. exact (conj E1 (conj E2 (conj E3 E4))).
Qed.
End InvQ6.

(* [comment removed for export] *)
Module RebuildRP.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "mul"; "div"; "pow"; "sub"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "AA"; "aa_cls"; "class_state"; "cs_empty"; "sec_chunk"; "cs_allocated_user"; "aa_live"; "aa_sec"; "aa_q_global"; "aa_q_thread"; "ag_spacebeg"; "ag_thread"; "ageom"; "qbatch"; "sc_map_beg"; "sc_map_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "nthZ"; "q_foot"; "QG"; "class_repr"; "live_ids"; "quarantine_repr"; "geom_ok"; "live_block_repr"; "slot_zone"; "@Stdlib.Lists.List"; "In"; "NoDup"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "Sh"; "kUserSpaceSize"; "rz"; "@Corelib.Init.Datatypes"; "list"; "option"; "app"; "nat"; "pair"; "Some"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "q_ids"; "qall"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3"; "qslot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "czone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "cls_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "q_pure"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws RefillModel RebuildRZ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma NoDup_app_in : ltac2:(tb__ "0|1|
S31S0A1M0G0S0S2aS0S33S0R3R2A3A2S29S0R2R4A3S29S0R3R4A3SeF_;F_;F_;Fx;Fl2;Fl1;").
Proof.
  induction l1 as [|a l1 IH]; intros l2 x ND H1 H2; [destruct H1|]. cbn [app] in ND. inversion ND as [|? ? Ha ND']; subst.
  destruct H1 as [->|H1]; [apply Ha; apply in_or_app; right; exact H2 | exact (IH l2 x ND' H1 H2)].
Qed.

Lemma id16_of : ltac2:(tb__ "0|2|
S0S0S3Z0M0R1A2SaS0S4R2Z10M1A2G0A3SaS0S4R4R3A2G0A3SaS0S5G1S6R5G1A2A2R5A3F_;F_;F_;FS;Fo;").
Proof.
  intros o S HS H16 HoS.
  destruct (proj1 (Z.mod_divide o S ltac:(lia)) HoS) as [q Hq]. destruct (proj1 (Z.mod_divide S 16 ltac:(lia)) H16) as [r Hr].
  subst o. rewrite Hr. replace (q * (r * 16)) with (q * r * 16) by ring. rewrite Z.div_mul by lia. ring.
Qed.

Lemma valid_of_off : ltac2:(tb__ "0|4|
S0S0S0S3Z0M0R2A2SaS0S4R3Z10M1A2G0A3S1G0R5A2SaS0S4R6R5A2G0A3S1S2R7R6A2R5A2S9S1G0S6R8G1A2M2A2S9SaS0S4S5G1G2A2M3R7A2G0A3S1S2G3R7A2R6A2A2A2F_;F_;F_;F_;F_;Fau;FS;Fo;").
Proof.
  intros o S au HS H16 Ho HoS Hau. rewrite (id16_of o S HS H16 HoS). split; [apply Z.div_pos; lia|]. split; [exact HoS | exact Hau].
Qed.

Lemma live_ids_valid : ltac2:(tb__ "0|3|
S2cS10S0S0S9S1Z1R2A2S1R2Z1eA2A2S23R5SfR4A1R4R3S20S12S11R4A1R3S13A4A5S29S0R3S24SfR5A1R5R4A3A3S9S1Z0M0R4A2S9SaS0S4S5Z10R4A2M1S2dR5A1M2A2G0A3S1S2G1G2A2S15S20S12S11R6A1R5S13A4A1A2A2A2F_;F_;F_;Fx;Fc;FA;Fm;").
Proof.
  intros m A c x Hc P4 Hx. destruct (Size_facts c Hc) as (SZ & SM).
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
  unfold live_ids in Hx. apply in_map_iff in Hx as ([b n] & <- & Hin).

  apply (proj2 (list_elem_of_In _ _)) in Hin. apply (proj1 (list_basics.list.list_elem_of_filter _ _ _)) in Hin as [Hf Hin].
  apply (proj1 (list_elem_of_In _ _)) in Hin. cbn [fst snd] in *.
  destruct (is_primary n) eqn:Hp; [|cbn in Hf; destruct Hf].
  destruct (Z.eqb_spec (ClassID (needed n)) c) as [Hcl|Hcl]; [|cbn in Hf; destruct Hf].
  destruct (LV b n Hin Hp Hcl) as (V1 & V2 & V3).
  apply valid_of_off; [lia | exact SM | lia | exact V2 | exact V3].
Qed.

Lemma q_ids_valid : ltac2:(tb__ "0|3|
S10S0S0S9S1Z1R2A2S1R2Z1eA2A2S3fR4A1S29S0R3S38SfR5A1S39R5A1R4A3A3S9S1Z0M0R4A2S9SaS0S4S5Z10R4A2M1S2dR5A1M2A2G0A3S1S2G1G2A2S15S20S12S11R6A1R5S13A4A1A2A2A2F_;F_;F_;Fx;Fc;FA;").
Proof.
  intros A c x Hc [HBP _] Hx. destruct (Size_facts c Hc) as (SZ & SM).
  unfold q_ids in Hx. apply in_app_or in Hx as [Hx|Hx].
  - apply in_map_iff in Hx as (it & <- & Hin). apply filter_In in Hin as [Hin Hf]. apply andb_prop in Hf as [Hp Hcl]. apply Z.eqb_eq in Hcl.
    unfold qitems in Hin. apply in_flat_map in Hin as (b & Hb & Hit).
    pose proof (proj1 (Forall_forall _ _) HBP b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (_ & _ & I3 & _).
    specialize (I3 Hp). cbv zeta in I3. unfold it_cls in Hcl. rewrite Hcl in I3. destruct I3 as (I3a & I3b & I3c).
    unfold it_id, it_ab, it_cls, ptr_to_compact, kCompactPtrScale. rewrite Hcl. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
    unfold SegQ_wf2.cls_of in I3c.
    apply valid_of_off; [lia | exact SM | lia | exact I3b | exact I3c].
  - destruct (Z.eqb_spec c 24) as [->|Hne]; [|destruct Hx].
    apply in_map_iff in Hx as (b & <- & Hb).
    pose proof (proj1 (Forall_forall _ _) HBP b Hb) as (_ & _ & (y & E & Y0 & YM & Y1) & _).
    unfold qb_id, ptr_to_compact, kCompactPtrScale. rewrite E. replace (region_beg (ag_spacebeg (aa_geom A)) 24 + 16 * y - region_beg (ag_spacebeg (aa_geom A)) 24) with (y * 2 ^ 4) by lia.
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
    unfold SegQ_wf2.cls_of, kQuarantineBatchSize in Y1. change (Size 24) with 8192.
    split; [exact Y0|]. split; [|exact Y1].
    destruct (proj1 (Z.mod_divide y 512 ltac:(lia)) YM) as [k Hk]. subst y. replace (16 * (k * 512)) with (k * 8192) by lia. apply Z_mod_mult.
Qed.

Lemma entry_cls_pure : ltac2:(tb__ "0|1|
S2cS10S0S9S1Z1R1A2S1R1Z1eA2A2S26SfR3A1A1S23R5SfR4A1R4R3S20S12S11R4A1R3S13A4A5S25R6R5A2S3dR5S20S12S11R6A1R5S13A4S33S0S24SfR6A1M0R6R5A3S38G0S39R6A1R5A3A3A3F_;F_;F_;F_;Fc;FA;Fm;").
Proof.
  intros m A c Hc HG P4 HQ. pose proof (fun x => live_ids_valid m A c x Hc P4) as LVV. pose proof (q_ids_valid A c) as QVV.
  destruct (quarantine_repr_pure m A HG HQ) as [HQP _].
  set (cs := nthZ (aa_cls A) c cs_empty) in *. unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & N7 & _ & _ & _ & ND & _ & _ & _ & TI10 & CV10 & MC10 & FC10).
  unfold cls_pure. split; [exact N1|]. split; [exact N2|]. split; [exact N4|]. split; [exact N5|].
  split; [pose proof (Zle_0_nat (length (cs_free_array cs))); lia|]. split; [lia|].
  split.
  { intros x Hx. rewrite app_assoc in Hx. apply in_app_or in Hx as [Hx|Hx].
    - destruct (N7 x Hx) as (X1 & X2 & X3). unfold kCompactPtrScale in X2, X3. rewrite Z.shiftl_mul_pow2 in X2, X3 by lia. change (2 ^ 4) with 16 in X2, X3.
      replace (16 * x) with (x * 16) by lia. split; [exact X1|]. split; [exact X2 | exact X3].
    - apply in_app_or in Hx as [Hx|Hx]; [exact (LVV x Hx) | exact (QVV x Hc HQP Hx)]. }
  split; [exact (proj1 (NoDup_ListNoDup _) ND)|]. split; [exact TI10|].
  split; [unfold slots in CV10; rewrite CV10, length_app; f_equal; lia|].
  exact (conj MC10 FC10).
Qed.

Lemma live_block_repr_agree : ltac2:(tb__ "0|4|
S2cS2cS10S10SaS31S37S0S0A2M0A1S16R1A1S16R2A1A3S0S0S0S29G0S35S0S0R3R2A4S16R6A1M1A3ScS9S1S8R4S30R3A1A2R2A2S3R2S2R4R3A2A2A2S9S1S2eR4A1M2R2A2S3R2S2G2S6S2R3Z7A2Z8A2A2A2A2A2SaS32S3aQ8A1A1R9R3A1RaR3A1A3F_;F_;Fz;Fn;Fb;S0S0S29G0S35S0S0R2R1A4G1A3S1Z1R2A2F_;Fn;Fb;S27R7R5A2M3G3F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EL AG HN HL b n Hin. rewrite EL in Hin. destruct (HL b n Hin) as (B1 & B2 & B3 & [B4 B5] & B6 & B7).
  pose proof (HN b n Hin) as Hn1. pose proof (rz_bound n) as RZ.
  assert (AGb : forall z, b - rz n <= z < b + n -> m' z = m z) by (intros z Hz; apply (AG b n z Hin); left; exact Hz).
  assert (AGs : forall z, Sh b <= z < Sh b + (n + 7) / 8 -> m' z = m z) by (intros z Hz; apply (AG b n z Hin); right; exact Hz).
  split; [rewrite AGb by lia; exact B1|].
  split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply AGb; lia|].
  split; [eapply cell_ok_agree; [|exact B3]; cbn [c_addr c_w]; intros k Hk; apply AGb; lia|].
  split; [split|split].
  - intros g Hg. rewrite AGs by lia. exact (B4 g Hg).
  - intros Hm. rewrite AGs by lia. exact (B5 Hm).
  - apply (alloc_magic_ok_agree m m' b n); [|lia|exact B6]. intros z Hz. apply AGb. lia.
  - destruct B7 as (t & Ht & Hm4). exists t. split; [|exact Hm4]. rewrite AGb by lia. exact Ht.
Qed.

Lemma quarantine_repr_agreeR : ltac2:(tb__ "0|6|
S2cS2cS10S10SaS1cSfR1A1SfR2A1A3SaS31S14A1S17R2A1S17R3A1A3SaS31S1dA1M0S19R3A1S19R4A1A3SaG0S18R4A1S18R5A1A3S0S1S15S20S12S11R7A1R1S13A4A1S15S20S12S11R6A1R1S13A4A1A2Fc;S0S21R8R1A2SaS32S3aQ8A1A1M1RaR2A1RbR2A1M2A3F_;Fz;S0S9S1S2S1bSfR9A1A1M3Z50A2R1A2S3R1S2G3Z70A2A2A2SaG1G2RcR2A1M4A3F_;Fz;S0S9S1S2S22Z40A2R1A2S3R1S2S22Zc0A2A2A2SaG1G4RdR2A1A3F_;Fz;S25RcRaA2M5G5F_;F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EG ES ET EGq EAU AG AGT AGI (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  unfold quarantine_repr. rewrite EG, ET, EGq.
  assert (FQ : forall qb z, In qb (aa_q_thread A ++ aa_q_global A) ->
            (qb_addr qb <= z < qb_addr qb + kQuarantineBatchSize)
            \/ Exists (fun it : Z * Z => (fst it - rz (snd it) <= z < fst it) \/ (Sh (fst it) <= z < Sh (fst it) + (snd it + 7) / 8)) (qb_items qb) -> m' z = m z).
  { intros qb z Hqb Hz. apply AG. unfold q_foot. apply Exists_exists. exists qb. split; [exact Hqb | exact Hz]. }
  split.
  { apply Forall_forall. intros qb Hqb. pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
    unfold batch_repr. rewrite EG. unfold kQuarantineBatchSize in *.
    split; [exact B0|]. split; [eapply cell_ok_agree; [|exact B1]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
    split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
    split; [exact B3|]. split; [exact B4|].
    split; [eapply present_agree; [|exact B5]; intros z Hz; apply (FQ qb); [exact Hqb | left; lia]|].
    split.
    - intros i it Hi. destruct (B6 i it Hi) as [I1 I2]. pose proof (nth_error_Some_lt _ _ _ Hi) as L. pose proof (nth_error_In _ _ Hi) as Hin.
      unfold kQuarantineBatchCount in B3.
      split; [eapply cell_ok_agree; [|exact I1]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
      pose proof (rz_bound (snd it)) as RZi.
      unfold q_item_ok in I2 |- *. cbn zeta in I2 |- *. rewrite EG, ES.
      destruct I2 as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11).
      assert (AGi : forall z, fst it - rz (snd it) <= z < fst it -> m' z = m z).
      { intros z Hz. apply (FQ qb); [exact Hqb|]. right. apply Exists_exists. exists it. split; [exact Hin | left; exact Hz]. }
      split; [exact J1|]. split; [exact J2|].
      split; [rewrite AGi by lia; exact J3|].
      split; [eapply present_agree; [|exact J4]; intros z Hz; apply AGi; lia|].
      split; [eapply cell_ok_agree; [|exact J5]; cbn [c_addr c_w]; intros k Hk; apply AGi; lia|].
      split; [eapply cell_ok_agree; [|exact J6]; cbn [c_addr c_w]; intros k Hk; apply AGi; lia|].
      split; [eapply present_agree; [|exact J7]; intros z Hz; apply AGi; lia|].
      split; [apply (alloc_magic_ok_agree m m'); [exact AGi | lia | exact J8]|].
      split; [intros Hp; destruct (J9 Hp) as (K1 & K2 & K3); split; [exact K1|]; split; [exact K2|]; pose proof (EAU (ClassID (needed (snd it)))); lia|].
      split; [exact J10|].
      assert (0 <= (snd it + 7) / 8) by (apply Z.div_pos; lia).
      eapply present_agree; [|exact J11]. intros z Hz. apply (FQ qb); [exact Hqb|]. right. apply Exists_exists. exists it. split; [exact Hin | right; lia].
    - destruct B7 as (x & E1 & E2 & E3 & E4). exists x. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. pose proof (EAU 24). lia. }
  assert (HB : forall b z, In b (aa_q_thread A ++ aa_q_global A) -> qb_addr b <= z < qb_addr b + 8 -> m' z = m z).
  { intros b z Hb Hz. apply (FQ b); [exact Hb | left; unfold kQuarantineBatchSize; lia]. }
  split; [apply (qlinks_agree m m'); [intros b z Hb Hz; apply (HB b); [apply in_or_app; left; exact Hb | exact Hz] | exact Q2]|].
  split; [apply (qlinks_agree m m'); [intros b z Hb Hz; apply (HB b); [apply in_or_app; right; exact Hb | exact Hz] | exact Q3]|].
  split; [apply (qhdr_repr_agree m m'); [intros z Hz; apply AGT; lia | exact Q4]|].
  split; [apply (qhdr_repr_agree m m'); [intros z Hz; apply AGI; unfold QG in *; lia | exact Q5]|].
  split; [eapply cell_ok_agree; [|exact Q6]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold QG; lia|].
  split; [eapply cell_ok_agree; [|exact Q7]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold QG; lia|].
  split; [exact Q8 | exact Q9].
Qed.

Section QSlot.
Variables (A : AA) (mq : bview).
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HI3 : inv3 A.
Hypothesis HQP : q_pure A.
Hypothesis HSR : secondary_repr mq A.
Hypothesis HAU : ltac2:(tb__ "0|1|
S0S9S1Z1R1A2S1R1Z1eA2A2S9S1Z0S15S3eVA;R2A2A1M0A2S1G0S2fA2A2F_;Fc;").

Lemma qfoot_cases : ltac2:(tb__ "0|2|
S0S21VA;R1A2ScSbS0S0SbS0S0S9S3bVA;R2R1A3S3cS1aSfVA;A1A1R2R1S2dR2A1R4A5A2Lo';A2Lc';A2SbS34S34SbS14S14S9SaS32S14A1S2bS14S17VA;A1R2A3S36S14R1A2A3ScS9S1S1eR1A1M0R4A2S3R4S2G0S1fR1A1A2M1A2A2S9S1S2eG0A1R4A2S3R4S2eG1A1A2A2A2A2Lch;A2Li;A2A2F_;Fz;").
Proof.
  intros z Hz. pose proof HI3 as (H3 & _).
  unfold q_foot in Hz. fold (qall A) in Hz.
  apply Exists_exists in Hz as (b & Hb & Hz).
  assert (PRIM : qzone A z -> exists c' o', qslot A c' o' /\ czone (ag_spacebeg (aa_geom A)) c' o' (Size c') z).
  { intros QZ. exact (qzone_czone A HG H3 HQP HAU z QZ). }
  destruct Hz as [Hz|Hz].
  - left. apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | left; exact Hz].
  - apply Exists_exists in Hz as (it & Hit & Hz). destruct (is_primary (snd it)) eqn:EP.
    + left. apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | right]. apply Exists_exists. exists it. split; [exact Hit|]. split; [exact EP | exact Hz].
    + right. destruct HQP as [HQ1 _]. pose proof (proj1 (Forall_forall _ _) HQ1 b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
      destruct (IP4 EP) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [i Hi]. exists i, ch. split; [exact Hi|].
      destruct HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      pose proof (rz_sec (snd it) IP2 EP) as RZ. pose proof (round_up_ge8 (snd it)) as R8. unfold PG in *.
      destruct Hz as [Hz|Hz]; [left; clear -Hz RZ Eu Esz D8 R8 IP2; lia | right].
      assert (B8 : fst it mod 8 = 0).
      { destruct (proj1 (Z.mod_divide (sc_map_beg ch) 4096 ltac:(lia)) D6) as [k0 Hk0]. apply Z.mod_divide; [lia|]. exists (k0 * 512 + 768). lia. }
      pose proof (Sh_SB (fst it) (8 * ((snd it + 7) / 8)) B8) as E8. rewrite (Z.mul_comm 8), Z.div_mul in E8 by lia.
      pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)) as MB.
      pose proof (Geometry.Sh_mono (sc_map_beg ch) (fst it) ltac:(clear -Eu; lia)) as M1.
      pose proof (Geometry.Sh_mono (fst it + (snd it + 7) / 8 * 8) (sc_map_beg ch + sc_map_size ch) ltac:(clear -Eu Esz D8 R8 DM MB; lia)) as M2.
      clear -Hz E8 M1 M2. lia.
Qed.

Lemma qfoot_slot_out : ltac2:(tb__ "0|4|
S0S0S0S9S1Z1R3A2S1R3Z1eA2A2S1Z0M0R3A2SaS0S4S5Z10M1R4A2S2dR5A1A2G0A3S1S2S5G1R5A2S2dR6A1A2S8S7Z2M2Z20A2S7G2Z1dA2A2A2SdS29S0R6S38SfVA;A1M3S39VA;A1R7A3A3A1S21VA;R6A2SdS28G3R9R8R7A4A1F_;F_;F_;F_;F_;F_;Fz;Fx;Fc;").
Proof.
  intros c x z Hc X0 XM XE NX Hz HS. pose proof HI3 as (H3 & _ & SEC3 & _).
  pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  apply (slot_czone A c x z) in HS.
  destruct (qfoot_cases z Hz) as [(c' & o' & (C1' & O0' & OM' & OE' & IDin') & CZ')|(i & ch & Hi & Hr)].
  - apply (czone_slots_disj (ag_spacebeg (aa_geom A)) c (16 * x) c' o' z S1 ltac:(clear -S2 TG; lia) S8 Hc C1' ltac:(clear -X0; lia) O0' XM OM' XE OE'); [|exact HS|exact CZ'].
    destruct (Z.eq_dec c c') as [EC|NC]; [right | left; exact NC]. subst c'. intros EO. apply NX.
    rewrite <- EO in IDin'. replace (16 * x / 16) with x in IDin' by (rewrite Z.mul_comm, Z.div_mul; lia). exact IDin'.
  - destruct HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
    destruct (SEC3 i ch Hi) as (X1 & _). rewrite kSpaceSize_val in X1.
    destruct D10 as (E1 & E2 & E3 & E4 & E5). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in E5.
    destruct Hr as [Hr|Hr].
    + apply (czone_out A HG H3 c (16 * x) (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z Hc ltac:(clear -X0; lia) XM XE);
        [exact Hr | clear -X1; lia | exact E5 | exact HS].
    + apply (czone_sh_out A HG H3 c (16 * x) (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z Hc ltac:(clear -X0; lia) XM XE);
        [exact Hr | clear -E1; lia | clear -E3 TG; lia | clear -X1; lia | exact HS].
Qed.
End QSlot.
End RebuildRP.

(* [comment removed for export] *)
Module InvQ4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "aa_geom"; "cs_cache"; "cs_allocated_user"; "AA"; "ageom"; "class_state"; "aa_cache_inited"; "cs_mapped_free_array"; "qb_items"; "ag_thread"; "cs_mapped_user"; "mkQB"; "cs_free_array"; "aa_cls"; "aa_live"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "is_large"; "qb_addr"; "ag_spacebeg"; "list_upd"; "sec_chunk"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "mul"; "eqb"; "modulo"; "shiftl"; "to_nat"; "@Corelib.Init.Datatypes"; "app"; "list"; "nil"; "length"; "cons"; "bool"; "prod"; "option"; "true"; "None"; "snd"; "nat"; "Some"; "andb"; "false"; "fst"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "cell_ok"; "mkACell"; "maskv"; "bview"; "acell"; "c_addr"; "c_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "set_q"; "push_cache"; "QW"; "pc_entry"; "push_zone"; "batch_pure"; "push_cs"; "KQ_laws"; "q_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "rw"; "rl"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "q_ids"; "qall"; "qitems"; "it_cls"; "it_id"; "qb_id"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@Stdlib.Lists.List"; "In"; "filter"; "nth_error"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "is_primary"; "Size"; "max_count"; "kCompactPtrScale"; "free_array"; "kUserSpaceSize"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "fs_footb"; "class_repr"; "live_ids"; "q_foot"; "geom_ok"; "inv3"; "live_sep"; "model_inv"; "primary_repr"; "qlarge"; "secondary_repr"; "slot_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "prim_credit"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4"; "cls_metaRF"; "@stdpp.base"; "NoDup"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull SMGlue RebuildM SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma perm_push : ltac2:(tb__ "0|1|
S29S0A1M0G0G0G0S0S5bS0S28S0R5S28S0S28S0R4S2cS0R1S2aS0A1A3A3S28S0R3R2A3A3A3S28S0R5S28S0R4S28S0R3S2cS0R1R2A3A3A3A3A3Fx;FB;FL;FC;FF;").
Proof.
  intros F C L B x. apply Permutation_app_head. rewrite <- app_assoc. apply Permutation_app_head. cbn [app]. apply Permutation_middle.
Qed.

Lemma qitems_mid : ltac2:(tb__ "0|2|
S29S7A1M0S7G0S2S29S2eS0S0A2M1A1S52S28S7R3S2cS7R2R1A3A3A1S28G1S52R3A1S28G1S10R2A1S52R1A1A3A3A3Fg2;Fb;Fg1;").
Proof. intros. unfold qitems. rewrite flat_map_app. reflexivity. Qed.

Lemma filter_map_mid : forall {X Y} (f : X -> Y) (P : X -> bool) (l1 : list X) (x : X) (l2 l3 : list X),
  Permutation (map f (List.filter P (l1 ++ (x :: l2) ++ l3))) ((if P x then [f x] else []) ++ map f (List.filter P (l1 ++ l2 ++ l3))).
Proof.
  intros X Y f P l1 x l2 l3. rewrite !List.filter_app. cbn [List.filter]. destruct (P x).
  - rewrite !map_app. cbn [map app]. apply Permutation_sym. apply Permutation_middle.
  - cbn [app]. apply Permutation_refl.
Qed.
Lemma q_ids_pop_item : ltac2:(tb__ "0|3|
ScS29S7A1M0G0S0S2eS0S0A2M1S29G1A1S0S0S0S5bS0S50R9S28S7R8S2cS7S13R6S2cG1R5R4A3R3A3R7A3A3R1A3S28S0S2dS29S0A1L_;S35S5dS32S0S0R5A3A1S24S53R5A1R1A2A2S2cS0S54R9R5A2S2aS0A1M2A3G2X2dx2S50R9S28S7R8S2cS7S13R6R4R2A3R7A3A3R1A3A3A3Fc';Fs';Fs;Fi2;Fit;Fa;Fg2;Fg1;FG;").
Proof.
  intros G g1 g2 a it i2 s s' c'. unfold q_ids. rewrite !qitems_mid. cbn [qb_items].
  replace (map (qb_id G) (g1 ++ mkQB a (it :: i2) s :: g2)) with (map (qb_id G) (g1 ++ mkQB a i2 s' :: g2)) by (rewrite !map_app; reflexivity).
  eapply Permutation_trans.
  { apply Permutation_app_tail. exact (filter_map_mid (it_id G) (fun it0 : Z * Z => is_primary (snd it0) && (it_cls it0 =? c')) (qitems g1) it i2 (qitems g2)). }
  cbn beta. rewrite <- app_assoc. apply Permutation_refl.
Qed.

Lemma q_ids_pop_batch : ltac2:(tb__ "0|3|
ScS29S7A1M0G0S7S0S2S29S2eS0S0A2M1A1S10R2A1S2aG1A1A3S5bS0S50R6S28S7R5S2cS7R3R4A3A3R2A3S28S0S2dS29S0A1L_;S24R2Z18A2S2cS0S55R6R3A2S2aS0A1M2A3G2X2dx2S50R6S28S7R5R4A3R2A3A3A3F_;Fc';Fb;Fg2;Fg1;FG;").
Proof.
  intros G g1 g2 b c' HE. unfold q_ids. rewrite qitems_mid, HE. cbn [app].
  replace (qitems g1 ++ qitems g2) with (qitems (g1 ++ g2)) by (unfold qitems; apply flat_map_app).
  destruct (c' =? 24).
  - rewrite !map_app. cbn [map app].
    set (F := map (it_id G) _). set (M1 := map (qb_id G) g1). set (M2 := map (qb_id G) g2).
    rewrite (app_assoc F M1). rewrite (app_assoc F M1 M2). apply Permutation_sym. apply Permutation_middle.
  - cbn [app]. apply Permutation_refl.
Qed.

Lemma batch_pure_same : ltac2:(tb__ "0|0|
SbSbS7S2ScS8R2A1S8R3A1A3S2S29S1eA1S19R3A1S19R4A1A3S0S2S0SaS42R5R1A2A1SaS42R6R1A2A1A3Fc';S48R6R4A2S48R6R5A2F_;F_;F_;F_;Fb;FA';FA;").
Proof.
  intros A A' b EG ES EAU (B1 & B2 & (y & E & Y0 & YM & Y1) & B4). unfold batch_pure. rewrite EG, (EAU 24).
  split; [exact B1|]. split; [exact B2|]. split; [exists y; exact (conj E (conj Y0 (conj YM Y1)))|].
  eapply Forall_impl; [|exact B4]. intros it (I1 & I2 & I3 & I4). unfold item_pure. cbn zeta. rewrite EG, ES, (EAU (ClassID (needed (snd it)))).
  exact (conj I1 (conj I2 (conj I3 I4))).
Qed.

Definition cls_metaRF (G : ageom) (c : Z) (cs : class_state) (z : Z) : Prop := ltac2:(tb__ "0|1|
S63S1cVG;A1M0Vc;A2S0S61G0Vc;A2S0S6S3S20R2Vz;A2S22Vz;S1fR2Z80A2A2A2S3S20R1Vz;A2S22Vz;S1fR1SfVcs;A1A2A2A2A2Tfa;Tri;").

Lemma class_repr_push_gen : ltac2:(tb__ "0|e|
S3eS3eScSbSbS0SdSdS3S20Z1R3A2S20R3Z1eA2A2S2S2dSeR5A1SeR6A1A3S2S29S2eS0S0A2A1S16R6A1S16R7A1A3S2S29S0A1S14R4A1S14R5A1A3S2S0SfR5A1SfR6A1A3S2S0SaR6A1SaR7A1A3S2S0S12R7A1S12R8A1A3S0S77ReRbRaR1A4S2S2fS56Q8A1M0A1M1R10R2A1R11R2A1A3F_;Fz;S0S5G0G0S2G1R12R2A1S34G0R1A2M2A3Lb;A2S5G0G0S2G1R12R3A1G2A3Lb;A2F_;Fz;S78S0S28S0S14RbA1S28S0S9RaA1S28S0S66RfRdRcA3S50RfS51RdA1RcA3A3A3A3A2S2S33S5cS5cS2bS0S9RbA1A2S2bS0S66R10ReRdA3A2A2S2bS0S50R10S51ReA1RdA3A2A2S5cS5cS2bS0S9RcA1A2S2bS0S66R10RfRdA3A2A2S2bS0S50R10S51RfA1RdA3A2A2A3S0S58S0R1S9RdA1M3A3S3S20Z0M4R2A2S3S2S0S25S26R2S60A2M5S5eR10A1M6A2G4A3S20S1fG5G6A2SaRfA1A2A2A2F_;Fx;S3S3bR13S3cS1fS1fS11R12A1Zd0M7A2S23Z50M8RfA2A2M9U4MaS21S2bS0G3A2A1MbA3A2S3S3bR13S3cS1fG9Z4McA2GaS5fRfA1MdA3A2S3S3bR13S3cS1fG9Z8A2U8S5eRfA1A3A2S3S33S0S2S2fS0A1S5aS0S9RfA1R2A3S34S0R1A2A3S3bR16S3cS1fS1fS1fS1fS11R15A1G7A2S23G8R12A2A2Z10A2S23GcS21R3A1A2A2GaR2A3A2F_;Fx;Fi;S20GbGdA2A2A2A2A2S2S2dSeR12A1S30A3S65R16R14R13R11R10A5S65R16R15R13R12R10A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fcs';Fcs;Fc;FA';FA;FG;Fm';Fm;").
Proof.
  intros m m' G A A' c cs cs' Hc ECI ELV EF EMF EAU EMU AG PK ND' CNT' SL' CI' HCI P4.
  assert (CA : forall cc, (forall k, (k < c_w cc)%nat -> cls_metaRF G c cs (c_addr cc + Z.of_nat k)) -> cell_ok m cc -> cell_ok m' cc).
  { intros cc Hf. apply cell_ok_agree. intros k Hk. apply AG. exact (Hf k Hk). }
  assert (PP : forall lo hi, present m lo hi -> present m' lo hi) by (intros lo hi H z Hz; exact (PK z (H z Hz))).
  unfold class_repr in P4 |- *. rewrite ECI, ELV, EF, EMF, EAU, EMU.
  set (ri := region_info (ag_spacebeg G) c) in *. set (fa := free_array (ag_spacebeg G) c) in *. set (rb := region_beg (ag_spacebeg G) c) in *.
  destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & C9 & PR & N7 & PU & PS & PE & ND & LV & CI & CN & CT & CC & CMU & CFA).
  assert (FRI : forall off w, 0 <= off -> off + Z.of_nat w <= 72 -> forall k, (k < w)%nat -> cls_metaRF G c cs (ri + off + Z.of_nat k)).
  { intros off w Ho Hw k Hk. left. unfold ri in *. lia. }
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mutex; lia | exact C1]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_num_freed; lia | exact C2]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_free_array; lia | exact C3]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_user; lia | exact C4]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_meta; lia | exact C5]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_user; lia | exact C6]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_meta; lia | exact C7]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_exhausted; lia | exact C8]|].
  split; [exact (PP _ _ PRI)|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split.
  { intros i x Hi. apply CA; [|exact (C9 i x Hi)]. cbn [c_addr c_w]. intros k Hk. right.
    pose proof (nth_error_Some_lt _ _ _ Hi) as L. unfold fa in *. lia. }
  split; [exact (PP _ _ PR)|].
  split.
  { intros x0 Hx0. apply in_app_or in Hx0 as [Hx0|Hx0]; [apply N7; apply in_or_app; left; exact Hx0 | exact (SL' x0 Hx0)]. }
  split; [intros z Hz Hn; exact (PK z (PU z Hz Hn))|].
  split; [exact (PP _ _ PS)|]. split; [exact (PP _ _ PE)|].
  split; [exact ND'|].
  split; [exact LV|].
  split; [intros _; exact CI'|]. split; [intros HF; rewrite HCI in HF; discriminate|].
  split; [exact CT|]. split; [|exact (conj CMU CFA)].
  unfold slots in CC |- *. rewrite EAU, CC. f_equal. clear -CNT'. lia.
Qed.

Section Push.
Variables (Kc : KcA) (A : AA) (rho rho' : valuation) (tp : list word) (tr : list event) (md : Model).
Variables (q' : list qbatch) (c x : Z).
Local Abbreviation Gq := (aa_geom A).
Local Abbreviation SBq := (ag_spacebeg (aa_geom A)).
Local Abbreviation Tq := (ag_thread (aa_geom A)).
Local Abbreviation v0 := (view segsA (rm rho)).
Local Abbreviation v1 := (view segsA (rm rho')).
Local Abbreviation mm := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho))).
Local Abbreviation mm' := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho'))).
Local Abbreviation kk := (Z.of_nat (length (cs_cache (cls_of A c)))).
Local Abbreviation A1 := (set_q A [] q').
Local Abbreviation Ap := (push_cache (set_q A [] q') c x).

Hypothesis HK : ltac2:(tb__ "0|0|
S57VKc;VA;Vrho;Vtp;Vtr;Vmd;A6").
Hypothesis HCI : aa_cache_inited A = true.
Hypothesis Hc : 1 <= c <= 30.
Hypothesis Hk : kk < max_count c.
Hypothesis Hw : ltac2:(tb__ "0|0|
S1S2S56Q40A1S4dVrho';R1A2S4dVrho;R1A2A3Fi;").
Hypothesis HOUT : ltac2:(tb__ "0|0|
S0S4S45VA;R1A2A1S4S47S8VA;A1Vc;S21S2bS0S9S42VA;Vc;A2A1A2A1R2A4A1S2S2fS56Q8A1A1S3aS39S4cVrho';A1R3A3S3aS39S4cVrho;A1R3A3A3F_;F_;Fz;").
Hypothesis HIN : ltac2:(tb__ "0|3|
S0S45VA;R1A2S4S2S2fS56Q8A1M0A1M1S3aS39S4cVrho;A1R2A3S31G0A1M2A3A1S4S2G1S3aS39S4cVrho';A1R3A3G2A3A1F_;F_;Fz;").
Hypothesis HC1 : ltac2:(tb__ "0|0|
S3bS3aS39S4cVrho';A1A2S3cS46S8VA;A1Vc;A2U4S1fS21S2bS0S9S42VA;Vc;A2A1A2A1Z1A2A3A2").
Hypothesis HC2 : ltac2:(tb__ "0|0|
S3bS3aS39S4cVrho';A1A2S3cS1fS1fS46S8VA;A1Vc;A2Z10A2S23Z4S21S2bS0S9S42VA;Vc;A2A1A2A1A2A2U4Vx;A3A2").

Hypothesis HQ1 : Forall (batch_pure A) q'.
Hypothesis HQ2 : NoDup (map qb_addr q').
Hypothesis HQ3 : ltac2:(tb__ "0|2|
S0S3S20Z1R1A2S20R1Z1eA2A2S5bS0S50S8VA;A1M0S51VA;A1R2A3S28S0S2dS29S0A1L_;S24R2Vc;A2S2cS0Vx;S2aS0A1M1A3G1X2dx2S50G0Vq';R2A3A3A3F_;Fc';").
Hypothesis HSUB : ltac2:(tb__ "0|1|
S7S58S7R1Vq';A3S5S7S7S3S58S7R1S51VA;A1A3S3S2S0S1bR3A1S1bR1A1A3S2eS0S0A2M0S58G0R1S10R4A1A3S58G0R2S10R3A1A3F_;Fit;A2A2Lb;A2F_;Fb';").
Hypothesis HQ6 : ltac2:(tb__ "0|3|
S5bS0S72S2eS0S0A2M0S0S37S0S0A2M1S59G0G0S38S5dS32S0S0R1A3A1A1Lit;M2S52Vq';A1A3A4S72G0S0G1S59G0G2S52S51VA;A1A1A3A4A3").
Hypothesis HQ7 : ltac2:(tb__ "0|1|
S2S0S21S2bS2eS0S0A2M0S59G0S1aS52Vq';A1A3A2A1S6dVA;A1A3").
Hypothesis HX : ltac2:(tb__ "0|3|
S3S20Z0M0Vx;A2S3S2S0S25S26Vx;S60A2M1S5eVc;A1M2A2G0A3S20S1fG1G2A2SaS42VA;Vc;A2A1A2A2A2").

Lemma P_facts : ltac2:(tb__ "0|3|
S3S68S8VA;A1M0A1S3S69VA;A1S3S4bVA;A1S3S6aVA;A1S3S6cS3dS64G0A1S3aS39S4cVrho;A1A2A2M1VA;A2S3S6eG1VA;A2S0S3S20Z1R1A2S20R1Z1eA2A2S3S20Z0SaS42VA;R2A2A1M2A2S20G2S62A2A2F_;Fc';A2A2A2A2A2A2").
Proof.
  pose proof HK as (HA & _). destruct HA as (HG & _ & _ & HRest & _ & HI3 & _). cbn zeta in HRest.
  destruct HRest as (R1 & _ & R3 & R4 & (R5 & _) & _).
  split; [exact HG|]. split; [exact HI3|]. split; [exact R5|]. split; [exact R1|]. split; [exact R3|]. split; [exact R4|].
  intros c' Hc'. destruct R3 as (_ & _ & _ & P4). pose proof (P4 c' Hc') as HC. unfold class_repr in HC. cbn zeta in HC.
  destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold cls_of, kUserMapSize in *. lia.
Qed.

Lemma PZ_T : ltac2:(tb__ "0|2|
S0S47S8VA;A1M0Vc;S21S2bS0S9S42VA;Vc;A2A1A2A1R1A4S3S20S1fS11G0A1M1Zd0A2R2A2S22R2S1fG1Zad0A2A2A2F_;Fz;").
Proof.
  intros z Hz. unfold push_zone, pc_entry in Hz. pose proof (max_count_le16 c Hc) as M16. pose proof (Zle_0_nat (length (cs_cache (cls_of A c)))) as K0'.
  clear -Hz Hc Hk M16 K0'. lia.
Qed.
Lemma HINp : ltac2:(tb__ "0|3|
S0S6S45VA;R1A2S47S8VA;A1Vc;S21S2bS0S9S42VA;Vc;A2A1A2A1R1A4A2S4S2S2fS56Q8A1M0A1M1S3aS39S4cVrho;A1R2A3S31G0A1M2A3A1S4S2G1S3aS39S4cVrho';A1R3A3G2A3A1F_;F_;Fz;").
Proof.
  intros z [H|H] Hz; [exact (HIN z H Hz)|]. destruct H as [H|H].
  - apply (cell_ok_some v1 _ 4%nat _ z HC1). replace (Z.of_nat 4) with 4 by reflexivity. exact H.
  - apply (cell_ok_some v1 _ 4%nat _ z HC2). replace (Z.of_nat 4) with 4 by reflexivity. exact H.
Qed.

Lemma PLEN : length (aa_cls A) = 32%nat.
Proof. pose proof P_facts as (_ & _ & _ & _ & (PL & _) & _). exact PL. Qed.
Lemma ECLS_raw : ltac2:(tb__ "0|0|
S2S29SdA1S15S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3A1S1dSdS15VA;A1S27Vc;A1S49S42VA;Vc;A2Vx;A2A4A3").
Proof. reflexivity. Qed.
Lemma ECLS_c : ltac2:(tb__ "0|0|
S2SdS42S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3Vc;A2S49S42VA;Vc;A2Vx;A2A3").
Proof. unfold cls_of at 1. unfold nthZ. rewrite ECLS_raw. apply nth_list_upd_same. rewrite PLEN. clear -Hc. lia. Qed.
Lemma ECLS_o : ltac2:(tb__ "0|0|
S0S3S20Z1R1A2S20R1Z1eA2A2S4S2S0R2Vc;A3A1S2SdS42S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3R3A2S42VA;R3A2A3F_;F_;Fc';").
Proof. intros c' Hc' NE. unfold cls_of, nthZ. rewrite ECLS_raw. apply nth_list_upd_other. clear -Hc Hc' NE. lia. Qed.
Lemma ECLS_nums : ltac2:(tb__ "0|2|
S0S3S2S0SaS42S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3R1A2M0A1SaS42VA;R1A2M1A1A3S2S0S12G0A1S12G1A1A3A2Fc';").
Proof.
  intros c'. unfold cls_of, nthZ. rewrite ECLS_raw. destruct (Nat.eq_dec (Z.to_nat c) (Z.to_nat c')) as [E|NE].
  - rewrite <- E. rewrite nth_list_upd_same by (rewrite PLEN; clear -Hc; lia). split; reflexivity.
  - rewrite nth_list_upd_other by exact NE. split; reflexivity.
Qed.

Lemma NX : ltac2:(tb__ "0|0|
S4S58S0Vx;S50S8VA;A1Vq';Vc;A3A3A1").
Proof.
  intros Hin. pose proof P_facts as (_ & _ & _ & _ & (_ & _ & _ & P4) & _).
  destruct (P4 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
  apply NoDup_app_r in ND. apply NoDup_app_r in ND. apply NoDup_app_r in ND.
  pose proof (HQ3 c Hc) as P. rewrite Z.eqb_refl in P.
  pose proof (ND_permQ _ _ (Permutation_sym P) ND) as ND2.
  exact (NoDup_app_disj [x] (q_ids Gq q' c) x ND2 (or_introl eq_refl) Hin).
Qed.

Lemma QP1 : q_pure A1.
Proof. split; [exact HQ1 | exact HQ2]. Qed.
Lemma QFOOT_sub : ltac2:(tb__ "0|0|
S0S67S43VA;S2aS7A1Vq';A3R1A2S67VA;R2A2F_;Fz;").
Proof.
  intros z Hz. unfold q_foot in *. change (aa_q_thread A1 ++ aa_q_global A1) with q' in Hz. fold (qall A).
  apply Exists_exists in Hz as (b' & Hb' & Hz). destruct (HSUB b' Hb') as (b & Hb & EA & HI). apply Exists_exists. exists b. split; [exact Hb|].
  rewrite <- EA. destruct Hz as [Hz|Hz]; [left; exact Hz | right].
  apply Exists_exists in Hz as (it & Hit & Hz). apply Exists_exists. exists it. split; [exact (HI it Hit) | exact Hz].
Qed.

Lemma QFOOT_slot : ltac2:(tb__ "0|0|
S0S67S43VA;S2aS7A1Vq';A3R1A2S4S6fS8VA;A1Vc;Vx;R2A4A1F_;Fz;").
Proof.
  intros z Hz HS. pose proof P_facts as (HG & HI3 & HQP & HLS & HPR & HSR & HAU). pose proof HI3 as (H3 & _ & SEC3 & _).
  pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  apply (slot_czone A c x z) in HS.
  pose proof HX as (X0 & XM & XE). unfold kCompactPtrScale in XM, XE. rewrite Z.shiftl_mul_pow2 in XM, XE by lia. change (2 ^ 4) with 16 in XM, XE.
  replace (x * 16) with (16 * x) in XM, XE by lia.
  pose proof (HAU c Hc) as AUc. rewrite kUserSpaceSize_val in AUc.
  unfold q_foot in Hz. change (aa_q_thread A1 ++ aa_q_global A1) with q' in Hz.
  apply Exists_exists in Hz as (b & Hb & Hz).
  assert (PRIM : qzone A1 z -> False).
  { intros QZ. destruct (qzone_czone A1 HG H3 QP1 HAU z QZ) as (c' & o' & (C1' & O0' & OM' & OE' & IDin') & CZ').
    apply (czone_slots_disj SBq c (16 * x) c' o' z S1 ltac:(clear -S2 TG; lia) S8 Hc C1' ltac:(clear -X0; lia) O0' XM OM' ltac:(clear -XE AUc; lia) OE'); [|exact HS|exact CZ'].
    destruct (Z.eq_dec c c') as [EC|NC]; [right | left; exact NC]. subst c'. intros EO. apply NX.
    rewrite <- EO in IDin'. replace (16 * x / 16) with x in IDin' by (rewrite Z.mul_comm, Z.div_mul; lia). exact IDin'. }
  destruct Hz as [Hz|Hz].
  - apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | left; exact Hz].
  - apply Exists_exists in Hz as (it & Hit & Hz). destruct (is_primary (snd it)) eqn:EP.
    + apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | right]. apply Exists_exists. exists it. split; [exact Hit|]. split; [exact EP | exact Hz].
    + pose proof (proj1 (Forall_forall _ _) HQ1 b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
      destruct (IP4 EP) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [i Hi].
      destruct HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      destruct (SEC3 i ch Hi) as (X1 & _). rewrite kSpaceSize_val in X1.
      destruct D10 as (E1 & E2 & E3 & E4 & E5). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in E5.
      pose proof (rz_sec (snd it) IP2 EP) as RZ. pose proof (round_up_ge8 (snd it)) as R8. unfold PG in *.
      destruct Hz as [Hz|Hz].
      * apply (czone_out A HG H3 c (16 * x) (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z Hc ltac:(clear -X0; lia) XM ltac:(clear -XE AUc; lia));
          [clear -Hz RZ Eu Esz D8 R8 IP2; lia | clear -X1; lia | exact E5 | exact HS].
      * apply (czone_sh_out A HG H3 c (16 * x) (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z Hc ltac:(clear -X0; lia) XM ltac:(clear -XE AUc; lia));
          [| clear -E1; lia | clear -E3 TG; lia | clear -X1; lia | exact HS].
        assert (B8 : fst it mod 8 = 0).
        { destruct (proj1 (Z.mod_divide (sc_map_beg ch) 4096 ltac:(lia)) D6) as [k0 Hk0]. apply Z.mod_divide; [lia|]. exists (k0 * 512 + 768). lia. }
        pose proof (Sh_SB (fst it) (8 * ((snd it + 7) / 8)) B8) as E8. rewrite (Z.mul_comm 8), Z.div_mul in E8 by lia.
        pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)) as MB.
        pose proof (Geometry.Sh_mono (sc_map_beg ch) (fst it) ltac:(clear -Eu; lia)) as M1.
        pose proof (Geometry.Sh_mono (fst it + (snd it + 7) / 8 * 8) (sc_map_beg ch + sc_map_size ch) ltac:(clear -Eu Esz D8 R8 DM MB; lia)) as M2.
        clear -Hz E8 M1 M2. lia.
Qed.

Lemma CELLM : ltac2:(tb__ "0|3|
S3fS33S76R1S41R2A1A2S3S4S45VA;S1fS40R3A1S21R2A1A2M0A2A1S4S47S8VA;A1M1Vc;S21S2bS0S9S42VA;Vc;A2A1A2A1G0A4A1A2F_;Fj;S3bS3dS64G1A1M2S3aS39S4cVrho;A1A2A2R2A2S3bS3dG2S3aS39S4cVrho';A1A2A2R3A2F_;F_;Fcc;").
Proof. intros cc H. apply cell_ok_agree. intros j Hj. destruct (H j Hj) as [N1 N2]. unfold maskv. rewrite (HOUT _ N1 N2). reflexivity. Qed.
Lemma MT_eq : ltac2:(tb__ "0|2|
S3eS0S3S20S11S8VA;A1M0A1M1R1A2S22R1S1fG1Z1000A2A2A2S2S2fS56Q8A1A1S3dS64G0A1R3R2A3R3R2A1A3F_;Fz;Fv;").
Proof. intros v z Hz. pose proof P_facts as (HG & _). apply maskv_out. apply fs_footb_T; [exact HG | exact Hz]. Qed.

Lemma CR_push : ltac2:(tb__ "0|2|
S0S3S20Z1R1A2S20R1Z1eA2A2S65S3dS64S8VA;A1M0A1S3aS39S4cVrho';A1A2A2G0S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3M1R2S42G1R2A2A5F_;Fc';").
Proof.
  intros c' Hc'. pose proof P_facts as (HG & HI3 & HQP & HLS & HPR & HSR & HAU). pose proof HI3 as (H3 & _).
  pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  destruct HPR as (PL & _ & _ & P4). pose proof (P4 c' Hc') as PC. fold (cls_of A c') in PC.
  assert (HFA : 0 <= cs_mapped_free_array (cls_of A c') <= kFreeArraySize).
  { unfold class_repr in PC. cbn zeta in PC. destruct PC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N6 & _). clear -N6. lia. }
  assert (NPZ : forall z, SBq <= z < SBq + 2 ^ 37 + 4096 -> ~ push_zone Gq c kk z).
  { intros z Hz HP. pose proof (PZ_T z HP) as HT. clear -Hz HT ST. lia. }
  assert (AGRF : forall z, cls_metaRF Gq c' (cls_of A c') z -> mm' z = mm z).
  { intros z Hz. unfold maskv. rewrite HOUT; [reflexivity | |].
    - intros HQ. apply (QW_not_metaV A HG H3 HQP HAU c' (cls_of A c') Hc' HFA z HQ). unfold cls_metaRF in Hz. unfold cls_metaV. cbn zeta in *. destruct Hz as [Hz|Hz]; [left | right; left]; exact Hz.
    - apply NPZ. unfold cls_metaRF, region_info, free_array, region_beg, kRegionInfoStride in Hz. cbn zeta in Hz. rewrite kSpaceSize_val in Hz.
      unfold kFreeArraySize in HFA. rewrite kUserSpaceSize_val in Hz. unfold kRegionSize in Hz. clear -Hz Hc' HFA. nia. }
  assert (PK : forall z, (exists b, mm z = Some b) -> exists b, mm' z = Some b).
  { exact (MSOME A HG H3 HQP HAU rho rho' (push_zone Gq c kk) PZ_T HOUT HINp). }
  destruct (Z.eq_dec c' c) as [EC|NC].
  - subst c'. rewrite ECLS_c.
    pose proof PC as PC0. unfold class_repr in PC0. cbn zeta in PC0.
    destruct PC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N7 & _ & _ & _ & ND & _ & CI & _).
    destruct (CI HCI) as (K1 & K2 & K3 & K4 & K5).
    apply (class_repr_push_gen mm mm' Gq A Ap c (cls_of A c) (push_cs (cls_of A c) x) Hc eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl AGRF PK); [| | | | exact HCI | exact PC].
    + cbn [push_cs cs_cache]. change (qall Ap) with q'. change (live_ids Gq Ap c) with (live_ids Gq A c).
      eapply ND_permQ; [|exact ND]. eapply Permutation_trans; [apply perm_push|].
      apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head.
      pose proof (HQ3 c Hc) as P. rewrite Z.eqb_refl in P. cbn [app] in P. apply Permutation_sym. exact P.
    +   cbn [push_cs cs_cache]. change (qall Ap) with q'. change (live_ids Gq Ap c) with (live_ids Gq A c).
      pose proof (HQ3 c Hc) as P. rewrite Z.eqb_refl in P. apply Permutation_length in P. cbn [app length] in P. rewrite length_app. cbn [length]. clear -P. lia.
    + cbn [push_cs cs_cache]. intros x0 Hx0. apply in_app_or in Hx0 as [Hx0|Hx0]; [apply N7; apply in_or_app; right; exact Hx0|].
      destruct Hx0 as [<-|[]]. exact HX.
    + cbn [push_cs cs_cache]. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
      pose proof (max_count_le16 c Hc) as M16. pose proof (Zle_0_nat (length (cs_cache (cls_of A c)))) as K0'.
      split; [|split; [|split; [|split; [|clear -Hk; lia]]]].
      * eapply cell_ok_agree; [|exact HC1]. cbn [c_addr c_w]. intros j Hj. apply MT_eq. unfold pc_entry. clear -Hj Hc. lia.
      * apply CELLM; [|exact K2]. cbn [c_addr c_w]. intros j Hj. split; [apply (QW_T A HG H3 HQP HAU); clear -Hj Hc; lia|].
        unfold push_zone, pc_entry. clear -Hj K0'. lia.
      * apply CELLM; [|exact K3]. cbn [c_addr c_w]. intros j Hj. split; [apply (QW_T A HG H3 HQP HAU); clear -Hj Hc; lia|].
        unfold push_zone, pc_entry. clear -Hj K0'. lia.
      * intros i x0 Hi. destruct (Nat.lt_ge_cases i (length (cs_cache (cls_of A c)))) as [L|L].
        -- rewrite nth_error_app1 in Hi by exact L. apply CELLM; [|exact (K4 i x0 Hi)]. cbn [c_addr c_w]. intros j Hj.
           split; [apply (QW_T A HG H3 HQP HAU); clear -Hj Hc L Hk M16; lia|]. unfold push_zone, pc_entry. clear -Hj L. lia.
        -- rewrite nth_error_app2 in Hi by exact L. destruct (i - length (cs_cache (cls_of A c)))%nat as [|d] eqn:ED; [|destruct d; discriminate].
           cbn in Hi. injection Hi as <-. assert (Ei : i = length (cs_cache (cls_of A c))) by (clear -L ED; lia). rewrite Ei.
           eapply cell_ok_agree; [|exact HC2]. cbn [c_addr c_w]. intros j Hj. apply MT_eq. unfold pc_entry. clear -Hj Hc Hk M16 K0'. lia.
  - rewrite (ECLS_o c' Hc' NC).
    pose proof PC as PC0. unfold class_repr in PC0. cbn zeta in PC0.
    destruct PC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N7 & _ & _ & _ & ND & _ & CI & _).
    destruct (CI HCI) as (K1 & K2 & K3 & K4 & K5).
    pose proof (max_count_le16 c' Hc') as M16.
    assert (PCE : forall z, Tq + 208 + 80 * c' <= z < Tq + 208 + 80 * c' + 80 -> ~ QW A z /\ ~ push_zone Gq c kk z).
    { intros z Hz. split; [apply (QW_T A HG H3 HQP HAU); clear -Hz Hc'; lia|]. intros HP. unfold push_zone, pc_entry in HP.
      pose proof (max_count_le16 c Hc) as M16c. pose proof (Zle_0_nat (length (cs_cache (cls_of A c)))) as K0'. clear -Hz HP NC Hk M16c K0'. lia. }
    apply (class_repr_push_gen mm mm' Gq A Ap c' (cls_of A c') (cls_of A c') Hc' eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl AGRF PK); [| | | | exact HCI | exact PC].
    + change (qall Ap) with q'. change (live_ids Gq Ap c') with (live_ids Gq A c').
      eapply ND_permQ; [|exact ND]. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head.
      pose proof (HQ3 c' Hc') as P. destruct (Z.eqb_spec c' c) as [E|_]; [exfalso; exact (NC E)|]. cbn [app] in P. apply Permutation_sym. exact P.
    +   change (qall Ap) with q'. change (live_ids Gq Ap c') with (live_ids Gq A c').
      pose proof (HQ3 c' Hc') as P. destruct (Z.eqb_spec c' c) as [E|_]; [exfalso; exact (NC E)|]. cbn [app] in P. apply Permutation_length in P. clear -P. lia.
    + intros x0 Hx0. apply N7. apply in_or_app. right. exact Hx0.
    + split; [|split; [|split; [|split; [|exact K5]]]].
      * apply CELLM; [|exact K1]. cbn [c_addr c_w]. intros j Hj. apply PCE. clear -Hj. lia.
      * apply CELLM; [|exact K2]. cbn [c_addr c_w]. intros j Hj. apply PCE. clear -Hj. lia.
      * apply CELLM; [|exact K3]. cbn [c_addr c_w]. intros j Hj. apply PCE. clear -Hj. lia.
      * intros i x0 Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as L. apply CELLM; [|exact (K4 i x0 Hi)]. cbn [c_addr c_w]. intros j Hj. apply PCE. clear -Hj L K5 M16. lia.
Qed.

Lemma PR_push : primary_repr mm' Ap.
Proof.
  pose proof P_facts as (_ & _ & _ & _ & (PL & P0 & P31 & _) & _).
  split; [rewrite ECLS_raw, length_list_upd; exact PL|].
  split; [unfold nthZ in *; rewrite ECLS_raw, nth_list_upd_other by (clear -Hc; lia); exact P0|].
  split; [unfold nthZ in *; rewrite ECLS_raw, nth_list_upd_other by (clear -Hc; lia); exact P31|].
  intros c' Hc'. exact (CR_push c' Hc').
Qed.

Lemma QP_push : q_pure Ap.
Proof.
  split; [|exact HQ2]. change (qall Ap) with q'. eapply Forall_impl; [|exact HQ1]. intros b Hb.
  apply (batch_pure_same A Ap b eq_refl eq_refl); [|exact Hb]. intros c'. exact (proj1 (ECLS_nums c')).
Qed.

Lemma I3_push : inv3 Ap.
Proof.
  pose proof P_facts as (_ & HI3 & _). destruct HI3 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold inv3. cbn zeta.
  change (aa_geom Ap) with (aa_geom A). change (aa_live Ap) with (aa_live A). change (aa_sec Ap) with (aa_sec A). change (aa_depot Ap) with (aa_depot A).
  split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
  split.
  { intros z Hz. change (q_foot A1 z) in Hz. destruct (I4 z (QFOOT_sub z Hz)) as [NT NC]. split; [exact NT|].
    intros c' x' Hc' Hx'. fold (cls_of Ap c') in Hx'. destruct (Z.eq_dec c' c) as [EC|NE].
    - subst c'. rewrite ECLS_c in Hx'. cbn [push_cs cs_cache] in Hx'. apply in_app_or in Hx' as [Hx'|Hx'].
      + exact (NC c x' Hc Hx').
      + destruct Hx' as [<-|[]]. exact (QFOOT_slot z Hz).
    - rewrite (ECLS_o c' Hc' NE) in Hx'. exact (NC c' x' Hc' Hx'). }
  split; [exact I5|].
  split.
  { change (qall Ap) with q'. eapply ND_permQ; [|exact I6]. apply Permutation_app_head. exact HQ6. }
  split; [unfold qlarge, large_live in *; change (qall Ap) with q'; change (aa_live Ap) with (aa_live A); rewrite HQ7; exact I7|].
  split; [exact I8 | intros _; exact HCI].
Qed.

Lemma ECLS_mfa : ltac2:(tb__ "0|0|
S0S2S0SfS42S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3R1A2A1SfS42VA;R1A2A1A3Fc';").
Proof.
  intros c'. unfold cls_of, nthZ. rewrite ECLS_raw. destruct (Nat.eq_dec (Z.to_nat c) (Z.to_nat c')) as [E|NE].
  - rewrite <- E. rewrite nth_list_upd_same by (rewrite PLEN; clear -Hc; lia). reflexivity.
  - rewrite nth_list_upd_other by exact NE. reflexivity.
Qed.
Lemma PC_push : ltac2:(tb__ "0|0|
S2S0S75S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3A1S75VA;A1A3").
Proof. apply PrimCreditLaws.prim_credit_maps. intros c' Hc'. split; [exact (proj2 (ECLS_nums c')) | exact (ECLS_mfa c')]. Qed.

Lemma MD_push : ltac2:(tb__ "0|0|
S6bS39S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3Vtp;Vmd;A4").
Proof.
  pose proof HK as (HA & _). destruct HA as (_ & _ & _ & _ & HM & _).
  unfold model_inv in HM |- *. destruct HM as (VG & PB & LIM & V0 & K0' & F0 & TOPm & LED).
  split; [exact VG|]. split; [rewrite PC_push; exact PB|]. split; [exact LIM|]. split; [exact V0|]. split; [exact K0'|]. split; [exact F0|]. split; [exact TOPm|].
  unfold ledger_inv in LED |- *. destruct LED as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|].
  split; [exact L8 | exact L9].
Qed.

Theorem K0_push_gen : ltac2:(tb__ "0|0|
S57VKc;S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3Vrho';Vtp;Vtr;Vmd;A6").
Proof.
  pose proof P_facts as (HG & HI3 & HQP & HLS & HPR & HSR & HAU). pose proof HI3 as (H3 & _).
  pose proof HK as (HA & HKc & Htp & Htop & HRG).
  pose proof (view_parts A HG H3 HQP HAU rho rho' (push_zone Gq c kk) PZ_T HOUT HINp tp md HA) as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
  split; [|split; [exact HKc|split; [|split]]].
  - unfold AInvQ. cbn zeta. change (aa_geom Ap) with (aa_geom A).
    split; [exact HG|]. split; [exact V1|]. split; [exact V2|]. split; [|split; [exact MD_push | split; [exact I3_push | exact V10]]].
    split; [exact HLS|]. split; [exact V3|]. split; [exact PR_push|]. split; [exact V4|]. split; [exact (conj QP_push V5)|].
    split; [exact V6|]. split; [exact V7|]. split; [exact V8 | exact V9].
  - unfold tp_ok in *. change (aa_geom Ap) with (aa_geom A). rewrite (Hw 24%positive). exact Htp.
  - unfold top_high in *. change (aa_geom Ap) with (aa_geom A). rewrite (Hw 10%positive), (Hw V_DEPTH). exact Htop.
  - destruct HRG as (E1 & E2 & E3 & E4). unfold rigidQ. change (aa_geom Ap) with (aa_geom A). rewrite !Hw. exact (conj E1 (conj E2 (conj E3 E4))).
Qed.
End Push.

Lemma primary_not_large : ltac2:(tb__ "0|0|
S2eS0S0A2S2S2dS5dS32S0S0R1A3A1S30A3S2S2dS1aR2A1S36A3F_;Fit;").
Proof.
  intros it HP. unfold is_large. apply Z.leb_gt. destruct (Z_le_dec 64513 (snd it)) as [L|L]; [|lia].
  rewrite (not_primary_large _ L) in HP. discriminate.
Qed.

Theorem K0_push_item : ltac2:(tb__ "0|b|
S70SbS4fS4fS29S56Q40A1M0A1S29S74A1S73S29S7A1M1G1S0S2eS0S0A2M2S29G2A1S0S0S2G1S18RdA1S2aS7A1M3A3S2G1S17ReA1S28S7R8S2cS7S13R6S2cG2R5R4A3R3A3R7A3A3A3S2S2dSeRfA1S30A3S2S2dS5dS32S0S0R7A3A1S30A3S8R11A1ScS53R9A1S0S54R2RaA2S0S21S2bS0S9S42R14R2A2A1A2A1S0S22R1S5fR3A1A2S1S2G0S4dR15R1A2S4dR16R1A2A3Fi;S1S2S29S56Q8A1M4A1S4eR16R1A2S4eR17R1A2A3Fl;S0S4S45R19R1A2A1S4S47R9R8R6R2A4A1S2S2fG4A1M5S3aS39S4cR19A1M6R3A3S3aS39S4cR1aA1M7R3A3M8A3F_;F_;Fz;S0S45R1aR1A2S4S2G5S3aS39G7R2A3S31G4A1M9A3A1S4S2G5G8G9A3A1F_;F_;Fz;S3bS3aS39S4cR18A1A2S3cS46R9R8A2U4MaS1fR6Z1A2A3A2S3bS3aS39G6A2S3cS1fS1fS46RaR9A2Z10A2S23Z4R7A2A2GaR8A3A2S57R1dR1cR1bR19R18R17A6S57R1eS44S43R1dG3S28S7R17S2cS7S13R15R13R11A3R16A3A3A3RbRaA3R1bR1aR19R18A6F_;F_;F_;F_;F_;F_;F_;F_;Tk;Tx;Tc;TG;F_;F_;F_;F_;Fs';Fs;Fi2;Fit;Fa;Fg2;Fg1;Fmd;Ftr;Ftp;Frho';Frho;FA;FKc;").
Proof.
  intros Kc A rho rho' tp tr md g1 g2 a it i2 s s' HT HGL HCI HP G c x k Hk Hw Hl HOUT HIN HC1 HC2 HK. subst G.
  assert (EQA : qall A = g1 ++ mkQB a (it :: i2) s :: g2) by (unfold qall; rewrite HT, HGL; reflexivity).
  pose proof HK as (HA & _). pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _). cbn zeta in HRest.
  destruct HRest as (_ & _ & R3 & _ & (R5 & _) & _). pose proof HI3 as (H3 & _).
  assert (HAU : forall c', 1 <= c' <= 30 -> 0 <= cs_allocated_user (cls_of A c') <= kUserSpaceSize).
  { intros c' Hc'. destruct R3 as (_ & _ & _ & P4). pose proof (P4 c' Hc') as HC. unfold class_repr in HC. cbn zeta in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold cls_of, kUserMapSize in *. lia. }
  assert (Hit : In it (qitems (qall A))) by (rewrite EQA, qitems_mid; apply in_or_app; right; left; reflexivity).
  pose proof (item_slot A R5 HAU HG it Hit HP) as IS. cbv zeta in IS. fold c in IS.
  destruct IS as (C1 & RB1 & M1 & U1 & A16 & Z1 & Z2 & RZ & RZ16 & EU & UN & N1 & HS & TOP).
  pose proof R5 as [QF QN]. rewrite EQA in QF, QN.
  apply (K0_push_gen Kc A rho rho' tp tr md (g1 ++ mkQB a i2 s' :: g2) c x HK HCI C1 Hk Hw HOUT HIN HC1 HC2).
  -
    apply Forall_app in QF as [QF1 QF2]. inversion QF2 as [|? ? QB QF3]; subst. apply Forall_app. split; [exact QF1|]. constructor; [|exact QF3].
    unfold batch_pure in QB |- *. cbn [qb_addr qb_items] in QB |- *. destruct QB as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [cbn [length] in B2; clear -B2; lia|]. split; [exact B3|].
    inversion B4; subst; assumption.
  - rewrite map_app in QN |- *. cbn [map qb_addr] in QN |- *. exact QN.
  - intros c' Hc'. rewrite EQA. pose proof (q_ids_pop_item (aa_geom A) g1 g2 a it i2 s s' c') as P. rewrite HP in P. cbn [andb] in P. fold c in P.
    rewrite (Z.eqb_sym c' c). exact P.
  - intros b' Hb'. apply in_app_or in Hb' as [Hb'|[<-|Hb']].
    + exists b'. split; [rewrite EQA; apply in_or_app; left; exact Hb' | split; [reflexivity | intros it0 H0; exact H0]].
    + exists (mkQB a (it :: i2) s). split; [rewrite EQA; apply in_or_app; right; left; reflexivity | split; [reflexivity | intros it0 H0; right; exact H0]].
    + exists b'. split; [rewrite EQA; apply in_or_app; right; right; exact Hb' | split; [reflexivity | intros it0 H0; exact H0]].
  - rewrite EQA, !qitems_mid. cbn [qb_items]. rewrite !List.filter_app. cbn [List.filter]. rewrite HP. cbn [negb]. apply Permutation_refl.
  - unfold qlarge. rewrite EQA, !qitems_mid. cbn [qb_items]. rewrite !List.filter_app. cbn [List.filter]. rewrite (primary_not_large it HP). reflexivity.
  -
    assert (EX : Z.shiftl x kCompactPtrScale = it_ab it - (ag_spacebeg (aa_geom A) + c * 2 ^ 32)).
    { unfold x, it_id, ptr_to_compact, kCompactPtrScale, region_beg, kRegionSize. fold c. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
      assert (M16 : (it_ab it - (ag_spacebeg (aa_geom A) + c * 2 ^ 32)) mod 16 = 0).
      { destruct (proj1 (Z.mod_divide _ (Size c) ltac:(lia)) M1) as [j Hj]. destruct (proj1 (Z.mod_divide (Size c) 16 ltac:(lia)) Z2) as [j2 Hj2].
        apply Z.mod_divide; [lia|]. exists (j * j2). rewrite Hj, Hj2. ring. }
      pose proof (Z.div_mod (it_ab it - (ag_spacebeg (aa_geom A) + c * 2 ^ 32)) 16 ltac:(lia)) as DM. rewrite M16 in DM. lia. }
    assert (X0 : 0 <= x).
    { unfold x, it_id, ptr_to_compact, kCompactPtrScale, region_beg, kRegionSize. fold c. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_pos; [clear -RB1; lia | lia]. }
    rewrite EX. pose proof R5 as [QF0 _]. rewrite EQA in QF0. apply Forall_app in QF0 as [_ QF2]. inversion QF2 as [|? ? QB _]; subst.
    destruct QB as (_ & _ & _ & B4). inversion B4 as [|? ? IP _]; subst. destruct IP as (_ & _ & IP3 & _). specialize (IP3 HP). cbn zeta in IP3.
    unfold region_beg, kRegionSize in IP3. split; [exact X0|]. split; [exact M1|].
    unfold c, it_cls, it_ab in *. unfold cls_of in *. clear -IP3. lia.
Qed.

Theorem K0_push_batch : ltac2:(tb__ "0|c|
S70SbS4fS4fS29S56Q40A1M0A1S29S74A1S73S29S7A1M1G1S7S2G1S18R9A1S2aS7A1M2A3S2G1S17RaA1S28S7R4S2cS7R2R3A3A3A3S2S29S2eS0S0A2M3A1S10R3A1S2aG3A1A3S2S2dSeRcA1S30A3S8RdA1ScS55R1R6A2S0S21S2bS0S9S42RfZ18M4A2A1A2A1S0S22R1S5fG4A1A2S1S2G0S4dR10R1A2S4dR11R1A2A3Fi;S1S2S29S56Q8A1M5A1S4eR11R1A2S4eR12R1A2A3Fl;S0S4S45R14R1A2A1S4S47R8G4R6R2A4A1S2S2fG5A1M6S3aS39S4cR14A1M7R3A3S3aS39S4cR15A1M8R3A3M9A3F_;F_;Fz;S0S45R15R1A2S4S2G6S3aS39G8R2A3S31G5A1MaA3A1S4S2G6G9GaA3A1F_;F_;Fz;S3bS3aS39S4cR13A1A2S3cS46R8G4A2U4MbS1fR6Z1A2A3A2S3bS3aS39G7A2S3cS1fS1fS46R9G4A2Z10A2S23Z4R7A2A2GbR8A3A2S57R18R17R16R14R13R12A6S57R19S44S43R18G2S28S7R12R11A3A3G4RaA3R16R15R14R13A6F_;F_;F_;F_;F_;F_;F_;F_;Tk;Tx;TG;F_;F_;F_;F_;Fb;Fg2;Fg1;Fmd;Ftr;Ftp;Frho';Frho;FA;FKc;").
Proof.
  intros Kc A rho rho' tp tr md g1 g2 b HT HGL HE HCI G x k Hk Hw Hl HOUT HIN HC1 HC2 HK. subst G.
  assert (EQA : qall A = g1 ++ b :: g2) by (unfold qall; rewrite HT, HGL; reflexivity).
  pose proof HK as (HA & _). pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _). cbn zeta in HRest.
  destruct HRest as (_ & _ & R3 & _ & (R5 & _) & _).
  pose proof R5 as [QF QN]. rewrite EQA in QF, QN.
  apply (K0_push_gen Kc A rho rho' tp tr md (g1 ++ g2) 24 x HK HCI ltac:(lia) Hk Hw HOUT HIN HC1 HC2).
  - apply Forall_app in QF as [QF1 QF2]. inversion QF2; subst. apply Forall_app. split; assumption.
  - rewrite map_app in QN |- *. cbn [map] in QN.
    pose proof (ND_permQ _ _ (Permutation_middle (map qb_addr g1) (map qb_addr g2) (qb_addr b)) QN) as QN'.
    exact (NoDup_app_r [qb_addr b] _ QN').
  - intros c' Hc'. rewrite EQA. exact (q_ids_pop_batch (aa_geom A) g1 g2 b c' HE).
  - intros b' Hb'. exists b'. split; [rewrite EQA; apply in_app_or in Hb' as [Hb'|Hb']; apply in_or_app; [left | right; right]; exact Hb' | split; [reflexivity | intros it0 H0; exact H0]].
  - rewrite EQA, qitems_mid, HE. cbn [app]. replace (qitems g1 ++ qitems g2) with (qitems (g1 ++ g2)) by (unfold qitems; apply flat_map_app). apply Permutation_refl.
  - unfold qlarge. rewrite EQA, qitems_mid, HE. cbn [app]. replace (qitems g1 ++ qitems g2) with (qitems (g1 ++ g2)) by (unfold qitems; apply flat_map_app). reflexivity.
  - apply Forall_app in QF as [_ QF2]. inversion QF2 as [|? ? QB _]; subst. destruct QB as (_ & _ & (y & E & Y0 & YM & Y1) & _).
    assert (EX : x = y).
    { unfold x, qb_id, ptr_to_compact, kCompactPtrScale. rewrite E. replace (region_beg (ag_spacebeg (aa_geom A)) 24 + 16 * y - region_beg (ag_spacebeg (aa_geom A)) 24) with (y * 2 ^ 4) by lia.
      rewrite Z.shiftr_div_pow2, Z.div_mul by lia. reflexivity. }
    clearbody x. subst x. unfold kCompactPtrScale. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. change (Size 24) with 8192. unfold kQuarantineBatchSize in Y1.
    split; [exact Y0|]. split; [|clear -Y1; lia].
    apply Z.mod_divide; [lia|]. destruct (proj1 (Z.mod_divide y 512 ltac:(lia)) YM) as [j Hj]. exists j. clear -Hj. lia.
Qed.

Theorem K0_laws : ltac2:(tb__ "0|0|
S70S71R1A1S4aS39S57R2A1A2F_;FKc;").
Proof.
  intros Kc HKc. constructor.
  - intros A. exact (K0_stable Kc A HKc).
  - intros A rho tp tr md H. exact (K0_facts Kc A rho tp tr md H).
  - intros A rho rho' tp tr md Hw Hl HO HI H. exact (K0_view Kc A rho rho' tp tr md Hw Hl HO HI H).
  - intros A t g rho tp tr md P H. exact (K0_perm Kc A t g rho tp tr md P H).
  - intros A rho rho' tp tr md g1 g2 a it i2 s s'. exact (K0_push_item Kc A rho rho' tp tr md g1 g2 a it i2 s s').
  - intros A rho rho' tp tr md g1 g2 b. exact (K0_push_batch Kc A rho rho' tp tr md g1 g2 b).
Qed.
End InvQ4.

(* [comment removed for export] *)
Module F0A_dzone.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "leb"; "sub"; "modulo"; "pow"; "mul"; "opp"; "div"; "@Corelib.Init.Datatypes"; "bool"; "false"; "prod"; "andb"; "true"; "list"; "orb"; "pair"; "fst"; "nat"; "nil"; "snd"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "obj_range"; "sobj"; "valuation"; "ob_base"; "ob_hi"; "ob_lo"; "rm"; "rw"; "sv_below"; "sv_eqb"; "agree_below"; "holds"; "sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "qbatch"; "sec_chunk"; "AA"; "aa_live"; "aa_sec"; "ag_thread"; "aa_q_thread"; "ageom"; "DG"; "aa_depot"; "ag_ctx"; "ag_spacebeg"; "sc_map_beg"; "sc_map_size"; "topG"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone"; "same_rng"; "zoneF"; "rng_below"; "img_okD"; "rd_okb"; "winpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "QG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "NFS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "hw_of"; "j_min"; "j_qb"; "j_qf"; "j_st"; "rhoF_of"; "ZD_NRT"; "ZD_NV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "O_blkN"; "O_sh"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "IMG_LO"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Sh"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "Wcan"; "free_depth"; "V_DEPTH"; "chain_pre"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "DFP"; "MAP1"; "MAP1N"; "STORE"; "DFPw"; "dfp_static"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "bv_signed"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_geo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD"; "AInvX"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundA SymSoundM SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs Inv GlueM InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull SpineMallocS4 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvKf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition zoneF (A : AA) (a : Z) : Prop := ltac2:(tb__ "0|5|
S32VA;A1S3aS5S3S3S8S5fVa;A2S9Va;S5eA2A2S5S9Va;S6cA2S8SaS6aSfZ8S6bA2A2Va;A2A2A2S5S3S8S38R1A1M0Va;A2S9Va;SaG0Z1000M1A2A2A2S5S3S8S3dR1A1M2Va;A2S9Va;SaG2G1A2A2A2S5S3S8S3eR1A1M3Va;A2S9Va;SaG3S63A2A2A2S5S6S34S34S3S42S34R1S37VA;A1A3S3S8S3fR1A1M4Va;A2S9Va;SaG4S40R1A1A2A2A2A2Lch;A2S5S3S8S61Va;A2S9Va;S60A2A2S8S41R1A1Va;A2A2A2A2A2A2A2TG;").

Lemma DFP_splitF : ltac2:(tb__ "0|0|
S3bS0S69R2R1A2S5S6eR2A1S6dR3R2A2A2F_;Fa;FG;").
Proof. intros G a [H|[H|H]]; [left; exact H | right; right; left; exact H | right; right; right; exact H]. Qed.

Lemma zoneF_not_DFP : ltac2:(tb__ "0|0|
S35S35S25S17S6fQ40A1A1S50S0S77R5R4R3R2A4S4S3aS32R6A1S32R7A1A3S4S17S34A1S37R7A1S37R8A1A3S46R9R4A2S7S69S3cR9A1R5A2A1F_;F_;F_;F_;Fa;Fmd;Ftp;Frho;FAx;FA;").
Proof.
  intros A Ax rho tp md a HX EG ES HZ HD. unfold zoneF in HZ. cbn zeta in HZ. rewrite <- EG, <- ES in HZ.
  pose proof HX as (HG & HR & HF & HRest & HM & HI3 & HB). destruct HRest as (Hsep & Hlive & HP & HS & _).
  assert (HSEC : forall i ch, nth_error (aa_sec Ax) i = Some ch -> dyn_in (topG (aa_geom Ax)) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG (aa_geom Ax)) (ag_pab (aa_geom Ax)) kPtrArrayReserve) by (destruct HS as (_ & _ & _ & _ & X4 & _); exact X4).
  pose proof (zones_not_DFPw Ax a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2, HZ.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). unfold IMG_LO, IMG_HI in TI, CI.
  assert (GOAL : forall (P : Prop), (P -> ~ DFPw (aa_depot Ax) a) -> P -> ~ dfp_static a -> False).
  { intros P XP Xp Xns. destruct (DFP_splitF _ _ HD) as [Hs|Hw]; [exact (Xns Hs) | exact (XP Xp Hw)]. }
  assert (NS : forall lo hi, lo <= a < hi -> (hi <= STORE \/ MAP1 + 8 * MAP1N <= lo) -> ~ dfp_static a).
  { intros lo hi X1 X2 Hs. pose proof (dstat_range a Hs). lia. }
  destruct HZ as [[Z1 Z2]|[ZT|[ZC|[ZA|[ZM|[ZS|ZK]]]]]].
  - apply (GOAL (IMG_LO <= a < IMG_HI /\ ~ dstatw a)); [intros H; apply ZN; left; exact H | |].
    + split; [exact Z1|]. intros [Hs _]. pose proof (dstat_range a Hs). lia.
    + intros Hs. pose proof (dstat_range a Hs). lia.
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_introl H)))) ZT). eapply NS; [exact ZT | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_intror (or_introl H))))) ZC). eapply NS; [exact ZC | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL (ag_spacebeg (aa_geom Ax) <= a < ag_spacebeg (aa_geom Ax) + kSpaceSize + 4096)); [intros H; apply ZN; right; left; exact H | rewrite kSpaceSize_val; lia |].
    apply (NS (ag_spacebeg (aa_geom Ax)) (a + 1)); [lia | unfold MAP1, MAP1N; lia].
  - destruct ZM as (ch & Hch & Hz).
    apply (GOAL (exists ch, In ch (aa_sec Ax) /\ sc_map_beg ch <= a < sc_map_beg ch + sc_map_size ch)).
    + intros H. apply ZN. do 7 right. left. exact H.
    + exists ch. exact (conj Hch Hz).
    + destruct (In_nth_error _ _ Hch) as (i & Hi). destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & D10 & _).
      pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; lia)) as CB. eapply NS; [exact Hz | unfold IMG_HI in CB; unfold MAP1, MAP1N; lia].
  - apply (GOAL (SHADOW_BAND_LO <= a < SHADOW_BAND_HI)); [intros H; apply ZN; do 8 right; left; exact H | exact ZS |].
    apply (NS SHADOW_BAND_LO (a + 1)); [lia | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, MAP1, MAP1N; lia].
  - apply (GOAL (topG (aa_geom Ax) <= a)); [intros H; apply ZN; do 9 right; exact H | exact ZK |].
    apply (NS (topG (aa_geom Ax)) (a + 1)); [lia | unfold MAP1, MAP1N; lia].
Qed.

Lemma chunk_zoneF : ltac2:(tb__ "0|0|
S35S25S17S6fQ40A1A1S50S0S0S0S4eS30R7R6R5R4A5S42S14S0S0A2S19S0S0R4R3A4S36R8A1A3S3S8ScR5Z10A2R3A2S9R3SaR5S4bR4A1A2A2A2S46RaR4A2F_;F_;F_;Fa;Fn;Fp;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md p n a HA HL Ha. unfold zoneF. cbn zeta.
  destruct (is_primary n) eqn:EP.
  - pose proof (live_slot A rho tp md p n HA HL EP) as LS. cbn zeta in LS. destruct LS as (C1 & O1 & _ & _ & L1 & L2 & _).
    pose proof (live_prim_facts segsA A rho tp md p n HA HL EP) as LP. cbn zeta in LP. destruct LP as (_ & _ & X0 & _ & X1 & _).
    unfold region_beg, kUserSpaceSize, kFreeArraySize in *. unfold kRegionSize in *. rewrite kSpaceSize_val. change (2 ^ 32) with 4294967296 in *. do 3 right. left.
    set (c := ClassID (needed n)) in *. set (SB := ag_spacebeg (aa_geom A)) in *. clearbody c SB. clear -C1 O1 L1 L2 X0 X1 Ha. lia.
  - destruct (live_sec A rho tp md p n HA HL EP) as (ch & Hch & M1 & M2 & _).
    do 4 right. left. exists ch. split; [exact Hch | lia].
Qed.

Definition img_okD (d : zdesc) : bool := ltac2:(tb__ "0|1|
S14S14S1bS0A2M0S0A2S12Ld;Vd;G0S0G0S12Lp;R2S1bS0S12S12L_;S78R2U0A2S15S15SbS5fR1A2SbR3S5eA2A2S18SbR3S6cA2SbSaS6aSfZ8S6bA2A2R1A2A2A2S16X12x2Llo;Lz;X14x1Lhi;Lp;X14x1").
Lemma ZD_chkD : ltac2:(tb__ "0|0|
S5cS4S12S44S5dS48S1eS5dS58S59R1A1A3A3S16A3Fq;").
Proof. intros [| |]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section NFSZ.
Variables (A : AA) (rho : valuation) (tp : list word) (md : Model) (p n : Z).
Hypothesis HA : ltac2:(tb__ "0|0|
S4eS30VA;Vrho;Vtp;Vmd;A5").
Hypothesis HL : ltac2:(tb__ "0|0|
S42S14S0S0A2S19S0S0Vp;Vn;A4S36VA;A1A3").
Hypothesis HHI : blk_cls p n.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S4S0S70Q40S2aVrho;PcA2A2Vp;A3").
Variables (t : Z) (jv : junkF).
Hypothesis Ht : ltac2:(tb__ "0|2|
S3S3S8Z0Vt;A2S9Vt;Z100A2A2S3S4S0SdVt;Z4A2Z1A3S3S1fS21S30S29Vrho;A1A2M0S20ScVp;Z10A2U4M1S52Vt;Vn;A2A3A2S1fG0S20ScVp;ZcA2G1SdVn;SeZ2Z20A2A2A3A2A2A2A2").
Hypothesis Hjv : ltac2:(tb__ "0|9|
S3S3S8Z0M0S53Vjv;A1M1A2S9G1SeZ2Z40A2M2A2A2S3S3S8G0S56Vjv;A1M3A2S9G3G2A2A2S3S3S8G0S55Vjv;A1M4A2S9G4G2A2A2S3S3S8G0S54Vjv;A1M5A2S9G5G2A2A2S3S1fS21S30S29Vrho;A1A2M6S20SaS4fZ48A2U8M7G1A3A2S3S1fG6S20SaS38S32VA;A1A1M8Zae0A2G7G3A3A2S4S17S33A1S39VA;A1S1cS33A1A3S3S1fG6S20SaG8Z58A2G7G4A3A2S1fG6S20SaG8Z60A2G7G5A3A2A2F_;A2A2A2A2A2A2").
Variable q : qvar.
Hypothesis QC : qcond q A.

Theorem nfs_zoneF : ltac2:(tb__ "0|1|
S4cS42S4cR1S51Vq;A1A3S0S3S8S1aS0S0S23S57VA;Vrho;Vp;Vn;Vt;Vjv;A6S4dR3A1A2M0A3R1A2S9R1S1dS0S0G0A3A2A2S46VA;R2A2F_;Fa;F_;Fk;").
Proof.
  intros k Hk a Ha. unfold zoneF. cbn zeta.
  pose proof (inz_NFS A rho tp md p n HA HL HHI Hp12 t Ht jv Hjv q QC) as F2.
  destruct (Forall2_In_l _ _ _ (carve_obj k) F2 (in_map carve_obj _ _ Hk)) as (d & Hd & IZ).
  pose proof (proj1 (forallb_forall _ _) (ZD_chkD q) d Hd) as OKd.
  destruct d as [ [z lo] hi]. unfold in_zone in IZ. destruct IZ as (HU & L1 & L2 & R). destruct R as [R|[R1 R2]]; [lia|].
  assert (Z5 : (z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5)%nat).
  { clear -HU. destruct q; cbn [ZU In] in HU; lia. }
  destruct Z5 as [-> | [-> | [-> | [-> | [-> | ->] ] ] ] ]; cbn [zloF zhiF] in L1, L2; cbn beta iota in R1, R2.
  -   unfold img_okD in OKd. cbn [Nat.eqb] in OKd. apply andb_prop in OKd as [OK1 OK3]. apply andb_prop in OK1 as [OK1 OK2].
    apply Z.leb_le in OK1, OK2. left. split; [lia|]. apply Bool.orb_prop in OK3 as [OK3|OK3]; apply Z.leb_le in OK3; lia.
  - right. left. lia.
  - right. right. left. lia.
  - apply (chunk_zoneF A rho tp md p n a HA HL : (fun P => P) _). pose proof (N8_facts n) as NF. destruct (blkF_geom A rho tp md p n HA HL HHI) as (_ & _ & N1 & _). specialize (NF N1). lia.
  -
    assert (QNE : aa_q_thread A <> []) by (clear -QC HU; destruct q; cbn [ZU In] in HU; [exact (proj1 QC) | exfalso; lia | exact (proj1 QC)]).
    pose proof (qF A rho tp md p n HA HL) as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QF). specialize (QF QNE).
    destruct QF as (_ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). unfold kQuarantineBatchSize in S2. unfold lastq in R1, R2.
    do 3 right. left. lia.
  -
    assert (CI : aa_cache_inited A = true /\ cache24 A <> []) by (clear -QC HU; destruct q; cbn [ZU In] in HU; [exfalso; lia | exact (proj2 QC) | exact (proj2 (proj2 QC))]).
    pose proof (cF A rho tp md p n HA HL (proj1 CI) (proj2 CI)) as CF. cbn zeta in CF. destruct CF as (_ & _ & _ & _ & _ & X & _).
    rewrite kSpaceSize_val. change (2 ^ 32) with 4294967296 in *. change (2 ^ 28) with 268435456 in X. do 3 right. left. lia.
Qed.
End NFSZ.

Definition same_rng (o o' : sobj) : bool := ltac2:(tb__ "0|0|
S15S15S2cS26Vo;A1S26Vo';A1A2S2cS28Vo;A1S28Vo';A1A2A2S2cS27Vo;A1S27Vo';A1A2A2").
Lemma same_rng_range : ltac2:(tb__ "0|0|
S25S24S24S4S12S45R2R1A2S16A3S4S14S0S0A2S23R4R3A2S23R4R2A2A3F_;Fo';Fo;Frho;").
Proof.
  intros rho o o' H. unfold same_rng in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1, H2, H3. unfold obj_range, obj_lo_of, obj_hi_of. rewrite H1, H2, H3. reflexivity.
Qed.
Definition rng_below (k : positive) (o : sobj) : bool := ltac2:(tb__ "0|0|
S15S15S2bVk;S26Vo;A1A2S2bVk;S28Vo;A1A2A2S2bVk;S27Vo;A1A2A2").
Lemma rng_below_agree : ltac2:(tb__ "0|0|
S1S25S25S24S2dR4R3R2A3S4S12S47R5R2A2S16A3S4S14S0S0A2S23R4R3A2S23R5R3A2A3F_;F_;Fo;Frho';Frho;Fk;").
Proof.
  intros k rho rho' o Hag H. unfold rng_below in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite <- (eval_agree k rho rho' _ Hag H1), (soff_agree k rho rho' _ Hag H2), (soff_agree k rho rho' _ Hag H3). reflexivity.
Qed.

Definition winpb (o : sobj) : bool := ltac2:(tb__ "0|9|
S22S12Lx;M0S26Vo;A1S0S13Lz;S1S1S12Li;R1S1S13Lp;S1S1S12Lp;R1S1S1S12Lp0;R1S1S13Lp1;S1S1S12Lp1;R1S1S13Lp2;M1G1G0S28Vo;A1S0G0S27Vo;A1S0S15S15SbS10S65A1R2A2SbR2R1A2A2SbR1Z0A2A2Lhi;S1S13Li0;M2S74S22S22S13Lb;La;M3Lop;M4G4S75G3Lop;M5G5S12S2S22S13La;Lw;Lsgn;M6S1S22S0S13Lk;M7Li0;Ll;M8X22x8Llo;G2G4G4G5G5G6G8X22x8X1x3Lp1;S13X1x3Lp0;S1S13Lp0;S13X1x3Lp;S13X1x3Li;G4G4G5G5G6S1S22G7Li;Ll;X22x8").
Definition rd_okb (nW : nat) (q : qvar) (o : sobj) : bool := ltac2:(tb__ "0|1|
S18S18S18S18S43S24S45Vo;A1M0S73S4cS24S4dS51Vq;A1A4A3S45Vo;S5bA2A2S45Vo;S5aA2A2S4aVo;A1A2S43S24G0S68S64VnW;A1A1A3A2").

Section RDZ.
Variables (A : AA) (rho : valuation) (tp0 : list word) (md0 : Model) (p n : Z).
Hypothesis HA : ltac2:(tb__ "0|0|
S4eS30VA;Vrho;Vtp0;Vmd0;A5").
Hypothesis HL : ltac2:(tb__ "0|0|
S42S14S0S0A2S19S0S0Vp;Vn;A4S36VA;A1A3").
Hypothesis HHI : blk_cls p n.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S4S0S70Q40S2aVrho;PcA2A2Vp;A3").
Variables (t : Z) (jv : junkF).
Hypothesis Ht : ltac2:(tb__ "0|2|
S3S3S8Z0Vt;A2S9Vt;Z100A2A2S3S4S0SdVt;Z4A2Z1A3S3S1fS21S30S29Vrho;A1A2M0S20ScVp;Z10A2U4M1S52Vt;Vn;A2A3A2S1fG0S20ScVp;ZcA2G1SdVn;SeZ2Z20A2A2A3A2A2A2A2").
Hypothesis Hjv : ltac2:(tb__ "0|9|
S3S3S8Z0M0S53Vjv;A1M1A2S9G1SeZ2Z40A2M2A2A2S3S3S8G0S56Vjv;A1M3A2S9G3G2A2A2S3S3S8G0S55Vjv;A1M4A2S9G4G2A2A2S3S3S8G0S54Vjv;A1M5A2S9G5G2A2A2S3S1fS21S30S29Vrho;A1A2M6S20SaS4fZ48A2U8M7G1A3A2S3S1fG6S20SaS38S32VA;A1A1M8Zae0A2G7G3A3A2S4S17S33A1S39VA;A1S1cS33A1A3S3S1fG6S20SaG8Z58A2G7G4A3A2S1fG6S20SaG8Z60A2G7G5A3A2A2F_;A2A2A2A2A2A2").
Variables (nW : nat) (q : qvar).
Hypothesis QC : qcond q A.
Let rho1 : valuation := ltac2:(tb__ "0|0|
S57VA;Vrho;Vp;Vn;Vt;Vjv;A6").
Variable rhoE : valuation.
Hypothesis HAG : ltac2:(tb__ "0|0|
S2dS31Vrho1;VrhoE;A3").
Hypothesis HTOP : top_high A rhoE.
Hypothesis HDEP : ltac2:(tb__ "0|0|
S8S71Q40S2aVrhoE;S66A2A2S10S65A1A2").
Hypothesis HCH : ltac2:(tb__ "0|0|
S72S2fS2eVrhoE;A1S67S64VnW;A1A1A3").

Lemma BNDz : ltac2:(tb__ "0|1|
S3S76Vp;S4bVn;A1M0A2S3S8Z1Vn;A2S3S9SaVp;G0A2Z7fffff800000A2S3S8Vn;G0A2S8Z8G0A2A2A2A2A2").
Proof.
  pose proof (blkF_geom A rho tp0 md0 p n HA HL HHI) as (B1 & _ & B3 & B4 & _). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (N8_facts n B3) as (N1 & _ & N3 & _). repeat split; try assumption; lia.
Qed.
Lemma R_blk1 : ltac2:(tb__ "0|0|
S4S14S0S0A2S23Vrho1;S5aA2S19S0S0Vp;SaVp;S4bVn;A1A2A4A3").
Proof.
  pose proof BNDz as (B1 & B2 & B3 & B4 & B5). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. unfold O_blkN, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite soff_lit_small by lia. rewrite (soff_of_val rho1 vN8 (N8 n)); [| change (eval rho1 vN8) with (Z_to_bv 64 (N8 n)); apply u64_lit; lia | lia].
  change (eval rho1 (SVar 12)) with (rw rho 12%positive). rewrite Hp12. f_equal; lia.
Qed.
Lemma R_sh1 : ltac2:(tb__ "0|1|
S4S14S0S0A2S23Vrho1;S5bA2S19S0S0S62Vp;A1M0SaG0S11S4bVn;A1Z8A2A2A4A3").
Proof.
  pose proof BNDz as (B1 & B2 & B3 & B4 & B5). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. unfold O_sh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  pose proof (Z.div_pos (N8 n) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (N8 n) 8 (N8 n) ltac:(lia) ltac:(lia)).
  rewrite soff_lit_small by lia. rewrite (soff_of_val rho1 vN8g (N8 n / 8)); [| change (eval rho1 vN8g) with (Z_to_bv 64 (N8 n / 8)); apply u64_lit; lia | lia].
  assert (E : bv_unsigned (eval rho1 shb) = Sh p).
  { cbn [eval shb]. change (rw rho1 12%positive) with (rw rho 12%positive). rewrite add_val, srl_val, !u64_lit by (unfold SHADOW_OFF; lia). rewrite Hp12. change (3 mod 64) with 3.
    rewrite Z.shiftr_div_pow2 by lia. unfold Sh, SHADOW_OFF. pose proof (Z.div_lt_upper_bound p (2 ^ 3) (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos p (2 ^ 3) ltac:(lia) ltac:(lia)). rewrite Z.mod_small by lia. reflexivity. }
  rewrite E. f_equal; lia.
Qed.

Theorem rd_zone : ltac2:(tb__ "0|1|
S24S4S12S49VnW;Vq;R1A3S16A3S4S12S47S31R2A2S16A3S0S3S8S1aS0S0S23VrhoE;R4A2M0A3R1A2S9R1S1dS0S0G0A3A2A2S46VA;R2A2F_;Fa;F_;F_;Fo;").
Proof.
  intros o Hok Hb a Ha. rewrite (rng_below_agree GW rho1 rhoE o HAG Hb) in Ha.
  pose proof BNDz as (B1 & B2 & B3 & B4 & B5). unfold blk_geo in B1.
  unfold rd_okb in Hok. apply Bool.orb_prop in Hok as [Hok|Hok]; [apply Bool.orb_prop in Hok as [Hok|Hok]; [apply Bool.orb_prop in Hok as [Hok|Hok]; [apply Bool.orb_prop in Hok as [Hok|Hok]|]|]|].
  - apply existsb_exists in Hok as (o' & Ho' & Hs). rewrite (same_rng_range rho1 o o' Hs) in Ha.
    apply in_map_iff in Ho' as (k & <- & Hk). exact (nfs_zoneF A rho tp0 md0 p n HA HL HHI Hp12 t jv Ht Hjv q QC k Hk a Ha).
  - rewrite (same_rng_range rho1 o O_sh Hok), R_sh1 in Ha. cbn [fst snd] in Ha. unfold zoneF. cbn zeta. do 5 right. left.
    pose proof (Sh_in_band p ltac:(unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1; lia)) as S1. pose proof (Sh_in_band (p + N8 n) ltac:(unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1; lia)) as S2.
    assert (S3 : Sh p + N8 n / 8 <= Sh (p + N8 n)).
    { unfold Sh. pose proof (N8_facts n B2) as (_ & _ & _ & N4). rewrite <- N4 at 2. rewrite Z.div_add by lia. lia. }
    lia.
  - rewrite (same_rng_range rho1 o O_blkN Hok), R_blk1 in Ha. cbn [fst snd] in Ha. apply (chunk_zoneF A rho tp0 md0 p n a HA HL). lia.
  -
    unfold winpb in Hok. destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in Hok.
    destruct ob as [| v | | | | | | ]; try discriminate. destruct v as [v|v|]; try discriminate. do 3 (destruct v as [v|v|]; try discriminate).
    destruct olo as [lo| | | | | | | ]; try discriminate. destruct ohi as [hi| | | | | | | ]; try discriminate.
    apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2]. apply Z.leb_le in H1, H2, H3. unfold free_depth in *.
    rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha.
    assert (E10 : rw rho1 10%positive = rw rhoE 10%positive) by (apply (proj1 HAG); unfold GW; lia). rewrite E10 in Ha.
    unfold top_high in HTOP. unfold zoneF. cbn zeta. do 6 right. lia.
  -
    apply existsb_exists in Hok as (o' & Ho' & Hs). rewrite (same_rng_range rho1 o o' Hs) in Ha.
    assert (LNK : Forall (fun o => bv_unsigned (rw rhoE 10%positive) + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs (Wcan nW))).
    { unfold unwind_objs. destruct (Wcan nW) as [|l W'] eqn:EW; [constructor|].
      unfold chain_pre in HCH. cbn [app] in HCH.
      pose proof (Forall_inv HCH) as C0. pose proof (Forall_inv (Forall_inv_tail HCH)) as C1.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HCH))) as C2. do 3 apply Forall_inv_tail in HCH.
      cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
      pose proof (urange (rw rhoE 10%positive)). rewrite Z.mod_small in C1 by lia.
      eapply Forall_impl; [|apply (chain_facts_bases rhoE (SVar 28) (l :: W') HCH); cbn [eval]; lia].
      intros o0 (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia. }
    pose proof (proj1 (Forall_forall _ _) LNK o' Ho') as (L1 & L2 & L3).
    assert (WF' : rng_below GW o' = true).
    { unfold rng_below in Hb |- *. unfold same_rng in Hs. apply andb_prop in Hs as [Hs S3]. apply andb_prop in Hs as [S1 S2].
      apply sv_eqb_sound in S1, S2, S3. rewrite <- S1, <- S2, <- S3. exact Hb. }
    rewrite <- (rng_below_agree GW rho1 rhoE o' HAG WF') in Ha.
    destruct o' as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in L1, L2, L3. subst olo ohi. rewrite obj_range_mk in Ha by lia. cbn [fst snd] in Ha.
    unfold top_high in HTOP. unfold free_depth in HDEP. unfold zoneF. cbn zeta. do 6 right. lia.
Qed.
End RDZ.
End F0A_dzone.

