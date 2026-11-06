(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv F0A_instG i9 je.

(* [comment removed for export] *)
Module F0T_minstG.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "FcsrFrm0"; "mkSS"; "sprop"; "swf"; "SVar"; "valuation"; "DUnknown"; "SLit"; "agree_below"; "cell"; "mkObj"; "rw"; "sprop_below"; "ss_objs"; "@Corelib.Init.Datatypes"; "app"; "cons"; "nil"; "None"; "bool"; "false"; "true"; "list"; "prod"; "Some"; "length"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates"; "MIDPC"; "regs_mid"; "stack_win_mid"; "Pre_mid"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "NRT"; "O_pad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "FACTS_Tg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "O_sh"; "RT_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "mkA"; "unwind_objs"; "ustop"; "KcA"; "free_depth"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "tol_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "instG_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG.StatesMG"; "sd_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "JT"; "objs_le"; "@Stdlib.Lists.List"; "forallb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section StatesMG.
Variable khi : bool.
Variables (W : list ulink) (st : ustop) (NVl : list carve_spec) (VF : list sprop).
Let PREOBJS : list sobj := ltac2:(tb__ "0|0|
S11S0S25S10S0S37VW;A1S10S0S11S0ScS6PcA1S9Z0A1S6PdA1S12SbA1S8A5S12S0A1A3S35A3A3A3").
Let PREFACTS : list sprop := ltac2:(tb__ "0|0|
S10S4S38S17S4A1Lst;Vst;S3cS3cX38x2S3bS3aA1A3").
Definition sb_mg : sstate := ltac2:(tb__ "0|0|
S3S23S24S22S2S13S1A1S10S0VPREOBJS;S21S1cS0S1dS10S1cS28VNVl;A3A4A3VPREFACTS;S1eS15A9").
Definition sc_mg : sstate := ltac2:(tb__ "0|0|
S3S23S24S22S2S13S1A1S10S0S10S0VPREOBJS;S21S1cS0S1dS10S1cS28VNVl;A3A4A3S11S0S2eS12S0A1A3A3VPREFACTS;S1eS15A9").
Definition sd_mg : sstate := ltac2:(tb__ "0|1|
S3S23S24S22S2S13S1A1S10S0S10S0S10S0VPREOBJS;S21S1cS0S1dS10S1cS28VNVl;A3A4A3S11S0S2eS12S0A1M0A3A3S11S0S29G0A3A3VPREFACTS;S1eS15A9").
Definition se_mg : axst := ltac2:(tb__ "0|0|
S36S3eS43S2aVkhi;VVF;A2A2S12S18S1S1A2A1A2").
End StatesMG.

Definition PMID_g (khi : bool) (W : list ulink) (st : ustop) (VOBJl : list sobj) (VF : list sprop) : axst := ltac2:(tb__ "0|0|
S36S3S23S24S22S2S13S1A1S10S0S10S0S11S0S25S10S0S37VW;A1S35A3A3S2fA3VVOBJl;A3S2aVkhi;VVF;A2S1eS15A9S12S18S1S1A2A1A2").

Section INSTMG.
Let segs : list Segment := segsA.
Variable khi : bool.
Let nW : nat := 0%nat. Let st : ustop := UStopLe. Variable NVl : list carve_spec. Variable VF : list sprop.
Let W : list ulink := Wcan nW.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (A : AA) (Kc : KcA) : jpredA := J_free_tol_preT A Kc.

Hypothesis Wb : ltac2:(tb__ "0|0|
S1fS14S5S31VW;Vst;VNVl;A3A1S16A3").
Hypothesis Wc : ltac2:(tb__ "0|0|
S1fS14S5S32VW;Vst;VNVl;A3A1S16A3").
Hypothesis Wd : ltac2:(tb__ "0|0|
S1fS14S5S33VW;Vst;VNVl;A3A1S16A3").
Hypothesis Fe : ltac2:(tb__ "0|0|
S1fS14S49S4SeS1eA1S2aVkhi;VVF;A2A3S16A3").
Hypothesis AXI : ltac2:(tb__ "0|0|
S1fS1bS2cA1S3fS34Vkhi;VW;Vst;VNVl;VVF;A5S40VnW;S1aS1cVNVl;A2A2A2S19S2cS30Vkhi;VW;Vst;S21S1cS0S1dVNVl;A4VVF;A5A2A3").

Theorem g_instantiate_mid : ltac2:(tb__ "0|2|
S44S39S7S7S17S4aQ40M0A1A1S3dS27S27S27SaS1eR7R6A3S41Vkhi;VW;Vst;VNVl;VVF;R7R4R3R2S46S45RaA1A1AaS2bVsegs;VJ;RbRaA2S26VW;Vst;A2R9R7R6A6S20S42RaR9A2S20S2bVsegs;S47RcRbR9A3S30Vkhi;VW;Vst;S21S1cS0S1dVNVl;A4VVF;A5M1R9R8R7A6S48R9S4bG0SdR9PaA2A2SfS2dG1A1A1A3A2A2F_;F_;F_;Fn8;Fn;Fp;Fw;Ftp;Frho1;Frho;FKc;FA;").
Proof.
  intros A Kc rho rho1 tp w p n n8 Hag2 IFF H.
  assert (Hag : agree_below NF rho rho1) by (eapply agree_below_le; [|exact Hag2]; cbv; discriminate).
  destruct IFF as [E12 E13 E105 E106 Hpn Hcarve Hzone Hpd Hsh Hpadm Hfacts Hrig].
  split; [exact (Hrig rho (agree_below_vals _ _ _ Hag))|]. unfold blk_geo, IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in Hpn.
  pose proof H as [HsmA HJ]. destruct HJ as ((HA & HU & HL & HK & Htp & HB & Htop) & HKM & HPRES).
  pose proof HA as (HG & _).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & _).
  pose proof (topG_range (aa_geom A)) as TR. set (TOP := topG (aa_geom A)) in *.

  assert (H1 : SPA segs (J A Kc) (Pre_mid W st) rho1 tp w).
  { eapply SPA_agree; [| |exact H]; [eapply agree_below_le; [|exact Hag2]; cbv; discriminate | apply (JTr_agree A Kc rho rho1); exact Hag]. }
  clear H HsmA.
  assert (E24 : rw rho1 24%positive = rw rho 24%positive) by (symmetry; apply (proj1 Hag); unfold NF; lia).

  pose proof (proj2 H1) as ((_ & _ & _ & _ & _ & _ & Htop1) & _).
  assert (TOPlo : TOP <= fst (obj_range rho1 stack_win)) by exact Htop1.

  assert (H2 : SPA segs (J A Kc) (mkAX (sa_m W st) [] base_sv) rho1 tp w) by exact H1.
  clear H1.

  pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
  assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn [ss_facts sa_m]; apply in_or_app; right; cbn; tauto).
  destruct (stack_winm_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
  assert (LNK : Forall (fun o => TOP + 16 <= bv_unsigned (eval rho1 (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { constructor. }

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
  { unfold se_mg. change (mkA (with_facts (sd_mg W st NVl) (FACTS_Tg khi VF)) []) with (ax_with_facts (mkAX (sd_mg W st NVl) [] base_sv) (FACTS_Tg khi VF)).
    eapply SPA_refacts; [exact H5 | exact Fe |].
    intros Hold. unfold FACTSc.
    assert (HP : Forall (holds rho1) (tol_facts ++ pre_facts free_depth)).
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

  split; [exact (SPA_JT_intro A Kc (PMID_g khi W st (map carve_obj NVl) VF) rho1 tp w H7)|].
  clear H6 H7. unfold objs_le, PMID_g, mkA. cbn [ss_objs ax_S]. rewrite <- NRT_ok.
  assert (CARVE : forall l, incl l (NRT ++ NVl) -> Forall (fun o => snd (obj_range rho1 o) <= bv_unsigned (rw rho1 10%positive)) (map carve_obj l)).
  { intros l Hl. apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk0). pose proof (Hl k Hk0) as Hk.
    pose proof (proj1 (Forall_forall _ _) Hzone k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) Hcarve k Hk) as Ck.
    destruct k as [[[base lo] hi] cs]. unfold spec_zone, zone_ok in Zk. unfold carve_ok in Ck. cbn zeta in Zk, Ck.
    destruct Ck as (C1 & C2 & C3 & _). cbn [carve_obj]. unfold carved. rewrite obj_range_mk by lia. cbn [fst snd].
    unfold IMG_HI in *. lia. }
  repeat rewrite <- app_assoc. cbn [app]. apply Forall_cons; [change (obj_range rho1 stack_win_mid) with (obj_range rho1 stack_win); lia|].
  unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
  apply Forall_cons; [rewrite obj_range_mk by lia; cbn [fst snd eval]; rewrite u64_lit by lia; lia|].
  apply Forall_cons; [rewrite obj_range_mk by lia; cbn [fst snd eval]; rewrite u64_lit by lia; lia|].
  apply Forall_app. split; [apply CARVE; apply incl_appl; apply incl_refl|].
  apply Forall_cons.
  { unfold O_sh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
    rewrite Hshb. unfold vN8g. rewrite (soff_var rho1 106%positive (n8 / 8) E106) by (split; [lia | apply Z.div_lt_upper_bound; lia]). lia. }
  apply Forall_cons.
  { unfold O_blkN, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
    unfold vN8. rewrite (soff_var rho1 105%positive n8 E105) by lia. cbn [eval]. rewrite Ep. lia. }
  apply CARVE. apply incl_appr. apply incl_refl.
Qed.
End INSTMG.
End F0T_minstG.

(* [comment removed for export] *)
Module SpineCallocE.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "leafA"; "la_state"; "ax_setS"; "ax_X"; "mkLeafA"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "nil"; "list"; "prod"; "pair"; "option"; "Some"; "app"; "false"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "valuation"; "ss_next"; "ss_facts"; "swf"; "SLit"; "sobj"; "SVar"; "sprop_below"; "SPBranch"; "rw"; "SPNot"; "SPUle"; "ss_objs"; "rm"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "check_cfgA"; "vna_state"; "SPfamEA"; "enodeA"; "to_enodeA"; "vmeasA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "LQA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "JGb"; "E5s1'"; "E5s2'"; "depot_onlyK"; "hd_link"; "tab1_ok"; "clsp_e"; "clsp_e31"; "@Stdlib.Lists.List"; "In"; "incl"; "forallb"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "AE_A"; "A_globals"; "Pre_callocI"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E3p"; "F_gen"; "C5m1"; "C5m2"; "C6m"; "C1g"; "V_CLS"; "C5b"; "C6"; "C6l"; "C7"; "C7p"; "C5c"; "E2a"; "E2b"; "E7c1"; "E7c2"; "C3"; "C5"; "C5d"; "C5e"; "C6b"; "E5s1"; "E5s2"; "E7p"; "E7q1"; "E7q2"; "V_ND"; "C2p"; "C2r"; "E5f"; "E5m1"; "E5m2"; "E6l"; "E6s"; "E6m"; "C2p0"; "C2r0"; "C8"; "C8p"; "E3r"; "E4d"; "E5j"; "E5n"; "E6j"; "O_U"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "creg_a"; "creg_b"; "n8e"; "sreg1"; "sreg2"; "F_cls"; "V_SIZE"; "BP"; "BR"; "F_pop"; "LLe"; "LPe"; "LRe"; "LUe"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "V_CNT"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "modulo"; "mul"; "pow"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "tab_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "P0c"; "E_s1"; "F_hi_p"; "F_lo_p"; "F_s1"; "s1_exits"; "sw_s1"; "s1_cuts_pcs"; "stop_le"; "stop_pc"; "E_pre"; "s1_cuts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2"; "rho_c"; "s_sw"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "memset_entryA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "X2"; "X2r"; "X1"; "X1b"; "X1c"; "X1r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2"; "E2a'"; "E2b'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8"; "E7c1'"; "E7c2'"; "E7q1'"; "E7q2'"; "a0e7"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI"; "FACTSe"; "F_hi_e"; "F_lo_e"; "Jc"; "P0e"; "sa_c"; "sb_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4"; "Y7"; "Y1"; "Y2"; "Y3"; "Y4"; "Y5"; "Y6"; "sep_geom"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "list_set"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zero_covered"; "zobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE.E"; "HDE_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1"; "d_k"; "dp_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6"; "a0e2"; "len1e"; "len2e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7"; "len3e"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S29Se0VCST;R1A2Se0SfaR2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S57VAInv;VW;Vst;VA;VKc;S21PcA1A6").
Hypothesis law_die : ltac2:(tb__ "0|0|
S4bS1bS11S49Q40A1A1Sf3VAInv;R4R3R2R1A4Se1Se3Vsegs;S28R4A1A2Se2Z17fbdcU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Lemma ecfg_cut : ltac2:(tb__ "0|1|
S18S11S29A1S2aS11S2dA1M0G0S39S37OF_;S11S49Q40A1A1S6S1bS3aVsegs;R8R5A3S2dS44S2dR1R9A3S48RbS1cS5S31R2A1A1A1A2F_;Fn;S0SdS2fVsegs;RcRbRaR9R8A6SfA3S2dS1bS44S2dR2RbA3S36Vsegs;S38Vsegs;RbS31R3A1R2R9A5S37S2S32Vsegs;S5cS2dS33S34RcA1ReA4RaS35R4R3A2R1A5RbR1A1A2Lw;A3F_;Frho';FE;S44S2dS2eR6Z1S1fZ0A1A3RbA3S36Vsegs;S38Vsegs;RaR7R6R8A5R9A3F_;F_;F_;F_;F_;Frho;FC;Ftp;FQ;FJx;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g cuts exits Jx Q tp C rho HS HN HC HE HI. exact (cfg_complete_autoA segs fuel cutpcs g cuts exits Jx Q tp HS HN HC HE (mkVNA C 1 (SLit 0)) rho HI). Qed.

Section ECall.
Variables (Cst T D : axst) (s : wsub) (R : list sobj) (sd : wsub).
Variables (Pre : axst) (Posts : list leafA) (Pret : sstate).
Hypothesis HPosts : ltac2:(tb__ "0|0|
S0S11S8A1VPosts;SeS8ScSc9VPret;A1Sf4A2S10S8A1A3A3").
Hypothesis Hsum : ltac2:(tb__ "0|0|
S39S1bS11S49Q40A1A1S3aScaSdbR3A3S36ScaS38ScaR4VPre;R3R2A5S3bScaR4SdbR3R2VPosts;A6A3F_;Ftp;Frho;FJx;").
Hypothesis He : ltac2:(tb__ "0|1|
S0S14S11S20A1M0A1ScdVCst;VPre;Vs;A3S15G0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0SdSccVCst;VPre;Vs;VR;S5cS8S6S9VPosts;A4A5SfA3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S6SceVs;VPre;Sc9VPret;A1VCst;VR;A5VT;A3").
Hypothesis FBC : ltac2:(tb__ "0|1|
S0SdS46S19S22S1cS5VCst;A1M0A1A1S1dG0A1A3SfA3").
Hypothesis FBT : ltac2:(tb__ "0|0|
S0SdS46S19S22S1cS5VT;A1A1A1S1dS5VCst;A1A1A3SfA3").
Hypothesis ENT : ltac2:(tb__ "0|0|
S0SdS7ScbVT;S1dS5VCst;A1A1A2VD;Vsd;A3SfA3").
Hypothesis SID : ltac2:(tb__ "0|0|
S0SdS4dVsd;S2bA2SfA3").
Hypothesis NXC : ltac2:(tb__ "0|0|
S48S2bS1cS5VCst;A1A1A2").
Hypothesis NPre : ltac2:(tb__ "0|0|
S0S2aS1cS5VPre;A1A1SdbA3").

Lemma ecall_gen : ltac2:(tb__ "0|1|
S4bS4eS1bS11S49Q40A1A1M0S1bS37OF_;S59VW;Vst;A2S4fR6A1S1bG0S36Vsegs;S38Vsegs;S3cVW;Vst;RaR9R8A5VD;R2R1A5R5A3FtpX;FrhoX;S36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5VCst;R5R6A5R4A3F_;F_;F_;FQ;FrhoE;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp rhoE Q HUS HKc HD.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  set (Jf := (fun (_ : valuation) t tr md => JGb W st A Kc rho rhoE t tr md) : jpredA).
  assert (Jf_st : stableA segs NF Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  apply (etriple_pre_pure segs _ _ (Forall (holds rhoE) (ss_facts (ax_S Cst)))).
  { intros w Hw. exact (SPA_facts_hold segs _ rhoE Cst tp w Hw). }
  intros HFC.
  apply (call_completeA segs (JGb W st A Kc rho) Jf Jf (JGb W st A Kc rho) Cst Pre s R Posts Q rhoE tp He Hchk).
  - intros rho1 tp1. rewrite NPre. exact (Hsum Jf rho1 tp1 Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ'].
    eapply agree_below_le; [exact NXC | exact (proj1 HLK)].
  - intros L rho' tpL HinL Hag. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state]. rewrite HT.
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HD (rho_sub rho' sd) tpL)].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (ax_with_facts T (ss_facts (ax_S Cst))) D sd rho' tpL w ENT SID HST).
    apply SPA_refacts; [exact Hw | exact FBT |]. intros _.
    exact (Forall_holds_agree _ rhoE rho' _ Hag FBC HFC).
Qed.
End ECall.

Section E_spine_s1c.
Hypothesis WC1 : ltac2:(tb__ "0|0|
S0SdS1eS5S62VW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis DC1 : ltac2:(tb__ "0|3|
S29S1Sa2Z0R1A2Sa2R1Z7A2A2S0S14S12S11S12S1aS1aA2A1M0S11S19A1M1A2M2A1S58S5SacVW;Vst;Vtmax;R2A4A1S5S62VW;Vst;Vtmax;A3A1A2S15G2S13G0G1SfcR2A1S5eA4A2A3F_;Fk;").
Hypothesis WE1 : ltac2:(tb__ "0|0|
S29S1Sa2Z0R1A2Sa2R1Z8A2A2S0SdS1eS5SacVW;Vst;Vtmax;R2A4A1A1SfA3F_;Fk;").
Hypothesis DE1 : ltac2:(tb__ "0|3|
S29S1Sa2Z0R1A2Sa2R1Z8A2A2S0SdS14S12S11S12S1aS1aA2A1M0S11S19A1M1A2M2A1SdLx;S58S5Sb5VW;Vst;Vtmax;R2A4A1S5SacVW;Vst;Vtmax;R2A4A1A2G2G2SdLp;R1G0G1SfdR5R2A2Ll;Ld;X12x1Lp;S17X14x2SfA3F_;Fk;").
Hypothesis HSW : stopJ_sw W st.
Hypothesis HUS : stopJ_stable W st.
Hypothesis Wa : ltac2:(tb__ "0|0|
S0SdS1eSe9VW;Vst;A2A1SfA3").
Hypothesis Da : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S52S50VW;Vst;A3A1Se9VW;Vst;A2A2S15G3S13G1G2SeG0S13S1aS1aS21P18A1S1fSf9A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S0SdS1eSeaVW;Vst;A2A1SfA3").
Hypothesis Fbh : ltac2:(tb__ "0|0|
S0SdS46S19S22SdfA1S16S19Se4VW;Vst;A2Se5A3A3SfA3").
Hypothesis Fbl : ltac2:(tb__ "0|0|
S0SdS46S19S22SdfA1S16S19Se4VW;Vst;A2Se6A3A3SfA3").
Hypothesis ENTh : ltac2:(tb__ "0|0|
S0SdS7Se8VW;Vst;Se5A3SabVW;Vst;SadA3Sb8A3SfA3").
Hypothesis ENTl : ltac2:(tb__ "0|0|
S0SdS7Se8VW;Vst;Se6A3SabVW;Vst;SaeA3Sb8A3SfA3").

Lemma es1c_exits : ltac2:(tb__ "0|1|
S4bS4eS1bS11S49Q40A1A1S37OF_;M0G0S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R7R6Sb7R5A1A5S62VW;Vst;Vtmax;A3R1R4A5R3A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R8R7Sb7R6A1A5SacVW;Vst;Vtmax;Z8A4R1R5A5R4A3FrhoE;S6S1bS44S6R2Sb0VnW;Vst;Vtmax;A3A3S36Vsegs;S38Vsegs;S5bVW;Vst;RbRaSb7R9A1A5R3R2R8A5S37S2R7R1A1R8R1A1A2Lw';A3F_;FrhoE;FE;F_;F_;FR;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q R HC1 HSEC E rhoE HinE. unfold s1_exits in HinE. cbn [map] in HinE.
  assert (RS : forall k w, 0 <= k <= 8 -> SPA segs (JG W st A Kc (rho_c rho)) (E_pre W st tmax k) rhoE tp w ->
                            SPA segs (JG W st A Kc (rho_c rho)) (E_s1 W st tmax k) rhoE tp w).
  { intros k w Hk Hw. apply (e_pre_s1 nW st tmax WE1 DE1 k A Kc (rho_c rho) tp w rhoE Hk); [|exact Hw].
    destruct Hw as [_ [Hag _]]. exact (rc_prod A rho rhoE Hag). }
  destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]].
  9: { eapply etriple_conseq; [intros w Hw; apply (RS 8 w ltac:(lia) Hw) | intros w Hw; right; exact Hw | apply HSEC]. }
  all: eapply etriple_conseq; [intros w Hw; eapply (e_s1_c1g nW st tmax WC1 DC1 _ A Kc (rho_c rho) tp w rhoE); [|apply RS; [|exact Hw]]; lia | intros w Hw; right; exact Hw | apply HC1].
Qed.

Section LE.
Hypothesis NXhi : ltac2:(tb__ "0|0|
S48S2bS1cS5SabVW;Vst;SadA3A1A1A2").
Hypothesis NXlo : ltac2:(tb__ "0|0|
S48S2bS1cS5SabVW;Vst;SaeA3A1A1A2").
Hypothesis ECert1 : ltac2:(tb__ "0|2|
S0SdS2fS2cUfa0SeS29Z40bacS10S29A1A3S2bS5cS6S2dS6S2eR1Z1S1fZ0M0A1M1A3Lc;Sb6VnW;Vst;A2A4S5cS6S2dS6S2eR1G0G1A3Le;Sb0VnW;Vst;Vtmax;A3A4A6SfA3").
Theorem espine_s1c : ltac2:(tb__ "0|1|
S4bS4eS1bS11S49Q40M0A1A1S37OF_;S4fR4A1Sa3Sa5S4aG0S24R4PcA2A2S4aG0S24R4PdA2A2A2Sa6Z2Z40A2A2S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R8R7Sb7R6A1A5S62VW;Vst;Vtmax;A3R1R5A5R4A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R9R8Sb7R7A1A5SacVW;Vst;Vtmax;Z8A4R1R6A5R5A3FrhoE;S36Vsegs;S38Vsegs;Se7VW;Vst;R9R8A4S52S50VW;Vst;A3R7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HKc Hmul HC1 HSEC.
  eapply etriple_conseq; [intros w Hw; exact (c_front law_die nW st HSW HUS Wa Da Wb Fbh Fbl ENTh ENTl A Kc rho tp w Hmul Hw) | intros w Hw; exact Hw |].
  set (P0 := P0c W st (if Z_lt_dec (bv_unsigned (nwc rho)) 64513 then F_lo_p else F_hi_p)).
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs _ GW P0 (rhoM_of A (rho_c rho)) tp w Hw) | intros w Hw; exact Hw |].
  apply (ecfg_cut 4000%nat [0x40bac] GW (map (fun c => mkVNA c 1 (SLit 0)) (s1_cuts nW st)) (map (fun e => mkVNA e 0 (SLit 0)) (s1_exits nW st tmax))
           (JG W st A Kc (rho_c rho)) Q tp P0 _ (JG_stable nW st A Kc (rho_c rho) HUS HKc)).
  - intros n Hn. unfold s1_cuts in Hn. cbn [map] in Hn. destruct Hn as [<-|[<-|[]]]; cbn [vna_state]; [exact NXhi | exact NXlo].
  - exact ECert1.
  - intros E rhoE HinE. clear NXhi NXlo ECert1. apply in_map_iff in HinE. destruct HinE as (E0 & <- & HinE). cbn [vna_state].
    exact (es1c_exits A Kc rho tp Q _ HC1 HSEC E0 rhoE HinE).
  - unfold s1_cuts, P0. cbn [map]. destruct (Z_lt_dec _ _); [right; left; reflexivity | left; reflexivity].
Qed.
End LE.

Section PC.
Hypothesis NXpc : ltac2:(tb__ "0|0|
S6S44S6R1Sb2VnW;Vst;A2A3S48S2bS1cS5R2A1A1A2F_;Fc;").
Hypothesis ECert1pc : ltac2:(tb__ "0|2|
S0SdS2fS2cUfa0SeS29Z40bacS10S29A1A3S2bS5cS6S2dS6S2eR1Z1S1fZ0M0A1M1A3Lc;Sb2VnW;Vst;A2A4S5cS6S2dS6S2eR1G0G1A3Le;Sb0VnW;Vst;Vtmax;A3A4A6SfA3").
Hypothesis Est : st = UStopLeOrPc.
Hypothesis WPC : ltac2:(tb__ "0|2|
S11S19A1M0G0S44G0R2SeG0SadSeG0SaeS10G0A1M1A3A3A3S44G0R2SeG0Sb4VW;A1SeG0Sb3VW;A1G1A3A3A3S0SdS1eS5SabVW;Vst;S16S19R4R3A3A3A1A1SfA3F_;F_;Fsx;Ffx;").
Hypothesis DPC : ltac2:(tb__ "0|5|
S11S19A1M0G0S44G0R2SeG0SadSeG0SaeS10G0A1M1A3A3A3S44G0R2SeG0Sb4VW;A1SeG0Sb3VW;A1G1A3A3A3S0S14S12S11S12S1aS1aA2M2A1M3G0A2M4A1S58S5SabVW;Vst;R4A3A1S5SabVW;Vst;S16S19R4R3A3A3A1A2S15G4S13G3G0S10G2A1R3A4A2A3F_;F_;Fsx;Ffx;").
Hypothesis HWne : W <> [].
Theorem espine_s1c_pc : ltac2:(tb__ "0|1|
S4bS4eS1bS11S49Q40M0A1A1S37OF_;S4fR4A1Sa3Sa5S4aG0S24R4PcA2A2S4aG0S24R4PdA2A2A2Sa6Z2Z40A2A2S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R8R7Sb7R6A1A5S62VW;Vst;Vtmax;A3R1R5A5R4A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R9R8Sb7R7A1A5SacVW;Vst;Vtmax;Z8A4R1R6A5R5A3FrhoE;S36Vsegs;S38Vsegs;Se7VW;Vst;R9R8A4S52S50VW;Vst;A3R7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HKc Hmul HC1 HSEC.
  eapply etriple_conseq; [intros w Hw; exact (c_front law_die nW st HSW HUS Wa Da Wb Fbh Fbl ENTh ENTl A Kc rho tp w Hmul Hw) | intros w Hw; exact Hw |].
  set (fx := if Z_lt_dec (bv_unsigned (nwc rho)) 64513 then F_lo_p else F_hi_p).
  assert (Hfx : In fx [F_hi_p; F_lo_p]) by (unfold fx; destruct (Z_lt_dec _ _); cbn; tauto).
  apply (etriple_pre_pure segs _ _ (unwind_stopJ W st (rhoM_of A (rho_c rho)))).
  { intros w [_ HJ]. exact (proj1 (proj2 (proj2 (proj2 HJ)))). }
  intros HST.
  assert (HSX : exists sx, In sx [stop_pc W; stop_le W] /\ Forall (holds (rhoM_of A (rho_c rho))) sx).
  { unfold unwind_stopJ in HST. rewrite Est in HST. destruct W as [|l W'] eqn:EW; [contradiction HWne; reflexivity|]. rewrite <- EW in *.
    destruct (last_link (SVar 28) W) as [[bp nbp] pc] eqn:EL. destruct HST as [Hp|Hl].
    - exists (stop_pc W). split; [left; reflexivity|]. apply (stop_pc_holds nW). fold W. rewrite EL. exact Hp.
    - exists (stop_le W). split; [right; left; reflexivity|]. apply (stop_le_holds nW). fold W. rewrite EL. exact Hl. }
  destruct HSX as (sx & Hsx & Hholds).
  set (P0 := P0c W st (fx ++ sx)).
  apply etriple_conseq with (P := SPA segs (JG W st A Kc (rho_c rho)) P0 (rhoM_of A (rho_c rho)) tp) (Q := Q); [intros w Hw | intros w Hw; exact Hw |].
  { apply (SPA_withG_intro segs (J W st A Kc) GW P0 (rhoM_of A (rho_c rho)) tp w).
    change P0 with (ax_setS (P0c W st fx) (ax_S (P0c W st (fx ++ sx)))).
    eapply SPA_restate; [exact (WPC fx sx Hfx Hsx) | exact (DPC fx sx Hfx Hsx) | reflexivity | constructor | exact Hholds | exact Hw]. }
  assert (HinP : In P0 (s1_cuts_pcs nW st)).
  { unfold s1_cuts_pcs, P0. fold W. unfold fx in *. clear - Hfx Hsx. destruct Hsx as [<-|[<-|[]]]; destruct (Z_lt_dec _ _); cbn; tauto. }
  apply (ecfg_cut 4000%nat [0x40bac] GW (map (fun c => mkVNA c 1 (SLit 0)) (s1_cuts_pcs nW st)) (map (fun e => mkVNA e 0 (SLit 0)) (s1_exits nW st tmax))
           (JG W st A Kc (rho_c rho)) Q tp P0 _ (JG_stable nW st A Kc (rho_c rho) HUS HKc)).
  - intros n Hn. apply in_map_iff in Hn. destruct Hn as (c & <- & Hc). cbn [vna_state]. exact (NXpc c Hc).
  - exact ECert1pc.
  - intros E rhoE HinE. clear ECert1pc. apply in_map_iff in HinE. destruct HinE as (E0 & <- & HinE). cbn [vna_state].
    exact (es1c_exits A Kc rho tp Q _ HC1 HSEC E0 rhoE HinE).
  - apply in_map_iff. exists P0. split; [reflexivity | exact HinP].
Qed.
End PC.
End E_spine_s1c.

Section E_spine_s2.
Let Xa : axst := ltac2:(tb__ "0|0|
SaS6aVW;Vst;Vtmax;A3S5ScfVnW;Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
SaS6bVW;Vst;Vtmax;A3S5Sd0VnW;Vst;Vtmax;A3A1A2").
Hypothesis Cert2 : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z40d40S10S29A1A3S2bSeS6S62VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S6aVW;Vst;Vtmax;A3SeS6S6bVW;Vst;Vtmax;A3G0A3A3A6SfA3").
Hypothesis OVa : ltac2:(tb__ "0|0|
S0SdSa9P9dS8fVW;Vst;Vtmax;A3A2SfA3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S0SdSa9P9dS90VW;Vst;Vtmax;A3A2SfA3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S0SdSaaP9dS8fVW;Vst;Vtmax;A3Sc0Z208Sd6Sd7Sb9SbaSbbSb9SbcA1A1A1A1A1A1A5SfA3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S0SdSaaP9dS90VW;Vst;Vtmax;A3Sc0Z18U3eA5SfA3").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S0SdS1eS5ScfVnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S0SdS1eS5Sd0VnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S6aVW;Vst;Vtmax;A3A1S5ScfVnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS8fVW;Vst;Vtmax;A3S21S63A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S6bVW;Vst;Vtmax;A3A1S5Sd0VnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS90VW;Vst;Vtmax;A3S21S63A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis NXa : ltac2:(tb__ "0|0|
S0S2aS1cS5ScfVnW;Vst;Vtmax;A3A1A1S1cS5S6aVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S0S2aS1cS5Sd0VnW;Vst;Vtmax;A3A1A1S1cS5S6bVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fa : ltac2:(tb__ "0|0|
S44S19S23Sa7S1fZ200A1S21S78A1A3S1dS5S6aVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S44S19S25S23Sa7S1fZ200A1S21S78A1A3A1S1dS5S6bVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Ga : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S6aVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S6bVW;Vst;Vtmax;A3A1A1A3").
Hypothesis SKa : ltac2:(tb__ "0|1|
S0S11S12S12S1aS1aA2S1aA2M0A1S5cS20G0Sc2S27S5VXa;A1A1A4S5cS20G0Sc2S16S20SeS20Sb1S16S20S56VW;A1S51A3A3SdcA3A4A3").
Hypothesis SKb : ltac2:(tb__ "0|1|
S0S11S12S12S1aS1aA2S1aA2M0A1S5cS20G0Sc2S27S5VXb;A1A1A4S5cS20G0Sc2S16S20SeS20Sb1S16S20S56VW;A1S51A3A3SdcA3A4A3").
Hypothesis XXa : ax_X Xa = [].
Hypothesis XXb : ax_X Xb = [].
Hypothesis XFa : ltac2:(tb__ "0|0|
S45S19S16S19S16S19S16S19S55VW;Vst;A2S54S53A1A3SafA3S5eA3S1dS5VXa;A1A1A3").
Hypothesis XFb : ltac2:(tb__ "0|0|
S45S19S16S19S16S19S16S19S55VW;Vst;A2S54S53A1A3SafA3S5eA3S1dS5VXb;A1A1A3").
Hypothesis W1a : ltac2:(tb__ "0|0|
S0SdS1eS5Sc5VXa;A1A1A1SfA3").
Hypothesis W1ba : ltac2:(tb__ "0|0|
S0SdS1eS5Sc6VXa;A1A1A1SfA3").
Hypothesis W1ca : ltac2:(tb__ "0|0|
S0SdS1eS5Sc7VXa;A1A1A1SfA3").
Hypothesis W2a : ltac2:(tb__ "0|0|
S0SdS1eS5Sc3VXa;A1A1A1SfA3").
Hypothesis W1ra : ltac2:(tb__ "0|0|
S0SdS1eS5Sc8VXa;A1A1A1SfA3").
Hypothesis W2ra : ltac2:(tb__ "0|0|
S0SdS1eS5Sc4VXa;A1A1A1SfA3").
Hypothesis W1b : ltac2:(tb__ "0|0|
S0SdS1eS5Sc5VXb;A1A1A1SfA3").
Hypothesis W1bb : ltac2:(tb__ "0|0|
S0SdS1eS5Sc6VXb;A1A1A1SfA3").
Hypothesis W1cb : ltac2:(tb__ "0|0|
S0SdS1eS5Sc7VXb;A1A1A1SfA3").
Hypothesis W2b : ltac2:(tb__ "0|0|
S0SdS1eS5Sc3VXb;A1A1A1SfA3").
Hypothesis W1rb : ltac2:(tb__ "0|0|
S0SdS1eS5Sc8VXb;A1A1A1SfA3").
Hypothesis W2rb : ltac2:(tb__ "0|0|
S0SdS1eS5Sc4VXb;A1A1A1SfA3").
Variables sa sra sb srb : wsub.
Hypothesis ENTa : ltac2:(tb__ "0|0|
S0SdS7Sc3VXa;A1S81VW;Vst;Vtmax;A3Vsa;A3SfA3").
Hypothesis ENTra : ltac2:(tb__ "0|0|
S0SdS7Sc4VXa;A1S82VW;Vst;Vtmax;A3Vsra;A3SfA3").
Hypothesis ENTb : ltac2:(tb__ "0|0|
S0SdS7Sc3VXb;A1S81VW;Vst;Vtmax;A3Vsb;A3SfA3").
Hypothesis ENTrb : ltac2:(tb__ "0|0|
S0SdS7Sc4VXb;A1S82VW;Vst;Vtmax;A3Vsrb;A3SfA3").
Hypothesis SIDa : ltac2:(tb__ "0|0|
S0SdS4dVsa;S2bA2SfA3").
Hypothesis SIDra : ltac2:(tb__ "0|0|
S0SdS4dVsra;S2bA2SfA3").
Hypothesis SIDb : ltac2:(tb__ "0|0|
S0SdS4dVsb;S2bA2SfA3").
Hypothesis SIDrb : ltac2:(tb__ "0|0|
S0SdS4dVsrb;S2bA2SfA3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0SdS46S19S22S1cS5S81VW;Vst;Vtmax;A3A1A1A1S16S19S94S98A3A3SfA3").
Hypothesis FBr : ltac2:(tb__ "0|0|
S0SdS46S19S22S1cS5S82VW;Vst;Vtmax;A3A1A1A1S94A3SfA3").

Hypothesis NXC1g : ltac2:(tb__ "0|0|
S48S2bS1cS5S62VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert2 : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z40d40S10S29A1A3S2bSeS2dS2eS62VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS6aVW;Vst;Vtmax;A3G0G1A3SeS2dS2eS6bVW;Vst;Vtmax;A3G0G1A3G2A3A3A6SfA3").
Theorem espine_s2 : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;SdeVW;Vst;A2S59VW;Vst;A2S4fR6A1S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R9R8R7A5S79VW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;RaR9R8A5S7aVW;Vst;Vtmax;A3R1R7A5R6A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;RbRaR9A5S62VW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HW HUS HKc HP HR rhoE.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as Hc0.
  change (0 <= cnt_of A (bv_unsigned (rw rho 12%positive))) in Hc0.
  apply (ecfg_cut 4000%nat [0x40d40] GW [mkVNA (C1g W st tmax) 1 (SLit 0)] [mkVNA (E2a W st tmax) 0 (SLit 0); mkVNA (E2b W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C1g W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC1g].
  - exact ECert2.
  - intros E rhoX HinE. clear NXC1g ECert2. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sa))].
        apply (b1_pop nW st tmax Xa SKa XXa XFa W1a W1ba W1ca W2a sa sra ENTa SIDa FB ENTra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR (rho_sub rhoX sra))].
        apply (b1_refill nW st tmax Xa SKa XXa XFa W1ra W2ra sa sra ENTa FB ENTra SIDra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sb))].
        apply (b1_pop nW st tmax Xb SKb XXb XFb W1b W1bb W1cb W2b sb srb ENTb SIDb FB ENTrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR (rho_sub rhoX srb))].
        apply (b1_refill nW st tmax Xb SKb XXb XFb W1rb W2rb sb srb ENTb FB ENTrb SIDrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
  - left. reflexivity.
Qed.
End E_spine_s2.

Section E_spine_s3p.
Hypothesis Cert3p : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z40e58SeS29Z3c614S10S29A1A3A3S2bSeS6S79VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S5dVW;Vst;Vtmax;A3G0A3A6SfA3").
Hypothesis SKY : ltac2:(tb__ "0|1|
S0S11S12S12S1aS1aA2S1aA2M0A1S5cS20G0Sc2S27S5S5dVW;Vst;Vtmax;A3A1A1A4S5cS20G0Sc2S16S20S16S20SeS20Sb1S16S20S56VW;A1S51A3A3SdcA3SeS20S9dSeS20S9fSeS20S9eSeS20Sa0S10S20A1A3A3A3A3A3A4A3").
Hypothesis YX : ltac2:(tb__ "0|1|
S0S11S12S1aS1aA2M0A1SbS5dVW;Vst;Vtmax;A3A1S10G0A1A3").
Hypothesis YF : ltac2:(tb__ "0|0|
S45S19S16S19S16S19S16S19S55VW;Vst;A2S54S53A1A3SafA3S5eA3S1dS5S5dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis YP : ltac2:(tb__ "0|0|
S44S19S26S1fZ1A1S21Sa1A1A2S1dS5S5dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis WY1 : ltac2:(tb__ "0|0|
S0SdS1eS5SecS5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Hypothesis WY2 : ltac2:(tb__ "0|0|
S0SdS1eS5SedS5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Hypothesis WY3 : ltac2:(tb__ "0|0|
S0SdS1eS5SeeS5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Hypothesis WY4 : ltac2:(tb__ "0|0|
S0SdS1eS5SefS5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Hypothesis WY5 : ltac2:(tb__ "0|0|
S0SdS1eS5Sf0S5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Hypothesis WY6 : ltac2:(tb__ "0|0|
S0SdS1eS5Sf1S5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Hypothesis WY7 : ltac2:(tb__ "0|0|
S0SdS1eS5SebS5dVW;Vst;Vtmax;A3A1A1A1SfA3").
Variable s3 : wsub.
Hypothesis ENT3 : ltac2:(tb__ "0|0|
S0SdS7SebS5dVW;Vst;Vtmax;A3A1S6eVW;Vst;Vtmax;A3Vs3;A3SfA3").
Hypothesis SID3 : ltac2:(tb__ "0|0|
S0SdS4dVs3;S2bA2SfA3").

Hypothesis NXC2p : ltac2:(tb__ "0|0|
S48S2bS1cS5S79VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert3p : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z40e58SeS29Z3c614S10S29A1A3A3S2bSeS2dS2eS79VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS5dVW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s3p : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;SdeVW;Vst;A2S59VW;Vst;A2S4fR6A1Sf2S4cR8A1A1S1bS36Vsegs;S38Vsegs;S5bVW;Vst;RaR9R8A5S6eVW;Vst;Vtmax;A3R1R7A5R6A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;RbRaR9A5S79VW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HW HUS HKc HSEP HC rhoE.
  apply (ecfg_cut 4000%nat [0x40e58; 0x3c614] GW [mkVNA (C2p W st tmax) 1 (SLit 0)] [mkVNA (E3p W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C2p W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC2p].
  - exact ECert3p.
  - intros E rhoX HinE. clear NXC2p ECert3p. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s3))].
    apply (b3_carve nW st tmax (E3p W st tmax) SKY YX YF WY1 WY2 WY3 WY4 WY5 WY6 WY7 s3 ENT3 SID3 A Kc rho tp w rhoX HW HUS HKc HSEP); [|exact Hw].
    exact (cnt_pos_of_fact nW st A Kc rho rhoX tp w _ Hw YP).
  - left. reflexivity.
Qed.
End E_spine_s3p.

Section E_spine_s3r.
Hypothesis Cert3r : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z40e58SeS29Z3c614S10S29A1A3A3S2bSeS6S7aVW;Vst;Vtmax;A3S10S6A1M0A3SeS6S85VW;Vst;Vtmax;A3G0A3A6SfA3").

Hypothesis NXC2r : ltac2:(tb__ "0|0|
S48S2bS1cS5S7aVW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert3r : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z40e58SeS29Z3c614S10S29A1A3A3S2bSeS2dS2eS7aVW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS85VW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s3r : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;S59VW;Vst;A2S4fR5A1S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R8R7R6A5S85VW;Vst;Vtmax;A3R1R5A5R4A3FrhoE;S1bS36Vsegs;S38Vsegs;S5bVW;Vst;R9R8R7A5S7aVW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HR rhoE.
  apply (ecfg_cut 4000%nat [0x40e58; 0x3c614] GW [mkVNA (C2r W st tmax) 1 (SLit 0)] [mkVNA (E3r W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C2r W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC2r].
  - exact ECert3r.
  - intros E rhoX HinE. clear NXC2r ECert3r. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HR].
  - left. reflexivity.
Qed.
End E_spine_s3r.

Definition HDE_stmt (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho : valuation) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|1|
S1bS11S49Q40A1A1M0S4bS1bS1bG0S3fVA;R4A2S40Vkeep;Vrho;R4A3S36Vsegs;S38Vsegs;S3cVW;Vst;R6VKc;R5A5S6fVW;Vst;Vtmax;A3R4R3A5VQ;A3F_;F_;Ftp';FrhoX;Frho';FA';S36Vsegs;S38Vsegs;S5bVW;Vst;VA;VKc;Vrho;A5S86VW;Vst;Vtmax;A3R3R2A5VQ;A3F_;Ftp;FrhoE;").
Section E_spine_s4.
Hypothesis Cert4 : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z7e9e4S10S29A1A3S2bSeS6S6eVW;Vst;Vtmax;A3S10S6A1M0A3SeS6S86VW;Vst;Vtmax;A3G0A3A6SfA3").

Hypothesis NXC3 : ltac2:(tb__ "0|0|
S48S2bS1cS5S6eVW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert4 : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z7e9e4S10S29A1A3S2bSeS2dS2eS6eVW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS86VW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s4 : ltac2:(tb__ "0|1|
S29OF_;S4bS4eS1bS11S49Q40A1A1M0S37OF_;S59VW;Vst;A2S4fR5A1SfbR8R7R6R5R3A5S4bS1bS1bG0S3fRcR4A2S40ReRbR4A3S36Vsegs;S38Vsegs;S3cVW;Vst;R6RdR5A5S6fVW;Vst;Vtmax;A3R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FA';S1bS36Vsegs;S38Vsegs;S5bVW;Vst;RaR9R8A5S6eVW;Vst;Vtmax;A3R1R7A5R6A3FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho tp Q HUS HKc HD HC rhoE.
  apply (ecfg_cut 4000%nat [0x7e9e4] GW [mkVNA (C3 W st tmax) 1 (SLit 0)] [mkVNA (E4d W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C3 W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC3].
  - exact ECert4.
  - intros E rhoX HinE. clear NXC3 ECert4. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HD; exact HC].
  - left. reflexivity.
Qed.
End E_spine_s4.

Section E_spine_s5.
Hypothesis Cert5 : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z3c774SeS29Z3c80cS10S29A1A3A3S2bSeS6S6fVW;Vst;Vtmax;A3S10S6A1M0A3SeS6S88VW;Vst;Vtmax;A3SeS6S7bVW;Vst;Vtmax;A3G0A3A3A6SfA3").
Variable s6n : wsub.
Hypothesis ENT6n : ltac2:(tb__ "0|0|
S0SdS7S88VW;Vst;Vtmax;A3S65VW;Vst;Vtmax;A3Vs6n;A3SfA3").
Hypothesis SID6n : ltac2:(tb__ "0|0|
S0SdS4dVs6n;S2bA2SfA3").
Hypothesis W5b : ltac2:(tb__ "0|0|
S0SdS1eS5S64VW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D5b : ltac2:(tb__ "0|5|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S7bVW;Vst;Vtmax;A3A1S5S64VW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS43S21S63A1M4A4SeG0S13S1aS1aS42G4A4S10G0A1A3A3S10S19A1A4A2A3").
Hypothesis NX5b : ltac2:(tb__ "0|0|
S0S2aS1cS5S64VW;Vst;Vtmax;A3A1A1S1cS5S7bVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F5f64 : ltac2:(tb__ "0|0|
S44S19S26S21PcA1S1fZfc00A1A2S1dS5S7bVW;Vst;Vtmax;A3A1A1A3").

Hypothesis NXC5 : ltac2:(tb__ "0|0|
S48S2bS1cS5S6fVW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert5 : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z3c774SeS29Z3c80cS10S29A1A3A3S2bSeS2dS2eS6fVW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS88VW;Vst;Vtmax;A3G0G1A3SeS2dS2eS7bVW;Vst;Vtmax;A3G0G1A3G2A3A3A6SfA3").
Theorem espine_s5 : ltac2:(tb__ "0|1|
S4bS4eS1bS11S49Q40M0A1A1S37OF_;S59VW;Vst;A2S4fR5A1Sa2Z1S5aR7S4aG0S24R5PcA2A2A2A2S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5S65VW;Vst;Vtmax;A3R1R6A5R5A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;RaR9R8A5S64VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;RbRaR9A5S6fVW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt H6 H5b rhoE.
  apply (ecfg_cut 4000%nat [0x3c774; 0x3c80c] GW [mkVNA (C5 W st tmax) 1 (SLit 0)] [mkVNA (E5n W st tmax) 0 (SLit 0); mkVNA (E5f W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5 W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5].
  - exact ECert5.
  - intros E rhoX HinE. clear NXC5 ECert5. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    +
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (H6 (rho_sub rhoX s6n))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5n W st tmax) (C6 W st tmax) s6n rhoX tp w ENT6n SID6n); [|exact Hw].
      apply JGb_stable; [exact HUS | exact HKc].
    +
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (H5b rhoX)].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model nW st A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F5f64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, E148, E149, E150, E158, E159, Hcnt |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      pose proof (pc_entry_facts segs A rhoX tp md nv HA ltac:(lia) Hcnt) as PF. cbn zeta in PF. destruct PF as (_ & _ & _ & _ & _ & Hch & _ & _).
      destruct (clsp_eval rhoX (cls_of nv) (chk_of A nv) E158 E159 ltac:(lia) Hch) as [EV1 EV2].
      unfold C5b, upd. lazy zeta. eapply SPA_restate; [exact W5b | exact D5b | exact NX5b | | constructor | exact Hw].
      unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold V_CLS; cbn [eval]; rewrite ?EV1, ?EV2, E158; reflexivity.
  - left. reflexivity.
Qed.
End E_spine_s5.

Section E_spine_s5b.
Hypothesis Cert5b : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z3c7e0S10S29A1A3S2bSeS6S64VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S73VW;Vst;Vtmax;A3SeS6S74VW;Vst;Vtmax;A3G0A3A3A6SfA3").
Hypothesis OV1 : ltac2:(tb__ "0|0|
S0SdSa9P9eS92VW;Vst;Vtmax;A3A2SfA3").
Hypothesis OV2 : ltac2:(tb__ "0|0|
S0SdSa9P9eS93VW;Vst;Vtmax;A3A2SfA3").
Hypothesis TAB1 : ltac2:(tb__ "0|0|
S0SdS41P9eS92VW;Vst;Vtmax;A3Sc1Z11UeA5SfA3").
Hypothesis TAB2 : ltac2:(tb__ "0|0|
S0SdS41P9eS93VW;Vst;Vtmax;A3Sc1Z1U10A5SfA3").
Hypothesis W1' : ltac2:(tb__ "0|0|
S0SdS1eS5S3dVnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis W2' : ltac2:(tb__ "0|0|
S0SdS1eS5S3eVnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D1' : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S73VW;Vst;Vtmax;A3A1S5S3dVnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS92VW;Vst;Vtmax;A3S21S95A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis D2' : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S74VW;Vst;Vtmax;A3A1S5S3eVnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS93VW;Vst;Vtmax;A3S21S95A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis NX1' : ltac2:(tb__ "0|0|
S0S2aS1cS5S3dVnW;Vst;Vtmax;A3A1A1S1cS5S73VW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX2' : ltac2:(tb__ "0|0|
S0S2aS1cS5S3eVnW;Vst;Vtmax;A3A1A1S1cS5S74VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F1gt : ltac2:(tb__ "0|0|
S44S19S23Sa7S1fZ10A1S21S63A1A3S1dS5S73VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F2le : ltac2:(tb__ "0|0|
S44S19S25S23Sa7S1fZ10A1S21S63A1A3A1S1dS5S74VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F1_64 : ltac2:(tb__ "0|0|
S44S19S26S21PcA1S1fZfc00A1A2S1dS5S73VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F2_64 : ltac2:(tb__ "0|0|
S44S19S26S21PcA1S1fZfc00A1A2S1dS5S74VW;Vst;Vtmax;A3A1A1A3").
Variables s1 s2 : wsub.
Hypothesis ENT1 : ltac2:(tb__ "0|0|
S0SdS7S3dVnW;Vst;Vtmax;A3S69VW;Vst;Vtmax;A3Vs1;A3SfA3").
Hypothesis ENT2 : ltac2:(tb__ "0|0|
S0SdS7S3eVnW;Vst;Vtmax;A3S69VW;Vst;Vtmax;A3Vs2;A3SfA3").
Hypothesis SID1 : ltac2:(tb__ "0|0|
S0SdS4dVs1;S2bA2SfA3").
Hypothesis SID2 : ltac2:(tb__ "0|0|
S0SdS4dVs2;S2bA2SfA3").

Hypothesis NXC5b : ltac2:(tb__ "0|0|
S48S2bS1cS5S64VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert5b : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z3c7e0S10S29A1A3S2bSeS2dS2eS64VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS73VW;Vst;Vtmax;A3G0G1A3SeS2dS2eS74VW;Vst;Vtmax;A3G0G1A3G2A3A3A6SfA3").
Theorem espine_s5b : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;S59VW;Vst;A2S4fR5A1S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R8R7R6A5S69VW;Vst;Vtmax;A3R1R5A5R4A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5S64VW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0x3c7e0] GW [mkVNA (C5b W st tmax) 1 (SLit 0)] [mkVNA (E5s1 W st tmax) 0 (SLit 0); mkVNA (E5s2 W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5b W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5b].
  - exact ECert5b.
  - intros E rhoX HinE. clear NXC5b ECert5b. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s1))].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model nW st A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F1_64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F1gt) as Fgt. cbn [holds eval] in Fgt. unfold V_CLS in Fgt. rewrite E158 in Fgt.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, Fgt, E148, E149, E150, E158, E159 |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      rewrite bt_ltu_lit in Fgt by lia. apply Z.ltb_lt in Fgt.
      assert (H' : SPA segs (JGb W st A Kc rho) (E5s1' nW st tmax) rhoX tp (tr, mkCfg ms md)).
      { unfold E5s1', upd. lazy zeta. eapply SPA_restate; [exact W1' | exact D1' | exact NX1' | | constructor | exact Hw].
        unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_SIZE. cbn [eval]. rewrite E148.
        exact (tab1_ok_sound 158 _ Size 17 14%nat rhoX (cls_of nv) TAB1 OV1 E158 ltac:(cbn; lia)). }
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5s1' nW st tmax) (C5c W st tmax) s1 rhoX tp _ ENT1 SID1); [|exact H'].
      apply JGb_stable; [exact HUS | exact HKc].
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s2))].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model nW st A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F2_64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F2le) as Fle. cbn [holds eval] in Fle. unfold V_CLS in Fle. rewrite E158 in Fle.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, Fle, E148, E149, E150, E158, E159 |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      rewrite bt_ltu_lit in Fle by lia.
      assert (Hle : cls_of nv <= 16) by (destruct (Z.ltb_spec 16 (cls_of nv)); [exfalso; apply Fle; reflexivity | lia]).
      assert (H' : SPA segs (JGb W st A Kc rho) (E5s2' nW st tmax) rhoX tp (tr, mkCfg ms md)).
      { unfold E5s2', upd. lazy zeta. eapply SPA_restate; [exact W2' | exact D2' | exact NX2' | | constructor | exact Hw].
        unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_SIZE. cbn [eval]. rewrite E148.
        exact (tab1_ok_sound 158 _ Size 1 16%nat rhoX (cls_of nv) TAB2 OV2 E158 ltac:(cbn; lia)). }
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5s2' nW st tmax) (C5c W st tmax) s2 rhoX tp _ ENT2 SID2); [|exact H'].
      apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End E_spine_s5b.

Section E_spine_s5c.
Hypothesis Cert5c : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Zdb004S10S29A1A3S2bSeS6S69VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S7cVW;Vst;Vtmax;A3G0A3A6SfA3").
Hypothesis G5m1 : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S7cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis W5m1 : ltac2:(tb__ "0|0|
S0SdS1eS5S5fVW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D5m1 : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S7cVW;Vst;Vtmax;A3A1S5S5fVW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aSffS99A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis NX5m1 : ltac2:(tb__ "0|0|
S0S2aS1cS5S5fVW;Vst;Vtmax;A3A1A1S1cS5S7cVW;Vst;Vtmax;A3A1A1A3").
Variables (s51 sd51 : wsub) (R51 : list sobj) (T51 : axst).
Hypothesis He51 : ltac2:(tb__ "0|1|
S0S14S11S20A1M0A1ScdS5fVW;Vst;Vtmax;A3SbdVs51;A3S15G0VR51;A2A3").
Hypothesis Hchk51 : ltac2:(tb__ "0|0|
S0SdSccS5fVW;Vst;Vtmax;A3SbdVs51;VR51;S5cS8S6S9SbeA4A5SfA3").
Hypothesis HT51 : ltac2:(tb__ "0|0|
S0S6SceVs51;SbdSc9SddSbfA1A1S5fVW;Vst;Vtmax;A3VR51;A5VT51;A3").
Hypothesis FBC51 : ltac2:(tb__ "0|1|
S0SdS46S19S22S1cS5S5fVW;Vst;Vtmax;A3A1M0A1A1S1dG0A1A3SfA3").
Hypothesis FBT51 : ltac2:(tb__ "0|0|
S0SdS46S19S22S1cS5VT51;A1A1A1S1dS5S5fVW;Vst;Vtmax;A3A1A1A3SfA3").
Hypothesis ENT51 : ltac2:(tb__ "0|0|
S0SdS7ScbVT51;S1dS5S5fVW;Vst;Vtmax;A3A1A1A2S70VW;Vst;Vtmax;A3Vsd51;A3SfA3").
Hypothesis SID51 : ltac2:(tb__ "0|0|
S0SdS4dVsd51;S2bA2SfA3").
Hypothesis NXC51 : ltac2:(tb__ "0|0|
S48S2bS1cS5S5fVW;Vst;Vtmax;A3A1A1A2").

Hypothesis NXC5c : ltac2:(tb__ "0|0|
S48S2bS1cS5S69VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert5c : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Zdb004S10S29A1A3S2bSeS2dS2eS69VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS7cVW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s5c : ltac2:(tb__ "0|3|
S4bS4eS1bS11S49Q40M0A1A1M1S37OF_;S59VW;Vst;A2S4fR5A1Sa2Z1S5aR7S4aG0S24R5PcA2A2A2A2S1bG1S36Vsegs;S38Vsegs;S3cVW;Vst;RaR9R8A5M2S70VW;Vst;Vtmax;A3R2R1A5R6A3FtpX;FrhoX;S1bS36Vsegs;S38Vsegs;G2S69VW;Vst;Vtmax;A3R1R7A5R6A3FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt HC rhoE.
  apply (ecfg_cut 4000%nat [0xdb004] GW [mkVNA (C5c W st tmax) 1 (SLit 0)] [mkVNA (E5m1 W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5c W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5c].
  - exact ECert5c.
  - intros E rhoX HinE. clear NXC5c ECert5c. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (ecall_gen (C5m1 W st tmax) T51 (C5d W st tmax) s51 R51 sd51 Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
                eq_refl (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) He51 Hchk51 HT51 FBC51 FBT51 ENT51 SID51 NXC51 eq_refl
                A Kc rho tp rhoX Q HUS HKc HC). }
    pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G5m1 Hcnt) as PV. cbn zeta in PV.
    unfold C5m1, upd. lazy zeta. eapply SPA_restate; [exact W5m1 | exact D5m1 | exact NX5m1 | | constructor | exact Hw].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_len1 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End E_spine_s5c.

Section E_spine_s5d.
Hypothesis Cert5d : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Zdb004S10S29A1A3S2bSeS6S70VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S7dVW;Vst;Vtmax;A3G0A3A6SfA3").
Hypothesis G5m2 : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S7dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis W5m2 : ltac2:(tb__ "0|0|
S0SdS1eS5S60VW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D5m2 : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S7dVW;Vst;Vtmax;A3A1S5S60VW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aSfeS97A4SeG0S13S1aS1aS100S9bA4S10G0A1A3A3S10S19A1A4A2A3").
Hypothesis NX5m2 : ltac2:(tb__ "0|0|
S0S2aS1cS5S60VW;Vst;Vtmax;A3A1A1S1cS5S7dVW;Vst;Vtmax;A3A1A1A3").
Variables (s52 sd52 : wsub) (R52 : list sobj) (T52 : axst).
Hypothesis He52 : ltac2:(tb__ "0|1|
S0S14S11S20A1M0A1ScdS60VW;Vst;Vtmax;A3SbdVs52;A3S15G0VR52;A2A3").
Hypothesis Hchk52 : ltac2:(tb__ "0|0|
S0SdSccS60VW;Vst;Vtmax;A3SbdVs52;VR52;S5cS8S6S9SbeA4A5SfA3").
Hypothesis HT52 : ltac2:(tb__ "0|0|
S0S6SceVs52;SbdSc9SddSbfA1A1S60VW;Vst;Vtmax;A3VR52;A5VT52;A3").
Hypothesis FBC52 : ltac2:(tb__ "0|1|
S0SdS46S19S22S1cS5S60VW;Vst;Vtmax;A3A1M0A1A1S1dG0A1A3SfA3").
Hypothesis FBT52 : ltac2:(tb__ "0|0|
S0SdS46S19S22S1cS5VT52;A1A1A1S1dS5S60VW;Vst;Vtmax;A3A1A1A3SfA3").
Hypothesis ENT52 : ltac2:(tb__ "0|0|
S0SdS7ScbVT52;S1dS5S60VW;Vst;Vtmax;A3A1A1A2S71VW;Vst;Vtmax;A3Vsd52;A3SfA3").
Hypothesis SID52 : ltac2:(tb__ "0|0|
S0SdS4dVsd52;S2bA2SfA3").
Hypothesis NXC52 : ltac2:(tb__ "0|0|
S48S2bS1cS5S60VW;Vst;Vtmax;A3A1A1A2").

Hypothesis NXC5d : ltac2:(tb__ "0|0|
S48S2bS1cS5S70VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert5d : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Zdb004S10S29A1A3S2bSeS2dS2eS70VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS7dVW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s5d : ltac2:(tb__ "0|3|
S4bS4eS1bS11S49Q40M0A1A1M1S37OF_;S59VW;Vst;A2S4fR5A1Sa2Z1S5aR7S4aG0S24R5PcA2A2A2A2S1bG1S36Vsegs;S38Vsegs;S3cVW;Vst;RaR9R8A5M2S71VW;Vst;Vtmax;A3R2R1A5R6A3FtpX;FrhoX;S1bS36Vsegs;S38Vsegs;G2S70VW;Vst;Vtmax;A3R1R7A5R6A3FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt HC rhoE.
  apply (ecfg_cut 4000%nat [0xdb004] GW [mkVNA (C5d W st tmax) 1 (SLit 0)] [mkVNA (E5m2 W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5d W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5d].
  - exact ECert5d.
  - intros E rhoX HinE. clear NXC5d ECert5d. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (ecall_gen (C5m2 W st tmax) T52 (C5e W st tmax) s52 R52 sd52 Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
                eq_refl (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) He52 Hchk52 HT52 FBC52 FBT52 ENT52 SID52 NXC52 eq_refl
                A Kc rho tp rhoX Q HUS HKc HC). }
    pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G5m2 Hcnt) as PV. cbn zeta in PV.
    unfold C5m2, upd. lazy zeta. eapply SPA_restate; [exact W5m2 | exact D5m2 | exact NX5m2 | | constructor | exact Hw].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + exact (pv_a0e2 rhoX _ _ _ _ _ _ PV).
    + exact (pv_len2 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End E_spine_s5d.

Section E_spine_s5e.
Hypothesis Cert5e : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z3c80cS10S29A1A3S2bSeS6S71VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S87VW;Vst;Vtmax;A3G0A3A6SfA3").
Variable s6j : wsub.
Hypothesis ENT6j : ltac2:(tb__ "0|0|
S0SdS7S87VW;Vst;Vtmax;A3S65VW;Vst;Vtmax;A3Vs6j;A3SfA3").
Hypothesis SID6j : ltac2:(tb__ "0|0|
S0SdS4dVs6j;S2bA2SfA3").

Hypothesis NXC5e : ltac2:(tb__ "0|0|
S48S2bS1cS5S71VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert5e : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z3c80cS10S29A1A3S2bSeS2dS2eS71VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS87VW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s5e : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;S59VW;Vst;A2S4fR5A1S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R8R7R6A5S65VW;Vst;Vtmax;A3R1R5A5R4A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5S71VW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0x3c80c] GW [mkVNA (C5e W st tmax) 1 (SLit 0)] [mkVNA (E5j W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5e W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5e].
  - exact ECert5e.
  - intros E rhoX HinE. clear NXC5e ECert5e. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s6j))].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5j W st tmax) (C6 W st tmax) s6j rhoX tp w ENT6j SID6j); [|exact Hw].
    apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End E_spine_s5e.

Section E_spine_s6.
Hypothesis Cert6 : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z5f9f8SeS29Z3c82cS10S29A1A3A3S2bSeS6S65VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S7fVW;Vst;Vtmax;A3SeS6S7eVW;Vst;Vtmax;A3G0A3A3A6SfA3").
Variable k6 : nat.
Hypothesis NTH6s : ltac2:(tb__ "0|0|
S0S14S20A1S47S20S27S5S7fVW;Vst;Vtmax;A3A1A1Vk6;A3S15S20S8aA2A3").
Hypothesis ZC6s : ltac2:(tb__ "0|0|
S0SdSf7S1dS5S7fVW;Vst;Vtmax;A3A1A1S8aA2SfA3").
Variable s7s : wsub.
Hypothesis ENT7s : ltac2:(tb__ "0|2|
S0SdS7SaS7fVW;Vst;Vtmax;A3M0Sf6S5G0A1M1Sf5S20S27G1A1Vk6;Sf8S8aA1A4A2A2S67VW;Vst;Vtmax;A3Vs7s;A3SfA3").
Hypothesis SID7s : ltac2:(tb__ "0|0|
S0SdS4dVs7s;S2bA2SfA3").
Hypothesis G6l : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S7eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis W6l : ltac2:(tb__ "0|0|
S0SdS1eS5S66VW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D6l : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S7eVW;Vst;Vtmax;A3A1S5S66VW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS101S9cA4S10G0A1A3S10S19A1A4A2A3").
Hypothesis NX6l : ltac2:(tb__ "0|0|
S0S2aS1cS5S66VW;Vst;Vtmax;A3A1A1S1cS5S7eVW;Vst;Vtmax;A3A1A1A3").

Hypothesis NXC6 : ltac2:(tb__ "0|0|
S48S2bS1cS5S65VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert6 : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z5f9f8SeS29Z3c82cS10S29A1A3A3S2bSeS2dS2eS65VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS7fVW;Vst;Vtmax;A3G0G1A3SeS2dS2eS7eVW;Vst;Vtmax;A3G0G1A3G2A3A3A6SfA3").
Theorem espine_s6 : ltac2:(tb__ "0|1|
S4bS4eS1bS11S49Q40M0A1A1S37OF_;S59VW;Vst;A2S4fR5A1Sa2Z1S5aR7S4aG0S24R5PcA2A2A2A2S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5S67VW;Vst;Vtmax;A3R1R6A5R5A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;RaR9R8A5S66VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;RbRaR9A5S65VW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt HC7 HC6l rhoE.
  apply (ecfg_cut 4000%nat [0x5f9f8; 0x3c82c] GW [mkVNA (C6 W st tmax) 1 (SLit 0)] [mkVNA (E6s W st tmax) 0 (SLit 0); mkVNA (E6l W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C6 W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC6].
  - exact ECert6.
  - intros E rhoX HinE. clear NXC6 ECert6. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC7 (rho_sub rhoX s7s))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW _ (C7 W st tmax) s7s rhoX tp w ENT7s SID7s); [apply JGb_stable; [exact HUS | exact HKc]|].
      apply (SPA_zero_fold segs (JGb W st A Kc rho) rhoX (E6s W st tmax) tp w k6 O_U NTH6s ZC6s Hw).
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC6l rhoX)].
      pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G6l Hcnt) as PV. cbn zeta in PV.
      unfold C6l, upd. lazy zeta. eapply SPA_restate; [exact W6l | exact D6l | exact NX6l | | constructor | exact Hw].
      unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_len3 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End E_spine_s6.

Section E_spine_s6l.
Hypothesis Cert6l : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Zdb004S10S29A1A3S2bSeS6S66VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S80VW;Vst;Vtmax;A3G0A3A6SfA3").
Hypothesis W6m : ltac2:(tb__ "0|0|
S0SdS1eS5S61VW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D6m : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S80VW;Vst;Vtmax;A3A1S5S61VW;Vst;Vtmax;A3A1A2S15G3S13G1G2S10G0A1S10S19A1A4A2A3").
Hypothesis NX6m : ltac2:(tb__ "0|0|
S0S2aS1cS5S61VW;Vst;Vtmax;A3A1A1S1cS5S80VW;Vst;Vtmax;A3A1A1A3").
Variables (s6 sd6 : wsub) (R6 : list sobj) (T6 : axst).
Hypothesis He6 : ltac2:(tb__ "0|1|
S0S14S11S20A1M0A1ScdS61VW;Vst;Vtmax;A3Sd8Vs6;A3S15G0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0SdSccS61VW;Vst;Vtmax;A3Sd8Vs6;VR6;S5cS8S6S9SdaA4A5SfA3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0S6SceVs6;Sd8Sc9Sd9A1S61VW;Vst;Vtmax;A3VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0SdS46S19S22S1cS5S61VW;Vst;Vtmax;A3A1M0A1A1S1dG0A1A3SfA3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0SdS46S19S22S1cS5VT6;A1A1A1S1dS5S61VW;Vst;Vtmax;A3A1A1A3SfA3").
Hypothesis ENT6 : ltac2:(tb__ "0|0|
S0SdS7ScbVT6;S1dS5S61VW;Vst;Vtmax;A3A1A1A2S72VW;Vst;Vtmax;A3Vsd6;A3SfA3").
Hypothesis SID6 : ltac2:(tb__ "0|0|
S0SdS4dVsd6;S2bA2SfA3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S48S2bS1cS5S61VW;Vst;Vtmax;A3A1A1A2").

Hypothesis NXC6l : ltac2:(tb__ "0|0|
S48S2bS1cS5S66VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert6l : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Zdb004S10S29A1A3S2bSeS2dS2eS66VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS80VW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s6l : ltac2:(tb__ "0|2|
S4bS4eS1bS11S49Q40A1A1M0S37OF_;S59VW;Vst;A2S4fR5A1S1bG0S36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5M1S72VW;Vst;Vtmax;A3R2R1A5R5A3FtpX;FrhoX;S1bS36Vsegs;S38Vsegs;G1S66VW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0xdb004] GW [mkVNA (C6l W st tmax) 1 (SLit 0)] [mkVNA (E6m W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C6l W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC6l].
  - exact ECert6l.
  - intros E rhoX HinE. clear NXC6l ECert6l. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (ecall_gen (C6m W st tmax) T6 (C6b W st tmax) s6 R6 sd6 Pre_mszA Posts_mszA P_msz
                eq_refl (fun Jx r0 t0 Hs => memsetZ_sumA_ex Jx Hs r0 t0) He6 Hchk6 HT6 FBC6 FBT6 ENT6 SID6 NXC6 eq_refl
                A Kc rho tp rhoX Q HUS HKc HC). }
    unfold C6m, upd. lazy zeta. eapply SPA_restate; [exact W6m | exact D6m | exact NX6m | constructor | constructor | exact Hw].
  - left. reflexivity.
Qed.
End E_spine_s6l.

Section E_spine_s6b.
Hypothesis Cert6b : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z3c82cS10S29A1A3S2bSeS6S72VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S89VW;Vst;Vtmax;A3G0A3A6SfA3").
Variable s7j : wsub.
Hypothesis ENT7j : ltac2:(tb__ "0|0|
S0SdS7S89VW;Vst;Vtmax;A3S67VW;Vst;Vtmax;A3Vs7j;A3SfA3").
Hypothesis SID7j : ltac2:(tb__ "0|0|
S0SdS4dVs7j;S2bA2SfA3").

Hypothesis NXC6b : ltac2:(tb__ "0|0|
S48S2bS1cS5S72VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert6b : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z3c82cS10S29A1A3S2bSeS2dS2eS72VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS89VW;Vst;Vtmax;A3G0G1A3G2A3A6SfA3").
Theorem espine_s6b : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;S59VW;Vst;A2S4fR5A1S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R8R7R6A5S67VW;Vst;Vtmax;A3R1R5A5R4A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5S72VW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0x3c82c] GW [mkVNA (C6b W st tmax) 1 (SLit 0)] [mkVNA (E6j W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C6b W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC6b].
  - exact ECert6b.
  - intros E rhoX HinE. clear NXC6b ECert6b. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s7j))].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E6j W st tmax) (C7 W st tmax) s7j rhoX tp w ENT7j SID7j); [|exact Hw].
    apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End E_spine_s6b.

Section E_spine_s7.
Hypothesis Cert7 : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z3c8bcSeS29Z3ca04S10S29A1A3A3S2bSeS6S67VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S6cVW;Vst;Vtmax;A3SeS6S6dVW;Vst;Vtmax;A3SeS6S75VW;Vst;Vtmax;A3G0A3A3A3A6SfA3").
Hypothesis OV7a : ltac2:(tb__ "0|0|
S0SdSa9P9dS8bVW;Vst;Vtmax;A3A2SfA3").
Hypothesis OV7b : ltac2:(tb__ "0|0|
S0SdSa9P9dS8cVW;Vst;Vtmax;A3A2SfA3").
Hypothesis TAB7a : ltac2:(tb__ "0|0|
S0SdSaaP9dS8bVW;Vst;Vtmax;A3Sc0Z208Sd6Sd7Sb9SbaSbbSb9SbcA1A1A1A1A1A1A5SfA3").
Hypothesis TAB7b : ltac2:(tb__ "0|0|
S0SdSaaP9dS8cVW;Vst;Vtmax;A3Sc0Z18U3eA5SfA3").
Hypothesis W7a : ltac2:(tb__ "0|0|
S0SdS1eS5Sd1VnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis W7b : ltac2:(tb__ "0|0|
S0SdS1eS5Sd2VnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D7a : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S6cVW;Vst;Vtmax;A3A1S5Sd1VnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS8bVW;Vst;Vtmax;A3S21S63A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis D7b : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S6dVW;Vst;Vtmax;A3A1S5Sd2VnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS8cVW;Vst;Vtmax;A3S21S63A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis NX7a : ltac2:(tb__ "0|0|
S0S2aS1cS5Sd1VnW;Vst;Vtmax;A3A1A1S1cS5S6cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX7b : ltac2:(tb__ "0|0|
S0S2aS1cS5Sd2VnW;Vst;Vtmax;A3A1A1S1cS5S6dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7a : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S6cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7b : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S6dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7a : ltac2:(tb__ "0|0|
S44S19S23Sa7S1fZ200A1S21S78A1A3S1dS5S6cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7b : ltac2:(tb__ "0|0|
S44S19S25S23Sa7S1fZ200A1S21S78A1A3A1S1dS5S6dVW;Vst;Vtmax;A3A1A1A3").
Variables s8a s8b : wsub.
Hypothesis ENT8a : ltac2:(tb__ "0|0|
S0SdS7Sd1VnW;Vst;Vtmax;A3S83VW;Vst;Vtmax;A3Vs8a;A3SfA3").
Hypothesis ENT8b : ltac2:(tb__ "0|0|
S0SdS7Sd2VnW;Vst;Vtmax;A3S83VW;Vst;Vtmax;A3Vs8b;A3SfA3").
Hypothesis SID8a : ltac2:(tb__ "0|0|
S0SdS4dVs8a;S2bA2SfA3").
Hypothesis SID8b : ltac2:(tb__ "0|0|
S0SdS4dVs8b;S2bA2SfA3").
Hypothesis G7p : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S75VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7p : ltac2:(tb__ "0|0|
S44S19S25S23Sa8S21PcA1S91A3A1S1dS5S75VW;Vst;Vtmax;A3A1A1A3").
Hypothesis W7p : ltac2:(tb__ "0|0|
S0SdS1eS5S68VW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D7p : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S75VW;Vst;Vtmax;A3A1S5S68VW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aSd5S96A4S10G0A1A3SeS19S26S1fZ1A1S9aA2S10S19A1A3A4A2A3").
Hypothesis NX7p : ltac2:(tb__ "0|0|
S0S2aS1cS5S68VW;Vst;Vtmax;A3A1A1S1cS5S75VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7an : ltac2:(tb__ "0|0|
S44S19S23Sa8S21PcA1S91A3S1dS5S6cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7bn : ltac2:(tb__ "0|0|
S44S19S23Sa8S21PcA1S91A3S1dS5S6dVW;Vst;Vtmax;A3A1A1A3").

Hypothesis NXC7 : ltac2:(tb__ "0|0|
S48S2bS1cS5S67VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert7 : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z3c8bcSeS29Z3ca04S10S29A1A3A3S2bSeS2dS2eS67VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS6cVW;Vst;Vtmax;A3G0G1A3SeS2dS2eS6dVW;Vst;Vtmax;A3G0G1A3SeS2dS2eS75VW;Vst;Vtmax;A3G0G1A3G2A3A3A3A6SfA3").
Theorem espine_s7 : ltac2:(tb__ "0|5|
S4bS4eS1bS11S49Q40M0A1A1S37OF_;S59VW;Vst;A2S4fR5A1Sa2Z1S5aR7S4aG0S24R5PcM1A2A2A2A2S0S29Sa4S4aG0S24R6G1A2A2Z8M2A2Z0M3A3S1bS36Vsegs;S38Vsegs;S3cVW;Vst;RaR9R8A5S83VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;S4S0S29Sa4S4aG0S24R7G1A2A2G2A2G3A3A1S1bS36Vsegs;S38Vsegs;S3cVW;Vst;RbRaR9A5M4S68VW;Vst;Vtmax;A3R1R8A5R7A3FrhoX;F_;S1bS36Vsegs;S38Vsegs;G4S67VW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt HC8 HC7p rhoE.
  apply (ecfg_cut 4000%nat [0x3c8bc; 0x3ca04] GW [mkVNA (C7 W st tmax) 1 (SLit 0)] [mkVNA (E7c1 W st tmax) 0 (SLit 0); mkVNA (E7c2 W st tmax) 0 (SLit 0); mkVNA (E7p W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C7 W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC7].
  - exact ECert7.
  - intros E rhoX HinE. clear NXC7 ECert7. destruct HinE as [<-|[<-|[<-|[]]]]; cbn [vna_state].
    + apply (etriple_pre_pure segs _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact nW st tmax NX7a NX7b NX7p A Kc rho rhoX tp w _ true Hw G7a F7an)|]. intros Hm0.
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8a))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E7c1' nW st tmax) (C8 W st tmax) s8a rhoX tp w ENT8a SID8a); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c1', upd. lazy zeta.
      apply (class_restate_gen nW st (E7c1 W st tmax) _ (creg7a W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7a TAB7a W7a D7a NX7a); [|exact Hw].
      exact (needed_range nW st A Kc rho rhoX tp w _ true Hw G7a F7a).
    + apply (etriple_pre_pure segs _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact nW st tmax NX7a NX7b NX7p A Kc rho rhoX tp w _ true Hw G7b F7bn)|]. intros Hm0.
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8b))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E7c2' nW st tmax) (C8 W st tmax) s8b rhoX tp w ENT8b SID8b); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c2', upd. lazy zeta.
      apply (class_restate_gen nW st (E7c2 W st tmax) _ (creg7b W st tmax) 24 62%nat A Kc rho tp w rhoX OV7b TAB7b W7b D7b NX7b); [|exact Hw].
      exact (needed_range nW st A Kc rho rhoX tp w _ false Hw G7b F7b).
    + apply (etriple_pre_pure segs _ _ (bv_unsigned (rw rho 12%positive) mod 8 <> 0)); [intros w Hw; exact (nmod8_of_fact nW st tmax NX7a NX7b NX7p A Kc rho rhoX tp w _ false Hw G7p F7p)|]. intros Hm8.
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC7p Hm8 rhoX)].
      pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G7p Hcnt) as PV. cbn zeta in PV.
      destruct w as [tr [ms md]].
      unfold C7p, upd. lazy zeta. eapply SPA_restate; [exact W7p | exact D7p | exact NX7p | | | exact Hw].
      * unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_a0e7 rhoX _ _ _ _ _ _ PV).
      * apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. fold LPe. rewrite (pv_lp1 rhoX _ _ _ _ _ _ PV Hm8). rewrite u64_lit by lia. lia.
  - left. reflexivity.
Qed.
End E_spine_s7.

Section E_spine_s7p.
Hypothesis Cert7p : ltac2:(tb__ "0|1|
S0SdS30S2cUfa0SeS29Z3ca04S10S29A1A3S2bSeS6S68VW;Vst;Vtmax;A3S10S6A1M0A3SeS6S76VW;Vst;Vtmax;A3SeS6S77VW;Vst;Vtmax;A3G0A3A3A6SfA3").
Hypothesis OV7c : ltac2:(tb__ "0|0|
S0SdSa9P9dS8dVW;Vst;Vtmax;A3A2SfA3").
Hypothesis OV7d : ltac2:(tb__ "0|0|
S0SdSa9P9dS8eVW;Vst;Vtmax;A3A2SfA3").
Hypothesis TAB7c : ltac2:(tb__ "0|0|
S0SdSaaP9dS8dVW;Vst;Vtmax;A3Sc0Z208Sd6Sd7Sb9SbaSbbSb9SbcA1A1A1A1A1A1A5SfA3").
Hypothesis TAB7d : ltac2:(tb__ "0|0|
S0SdSaaP9dS8eVW;Vst;Vtmax;A3Sc0Z18U3eA5SfA3").
Hypothesis W7c : ltac2:(tb__ "0|0|
S0SdS1eS5Sd3VnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis W7d : ltac2:(tb__ "0|0|
S0SdS1eS5Sd4VnW;Vst;Vtmax;A3A1A1SfA3").
Hypothesis D7c : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S76VW;Vst;Vtmax;A3A1S5Sd3VnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS8dVW;Vst;Vtmax;A3S21S63A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis D7d : ltac2:(tb__ "0|4|
S0S14S12S11S12S1aS1aA2M0A1M1S11S19A1M2A2M3A1S58S5S77VW;Vst;Vtmax;A3A1S5Sd4VnW;Vst;Vtmax;A3A1A2S15G3S13G1G2SeG0S13S1aS1aS8eVW;Vst;Vtmax;A3S21S63A1A4S10G0A1A3S10S19A1A4A2A3").
Hypothesis NX7c : ltac2:(tb__ "0|0|
S0S2aS1cS5Sd3VnW;Vst;Vtmax;A3A1A1S1cS5S76VW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX7d : ltac2:(tb__ "0|0|
S0S2aS1cS5Sd4VnW;Vst;Vtmax;A3A1A1S1cS5S77VW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7c : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S76VW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7d : ltac2:(tb__ "0|0|
S45S19S5eS1dS5S77VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7c : ltac2:(tb__ "0|0|
S44S19S23Sa7S1fZ200A1S21S78A1A3S1dS5S76VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7d : ltac2:(tb__ "0|0|
S44S19S25S23Sa7S1fZ200A1S21S78A1A3A1S1dS5S77VW;Vst;Vtmax;A3A1A1A3").
Variables s8c s8d : wsub.
Hypothesis ENT8c : ltac2:(tb__ "0|0|
S0SdS7Sd3VnW;Vst;Vtmax;A3S84VW;Vst;Vtmax;A3Vs8c;A3SfA3").
Hypothesis ENT8d : ltac2:(tb__ "0|0|
S0SdS7Sd4VnW;Vst;Vtmax;A3S84VW;Vst;Vtmax;A3Vs8d;A3SfA3").
Hypothesis SID8c : ltac2:(tb__ "0|0|
S0SdS4dVs8c;S2bA2SfA3").
Hypothesis SID8d : ltac2:(tb__ "0|0|
S0SdS4dVs8d;S2bA2SfA3").

Hypothesis NXC7p : ltac2:(tb__ "0|0|
S48S2bS1cS5S68VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert7p : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Z3ca04S10S29A1A3S2bSeS2dS2eS68VW;Vst;Vtmax;A3Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eS76VW;Vst;Vtmax;A3G0G1A3SeS2dS2eS77VW;Vst;Vtmax;A3G0G1A3G2A3A3A6SfA3").
Theorem espine_s7p : ltac2:(tb__ "0|0|
S4bS4eS1bS11S49Q40A1A1S37OF_;S59VW;Vst;A2S4fR5A1S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R8R7R6A5S84VW;Vst;Vtmax;A3R1R5A5R4A3FrhoX;S1bS36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5S68VW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HC8 rhoE.
  apply (ecfg_cut 4000%nat [0x3ca04] GW [mkVNA (C7p W st tmax) 1 (SLit 0)] [mkVNA (E7q1 W st tmax) 0 (SLit 0); mkVNA (E7q2 W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C7p W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC7p].
  - exact ECert7p.
  - intros E rhoX HinE. clear NXC7p ECert7p. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8c))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E7q1' nW st tmax) (C8p W st tmax) s8c rhoX tp w ENT8c SID8c); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q1', upd. lazy zeta.
      apply (class_restate_gen nW st (E7q1 W st tmax) _ (creg7c W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7c TAB7c W7c D7c NX7c); [|exact Hw].
      exact (needed_range nW st A Kc rho rhoX tp w _ true Hw G7c F7c).
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8d))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E7q2' nW st tmax) (C8p W st tmax) s8d rhoX tp w ENT8d SID8d); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q2', upd. lazy zeta.
      apply (class_restate_gen nW st (E7q2 W st tmax) _ (creg7d W st tmax) 24 62%nat A Kc rho tp w rhoX OV7d TAB7d W7d D7d NX7d); [|exact Hw].
      exact (needed_range nW st A Kc rho rhoX tp w _ false Hw G7d F7d).
  - left. reflexivity.
Qed.
End E_spine_s7p.

Section E_spine_s8c.

Variables (CC8 CC9 EE8n : axst).
Variable s9e : wsub.
Hypothesis ENT9 : ltac2:(tb__ "0|0|
S0SdS7VEE8n;VCC9;Vs9e;A3SfA3").
Hypothesis SID9 : ltac2:(tb__ "0|0|
S0SdS4dVs9e;S2bA2SfA3").
Hypothesis NXCC8 : ltac2:(tb__ "0|0|
S48S2bS1cS5VCC8;A1A1A2").
Hypothesis ECert8 : ltac2:(tb__ "0|3|
S0SdS2fS2cUfa0SeS29Zdb004SeS29Z3ca54S10S29A1A3A3S2bSeS2dS2eVCC8;Z1S1fZ0M0A1M1A3S10S2dA1M2A3SeS2dS2eVEE8n;G0G1A3G2A3A6SfA3").
Theorem espine_s8c : ltac2:(tb__ "0|2|
S4bS4eS1bS11S49Q40A1A1M0S37OF_;S59VW;Vst;A2S4fR5A1S1bG0S36Vsegs;S38Vsegs;S3cVW;Vst;R9R8R7A5M1VCC9;R2R1A5R5A3FtpX;FrhoX;S1bS36Vsegs;S38Vsegs;G1VCC8;R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HUS HKc HC9 rhoE.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  apply (ecfg_cut 4000%nat [0xdb004; 0x3ca54] GW [mkVNA (CC8) 1 (SLit 0)] [mkVNA (EE8n) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (CC8) _ HST).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; exact NXCC8.
  - exact ECert8.
  - intros E rhoX HinE. clear NXCC8 ECert8. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC9 (rho_sub rhoX s9e) tp)].
    exact (SPA_entails0 segs (JGb W st A Kc rho) GW EE8n CC9 s9e rhoX tp w ENT9 SID9 HST Hw).
  - left. reflexivity.
Qed.
End E_spine_s8c.

End E.
End SpineCallocE.

(* [comment removed for export] *)
Module SpineCallocS7i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "option"; "Some"; "prod"; "pair"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "C6m"; "E6s"; "C6l"; "C7"; "E6l"; "O_U"; "C6b"; "E6j"; "E6m"; "C6"; "F_gen"; "LUe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sv"; "ss_objs"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocS7i.INST"; "s6_0"; "R6_0"; "T6_0"; "k6_0"; "s7j_0"; "s7s_0"; "sd6_0"; "E6sz_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zobj"; "zero_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@Stdlib.Lists.List"; "forallb"; "incl"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7"; "len3e"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CallocMemoSP.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Lemma Cert6_0 : ltac2:(tb__ "0|1|
S6S7S38S27Ufa0S9S28Z5f9f8S9S28Z3c82cSaS28A1A3A3S26S9S1S1bVW;Vst;Vtmax;A3SaS1A1M0A3S9S1S13VW;Vst;Vtmax;A3S9S1S16VW;Vst;Vtmax;A3G0A3A3A6S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition k6_0 : ltac2:(tb__ "0|0|
S11") := ltac2:(tb__ "0|0|
S46S10S1eS23S0S13VW;Vst;Vtmax;A3A1A1A2U3A2").
Lemma NTH6s_0 : ltac2:(tb__ "0|0|
S6ScS1eA1S45S1eS23S0S13VW;Vst;Vtmax;A3A1A1S30A3SdS1eS17A2A3").
Proof. unfold k6_0. cbv beta zeta delta [W st tmax k6_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ZC6s_0 : ltac2:(tb__ "0|0|
S6S7S3fS21S0S13VW;Vst;Vtmax;A3A1A1S17A2S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition E6sz_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|2|
S3S13VW;Vst;Vtmax;A3M0S3cS0G0A1M1S3bS1eS23G1A1S30S3eS17A1A4A2A2").
Definition s7s_0 : ltac2:(tb__ "0|0|
S36") := ltac2:(tb__ "0|0|
S35S26S0S34A1S0S15VW;Vst;Vtmax;A3A1A3").
Lemma ENT7s_0 : ltac2:(tb__ "0|2|
S6S7S2S3S13VW;Vst;Vtmax;A3M0S3cS0G0A1M1S3bS1eS23G1A1S30S3eS17A1A4A2A2S15VW;Vst;Vtmax;A3S32A3S8A3").
Proof. unfold k6_0, s7s_0. cbv beta zeta delta [W st tmax E6sz_0 k6_0 s7s_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID7s_0 : ltac2:(tb__ "0|0|
S6S7S37S32S26A2S8A3").
Proof. unfold s7s_0. cbv beta zeta delta [W st tmax E6sz_0 k6_0 s7s_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma G6l_0 : ltac2:(tb__ "0|0|
S44S1fS1cS21S0S16VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W6l_0 : ltac2:(tb__ "0|0|
S6S7S25S0S14VW;Vst;Vtmax;A3A1A1S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D6l_0 : ltac2:(tb__ "0|4|
S6ScSeSbSeS22S22A2M0A1M1SbS1fA1M2A2M3A1S3aS0S16VW;Vst;Vtmax;A3A1S0S14VW;Vst;Vtmax;A3A1A2SdG3SfG1G2S9G0SfS22S22S48S1dA4SaG0A1A3SaS1fA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX6l_0 : ltac2:(tb__ "0|0|
S6S29S20S0S14VW;Vst;Vtmax;A3A1A1S20S0S16VW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert6l_0 : ltac2:(tb__ "0|1|
S6S7S38S27Ufa0S9S28Zdb004SaS28A1A3S26S9S1S14VW;Vst;Vtmax;A3SaS1A1M0A3S9S1S1aVW;Vst;Vtmax;A3G0A3A6S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W6m_0 : ltac2:(tb__ "0|0|
S6S7S25S0S12VW;Vst;Vtmax;A3A1A1S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D6m_0 : ltac2:(tb__ "0|4|
S6ScSeSbSeS22S22A2M0A1M1SbS1fA1M2A2M3A1S3aS0S1aVW;Vst;Vtmax;A3A1S0S12VW;Vst;Vtmax;A3A1A2SdG3SfG1G2SaG0A1SaS1fA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX6m_0 : ltac2:(tb__ "0|0|
S6S29S20S0S12VW;Vst;Vtmax;A3A1A1S20S0S1aVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s6_0 : ltac2:(tb__ "0|0|
S36") := ltac2:(tb__ "0|0|
S35P1S0S12VW;Vst;Vtmax;A3A1S0S2aA1A3").
Definition R6_0 : ltac2:(tb__ "0|0|
SbS1eA1") := ltac2:(tb__ "0|1|
ScSbS1eA1M0A1G0Lx;S40S12VW;Vst;Vtmax;A3S2aS2dA3G0R1LR;SaS1eA1Xcx2").
Definition T6_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S41S2dS2aS39S2bA1S12VW;Vst;Vtmax;A3S2eA5").
Definition sd6_0 : ltac2:(tb__ "0|0|
S36") := ltac2:(tb__ "0|0|
S35S26S0S3dS2fS21S0S12VW;Vst;Vtmax;A3A1A1A2A1S0S18VW;Vst;Vtmax;A3A1A3").
Lemma He6_0 : ltac2:(tb__ "0|1|
S6ScSbS1eA1M0A1S40S12VW;Vst;Vtmax;A3S2aS2dA3SdG0S2eA2A3").
Proof. unfold s6_0, R6_0. cbv beta zeta delta [W st tmax R6_0 s6_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Hchk6_0 : ltac2:(tb__ "0|0|
S6S7S42S12VW;Vst;Vtmax;A3S2aS2dS2eS47S5S1S4S2cA4A5S8A3").
Proof. unfold s6_0, R6_0. cbv beta zeta delta [W st tmax R6_0 s6_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma HT6_0 : ltac2:(tb__ "0|0|
S6S1S41S2dS2aS39S2bA1S12VW;Vst;Vtmax;A3S2eA5S2fA3").
Proof. reflexivity. Qed.
Lemma FBC6_0 : ltac2:(tb__ "0|1|
S6S7S43S1fS24S20S0S12VW;Vst;Vtmax;A3A1M0A1A1S21G0A1A3S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma FBT6_0 : ltac2:(tb__ "0|0|
S6S7S43S1fS24S20S0S2fA1A1A1S21S0S12VW;Vst;Vtmax;A3A1A1A3S8A3").
Proof. unfold T6_0. cbv beta zeta delta [W st tmax R6_0 T6_0 s6_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ENT6_0 : ltac2:(tb__ "0|0|
S6S7S2S3dS2fS21S0S12VW;Vst;Vtmax;A3A1A1A2S18VW;Vst;Vtmax;A3S33A3S8A3").
Proof. unfold T6_0, sd6_0. cbv beta zeta delta [W st tmax R6_0 T6_0 s6_0 sd6_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID6_0 : ltac2:(tb__ "0|0|
S6S7S37S33S26A2S8A3").
Proof. unfold sd6_0. cbv beta zeta delta [W st tmax R6_0 T6_0 s6_0 sd6_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NXC6_0 : ltac2:(tb__ "0|0|
S49S26S20S0S12VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert6b_0 : ltac2:(tb__ "0|1|
S6S7S38S27Ufa0S9S28Z3c82cSaS28A1A3S26S9S1S18VW;Vst;Vtmax;A3SaS1A1M0A3S9S1S19VW;Vst;Vtmax;A3G0A3A6S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s7j_0 : ltac2:(tb__ "0|0|
S36") := ltac2:(tb__ "0|0|
S35S26S0S19VW;Vst;Vtmax;A3A1S0S15VW;Vst;Vtmax;A3A1A3").
Lemma ENT7j_0 : ltac2:(tb__ "0|0|
S6S7S2S19VW;Vst;Vtmax;A3S15VW;Vst;Vtmax;A3S31A3S8A3").
Proof. unfold s7j_0. cbv beta zeta delta [W st tmax s7j_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID7j_0 : ltac2:(tb__ "0|0|
S6S7S37S31S26A2S8A3").
Proof. unfold s7j_0. cbv beta zeta delta [W st tmax s7j_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
End INST.
End SpineCallocS7i.

(* [comment removed for export] *)
Module SpineCallocS6i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "option"; "pair"; "Some"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "C5m1"; "C5m2"; "E5m1"; "E5m2"; "C5d"; "C5e"; "E5j"; "C6"; "F_gen"; "BR"; "C5c"; "LLe"; "LRe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "memset_entryA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "ss_facts"; "ss_next"; "sv"; "sobj"; "sprop_below"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocS6i.INST"; "s51_0"; "s52_0"; "R51_0"; "R52_0"; "T51_0"; "T52_0"; "s6j_0"; "sd51_0"; "sd52_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6"; "a0e2"; "len1e"; "len2e"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CallocMemoSP.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Lemma Cert5c_0 : ltac2:(tb__ "0|1|
S5S6S3eS20Ufa0S8S28Zdb004S9S28A1A3S1fS8S1S19VW;Vst;Vtmax;A3S9S1A1M0A3S8S1S11VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma G5m1_0 : ltac2:(tb__ "0|0|
S3dS21S17S22S0S11VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W5m1_0 : ltac2:(tb__ "0|0|
S5S6S27S0SfVW;Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D5m1_0 : ltac2:(tb__ "0|4|
S5SbSeSaSeS24S24A2M0A1M1SaS21A1M2A2M3A1S40S0S11VW;Vst;Vtmax;A3A1S0SfVW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS24S24S43S1aA4S9G0A1A3S9S21A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX5m1_0 : ltac2:(tb__ "0|0|
S5S29S23S0SfVW;Vst;Vtmax;A3A1A1S23S0S11VW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s51_0 : ltac2:(tb__ "0|0|
S2b") := ltac2:(tb__ "0|0|
S2aP1S0SfVW;Vst;Vtmax;A3A1S0S1cA1A3").
Definition R51_0 : ltac2:(tb__ "0|0|
SaS25A1") := ltac2:(tb__ "0|1|
SbSaS25A1M0A1G0Lx;S38SfVW;Vst;Vtmax;A3S1cS2dA3G0R1LR;S9S25A1Xbx2").
Definition T51_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S39S2dS1cS36S3bS1dA1A1SfVW;Vst;Vtmax;A3S2fA5").
Definition sd51_0 : ltac2:(tb__ "0|0|
S2b") := ltac2:(tb__ "0|0|
S2aS1fS0S37S31S22S0SfVW;Vst;Vtmax;A3A1A1A2A1S0S13VW;Vst;Vtmax;A3A1A3").
Lemma He51_0 : ltac2:(tb__ "0|1|
S5SbSaS25A1M0A1S38SfVW;Vst;Vtmax;A3S1cS2dA3SdG0S2fA2A3").
Proof. unfold s51_0, R51_0. cbv beta zeta delta [W st tmax R51_0 s51_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Hchk51_0 : ltac2:(tb__ "0|0|
S5S6S3aSfVW;Vst;Vtmax;A3S1cS2dS2fS3fS4S1S3S1eA4A5S7A3").
Proof. unfold s51_0, R51_0. cbv beta zeta delta [W st tmax R51_0 s51_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma HT51_0 : ltac2:(tb__ "0|0|
S5S1S39S2dS1cS36S3bS1dA1A1SfVW;Vst;Vtmax;A3S2fA5S31A3").
Proof. reflexivity. Qed.
Lemma FBC51_0 : ltac2:(tb__ "0|1|
S5S6S3cS21S26S23S0SfVW;Vst;Vtmax;A3A1M0A1A1S22G0A1A3S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma FBT51_0 : ltac2:(tb__ "0|0|
S5S6S3cS21S26S23S0S31A1A1A1S22S0SfVW;Vst;Vtmax;A3A1A1A3S7A3").
Proof. unfold T51_0. cbv beta zeta delta [W st tmax R51_0 T51_0 s51_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ENT51_0 : ltac2:(tb__ "0|0|
S5S6S2S37S31S22S0SfVW;Vst;Vtmax;A3A1A1A2S13VW;Vst;Vtmax;A3S34A3S7A3").
Proof. unfold T51_0, sd51_0. cbv beta zeta delta [W st tmax R51_0 T51_0 s51_0 sd51_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID51_0 : ltac2:(tb__ "0|0|
S5S6S2cS34S1fA2S7A3").
Proof. unfold sd51_0. cbv beta zeta delta [W st tmax R51_0 T51_0 s51_0 sd51_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NXC51_0 : ltac2:(tb__ "0|0|
S41S1fS23S0SfVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert5d_0 : ltac2:(tb__ "0|1|
S5S6S3eS20Ufa0S8S28Zdb004S9S28A1A3S1fS8S1S13VW;Vst;Vtmax;A3S9S1A1M0A3S8S1S12VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma G5m2_0 : ltac2:(tb__ "0|0|
S3dS21S17S22S0S12VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W5m2_0 : ltac2:(tb__ "0|0|
S5S6S27S0S10VW;Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D5m2_0 : ltac2:(tb__ "0|4|
S5SbSeSaSeS24S24A2M0A1M1SaS21A1M2A2M3A1S40S0S12VW;Vst;Vtmax;A3A1S0S10VW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS24S24S42S18A4S8G0ScS24S24S44S1bA4S9G0A1A3A3S9S21A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX5m2_0 : ltac2:(tb__ "0|0|
S5S29S23S0S10VW;Vst;Vtmax;A3A1A1S23S0S12VW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s52_0 : ltac2:(tb__ "0|0|
S2b") := ltac2:(tb__ "0|0|
S2aP1S0S10VW;Vst;Vtmax;A3A1S0S1cA1A3").
Definition R52_0 : ltac2:(tb__ "0|0|
SaS25A1") := ltac2:(tb__ "0|1|
SbSaS25A1M0A1G0Lx;S38S10VW;Vst;Vtmax;A3S1cS2eA3G0R1LR;S9S25A1Xbx2").
Definition T52_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S39S2eS1cS36S3bS1dA1A1S10VW;Vst;Vtmax;A3S30A5").
Definition sd52_0 : ltac2:(tb__ "0|0|
S2b") := ltac2:(tb__ "0|0|
S2aS1fS0S37S32S22S0S10VW;Vst;Vtmax;A3A1A1A2A1S0S14VW;Vst;Vtmax;A3A1A3").
Lemma He52_0 : ltac2:(tb__ "0|1|
S5SbSaS25A1M0A1S38S10VW;Vst;Vtmax;A3S1cS2eA3SdG0S30A2A3").
Proof. unfold s52_0, R52_0. cbv beta zeta delta [W st tmax R52_0 s52_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Hchk52_0 : ltac2:(tb__ "0|0|
S5S6S3aS10VW;Vst;Vtmax;A3S1cS2eS30S3fS4S1S3S1eA4A5S7A3").
Proof. unfold s52_0, R52_0. cbv beta zeta delta [W st tmax R52_0 s52_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma HT52_0 : ltac2:(tb__ "0|0|
S5S1S39S2eS1cS36S3bS1dA1A1S10VW;Vst;Vtmax;A3S30A5S32A3").
Proof. reflexivity. Qed.
Lemma FBC52_0 : ltac2:(tb__ "0|1|
S5S6S3cS21S26S23S0S10VW;Vst;Vtmax;A3A1M0A1A1S22G0A1A3S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma FBT52_0 : ltac2:(tb__ "0|0|
S5S6S3cS21S26S23S0S32A1A1A1S22S0S10VW;Vst;Vtmax;A3A1A1A3S7A3").
Proof. unfold T52_0. cbv beta zeta delta [W st tmax R52_0 T52_0 s52_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ENT52_0 : ltac2:(tb__ "0|0|
S5S6S2S37S32S22S0S10VW;Vst;Vtmax;A3A1A1A2S14VW;Vst;Vtmax;A3S35A3S7A3").
Proof. unfold T52_0, sd52_0. cbv beta zeta delta [W st tmax R52_0 T52_0 s52_0 sd52_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID52_0 : ltac2:(tb__ "0|0|
S5S6S2cS35S1fA2S7A3").
Proof. unfold sd52_0. cbv beta zeta delta [W st tmax R52_0 T52_0 s52_0 sd52_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NXC52_0 : ltac2:(tb__ "0|0|
S41S1fS23S0S10VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert5e_0 : ltac2:(tb__ "0|1|
S5S6S3eS20Ufa0S8S28Z3c80cS9S28A1A3S1fS8S1S14VW;Vst;Vtmax;A3S9S1A1M0A3S8S1S15VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s6j_0 : ltac2:(tb__ "0|0|
S2b") := ltac2:(tb__ "0|0|
S2aS1fS0S15VW;Vst;Vtmax;A3A1S0S16VW;Vst;Vtmax;A3A1A3").
Lemma ENT6j_0 : ltac2:(tb__ "0|0|
S5S6S2S15VW;Vst;Vtmax;A3S16VW;Vst;Vtmax;A3S33A3S7A3").
Proof. unfold s6j_0. cbv beta zeta delta [W st tmax s6j_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID6j_0 : ltac2:(tb__ "0|0|
S5S6S2cS33S1fA2S7A3").
Proof. unfold s6j_0. cbv beta zeta delta [W st tmax s6j_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
End INST.
End SpineCallocS6i.

(* [comment removed for export] *)
Module RebuildI.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "pow"; "sub"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "ag_thread"; "aa_cache_inited"; "aa_geom"; "aa_live"; "ageom"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cls"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "ag_spacebeg"; "class_state"; "cs_mapped_free_array"; "cs_mapped_user"; "mkAA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "bview"; "view"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.RebuildI"; "ZI"; "initA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "Size"; "max_count"; "IMG_HI"; "IMG_LO"; "free_array"; "region_beg"; "region_info"; "@Corelib.Init.Datatypes"; "bool"; "false"; "option"; "true"; "Some"; "list"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "class_repr"; "bandtp_inv"; "model_inv"; "present_but"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ"; "geoR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "czone"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue ContractFreeNull SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.RebuildR.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition initA (A : AA) : AA := ltac2:(tb__ "0|0|
S24S11VA;A1S17VA;A1S37S1fVA;A1S1cVA;A1S12VA;A1S1eVA;A1S1dVA;A1S18VA;A1S1aVA;A1S19VA;A1S1bVA;A1S16VA;A1S15VA;A1S14VA;A1Af").
Lemma refillA_initA : ltac2:(tb__ "0|0|
SeS0S8SeS42S2bR2A1R1A2S42R2R1A2A3Fc;FA;"). Proof. reflexivity. Qed.
Lemma initA_inited : ltac2:(tb__ "0|0|
SeS8S34S10R1A1S37A3S8SeS2bR2A1R2A3F_;FA;"). Proof. intros [? ? i ? ? ? ? ? ? ? ? ? ? ? ?] H. cbn in H. subst i. reflexivity. Qed.

Definition ZI (T z : Z) : Prop := ltac2:(tb__ "0|0|
S7S2S1VT;Z120A2Vz;A2S3Vz;S1VT;Zad0A2A2A2").

Lemma zi_out : ltac2:(tb__ "0|0|
S0S0S0S0S7S2R3R1A2S3R1R2A2A2SaS2R3S1R5Z120A2A2S2S1R5Zad0A2R4A2A2S9S2aR6R3A2A1F_;F_;Fz;Fhi;Flo;FT;").
Proof. intros T lo hi z Hz HO HZ. unfold ZI in HZ. lia. Qed.
Lemma zi_sh_out : ltac2:(tb__ "0|0|
S0S0S0S0S0S0S41R6R5R4A3S7S2S2cR4A1R2A2S3R2S2cR3A1A2A2S2Z0R5A2S2R5S5Z2Z2fA2A2S9S2aR9R5A2A1F_;F_;F_;F_;Fz;Fhi;Flo;Ftop;FT;FSB;").
Proof.
  intros SB T top lo hi z (S1 & S2 & TG & T1 & T2 & ST & TB) Hz L0 HT HZ. unfold ZI in HZ.
  assert (LH : lo <= hi) by (destruct (Z_le_dec lo hi) as [X|X]; [exact X|]; pose proof (Geometry.Sh_mono hi lo ltac:(lia)); lia).
  pose proof (Sh_band lo ltac:(lia)) as B1. pose proof (Sh_band hi ltac:(lia)) as B2. lia.
Qed.
Lemma zi_czone : ltac2:(tb__ "0|2|
S0S0S0S0S0S0S0S41R7R6R5A3S7S2Z1R5A2S2R5Z1eA2A2S2Z0M0R5A2S3G0R5A2S2S1R7R6A2S6S5Z2M1Z20A2S5G1Z1dA2A2A2S44RcR9R8R7R6A5S9S2aRcR7A2A1F_;F_;F_;F_;F_;F_;Fz;FS;Fo;Fc;Ftop;FT;FSB;").
Proof.
  intros SB T top c o S z HG Hc Ho HS HoS HZ. pose proof HG as (S1 & S2 & TG & T1 & T2 & ST & TB). unfold czone in HZ. cbn zeta in HZ.
  destruct HZ as [H|H].
  - apply (zi_out T (SB + 2 ^ 32) (SB + 2 ^ 37) z); lia.
  - pose proof (Sh_add_le (SB + c * 2 ^ 32 + o) S (SB + c * 2 ^ 32 + o + S) ltac:(lia) ltac:(lia) ltac:(lia)) as M.
    apply (zi_sh_out SB T top (SB + c * 2 ^ 32 + o) (SB + c * 2 ^ 32 + o + S) z HG); lia.
Qed.

Lemma class_repr_init : ltac2:(tb__ "0|9|
S27S27S13SeS0S21S7S2Z1R2A2S2R2Z1eA2A2S8S34S10R4A1S35A3S0SaS7S2S33S20R7A1M0R5A2M1R1A2S3R1S1G1Z80A2A2A2SaS7S2S31G0R5A2M2R1A2S3R1S1G2S22R4A1A2A2A2S7S2S2cS32G0R5A2M3A1R1A2S3R1S2cS1G3S23R4A1A2M4A1A2A2A2A2S8S36S3aQ8A1A1R9R2A1RaR2A1A3F_;Fz;S40R8G3G4S12R6A1A4S29R9S1S1SfR8A1Zd0M5A2S4Z50M6R6A2A2M7S1G7G6A2A3S25RaS26S1S1SfR9A1G5A2S4G6R7A2A2U4M8Z0A3A2S25RbS26S1S1S1SfRaA1G5A2S4G6R8A2A2Z4A2G8S2eR8A1A3A2S25RcS26S1S1S1SfRbA1G5A2S4G6R9A2A2Z8A2U8S2dR9A1A3A2S3dReRcRbRaR9A5S3dReRdS2bRcA1RbRaA5F_;F_;F_;F_;F_;F_;F_;F_;F_;Fcs;Fc;FA;FG;Fm';Fm;").
Proof.
  intros m m' G A c cs Hc Hini AG PU' PE' K1' K2' K3' P4.
  assert (CA : forall cc, (forall k, (k < c_w cc)%nat ->
             (region_info (ag_spacebeg G) c <= c_addr cc + Z.of_nat k < region_info (ag_spacebeg G) c + 128
              \/ free_array (ag_spacebeg G) c <= c_addr cc + Z.of_nat k < free_array (ag_spacebeg G) c + cs_mapped_free_array cs
              \/ Sh (region_beg (ag_spacebeg G) c) <= c_addr cc + Z.of_nat k < Sh (region_beg (ag_spacebeg G) c + cs_mapped_user cs))) -> cell_ok m cc -> cell_ok m' cc).
  { intros cc Hf. apply cell_ok_agree. intros k Hk. apply AG. exact (Hf k Hk). }
  unfold class_repr in P4 |- *.
  change (live_ids G (initA A) c) with (live_ids G A c). change (qall (initA A)) with (qall A). change (aa_live (initA A)) with (aa_live A).
  change (aa_cache_inited (initA A)) with true.
  set (ri := region_info (ag_spacebeg G) c) in *. set (fa := free_array (ag_spacebeg G) c) in *. set (rb := region_beg (ag_spacebeg G) c) in *.
  destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & C9 & PR & N7 & PU & PS & PE & ND & LV & CI & CN & TI10 & CV10 & MC10 & FC10).
  assert (FRI : forall off w, 0 <= off -> off + Z.of_nat w <= 72 -> forall k, (k < w)%nat ->
            (ri <= ri + off + Z.of_nat k < ri + 128 \/ fa <= ri + off + Z.of_nat k < fa + cs_mapped_free_array cs
             \/ Sh rb <= ri + off + Z.of_nat k < Sh (rb + cs_mapped_user cs))).
  { intros off w Ho Hw k Hk. left. lia. }
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mutex; lia | exact C1]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_num_freed; lia | exact C2]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_free_array; lia | exact C3]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_user; lia | exact C4]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_meta; lia | exact C5]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_user; lia | exact C6]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_meta; lia | exact C7]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_exhausted; lia | exact C8]|].
  split; [eapply present_agree; [|exact PRI]; intros z Hz; apply AG; left; unfold kRegionInfoStride in Hz; lia|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split.
  { intros i x Hi. apply CA; [|exact (C9 i x Hi)]. cbn [c_addr c_w]. intros k Hk. right; left.
    pose proof (nth_error_Some_lt _ _ _ Hi) as L. lia. }
  split; [eapply present_agree; [|exact PR]; intros z Hz; apply AG; right; left; lia|].
  split; [exact N7|].
  split; [exact PU'|].
  split; [eapply present_agree; [|exact PS]; intros z Hz; apply AG; right; right; lia|].
  split; [exact PE'|].
  split; [exact ND|].
  split; [exact LV|].
  destruct (CN Hini) as [EC _].
  split.
  - intros _. rewrite EC. cbn [length Z.of_nat]. split; [exact K1'|]. split; [exact K2'|]. split; [exact K3'|].
    split; [intros i x Hi; destruct i; discriminate Hi|]. destruct (kchunks_facts c Hc) as (X1 & X2 & _). lia.
  - split; [intros X; discriminate X|]. exact (conj TI10 (conj CV10 (conj MC10 FC10))).
Qed.

Section RI.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Lemma init_rebuild : ltac2:(tb__ "0|8|
SeSdSdS39S3aQ40M0A1A1M1G1S3cS3cVAInv;R7R6R4R2A4S8S34S10R8A1S35A3S11R9A1S13SfR1A1S0S28Vsegs;ScR9A1A2S27S28Vsegs;ScRbA1A2S27S0S9S2aR4R1A2A1S8S36S3aQ8A1M2A1M3R4R2A1R3R2A1A3F_;Fz;S0S2aR5R1A2SbG2G2S8G3R6R3A1S38G2R1A2A3Lb;A2F_;Fz;S0S7S2S30R1A2S3R1S2fA2A2S8G3ScRfS3bG0R2A2M4A2ScR10G4A2A3F_;Fa;S0S7S2Z1R1A2S2R1Z1eA2A2S7S25R7S26S1S1R8Zd0A2S4Z50R2A2A2M5U4M6Z0A3A2S7S25R7S26S1G5Z4A2G6S2eR2A1A3A2S25R7S26S1G5Z8A2U8S2dR2A1A3A2A2A2F_;Fc;S3fVsegs;S2bR11A1RdRbA4S3eR7ReA2S7VAInv;S2bR13A1M7R11RfRdA4S43VCST;VXGL;R13G7ScR12A1ScR11A1A6A2F_;F_;F_;F_;F_;F_;TvE;Tv3;TT;TG;F_;F_;Fmd;Fmd0;Ftp;Ftp0;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp0 tp md0 md HA Hini G T v3 vE VO PRES HRMI HCELLS HMD HBT.
  set (Ar := initA A).
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB). fold vE in HR, HF, HRest. fold G in HG, HR, HF, HRest.
  pose proof HG as HG0. pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & TG).
  fold G in G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, TG. fold T in G4, G5, G10, G13, G14.
  set (SB := ag_spacebeg G) in *.
  assert (GS : 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G /\ SB mod 2 ^ 16 = 0
               /\ (ag_fsb G + 11571200 <= SB \/ SB + 2 ^ 37 + 4096 <= ag_fsb G)).
  { pose proof (geom_old _ HG) as X. rewrite FS_total_val, kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G in X. fold SB in X. clear -X. tauto. }
  destruct GS as (S1 & S2 & S3 & S4).
  pose proof (geom_bands _ HG) as (WF & TB & CB & DB & TI & CTI & DTI). fold G T in TB, TI. fold G in WF, CB, DB, CTI, DTI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in WF, TB, CB, DB, TI, CTI, DTI. rewrite FS_total_val in WF.
  pose proof HI3 as HI3c. destruct HI3 as (SG3 & LIV3 & SEC3 & Q3 & DEP3 & ND3). fold G in SG3, SEC3, Q3, DEP3.
  pose proof SG3 as SG3c. destruct SG3 as (T3 & CTX3 & DTLS3 & PAB3 & PABT3 & _). rewrite kSpaceSize_val in T3, CTX3, DTLS3, PAB3, SEC3. fold T in T3, PABT3. fold SB in T3, CTX3, DTLS3, PAB3.
  destruct HRest as (Hsep & Hlive & Hprim & Hsec & Hq & Hdep & Hia & HTH & Hmisc). pose proof Hprim as Hprim0.
  destruct Hprim as (PL & P0 & P31 & PC).
  assert (GEO : geoR SB T (topG G)).
  { unfold geoR. clear -S1 S2 TG G4 G5 T3 TB. lia. }
  assert (ZND : forall z, ZI T z \/ ~ ZI T z) by (intros z; unfold ZI; clear; lia).

  assert (ENVF : forall z, ZI T z -> fs_footb G z = false).
  { intros z Hz. apply fs_footb_thread; [exact HG0 | fold G T; unfold ZI in Hz; clear -Hz; lia]. }
  set (m3 := maskv (fs_footb G) v3). set (mE := maskv (fs_footb G) vE).
  assert (AGm : forall z, ~ ZI T z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity | exact (VO z Hz)]. }
  assert (MTH : forall z, T <= z < T + 4096 -> m3 z = v3 z).
  { intros z Hz. unfold m3. apply maskv_out. apply fs_footb_thread; [exact HG0 | fold G T; clear -Hz; lia]. }
  fold mE in Hlive, PC, Hsec, Hq, Hdep, Hia, HTH, Hmisc.
  assert (PRES3 : forall z, ZI T z -> exists b, m3 z = Some b).
  { intros z Hz. rewrite MTH by (unfold ZI in Hz; clear -Hz; lia). exact (PRES z Hz). }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc) | rewrite (AGm z Hn); exact (Hp z Hz)]. }
  assert (PRESB : forall lo hi L, present_but mE lo hi L -> present_but m3 lo hi L).
  { intros lo hi L Hp z Hz HL. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc) | rewrite (AGm z Hn); exact (Hp z Hz HL)]. }
  assert (EG' : aa_geom Ar = G) by reflexivity.
  assert (HQP : q_pure A) by exact (proj1 (quarantine_repr_pure mE A HG Hq)).
  assert (HAU : forall c', 1 <= c' <= 30 -> 0 <= cs_allocated_user (SegQ_wf2.cls_of A c') <= kUserSpaceSize).
  { intros c' Hc'. pose proof (PC c' Hc') as HC. unfold class_repr in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _). unfold SegQ_wf2.cls_of, kUserMapSize in *. clear -M2 M3. lia. }

  assert (NE_img : forall z, IMG_LO <= z < IMG_HI -> ~ ZI T z).
  { intros z Hz. unfold IMG_LO, IMG_HI in Hz. apply (zi_out T 65536 6565888 z Hz). clear -TI. lia. }
  assert (NE_space : forall z, SB <= z < SB + 2 ^ 37 + 4096 -> ~ ZI T z).
  { intros z Hz. apply (zi_out T SB (SB + 2 ^ 37 + 4096) z Hz). clear -T3. lia. }
  assert (NE_sec : forall i ch z, nth_error (aa_sec A) i = Some ch ->
            (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch \/ Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)) -> ~ ZI T z).
  { intros i ch z Hi Hz. destruct (SEC3 i ch Hi) as (E1 & E2 & _). fold T in E2. fold SB in E1.
    destruct Hsec as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D10, D12. unfold PG in D8.
    destruct D10 as (D10a & D10l & _ & _ & D10b).
    destruct Hz as [Hz|Hz].
    - apply (zi_out T (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z Hz). clear -E2. lia.
    - apply (zi_sh_out SB T (topG G) (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z GEO Hz); [clear -D10a; lia | clear -D12 TG; lia]. }
  assert (LIVE_OUT : forall b n z, In (b, n) (aa_live A) ->
            (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> ~ ZI T z).
  { intros b n z Hin Hz. destruct (is_primary n) eqn:HP.
    - pose proof (live_prim_czone A HG SG3c mE Hsep Hprim0 b n Hin HP) as LPC. cbv zeta in LPC. destruct LPC as (D1 & O0 & OM & OE & _ & _ & CZ). fold SB in O0, OM, OE, CZ.
      set (c' := ClassID (needed n)) in *. set (o' := b - rz n - (SB + c' * 2 ^ 32)) in *.
      assert (SZ0 : 0 < Size c') by (destruct (Size_facts c' D1) as [X _]; clear -X; lia).
      exact (zi_czone SB T (topG G) c' o' (Size c') z GEO D1 O0 SZ0 OE (CZ z Hz)).
    - destruct (live_sec_map A mE Hsep Hsec HI3c b n Hin HP) as (i & ch & Hi & Eb & RZ & Hn1 & BN & D6 & D0 & DI). unfold PG in Eb, D6.
      apply (NE_sec i ch z Hi). destruct Hz as [Hz|Hz]; [left; clear -Hz Eb RZ BN; lia | right].
      pose proof (Geometry.Sh_mono (sc_map_beg ch) b ltac:(clear -Eb; lia)) as M1.
      pose proof (Sh_add_le b (n + 7) (sc_map_beg ch + sc_map_size ch) ltac:(clear -Eb DI; destruct DI as (X & _); lia) ltac:(clear -Hn1; lia) ltac:(clear -BN; lia)) as M2.
      clear -Hz M1 M2. lia. }
  assert (QF_OUT : forall z, q_foot A z -> ~ ZI T z).
  { intros z Hz. destruct (qfoot_cases A mE HG HI3c HQP Hsec HAU z Hz) as [(c' & o' & (D1 & O0 & OM & OE & IDin) & CZ)|(i & ch & Hi & Hr)].
    - fold SB in CZ. assert (SZ0 : 0 < Size c') by (destruct (Size_facts c' D1) as [X _]; clear -X; lia).
      exact (zi_czone SB T (topG G) c' o' (Size c') z GEO D1 O0 SZ0 OE CZ).
    - exact (NE_sec i ch z Hi Hr). }

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz. apply VO.
    destruct (rtc_foot_cases G z Hz) as [K|[K|[K|[K|K]]]].
    - exact (NE_img z K).
    - fold T in K. apply (zi_out T T (T + 288) z); clear -K; lia.
    - apply (zi_out T (ag_ctx G) (ag_ctx G + 4096) z ltac:(clear -K; lia)). clear -G13. lia.
    - apply (zi_out T (ag_dtls G) (ag_dtls G + 4096) z ltac:(clear -K; lia)). clear -G14. lia.
    - apply (zi_out T (ag_fsb G) (ag_fsb G + 11571200) z ltac:(clear -K; lia)). clear -G10. lia. }
  assert (HFS : fs_inv (restrictv (fs_footb G) v3) Ar).
  { rewrite (restrictv_ext (fs_footb G) vE v3) by (intros z Hz; apply VO; intros Hc; rewrite (ENVF z Hc) in Hz; discriminate).
    exact HF. }
  assert (HLS : live_sep Ar) by exact Hsep.
  assert (HLB : live_block_repr m3 Ar).
  { apply (live_block_repr_agree mE m3 A Ar eq_refl); [|intros b n Hin; exact (proj1 (Hsep b n Hin))|exact Hlive].
    intros b n z Hin Hz. apply AGm. exact (LIVE_OUT b n z Hin Hz). }
  assert (HPR : primary_repr m3 Ar).
  { unfold primary_repr. rewrite EG'. split; [exact PL|]. split; [exact P0|]. split; [exact P31|].
    intros c' Hc'. change (aa_cls Ar) with (aa_cls A).
    pose proof (PC c' Hc') as PC'. pose proof PC' as PCd. unfold class_repr in PCd.
    destruct PCd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & M6 & _ & _ & _ & PU & _ & PE & _).
    pose proof (Zle_0_nat (length (cs_free_array (nthZ (aa_cls A) c' cs_empty)))) as L0.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3, M6.
    destruct (HCELLS c' Hc') as (K1' & K2' & K3').
    assert (PCB : T + 288 <= T + 0xd0 + 80 * c' /\ T + 0xd0 + 80 * c' + 80 <= T + 2768) by (clear -Hc'; lia).
    apply (class_repr_init mE m3 G A c' _ Hc' Hini); [| apply PRESB; exact PU | apply PRESX; exact PE | | | | exact PC'].
    - intros z Hz. apply AGm. fold SB in Hz.
      unfold region_info, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kRegionInfoStride in Hz. rewrite kSpaceSize_val in Hz.
      destruct Hz as [Hz|[Hz|Hz]].
      + apply NE_space. clear -Hz Hc'. lia.
      + apply NE_space. clear -Hz Hc' M6 L0. lia.
      + apply (zi_sh_out SB T (topG G) _ _ z GEO Hz); [clear -S1 Hc'; lia | clear -S2 TG Hc' M2 M3; lia].
    - eapply cell_ok_agree; [|exact K1']. cbn [c_addr c_w]. intros k Hk. apply MTH. clear -Hk PCB G4. lia.
    - eapply cell_ok_agree; [|exact K2']. cbn [c_addr c_w]. intros k Hk. apply MTH. clear -Hk PCB G4. lia.
    - eapply cell_ok_agree; [|exact K3']. cbn [c_addr c_w]. intros k Hk. apply MTH. clear -Hk PCB G4. lia. }
  assert (LIVM : forall z, in_rangesZ (aa_live A) z -> in_rangesZ (aa_live Ar) z) by (intros z Hz; exact Hz).
  assert (HSR : secondary_repr m3 Ar).
  { refine (secondary_repr_agree mE m3 A Ar eq_refl eq_refl eq_refl _ _ _ LIVM Hsec).
    - intros i ch z Hi Hz. apply AGm. exact (NE_sec i ch z Hi Hz).
    - intros z Hz. apply AGm. destruct Hsec as (_ & _ & SC2 & _ & SC45 & _). fold G in SC45, Hz. destruct SC45 as [_ (SC4a & _ & SC5 & _ & SC4)].
      unfold kPtrArrayReserve in SC2, SC4, PAB3, PABT3.
      apply (zi_out T (ag_pab G) (ag_pab G + 2 ^ 23) z ltac:(clear -Hz SC2; lia)). clear -PABT3. lia.
    - intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HQR : quarantine_repr m3 Ar).
  { refine (quarantine_repr_agreeR mE m3 A Ar eq_refl eq_refl eq_refl eq_refl _ _ _ _ Hq).
    - intros c'. change (aa_cls Ar) with (aa_cls A). clear; lia.
    - intros z Hz. apply AGm. exact (QF_OUT z Hz).
    - intros z Hz. apply AGm. fold G T in Hz. apply (zi_out T T (T + 288) z); clear -Hz; lia.
    - intros z Hz. apply AGm. apply NE_img. unfold QG, IMG_LO, IMG_HI in *. clear -Hz. lia. }
  assert (HIA : ia_inv m3 Ar).
  { refine (ia_inv_agree mE m3 A Ar eq_refl _ Hia). intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HTI : thread_inv m3 G).
  { destruct HTH as [TH1 TH2]. fold G T in TH1, TH2. unfold thread_inv. fold T. split.
    - rewrite AGm; [exact TH1|]. unfold ZI. clear. lia.
    - apply PRESX. exact TH2. }
  assert (HMI : misc_inv m3).
  { refine (misc_inv_agree mE m3 _ Hmisc). intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HDEP : depot_wf m3 Ar).
  { unfold depot_wf in Hdep |- *. change (aa_depot Ar) with (aa_depot A). eapply depot_mem_frame; [|exact Hdep]. intros a Ha. apply AGm.
    assert (BLK : forall bb L, In (bb, L) (dblocks (aa_depot A)) -> bb <= a < bb + L -> ~ ZI T a).
    { intros bb L Hbb Hab. destruct (DEP3 (bb, L) Hbb) as (DI & ST & _ & _ & _ & SS & _). unfold sepZ in ST, SS. cbn [fst snd] in DI, ST, SS. fold T in ST.
      apply (zi_out T bb (bb + L) a Hab). clear -ST. lia. }
    destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
    - apply (NE_img a). unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. unfold IMG_LO, IMG_HI. clear -Hs. lia.
    - apply (BLK bb NBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. left. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
    - apply (BLK bb FBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. right. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb]. }
  assert (HI3' : inv3 Ar).
  { pose proof HI3c as (X1' & X2' & X3' & X4' & X5' & X6' & X7' & X8' & X9'). split; [exact X1'|]. split; [exact X2'|]. split; [exact X3'|].
    split; [exact X4'|]. split; [exact X5'|]. split; [exact X6'|]. split; [exact X7'|]. split; [exact X8'|]. intros _. reflexivity. }
  assert (HA' : AInv Ar rho3 tp md).
  { unfold AInv, AInvA. rewrite EG'. fold v3. split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|].
    split; [|split; [exact HMD | split; [exact HI3' | exact HBT]]].
    fold m3. split; [exact HLS|]. split; [exact HLB|]. split; [exact HPR|]. split; [exact HSR|]. split; [exact HQR|].
    split; [exact HDEP|]. split; [exact HIA|]. split; [exact HTI | exact HMI]. }
  split; [exact HA'|].

  assert (HFv : fs_inv (restrictv (fs_footb G) vE) A) by exact HF.
  assert (RMO : forall a, 0 <= a < 2 ^ 64 -> ~ ZI T a -> rm rho3 (Z_to_bv 64 a) = rm rhoE (Z_to_bv 64 a)).
  { intros a Ha Hn. destruct (Z_lt_dec a IMG_LO) as [LO|NLO]; [|destruct (Z_le_dec IMG_HI a) as [HI|NHI]].
    - rewrite <- (view_rm_off (rm rho3) a Ha (or_introl LO)), <- (view_rm_off (rm rhoE) a Ha (or_introl LO)). exact (VO a Hn).
    - rewrite <- (view_rm_off (rm rho3) a Ha (or_intror HI)), <- (view_rm_off (rm rhoE) a Ha (or_intror HI)). exact (VO a Hn).
    - apply HRMI. clear -NLO NHI. lia. }
  assert (DEFM : forall a, IMG_HI <= a < 2 ^ 64 -> rm rhoE (Z_to_bv 64 a) <> None -> rm rho3 (Z_to_bv 64 a) <> None).
  { intros a Ha Hd. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold IMG_HI in Ha; clear -Ha; lia).
    rewrite <- (view_rm_off (rm rho3) a Ha' (or_intror (proj1 Ha))). rewrite <- (view_rm_off (rm rhoE) a Ha' (or_intror (proj1 Ha))) in Hd.
    change (v3 a <> None). change (vE a <> None) in Hd. destruct (ZND a) as [Hc|Hn]; [destruct (PRES a Hc) as [b Hb]; rewrite Hb; discriminate | rewrite (VO a Hn); exact Hd]. }
  split.
  2: { intros x0 j Hx Hj Hdef.
       assert (Bx : 0 <= x0 < 2 ^ 47).
       { destruct Hx as [[CX _]|GX]; [exact (proj1 (client_addr_bounds CST HCST A x0 _ HG HFv Hsep CX))|].
         destruct (HXGL x0 GX) as [XG1 XG2]. unfold IMG_HI in XG2. clear -XG1 XG2. lia. }
       unfold word_byte. apply DEFM; [|exact Hdef].
       pose proof (Z.div_mod (Sh x0) 8 ltac:(clear; lia)) as DM. pose proof (Z.mod_pos_bound (Sh x0) 8 ltac:(clear; lia)) as MB.
       unfold Sh, SHADOW_OFF, IMG_HI in DM, MB |- *. pose proof (Z.div_le_mono 0 x0 8 ltac:(clear; lia) ltac:(clear -Bx; lia)) as D0.
       pose proof (Z.div_lt_upper_bound x0 8 (2 ^ 44) ltac:(clear; lia) ltac:(clear -Bx; lia)) as D1. change (0 / 8) with 0 in D0.
       clear -Hj DM MB D0 D1. lia. }
  intros a Ha Hcl.

  assert (NOC : forall y, client_addrA CST A y ->
            (exists b n, In (b, n) (aa_live A) /\ b <= y < b + n)
            \/ (0 <= y < 2 ^ 47 /\ (y < T \/ T + 4096 <= y))).
  { intros y Hy.
    destruct (client_addr_cases CST A y _ HFv Hy) as [S|[L|[FR|[C|FL]]]].
    - right. fold G in S. clear -S S2 G5 TG. lia.
    - left. exact L.
    - right. destruct FR as (c0 & p0 & Hc0 & Hp0 & _ & Hyf). pose proof (fs_geom_nums G c0 p0 HG Hc0 Hp0) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Hyf. clear -Hyf M S4 G10 WF G2 G3 TG. lia.
    - right. destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in X. clear -X S1 TI. lia.
    - right. destruct FL as (c0 & p0 & Hc0 & Hp0 & _ & ->). pose proof (fs_geom_nums G c0 p0 HG Hc0 Hp0) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G. unfold fs_flags. rewrite FS_kFlagsOffset_val.
      unfold fs_flags in M. rewrite FS_kFlagsOffset_val in M. clear -M S4 G10 WF G2 G3 TG. lia. }
  assert (SHY : forall y, 0 <= y < 2 ^ 47 -> ~ ZI T (Sh y)).
  { intros y By.
    pose proof (Z.div_mod y 8 ltac:(clear; lia)) as DY. pose proof (Z.mod_pos_bound y 8 ltac:(clear; lia)) as MY.
    apply (zi_sh_out SB T (topG G) (8 * (y / 8)) (8 * (y / 8) + 8) (Sh y) GEO); [|clear -By DY MY; lia|clear -By DY MY; lia].
    unfold Sh. replace (8 * (y / 8) / 8) with (y / 8) by (rewrite Z.mul_comm, Z.div_mul; clear; lia).
    replace ((8 * (y / 8) + 8) / 8) with (y / 8 + 1) by (replace (8 * (y / 8) + 8) with ((y / 8 + 1) * 8) by (clear; lia); rewrite Z.div_mul; clear; lia).
    clear. lia. }
  apply RMO; [exact Ha|].
  destruct Hcl as [[CL1 _]|[CL1 _]].
  - destruct (NOC a CL1) as [(b & n & Hbn & Hab)|(B1 & B2)].
    + apply (LIVE_OUT b n a Hbn). left. pose proof (rz_bound n). clear -Hab H. lia.
    + unfold ZI. clear -B2. lia.
  - destruct CL1 as [(y & Cy & ->)|(y & Gy & ->)].
    + apply SHY. destruct (NOC y Cy) as [(b & n & Hbn & Hyb)|(B1 & _)]; [|exact B1].
      exact (proj1 (client_addr_bounds CST HCST A y _ HG HFv Hsep Cy)).
    + destruct (HXGL y Gy) as [Y1 Y2]. unfold IMG_HI in Y2. apply (SHY y). clear -Y1 Y2. lia.
Qed.
End RI.
End RebuildI.

(* [comment removed for export] *)
Module SpineCallocS5i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "prod"; "list"; "pair"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "swf"; "SVar"; "ss_facts"; "SLit"; "ss_next"; "SPUle"; "SPBranch"; "SPNot"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E3p"; "E5s1"; "E5s2"; "C5b"; "C5c"; "E5f"; "C3"; "E5n"; "V_CLS"; "sreg1"; "sreg2"; "C6"; "V_SIZE"; "C2p"; "C2r"; "C5"; "E3r"; "E4d"; "F_gen"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "V_CNT"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "E5s1'"; "E5s2'"; "tab1_ok"; "clsp_e"; "clsp_e31"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4"; "Y7"; "Y1"; "Y2"; "Y3"; "Y4"; "Y5"; "Y6"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocS5i.INST"; "s1_0"; "s2_0"; "s3_0"; "s6n_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CallocMemoSP.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Lemma Cert3p_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z40e58S5S33Z3c614S8S33A1A3A3S35S5S1S28VW;Vst;Vtmax;A3S8S1A1M0A3S5S1S1bVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SKY_0 : ltac2:(tb__ "0|1|
S4SaS9S9SfSfA2SfA2M0A1S4aS11G0S4dS1aS0S1bVW;Vst;Vtmax;A3A1A1A4S4aS11G0S4dScS11ScS11S5S11S54ScS11S5aVW;A1S56A3A3S55A3S5S11S2eS5S11S30S5S11S2fS5S11S31S8S11A1A3A3A3A3A3A4A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma YX_0 : ltac2:(tb__ "0|1|
S4SaS9SfSfA2M0A1S3S1bVW;Vst;Vtmax;A3A1S8G0A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma YF_0 : ltac2:(tb__ "0|0|
S38S10ScS10ScS10ScS10S59VW;Vst;A2S58S57A1A3S53A3S2dA3S14S0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma YP_0 : ltac2:(tb__ "0|0|
S37S10S17S15Z1A1S13S32A1A2S14S0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY1_0 : ltac2:(tb__ "0|0|
S4S6S12S0S44S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY2_0 : ltac2:(tb__ "0|0|
S4S6S12S0S45S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY3_0 : ltac2:(tb__ "0|0|
S4S6S12S0S46S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY4_0 : ltac2:(tb__ "0|0|
S4S6S12S0S47S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY5_0 : ltac2:(tb__ "0|0|
S4S6S12S0S48S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY6_0 : ltac2:(tb__ "0|0|
S4S6S12S0S49S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY7_0 : ltac2:(tb__ "0|0|
S4S6S12S0S43S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s3_0 : ltac2:(tb__ "0|0|
S40") := ltac2:(tb__ "0|0|
S3fS35S0S43S1bVW;Vst;Vtmax;A3A1A1S0S21VW;Vst;Vtmax;A3A1A3").
Lemma ENT3_0 : ltac2:(tb__ "0|0|
S4S6S2S43S1bVW;Vst;Vtmax;A3A1S21VW;Vst;Vtmax;A3S50A3S7A3").
Proof. unfold s3_0. cbv beta zeta delta [W st tmax s3_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID3_0 : ltac2:(tb__ "0|0|
S4S6S41S50S35A2S7A3").
Proof. unfold s3_0. cbv beta zeta delta [W st tmax s3_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert3r_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z40e58S5S33Z3c614S8S33A1A3A3S35S5S1S29VW;Vst;Vtmax;A3S8S1A1M0A3S5S1S2bVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert4_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z7e9e4S8S33A1A3S35S5S1S21VW;Vst;Vtmax;A3S8S1A1M0A3S5S1S2cVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert5_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z3c774S5S33Z3c80cS8S33A1A3A3S35S5S1S2aVW;Vst;Vtmax;A3S8S1A1M0A3S5S1S22VW;Vst;Vtmax;A3S5S1S20VW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s6n_0 : ltac2:(tb__ "0|0|
S40") := ltac2:(tb__ "0|0|
S3fS35S0S22VW;Vst;Vtmax;A3A1S0S26VW;Vst;Vtmax;A3A1A3").
Lemma ENT6n_0 : ltac2:(tb__ "0|0|
S4S6S2S22VW;Vst;Vtmax;A3S26VW;Vst;Vtmax;A3S51A3S7A3").
Proof. unfold s6n_0. cbv beta zeta delta [W st tmax s6n_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID6n_0 : ltac2:(tb__ "0|0|
S4S6S41S51S35A2S7A3").
Proof. unfold s6n_0. cbv beta zeta delta [W st tmax s6n_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W5b_0 : ltac2:(tb__ "0|0|
S4S6S12S0S1eVW;Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D5b_0 : ltac2:(tb__ "0|5|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S42S0S20VW;Vst;Vtmax;A3A1S0S1eVW;Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS3eS13S23A1M4A4S5G0SbSfSfS3dG4A4S8G0A1A3A3S8S10A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX5b_0 : ltac2:(tb__ "0|0|
S4S34S16S0S1eVW;Vst;Vtmax;A3A1A1S16S0S20VW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F5f64_0 : ltac2:(tb__ "0|0|
S37S10S17S13PcA1S15Zfc00A1A2S14S0S20VW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert5b_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z3c7e0S8S33A1A3S35S5S1S1eVW;Vst;Vtmax;A3S8S1A1M0A3S5S1S1cVW;Vst;Vtmax;A3S5S1S1dVW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma OV1_0 : ltac2:(tb__ "0|0|
S4S6S52P9eS24VW;Vst;Vtmax;A3A2S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma OV2_0 : ltac2:(tb__ "0|0|
S4S6S52P9eS25VW;Vst;Vtmax;A3A2S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma TAB1_0 : ltac2:(tb__ "0|0|
S4S6S3cP9eS24VW;Vst;Vtmax;A3S4cZ11UeA5S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma TAB2_0 : ltac2:(tb__ "0|0|
S4S6S3cP9eS25VW;Vst;Vtmax;A3S4cZ1U10A5S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W1'_0 : ltac2:(tb__ "0|0|
S4S6S12S0S3aU0Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax E5s1']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W2'_0 : ltac2:(tb__ "0|0|
S4S6S12S0S3bU0Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax E5s2']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D1'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S42S0S1cVW;Vst;Vtmax;A3A1S0S3aU0Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS24VW;Vst;Vtmax;A3S13S27A1A4S8G0A1A3S8S10A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E5s1']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D2'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S42S0S1dVW;Vst;Vtmax;A3A1S0S3bU0Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS25VW;Vst;Vtmax;A3S13S27A1A4S8G0A1A3S8S10A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E5s2']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX1'_0 : ltac2:(tb__ "0|0|
S4S34S16S0S3aU0Vst;Vtmax;A3A1A1S16S0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E5s1']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX2'_0 : ltac2:(tb__ "0|0|
S4S34S16S0S3bU0Vst;Vtmax;A3A1A1S16S0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E5s2']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F1gt_0 : ltac2:(tb__ "0|0|
S37S10S18S4bS15Z10A1S13S23A1A3S14S0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F2le_0 : ltac2:(tb__ "0|0|
S37S10S19S18S4bS15Z10A1S13S23A1A3A1S14S0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F1_64_0 : ltac2:(tb__ "0|0|
S37S10S17S13PcA1S15Zfc00A1A2S14S0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F2_64_0 : ltac2:(tb__ "0|0|
S37S10S17S13PcA1S15Zfc00A1A2S14S0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s1_0 : ltac2:(tb__ "0|0|
S40") := ltac2:(tb__ "0|0|
S3fS35S0S3aU0Vst;Vtmax;A3A1S0S1fVW;Vst;Vtmax;A3A1A3").
Definition s2_0 : ltac2:(tb__ "0|0|
S40") := ltac2:(tb__ "0|0|
S3fS35S0S3bU0Vst;Vtmax;A3A1S0S1fVW;Vst;Vtmax;A3A1A3").
Lemma ENT1_0 : ltac2:(tb__ "0|0|
S4S6S2S3aU0Vst;Vtmax;A3S1fVW;Vst;Vtmax;A3S4eA3S7A3").
Proof. unfold s1_0. cbv beta zeta delta [W st tmax E5s1' s1_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ENT2_0 : ltac2:(tb__ "0|0|
S4S6S2S3bU0Vst;Vtmax;A3S1fVW;Vst;Vtmax;A3S4fA3S7A3").
Proof. unfold s2_0. cbv beta zeta delta [W st tmax E5s2' s2_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID1_0 : ltac2:(tb__ "0|0|
S4S6S41S4eS35A2S7A3").
Proof. unfold s1_0. cbv beta zeta delta [W st tmax E5s1' s1_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID2_0 : ltac2:(tb__ "0|0|
S4S6S41S4fS35A2S7A3").
Proof. unfold s2_0. cbv beta zeta delta [W st tmax E5s2' s2_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
End INST.
End SpineCallocS5i.

