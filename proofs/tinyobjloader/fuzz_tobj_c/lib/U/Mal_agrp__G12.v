(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "SAlu"; "SPUle"; "SPAlign"; "SExt"; "SLBytes"; "SPBranch"; "SPNot"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "list"; "prod"; "nil"; "Some"; "option"; "false"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "@Corelib.Init.Logic"; "eq"; "and"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "SM1pre"; "SCsym"; "SN2pre"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "POST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "ia_mW"; "ia_sc"; "icnt0"; "ij"; "isize"; "iszc"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "rhoW"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "tier"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "UNIT"; "@Stdlib.ZArith.BinInt.Z"; "add"; "div"; "le"; "lt"; "mul"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G12.Mal_agrp_c4"; "LC_4_0"; "LC_4_1"; "LC_4_2"; "dC_4"; "dL_4_0"; "dL_4_1"; "dL_4_2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G12.Mal_agrp_c43"; "LC_43_0"; "LC_43_1"; "LC_43_2"; "LC_43_3"; "LC_43_4"; "LC_43_5"; "dC_43"; "dL_43_0"; "dL_43_1"; "dL_43_2"; "dL_43_3"; "dL_43_4"; "dL_43_5"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G12.Mal_agrp_c44"; "LC_44_0"; "LC_44_1"; "LC_44_2"; "dC_44"; "dL_44_0"; "dL_44_1"; "dL_44_2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G12.Mal_agrp_c45"; "LC_45_0"; "LC_45_1"; "LC_45_2"; "LC_45_3"; "dC_45"; "dL_45_0"; "dL_45_1"; "dL_45_2"; "dL_45_3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G12.Mal_agrp_c46"; "LC_46_0"; "LC_46_1"; "LC_46_2"; "dC_46"; "dL_46_0"; "dL_46_1"; "dL_46_2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC"; "SC_4"; "SC_43"; "SC_44"; "SC_45"; "SC_46"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_c4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_4 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_4 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_4 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS5aA2S10G0S32A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_4)). Qed.
Definition setsC_4 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_4)) in exact x).
Definition LC_4_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_4 0 SC_4) in exact x).
Definition dL_4_0 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_4_0 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_4_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S2fS1bA2S10G0S33A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_4_0)). Qed.
Definition setsL_4_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_4_0)) in exact x).
Definition LC_4_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_4 1 SC_4) in exact x).
Definition dL_4_1 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_4_1 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_4_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S30S1bA2S10G0S34A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_4_1)). Qed.
Definition setsL_4_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_4_1)) in exact x).
Definition LC_4_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_4 2 SC_4) in exact x).
Definition dL_4_2 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff LC_4_2 SN2pre with Some d => d | None => ([], []) end) in exact x).
Lemma sdL_4_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S31S1bA2S10G0S35A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_4_2)). Qed.
Definition setsL_4_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_4_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 4.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_4 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_4 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_4 (setp rhoB setsC_4))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_4 w setsC_4 (fst dC_4) (snd dC_4)); [reflexivity | reflexivity | exact sdC_4 | | | exact HSP].
    - cbn [fst dC_4]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_4) (snd dC_4) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_4 LC_4 (setp rhoB setsC_4) Q HkB (eq_trans runC_4 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 100 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 100)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 25).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 4 (usg ia) 25 12 6) by reflexivity.
      change (class_size 4) with 80. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 2012) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 23) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_4 0 SC_4) with LC_4_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_4_0 SN2pre setsL_4_0 (fst dL_4_0) (snd dL_4_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_4_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_4_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_4_0) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 23 2012 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_geu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 48)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 100 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 100))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 12).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 4 (usg ia) 25 12 6) by reflexivity.
      change (class_size 4) with 80. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 972) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 19) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_4 1 SC_4) with LC_4_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_4_1 SN2pre setsL_4_1 (fst dL_4_1) (snd dL_4_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_4_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_4_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_4_1) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 19 972 Hj Htot ltac:(lia) ltac:(lia))).
  -
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 100 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 100))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 6).
    { unfold icnt0. rewrite Hsc. rewrite icnt_small by lia. rewrite (small_cnt_eq 4 (usg ia) 25 12 6) by reflexivity.
      change (class_size 4) with 80. cbv zeta. repeat ltb_dec. cbv. reflexivity. }
    assert (Htot : itotal ia = 492) by (unfold itotal, isize; rewrite Hc0, Hsc; reflexivity).
    assert (Hj : ij ia = 15) by (unfold ij; rewrite Htot; vm_compute; reflexivity).
    assert (Harm : isize ia * icnt0 ia + UNIT <= PGSZ / 2) by (unfold isize; rewrite Hc0, Hsc; vm_compute; discriminate).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SN2pre)); [|apply (CONT_N Harm); [rewrite Hj, Hsc; cbv; lia | rewrite Hj; lia]].
    intros w' HSP'. change (lfs LC_4 2 SC_4) with LC_4_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_4_2 SN2pre setsL_4_2 (fst dL_4_2) (snd dL_4_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_4_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_4_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hj, ?Htot, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_4_2) (F_G ++ F_M ++ F_CTX ++ F_SZ ++ F_N) HagS' eq_refl eq_refl eq_refl (ZF_allN ia Hi 15 492 Hj Htot ltac:(lia) ltac:(lia))).
Qed.
End C.
End Mal_agrp_c4.

Module Mal_agrp_c45.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_45 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_45 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_45 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS5dA2S10G0S4eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_45)). Qed.
Definition setsC_45 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_45)) in exact x).
Definition LC_45_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_45 0 SC_45) in exact x).
Definition dL_45_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2dA1S2PcA1M1A4SbG0ScS0S0S1Z15550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfff00A1S2PacA1M4A4SbG0ScS0S0S1Zfff10A1S4S13G4G3A3A4SbG0ScS0S0S1ZcA1S2PafA1M5A4SbG0ScS0S0S1Z5a588A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a530A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z15540A1G2A4SbG0ScS0S0S1Z1c0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1c8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z340A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z348A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_45_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4aS19A2S10G0S4fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_45_0)). Qed.
Definition setsL_45_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_45_0)) in exact x).
Definition LC_45_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_45 1 SC_45) in exact x).
Definition dL_45_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2dA1S2PcA1M1A4SbG0ScS0S0S1Z15550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfff00A1S2PacA1M4A4SbG0ScS0S0S1Zfff10A1S4S13G4G3A3A4SbG0ScS0S0S1ZcA1S2PafA1M5A4SbG0ScS0S0S1Z5a588A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a530A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z15540A1G2A4SbG0ScS0S0S1Z1c0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1c8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z340A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z348A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_45_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4bS19A2S10G0S50A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_45_1)). Qed.
Definition setsL_45_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_45_1)) in exact x).
Definition LC_45_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_45 2 SC_45) in exact x).
Definition dL_45_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2dA1S2PcA1M1A4SbG0ScS0S0S1Z15550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7ff80A1S2PacA1M4A4SbG0ScS0S0S1Z7ff90A1S4S13G4G3A3A4SbG0ScS0S0S1Z6A1S2PafA1M5A4SbG0ScS0S0S1Z5a588A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a530A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z15540A1G2A4SbG0ScS0S0S1Z1c0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1c8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z340A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z348A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_45_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4cS19A2S10G0S51A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_45_2)). Qed.
Definition setsL_45_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_45_2)) in exact x).
Definition LC_45_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_45 3 SC_45) in exact x).
Definition dL_45_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2dA1S2PcA1M1A4SbG0ScS0S0S1Z15550A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3ffc0A1S2PacA1M4A4SbG0ScS0S0S1Z3ffd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z3A1M5S2PafA1M6A4SbG0ScS0S0S1Z5a588A1S4S13S4S14G1G5A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a530A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Z15540A1G2A4SbG0ScS0S0S1Z1c0A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z1c8A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z340A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z348A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6S1Z20A1A2SbS3S5S1Z1A1G6A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_45_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S4dS19A2S10G0S52A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_45_3)). Qed.
Definition setsL_45_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_45_3)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 45.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_45 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_45 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_45 (setp rhoB setsC_45))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_45 w setsC_45 (fst dC_45) (snd dC_45)); [reflexivity | reflexivity | exact sdC_45 | | | exact HSP].
    - cbn [fst dC_45]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_45) (snd dC_45) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_45 LC_45 (setp rhoB setsC_45) Q HkB (eq_trans runC_45 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 96)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 12).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 45 3) med_cnt_tab) with 24. change (class_size 45) with 87360. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_45 0 SC_45) with LC_45_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_45_0 SM1pre setsL_45_0 (fst dL_45_0) (snd dL_45_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_45_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_45_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_45_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 48)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 12).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 45 3) med_cnt_tab) with 24. change (class_size 45) with 87360. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_45 1 SC_45) with LC_45_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_45_1 SM1pre setsL_45_1 (fst dL_45_1) (snd dL_45_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_45_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_45_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_45_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 24)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 6).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 45 3) med_cnt_tab) with 24. change (class_size 45) with 87360. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_45 2 SC_45) with LC_45_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_45_2 SM1pre setsL_45_2 (fst dL_45_2) (snd dL_45_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_45_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_45_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_45_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 24 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 24))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 48 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 48))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 96 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 96))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 3).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 45 3) med_cnt_tab) with 24. change (class_size 45) with 87360. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_45 3 SC_45) with LC_45_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_45_3 SM1pre setsL_45_3 (fst dL_45_3) (snd dL_45_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_45_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_45_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_45_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c45.

Module Mal_agrp_c44.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_44 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_44 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_44 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS5cA2S10G0S46A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_44)). Qed.
Definition setsC_44 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_44)) in exact x).
Definition LC_44_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_44 0 SC_44) in exact x).
Definition dL_44_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2cA1S2PcA1M1A4SbG0ScS0S0S1Z12490A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfff00A1S2PacA1M4A4SbG0ScS0S0S1Zfff10A1S4S13G4G3A3A4SbG0ScS0S0S1ZeA1S2PafA1M5A4SbG0ScS0S0S1Z5a580A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a528A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z12480A1G2A4SbG0ScS0S0S1Z1b8A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1c0A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z338A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z340A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_44_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S43S19A2S10G0S47A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_44_0)). Qed.
Definition setsL_44_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_44_0)) in exact x).
Definition LC_44_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_44 1 SC_44) in exact x).
Definition dL_44_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2cA1S2PcA1M1A4SbG0ScS0S0S1Z12490A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfff00A1S2PacA1M4A4SbG0ScS0S0S1Zfff10A1S4S13G4G3A3A4SbG0ScS0S0S1ZeA1S2PafA1M5A4SbG0ScS0S0S1Z5a580A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a528A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z12480A1G2A4SbG0ScS0S0S1Z1b8A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1c0A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z338A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z340A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_44_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S44S19A2S10G0S48A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_44_1)). Qed.
Definition setsL_44_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_44_1)) in exact x).
Definition LC_44_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_44 2 SC_44) in exact x).
Definition dL_44_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2cA1S2PcA1M1A4SbG0ScS0S0S1Z12490A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7ff80A1S2PacA1M4A4SbG0ScS0S0S1Z7ff90A1S4S13G4G3A3A4SbG0ScS0S0S1Z7A1S2PafA1M5A4SbG0ScS0S0S1Z5a580A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a528A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z12480A1G2A4SbG0ScS0S0S1Z1b8A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1c0A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z338A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z340A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_44_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S45S19A2S10G0S49A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_44_2)). Qed.
Definition setsL_44_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_44_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 44.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_44 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_44 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_44 (setp rhoB setsC_44))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_44 w setsC_44 (fst dC_44) (snd dC_44)); [reflexivity | reflexivity | exact sdC_44 | | | exact HSP].
    - cbn [fst dC_44]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_44) (snd dC_44) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_44 LC_44 (setp rhoB setsC_44) Q HkB (eq_trans runC_44 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 112)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 14).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 44 3) med_cnt_tab) with 28. change (class_size 44) with 74880. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_44 0 SC_44) with LC_44_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_44_0 SM1pre setsL_44_0 (fst dL_44_0) (snd dL_44_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_44_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_44_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_44_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 56)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 14).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 44 3) med_cnt_tab) with 28. change (class_size 44) with 74880. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_44 1 SC_44) with LC_44_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_44_1 SM1pre setsL_44_1 (fst dL_44_1) (snd dL_44_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_44_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_44_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_44_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 56 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 56))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 112 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 112))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 7).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 44 3) med_cnt_tab) with 28. change (class_size 44) with 74880. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_44 2 SC_44) with LC_44_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_44_2 SM1pre setsL_44_2 (fst dL_44_2) (snd dL_44_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_44_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_44_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_44_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c44.

Module Mal_agrp_c46.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_46 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_46 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_46 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS5eA2S10G0S56A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_46)). Qed.
Definition setsC_46 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_46)) in exact x).
Definition LC_46_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_46 0 SC_46) in exact x).
Definition dL_46_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2eA1S2PcA1M1A4SbG0ScS0S0S1Z19990A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfff00A1S2PacA1M4A4SbG0ScS0S0S1Zfff10A1S4S13G4G3A3A4SbG0ScS0S0S1ZaA1S2PafA1M5A4SbG0ScS0S0S1Z5a590A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a538A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z19980A1G2A4SbG0ScS0S0S1Z1c8A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1d0A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z348A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z350A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_46_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S53S19A2S10G0S57A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_46_0)). Qed.
Definition setsL_46_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_46_0)) in exact x).
Definition LC_46_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_46 1 SC_46) in exact x).
Definition dL_46_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2eA1S2PcA1M1A4SbG0ScS0S0S1Z19990A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfff00A1S2PacA1M4A4SbG0ScS0S0S1Zfff10A1S4S13G4G3A3A4SbG0ScS0S0S1ZaA1S2PafA1M5A4SbG0ScS0S0S1Z5a590A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a538A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z19980A1G2A4SbG0ScS0S0S1Z1c8A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1d0A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z348A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z350A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_46_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S54S19A2S10G0S58A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_46_1)). Qed.
Definition setsL_46_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_46_1)) in exact x).
Definition LC_46_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_46 2 SC_46) in exact x).
Definition dL_46_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2eA1S2PcA1M1A4SbG0ScS0S0S1Z19990A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7ff80A1S2PacA1M4A4SbG0ScS0S0S1Z7ff90A1S4S13G4G3A3A4SbG0ScS0S0S1Z5A1S2PafA1M5A4SbG0ScS0S0S1Z5a590A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a538A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Z19980A1G2A4SbG0ScS0S0S1Z1c8A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1d0A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z348A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z350A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_46_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S55S19A2S10G0S59A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_46_2)). Qed.
Definition setsL_46_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_46_2)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 46.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_46 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_46 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_46 (setp rhoB setsC_46))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_46 w setsC_46 (fst dC_46) (snd dC_46)); [reflexivity | reflexivity | exact sdC_46 | | | exact HSP].
    - cbn [fst dC_46]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_46) (snd dC_46) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_46 LC_46 (setp rhoB setsC_46) Q HkB (eq_trans runC_46 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 80)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 10).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 46 3) med_cnt_tab) with 20. change (class_size 46) with 104832. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_46 0 SC_46) with LC_46_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_46_0 SM1pre setsL_46_0 (fst dL_46_0) (snd dL_46_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_46_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_46_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_46_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 40)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 10).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 46 3) med_cnt_tab) with 20. change (class_size 46) with 104832. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_46 1 SC_46) with LC_46_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_46_1 SM1pre setsL_46_1 (fst dL_46_1) (snd dL_46_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_46_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_46_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_46_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 40 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 40))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 80 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 80))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 5).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 46 3) med_cnt_tab) with 20. change (class_size 46) with 104832. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_46 2 SC_46) with LC_46_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_46_2 SM1pre setsL_46_2 (fst dL_46_2) (snd dL_46_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_46_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_46_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_46_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c46.

Module Mal_agrp_c43.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rC.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dC_43 : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SCsym) SC_43 with Some d => d | None => ([], []) end) in exact x).
Lemma sdC_43 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S1aS5bA2S10G0S3cA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dC_43)). Qed.
Definition setsC_43 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dC_43)) in exact x).
Definition LC_43_0 : sstate := ltac:(let x := eval vm_compute in (lfs LC_43 0 SC_43) in exact x).
Definition dL_43_0 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2bA1S2PcA1M1A4SbG0ScS0S0S1Z10000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfff00A1S2PacA1M4A4SbG0ScS0S0S1Zfff10A1S4S13G4G3A3A4SbG0ScS0S0G3S2PafA1M5A4SbG0ScS0S0S1Z5a578A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a520A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zfff0A1G2A4SbG0ScS0S0S1Z1b0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1b8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z330A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z338A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_43_0 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S36S19A2S10G0S3dA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_43_0)). Qed.
Definition setsL_43_0 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_43_0)) in exact x).
Definition LC_43_1 : sstate := ltac:(let x := eval vm_compute in (lfs LC_43 1 SC_43) in exact x).
Definition dL_43_1 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2bA1S2PcA1M1A4SbG0ScS0S0S1Z10000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Zfff00A1S2PacA1M4A4SbG0ScS0S0S1Zfff10A1S4S13G4G3A3A4SbG0ScS0S0G3S2PafA1M5A4SbG0ScS0S0S1Z5a578A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a520A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zfff0A1G2A4SbG0ScS0S0S1Z1b0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1b8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z330A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z338A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_43_1 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S37S19A2S10G0S3eA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_43_1)). Qed.
Definition setsL_43_1 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_43_1)) in exact x).
Definition LC_43_2 : sstate := ltac:(let x := eval vm_compute in (lfs LC_43 2 SC_43) in exact x).
Definition dL_43_2 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2bA1S2PcA1M1A4SbG0ScS0S0S1Z10000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z7ff80A1S2PacA1M4A4SbG0ScS0S0S1Z7ff90A1S4S13G4G3A3A4SbG0ScS0S0S1Z8A1S2PafA1M5A4SbG0ScS0S0S1Z5a578A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a520A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zfff0A1G2A4SbG0ScS0S0S1Z1b0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1b8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z330A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z338A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_43_2 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S38S19A2S10G0S3fA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_43_2)). Qed.
Definition setsL_43_2 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_43_2)) in exact x).
Definition LC_43_3 : sstate := ltac:(let x := eval vm_compute in (lfs LC_43 3 SC_43) in exact x).
Definition dL_43_3 : list (sv * sv) * list sprop := ltac2:(tb__ "0|9|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2bA1S2PcA1M1A4SbG0ScS0S0S1Z10000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z3ffc0A1S2PacA1M4A4SbG0ScS0S0S1Z3ffd0A1S4S13G4G3A3A4SbG0ScS0S0S1Z4A1S2PafA1M5A4SbG0ScS0S0S1Z5a578A1S4S13S4S14G1S1Z3A1A3M6S1Z5a420A1A3A4SbG0ScS0S0S1Z5a520A1S4S13G6S1Z5a3c8A1A3A4SbG0ScS0S0S1Zfff0A1G2A4SbG0ScS0S0S1Z1b0A1S4S13G6S1Z58A1A3A4M7SbG0ScS0S0S1Z1b8A1S4S13G6S1Z60A1A3A4SbG0G7SbG0ScS0S0S1Z330A1S4S13G6S1Z1d8A1A3A4M8SbG0ScS0S0S1Z338A1S4S13G6S1Z1e0A1A3A4SbG0G8SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G5S1Z20A1A2SbS3S5S1Z1A1G5A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_43_3 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S39S19A2S10G0S40A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_43_3)). Qed.
Definition setsL_43_3 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_43_3)) in exact x).
Definition LC_43_4 : sstate := ltac:(let x := eval vm_compute in (lfs LC_43 4 SC_43) in exact x).
Definition dL_43_4 : list (sv * sv) * list sprop := ltac2:(tb__ "0|a|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2bA1S2PcA1M1A4SbG0ScS0S0S1Z10000A1S4S13S2PbfA1M2S1Z10A1M3A3A4SbG0ScS0S0S1Z1ffe0A1S2PacA1M4A4SbG0ScS0S0S1Z1fff0A1M5S4S13G4G3A3A4SbG0ScS0S0S1Z2A1S2PafA1M6A4SbG0ScS0S0S1Z5a578A1S4S13S4S14G1S1Z3A1A3M7S1Z5a420A1A3A4SbG0ScS0S0S1Z5a520A1S4S13G7S1Z5a3c8A1A3A4SbG0ScS0S0S1Zfff0A1G2A4SbG0ScS0S0S1Z1b0A1S4S13G7S1Z58A1A3A4M8SbG0ScS0S0S1Z1b8A1S4S13G7S1Z60A1A3A4SbG0G8SbG0ScS0S0S1Z330A1S4S13G7S1Z1d8A1A3A4M9SbG0ScS0S0S1Z338A1S4S13G7S1Z1e0A1A3A4SbG0G9SfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G6S1Z20A1A2SbS3S5S1Z1A1G6A2SbS3S5G4S1Z800000A1A2SbS3S5G3G2A2SbS3S5G2G5A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_43_4 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S3aS19A2S10G0S41A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_43_4)). Qed.
Definition setsL_43_4 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_43_4)) in exact x).
Definition LC_43_5 : sstate := ltac:(let x := eval vm_compute in (lfs LC_43 5 SC_43) in exact x).
Definition dL_43_5 : list (sv * sv) * list sprop := ltac2:(tb__ "0|c|
ScSdSeS0S0A2M0A1SdS3A1SbG0ScS0S0S1Z2bA1S2PcA1M1A4SbG0ScS0S0S1Z10000A1M2S4S13S2PbfA1M3S1Z10A1M4A3A4SbG0ScS0S0S1Zfff0A1M5S2PacA1M6A4SbG0ScS0S0G2S4S13G6G4A3A4SbG0ScS0S0S1Z1A1M7S2PafA1M8A4SbG0ScS0S0S1Z5a578A1S4S13S4S14G1S1Z3A1A3M9S1Z5a420A1A3A4SbG0ScS0S0S1Z5a520A1S4S13G9S1Z5a3c8A1A3A4SbG0ScS0S0G5G3A4SbG0ScS0S0S1Z1b0A1S4S13G9S1Z58A1A3A4MaSbG0ScS0S0S1Z1b8A1S4S13G9S1Z60A1A3A4SbG0GaSbG0ScS0S0S1Z330A1S4S13G9S1Z1d8A1A3A4MbSbG0ScS0S0S1Z338A1S4S13G9S1Z1e0A1A3A4SbG0GbSfG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3SbS3S5G8S1Z20A1A2SbS3S5G7G8A2SbS3S5G6S1Z800000A1A2SbS3S5G4G3A2SbS3S5G3S1Z1fff0A1A2SbS3S5G1S1Z2fA1A2SfS3A1A3A3A3A3A3A3A4").
Lemma sdL_43_5 : ltac2:(tb__ "0|1|
S16S11SeSdSeS0S0A2A1SdS3A1A2M0A1S18S3bS19A2S10G0S42A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dL_43_5)). Qed.
Definition setsL_43_5 : list (positive * sv) := ltac:(let x := eval vm_compute in (scratch_of (fst dL_43_5)) in exact x).

Section C.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S2eS1cVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis Hsc : ia_sc ia = 43.
Let K := K_ia Kc ia.
Variable Q : assn.
Hypothesis CONT_M : ltac2:(tb__ "0|0|
S2bS29S26Z2A2S28S23Via;A1S27A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S19A4VQ;A3F_;").
Hypothesis CONT_N : ltac2:(tb__ "0|1|
S2aS28S2cS22Via;A1S20Via;A1A2S27A2S29S26Z2A2A2S2dS25S21Via;A1M0A1S25S1fVia;A1A1A2S17S2aZ0G0A2S2bG0Z30A2A2VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1bA4VQ;A3F_;F_;F_;").

Theorem cls_43 : ltac2:(tb__ "0|0|
VTR;VkB;S1dS1cVK;S24Via;S1eVia;A1A2S1aA4VQ;A3").
Proof using CONT_M CONT_N Hi HkB Hsc RR.
  pose proof (iok_sc ia Hi) as SC. rewrite Hsc in SC.
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  pose proof (agrees_setp (rhoW ia (ia_mW ia)) rhoB setsC_43 Hag eq_refl) as HagS.
  apply (trr_pre RR (SymSoundR.SP segsU K SC_43 (setp rhoB setsC_43))).
  { intros w [_ HSP].
    apply (relinkp segsU K rhoB (SCsym) SC_43 w setsC_43 (fst dC_43) (snd dC_43)); [reflexivity | reflexivity | exact sdC_43 | | | exact HSP].
    - cbn [fst dC_43]. solve_pairs ia Hi HagS ltac:(rewrite ?Hsc; reflexivity).
    - apply (nf_of_big ia _ (setp rhoB setsC_43) (snd dC_43) (F_G ++ F_M ++ F_CTX) HagS); [reflexivity | reflexivity | reflexivity | exact (ZF_all ia Hi)]. }
  apply ((trr_run RR) kB 500%nat CUTS_C K SC_43 LC_43 (setp rhoB setsC_43) Q HkB (eq_trans runC_43 eq_refl) eq_refl (K_ia_impl Kc ia)).
  intros Lf rho' Hin Hab.
  assert (HagL : agrees (rhoW ia (ia_mW ia)) rho') by (eapply agrees_below; [exact HagS | exact Hab | cbv; discriminate]).
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [lf_state]; (apply (trr_inh RR); [lia|]); intros w HSP.
  -
    pose proof (usg_geu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 128)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    assert (Hc0 : icnt0 ia = 16).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 43 3) med_cnt_tab) with 32. change (class_size 43) with 65520. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_43 0 SC_43) with LC_43_0 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_43_0 SM1pre setsL_43_0 (fst dL_43_0) (snd dL_43_0) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_43_0 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_43_0]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_43_0) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 64)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    assert (Hc0 : icnt0 ia = 16).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 43 3) med_cnt_tab) with 32. change (class_size 43) with 65520. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_43 1 SC_43) with LC_43_1 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_43_1 SM1pre setsL_43_1 (fst dL_43_1) (snd dL_43_1) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_43_1 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_43_1]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_43_1) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 32)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    assert (Hc0 : icnt0 ia = 8).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 43 3) med_cnt_tab) with 32. change (class_size 43) with 65520. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_43 2 SC_43) with LC_43_2 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_43_2 SM1pre setsL_43_2 (fst dL_43_2) (snd dL_43_2) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_43_2 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_43_2]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_43_2) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 16)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    assert (Hc0 : icnt0 ia = 4).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 43 3) med_cnt_tab) with 32. change (class_size 43) with 65520. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_43 3 SC_43) with LC_43_3 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_43_3 SM1pre setsL_43_3 (fst dL_43_3) (snd dL_43_3) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_43_3 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_43_3]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_43_3) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_geu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPBranch BC_GEU (SVar 192) (SLit 8)) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 2).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 43 3) med_cnt_tab) with 32. change (class_size 43) with 65520. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_43 4 SC_43) with LC_43_4 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_43_4 SM1pre setsL_43_4 (fst dL_43_4) (snd dL_43_4) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_43_4 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_43_4]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_43_4) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
  -
    pose proof (usg_ltu_of ia Hi 8 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 8))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U0.
    pose proof (usg_ltu_of ia Hi 16 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 16))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U1.
    pose proof (usg_ltu_of ia Hi 32 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 32))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U2.
    pose proof (usg_ltu_of ia Hi 64 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 64))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U3.
    pose proof (usg_ltu_of ia Hi 128 ltac:(lia) (leaf_factw ia _ K rho' _ w (SPNot (SPBranch BC_GEU (SVar 192) (SLit 128))) HagL HSP ltac:(cbn; tauto) eq_refl eq_refl)) as U4.
    assert (Hc0 : icnt0 ia = 1).
    { unfold icnt0. rewrite Hsc. rewrite icnt_med by lia. change (znth (Z.land 43 3) med_cnt_tab) with 32. change (class_size 43) with 65520. icnt_decide. }
    assert (Harm : PGSZ / 2 < iszc ia + UNIT) by (unfold iszc, isize; rewrite Hc0, Hsc; vm_compute; reflexivity).
    apply (trr_pre RR (POST segsU K (rhoW ia (ia_mW ia)) SM1pre)); [|exact (CONT_M Harm)].
    intros w' HSP'. change (lfs LC_43 5 SC_43) with LC_43_5 in HSP'.
    apply (linkp segsU K (rhoW ia (ia_mW ia)) LC_43_5 SM1pre setsL_43_5 (fst dL_43_5) (snd dL_43_5) rho' w'); [reflexivity | reflexivity | reflexivity | exact sdL_43_5 | exact HagL | | exact HSP'].
    intros HagS' _. split.
    + cbn [fst dL_43_5]. solve_pairs ia Hi HagS' ltac:(unfold iszc, isize; rewrite ?Hc0, ?Hsc; reflexivity).
    + exact (nf_of_big ia _ _ (snd dL_43_5) (F_G ++ F_M ++ F_CTX ++ F_SZ) HagS' eq_refl eq_refl eq_refl (ZF_allSZ ia Hi)).
Qed.
End C.
End Mal_agrp_c43.
