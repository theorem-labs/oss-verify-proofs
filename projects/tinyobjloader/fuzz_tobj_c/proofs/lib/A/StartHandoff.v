(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "rl"; "sobj"; "rm"; "smatch"; "ss_objs"; "sv"; "sprop"; "SLit"; "SVar"; "eval"; "sstate"; "holds"; "obj_range"; "sv_eqb"; "sprop_eqb"; "cell"; "ob_base"; "ob_lo"; "obj_holds"; "outside_all"; "ranges_disjoint"; "sprop_below"; "swf"; "DList"; "SPUle"; "SPUlt"; "enc_bytes"; "ob_cells"; "ob_dflt"; "ob_hi"; "obj_hi_of"; "odefault"; "rd"; "soff"; "ss_facts"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "modulo"; "div"; "of_nat"; "pow"; "leb"; "mul"; "opp"; "to_nat"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "pair"; "option"; "Some"; "length"; "prod"; "andb"; "cons"; "app"; "nil"; "nat"; "snd"; "false"; "negb"; "orb"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_ms"; "mkEntry"; "cfg_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "xr_ok"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "FdEntry"; "in_fs"; "m_fds"; "m_fs"; "vm_limit"; "m_vm_lazy"; "page_in_ranges"; "vm_noaccess"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR"; "Uv"; "std_fds"; "ZARG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8"; "MAIN_of"; "TPmain"; "m22"; "m23a"; "rhoOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "In"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoff"; "tpF"; "ZPAGES"; "obj_far_b"; "PA0"; "PR0"; "rho3M"; "rho3U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "rho_sub"; "rho_absorb"; "subst_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartArgBytes"; "RNDo"; "ARGC"; "LEN"; "argv0"; "STRo"; "A1o"; "argv1"; "L2U"; "L3"; "ms0A"; "RND16"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.StartHandoffBytes"; "cell_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_LO"; "SHADOW_BAND_HI"; "SHADOW_RW_LO_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoffLib"; "set_rl"; "state_vl_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape"; "binfo_eqb"; "zseq"; "binfo"; "byte_info"; "BNone"; "lit_small"; "BLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceM"; "facts_M"; "facts_U"; "S_M"; "S_U"; "objs_M"; "objs_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TP"; "RD_STAGE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7"; "out18"; "Q18"; "TP18"; "ZX18"; "out18_model"; "out18_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "ARGF"; "RMH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g5.StartHandoffStates"; "LU3"; "s2"; "sFM"; "sFU"; "vENDL"; "KN"; "LM2"; "LM3"; "LU2"; "vA1L"; "O_a1pL"; "S_M0"; "S_U0";
"add_objs"; "shape_deep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g5.StartHandoffApart"; "obj_low_b"; "ZLOW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartMain"; "M1"; "B0"; "QMain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartTop"; "Mmain"; "Bmain"; "Lmain"; "mA1"; "mB"; "mS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "virt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "rnd0"; "rnd1"; "Jinit"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "eqb"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "DEEP"; "X_rds"; "sp0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init"; "imgA"; "c0A"; "pcA"; "phA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "pages_rev"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoff.Main"; "sheet"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoff.Top"; "rho3M"; "rho3U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "valid_entry48"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork"; "PID_MAX_ENVELOPE"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvM"; "P0M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.MainJoin"; "P0U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start2"; "n5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start3"; "n6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4"; "m10"; "m11"; "m8"; "m9"; "n7"; "n9"; "priZ"; "spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5"; "m12"; "m13"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6"; "m16"; "n17"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8M"; "minv8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.StartBD"; "BDT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundI SymSoundM SymEntail SymCFG SymSummary SymFrame SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceM DrvIfaceT DrvIfaceR StartReshape StartHandoffLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoffLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g5.StartHandoffStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import TAddr.
Close Scope bv_scope. Open Scope Z_scope.

Lemma swf_s2 : ltac2:(tb__ "0|0|
S3bS0S3bS1fS7bSa6S53S66R1A1A1Pc2A3A1S3dA3Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma shape_deep_sound : ltac2:(tb__ "0|0|
S8S13S13S42S3cS57A1S4eA2S0S3fS13A1Sb3R3A1S40S13R2A2A3ScS4dR5R4R2A4ScS4dR6R4R3A4F_;F_;Fw;FS';FS;Frho;").
Proof.
  intros rho S S' w H Hsm. unfold shape_deep in H.
  destruct (rebase_obj_at S 1) as [S1|] eqn:E1; [|discriminate].
  destruct (merge_objs_at S1 0) as [S2|] eqn:E2; [|discriminate].
  apply (smatch_merge segsA rho S2 0 S' w H). apply (smatch_merge segsA rho S1 0 S2 w E2). apply (smatch_rebase segsA rho S 1 S1 w E1). exact Hsm.
Qed.

Lemma chain_M : ltac2:(tb__ "0|2|
S3bS8S3cS57A1M0S61S56S3cS3aQ8A1A1S0S3aQ40M1A1S7R5P2A2S39G1Z2A2A3ScS4dR6S53S66R7A1A1S3eG0S4eR5S4fR4R3A2A4A4SdS7bSa6S53S66R8A1A1Pc2A3A1S3cSaA1ScS4dS8bS7aR8R1R6A3P3R4A3SabR9A1S3eG0S4eR7S4fR6R5A2A4A4TL;F_;F_;Fbs3;Fmd;Fms;Ftr;Frho;Fv;").
Proof.
  intros v rho tr ms md bs3 H2 Hsm L.
  pose proof (reshape_M v) as (R1 & W1 & D1). pose proof (entails_M v) as (_ & _ & U3).
  apply smatch_set_rl; [exact U3|]. unfold LM2. apply smatch_drop_facts.
  apply (shape_deep_sound _ (LM1 v)); [exact D1|]. unfold LM1.
  apply (smatch_reshape segsA rho (subst_state s2 (ax_S (MAIN_of v)) 194%positive) TM tr ms md R1 W1).
  apply smatch_fold_const; [exact H2 | apply swf_s2 | exact Hsm].
Qed.

Lemma chain_U : ltac2:(tb__ "0|1|
S3bS8S3cS57A1M0S61S56S3cS3aQ8A1A1ScS4dR5S53S66R6A1A1S3eG0S4eR4S4fR3R2A2A4A4SdS53S66R7A1A1A1S3cSaA1ScS4dS8bS7aR7R1R5A3P2R3A3SadR8A1S3eG0S4eR6S4fR5R4A2A4A4TL;F_;Fbs2;Fmd;Fms;Ftr;Frho;Fv;").
Proof.
  intros v rho tr ms md bs2 Hsm L.
  pose proof (reshape_U v) as (R1 & W1 & D1). pose proof (entails_U v) as (_ & _ & U3).
  apply smatch_set_rl; [exact U3|]. unfold LU2. apply smatch_drop_facts.
  apply (shape_deep_sound _ (LU1 v)); [exact D1|]. unfold LU1.
  exact (smatch_reshape segsA rho (ax_S (MAIN_of v)) TU tr ms md R1 W1 Hsm).
Qed.

Lemma S_M_eq : ltac2:(tb__ "0|0|
S0S13S53S96A1Sd5Sb0S94A2A3"). Proof. reflexivity. Qed.
Lemma S_U_eq : ltac2:(tb__ "0|0|
S0S13S53S97A1Sd5Sb1S95A2A3"). Proof. reflexivity. Qed.
Lemma facts_M_below : ltac2:(tb__ "0|0|
S0S3bS6cSfS1ePbeA1S94A3S3dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma facts_U_below : ltac2:(tb__ "0|0|
S0S3bS6cSfS1ePbeA1S95A3S3dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma finish_M : ltac2:(tb__ "0|0|
S3bS8S42S3cS57A1S4eA2ScS4dR2SacR3A1R1A4S6fSfS14S79R3Sa7A2A1S94A3ScS4dS79R4Sa7A2S53S96A1R3A4F_;F_;Fw;Frho3;Fv;").
Proof.
  intros v rho3 w Hsm HF. pose proof (entails_M v) as (_ & E & _).
  rewrite S_M_eq. apply smatch_refacts; [| exact facts_M_below | exact HF].
  exact (entails_sound segsA (LM3 v) S_M0 sFM rho3 w E Hsm).
Qed.

Lemma finish_U : ltac2:(tb__ "0|0|
S3bS8S42S3cS57A1S4eA2ScS4dR2Sa5R3A1R1A4S6fSfS14S79R3Sa8A2A1S95A3ScS4dS79R4Sa8A2S53S97A1R3A4F_;F_;Fw;Frho3;Fv;").
Proof.
  intros v rho3 w Hsm HF. pose proof (entails_U v) as (_ & E & _).
  rewrite S_U_eq. apply smatch_refacts; [| exact facts_U_below | exact HF].
  exact (entails_sound segsA (LU3 v) S_U0 sFU rho3 w E Hsm).
Qed.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartHandoffCarve.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g5.StartHandoffApart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoffCarve.

Lemma LM2_low : ltac2:(tb__ "0|3|
S3bS1S0S3bS6cSaSb6Z10A1SdSabR1A1M0A1M1A3S3dA3S1S0S3bS6cSaSb6Z18A1S45SaG1S44SaSafS46SaA1A3M2A3A3S3dA3S0S3bS1fSb2G0G2A2A1S3dA3A2A2Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma LU2_low : ltac2:(tb__ "0|0|
S3bS0S3bS6cSaSb6Z10A1SdSadR1A1A1A3S3dA3Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma U_sub_nowrap : ltac2:(tb__ "0|3|
S3aQ40M0A1M1G1S2cS38G0R1A2S38G0R2A2M2A2S0S5S38G0Sc8SdaR3R2A3A2S2fS38G0R3A2G2A2A3F_;Fy;Fx;").
Proof.
  intros x y H. unfold alu64, alu. rewrite bv_sub_unsigned. pose proof (urange x). pose proof (urange y).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Lemma soff_of_U : ltac2:(tb__ "0|0|
S8SeS5S0S5S38Q40S12R3R2A2A2R1A3S2eR2S33Z2Z3fA2A2S0S5S2aR5R4A2R3A3F_;F_;Fz;Fe;Frho;").
Proof.
  intros rho e z H Hz. unfold soff. rewrite signed_small; [exact H|]. pose proof (urange (eval rho e)). lia.
Qed.

Lemma carve_M : ltac2:(tb__ "0|9|
S3bS8S3cS57A1M0S61S56ScS4dR4SabR5A1S3eG0S4eR3S4fR2R1A2A4A4S38Q40M1S7R5P1A2A2S5S38G1S12R6SaeA2A2S5S38G1S12R7Sa9A2A2S5S2cZ7fff80000000R3A2S2cS2dR4Z18A2R3A2S1S2cR4R3A2S2cR3S33Z2Z2fA2A2A2S0S5S32S41S3aQ8M2A1M3S9RbP3M4A2A2A1S2fR4R5A2A3S47Sb5R1U8M5A2S0S3fG3A1M6SbReS39G1S2dS2dR9Z10A2S32R2A1M7A2A2A2S40G3S70G3R2S23G5S12ReSaeA2A2S39G2Z0A2M8A4A2A3F_;Fj;S47Sb5R1S41G3S9ReG4A2A2A2S0G6SbRfS39G1S2dR9G7A2A2A2S40G3S70G3R2S9RfG4A2G8A4A2A3F_;Fj;ScS4dReSacRfA1S3eG0S4eRdS4fRcRbA2A4A4F_;F_;F_;F_;F_;F_;Te;Tb1;Tsp0;F_;Fmd;Fms;Ftr;Frho2;Fv;").
Proof.
  intros v rho2 tr ms md Hsm sp0 b1 e Hsp Hb1 He Hlen HB1 HB3.
  pose proof (LM2_low v) as (LO16 & LO24 & WF1). pose proof (entails_M v) as (WF3 & _).
  assert (EL3 : bv_unsigned (eval rho2 vL3L) = e - b1) by (unfold vL3L; cbn [eval]; fold vENDL vA1L; apply U_sub_nowrap; lia).

  assert (H1 : smatch segsA rho2 (add_objs (LM2 v) [O_a1pL]) (tr, mkCfg ms md)).
  { unfold add_objs. change O_a1pL with (win (SVar 1) 16 8 vA1L).
    replace ([]: list sprop) with (ss_facts (LM2 v)) by (destruct v; reflexivity).
    apply (smatch_carve_win segsA rho2 (LM2 v) (tr, mkCfg ms md) (SVar 1) 16 8 vA1L); try (cbn; lia).
    - exact Hsm.
    - exact WF1.
    - apply (objs_low_sound rho2 16); [exact LO16 | cbn [eval]; lia | cbn [eval]; lia].
    - intros j Hj. cbn [eval]. exact (HB1 j Hj). }

  pose proof (smatch_carve_listS segsA rho2 (add_objs (LM2 v) [O_a1pL]) (tr, mkCfg ms md) vA1L (SLit 0) vL3L 3%positive (ss_next (LM2 v)) H1) as X.
  cbv zeta in X. unfold add_objs in X. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in X.
  rewrite <- app_assoc in X. cbn [app] in X. change (list_objS vA1L (SLit 0) vL3L 3) with O_arg1L in X.
  rewrite soff_lit_small in X by lia. rewrite (soff_of_U rho2 vL3L (e - b1) EL3 ltac:(lia)) in X.
  unfold LM3, add_objs. apply X; clear X.
  - exact WF3.
  - lia.
  - lia.
  - fold b1. lia.
  - fold b1. lia.
  - rewrite Hlen. lia.
  - fold b1. rewrite Z.add_0_r. replace (b1 + (e - b1)) with e by lia. apply (objs_low_sound rho2 24); [exact LO24 | lia | lia].
  - fold b1. rewrite Z.add_0_r. exact HB3.
Qed.

Lemma carve_U : ltac2:(tb__ "0|5|
S3bS8S3cS57A1M0S61S56ScS4dR4SadR5A1S3eG0S4eR3S4fR2R1A2A4A4S38Q40M1S7R5P1A2A2S5S38G1S7R6P4A2A2S5S38G1S12R7Sa9A2A2S5S2cZ7fff80000000R3A2S2cS2dR4Z10A2R3A2S1S2cR4R3A2S2cR3S33Z2Z2fA2A2A2S0S5S32S41S3aQ8M2A1M3S9RbP2M4A2A2A1S2fR4R5A2A3S47Sb5R1S41G3S9RdG4A2A2A2S0S3fG3A1SbReS39G1S2dR8S32R2A1A2A2A2S40G3S70G3R2S9ReG4A2S39G2Z0A2A4A2A3F_;Fj;ScS4dRdSa5ReA1S3eG0S4eRcS4fRbRaA2A4A4F_;F_;F_;F_;F_;Te;Tb0;Tsp0;F_;Fmd;Fms;Ftr;Frho2;Fv;").
Proof.
  intros v rho2 tr ms md Hsm sp0 b0 e Hsp Hb0 He Hlen HB2.
  pose proof (LU2_low v) as LO16. pose proof (entails_U v) as (WF3 & _).
  assert (EL2 : bv_unsigned (eval rho2 vL2L) = e - b0) by (unfold vL2L; cbn [eval]; fold vENDL; apply U_sub_nowrap; cbn [eval]; lia).
  pose proof (smatch_carve_listS segsA rho2 (LU2 v) (tr, mkCfg ms md) (SVar 4) (SLit 0) vL2L 2%positive (ss_next (LU2 v)) Hsm) as X.
  cbv zeta in X. cbn [eval] in X. change (list_objS (SVar 4) (SLit 0) vL2L 2) with O_arg0L in X.
  rewrite soff_lit_small in X by lia. rewrite (soff_of_U rho2 vL2L (e - b0) EL2 ltac:(lia)) in X.
  replace (ss_facts (LU2 v)) with ([] : list sprop) in X by (destruct v; reflexivity).
  unfold LU3, add_objs. apply X; clear X.
  - exact WF3.
  - lia.
  - lia.
  - fold b0. lia.
  - fold b0. lia.
  - rewrite Hlen. lia.
  - fold b0. rewrite Z.add_0_r. replace (b0 + (e - b0)) with e by lia. apply (objs_low_sound rho2 16); [exact LO16 | lia | lia].
  - fold b0. rewrite Z.add_0_r. exact HB2.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Init Placement KxA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartArgBytes Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartTop StartMain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartArgBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.StartBD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8M OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8Out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartTop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.StartHandoffBlocks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g5.StartHandoffLits.

Lemma apart_disjoint : ltac2:(tb__ "0|2|
S8S61S3cSaA1S5S5S6fSaS1bS4dR5R4A3R3A3S2cZ0R3A2S2cR3S33Z2Z40A2A2S3aQ40M0A1S1S2cR6S38G0R1A2M1A2S2eG1R5A2A2S3S78RaR8R2A3A1F_;Fa;S6fSaSaS1dS15RaR1A2S3eS5S5R7R6A4A2Lo;R7A3F_;F_;F_;F_;Fhi;Flo;Fobjs;Fms;Frho;").
Proof.
  intros rho ms objs lo hi HO Hlo Hhi HA. apply Forall_forall. intros o Hin.
  pose proof (proj1 (Forall_forall _ _) HO o Hin) as ((B1 & B2 & B3 & _) & _). unfold obj_range, ranges_disjoint. cbn [fst snd].
  set (l := bv_unsigned (eval rho (ob_base o)) + obj_lo_of rho o) in *. set (h := bv_unsigned (eval rho (ob_base o)) + obj_hi_of rho o) in *.
  destruct (Z.le_gt_cases h l); [lia|]. destruct (Z.le_gt_cases hi lo); [lia|]. destruct (Z.le_gt_cases h lo); [lia|]. destruct (Z.le_gt_cases hi l); [lia|].
  exfalso. apply (HA (Z_to_bv 64 (Z.max lo l))).
  - rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
  - exists o. split; [exact Hin|]. unfold obj_range. cbn [fst snd]. fold l h. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.

Lemma obj_range_rwrl : ltac2:(tb__ "0|0|
S8S8SaS6S0S3aQ40A1S7R3R1A2S7R4R1A2A3Fi;S6S0S3cS3aQ8A1A1S9R4R1A2S9R5R1A2A3Fl;S0S42S5S5A2S15R4R3A2S15R5R3A2A3F_;F_;Fo;Frho';Frho;").
Proof.
  intros rho rho' o Hw Hl. unfold obj_range, obj_lo_of, obj_hi_of, soff. rewrite !(eval_ext_rwrl rho rho') by assumption. reflexivity.
Qed.
Lemma in_ranges_rwrl : ltac2:(tb__ "0|1|
S8S8S3cSaA1S3aQ40A1M0S6S0G0S7R4R1A2S7R5R1A2A3Fi;S6S0S3cS3aQ8A1A1S9R5R1A2S9R6R1A2A3Fl;S78R5R4R3A3S78R7R5R4A3F_;F_;F_;Fa;FL;Frho';Frho;").
Proof.
  intros rho rho' L a Hw Hl (o & Hin & Hr). exists o. split; [exact Hin|]. rewrite <- (obj_range_rwrl rho rho' o Hw Hl). exact Hr.
Qed.

Lemma nth_firstn_small : forall {A} (l : list A) n j d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n j d Hj; [destruct n; reflexivity|].
  destruct n as [|n]; [lia|]. destruct j as [|j]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma dlist_byte : ltac2:(tb__ "0|4|
S8S61SaS6S5S1bS4dR5R4R3A4S0S3cS18A1S24R4A1S46S18A1A3S0S28S25R5A1S20R4A1A3S0SeS1aR6A1S10Z0M0A1A3S1S2cG0R5A2S2eR5S27R9R7A2A2A2S0S3fS3aQ8M1A1M2A1S29R9S39Q40M3S2dS38G3S12RaS19R8A1A2A2R6A2A2A2S40G2S70G2S37R6A1S9RaR7A2S39G1G0A2A4A2A3F_;F_;F_;F_;F_;Foff;Fl;Fo;Fms;Frho;").
Proof.
  intros rho ms o l off (Hb & Hw & Hc & Hd & Hi) Hcells Hdf Hlo Hoff.
  rewrite Hdf in Hd. specialize (Hd off ltac:(unfold obj_lo_of; rewrite Hlo, soff_lit_small by lia; lia)).
  rewrite Hcells in Hd. specialize (Hd ltac:(intros X; inversion X)). cbn in Hd. unfold oaddr in Hd. unfold obj_lo_of in Hd. rewrite Hlo, soff_lit_small in Hd by lia.
  rewrite Z.sub_0_r in Hd. exact Hd.
Qed.

Lemma binfo_eqb_sound : ltac2:(tb__ "0|0|
S8fS8fS0S3bS8dR2R1A2S3dA3S0S8fR3R2A3F_;Fb;Fa;").
Proof. intros [| |x|] [| |y|] H; cbn in H; try discriminate; try reflexivity. apply Z.eqb_eq in H. subst. reflexivity. Qed.

Lemma U_add_neglit : ltac2:(tb__ "0|1|
S3aQ40M0A1S5S1S2cZ0R1A2S2cR1S38G0R2A2A2A2S0S5S38G0Sc8Sd9R3S39G0S36R2A1A2A3A2S2fS38G0R3A2R2A2A3F_;Fc;Fw;").
Proof.
  intros w c Hc. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (urange w). destruct (Z.eq_dec c 0) as [->|Hne].
  - rewrite Z.mod_0_l, Z.add_0_r, Z.mod_small by lia. lia.
  - replace (- c mod 2 ^ 64) with (2 ^ 64 - c). 2:{ rewrite <- (Z.mod_add (-c) 1 (2 ^ 64)) by lia. rewrite Z.mod_small; lia. }
    rewrite <- (Z.mod_add _ (-1) (2 ^ 64)) by lia. rewrite Z.mod_small; lia.
Qed.

Definition PA0 : Z := 0x7fffa000.
Definition PR0 : Z := 0x800ba000.
Definition tpF (tp : list word) : list word := ltac2:(tb__ "0|2|
S45S3aQ40A1M0Sd0S75U2M1A2S45G0Sd0S74G1A2Vtp;A3A3").
Definition ZPAGES (z : Z) : Prop := ltac2:(tb__ "0|1|
S4S1S2cS74Vz;A2S2eVz;S2dS74Z2000M0A2A2A2S1S2cS75Vz;A2S2eVz;S2dS75G0A2A2A2A2").

Lemma ZPAGES_ZLOW : ltac2:(tb__ "0|0|
S5S72R1A1Sb7R2A1F_;Fz;").
Proof. intros z Hz. unfold ZPAGES, ZLOW, PA0, PR0 in *. lia. Qed.

Lemma length_tpF : ltac2:(tb__ "0|1|
S3cS3aQ40A1M0A1S0S47S41G0S71R1A1A2Sd7U4S41G0R1A2A2A3Ftp;").
Proof. intros tp. unfold tpF. rewrite !length_app, !length_pages_rev. lia. Qed.

Lemma stage1 : ltac2:(tb__ "0|d|
S54S56S5S8S3cS3aQ40M0A1M1A1M2S3cS57A1M3S61S56SdS53R8A1A1S3cSaA1Sb4S4dS9cR8R7A2R9R6R5S3eG3S4eR4S4fR3R2A2A4A6G1S2cS88S38G0R1A2M4A2S2cS2dS38G0R2A2M5Z1000A2S8aA2S0S3bS5fR3S5eRcA1A2S3dA3F_;F_;Fp;S5S1S2cS88R1A2S2eR1S8aA2A2S0S3bSefS60S58RcA1A1R2A2S49A3F_;Fz;S2cS2dRaZ4000M6A2S5dS58RbA1A1A2G1S6eG1R1RaA3S3S72G5A1A1F_;Fp;G1S5S2cZ0M7R1A2S5S1S2cS38G0R4A2M8R1A2S2eR1S2dG8R3A2A2A2Sb7R2A1F_;Fy;S6fSaSaS1dS15R10R1A2S3eS5S5S38G0R5A2M9S2dG9R4A2A4A2Lo;RaA3F_;F_;Fn;Fa;S2S8S8S1Sb4S4dS8G2G3S56S9cR13S2dR12G6A2R4S71R10A1R2R1A6Lmd0;Ltr0;L_;Lr;R10R1S71RcA1S3eG3S4eRbS4fRaR9A2A4A6S1S6S0G1S7R2R1A2S7ReR1A2A3Fi;S1S6S0S3cS3aQ8MaA1MbA1S9R2R1A2S9ReR1A2A3Fl;S1S5S72R1A1S0S3fGbA1McSbR3S39G0R2A2A2S40GbS39GaG7A2A2A3F_;Fa;G1S3S72G4A1A1S0GcSbR3R2A2SbRfR2A2A3F_;Fa;A2A2A2A2Lrho1;A2F_;F_;F_;F_;F_;F_;TL;Fmd;Fms;Ftr;Ftp;Frho;FBm;FMm;FA;").
Proof.
  intros A Mm Bm rho tp tr ms md L Hsp Hlz Hacc HB NIN HDJ.
  pose proof Hsp as [Hsm (Htr & Hem & Hpaid)]. cbn [w_tr w_cfg cfg_model fst snd] in Htr, Hem, Hpaid.
  pose proof (erase_mat_eq_fields md Mm Hem) as (Evm & Elz & _).
  set (J' := fun (r : valuation) (_ : list word) (tr0 : list event) (md0 : Model) => KxA Mm (Bm + 16384) r (tpF tp) tr0 md0).
  assert (HJ' : forall r r' t t', J' r t tr md -> J' r' t' tr md) by (intros r r' t t' X; exact X).
  assert (PB : paid md (tpF tp) <= Bm + 16384).
  { unfold tpF. pose proof (paid_app_le md (pages_rev PR0 2) (pages_rev PA0 2 ++ tp)). pose proof (paid_app_le md (pages_rev PA0 2) tp).
    rewrite !length_pages_rev in *. unfold page_size in *. lia. }
  assert (Hsp0 : SPA segsA J' A rho tp (tr, mkCfg ms md)).
  { split; [exact Hsm|]. subst J'. cbv beta. split; [exact Htr|]. split; [exact Hem|]. exact PB. }

  destruct (SPA_prepay_pages_rm J' A PA0 2 rho tp tr ms md Hsp0 HJ' eq_refl ltac:(unfold PA0; lia) ltac:(unfold PA0; lia)) as (rhoa & Hspa & RWa & RLa & Za & Oa).
  - intros k Hk. rewrite Elz. apply Hlz; unfold pageZ, PA0; rewrite u64_of_lit by lia; unfold SHADOW_BAND_LO, SHADOW_RW_LO_END; lia.
  - intros k Hk Hin. apply (NIN _ Hin). unfold pageZ, ZPAGES, PA0. rewrite u64_of_lit by lia. lia.
  - intros z Hz. rewrite Evm. apply Hacc. unfold PA0, SHADOW_BAND_LO, SHADOW_RW_LO_END in *. lia.
  - unfold headroom. rewrite Evm. unfold page_size in *. lia.
  - apply (HDJ (Z_to_bv 64 PA0) (4096 * Z.of_nat 2)); [lia|]. intros y Hy. rewrite u64_of_lit in Hy by (unfold PA0; lia). unfold ZLOW, PA0 in *. lia.
  -
    assert (HDJa : forall (a : word) n, 0 <= n -> (forall y, bv_unsigned a <= y < bv_unsigned a + n -> ZLOW y) ->
              Forall (fun o => ranges_disjoint (obj_range rhoa o) (bv_unsigned a, bv_unsigned a + n)) L).
    { intros a n Hn HZ. apply Forall_forall. intros o Hin. rewrite (obj_range_rwrl rho rhoa o RWa RLa). exact (proj1 (Forall_forall _ _) (HDJ a n Hn HZ) o Hin). }
    destruct (SPA_prepay_pages_rm J' A PR0 2 rhoa (pages_rev PA0 2 ++ tp) tr ms md Hspa HJ' eq_refl ltac:(unfold PR0; lia) ltac:(unfold PR0; lia)) as (rhob & Hspb & RWb & RLb & Zb & Ob).
    + intros k Hk. rewrite Elz. apply Hlz; unfold pageZ, PR0; rewrite u64_of_lit by lia; unfold SHADOW_BAND_LO, SHADOW_RW_LO_END; lia.
    + intros k Hk Hin. apply in_app_iff in Hin as [Hin|Hin].
      * apply In_pages_rev in Hin as (k' & Hk' & E). apply (f_equal bv_unsigned) in E. unfold pageZ, PR0, PA0 in E. rewrite !u64_of_lit in E by lia. lia.
      * apply (NIN _ Hin). unfold pageZ, ZPAGES, PR0. rewrite u64_of_lit by lia. lia.
    + intros z Hz. rewrite Evm. apply Hacc. unfold PR0, SHADOW_BAND_LO, SHADOW_RW_LO_END in *. lia.
    + unfold headroom. rewrite Evm. pose proof (paid_app_le md (pages_rev PA0 2) tp) as PL. rewrite length_pages_rev in PL. unfold page_size in *. lia.
    + apply (HDJa (Z_to_bv 64 PR0) (4096 * Z.of_nat 2)); [lia|]. intros y Hy. rewrite u64_of_lit in Hy by (unfold PR0; lia). unfold ZLOW, PR0 in *. lia.
    + exists rhob. fold (tpF tp) in Hspb. split; [exact Hspb|].
      split; [intros i; rewrite RWb; apply RWa|]. split; [intros l; rewrite RLb; apply RLa|]. split.
      * intros a Ha. unfold ZPAGES, PA0, PR0 in Ha. destruct Ha as [Ha|Ha].
        -- rewrite Ob by (rewrite u64_of_lit by lia; unfold PR0; lia). apply Za. unfold PA0. lia.
        -- apply Zb. unfold PR0. lia.
      * intros a Ha. unfold ZPAGES in Ha. rewrite Ob by lia. apply Oa. lia.
Qed.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.StartHandoffBytes.

Lemma cells20 : ltac2:(tb__ "0|a|
S3bS1S0S3fS42S5SeA2M0A1M1S87SdS7bSa6S53S66R1A1A1M2Pc2A3A1M3S11P6A1M4Z0M5A3S40G0S3eS5SeZ8M6S11P9A1A4A2M7A3S1S0G1S87G3G4G6A3S40G0S3eS5SeG6S11PaA1A4A2M8A3S1S0G1S87SdG2A1M9G4G5A3G7A3S0G1S87G9G4G6A3G8A3A2A2A2Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Section Top.
Variables (sp brk mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
Hypothesis Hent : ltac2:(tb__ "0|0|
Sd6SccS51Vsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Hypothesis Hlim : 2 ^ 25 <= lim.

Local Notation ARGC := (StartArgBytes.ARGC inp).
Local Notation argv0 := (StartArgBytes.argv0 inp).
Local Notation argv1 := (StartArgBytes.argv1 inp).
Local Notation STRo := (StartArgBytes.STRo inp).
Local Notation A1o := (StartArgBytes.A1o inp).
Local Notation RNDo := (StartArgBytes.RNDo inp).
Local Notation LEN := (StartArgBytes.LEN inp).
Local Notation L3 := (StartArgBytes.L3 sp draw inp).
Local Notation L2U := (StartArgBytes.L2U sp draw inp).
Local Notation RND16 := (StartArgBytes.RND16 draw).
Local Notation ms0A := (StartArgBytes.ms0A sp draw inp).
Local Notation arg_nums := (StartArgBytes.arg_nums sp brk mb draw inp Hent Hinp).

Lemma rand_byte : ltac2:(tb__ "0|e|
S3bS13S8S3cS57A1M0S61S56S5ScS4dR5R6S3eG0S4eR4S4fR3R2A2A4A4S0S3fS42S5SeA2M1A1M2S87SdR7A1S11P6M3A1M4Z0M5A3S40G1S3eS5SeZ8M6S11P9M7A1A4A2A3S0G2S87SdR8A1G4G6A3S40G1S3eS5SeG6S11PaM8A1A4A2A3S0S3aQ40M9A1MaS7R8G7A2Sc2Vdraw;A1A3S0GaS7R9G8A2Sc3Vdraw;A1A3S0S5S38G9S7RaG3A2A2S2dS38G9Vsp;A2S7cVinp;A1A2MbA3S1S2cG5R7A2S2eR7Z10A2A2S0S3fS3aQ8McA1MdA1SbS7aRcSdRdA1RaA3S39G9S2dGbR8A2A2A2S40GdS70GdS37R8A1S86Vdraw;A1S39GcG5A2A4A2A3F_;F_;F_;F_;F_;F_;F_;Fk;Fmd;Fms;Ftr;Frho1;FS;Fv;").
Proof.
  intros v S rho1 tr ms md k Hsm C0 C8 E9 E10 U6 Hk.
  pose proof arg_nums as (Nsp & Nfit & N16 & Nargc & Nstr & Nstr8 & NA1 & NA1b & Nrnd & Npad & Nrnd8 & Nlen & Nlenb & Nlen0 & Ntab1 & Ntab2).
  set (rho2 := rho_absorb rho1 (ss_objs S) ms).
  assert (RM2i : forall a : word, in_ranges rho1 (ss_objs S) a -> rm rho2 a = ms_mem ms a) by (intros a Ha; apply rm_reshape_inside; exact Ha).
  assert (IMN : image_byte segsA (Z_to_bv 64 (bv_unsigned sp + RNDo + k)) = None) by (apply image_byte_none_A; rewrite u64_of_lit by lia; lia).
  destruct (Z_lt_ge_dec k 8) as [H8|H8].
  - pose proof (handoff_cell rho1 rho2 S tr ms md (SVar 6) 0 8 (SVar 9%positive) Hsm RM2i C0) as (_ & _ & HC).
    specialize (HC (Z.to_nat k) ltac:(lia)). cbn [eval] in HC. rewrite U6, E9, Z2Nat.id in HC by lia.
    replace (bv_unsigned sp + RNDo + 0 + k) with (bv_unsigned sp + RNDo + k) in HC by lia.
    rewrite view_in in HC by lia. unfold Glue.rd_of in HC. rewrite IMN in HC.
    destruct (rm rho2 (Z_to_bv 64 (bv_unsigned sp + RNDo + k))) as [b|]; [|discriminate]. rewrite HC. f_equal.
    rewrite (RND16_cell0 draw) by lia. rewrite word_le8_enc. reflexivity.
  - pose proof (handoff_cell rho1 rho2 S tr ms md (SVar 6) 8 8 (SVar 10%positive) Hsm RM2i C8) as (_ & _ & HC).
    specialize (HC (Z.to_nat (k - 8)) ltac:(lia)). cbn [eval] in HC. rewrite U6, E10, Z2Nat.id in HC by lia.
    replace (bv_unsigned sp + RNDo + 8 + (k - 8)) with (bv_unsigned sp + RNDo + k) in HC by lia.
    rewrite view_in in HC by lia. unfold Glue.rd_of in HC. rewrite IMN in HC.
    destruct (rm rho2 (Z_to_bv 64 (bv_unsigned sp + RNDo + k))) as [b|]; [|discriminate]. rewrite HC. f_equal.
    rewrite (RND16_cell1 draw) by lia. rewrite word_le8_enc. replace (Z.to_nat k - 8)%nat with (Z.to_nat (k - 8)) by lia. reflexivity.
Qed.

Definition rho3M (v : bool) (rho1 : valuation) (ms : machine_state) (bs3 : list byte) (n9 : Z) : valuation := ltac2:(tb__ "0|0|
SeeS8bS7aVrho1;SdS7bSa6S53S66Vv;A1A1Pc2A3A1Vms;A3P3Vbs3;A3SaaS39Q40Vn9;A2A3").

Lemma stage2_M : ltac2:(tb__ "0|d|
S3bS8S3cS57A1M0S61S56S66R5A1S54SdS53R1A1A1S3cSaA1ScS4dR6S53R2A1S3eG0S4eR5S4fR4R3A2A4A4S2cZ2M1S7dVinp;A1A2S0S3aQ40M2A1M3S7R8P2A2S39G2G1A2A3S0G3S7R9P1A2Vsp;A3S0G3S7RaP4A2S39G2S2dS38G2Vsp;A2M4S80Vinp;A1A2A2A3S0G3S7RbP5A2S39G2S32S41S3aQ8A1M5S7fVinp;A1A2A1A2A3S0G3S7RcP6A2S39G2S2dG4S7cVinp;A1A2A2A3S0G3S7RdP9A2Sc2Vdraw;A1A3S0G3S7RePaA2Sc3Vdraw;A1A3G3Sa3R10R1A2S0S3fG5A1M6SbR11R2A2S62S85Vsp;Vdraw;Vinp;A3R2A2A3F_;Fa;G3Sa3R11R1A2S3S78R12RdR2A3A1F_;Fa;Sd2R12R11RfS84Vsp;Vdraw;Vinp;A3M7S32S41G5S82Vinp;A1A2A1M8A5S8S1ScS4dR1SacR13A1S3eG0S4eR11S4fR10RfA2A4A4S1S6S3S0S6R1SaaA3A1S0G3S7R3R2A2S7R14R2A2A3F_;Fi;S1S0G3S7R1SaaA2S39G2G8A2A3S1S0S3cG5A1M9S9R1P3MaA2G7A3S1S6S3S0S6R1GaA3A1S0G9S9R3R2A2S9R14R2A2A3F_;Fl;S1G3S3S78R13ReR1A3MbA1S0G6SbR3R2A2McSbR14R2A2A3F_;Fa;S1G3GbS0G6GcS62R12R2A2A3F_;Fa;S1S0S5S38G2S12R12SaeA2A2S2dG4S81Vinp;A1A2A3S0S5S38G2S12R12Sa9A2A2S2dG4S7eVinp;A1A2A3A2A2A2A2A2A2A2A2Trho3;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TL0;TA;Fmd;Fms;Ftr;Frho1;Fv;").
Proof.
  intros v rho1 tr ms md A L0 Hsm H2 E2 E1 E4 E5 E6 E9 E10 HRM AP rho3.
  pose proof arg_nums as (Nsp & Nfit & N16 & Nargc & Nstr & Nstr8 & NA1 & NA1b & Nrnd & Npad & Nrnd8 & Nlen & Nlenb & Nlen0 & Ntab1 & Ntab2).
  pose proof (Zle_0_nat (tab (in_argv inp))) as T0. pose proof (Zle_0_nat (tab (in_envp inp))) as T1. pose proof (Zle_0_nat (pad_len (in_argv inp) (in_envp inp))) as T2.
  pose proof (Zle_0_nat (length argv0)) as T3.

  assert (U1 : bv_unsigned (rw rho1 1%positive) = bv_unsigned sp) by (rewrite E1; reflexivity).
  assert (U4 : bv_unsigned (rw rho1 4%positive) = bv_unsigned sp + STRo) by (rewrite E4, u64_of_lit by lia; reflexivity).
  assert (U5 : bv_unsigned (rw rho1 5%positive) = Z.of_nat (length argv0)) by (rewrite E5, u64_of_lit by lia; reflexivity).
  assert (U6 : bv_unsigned (rw rho1 6%positive) = bv_unsigned sp + RNDo) by (rewrite E6, u64_of_lit by lia; reflexivity).
  assert (U2 : bv_unsigned (rw rho1 2%positive) = 2) by (rewrite E2; reflexivity).
  assert (UA : bv_unsigned (eval rho1 vA1L) = bv_unsigned sp + A1o).
  { unfold vA1L. cbn [eval]. rewrite U_add_small; [| lia | rewrite U_add_words by lia; lia]. rewrite U_add_words by lia. lia. }
  assert (UE : bv_unsigned (eval rho1 vENDL) = bv_unsigned sp + LEN).
  { unfold vENDL. cbn [eval]. rewrite U_add_small by lia. lia. }
  set (L := ss_objs (subst_state s2 (ax_S A) 194%positive)).
  assert (EQL : forall a, in_ranges rho1 L a <-> in_ranges rho1 L0 a) by (intros a; apply (in_ranges_subst_const rho1 2%positive 2 L0 a 194%positive (ax_S A) E2 eq_refl)).
  set (rho2 := set_rl (rho_absorb rho1 L ms) 3%positive L3).
  assert (RM2o : forall a : word, ~ in_ranges rho1 L0 a -> rm rho2 a = rm rho1 a).
  { intros a Ha. unfold rho2, set_rl. cbn [rm]. apply rm_reshape_outside. intros X. apply Ha. apply EQL. exact X. }
  assert (RM2i : forall a : word, in_ranges rho1 L0 a -> rm rho2 a = ms_mem ms a).
  { intros a Ha. unfold rho2, set_rl. cbn [rm]. apply rm_reshape_inside. apply EQL. exact Ha. }

  pose proof (chain_M v rho1 tr ms md L3 E2 Hsm) as C1. cbv zeta in C1. fold L in C1. fold rho2 in C1.

  pose proof (length_L3 sp brk mb draw inp Hent Hinp) as LL3.
  assert (RL2 : rl rho2 3%positive = L3) by (unfold rho2, set_rl; cbn [rl]; rewrite Pos.eqb_refl; reflexivity).
  assert (RW2 : forall i, rw rho2 i = rw rho1 i) by (intros i; reflexivity).
  assert (EVA : eval rho2 vA1L = eval rho1 vA1L) by reflexivity. assert (EVE : eval rho2 vENDL = eval rho1 vENDL) by reflexivity.
  pose proof (smatch_fold_const segsA rho1 (ax_S A) (tr, mkCfg ms md) 2%positive 2 194%positive E2 (swf_s2 v) Hsm) as SM1.
  pose proof (cells20 v) as (C0 & C8 & _).
  assert (C2 : smatch segsA rho2 (LM3 v) (tr, mkCfg ms md)).
  { apply (carve_M v rho2 tr ms md C1); rewrite ?RW2, ?EVA, ?EVE, ?RL2, ?UA, ?UE, ?U1.
    - lia.
    - lia.
    - lia.
    - rewrite LL3. lia.
    -
      intros j Hj.
      assert (AF : ARGF rho1 (Z_to_bv 64 (bv_unsigned sp + 16 + Z.of_nat j))).
      { unfold ARGF. rewrite u64_of_lit by lia. lia. }
      rewrite (RM2o _ (AP _ AF)), (HRM _ AF). rewrite (a1p_word sp brk mb draw inp Hent Hinp H2 j Hj). f_equal.
      rewrite (word_le8_enc (Z_to_bv 64 (bv_unsigned sp + A1o))). f_equal. f_equal. apply bv_eq. rewrite u64_of_lit by lia. symmetry; exact UA.
    -
      intros j Hj. destruct (Z_lt_ge_dec (A1o + Z.of_nat j) RNDo) as [Hfr|Hrnd].
      + assert (AF : ARGF rho1 (Z_to_bv 64 (bv_unsigned sp + A1o + Z.of_nat j))).
        { unfold ARGF. rewrite u64_of_lit by lia. lia. }
        rewrite (RM2o _ (AP _ AF)), (HRM _ AF). exact (L3_byte sp brk mb draw inp Hent Hinp j Hj).
      + assert (Hj' : Z.of_nat j < LEN - A1o) by (rewrite <- LL3; apply (proj1 (Nat2Z.inj_lt _ _)); exact Hj).
        unfold rho2, set_rl. cbn [rm]. subst L. unfold s2.
        replace (bv_unsigned sp + A1o + Z.of_nat j) with (bv_unsigned sp + RNDo + (A1o + Z.of_nat j - RNDo)) by lia.
        rewrite (rand_byte v _ rho1 tr ms md (A1o + Z.of_nat j - RNDo) SM1 C0 C8 E9 E10 U6 ltac:(lia)). f_equal.
        unfold StartArgBytes.L3. rewrite nth_skipn.
        replace (Z.to_nat A1o + j)%nat with (Z.to_nat RNDo + Z.to_nat (A1o + Z.of_nat j - RNDo))%nat by lia.
        symmetry. apply (BSB_rand sp draw inp). lia. }

  pose proof (LM3_noKN v) as [NO9 _].
  assert (C3 : smatch segsA rho3 (LM3 v) (tr, mkCfg ms md)).
  { unfold rho3, rho3M. fold A. fold L. fold rho2.
    apply (smatch_agree_vl (fun i => negb (Pos.eqb i KN)) (fun _ => true) rho2); [| intros; reflexivity | reflexivity | exact NO9 | exact C2].
    intros i Hi. destruct (Pos.eqb_spec i KN) as [E|NE]; [discriminate|]. symmetry. apply rho_set_rw_other. exact NE. }
  split; [exact C3|].
  split; [intros i Hi; unfold rho3, rho3M; rewrite rho_set_rw_other by exact Hi; reflexivity|].
  split; [unfold rho3, rho3M; apply rho_set_rw_at|].
  split; [unfold rho3, rho3M; cbn [rl rho_set_rw set_rl]; rewrite Pos.eqb_refl; reflexivity|].
  split; [intros l Hl; unfold rho3, rho3M; cbn [rl rho_set_rw set_rl]; destruct (Pos.eqb_spec l 3); [contradiction | reflexivity]|].
  split; [intros a Ha; unfold rho3, rho3M; cbn [rm rho_set_rw set_rl]; fold A L; exact (RM2o a Ha)|].
  split; [intros a Ha; unfold rho3, rho3M; cbn [rm rho_set_rw set_rl]; fold A L; exact (RM2i a Ha)|].
  split; [exact UA | exact UE].
Qed.

Lemma argv1_fits : ltac2:(tb__ "0|1|
S2cZ2S7dVinp;A1A2S1S2cS2dS2dS81Vinp;A1S32S41S3aQ8A1S82Vinp;A1A2A1M0A2Z1A2S7cVinp;A1A2S2cG0Z1ffffA2A2F_;").
Proof.
  intros H2. pose proof arg_nums as (Nsp & Nfit & N16 & Nargc & Nstr & Nstr8 & NA1 & NA1b & Nrnd & Npad & Nrnd8 & Nlen & Nlenb & Nlen0 & Ntab1 & Ntab2).
  pose proof Hinp as ((_ & _ & Hlen & _) & _).
  unfold StartArgBytes.ARGC, StartArgBytes.argv1, StartArgBytes.argv0, StartArgBytes.A1o in *. destruct (in_argv inp) as [|a0 [|a1 r]]; cbn in H2; try lia.
  cbn [nth]. cbn [nth] in NA1. split.
  - assert (T : Z.of_nat (tab (a0 :: a1 :: r)) = Z.of_nat (length a0) + 1 + Z.of_nat (length a1) + 1 + Z.of_nat (tab r)) by (cbn [tab]; lia).
    pose proof (Zle_0_nat (tab r)). pose proof (Zle_0_nat (tab (in_envp inp))). pose proof (Zle_0_nat (pad_len (a0 :: a1 :: r) (in_envp inp))). lia.
  - apply Forall_inv_tail in Hlen. apply Forall_inv in Hlen. exact Hlen.
Qed.

Lemma factsM_hold : ltac2:(tb__ "0|11|
S3bS8S61S2cZ2S7dVinp;A1A2S0S3aQ40M0A1M1S7R3P1M2A2Vsp;A3S0G1S7R4P4M3A2S39G0S2dS38G0Vsp;A2M4S80Vinp;A1A2A2A3S0G1S7R5P5M5A2S39G0S32S41S3aQ8A1M6S7fVinp;A1A2A1A2A3S0G1S7R6P6M7A2S39G0S2dG4S7cVinp;A1A2A2A3S1S2cZ1S38G0S7R7P18M8A2A2M9A2S2eG9Z400000A2A2S79Sd2R9R8R7S84Vsp;Vdraw;Vinp;A3MaS32S41G6S82Vinp;A1A2A1MbA5Sa7A2S8S1S6fSfS14R1A1S94A3S1S0S5S38G0S7R1G2A2McA2G4A3S1S0S5S38G0S7R1P8A2A2S2dG4S81Vinp;A1MdA2A3S1S0S5S38G0S7R1P9A2A2GbA3S1S0S5S38G0S7R1PaA2A2S2fS7eVinp;A1MeGdA2A3S1S0S5S38G0S7R1PbA2A2GeA3S1S0G1S7R1P10A2S7R9G8A2A3S1S0S5S38G0S7R1G8A2A2S9aA3S1S0S5S38G0S7R1P1eA2A2S2fG4Z800000A2A3S1S0G1S7R1G3A2S7R9G3A2A3S1S0G1S7R1G5A2S7R9G5A2A3S1S0S3cG6A1MfS9R1P3A2GaA3S1S0GfS9R1P2M10A2S9R9G10A2A3S1S0G1GcS7R9G2A2A3S1S0G1S7R1G10A2S7R9G10A2A3S0G1S7R1G7A2S7R9G7A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2TrhoM;F_;F_;F_;F_;F_;F_;Fms;Frho1;Fv;").
Proof.
  intros v rho1 ms H2 E1 E4 E5 E6 H24 rhoM.
  pose proof arg_nums as (Nsp & Nfit & N16 & Nargc & Nstr & Nstr8 & NA1 & NA1b & Nrnd & Npad & Nrnd8 & Nlen & Nlenb & Nlen0 & Ntab1 & Ntab2).
  pose proof (Zle_0_nat (tab (in_argv inp))) as T0. pose proof (Zle_0_nat (tab (in_envp inp))) as T1. pose proof (Zle_0_nat (pad_len (in_argv inp) (in_envp inp))) as T2.
  pose proof (Zle_0_nat (length argv0)) as T3. pose proof (Zle_0_nat (length argv1)) as T4. destruct (argv1_fits H2) as [F1 F2].
  set (rho3 := rho3M v rho1 ms L3 (Z.of_nat (length argv1))) in *.
  assert (R3 : forall i, i <> KN -> rw rho3 i = rw rho1 i) by (intros i Hi; unfold rho3, rho3M; rewrite rho_set_rw_other by exact Hi; reflexivity).
  assert (R9 : rw rho3 KN = Z_to_bv 64 (Z.of_nat (length argv1))) by (unfold rho3, rho3M; apply rho_set_rw_at).
  assert (U1 : bv_unsigned (rw rho3 1%positive) = bv_unsigned sp) by (rewrite R3 by (unfold KN; discriminate); rewrite E1; reflexivity).
  assert (U4 : bv_unsigned (rw rho3 4%positive) = bv_unsigned sp + STRo) by (rewrite R3 by (unfold KN; discriminate); rewrite E4, u64_of_lit by lia; reflexivity).
  assert (U5 : bv_unsigned (rw rho3 5%positive) = Z.of_nat (length argv0)) by (rewrite R3 by (unfold KN; discriminate); rewrite E5, u64_of_lit by lia; reflexivity).
  assert (U6 : bv_unsigned (rw rho3 6%positive) = bv_unsigned sp + RNDo) by (rewrite R3 by (unfold KN; discriminate); rewrite E6, u64_of_lit by lia; reflexivity).
  assert (U9 : bv_unsigned (rw rho3 KN) = Z.of_nat (length argv1)) by (rewrite R9, u64_of_lit by lia; reflexivity).
  assert (UA : bv_unsigned (eval rho3 vA1L) = bv_unsigned sp + A1o).
  { unfold vA1L. cbn [eval]. rewrite U_add_small; [| lia | rewrite U_add_words by lia; lia]. rewrite U_add_words by lia. lia. }
  assert (UE : bv_unsigned (eval rho3 vENDL) = bv_unsigned sp + LEN) by (unfold vENDL; cbn [eval]; rewrite U_add_small by lia; lia).
  assert (UL3 : bv_unsigned (eval rho3 vL3L) = LEN - A1o) by (unfold vL3L; cbn [eval]; fold vENDL vA1L; rewrite U_sub_nowrap by lia; lia).
  assert (UAL : bv_unsigned (eval rho3 vALL) = LEN) by (unfold vALL; cbn [eval]; fold vENDL; rewrite U_sub_nowrap by (cbn [eval]; lia); cbn [eval]; lia).
  assert (UTOP : bv_unsigned (eval rho3 (SAlu ALU_ADD (SVar 1) (SLit (-8388608)))) = bv_unsigned sp - 8388608).
  { cbn [eval]. change (-8388608) with (Z.opp 8388608). rewrite U_add_neglit by (rewrite U1; lia). rewrite U1. reflexivity. }

  assert (W : forall i, rw rhoM i = eval rho3 (wsub_get sFM i)) by (intros i; reflexivity).
  assert (V1 : bv_unsigned (rw rhoM 1%positive) = bv_unsigned sp) by (rewrite W; cbn [wsub_get sFM sM sJ app Pos.eqb eval]; exact U1).
  assert (V8 : bv_unsigned (rw rhoM 8%positive) = bv_unsigned sp + A1o) by (rewrite W; exact UA).
  assert (V9 : bv_unsigned (rw rhoM 9%positive) = Z.of_nat (length argv1)) by (rewrite W; cbn [wsub_get sFM sM sJ app Pos.eqb eval KN]; exact U9).
  assert (V10 : bv_unsigned (rw rhoM 10%positive) = LEN - A1o) by (rewrite W; exact UL3).
  assert (V11 : bv_unsigned (rw rhoM 11%positive) = LEN) by (rewrite W; exact UAL).
  assert (V16 : rw rhoM 16%positive = rw rho1 24%positive) by (rewrite W; cbn [wsub_get sFM sM sJ app Pos.eqb eval]; apply R3; unfold KN; discriminate).
  assert (V24 : bv_unsigned (rw rhoM 24%positive) = TP) by (rewrite W; cbn [wsub_get sFM sM sJ app Pos.eqb eval]; apply u64_of_lit; unfold TP; lia).
  assert (V30 : bv_unsigned (rw rhoM 30%positive) = bv_unsigned sp - 8388608) by (rewrite W; exact UTOP).
  split.
  - unfold facts_M, facts_M0, top_facts, arg1_factsM, argsX_facts, DrvIfaceT.sp0, DrvIfaceT.vA1, DrvIfaceT.vL1, DrvIfaceT.vL3, DrvIfaceR.vAL, DrvIfaceT.vTID, DrvIfaceT.vTP, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.add.
    pose proof (urange (rw rhoM 1%positive)) as R1. pose proof (urange (rw rhoM 8%positive)) as R8. pose proof (urange (rw rhoM 10%positive)) as R10. pose proof (urange (rw rhoM 11%positive)) as R11.
    assert (VT : bv_unsigned (eval rhoM (SAlu ALU_ADD (SVar 1) (SLit (-8388608)))) = bv_unsigned sp - 8388608).
    { cbn [eval]. change (-8388608) with (Z.opp 8388608). rewrite U_add_neglit by (rewrite V1; lia). rewrite V1. reflexivity. }
    repeat (apply Forall_app; split); repeat constructor; cbn [holds]; unfold TP in *; rewrite ?VT; cbn [eval]; rewrite ?u64_of_lit by lia;
      rewrite ?V1, ?V8, ?V9, ?V10, ?V11, ?V16, ?V24, ?V30; try lia.
    all: try (rewrite U_add_words by (rewrite ?V1, ?V8, ?V9, ?V10, ?V11; lia)); try (rewrite U_add_small by (rewrite ?V1, ?V8, ?V9, ?V10, ?V11; lia));
         rewrite ?u64_of_lit by lia; rewrite ?V1, ?V8, ?V9, ?V10, ?V11, ?V30; try lia.
    all: try (rewrite U_add_words by (rewrite ?V1, ?V8, ?V9, ?V10, ?V11; lia)); rewrite ?V1, ?V8, ?V9, ?V10, ?V11; try lia.
    all: try (apply bv_eq; rewrite V24, u64_of_lit by lia; reflexivity).
  - repeat split; try assumption; try reflexivity.
    all: try (rewrite W; cbn [wsub_get sFM sM sJ app Pos.eqb eval]; apply R3; unfold KN; discriminate).
    all: unfold rhoM, rho_sub; cbn [rl]; unfold rho3, rho3M; cbn [rl rho_set_rw set_rl]; reflexivity.
Qed.

Definition rho3U (v : bool) (rho1 : valuation) (ms : machine_state) (bs2 : list byte) : valuation := ltac2:(tb__ "0|0|
S8bS8bS7aVrho1;SdS53S66Vv;A1A1A1Vms;A3P2Vbs2;A3P3Vbs2;A3").

Lemma LU3_no3 : ltac2:(tb__ "0|0|
S3bS0S3bS8cS6S3dL_;S6S4aSc6R1P3A2A1Ll';Sa5R1A1A3S3dA3Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma stage2_U : ltac2:(tb__ "0|e|
S3bS8S3cS57A1M0S61S56S66R5A1S54SdS53R1A1A1S3cSaA1ScS4dR6S53R2A1S3eG0S4eR5S4fR4R3A2A4A4S0S3aQ40M1A1M2S7R7P1A2Vsp;A3S0G2S7R8P4A2S39G1S2dS38G1Vsp;A2M3S80Vinp;A1A2A2A3S0G2S7R9P5A2S39G1S32S41S3aQ8M4A1M5S7fVinp;A1M6A2A1A2A3S0G2S7RaP6A2S39G1S2dG3S7cVinp;A1A2A2A3S0G2S7RbP9A2Sc2Vdraw;A1A3S0G2S7RcPaA2Sc3Vdraw;A1A3S0S3cG5A1M7S9RdP2M8A2S45G5G6S44G5S39G4Z0A2S46G5A1A3A3A3G2Sa3RfR1A2S0S3fG5A1M9SbR10R2A2S62S85Vsp;Vdraw;Vinp;A3R2A2A3F_;Fa;G2Sa3R10R1A2S3S78R11RcR2A3A1F_;Fa;Sd3R11R10ReS83Vsp;Vdraw;Vinp;A3MaA4S8S1ScS4dR1Sa5R12A1S3eG0S4eR10S4fRfReA2A4A4S1S6S0G2S7R2R1A2S7R12R1A2A3Fi;S1S0G7S9R1G8A2GaA3S1S0G7S9R1P3MbA2GaA3S1S6S3S0S6R1G8A3A1S3S0S6R2GbA3A1S0G7S9R4R3A2S9R14R3A2A3F_;F_;Fl;S1G2S3S78R12RdR1A3McA1S0G9SbR3R2A2MdSbR13R2A2A3F_;Fa;S1G2GcS0G9GdS62R11R2A2A3F_;Fa;S0S5S38G1S12R11Sa9A2A2S2dG3S7eVinp;A1A2A3A2A2A2A2A2A2A2Trho3;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TL0;TA;Fmd;Fms;Ftr;Frho1;Fv;").
Proof.
  intros v rho1 tr ms md A L0 Hsm E1 E4 E5 E6 E9 E10 HL2 HRM AP rho3'.
  set (rho3 := set_rl (rho_absorb rho1 L0 ms) 2%positive L2U).
  assert (E3' : rho3' = set_rl rho3 3%positive L2U) by reflexivity.
  pose proof arg_nums as (Nsp & Nfit & N16 & Nargc & Nstr & Nstr8 & NA1 & NA1b & Nrnd & Npad & Nrnd8 & Nlen & Nlenb & Nlen0 & Ntab1 & Ntab2).
  pose proof (Zle_0_nat (tab (in_argv inp))) as T0. pose proof (Zle_0_nat (tab (in_envp inp))) as T1. pose proof (Zle_0_nat (pad_len (in_argv inp) (in_envp inp))) as T2.
  pose proof (Zle_0_nat (length argv0)) as T3.
  assert (U1 : bv_unsigned (rw rho1 1%positive) = bv_unsigned sp) by (rewrite E1; reflexivity).
  assert (U4 : bv_unsigned (rw rho1 4%positive) = bv_unsigned sp + STRo) by (rewrite E4, u64_of_lit by lia; reflexivity).
  assert (U5 : bv_unsigned (rw rho1 5%positive) = Z.of_nat (length argv0)) by (rewrite E5, u64_of_lit by lia; reflexivity).
  assert (U6 : bv_unsigned (rw rho1 6%positive) = bv_unsigned sp + RNDo) by (rewrite E6, u64_of_lit by lia; reflexivity).
  assert (UE : bv_unsigned (eval rho1 vENDL) = bv_unsigned sp + LEN).
  { unfold vENDL. cbn [eval]. rewrite U_add_small by lia. lia. }
  pose proof (smatch_facts segsA _ _ _ Hsm) as HF0.
  assert (RM2o : forall a : word, ~ in_ranges rho1 L0 a -> rm rho3 a = rm rho1 a).
  { intros a Ha. unfold rho3, set_rl. cbn [rm]. apply rm_reshape_outside. exact Ha. }
  assert (RM2i : forall a : word, in_ranges rho1 L0 a -> rm rho3 a = ms_mem ms a).
  { intros a Ha. unfold rho3, set_rl. cbn [rm]. apply rm_reshape_inside. exact Ha. }
  pose proof (chain_U v rho1 tr ms md L2U Hsm) as C1. cbv zeta in C1. fold L0 in C1. fold rho3 in C1.
  pose proof (length_L2U sp brk mb draw inp Hent Hinp) as LL2.
  assert (RL2 : rl rho3 2%positive = L2U) by (unfold rho3, set_rl; cbn [rl]; rewrite Pos.eqb_refl; reflexivity).
  assert (RW2 : forall i, rw rho3 i = rw rho1 i) by (intros i; reflexivity).
  assert (EVE : eval rho3 vENDL = eval rho1 vENDL) by reflexivity.
  pose proof (proj1 (smatch_mm segsA _ _ _ _ _ Hsm)) as HOL. change (ss_objs (ax_S A)) with L0 in HOL.
  pose proof Hsm as (_ & _ & _ & _ & ROM & _). cbn [fst snd cfg_ms cfg_model] in ROM.
  pose proof (cells20 v) as (_ & _ & C0 & C8).
  assert (C2 : smatch segsA rho3 (LU3 v) (tr, mkCfg ms md)).
  { apply (carve_U v rho3 tr ms md C1); rewrite ?RW2, ?EVE, ?RL2, ?UE, ?U1, ?U4.
    - lia.
    - lia.
    - lia.
    - rewrite LL2. lia.
    - intros j Hj. assert (Hj' : Z.of_nat j < LEN - STRo) by (rewrite <- LL2; apply (proj1 (Nat2Z.inj_lt _ _)); exact Hj).
      destruct (Z_lt_ge_dec (Z.of_nat j) (Z.of_nat (length argv0) + 1)) as [Hstr|Hge].
      +
        set (o19 := mkObj (SVar 4) (SLit 0) (SAlu ALU_ADD (SVar 5) (SLit 1)) [] (DList 2)).
        assert (IN19 : In o19 L0) by (eapply nth_error_In; exact (nth19 v)).
        assert (HI : obj_hi_of rho1 o19 = Z.of_nat (length argv0) + 1).
        { unfold obj_hi_of, o19. cbn [ob_hi]. apply soff_of_U; [| lia]. cbn [eval]. rewrite U_add_small by lia. lia. }
        pose proof (dlist_byte rho1 ms o19 2%positive (Z.of_nat j) (proj1 (Forall_forall _ _) HOL o19 IN19) eq_refl eq_refl eq_refl ltac:(rewrite HI; lia)) as HD.
        unfold o19 in HD. cbn [ob_base eval] in HD. rewrite U4, Nat2Z.id, HL2 in HD.
        assert (IN : in_ranges rho1 L0 (Z_to_bv 64 (bv_unsigned sp + STRo + Z.of_nat j))).
        { exists o19. split; [exact IN19|]. unfold obj_range. rewrite HI. unfold obj_lo_of, o19. cbn [ob_base ob_lo eval]. rewrite soff_lit_small by lia.
          cbn [fst snd]. rewrite U4, u64_of_lit by lia. lia. }
        rewrite (RM2i _ IN). unfold rd, ms_read_byte in HD.
        destruct (ms_mem ms (Z_to_bv 64 (bv_unsigned sp + STRo + Z.of_nat j))) as [b|] eqn:EM.
        * rewrite HD. f_equal. rewrite <- (L2U_head sp brk mb draw inp Hent Hinp). rewrite nth_firstn_small by lia. reflexivity.
        * exfalso. rewrite (ROM _), (image_byte_none_A (Z_to_bv 64 (bv_unsigned sp + STRo + Z.of_nat j)) ltac:(rewrite u64_of_lit by lia; lia)) in HD. discriminate.
      + destruct (Z_lt_ge_dec (STRo + Z.of_nat j) RNDo) as [Hfr|Hrnd].
        *
          assert (AF : ARGF rho1 (Z_to_bv 64 (bv_unsigned sp + STRo + Z.of_nat j))).
          { unfold ARGF. rewrite u64_of_lit by lia. lia. }
          rewrite (RM2o _ (AP _ AF)), (HRM _ AF). exact (L2U_byte sp brk mb draw inp Hent Hinp j Hj).
        *
          unfold rho3, set_rl. cbn [rm]. subst L0.
          replace (bv_unsigned sp + STRo + Z.of_nat j) with (bv_unsigned sp + RNDo + (STRo + Z.of_nat j - RNDo)) by lia.
          rewrite (rand_byte v (ax_S A) rho1 tr ms md (STRo + Z.of_nat j - RNDo) Hsm C0 C8 E9 E10 U6 ltac:(lia)). f_equal.
          unfold StartArgBytes.L2U. rewrite nth_skipn.
          replace (Z.to_nat STRo + j)%nat with (Z.to_nat RNDo + Z.to_nat (STRo + Z.of_nat j - RNDo))%nat by lia.
          symmetry. apply (BSB_rand sp draw inp). lia. }
  rewrite E3'. split; [apply smatch_set_rl; [exact (LU3_no3 v) | exact C2]|]. split; [exact RW2|]. split; [exact RL2|].
  split; [cbn [rl set_rl]; reflexivity|].
  split; [intros l Hl Hl3; unfold rho3; cbn [rl set_rl]; destruct (Pos.eqb_spec l 3); [contradiction|]; destruct (Pos.eqb_spec l 2); [contradiction | reflexivity]|].
  split; [exact RM2o|]. split; [exact RM2i|]. exact UE.
Qed.

Lemma factsU_hold : ltac2:(tb__ "0|13|
S3bS8S61S3S0S5S7dVinp;A1M0Z2A3A1S0S3aQ40M1A1M2S7R3P1M3A2Vsp;A3S0G2S7R4P2M4A2S39G1G0A2A3S0G2S7R5P4M5A2S39G1S2dS38G1Vsp;A2M6S80Vinp;A1M7A2M8A2A3S0G2S7R6P5M9A2S39G1S32S41S3aQ8A1MaS7fVinp;A1A2A1MbA2A3S0G2S7R7P6A2S39G1S2dG6S7cVinp;A1A2A2A3S1S2cZ1S38G1S7R8P18McA2A2MdA2S2eGdZ400000A2A2S79Sd3RaR9R8S83Vsp;Vdraw;Vinp;A3MeA4Sa8A2S8S1S6fSfS14R1A1S95A3S1S0S5S38G1S7R1G3A2A2G6A3S1S0S5S38G1S7R1G4A2A2G0A3S1S0S5S38G1S7R1G5A2A2G8A3S1S0S5S38G1S7R1G9A2A2GbA3S1S0S5S38G1S7R1PcA2A2S2fS7eVinp;A1MfG7A2A3S1S0S5S38G1S7R1PbM10A2A2GfA3S1S0G2S7R1P10A2S7RaGcA2A3S1S0S5S38G1S7R1GcA2A2S9aA3S1S0S5S38G1S7R1P1eA2A2S2fG6Z800000A2A3S1S6Sc5R1G10A2S0G2S7R3R2A2S7RcR2A2A3F_;Fi;S1S0S3cGaA1M11S9R1G4A2GeA3S1S0G11S9R1P3M12A2GeA3S6S3S0S6R1G4A3A1S3S0S6R2G12A3A1S0G11S9R4R3A2S9RdR3A2A3F_;F_;Fl;A2A2A2A2A2A2A2A2A2A2A2A2A2TrhoM;F_;F_;F_;F_;F_;F_;F_;Fms;Frho1;Fv;").
Proof.
  intros v rho1 ms HA2 E1 E2 E4 E5 E6 H24 rhoM.
  pose proof arg_nums as (Nsp & Nfit & N16 & Nargc & Nstr & Nstr8 & NA1 & NA1b & Nrnd & Npad & Nrnd8 & Nlen & Nlenb & Nlen0 & Ntab1 & Ntab2).
  pose proof (Zle_0_nat (tab (in_argv inp))) as T0. pose proof (Zle_0_nat (tab (in_envp inp))) as T1. pose proof (Zle_0_nat (pad_len (in_argv inp) (in_envp inp))) as T2.
  pose proof (Zle_0_nat (length argv0)) as T3.
  set (rho3 := rho3U v rho1 ms L2U) in *.
  assert (R3 : forall i, rw rho3 i = rw rho1 i) by (intros i; reflexivity).
  assert (U1 : bv_unsigned (rw rho3 1%positive) = bv_unsigned sp) by (rewrite R3, E1; reflexivity).
  assert (U2 : bv_unsigned (rw rho3 2%positive) = ARGC) by (rewrite R3, E2, u64_of_lit by lia; reflexivity).
  assert (U4 : bv_unsigned (rw rho3 4%positive) = bv_unsigned sp + STRo) by (rewrite R3, E4, u64_of_lit by lia; reflexivity).
  assert (U5 : bv_unsigned (rw rho3 5%positive) = Z.of_nat (length argv0)) by (rewrite R3, E5, u64_of_lit by lia; reflexivity).
  assert (U6 : bv_unsigned (rw rho3 6%positive) = bv_unsigned sp + RNDo) by (rewrite R3, E6, u64_of_lit by lia; reflexivity).
  assert (UE : bv_unsigned (eval rho3 vENDL) = bv_unsigned sp + LEN) by (unfold vENDL; cbn [eval]; rewrite U_add_small by lia; lia).
  assert (UL2 : bv_unsigned (eval rho3 vL2L) = LEN - STRo) by (unfold vL2L; cbn [eval]; fold vENDL; rewrite U_sub_nowrap by (cbn [eval]; lia); cbn [eval]; lia).
  assert (UAL : bv_unsigned (eval rho3 vALL) = LEN) by (unfold vALL; cbn [eval]; fold vENDL; rewrite U_sub_nowrap by (cbn [eval]; lia); cbn [eval]; lia).
  assert (UTOP : bv_unsigned (eval rho3 (SAlu ALU_ADD (SVar 1) (SLit (-8388608)))) = bv_unsigned sp - 8388608).
  { cbn [eval]. change (-8388608) with (Z.opp 8388608). rewrite U_add_neglit by (rewrite U1; lia). rewrite U1. reflexivity. }
  assert (W : forall i, rw rhoM i = eval rho3 (wsub_get sFU i)) by (intros i; reflexivity).
  assert (V1 : bv_unsigned (rw rhoM 1%positive) = bv_unsigned sp) by (rewrite W; cbn [wsub_get sFU sM sJ app Pos.eqb eval]; exact U1).
  assert (V2 : bv_unsigned (rw rhoM 2%positive) = ARGC) by (rewrite W; cbn [wsub_get sFU sM sJ app Pos.eqb eval]; exact U2).
  assert (V4 : bv_unsigned (rw rhoM 4%positive) = bv_unsigned sp + STRo) by (rewrite W; cbn [wsub_get sFU sM sJ app Pos.eqb eval]; exact U4).
  assert (V5 : bv_unsigned (rw rhoM 5%positive) = Z.of_nat (length argv0)) by (rewrite W; cbn [wsub_get sFU sM sJ app Pos.eqb eval]; exact U5).
  assert (V12 : bv_unsigned (rw rhoM 12%positive) = LEN - STRo) by (rewrite W; exact UL2).
  assert (V11 : bv_unsigned (rw rhoM 11%positive) = LEN) by (rewrite W; exact UAL).
  assert (V16 : rw rhoM 16%positive = rw rho1 24%positive) by (rewrite W; cbn [wsub_get sFU sM sJ app Pos.eqb eval]; apply R3).
  assert (V24 : bv_unsigned (rw rhoM 24%positive) = TP) by (rewrite W; cbn [wsub_get sFU sM sJ app Pos.eqb eval]; apply u64_of_lit; unfold TP; lia).
  assert (V30 : bv_unsigned (rw rhoM 30%positive) = bv_unsigned sp - 8388608) by (rewrite W; exact UTOP).
  split.
  - unfold facts_U, facts_M0, top_facts, arg0_facts, DrvIfaceT.sp0, DrvIfaceT.vA0, DrvIfaceT.vL0, vL2, vARGC, DrvIfaceR.vAL, DrvIfaceT.vTID, DrvIfaceT.vTP, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.add.
    pose proof (urange (rw rhoM 1%positive)) as R1. pose proof (urange (rw rhoM 4%positive)) as R4. pose proof (urange (rw rhoM 12%positive)) as R12. pose proof (urange (rw rhoM 11%positive)) as R11.
    assert (VT : bv_unsigned (eval rhoM (SAlu ALU_ADD (SVar 1) (SLit (-8388608)))) = bv_unsigned sp - 8388608).
    { cbn [eval]. change (-8388608) with (Z.opp 8388608). rewrite U_add_neglit by (rewrite V1; lia). rewrite V1. reflexivity. }
    repeat (apply Forall_app; split); repeat constructor; cbn [holds]; unfold TP in *; rewrite ?VT; cbn [eval]; rewrite ?u64_of_lit by lia;
      rewrite ?V1, ?V2, ?V4, ?V5, ?V12, ?V11, ?V16, ?V24, ?V30; try lia.
    all: try (rewrite U_add_words by (rewrite ?V1, ?V4, ?V5, ?V12, ?V11; lia)); try (rewrite U_add_small by (rewrite ?V1, ?V4, ?V5, ?V12, ?V11; lia));
         rewrite ?u64_of_lit by lia; rewrite ?V1, ?V2, ?V4, ?V5, ?V12, ?V11, ?V30; try lia.
    all: try (rewrite U_add_words by (rewrite ?V1, ?V4, ?V5, ?V12, ?V11; lia)); rewrite ?V1, ?V4, ?V5, ?V12, ?V11; try lia.
    all: try (apply bv_eq; rewrite V24, u64_of_lit by lia; reflexivity).
    all: unfold branch_taken, bv_eqb; rewrite V2, u64_of_lit by lia; apply Bool.negb_true_iff; apply Z.eqb_neq; exact HA2.
  - repeat split; try assumption.
    + intros i Hi. rewrite W. destruct i as [i|i|]; cbn; try reflexivity; destruct i as [i|i|]; cbn; try reflexivity; try (destruct i as [i|i|]; cbn; try reflexivity; destruct i; cbn; try reflexivity; lia).
    + intros l Hl Hl3. unfold rhoM, rho_sub; cbn [rl]; unfold rho3, rho3U; cbn [rl set_rl].
      destruct (Pos.eqb_spec l 3); [contradiction|]. destruct (Pos.eqb_spec l 2); [contradiction | reflexivity].
Qed.
End Top.

Definition obj_far_b (allow8 : bool) (o : sobj) : bool := ltac2:(tb__ "0|3|
S3fS5A1S3bLx;M0S92S1aVo;A1A1S5G0S92S26Vo;A1A1S5S43S34R2R1A2S4bS43S16S19Vo;A1M1S11P1A1A2S34S36S33Z2Z14A2A1R2A2A2S43S43S16G1S10Z0M2A1A2S34G2R2A2A2S34R1Z646000A2A2A2A2Lh;S43S4bS43Vallow8;S16G1S11P8A1A2A2S16G1S11P4A1A2A2S34G2R1A2A2X3fx2Ll;S49X3fx2").
Lemma objs_MU_far : ltac2:(tb__ "0|0|
S1S0S3bS6cSaS73S3dA1S98A3S3dA3S0S3bS6cSaS73S49A1S99A3S3dA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma obj_far_sound : ltac2:(tb__ "0|3|
S3bS8SaS5S0S3bS73R4R2A2S3dA3S2cZ7fff80000000M0S38Q40M1S7R4P1A2A2A2S0S3bR6S3dA3S2cG0S38G1S7R6P8A2A2A2F_;S2cG0S38G1S7R6P4A2A2A2S1S2cZ646000R5A2S2eR5Z7fff00000000A2A2S3S1S2cS4cS5S5S15R8R7A2M2A3R6A2S2eR6S48S5S5G2A3A2A2A1F_;F_;F_;F_;F_;Fz;Fo;Frho;Fallow8;").
Proof.
  intros allow8 rho o z Hb H1 H8 H4 Hz. unfold obj_far_b in Hb. unfold obj_range, obj_lo_of, obj_hi_of. cbn [fst snd].
  destruct (lit_small (ob_lo o)) as [l|] eqn:El; [|discriminate]. rewrite (StartReshape.soff_small rho _ _ El).
  destruct (lit_small (ob_hi o)) as [h|] eqn:Eh.
  - rewrite (StartReshape.soff_small rho _ _ Eh). apply andb_prop in Hb as [Hlh Hb]. apply Z.leb_le in Hlh. apply Bool.orb_prop in Hb as [Hb|Hb].
    + apply andb_prop in Hb as [E Hl]. apply sv_eqb_sound in E. apply Z.leb_le in Hl. rewrite E. cbn [eval]. lia.
    + apply andb_prop in Hb as [Hb Hh]. apply andb_prop in Hb as [E Hl]. apply sv_eqb_sound in E. apply Z.leb_le in Hl. apply Z.leb_le in Hh.
      rewrite E. cbn [eval]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. lia.
  - apply andb_prop in Hb as [E Hl]. apply Z.leb_le in Hl. apply Bool.orb_prop in E as [E|E].
    + apply andb_prop in E as [A8 E]. specialize (H8 A8). apply sv_eqb_sound in E; rewrite E; cbn [eval]; lia.
    + apply sv_eqb_sound in E; rewrite E; cbn [eval]; lia.
Qed.

Lemma objs_far_outside : ltac2:(tb__ "0|2|
S3bS8S3cSaA1S5S0S3bS6cSaS73R4A1R2A3S3dA3S2cZ7fff80000000M0S38Q40M1S7R4P1A2A2A2S0S3bR6S3dA3S2cG0S38G1S7R6P8A2A2A2F_;S2cG0S38G1S7R6P4A2A2A2S1S2cZ646000R5A2S2eR5Z7fff00000000A2A2S1cR8R7S39G1R6A2A3F_;F_;F_;F_;F_;Fz;Fobjs;Frho;Fallow8;").
Proof.
  intros allow8 rho objs z Hb H1 H8 H4 Hz. unfold outside_all. apply Forall_forall. intros o Hin. cbn beta. rewrite u64_of_lit by lia.
  exact (obj_far_sound allow8 rho o z (proj1 (forallb_forall _ _) Hb o Hin) H1 H8 H4 Hz).
Qed.

Lemma sh0_checks : forall v : bool,
  let L := ss_objs (ax_S (MAIN_of v)) in
  forallb (fun off => binfo_eqb (byte_info L (SLit 0x800bc000) off) (BLit 0)) (zseq 0 (Z.to_nat 0x4c00)) = true /\
  forallb (fun off => negb (binfo_eqb (byte_info L (SLit 0x7fffc000) off) BNone)) (zseq 1392 480) = true /\
  forallb (fun off => negb (binfo_eqb (byte_info L (SLit 0x80015000) off) BNone)) (zseq 2216 768) = true /\
  forallb (fun off => binfo_eqb (byte_info L (SLit 0x7fffc000) off) (BLit 0)) (zseq 648 16) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma view_rm : ltac2:(tb__ "0|3|
S3aQ40M0A1S3fS3aQ8A1M1A1M2F_;S5G1S1S2cZ646000R2A2S2eR2S33Z2Z40A2A2A2S0G2Sf0S4dR4R3A3S40G1R2A2A3S0G2R5S39G0R4A2A1S40G1R3A2A3F_;F_;Fb;Fz;Fm;").
Proof.
  intros m z b Hz Hv. rewrite view_in in Hv by lia. unfold Glue.rd_of in Hv.
  rewrite (image_byte_none_A (Z_to_bv 64 z)) in Hv by (rewrite u64_of_lit by lia; lia).
  destruct (m (Z_to_bv 64 z)); [exact Hv | discriminate].
Qed.

Lemma win1_arith : ltac2:(tb__ "0|3|
S5S1S2cZ14d40M0R1A2S2eR1S2dG0Z80A2A2A2S1S2cZ7fffa000M1S2dZ7fff8000S31R2Z8A2A2M2A2S2eG2S2dG1Z1000A2A2A2F_;Fa;").
Proof. intros a Ha. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia. Qed.

Lemma win3_arith : ltac2:(tb__ "0|1|
S5S1S2cS9bR1A2S2eR1S2dS9bZ10000A2A2A2S1S2cZ800ba000S2dZ7fff8000S31R2Z8A2A2M0A2S2eG0Z800bc750A2A2F_;Fa;").
Proof. intros a Ha. unfold RD_STAGE in Ha. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia. Qed.

Lemma pagedown_le : ltac2:(tb__ "0|2|
S5S1S2cS2fR1S30R1Z1000M0A2A2M1R1A2S1S0S5S30G1Z8A2Z0A3S2eS2fR1G0A2G1A2A2A2Fs;").
Proof.
  intros s. pose proof (Z.div_mod s 4096 ltac:(lia)). pose proof (Z.mod_pos_bound s 4096 ltac:(lia)).
  split; [lia|]. split; [|lia]. replace (s - s mod 4096) with (512 * (s / 4096) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma floor8_props : ltac2:(tb__ "0|2|
S5S1S2cS2fR1S30R1Z8M0A2A2M1R1A2S1S0S5S30G1G0A2Z0A3S2eS2fR1G0A2G1A2A2A2Fs;").
Proof.
  intros s. pose proof (Z.div_mod s 8 ltac:(lia)). pose proof (Z.mod_pos_bound s 8 ltac:(lia)).
  split; [lia|]. split; [|lia]. replace (s - s mod 8) with ((s / 8) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma div8_lower : ltac2:(tb__ "0|1|
S5S5S2cS35Z8M0R1A2R2A2S2cR2S31R3G0A2A2F_;Fm;Fa;").
Proof. intros a m H. replace m with (8 * m / 8) by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity). apply Z.div_le_mono; lia. Qed.
Lemma div8_upper : ltac2:(tb__ "0|1|
S5S5S2eR2S35Z8M0R1A2A2S2eS31R3G0A2R2A2F_;Fm;Fa;").
Proof. intros a m H. apply Z.div_lt_upper_bound; lia. Qed.

Lemma win2_arith : ltac2:(tb__ "0|7|
S5S5S0S5S30R2Z10A2Z0A3S2cZ10000M0R3A2S1S2cS2fR4G0A2M1R3A2S2eR3S2dG1Zff90A2A2A2S2dS31R5Z8M2A2M3Z7fff8000M4A2S5S1S2cS2fS2fR1Z20000A2M5S30G5Z1000A2A2S2dG4G3A2M6A2S2eG6S2fR1S30R1G2A2A2A2A2Tshx;F_;F_;F_;Fa;Fsp;").
Proof.
  intros sp a H16 Hsp Ha shx. pose proof (pagedown_le (shx - 131072)) as (P1 & P2 & P3). pose proof (floor8_props shx) as (F1 & F2 & F3).
  pose proof (Z.div_mod sp 16 ltac:(lia)) as D16. rewrite H16, Z.add_0_r in D16. set (k := sp / 16) in *.
  assert (D8 : sp / 8 = 2 * k) by (rewrite D16; replace (16 * k) with (2 * k * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
  pose proof (div8_lower a (2 * k - 8192) ltac:(lia)) as L. pose proof (div8_upper a (2 * k - 14) ltac:(lia)) as U.
  subst shx. rewrite D8 in *. lia.
Qed.

Lemma zarg_arith : ltac2:(tb__ "0|5|
S5S5S5S5S5S0S5S30R5Z10M0A2Z0M1A3S2cZ10000R6A2S2cG0R6A2S2cS2dR8R7A2R6A2S0S5S30R7Z40A2G1A3S0S5R7S2dZ7fff8000M2S31R8Z8M3A2A2A3S1S2cS35S31S2dS31RbG3A2G2A2G3A2G3A2R7A2S2eR7S2dS35S31S2dS31S2fS2dRbRaA2Z1A2G3A2G2A2G3A2G3A2G3A2A2A2S2dS31RcG3A2G2A2S5S1S2cS2fS2fR1Z20000A2M4S30G4Z1000A2A2R9A2S2eR9RaA2A2Tshx;F_;F_;F_;F_;F_;F_;F_;Fz;FSXE;FXEz;FLEN;Fsp;").
Proof.
  intros sp LEN XEz SXE z H16 Hsp HL HX HX64 HS Hz shx. pose proof (pagedown_le (shx - 131072)) as (P1 & P2 & P3).
  pose proof (Z.div_mod XEz 64 ltac:(lia)) as D64. rewrite HX64, Z.add_0_r in D64. set (q := XEz / 64) in *.
  assert (DX : XEz / 8 = 8 * q) by (rewrite D64; replace (64 * q) with (8 * q * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
  pose proof (Z.div_mod (sp / 8 + 0x7fff8000) 8 ltac:(lia)) as A1. pose proof (Z.mod_pos_bound (sp / 8 + 0x7fff8000) 8 ltac:(lia)) as A2.
  pose proof (div8_upper (sp + LEN - 1) (8 * q) ltac:(lia)) as U.
  pose proof (Z.div_mod ((sp + LEN - 1) / 8 + 0x7fff8000) 8 ltac:(lia)) as B1. pose proof (Z.mod_pos_bound ((sp + LEN - 1) / 8 + 0x7fff8000) 8 ltac:(lia)) as B2.
  subst shx. split; [lia|].
  set (t := (sp + LEN - 1) / 8 + 2147450880) in *.
  assert (T : t < 2147450880 + 8 * q) by lia.
  assert (T8 : t / 8 * 8 + 8 <= 2147450880 + 8 * q).
  { replace (2147450880 + 8 * q) with ((268431360 + q) * 8) in T |- * by lia. pose proof (div8_upper t (268431360 + q) ltac:(lia)). nia. }
  lia.
Qed.

Lemma shadow_ok_X3 : ltac2:(tb__ "0|e|
S8S3cSaA1S5S5S5S5S1S2cZ646000M0R1A2S2eR1Z7fff00000000A2A2S1cR7R6S39Q40M1R2A2M2A3F_;Fz;S0S5S38G1S7R6P1A2A2R4A3S0S5S30R5Z10A2Z0M3A3S1S2cZ7fff80000000R6A2S2cR6S33Z2Z2fA2A2A2S2cG0R6A2S0S5S30R7Z8M4A2G3A3S2cR8S2fS2fS2dS31R9G4A2Z7fff8000M5A2Z20000A2M6S30G6Z1000A2A2A2S0S5R8S2fS2dS31RaG4A2G5A2M7S30G7G4A2A2A3S5S72R1A1S0S3fS3aQ8M8A1M9A1MaSbRfG2A2S40G9S39G8G3A2A2MbA3F_;Fz;S5S1S2cZ800bc000R1A2S2eR1Z800bcc00A2A2S0GaSbR10G2A2GbA3F_;Fz;S5S1S2cRdR1A2S2eR1RcA2A2S0GaSbR11G2A2GbA3F_;Fz;S6fS42SeSeA2McS55R10RfG5A3S44GcS3eSeSeS10Z14d40A1S10Z80MdA1A4S44GcS3eSeSeSdcScbS10S36S2dSc9GdA2A1A1A2S10Sc9A1A4S44GcScaS46GcA1A3A3A3A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fqhi;Fqlo;Fsp;Fobjs;FrhoM;").
Proof.
  intros rhoM objs sp qlo qhi OUTM V1 N16 Hsp Hq0 Hq8 Hqle Hqhi ZPG ZLOWP ZB.
  pose proof (floor8_props (sp / 8 + 2147450880)) as (F81 & F82 & F83). rewrite <- Hqhi in F81, F82, F83.
  pose proof (Z.div_le_mono sp (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D47. change (2 ^ 47 / 8) with 17592186044416 in D47.
  constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (xr_ok_of_zero rhoM objs 2147450880 _ PA0 (PA0 + 4096)); cbn [fst snd eval]; rewrite ?u64_of_lit by lia; unfold PA0.
    1-6: first [reflexivity | lia].
    + intros a Ha. apply win1_arith. exact Ha.
    + intros z Hz. apply ZPG. unfold ZPAGES, PA0. lia.
    + intros z Hz. apply OUTM. lia.
  - assert (EB : bv_unsigned (eval rhoM (fst (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.add DrvIfaceT.sp0 (SLit (- (DEEP + 128))), SLit DEEP))) = sp - 65536).
    { cbn [fst eval]. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.add, DrvIfaceT.sp0, DEEP. cbn [eval]. change (- (65408 + 128)) with (Z.opp 65536). rewrite U_add_neglit by (rewrite V1; lia). rewrite V1. reflexivity. }
    apply (xr_ok_of_zero rhoM objs 2147450880 _ qlo qhi); rewrite ?EB; cbn [snd eval]; unfold DEEP; rewrite ?u64_of_lit by lia.
    + pose proof (Z.div_mod sp 16 ltac:(lia)). replace (sp - 65536) with ((sp / 16 - 4096) * 2 * 8) by lia. apply Z_mod_mult.
    + lia. + lia. + lia. + exact Hq8. + exact F82.
    + intros a Ha. pose proof (win2_arith sp a N16 ltac:(lia) ltac:(lia)) as W. cbv zeta in W. lia.
    + intros z Hz. apply ZB. lia.
    + intros z Hz. apply OUTM. lia.
  - unfold X_rds. apply (xr_ok_of_zero rhoM objs 2147450880 _ PR0 0x800bc750); cbn [fst snd eval]; unfold RD_STAGE; rewrite ?u64_of_lit by lia; unfold PR0.
    1-6: first [reflexivity | lia].
    + intros a Ha. apply win3_arith. unfold RD_STAGE. exact Ha.
    + intros z Hz. destruct (Z_lt_dec z 0x800bc000) as [C|C]; [apply ZPG; unfold ZPAGES, PR0; lia | apply ZLOWP; lia].
    + intros z Hz. apply OUTM. lia.
Qed.

Lemma ZARG_of : ltac2:(tb__ "0|8|
S8S5S5S5S5S5S5S0S5S38Q40M0S7R7P1A2A2R6A3S0S5S38G0S7R8PbA2A2R6A3S0S5S30R8Z10M1A2Z0M2A3S2cZ7fff80000000R9A2S2cG1R9A2S2cS2dRbRaA2S33Z2Z2fA2A2S2cS2dRcRbA2RaA2S0S5S30RbZ40A2G2A3S0S5RbS2dZ7fff8000M3S31RcZ8M4A2A2A3S2cRcRaA2S2cRcS2fS2fS2dS31R10G4A2G3A2Z20000A2M5S30G5Z1000A2A2A2S5S1S2cReR1A2S2eR1RdA2A2S0S3fS3aQ8M6A1M7A1SbR14S39G0R2A2A2S40G7S39G6G2A2A2A3F_;Fz;S65R13A1F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fqtop;Fqlo;FSXE;FXEz;FLEN;Fsp;FrhoM;").
Proof.
  intros rhoM sp LEN XEz SXE qlo qtop V1 V11 N16 Hsp HL Hfit HX HX64 HS HSt Hq ZB.
  unfold ZARG, Uv, Geometry.Sh, Geometry.SHADOW_OFF. rewrite V1, V11. split; [lia|]. split; [lia|].
  intros z Hz. apply ZB. pose proof (zarg_arith sp LEN XEz SXE z N16 ltac:(lia) HL HX HX64 HS Hz) as W. cbv zeta in W. lia.
Qed.

Lemma fact_in : ltac2:(tb__ "0|0|
S8SfS3cSfA1S0S3bS6dSfS17R2A1R1A3S3dA3S6fSfS14R4A1R2A3S14R5R4A2F_;F_;Fl;Fp;Frho;").
Proof.
  intros rho p l Hb HF. apply existsb_exists in Hb as (q & Hin & Heq). apply sprop_eqb_sound in Heq. subst q. exact (proj1 (Forall_forall _ _) HF p Hin).
Qed.
Lemma facts24 : ltac2:(tb__ "0|2|
S3bS1S0S3bS6dSfS17S21S10Z1A1S11P18A1M0A2A1S2bS53S66R1A1A1A1M1A3S3dA3S0S3bS6dSfS17S22G0S10Z400000A1A2A1G1A3S3dA3A2Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Kernel.Fork.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvM MainJoin.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.StartMainFds OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.MainJoin.

Section Main.
Variables (sp brk mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
Hypothesis Hent : ltac2:(tb__ "0|0|
Sd6SccS51Vsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Hypothesis Hlim : 2 ^ 25 <= lim.

Local Notation ARGC := (StartArgBytes.ARGC inp).
Local Notation argv0 := (StartArgBytes.argv0 inp).
Local Notation argv1 := (StartArgBytes.argv1 inp).
Local Notation STRo := (StartArgBytes.STRo inp).
Local Notation A1o := (StartArgBytes.A1o inp).
Local Notation RNDo := (StartArgBytes.RNDo inp).
Local Notation LEN := (StartArgBytes.LEN inp).
Local Notation L3 := (StartArgBytes.L3 sp draw inp).
Local Notation L2U := (StartArgBytes.L2U sp draw inp).
Local Notation ms0A := (StartArgBytes.ms0A sp draw inp).
Local Notation M1 := (StartMain.M1 sp brk mb draw lim inp).

Lemma init_fds_std : ltac2:(tb__ "0|1|
S1S0S3cS42S3aQ40A1S59A2A1S5bS52ScdVsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;A6A1M0A1S64A3S0Sc7S5cG0A1S5aVinp;A1A3A2").
Proof. split; reflexivity. Qed.

Lemma Bmain_val : StartTop.Bmain B0 = 17911808.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition sheet (tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 : word) (x : Z) (o : out18) (v : bool) (rho4 rho' rho1 rhoM : valuation) (tp : list word) (w : world) : Prop := ltac2:(tb__ "0|1e|
Sb8Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7S56SbbR1Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10S56S50S48S3cS57A1S4eSc1S71Vtp;A1Vw;A2M0A3A1S61S1S0S3cS42S3aQ40M1A1M2S59A2A1S5bR2A1S64A3S1S0Sc7S5cR2A1S5aVinp;A1A3S1S0S5S5dS58R2A1A1Vlim;A3S1SecSbdR3Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10Vlim;Vsp;S9eVx;A1R2A5S1S1S2eZ0M3S38G1Vtid;A2M4A2S2eG4Sd8A2A2S1S0S5Vx;S38G1Vsp;A2M5A3S1S6bS39G1G3A2M6SbfR3A1SdeVa1;A4S1S6bG6SbeR3Va1;A2SdfVa2;A4S1S6bG6Sc0R3Va1;Va2;A3M7Se4VP;A4S1S6bG6Se2G7VP;A2Se5Vb4;A4S1S6bG6Se3G7VP;Vb4;A3S39G1Z1000M8A2M9Vb5;A4S1S6bG6Se0G7VP;Vb4;Vb5;A4S39G1Z10000A2Vb6;A4S1S6bG6Se1G7VP;Vb4;Vb5;Vb6;A5G9Vb7;A4S1S6bG6Se8G7VP;Vb4;Vb5;Vb6;Vb7;A6G9Vb8;A4S1S6bG6Se9G7VP;Vb4;Vb5;Vb6;Vb7;Vb8;A7G9Vb9;A4S1S6bG6SeaG7VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;A9S39G1SebA2Vb10;A4S1Sa2G7VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;AbS1S6bG6Sa1G7VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;AbMaS39G1Z100000MbA2Vb12;A4S1S6bG6S68GaVb12;A2S39G1Z800000McA2Vb13;A4S1S6bG6S69GaVb12;Vb13;A3G9Vb14;A4S1S1S4S2cS2dS38G1Vb12;A2MdGbA2MeS88A2S2cS89GdA2A2S2cGeS2fVx;GcA2MfA2A2S1S1S4S2cS2dS38G1Vb13;A2M10GcA2M11S88A2S2cS89G10A2A2S2cG11GfA2A2S1S1S4S2cS2dS38G1Vb14;A2M12G8A2M13S88A2S2cS89G12A2A2S2cG13GfA2A2S1Sc4S4dSceScfVsp;Vdraw;Vinp;Vrho4;A7S1S6Sc5R1P19A2S0G2S7Vrho';R2A2S7Vrho4;R2A2A3F_;Fi;S1S6S0S3cS3aQ8M14A1M15A1M16S9Vrho';R1A2M17S9Vrho4;R1A2A3Fl;S1S6aG7Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vrho';AdS1S6S0G2S7Vrho1;R1A2S7Vrho';R1A2A3Fi;S1S6S0G16S9Vrho1;R1A2G17A3Fl;S1S0G2S7Vrho';P1bA2Va1;A3S1S0G2S7Vrho';P1cA2Va2;A3S1S0G2S7Vrho';P1dA2VP;A3S1S0G2S7Vrho';P1eA2Se7VP;A1M18A3S1S0S5S35Z8S38G1S7Vrho';P1fA2A2A2S38G1G18A2A3S1S0G2S7Vrho';P20A2Vb4;A3S1S0G2S7Vrho';P21A2Vb5;A3S1S0G2S7Vrho';P22A2Vb6;A3S1S0G2S7Vrho';P24A2Vb7;A3S1S0G2S7Vrho';P4dA2Vb8;A3S1S0G2S7Vrho';P4eA2Vb9;A3S1S0G2S7Vrho';P53A2Vb10;A3S1S0G2S7Vrho';P9fA2Vb12;A3S1S0G2S7Vrho';Pa0A2Vb13;A3S1S0G2S7Vrho';Pa1A2Vb14;A3S1S0S3cG2A1Vtp;S67Vx;Vb13;Vrho';A3A3S1ScS4dVrho1;S53S66Vv;A1A1M19G0A4S1G2S3S78Vrho1;SdG19A1R1A3M1aA1S0S3fG15A1M1bSbVrhoM;R2A2M1cSbVrho1;R2A2M1dA3F_;Fa;S1G2G1aS0G1bG1cS62R3R2A2A3F_;Fa;S1S5S72R1A1S0G1bSbVrho1;S39G1R2A2A2S40G15S39G14G3A2A2A3F_;Fa;S1G2S3S72S38G1R1A2A1A1S0G1bG1dSbVrho';R2A2A3F_;Fa;S1Sa4Vrho4;Vrho';A2S1Sa0Vx;S2dG5S7cVinp;A1A2Vrho';A3S1SedS9fVx;Vrho';A2Se6Vrho';A1Vrho';A3S0G2S7VrhoM;P10A2S7Vrho';P18A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Tvms_;TMm;Tm1;").

Theorem main_handoff_M : ltac2:(tb__ "0|c|
Sd4S0S5S7dVinp;A1Z2A3SbaVsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;R2A7S2S3aQ40M0A1M1G1S2G1G1S2G1G1S2G1G1S2G1G1S2G1G1S2G1G1S2G1G1S2G1G1S2G1G1S2G1G1S2G1G1S2G1G1S2G1G1S2S5S5S2S9dS9dS2S3bS3bS2S8S8S2S8S8S2S8S8S2S3cG1A1M2G2Sb8Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;R15A7S56SbbR1R15R14R13R12R11R10RfReRdR8RcR7RbRaR9A10S56S50S48S3cS57A1S4eSc1S71R3A1R1aA2A3A1S61S79S76R8R5R1S84Vsp;Vdraw;Vinp;A3M3S32S41S3aQ8M4A1M5S82Vinp;A1M6A2A1M7A5Sa7A2S8S1Sb4S4dS9cR3S2dSbcSb9A1Z4000A2A2S96R1S71R5A1R1cA6S1SdbG6R1A2S1S0S5S63R1P18A2S9aA3S1S0S5S63R1P1A2S38G0Vsp;A2M8A3S1S0S5S63R1P8A2S2dG8S81Vinp;A1M9A2A3S1S0S5S63R1P9A2G7A3S1S0S5S63R1PaA2S2fS7eVinp;A1MaG9A2A3S1S0S5S63R1PbA2GaA3S1S0S5S63R1P1eA2S2fG8Z800000A2A3S1S0S3cG5A1MbS9R1P3A2G3A3S1S0GbS9R1P2A2S45G5S7fVinp;A1S44G5S39G4Z0A2S46G5A1A3A3A3Sd1R19R18R17R16R15R14R13R12R11R10RfReRdRcRbRaR9R8R7R6R1R5R1cA17A2A2A2A2A2A2A2A2A2A2A2TrhoM;Tvms_;TMm;Tm1;Ltp;A2Lrho1;A2Lrho';A2Lrho4;A2Lv;A2Lo;A2Lx;A2Lb14;A2Lb13;A2Lb12;A2Lb10;A2Lb9;A2Lb8;A2Lb7;A2Lb6;A2Lb5;A2Lb4;A2LP;A2La2;A2La1;A2Ltid;A2F_;F_;Fw;").
Proof.
  intros w HARGC HQ.
  destruct HQ as (tid & rho4 & Htid & HJ & PM).
  destruct PM as (a1 & a2 & P & b4 & b5 & b6 & b7 & b8 & b9 & x & b10 & o & v & b12 & b13 & b14 & rho' & PM).
  destruct PM as (G2 & G3 & HPL & HPL4 & HPL5 & HPL6 & HPL7 & HPL8 & HPL9 & Ex & HPL10 & Ho & HPL12 & HPL13 & HPL14 & HMI & W12 & W13 & W14 & V25 & Lr & RM & ZX & BD & ROK & PM).
  destruct PM as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & H36 & H77 & H78 & H79 & H80 & H81 & H83 & H159 & H160 & H161 & Hsp).
  destruct w as [tr [ms md]].

  pose proof (M1_fields sp brk mb draw lim inp tid) as (Fh & Flz & Fmt & Fres & Fmaps & Fna & Flim & Fsb & Fbrk & Fisp & Fused & Ftid & Ffds & Ffs & _).
  pose proof (StartMain.sp_facts sp brk mb draw inp Hent Hinp) as (Hwin & Hspr & Hsp16).
  assert (Htop : init_sp_ok (m_vmmaps (M1 tid))) by (unfold init_sp_ok; rewrite Fisp; exact Hwin).
  pose proof (mS_fields (M1 tid) Flz Fmaps Fna a1 a2) as (RS & MS & NS & LS & LMS & IS & KS & SKS).
  assert (SRES : vm_reserved (m_vmmaps (mS (M1 tid) a1 a2)) = segments_reserved segsA) by (rewrite RS; exact Fres).
  assert (SMAPS : vm_maps (m_vmmaps (mS (M1 tid) a1 a2)) = [(a2, Z_to_bv 64 0x38e000); (a1, Z_to_bv 64 0x10000);
            (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000); (Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000); (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000)])
    by (rewrite MS; reflexivity).
  assert (STOP : init_sp_ok (m_vmmaps (mS (M1 tid) a1 a2))) by (clear - Htop IS; unfold init_sp_ok in *; rewrite IS; exact Htop).
  pose proof (a1_facts (M1 tid) Fres Fmaps Fna Htop a1 G2) as (F1lo & F1band & F1top & F1al & F1free).
  pose proof (a2_facts (M1 tid) Fres Fmaps Fna Htop a1 a2 G3) as (F2lo & F2band & F2top & F2al & F2free).
  assert (SA1 : 0x646000 <= bv_unsigned a1 /\ (bv_unsigned a1 + 0x10000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned a1) /\ bv_unsigned a1 + 0x10000 <= alloc_top (m_vmmaps (mS (M1 tid) a1 a2))).
  { unfold alloc_top in *. rewrite IS. repeat split; assumption. }
  assert (SA2 : 0x646000 <= bv_unsigned a2 /\ (bv_unsigned a2 + 0x38e000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned a2) /\ bv_unsigned a2 + 0x38e000 <= alloc_top (m_vmmaps (mS (M1 tid) a1 a2))).
  { unfold alloc_top in *. rewrite IS. repeat split; assumption. }

  pose proof (StartArgBytes.arg_nums sp brk mb draw inp Hent Hinp) as (Nsp & Nfit & N16 & Nargc & Nstr & Nstr8 & NA1 & NA1b & Nrnd & Npad & Nrnd8 & Nlen & Nlenb & Nlen0 & Ntab1 & Ntab2).
  pose proof (Zle_0_nat (tab (in_argv inp))) as T0. pose proof (Zle_0_nat (tab (in_envp inp))) as T1. pose proof (Zle_0_nat (pad_len (in_argv inp) (in_envp inp))) as T2.
  pose proof (A1o_eq sp brk mb draw inp Hent Hinp rho4 HJ) as (J45 & J6 & J1 & J2 & J9 & J10).
  assert (E1 : rw rho' 1%positive = sp) by (rewrite (V25 1%positive) by lia; exact (ji_sp _ _ _ _ _ _ _ HJ)).
  assert (E2 : rw rho' 2%positive = Z_to_bv 64 2).
  { rewrite (V25 2%positive) by lia. rewrite (ji_argc _ _ _ _ _ _ _ HJ). unfold StartArgBytes.ARGC in HARGC. rewrite HARGC. reflexivity. }
  assert (E4 : rw rho' 4%positive = Z_to_bv 64 (bv_unsigned sp + STRo)) by (rewrite (V25 4%positive) by lia; exact (ji_argv0 _ _ _ _ _ _ _ HJ)).
  assert (E5 : rw rho' 5%positive = Z_to_bv 64 (Z.of_nat (length argv0))) by (rewrite (V25 5%positive) by lia; exact (ji_len0 _ _ _ _ _ _ _ HJ)).
  assert (E6 : rw rho' 6%positive = Z_to_bv 64 (bv_unsigned sp + RNDo)) by (rewrite (V25 6%positive) by lia; exact (ji_rand _ _ _ _ _ _ _ HJ)).
  assert (E9 : rw rho' 9%positive = rnd0 draw) by (rewrite (V25 9%positive) by lia; exact J9).
  assert (E10 : rw rho' 10%positive = rnd1 draw) by (rewrite (V25 10%positive) by lia; exact J10).
  assert (Ex' : x = bv_unsigned sp) by (rewrite Ex; unfold x1; rewrite (ji_sp _ _ _ _ _ _ _ HJ); reflexivity).
  assert (R6 : Start7.r6of rho4 = bv_unsigned sp + RNDo) by (unfold Start7.r6of; exact J6).
  assert (Hx : 0x7fff80000000 <= x <= 2 ^ 47) by (first [clear - Ex' Nsp Nfit N16; lia | lia]).
  assert (H16 : x mod 16 = 0) by (rewrite Ex'; exact N16).
  assert (Hxtop : alloc_top (m_vmmaps (mS (M1 tid) a1 a2)) = x - 8388608) by (unfold alloc_top; rewrite IS, Fisp, stack_max_size_val; lia).
  assert (HAL' : arg_layout rho').
  { apply (arg_layout_ext rho4 rho'); [intros i Hi; apply V25; lia|]. exact (arg_layout_of_Jinit sp brk mb draw inp Hent Hinp rho4 HJ). }
  assert (H6' : bv_unsigned (rw rho' 4%positive) + bv_unsigned (rw rho' 5%positive) + 1 <= bv_unsigned (rw rho' 6%positive) /\ bv_unsigned (rw rho' 6%positive) + 16 <= 2 ^ 47).
  { rewrite (V25 4%positive), (V25 5%positive), (V25 6%positive) by lia.
    first [clear - J45 J6 Nsp Nfit N16 Nargc Nstr Nstr8 NA1 NA1b Nrnd Npad Nrnd8 Nlen Nlenb Nlen0 Ntab1 Ntab2 T0 T1 T2 Hx Ex'; lia | lia]. }
  assert (HX1' : 0x7fff80000000 <= bv_unsigned (rw rho' 1%positive) <= 2 ^ 47) by (rewrite E1; lia).

  pose proof W12 as (_ & W12b & _ & W12t). pose proof W13 as (_ & W13b & _ & W13t). pose proof W14 as (_ & W14b & _ & W14t).
  pose proof (GM_low (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10
                rho' b12 b13 b14 ROK H159 H160 H161 (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)) as HGlow.
  pose proof (GM_high (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10
                rho' b12 b13 b14 ROK H159 H160 H161 (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)) as HGhigh.
  pose proof (GM_argf (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10
                rho' b12 b13 b14 ROK H159 H160 H161 (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)) as HGargf.
  pose proof (q12x_lo x Hx) as [Q1 Q2].

  set (Mm := Mmain (M1 tid) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 o b12 b13 b14) in *.
  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF'.
  pose proof HMI as MI. rewrite Flim, Fisp in MI.
  destruct (stage1 (MAIN_of v) Mm (StartTop.Bmain B0) rho' (TPmain x b13 rho') tr ms md Hsp (mi_lzlow MI) (mi_acclow MI)) as (rho1 & Hsp1 & RW1 & RL1 & Z1 & O1).
  { rewrite (mi_lim MI), Bmain_val. clear -Hlim. lia. }
  { intros p Hp HZ. unfold TPmain in Hp. unfold ZPAGES, PA0, PR0 in HZ.
    destruct Hp as [<-|[<-|[<-|Hp]]]; [clear -HZ; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs.PGB in HZ; rewrite u64_of_lit in HZ by lia; lia | clear -HZ; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs.PGA in HZ; rewrite u64_of_lit in HZ by lia; lia | |].
    - clear -W13b HZ. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in W13b. lia.
    - pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8.TP18_facts (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 x b10 Hx H16 rho' ROK p Hp) as [TQ1 TQ2]. clear -TQ1 HZ. lia. }
  { intros a n Hn HZ. exact (main_disjoint_low v rho' HF' HGlow a n Hn HZ). }

  pose proof Hsp1 as [HsmA1 HJ1]. pose proof (smatchA_smatch segsA _ _ _ _ HsmA1) as Hsm1. rewrite virt_unfold in Hsm1.
  set (msv := vms md (tpF (TPmain x b13 rho')) ms) in *. set (mdv := vmd md) in *.
  assert (E1r : rw rho1 1%positive = sp) by (rewrite RW1; exact E1).
  assert (E2r : rw rho1 2%positive = Z_to_bv 64 2) by (rewrite RW1; exact E2).
  assert (E4r : rw rho1 4%positive = Z_to_bv 64 (bv_unsigned sp + STRo)) by (rewrite RW1; exact E4).
  assert (E5r : rw rho1 5%positive = Z_to_bv 64 (Z.of_nat (length argv0))) by (rewrite RW1; exact E5).
  assert (E6r : rw rho1 6%positive = Z_to_bv 64 (bv_unsigned sp + RNDo)) by (rewrite RW1; exact E6).
  assert (E9r : rw rho1 9%positive = rnd0 draw) by (rewrite RW1; exact E9).
  assert (E10r : rw rho1 10%positive = rnd1 draw) by (rewrite RW1; exact E10).
  assert (HRM : forall a : word, ARGF rho1 a -> rm rho1 a = ms_mem ms0A a).
  { intros a Ha. assert (Ha' : ARGF rho' a) by (apply (ARGF_ext rho' rho1 a ltac:(intros i Hi; apply RW1)); exact Ha).
    assert (Ha4 : ARGF rho4 a) by (apply (ARGF_ext rho4 rho' a ltac:(intros i Hi; apply V25; lia)); exact Ha').
    pose proof Ha' as [HaLo _]. rewrite E1 in HaLo.
    rewrite O1 by (unfold ZPAGES, PA0, PR0; first [clear - HaLo Ex' Hx; lia | lia]). rewrite (RM a Ha4). exact (ji_mem _ _ _ _ _ _ _ HJ a). }
  pose proof (smatch_facts segsA _ _ _ Hsm1) as HF1.
  assert (HROK1 : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8.rhoOK (mS (M1 tid) a1 a2) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 rho1).
  { apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8.rhoOK_agree (mS (M1 tid) a1 a2) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 200%positive rho' rho1); [lia | exact ROK | intros i Hi; apply RW1]. }
  pose proof (GM_argf (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10
                rho1 b12 b13 b14 HROK1 ltac:(rewrite RW1; exact H159) ltac:(rewrite RW1; exact H160) ltac:(rewrite RW1; exact H161)
                (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)) as HGargf1.
  pose proof (GM_low (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10
                rho1 b12 b13 b14 HROK1 ltac:(rewrite RW1; exact H159) ltac:(rewrite RW1; exact H160) ltac:(rewrite RW1; exact H161)
                (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)) as HGlow1.
  pose proof (GM_high (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10
                rho1 b12 b13 b14 HROK1 ltac:(rewrite RW1; exact H159) ltac:(rewrite RW1; exact H160) ltac:(rewrite RW1; exact H161)
                (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)) as HGhigh1.
  assert (HX1r : 0x7fff80000000 <= bv_unsigned (rw rho1 1%positive) <= 2 ^ 47) by (rewrite RW1; exact HX1').
  assert (HALr : arg_layout rho1) by (exact (arg_layout_ext rho' rho1 ltac:(intros i Hi; apply RW1) HAL')).
  assert (H6r : bv_unsigned (rw rho1 4%positive) + bv_unsigned (rw rho1 5%positive) + 1 <= bv_unsigned (rw rho1 6%positive) /\ bv_unsigned (rw rho1 6%positive) + 16 <= 2 ^ 47) by (rewrite !RW1; exact H6').
  assert (AP : forall a : word, ARGF rho1 a -> ~ in_ranges rho1 (ss_objs (ax_S (MAIN_of v))) a).
  { intros a Ha. exact (main_apart_argf v rho1 HX1r HALr H6r ltac:(rewrite E1r; rewrite <- Ex'; exact HGargf1) a Ha). }
  assert (H2 : 2 <= ARGC) by (clear -HARGC; lia).
  destruct (stage2_M sp brk mb draw inp Hent Hinp v rho1 tr msv mdv Hsm1 H2 E2r E1r E4r E5r E6r E9r E10r HRM AP)
    as (C3 & R3 & R9 & RL3 & RLo & RMo & RMi & UA & UE).
  assert (H24 : 1 <= bv_unsigned (rw rho1 24%positive) < 4194304).
  { destruct (facts24 v) as [Fa Fb]. pose proof (fact_in rho' _ _ Fa HF') as X1. pose proof (fact_in rho' _ _ Fb HF') as X2.
    cbn [holds eval] in X1, X2. rewrite !u64_of_lit in X1, X2 by (clear; lia). rewrite RW1. clear -X1 X2. lia. }
  destruct (factsM_hold sp brk mb draw inp Hent Hinp v rho1 msv H2 E1r E4r E5r E6r H24) as (HFM & V1 & V8 & V9 & V10 & V11 & V16 & V24 & V30 & V4 & V5 & VL3 & VL2 & VW1 & VW2 & VW6).
  set (rho3 := rho3M v rho1 msv L3 (Z.of_nat (length argv1))) in *.
  set (rhoM := rho_sub rho3 sFM) in *.
  pose proof (finish_M v rho3 _ C3 HFM) as SMM. fold rhoM in SMM.
  assert (RMM : forall a, rm rhoM a = rm rho3 a) by (intros a; reflexivity).
  exists tid, a1, a2, P, b4, b5, b6, b7, b8, b9, b10, b12, b13, b14, x, o, v, rho4, rho', rho1, (TPmain x b13 rho').
  cbv zeta. rewrite !virt_unfold. cbn [snd cfg_ms]. fold Mm. fold msv. fold mdv. fold rho3. fold rhoM.

  assert (ZPG : forall z, ZPAGES z -> rm rhoM (Z_to_bv 64 z) = Some (Z_to_bv 8 0)).
  { intros z Hz. rewrite RMM, RMo; [exact (Z1 z Hz)|]. apply (main_apart_low v rho1 HF1 HGlow1). rewrite u64_of_lit by (clear -Hz; unfold ZPAGES, PA0, PR0 in Hz; lia). apply ZPAGES_ZLOW. exact Hz. }
  pose proof (Start7.arith18 x Hx H16 (bv_unsigned sp + RNDo) ltac:(clear -Ex' Nrnd Nstr Nargc T0 T1 T2; lia) ltac:(clear -Ex' Nfit Nlen; lia) ltac:(clear -Ex' Nlenb Nlen Nsp; lia)) as AR.
  destruct AR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24).
  assert (ZB : forall z, q12x x <= z < Z.max (Start7.Q18 x) (Start7.Wz (bv_unsigned sp + RNDo)) -> rm rhoM (Z_to_bv 64 z) = Some (Z_to_bv 8 0)).
  { intros z Hz.
    assert (Hz64 : 0 <= z < 2 ^ 64) by (clear -Hz Q1 A14 A18; unfold kHighMemBeg in *; lia).
    assert (HzP : ~ ZPAGES z) by (clear -Hz Q1; unfold ZPAGES, PA0, PR0; lia).
    rewrite RMM, RMo.
    - rewrite O1 by (rewrite u64_of_lit by exact Hz64; exact HzP). rewrite R6 in ZX. exact (ZX z Hz).
    - apply (main_apart_band v rho1 HF1 (q12x x) ltac:(clear -Q1 Q2; unfold kHighMemBeg in *; lia) HGhigh1). rewrite u64_of_lit by exact Hz64.
      clear -Hz A14 A18. unfold kHighMemBeg in *. lia. }

  assert (RMiM : forall a : word, in_ranges rho1 (ss_objs (ax_S (MAIN_of v))) a -> rm rhoM a = ms_mem msv a) by (intros a Ha; rewrite RMM; exact (RMi a Ha)).
  pose proof (sh0_checks v) as (CK0 & CK1 & CK2 & CK3). cbv zeta in CK0, CK1, CK2, CK3.
  assert (LOWZ0 : forall a, 0x800bc000 <= a < 0x800c0c00 -> rm rhoM (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  { intros a Ha. pose proof (handoff_view_zero_range rho1 rhoM (ax_S (MAIN_of v)) tr msv mdv (SLit 0x800bc000) _ Hsm1 RMiM CK0 (a - 0x800bc000) ltac:(clear -Ha; apply In_zseq; rewrite Z2Nat.id by lia; lia)) as X.
    cbn [eval] in X. rewrite u64_of_lit in X by (clear; lia). replace (0x800bc000 + (a - 0x800bc000)) with a in X by (clear; lia). exact (view_rm _ a _ ltac:(clear -Ha; lia) X). }
  assert (LOWZ : forall a, 0x800c0998 <= a < 0x800c09a8 -> rm rhoM (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) by (intros a Ha; apply LOWZ0; clear -Ha; lia).
  assert (PGAZ : forall a, 0x7fffc288 <= a < 0x7fffc298 -> rm rhoM (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  { intros a Ha. pose proof (handoff_view_zero_range rho1 rhoM (ax_S (MAIN_of v)) tr msv mdv (SLit 0x7fffc000) _ Hsm1 RMiM CK3 (a - 0x7fffc000) ltac:(clear -Ha; apply In_zseq; simpl Z.of_nat; lia)) as X.
    cbn [eval] in X. rewrite u64_of_lit in X by (clear; lia). replace (0x7fffc000 + (a - 0x7fffc000)) with a in X by (clear; lia). exact (view_rm _ a _ ltac:(clear -Ha; lia) X). }
  assert (PRES : forall a, (0x7fffc570 <= a < 0x7fffc750 \/ 0x800158a8 <= a < 0x80015ba8) -> rm rhoM (Z_to_bv 64 a) <> None).
  { intros a [Ha|Ha].
    - destruct (handoff_view_present_range rho1 rhoM (ax_S (MAIN_of v)) tr msv mdv (SLit 0x7fffc000) _ Hsm1 RMiM CK1 (a - 0x7fffc000) ltac:(clear -Ha; apply In_zseq; simpl Z.of_nat; lia)) as [b X].
      cbn [eval] in X. rewrite u64_of_lit in X by (clear; lia). replace (0x7fffc000 + (a - 0x7fffc000)) with a in X by (clear; lia). rewrite (view_rm _ a _ ltac:(clear -Ha; lia) X). discriminate.
    - destruct (handoff_view_present_range rho1 rhoM (ax_S (MAIN_of v)) tr msv mdv (SLit 0x80015000) _ Hsm1 RMiM CK2 (a - 0x80015000) ltac:(clear -Ha; apply In_zseq; simpl Z.of_nat; lia)) as [b X].
      cbn [eval] in X. rewrite u64_of_lit in X by (clear; lia). replace (0x80015000 + (a - 0x80015000)) with a in X by (clear; lia). rewrite (view_rm _ a _ ltac:(clear -Ha; lia) X). discriminate. }
  assert (LITM : forall offp b, 0 <= offp < 4096 -> byte_info (ss_objs (ax_S (MAIN_of v))) (SLit PGLIT) offp = BLit b -> rm rhoM (Z_to_bv 64 (PGLIT + offp)) = Some (Z_to_bv 8 b)).
  { intros offp b Hoff Hbi. pose proof (handoff_view rho1 rhoM (ax_S (MAIN_of v)) tr msv mdv (SLit PGLIT) offp Hsm1 RMiM ltac:(rewrite Hbi; discriminate)) as (_ & _ & X).
    rewrite Hbi in X. cbv beta iota in X. change (eval rho1 (SLit PGLIT)) with (Z_to_bv 64 PGLIT) in X. unfold PGLIT in X, Hoff |- *.
    rewrite u64_of_lit in X by (clear; lia). eapply view_rm; [clear -Hoff; lia | exact X]. }

  assert (OUTM : forall z, 0x646000 <= z < 0x7fff00000000 -> outside_all rhoM objs_M (Z_to_bv 64 z)).
  { intros z Hz. apply (objs_far_outside true rhoM objs_M z (proj1 objs_MU_far)); [rewrite V1; exact Nsp | intros _; rewrite V8; clear -Nsp Nstr NA1 Nargc; lia | | exact Hz].
    rewrite V4, E4r, u64_of_lit by (clear -Nsp Nfit Nstr Nrnd Nlen NA1b Nargc T0 T1 T2; lia). clear -Nsp Nstr Nargc; lia. }

  pose proof (floor8_props (shx x)) as (F81 & F82 & F83).
  assert (SHXle : shx x <= Start7.SXE (bv_unsigned sp + RNDo)).
  { unfold shx, Start7.SXE, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib.SHB. rewrite Ex'. clear -A4 Nsp Nrnd Nstr T0 T1 T2 Nargc.
    pose proof (Z.div_le_mono (bv_unsigned sp) (Start7.XEz (bv_unsigned sp + RNDo)) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (SHOK : shadow_ok rhoM S_M).
  { unfold shadow_ok. change (ax_X S_M) with ([(SLit 0x14d40, SLit 0x80); (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.add DrvIfaceT.sp0 (SLit (- (DEEP + 128))), SLit DEEP); X_rds] ++ X_lits).
    replace (bv_unsigned (eval rhoM (ax_base S_M))) with 0x7fff8000 by (cbn [ax_base S_M eval]; rewrite u64_of_lit; [reflexivity | unfold Code.SHB; lia]).
    apply Forall_app. split.
    - apply (shadow_ok_X3 rhoM objs_M (bv_unsigned sp) (q12x x) (shx x - shx x mod 8) OUTM V1 N16 ltac:(clear -Hx Ex'; lia)).
      + clear -Q1. lia.
      + unfold q12x. apply (proj1 (proj2 (pagedown_le _))).
      + unfold q12x, shx. rewrite Ex'. clear. lia.
      + unfold shx. rewrite Ex'. reflexivity.
      + exact ZPG.
      + intros z Hz. apply LOWZ0. clear -Hz. lia.
      + intros z Hz. apply ZB. clear -Hz F81 SHXle A12. lia.
    - apply (lits_sound rhoM (ss_objs (ax_S (MAIN_of v))) objs_M PGLIT 0x7fff8000); [clear; unfold PGLIT; lia | clear; lia | exact LITM | | exact (lits_ok_main v)].
      intros z Hz. apply OUTM. clear -Hz. unfold PGLIT in Hz. lia. }

  pose proof HsmA1 as (_ & MI1 & _ & _ & HZ1). cbn [snd cfg_model cfg_ms] in MI1, HZ1.
  pose proof (Mmain_fds (M1 tid) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 o b12 b13 b14) as [MF1 MF2]. fold Mm in MF1, MF2.
  split.
  {   split; [| exact HJ1].
    split; [exact SMM|]. split; [exact MI1|]. split; [exact (proj1 S_M_wf)|]. split; [exact SHOK | exact HZ1]. }
  split.
  {   unfold DrvM.P0M. split; [| split; [| split; [| split]]].
    - split.
      + split; [exact LOWZ | exact PRES].
      + intros z Hz. unfold SHRZ, Geometry.Sh, Geometry.SHADOW_OFF in Hz. cbn in Hz. destruct Hz as [Hz|Hz]; [apply PGAZ; clear -Hz; lia|]. apply ZPG. unfold ZPAGES, PA0, PR0. clear -Hz. lia.
    - rewrite VL3. exact (L3_head sp brk mb draw inp Hent Hinp H2).
    - unfold Uv. exact V9.
    - split.
      + apply (ZARG_of rhoM (bv_unsigned sp) LEN (Start7.XEz (bv_unsigned sp + RNDo)) (Start7.SXE (bv_unsigned sp + RNDo)) (q12x x)
                 (Z.max (Start7.Q18 x) (Start7.Wz (bv_unsigned sp + RNDo))) V1 V11 N16).
        * clear -Nsp. lia.
        * clear -Nlen Nrnd Nstr T0 T1 T2 Nargc. lia.
        * clear -Nfit. lia.
        * clear -A4 Nlen. lia.
        * exact A3.
        * unfold Start7.SXE, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib.SHB. reflexivity.
        * clear -A12. lia.
        * unfold q12x, shx. rewrite Ex'. clear. lia.
        * exact ZB.
      + intros z Hz. unfold SHRZ2, Geometry.Sh, Geometry.SHADOW_OFF in Hz. apply ZPG. unfold ZPAGES, PA0, PR0. clear -Hz. cbn in Hz. lia.
    - unfold SLK1, Uv. rewrite V9, V10. pose proof (argv1_fits sp brk mb draw inp Hent Hinp H2) as [F1 _]. clear -F1 Nlen. lia. }

  split; [unfold Uv; exact V24|]. split; [unfold Uv; exact V1|]. split; [unfold Uv; exact V8|]. split; [unfold Uv; exact V9|]. split; [unfold Uv; exact V10|].
  split; [unfold Uv; exact V11|]. split; [unfold Uv; exact V30|]. split; [exact VL3|].
  split; [rewrite VL2, RL1, Lr; rewrite (ji_str0 _ _ _ _ _ _ _ HJ); reflexivity|].

  unfold sheet. cbv zeta. rewrite !virt_unfold. cbn [snd cfg_ms]. fold Mm msv.
  pose proof HMI as MI2. rewrite Flim, Fisp in MI2.
  split; [rewrite MF1; exact Ffds|]. split; [rewrite MF2; exact Ffs|]. split; [exact (mi_lim MI)|].
  split; [exact MI2|]. split; [exact Htid|]. split; [exact Ex'|].
  split; [exact G2|]. split; [exact G3|]. split; [exact HPL|]. split; [exact HPL4|]. split; [exact HPL5|]. split; [exact HPL6|].
  split; [exact HPL7|]. split; [exact HPL8|]. split; [exact HPL9|]. split; [exact HPL10|]. split; [exact Ho|].
  split; [exact HPL12|]. split; [exact HPL13|]. split; [exact HPL14|].
  split; [exact (conj W12b W12t)|]. split; [exact (conj W13b W13t)|]. split; [exact (conj W14b W14t)|].
  split; [exact HJ|]. split; [exact V25|]. split; [exact Lr|]. split; [exact ROK|]. split; [exact RW1|]. split; [exact RL1|].
  split; [exact H27|]. split; [exact H28|]. split; [exact H29|]. split; [exact H30|]. split; [exact H31|].
  split; [exact H32|]. split; [exact H33|]. split; [exact H34|]. split; [exact H36|]. split; [exact H77|]. split; [exact H78|].
  split; [exact H83|]. split; [exact H159|]. split; [exact H160|]. split; [exact H161|].
  split; [reflexivity|].
  split; [exact Hsm1|].
  split; [intros a Ha; rewrite RMM; exact (RMo a Ha)|].
  split; [exact RMiM|].
  split; [exact Z1|]. split; [exact O1|]. split; [exact RM|].
  split; [rewrite <- R6; exact ZX|]. split; [exact BD|].
  rewrite V16. apply RW1.
Qed.

Theorem main_handoff_U : ltac2:(tb__ "0|d|
Sd4S3S0S5S7dVinp;A1M0Z2A3A1SbaVsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;R2A7S2S3aQ40M1A1M2G2S2G2G2S2G2G2S2G2G2S2G2G2S2G2G2S2G2G2S2G2G2S2G2G2S2G2G2S2G2G2S2G2G2S2G2G2S2G2G2S2S5S5S2S9dS9dS2S3bS3bS2S8S8S2S8S8S2S8S8S2S3cG2A1M3G3Sb8Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;R15A7S56SbbR1R15R14R13R12R11R10RfReRdR8RcR7RbRaR9A10S56S50S48S3cS57A1S4eSc1S71R3A1R1aA2A3A1S61S79S77R8R5R1S83Vsp;Vdraw;Vinp;A3M4A4Sa8A2S8S1Sb4S4dS9cR3S2dSbcSb9A1Z4000A2A2S97R1S71R5A1R1cA6S1SddS7fVinp;A1M5R1A2S1S0S5S63R1P18A2S9aA3S1S0S5S63R1P1A2S38G1Vsp;A2M6A3S1S0S5S63R1P2M7A2G0A3S1S0S5S63R1P4A2S2dG6S80Vinp;A1M8A2A3S1S0S5S63R1P5A2S32S41S3aQ8A1M9G5A2A1A3S1S0S5S63R1PcA2S2fS7eVinp;A1MaG8A2A3S1S0S5S63R1PbMbA2GaA3S1S0S5S63R1P1eA2S2fG6Z800000A2A3S1S6Sc5R1GbA2S0G2S7R3R2A2S7R9R2A2A3F_;Fi;S1S0S3cG9A1McS9R1G7A2G4A3S1S0GcS9R1P3A2G4A3Sd1R19R18R17R16R15R14R13R12R11R10RfReRdRcRbRaR9R8R7R6R1R5R1cA17A2A2A2A2A2A2A2A2A2A2A2A2A2TrhoM;Tvms_;TMm;Tm1;Ltp;A2Lrho1;A2Lrho';A2Lrho4;A2Lv;A2Lo;A2Lx;A2Lb14;A2Lb13;A2Lb12;A2Lb10;A2Lb9;A2Lb8;A2Lb7;A2Lb6;A2Lb5;A2Lb4;A2LP;A2La2;A2La1;A2Ltid;A2F_;F_;Fw;").
Proof.
  intros w HARGC HQ.
  destruct HQ as (tid & rho4 & Htid & HJ & PM).
  destruct PM as (a1 & a2 & P & b4 & b5 & b6 & b7 & b8 & b9 & x & b10 & o & v & b12 & b13 & b14 & rho' & PM).
  destruct PM as (G2 & G3 & HPL & HPL4 & HPL5 & HPL6 & HPL7 & HPL8 & HPL9 & Ex & HPL10 & Ho & HPL12 & HPL13 & HPL14 & HMI & W12 & W13 & W14 & V25 & Lr & RM & ZX & BD & ROK & PM).
  destruct PM as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & H36 & H77 & H78 & H79 & H80 & H81 & H83 & H159 & H160 & H161 & Hsp).
  destruct w as [tr [ms md]].

  pose proof (M1_fields sp brk mb draw lim inp tid) as (Fh & Flz & Fmt & Fres & Fmaps & Fna & Flim & Fsb & Fbrk & Fisp & Fused & Ftid & Ffds & Ffs & _).
  pose proof (StartMain.sp_facts sp brk mb draw inp Hent Hinp) as (Hwin & Hspr & Hsp16).
  assert (Htop : init_sp_ok (m_vmmaps (M1 tid))) by (unfold init_sp_ok; rewrite Fisp; exact Hwin).
  pose proof (mS_fields (M1 tid) Flz Fmaps Fna a1 a2) as (RS & MS & NS & LS & LMS & IS & KS & SKS).
  assert (SRES : vm_reserved (m_vmmaps (mS (M1 tid) a1 a2)) = segments_reserved segsA) by (rewrite RS; exact Fres).
  assert (SMAPS : vm_maps (m_vmmaps (mS (M1 tid) a1 a2)) = [(a2, Z_to_bv 64 0x38e000); (a1, Z_to_bv 64 0x10000);
            (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000); (Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000); (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000)])
    by (rewrite MS; reflexivity).
  assert (STOP : init_sp_ok (m_vmmaps (mS (M1 tid) a1 a2))) by (clear - Htop IS; unfold init_sp_ok in *; rewrite IS; exact Htop).
  pose proof (a1_facts (M1 tid) Fres Fmaps Fna Htop a1 G2) as (F1lo & F1band & F1top & F1al & F1free).
  pose proof (a2_facts (M1 tid) Fres Fmaps Fna Htop a1 a2 G3) as (F2lo & F2band & F2top & F2al & F2free).
  assert (SA1 : 0x646000 <= bv_unsigned a1 /\ (bv_unsigned a1 + 0x10000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned a1) /\ bv_unsigned a1 + 0x10000 <= alloc_top (m_vmmaps (mS (M1 tid) a1 a2))).
  { unfold alloc_top in *. rewrite IS. repeat split; assumption. }
  assert (SA2 : 0x646000 <= bv_unsigned a2 /\ (bv_unsigned a2 + 0x38e000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned a2) /\ bv_unsigned a2 + 0x38e000 <= alloc_top (m_vmmaps (mS (M1 tid) a1 a2))).
  { unfold alloc_top in *. rewrite IS. repeat split; assumption. }

  pose proof (StartArgBytes.arg_nums sp brk mb draw inp Hent Hinp) as (Nsp & Nfit & N16 & Nargc & Nstr & Nstr8 & NA1 & NA1b & Nrnd & Npad & Nrnd8 & Nlen & Nlenb & Nlen0 & Ntab1 & Ntab2).
  pose proof (Zle_0_nat (tab (in_argv inp))) as T0. pose proof (Zle_0_nat (tab (in_envp inp))) as T1. pose proof (Zle_0_nat (pad_len (in_argv inp) (in_envp inp))) as T2.
  pose proof (A1o_eq sp brk mb draw inp Hent Hinp rho4 HJ) as (J45 & J6 & J1 & J2 & J9 & J10).
  assert (E1 : rw rho' 1%positive = sp) by (rewrite (V25 1%positive) by lia; exact (ji_sp _ _ _ _ _ _ _ HJ)).
  assert (E2 : rw rho' 2%positive = Z_to_bv 64 ARGC) by (rewrite (V25 2%positive) by lia; exact (ji_argc _ _ _ _ _ _ _ HJ)).
  assert (E4 : rw rho' 4%positive = Z_to_bv 64 (bv_unsigned sp + STRo)) by (rewrite (V25 4%positive) by lia; exact (ji_argv0 _ _ _ _ _ _ _ HJ)).
  assert (E5 : rw rho' 5%positive = Z_to_bv 64 (Z.of_nat (length argv0))) by (rewrite (V25 5%positive) by lia; exact (ji_len0 _ _ _ _ _ _ _ HJ)).
  assert (E6 : rw rho' 6%positive = Z_to_bv 64 (bv_unsigned sp + RNDo)) by (rewrite (V25 6%positive) by lia; exact (ji_rand _ _ _ _ _ _ _ HJ)).
  assert (E9 : rw rho' 9%positive = rnd0 draw) by (rewrite (V25 9%positive) by lia; exact J9).
  assert (E10 : rw rho' 10%positive = rnd1 draw) by (rewrite (V25 10%positive) by lia; exact J10).
  assert (Ex' : x = bv_unsigned sp) by (rewrite Ex; unfold x1; rewrite (ji_sp _ _ _ _ _ _ _ HJ); reflexivity).
  assert (R6 : Start7.r6of rho4 = bv_unsigned sp + RNDo) by (unfold Start7.r6of; exact J6).
  assert (Hx : 0x7fff80000000 <= x <= 2 ^ 47) by (first [clear - Ex' Nsp Nfit N16; lia | lia]).
  assert (H16 : x mod 16 = 0) by (rewrite Ex'; exact N16).
  assert (Hxtop : alloc_top (m_vmmaps (mS (M1 tid) a1 a2)) = x - 8388608) by (unfold alloc_top; rewrite IS, Fisp, stack_max_size_val; lia).
  assert (HAL' : arg_layout rho').
  { apply (arg_layout_ext rho4 rho'); [intros i Hi; apply V25; lia|]. exact (arg_layout_of_Jinit sp brk mb draw inp Hent Hinp rho4 HJ). }
  assert (H6' : bv_unsigned (rw rho' 4%positive) + bv_unsigned (rw rho' 5%positive) + 1 <= bv_unsigned (rw rho' 6%positive) /\ bv_unsigned (rw rho' 6%positive) + 16 <= 2 ^ 47).
  { rewrite (V25 4%positive), (V25 5%positive), (V25 6%positive) by lia.
    first [clear - J45 J6 Nsp Nfit N16 Nargc Nstr Nstr8 NA1 NA1b Nrnd Npad Nrnd8 Nlen Nlenb Nlen0 Ntab1 Ntab2 T0 T1 T2 Hx Ex'; lia | lia]. }
  assert (HX1' : 0x7fff80000000 <= bv_unsigned (rw rho' 1%positive) <= 2 ^ 47) by (rewrite E1; lia).

  pose proof W12 as (_ & W12b & _ & W12t). pose proof W13 as (_ & W13b & _ & W13t). pose proof W14 as (_ & W14b & _ & W14t).
  pose proof (GM_low (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10
                rho' b12 b13 b14 ROK H159 H160 H161 (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)) as HGlow.
  pose proof (GM_high (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10
                rho' b12 b13 b14 ROK H159 H160 H161 (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)) as HGhigh.
  pose proof (GM_argf (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10
                rho' b12 b13 b14 ROK H159 H160 H161 (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)) as HGargf.
  pose proof (q12x_lo x Hx) as [Q1 Q2].

  set (Mm := Mmain (M1 tid) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 o b12 b13 b14) in *.
  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF'.
  pose proof HMI as MI. rewrite Flim, Fisp in MI.
  destruct (stage1 (MAIN_of v) Mm (StartTop.Bmain B0) rho' (TPmain x b13 rho') tr ms md Hsp (mi_lzlow MI) (mi_acclow MI)) as (rho1 & Hsp1 & RW1 & RL1 & Z1 & O1).
  { rewrite (mi_lim MI), Bmain_val. clear -Hlim. lia. }
  { intros p Hp HZ. unfold TPmain in Hp. unfold ZPAGES, PA0, PR0 in HZ.
    destruct Hp as [<-|[<-|[<-|Hp]]]; [clear -HZ; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs.PGB in HZ; rewrite u64_of_lit in HZ by lia; lia | clear -HZ; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs.PGA in HZ; rewrite u64_of_lit in HZ by lia; lia | |].
    - clear -W13b HZ. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in W13b. lia.
    - pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8.TP18_facts (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 x b10 Hx H16 rho' ROK p Hp) as [TQ1 TQ2]. clear -TQ1 HZ. lia. }
  { intros a n Hn HZ. exact (main_disjoint_low v rho' HF' HGlow a n Hn HZ). }

  pose proof Hsp1 as [HsmA1 HJ1]. pose proof (smatchA_smatch segsA _ _ _ _ HsmA1) as Hsm1. rewrite virt_unfold in Hsm1.
  set (msv := vms md (tpF (TPmain x b13 rho')) ms) in *. set (mdv := vmd md) in *.
  assert (E1r : rw rho1 1%positive = sp) by (rewrite RW1; exact E1).
  assert (E2r : rw rho1 2%positive = Z_to_bv 64 ARGC) by (rewrite RW1; exact E2).
  assert (HL2 : rl rho1 2%positive = argv0 ++ [Z_to_bv 8 0]) by (rewrite RL1, Lr; exact (ji_str0 _ _ _ _ _ _ _ HJ)).
  assert (E4r : rw rho1 4%positive = Z_to_bv 64 (bv_unsigned sp + STRo)) by (rewrite RW1; exact E4).
  assert (E5r : rw rho1 5%positive = Z_to_bv 64 (Z.of_nat (length argv0))) by (rewrite RW1; exact E5).
  assert (E6r : rw rho1 6%positive = Z_to_bv 64 (bv_unsigned sp + RNDo)) by (rewrite RW1; exact E6).
  assert (E9r : rw rho1 9%positive = rnd0 draw) by (rewrite RW1; exact E9).
  assert (E10r : rw rho1 10%positive = rnd1 draw) by (rewrite RW1; exact E10).
  assert (HRM : forall a : word, ARGF rho1 a -> rm rho1 a = ms_mem ms0A a).
  { intros a Ha. assert (Ha' : ARGF rho' a) by (apply (ARGF_ext rho' rho1 a ltac:(intros i Hi; apply RW1)); exact Ha).
    assert (Ha4 : ARGF rho4 a) by (apply (ARGF_ext rho4 rho' a ltac:(intros i Hi; apply V25; lia)); exact Ha').
    pose proof Ha' as [HaLo _]. rewrite E1 in HaLo.
    rewrite O1 by (unfold ZPAGES, PA0, PR0; first [clear - HaLo Ex' Hx; lia | lia]). rewrite (RM a Ha4). exact (ji_mem _ _ _ _ _ _ _ HJ a). }
  pose proof (smatch_facts segsA _ _ _ Hsm1) as HF1.
  assert (HROK1 : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8.rhoOK (mS (M1 tid) a1 a2) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 rho1).
  { apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8.rhoOK_agree (mS (M1 tid) a1 a2) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 200%positive rho' rho1); [lia | exact ROK | intros i Hi; apply RW1]. }
  pose proof (GM_argf (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10
                rho1 b12 b13 b14 HROK1 ltac:(rewrite RW1; exact H159) ltac:(rewrite RW1; exact H160) ltac:(rewrite RW1; exact H161)
                (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)) as HGargf1.
  pose proof (GM_low (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10
                rho1 b12 b13 b14 HROK1 ltac:(rewrite RW1; exact H159) ltac:(rewrite RW1; exact H160) ltac:(rewrite RW1; exact H161)
                (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)) as HGlow1.
  pose proof (GM_high (mS (M1 tid) a1 a2) a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10
                rho1 b12 b13 b14 HROK1 ltac:(rewrite RW1; exact H159) ltac:(rewrite RW1; exact H160) ltac:(rewrite RW1; exact H161)
                (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)) as HGhigh1.
  assert (HX1r : 0x7fff80000000 <= bv_unsigned (rw rho1 1%positive) <= 2 ^ 47) by (rewrite RW1; exact HX1').
  assert (HALr : arg_layout rho1) by (exact (arg_layout_ext rho' rho1 ltac:(intros i Hi; apply RW1) HAL')).
  assert (H6r : bv_unsigned (rw rho1 4%positive) + bv_unsigned (rw rho1 5%positive) + 1 <= bv_unsigned (rw rho1 6%positive) /\ bv_unsigned (rw rho1 6%positive) + 16 <= 2 ^ 47) by (rewrite !RW1; exact H6').
  assert (AP : forall a : word, ARGF rho1 a -> ~ in_ranges rho1 (ss_objs (ax_S (MAIN_of v))) a).
  { intros a Ha. exact (main_apart_argf v rho1 HX1r HALr H6r ltac:(rewrite E1r; rewrite <- Ex'; exact HGargf1) a Ha). }
  destruct (stage2_U sp brk mb draw inp Hent Hinp v rho1 tr msv mdv Hsm1 E1r E4r E5r E6r E9r E10r HL2 HRM AP)
    as (C3 & R3 & RL2' & RL3' & RLo & RMo & RMi & UE).
  assert (H24 : 1 <= bv_unsigned (rw rho1 24%positive) < 4194304).
  { destruct (facts24 v) as [Fa Fb]. pose proof (fact_in rho' _ _ Fa HF') as X1. pose proof (fact_in rho' _ _ Fb HF') as X2.
    cbn [holds eval] in X1, X2. rewrite !u64_of_lit in X1, X2 by (clear; lia). rewrite RW1. clear -X1 X2. lia. }
  destruct (factsU_hold sp brk mb draw inp Hent Hinp v rho1 msv HARGC E1r E2r E4r E5r E6r H24) as (HFU & V1 & V2 & V4 & V5 & V12 & V11 & V16 & V24 & V30 & V11lo & VL2 & VL3 & VLo).
  set (rho3 := rho3U v rho1 msv L2U) in *.
  set (rhoM := rho_sub rho3 sFU) in *.
  pose proof (finish_U v rho3 _ C3 HFU) as SMM. fold rhoM in SMM.
  assert (RMM : forall a, rm rhoM a = rm rho3 a) by (intros a; reflexivity).
  exists tid, a1, a2, P, b4, b5, b6, b7, b8, b9, b10, b12, b13, b14, x, o, v, rho4, rho', rho1, (TPmain x b13 rho').
  cbv zeta. rewrite !virt_unfold. cbn [snd cfg_ms]. fold Mm. fold msv. fold mdv. fold rho3. fold rhoM.

  assert (ZPG : forall z, ZPAGES z -> rm rhoM (Z_to_bv 64 z) = Some (Z_to_bv 8 0)).
  { intros z Hz. rewrite RMM, RMo; [exact (Z1 z Hz)|]. apply (main_apart_low v rho1 HF1 HGlow1). rewrite u64_of_lit by (clear -Hz; unfold ZPAGES, PA0, PR0 in Hz; lia). apply ZPAGES_ZLOW. exact Hz. }
  pose proof (Start7.arith18 x Hx H16 (bv_unsigned sp + RNDo) ltac:(clear -Ex' Nrnd Nstr Nargc T0 T1 T2; lia) ltac:(clear -Ex' Nfit Nlen; lia) ltac:(clear -Ex' Nlenb Nlen Nsp; lia)) as AR.
  destruct AR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24).
  assert (ZB : forall z, q12x x <= z < Z.max (Start7.Q18 x) (Start7.Wz (bv_unsigned sp + RNDo)) -> rm rhoM (Z_to_bv 64 z) = Some (Z_to_bv 8 0)).
  { intros z Hz.
    assert (Hz64 : 0 <= z < 2 ^ 64) by (clear -Hz Q1 A14 A18; unfold kHighMemBeg in *; lia).
    assert (HzP : ~ ZPAGES z) by (clear -Hz Q1; unfold ZPAGES, PA0, PR0; lia).
    rewrite RMM, RMo.
    - rewrite O1 by (rewrite u64_of_lit by exact Hz64; exact HzP). rewrite R6 in ZX. exact (ZX z Hz).
    - apply (main_apart_band v rho1 HF1 (q12x x) ltac:(clear -Q1 Q2; unfold kHighMemBeg in *; lia) HGhigh1). rewrite u64_of_lit by exact Hz64.
      clear -Hz A14 A18. unfold kHighMemBeg in *. lia. }

  assert (RMiM : forall a : word, in_ranges rho1 (ss_objs (ax_S (MAIN_of v))) a -> rm rhoM a = ms_mem msv a) by (intros a Ha; rewrite RMM; exact (RMi a Ha)).
  pose proof (sh0_checks v) as (CK0 & CK1 & CK2 & CK3). cbv zeta in CK0, CK1, CK2, CK3.
  assert (LOWZ0 : forall a, 0x800bc000 <= a < 0x800c0c00 -> rm rhoM (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  { intros a Ha. pose proof (handoff_view_zero_range rho1 rhoM (ax_S (MAIN_of v)) tr msv mdv (SLit 0x800bc000) _ Hsm1 RMiM CK0 (a - 0x800bc000) ltac:(clear -Ha; apply In_zseq; rewrite Z2Nat.id by lia; lia)) as X.
    cbn [eval] in X. rewrite u64_of_lit in X by (clear; lia). replace (0x800bc000 + (a - 0x800bc000)) with a in X by (clear; lia). exact (view_rm _ a _ ltac:(clear -Ha; lia) X). }
  assert (LOWZ : forall a, 0x800c0998 <= a < 0x800c09a8 -> rm rhoM (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) by (intros a Ha; apply LOWZ0; clear -Ha; lia).
  assert (PGAZ : forall a, 0x7fffc288 <= a < 0x7fffc298 -> rm rhoM (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  { intros a Ha. pose proof (handoff_view_zero_range rho1 rhoM (ax_S (MAIN_of v)) tr msv mdv (SLit 0x7fffc000) _ Hsm1 RMiM CK3 (a - 0x7fffc000) ltac:(clear -Ha; apply In_zseq; simpl Z.of_nat; lia)) as X.
    cbn [eval] in X. rewrite u64_of_lit in X by (clear; lia). replace (0x7fffc000 + (a - 0x7fffc000)) with a in X by (clear; lia). exact (view_rm _ a _ ltac:(clear -Ha; lia) X). }
  assert (PRES : forall a, (0x7fffc570 <= a < 0x7fffc750 \/ 0x800158a8 <= a < 0x80015ba8) -> rm rhoM (Z_to_bv 64 a) <> None).
  { intros a [Ha|Ha].
    - destruct (handoff_view_present_range rho1 rhoM (ax_S (MAIN_of v)) tr msv mdv (SLit 0x7fffc000) _ Hsm1 RMiM CK1 (a - 0x7fffc000) ltac:(clear -Ha; apply In_zseq; simpl Z.of_nat; lia)) as [b X].
      cbn [eval] in X. rewrite u64_of_lit in X by (clear; lia). replace (0x7fffc000 + (a - 0x7fffc000)) with a in X by (clear; lia). rewrite (view_rm _ a _ ltac:(clear -Ha; lia) X). discriminate.
    - destruct (handoff_view_present_range rho1 rhoM (ax_S (MAIN_of v)) tr msv mdv (SLit 0x80015000) _ Hsm1 RMiM CK2 (a - 0x80015000) ltac:(clear -Ha; apply In_zseq; simpl Z.of_nat; lia)) as [b X].
      cbn [eval] in X. rewrite u64_of_lit in X by (clear; lia). replace (0x80015000 + (a - 0x80015000)) with a in X by (clear; lia). rewrite (view_rm _ a _ ltac:(clear -Ha; lia) X). discriminate. }
  assert (LITM : forall offp b, 0 <= offp < 4096 -> byte_info (ss_objs (ax_S (MAIN_of v))) (SLit PGLIT) offp = BLit b -> rm rhoM (Z_to_bv 64 (PGLIT + offp)) = Some (Z_to_bv 8 b)).
  { intros offp b Hoff Hbi. pose proof (handoff_view rho1 rhoM (ax_S (MAIN_of v)) tr msv mdv (SLit PGLIT) offp Hsm1 RMiM ltac:(rewrite Hbi; discriminate)) as (_ & _ & X).
    rewrite Hbi in X. cbv beta iota in X. change (eval rho1 (SLit PGLIT)) with (Z_to_bv 64 PGLIT) in X. unfold PGLIT in X, Hoff |- *.
    rewrite u64_of_lit in X by (clear; lia). eapply view_rm; [clear -Hoff; lia | exact X]. }

  assert (OUTM : forall z, 0x646000 <= z < 0x7fff00000000 -> outside_all rhoM objs_U (Z_to_bv 64 z)).
  { intros z Hz. apply (objs_far_outside false rhoM objs_U z (proj2 objs_MU_far)); [rewrite V1; exact Nsp | intros X; discriminate X | | exact Hz].
    rewrite V4. clear -Nsp Nstr Nargc; lia. }

  pose proof (floor8_props (shx x)) as (F81 & F82 & F83).
  assert (SHXle : shx x <= Start7.SXE (bv_unsigned sp + RNDo)).
  { unfold shx, Start7.SXE, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib.SHB. rewrite Ex'. clear -A4 Nsp Nrnd Nstr T0 T1 T2 Nargc.
    pose proof (Z.div_le_mono (bv_unsigned sp) (Start7.XEz (bv_unsigned sp + RNDo)) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (SHOK : shadow_ok rhoM S_U).
  { unfold shadow_ok. change (ax_X S_U) with ([(SLit 0x14d40, SLit 0x80); (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.add DrvIfaceT.sp0 (SLit (- (DEEP + 128))), SLit DEEP)]).
    replace (bv_unsigned (eval rhoM (ax_base S_U))) with 0x7fff8000 by (cbn [ax_base S_U eval]; rewrite u64_of_lit; [reflexivity | unfold Code.SHB; lia]).
    pose proof (shadow_ok_X3 rhoM objs_U (bv_unsigned sp) (q12x x) (shx x - shx x mod 8) OUTM V1 N16 ltac:(clear -Hx Ex'; lia)) as SH3.
    eassert (SH3' : _).
    { apply SH3.
      + clear -Q1. lia.
      + unfold q12x. apply (proj1 (proj2 (pagedown_le _))).
      + unfold q12x, shx. rewrite Ex'. clear. lia.
      + unfold shx. rewrite Ex'. reflexivity.
      + exact ZPG.
      + intros z Hz. apply LOWZ0. clear -Hz. lia.
      + intros z Hz. apply ZB. clear -Hz F81 SHXle A12. lia. }
    constructor; [exact (Forall_inv SH3')|]. constructor; [exact (Forall_inv (Forall_inv_tail SH3'))| constructor]. }

  pose proof HsmA1 as (_ & MI1 & _ & _ & HZ1). cbn [snd cfg_model cfg_ms] in MI1, HZ1.
  pose proof (Mmain_fds (M1 tid) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 o b12 b13 b14) as [MF1 MF2]. fold Mm in MF1, MF2.
  split.
  {   split; [| exact HJ1].
    split; [exact SMM|]. split; [exact MI1|]. split; [exact (proj1 S_U_wf)|]. split; [exact SHOK | exact HZ1]. }
  split.
  {   unfold MainJoin.P0U. split; [unfold Uv; exact V24|]. split; [| split; [| split; [| split; [|split]]]].
    - split.
      + split; [exact LOWZ | exact PRES].
      + intros z Hz. unfold SHRZ, Geometry.Sh, Geometry.SHADOW_OFF in Hz. cbn in Hz. destruct Hz as [Hz|Hz]; [apply PGAZ; clear -Hz; lia|]. apply ZPG. unfold ZPAGES, PA0, PR0. clear -Hz. lia.
    - rewrite VL2. exact (L2U_head sp brk mb draw inp Hent Hinp).
    - unfold Uv. exact V5.
    - split.
      + apply (ZARG_of rhoM (bv_unsigned sp) LEN (Start7.XEz (bv_unsigned sp + RNDo)) (Start7.SXE (bv_unsigned sp + RNDo)) (q12x x)
                 (Z.max (Start7.Q18 x) (Start7.Wz (bv_unsigned sp + RNDo))) V1 V11 N16).
        * clear -Nsp. lia.
        * clear -Nlen Nrnd Nstr T0 T1 T2 Nargc. lia.
        * clear -Nfit. lia.
        * clear -A4 Nlen. lia.
        * exact A3.
        * unfold Start7.SXE, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib.SHB. reflexivity.
        * clear -A12. lia.
        * unfold q12x, shx. rewrite Ex'. clear. lia.
        * exact ZB.
      + intros z Hz. unfold SHRZ2, Geometry.Sh, Geometry.SHADOW_OFF in Hz. apply ZPG. unfold ZPAGES, PA0, PR0. clear -Hz. cbn in Hz. lia.
    - rewrite VL3, VL2. reflexivity.
    - unfold SLK0, Uv. rewrite V5, V12. clear -Nlen Nrnd NA1 NA1b T1 T2. lia. }

  split; [unfold Uv; exact V24|]. split; [unfold Uv; exact V1|]. split; [unfold Uv; exact V2|]. split; [unfold Uv; exact V4|]. split; [unfold Uv; exact V5|].
  split; [unfold Uv; exact V12|]. split; [unfold Uv; exact V11|]. split; [unfold Uv; exact V30|].
  split; [intros i Hi; rewrite (V11lo i Hi); apply RW1|].
  split; [exact VL2|]. split; [exact VL3|].

  unfold sheet. cbv zeta. rewrite !virt_unfold. cbn [snd cfg_ms]. fold Mm msv.
  pose proof HMI as MI2. rewrite Flim, Fisp in MI2.
  split; [rewrite MF1; exact Ffds|]. split; [rewrite MF2; exact Ffs|]. split; [exact (mi_lim MI)|].
  split; [exact MI2|]. split; [exact Htid|]. split; [exact Ex'|].
  split; [exact G2|]. split; [exact G3|]. split; [exact HPL|]. split; [exact HPL4|]. split; [exact HPL5|]. split; [exact HPL6|].
  split; [exact HPL7|]. split; [exact HPL8|]. split; [exact HPL9|]. split; [exact HPL10|]. split; [exact Ho|].
  split; [exact HPL12|]. split; [exact HPL13|]. split; [exact HPL14|].
  split; [exact (conj W12b W12t)|]. split; [exact (conj W13b W13t)|]. split; [exact (conj W14b W14t)|].
  split; [exact HJ|]. split; [exact V25|]. split; [exact Lr|]. split; [exact ROK|]. split; [exact RW1|]. split; [exact RL1|].
  split; [exact H27|]. split; [exact H28|]. split; [exact H29|]. split; [exact H30|]. split; [exact H31|].
  split; [exact H32|]. split; [exact H33|]. split; [exact H34|]. split; [exact H36|]. split; [exact H77|]. split; [exact H78|].
  split; [exact H83|]. split; [exact H159|]. split; [exact H160|]. split; [exact H161|].
  split; [reflexivity|].
  split; [exact Hsm1|].
  split; [intros a Ha; rewrite RMM; exact (RMo a Ha)|].
  split; [exact RMiM|].
  split; [exact Z1|]. split; [exact O1|]. split; [exact RM|].
  split; [rewrite <- R6; exact ZX|]. split; [exact BD|].
  rewrite V16. apply RW1.
Qed.
End Main.
