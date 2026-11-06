(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IL SpineMallocSec4I SpineMallocSec4ILW2.

(* [comment removed for export] *)
Module SpineCallocOviW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLeOrPc"; "Wcan"; "AE_A"; "L_calloc_null"; "JL_calloc_null"; "KcA"; "Kc_ok"; "Pre_callocI"; "unwind_stopJ"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "nil"; "prod"; "pair"; "cons"; "option"; "Some"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@Corelib.Init.Logic"; "eq"; "False"; "and"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "cst_ok"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "rw"; "ss_next"; "sv"; "sobj"; "valuation"; "SLit"; "sprop_below"; "swf"; "SVar"; "holds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertCallocOv"; "ov_cuts_pcs"; "stRo_S"; "EXo"; "s_o"; "stKo"; "N_ovn"; "R_o"; "stRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Stdlib.Lists.List"; "In"; "forallb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI"; "Jc"; "rho_ce"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocIo"; "FACTSo"; "P0o"; "sb_o"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocSec2 SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocIo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocIo OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertCallocOv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS1iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineCallocOv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineCallocOvA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Wb_o : ltac2:(tb__ "0|0|
S15SaS2aS5cS1U1A1S0A2A1SbA3"). Proof. MemoFast.vmc. Qed.
Lemma Fb_o : ltac2:(tb__ "0|0|
S15SaS38S22S29S55A1S5aS1U1A1S0A2A3SbA3"). Proof. MemoFast.vmc. Qed.
Lemma RN_o : ltac2:(tb__ "0|0|
S15S9S26A1S33S1U1A1S0A2S12S26S56S42S59S26S58S32A4A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WRn_o : ltac2:(tb__ "0|0|
S15SaS2aS2eS1U1A1S0A2A1SbA3"). Proof. MemoFast.vmc. Qed.
Lemma DKRn_o : ltac2:(tb__ "0|5|
S15S10SdS9SdS25S25A2M0A1M1S9S22A1M2A2M3A1S52S1cS31S1U1A1M4S0A2A1S2eG4S0A2A2S11G3SeG1G2SfG0SeS25S25S28S57A1S2bP18A1A4ScG0A1A3ScS22A1A4A2A3"). Proof. MemoFast.vmc. Qed.
Lemma NXRn_o : ltac2:(tb__ "0|1|
S15S1aS24S2eS1U1A1M0S0A2A1S24S1cS31G0S0A2A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTn_o : ltac2:(tb__ "0|1|
S15SaS1dS34S1U1A1M0S0A2S3S2G0S0A3S30G0S0A2A3SbA3"). Proof. MemoFast.vmc. Qed.
Lemma IDn_o : ltac2:(tb__ "0|0|
S15SaS53S30S1U1A1S0A2S3bA2SbA3"). Proof. MemoFast.vmc. Qed.
Definition CertO_o__runs : ltac2:(tb__ "0|0|
S9S10S9S1eA1A1A1") := ltac2:(tb__ "0|0|
S54S13Ufa0ScS19A1S2dU1S0A2A4").
Lemma CertO_o : ltac2:(tb__ "0|1|
S15SaS3fS13Ufa0ScS19A1S14S2dU1M0S0A2SfS1bS2fS1G0A1S0A2ScS1bA1A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GW (ov_cuts_pcs 1 UStopLeOrPc) [EXo (Wcan 1) UStopLeOrPc] CertO_o__runs); [unfold CertO_o__runs; reflexivity | MemoFast.vmc]. Qed.
Lemma ECertO_o : ltac2:(tb__ "0|3|
S15SaS40S13Ufa0ScS19A1S14S42S1bS3cS1bS3dR1Z1S28Z0M0A1M1A3Lc;S2dU1M2S0A2A4SfS3cS3dS2fS1G2A1S0A2G0G1A3ScS3cA1A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GW (map (fun c => mkVNA c 1 (SLit 0)) (ov_cuts_pcs 1 UStopLeOrPc)) [mkVNA (EXo (Wcan 1) UStopLeOrPc) 0 (SLit 0)] CertO_o__runs); [unfold CertO_o__runs; reflexivity | MemoFast.vmc]. Qed.
Lemma NXcuts_o : ltac2:(tb__ "0|0|
S1bS37S1bR1S2dU1S0A2A3S5dS14S24S1cR2A1A1A2F_;FC;").
Proof. intros C HC. apply Pos.leb_le. unfold ov_cuts_pcs in HC. destruct HC as [<-|[<-|[]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCUT_o : ltac2:(tb__ "0|4|
S41S27S8S1U1M0A1M1S0S4aR2R1A2A3S18S9S22A1M2G2S17S37S1bS3eR1S5bG1S0A2M3A2S2dG0S0A2A3S17S43S22S2cS4aR4R3A2A1R1A3S15SaS38S22S29S24S1cG3A1A1A1R1A3SbA3A2A2Lsx;A2F_;Frho;FA;").
Proof.
  intros A rho HST. unfold unwind_stopJ in HST.
  assert (HWne : (Wcan 1) <> []) by discriminate.
  destruct (Wcan 1) as [|l W'] eqn:EW; [contradiction HWne; reflexivity|]. rewrite <- EW in *.
  destruct (last_link (SVar 28) (Wcan 1)) as [[bp nbp] pc] eqn:EL. destruct HST as [Hp|Hl].
  - exists (stop_pc (Wcan 1)). split; [left; reflexivity|]. split; [apply (stop_pc_holds 1); rewrite EL; exact Hp | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - exists (stop_le (Wcan 1)). split; [right; left; reflexivity|]. split; [apply (stop_le_holds 1); rewrite EL; exact Hl | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
Qed.

Theorem calloc_ov_1 : ltac2:(tb__ "0|4|
S9SdS19S19A2A1M0G0S20R2A1S21R2A1S19S1fR5R1A2S1fS48R2A2S16F_;F_;Fa;S19S1fR6R1A2S1fS4bR2A2S16F_;F_;Fa;S51OF_;S41S5S27S9S3aQ40M1A1A1S9SdS1bS35A2M2A1S6R4A1S46S13R7S45R5A1A3S37G2SeS1bS35S3S2S1U1A1M3S0A3S4S47S13A1ReRdR7R6A5A4R3A3S4cS4eZ2Z40A2S4dS39G1S23R6PcA2A2S39G1S23R6PdA2A2A2A2S50S13RaS44S13S49G3S0R9R8A4S7S2G3S0A3R7R6A5S36S13S3bR7R6R5A5A4F_;F_;F_;F_;FPosts;Ftp;Frho;FKc;FA;Fok;F_;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTM HCSTS.
  exact (calloc_ov 1 UStopLeOrPc CST XGL HCST HXGL HCSTM HCSTS HUS_c Wa_c Da_c Wb_o Fb_o RN_o WRn_o DKRn_o NXRn_o ENTn_o IDn_o (ov_cuts_pcs 1 UStopLeOrPc) HCUT_o CertO_o).
Qed.
Theorem ecalloc_ov_1 : ltac2:(tb__ "0|4|
S9SdS19S19A2A1M0G0S20R2A1S21R2A1S19S1fR5R1A2S1fS48R2A2S16F_;F_;Fa;S19S1fR6R1A2S1fS4bR2A2S16F_;F_;Fa;S41S5S27S9S3aQ40M1A1A1S9SdS1bS35A2M2A1S6R4A1S37G2SeS1bS35S3S2S1U1A1M3S0A3S4S47S13A1RcRbR6R5A5A4R2A3S4cS4eZ2Z40A2S4dS39G1S23R5PcA2A2S39G1S23R5PdA2A2A2A2S4fS13S44S13S49G3S0R8R7A4S7S2G3S0A3R6R5A5S36S13S3bR6R5R4A5A3F_;F_;F_;FPosts;Ftp;Frho;FKc;FA;F_;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTM HCSTS.
  exact (ecalloc_ov 1 UStopLeOrPc CST XGL HCST HXGL HCSTM HCSTS HUS_c Wa_c Da_c Wb_o Fb_o RN_o WRn_o DKRn_o NXRn_o ENTn_o IDn_o (ov_cuts_pcs 1 UStopLeOrPc) HCUT_o NXcuts_o ECertO_o).
Qed.
End SpineCallocOviW1.

(* [comment removed for export] *)
Module SpineMallocSecOK.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "rl"; "sprop"; "SVar"; "reg_sv"; "ss_facts"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_sec"; "DG"; "sec_chunk"; "aa_geom"; "aa_Km"; "aa_fs_busy"; "aa_live"; "ageom"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "None"; "app"; "length"; "option"; "nil"; "true"; "bool"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "ulink"; "UStopLeOrPc"; "mem_keptA"; "ustop"; "AE_A"; "Posts_malloc"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "dlink"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGsC"; "clsP"; "slink"; "JGs"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "with_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "CS1"; "V_MS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4"; "slink4"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "F_fam"; "F_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SecLinks.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section OK.
Variable nW : nat. Variable st : ustop. Variable nx : positive. Variable hi : bool.
Let W : list ulink := Wcan nW.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S14S5cVCST;R1A2S5cS6bR2A2S27F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S14S5cVCST;R1A2S26S44R2A1A1F_;Fa;").
Let JGs : ltac2:(tb__ "0|0|
SbSbF_;SbS31S2S17Q40A1S2eFa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S51VnW;Vst;Vnx;A3").
Let JGsC : ltac2:(tb__ "0|0|
SbSbF_;SbS31S2S17Q40A1S2eFa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S4eVnW;Vst;Vnx;A3").
Let Posts (A : AA) (Kc : KcA) : ltac2:(tb__ "0|0|
S19S1bS5fS58A2A1") := ltac2:(tb__ "0|0|
S38S37S69S0A1VCST;VXGL;VW;Vst;VA;VKc;A8").

Variables (E1 D2 T4a T4b C5a C5b : axst).

Hypothesis HG12 : ltac2:(tb__ "0|5|
S29OF_;SbS31S2S17Q40M0A1M1S19G1A1M2S2aS30VW;Vst;A2S32R6A1S2dS0R9S2cR7A1A3S4fVhi;S16G0R6A2S2fS16G0S3R7PcM3A2A2A1A3S2S2G2S50S16G0RaA2S2fS16G0S3RbG3A2A2A1RbR3A4S28S0RfS2bS0VJGs;SbR1LX;M4ReRdR4RbA5VD2;R3R2A5R9A4F_;FtpY;FrhoY;Frho';S2S28S0RdS2bS0VJGsC;G4RcRbRaR9A5VE1;R1R8A5R7A4FrhoX;F_;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Hypothesis HG3 : ltac2:(tb__ "0|7|
S29OF_;SbS31S2S17Q40M0A1M1S2aS30VW;Vst;A2S32R5A1S2dS0R8S2cR6A1A3S4bS0R9S2cR7A1A3S3eS3dS40S1eSeScR9A1A2A1Z1A2S41Z2Z14A2A2S14S25S3cS4dS16G0R8A2A1M2R1A2S3eR1S3dG2S3fS2fS16G0S3R9PcM3A2A2A1Z8A2A2A2A2S26S24S1fS17Q8A1M4A1S4RaS18G0R2A2A2S1cG4A1A3A1F_;Fz;S2S2S19G1A1M5S60SfReA1S16G0RbA2S2fS16G0S3RcG3A2A2A1RcR3A5S28S0R10S2bS0VJGs;SbS5dR1A1LX;RfReR4RcA5VT4a;R3R2A5RbA4F_;FtY;FrY;Frho'';S2G5S28S0RfS2bS0VJGs;SbR1LX;M6ReRdRcRbA5VT4b;R2R1A5RaA4FtY;FrY;S2G5S28S0R10S2bS0VJGs;G6RfReRdRcA5VD2;R2R1A5RbA4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Hypothesis HG41a : ltac2:(tb__ "0|5|
S29OF_;SbS31S2S17Q40M0A1M1S2aS24S36Vst;S34A3S24S19S33A1VW;S20S33A1A3F_;S30VW;Vst;A2S32R6A1S2dS0R9S2cR7A1A3S4bS0RaS2cR8A1A3SdS2S2S19G1A1M2S1bS14S14A2M3S45G3R1S43R5A1A3S42R2S1aS14S14S16G0RdA2S2fS16G0S3RePcA2A2A1A4A2F_;Fbn;S48R5RdR4A3S28S0R11S2bS0VJGs;S47SbS5dR1A1LX;M4R6A2R10RfR5RdA5VC5a;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S28S0ReS2bS0VJGs;G4RdRcRbRaA5VT4a;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Hypothesis HG41b : ltac2:(tb__ "0|5|
S29OF_;SbS31S2S17Q40M0A1M1S2aS24S36Vst;S34A3S24S19S33A1VW;S20S33A1A3F_;S30VW;Vst;A2S32R6A1S2dS0R9S2cR7A1A3S4bS0RaS2cR8A1A3SdS2S2S19G1A1M2S1bS14S14A2M3S45G3R1S43R5A1A3S42R2S1aS14S14S16G0RdA2S2fS16G0S3RePcA2A2A1A4A2F_;Fbn;S48R5RdR4A3S28S0R11S2bS0VJGs;S47SbR1LX;M4R6A2R10RfR5RdA5VC5b;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S28S0ReS2bS0VJGs;G4RdRcRbRaA5VT4b;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Hypothesis HTLa : ltac2:(tb__ "0|8|
S29OF_;SbS31S2S2S17Q40M0A1M1S19G1A1M2SdS30VW;Vst;A2S32R7A1S2dS0RaS2cR8A1A3S15S24G1S3R8R1A2S3R9R1A2A3Fi;S15S24S19S17Q8A1M3A1S5R9R1A2S5RaR1A2A3Fl;S35VCST;VXGL;RcRcS4RaA1S4R9A1A6S3cS40S1eSeScRdA1A2A1S10RdA1A2S1bS14S14A2M4S45G4R1S43R9A1A3S42R2S1aS14S14S16G0RcA2M5S2fS16G0S3RdPcA2A2A1M6A4A2F_;Fbn;S14S25S3cS4dG5A1M7R1A2S3eR1S3dG7S3fG6Z8A2A2A2A2S26S24S1fG3A1S4ReS18G0R2A2A2S1cG3A1A3A1F_;Fz;S2G2S28S0R13S2bS0VJGs;S47SbS5dR1A1LX;RcA2R12R11RfReA5VC5a;R2R1A5S57S0S56R10RdVPosts;R12R11A2A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Hypothesis HTLb : ltac2:(tb__ "0|8|
S29OF_;SbS31S2S2S17Q40M0A1M1S19G1A1M2SdS30VW;Vst;A2S32R7A1S2dS0RaS2cR8A1A3S15S24G1S3R8R1A2S3R9R1A2A3Fi;S15S24S19S17Q8A1M3A1S5R9R1A2S5RaR1A2A3Fl;S35VCST;VXGL;RcRcS4RaA1S4R9A1A6S3cS40S1eSeScRdA1A2A1S10RdA1A2S1bS14S14A2M4S45G4R1S43R9A1A3S42R2S1aS14S14S16G0RcA2M5S2fS16G0S3RdPcA2A2A1M6A4A2F_;Fbn;S14S25S3cS4dG5A1M7R1A2S3eR1S3dG7S3fG6Z8A2A2A2A2S26S24S1fG3A1S4ReS18G0R2A2A2S1cG3A1A3A1F_;Fz;S2G2S28S0R13S2bS0VJGs;S47SbR1LX;RcA2R12R11RfReA5VC5b;R2R1A5S57S0S56R10RdVPosts;R12R11A2A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").

Lemma c5_pure : ltac2:(tb__ "0|7|
SbSbF_;SdSbS31S2S2S2S2S17Q40M0A1M1S2S19G1A1S19S53A1S52SbS24S13SfReR1A1A1SfR1A1A3FX;SbS24S19SeA1ScRfR1A1A1ScR1A1A3FX;SbS24S19S1bS14S14A2M2A1M3S12R10R1A1A1S12R1A1A3FX;SbS24S19G3A1S11R11R1A1A1S11R1A1A3FX;S16G0R9A2S14S2fS16G0S3RePcM4A2A2A1S14S50R2R1RfReA4S60SfR12A1R3R2RfReA5S48R14RfReA3G2S45G2R1S43R16A1A3S42R2S1aS14S14R7R6A4A2F_;Fbn;VJGs;S47R17R16A2R15R14R10RfReRdRcRbA9S25S35VCST;VXGL;R16R16S4R14A1S4R11A1A6S25S14S25S3cS4dR8A1M5R1A2S3eR1S3dG5S3fS2fS16G0S3R12G4A2A2A1Z8A2A2A2A2S26S24S1fS17Q8A1M6A1S4R13S18G0R2A2A2S1cG6A1A3A1F_;Fz;S25S15S24G1S3R12R1A2S3R15R1A2A3Fi;S25S15S24S19G6A1S5R12R1A2S5R15R1A2A3Fl;G2S45G2R1S43R18A1A3S42R2S1aS14S14R9S2fS16G0S3R13G4A2A2A1A4A2F_;Fbn;A2A2A2A2F_;F_;F_;F_;F_;TL;Tua;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho3;Frho2;Frho1;Frho;FKc;FA;FG2;FBX;").
Proof.
  intros BX G2 A Kc rho rho1 rho2 rho3 a r tp tr md BXg BXs BXl BXf ua L SL1 SL4 DL HDB HJ.
  assert (E12 : rw rho3 12%positive = rw rho 12%positive).
  { destruct SL1 as (W1 & _). destruct SL4 as (W2 & _). destruct DL as (W3 & _). rewrite W3, W2. apply W1. }
  unfold JGs, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.JGs in HJ. rewrite E12 in HJ. fold L in HJ. cbn zeta in HJ.
  destruct HJ as (_ & _ & HA & HPD & _ & _ & _ & Hnv & _).
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  set (As := AXK BX G2 (bumpV A nv)) in *.
  assert (Eg : aa_geom As = aa_geom A) by (unfold As, AXK; cbn [aa_geom bumpK with_depot]; rewrite BXg; reflexivity).
  assert (Es : aa_sec As = aa_sec A) by (unfold As, AXK; cbn [aa_sec bumpK with_depot]; rewrite BXs; reflexivity).
  assert (El : aa_live As = aa_live A) by (unfold As, AXK; cbn [aa_live bumpK with_depot]; rewrite BXl; reflexivity).
  assert (Ef : aa_fs_busy As = aa_fs_busy A) by (unfold As, AXK; cbn [aa_fs_busy bumpK with_depot]; rewrite BXf; reflexivity).
  assert (Ed : aa_depot As = G2) by reflexivity.
  assert (HPDs : pendS As ua L md).
  { destruct HPD as (PM & PAL & PL0 & PDI & ST & SC & SD & SF & SS & SP & SX & SDB).
    unfold pendS. rewrite Eg, Es, Ed. repeat (split; [assumption|]). exact HDB. }
  rewrite <- Eg in SL4. rewrite <- Ed in DL.
  destruct (links_kept CST XGL HCST HXGL HCSTS HCSTD As r tp md nv ua rho rho1 rho2 rho3 HA Hnv HPDs SL1 SL4 DL) as (HK & RD & HW & HL).
  rewrite E12. fold nv L.
  split; [|split; [exact RD|split; [exact HW|split; [exact HL|exact HDB]]]].
  -
    assert (CA : forall x, client_addrA CST As x <-> client_addrA CST A x).
    { intros x. unfold client_addrA, client_mut_addrA, aa_frames. rewrite Eg, El, Ef. reflexivity. }
    assert (CS : forall x, client_shadowA CST XGL As x <-> client_shadowA CST XGL A x).
    { intros x. unfold client_shadowA. split; (intros [(y & Hy & E)|H]; [left; exists y; split; [apply CA; exact Hy | exact E] | right; exact H]). }
    destruct HK as [K1 K2]. split.
    + intros x Bx Hx. apply K1; [exact Bx|]. destruct Hx as [(C1 & C2 & NE)|(C1 & C2 & Hd)]; [left | right]; (split; [|split]); try assumption; first [apply CA | apply CS]; assumption.
    + intros x j Hx Hj Hd. apply (K2 x j); [|exact Hj|exact Hd]. destruct Hx as [[C1 C2]|GX]; [left; split; apply CA; assumption | right; exact GX].
Qed.

Lemma d2_pure : ltac2:(tb__ "0|2|
SbS31S2S17Q40A1M0S2S19G0A1S19S53A1S52VJGs;SbR1LX;R8R7R6R5R4R3R2R1A9S25S3eS3dS40S1eSeScR9A1A2A1M1Z1A2S41Z2Z14A2A2S3cG1S10R9A1A2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ. unfold JGs, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.JGs in HJ. cbn zeta in HJ.
  destruct HJ as (_ & _ & HA & _ & _ & _ & _ & _ & _ & HBO).
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  split.
  - pose proof (AInvA_sec_bound segsA _ r tp md HA) as SB. cbn [aa_sec bumpV] in SB.
    assert (E : large_live (bumpV A nv) = large_live A) by reflexivity. rewrite E in SB.
    pose proof (budget_ok_alloc_room A nv HBO) as RM. unfold sec_room, SEC_SLACK in RM. clear -SB RM. lia.
  - destruct HA as (_ & _ & _ & _ & HM & _). destruct HM as (_ & _ & _ & _ & _ & _ & _ & HLd).
    destruct HLd as (_ & _ & _ & _ & _ & _ & _ & _ & L9 & _). cbn [aa_sec aa_Km bumpV] in L9. exact L9.
Qed.

Theorem sec_ok_chain : ltac2:(tb__ "0|2|
S29OF_;SbS31S2S17Q40M0A1M1S19G1A1S24S36Vst;S34A3S24S19S33A1VW;S20S33A1A3F_;S30VW;Vst;A2S32R6A1S2dS0R9S2cR7A1A3S4bS0RaS2cR8A1A3S4fVhi;S16G0R7A2S2fS16G0S3R8PcA2A2A1A3S2S28S0RdS2bS0VJGsC;SbR1LX;RcRbRaR9A5VE1;R1R8A5S57S0S56RaR8VPosts;RcRbA2A5A4FrhoX;F_;F_;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HW HUS HKc Hokl Hokpl HC rhoX.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *.
  apply (HG12 ok A Kc rho a tp _ HUS HKc Hokl HC). intros rho1 rhoY tpY SL1.
  apply (triple_pre_pure segsA ok _ _ (Z.of_nat (length (aa_sec A)) + 1 < 2 ^ 20 /\ Z.of_nat (length (aa_sec A)) <= aa_Km A)).
  { intros [tr [ms md]] Hw. exact (d2_pure A Kc rho1 a rhoY tpY tr md (proj2 Hw)). }
  intros [HRM HL9].
  assert (E1r : rw rho1 12%positive = rw rho 12%positive) by (destruct SL1 as (W1 & _); apply W1).
  assert (RD1 : forall z, Sh ua <= z < Sh ua + L / 8 -> rm rho1 (Z_to_bv 64 z) <> None) by (destruct SL1 as (_ & _ & _ & D1); exact D1).
  apply (HG3 ok A Kc rho1 a _ HUS HKc Hokl Hokpl HRM); [rewrite E1r; exact RD1 | |].
  -
    rewrite E1r. fold ua L. intros rho2 rY tY SL4.
    assert (E2r : rw rho2 12%positive = rw rho 12%positive) by (destruct SL4 as (W2 & _); rewrite W2; exact E1r).
    apply (HG41a ok A Kc rho2 a _ HW HUS HKc Hokl Hokpl). rewrite E2r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (triple_pre_pure segsA ok _ _ _ (fun w Hw => c5_pure (fun X : AA => bumpP X) G2 A Kc rho rho1 rho2 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 SL4 DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (HTLa ok A Kc rho rho3 a tp G2 HUS HKc Hokl HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
  -
    intros rY tY.
    apply (HG41b ok A Kc rho1 a _ HW HUS HKc Hokl Hokpl). rewrite E1r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (triple_pre_pure segsA ok _ _ _ (fun w Hw => c5_pure (fun X : AA => X) G2 A Kc rho rho1 rho1 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 (slink4_refl (aa_geom A) ua L rho1 RD1) DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (HTLb ok A Kc rho rho3 a tp G2 HUS HKc Hokl HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
Qed.
End OK.

Section GRANT.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S24S15S5bVW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S24S22S6cS1Vnx;A2S21A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S24SaS8S5eS59VW;Vst;Vtmax;A3A1ZbA2S7S5aA1A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S46S6S1dS6S1dS6S1dS6S1dS6S3bVW;Vst;A2S3aS39A1A3S66A3S68A3S67Vtmax;Z8A2A3S9S5eS59VW;Vst;Vtmax;A3A1A1A3").

Lemma grant_Jo : ltac2:(tb__ "0|3|
SbS31S2S2S19S17Q40A1M0A1S19S53A1M1S4aS52G0S30VW;Vst;A2S32R9A1S4cS0R8R7S59VW;Vst;Vtmax;A3S1aG1S61R6S62R5R4A2A4A5S6aVW;Vst;RcRbRaR9R8R7R5A9S63S49R7U0A2S49R7U3A2R6S49R7U1M2A2R5A5S4eVnW;Vst;Vnx;SbR1LX;ReRdRcR6S65RbVnx;R6A3RaR9S55S64S54R7A1S49R8G2A2R6A3R7A2AcF_;F_;F_;F_;F_;Fa;Fmd;Fms;Ftr;Ftp;FrhoX;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoX tp tr ms md a HUS HKc Hsp HJG Hpl.
  set (nv := bv_unsigned (rw rho 12%positive)).
  pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md HJG) as (E12 & _ & E142 & _).
  assert (Hnv : 64513 <= nv < 2 ^ 39).
  { pose proof (proj1 (Forall_forall _ _) (smatch_pendingA_facts segsA rhoX tp _ _ Hsp) (SPUle (SLit (rzf_lo 8)) (SVar 12))
                  ltac:(apply FC1; apply in_or_app; right; unfold F_fam; cbn [In]; left; reflexivity)) as F.
    destruct HJG as [_ HJ]. destruct HJ as (_ & _ & _ & _ & _ & HN & _). cbn [eval] in HN. rewrite E12 in HN.
    cbn [holds eval rzf_lo] in F. rewrite E12, u64_lit in F by lia. fold nv in F, HN. clear -F HN. lia. }
  pose proof (round_up_ge' nv 8 ltac:(lia)) as RU1. pose proof (round_up_ge' (secneeded nv) PG ltac:(unfold PG; lia)) as RU2.
  pose proof (round_up_mod (secneeded nv) PG ltac:(unfold PG; lia)) as RM2. unfold PG in RU2, RM2.
  assert (NS : secneeded nv = round_up nv 8 + 4096) by reflexivity.
  assert (MS : secmapsize nv = round_up (secneeded nv) 4096 + 4096) by reflexivity.
  assert (BMS : nv + 8192 <= secmapsize nv <= nv + 12294 /\ secmapsize nv mod 4096 = 0).
  { rewrite MS. split; [lia|]. rewrite Z.add_mod, RM2 by lia. reflexivity. }
  pose proof (mmap_len_sym segsA rhoX tp (CS1 W st tmax) tr ms md (SVar V_MS) (secmapsize nv) Hsp R11
                ltac:(cbn [eval]; unfold V_MS; rewrite E142; apply u64_lit; lia) (proj2 BMS) ltac:(lia)) as [_ HnZ].
  apply (JGsC_of_Sec nW st tmax nx Hnx (fun X : AA => X) A Kc rho a _ tp tr _ (fun X => eq_refl)). pose proof Hnx as Hnx'. unfold W in Hnx'.
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv.JGsC, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv.JGs. rewrite Hnx'.
  assert (NXG' : Pos.leb GW (nxS W st tmax) = true) by (rewrite Hnx; exact NXG).
  pose proof (JGsC_grant W st tmax A Kc rho rhoX tp tr md a (ms_gpr ms 1) (ms_gpr ms 0) (ms_gpr ms 3) HUS HKc HJG
                (smatch_pendingA_MI segsA rhoX tp _ tr ms md Hsp) Hnv HnZ Hpl NXG') as H.
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv.JGsC, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv.JGs in H. rewrite Hnx in H. exact H.
Qed.

Lemma cls_split : ltac2:(tb__ "0|5|
S29OF_;SbS31S2S17Q40M0A1M1S5fS2S19G1A1S2aS4fS21S16G0R5A2S2fS16G0S3R6PcM2A2A2A1A3S28S0RaS2bS0S4eVnW;Vst;Vnx;SbR1LX;M3R9R8R7R6A8R5R4R3A5R2A4F_;S4fS23S16G0R6A2S2fS16G0S3R7G2A2A2A1A3S28S0RbS2bS0S4eVnW;Vst;Vnx;G3RaR9R8R7A8R6R5R4A5R3A4M4F_;G4F_;F_;FQ;Ftp;FrhoX;FE;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a E rhoX tp Q HH HL.
  apply (triple_pre_pure segsA ok _ _ (clsP true (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive)))
                                       \/ clsP false (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))))).
  - intros [tr [ms md]] Hw. pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
    destruct HJ as [HJ _]. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.JGs in HJ. cbn zeta in HJ. destruct HJ as (_ & _ & _ & HPD & _).
    destruct HPD as (_ & _ & _ & PDI & _). destruct PDI as (_ & _ & _ & _ & PDB).
    unfold clsP. destruct PDB as [X|X]; [right; exact X | left; exact X].
  - intros [X|X]; [exact (HH X) | exact (HL X)].
Qed.
End GRANT.
End SpineMallocSecOK.

(* [comment removed for export] *)
Module SpineMallocSec6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "nil"; "prod"; "option"; "pair"; "Some"; "app"; "None"; "nat"; "fst"; "snd"; "S"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ageom"; "aa_ptr_committed"; "aa_sec"; "sec_chunk"; "ag_pab"; "DG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "sprop"; "ss_next"; "ss_facts"; "eval"; "rw"; "holds"; "obj_range"; "sprop_below"; "swf"; "SLit"; "SVar"; "rm"; "ss_objs"; "DUnknown"; "SPBranch"; "SPNot"; "cell"; "mkObj"; "ranges_disjoint"; "sstate"; "SAlu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "entailsA"; "mkLeafA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "ulink"; "UStopLeOrPc"; "ustop"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "LQA"; "jpredA"; "stableA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "div"; "sub"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "kPtrArrayCommit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "secneeded"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST"; "O_1"; "O_2"; "carveS"; "BR"; "Pret_ms"; "O_blk"; "O_w"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "MSENT"; "M48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "range_noband"; "SKEL0"; "JGs"; "noband"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV"; "L3"; "O_3"; "B3"; "B4"; "F_A"; "F_B"; "F_par"; "O_3b"; "a2e8"; "perm7"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "a0e7"; "a2e6"; "a2e7"; "osplit"; "END8"; "O_4z"; "PGST"; "UE9"; "fx8"; "sel7"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_NCH"; "V_NRES"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "Posts_mszA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Placement StartLib StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require EnsureMapA DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.EnsureMapA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SEC6.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S3cS9fVW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S5S7dSb3Vnx;A2S6A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
S7bVnW;Vst;Vnx;VBX;A4").

Lemma run_band : ltac2:(tb__ "0|3|
S14S14F_;S14S40S1dS3eQ40M0A1M1S1dS4G1A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S3bS1S52S61S3dG0R7A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R8PcA2A2A1Z8A2A2A2A2S1S52S63R2A2S53R2S62A2A2F_;Fz;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ z Hz.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _). cbn zeta in *.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *. unfold IMG_HI in IMG.
  pose proof (Sh_in_band ua ltac:(clear -IMG HTOP SMB; lia)) as B1. pose proof (Sh_in_band (ua + L) ltac:(clear -IMG HTOP SMB; lia)) as B2.
  assert (DS : Sh ua + L / 8 <= Sh (ua + L)).
  { unfold Sh. assert (ua / 8 + L / 8 <= (ua + L) / 8); [|lia]. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le ua 8). pose proof (Z.mul_div_le L 8). lia. }
  clear -Hz B1 B2 DS. lia.
Qed.

Lemma ex1_band : ltac2:(tb__ "0|2|
S14S14F_;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S3bVJG;RaR9R8R7R6R5R4R3R2A9S1S52S10S3bS3bS25R6S6eVnx;A1A2M1A3R2A2S53R2S11S3bS3bG1A3A2A2S1S52S63R3A2S53R3S62A2A2F_;F_;Fz;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md z HJ Hz.
  pose proof (site1_bounds nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (EB & _ & LE).
  unfold O_1, L1 in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz. rewrite EB in Hz.
  apply (run_band BX A Kc rho a r tp tr md HJ z). clear -Hz LE. lia.
Qed.

Lemma ex2_band : ltac2:(tb__ "0|2|
S14S14F_;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S3bVJG;RaR9R8R7R6R5R4R3R2A9S1S52S10S3bS3bS25R6S6fVnx;A1A2M1A3R2A2S53R2S11S3bS3bG1A3A2A2S1S52S63R3A2S53R3S62A2A2F_;F_;Fz;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md z HJ Hz.
  pose proof (site2_vals nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & EB & _ & EL & LR). cbn zeta in EB, EL, LR.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & _ & _ & ENS & _). cbn zeta in HN, SMB, ENS.
  unfold O_2, obj_range, obj_lo_of, obj_hi_of in Hz. cbn [ob_base ob_lo ob_hi fst snd] in Hz.
  rewrite soff_lit_small in Hz by lia. rewrite (soff_of_val r L2 _ EL) in Hz by (clear -LR; lia). rewrite EB in Hz.
  apply (run_band BX A Kc rho a r tp tr md HJ z).
  assert (0 <= secneeded (bv_unsigned (rw rho 12%positive)) / 8) by (apply Z.div_pos; [rewrite ENS; pose proof (round_up_ge' (bv_unsigned (rw rho 12%positive)) 8 ltac:(lia)); lia | lia]).
  clear -Hz LR H. lia.
Qed.

Lemma exblk_pab : ltac2:(tb__ "0|3|
S14S14Fx;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S3bS14S0S16S15RbR1A1A1S15R1A1A3FX;S14S0S4S19A1S18RcR1A1A1S18R1A1A3FX;S14S0S3bS17RdR1A1A1S51S17R1A1S65A2A3FX;VJG;RdRcRbRaR9R8R7R6R5A9S24R9S2dS9bS29S9dA1S29S9eA1A3A2S1S52S10S3bS3bS25RaS73A2M1A3R6A2S53R6S11S3bS3bG1A3A2A2S1S52S1aS15RfA1A1M2R7A2S53R7S51G2S64A2A2A2F_;F_;F_;F_;F_;F_;Fz;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md z BXg BXs BXp HJ HBR Hz.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & _ & _ & _ & _ & E145 & E146 & E147 & _).
  destruct HJ as (_ & _ & HA & _). pose proof (AInvA_pab _ _ _ _ HA) as X. rewrite BXg, BXs, BXp in X. cbn [aa_geom aa_sec aa_ptr_committed bumpV] in X. cbn zeta in X.
  destruct X as (P1 & P2 & P3 & P4 & P5 & P6 & _).
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *.
  pose proof (topG_range G) as TG. pose proof (Zle_0_nat (length (aa_sec A))) as NN.
  unfold kPtrArrayReserve, kPtrArrayCommit, PG, IMG_HI in *.
  assert (C17 : c mod 2 ^ 17 = 0).
  { pose proof (Z.mod_add c 1 (2 ^ 17) ltac:(lia)) as MA. rewrite <- MA. rewrite <- P6. f_equal. }
  pose proof (Z.div_mod c (2 ^ 17) ltac:(lia)) as X. rewrite C17, Z.add_0_r in X.
  pose proof (Z.div_mod c 8 ltac:(lia)) as X8.
  assert (C8 : c mod 8 = 0) by (rewrite X; replace (2 ^ 17 * (c / 2 ^ 17)) with ((2 ^ 14 * (c / 2 ^ 17)) * 8) by lia; apply Z_mod_mult).
  rewrite C8, Z.add_0_r in X8.
  cbn [holds eval] in HBR. rewrite E147, E146 in HBR. fold c in HBR.
  assert (C0 : 0 <= c).
  { destruct (Z_lt_le_dec c 0) as [Hneg|]; [exfalso | assumption].
    assert (Ec : c = - 2 ^ 17) by (clear -X Hneg P5 NN; lia).
    assert (En : Z.of_nat (length (aa_sec A)) = 0) by (clear -Ec P5 NN; lia).
    rewrite En, Ec in HBR. vm_compute in HBR. discriminate HBR. }
  pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_le_mono c (2 ^ 23) 8 ltac:(clear -P5; lia) ltac:(clear -P5; lia)) as DM. cbn in DM.
  rewrite bt_eq_lit in HBR by (clear -DP DM NN P5; lia). apply Z.eqb_eq in HBR.
  assert (HcN : 8 * Z.of_nat (length (aa_sec A)) = c) by (rewrite HBR; clear -X8; lia).
  assert (R64 : 0 <= ag_pab G + Z.of_nat (length (aa_sec A)) * 8 < 2 ^ 64) by (clear -P1 P2 TG HcN P5 NN; lia).
  assert (EBw : bv_unsigned (eval r Bw) = ag_pab G + c).
  { unfold Bw. cbn [eval]. rewrite E145, E147, add_val, sll_val. fold G. rewrite !u64_lit by (clear -P1 P2 TG NN HcN P5; lia).
    change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (Z.mod_small (Z.of_nat (length (aa_sec A)) * 8)) by (clear -NN HcN P5; lia). rewrite (Z.mod_small _ _ R64). clear -HcN. lia. }
  unfold O_blk in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz. rewrite EBw in Hz. clear -Hz P5 C0. lia.
Qed.

Lemma exw_pab : ltac2:(tb__ "0|3|
S14S14Fx;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S3bS14S0S16S15RbR1A1A1S15R1A1A3FX;S14S0S4S19A1S18RcR1A1A1S18R1A1A3FX;S14S0S3bS17RdR1A1A1S17R1A1A3FX;VJG;RdRcRbRaR9R8R7R6R5A9S24R9S2eS2dS9bS29S9dA1S29S9eA1A3A1A2S1S52S10S3bS3bS25RaS74A2M1A3R6A2S53R6S11S3bS3bG1A3A2A2S1S52S1aS15RfA1A1M2R7A2S53R7S51G2S64A2A2A2F_;F_;F_;F_;F_;F_;Fz;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md z BXg BXs BXp HJ HBR Hz.
  pose proof (site_b nW st tmax nx Hnx Pret_ms Pret_ms Pret_ms Pret_ms eq_refl eq_refl BX A Kc rho a r tp tr md BXg BXs BXp HJ HBR) as (EBw & B1 & B2 & B3 & _). cbn zeta in EBw, B1, B2, B3.
  unfold O_w in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz. rewrite EBw in Hz. clear -Hz B1 B2 B3. lia.
Qed.

Lemma pab_noband : ltac2:(tb__ "0|2|
S14S14Fx;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S14S0S16S15RaR1A1A1S15R1A1A3FX;VJG;RaR9R8R7R6R5R4R3R2A9S3bS1S52S1aS15RbA1A1M1R1A2S53R1S51G1S64A2A2A2S7cR2A1F_;Fz;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg HJ z Hz. destruct HJ as (_ & _ & HA & _).
  pose proof (AInvA_pab _ _ _ _ HA) as X. rewrite BXg in X. cbn [aa_geom bumpV] in X. cbn zeta in X. destruct X as (_ & _ & _ & P4 & _).
  unfold noband. clear -P4 Hz. lia.
Qed.
Lemma pxa_noband : ltac2:(tb__ "0|2|
S14S14Fx;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S14S0S16S15RaR1A1A1S15R1A1A3FX;S14S0S4S19A1S18RbR1A1A1S18R1A1A3FX;S14S0S3bS17RcR1A1A1S51S17R1A1S65A2A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S4fS1fS24R8A1S7S1fS2dS9bS29S9dA1S29S9eA1A3S8S1fA1A3A3S4S1cA1S0S4S9S9S1eS1eA2S1eA2M1A1S4eS1cG1S57R1A4S4eS1cG1S57S7S1cS73S8S1cA1A3A4A3S4fS1cS1cS79S25RcR1A2A1Lo;R2A3F_;Fl;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HF l EE. apply Forall_inv in HF.
  destruct l as [|o [|o' l']]; try (cbn in EE; discriminate EE). assert (Es : skel o = skel O_blk) by (cbn in EE; congruence).
  apply Forall_cons; [|apply Forall_nil]. rewrite (obj_range_skel r o O_blk Es). intros z Hz.
  exact (pab_noband BX A Kc rho a r tp tr md BXg HJ z (exblk_pab BX A Kc rho a r tp tr md z BXg BXs BXp HJ HF Hz)).
Qed.
Lemma pxb_noband : ltac2:(tb__ "0|2|
S14S14Fx;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S14S0S16S15RaR1A1A1S15R1A1A3FX;S14S0S4S19A1S18RbR1A1A1S18R1A1A3FX;S14S0S3bS17RcR1A1A1S17R1A1A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S4fS1fS24R8A1S7S1fS2eS2dS9bS29S9dA1S29S9eA1A3A1S8S1fA1A3A3S4S1cA1S0S4S9S9S1eS1eA2S1eA2M1A1S4eS1cG1S57R1A4S4eS1cG1S57S7S1cS74S8S1cA1A3A4A3S4fS1cS1cS79S25RcR1A2A1Lo;R2A3F_;Fl;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HF l EE. apply Forall_inv in HF.
  destruct l as [|o [|o' l']]; try (cbn in EE; discriminate EE). assert (Es : skel o = skel O_w) by (cbn in EE; congruence).
  apply Forall_cons; [|apply Forall_nil]. rewrite (obj_range_skel r o O_w Es). intros z Hz.
  exact (pab_noband BX A Kc rho a r tp tr md BXg HJ z (exw_pab BX A Kc rho a r tp tr md z BXg BXs BXp HJ HF Hz)).
Qed.

Section G41.
Variable BX : AA -> AA.
Variables (T4 U4 X5 C5 : axst).
Hypothesis WU4 : ltac2:(tb__ "0|0|
S0S5S27S34VU4;A1A1S6A3").
Hypothesis DU4 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VT4;A1S34VU4;A1A2ScG3SbG1G2S8G0A1Sb2Vnx;A1A4A2A3").
Hypothesis NXU4 : ltac2:(tb__ "0|0|
S0S3cS20S34VU4;A1A1S20S34VT4;A1A1A3").
Hypothesis HU4 : ltac2:(tb__ "0|0|
S0S35S37VT4;S34VU4;A1A2VU4;A3").
Hypothesis Cert5 : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bSb1S8S3bA1A3VGS;S7S35VU4;S8S35A1M0A3S7S35VX5;G0A3A6S6A3").

Hypothesis HDS : ltac2:(tb__ "0|4|
S5bOF_;S14S40S1dS3eQ40M0A1M1S5cS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3Sa5Vsegs;RaS49R8A1A3S1bS1dS1dS4G1A1M2S9S3bS3bA2M3S5fG3R1SacR5A1A3SabR2SbS3bS3bS3dG0RdA2S66S3dG0S23RePcA2A2A1A4A2F_;Fbn;SaaR5RdR4A3S5aVsegs;R11S48Vsegs;VJG;Sa9VBX;R6A2R10RfR5RdA5VC5;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S1dG2S5aVsegs;ReS48Vsegs;VJG;VBX;RdRcRbRaA5VX5;R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").

Theorem sec_g41 : ltac2:(tb__ "0|4|
S5bOF_;S14S40S1dS3eQ40M0A1M1S5cS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3Sa5Vsegs;RaS49R8A1A3S1bS1dS1dS4G1A1M2S9S3bS3bA2M3S5fG3R1SacR5A1A3SabR2SbS3bS3bS3dG0RdA2S66S3dG0S23RePcA2A2A1A4A2F_;Fbn;SaaR5RdR4A3S5aVsegs;R11S48Vsegs;VJG;Sa9VBX;R6A2R10RfR5RdA5VC5;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S1dG2S5aVsegs;ReS48Vsegs;VJG;VBX;RdRcRbRaA5VT4;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl Hokpl Hcont rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  eapply triple_conseq; [intros w Hw; exact (RSU4 nW st tmax nx Hnx T4 U4 WU4 DU4 NXU4 HU4 BX A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [DPENT] GS [U4] [X5] (JG BX A Kc rho a) ok Q tX Hokf HST Cert5); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  exact (HDS ok A Kc rho a Q HW HUS HKc Hokl Hokpl Hcont rE tX).
Qed.
End G41.

Lemma diamond_hold : ltac2:(tb__ "0|2|
S14S14Fx;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58S14S0S16S15RaR1A1A1S15R1A1A3FX;VJG;RaR9R8R7R6R5R4R3R2A9S3S4fS1fS24R6A1M1S86Vnx;A1A3S4fS1fG1S87Vnx;A1A3A2F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & Enx & _ & E142 & _ & _ & E155 & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _). cbn zeta in *.
  destruct HJ as (_ & _ & HA & HP & _). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & SSP & _).
  pose proof (proj1 HA) as HG. rewrite BXg in HG. cbn [aa_geom bumpV] in HG.
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  unfold sepZ in SSP. cbn [fst snd] in SSP. rewrite kSpaceSize_val in SSP.
  pose proof (urange a) as Ra. unfold IMG_HI in IMG.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *. set (SB := ag_spacebeg (aa_geom A)) in *.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (RSB : 0 <= SB < 2 ^ 64) by (clear -S1 S2 TG; lia).
  assert (RL : 0 <= L < 2 ^ 64) by (clear -SMB HN; lia).
  destruct SSP as [SA|SB'].
  - left. unfold F_A. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite Enx, E142, E155, add_val. fold ua L SB.
    rewrite (u64_lit L RL), (u64_lit SB RSB). rewrite Z.mod_small by (clear -IMG HTOP SMB; lia). exact SA.
  - right. unfold F_B. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite Enx, E155, add_val. fold ua SB.
    rewrite (u64_lit SB RSB). rewrite u64_lit by lia. rewrite Z.mod_small by (clear -S1 S2 TG; lia). clear -SB'. lia.
Qed.

Lemma site3_vals : ltac2:(tb__ "0|3|
S14S14F_;S14S40S1dS3eQ40M0A1M1S1dS4G1A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S1S0S3bS3dG0S22R5S84Vnx;A1A2A2S51S61S3dG0R6A2A1Z200A2A3S1S0G1S22R5S92Vnx;A1A2S22R5S82A2M2A3S0S3bS3dG0G2A2Z100A3A2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & AL & IMG & HTOP & _). cbn zeta in *.
  pose proof (urange a) as Ra. unfold PG in AL. set (ua := bv_unsigned a) in *. unfold IMG_HI in IMG.
  assert (D1 : (ua + 4096) / 8 = ua / 8 + 512) by (replace (ua + 4096) with (ua + 512 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
  assert (D2 : (ua + 6136) / 8 = ua / 8 + 767) by (replace (ua + 6136) with (ua + 767 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
  pose proof (Z.div_pos ua 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_lt_upper_bound ua 8 (2 ^ 61) ltac:(lia) ltac:(lia)) as DU.
  split; [|split].
  - unfold B3. cbn [eval]. rewrite Enx, add_val, srl_val, add_val, !u64_lit by lia. fold ua. change (3 mod 64) with 3.
    rewrite (Z.mod_small (ua + 4096)) by (clear -Ra HTOP SMB; lia). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite D1.
    unfold Sh, SHADOW_OFF. rewrite Z.mod_small by (clear -DP DU; lia). lia.
  - unfold a2e6, L3. cbn [eval]. rewrite Enx. apply bv_eq.
    rewrite sub_val, add_val, !srl_val, !add_val, !u64_lit by lia. fold ua. change (3 mod 64) with 3.
    rewrite (Z.mod_small (ua + 4096)) by (clear -Ra HTOP SMB; lia). rewrite (Z.mod_small (ua + 6136)) by (clear -Ra HTOP SMB; lia).
    rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite D1, D2.
    rewrite (Z.mod_small (ua / 8 + 767 + 1)) by (clear -DP DU; lia). replace (ua / 8 + 767 + 1 - (ua / 8 + 512)) with 256 by lia. reflexivity.
  - unfold L3. cbn [eval]. apply u64_lit. lia.
Qed.

Section G43.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S14S0S16S15VBX;R1A1A1S15R1A1A3FX;").

Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;VBX;R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1VFXP;A3S4S1cA1S0S4S9S9S1eS1eA2S1eA2M1A1S4eS1cG1S57R1A4S4eS1cG1S57VPX;A4A3S4fS1cS1cS79S25R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (C5 C5A C5B Y6A Y6B E6 CT6 CO6 T6 : axst) (sA sB s6 : wsub) (R6 : list sobj).
Let D6 : axst := ltac2:(tb__ "0|0|
S7eVT6;S21S34VCO6;A1A1A2").
Hypothesis HC5A : ltac2:(tb__ "0|0|
S0S35S6dS86Vnx;A1VC5;A2VC5A;A3").
Hypothesis HC5B : ltac2:(tb__ "0|0|
S0S35S6dS87Vnx;A1VC5;A2VC5B;A3").
Hypothesis FBA : ltac2:(tb__ "0|0|
S0S5S5dS1fS26S20S34VC5;A1A1A1S86Vnx;A1A3S6A3").
Hypothesis FBB : ltac2:(tb__ "0|0|
S0S5S5dS1fS26S20S34VC5;A1A1A1S87Vnx;A1A3S6A3").
Hypothesis Cert6A : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bS77S8S3bA1A3VGS;S7S35VC5A;S8S35A1M0A3S7S35VY6A;G0A3A6S6A3").
Hypothesis Cert6B : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bS77S8S3bA1A3VGS;S7S35VC5B;S8S35A1M0A3S7S35VY6B;G0A3A6S6A3").
Hypothesis E6A : ltac2:(tb__ "0|0|
S0S5S39VY6A;VE6;VsA;A3S6A3").
Hypothesis I6A : ltac2:(tb__ "0|0|
S0S5Sa3VsA;VGS;A2S6A3").
Hypothesis E6B : ltac2:(tb__ "0|0|
S0S5S39VY6B;VE6;VsB;A3S6A3").
Hypothesis I6B : ltac2:(tb__ "0|0|
S0S5Sa3VsB;VGS;A2S6A3").

Hypothesis WC6 : ltac2:(tb__ "0|0|
S0S5S27S34VCT6;A1A1S6A3").
Hypothesis DF6 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VE6;A1S34VCT6;A1A2ScG3SbG1G2S7G0SbS1eS1eS92Vnx;A1S82A4S8G0A1A3S8S1fA1A4A2A3").
Hypothesis NX6 : ltac2:(tb__ "0|0|
S0S3cS20S34VCT6;A1A1S20S34VE6;A1A1A3").
Hypothesis HC6 : ltac2:(tb__ "0|0|
S0S35S37VE6;S34VCT6;A1A2VCT6;A3").
Hypothesis SK6 : ltac2:(tb__ "0|1|
S0S4S9S9S1eS1eA2S1eA2M0A1S4eS1cG0S57S2bS34VCT6;A1A1A4S4eS1cG0S57SdS1cS7S1cS6fVnx;A1S7S1cS6eVnx;A1S8S1cA1A3A3SdS1cS7aVnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC6 : ltac2:(tb__ "0|0|
S5eS1fSdS1fS47VW;Vst;A2S46S45A1A3S21S34VCT6;A1A1A3").
Hypothesis FX6 : ltac2:(tb__ "0|0|
S5eS1fVFXP;S21S34VCT6;A1A1A3").
Hypothesis XC6 : ax_X CT6 = [].
Hypothesis HCO6 : ltac2:(tb__ "0|0|
S0S35S70VCT6;S30S84Vnx;A1S28Z0A1S82S8S2fA1S2cA5A2VCO6;A3").
Hypothesis WCO6 : ltac2:(tb__ "0|0|
S0S5S27S34VCO6;A1A1S6A3").
Hypothesis He6 : ltac2:(tb__ "0|1|
S0SaS4S1cA1M0A1S80VCO6;S69Vs6;A3ScG0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0S5S7fVCO6;S69Vs6;VR6;S4eS36S35S38S6aA4A5S6A3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0S35S81Vs6;S69S72VCO6;VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0S5S5dS1fS26S20S34VCO6;A1M0A1A1S21G0A1A3S6A3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0S5S5dS1fS26S20S34VT6;A1A1A1S21S34VCO6;A1A1A3S6A3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S0S5S7dVGS;S20S34VCO6;A1A1A2S6A3").

Lemma RS6 : ltac2:(tb__ "0|1|
S14S40S1dS3eQ40A1M0S1dS4G0A1S5bS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S48Vsegs;VJG;VBX;R8R7R6R5A5VE6;R4R3R2A6S48Vsegs;VJG;VBX;R9R8R7R6A5VCT6;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW Hw. destruct w as [tr [ms md]]. rewrite <- HC6.
  eapply SPA_restate; [exact WC6 | exact DF6 | exact NX6 | | constructor | exact Hw].
  unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
  exact (proj1 (proj2 (site3_vals BX A Kc rho a rhoX tp tr md (proj2 Hw)))).
Qed.

Lemma HBL6 : ltac2:(tb__ "0|b|
S14S40S1dS3eQ40M0A1M1S1dS4G1A1S5bS48Vsegs;VJG;VBX;R7R6R5R4A5VCT6;R3R2R1A6S1S52S61S3dG0R5A2A1M2S3dG0S22R4S84Vnx;A1M3A2A2M4A2S1S52S51G4S3dG0S22R4S82A2A2A2S51G2S54S66S3dG0S23R6PcA2A2A1Z8A2A2A2S1S4S1cA1M5S0S4S9S9S1eS1eA2S1eA2M6A1M7S4eS1cG6S57R1A4M8S4eS1cG6S57S7S1cS6fVnx;A1S7S1cS6eVnx;A1S8S1cA1A3A3A4A3S4fS1cS1cS31S25R7R1A2SbS3bS3bS3dG0S22R7G3A2A2M9S51G9S3dG0S22R7S82A2A2A2A4A2Lo;R2A3MaF_;Fl;G5S0G7G8S4eS1cG6S57VPX;A4A3GaF_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. pose proof (SPA_facts_hold segs _ rhoX CT6 tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct (site3_vals BX A Kc rho a rhoX tp tr md HJ) as (EB & _ & EL). rewrite EB, EL.
  destruct (site2_vals nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (_ & EB2 & _ & EL2 & BL2 & _). cbn zeta in EB2, EL2, BL2.
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (EB1 & EL1 & BB1).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  assert (V512 : 512 <= secneeded (bv_unsigned (rw rho 12%positive)) / 8) by (rewrite ENS; apply Z.div_le_lower_bound; clear -R8B HN; lia).
  assert (L9216 : 9216 <= secmapsize (bv_unsigned (rw rho 12%positive)) / 8) by (apply Z.div_le_lower_bound; clear -SMB; lia).
  split; [lia|]. split; [clear -L9216; lia|]. split.
  - intros l2 EE. destruct l2 as [|o [|o' [|o'' l2']]]; try (cbn in EE; discriminate EE).
    assert (Es : skel o = skel (O_2 nx)) by (cbn in EE; congruence). assert (Es' : skel o' = skel (O_1 nx)) by (cbn in EE; congruence).
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + rewrite (obj_range_skel rhoX o (O_2 nx) Es). unfold O_2, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
      rewrite soff_lit_small by lia. rewrite (soff_of_val rhoX L2 _ EL2) by (clear -BL2; lia). rewrite EB2.
      unfold ranges_disjoint. cbn [fst snd]. right. right. right. clear -V512. lia.
    + rewrite (obj_range_skel rhoX o' (O_1 nx) Es'). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
      unfold ranges_disjoint. cbn [fst snd]. right. right. left. lia.
  - intros l2 EE. pose proof (run_band BX A Kc rho a rhoX tp tr md HJ) as RB.
    assert (HFX : Forall (holds rhoX) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HF p (FX6 p Hp))).
    pose proof (PX_noband A Kc rho a rhoX tp tr md HJ HFX l2 EE) as NB.
    eapply Forall_impl; [|exact NB]. intros o Ho. cbn beta in Ho. unfold ranges_disjoint. cbn [fst snd].
    destruct (Z_lt_le_dec (fst (obj_range rhoX o)) (snd (obj_range rhoX o))) as [NE|]; [|left; lia].
    destruct (Z_le_gt_dec (snd (obj_range rhoX o)) (Sh (bv_unsigned a) + 512)) as [|G1]; [right; right; left; lia|].
    destruct (Z_le_gt_dec (Sh (bv_unsigned a) + 512 + 256) (fst (obj_range rhoX o))) as [|G2]; [right; right; right; lia|].
    exfalso. set (x := Z.max (fst (obj_range rhoX o)) (Sh (bv_unsigned a) + 512)).
    pose proof (Ho x ltac:(unfold x; lia)) as NBx. pose proof (RB x ltac:(unfold x; clear -L9216 G1 G2 NE; lia)) as Bx.
    unfold noband in NBx. clear -NBx Bx. lia.
Qed.

Theorem sec_g43 : ltac2:(tb__ "0|5|
S5bOF_;S14S40S1dS3eQ40M0A1M1S5cS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3S3bS1S52S61S3dG0R7A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R8PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S2aR9S3fG0R2A2A2SeG3A1A3A1F_;Fz;S1dS4G1A1M4S5aVsegs;RdS48Vsegs;VJG;VBX;RcRbRaR9A5VD6;R2R1A5R8A4FtpY;FrhoY;S1dG4S5aVsegs;ReS48Vsegs;VJG;VBX;RdRcRbRaA5VC5;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCONT rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  assert (SL : slink (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }

  assert (TAIL : forall rE tE, triple segs ok (SPA segs (JG BX A Kc rho a) E6 rE tE) Q).
  { intros rE tE.
    apply (ms_step nW st tmax nx Hnx NXG BX BXg E6 CT6 CO6 T6 (B3 nx) L3 [O_2 nx; O_1 nx] PX Pre_memsetA Pret_ms Posts_memsetA s6 R6 eq_refl
             (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl RS6 HBL6 SK6 FC6 XC6 HCO6 WCO6 He6 Hchk6 HT6 FBC6 FBT6 NXC6
             ok A Kc rho rho a tE Q HW HUS HKc Hokl SL).
    intros rhoY tpY. exact (HCONT rhoY tpY). }

  apply (triple_conseq (P:=fun w => SPA segs (JG BX A Kc rho a) C5A rX tX w \/ SPA segs (JG BX A Kc rho a) C5B rX tX w)
           (SPA segs (JG BX A Kc rho a) C5 rX tX) (Q:=Q)); [intros w Hw | intros w Hw; exact Hw |].
  { destruct w as [tr [ms md]]. destruct (diamond_hold BX A Kc rho a rX tX tr md BXg (proj2 Hw)) as [FA|FB]; [left; rewrite <- HC5A | right; rewrite <- HC5B].
    - split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_A nx) _ _ (proj1 Hw) FA FBA).
    - split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_B nx) _ _ (proj1 Hw) FB FBB). }
  apply triple_disj.
  - apply (cfg_soundA segs 4000%nat [MSENT] GS [C5A] [Y6A] (JG BX A Kc rho a) ok Q tX Hokf HST Cert6A); [|left; reflexivity].
    intros E rE HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact (join4 nW st tmax nx Hnx NXG BX A Kc rho a Y6A E6 sA rE tX w HUS HKc E6A I6A Hw) | intros w Hw; right; exact Hw |].
    apply TAIL.
  - apply (cfg_soundA segs 4000%nat [MSENT] GS [C5B] [Y6B] (JG BX A Kc rho a) ok Q tX Hokf HST Cert6B); [|left; reflexivity].
    intros E rE HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact (join4 nW st tmax nx Hnx NXG BX A Kc rho a Y6B E6 sB rE tX w HUS HKc E6B I6B Hw) | intros w Hw; right; exact Hw |].
    apply TAIL.
Qed.
End G43.

Lemma ms_call : ltac2:(tb__ "0|8|
S14S14F_;S35S35S35S35S4S36A1M0Sa4S4S1cA1M1S0G0R3S7S36S3aR4Sb0A2S8S36A1A3A3S5bOF_;M2S4cS1dS4S3eQ40A1M3A1M4S4aVsegs;R4R3A3S4dVsegs;Sa2R4A3S5aVsegs;R6S48Vsegs;R5RcR4R3A5S4bVsegs;R5Sa2R4R3RaA6A4F_;F_;Ftp;Frho;FJx;Fok;S0S3cS20S34R7A1A1Sa2A3S0SaG1A1S80RaR8R5A3ScG1R4A2A3S0S5S7fRbR9R6R5S4eS36S35S38R7A4A5S6A3S0S35S81R7RaR9RcR6A5RbA3S0S5S5dS1fS26S20S34RdA1M5A1A1M6S21G5A1A3S6A3S0S5S5dS1fG6S21S34ReA1A1A3S6A3S0S5S7dVGS;S20S34RfA1A1A2S6A3G2S14S40S1dG3G4S5cS67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3S1dG4S5aVsegs;RcS48Vsegs;VJG;R1dRbRaR9R8A5M7S7eR1bS21S34R1cA1A1A2R2R1A5R6A4FtpY;FrhoY;S1dS5aVsegs;RcS48Vsegs;G7R1cR1R7A5R6A4FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;F_;F_;F_;F_;F_;F_;F_;F_;F_;FR;Fs;FPosts;FPret;FPre;FT;FCM;FBX;").
Proof.
  intros BX CM T Pre Pret Posts s R HPosts Hsum NPre He Hchk HT FBC FBT NXC ok A Kc rho a tp Q HUS HKc Hokf HD rhoX.
  pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  set (Jf := (fun (_ : valuation) t tr md => JG BX A Kc rho a rhoX t tr md) : jpredA).
  assert (Jf_okf : ok_frameA segs ok Jf).
  { intros r t tr ms md msv' HJ HMI Hh Hp Hs. exact (Hokf rhoX t tr ms md msv' (JG_K nW st nx BX A Kc rho a _ _ _ _ HJ) HMI Hh Hp Hs). }
  assert (Jf_st : stableA segs NF Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  apply (triple_pre_pure segs ok _ _ (Forall (holds rhoX) (ss_facts (ax_S CM)))).
  { intros w Hw. exact (SPA_facts_hold segs _ rhoX CM tp w Hw). }
  intros HFC.
  apply (call_soundA segs ok (JG BX A Kc rho a) Jf Jf (JG BX A Kc rho a) CM Pre s R Posts Q rhoX tp He Hchk).
  - intros rho1 tp1. rewrite NPre. exact (Hsum ok Jf rho1 tp1 Jf_okf Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros Lf rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ'].
    eapply agree_below_le; [apply Pos.leb_le; exact NXC | exact (proj1 HLK)].
  - intros Lf rho' tpL HinL Hag. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state]. rewrite HT.
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HD rho' tpL)].
    apply SPA_refacts; [exact Hw | exact FBT |]. intros _.
    exact (Forall_holds_agree _ rhoX rho' _ Hag FBC HFC).
Qed.

Lemma F_g7_hold : ltac2:(tb__ "0|1|
S14S14F_;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1S8dVnx;A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & AL & IMG & HTOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. unfold IMG_HI in IMG.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). unfold PG in *. lia. }
  unfold F_g7, RUE. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval branch_taken]. intros H. unfold bv_ltu in H. apply Z.ltb_lt in H.
  rewrite and_val, !add_val, Enx, E12, !u64_lit in H by lia. fold ua nv in H.
  rewrite (Z.mod_small (ua + 6144)) in H by (clear -Ra HTOP SMB; lia). rewrite (Z.mod_small (ua + 6144 + nv)) in H by (clear -Ra HTOP LB HN SMB; lia).
  rewrite (Z.mod_small (ua + 6144 + nv + 7)) in H by (clear -Ra HTOP LB HN SMB; lia).
  rewrite (land_m8E nW st tmax nx Hnx) in H by (clear -Ra HTOP LB HN SMB; lia). pose proof (Z.mod_pos_bound (ua + 6144 + nv + 7) 8 ltac:(lia)) as MB. clear -H MB HTOP LB Ra HN SMB. lia.
Qed.

Lemma site7_vals : ltac2:(tb__ "0|9|
S14S14F_;S14S40S1dS3eQ40M0A1M1S1dS4G1A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S3dG0S23R7PcA2A2S3bS3dG0R7A2S3bS68R2A1S3bS66R3A1S3bS1S0G1S22R9S91Vnx;A1A2S22R9S71Vnx;A1A2M2A3S1S0G1S22R9S93Vnx;A1A2S22R9S90A2M3A3S1S0S3bS3dG0G2A2S51S51S61R3A1S54R2Z8M4A2M5A2Z100M6A2A3S1S0S3bS3dG0G3A2S55S55S54R1G4A2M7G5A2G6A2A3S1S52Z200M8G5A2S52S51G5G8A2G7A2A2A2A2A2A2TMS;TVNS;Tua;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & E141 & E142 & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  pose proof (site2_vals nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & EL2 & BL2 & _).
  pose proof (urange a) as Ra. cbn zeta in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  set (VNS := secneeded nv) in *. set (MS := secmapsize nv) in *. unfold IMG_HI in IMG.
  assert (V8 : VNS mod 8 = 0) by (rewrite ENS, Z.add_mod, R8M by lia; reflexivity).
  assert (M8 : MS mod 8 = 0).
  { pose proof (Z.div_mod MS 4096 ltac:(lia)) as X. unfold PG in SMM. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (MS / 4096)) with ((512 * (MS / 4096)) * 8) by lia. apply Z_mod_mult. }
  assert (A8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(lia)) as X. unfold PG in AL. rewrite AL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by lia. apply Z_mod_mult. }
  assert (VB : 68609 <= VNS <= nv + 4103) by (rewrite ENS; clear -R8B HN; lia).
  assert (MB : VNS + 4096 <= MS <= VNS + 8191).
  { rewrite EMS. unfold PG. pose proof (round_up_ge' VNS 4096 ltac:(lia)) as H. clear -H. lia. }
  pose proof (Z.div_mod VNS 8 ltac:(lia)) as DV. pose proof (Z.div_mod MS 8 ltac:(lia)) as DM. pose proof (Z.div_mod ua 8 ltac:(lia)) as DA.
  rewrite V8 in DV. rewrite M8 in DM. rewrite A8 in DA.
  assert (SHB : Sh ua + MS / 8 < 2 ^ 45) by (unfold Sh, SHADOW_OFF; clear -TOP DM DA Ra MB VB; lia).

  assert (ERUE : bv_unsigned (eval r (RUE nx)) = ua + 2048 + VNS).
  { unfold RUE. cbn [eval]. rewrite Enx, E12, and_val, !add_val, !u64_lit by lia. fold ua nv.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP MB VB; lia). rewrite (Z.mod_small (ua + 6144 + nv)) by (clear -Ra TOP MB VB HN; lia).
    rewrite (Z.mod_small (ua + 6144 + nv + 7)) by (clear -Ra TOP MB VB HN; lia). rewrite (land_m8E nW st tmax nx Hnx) by (clear -Ra TOP MB VB HN; lia).
    rewrite ENS. unfold round_up. replace (ua + 6144 + nv + 7) with (nv + 8 - 1 + (ua / 8 + 768) * 8) by (clear -DA; lia). rewrite Z_mod_plus_full.
    pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)) as X. clear -X DA. lia. }
  assert (EA0 : bv_unsigned (eval r (a0e7 nx)) = Sh ua + VNS / 8 + 256).
  { unfold a0e7. cbn [eval]. change (eval r (RUE nx)) with (eval r (RUE nx)). rewrite add_val, srl_val. cbn [eval] in ERUE. rewrite ERUE.
    rewrite !u64_lit by lia. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    replace (ua + 2048 + VNS) with ((ua / 8 + 256 + VNS / 8) * 8) by (clear -DA DV; lia). rewrite Z.div_mul by lia.
    unfold Sh, SHADOW_OFF in *. rewrite Z.mod_small; clear -SHB DM DA DV MB Ra VB; lia. }
  assert (EB : bv_unsigned (eval r (BR nx)) = Sh ua + VNS / 8 + 256).
  { unfold BR, shS, vMAPn. cbn [eval]. rewrite Enx, E141.
    rewrite !add_val. rewrite !srl_val. rewrite !u64_lit by (unfold SHADOW_OFF in *; lia).
    fold ua. change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold Sh, SHADOW_OFF in *. rewrite !Z.mod_small; clear -SHB DM DA DV MB Ra VB; lia. }
  assert (EL : bv_unsigned (eval r L3b) = MS / 8 - VNS / 8 - 256).
  { unfold L3b. cbn [eval]. rewrite add_val. cbn [eval] in EL2. rewrite EL2, u64_lit by lia. rewrite Z.mod_small by (clear -BL2; lia). lia. }
  assert (EA2 : bv_unsigned (eval r (a2e7 nx)) = MS / 8 - VNS / 8 - 256).
  { unfold a2e7. cbn [eval]. cbn [eval] in ERUE. rewrite E141, Enx.
    rewrite !sub_val, !add_val, !srl_val, !add_val, !sub_val, !add_val, and_val, add_val. rewrite ERUE.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity.
    rewrite !u64_lit by lia. fold ua. change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (Z.mod_small (VNS + 4095)) by lia. rewrite (land_m4096E nW st tmax nx Hnx) by lia.
    assert (ERU : VNS + 4095 - (VNS + 4095) mod 4096 + 4096 = MS).
    { rewrite EMS. unfold round_up, PG. pose proof (Z.div_mod (VNS + 4096 - 1) 4096 ltac:(lia)). replace (VNS + 4095) with (VNS + 4096 - 1) by lia. lia. }
    set (RPG := VNS + 4095 - (VNS + 4095) mod 4096) in *.
    rewrite (Z.mod_small (ua + 4096)) by (clear -Ra TOP MB VB; lia).

    rewrite (Z.add_mod_idemp_l (ua + 4096 - (ua + 2048 + VNS))) by lia.
    rewrite (Z.add_mod_idemp_r (ua + 2048 + VNS)) by lia.
    replace (ua + 2048 + VNS + (ua + 4096 - (ua + 2048 + VNS) + RPG)) with (ua + MS) by (clear -ERU; lia).
    rewrite (Z.mod_small (ua + MS)) by (clear -Ra TOP MB VB; lia).
    replace ((ua + MS + (2 ^ 64 - 8)) mod 2 ^ 64) with (ua + MS - 8).
    2:{ replace (ua + MS + (2 ^ 64 - 8)) with (ua + MS - 8 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. clear -Ra TOP MB VB IMG. lia. }
    replace (ua + MS - 8) with ((MS / 8 + ua / 8 - 1) * 8) by (clear -DA DM; lia). rewrite Z.div_mul by lia.
    replace (ua + 2048 + VNS) with ((ua / 8 + 256 + VNS / 8) * 8) by (clear -DA DV; lia). rewrite Z.div_mul by lia.
    rewrite (Z.mod_small (MS / 8 + ua / 8 - 1 + 1)) by (clear -DA DM DV MB Ra VB TOP IMG; lia). rewrite Z.mod_small by (clear -DA DM DV MB Ra VB TOP IMG; lia). lia. }
  split; [apply bv_eq; rewrite EA0, EB; reflexivity|]. split; [apply bv_eq; rewrite EA2, EL; reflexivity|].
  split; [exact EB|]. split; [exact EL|]. split; [clear -DV VB; lia | clear -DV DM MB; lia].
Qed.

Section G44.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S14S0S16S15VBX;R1A1A1S15R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;VBX;R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1VFXP;A3S4S1cA1S0S4S9S9S1eS1eA2S1eA2M1A1S4eS1cG1S57R1A4S4eS1cG1S57VPX;A4A3S4fS1cS1cS79S25R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D6 U7 ET7 CT7 CO7 CR7 CS7 CM7 T7 : axst) (s7 : wsub) (R7 : list sobj) (n7 : nat).
Let D7 : axst := ltac2:(tb__ "0|0|
S7eVT7;S21S34VCM7;A1A1A2").
Hypothesis WU7 : ltac2:(tb__ "0|0|
S0S5S27S34VU7;A1A1S6A3").
Hypothesis DU7 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VD6;A1S34VU7;A1A2ScG3SbG1G2S8G0A1S8dVnx;A1A4A2A3").
Hypothesis NXU7 : ltac2:(tb__ "0|0|
S0S3cS20S34VU7;A1A1S20S34VD6;A1A1A3").
Hypothesis HU7 : ltac2:(tb__ "0|0|
S0S35S37VD6;S34VU7;A1A2VU7;A3").
Hypothesis Cert7 : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bS77S8S3bA1A3VGS;S7S35VU7;S8S35A1M0A3S7S35VET7;G0A3A6S6A3").
Hypothesis WC7 : ltac2:(tb__ "0|0|
S0S5S27S34VCT7;A1A1S6A3").
Hypothesis DF7 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VET7;A1S34VCT7;A1A2ScG3SbG1G2S7G0SbS1eS1eS91Vnx;A1S71Vnx;A1A4S7G0SbS1eS1eS93Vnx;A1S90A4S8G0A1A3A3S8S1fA1A4A2A3").
Hypothesis NX7 : ltac2:(tb__ "0|0|
S0S3cS20S34VCT7;A1A1S20S34VET7;A1A1A3").
Hypothesis HC7 : ltac2:(tb__ "0|0|
S0S35S37VET7;S34VCT7;A1A2VCT7;A3").
Hypothesis SK7 : ltac2:(tb__ "0|1|
S0S4S9S9S1eS1eA2S1eA2M0A1S4eS1cG0S57S2bS34VCT7;A1A1A4S4eS1cG0S57SdS1cS7S1cS83Vnx;A1S7S1cS6fVnx;A1S7S1cS6eVnx;A1S8S1cA1A3A3A3SdS1cS7aVnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC7 : ltac2:(tb__ "0|0|
S5eS1fSdS1fS47VW;Vst;A2S46S45A1A3S21S34VCT7;A1A1A3").
Hypothesis FX7 : ltac2:(tb__ "0|0|
S5eS1fVFXP;S21S34VCT7;A1A1A3").
Hypothesis XC7 : ax_X CT7 = [].
Hypothesis HCO7 : ltac2:(tb__ "0|0|
S0S35S70VCT7;S30S71Vnx;A1S28Z0A1S28Z100A1S8S2fA1S2cA5A2VCO7;A3").
Hypothesis WCO7 : ltac2:(tb__ "0|0|
S0S5S27S34VCO7;A1A1S6A3").

Hypothesis RB7 : ltac2:(tb__ "0|0|
S0S5Sa6S32SafS34VCO7;A1U1A2A2S6A3").
Hypothesis HCR7 : ltac2:(tb__ "0|0|
S0S35Sa8VCO7;U1A2VCR7;A3").
Hypothesis LEN7 : ltac2:(tb__ "0|0|
S0SfS13S1cS2bS34VCR7;A1A1A2Vn7;A3").
Hypothesis PERM_nd7 : ltac2:(tb__ "0|0|
S0S5SadS8bVn7;A1A1S6A3").
Hypothesis PERM_lt7 : ltac2:(tb__ "0|0|
S0S5S5dSfSfSb5R1Vn7;A2Li;S8bVn7;A1A3S6A3").
Hypothesis PERM_cov7 : ltac2:(tb__ "0|0|
S0S5S5dSfSfS60SfSb4R1A1S8bVn7;A1A3Li;S50U0Vn7;A2A3S6A3").
Hypothesis HCS7 : ltac2:(tb__ "0|0|
S0S35S9aVCR7;A1VCS7;A3").
Hypothesis MRG7 : ltac2:(tb__ "0|0|
S0S5Sa6S32SaeS34VCS7;A1U1A2A2S6A3").
Hypothesis HCM7 : ltac2:(tb__ "0|0|
S0S35Sa7VCS7;U1A2VCM7;A3").
Hypothesis He7 : ltac2:(tb__ "0|1|
S0SaS4S1cA1M0A1S80VCM7;S69Vs7;A3ScG0VR7;A2A3").
Hypothesis Hchk7 : ltac2:(tb__ "0|0|
S0S5S7fVCM7;S69Vs7;VR7;S4eS36S35S38S6aA4A5S6A3").
Hypothesis HT7 : ltac2:(tb__ "0|0|
S0S35S81Vs7;S69S72VCM7;VR7;A5VT7;A3").
Hypothesis FBC7 : ltac2:(tb__ "0|1|
S0S5S5dS1fS26S20S34VCM7;A1M0A1A1S21G0A1A3S6A3").
Hypothesis FBT7 : ltac2:(tb__ "0|0|
S0S5S5dS1fS26S20S34VT7;A1A1A1S21S34VCM7;A1A1A3S6A3").
Hypothesis NXC7 : ltac2:(tb__ "0|0|
S0S5S7dVGS;S20S34VCM7;A1A1A2S6A3").

Lemma RSU7 : ltac2:(tb__ "0|1|
S14S40S1dS3eQ40A1M0S1dS4G0A1S5bS48Vsegs;VJG;VBX;R7R6R5R4A5VD6;R3R2R1A6S48Vsegs;VJG;VBX;R8R7R6R5A5VU7;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HU7.
  eapply SPA_restate; [exact WU7 | exact DU7 | exact NXU7 | constructor | | exact Hw].
  exact (F_g7_hold BX A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.

Lemma prep7 : ltac2:(tb__ "0|4|
S14S40S1dS3eQ40M0A1M1S1dS4G1A1S5bS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S3bS1S52S61S3dG0R6A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R7PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S2aR8S3fG0R2A2A2SeG3A1A3A1F_;Fz;S48Vsegs;VJG;VBX;R9R8R7R6A5VET7;R5R4R3A6S48Vsegs;VJG;VBX;RaR9R8R7A5VCM7;R6R5R4A6F_;F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW RUNDEF Hw. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct (site7_vals BX A Kc rho a rhoX tp tr md HJ) as (EA0 & EA2 & EB & EL & V512 & VM). cbn zeta in EB, EL, V512, VM.
  destruct (site3_vals BX A Kc rho a rhoX tp tr md HJ) as (EB3 & _ & EL3).
  destruct (site2_vals nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (_ & EB2 & _ & EL2 & BL2 & _). cbn zeta in EB2, EL2, BL2.
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (EB1 & EL1 & BB1).

  assert (HC : SPA segs (JG BX A Kc rho a) CT7 rhoX tp (tr, mkCfg ms md)).
  { rewrite <- HC7. eapply SPA_restate; [exact WC7 | exact DF7 | exact NX7 | | constructor | exact Hw].
    unfold diffs_ok. apply Forall_cons; [exact EA0|]. apply Forall_cons; [exact EA2 | apply Forall_nil]. }
  pose proof (SPA_facts_hold segs _ rhoX CT7 tp _ HC) as HF.

  assert (SL : slink (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }
  assert (E256 : bv_unsigned (eval rhoX (SLit 256)) = 256) by (cbn [eval]; apply u64_lit; lia).
  assert (HCO : SPA segs (JG BX A Kc rho a) CO7 rhoX tp (tr, mkCfg ms md)).
  { rewrite <- HCO7. apply (carve_piece nW st tmax nx Hnx BX CT7 (BR nx) (SLit 256) A Kc rho rho a rhoX tp _ SL HC); [rewrite HCO7; exact WCO7 | exact XC7 | | |].
    - rewrite EB. clear -V512. lia.
    - rewrite EB, E256. clear -VM. lia.
    - rewrite EB, E256. pose proof (run_band BX A Kc rho a rhoX tp tr md HJ) as RB.
      apply (pieces_disjoint nW st tmax nx Hnx BX BXg CT7 [O_3 nx; O_2 nx; O_1 nx] PX A Kc rho a rhoX tp _ _ _ HW HC SK7 FC7).
      + apply (RB (Sh (bv_unsigned a) + secneeded (bv_unsigned (rw rho 12%positive)) / 8 + 256)). clear -V512 VM. lia.
      + pose proof (RB (Sh (bv_unsigned a) + secneeded (bv_unsigned (rw rho 12%positive)) / 8 + 256 + 256 - 1) ltac:(clear -V512 VM; lia)). lia.
      + intros l2 EE. destruct l2 as [|o [|o' [|o'' [|o3 l2']]]]; try (cbn in EE; discriminate EE).
        assert (Es : skel o = skel (O_3 nx)) by (cbn in EE; congruence). assert (Es' : skel o' = skel (O_2 nx)) by (cbn in EE; congruence).
        assert (Es'' : skel o'' = skel (O_1 nx)) by (cbn in EE; congruence).
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        * rewrite (obj_range_skel rhoX o (O_3 nx) Es). unfold O_3, L3. rewrite obj_range_mk by lia. rewrite EB3.
          unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -V512. lia.
        * rewrite (obj_range_skel rhoX o' (O_2 nx) Es'). unfold O_2, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
          rewrite soff_lit_small by lia. rewrite (soff_of_val rhoX L2 _ EL2) by (clear -BL2; lia). rewrite EB2.
          unfold ranges_disjoint. cbn [fst snd]. right. right. right. lia.
        * rewrite (obj_range_skel rhoX o'' (O_1 nx) Es''). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
          unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -V512. lia.
      + intros l2 EE.
        assert (HFX : Forall (holds rhoX) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HF p (FX7 p Hp))).
        pose proof (PX_noband A Kc rho a rhoX tp tr md HJ HFX l2 EE) as NB.
        eapply Forall_impl; [|exact NB]. intros o Ho. cbn beta in Ho. unfold ranges_disjoint. cbn [fst snd].
        set (lo := Sh (bv_unsigned a) + secneeded (bv_unsigned (rw rho 12%positive)) / 8 + 256) in *.
        destruct (Z_lt_le_dec (fst (obj_range rhoX o)) (snd (obj_range rhoX o))) as [NE|]; [|left; lia].
        destruct (Z_le_gt_dec (snd (obj_range rhoX o)) lo) as [|G1]; [right; right; left; lia|].
        destruct (Z_le_gt_dec (lo + 256) (fst (obj_range rhoX o))) as [|G2]; [right; right; right; lia|].
        exfalso. set (x := Z.max (fst (obj_range rhoX o)) lo).
        pose proof (Ho x ltac:(unfold x; lia)) as NBx. pose proof (RB x ltac:(unfold x, lo in *; clear -V512 VM G1 G2 NE; lia)) as Bx.
        unfold noband in NBx. clear -NBx Bx. lia. }

  assert (XCO : ax_X CO7 = []) by (rewrite <- HCO7; exact XC7).
  assert (HCR : SPA segs (JG BX A Kc rho a) CR7 rhoX tp (tr, mkCfg ms md)).
  { rewrite <- HCR7. unfold oreb. destruct (rebase_obj_at (ax_S CO7) 1) as [S'|] eqn:E; [|exact HCO]. eapply (SPA_rebase segs); [exact E | exact XCO | exact HCO]. }
  assert (HCS : SPA segs (JG BX A Kc rho a) CS7 rhoX tp (tr, mkCfg ms md)).
  { rewrite <- HCS7. unfold sel7. rewrite LEN7. apply (SPA_select segs); [exact HCR | exact PERM_nd7 | |].
    - intros i Hi. rewrite LEN7. apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) PERM_lt7 i Hi).
    - intros i Hi. rewrite LEN7 in Hi. pose proof (proj1 (forallb_forall _ _) PERM_cov7 i ltac:(apply in_seq; lia)) as X.
      apply existsb_exists in X as (j & Hj & E). apply Nat.eqb_eq in E. subst j. exact Hj. }
  rewrite <- HCM7. unfold omrg. destruct (merge_objs_at (ax_S CS7) 1) as [S'|] eqn:E; [|exact HCS]. eapply (SPA_merge segs); [exact E | exact HCS].
Qed.

Theorem sec_g44 : ltac2:(tb__ "0|5|
S5bOF_;S14S40S1dS3eQ40M0A1M1S5cS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3S3bS1S52S61S3dG0R7A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R8PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S2aR9S3fG0R2A2A2SeG3A1A3A1F_;Fz;S1dS4G1A1M4S5aVsegs;RdS48Vsegs;VJG;VBX;RcRbRaR9A5VD7;R2R1A5R8A4FtpY;FrhoY;S1dG4S5aVsegs;ReS48Vsegs;VJG;VBX;RdRcRbRaA5VD6;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCONT rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  eapply triple_conseq; [intros w Hw; exact (RSU7 A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [MSENT] GS [U7] [ET7] (JG BX A Kc rho a) ok Q tX Hokf HST Cert7); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact (prep7 A Kc rho a rE tX w HW RUNDEF Hw) | intros w Hw; right; exact Hw |].
  exact (ms_call BX CM7 T7 Pre_memsetA Pret_ms Posts_memsetA s7 R7 eq_refl (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl
           He7 Hchk7 HT7 FBC7 FBT7 NXC7 ok A Kc rho a tX Q HUS HKc Hokl HCONT rE).
Qed.
End G44.

Lemma site8_vals : ltac2:(tb__ "0|5|
S14S14F_;S14S40S1dS3eQ40M0A1M1S1dS4G1A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S3dG0S23R7PcM2A2A2S3bS3dG0R7A2S3bS1S0S3bS3dG0S22R7S85Vnx;A1A2A2S51S61R1A1Z300A2A3S1S0S3bS3dG0S22R7S8aVnx;A1A2A2S54R2Z8M3A2A3S1S0S3bS3dG0S22R7S33S9cS29G2A1S28S78A1A3A2A2S55R2S56R2G3A2A2M4A3S0S3bS3dG0S22R7S95Vnx;A1A2A2S55S51S51R1Z1800A2G4A2G3A2A3A2A2A2Tua;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  pose proof (urange a) as Ra. cbn zeta in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *. unfold IMG_HI in IMG.
  assert (A8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(lia)) as X. unfold PG in AL. rewrite AL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by lia. apply Z_mod_mult. }
  pose proof (Z.div_mod ua 8 ltac:(lia)) as DA. rewrite A8, Z.add_0_r in DA.
  pose proof (Z.div_mod nv 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  assert (EN8 : bv_unsigned (eval r (SAlu ALU_AND (SVar 12) (SLit M48))) = nv - nv mod 8).
  { cbn [eval]. rewrite and_val, E12, !u64_lit by (unfold M48; lia). fold nv. apply land_M48. clear -HN. lia. }
  assert (EE : bv_unsigned (eval r (END8 nx)) = ua + 6144 + (nv - nv mod 8) - 8).
  { unfold END8. cbn [eval] in EN8 |- *. rewrite add_val, add_val, EN8, add_val, Enx, !u64_lit by lia. fold ua.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP SMB; lia). rewrite (Z.mod_small (ua + 6144 + (nv - nv mod 8))) by (clear -Ra TOP SMB HN MN; lia).
    replace (ua + 6144 + (nv - nv mod 8) + (2 ^ 64 - 8)) with (ua + 6144 + (nv - nv mod 8) - 8 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
    apply Z.mod_small. clear -Ra TOP SMB HN MN IMG. lia. }
  assert (D1 : (ua + 6144) / 8 = ua / 8 + 768) by (replace (ua + 6144) with (ua + 768 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
  pose proof (Z.div_pos ua 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_lt_upper_bound ua 8 (2 ^ 61) ltac:(lia) ltac:(lia)) as DU.
  split; [|split; [|split; [exact EN8 | exact EE]]].
  - unfold B4. cbn [eval]. rewrite Enx, add_val, srl_val, add_val, !u64_lit by lia. fold ua. change (3 mod 64) with 3.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP SMB; lia). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite D1.
    unfold Sh, SHADOW_OFF. rewrite Z.mod_small by (clear -DP DU; lia). lia.
  - unfold a2e8. cbn [eval]. cbn [eval] in EE. rewrite sub_val, add_val, !srl_val, EE, add_val, Enx, !u64_lit by lia. fold ua. change (3 mod 64) with 3.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP SMB; lia). rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite D1.
    replace (ua + 6144 + (nv - nv mod 8) - 8) with ((ua / 8 + 767 + nv / 8) * 8) by (clear -DA DN; lia). rewrite Z.div_mul by lia.
    pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)) as NU.
    rewrite (Z.mod_small (ua / 8 + 767 + nv / 8 + 1)) by (clear -DP DU NP NU; lia).
    replace (ua / 8 + 767 + nv / 8 + 1 - (ua / 8 + 768)) with (nv / 8) by lia. apply Z.mod_small. clear -NP NU. lia.
Qed.

Lemma F_g8_hold : ltac2:(tb__ "0|1|
S14S14F_;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1S8eVnx;A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  destruct (site8_vals BX A Kc rho a r tp tr md HJ) as (_ & EL & EN8 & EE). cbn zeta in EL, EN8, EE.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & TOP & ENS & EMS & _). cbn zeta in *.
  pose proof (urange a) as Ra. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *. unfold IMG_HI in IMG.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)) as NU.
  unfold F_g8. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - cbn [holds branch_taken]. unfold bv_ltu. apply Z.ltb_lt. rewrite EL. cbn [eval]. rewrite u64_lit by lia. clear -NP NU. lia.
  - cbn [holds branch_taken]. intros H. unfold bv_ltu in H. apply Z.ltb_lt in H. rewrite EE in H. cbn [eval] in H. rewrite u64_lit in H by lia. clear -H Ra TOP SMB HN MN LB. lia.
  - cbn [holds branch_taken]. intros H. unfold bv_eqb in H. apply Z.eqb_eq in H. rewrite EN8 in H. cbn [eval] in H. rewrite u64_lit in H by lia. clear -H HN MN. lia.
Qed.

Section G45.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S14S0S16S15VBX;R1A1A1S15R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;VBX;R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1VFXP;A3S4S1cA1S0S4S9S9S1eS1eA2S1eA2M1A1S4eS1cG1S57R1A4S4eS1cG1S57VPX;A4A3S4fS1cS1cS79S25R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D7 U8 ET8 CT8 CO8 T8 : axst) (s8 : wsub) (R8 : list sobj).
Let D8 : axst := ltac2:(tb__ "0|0|
S7eVT8;S21S34VCO8;A1A1A2").
Hypothesis WU8 : ltac2:(tb__ "0|0|
S0S5S27S34VU8;A1A1S6A3").
Hypothesis DU8 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VD7;A1S34VU8;A1A2ScG3SbG1G2S8G0A1S8eVnx;A1A4A2A3").
Hypothesis NXU8 : ltac2:(tb__ "0|0|
S0S3cS20S34VU8;A1A1S20S34VD7;A1A1A3").
Hypothesis HU8 : ltac2:(tb__ "0|0|
S0S35S37VD7;S34VU8;A1A2VU8;A3").
Hypothesis Cert8 : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bS77S8S3bA1A3VGS;S7S35VU8;S8S35A1M0A3S7S35VET8;G0A3A6S6A3").
Hypothesis WC8 : ltac2:(tb__ "0|0|
S0S5S27S34VCT8;A1A1S6A3").
Hypothesis DF8 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VET8;A1S34VCT8;A1A2ScG3SbG1G2S8G0A1S99Vnx;A1A4A2A3").
Hypothesis NX8 : ltac2:(tb__ "0|0|
S0S3cS20S34VCT8;A1A1S20S34VET8;A1A1A3").
Hypothesis HC8 : ltac2:(tb__ "0|0|
S0S35S37VET8;S34VCT8;A1A2VCT8;A3").
Hypothesis SK8 : ltac2:(tb__ "0|1|
S0S4S9S9S1eS1eA2S1eA2M0A1S4eS1cG0S57S2bS34VCT8;A1A1A4S4eS1cG0S57SdS1cS7S1cS89Vnx;A1S7S1cS83Vnx;A1S7S1cS6eVnx;A1S8S1cA1A3A3A3SdS1cS7aVnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC8 : ltac2:(tb__ "0|0|
S5eS1fSdS1fS47VW;Vst;A2S46S45A1A3S21S34VCT8;A1A1A3").
Hypothesis FX8 : ltac2:(tb__ "0|0|
S5eS1fVFXP;S21S34VCT8;A1A1A3").
Hypothesis XC8 : ax_X CT8 = [].
Hypothesis HCO8 : ltac2:(tb__ "0|0|
S0S35S70VCT8;S30S85Vnx;A1S28Z0A1S8aVnx;A1S8S2fA1S2cA5A2VCO8;A3").
Hypothesis WCO8 : ltac2:(tb__ "0|0|
S0S5S27S34VCO8;A1A1S6A3").
Hypothesis He8 : ltac2:(tb__ "0|1|
S0SaS4S1cA1M0A1S80VCO8;Sa0Vs8;A3ScG0VR8;A2A3").
Hypothesis Hchk8 : ltac2:(tb__ "0|0|
S0S5S7fVCO8;Sa0Vs8;VR8;S4eS36S35S38Sa1A4A5S6A3").
Hypothesis HT8 : ltac2:(tb__ "0|0|
S0S35S81Vs8;Sa0S75VCO8;VR8;A5VT8;A3").
Hypothesis FBC8 : ltac2:(tb__ "0|1|
S0S5S5dS1fS26S20S34VCO8;A1M0A1A1S21G0A1A3S6A3").
Hypothesis FBT8 : ltac2:(tb__ "0|0|
S0S5S5dS1fS26S20S34VT8;A1A1A1S21S34VCO8;A1A1A3S6A3").
Hypothesis NXC8 : ltac2:(tb__ "0|0|
S0S5S7dVGS;S20S34VCO8;A1A1A2S6A3").

Lemma RSU8 : ltac2:(tb__ "0|1|
S14S40S1dS3eQ40A1M0S1dS4G0A1S5bS48Vsegs;VJG;VBX;R7R6R5R4A5VD7;R3R2R1A6S48Vsegs;VJG;VBX;R8R7R6R5A5VU8;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HU8.
  eapply SPA_restate; [exact WU8 | exact DU8 | exact NXU8 | constructor | | exact Hw].
  exact (F_g8_hold BX A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.

Lemma RS8 : ltac2:(tb__ "0|1|
S14S40S1dS3eQ40A1M0S1dS4G0A1S5bS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S48Vsegs;VJG;VBX;R8R7R6R5A5VET8;R4R3R2A6S48Vsegs;VJG;VBX;R9R8R7R6A5VCT8;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW Hw. destruct w as [tr [ms md]]. rewrite <- HC8.
  eapply SPA_restate; [exact WC8 | exact DF8 | exact NX8 | constructor | | exact Hw].
  destruct (site8_vals BX A Kc rho a rhoX tp tr md (proj2 Hw)) as (_ & EL & _). cbn zeta in EL.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md (proj2 Hw)) as (HN & _). cbn zeta in HN.
  unfold fx8. apply Forall_cons; [|apply Forall_nil]. cbn [holds]. rewrite EL. cbn [eval]. rewrite u64_lit by lia.
  pose proof (Z.div_lt_upper_bound (bv_unsigned (rw rho 12%positive)) 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)) as NU. clear -NU. lia.
Qed.

Lemma HBL8 : ltac2:(tb__ "0|c|
S14S40S1dS3eQ40M0A1M1S1dS4G1A1S5bS48Vsegs;VJG;VBX;R7R6R5R4A5VCT8;R3R2R1A6S1S52S61S3dG0R5A2A1M2S3dG0S22R4S85Vnx;A1M3A2A2M4A2S1S52S51G4S3dG0S22R4S8aVnx;A1M5A2A2A2S51G2S54S66S3dG0S23R6PcA2A2A1Z8A2A2A2S1S4S1cA1M6S0S4S9S9S1eS1eA2S1eA2M7A1M8S4eS1cG7S57R1A4M9S4eS1cG7S57S7S1cS89Vnx;A1S7S1cS83Vnx;A1S7S1cS6eVnx;A1S8S1cA1A3A3A3A4A3S4fS1cS1cS31S25R7R1A2SbS3bS3bS3dG0S22R7G3A2A2MaS51GaS3dG0S22R7G5A2A2A2A4A2Lo;R2A3MbF_;Fl;G6S0G8G9S4eS1cG7S57VPX;A4A3GbF_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. pose proof (SPA_facts_hold segs _ rhoX CT8 tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct (site8_vals BX A Kc rho a rhoX tp tr md HJ) as (EB & EL & _). cbn zeta in EB, EL. rewrite EB, EL.
  destruct (site7_vals BX A Kc rho a rhoX tp tr md HJ) as (_ & _ & EBR & EL3b & V512 & VM). cbn zeta in EBR, EL3b, V512, VM.
  destruct (site3_vals BX A Kc rho a rhoX tp tr md HJ) as (EB3 & _ & EL3).
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (EB1 & EL1 & BB1).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.

  assert (NV8 : nv / 8 <= secneeded nv / 8 - 512).
  { rewrite ENS. replace (round_up nv 8 + 4096) with (round_up nv 8 + 512 * 8) by lia. rewrite Z.div_add by lia.
    pose proof (Z.div_le_mono nv (round_up nv 8) 8 ltac:(lia) ltac:(clear -R8B; lia)). lia. }
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP.
  split; [lia|]. split; [clear -NV8 VM; lia|]. split.
  - intros l2 EE. destruct l2 as [|o [|o' [|o'' [|o3 l2']]]]; try (cbn in EE; discriminate EE).
    assert (Es : skel o = skel (O_3b nx)) by (cbn in EE; congruence). assert (Es' : skel o' = skel (O_3 nx)) by (cbn in EE; congruence).
    assert (Es'' : skel o'' = skel (O_1 nx)) by (cbn in EE; congruence).
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + rewrite (obj_range_skel rhoX o (O_3b nx) Es). unfold O_3b, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
      rewrite soff_lit_small by lia. rewrite EBR. unfold ranges_disjoint. cbn [fst snd]. right. right. right. clear -NV8. lia.
    + rewrite (obj_range_skel rhoX o' (O_3 nx) Es'). unfold O_3, L3. rewrite obj_range_mk by lia. rewrite EB3.
      unfold ranges_disjoint. cbn [fst snd]. right. right. left. lia.
    + rewrite (obj_range_skel rhoX o'' (O_1 nx) Es''). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
      unfold ranges_disjoint. cbn [fst snd]. right. right. left. lia.
  - intros l2 EE. pose proof (run_band BX A Kc rho a rhoX tp tr md HJ) as RB.
    assert (HFX : Forall (holds rhoX) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HF p (FX8 p Hp))).
    pose proof (PX_noband A Kc rho a rhoX tp tr md HJ HFX l2 EE) as NB.
    eapply Forall_impl; [|exact NB]. intros o Ho. cbn beta in Ho. unfold ranges_disjoint. cbn [fst snd].
    set (lo := Sh (bv_unsigned a) + 768) in *.
    destruct (Z_lt_le_dec (fst (obj_range rhoX o)) (snd (obj_range rhoX o))) as [NE|]; [|left; lia].
    destruct (Z_le_gt_dec (snd (obj_range rhoX o)) lo) as [|G1]; [right; right; left; lia|].
    destruct (Z_le_gt_dec (lo + nv / 8) (fst (obj_range rhoX o))) as [|G2]; [right; right; right; lia|].
    exfalso. set (x := Z.max (fst (obj_range rhoX o)) lo).
    pose proof (Ho x ltac:(unfold x; lia)) as NBx. pose proof (RB x ltac:(unfold x, lo in *; fold nv; clear -NV8 VM G1 G2 NE NP; lia)) as Bx.
    unfold noband in NBx. clear -NBx Bx. lia.
Qed.

Theorem sec_g45 : ltac2:(tb__ "0|5|
S5bOF_;S14S40S1dS3eQ40M0A1M1S5cS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3S3bS1S52S61S3dG0R7A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R8PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S2aR9S3fG0R2A2A2SeG3A1A3A1F_;Fz;S1dS4G1A1M4S5aVsegs;RdS48Vsegs;VJG;VBX;RcRbRaR9A5VD8;R2R1A5R8A4FtpY;FrhoY;S1dG4S5aVsegs;ReS48Vsegs;VJG;VBX;RdRcRbRaA5VD7;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCONT rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  assert (SL : slink (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }
  eapply triple_conseq; [intros w Hw; exact (RSU8 A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [MSENT] GS [U8] [ET8] (JG BX A Kc rho a) ok Q tX Hokf HST Cert8); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  apply (ms_step nW st tmax nx Hnx NXG BX BXg ET8 CT8 CO8 T8 (B4 nx) (a2e8 nx) [O_3b nx; O_3 nx; O_1 nx] PX Pre_mszA Pret_mz Posts_mszA s8 R8 eq_refl
           (fun ok0 Jx r0 t0 Ho Hs => memsetZ_sumA ok0 Jx Ho Hs r0 t0) eq_refl RS8 HBL8 SK8 FC8 XC8 HCO8 WCO8 He8 Hchk8 HT8 FBC8 FBT8 NXC8
           ok A Kc rho rho a tX Q HW HUS HKc Hokl SL).
  intros rhoY tpY. exact (HCONT rhoY tpY).
Qed.
End G45.

Lemma site9_vals : ltac2:(tb__ "0|3|
S14S14F_;S14S40S1dS3eQ40M0A1M1S1dS4G1A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S3dG0S23R7PcA2A2S3bS3dG0R7A2S3bS1S0S3bS3dG0S22R7S98Vnx;A1A2A2S51S51R1Z1800A2S55R2S56R2Z8M2A2A2A2A3S0S3bS3dG0S22R7S8cVnx;A1A2A2S51S51S61R1A1Z300A2S54R2G2A2A2A3A2Tua;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  destruct (site8_vals BX A Kc rho a r tp tr md HJ) as (_ & _ & EN8 & _). cbn zeta in EN8.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  pose proof (urange a) as Ra. cbn zeta in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *. unfold IMG_HI in IMG.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  assert (A8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(lia)) as X. unfold PG in AL. rewrite AL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by lia. apply Z_mod_mult. }
  pose proof (Z.div_mod ua 8 ltac:(lia)) as DA. rewrite A8, Z.add_0_r in DA.
  pose proof (Z.div_mod nv 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  assert (EU : bv_unsigned (eval r (UE9 nx)) = ua + 6144 + (nv - nv mod 8)).
  { unfold UE9. cbn [eval] in EN8 |- *. rewrite add_val, EN8, add_val, Enx, !u64_lit by lia. fold ua.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP SMB; lia). apply Z.mod_small. clear -Ra TOP SMB HN MN LB. lia. }
  split; [exact EU|].
  unfold BP9. cbn [eval]. cbn [eval] in EU. rewrite add_val, srl_val, EU, !u64_lit by lia. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  replace (ua + 6144 + (nv - nv mod 8)) with ((ua / 8 + 768 + nv / 8) * 8) by (clear -DA DN; lia). rewrite Z.div_mul by lia.
  pose proof (Z.div_pos ua 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_lt_upper_bound ua 8 (2 ^ 61) ltac:(lia) ltac:(lia)) as DU.
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)) as NU.
  unfold Sh, SHADOW_OFF. rewrite Z.mod_small by (clear -DP DU NP NU; lia). lia.
Qed.

Lemma F_g9_hold : ltac2:(tb__ "0|1|
S14S14F_;S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1S8fVnx;A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  destruct (site9_vals BX A Kc rho a r tp tr md HJ) as (EU & _). cbn zeta in EU.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & TOP & ENS & EMS & _). cbn zeta in *.
  pose proof (urange a) as Ra. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  unfold F_g9. apply Forall_cons; [|apply Forall_nil]. cbn [holds branch_taken]. intros H. unfold bv_ltu in H. apply Z.ltb_lt in H.
  rewrite EU in H. cbn [eval] in H. rewrite u64_lit in H by lia. clear -H Ra TOP SMB HN MN LB. lia.
Qed.

Lemma nmod8_of_par : ltac2:(tb__ "0|3|
S14S14F_;S14S40S1dS3eQ40M0A1M1S1dS4G1A1S4S59A1S58VJG;R9R8R7R6R5R4R3R2R1A9S1S24R5S88A2S0S3bS56S3dG0S23R8PcA2A2Z8A2Z0A3M2F_;S24R5S2eS88A1A2S2G2A1F_;A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  destruct (site8_vals BX A Kc rho a r tp tr md HJ) as (_ & _ & EN8 & _). cbn zeta in EN8.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & _).
  assert (EQ : branch_taken BC_EQ (eval r (SVar 12)) (eval r (SAlu ALU_AND (SVar 12) (SLit M48))) = (bv_unsigned (rw rho 12%positive) mod 8 =? 0)).
  { cbn [branch_taken]. unfold bv_eqb. rewrite EN8. cbn [eval]. rewrite E12.
    pose proof (Z.mod_pos_bound (bv_unsigned (rw rho 12%positive)) 8 ltac:(lia)) as MN.
    destruct (Z.eqb_spec (bv_unsigned (rw rho 12%positive) mod 8) 0) as [E|NE]; [apply Z.eqb_eq; lia | apply Z.eqb_neq; lia]. }
  unfold F_par. cbn [holds]. rewrite EQ. split.
  - intros H. apply Z.eqb_eq in H. exact H.
  - intros H E. apply H. apply Z.eqb_eq. exact E.
Qed.

Section G46.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S14S0S16S15VBX;R1A1A1S15R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S14S40S1dS3eQ40A1M0S1dS4G0A1S4S59A1S58VJG;VBX;R8R7R6R5R4R3R2R1A9S4fS1fS24R5A1VFXP;A3S4S1cA1S0S4S9S9S1eS1eA2S1eA2M1A1S4eS1cG1S57R1A4S4eS1cG1S57VPX;A4A3S4fS1cS1cS79S25R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D8 U9 E9f E9p CO9p E9q : axst).
Hypothesis WU9 : ltac2:(tb__ "0|0|
S0S5S27S34VU9;A1A1S6A3").
Hypothesis DU9 : ltac2:(tb__ "0|4|
S0SaS9S4S9S1eS1eA2M0A1M1S4S1fA1M2A2M3A1S6bS34VD8;A1S34VU9;A1A2ScG3SbG1G2S8G0A1S8fVnx;A1A4A2A3").
Hypothesis NXU9 : ltac2:(tb__ "0|0|
S0S3cS20S34VU9;A1A1S20S34VD8;A1A1A3").
Hypothesis HU9 : ltac2:(tb__ "0|0|
S0S35S37VD8;S34VU9;A1A2VU9;A3").
Hypothesis Cert9 : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bS77S7S3bS97S8S3bA1A3A3VGS;S7S35VU9;S8S35A1M0A3S7S35VE9f;S7S35VE9p;G0A3A3A6S6A3").
Hypothesis SK9 : ltac2:(tb__ "0|1|
S0S4S9S9S1eS1eA2S1eA2M0A1S4eS1cG0S57S2bS34VE9p;A1A1A4S4eS1cG0S57SdS1cS7S1cS96Vnx;A1S7S1cS89Vnx;A1S7S1cS83Vnx;A1S7S1cS6eVnx;A1S8S1cA1A3A3A3A3SdS1cS7aVnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC9 : ltac2:(tb__ "0|0|
S5eS1fSdS1fS47VW;Vst;A2S46S45A1A3S21S34VE9p;A1A1A3").
Hypothesis FX9 : ltac2:(tb__ "0|0|
S5eS1fVFXP;S21S34VE9p;A1A1A3").
Hypothesis FP9 : ltac2:(tb__ "0|0|
S5fS1fS2eS88A1S21S34VE9p;A1A1A3").
Hypothesis XC9 : ax_X E9p = [].
Hypothesis HCO9 : ltac2:(tb__ "0|0|
S0S35S70VE9p;S30S8cVnx;A1S28Z0A1S28Z1A1S8S2fA1S2cA5A2VCO9p;A3").
Hypothesis WCO9 : ltac2:(tb__ "0|0|
S0S5S27S34VCO9p;A1A1S6A3").
Hypothesis Cert9q : ltac2:(tb__ "0|1|
S0S5S6cS76Ufa0S7S3bS77S8S3bA1A3VGS;S7S35VCO9p;S8S35A1M0A3S7S35VE9q;G0A3A6S6A3").

Lemma RSU9 : ltac2:(tb__ "0|1|
S14S40S1dS3eQ40A1M0S1dS4G0A1S5bS48Vsegs;VJG;VBX;R7R6R5R4A5VD8;R3R2R1A6S48Vsegs;VJG;VBX;R8R7R6R5A5VU9;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HU9.
  eapply SPA_restate; [exact WU9 | exact DU9 | exact NXU9 | constructor | | exact Hw].
  exact (F_g9_hold BX A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.

Lemma prep9 : ltac2:(tb__ "0|4|
S14S40S1dS3eQ40M0A1M1S1dS4G1A1S5bS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S3bS1S52S61S3dG0R6A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R7PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S2aR8S3fG0R2A2A2SeG3A1A3A1F_;Fz;S48Vsegs;VJG;VBX;R9R8R7R6A5VE9p;R5R4R3A6S48Vsegs;VJG;VBX;RaR9R8R7A5VCO9p;R6R5R4A6F_;F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW RUNDEF Hw. pose proof (SPA_facts_hold segs _ rhoX E9p tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct (site9_vals BX A Kc rho a rhoX tp tr md HJ) as (_ & EB). cbn zeta in EB.
  destruct (site8_vals BX A Kc rho a rhoX tp tr md HJ) as (EB4 & EL4 & _). cbn zeta in EB4, EL4.
  destruct (site7_vals BX A Kc rho a rhoX tp tr md HJ) as (_ & _ & EBR & EL3b & V512 & VM). cbn zeta in EBR, EL3b, V512, VM.
  destruct (site3_vals BX A Kc rho a rhoX tp tr md HJ) as (EB3 & _ & EL3).
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (EB1 & EL1 & BB1).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  pose proof (proj2 (nmod8_of_par BX A Kc rho a rhoX tp tr md HJ) (proj1 (Forall_forall _ _) HF _ FP9)) as NM8.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.

  assert (NV8 : secneeded nv / 8 = nv / 8 + 1 + 512).
  { rewrite ENS. replace (round_up nv 8 + 4096) with (round_up nv 8 + 512 * 8) by lia. rewrite Z.div_add by lia. f_equal.
    unfold round_up. rewrite Z.div_mul by lia. pose proof (Z.div_mod nv 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
    symmetry. apply Z.div_unique with (nv mod 8 - 1); lia. }
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP.
  assert (SL : slink (bv_unsigned a) (secmapsize nv) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }
  assert (E1 : bv_unsigned (eval rhoX (SLit 1)) = 1) by (cbn [eval]; apply u64_lit; lia).
  rewrite <- HCO9. apply (carve_piece nW st tmax nx Hnx BX E9p (BP9 nx) (SLit 1) A Kc rho rho a rhoX tp _ SL Hw); [rewrite HCO9; exact WCO9 | exact XC9 | | |].
  - rewrite EB. clear -NP. lia.
  - rewrite EB, E1. fold nv. clear -NV8 VM. lia.
  - rewrite EB, E1. pose proof (run_band BX A Kc rho a rhoX tp tr md HJ) as RB.
    apply (pieces_disjoint nW st tmax nx Hnx BX BXg E9p [O_4z nx; O_3b nx; O_3 nx; O_1 nx] PX A Kc rho a rhoX tp _ _ _ HW Hw SK9 FC9).
    + apply (RB (Sh (bv_unsigned a) + 768 + nv / 8)). fold nv. clear -NV8 VM NP. lia.
    + pose proof (RB (Sh (bv_unsigned a) + 768 + nv / 8) ltac:(fold nv; clear -NV8 VM NP; lia)). lia.
    + intros l2 EE. destruct l2 as [|o [|o' [|o'' [|o3 [|o4 l2']]]]]; try (cbn in EE; discriminate EE).
      assert (Es : skel o = skel (O_4z nx)) by (cbn in EE; congruence). assert (Es' : skel o' = skel (O_3b nx)) by (cbn in EE; congruence).
      assert (Es'' : skel o'' = skel (O_3 nx)) by (cbn in EE; congruence). assert (Es3 : skel o3 = skel (O_1 nx)) by (cbn in EE; congruence).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * rewrite (obj_range_skel rhoX o (O_4z nx) Es). unfold O_4z, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
        rewrite soff_lit_small by lia. rewrite (soff_of_val rhoX (a2e8 nx) _ EL4) by (pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)); fold nv; lia). rewrite EB4.
        unfold ranges_disjoint. cbn [fst snd]. right. right. left. fold nv. lia.
      * rewrite (obj_range_skel rhoX o' (O_3b nx) Es'). unfold O_3b, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
        rewrite soff_lit_small by lia. rewrite EBR. unfold ranges_disjoint. cbn [fst snd]. right. right. right. clear -NV8. lia.
      * rewrite (obj_range_skel rhoX o'' (O_3 nx) Es''). unfold O_3, L3. rewrite obj_range_mk by lia. rewrite EB3.
        unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -NP. lia.
      * rewrite (obj_range_skel rhoX o3 (O_1 nx) Es3). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
        unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -NP. lia.
    + intros l2 EE.
      assert (HFX : Forall (holds rhoX) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HF p (FX9 p Hp))).
      pose proof (PX_noband A Kc rho a rhoX tp tr md HJ HFX l2 EE) as NB.
      eapply Forall_impl; [|exact NB]. intros o Ho. cbn beta in Ho. unfold ranges_disjoint. cbn [fst snd].
      set (lo := Sh (bv_unsigned a) + 768 + nv / 8) in *.
      destruct (Z_lt_le_dec (fst (obj_range rhoX o)) (snd (obj_range rhoX o))) as [NE|]; [|left; lia].
      destruct (Z_le_gt_dec (snd (obj_range rhoX o)) lo) as [|G1]; [right; right; left; lia|].
      destruct (Z_le_gt_dec (lo + 1) (fst (obj_range rhoX o))) as [|G2]; [right; right; right; lia|].
      exfalso. pose proof (Ho lo ltac:(lia)) as NBx. pose proof (RB lo ltac:(unfold lo; fold nv; clear -NV8 VM NP; lia)) as Bx.
      unfold noband in NBx. clear -NBx Bx. lia.
Qed.

Theorem sec_g46 : ltac2:(tb__ "0|5|
S5bOF_;S14S40S1dS3eQ40M0A1M1S5cS0S43Vst;S42A3S0S4S41A1VW;S8S41A1A3F_;S67VW;Vst;A2S44R6A1S4aVsegs;R9S49R7A1A3S3bS1S52S61S3dG0R7A2A1M2R1A2S53R1S51G2S54S66S3dG0S23R8PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S2aR9S3fG0R2A2A2SeG3A1A3A1F_;Fz;S1dS4G1A1M4S5aVsegs;RdS48Vsegs;VJG;VBX;RcRbRaR9A5VE9f;R2R1A5R8A4FtpY;FrhoY;S1dG4S5aVsegs;ReS48Vsegs;VJG;VBX;RdRcRbRaA5VE9q;R2R1A5R9A4FtpY;FrhoY;S1dG4S5aVsegs;RfS48Vsegs;VJG;VBX;ReRdRcRbA5VD8;R2R1A5RaA4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCF HCQ rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  eapply triple_conseq; [intros w Hw; exact (RSU9 A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [MSENT; PGST] GS [U9] [E9f; E9p] (JG BX A Kc rho a) ok Q tX Hokf HST Cert9); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[<-|[]]].
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HCF rE tX)].
  - eapply triple_conseq; [intros w Hw; exact (prep9 A Kc rho a rE tX w HW RUNDEF Hw) | intros w Hw; right; exact Hw |].
    apply (cfg_soundA segs 4000%nat [MSENT] GS [CO9p] [E9q] (JG BX A Kc rho a) ok Q tX Hokf HST Cert9q); [|left; reflexivity].
    intros E rE' HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HCQ rE' tX)].
Qed.
End G46.

Section G47.
Variable BX : AA -> AA.
Variables (E S9a S9b T9 : axst) (iM : nat) (s9 : wsub) (R9 : list sobj).
Let D9 : axst := ltac2:(tb__ "0|0|
S7eVT9;S21S34VS9b;A1A1A2").
Hypothesis HS9a : ltac2:(tb__ "0|0|
S0S35S94VE;ViM;S28Z1800A1A3VS9a;A3").
Hypothesis HS9b : ltac2:(tb__ "0|0|
S0S35S94VS9a;S12ViM;A1S28Z2800A1A3VS9b;A3").
Hypothesis He9 : ltac2:(tb__ "0|1|
S0SaS4S1cA1M0A1S80VS9b;S69Vs9;A3ScG0VR9;A2A3").
Hypothesis Hchk9 : ltac2:(tb__ "0|0|
S0S5S7fVS9b;S69Vs9;VR9;S4eS36S35S38S6aA4A5S6A3").
Hypothesis HT9 : ltac2:(tb__ "0|0|
S0S35S81Vs9;S69S72VS9b;VR9;A5VT9;A3").
Hypothesis FBC9 : ltac2:(tb__ "0|1|
S0S5S5dS1fS26S20S34VS9b;A1M0A1A1S21G0A1A3S6A3").
Hypothesis FBT9 : ltac2:(tb__ "0|0|
S0S5S5dS1fS26S20S34VT9;A1A1A1S21S34VS9b;A1A1A3S6A3").
Hypothesis NXC9 : ltac2:(tb__ "0|0|
S0S5S7dVGS;S20S34VS9b;A1A1A2S6A3").

Lemma prepF : ltac2:(tb__ "0|1|
S14S40S1dS3eQ40A1M0S1dS4G0A1S5bS48Vsegs;VJG;VBX;R7R6R5R4A5VE;R3R2R1A6S48Vsegs;VJG;VBX;R8R7R6R5A5VS9b;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw.
  assert (Ha : SPA segs (JG BX A Kc rho a) S9a rhoX tp w).
  { rewrite <- HS9a. unfold osplit. destruct (split_obj_at (ax_S E) iM (SLit 6144)) as [S'|] eqn:E1; [|exact Hw]. eapply (SPA_split segs); [exact E1 | exact Hw]. }
  rewrite <- HS9b. unfold osplit. destruct (split_obj_at (ax_S S9a) (S iM) (SLit 10240)) as [S'|] eqn:E2; [|exact Ha]. eapply (SPA_split segs); [exact E2 | exact Ha].
Qed.

Theorem sec_g47 : ltac2:(tb__ "0|2|
S5bOF_;S14S40S1dS3eQ40A1M0S5cS67VW;Vst;A2S44R5A1S4aVsegs;R8S49R6A1A3S1dS4G0A1M1S5aVsegs;RbS48Vsegs;VJG;VBX;RaR9R8R7A5VD9;R2R1A5R6A4FtpY;FrhoY;S1dG1S5aVsegs;RcS48Vsegs;VJG;VBX;RbRaR9R8A5VE;R2R1A5R7A4FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HUS HKc Hokl HCONT rX tX.
  eapply triple_conseq; [intros w Hw; exact (prepF A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  exact (ms_call BX S9b T9 Pre_memsetA Pret_ms Posts_memsetA s9 R9 eq_refl (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl
           He9 Hchk9 HT9 FBC9 FBT9 NXC9 ok A Kc rho a tX Q HUS HKc Hokl HCONT rX).
Qed.
End G47.
End SEC6.
End SpineMallocSec6.

(* [comment removed for export] *)
Module SpineMallocSec4IEL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "None"; "length"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IL"; "CO3bc"; "G3c"; "L3ac"; "U2c"; "T4ac"; "T4bc"; "X3a3c"; "X3ac"; "X3bc"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSecE2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Lemma NXEU2_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S29A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEG3_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S27A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEL3a_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S28A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXECOb_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S26A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert3_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ7050cS0SbZ40f5cS2SbA1A3A3VGS0;S0S8S9S29Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2dG0G1A3S0S8S9S2eG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x7050c; 0x40f5c] GS0 [mkVNA U2c 1 (SLit 0)] [mkVNA X3ac 0 (SLit 0); mkVNA X3bc 0 (SLit 0)] [SpineMallocSec4IL.run3]); [exact SpineMallocSec4IL.run3__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert3a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ40f5cS2SbA1A3VGS0;S0S8S9S27Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2cG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x40f5c] GS0 [mkVNA G3c 1 (SLit 0)] [mkVNA X3a3c 0 (SLit 0)] [SpineMallocSec4IL.run3a]); [exact SpineMallocSec4IL.run3a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c480S2SbA1A3VGS0;S0S8S9S28Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2fG0G1A3S0S8S9S30G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c480] GS0 [mkVNA L3ac 1 (SLit 0)] [mkVNA Y4a0c 0 (SLit 0); mkVNA Y4a1c 0 (SLit 0)] [SpineMallocSec4IL.run4a]); [exact SpineMallocSec4IL.run4a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4b_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c480S2SbA1A3VGS0;S0S8S9S26Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S31G0G1A3S0S8S9S32G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c480] GS0 [mkVNA CO3bc 1 (SLit 0)] [mkVNA Y4b0c 0 (SLit 0); mkVNA Y4b1c 0 (SLit 0)] [SpineMallocSec4IL.run4b]); [exact SpineMallocSec4IL.run4b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g3_0l : ltac2:(tb__ "0|8|
S1dS3aS10S18Q40M0A1M1S1bOF_;S25VW;Vst;A2S3bR5A1S34S33S37S5S20S1fR7A1A2A1Z1A2S38Z2Z14A2A2SbSeS36S39S17G0R6A2A1M2R1A2S34R1S33G2S35S24S17G0S13R7PcM3A2A2A1Z8A2A2A2A2SfSdS7S18Q8A1M4A1S14R8S19G0R2A2A2S4G4A1A3A1F_;Fz;S10S10S6G1A1M5S3dS1eRcA1S17G0R9A2S24S17G0S13RaG3A2A2A1RaR3A5S1aScS1cScS21U0M6Vst;S22S1dS3cR1A1LX;RdRcR4RaA8S2aR3R2A5R9A3F_;FtY;FrY;Frho'';S10G5S1aScS1cScS21G6Vst;S22S1dR1LX;M7RcRbRaR9A8S2bR2R1A5R8A3FtY;FrY;S10G5S1aScS1cScS21G6Vst;S22G7RdRcRbRaA8S23R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HUS HKc Hok RUNDEF HCa HCb rX tX.
  eapply esec_g3 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (AX := (fun X : AA => X)) (AXg := (fun X => eq_refl)) (AXs := (fun X => eq_refl))
    (AXp := (fun X => eq_refl)) (AXb := (fun X => eq_refl)) (D2 := D2c) (U2 := U2c) (X3a := X3ac) (X3b := X3bc) (CS3 := CS3c) (G3 := G3c) (X3a3 := X3a3c) (L3a := L3ac)
    (L3b := L3bc) (CO3b := CO3bc) (T4a := T4ac) (T4b := T4bc) (Y4a0 := Y4a0c) (Y4a1 := Y4a1c) (Y4b0 := Y4b0c) (Y4b1 := Y4b1c) (sLa := sLa) (sLb := sLb) (s4a0 := s4a0)
    (s4a1 := s4a1) (s4b0 := s4b0) (s4b1 := s4b1) (WU2 := WU2_0) (DU2 := DU2_0) (NXU2 := NXU2_0) (HU2 := HU2_0) (Cert3 := Cert3_0) (WC3 := WC3_0) (DC3 := DC3_0)
    (NXC3 := NXC3_0) (HC3 := HC3_0) (FX3a := FX3a_0) (IC3 := IC3_0) (R17 := R17_0) (R10 := R10_0) (BBw := BBw_0) (R11 := R11_0) (R12 := R12_0) (R13 := R13_0)
    (R14 := R14_0) (R15 := R15_0) (XC3 := XC3_0) (SK3 := SK3_0) (FC3 := FC3_0) (FCS3 := FCS3_0) (NXS3 := NXS3_0) (HG3 := HG3_0) (Cert3a := Cert3a_0) (ELa := ELa_0)
    (IDa := IDa_0) (GLa := GLa_0) (FBLa := FBLa_0) (HL3a := HL3a_0) (ELb := ELb_0) (IDb := IDb_0) (GLb := GLb_0) (FBLb := FBLb_0) (HL3b := HL3b_0) (HCOb := HCOb_0)
    (WCOb := WCOb_0) (XCb := XCb_0) (SKb := SKb_0) (FCb := FCb_0) (FXb := FXb_0) (Cert4a := Cert4a_0) (E4a0 := E4a0_0) (I4a0 := I4a0_0) (E4a1 := E4a1_0) (I4a1 := I4a1_0)
    (Cert4b := Cert4b_0) (E4b0 := E4b0_0) (I4b0 := I4b0_0) (E4b1 := E4b1_0) (I4b1 := I4b1_0) (NXEU2 := NXEU2_0) (NXEG3 := NXEG3_0) (NXEL3a := NXEL3a_0)
    (NXECOb := NXECOb_0) (ECert3 := ECert3_0) (ECert3a := ECert3a_0) (ECert4a := ECert4a_0) (ECert4b := ECert4b_0);
    [intros E; discriminate E | exact HUS | exact HKc | exact Hok | exact RUNDEF | exact HCa | exact HCb].
Qed.
End INST.
End SpineMallocSec4IEL.

(* [comment removed for export] *)
Module SpineMallocSec4IE.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "None"; "length"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4I"; "CO3bc"; "G3c"; "L3ac"; "U2c"; "T4ac"; "T4bc"; "X3a3c"; "X3ac"; "X3bc"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSecE2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Lemma NXEU2_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S29A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEG3_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S27A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEL3a_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S28A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXECOb_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S26A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert3_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ7050cS0SbZ40f5cS2SbA1A3A3VGS0;S0S8S9S29Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2dG0G1A3S0S8S9S2eG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x7050c; 0x40f5c] GS0 [mkVNA U2c 1 (SLit 0)] [mkVNA X3ac 0 (SLit 0); mkVNA X3bc 0 (SLit 0)] [SpineMallocSec4I.run3]); [exact SpineMallocSec4I.run3__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert3a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ40f5cS2SbA1A3VGS0;S0S8S9S27Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2cG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x40f5c] GS0 [mkVNA G3c 1 (SLit 0)] [mkVNA X3a3c 0 (SLit 0)] [SpineMallocSec4I.run3a]); [exact SpineMallocSec4I.run3a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c480S2SbA1A3VGS0;S0S8S9S28Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2fG0G1A3S0S8S9S30G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c480] GS0 [mkVNA L3ac 1 (SLit 0)] [mkVNA Y4a0c 0 (SLit 0); mkVNA Y4a1c 0 (SLit 0)] [SpineMallocSec4I.run4a]); [exact SpineMallocSec4I.run4a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4b_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c480S2SbA1A3VGS0;S0S8S9S26Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S31G0G1A3S0S8S9S32G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c480] GS0 [mkVNA CO3bc 1 (SLit 0)] [mkVNA Y4b0c 0 (SLit 0); mkVNA Y4b1c 0 (SLit 0)] [SpineMallocSec4I.run4b]); [exact SpineMallocSec4I.run4b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g3_0h : ltac2:(tb__ "0|8|
S1dS3aS10S18Q40M0A1M1S1bOF_;S25VW;Vst;A2S3bR5A1S34S33S37S5S20S1fR7A1A2A1Z1A2S38Z2Z14A2A2SbSeS36S39S17G0R6A2A1M2R1A2S34R1S33G2S35S24S17G0S13R7PcM3A2A2A1Z8A2A2A2A2SfSdS7S18Q8A1M4A1S14R8S19G0R2A2A2S4G4A1A3A1F_;Fz;S10S10S6G1A1M5S3dS1eRcA1S17G0R9A2S24S17G0S13RaG3A2A2A1RaR3A5S1aScS1cScS21U0M6Vst;S22S1dS3cR1A1LX;RdRcR4RaA8S2aR3R2A5R9A3F_;FtY;FrY;Frho'';S10G5S1aScS1cScS21G6Vst;S22S1dR1LX;M7RcRbRaR9A8S2bR2R1A5R8A3FtY;FrY;S10G5S1aScS1cScS21G6Vst;S22G7RdRcRbRaA8S23R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HUS HKc Hok RUNDEF HCa HCb rX tX.
  eapply esec_g3 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (AX := (fun X : AA => X)) (AXg := (fun X => eq_refl)) (AXs := (fun X => eq_refl))
    (AXp := (fun X => eq_refl)) (AXb := (fun X => eq_refl)) (D2 := D2c) (U2 := U2c) (X3a := X3ac) (X3b := X3bc) (CS3 := CS3c) (G3 := G3c) (X3a3 := X3a3c) (L3a := L3ac)
    (L3b := L3bc) (CO3b := CO3bc) (T4a := T4ac) (T4b := T4bc) (Y4a0 := Y4a0c) (Y4a1 := Y4a1c) (Y4b0 := Y4b0c) (Y4b1 := Y4b1c) (sLa := sLa) (sLb := sLb) (s4a0 := s4a0)
    (s4a1 := s4a1) (s4b0 := s4b0) (s4b1 := s4b1) (WU2 := WU2_0) (DU2 := DU2_0) (NXU2 := NXU2_0) (HU2 := HU2_0) (Cert3 := Cert3_0) (WC3 := WC3_0) (DC3 := DC3_0)
    (NXC3 := NXC3_0) (HC3 := HC3_0) (FX3a := FX3a_0) (IC3 := IC3_0) (R17 := R17_0) (R10 := R10_0) (BBw := BBw_0) (R11 := R11_0) (R12 := R12_0) (R13 := R13_0)
    (R14 := R14_0) (R15 := R15_0) (XC3 := XC3_0) (SK3 := SK3_0) (FC3 := FC3_0) (FCS3 := FCS3_0) (NXS3 := NXS3_0) (HG3 := HG3_0) (Cert3a := Cert3a_0) (ELa := ELa_0)
    (IDa := IDa_0) (GLa := GLa_0) (FBLa := FBLa_0) (HL3a := HL3a_0) (ELb := ELb_0) (IDb := IDb_0) (GLb := GLb_0) (FBLb := FBLb_0) (HL3b := HL3b_0) (HCOb := HCOb_0)
    (WCOb := WCOb_0) (XCb := XCb_0) (SKb := SKb_0) (FCb := FCb_0) (FXb := FXb_0) (Cert4a := Cert4a_0) (E4a0 := E4a0_0) (I4a0 := I4a0_0) (E4a1 := E4a1_0) (I4a1 := I4a1_0)
    (Cert4b := Cert4b_0) (E4b0 := E4b0_0) (I4b0 := I4b0_0) (E4b1 := E4b1_0) (I4b1 := I4b1_0) (NXEU2 := NXEU2_0) (NXEG3 := NXEG3_0) (NXEL3a := NXEL3a_0)
    (NXECOb := NXECOb_0) (ECert3 := ECert3_0) (ECert3a := ECert3a_0) (ECert4a := ECert4a_0) (ECert4b := ECert4b_0);
    [intros E; discriminate E | exact HUS | exact HKc | exact Hok | exact RUNDEF | exact HCa | exact HCb].
Qed.
End INST.
End SpineMallocSec4IE.

(* [comment removed for export] *)
Module SpineMallocSec4IELW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "None"; "length"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4ILW2"; "CO3bc"; "G3c"; "L3ac"; "U2c"; "T4ac"; "T4bc"; "X3a3c"; "X3ac"; "X3bc"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4ILW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSecE2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Lemma NXEU2_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S29A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEG3_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S27A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEL3a_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S28A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXECOb_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S26A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert3_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ7050cS0SbZ40f5cS2SbA1A3A3VGS0;S0S8S9S29Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2dG0G1A3S0S8S9S2eG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x7050c; 0x40f5c] GS0 [mkVNA U2c 1 (SLit 0)] [mkVNA X3ac 0 (SLit 0); mkVNA X3bc 0 (SLit 0)] [SpineMallocSec4ILW2.run3]); [exact SpineMallocSec4ILW2.run3__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert3a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ40f5cS2SbA1A3VGS0;S0S8S9S27Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2cG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x40f5c] GS0 [mkVNA G3c 1 (SLit 0)] [mkVNA X3a3c 0 (SLit 0)] [SpineMallocSec4ILW2.run3a]); [exact SpineMallocSec4ILW2.run3a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c480S2SbA1A3VGS0;S0S8S9S28Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2fG0G1A3S0S8S9S30G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c480] GS0 [mkVNA L3ac 1 (SLit 0)] [mkVNA Y4a0c 0 (SLit 0); mkVNA Y4a1c 0 (SLit 0)] [SpineMallocSec4ILW2.run4a]); [exact SpineMallocSec4ILW2.run4a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4b_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c480S2SbA1A3VGS0;S0S8S9S26Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S31G0G1A3S0S8S9S32G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c480] GS0 [mkVNA CO3bc 1 (SLit 0)] [mkVNA Y4b0c 0 (SLit 0); mkVNA Y4b1c 0 (SLit 0)] [SpineMallocSec4ILW2.run4b]); [exact SpineMallocSec4ILW2.run4b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g3_2l : ltac2:(tb__ "0|8|
S1dS3aS10S18Q40M0A1M1S1bOF_;S25VW;Vst;A2S3bR5A1S34S33S37S5S20S1fR7A1A2A1Z1A2S38Z2Z14A2A2SbSeS36S39S17G0R6A2A1M2R1A2S34R1S33G2S35S24S17G0S13R7PcM3A2A2A1Z8A2A2A2A2SfSdS7S18Q8A1M4A1S14R8S19G0R2A2A2S4G4A1A3A1F_;Fz;S10S10S6G1A1M5S3dS1eRcA1S17G0R9A2S24S17G0S13RaG3A2A2A1RaR3A5S1aScS1cScS21U2M6Vst;S22S1dS3cR1A1LX;RdRcR4RaA8S2aR3R2A5R9A3F_;FtY;FrY;Frho'';S10G5S1aScS1cScS21G6Vst;S22S1dR1LX;M7RcRbRaR9A8S2bR2R1A5R8A3FtY;FrY;S10G5S1aScS1cScS21G6Vst;S22G7RdRcRbRaA8S23R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HUS HKc Hok RUNDEF HCa HCb rX tX.
  eapply esec_g3 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (AX := (fun X : AA => X)) (AXg := (fun X => eq_refl)) (AXs := (fun X => eq_refl))
    (AXp := (fun X => eq_refl)) (AXb := (fun X => eq_refl)) (D2 := D2c) (U2 := U2c) (X3a := X3ac) (X3b := X3bc) (CS3 := CS3c) (G3 := G3c) (X3a3 := X3a3c) (L3a := L3ac)
    (L3b := L3bc) (CO3b := CO3bc) (T4a := T4ac) (T4b := T4bc) (Y4a0 := Y4a0c) (Y4a1 := Y4a1c) (Y4b0 := Y4b0c) (Y4b1 := Y4b1c) (sLa := sLa) (sLb := sLb) (s4a0 := s4a0)
    (s4a1 := s4a1) (s4b0 := s4b0) (s4b1 := s4b1) (WU2 := WU2_0) (DU2 := DU2_0) (NXU2 := NXU2_0) (HU2 := HU2_0) (Cert3 := Cert3_0) (WC3 := WC3_0) (DC3 := DC3_0)
    (NXC3 := NXC3_0) (HC3 := HC3_0) (FX3a := FX3a_0) (IC3 := IC3_0) (R17 := R17_0) (R10 := R10_0) (BBw := BBw_0) (R11 := R11_0) (R12 := R12_0) (R13 := R13_0)
    (R14 := R14_0) (R15 := R15_0) (XC3 := XC3_0) (SK3 := SK3_0) (FC3 := FC3_0) (FCS3 := FCS3_0) (NXS3 := NXS3_0) (HG3 := HG3_0) (Cert3a := Cert3a_0) (ELa := ELa_0)
    (IDa := IDa_0) (GLa := GLa_0) (FBLa := FBLa_0) (HL3a := HL3a_0) (ELb := ELb_0) (IDb := IDb_0) (GLb := GLb_0) (FBLb := FBLb_0) (HL3b := HL3b_0) (HCOb := HCOb_0)
    (WCOb := WCOb_0) (XCb := XCb_0) (SKb := SKb_0) (FCb := FCb_0) (FXb := FXb_0) (Cert4a := Cert4a_0) (E4a0 := E4a0_0) (I4a0 := I4a0_0) (E4a1 := E4a1_0) (I4a1 := I4a1_0)
    (Cert4b := Cert4b_0) (E4b0 := E4b0_0) (I4b0 := I4b0_0) (E4b1 := E4b1_0) (I4b1 := I4b1_0) (NXEU2 := NXEU2_0) (NXEG3 := NXEG3_0) (NXEL3a := NXEL3a_0)
    (NXECOb := NXECOb_0) (ECert3 := ECert3_0) (ECert3a := ECert3a_0) (ECert4a := ECert4a_0) (ECert4b := ECert4b_0);
    [intros E; discriminate E | exact HUS | exact HKc | exact Hok | exact RUNDEF | exact HCa | exact HCb].
Qed.
End INST.
End SpineMallocSec4IELW2.

