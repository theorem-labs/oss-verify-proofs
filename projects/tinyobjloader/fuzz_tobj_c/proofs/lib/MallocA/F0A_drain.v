(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "proj2"; "proj1"; "not"; "or"; "ex"; "False"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "nil"; "cons"; "prod"; "app"; "pair"; "false"; "Some"; "option"; "nat"; "fst"; "orb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "sobj"; "SLit"; "SAlu"; "ss_facts"; "ss_next"; "sprop_below"; "valuation"; "rw"; "ss_objs"; "sprop_eqb"; "sv_eqb"; "rl"; "rm"; "holds"; "ss_lenient"; "SPBranch"; "SPNot"; "obj_range"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "in_ranges"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "ax_setS"; "leafA"; "entailsA"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "In"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "PreQ3"; "PostQ3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "import_okPA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "Wcan"; "chain_pre"; "free_depth"; "F_depth"; "AE_A"; "L_free"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "top_high"; "V_DEPTH"; "mem_keptA"; "J_free_preT"; "Pre_freeI"; "tp_ok"; "ulink"; "unwind_objs"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "qbatch"; "aa_geom"; "aa_live"; "aa_cache_inited"; "aa_q_thread"; "budget_bound"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_frames"; "budget_ok_free"; "aa_internal_inited"; "ageom"; "cls_kept_freeA"; "topG"; "ag_ctx"; "ag_spacebeg"; "ag_thread"; "cs_allocated_user"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "rq_okb"; "qchkb"; "F_cne"; "drain_sum"; "drain_sumE"; "qchkb_sound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "coveredb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone"; "rng_below"; "same_rng"; "winpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kSpaceSize"; "kQuarantineMin"; "kQuarantineBatchSize"; "kUserSpaceSize"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "opp"; "lt"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "liftKA"; "smatchA"; "stableA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "qcond"; "j_min"; "junkF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.DR.SITE"; "JC"; "site_factsQ"; "JX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "AInvQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "qbounded"; "JQ3"; "JLQ3"; "qpost"; "cls_of"; "q_pure"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "isnil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "depot_onlyKf"; "JF"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "RETF"; "FUELF"; "leaves_at"; "qvar"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "maskv"; "restrictv"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "PostsQ3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qsize"; "AInvA"; "IA_BEG"; "IA_END"; "fs_footb"; "fs_inv"; "geom_ok"; "inv3"; "live_sep"; "primary_repr"; "secondary_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.DR"; "JC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "AInvB"; "IMG_F"; "freeA"; "freeQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "QG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymSoundW SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA CompleteA EntailA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_rebuildW.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition F_cne : sprop := ltac2:(tb__ "0|0|
S2aS29S3fS1bS8aSdcZa0A2A1S1cS3eS19P97A1S1bZ50A1A3A3A1").

Definition drain_sum (ok : world -> Prop) (Kc : KcA) : Prop := ltac2:(tb__ "0|1|
S62S20SaS4aQ40A1A1S4S0SaS63A1S67R3A1SbS63A1A3A1S0S8S66R4A1S9A3Sa6R5A1S89S68R6A1Sa3A2S99S8fVok;S90S8fSa7S8fSa4VKc;A1M0R7A3S40R6R5A5S45S8fSceR6R5SbfG0R7A2A5A4F_;F_;F_;F_;Ftp;Frho;FA;").
Definition drain_sumE (Kc : KcA) : Prop := ltac2:(tb__ "0|1|
S62S20SaS4aQ40A1A1S4S0SaS63A1S67R3A1SbS63A1A3A1S0S8S66R4A1S9A3Sa6R5A1S89S68R6A1Sa3A2S98S8fS90S8fSa7S8fSa4VKc;A1M0R7A3S40R6R5A5S45S8fSceR6R5SbfG0R7A2A5A3F_;F_;F_;F_;Ftp;Frho;FA;").

Lemma budget_depot : ltac2:(tb__ "0|0|
S62S62S6dR2A1SafR3R2A2S89S68R3A1Sa3A2F_;F_;FA';FA;").
Proof.
  intros A A' HB (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EV & EKm & EKf).
  unfold budget_ok_free, limit_ok_free in HB. unfold budget_bound. rewrite EV, EKm, EKf. exact HB.
Qed.
Lemma entry_budget : ltac2:(tb__ "0|0|
SaS5fA1S61S62S55S20SaS4aQ40A1A1S97S90S8fS5cSc4S8fA1R7R6R5R4A5S5dS52R7R6A3R3R2R1A6S6dR6A1F_;Fw;Ftp;Frho;FKc;FA;Fst;FW;").
Proof. intros W st A Kc rho tp w [_ HJ]. destruct HJ as (_ & _ & _ & _ & _ & HB & _). exact HB. Qed.

Definition rq_okb (nW : nat) (o : sobj) : bool := ltac2:(tb__ "0|0|
S15S84Vo;A1S3aS1aS83Vo;A1S60S4eVnW;A1A1A3A2").

Definition qchkb (nW : nat) (Cd Pq TQ : axst) (sQ : wsub) (RQ : list sobj) : bool := ltac2:(tb__ "0|c|
S39S8S8R1Lb;ScS8SaeSdS17S17A2M0S34VCd;A1A2ScS8SaeG0S34VTQ;A1A2ScS8S76S42S1eS33VCd;A1M1A1M2A2ScS8S39S18S1fG2A1S1dG1A1M3A3ScS8S39S18S1fS1eS33S43VsQ;S40VPq;VCd;VRQ;A5A1A1A1G3A3ScS8S24S2dVsQ;PaM4A2S1cS3eS19G4A1S1bN8a0A1A3A2ScS8S24S2dVsQ;PfM5A2S1cS3eS19G5A1S1bZ8a0A1A3A2ScS8S24S2dVsQ;P18M6A2S19G6A1A2ScS8S24S2dVsQ;P97M7A2S19G7A1A2ScS8S24S2dVsQ;P98M8A2S19G8A1A2ScS8S24S2dVsQ;P9bM9A2S19G9A1MaA2ScS8S24S2dVsQ;P9cA2S1cS3eGaS1bS85A1A3A2ScS8S39S1aS79VnW;A1VRQ;A3ScS8S39S1aS82S42A1VRQ;A3ScS8S39S18S18S3aS18S23R1A1G3A3Lf;SeS18S4fS4eVnW;A1A1S51S50A1A3A3ScS8SaeS1aS7fS33S40A1S33VPq;A1A2A2ScS8SaeG0S34VPq;A1A2ScS8S81S1dS33VTQ;A1MbA1VRQ;S22GbA1A3SbS8A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma qchkb_sound : ltac2:(tb__ "0|f|
S13S35S35S35S31SaS1aA1M0S0S8S7aR6R5R4R3R2R1A6S9A3S1S0SaSdS17S17A2M1A1M2S34R6A1SbG1A1M3A3S1S0G2S34R4A1G3A3S1S0S8S76S42S1eS33R6A1M4A1M5A2S9A3S1S0S8S39S18S1fG5A1S1dG4A1M6A3S9A3S1S0S8S39S18S1fS1eS33S43R3S40R5R6R2A5A1A1A1G6A3S9A3S1S0S17S2dR3PaM7A2S1cS3eS19G7A1S1bN8a0A1A3A3S1S0S17S2dR3PfM8A2S1cS3eS19G8A1S1bZ8a0A1A3A3S1S0S17S2dR3P18M9A2S19G9A1A3S1S0S17S2dR3P97MaA2S19GaA1A3S1S0S17S2dR3P98MbA2S19GbA1A3S1S0S17S2dR3P9bMcA2S19GcA1MdA3S1S0S17S2dR3P9cA2S1cS3eGdS1bS85A1A3A3S1S0S8S39S1aS79R7A1R2A3S9A3S1S0S8S39S1aS82S42A1R2A3S9A3S1S0S8S39S18S18S3aS18S23R1A1S1dS33R7A1A1A3Lf;SeS18S4fS4eR7A1A1S51S50A1A3A3S9A3S1S0G0S7fS33S40A1S33R5A1A2SbS1aA1A3S1S0G2S34R5A1G3A3S0S8S81S1dS33R4A1MeA1R2S22GeA1A3S9A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2F_;FRQ;FsQ;FTQ;FPq;FCd;FnW;").
Proof.
  intros nW Cd Pq TQ sQ RQ H. unfold qchkb in H. cbn [forallb] in H.
  apply andb_prop in H as [H1 H]. apply andb_prop in H as [H2 H]. apply andb_prop in H as [H3 H]. apply andb_prop in H as [H4 H].
  apply andb_prop in H as [H5 H]. apply andb_prop in H as [H6 H]. apply andb_prop in H as [H7 H]. apply andb_prop in H as [H8 H].
  apply andb_prop in H as [H9 H]. apply andb_prop in H as [H10 H]. apply andb_prop in H as [H11 H]. apply andb_prop in H as [H12 H].
  apply andb_prop in H as [H13 H]. apply andb_prop in H as [H14 H]. apply andb_prop in H as [H15 H]. apply andb_prop in H as [H16 H].
  apply andb_prop in H as [H17 H]. apply andb_prop in H as [H18 _].
  apply isnil_sound in H1, H2, H16, H17. apply sv_eqb_sound in H6, H7, H8, H9, H10, H11, H12.
  repeat split; assumption.
Qed.

Lemma rq_top : ltac2:(tb__ "0|1|
S13S62S20S1aS3cS59R4R3A2S89S4dQ40S21R4S5aA2A2S8bS50A1A2Sc1S18S27R5A1S4fS4eR7A1A1A3S0S8S79R8R5A2S9A3S1S89S14S3cS3cS2bR7R6A2M0A3R5A2S8cR5S16S3cS3cG0A3A2A2S89S71S64R9A1A1R6A2F_;F_;F_;F_;F_;Fa;Fo;FrhoE;FA;FnW;").
Proof.
  intros nW A rhoE o a HTOP HDEP HCH Hok Ha. unfold rq_okb in Hok. apply Bool.orb_prop in Hok as [Hok|Hok].
  - unfold winpb in Hok. destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in Hok.
    destruct ob as [| v | | | | | | ]; try discriminate. destruct v as [v|v|]; try discriminate. do 3 (destruct v as [v|v|]; try discriminate).
    destruct olo as [lo| | | | | | | ]; try discriminate. destruct ohi as [hi| | | | | | | ]; try discriminate.
    apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2]. apply Z.leb_le in H1, H2, H3. unfold free_depth in *.
    rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. unfold top_high in HTOP. lia.
  - apply existsb_exists in Hok as (o' & Ho' & Hs). rewrite (same_rng_range rhoE o o' Hs) in Ha.
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
    destruct o' as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in L1, L2, L3. subst olo ohi. rewrite obj_range_mk in Ha by lia. cbn [fst snd] in Ha.
    unfold top_high in HTOP. unfold free_depth in HDEP. lia.
Qed.

Lemma qsize_freeQ : ltac2:(tb__ "0|1|
Sb5S62S3cS3cS9cR4R3A2S89Z0R2A2S1S4S0SaS63A1Sd7R6R5R4R3A4M0SbS63A1A3A1S89Sc3G0A1S8aS8aSc3S67R5A1A1R3A2S87A2A2A2F_;F_;Fn;Fp;FA;Fq;").
Proof.
  intros q A p n QC Hn. unfold freeQ, kQuarantineBatchSize. destruct q; cbn zeta.
  - destruct QC as [HNE _]. split; [intros E; apply app_eq_nil in E as [_ E]; discriminate|].
    rewrite F0A_rebuild.qsize_app. rewrite (F0A_rebuild.qsize_removelast_last _ HNE). unfold qsize at 2. cbn [fold_right qb_size]. lia.
  - destruct QC as [HE _]. split; [discriminate|]. rewrite HE. unfold qsize. cbn [fold_right qb_size]. unfold kQuarantineBatchSize. lia.
  - split; [intros E; apply app_eq_nil in E as [_ E]; discriminate|].
    rewrite F0A_rebuild.qsize_app. unfold qsize at 2. cbn [fold_right qb_size]. unfold kQuarantineBatchSize. lia.
Qed.

Section DR.
Variable nW : nat. Variable q : qvar.
Let st : ustop := UStopLe.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S3cSbaVCST;R1A2S4SdbR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Variables (Cd TQ TQr : axst) (sQ : wsub) (RQ : list sobj).
Hypothesis HEQ : ltac2:(tb__ "0|1|
S0S12SaS1aA1M0A1S48VCd;S40VsQ;A3S11G0VRQ;A2A3").
Hypothesis HCK : ltac2:(tb__ "0|0|
S0S8S47VCd;S40VsQ;VRQ;ScS35S41ScS35SbeSbS35A1A3A3A5S9A3").
Hypothesis HTQ : ltac2:(tb__ "0|0|
S0S35VTQ;SadS43VsQ;S40S41VCd;VRQ;A5S1dS33VCd;A1A1A2A3").
Hypothesis HTQr : ltac2:(tb__ "0|0|
S0S35VTQr;SadS43VsQ;S40SbeVCd;VRQ;A5S1dS33VCd;A1A1A2A3").
Hypothesis QCHK : ltac2:(tb__ "0|0|
S0S8S7aVnW;VCd;S41VTQ;VsQ;VRQ;A6S9A3").
Hypothesis QCHKr : ltac2:(tb__ "0|0|
S0S8S7aVnW;VCd;SbeVTQr;VsQ;VRQ;A6S9A3").
Let PARTS := qchkb_sound nW Cd PostQ3 TQ sQ RQ QCHK.
Let XXC : ax_X Cd = [] := proj1 PARTS.
Let NXC : Pos.leb GW (ss_next (ax_S Cd)) = true := proj1 (proj2 (proj2 PARTS)).
Let FBX : forallb (sprop_below (ss_next (ax_S Cd))) (ss_facts (ax_S Cd)) = true := proj1 (proj2 (proj2 (proj2 PARTS))).
Let WG10 : wsub_get sQ 10 = SAlu ALU_ADD (SVar 10) (SLit (-2208)) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))).
Let WG15 : wsub_get sQ 15 = SAlu ALU_ADD (SVar 15) (SLit 2208) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))).
Let WG24 : wsub_get sQ 24 = SVar 24 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))).
Let WG151 : wsub_get sQ 151 = SVar 151 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))).
Let WG152 : wsub_get sQ 152 = SVar 152 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))))).
Let WG155 : wsub_get sQ 155 = SVar 155 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))).
Let WG156 : wsub_get sQ 156 = SAlu ALU_ADD (SVar 155) (SLit kSpaceSize) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))))))).
Let RQOK : forallb (rq_okb nW) RQ = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))))).
Let RQWF : forallb (rng_below GW) RQ = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))))))))).
Let FCH : forallb (fun f => existsb (sprop_eqb f) (ss_facts (ax_S Cd))) (chain_pre W ++ F_depth free_depth) = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))))))).

Variables (Xf2 XM2 XR2 : axst) (XEX2 : list axform) (sX2 : wsub) (l7 : list leafA).
Hypothesis NX7 : ltac2:(tb__ "0|1|
S1S0S8S28S33VTQ;A1M0A1S10A3S0S8S76S42S1eG0A1A2S9A3A2").
Hypothesis RUN7 : ltac2:(tb__ "0|0|
S0SaS37A1Sd0Sb3ScS3cSb2SbS3cA1A3VTQ;A3Vl7;A3").
Hypothesis L7 : ltac2:(tb__ "0|0|
S1S0S8Sb4Vl7;ScS3cSb2SbS3cA1A3A2S9A3S0S35ScfU0Vl7;A2VXf2;A3A2").

Variable l7r : list leafA.
Hypothesis NX7r : ltac2:(tb__ "0|1|
S1S0S8S28S33VTQr;A1M0A1S10A3S0S8S76S42S1eG0A1A2S9A3A2").
Hypothesis RUN7r : ltac2:(tb__ "0|0|
S0SaS37A1Sd0Sb3ScS3cSb2SbS3cA1A3VTQr;A3Vl7r;A3").
Hypothesis L7r : ltac2:(tb__ "0|0|
S1S0S8Sb4Vl7r;ScS3cSb2SbS3cA1A3A2S9A3S0S35ScfU0Vl7r;A2VXf2;A3A2").
Hypothesis AXE2 : ltac2:(tb__ "0|0|
S0S12S35A1Sc2VXf2;VXEX2;A2S11S35VXM2;A2A3").
Hypothesis WXR2 : ltac2:(tb__ "0|0|
S0S8S2cS33VXR2;A1A1S9A3").
Hypothesis DXR2 : ltac2:(tb__ "0|4|
S0S12SdSaSdS17S17A2M0A1M1SaS18A1M2A2M3A1Sd1S33VXM2;A1S33VXR2;A1A2S11G3SfG1G2ScG0SfS17S17S1bSb8A1S19P18A1A4SbG0A1A3SbS18A1A4A2A3").
Hypothesis NXR2 : ltac2:(tb__ "0|0|
S0S3dS1eS33VXR2;A1A1S1eS33VXM2;A1A1A3").
Hypothesis EQR2 : ltac2:(tb__ "0|0|
S0S35S36VXM2;S33VXR2;A1A2VXR2;A3").
Hypothesis ENT2 : ltac2:(tb__ "0|0|
S0S8S38VXR2;S53S52VW;Vst;A3VsX2;A3S9A3").
Hypothesis SID2 : ltac2:(tb__ "0|0|
S0S8S32VsX2;S9aA2S9A3").

Section SITE.
Variables (A A2 : AA) (Kc : KcA) (rho rho1 : valuation) (l1 l2 : list (Z * Z)) (p n : Z).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HRIG : ltac2:(tb__ "0|3|
S1S0S4aQ40M0A1M1S21Vrho1;P97A2S4cG0S74S64VA;A1M2A1A2A3S1S0G1S21Vrho1;P98A2S4cG0S72G2A1A2A3S0G1S21Vrho1;P9bA2S4cG0S73G2A1A2A3A2A2").

Definition JC : jpredA := ltac2:(tb__ "0|4|
S20SaS4aQ40A1M0A1SaS96A1S95S1Sd4S8eS8dZ2Z30A2Z1M1A2VA2;R4R3R1A5S1S1S0SaSdS3cS3cA2M2A1M3S65VA;A1SeG2Vl1;ScG2SfS3cS3cVp;Vn;A4Vl2;A3A3A3S1S0G3S65VA2;A1SeG2Vl1;Vl2;A3A3S1S0G3S6cVA2;A1S6cVA;A1A3S1S0S3cS6bVA2;A1S6bVA;A1A3S1S0S3cS6aVA2;A1S6aVA;A1A3S1S0S3cS69VA2;A1S8aS69VA;A1G1A2A3S1S0S6fS64VA2;A1S64VA;A1A3S70VA;VA2;A2A2A2A2A2A2A2A2S1S5bVCST;VXGL;VA;VA2;S26Vrho;A1S26R4A1A6S1VKc;R2R1A2S1S3dS77R1S42A2S0G0S21R6R2A2S21Vrho1;R2A2A3F_;Fi;S1S3dS0SaS4aQ8A1A1S25R5R1A2S25Vrho1;R1A2A3Fl;S1S5eVA2;R4A2S59VA2;R4A2A2A2A2A2A2A2A2Lmd;Ltr;Ltpx;Lr;").

Definition site_factsQ (rhoE : valuation) : Prop := ltac2:(tb__ "0|1|
S1S1S89S8bS8dZ2Z28A2A1S4dQ40S21VrhoE;S5aA2A2M0A2S89G0S8bS50A1A2A2Sc1S18S27VrhoE;A1S4fVW;A1A3A2").
Lemma dr_facts : ltac2:(tb__ "0|0|
S20SaS4aQ40A1A1S97S90Vsegs;Sa0VCd;R3R2R1A6Sa1R4A1F_;Fw;Ftp;FrhoE;").
Proof.
  intros rhoE tp w Hw. destruct w as [tr [ms md]].
  pose proof (proj1 Hw) as (Hsm & _). unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (FIN : forall f, In f (chain_pre W ++ F_depth free_depth) -> holds rhoE f).
  { intros f Hf. pose proof (proj1 (forallb_forall _ _) FCH f Hf) as X. apply existsb_exists in X as (g & Hg & E). apply sprop_eqb_sound in E. subst g.
    exact (proj1 (Forall_forall _ _) HFa f Hg). }
  split.
  - assert (D1 : holds rhoE (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))) by (apply FIN; apply in_or_app; right; left; reflexivity).
    assert (D2 : holds rhoE (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply FIN; apply in_or_app; right; right; left; reflexivity).
    cbn [holds eval branch_taken] in D1, D2. unfold bv_lts in D1, D2. apply negb_true_iff in D1, D2. apply Z.ltb_ge in D1, D2.
    change (bv_signed (Z_to_bv 64 (- free_depth))) with (- free_depth) in D1. change (bv_signed (Z_to_bv 64 (- 2 ^ 40))) with (- 2 ^ 40) in D2. lia.
  - apply Forall_forall. intros f Hf. apply FIN. apply in_or_app. left. exact Hf.
Qed.

Lemma dr_RQ_top : ltac2:(tb__ "0|1|
S20Sa1R1A1S59VA2;R2A2S4aQ40M0A1S30R4VRQ;R1A3S89S71S64VA2;A1A1S4bG0R2A2A2F_;Fa;F_;F_;FrhoE;").
Proof.
  intros rhoE (Hdep & Hch) Htop a (o & Ho & Hoa).
  exact (rq_top nW A2 rhoE o (bv_unsigned a) Htop (proj2 Hdep) Hch (proj1 (forallb_forall _ _) RQOK o Ho) Hoa).
Qed.

Lemma AInvQ_parts : ltac2:(tb__ "0|5|
S62S20SaS4aQ40A1A1S95Sa5R4R3R2R1A4S1Sc9S64R5A1M0A1S1ScaR5A1S1SabR5A1S1S3cS1S89Z1R1A2S89R1Z1eA2A2S1S89Z0S75SaaR7R2A2A1M1A2S89G1S88A2A2F_;Fc;S1ScbR5A1S1SccSbbSc7G0A1M2SbdS8fS26R4A1A2M3A2M4R5A2S1ScdG4R5A2Sc8SbcG2G3A2R5A2A2A2A2A2A2A2A2F_;Fmd;Ftpx;Fr;FAx;").
Proof.
  intros Ax r tpx md (HG & _ & HF & HRest & _ & HI3 & _). cbn zeta in HRest, HF. destruct HRest as (R1 & _ & R3 & R4 & (R5 & _) & _).
  split; [exact HG|]. split; [exact HI3|]. split; [exact R5|]. split; [|exact (conj R1 (conj R3 (conj R4 HF)))].
  intros c Hc. destruct R3 as (_ & _ & _ & P4). pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
  destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold SegQ_wf2.cls_of, kUserMapSize in *. lia.
Qed.

Lemma dr_entry : ltac2:(tb__ "0|0|
S20SaS4aQ40A1A1SaS96A1SacS95Sa1R5A1Sa0R6R5R4R2A4Sa7S8fSa4VKc;A1VA2;S2fS2eR7VRQ;S9fR3R6R4A3A3VsQ;A2R6R5R3A7F_;F_;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md SF (HB & HP & HKEPT & HK & HRW & HRL & Htp & Htop).
  destruct HP as (_ & _ & _ & _ & _ & _ & EG & _).
  destruct (AInvB_Q _ A2 rhoE tp md HB) as (HAQ & HQM & QB1 & QB2).
  destruct (AInvQ_parts A2 rhoE tp md HAQ) as (HG & HI3 & HQP & HAU & _ & _ & HSR & _).
  pose proof SF as (Hdep & _). unfold free_depth in Hdep.
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A2)) as TG.
  assert (AV : forall z, z < topG (aa_geom A2) -> view segsA (rm (rho_sub (rho_absorb rhoE RQ (vms md tp ms0)) sQ)) z = view segsA (rm rhoE) z).
  { intros z Hz. apply view_agree. intros Hr. apply rm_absorb_out. intros Hin.
    pose proof (dr_RQ_top rhoE SF Htop _ Hin) as X. rewrite u64_lit in X by exact Hr. lia. }
  split.
  - split; [exact (AInvQ_frame_top A2 rhoE _ tp md HAQ AV)|]. split; [exact HK|]. split; [|split].
    + unfold tp_ok in *. cbn [rw rho_sub]. rewrite WG24. cbn [eval rho_absorb rw]. exact Htp.
    + unfold top_high in *. unfold V_DEPTH in *. cbn [rw rho_sub]. rewrite WG10, WG15, !eval_absorb.
      assert (Em : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2208)))) = bv_unsigned (rw rhoE 10%positive) - 2208).
      { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2208))) with (2 ^ 64 - 2208) by reflexivity.
        rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
      rewrite Em. rewrite signed_add_lit by (cbn [eval]; lia). cbn [eval]. lia.
    + destruct HRIG as (E151 & E152 & E155). unfold rigidQ. rewrite EG. cbn [rw rho_sub]. rewrite WG151, WG152, WG155, WG156. cbn [eval rho_absorb rw].
      rewrite !HRW by (unfold GW; lia). rewrite E151, E152, E155.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. apply add_lit.
  - exact (q_mem_frame_top A2 HG HI3 HQP HAU _ HSR _ _ (fun z Hz => AV z Hz) HQM).
Qed.

Definition JX (A3 : AA) : jpredA := ltac2:(tb__ "0|1|
S20SaS4aQ40A1M0A1SaS96A1S95S1VAInv;VA3;R4R3R1A4S1VKc;R2R1A2S1S5bVCST;VXGL;VA;VA3;S26Vrho;A1S26R4A1A6S1S3dS77R1S42A2S0G0S21R6R2A2S21Vrho1;R2A2A3F_;Fi;S3dS0SaS4aQ8A1A1S25R5R1A2S25Vrho1;R1A2A3Fl;A2A2A2A2Lmd;Ltr;Ltpx;Lr;").

Section POSTQ.
Variables (Pq TQx : axst).
Hypothesis HTQx : ltac2:(tb__ "0|0|
S0S35VTQx;SadS43VsQ;S40VPq;VCd;VRQ;A5S1dS33VCd;A1A1A2A3").
Hypothesis QCHKx : ltac2:(tb__ "0|0|
S0S8S7aVnW;VCd;VPq;VTQx;VsQ;VRQ;A6S9A3").
Let PARTSx := qchkb_sound nW Cd Pq TQx sQ RQ QCHKx.
Let XTQ : ax_X TQx = [] := proj1 (proj2 PARTSx).
Let FBT : forallb (sprop_below (ss_next (ax_S (import_postA sQ PreQ3 Pq Cd RQ)))) (ss_facts (ax_S Cd)) = true := proj1 (proj2 (proj2 (proj2 (proj2 PARTSx)))).
Let NEWO : new_objs (ax_S PreQ3) (ax_S Pq) = [] := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTSx))))))))))))))).
Let XPost : ax_X Pq = [] := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTSx)))))))))))))))).
Let RQcov : coveredb (ss_facts (ax_S TQx)) RQ (ss_objs (ax_S TQx)) = true := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTSx)))))))))))))))).

Lemma dr_exit_ok : ltac2:(tb__ "0|2|
S20SaS4aQ40A1A1M0SaS96A1M1SacS95S20G0G1S95Sa1R9A1Sa0RaR9R8R6A4Sa8S8fSa4VKc;A1VA2;S2fS2eRbVRQ;S9fR7RaR8A3A3VsQ;A2RaR6R5R4R3A9S49RcS9fR8RbR9A3VRQ;VsQ;S40VPq;VCd;R7A8F_;F_;F_;Fmd';Ftr';FtpL;FrhoL;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md rhoL tpL tr' md' SF (HB & _ & _ & _ & _ & _ & _ & Htop) HJL.
  destruct (AInvB_Q _ A2 rhoE tp md HB) as (HAQ & _). destruct (AInvQ_parts A2 rhoE tp md HAQ) as (HG & HI3 & HQP & HAU & _).
  destruct HJL as (A3 & _ & _ & _ & HRM & _).
  split; [split|split].
  - intros a Hin. apply HRM. intros HQ. pose proof HAQ as (_ & _ & _ & HRest & _). cbn zeta in HRest. destruct HRest as (_ & _ & _ & R4 & _).
    pose proof (QRD_lt_top A2 HG HI3 HQP HAU _ R4 _ HQ) as X. pose proof (dr_RQ_top rhoE SF Htop a Hin) as Y. lia.
  - intros o' oR Ho' HoR. rewrite NEWO in Ho'. destruct Ho'.
  - intros r a j oR Hr. rewrite XPost in Hr. destruct Hr.
  - intros r a j Hr. rewrite XXC in Hr. destruct Hr.
Qed.

Lemma dr_exit_core : ltac2:(tb__ "0|2|
S20SaS4aQ40A1A1M0SaS96A1M1SacS95S20G0G1S95Sa1R9A1Sa8S8fSa4VKc;A1VA2;A3S44S2fS2eRbVRQ;S9fR7RaR8A3A3VsQ;A2S20S93Vsegs;RcRbVCd;SfG1Sb6RaSb7R9R8A2A4A5Sa0RdRcRbR9A4R4R3RdR9R8R7R6A6S20S97S80R11S9fRdR10ReA3VRQ;VsQ;S33S40A1S33VCd;A1S33VPq;A1R2RcA9S90Vsegs;S46R8R7R11RdRcA5S43VsQ;S40VPq;VCd;VRQ;A5R3RcR2A6S6S62S62S6S20S20S1Sa9VA2;R2A2S90Vsegs;Sa2R2A1VTQx;R1RfR5A6A2Lrho5;A2LA3;A2F_;F_;Fw';Frho';F_;F_;F_;TrhoC;TJL;F_;Fmd';Ftr';FtpL;FrhoL;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md rhoL tpL tr' md' SF JL rhoC Hsm0 HJ0 _ rho' w' HLK [Hsm' HJ'].
  pose proof HJ0 as (HB & HP & HKEPT & HK & HRW & HRL & Htp & Htop).
  destruct (AInvB_Q _ A2 rhoE tp md HB) as (HAQ & _).
  subst JL.
  destruct (entails_frA_sound segs Cd PreQ3 sQ RQ rhoE tp tr0 ms0 md HEQ Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'.
  destruct HJ' as (A3 & HK3 & HQM3 & HQPOST & HRM & HVW & HRL3 & EtpL & HDEF).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  assert (NXlt : forall i, (i < GW)%positive -> (i < ss_next (ax_S Cd))%positive).
  { intros i Hi. eapply Pos.lt_le_trans; [exact Hi|]. apply Pos.leb_le. exact NXC. }

  assert (HF4 : Forall (holds rho') (ss_facts (ax_S Cd))).
  { pose proof (proj1 Hsm0) as HsmX. pose proof HsmX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts4).
    apply Forall_forall. intros f Hf.
    exact (proj1 (holds_agree_vals _ rhoE rho' f Hag' (proj1 (forallb_forall _ _) FBX f Hf)) (proj1 (Forall_forall _ _) Hfacts4 f Hf)). }
  assert (HT40 : SPA segs (J_ofPA (JLQ3 segsA (K0 Kc) A2) rhoC tp rhoL tpL) TQx rho' tpL (tr2, mkCfg ms2 md2)).
  { rewrite HTQx. apply (SPA_refacts segs); [exact (conj Hsm' HJc) | exact FBT | intros _; exact HF4]. }

  assert (RNG : forall o, In o RQ -> obj_range rho' o = obj_range rhoE o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S Cd))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (rho5 := rho_absorb rho' RQ (ms_with_mem ms2 (rm rhoE))).
  assert (RM5 : forall a, rm rho5 a = if in_ranges_dec rho' RQ a then rm rhoE a else rm rhoL a).
  { intros a. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall a, in_ranges rho' RQ a <-> in_ranges rhoE RQ a).
  { intros a. split; intros (o & Ho & Hoa); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hoa). }
  assert (RTOP : forall a : word, in_ranges rhoE RQ a -> topG (aa_geom A2) <= bv_unsigned a) by exact (dr_RQ_top rhoE SF Htop).
  destruct (AInvQ_parts A2 rhoE tp md HAQ) as (HG2 & HI32 & HQP2 & HAU2 & _).

  assert (KEY : forall a : word, ~ QRD A2 (bv_unsigned a) -> rm rho5 a = rm rhoE a).
  { intros a Ha. rewrite RM5. destruct (in_ranges_dec rho' RQ a) as [Hi|Hn]; [reflexivity|].
    rewrite (HRM a Ha). apply rm_absorb_out. intros Hi. exact (Hn (proj2 (IRE a) Hi)). }
  assert (DEF5 : forall a : word, SHADOW_BAND_LO <= bv_unsigned a < SHADOW_BAND_HI -> rm rhoE a <> None -> rm rho5 a <> None).
  { intros a HBa Hd. rewrite RM5. destruct (in_ranges_dec rho' RQ a) as [Hi|Hn]; [exact Hd|].
    apply (HDEF a HBa). unfold rhoC. cbn [rm rho_sub]. rewrite (rm_absorb_out _ _ _ _ (fun Hi => Hn (proj2 (IRE a) Hi))). exact Hd. }

  pose proof (qpost_geom A2 A3 HQPOST) as EG3.
  pose proof HK3 as (HAQ3 & HKc3 & _).
  destruct (AInvQ_parts A3 rhoL tpL md2 HAQ3) as (HG3 & HI33 & HQP3 & HAU3 & _ & _ & HSR3 & _).
  assert (AV5 : forall z, z < topG (aa_geom A3) -> view segsA (rm rho5) z = view segsA (rm rhoL) z).
  { intros z Hz. apply view_agree. intros Hr. rewrite RM5. destruct (in_ranges_dec rho' RQ (Z_to_bv 64 z)) as [Hi|]; [|reflexivity]. exfalso.
    pose proof (RTOP _ (proj1 (IRE _) Hi)) as X. rewrite u64_lit in X by exact Hr. rewrite EG3 in Hz. lia. }
  assert (HA5 : AInv A3 rho5 tpL md2).
  { destruct HQPOST as (_ & ET3 & _ & _ & EQG3).
    apply (AInvQ_back A3 rho5 tpL md2 (AInvQ_frame_top A3 rhoL rho5 tpL md2 HAQ3 AV5)).
    - exact (q_mem_frame_top A3 HG3 HI33 HQP3 HAU3 _ HSR3 _ _ (fun z Hz => AV5 z Hz) HQM3).
    - rewrite ET3. cbn. unfold kQuarantineCacheMax. lia.
    - exact EQG3. }
  exists A3, rho5. split; [exact HQPOST|].
  assert (HJX5 : JX A3 rho5 tpL tr2 md2).
  { split; [exact HA5|]. split; [exact HKc3|].
    split; [exact (mem_kept_drain CST XGL HCST HXGL HCSTQ A A2 A3 tp md rhoE (rm rho) (rm rho5) HAQ (proj1 HQPOST) KEY DEF5 HKEPT)|].
    split.
    - intros i Hi. unfold rho5. cbn [rw rho_absorb]. rewrite <- (proj1 Hag' i (NXlt i Hi)). exact (HRW i Hi).
    - intros l. unfold rho5. cbn [rl rho_absorb]. rewrite <- (proj2 Hag' l). exact (HRL l). }
  pose proof (proj1 (proj1 HT40)) as HsmT. pose proof HsmT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HfT).
  unfold rho5. apply (SPA_absorb_any segs (J_ofPA (JLQ3 segsA (K0 Kc) A2) rhoC tp rhoL tpL)); [exact XTQ | | exact HT40 | exact HJX5].
  intros o a Ho Ha. exact (coveredb_sound _ _ _ rho' o a HfT RQcov Ho Ha).
Qed.

End POSTQ.

Lemma JX_stable : ltac2:(tb__ "0|0|
S62S3dS78S42R1A2S94Vsegs;R2Sa2R3A1A3F_;Fk;FA3;").
Proof.
  intros A3 k Hk r r' tpx tr md md' Hag Hme (HA & HK & HM & HW & HL). pose proof Hag as (Hw & Hl & Hm).
  assert (Erm : rm r' = rm r) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  split; [|split; [|split; [|split]]].
  - unfold AInv, AInvA in HA |- *. rewrite Erm. exact (AInvA_mat segs A3 r tpx md md' HA Hme).
  - destruct Hme as ((mat' & ->) & _). rewrite <- (with_vm_backing_id md) in HK. exact (Kc_ok_mat Kc tr md _ _ _ _ HKc HK).
  - rewrite Erm. exact HM.
  - intros i Hi. rewrite <- (Hw i ltac:(lia)). exact (HW i Hi).
  - intros l. rewrite <- (Hl l). exact (HL l).
Qed.
Lemma JX_okf : ltac2:(tb__ "0|0|
S97OF_;S62S91Vsegs;R2S92VKc;A1A3S91Vsegs;R3Sa2R2A1A3F_;FA3;Fok;").
Proof. intros ok A3 H r tpx tr ms md msv' (_ & HK & _). exact (H r tpx tr ms md msv' HK). Qed.

Variable tp : list word.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S0S3cS4bQ40S21Vrho;PcA2A2Vp;A3").
Hypothesis Hn13 : ltac2:(tb__ "0|0|
S0S3cS4bQ40S21Vrho;PdA2A2Vn;A3").
Hypothesis HAGW : ltac2:(tb__ "0|0|
S3dS77R1S9aA2S0S4aQ40A1S21Vrho;R2A2S21Vrho1;R2A2A3F_;Fk;").
Hypothesis HAGL : ltac2:(tb__ "0|0|
S3dS0SaS4aQ8A1A1S25Vrho;R1A2S25Vrho1;R1A2A3Fl;").
Hypothesis HTP24 : ltac2:(tb__ "0|0|
S0S3cS4bQ40S21Vrho1;P18A2A2Sb8A3").
Hypothesis HPURE : ltac2:(tb__ "0|2|
S1S0SaSdS3cS3cA2M0A1M1S65VA;A1SeG0Vl1;ScG0SfS3cS3cVp;Vn;A4Vl2;A3A3A3S1S0G1S65VA2;A1SeG0Vl1;Vl2;A3A3S1S0G1S6cVA2;A1S6cVA;A1A3S1S0S3cS6bVA2;A1S6bVA;A1A3S1S0S3cS6aVA2;A1S6aVA;A1A3S1S0S3cS69VA2;A1S8aS69VA;A1Z1A2A3S1S0S6fS64VA2;A1S64VA;A1A3S70VA;VA2;A2A2A2A2A2A2A2A2").

Theorem dr_finish : ltac2:(tb__ "0|1|
S62S20SaS4aQ40A1A1S97Sa9VA2;R4A2S90Vsegs;Sa2R5A1VXf2;R4R3R2A6S45Vsegs;S9aVrho;Vtp;ScSdS35S44A2M0SfS35S44S53S52VW;Vst;A3S54VAInv;VCST;VXGL;VA;VKc;A5A4SbG0A1A3R3A6F_;F_;Fw;FtpL;FrhoX;FA3;").
Proof.
  intros A3 rhoX tpL w HQPOST H. destruct w as [tr [ms md]].
  pose proof (proj2 H) as (HA3 & HK & HM & HW & HL). cbn [w_tr w_cfg cfg_model fst snd] in HA3, HK.
  pose proof (SPA_axforms segs (JX A3) XEX2 rhoX Xf2 XM2 tpL _ AXE2 H) as Ha.
  assert (Hc : SPA segs (JX A3) XR2 rhoX tpL (tr, mkCfg ms md)).
  { rewrite <- EQR2. eapply SPA_restate; [exact WXR2 | exact DXR2 | exact NXR2 | | constructor | exact Ha].
    constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. rewrite u64_lit by (unfold TP_A; clear; lia).
    rewrite (HW 24%positive) by (unfold GW; clear; lia). symmetry. exact HTP24. }
  pose proof (smatchA_entails segs _ _ _ rhoX tpL _ ENT2 (proj1 Hc)) as Hsm4.
  set (rho4 := rho_sub rhoX sX2) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoX k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ SID2 Hk). reflexivity. }
  assert (Erm4 : rm rho4 = rm rhoX) by exact (rm_rho_sub' rhoX sX2).
  exists (L_free AE_A W st), (JL_free AInv CST XGL A Kc), rho4, tpL.
  split; [left; reflexivity|]. split; [|split; [exact Hsm4|]].
  { split.
    - intros k Hk. rewrite (Hlow k Hk), (HW k) by (unfold NF, GW in *; clear -Hk; lia). exact (HAGW k Hk).
    - intros l. unfold rho4. cbn [rl rho_sub]. rewrite (HL l). exact (HAGL l). }
  cbn [w_tr w_cfg cfg_model fst snd]. unfold JL_free. exists A3, l1, l2.
  destruct HPURE as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). destruct HQPOST as (ESB & _ & _ & HFR & _).
  assert (E3 : aa_live A3 = aa_live A2 /\ aa_frames A3 = aa_frames A2 /\ aa_V A3 = aa_V A2 /\ aa_Km A3 = aa_Km A2 /\ aa_Kf A3 = aa_Kf A2 /\ aa_geom A3 = aa_geom A2).
  { unfold same_but_qcs in ESB. rewrite ESB. unfold aa_frames. cbn [aa_live aa_fs_busy aa_V aa_Km aa_Kf aa_geom]. repeat split; reflexivity. }
  destruct E3 as (F1 & F2 & F3 & F4 & F5 & F6).
  split; [unfold AInv, AInvA in HA3 |- *; rewrite Erm4; exact HA3|].
  split; [rewrite Hp12, Hn13; exact P1|].
  split; [rewrite F1; exact P2|]. split; [rewrite F2; exact P3|]. split; [rewrite F3; exact P4|]. split; [rewrite F4; exact P5|].
  split; [rewrite F5; exact P6|]. split; [rewrite F6; exact P7|].
  split; [rewrite Erm4; exact HM|]. split; [exact HK|].
  intros c Hc0 NE Hfr. exact (HFR c (P8 c Hc0 NE Hfr)).
Qed.

Theorem drain_call : ltac2:(tb__ "0|1|
S97OF_;S91Vsegs;R1S92VKc;A1A3S7cR2VKc;A2S4S0SaS63A1S67VA2;A1SbS63A1A3A1S0S8S66VA2;A1S9A3Sa6VA2;A1S89S68VA2;A1Sa3A2S20SaS4aQ40A1A1S99Vsegs;R9S90Vsegs;Sa0VCd;R2R1A5S45Vsegs;S9aVrho;Vtp;ScSdS35S44A2M0SfS35S44S53S52VW;Vst;A3S54VAInv;VCST;VXGL;VA;VKc;A5A4SbG0A1A3A5A4FtpE;FrhoE;F_;F_;F_;F_;F_;F_;Fok;").
Proof.
  intros ok Hokl HDS HT2 HCI2 HQB2 HBD2 rhoE tpE k HgQ w Hw. destruct w as [tr [ms md]].
  pose proof (dr_facts rhoE tpE _ Hw) as SF.
  apply (call_soundPA segs ok JC (JQ3 segsA (K0 Kc) A2) Cd PreQ3 sQ RQ (PostsQ3 (K0 Kc) A2)
           (LQPA segs NF rho tp [(L_free AE_A W st, JL_free AInv CST XGL A Kc)]) rhoE tpE HEQ).
  - change (map fst (PostsQ3 (K0 Kc) A2)) with [PostQ3; PostQ3r]. exact HCK.
  - intros rhoP tp1. exact (HDS A2 rhoP tp1 HT2 HCI2 HQB2 HBD2).
  - intros tr0 ms0 md1 Hsm0 HJ0. exact (dr_entry rhoE tpE tr0 ms0 md1 SF HJ0).
  - intros L JL tr0 ms0 md1 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[EL|[]]]; pose proof (f_equal fst EL) as EL1; pose proof (f_equal snd EL) as EL2; cbn [fst snd] in EL1, EL2; subst L JL; clear EL.
    + split; [exact (dr_exit_ok PostQ3 TQ QCHK rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF HJ0 HJL)|].
      intros rho' HLK n' Hg' w' Hw'.
      destruct (dr_exit_core PostQ3 TQ HTQ QCHK rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A3 & rho5 & HQP & HC5).
      refine (run_cont1 FUELF [RETF] TQ l7 (ss_next (ax_S TQ)) Xf2 (proj1 NX7) eq_refl RUN7 (proj2 L7) RETF (JX A3) ok rho5 tpL
                (LQPA segs NF rho tp [(L_free AE_A W st, JL_free AInv CST XGL A Kc)])
                (leaves_at1 _ _ (proj1 L7)) (JX_okf ok A3 Hokl) (JX_stable A3 _ (proj1 (Pos.leb_le _ _) (proj2 NX7))) _ n' Hg' w' HC5).
      intros rhoX _. eapply triple_conseq; [intros w0 Hw0; exact Hw0 | | apply triple_refl].
      intros w0 Hw0. exact (dr_finish A3 rhoX tpL w0 HQP Hw0).
    + split; [exact (dr_exit_ok PostQ3r TQr QCHKr rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF HJ0 HJL)|].
      intros rho' HLK n' Hg' w' Hw'.
      destruct (dr_exit_core PostQ3r TQr HTQr QCHKr rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A3 & rho5 & HQP & HC5).
      refine (run_cont1 FUELF [RETF] TQr l7r (ss_next (ax_S TQr)) Xf2 (proj1 NX7r) eq_refl RUN7r (proj2 L7r) RETF (JX A3) ok rho5 tpL
                (LQPA segs NF rho tp [(L_free AE_A W st, JL_free AInv CST XGL A Kc)])
                (leaves_at1 _ _ (proj1 L7r)) (JX_okf ok A3 Hokl) (JX_stable A3 _ (proj1 (Pos.leb_le _ _) (proj2 NX7r))) _ n' Hg' w' HC5).
      intros rhoX _. eapply triple_conseq; [intros w0 Hw0; exact Hw0 | | apply triple_refl].
      intros w0 Hw0. exact (dr_finish A3 rhoX tpL w0 HQP Hw0).
  - exact HgQ.
  - exact Hw.
Qed.

Theorem drain_callE : ltac2:(tb__ "0|1|
S7dVKc;A1S4S0SaS63A1S67VA2;A1SbS63A1A3A1S0S8S66VA2;A1S9A3Sa6VA2;A1S89S68VA2;A1Sa3A2S20SaS4aQ40A1A1S98Vsegs;S90Vsegs;Sa0VCd;R2R1A5S45Vsegs;S9aVrho;Vtp;ScSdS35S44A2M0SfS35S44S53S52VW;Vst;A3S54VAInv;VCST;VXGL;VA;VKc;A5A4SbG0A1A3A5A3FtpE;FrhoE;F_;F_;F_;F_;F_;").
Proof.
  intros HDS HT2 HCI2 HQB2 HBD2 rhoE tpE w Hw. destruct w as [tr [ms md]].
  pose proof (dr_facts rhoE tpE _ Hw) as SF.
  apply (call_completePA segs JC (JQ3 segsA (K0 Kc) A2) Cd PreQ3 sQ RQ (PostsQ3 (K0 Kc) A2)
           (LQPA segs NF rho tp [(L_free AE_A W st, JL_free AInv CST XGL A Kc)]) rhoE tpE HEQ).
  - change (map fst (PostsQ3 (K0 Kc) A2)) with [PostQ3; PostQ3r]. exact HCK.
  - intros rhoP tp1. exact (HDS A2 rhoP tp1 HT2 HCI2 HQB2 HBD2).
  - intros tr0 ms0 md1 Hsm0 HJ0. exact (dr_entry rhoE tpE tr0 ms0 md1 SF HJ0).
  - intros L JL tr0 ms0 md1 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[EL|[]]]; pose proof (f_equal fst EL) as EL1; pose proof (f_equal snd EL) as EL2; cbn [fst snd] in EL1, EL2; subst L JL; clear EL.
    + split; [exact (dr_exit_ok PostQ3 TQ QCHK rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF HJ0 HJL)|].
      intros rho' HLK w' Hw'.
      destruct (dr_exit_core PostQ3 TQ HTQ QCHK rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A3 & rho5 & HQP & HC5).
      refine (run_econt1 FUELF [RETF] TQ l7 (ss_next (ax_S TQ)) Xf2 (proj1 NX7) eq_refl RUN7 (proj2 L7) RETF (JX A3) rho5 tpL
                (LQPA segs NF rho tp [(L_free AE_A W st, JL_free AInv CST XGL A Kc)])
                (leaves_at1 _ _ (proj1 L7)) (JX_stable A3 _ (proj1 (Pos.leb_le _ _) (proj2 NX7))) _ w' HC5).
      intros rhoX _. eapply etriple_conseq; [intros w0 Hw0; exact Hw0 | | apply etriple_refl].
      intros w0 Hw0. exact (dr_finish A3 rhoX tpL w0 HQP Hw0).
    + split; [exact (dr_exit_ok PostQ3r TQr QCHKr rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF HJ0 HJL)|].
      intros rho' HLK w' Hw'.
      destruct (dr_exit_core PostQ3r TQr HTQr QCHKr rhoE tpE tr0 ms0 md1 rhoL tpL tr' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A3 & rho5 & HQP & HC5).
      refine (run_econt1 FUELF [RETF] TQr l7r (ss_next (ax_S TQr)) Xf2 (proj1 NX7r) eq_refl RUN7r (proj2 L7r) RETF (JX A3) rho5 tpL
                (LQPA segs NF rho tp [(L_free AE_A W st, JL_free AInv CST XGL A Kc)])
                (leaves_at1 _ _ (proj1 L7r)) (JX_stable A3 _ (proj1 (Pos.leb_le _ _) (proj2 NX7r))) _ w' HC5).
      intros rhoX _. eapply etriple_conseq; [intros w0 Hw0; exact Hw0 | | apply etriple_refl].
      intros w0 Hw0. exact (dr_finish A3 rhoX tpL w0 HQP Hw0).
  - exact Hw.
Qed.
End SITE.

Hypothesis HCSTF : ltac2:(tb__ "0|0|
S3cSbaVCST;R1A2S5SbaSd5R2A2S1S89Sc5R2A2S8cR2Sc6A2A2A2S7F_;F_;Fa;").

Variables (Edr XMd XKd : axst) (KEPTd RESTd : list sobj) (XEXd : list axform).
Hypothesis AXEd : ltac2:(tb__ "0|0|
S0S12S35A1Sc2VEdr;VXEXd;A2S11S35VXMd;A2A3").
Hypothesis OBJSd : ltac2:(tb__ "0|0|
S0SaS1aA1S22S33VXMd;A1A1SeS1aVKEPTd;VRESTd;A3A3").
Hypothesis EQKd : ltac2:(tb__ "0|0|
S0S35S36VXMd;Sd2S33VXMd;A1VKEPTd;A2A2VXKd;A3").
Hypothesis RCLSd : ltac2:(tb__ "0|0|
S0S8Sd9Vq;VRESTd;A2S9A3").
Hypothesis RCIVd : rcivb RESTd = true.
Hypothesis RCELLd : ltac2:(tb__ "0|0|
S0S8Sd8Vq;VRESTd;A2S9A3").
Hypothesis RWRd : rwrb RESTd = true.
Hypothesis RSHPd : ltac2:(tb__ "0|0|
S0S8SdaVq;VRESTd;A2S9A3").
Hypothesis ECd : ltac2:(tb__ "0|0|
S0S35VCd;SadVXKd;SeS18S1dS33VXKd;A1A1ScS18S7bSbS18A1A3A3A2A3").
Hypothesis FBCd : ltac2:(tb__ "0|1|
S0S8S39S18S1fS1eS33VXKd;A1M0A1A1SeS18S1dG0A1ScS18S7bSbS18A1A3A3A3S9A3").

Lemma dr_release : ltac2:(tb__ "0|6|
S62S55S20SaS4aQ40M0A1A1M1S3cS3cS3cS9eS3cOF_;S62S20S20G1SaS96A1M2SacS95SaSdS3cS3cA2M3A1M4G4S56R11A1S0S3cS4bG0S21R11PcA2A2RfA3S0S3cS4bG0S21R12PdA2A2RfA3S3bG3SfS3cS3cR11R10A4S65R15A1M5A3Sb9R12R11A2S0S8S6eR17A1S9A3S9cVq;R18A2Sb1R17S9bR19R17R15R14R13R12A6A2S0S3cS9dR13A1S86A3S3cS5S57VCST;R1cR1A3S58VCST;VXGL;R1cR1A4A2R15R2A1F_;Fa;SafR1cR13A2Sc0R15S9bR1dR1bR19R18R17R16A6R13A3S0G4G5SeG3ReScG3SfS3cS3cR1aR19A4RdA3A3A3S90Vsegs;Sb0VnW;Vst;S10R16R1eR15A6VEdr;R14R13SfG2Sb6R12Sb7R11R10A2A4A6Sd6Vq;R17R10RfR1cR1bA6S62S9bR21R1fR1dR1cR1bR1aA6S20S1S90Vsegs;Sd3R22R2R21R20R1R12R11R1eR1dA9VCd;S2eR17VRESTd;S9fR13R16R14A3A3R16SfG2Sb6R15Sb7R14R13A2A4A6S1S4S0SaS63A1S67R2A1SbS63A1A3A1S1Sa6R2A1S1S0S8S66R2A1S66R22A1A3S0S3cS4bG0S21R1P18A2A2Sb8A3A2A2A2A2Trho1;TA2;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fl2;Fl1;Fmd;Fms;Ftr;FtpE;FrhoE;Frho1';FA';Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv keep A' rho1' rhoE tpE tr ms md l1 l2 HKc Hp12 Hn13 HL HHI Hii QC HR HJMIN HKEEP HDO HLK ELV Hw A2 rho1. subst A2 rho1.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ. pose proof HJ as (HA' & _ & HL' & _).
  pose proof HDO as (EG & EC & ECI & ESEC & EPC & EL & EQT & EQG & EII & EFB & EFH & EV & EKM & EKF).

  assert (QC' : qcond q A').
  { clear -QC EC EQT ECI. unfold qcond, lastq, cache24 in *. rewrite EQT, ECI, EC. exact QC. }
  pose proof HA' as (HG' & _ & _ & HRest' & _). destruct HRest' as (HLS' & _ & _ & _ & HQR' & _). destruct HQR' as (_ & _ & _ & _ & _ & _ & _ & QT8 & QG9 & _).
  assert (Hn0 : 1 <= n /\ n < 2 ^ 47).
  { rewrite <- EL in HL. destruct (HLS' p n HL) as (N1 & N2 & N3 & _). pose proof (topG_range (aa_geom A')) as TG. unfold IMG_HI in N2. lia. }
  destruct (qsize_freeQ q A' p n QC' ltac:(lia)) as [FNE FSZ].
  assert (HQB : qsize (freeQ q A' p n) <= 2 ^ 48 - 1) by (unfold kQuarantineCacheMax, kQuarantineBatchSize in *; lia).
  destruct (f0_released CST XGL HCST HXGL HCSTF nW st q Edr XMd XKd XKd KEPTd RESTd XEXd AXEd OBJSd EQKd eq_refl RCLSd RCIVd RCELLd RWRd RSHPd
              A Kc rho tp p n t jv keep A' rho1' rhoE tpE tr ms md Hp12 Hn13 HL HHI Hii QC HR HJMIN HDO HLK HKEEP Hw (2 ^ 48 - 1) l1 l2 ELV HQB)
    as (Hb & HRB & HRW & HRL & Htp & Htop).
  unfold rebuilt_stmt in HRB. destruct HRB as (HB2 & _ & P1 & P2 & P3 & P4 & P5 & P6 & P7 & HKEPT & HK & P8).
  set (rho3 := rho_absorb rhoE RESTd (vms md tpE ms)) in *.
  assert (HJC : JC A (freeA q A' l1 l2 p n) Kc rho (rhoF_of A rho p n t jv) l1 l2 p n rho3 tpE tr md).
  { split; [exact HB2|]. split; [exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 P8)))))))|].
    split; [exact HKEPT|]. split; [exact HK|]. split; [exact HRW|]. split; [exact HRL|].
    split; [unfold tp_ok in *; exact Htp | unfold top_high in *; exact Htop]. }
  assert (E24 : bv_unsigned (rw (rhoF_of A rho p n t jv) 24%positive) = TP_A).
  { rewrite <- (HRW 24%positive) by (unfold GW; lia). unfold rho3. cbn [rho_absorb rw]. unfold tp_ok in Htp. rewrite Htp.
    destruct (geom_old _ HG') as (_ & _ & _ & G4 & _). rewrite G4. reflexivity. }
  split; [|split; [exact FNE | split; [split; [cbn [aa_q_thread freeA]; lia | exact QG9] | split; [exact ECI | exact E24]]]].

  rewrite ECd. apply (SPA_refacts segs); [exact (conj (proj1 Hb) HJC) | exact FBCd |].
  intros HF. apply Forall_app. split; [exact HF|]. constructor; [|constructor].
  unfold F_cne. cbn [holds eval]. intros E. unfold branch_taken, bv_eqb in E. apply Z.eqb_eq in E.
  assert (E151 : rw rho3 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by (rewrite HRW by (unfold GW; lia); reflexivity).
  rewrite E151, add_lit in E. pose proof (geom_numsS _ HG') as (_ & _ & _ & T1 & T2 & _). pose proof (topG_range (aa_geom A')) as TG.
  pose proof (geom_bands _ HG') as (_ & _ & _ & _ & TI & _). rewrite EG in T1, T2, TI, TG. unfold IMG_LO, IMG_HI in TI.
  rewrite !u64_lit in E by (unfold QG; lia). unfold QG in E. lia.
Qed.

Theorem f0_drain : ltac2:(tb__ "0|3|
S97OF_;S62S55S20SaS4aQ40M0A1A1M1S3cS3cS3cS9eS3cOF_;S56R8A1S91Vsegs;RbS92R9A1A3S7cRcRaA2S6dRcA1S0S3cS4bG0S21RbPcA2A2R9A3S0S3cS4bG0S21RcPdA2A2R9A3S3bSdS3cS3cA2SfS3cS3cRbRaA4S65RfA1A3Sb9RcRbA2S0S8S6eR11A1S9A3S9cVq;R12A2Sb1R11S9bR13R11RfReRdRcA6A2S0S3cS9dRdA1S86A3S3cS5S57VCST;R16R1A3S58VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S62S20S20G1SafR1aR4A2Sc0R13S9bR1bR19R17R16R15R14A6R4A3S99Vsegs;R1dS90Vsegs;Sb0VnW;Vst;S10R6R1bR5A6VEdr;R4R3A5S45Vsegs;S9aR1aR19ScSdS35S44A2M2SfS35S44S53S52VW;Vst;A3S54VAInv;VCST;VXGL;R1cR1bA5A4SbG2A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n t jv keep HKc Hokl HDS HBud Hp12 Hn13 HL HHI Hii QC HR HJMIN HKEEP A' rho1' rhoE tpE HDO HLK k HgQ w Hw.
  destruct w as [tr [ms md]].
  assert (HL' : In (p, n) (aa_live A')) by (destruct HDO as (_ & _ & _ & _ & _ & EL & _); rewrite EL; exact HL).
  destruct (in_split _ _ HL') as (l1 & l2 & ELV).
  destruct (dr_release A Kc rho tp p n t jv keep A' rho1' rhoE tpE tr ms md l1 l2 HKc Hp12 Hn13 HL HHI Hii QC HR HJMIN HKEEP HDO HLK ELV Hw) as (HC & HT2 & HQB2 & ECI2 & E24).
  pose proof (proj2 HC) as (HB2 & HPURE & _).

  assert (HCI2 : aa_cache_inited (freeA q A' l1 l2 p n) = true).
  { destruct HB2 as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & _ & _ & _ & _ & _ & _ & I9). apply I9. intros E. apply app_eq_nil in E as [E _]. exact (HT2 E). }
  destruct (rg_agree _ _ HR) as [HAGW HAGL].
  exact (drain_call A (freeA q A' l1 l2 p n) Kc rho (rhoF_of A rho p n t jv) l1 l2 p n HKc (conj eq_refl (conj eq_refl eq_refl)) tp Hp12 Hn13 HAGW HAGL E24 HPURE
           ok Hokl HDS HT2 HCI2 HQB2 (budget_depot A A' HBud HDO) _ tpE k HgQ _ HC).
Qed.
Theorem ef0_drain : ltac2:(tb__ "0|3|
S62S55S20SaS4aQ40M0A1A1M1S3cS3cS3cS9eS3cOF_;S56R8A1S7dR9A1S6dRbA1S0S3cS4bG0S21RaPcA2A2R8A3S0S3cS4bG0S21RbPdA2A2R8A3S3bSdS3cS3cA2SfS3cS3cRaR9A4S65ReA1A3Sb9RbRaA2S0S8S6eR10A1S9A3S9cVq;R11A2Sb1R10S9bR12R10ReRdRcRbA6A2S0S3cS9dRcA1S86A3S3cS5S57VCST;R15R1A3S58VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S62S20S20G1SafR19R4A2Sc0R12S9bR1aR18R16R15R14R13A6R4A3S98Vsegs;S90Vsegs;Sb0VnW;Vst;S10R6R1aR5A6VEdr;R4R3A5S45Vsegs;S9aR19R18ScSdS35S44A2M2SfS35S44S53S52VW;Vst;A3S54VAInv;VCST;VXGL;R1bR1aA5A4SbG2A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n t jv keep HKc HDS HBud Hp12 Hn13 HL HHI Hii QC HR HJMIN HKEEP A' rho1' rhoE tpE HDO HLK w Hw.
  destruct w as [tr [ms md]].
  assert (HL' : In (p, n) (aa_live A')) by (destruct HDO as (_ & _ & _ & _ & _ & EL & _); rewrite EL; exact HL).
  destruct (in_split _ _ HL') as (l1 & l2 & ELV).
  destruct (dr_release A Kc rho tp p n t jv keep A' rho1' rhoE tpE tr ms md l1 l2 HKc Hp12 Hn13 HL HHI Hii QC HR HJMIN HKEEP HDO HLK ELV Hw) as (HC & HT2 & HQB2 & ECI2 & E24).
  pose proof (proj2 HC) as (HB2 & HPURE & _).

  assert (HCI2 : aa_cache_inited (freeA q A' l1 l2 p n) = true).
  { destruct HB2 as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & _ & _ & _ & _ & _ & _ & I9). apply I9. intros E. apply app_eq_nil in E as [E _]. exact (HT2 E). }
  destruct (rg_agree _ _ HR) as [HAGW HAGL].
  exact (drain_callE A (freeA q A' l1 l2 p n) Kc rho (rhoF_of A rho p n t jv) l1 l2 p n HKc (conj eq_refl (conj eq_refl eq_refl)) tp Hp12 Hn13 HAGW HAGL E24 HPURE
           HDS HT2 HCI2 HQB2 (budget_depot A A' HBud HDO) _ tpE _ HC).
Qed.
End DR.
