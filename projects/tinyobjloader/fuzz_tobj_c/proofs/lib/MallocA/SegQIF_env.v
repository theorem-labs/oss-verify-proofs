(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "bool"; "list"; "prod"; "app"; "true"; "nil"; "option"; "snd"; "Some"; "andb"; "length"; "fst"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "mul"; "pow"; "lt"; "of_nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SVar"; "sobj"; "sv"; "SPUle"; "eval"; "rm"; "rw"; "valuation"; "ss_objs"; "SPAlign"; "ss_facts"; "SAlu"; "ss_next"; "sv_eqb"; "SPBranch"; "mkSS"; "ob_base"; "ob_hi"; "ob_lo"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "swf"; "SExt"; "SPNot"; "SPUlt"; "holds"; "obj_range"; "soff"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "in_zone"; "zcheck"; "zdisjb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.Lists.List"; "In"; "forallb"; "Forall2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "aa_geom"; "AA"; "aa_cache_inited"; "aa_q_global"; "aa_q_thread"; "ag_thread"; "cs_cache"; "mkQB"; "topG"; "ag_ctx"; "ag_spacebeg"; "cs_allocated_user"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env"; "qienvF"; "ZD_itmF"; "DQI1P"; "DQI2P"; "DQI3P"; "N_itmF"; "SQI1P"; "SQI2P"; "FQ_itP"; "N_qiF"; "findiP"; "idxP"; "is3P"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "is_primary"; "max_count"; "kSpaceSize"; "kUserSpaceSize"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "DQI0"; "zhiQ"; "zloQ"; "O_ishQ"; "ZD_fix"; "ZD_rti"; "entQ"; "rieQ"; "BLQ"; "N_rti"; "carve_okq"; "shQ"; "zbQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs"; "CqiP"; "factsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "QW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "vIT"; "DQIs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "it_cls"; "qall"; "qitems"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "vCTX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "top_high"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRI"; "CURB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith"; "QIV"; "vb_of"; "FQ_geo"; "FQ_mag"; "FQ_stk"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event";
"@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "ALU_SLL"; "ALU_SRL"; "BC_EQ"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel"; "HVI"; "HVS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states"; "kAllocBegMagic"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SegQIP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition N_itmF (vb : bool) : list carve_spec := ltac2:(tb__ "0|d|
S8S7S7S7S22S0A2M0S0A2M1S6S7S7S0S3A2M2S22A2M3A1M4A2M5S2G5S4G1G4S4G0S0S4S22S0S82Z30M6A4Z38A4S2G3S4G2S22S4S0S3G6U8M7A4S20PcaA1A4SaG3A1M8A3A4S2G5S4G1G4S4G0S0S4S22S0S8cZ0M9A4Z8MaA4S2G3S4G2S22S4S0S3G9U4MbA4S20PcbA1A4S2G3S4G2S22S4S0S3Z4GbA4S20PccA1A4G8A3A3A4S2G5S4G1G4S4G0S0S4S22S0S95Zad0A4Zc60A4S2G3S4G2S22S4S0S3Zae0G7A4S20Pd1A1A4G8A3A4SaG5A1McA3A3A3S5S6G5A1Lvb;Vvb;S2G5S4G1G4S4G0S0S4S22S0S20Pd2A1G9A4Z10A4S2G3S4G2S22S4S0S3G9G7A4S1fSabA1A4S2G3S4G2S22S4S0S3GaG7A4S8cA4G8A3A3A4GcA3GcX5x2A3").
Definition N_qiF (vb : bool) : list carve_spec := N_rti ++ N_itmF vb.
Definition SQI1P (vb : bool) : sstate := ltac2:(tb__ "0|0|
S5aS7bA1S39S2fS36R1A1S37R1A1S34R1A1S33R1A1S38R1A1S8S21S28R1A1S6eS78S21S79S6aVvb;A1A4A3S2aR1A1S2cR1A1S35R1A1A9TS;").
Definition DQI1P (vb : bool) : axst := ltac2:(tb__ "0|0|
S5bS7bS67Vvb;A1A2").
Definition SQI2P (vb : bool) : sstate := ltac2:(tb__ "0|0|
S5aS63Vvb;A1A1S39S2fS36R1A1S37R1A1S34R1A1S33R1A1S38R1A1S8S21S28R1A1S2S21S7eSaS21A1A3A3S2aR1A1S2cR1A1S35R1A1A9TS;").
Definition DQI2P (vb : bool) : axst := ltac2:(tb__ "0|0|
S5bS63Vvb;A1S68Vvb;A1A2").
Definition DQI3P (vb : bool) : axst := ltac2:(tb__ "0|1|
Sa7S64Vvb;A1M0S8S1eS2aS5aG0A1A1S89Vvb;A1A3A2").
Fixpoint findiP (f : sobj -> bool) (l : list sobj) (k : nat) : nat := match l with [] => k | o :: t => if f o then k else findiP f t (S k) end.
Definition is3P (r o : sobj) : bool := ltac2:(tb__ "0|0|
SeSeS2dS30Vo;A1S30Vr;A1A2S2dS32Vo;A1S32Vr;A1A2A2S2dS31Vo;A1S31Vr;A1A2A2").
Definition idxP_of (vb : bool) : list nat := ltac2:(tb__ "0|0|
S6eS21S3S21S6bS6dR1A1S28S5aS65Vvb;A1A1A1U0A3Lr;S28S5aS88Vvb;A1A1A1A4").
Definition idxP_a : list nat := Eval vm_compute in (idxP_of false).
Definition idxP_b : list nat := Eval vm_compute in (idxP_of true).
Definition idxP (vb : bool) : list nat := if vb then idxP_b else idxP_a.
Lemma DQI1P_swf : ltac2:(tb__ "0|0|
S5S11S5S3aS67R1A1A1S9A3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DQI2P_swf : ltac2:(tb__ "0|0|
S5S11S5S3aS68R1A1A1S9A3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DQI3P_below : ltac2:(tb__ "0|1|
S5S11S5S48S1eS41S2cS5aS64R1A1A1M0A1A1S8S1eS2aG0A1S89R1A1A3A3S9A3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CqiP_eq : ltac2:(tb__ "0|0|
S5S11SbS5cA1S94S65R1A1S2S92S93S6cR1A1A1SaS92A1A3A2SdS5cS88R1A1A2A3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition ZD_itmF (vb : bool) : list zdesc := ltac2:(tb__ "0|4|
S8S7S7S3S0A2M0S0A2M1S2G1S4G0S0S4S3S0U5Z0M2A4Z1000A4S2G1S4G0S0S4S3S0U3N10A4N8A4S2G1S4G0S0S4S3S0U1Zad0A4Zc60A4SaG1A1M3A3A3A3S5S6G1A1Lvb;Vvb;S2G1S4G0S0S4S3S0U9G2A4Z10A4G3A3G3X5x2A3").
Lemma ZDq_chkF : ltac2:(tb__ "0|4|
S5S12S11S5S44S8S42S80S62R1A1A3M0A1S9A3S12S11S5S48S42S42S48S42S45R1A1M1S7fA3Ld;G0A3S9A3S11S5S48S42S42S48S42G1S8S42S7fS8S42S80S62R2A1A3A3A3Ld;S2S7S7S3S0A2M2S0A2M3S4G2S0S4S3S0U4Z0A4Z1f81A4SaG3A1A3A3S9A3A2A2Fvb;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition FQ_itP : list sprop := ltac2:(tb__ "0|f|
S2S1eS29Pa5M0Z4M1A2S2S1eS29P9bM2Z10M3A2S2S1eS23S1fZ10007fff8000A1S20G2A1M4A2S2S1eS23G4S1fZ7fdfff7ff000A1A2S2S1eS2eSa5S20P9cA1S7aG4S1fZ2000000000A1A2M5A3S2S1eS23S1fZ1A1S20Pc8A1M6A2S2S1eS23G6S1fZ1eA1A2S2S1eS23S1fG3A1M7S20Pc9M8A1M9A2S2S1eS23G9S1fZ10000A1A2S2S1eS29G8G1A2S2S1eS23G4S20G0A1MaA2S2S1eS3dGaG5A2S2S1eS3cS2eSa6S2bSa2S3bS9Q20S20PcbA1A3S1fZffA1A3S1fZ3MbA1A3A1S2S1eS23S1fZ8A1S20PcdMcA1MdA2S2S1eS23GdS1fZ10000000000A1A2S2S1eS29GcGbA2S2S1eS23S7aS7aGaG7A2GdA2MeG5A2S2S1eS23GeS1fZ7fffff800000A1A2SaS1eA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma factsP_eq : ltac2:(tb__ "0|1|
S5S11S6S1eA1M0S89R1A1S8S1eS9fS8S1eS9dS8S1eS69S5G0Lvb;R1S9eSaS1eA1X5x2A3A3A3A3Fvb;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section ArithP.
Variable A : AA.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HQP : q_pure A.
Hypothesis HAU : ltac2:(tb__ "0|1|
S0S12S16Z1R1A2S16R1Z1eA2A2S12S16Z0S56S8aVA;R2A2A1M0A2S16G0S76A2A2F_;Fc;").
Variables (rho : valuation) (it : Z * Z) (t st : Z).
Hypothesis HIN : ltac2:(tb__ "0|0|
S47S7S0S0A2Vit;S90S8fVA;A1A1A3").
Hypothesis HPR : ltac2:(tb__ "0|0|
S11S5S73ScS0S0Vit;A3A1S9A3").
Let c := it_cls it.
Let cs := cls_of A c.
Hypothesis Ht : 0 <= t < 256.
Hypothesis HRIG : ltac2:(tb__ "0|4|
S12S11S58Q40M0A1M1S26Vrho;P97A2S59G0S50S4bVA;A1M2A1A2A3S12S11G1S26Vrho;P98A2S59G0S54G2A1A2A3S12S11G1S26Vrho;P9bA2S59G0S55G2A1M3A2A3S11G1S26Vrho;P9cA2S59G0S17G3S75A2A2A3A2A2A2").
Hypothesis HV : ltac2:(tb__ "0|0|
S9bVrho;Vit;Vcs;Vt;Vst;A5").
Lemma qi_it_factsP : Forall (holds rho) FQ_itP.
Proof.
  destruct HRIG as (E151 & E152 & E155 & E156). destruct HV as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
  pose proof (qi_geom A HG HQP HAU rho it t HIN HPR Ht HRIG) as GEO. cbv zeta in GEO. fold c in GEO. fold cs in GEO. fold c cs in E200, E201, E202, E206, E207.
  destruct GEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  pose proof (max_count_facts c C1) as MC. rewrite kSpaceSize_val in E156.
  assert (M16 : (fst it - 16) mod 16 = 0).
  { rewrite EU. pose proof (Z.div_mod (it_ab it) 16 ltac:(lia)) as DA. pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)) as DR. rewrite A16 in DA. rewrite RZ16 in DR.
    rewrite DA, DR. replace (16 * (it_ab it / 16) + 0 + (16 * (rz (snd it) / 16) + 0) - 16) with ((it_ab it / 16 + rz (snd it) / 16 - 1) * 16) by lia. apply Z.mod_mul. lia. }
  assert (N0 : snd it / 2 ^ 32 = 0) by (apply Z.div_small; lia).
  assert (EM : eval rho (add (SVar 165) (SLit 16)) = Z_to_bv 64 (fst it)).
  { pose proof (eval_add_lit A rho (SVar 165) (fst it - 16) 16 E165 ltac:(lia) ltac:(lia) ltac:(lia)) as X. replace (fst it - 16 + 16) with (fst it) in X by lia. exact X. }
  assert (EMN : eval rho (add (add (SVar 165) (SLit 16)) (SVar 205)) = Z_to_bv 64 (fst it + (snd it + 7) / 8 * 8)) by (apply eval_add_z; [exact EM | cbn [eval]; exact E205 | lia | lia | lia]).
  assert (ESK : eval rho (add (SVar 155) (SLit 137438953472)) = Z_to_bv 64 (ag_spacebeg (aa_geom A) + 137438953472)) by (apply (eval_add_lit A); try lia; cbn [eval]; exact E155).
  unfold FQ_itP. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. split; [lia|]. rewrite E165, u64_lit by lia. exact M16.
  - cbn [holds]. split; [lia|]. rewrite E155, u64_lit by lia. exact S1.
  - cbn [holds eval]. rewrite E155, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E155, !u64_lit by lia. lia.
  - cbn [holds branch_taken]. rewrite ESK. cbn [eval]. rewrite E156. unfold bv_eqb. apply Z.eqb_eq. reflexivity.
  - cbn [holds eval]. rewrite E200, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E200, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E201, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E201, !u64_lit by lia. lia.
  - cbn [holds]. split; [lia|]. rewrite E201, u64_lit by lia. exact Z2.
  - cbn [holds eval]. rewrite E155, E165, !u64_lit by lia. lia.
  - cbn [holds]. rewrite ESK. cbn [eval]. rewrite E165, !u64_lit by lia. lia.
  - cbn [holds branch_taken]. intros HB. apply negb_true_iff in HB. unfold bv_eqb in HB. apply Z.eqb_neq in HB. apply HB. clear HB.
    rewrite U_and2, U_sext_e by lia. cbn [eval]. rewrite E203, N0, !u64_lit by lia. change (Z.of_N 32) with 32.
    rewrite (Z.mod_small (3 + 256 * t + 65536 * 0) (2 ^ 32)) by lia. unfold CursorGlue.zsext. replace (3 + 256 * t + 65536 * 0 <? 2 ^ (32 - 1)) with true by (symmetry; apply Z.ltb_lt; lia).
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. replace (3 + 256 * t + 65536 * 0) with (3 + t * 2 ^ 8) by lia. rewrite Z.mod_add by lia. reflexivity.
  - cbn [holds eval]. rewrite E205, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E205, !u64_lit by lia. lia.
  - cbn [holds]. split; [lia|]. rewrite E205, u64_lit by lia. exact N8b.
  - cbn [holds]. rewrite EMN, ESK, !u64_lit by lia. lia.
  - cbn [holds]. rewrite EMN. cbn [eval]. rewrite !u64_lit by lia. lia.
Qed.
End ArithP.

Record qienvF (A : AA) (it : Z * Z) (rho : valuation) (t st : Z) : Prop := mkQEF {
  qf_hg : geom_ok (aa_geom A);
  qf_hsep3 : sep_geom3 (aa_geom A);
  qf_hrtc : rtc_inv (view segsA (rm rho)) (aa_geom A);
  qf_hrig : rw rho 151%positive = Z_to_bv 64 (ag_thread (aa_geom A)) /\ rw rho 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))
            /\ rw rho 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A)) /\ rw rho 156%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize);
  qf_hgeo : qgeo A it;
  qf_hv : QIV rho it (cls_of A (it_cls it)) t st;
  qf_hcv : cls_view (view segsA (rm rho)) (aa_geom A) (aa_live A) (it_cls it) (cls_of A (it_cls it));
  qf_him : item_mem (view segsA (rm rho)) it;
  qf_hstat : present (view segsA (rm rho)) (ag_thread (aa_geom A) + 2768) (ag_thread (aa_geom A) + 3168);
  qf_ht : 0 <= t < 256 /\ view segsA (rm rho) (fst it - 15) = Some (Z_to_bv 8 t);
  qf_hst : 0 <= st < 2 ^ 64 /\ cell_ok (view segsA (rm rho)) (mkACell (ag_thread (aa_geom A) + 2784) 8 st);
  qf_hnf : Z.of_nat (length (cs_cache (cls_of A (it_cls it)))) <= max_count (it_cls it);
  qf_hqp : q_pure A;
  qf_hau : forall c', 1 <= c' <= 30 -> 0 <= cs_allocated_user (cls_of A c') <= kUserSpaceSize;
  qf_hin : In it (qitems (qall A));
  qf_hpr : is_primary (snd it) = true;
  qf_hmu : cs_allocated_user (cls_of A (it_cls it)) <= cs_mapped_user (cls_of A (it_cls it)) <= kUserSpaceSize
}.

Lemma qienvF_agree : ltac2:(tb__ "0|1|
S4cS7S0S0A2S27S27S0S0S61R6R5R4R2R1A5S1SacR1Pd8A2S11S58Q40A1M0S26R6R2A2S26R7R2A2A3F_;Fi;S11G0SbS58Q8A1A1F_;S25R5A1S25R6A1A3S61R9R8R6R5R4A5F_;F_;F_;Fst;Ft;Fr';Fr;Fit;FA;").
Proof.
  intros A it r r' t st [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17] HRW HRM.
  constructor; rewrite ?HRM; try assumption.
  - destruct Q4 as (E151 & E152 & E155 & E156). repeat split; rewrite HRW by lia; assumption.
  - unfold QIV in *. cbv zeta in *. destruct Q6 as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
    repeat split; rewrite HRW by lia; assumption.
Qed.

Section QIEnvF.
Variables (A : AA) (it : Z * Z) (rho : valuation) (t st : Z).
Hypothesis QE : ltac2:(tb__ "0|0|
S61VA;Vit;Vrho;Vt;Vst;A5").
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
S19S18S17Vn;Z7A2Z8M0A2G0A2").
Let m : bview := ltac2:(tb__ "0|0|
S5dS46S25Vrho;A1A2").

Ltac qe_open := pose proof QE as [HG HSEP3 HRTC HRIG HGEO HV HCV HIM HSTAT Ht Hst HNF HQP HAU HIN HPR HMU]; unfold qgeo in HGEO.
Ltac qe_unf := unfold k, N8, m, cs, c, ab, u, n, T, CTX, SB in *.

Lemma qf_nums : ltac2:(tb__ "0|2|
S12S16Z1000M0VT;A2S12S16S17VT;G0A2S53S4bVA;A1A1M1A2S12S16G0VCTX;A2S12S16S17VCTX;G0A2G1A2S12S16S17S17VSB;S1aZ2Z25A2A2G0A2G1A2S12S12S16Z7fff7f800000G1A2S16G1Z7fffff800000A2A2S12S16Z0Vk;A2S16Vk;Z10A2A2A2A2A2A2A2A2").
Proof.
  qe_open. pose proof (geom_old _ HG) as HG'. rewrite kSpaceSize_val in HG'. destruct HG' as (_ & _ & _ & _ & G5 & G6 & _ & G8 & G9 & _ & _ & _ & _ & G14 & _).
  pose proof (topG_range (aa_geom A)) as TG. destruct HGEO as (C1 & _). pose proof (max_count_le16q _ C1) as MC.
  qe_unf. repeat split; lia.
Qed.
Lemma qf_wins : ltac2:(tb__ "0|8|
S12S13S16S17VT;Z1000M0A2M1Z10000M2A2S16Z646000M3VT;A2A2S12S13S16S17VCTX;G0A2M4G2A2S16G3VCTX;A2A2S12S13S16G1Z7fff7000M5A2S16Z10007fff8000M6VT;A2A2S12S13S16G4G5A2S16G6VCTX;A2A2S12S13S16G1VCTX;A2S16G4VT;A2A2S12S13S16G1VSB;A2S16S17S17VSB;S1aZ2Z25A2A2G0A2M7VT;A2A2S13S16G4VSB;A2S16G7VCTX;A2A2A2A2A2A2A2A2").
Proof.
  qe_open. pose proof (geom_bands _ HG) as (_ & TB & CB & _ & TI & CI & _). pose proof (geom_seps _ HG) as (_ & _ & _ & _ & Q5 & _).
  destruct HSEP3 as (S1 & S2 & _). rewrite kSpaceSize_val in S1, S2.
  unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. qe_unf.
  split; [exact TI|]. split; [exact CI|]. split; [exact TB|]. split; [exact CB|]. split; [exact Q5|]. split; [exact S1 | exact S2].
Qed.
Lemma qf_Sh : ltac2:(tb__ "0|3|
S12S16Z7fff8000S72Vu;A1M0A2S12S16S17G0Z1f81A2Z10007fff8000A2S12S12S16Z0S18VN8;Z8M1A2M2A2S16G2Z1f80A2A2S11S0G2S18S17Vn;Z7A2G1A2A3A2A2A2").
Proof.
  qe_open. destruct HGEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  qe_unf. unfold Sh, SHADOW_OFF.
  pose proof (Z.div_pos (fst it) 8 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_lt_upper_bound (fst it) 8 (2 ^ 44 - 2 ^ 20) ltac:(lia) ltac:(lia)) as D1.
  pose proof (Z.div_pos ((snd it + 7) / 8 * 8) 8 ltac:(lia) ltac:(lia)) as D2.
  pose proof (Z.div_le_upper_bound ((snd it + 7) / 8 * 8) 8 8064 ltac:(lia) ltac:(lia)) as D3.
  split; [lia|]. split; [lia|]. split; [lia|]. apply Z.div_mul. lia.
Qed.

Lemma qf_E : ltac2:(tb__ "0|3|
S12S11S0S57Q40M0S24Vrho;S95A2A2VT;A3S12S11S0S57G0S24Vrho;S96A2A2VCTX;A3S12S11S0S57G0S24Vrho;S8cA2A2S1dVu;Z10A2A3S12S11S0S57G0S24Vrho;S82A2A2S17S17VSB;S1aZ2M1Z25A2A2S19Z80Vc;A2A2A3S12S11S0S57G0S24Vrho;S81A2A2S17S17VT;Zd0A2S19Z50Vc;A2A2M2A3S12S11S0S57G0S24Vrho;S7aS81S2bSa3S20PceA1S1fG1A1A3A2A2A2S17G2S19Z4Vk;A2A2A3S12S11S0S57G0S24Vrho;S86A2A2S72Vu;A1A3S12S11S0S40Vrho;S2bSa4S20PcdA1S1fZ3A1A3A2S18VN8;Z8A2A3S11S0S57G0S24Vrho;S20Pd2A1A2A2Vab;A3A2A2A2A2A2A2A2A2").
Proof.
  qe_open. pose proof qf_nums as (T0 & T1 & C0 & C1' & S14 & TG & K16). pose proof qf_Sh as (SH0 & SH1 & L0 & _).
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

Lemma carve_rtiF : Forall (carve_okq rho) N_rti.
Proof.
  qe_open. pose proof qf_nums as (T0 & T1 & C0 & C1' & S14 & TG & K16). pose proof qf_wins as (_ & CI & _).
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

Lemma carve_itmF : ltac2:(tb__ "0|0|
S5S11S5R1S9A3S15S11S0S77Vn;A1Z10A3A1F_;S6fS78S85Vrho;A1S66R2A1A3F_;Fvb;").
Proof.
  intros vb HVB. qe_open.
  pose proof qf_nums as (T0 & T1 & C0 & C1' & S14 & TG & K16). pose proof qf_wins as (TI & _).
  pose proof qf_E as (EvT & EvC & EvIT & Erie & Eent & Eslot & Esh & Elen & E210u).
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
  unfold N_itmF. apply Forall_app. split.
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
S87VT;VCTX;VSB;Vu;Vab;S53S4bVA;A1A1S17S17VT;Zd0A2S19Z50Vc;A2A2M0G0S72Vu;A1A9").

Lemma inz_fixF : ltac2:(tb__ "0|0|
S6S3A1S47S3U0R1A3S47S3U6R2A3S97VA;Vrho;A2S6fS1eS3eVrho;A1S98SaaA1A3S49S21S42S43Vrho;Vzb;S7dS7cR5A5S28S5aS7bA1A1S7fA5F_;F_;F_;F_;Fzused;").
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

Lemma inz_rtiF : ltac2:(tb__ "0|0|
S6S3A1S47S3U0R1A3S47S3U2R2A3S49S21S42S43Vrho;Vzb;S7dS7cR3A5S6eS78S21S79S84A4S80A5F_;F_;Fzused;").
Proof.
  intros zused U0 U2. qe_open. pose proof qf_nums as (T0 & T1 & C0 & C1' & S14 & TG & K16). destruct HRIG as (E151 & E152 & E155 & E156).
  qe_unf. clear HGEO HSEP3 HV HCV HIM HSTAT Ht Hst HNF HQP HAU HIN HPR HMU HRTC.
  unfold N_rti, ZD_rti. cbn [map carve_obj]. unfold vCTX.
  repeat apply Forall2_cons; try apply Forall2_nil.
  all: unfold in_zone; split; [assumption | split; [cbn; lia | split; [cbn; lia | right]]].
  all: unfold carved; rewrite obj_range_mk by lia; unfold zb; cbn [fst snd eval zbQ]; rewrite ?E152, ?u64_lit by lia; lia.
Qed.

Lemma inz_itmF : ltac2:(tb__ "0|0|
S5S6S3A1S3S47S3R1S2S3U1S2S3U3S2S3U5S2S3U7S2S3U8SaS3A1A3A3A3A3A3A3S47S3R2R3A3F_;Fz;S11S5R3S9A3S47S3U9R3A3F_;S49S21S42S43Vrho;Vzb;S7dS7cR3A5S6eS78S21S79S66R4A1A4S62R4A1A5F_;F_;Fzused;Fvb;").
Proof.
  intros vb zused HU HU9. qe_open. pose proof qf_nums as (T0 & T1 & C0 & C1' & S14 & TG & K16).
  pose proof qf_E as (EvT & EvC & EvIT & Erie & Eent & Eslot & Esh & Elen & E210u).
  destruct HGEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  clear HSEP3 HV HCV HIM HSTAT Ht Hst HQP HAU HIN HPR HMU HRTC HRIG.
  unfold N_itmF, ZD_itmF. rewrite map_app. apply Forall2_app.
  - cbn [map carve_obj]. repeat apply Forall2_cons; try apply Forall2_nil.
    all: unfold in_zone; split; [apply HU; cbn; tauto | split; [cbn; lia | split; [cbn; lia | right]]].
    all: unfold carved; rewrite obj_range_mk by lia; unfold zb; cbn [fst snd zbQ]; rewrite ?EvT, ?EvIT, ?Erie, ?Eent, ?Eslot; qe_unf; lia.
  - destruct vb; cbn [map carve_obj]; [|apply Forall2_nil]. apply Forall2_cons; [|apply Forall2_nil].
    unfold in_zone. split; [exact (HU9 eq_refl)|]. split; [cbn; lia|]. split; [cbn; lia|]. right.
    unfold carved. rewrite obj_range_mk by lia. unfold zb. cbn [fst snd zbQ]. rewrite E210u. lia.
Qed.

Lemma ish_rangeF : ltac2:(tb__ "0|1|
S11S7S0S0A2S3fVrho;S7eA2S4S0S0S17S72Vu;A1M0Z0A2S17G0S18VN8;Z8A2A2A4A3").
Proof.
  pose proof qf_E as (_ & _ & _ & _ & _ & _ & Esh & Elen & _).
  unfold O_ishQ, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by lia. rewrite Elen, Esh. reflexivity.
Qed.
Lemma inz_ishF : ltac2:(tb__ "0|3|
S6S3A1S47S3U4M0R1A3S49S21S42S43Vrho;Vzb;S7dS7cR2A5S2S21S7eSaS21A1A3S2S7S7S3S0A2M1S0A2M2S4G1S0S4S3S0G0Z0A4Z1f81A4SaG2A1A3A5F_;Fzused;").
Proof.
  intros zused U4. pose proof qf_Sh as (_ & _ & L0 & _).
  apply Forall2_cons; [|apply Forall2_nil]. unfold in_zone. split; [exact U4|]. split; [cbn; lia|]. split; [cbn; lia|]. right.
  rewrite ish_rangeF. unfold zb. cbn [fst snd zbQ]. lia.
Qed.

Lemma qip_carve : ltac2:(tb__ "0|0|
S71S6S58Q40A1A1S91S97VA;Vrho;A2S70S46R4S7bVrho;R3R2A6S70S46R5S88S9cVit;A1A1Vrho;R4R3A6F_;F_;Fw;Ftp;FJ;").
Proof.
  intros J tp w HTOPH H0. remember (vb_of it) as vb eqn:EVB. qe_open.
  assert (HVB : vb = true -> rz n <> 16) by (rewrite EVB; unfold vb_of; intros X; apply negb_true_iff in X; apply Z.eqb_neq in X; exact X).
  pose proof (D_pre_facts DQI0 _ DQI0_facts rho (SPA_facts_hold segsA _ rho DQI0 tp _ H0)) as HFpre.
  pose proof qf_nums as (T0 & T1 & C0 & C1' & S14 & TG & K16). pose proof qf_Sh as (SH0 & SH1 & L0 & L1).
  pose proof qf_E as (EvT & EvC & EvIT & Erie & Eent & Eslot & Esh & Elen & E210u).
  pose proof qf_wins as (WTI & WCI & WTB & WCB & WTC & WTS & WCS).
  assert (HM : vb = true -> ab + 16 <= u - 16).
  { intros X. specialize (HVB X). destruct HGEO as (_ & _ & _ & RZ & RZ16 & EU & _). unfold u, n, ab in *. clear - HVB RZ RZ16 EU. unfold it_ab in *.
    pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)) as D. rewrite RZ16 in D. lia. }
  assert (HSEPZ : forall z z', In z (ZUQ vb) -> In z' (ZUQ vb) -> z <> z' -> zb z + zhiQ z <= zb z' + zloQ z' \/ zb z' + zhiQ z' <= zb z + zloQ z).
  { unfold zb. destruct HGEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
    intros z z' Hz Hz' NE.
    apply (zsepQ T CTX SB u ab (topG (aa_geom A)) (T + 208 + 80 * c) (T + 208 + 80 * c) (Sh u)) with (vb := vb); try assumption;
      clear WTI WCI WTB WCB WTC WTS WCS HM HVB; unfold k, N8, cs, c, ab, u, n, T, CTX, SB in *; lia. }
  assert (U_all : forall z, (z <= 8)%nat -> In z (ZUQ vb)) by (intros z Hz; unfold ZUQ; apply in_or_app; left; cbn; lia).
  assert (U9 : vb = true -> In 9%nat (ZUQ vb)) by (intros X; rewrite X; first [ repeat match goal with H : _ |- _ => clear H end; cbn; tauto | cbn; tauto ]).
  assert (INZN : Forall2 (in_zone rho zb zloQ zhiQ (ZUQ vb)) (map carve_obj (N_qiF vb)) (ZD_rti ++ ZD_itmF vb)).
  { unfold N_qiF. rewrite map_app. apply Forall2_app; [apply inz_rtiF; apply U_all; lia | apply inz_itmF; [|exact U9]].
    intros z Hz. apply U_all. cbn in Hz. first [ clear - Hz; lia | lia ]. }
  assert (INZF : Forall2 (in_zone rho zb zloQ zhiQ (ZUQ vb)) (ss_objs (ax_S DQI0)) ZD_fix) by (apply inz_fixF; [apply U_all; lia | apply U_all; lia | exact HTOPH | exact HFpre]).

  assert (H1 : SPA segsA J (DQI1P vb) rho tp w).
  { pose proof (SPA_carve_list segsA J rho DQI0 tp w (N_qiF vb) (ss_next (ax_S DQI0)) H0) as X. cbn zeta in X. apply X; clear X.
    - exact (DQI1P_swf vb).
    - apply Pos.le_refl.
    - unfold N_qiF. apply carve_okq_list; [reflexivity|]. apply Forall_app. split; [exact carve_rtiF | exact (carve_itmF vb HVB)].
    - exact (zones_cross rho zb zloQ zhiQ (ZUQ vb) HSEPZ _ _ _ _ INZN INZF (proj1 (proj2 (ZDq_chkF vb)))).
    - exact (zones_pd rho zb zloQ zhiQ (ZUQ vb) HSEPZ _ _ INZN (proj1 (ZDq_chkF vb))). }

  assert (H2 : SPA segsA J (DQI2P vb) rho tp w).
  { pose proof (SPA_carve_unk segsA J rho (DQI1P vb) tp w shQ (SLit 0) (SAlu ALU_SRL (SVar 205) (SLit 3)) (ss_next (ax_S (DQI1P vb))) H1) as X. cbn zeta in X.
    rewrite Esh, Elen, (soff_lit_small rho 0) in X by lia. apply X; clear X.
    - exact (DQI2P_swf vb).
    - apply Pos.le_refl.
    - lia.
    - lia.
    - lia.
    - lia.
    - pose proof (zones_cross rho zb zloQ zhiQ (ZUQ vb) HSEPZ [O_ishQ] [(4%nat, 0, 8065)] (ss_objs (ax_S DQI0) ++ map carve_obj (N_qiF vb)) (ZD_fix ++ ZD_rti ++ ZD_itmF vb)
                   (inz_ishF _ (U_all 4%nat ltac:(lia))) (Forall2_app INZF INZN) (proj2 (proj2 (ZDq_chkF vb)))) as ZC.
      pose proof (Forall_inv ZC) as ZC1. cbv beta in ZC1. rewrite ish_rangeF in ZC1. exact ZC1.
    - intros a0 Ha. destruct HIM as (_ & _ & _ & _ & _ & _ & IM7).
      assert (IM7' : present (view segsA (rm rho)) (Sh u) (Sh u + N8 / 8)) by (rewrite L1; exact IM7).
      apply (wr_present (rm rho) (Sh u) (Sh u + N8 / 8) a0 IM7'); lia.
    - intros rr y j Hin. destruct Hin. }
  assert (H3 : SPA segsA J (DQI3P vb) rho tp w).
  { apply SPA_refacts; [exact H2 | exact (DQI3P_below vb) |]. intros HF. apply Forall_app. split; [exact HF|]. rewrite factsP_eq.
    destruct Ht as [Ht1 Ht2].
    apply Forall_app. split; [exact (stk_facts_hold A rho HTOPH HFpre)|].
    apply Forall_app. split; [eapply (qi_geo_facts A); eassumption|].
    apply Forall_app. split; [eapply (qi_it_factsP A); eassumption|].
    destruct vb; [assert (EVB' : vb_of it = true) by (symmetry; exact EVB); eapply (qi_mag_facts A); eassumption | apply Forall_nil]. }
  exact (SPA_axforms segsA _ _ rho _ _ tp _ (CqiP_eq vb) H3).
Qed.
End QIEnvF.

Section QIPreF.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).

Lemma qienvF_of_K : ltac2:(tb__ "0|6|
S4cS0S0S0S3S7S0S0A2M0S6G0A1S6S4aA1M1G1S27S6S58Q40A1A1S6Sa1A1Sa0S0S0S11G1S4fRfA1SaS4aA1A3S11S5S4dR10A1S9A3S11G1S4eR11A1S2S4aS52R10S2G0RcRbA3RfA3S8S4aRaR9A3A3A3S11S5S73ScS0S0RdA3A1S9A3S16S1cSfS0S51S8aR13S8eReA1M2A2A1A2A1S74G2A1A2VK;R14RbRaR9R8A5S9aS5dS46S25RcA1A2R14R12R11S2G0R10RfA3A5S9bRdR11S8aR16S8eR11A1A2R9R8A5S12S16Z0M3RaA2S1bRaZ100A2A2S11SbS58Q8M4A1M5A1S5dS46S25RfA1S1dS10S0S0R13A3ZfA2A3SdG5S59G4RbA2A2A3S12S16G3RbA2S1bRbS1aZ2Z40A2A2A2S5fS5dS46S25R11A1A2S60S17S50S4bR1aA1A1Zae0A2U8RcA3A2S61R1bR16R12ReRdA5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fst;Ft;Fmd;Ftr;Ftp;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").
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

Lemma qip_pre : ltac2:(tb__ "0|4|
S4cS0S0S0S3S7S0S0A2M0S6G0A1S6S4aA1M1G1S27S6S58Q40A1M2A1S91S11G1S4fRcA1SaS4aA1A3S11S5S4dRdA1S9A3S0S8bRfR1A2S8bVA0;R2A2F_;Fz;S11G1S4eRfA1S2S4aS52ReS2G0RaR9A3RdA3S8S4aR8R7A3A3A3S11S5S73ScS0S0RbA3A1S9A3S16S1cSfS0S51S8aR11S8eRcA1M3A2A1A2A1S74G3A1A2S70S46S99VK;VA0;Vrho0;R12R11RfReS2G0RdRcA3RbRaAaS8dR9R8R7A6Sa8RaR12R10RfReA5Sa9RbR13R10RfA4S14S27S27S14S0S0S14S0S0S12S70S46S99VK;VA0;Vrho0;R18R17R15R14S2G0R13R12A3R11R10AaS88S9cR13A1A1R3ReRdA6S12S61R18R13R3R2R1A5S12S1S15S47S1R1S83A3A1S11G2S26R5R2A2S26R11R2A2A3F_;Fi;S11S5eS5dS46S25R3A1A2S5dS46S25RfA1A2A3A2A2A2Lst;A2Lt;A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it its tmp' rest rho tp w HTH HCI HQW HGL HPR HNF H HVi HVs. destruct w as [tr [ms md]].
  pose proof (qi_unobj K HL A0 rho0 A a s n0 nd its tmp' rest it rho tp tr ms md HTH HCI HQW HGL H HVi HVs) as X. cbn zeta in X. destruct X as [H0 EV0].
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
  assert (QE : qienvF A it rho2 t st).
  { apply (qienvF_of_K A a s n0 nd it its tmp' rest rho2 tp tr md t st HTH HCI HGL HPR HNF HK2 HCB2 HQV Ht1); [rewrite ERM; exact Ht2 | exact Hst1 | rewrite ERM; exact Hst2]. }
  exists rho2, t, st. split; [|split; [exact QE | split; [exact OTH | rewrite ERM; exact EV0]]].
  apply (qip_carve A it rho2 t st QE); [|exact H1].
  destruct (kq_facts segsA K HL A rho2 tp _ _ HK2) as [_ _ _ _ _ _ _ _ _ _ _ HKTOP2 _]. exact HKTOP2.
Qed.
End QIPreF.
