(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rcarve.
From Stdlib Require Lia.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg j8 kj.

(* [comment removed for export] *)
Module F0A_statesC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "nil"; "app"; "length"; "bool"; "pair"; "list"; "negb"; "S"; "false"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXSplit"; "AXMerge"; "AXUnbase"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "ss_objs"; "SVar"; "SAlu"; "sv"; "ss_next"; "SExt"; "ob_base"; "ss_facts"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "sobj_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "idx_of"; "XR2"; "XRa"; "find_idx"; "front"; "E3_of"; "KEPT1_of"; "RR_of"; "T2_of"; "XR1"; "XR3"; "XRC"; "XS_of"; "XSa"; "XSb"; "XW"; "back"; "eFRc"; "sR_of"; "selR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "axf"; "OFF_PUT"; "is_obj"; "optR"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "L_rf"; "@Stdlib.Lists.List"; "filter"; "existsb"; "flat_map"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "seq"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "complement"; "dummy_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "pred"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_OR"; "ALU_SLL"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "P0_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "eRIS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rcarve.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Fixpoint find_idx (g : sobj -> bool) (l : list sobj) (i : nat) : nat := match l with [] => i | o :: r => if g o then i else find_idx g r (S i) end.
Definition idx_of (A : axst) (b lo : sv) : nat := ltac2:(tb__ "0|0|
S24S37Vb;Vlo;A2S14S1dVA;A1A1U0A3").

Definition front (A : axst) (ns : list nat) : list nat := ltac2:(tb__ "0|0|
S3S0Vns;S46Vns;S4S13S14S1dVA;A1A1A2A2A3").
Definition back (A : axst) (ns : list nat) : list nat := ltac2:(tb__ "0|0|
S3S0S46Vns;S4S13S14S1dVA;A1A1A2A2Vns;A3").

Definition P0_C (khi : bool) (W : list ulink) (st : ustop) (f : bool) : axst := ltac2:(tb__ "0|0|
S59Vkhi;VW;Vst;S44S3aS13S3bS5aVf;A1A4S5bVf;A1A5").

Definition XR1 (Erf : axst) : list axform := ltac2:(tb__ "0|1|
S21VErf;S15PaA1S15S5eA1A3S0S1ScSeR1S12N8e0M0A1A2S1ScS10R1G0A2S2ScA1A3A3TiW;").
Definition XR2 (E1 : axst) : list axform := ltac2:(tb__ "0|1|
S21VE1;S48S12Zad0A1A3S0S1ScS11S9R1A1A1S1ScSfR1A1M0S1ScG0S2ScA1A3A3A3TiT;").
Definition XR3 (E2 : axst) : list axform := ltac2:(tb__ "0|3|
S21VE2;S12Z0A1M0S12Zeaa78A1A3S0S21VE2;G0S12Zeaa80A1A3S0S3eS0S0S8S4bR1R2A2A1Li;S43U0S4S13S14S1dVE2;A1A1A2A2A3S7S0A1M1S40S0S0S0S5G1L_;S4bR1R4A2S1S0R4S1S0R3S2S0A1M2A3A3S1S0R1G2A3X5x2Li;R1A4G1S1ScSdR1A1S1ScSfS5S0L_;S4cR3R4A2S4dR4A1R4X5x2A1S2ScA1A3A3Tsel;Trest;TiI;TiS;").
Definition XRa (Erf : axst) : list axform := ltac2:(tb__ "0|1|
S35VErf;S2aVErf;A1M0A2S1eS35R1S22R1A1A2S1eS3ScG0S3ScS22R2A1S2bR1A1A3A3TE2;TE1;").
Definition E3_of (Erf : axst) : axst := ltac2:(tb__ "0|0|
S35VErf;S23VErf;A1A2").

Definition sR_of (E3 : axst) : wsub := ltac2:(tb__ "0|1|
S1SbS39S17A2M0S6S39S17PcS12Z1f00A1A4S1G0S6S39S17S58S12Z2000A1A4S1G0S6S39S17P9cS5cA4S53P1S1dVE3;A1S1dS3cA1A3A3A3A3").
Definition RR_of (E : axst) (s : wsub) : list sobj := ltac2:(tb__ "0|0|
S38S56VE;S3cVs;A3A1").
Definition selR (E3 : axst) : list nat := ltac2:(tb__ "0|2|
S14S1dVE3;A1A1S7S13A1M0S28VE3;S33VE3;A1A2G0S0S3fS13S20S45S13R1R3S47A4A1R2A3Li;S0S5Fi;S3S0S3eS0S0S8R2R1A1A1Li;S43U0S4S13R3A2A2M1A3S3eS0R1G1A3A3TinR;TR0;Tobjs;").
Definition XRC (Erf : axst) : list axform := ltac2:(tb__ "0|0|
S3ScS23VErf;A1S1ScSdS34S26VErf;A1A1A1S2ScA1A3A3").
Definition EC_of (Erf : axst) : axst := ltac2:(tb__ "0|0|
S35VErf;S2cVErf;A1A2").
Definition KEPT_of (EC : axst) (RR : list sobj) : list sobj := ltac2:(tb__ "0|1|
S42S13S41S4S13S14S1dVEC;A1A1M0A2S4S13VRR;A2A2G0A3").

Definition T0_of (EC : axst) (s : wsub) (RR : list sobj) : axst := ltac2:(tb__ "0|0|
S55S57Vs;S3cS3dVEC;VRR;A5S1bS1dVEC;A1A1A2").
Definition XSa (T0 : axst) : list axform := ltac2:(tb__ "0|1|
S1ScSdS25VT0;S1S0S21VT0;S48S12Zad0A1A3S1S0S21VT0;S12Z0A1S12Zeaa78A1A3S2S0A1A3A3A2A1S1ScSeU0S12Zae0A1A2S1ScSeU1M0S12Zae8A1A2S1ScS10G0Zd0A2S1ScSeU3S12Zeaa80A1A2S2ScA1A3A3A3A3A3").
Definition XSb (T1a : axst) : list axform := ltac2:(tb__ "0|0|
S1ScSdS31VT1a;S1S0U2S1S0U4S1S0S21VT1a;S12Z0A1S12Zeaa88A1A3S2S0A1A3A3A3A2A1S2ScA1A3").
Definition XS_of (T0 : axst) : list axform := ltac2:(tb__ "0|1|
S3ScS2eVT0;A1M0S2fS35VT0;G0A2A1A3").
Definition T1_of (T0 : axst) : axst := ltac2:(tb__ "0|0|
S35VT0;S2dVT0;A1A2").
Definition KEPT1_of (T1 : axst) : list sobj := ltac2:(tb__ "0|1|
S42S13S41S4S13S14S1dVT1;A1A1M0A2U3A2G0A3").
Definition T2_of (T1 : axst) : axst := ltac2:(tb__ "0|0|
S1fVT1;S54S1dVT1;A1S27VT1;A1A2A2").

Definition eFRc : sv := ltac2:(tb__ "0|0|
S16S50S16S51S16S52S15P6bA1S12Z10A1A3S12Z20A1A3S19SaQ20S15P67A1A3A3").
Definition TR_of (T1 : axst) : axst := ltac2:(tb__ "0|2|
S49S29VT1;A1S1S3aS4aS32S18S1dVT1;A1A1M0S4eG0A1M1A3S2S3aA1A3S4eG1A1A3").

Definition TRs_of (TR : axst) : axst := ltac2:(tb__ "0|0|
S49VTR;S5dS18S1dVTR;A1A1A3").
Definition XW (Erq : axst) : list axform := ltac2:(tb__ "0|3|
S24S13S1cS1aR1A1S16S4fS15PaA1M0S12N8e0A1M1A3A2Lo;S14S1dVErq;A1A1U0M2A3S0S21VErq;G0G1A3S0S1ScSdS25VErq;S1S0R2S1S0R1S2S0A1A3A3A2A1S1ScS11G2A1S1ScSfG2A1S1ScSeG2S12S36A1A2S1ScS10G2S36A2S2ScA1A3A3A3A3A3Tk1;Tk0;").
Definition Erq2_of (Erq : axst) : axst := ltac2:(tb__ "0|0|
S35VErq;S30VErq;A1A2").
End F0A_statesC.

(* [comment removed for export] *)
Module F0A_asmC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "iff"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "true"; "nil"; "prod"; "false"; "option"; "pair"; "Some"; "nat"; "app"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "rl"; "rm"; "ss_next"; "ss_lenient"; "ss_objs"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "qbatch"; "aa_cache_inited"; "aa_internal_inited"; "budget_ok_free"; "aa_geom"; "aa_q_thread"; "budget_bound"; "qb_items"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "depot_onlyKf"; "JF"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "J_free_preT"; "KcA"; "client_addrA"; "JL_free"; "L_free"; "Pre_freeI"; "client_shadowA"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "rhoC_of"; "qcondCx"; "offp"; "K_i1"; "K_i2"; "NVC"; "VFC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_asmC"; "qC"; "entry_pureC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "RETQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "lastq"; "cache24"; "cnt24"; "j_min"; "qcond"; "top24"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "Pre_mid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "leaves_at"; "DRNE"; "RETF"; "qvar"; "O_stT2"; "QA"; "entsF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "L_rf"; "RF_ENT"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "rpins"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "kQuarantineBatchCount"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "instG_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"; "cpins"; "@Stdlib.ZArith.BinInt.Z"; "le"; "modulo"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rcarve.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hd_link_trans : ltac2:(tb__ "0|2|
S0OF_;M0G0S16S16S16S0R6R1A1R6R2A1F_;Fa;S4bR6R4R3A3M1G1S4bR8R6R4A3F_;F_;F_;Fr3;Fr2;Fr1;Fkeep';Fkeep;").
Proof.
  intros keep keep' r1 r2 r3 HK (W1 & L1 & M1 & D1) (W2 & L2 & M2 & D2).
  split; [intros i; rewrite W2; apply W1|]. split; [intros l; rewrite L2; apply L1|].
  split; [intros a Ha; rewrite (M2 a (HK _ Ha)); exact (M1 a Ha)|].
  intros a Ba Hd. exact (D2 a Ba (D1 a Ba Hd)).
Qed.
Lemma depot_refill : ltac2:(tb__ "0|1|
S1fS1fS31R2R1A2S31S30R3Z18M0A2S30R2G0A2A2F_;FA';FA;").
Proof.
  intros A A' (EG & EC & ECI & ES & EP & EL & EQT & EQG & EII & EFB & EFH & EV & EKm & EKf).
  unfold depot_onlyKf, refillA. cbn [aa_geom aa_cls aa_cache_inited aa_sec aa_ptr_committed aa_live aa_q_thread aa_q_global aa_internal_inited aa_fs_busy aa_fs_hint aa_V aa_Km aa_Kf].
  rewrite EC. repeat split; assumption.
Qed.
Lemma client_addr_depot : ltac2:(tb__ "0|0|
S9SeS0S0A2A1S1fS1fS0S31R3R2A2S6S3cR5R4R2A3S3cR5R3R2A3A2F_;Fa;FA';FA;FCST;").
Proof.
  intros CST A A' a (EG & _ & _ & _ & _ & EL & _ & _ & _ & EFB & _). unfold client_addrA, client_mut_addrA, aa_frames. rewrite EG, EL, EFB. tauto.
Qed.
Lemma KEEPD_depot : ltac2:(tb__ "0|1|
S9SeS0S0A2A1M0G0S1fS1fS0S31R3R2A2S51R6R5R4R2A4S51R7R6R4R3A4F_;F_;Fa;FA';FA;FXGL;FCST;").
Proof.
  intros CST XGL A A' a HD [H|H]; [left; exact (proj1 (client_addr_depot CST A A' a HD) H)|]. right.
  destruct H as [(x & Hx & ->)|H]; [left; exists x; split; [exact (proj1 (client_addr_depot CST A A' x HD) Hx) | reflexivity] | right; exact H].
Qed.

Lemma KEEPD_refill : ltac2:(tb__ "0|2|
S9SeS0S0A2A1M0G0S1fS0S4S3cR4S30R2Z18A2M1R1A3S40R4R3G1R1A4A2S51R5R4R3R2A4F_;Fa;FA;FXGL;FCST;").
Proof. intros CST XGL A a H. exact H. Qed.

Lemma budget_depot : ltac2:(tb__ "0|0|
S1fS1fS24R2A1S31R3R2A2S8bS27R3A1S83A2F_;F_;FA';FA;").
Proof.
  intros A A' HB (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EV & EKm & EKf).
  unfold budget_ok_free, limit_ok_free in HB. unfold budget_bound. rewrite EV, EKm, EKf. exact HB.
Qed.

Section PINS.
Variables (A : AA) (rho : valuation) (p n t : Z) (jv : junkF).
Let rho1 : valuation := ltac2:(tb__ "0|0|
S43VA;Vrho;Vp;Vn;Vt;Vjv;A6").
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S2S0S2fQ40S17Vrho;PcA2A2Vp;A3").
Hypothesis Hn13 : ltac2:(tb__ "0|0|
S2S0S2fQ40S17Vrho;PdA2A2Vn;A3").
Hypothesis HJM : j_min jv = kQuarantineMin.
Hypothesis HR : rigF rho rho1.
Variables (A' : AA) (r : valuation).
Hypothesis HDO : depot_onlyKf A A'.
Hypothesis HRW : ltac2:(tb__ "0|0|
S1S2S2eQ40A1S17Vr;R1A2S17Vrho1;R1A2A3Fi;").

Lemma pin107 : ltac2:(tb__ "0|0|
S2S0S8cS2fQ40S17Vrho1;P6bA2A2Z100A2Z3A3").
Proof.
  destruct HR as [_ (t' & T1 & T2 & E4) _ _ _ _ _ E7 _ _]. rewrite E7, E4.
  replace (2 + 256 * t' + 65536 * (bv_unsigned (rw rho1 13%positive) / 2 ^ 32) + 1) with (3 + (t' + 256 * (bv_unsigned (rw rho1 13%positive) / 2 ^ 32)) * 256) by (clear; lia).
  rewrite Z.mod_add by (clear; lia). reflexivity.
Qed.
Lemma lastq_depot : ltac2:(tb__ "0|0|
S2S21S5eVA';A1S5eVA;A1A3").
Proof. destruct HDO as (_ & _ & _ & _ & _ & _ & EQT & _). unfold lastq. rewrite EQT. reflexivity. Qed.

Lemma rpins_C : ltac2:(tb__ "0|0|
SaS44R1VA;A2S7aR2VA';Vp;Vn;Vr;A5F_;Ff;").
Proof.
  intros f QC. pose proof HDO as (EG & _ & _ & _ & _ & _ & EQT & _).
  unfold rpins. cbn zeta. rewrite !HRW, EG.
  split; [change (rw rho1 12%positive) with (rw rho 12%positive); rewrite <- Hp12; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [change (rw rho1 13%positive) with (rw rho 13%positive); rewrite <- Hn13; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact pin107|].
  split; [change (rw rho1 136%positive) with (Z_to_bv 64 (j_min jv)); rewrite HJM; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros ->. destruct QC as [[QN QK] _]. rewrite lastq_depot, EQT.
  split; [exact QN|]. split; [exact QK|].
  split; [|split; reflexivity].
  change (rw rho1 122%positive) with (Z_to_bv 64 (match aa_q_thread A with [] => j_qb jv | _ => qb_addr (lastq A) end)).
  destruct (aa_q_thread A); [exfalso; apply QN; reflexivity | reflexivity].
Qed.

Lemma cnt24_depot : ltac2:(tb__ "0|3|
S3S2S0S60S30VA';Z18M0A2M1A1S60S30VA;G0A2M2A1A3S2S0S63G1A1S63G2A1A3A2").
Proof.
  destruct HDO as (_ & EC & _). unfold cnt24, top24, cache24, refillA. cbn [aa_cls]. rewrite EC. split; reflexivity.
Qed.
Lemma cpins_C : ltac2:(tb__ "0|0|
S6aS8aR1S30VA';Z18A2Vp;Vn;Vr;A5Fq;").
Proof.
  intros q. pose proof HDO as (EG & _ & _ & _ & _ & _ & EQT & _). destruct cnt24_depot as [E1 E2].
  unfold cpins. cbn zeta. rewrite !HRW, E1, E2. change (aa_geom (refillA A' 24)) with (aa_geom A'). rewrite EG.
  split; [change (rw rho1 12%positive) with (rw rho 12%positive); rewrite <- Hp12; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [change (rw rho1 13%positive) with (rw rho 13%positive); rewrite <- Hn13; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  change (aa_q_thread (refillA A' 24)) with (aa_q_thread A'). change (lastq (refillA A' 24)) with (lastq A'). rewrite lastq_depot, EQT. intros QN.
  change (rw rho1 122%positive) with (Z_to_bv 64 (match aa_q_thread A with [] => j_qb jv | _ => qb_addr (lastq A) end)).
  destruct (aa_q_thread A); [exfalso; apply QN; reflexivity | reflexivity].
Qed.
End PINS.

Definition qC (f : bool) : qvar := if f then QBf else QBe.
Lemma qC_ne : ltac2:(tb__ "0|0|
SaS7S2S6aS52R1A1S6cA3A1Ff;"). Proof. intros [|]; discriminate. Qed.
Lemma qcond_refill : ltac2:(tb__ "0|0|
SaS1fS1fS16S9S2eQ40A1A1S4cS4aS8R5R3R2R1A5S44R7R6A2S4S2S1fR6R7A3S31R7R6A2A2S62S52R9A1S30R7Z18A2A2F_;F_;F_;Fmd;Ftp;Frho;FA';FA;Ff;").
Proof.
  intros f A A' rho tp md HA [QT HC0] HDO. pose proof (cnt24R A rho tp md 0 HA 0 HC0) as C1.
  assert (EE : cnt24 (refillA A' 24) = cnt24 (refillA A 24) /\ lastq A' = lastq A /\ aa_q_thread A' = aa_q_thread A).
  { destruct HDO as [->|HDO]; [repeat split|]. split; [exact (proj1 (cnt24_depot A A' HDO))|]. split; [exact (lastq_depot A A' HDO)|].
    destruct HDO as (_ & _ & _ & _ & _ & _ & EQT & _). exact EQT. }
  destruct EE as (E1 & ELQ & EQT). rewrite <- E1 in C1.
  assert (NE : cache24 (refillA A' 24) <> []) by (intros E; unfold cnt24 in C1; rewrite E in C1; cbn in C1; discriminate C1).
  destruct f; cbn [qC qcond].
  - destruct QT as [QN QK]. change (aa_q_thread (refillA A' 24)) with (aa_q_thread A'). change (lastq (refillA A' 24)) with (lastq A'). rewrite ELQ, EQT.
    split; [exact QN|]. split; [exact QK|]. split; [reflexivity | exact NE].
  - change (aa_q_thread (refillA A' 24)) with (aa_q_thread A'). rewrite EQT. split; [exact QT|]. split; [reflexivity | exact NE].
Qed.

Lemma cache24_uninit : ltac2:(tb__ "0|0|
S1fS16S9S2eQ40A1A1S4cS4aS8R4R3R2R1A5S2SaS22R5A1SfA3S2S9S0A1S5fR6A1SdS0A1A3F_;F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA Hci. pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & HPR & _).
  destruct HPR as (PL & _ & _ & PC). pose proof (PC 24 ltac:(lia)) as P24. unfold class_repr in P24.
  repeat match type of P24 with _ /\ _ => destruct P24 as [?X P24] end.
  match goal with H : aa_cache_inited A = false -> _ |- _ => exact (proj1 (H Hci)) end.
Qed.
Lemma qcondC_split : ltac2:(tb__ "0|0|
S1fS16S9S2eQ40A1A1S4cS4aS8R4R3R2R1A5S3S4S2S9S21A1S26R5A1SdS21A1A3S2S0S8dS15SeS0S0A2S28S5eR5A1A1A2A1S7cA3A2S4S2SaS22R5A1SfA3S2S9S0A1S5fR5A1SdS0A1A3A2A2S4S44SfR6A2S44ScR6A2A2F_;F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA [HQ HC].
  assert (HC0 : cache24 A = []) by (destruct HC as [HC|HC]; [exact (cache24_uninit A rho tp md HA HC) | exact HC]).
  destruct (aa_q_thread A) as [|b0 l0] eqn:EQ.
  - left. split; [exact EQ | exact HC0].
  - right. split; [|exact HC0]. split; [rewrite EQ; discriminate|]. destruct HQ as [HQ|HQ]; [discriminate HQ | exact HQ].
Qed.

Lemma post_refill : ltac2:(tb__ "0|4|
S9SeS0S0A2A1M0G0S13S1fS3bS16S9S2eQ40A1A1S4dS58S8S73R3R2SbSeS2aS57A2M1S11S2aS57S3eS39S38R6A1S37A3S3dS4aS8A1M2R8R7S30R5Z18A2R4A5A4SdG1A1M3A3R1A6S58S8S73R4R3SbG1S11S2aS57S3eS39S38R7A1S37A3S3dG2R9R8R6R5A5A4G3A3R2A6F_;Fw;Ftp;Frho;FKc;FA;FnW;FXGL;FCST;").
Proof.
  intros CST XGL nW A Kc rho tp w (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  destruct Hin as [E|[]]. injection E as <- <-.
  exists (L_free AE_A (Wcan nW) UStopLe), (JL_free (AInvA segsA) CST XGL A Kc), rho', tp'.
  split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|].
  destruct HJL as (A' & l1 & l2 & HA' & ELV & ELV' & EF & EV & EKm & EKf & EG & MK & HKc & CK).
  exists A', l1, l2. split; [exact HA'|]. split; [exact ELV|]. split; [exact ELV'|]. split; [exact EF|]. split; [exact EV|]. split; [exact EKm|].
  split; [exact EKf|]. split; [exact EG|]. split; [exact MK|]. split; [exact HKc|].
  intros c Hc Hne HF. apply (CK c Hc Hne). unfold class_fresh, refillA in *. cbn [aa_cls].
  rewrite nth_list_upd_other; [exact HF|]. change (Z.to_nat 24) with 24%nat. intros E. apply Hne. clear -E Hc. lia.
Qed.

Definition entry_pureC (khi : bool) (W : list ulink) (st : ustop) (f : bool) (A : AA) (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S2fQ40M0S17Vrho;PcA2A2S0S2fG0S17Vrho;PdA2A2S0S3S71SeS0S0A2S11S0S0R2R1A4S20VA;A1A3S3S24VA;A1S3S5S9S2eG0A1A1M1G1S5S4cS4cS4aS8VA;Vrho;R2R1A5Lmd0;A2Ltp0;A2S5S0S0S5S5dS5dS3S85VA;Vrho;R4R3R2R1A6S3S2S0S61R1A1S7bA3S86Vkhi;VW;Vst;S48Vf;A1S49Vf;A1S43VA;Vrho;R4R3R2R1A6R4R3S87R3A1S29S25VA;A1A1AaA2A2Ljv;A2Lt;A2A2A2A2Tn;Tp;").
Lemma entry_pure_C : ltac2:(tb__ "0|1|
SaS9S41A1S42SaS1fS3bS16S9S2eQ40M0A1A1S4dS84R9S2fG0S17R3PcA2A2S2fG0S17R3PdA2A2A3S2SaS23R6A1ScA3S44R8R7A2S34S8S3aS4aS8A1RbRaR8R7A5S3fS39RbRaA3R6R5R4A6S53RdRcRbRaR9R7A6F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;Ff;Fst;FW;Fkhi;").
Proof.
  intros khi W st f A Kc rho tp w HK Hii QC [_ HJ]. destruct HJ as (HA & _ & HL & _ & _ & HB & _).
  split; [exact HL|]. split; [exact HB|]. split; [exists tp, (cfg_model (w_cfg w)); exact HA|].
  pose proof (cls_hyp_blk khi _ _ HK) as HCL.
  destruct (blkF_mem A rho tp _ _ _ HA HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp _ HA) as (jv & JM & Hjv).
  exists t, jv. split; [exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv)|]. split; [exact JM|].
  exact (instG_here_C A rho tp _ _ _ HA HL HCL Hii eq_refl eq_refl t (conj T1 (conj T2 (conj T3 T4))) jv Hjv f QC khi W st HK).
Qed.

Lemma mid_vars : ltac2:(tb__ "0|0|
S13S72R1U2A2S2SaS80S45S2bS65S38R2A1S37A2A1A2ScA3F_;FnW;").
Proof. intros [|[|[|nW]]] H; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exfalso; lia]. Qed.
Lemma mid_repin : ltac2:(tb__ "0|5|
S13S1fS3bS16S16S9S2eQ40A1M0A1S4dS72R7U2A2S1S2SaS45R1A1ScA3S2G0S17R7R2A2S17R6R2A2A3F_;Fi;S1S2S9S2eQ8A1M1A1S19R7R1A2S19R6R1A2A3Fl;S2G0S10G1A1F_;S1aR7A1S1aR6A1A3S34S8S3aS4aS8A1M2S38RbA1M3S37RaR9A5S65G3S37A2R8R6R5A6S34S8S3aG2S38RcA1M4S37RbRaA5S65G4S37A2R8R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Frho2';Frho2;FKc;FA;FnW;").
Proof.
  intros nW A Kc rho2 rho2' tp w HnW Hw Hl Hm [(Hsm & HMI & Hwf & Hsh & Hhz) HJ].
  assert (Hag : agree_below NF rho2 rho2').
  { split; [|split; [exact Hl | intros a; rewrite Hm; reflexivity]]. intros i Hi. apply Hw. unfold offp.
    destruct (Pos.eqb_spec i 127) as [->|_]; [exfalso; unfold NF in Hi; lia|]. destruct (Pos.eqb_spec i 130) as [->|_]; [exfalso; unfold NF in Hi; lia | reflexivity]. }
  split.
  - split; [exact (smatch_agree_vars segsA offp rho2 rho2' _ _ Hw Hl Hm (mid_vars nW HnW) Hsm)|]. split; [exact HMI|]. split; [exact Hwf|]. split; [|exact Hhz].
    unfold shadow_ok. cbn [Pre_mid ax_X]. apply Forall_nil.
  - exact (JFr_agree nW UStopLe true A Kc rho2 rho2' tp _ _ (stopJ_stable_le _) Hag HJ).
Qed.

Lemma repin_eqs : ltac2:(tb__ "0|2|
S1fS16S0S0S0S5dS2S16S64R6R5R4R3R2R1A6R5A3S3S1S2SaS45R1A1ScA3S2S2eQ40A1M0S17R8R2A2S17S43R9R8R7R6R5R4A6R2A2A3F_;Fi;S3S1S2S9S2eQ8A1M1A1S19R7R1A2S19S43R8R7R6R5R4R3A6R1A2A3Fl;S2G0S10G1A1F_;S1aR6A1S1aS43R7R6R5R4R3R2A6A1A3A2A2F_;Fjv;Ft;Fn;Fp;Frho2;FA;").
Proof.
  intros A rho2 p n t jv EID.
  split; [intros i Hi; rewrite (pins_off A rho2 p n t jv i Hi), EID; reflexivity|].
  split; [intros l; rewrite (pins_rl A rho2 p n t jv l), EID; reflexivity | rewrite (pins_rm0 A rho2 p n t jv); reflexivity].
Qed.

Section CT.
Variable nW : nat. Variable f : bool.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Variables (TM Erf EC : axst) (l5 : list leafA) (XR : list axform).
Hypothesis NX5 : ltac2:(tb__ "0|1|
S3S2SaS7dS76S1bS2bVTM;A1M0A1A2ScA3S2SaS1cG0A1SfA3A2").
Hypothesis RUN5 : ltac2:(tb__ "0|0|
S2S9S2cA1S55S66SbS0S70SdS0A1A3VTM;A3Vl5;A3").
Hypothesis L5 : ltac2:(tb__ "0|0|
S3S2SaS67Vl5;SbS0S70SdS0A1A3A2ScA3S2S2aS54U0Vl5;A2VErf;A3A2").
Hypothesis AXR : ltac2:(tb__ "0|0|
S2S10S2aA1S5cVErf;VXR;A2S12S2aVEC;A2A3").

Variables (T0 T1 T2 TR : axst) (sR : wsub) (RR KEPT KEPT1 : list sobj) (XS : list axform) (eFR : sv).
Hypothesis HER : ltac2:(tb__ "0|1|
S2S10S9S18A1M0A1S5aVEC;S6eVsR;A3S12G0VRR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S2SaS59VEC;S6eVsR;VRR;SbS2aS6fSdS2aA1A3A5ScA3").
Hypothesis OBJS : ltac2:(tb__ "0|0|
S2S9S18A1S1dS2bVEC;A1A1S14S18VKEPT;VRR;A3A3").
Hypothesis HT0 : ltac2:(tb__ "0|0|
S2S2aVT0;S81S5bVsR;S6eS6fVEC;VRR;A5S1eS2bVEC;A1A1A2A3").
Hypothesis HXS : ltac2:(tb__ "0|0|
S2S10S2aA1S5cVT0;VXS;A2S12S2aVT1;A2A3").
Hypothesis OBJS1 : ltac2:(tb__ "0|0|
S2S9S18A1S1dS2bVT1;A1A1S14S18VKEPT1;SbS18S6bSbS18S74S46A1SbS18S74S47A1SdS18A1A3A3A3A3A3").
Hypothesis HT2 : ltac2:(tb__ "0|0|
S2S2aVT2;S2dVT1;S7fS2bVT1;A1VKEPT1;A2A2A3").
Hypothesis HTR : ltac2:(tb__ "0|2|
S2S2aVTR;S77VT2;SbS75S78VeFR;S1bS2bVT1;A1A1M0S7eG0A1M1A3SdS75A1A3S7eG1A1A3A3").
Hypothesis RCHK : ltac2:(tb__ "0|0|
S2SaS79VnW;Vf;VEC;VT1;VTR;VsR;VRR;VeFR;A8ScA3").

Variables (TRs Erq Erq2 TQ Edr Xf : axst) (l5d l6 : list leafA) (XWl : list axform).
Hypothesis HTRs : ltac2:(tb__ "0|0|
S2S2aVTRs;S77VTR;S88S1bS2bVTR;A1A1A3A3").
Hypothesis CCHK : ltac2:(tb__ "0|0|
S2SaS89VnW;S52Vf;A1VTR;VTRs;A4ScA3").
Hypothesis RUN5d : ltac2:(tb__ "0|0|
S2S9S2cA1S55S66SbS0S56SdS0A1A3VTRs;A3Vl5d;A3").
Hypothesis L5d : ltac2:(tb__ "0|0|
S3S2SaS67Vl5d;SbS0S56SdS0A1A3A2ScA3S2S2aS54U0Vl5d;A2VErq;A3A2").
Hypothesis AXW : ltac2:(tb__ "0|0|
S2S10S2aA1S5cVErq;VXWl;A2S12S2aVErq2;A2A3").
Hypothesis ENTQ : ltac2:(tb__ "0|0|
S2SaS6dVErq2;VTQ;A2ScA3").
Hypothesis NX6 : ltac2:(tb__ "0|1|
S3S2SaS7dS76S1bS2bVTQ;A1M0A1A2ScA3S2SaS1cG0A1SfA3A2").
Hypothesis RUN6 : ltac2:(tb__ "0|0|
S2S9S2cA1S55S66SbS0S68SbS0S69SdS0A1A3A3VTQ;A3Vl6;A3").
Hypothesis L6 : ltac2:(tb__ "0|0|
S3S2SaS67Vl6;SbS0S68SbS0S69SdS0A1A3A3A2ScA3S3S2S2aS54U0Vl6;A2VEdr;A3S2S2aS54U1Vl6;A2VXf;A3A2A2").

Section SITE.
Variables (A : AA) (Kc : KcA) (rho : valuation) (p n t : Z) (jv : junkF) (tp0 : list word) (md0 : Model).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HA0 : ltac2:(tb__ "0|0|
S4aS8VA;Vrho;Vtp0;Vmd0;A5").
Hypothesis HB : budget_ok_free A.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S2S0S2fQ40S17Vrho;PcA2A2Vp;A3").
Hypothesis Hn13 : ltac2:(tb__ "0|0|
S2S0S2fQ40S17Vrho;PdA2A2Vn;A3").
Hypothesis HL : ltac2:(tb__ "0|0|
S71SeS0S0A2S11S0S0Vp;Vn;A4S20VA;A1A3").
Hypothesis HCL : blk_cls p n.
Hypothesis Hii : aa_internal_inited A = true.
Hypothesis QC : qcondCx f A.
Hypothesis HR : ltac2:(tb__ "0|0|
S33Vrho;S43VA;Vrho;Vp;Vn;Vt;Vjv;A6A2").
Hypothesis HJM : ltac2:(tb__ "0|0|
S2S0S61Vjv;A1S7bA3").

Lemma virt_pure : ltac2:(tb__ "0|1|
S3S71SeS0S0A2S11S0S0Vp;Vn;A4S20S30VA;Z18A2M0A1A3S3S2SaS23G0A1ScA3S62S52Vf;A1G0A2A2A2").
Proof. split; [exact HL|]. split; [exact Hii|]. exact (qcond_refill f A A rho tp0 md0 HA0 QC (or_introl eq_refl)). Qed.

Theorem c_tail : ltac2:(tb__ "0|7|
S4dOF_;S50S36S8R2S35VKc;A1M0A3S82S8R3G0A3S1fS16S16S9S2eQ40A1A1M1S31S30VA;Z18A2R4A2M2S4bS51VCST;VXGL;VA;A3M3S43VA;Vrho;Vp;Vn;Vt;Vjv;A6M4R4A3M5S4fS8RaS34S8S32VnW;S37SfR6VKc;R5A6M6VEdr;R4R3A5R9A4F_;F_;FtpE;FrhoE;Fr2;FA2;S1fS16S16G1G2G5S4fS8RbS34S8G6VXf;R4R3A5RaA4F_;F_;FtpE;FrhoE;Fr2;FA2;S1fS16G1S31VA;R3A2S4bG3G4R3A3S16S4fS8RcS34S8G6VTM;R1R4A5RbA4FrhoM;F_;F_;FtpM;Frho1';FA';F_;F_;F_;F_;FQ;Fok;").
Proof.
  intros ok Q Hok Hokp HDR HXF A' rho1' tpM HDO HLK.
  assert (HUS : stopJ_stable (Wcan nW) UStopLe) by apply stopJ_stable_le.
  destruct (in_split _ _ HL) as (l1 & l2 & ELV).
  pose proof HDO as (_ & ECLS & _ & _ & _ & EL & _ & _ & EII & _).
  assert (HLV' : aa_live A' = l1 ++ (p, n) :: l2) by (rewrite EL; exact ELV).
  assert (Hii' : aa_internal_inited A' = true) by (rewrite EII; exact Hii).
  assert (HC0' : cache24 A' = []) by (unfold cache24; rewrite ECLS; exact (proj2 QC)).
  apply (f0_s5c nW TM Erf EC l5 XR NX5 RUN5 L5 AXR ok A' Kc rho1' tpM Q HKc Hok). intros rhoE.
  apply (refill_call_HRF nW f CST XGL HCST HXGL EC T0 T1 T2 TR sR RR KEPT KEPT1 XS eFR HER Hchk OBJS HT0 HXS OBJS1 HT2 HTR RCHK A' Kc rho1' p n l1 l2 HKc HLV' HCL Hii' HC0'
           (rpins_C A rho p n t jv Hp12 Hn13 HJM HR A' rho1' HDO (proj1 HLK) f QC) (budget_depot A A' HB HDO) ok Q Hok Hokp rhoE tpM).
  intros rho1'' rhoX tp' HLK2.
  assert (HL2 : In (p, n) (aa_live (refillA A' 24))) by (change (aa_live (refillA A' 24)) with (aa_live A'); rewrite EL; exact HL).
  apply (f0_s5d nW (qC f) (qC_ne f) TR TRs Erq Erq2 TQ l5d XWl HTRs CCHK RUN5d L5d AXW ENTQ (refillA A' 24) Kc rho1'' p n HKc HL2 HCL Hii'
           (qcond_refill f A A' rho tp0 md0 HA0 QC (or_intror HDO))
           (cpins_C A rho p n t jv Hp12 Hn13 A' rho1'' HDO (fun i => eq_trans (proj1 HLK2 i) (proj1 HLK i)) (qC f)) ok tp' Q Hok).
  intros rhoQ.
  pose proof (hd_link_trans (KEEPD CST XGL A) (KEEPD CST XGL A') _ _ _ (fun a H => KEEPD_depot CST XGL A A' a HDO H) HLK HLK2) as HLK3.
  apply (f0_s6 nW UStopLe false TQ Edr Xf l6 NX6 RUN6 L6 ok (refillA A' 24) Kc rho1'' tp' Q HUS HKc Hok).
  - intros rhoE2. exact (HDR (refillA A' 24) rho1'' rhoE2 tp' (depot_refill A A' HDO) HLK3).
  - intros rhoE2. exact (HXF (refillA A' 24) rho1'' rhoE2 tp' (depot_refill A A' HDO) HLK3).
Qed.
Theorem ec_tail : ltac2:(tb__ "0|6|
S4dOF_;S1fS16S16S9S2eQ40A1A1M0S31S30VA;Z18A2R4A2M1S4bS51VCST;VXGL;VA;A3M2S43VA;Vrho;Vp;Vn;Vt;Vjv;A6M3R4A3M4S4eS8S34S8S32VnW;S37SfR6VKc;R5A6M5VEdr;R4R3A5R7A3F_;F_;FtpE;FrhoE;Fr2;FA2;S1fS16S16G0G1G4S4eS8S34S8G5VXf;R4R3A5R8A3F_;F_;FtpE;FrhoE;Fr2;FA2;S1fS16G0S31VA;R3A2S4bG2G3R3A3S16S4eS8S34S8G5VTM;R1R4A5R9A3FrhoM;F_;F_;FtpM;Frho1';FA';F_;F_;FQ;").
Proof.
  intros Q HDR HXF A' rho1' tpM HDO HLK.
  assert (HUS : stopJ_stable (Wcan nW) UStopLe) by apply stopJ_stable_le.
  destruct (in_split _ _ HL) as (l1 & l2 & ELV).
  pose proof HDO as (_ & ECLS & _ & _ & _ & EL & _ & _ & EII & _).
  assert (HLV' : aa_live A' = l1 ++ (p, n) :: l2) by (rewrite EL; exact ELV).
  assert (Hii' : aa_internal_inited A' = true) by (rewrite EII; exact Hii).
  assert (HC0' : cache24 A' = []) by (unfold cache24; rewrite ECLS; exact (proj2 QC)).
  apply (ef0_s5c nW TM Erf EC l5 XR NX5 RUN5 L5 AXR A' Kc rho1' tpM Q HKc). intros rhoE.
  apply (refill_call_HRFE nW f CST XGL HCST HXGL EC T0 T1 T2 TR sR RR KEPT KEPT1 XS eFR HER Hchk OBJS HT0 HXS OBJS1 HT2 HTR RCHK A' Kc rho1' p n l1 l2 HKc HLV' HCL Hii' HC0'
           (rpins_C A rho p n t jv Hp12 Hn13 HJM HR A' rho1' HDO (proj1 HLK) f QC) (budget_depot A A' HB HDO) Q rhoE tpM).
  intros rho1'' rhoX tp' HLK2.
  assert (HL2 : In (p, n) (aa_live (refillA A' 24))) by (change (aa_live (refillA A' 24)) with (aa_live A'); rewrite EL; exact HL).
  apply (ef0_s5d nW (qC f) (qC_ne f) TR TRs Erq Erq2 TQ l5d XWl HTRs CCHK RUN5d L5d AXW ENTQ (refillA A' 24) Kc rho1'' p n HKc HL2 HCL Hii'
           (qcond_refill f A A' rho tp0 md0 HA0 QC (or_intror HDO))
           (cpins_C A rho p n t jv Hp12 Hn13 A' rho1'' HDO (fun i => eq_trans (proj1 HLK2 i) (proj1 HLK i)) (qC f)) tp' Q).
  intros rhoQ.
  pose proof (hd_link_trans (KEEPD CST XGL A) (KEEPD CST XGL A') _ _ _ (fun a H => KEEPD_depot CST XGL A A' a HDO H) HLK HLK2) as HLK3.
  apply (ef0_s6 nW UStopLe false TQ Edr Xf l6 NX6 RUN6 L6 (refillA A' 24) Kc rho1'' tp' Q HUS HKc).
  - intros rhoE2. exact (HDR (refillA A' 24) rho1'' rhoE2 tp' (depot_refill A A' HDO) HLK3).
  - intros rhoE2. exact (HXF (refillA A' 24) rho1'' rhoE2 tp' (depot_refill A A' HDO) HLK3).
Qed.
End SITE.
End CT.
End F0A_asmC.

