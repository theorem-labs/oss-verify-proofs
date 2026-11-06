(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "prod"; "nil"; "bool"; "app"; "list"; "false"; "true"; "andb"; "option"; "fst"; "length"; "snd"; "Some"; "negb"; "None"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sobj"; "SAlu"; "sprop"; "ss_objs"; "SPUle"; "sv_eqb"; "ob_hi"; "ob_lo"; "ob_base"; "ss_facts"; "SExt"; "SPAlign"; "SPBranch"; "SPNot"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_regs"; "ss_resv"; "sstate"; "valuation"; "SPUlt"; "ss_pc"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "ax_X"; "axwf"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "AXRebase"; "AXUnbase"; "AXMerge"; "AXSplit"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "skipn"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "eqb"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs"; "ref3"; "S7"; "TQPs"; "refo"; "selby"; "szMS"; "E8"; "REF_IN"; "VK7"; "XROs"; "chkS"; "cntS"; "mcS"; "optA"; "vCHq"; "D2S"; "FFM"; "L1h"; "N_M"; "PreD"; "REF_K8"; "VSM"; "XC1"; "dstM"; "entG"; "hdrS0"; "is3P'"; "magS0"; "pgbS"; "rieS0"; "run8"; "slotG"; "stqS0"; "BSM"; "F_OUT"; "NQW_M"; "NRO_M"; "NX7"; "N_OUT"; "PCS"; "PostD"; "REF_FR"; "REF_ITM"; "REF_ITM2"; "REF_OUT"; "S6h"; "SFREF"; "STK_M"; "XIN"; "XM1_of"; "ZD_K"; "ZD_KO"; "ZD_M"; "ZD_OUT"; "ZD_PC"; "ZD_XRO"; "callee_savedb"; "cfbS"; "cfcS"; "chk_cells"; "dstOS"; "dst_cellsM"; "entH"; "gmaxMS"; "hdrP"; "isfrM"; "magP"; "memNb"; "mtxMS"; "obj_specM"; "perm_fr"; "regs7"; "riMS"; "riOS"; "stqP"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "aluop"; "mulop"; "BC_EQ"; "ALU_XOR"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "entQ"; "N_rti"; "O_ishQ"; "DQI0"; "ZD_fix"; "ZD_rti"; "rieQ"; "zbQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "QG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "vmap"; "chkNM"; "entsM"; "keepsM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "vMFA"; "vNF"; "vAU"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "idxs"; "DH_ENT"; "DH_RET"; "F_fast"; "L_dh_f"; "Pre_dh_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQIF_defs"; "TQPf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "NPRE"; "add"; "leaf"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "vIT"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "add"; "le"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "TP_A";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue"; "addF"; "addO"; "dobj"; "dropN"; "dspec"; "forallb2"; "keepN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_env"; "findiP"; "N_itmF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states"; "QIRET"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib"; "mkST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "JOK"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG"; "F_grow"; "L_dh_g"; "Pre_dh_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs"; "Cqi"; "TQIf"; "@Stdlib.Lists.List"; "In"; "forallb"; "removelast"; "rev"; "tl"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQS_lib RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_env.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_env.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ls.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition vCHq (i : nat) : sv := SVar (Pos.of_nat (231 + i)).
Definition chk_cells (n : Z) : list (Z * nat * sv) := ltac2:(tb__ "0|1|
S42S5S6S6S0S5A2M0S16A2S5S4G0S16S4S0S5S46Z10S47Z4S46Vn;S49R1A1A2A2A2U4A4S58R1A1A4Li;Sb0Vn;A1A4").
Definition dstM : sv := ltac2:(tb__ "0|0|
S1aS95S1aS95SbbS1aS95S1aS96S18Pc8A1S17Z20A1A3S17Ze0000000A1A3A3S1aS96SadS17Z2A1A3A3").
Definition pgbS : carve_spec := ltac2:(tb__ "0|4|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0S17Z0A1Z17db60M3A4Z17db68A4S3G2S4G1S16S4S0S5G3U8A4S17SdfA1A4S7G2A1A3A4").
Definition cfcS : carve_spec := ltac2:(tb__ "0|5|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0S17Z0A1M3Z17fcecM4A4Z17fcedA4S3G2S4G1S16S4S0S5G4U1A4G3A4S7G2A1A3A4").
Definition cfbS : carve_spec := ltac2:(tb__ "0|5|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0S17Z0A1M3Z17fc78M4A4Z17fc80A4S3G2S4G1S16S4S0S5G4U8A4G3A4S7G2A1A3A4").
Definition XROs (g : bool) : list carve_spec := ltac2:(tb__ "0|1|
S8SaS33A1Lg;Vg;S3S33S66S3S33S84S3S33S83S7S33A1M0A3A3A3S3S33S66G0A3X8x2").
Definition chkS (n : Z) : carve_spec := ltac2:(tb__ "0|2|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2S16A2A1S4G0S0S4S16S0S9eS46Z10M1S47Z4Vn;A2A2A4S46G1S47Z8Vn;A2A2A4S85Vn;A1A4").
Definition mcS (n : Z) : carve_spec := ltac2:(tb__ "0|4|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0S9eZ4M3A4Z8A4S3G2S4G1S16S4S0S5G3U4A4S17S47Z2Vn;A2A1A4S7G2A1A3A4").
Definition cntS (k : Z) : carve_spec := ltac2:(tb__ "0|4|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0S9eZ0M3A4Z4A4S3G2S4G1S16S4S0S5G3U4A4S17Vk;A1A4S7G2A1A3A4").
Definition szMS : carve_spec := ltac2:(tb__ "0|4|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0S9eZ8M3A4Z10A4S3G2S4G1S16S4S0S5G3U8A4S18Pc9A1A4S7G2A1A3A4").
Definition riMS : carve_spec := ltac2:(tb__ "0|6|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0SafZ0M3A4Z80A4S3G2S4G1S16S4S0S5G3U8M4A4S17G3A1M5A4S3G2S4G1S16S4S0S5Z10G4A4SadA4S3G2S4G1S16S4S0S5Z18G4A4SacA4S3G2S4G1S16S4S0S5Z20G4A4SaeA4S3G2S4G1S16S4S0S5Z28G4A4G5A4S3G2S4G1S16S4S0S5Z30G4A4S18Pe0A1A4S3G2S4G1S16S4S0S5Z38G4A4G5A4S3G2S4G1S16S4S0S5Z44U1A4G5A4S7G2A1A3A3A3A3A3A3A3A3A4").
Definition PCS (n : Z) : list carve_spec := ltac2:(tb__ "0|0|
S3S33S54Vn;A1S3S33S56Vn;A1S3S33S55S47Z2Vn;A2A1S3S33S4fS7S33A1A3A3A3A3").
Definition N_M (n : Z) (g : bool) : list carve_spec := ltac2:(tb__ "0|6|
S9S33S53Vg;A1S9S33S71Vn;A1S9S33S3S33S92S7S33A1M0A3S8SaS33A1Lg;Vg;G0S3S6S6S6S16S0A2M1S0A2M2SaS6S6S0S5A2S16A2M3A1M4A2M5S4G2G4S4G1S0S4S16S0S61Z0A4S47Z4Vn;A2A4S7G3A1A4S7G5A1A3X8x2A3A3A3").
Definition BSM (n : Z) : list positive := ltac2:(tb__ "0|0|
S9S1S3S1PddS3S1PdeS3S1PdfS3S1Pe0S3S1Pe1S7S1A1A3A3A3A3A3S42S5S1S5SbdSc0Ue7R1A2A1Li;Sb0Vn;A1A4A3").
Definition FFM (n : Z) (g : bool) : list sprop := ltac2:(tb__ "0|0|
S3S1bS24Pe1Z7A2S3S1bS1dSadS17Z8000000A1A2S3S1bS24PdeZ12A2S3S1bS1dSacS17Z20000000A1A2S3S1bS8S1bLg;Vg;SdcVn;A1Sb3Vn;A1X8x2S3S1bS1dS17Z10000000000A1S18PaA1A2S7S1bA1A3A3A3A3A3A3").

Definition VSM : list positive := ltac2:(tb__ "0|0|
S3S1Pa0S3S1Pa1S3S1Pa2S3S1Pa3S3S1Pa4S3S1Pa5S3S1Pa6S3S1Pb8S3S1Pb9S3S1PbaS3S1PbbS3S1Pd0S3S1Pc8S3S1Pc9S3S1PcaS3S1PcbS3S1PccS3S1PcdS3S1PceS3S1PcfS3S1Pd1S3S1Pd2S3S1PddS3S1PdeS3S1PdfS3S1Pe0S3S1Pe1S3S1Pe7S3S1Pe8S3S1Pe9S3S1PeaS3S1PebS3S1PecS3S1PedS3S1PeeS7S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition is3P' (b lo hi : sv) (o : sobj) : bool := ltac2:(tb__ "0|0|
SdSdS1eS21Vo;A1Vb;A2S1eS20Vo;A1Vlo;A2A2S1eS1fVo;A1Vhi;A2A2").
Definition ref3 (k : carve_spec) : sv * sv * sv := ltac2:(tb__ "0|5|
S6S6S6S16S0A2M0S0A2M1SaS6S6S0S5A2S16A2A1M2A2S6S6S16S16A2M3S16A2M4Lk;Vk;G1G2G1G4Lp;R2G0S0G0G4Lp0;R2S16S0S4G3S16S4S16S16R2S17R1A1A4S17R3A1A4Llo;Lb;X6x1Lhi;Lp0;X6x1Ll;Lp;X6x1").
Definition refo (o : sobj) : sv * sv * sv := ltac2:(tb__ "0|0|
S4S6S16S16A2S16S4S16S16S21Vo;A1S20Vo;A1A4S1fVo;A1A4").
Definition selby (objs : list sobj) (refs : list (sv * sv * sv)) : list nat := ltac2:(tb__ "0|2|
S42S6S6S16S16A2M0S16A2M1S5G1G1S5Lr;R1G0S16G0S5Lp;R2S16S16ScdS64R2R1R3A3Vobjs;U0A3Llo;Lb;X6x1Lhi;Lp;X6x1Lr;Vrefs;A4").
Definition hdrS0 : carve_spec := ltac2:(tb__ "0|2|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2S16A2M1A1S4G0S0S4S16S0SbcZ0A4Z8A4S7G1A1A4").
Definition stqS0 : carve_spec := ltac2:(tb__ "0|2|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2S16A2M1A1S4G0S0S4S16S0Sc4Zad0A4Zc60A4S7G1A1A4").
Definition magS0 : carve_spec := ltac2:(tb__ "0|2|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2S16A2M1A1S4G0S0S4S16S0S18Pd2A1Z0A4Z10A4S7G1A1A4").
Definition rieS0 : carve_spec := ltac2:(tb__ "0|4|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0Sa4Z30M3A4Z38A4S3G2S4G1S16S4S0S5G3U8A4S18PcaA1A4S7G2A1A3A4").
Definition REF_K8 : list (sv * sv * sv) := ltac2:(tb__ "0|0|
S42S19S6S6S16S16A2S16A2S4dS1cS35Sa1A1A1A4").
Definition REF_ITM (vb : bool) : list (sv * sv * sv) := ltac2:(tb__ "0|2|
S9S6S6S16S16A2S16A2M0S3G0S4aS63A1S3G0S4aS6aA1S7G0A1M1A3A3S9G0S8SaG0A1Lvb;Vvb;S3G0S4aS65A1G1A3G1X8x2S3G0S4dSa0A1G1A3A3A3").
Definition REF_IN (vb : bool) : list (sv * sv * sv) := ltac2:(tb__ "0|1|
S9S6S6S16S16A2S16A2M0S5eS9G0S42S33G0S4aS9fA4S9G0S74Vvb;A1S3G0S4aS67A1S7G0A1A3A3A3A3").
Definition optA (d : axst) (o : option axst) : axst := match o with Some Y => Y | None => d end.
Definition TQPs_of (vb : bool) : axst := ltac2:(tb__ "0|1|
S57Sb6Vvb;A1M0S3dG0S3S3bS3cS4eS1cS35G0A1A1S51Vvb;A1A2A1S7S3bA1A3A2A2").
Definition TQPs_a : axst := Eval vm_compute in (TQPs_of false).
Definition TQPs_b : axst := Eval vm_compute in (TQPs_of true).
Definition TQPs (vb : bool) : axst := if vb then TQPs_b else TQPs_a.
Definition XIN (vb : bool) : list axform := ltac2:(tb__ "0|0|
S3S3bS3cS4eS1cS35Sb6Vvb;A1A1A1S51Vvb;A1A2A1S7S3bA1A3").
Lemma TQPs_eq : ltac2:(tb__ "0|0|
S8S9bSeS36A1S3dSb6R1A1S7aR1A1A2S12S36S4cR1A1A2A3Fvb;"). Proof. intros [|]; vmr. Qed.
Lemma TQPs_shape : ltac2:(tb__ "0|2|
S8S9bS8ScbS19S6S6S16S16A2M0S16A2M1S19G1G1S8Lr;R1G0S16G0S8Lp;R2S16S16S64R2R1R3R6A4Llo;Lb;X6x1Lhi;Lp;X6x1Lr;Lo;S1cS35S4cR1A1A1A1S51R1A1A5ScA3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TQPs_objs : ltac2:(tb__ "0|9|
S8S0S9bSaS19A1S1cS35S4cR2A1M0A1A1S9S19SccG0U1A2S42ScaS19Sc8S3S6S6S6S6S16S0A2M1S0A2M2SaS6S6S0S5A2M3S16A2M4A1M5A2M6S0A2M7S4G6S0S4G2G5S4G1S0S4S16S0Sa4Z30M8A4Z38A4S3G4S4G3S16S4S0S5G8U8A4S18PcaA1A4S7G4A1A3A4R1A4S7G7A1A3A4A3A3Fa;Fvb;"). Proof. intros [|] a; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition NXM : positive := 340%positive.
Definition bumpM (X : axst) (nx : positive) : axst := ltac2:(tb__ "0|0|
S35VX;A1S2eS37VX;S27S31R1A1S2cR1A1S29R1A1S28R1A1S2dR1A1S1cR1A1S22R1A1Vnx;S2aR1A1A9A2TS;").
Definition S0M_of (n : Z) (g vb : bool) : axst := ltac2:(tb__ "0|0|
Sc6Sc7Sc9S4cVvb;A1U1A2S42S33S19S34S5cVn;Vg;A2A4A2S5aVn;Vg;A2A2").

Definition zhiM (z : nat) : Z := match z with 7%nat => 80 | 12%nat => 536870912 | _ => zhiQ z end.
Definition zbM (T CTX SB u ab TOP E SHU FA : Z) (z : nat) : Z := ltac2:(tb__ "0|1|
S5S0Lz;Vz;Sa5VT;VCTX;VSB;Vu;Vab;VTOP;VE;VE;VSHU;Vz;AaM0S5S5S0Ln;R1G0S5S5S0Ln0;R1G0S5S5S0Ln1;R1G0S5S5S0Ln2;R1G0S5S5S0Ln3;R1G0S5S5S0Ln4;R1G0S5S5S0Ln5;R1G0S5S5S0Ln6;R1G0S5S5S0Ln7;R1G0S5S5S0Ln8;R1G0S5S5S0Ln9;R1G0S5S5S0Ln10;R1VFA;S5G0Ln11;X5x2Ln10;X5x2Ln9;X5x2Ln8;X5x2Ln7;X5x2Ln6;X5x2Ln5;X5x2Ln4;X5x2Ln3;X5x2Ln2;X5x2Ln1;X5x2Ln0;X5x2Ln;X5x2").
Definition ZUM (vb : bool) : list nat := ltac2:(tb__ "0|1|
S9S5S3S5U0S3S5U1S3S5U2S3S5U3S3S5U4S3S5U5S3S5U6S3S5U7S3S5UcS7S5A1M0A3A3A3A3A3A3A3A3A3S8SaS5A1Lvb;Vvb;S3S5U9G0A3G0X8x2A3").
Definition ZD_K (vb : bool) : list zdesc := ltac2:(tb__ "0|4|
S9S9dSa2S9S9dSa3S9S6S6S5S0A2M0S0A2M1S3G1S4G0S0S4S5S0U3N10A4N8A4S3G1S4G0S0S4S5S0U1Zad0A4Zc60A4S7G1A1M2A3A3S9G1S8SaG1A1Lvb;Vvb;S3G1S4G0S0S4S5S0U9Z0M3A4Z10A4G2A3G2X8x2S3G1S4G0S0S4S5S0U4G3A4Z1f81A4G2A3A3A3A3A3").
Definition ZD_XRO (g : bool) : list zdesc := ltac2:(tb__ "0|5|
S8SaS9dA1Lg;Vg;S3S6S6S5S0A2M0S0A2M1S4G0S0S4S5S0U0M2Z17db60A4Z17db68A4M3S3G1S4G0S0S4S5S0G2Z17fcecA4Z17fcedA4S3G1S4G0S0S4S5S0G2Z17fc78A4Z17fc80A4S7G1A1M4A3A3A3S3G1G3G4A3X8x2").
Definition ZD_PC (n : Z) : list zdesc := ltac2:(tb__ "0|6|
S3S6S6S5S0A2M0S0A2M1S4G0S0S4S5S0U7M2S46Z10M3S47Z4M4Vn;A2A2A4S46G3S47Z8M5Vn;A2A2A4S3G1S4G0S0S4S5S0G2G4A4G5A4S3G1S4G0S0S4S5S0G2Z0A4G4A4S3G1S4G0S0S4S5S0G2G5A4G3A4S7G1A1A3A3A3A3").
Definition ZD_M (n : Z) (g : bool) : list zdesc := ltac2:(tb__ "0|4|
S9S9dS81Vg;A1S9S9dS80Vn;A1S9S6S6S5S0A2M0S0A2M1S3G1S4G0S0S4S5S0U5Z0M2A4Z1000A4S7G1A1M3A3S8SaG1A1Lg;Vg;G3S3G1S4G0S0S4S5S0UcG2A4Z20000000A4G3A3X8x2A3A3A3").
Definition T_in (n : Z) (g vb : bool) (S0 : axst) : strans := ltac2:(tb__ "0|0|
Sd0S4cVvb;A1U1S5cVn;Vg;A2S6bVn;A1S5aVn;Vg;A2VS0;SabS5fA1S7cVvb;A1S7eVn;Vg;A2A9").

Definition PreD (n : Z) (g : bool) : axst := ltac2:(tb__ "0|0|
S8S36Lg;Vg;SdeVn;A1Sb5Vn;A1X8x2").
Definition PostD (n : Z) (g : bool) : axst := ltac2:(tb__ "0|0|
S8S36Lg;Vg;SddVn;A1Sb4Vn;A1X8x2").
Definition hdrP : carve_spec := ltac2:(tb__ "0|5|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0SbcZ0M3A4Z8A4S3G2S4G1S16S4S0S5G3U4M4A4S1aS9aS23ScQ20S18PcbA1A3S17Z3A1A3A4S3G2S4G1S16S4S0S5Z4G4A4S18PccA1A4S7G2A1A3A3A4").
Definition stqP : carve_spec := ltac2:(tb__ "0|3|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0Sc4Zad0A4Zc60A4S3G2S4G1S16S4S0S5Zae0U8A4S18Pd1A1A4S7G2A1A3A4").
Definition magP : carve_spec := ltac2:(tb__ "0|5|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0S18Pd2A1Z0M3A4Z10A4S3G2S4G1S16S4S0S5G3U8M4A4S17G3A1A4S3G2S4G1S16S4S0S5Z8G4A4SbcA4S7G2A1A3A3A4").
Definition mtxMS : carve_spec := ltac2:(tb__ "0|6|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0S17Z0A1M3S46Sa6Z98A2M4A4S46Sa6Z9cA2A4S3G2S4G1S16S4S0S5S46Sa6Z99A2U1M5A4G3A4S3G2S4G1S16S4S0S5G4G5A4G3A4S3G2S4G1S16S4S0S5S46Sa6Z9aA2U2A4G3A4S7G2A1A3A3A3A4").
Definition gmaxMS : carve_spec := ltac2:(tb__ "0|5|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0S17Z0A1S46Sa6Z40A2M3A4S46Sa6Z50A2A4S3G2S4G1S16S4S0S5G3U8M4A4S17Z10000000A1A4S3G2S4G1S16S4S0S5S46Sa6Z48A2G4A4S18Pd0A1A4S7G2A1A3A3A4").

Definition NRO_M (g : bool) : list carve_spec := ltac2:(tb__ "0|1|
S9S33S3S33S8eS3S33S89S7S33A1M0A3A3S9S33S8SaS33A1Lg;Vg;G0S45S33U2S9fA3X8x2S3S33S4fG0A3A3A3").
Definition NQW_M (g vb : bool) : list carve_spec := ltac2:(tb__ "0|2|
S9S33S8SaS33A1M0Lg;Vg;S7S33A1M1S3S33S94G1A3X8x2S9S33S3S33S8aG1A3S8G0Lvb;Vvb;S3S33S8cG1A3G1X8x2A3A3").
Definition STK_M : list (sv * sv * sv) := ltac2:(tb__ "0|6|
S3S6S6S16S16A2M0S16A2M1S4G0S16S4S16S16S1aS95S18PaA1M2S17Nc0A1M3A3S17N30A1A4S17Z0A1M4A4S3G1S4G0S16S4S16S16G2G3A4S17Nb8A1M5A4S3G1S4G0S16S4S16S16S1aS95G2G5A3G4A4S17Z10A1A4S3G1S4G0S16S4S16S16G2S17Na8A1A4G4A4S7G1A1A3A3A3A3").
Definition REF_FR (g vb : bool) : list (sv * sv * sv) := ltac2:(tb__ "0|1|
S9S6S6S16S16A2S16A2M0S79S9G0S42S33G0S4aS9S33S6eVg;A1S6dVg;Vvb;A2A3A4S3G0S4dSa0A1S7G0A1A3A3A3").
Fixpoint memNb (i : nat) (l : list nat) : bool := match l with [] => false | j :: t => Nat.eqb i j || memNb i t end.
Definition perm_fr (objs : list sobj) (refs : list (sv * sv * sv)) : list nat := ltac2:(tb__ "0|2|
S4eVobjs;Vrefs;A2SaS5A1M0S9S5Sd5S5G0Sd7S5A1S5Sd4S13S8dR1R2A2A1M1A1Li;S5Sd6G1A1Lx;S43U0S10S19Vobjs;A2A2A6R1A3Tf;").
Definition XC1 : list axform := ltac2:(tb__ "0|2|
S3S3bS41U0M0S17N30M1A1A2S3S3bS3fG0G1A2S7S3bA1A3A3").
Definition XC_of (g vb : bool) (L1 : axst) : list axform := ltac2:(tb__ "0|0|
S9S3bS60S3S3bS3cS90S1cS35S57VL1;S3dVL1;S60A2A2A1A1S73Vg;Vvb;A2A2A1S7S3bA1A3A3").
Definition sF_of (n : Z) (g : bool) (C1 : axst) : wsub := ltac2:(tb__ "0|0|
S3S6S1S16A2S4S1S16P94S18Pc9A1A4Sd8P1S35VC1;A1S35S5dVn;Vg;A2A1A3A3").
Definition T1f_of (n : Z) (g : bool) (C1 : axst) (sF : wsub) (RF : list sobj) : axst := ltac2:(tb__ "0|0|
SdaSdbVsF;S5dVn;Vg;A2S72Vn;Vg;A2VC1;VRF;A5S22S35VC1;A1A1A2").

Definition SFREF (n : Z) (g : bool) : list (positive * sv) := ltac2:(tb__ "0|d|
S9S6S1S16A2M0S3G0S4S1S16PaM1S1aS95S18G1A1S17Nf0A1A3A4S3G0S4S1S16PfM2S1aS95S18G2A1S17Zf0A1A3A4S3G0S4S1S16P18M3S8S16Lg;Vg;S18G3A1S17Sc5A1X8x2A4S3G0S4S1S16P97M4S18G4A1A4S3G0S4S1S16P98M5S18G5A1A4S3G0S4S1S16P9bM6S18G6A1A4S3G0S4S1S16P9cM7S18G7A1A4S3G0S4S1S16P9eS18Pc8A1A4S3G0S4S1S16P94S18Pc9A1A4S3G0S4S1S16PddM8S18G8A1A4S3G0S4S1S16PdeM9S18G9A1A4S3G0S4S1S16PdfMaS18GaA1A4S3G0S4S1S16Pe0MbS18GbA1A4S3G0S4S1S16Pe1McS18GcA1A4S7G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3S42S5G0S5S4S1S16SbdSc0UaaR1A2A1S58R1A1A4Li;Sb0Vn;A1A4A3").
Definition sF_okb (n : Z) (g : bool) (sF : wsub) : bool := ltac2:(tb__ "0|1|
Se3S6S1S16A2M0G0S1eSd9VsF;SfS1S16R1A3A2S11S1S16R1A3A2Lp;S78Vn;Vg;A2A3").

Definition riOS (n : Z) (g : bool) : carve_spec := ltac2:(tb__ "0|6|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0SafZ0M3A4Z80A4S3G2S4G1S16S4S0S5G3U8M4A4S17G3A1M5A4S3G2S4G1S16S4S0S5Z10G4A4S1aS95SadS17Vn;A1A3A4S3G2S4G1S16S4S0S5Z18G4A4S8S16Lg;Vg;S1aS95SacS17Z40000A1A3SacX8x2A4S3G2S4G1S16S4S0S5Z20G4A4SaeA4S3G2S4G1S16S4S0S5Z28G4A4G5A4S3G2S4G1S16S4S0S5Z30G4A4S18Pe0A1A4S3G2S4G1S16S4S0S5Z38G4A4G5A4S3G2S4G1S16S4S0S5Z44U1A4G5A4S7G2A1A3A3A3A3A3A3A3A3A4").
Definition dst_cellsM (n : Z) : list (Z * nat * sv) := ltac2:(tb__ "0|2|
Se5S6S6S0S5A2M0S16A2M1S42S5G1S5S4G0S16S4S0S5S47Z4S49R1A1A2U4A4S23ScQ20S58R1A1A3A4Li;Sb0Vn;A1A4A2").
Definition dstOS (n : Z) : carve_spec := ltac2:(tb__ "0|1|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2S16A2A1S4G0S0S4S16S0S61Z0A4S47Z4Vn;A2A4S87Vn;A1A4").
Definition D2S (n : Z) (g : bool) : list carve_spec := ltac2:(tb__ "0|0|
S9S33S53Vg;A1S3S33S54Vn;A1S3S33S56Vn;A1S3S33S55Vn;A1S3S33S4fS7S33A1A3A3A3A3A3").
Definition isfrM (o : sobj) : bool := ltac2:(tb__ "0|a|
S16S8Lx;M0S20Vo;A1S0G0S1fVo;A1S0SdS48R2N30A2S48R1Z0A2A2Lb;S1SbLi;M1S97S16S16SbLb;M2La0;M3Lop;M4G4S98G3Lop;M5G5S8S2S16SbLa0;Lw;Lsgn;S1S16S0SbLk;Li;Ll;M6X16x8La;G1S97S16G2La;M7Lop;M8G8S98G7Lop;M9G9S8S2S16SbLa;Lw;Lsgn;G6X16x8").
Definition XM1_of (T1f : axst) : list axform := ltac2:(tb__ "0|2|
S1cS35VT1f;A1A1SaS19A1ScdS8bR1U0M0A3S5S3S3bS3cS3S5G0S3S5R1Sd5S5SaS5A1Sd7S5A1S5Sd4S13S15Sd3R1G0A2Sd3R1R2A2A2A1M1A1Li;S5Sd6G1A1Lx;S43G0S10S19R2A2A2A6A3A3A1S3S3bS3eG0A1S3S3bS3eU1A1S3S3bS40G0A1S3S3bS3fG0Nc0A2S7S3bA1A3A3A3A3A3Tf;Tobjs;").
Definition REF_ITM2 (vb : bool) : list (sv * sv * sv) := ltac2:(tb__ "0|2|
S9S6S6S16S16A2S16A2M0S3G0S4aS63A1S3G0S4aS6aA1S7G0A1M1A3A3S8SaG0A1Lvb;Vvb;S3G0S4aS65A1G1A3G1X8x2A3").

Definition REF_OUT (n : Z) (g vb : bool) : list (sv * sv * sv) := ltac2:(tb__ "0|2|
S9S6S6S16S16A2S16A2M0S3G0S4dSa0A1S7G0A1M1A3S9G0S5eS9G0S42S33G0S4aS9fA4S9G0S75Vvb;A1S9G0S42S33G0S4aS59Vn;Vg;A2A4S3G0S4aS93Vn;Vg;A2A1S3G0S4aS86Vn;A1A1G1A3A3A3A3A3A3A3").
Definition XX_of (n : Z) (g vb : bool) (T1f : axst) : list axform := ltac2:(tb__ "0|1|
S9S3bS7bVT1f;A1M0S3S3bS3cS4eS1cS35S57VT1f;S3dVT1f;G0A2A2A1A1S76Vn;Vg;Vvb;A3A2A1S7S3bA1A3A3").

Definition entH : carve_spec := ltac2:(tb__ "0|6|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0S9eZ0M3A4Z10A4S3G2S4G1S16S4S0S5G3U4M4A4S18PcfA1M5A4S3G2S4G1S16S4S0S5Z4G4A4G5A4S3G2S4G1S16S4S0S5Z8U8A4S18Pc9A1A4S7G2A1A3A3A3A4").
Definition S6h (vb : bool) : axst := ltac2:(tb__ "0|1|
Sc6Sc7Sb6Vvb;A1S3S19S34S88A1S7S19A1A3A2S3S1bS26S25S99S18PcfA1M0S17Z0A1A3A1S3S1bS1dG0S17Z100A1A2S7S1bA1A3A3A2").
Definition L1h (vb : bool) : axst := ltac2:(tb__ "0|0|
SbaU0Sb7U12cS3S0Sb1S3S0Z3ec50S3S0Z3ec0cS3S0Z3ec2cS3S0Z3ebacS7S0A1A3A3A3A3A3S77Vvb;A1A3A2").
Definition callee_savedb (r : nat) : bool := match r with 1 | 2 | 3 | 4 | 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition NX7 : positive := 400%positive.
Definition regs7 (vb : bool) : list sv := ltac2:(tb__ "0|0|
S42S5S16S5S8S16L_;S82R1A1S44S16R1S2cS35S5bVvb;A1A1A1S17Z0A1A4S18SbeS6fSbdR1A1A2A1X8x2Lr;S43U0U20A2A4").
Definition entG : carve_spec := ltac2:(tb__ "0|5|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2M1S16A2M2A1S4G0S0S4S16S0S9eZ0M3A4Z10A4S3G2S4G1S16S4S0S5G3U4M4A4S18PceA1A4S3G2S4G1S16S4S0S5Z4G4A4S18PcfA1A4S3G2S4G1S16S4S0S5Z8U8A4S18Pc9A1A4S7G2A1A3A3A3A4").
Definition slotG : carve_spec := ltac2:(tb__ "0|2|
S4S6S6S16S0A2M0S0A2SaS6S6S0S5A2S16A2M1A1S4G0S0S4S16S0Sb9S9eS1aS96S18PceA1S17Z2A1A3A2Z10A4Z14A4S7G1A1A4").

Definition S7_of (vb : bool) : axst := ltac2:(tb__ "0|1|
S35S5bVvb;A1M0A1S2eS37G0S27Sb2S91Vvb;A1S29R1A1S28R1A1S2dR1A1S9S19Se4S19S1cR1A1A2S3S19S34S62A1S3S19S34S69A1S7S19A1A3A3A3S22S35Se0Vvb;A1A1A1P1b8SbA9A2TS;").
Definition S7_a : axst := Eval vm_compute in (S7_of false).
Definition S7_b : axst := Eval vm_compute in (S7_of true).
Definition S7 (vb : bool) : axst := if vb then S7_b else S7_a.
Definition run8 (vb : bool) : list leafA := ltac2:(tb__ "0|0|
Sb7U12cS3S0ScfS3S0Z3ec50S3S0Z3ec0cS3S0Z3ec2cS3S0Sb1S7S0A1A3A3A3A3A3S4bVvb;A1A3").
Definition E8_a : axst := Eval vm_compute in (leaf 0 (run8 false)).
Definition E8_b : axst := Eval vm_compute in (leaf 0 (run8 true)).
Definition E8 (vb : bool) : axst := if vb then E8_b else E8_a.
Definition VK7 : list positive := ltac2:(tb__ "0|0|
S3S1Pa0S3S1Pa1S3S1Pa2S3S1Pa3S3S1Pa4S3S1Pa5S3S1Pa6S3S1Pb8S3S1Pb9S3S1PbaS3S1PbbS3S1Pd0S3S1Pc8S3S1Pc9S3S1PcaS3S1PcbS3S1PccS3S1PcdS3S1PceS3S1PcfS3S1Pd1S3S1Pd2S7S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma run8_eq : ltac2:(tb__ "0|0|
S8S9bSaS3aA1Sb7U12cS3S0ScfS3S0Z3ec50S3S0Z3ec0cS3S0Z3ec2cS3S0Sb1S7S0A1A3A3A3A3A3S4bR1A1A3S68R1A1A3Fvb;"). Proof. intros vb. unfold run8. reflexivity. Qed.
Lemma chk8 : ltac2:(tb__ "0|1|
S8S9bS8Sa8S2bS35S4bR1A1A1A1S68R1A1S3S6S36Sa7A2M0S4S36Sa7S50R1A1SabS52A1A4S7G0A1A3A3ScA3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma nx7 : ltac2:(tb__ "0|1|
S8S9cS9bS8S2aS35S4bR1A1A1M0A1SbA3SbfSb8S2bG0A1A2A2Fvb;"). Proof. intros [|]; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]). Qed.
Lemma E8_ent : ltac2:(tb__ "0|0|
S8S9bS8Sa9S50R1A1Se1R1A1SabS52A1A3ScA3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma S7_wf : ltac2:(tb__ "0|2|
S8S9cS9bS8S32S35S4bR1A1M0A1A1ScA3S9cS9bS8S39G0A1ScA3S9bSaS6S16S16A2M1A1S38G0A1S7G1A1A3A2A2Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Section TRT.
Context {Q : assn} (X : trk Q).
Theorem seg_T8 : ltac2:(tb__ "0|1|
S8Sc2S2fSaSe7Q40A1A1Sd2VQ;VX;R3A3S36Sa7S2fSe2S6S36Sa7A2M0S4S36Sa7R3R2A4S3G0S4S36Sa7S50R8A1SabS52A1A4S7G0A1A3A3SaaR3R7R2A3Sd1VQ;VX;Sc1Sc3R9R5R3R7A5A3F_;F_;Frho';FM;FT;Sd1VQ;VX;Sc1Sc3R5S4bR6A1R4R3A5A3F_;F_;Ftp;Frho;FJ;Fvb;").
Proof. intros vb J rho tp HJ HC. exact (tr_piece X 300%nat _ (S7 vb) (run8 vb) [(E8 vb, idm VK7)] (run8_eq vb) (chk8 vb) (proj1 (nx7 vb)) (proj2 (nx7 vb)) J rho tp HJ HC). Qed.
End TRT.

Definition N_OUT : list carve_spec := ltac2:(tb__ "0|0|
S3S33S67S3S33S62S3S33S69S7S33A1A3A3A3").
Definition F_OUT : list sprop := ltac2:(tb__ "0|1|
S3S1bS26S25S99S18PcfA1M0S17Z0A1A3A1S3S1bS30S18PceA1G0A2S3S1bS1dG0S17Z100A1A2S7S1bA1A3A3A3").
Definition ZD_OUT (n : Z) : list zdesc := ltac2:(tb__ "0|6|
S3S6S6S5S0A2M0S0A2M1S4G0S0S4S5S0U5Z0M2A4Z1000A4S3G1S4G0S0S4S5S0U7M3G2A4Z10M4A4S3G1S4G0S0S4S5S0G3S46G4S47Z4Vn;A2M5A2A4S46Z14G5A2A4S7G1A1A3A3A3").
Definition ZD_KO (vb : bool) : list zdesc := ltac2:(tb__ "0|4|
S9S6S6S5S0A2M0S0A2M1S3G1S4G0S0S4S5S0U4Z0M2A4Z1f81A4S7G1A1M3A3S9S9dSa2S9S9dSa3S9G1S3G1S4G0S0S4S5S0U3N10A4N8A4S3G1S4G0S0S4S5S0U1Zad0A4Zc60A4G3A3A3S8SaG1A1Lvb;Vvb;S3G1S4G0S0S4S5S0U9G2A4Z10A4G3A3G3X8x2A3A3A3A3").
Definition T_out (n : Z) (g vb : bool) (Ly : axst) : strans := ltac2:(tb__ "0|0|
Sd0VLy;S10S33S59Vn;Vg;A2A2S70S3S1PceS3S1PcfS7S1A1A3A3S6cS4bVvb;A1SabS5fA1S7dVvb;A1S7fVn;A1A9").

Record mdata : Type := mkMD { m_S0 : axst; m_L1 : axst; m_XC : list axform; m_C1 : axst; m_sF : wsub; m_RF : list sobj; m_T1f : axst; m_XX : list axform; m_Lx : axst }.
Definition m_Ly (D : mdata) : axst := dropN (m_Lx D) 2.
Definition STK_MZ : list (sv * Z * Z) := ltac2:(tb__ "0|6|
S3S6S6S16S0A2M0S0A2M1S4G0S0S4S16S0S1aS95S18PaA1M2S17Nc0M3A1A3N30A4Z0M4A4S3G1S4G0S0S4S16S0G2G3A4Nb8M5A4S3G1S4G0S0S4S16S0S1aS95G2S17G5A1A3G4A4Z10A4S3G1S4G0S0S4S16S0G2Na8A4G4A4S7G1A1A3A3A3A3").
Definition obj_specM (o : sobj) : option (sv * Z * Z) := ltac2:(tb__ "0|a|
S16SeS6S6S16S0A2M0S0A2M1A1Lx;M2S20Vo;A1S0G2S1fVo;A1S0S12G1S4G0S0S4S16S0S21Vo;A1R2A4R1A4A2Lhi;S1S14G1A1M3Li;M4S97S16S16G3Lb;La;M5Lop;M6G6S98G5Lop;M7G7S8S2S16G3La;Lw;Lsgn;M8S1S16S0G3Lk;Li;Ll;M9X16x8Llo;G4G6G6G7G7G8G9X16x8").
Definition stk_okb (o : sobj) (k : sv * Z * Z) : bool := ltac2:(tb__ "0|3|
SeS6S6S16S0A2M0S0A2M1A1S8Lx;S8fVo;A1G1G1S8Lp;R1G0S0G0S8Lp0;R2S16S0SdSdS1eSfS16S0SfG0S0Vk;A3M2A3R2A2S48S11S16S0G2A3R1A2A2S48S11G0S0Vk;A3R3A2A2Llo';Lb';X6x1Lhi';Lp0;X6x1Lp;SbXex2").

Definition DSO (n : Z) (g : bool) (pce : Z) : list dspec := ltac2:(tb__ "0|9|
S9S6S6S6S6S16S0A2M0S0A2M1SaS6S6S0S5A2S16A2A1M2A2M3S0A2M4S42S33G4S33G3G4Lk;M5R1G1G2G1G4Lp;M6R2G0S0G0G4Lp0;M7R2S16S0S4G3S0S4G1G2S4G0S0S4S16S0R2R1A4R3A4R5A4M8Z0A4Llo;Lb;X6x1Lhi;Lp0;X6x1Lcs;Lp;X6x1Lk;S53Vg;A1A4S42S33G4S33G5R1G1G2G6R2G0S0G7R2S16S0S4G3S0G8Vpce;A4Llo;Lb;X6x1Lhi;Lp0;X6x1Lcs;Lp;X6x1Lk;S3S33S54Vn;A1S3S33S56Vn;A1S3S33S55Vn;A1S3S33S4fS7S33A1A3A3A3A3A4A3").

Definition REFOBJ_KO (vb : bool) : list sobj := ltac2:(tb__ "0|0|
S9S19S3S19Sa0S7S19A1A3S9S19S1cS35Sa1A1A1S9S19S42S33S19S34S9fA4S42S33S19S34Se6S33SceVvb;A1A2A4A3A3A3").
Record mcert (n : Z) (g vb : bool) (D : mdata) : Prop := mkMC {
  c_in : s_ok (T_in n g vb (m_S0 D)) = true;
  c_nx0 : ss_lenient (ax_S (m_S0 D)) = false /\ Pos.leb NPRE (ss_next (ax_S (m_S0 D))) = true;
  c_run1 : chkNM (ss_next (ax_S (m_S0 D))) (runA 300 [DH_ENT] (m_S0 D)) [(m_L1 D, idm VSM)] = true;
  c_C1 : apply_axforms (m_L1 D) (m_XC D) = Some (m_C1 D);
  c_He : entails_frA (m_C1 D) (PreD n g) (m_sF D) = Some (m_RF D);
  c_Hchk : call_checkPA (m_C1 D) (PreD n g) (m_sF D) (m_RF D) [PostD n g] = true;
  c_T1f : T1f_of n g (m_C1 D) (m_sF D) (m_RF D) = m_T1f D;
  c_FBC1 : forallb (sprop_below (ss_next (ax_S (m_C1 D)))) (ss_facts (ax_S (m_C1 D))) = true;
  c_FBT1 : forallb (sprop_below (ss_next (ax_S (import_postA (m_sF D) (PreD n g) (PostD n g) (m_C1 D) (m_RF D))))) (ss_facts (ax_S (m_C1 D))) = true;
  c_RFcov : coveredb (ss_facts (ax_S (m_T1f D))) (m_RF D) (ss_objs (ax_S (m_T1f D))) = true;
  c_new : new_objs (ax_S (PreD n g)) (ax_S (PostD n g)) = if g then [obj_subst [] (O_dstD n (dst_cells n))] else [];
  c_XF0 : ax_X (PostD n g) = [] /\ ax_X (m_C1 D) = [] /\ ax_X (m_T1f D) = [] /\ ss_next (ax_S (PreD n g)) = 240%positive /\ ss_next (ax_S (m_C1 D)) = NXM;
  c_sF : sF_okb n g (m_sF D) = true;
  c_C1pre : forallb (fun f => existsb (sprop_eqb f) (ss_facts (ax_S (m_C1 D)))) (pre_facts DEPTH_R) = true;
  c_C1objs : ss_objs (ax_S (m_C1 D)) = firstn (length (ss_objs (ax_S (m_C1 D))) - length (m_RF D)) (ss_objs (ax_S (m_C1 D))) ++ m_RF D;
  c_RFshape : m_RF D = firstn 4 (m_RF D) ++ map carve_obj (NRO_M g ++ NQW_M g vb) ++ [O_ishQ];
  c_RFstk : forallb2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQCF_call.stk_shapeb (firstn 4 (m_RF D)) STK_MZ = true;
  c_Lx : apply_axforms (m_T1f D) (m_XX D) = Some (m_Lx D);
  c_Lxshape : forallb2 (fun o (r : sv * sv * sv) => let '(b, lo, hi) := r in is3P' b lo hi o) (ss_objs (ax_S (m_Lx D))) (REF_OUT n g vb) = true;
  c_Lxobjs : ss_objs (ax_S (m_Lx D)) = keepN (m_Lx D) 2 ++ map carve_obj [riOS n g; dstOS n];
  c_out : s_ok (T_out n g vb (m_Ly D)) = true;
  c_outobjs : forall pce, ss_objs (ax_S (m_Ly D)) = keepN (m_Ly D) (length (D2S n g)) ++ map dobj (DSO n g pce);
  c_outK : forallb2 same_rng (keepN (m_Ly D) (length (D2S n g))) (REFOBJ_KO vb) = true;
  c_Lypre : forallb (fun f => existsb (sprop_eqb f) (ss_facts (ax_S (m_Ly D)))) (pre_facts DEPTH_R) = true
}.
