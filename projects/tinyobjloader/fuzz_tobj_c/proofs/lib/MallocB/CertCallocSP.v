(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "option"; "true"; "list"; "app"; "prod"; "false"; "bool"; "None"; "andb"; "S"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "sprop"; "SLit"; "sobj"; "cell"; "SAlu"; "SPUle"; "mkObj"; "DUnknown"; "ss_regs"; "mkSS"; "mkCell"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_objs"; "ss_pc"; "ss_resv"; "sstate"; "SPAlign"; "DZero"; "FcsrFrm0"; "c_off"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "SMd"; "SPUlt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "sym_runA"; "ax_S"; "ax_setS"; "axst"; "la_state"; "la_reason"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP.W"; "upd"; "F_cls"; "F_pop"; "LIVE"; "HAVOC_CALLER"; "prune_sw"; "set_obj_from_end"; "MSENT"; "MSRET"; "ube"; "LUe"; "O_UBz"; "pc_base"; "BU"; "E2b"; "O_L"; "ab_e"; "BP"; "BR"; "BSH"; "C2_ru"; "E5s1"; "E7c1"; "E7q1"; "F_rza"; "F_rzb"; "HAVOC_C8"; "HAVOC_JOIN"; "LLe"; "LPe"; "LRe"; "O_R"; "O_st"; "choff"; "C10a"; "C10b"; "C10pa"; "C10pb"; "C1g"; "C1g_regs"; "C2p"; "C2p0"; "C2r"; "C3"; "C5"; "C5b"; "C5c"; "C5d"; "C5e"; "C5m1"; "C5m2"; "C6"; "C6b"; "C6l"; "C6m"; "C7"; "C7p"; "C8"; "C8p"; "C9a"; "C9b"; "C9ma"; "C9mb"; "C9mpa"; "C9mpb"; "C9pa"; "C9pb"; "DUMMY"; "E2a"; "E3p"; "E4d"; "E5f"; "E5m1"; "E5m2"; "E5n"; "E5s2"; "E6j"; "E6l"; "E6m"; "E7c2"; "E7p"; "E7q2"; "E8n"; "E8pn"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "HAVOC_JOIN6"; "LTe"; "M48"; "O_H"; "O_P"; "O_T"; "O_U"; "O_UB"; "O_Uz"; "O_pcc"; "O_pcc0"; "O_pck"; "O_pcs"; "PIECES"; "call_cell"; "live_cell"; "prune_call"; "uee"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "gsv"; "shb"; "GW"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "ALU_SLL"; "ALU_SRL"; "ALU_AND"; "aluop"; "mulop"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "V_RZ"; "V_CLS"; "V_SIZE"; "V_ND"; "V_CH"; "V_CNT"; "F_gen"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "TP_A"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "ltb"; "pow"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "cut_regs"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "mkA"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "V_TSZ"; "rup8"; "vSB"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Definition V_SIZE : positive := 148%positive.
Definition V_CNT : positive := 149%positive.
Definition V_RZ : positive := 150%positive.
Definition V_ND : positive := 157%positive.
Definition V_CLS : positive := 158%positive.
Definition V_CH : positive := 159%positive.

Definition F_gen : list sprop := ltac2:(tb__ "0|3|
S0S12S17S13Z10A1S11Sb2A1M0A2S0S12S17G0S13Z400A1A2S0S12S26Sb2Z4A2S0S12S17S13Z18A1S11Sb5A1M1A2S0S12S17G1S13Z10000A1A2S0S12S26Sb5Z3A2S0S12S17S16SaaS11PcA1M2G0A3G1A2S0S12S17G2S13Zfc00A1A2S1S12A1A3A3A3A3A3A3A3A3").

Section W.
Variable W : list ulink.
Variable st : ustop.
Variable tmax : Z.
Let FACTS : list sprop := ltac2:(tb__ "0|1|
S7S12S7S12S7S12S7S12ScdVW;Vst;A2SccScbA1A3Sc8A3Sd4A3S7S12S0S12S17S13Z1A1S11Sd7A1M0A2S0S12S17G0S13Vtmax;A1A2S1S12A1A3A3Sb8A3A3").
Let OBJS (sw : sobj) (extra : list sobj) : list sobj := ltac2:(tb__ "0|0|
S7S14S7S14S0S14Vsw;S7S14SceVW;A1ScaA3A3Sd6A3Vextra;A3").

Definition DUMMY : leafA := ltac2:(tb__ "0|1|
S3bSc9S1bZ0S1S10A1M0G0S28SbS10A1S1S14A1S1S12A1Sc7S9A9S1S8S10S10A2A1A2Sc6A2").
Definition leaf (i : nat) (l : list leafA) : axst := ltac2:(tb__ "0|0|
S39Sb9S34Vi;Vl;S7fA4A1").

Definition upd (E : axst) (pc : Z) (ru : list (nat * sv)) (objs : list sobj) (reset : bool) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S36VE;A1S25S37VE;S1bVpc;Sc2S1aR1A1Vru;A2S1fR1A1S1eR1A1S24R1A1S7S14S22R1A1Vobjs;A3S7S12SaS6S12A1Lreset;Vreset;VFACTS;S1dR1A1Xax2Vfacts;A3S21R1A1S20R1A1A9A2TS;").

Definition C1g_regs : list sv := ltac2:(tb__ "0|7|
Sc2Sc3Sa9A1S0S8S2S10A2M0S3S2S10U1S13Z3c614A1A4S0G0S3S2S10U2S16SaaS11PaA1M1S13N910A1A3A4S0G0S3S2S10U4S13SbdA1A4S0G0S3S2S10U8S13Z1A1M2A4S0G0S3S2S10U9S11PcA1M3A4S0G0S3S2S10UaS13Zeaa58A1M4A4S0G0S3S2S10UbS16SaaSbcS13Zd0A1A3A4S0G0S3S2S10UcS11Sb5A1M5A4S0G0S3S2S10UdS13Z8A1M6A4S0G0S3S2S10U12G6A4S0G0S3S2S10U13G5A4S0G0S3S2S10U14S11Sb2A1A4S0G0S3S2S10U15G3A4S0G0S3S2S10U16G4A4S0G0S3S2S10U17S16SaaG1S13N858A1A3A4S0G0S3S2S10U18S13Zfffffffffffffff8A1A4S0G0S3S2S10U19S13Z7A1A4S0G0S3S2S10U1aSbcA4S0G0S3S2S10U1bG2A4S1G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition C1g : axst := ltac2:(tb__ "0|0|
Sc9S1bZ40bacS63Sc4S28SbS10A1VOBJS;Sd5S1S14A1A2VFACTS;Sc7S9A9S1S8S10S10A2A1A2").
Definition run2 : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Z40d40S1S31A1A3S62S5A5G0R1Ll;S1S34A1X4x2").
Definition E2a : axst := leaf 0 run2.
Definition E2b : axst := leaf 1 run2.
Definition creg_a : sv := ltac2:(tb__ "0|0|
Sb9S10U8S1aS36S80A1A1S13Z0A1A4").
Definition creg_b : sv := ltac2:(tb__ "0|0|
Sb9S10U8S1aS36S4aA1A1S13Z0A1A4").

Definition pc_base : sv := ltac2:(tb__ "0|0|
S16SaaS16SaaSbcS13Zd0A1A3S2fSb1S11Sb3A1S13Z50A1A3A3").
Definition choff : sv := ltac2:(tb__ "0|0|
S16SaaS16SacS16SaaS11Sb7A1S13N1A1A3S13Z2A1A3S13Z10A1A3").

Definition O_pcc : sobj := ltac2:(tb__ "0|2|
S18S48S13Z0A1M0S13Z4M1A1S0S15S1cG0G1S11Sb7A1A3S1S15A1A3S19A5").
Definition O_pcs : sobj := ltac2:(tb__ "0|2|
S18S48S13Z8M0A1M1S13Z10A1S0S15S1cG1G0S11Sb4A1A3S1S15A1A3S19A5").
Definition O_pck : sobj := ltac2:(tb__ "0|0|
S18S48S5dS13Z50A1S0S15S1cS5dZ4S11Sb6A1A3S1S15A1A3S19A5").

Definition O_pcc0 : sobj := ltac2:(tb__ "0|2|
S18S48S13Z0A1M0S13Z4M1A1S0S15S1cG0G1G0A3S1S15A1A3S19A5").
Definition O_st : sobj := ltac2:(tb__ "0|0|
S18SbcS13Zad0A1S13Zc60A1S1S15A1S19A5").
Definition F_cls : list sprop := ltac2:(tb__ "0|2|
S0S12S17S13Z1A1S11Sb3A1M0A2S0S12S17G0S13Z1eA1A2S0S12S17S11Sb5A1S11Sb4A1M1A2S0S12S17G1S13Z10000A1A2S0S12S26Sb4Z4A2S1S12A1A3A3A3A3A3").
Definition F_pop : list sprop := ltac2:(tb__ "0|1|
S0S12S17S13Z1A1S11Sb7A1M0A2S0S12S17G0S13Z10A1A2S0S12S30S11Sb6A1S13Sc0Z2Z1cA2A1A2S1S12A1A3A3A3").
Definition C2_ru : list (nat * sv) := ltac2:(tb__ "0|1|
S0S8S2S10A2M0S3S2S10U5S11Pa5A1A4S0G0S3S2S10U6S11Pa6A1A4S0G0S3S2S10U7S11Pa7A1A4S0G0S3S2S10U8S11Sb3A1A4S0G0S3S2S10UcS11PacA1A4S0G0S3S2S10UeS11PaeA1A4S0G0S3S2S10UfS11PafA1A4S0G0S3S2S10U10S11Pb0A1A4S0G0S3S2S10U11S11Pb1A1A4S1G0A1A3A3A3A3A3A3A3A3A3").

Definition C2p0 : axst := ltac2:(tb__ "0|0|
S3cS4aZ40d40S50S0S14S9dS0S14Sa0S0S14S9fS0S14S5cS1S14A1A3A3A3A3S5S1S12A1A6").
Definition C2r0 : axst := ltac2:(tb__ "0|0|
S3cS4aZ40d40S50S0S14S9eS0S14S5cS1S14A1A3A3S5S1S12A1A6").
Definition C2p : axst := ltac2:(tb__ "0|0|
Sd3S7S12S3dS3eA3S65A2").
Definition C2r : axst := ax_add_facts F_cls C2r0.
Definition run3p : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Z40e58S0S31Z3c614S1S31A1A3A3S64S5A5G0R1Ll;S1S34A1X4x2").
Definition run3r : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Z40e58S0S31Z3c614S1S31A1A3A3S66S5A5G0R1Ll;S1S34A1X4x2").
Definition E3p : axst := leaf 0 run3p.
Definition E3r : axst := leaf 0 run3r.

Definition ab_e : sv := ltac2:(tb__ "0|0|
S16SaaS16SacS11Sb6A1S13Z4A1A3S16SaaS16SacS11Sb3A1S13Z20A1A3Sd9A3A3").
Definition ube : sv := ltac2:(tb__ "0|0|
S16SaaS4cS11Sb2A1A3").
Definition uee : sv := SAlu ALU_ADD ube (SVar 12).
Definition M48 : Z := 281474976710648.
Definition n8e : sv := ltac2:(tb__ "0|0|
S16SaeS11PcA1S13S96A1A3").
Definition LLe : sv := ltac2:(tb__ "0|0|
S16SadS11Sb2A1S13Z3A1A3").
Definition LUe : sv := SAlu ALU_SRL n8e (SLit 3).
Definition LPe : sv := ltac2:(tb__ "0|1|
S16SadS16SaaS16SaeS11PcA1S13Z7A1M0A3G0A3S13Z3A1A3").
Definition LRe : sv := ltac2:(tb__ "0|0|
S16SadS16SabS16SabS11Sb4A1S11Sb2A1A3Sd8A3S13Z3A1A3").
Definition LTe : sv := ltac2:(tb__ "0|0|
S16SabS16SabS11Sb4A1S11Sb2A1A3S11PcA1A3").
Definition BSH : sv := ltac2:(tb__ "0|0|
S16SaaSa7S4cA1Sa8A3").
Definition BU : sv := ltac2:(tb__ "0|0|
S16SaaSa7S45A1Sa8A3").
Definition BP : sv := SAlu ALU_ADD BU LUe.
Definition BR : sv := SAlu ALU_ADD BP LPe.
Definition O_H : sobj := ltac2:(tb__ "0|0|
S18S4cS13Z0A1S11Sb2A1S1S15A1S19A5").
Definition O_UB : sobj := ltac2:(tb__ "0|0|
S18S45S13Z0A1S11PcA1S1S15A1S19A5").
Definition O_T : sobj := ltac2:(tb__ "0|0|
S18Sa5S13Z0A1S95S1S15A1S19A5").
Definition O_L : sobj := ltac2:(tb__ "0|0|
S18S4fS13Z0A1S58S1S15A1S19A5").
Definition O_U : sobj := ltac2:(tb__ "0|0|
S18S49S13Z0A1S46S1S15A1S19A5").
Definition O_Uz : sobj := ltac2:(tb__ "0|0|
S18S49S13Z0A1S46S1S15A1S27A5").
Definition O_P : sobj := ltac2:(tb__ "0|0|
S18S4dS13Z0A1S59S1S15A1S19A5").
Definition O_R : sobj := ltac2:(tb__ "0|0|
S18S4eS13Z0A1S5aS1S15A1S19A5").
Definition PIECES : list sobj := ltac2:(tb__ "0|0|
S0S14S97S0S14S9bS0S14S99S0S14S4bS0S14S9aS0S14S98S0S14S5bS1S14A1A3A3A3A3A3A3A3").
Definition C3 : axst := ltac2:(tb__ "0|0|
S3cS81Z3c614S1S8S2S10A2A1Sa1S9S1S12A1A6").
Definition run4 : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Z7e9e4S1S31A1A3S67S5A5G0R1Ll;S1S34A1X4x2").
Definition E4d : axst := leaf 0 run4.

Definition HAVOC_CALLER : list (nat * sv) := ltac2:(tb__ "0|1|
S0S8S2S10A2M0S3S2S10U5S11Pa5A1A4S0G0S3S2S10U6S11Pa6A1A4S0G0S3S2S10U7S11Pa7A1A4S0G0S3S2S10UbS11PabA1A4S0G0S3S2S10UcS11PacA1A4S0G0S3S2S10UdS11PadA1A4S0G0S3S2S10UeS11PaeA1A4S0G0S3S2S10UfS11PafA1A4S0G0S3S2S10U10S11Pb0A1A4S0G0S3S2S10U11S11Pb1A1A4S0G0S3S2S10U1cS11PbcA1A4S0G0S3S2S10U1dS11PbdA1A4S0G0S3S2S10U1eS11PbeA1A4S0G0S3S2S10U1fS11PbfA1A4S1G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition HAVOC_JOIN : list (nat * sv) := ltac2:(tb__ "0|1|
S7S8S2S10A2M0S40S0G0S3S2S10U1S11Pa9A1A4S0G0S3S2S10U8S11Pa8A1A4S0G0S3S2S10UaS11Pb4A1A4S0G0S3S2S10U19S11Pb9A1A4S1G0A1A3A3A3A3A3").
Definition HAVOC_JOIN6 : list (nat * sv) := ltac2:(tb__ "0|1|
S7S8S2S10A2M0S57S0G0S3S2S10U16S11Pb6A1A4S1G0A1A3A3").

Definition set_obj_from_end (k : nat) (o : sobj) (E : axst) : axst := ltac2:(tb__ "0|0|
S36VE;A1S25S22R1A1S6S14A1Sc1Sc1SeS14R1A2U1A2Vk;A2S2S37VE;S1bS23R3A1S1aR3A1S1fR3A1S1eR3A1S24R3A1S7S14SbaS14R1R2A3S7S14S0S14Vo;S1S14A1A3SbbS14SdR1A1R2A3A3A3S1dR3A1S21R3A1S20R3A1A9A2Ti;Tobjs;TS;").

Definition live_cell (lo : Z) (c : cell) : bool := ltac2:(tb__ "0|3|
S10SaLx;S29Vc;A1S31SbeVlo;R1A2Lz;S32S5Li;SafS10S10S5Lb;La;M0Lop;M1G1Sb0G0Lop;M2G2SaS33S10S5La;Lw;Lsgn;S32S10S31S5Lk;Li;Ll;X10x8").
Definition prune_sw (lo : Z) (E : axst) : axst := ltac2:(tb__ "0|2|
S36VE;A1S25S6S14A1M0S38Lx;S22R1A1VE;S14G0S37VE;S1bS23R3A1S1aR3A1S1fR3A1S1eR3A1S24R3A1S0S14S18S2aR2A1S2eR2A1S2dR2A1Sd0S15S6S15A1Sd2S15A1S15ScfSa3Vlo;R1A2M1A1Lc;S15Sd1G1A1Lx;S2bR2A1A6S2cR2A1A5R1A3S1dR3A1S21R3A1S20R3A1A9A2Lrest;Lo;X6x2TS;").
Definition LIVE : Z := -2320.

Definition call_cell (c : cell) : bool := ltac2:(tb__ "0|3|
S10SaLx;S29Vc;A1S31ScSbeS3fR1A2SfScSbeN848R1A2SbfR1N50A2A2A1A2Lz;S32S5Li;SafS10S10S5Lb;La;M0Lop;M1G1Sb0G0Lop;M2G2SaS33S10S5La;Lw;Lsgn;S32S10S31S5Lk;Li;Ll;X10x8").
Definition prune_call (E : axst) : axst := ltac2:(tb__ "0|2|
S36VE;A1S25S6S14A1M0S38Lx;S22R1A1VE;S14G0S37VE;S1bS23R3A1S1aR3A1S1fR3A1S1eR3A1S24R3A1S0S14S18S2aR2A1S2eR2A1S2dR2A1Sd0S15S6S15A1Sd2S15A1S15ScfSa2R1A1M1A1Lc;S15Sd1G1A1Lx;S2bR2A1A6S2cR2A1A5R1A3S1dR3A1S21R3A1S20R3A1A9A2Lrest;Lo;X6x2TS;").
Definition C5 : axst := ltac2:(tb__ "0|1|
Sa4S3cS82Z7ec58S0S8S2S10A2M0S3S2S10UaS11PaaA1A4S0G0S3S2S10U1S13Z3c720A1A4S40A3A3S1S14A1S9S1S12A1A6A1").
Definition run5 : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Z3c774S0S31Z3c80cS1S31A1A3A3S68S5A5G0R1Ll;S1S34A1X4x2").
Definition E5n : axst := leaf 0 run5.
Definition E5f : axst := leaf 1 run5.

Definition C5b : axst := ltac2:(tb__ "0|2|
S3cS83Z3c774S0S8S2S10A2M0S3S2S10U8S11Sb3A1M1A4S0G0S3S2S10UaG1A4S1G0A1A3A3S1S14A1S9S1S12A1A6").
Definition run5b : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Z3c7e0S1S31A1A3S69S5A5G0R1Ll;S1S34A1X4x2").
Definition E5s1 : axst := leaf 0 run5b.
Definition E5s2 : axst := leaf 1 run5b.
Definition sreg1 : sv := ltac2:(tb__ "0|0|
Sb9S10U8S1aS36S51A1A1S13Z0A1A4").
Definition sreg2 : sv := ltac2:(tb__ "0|0|
Sb9S10U8S1aS36S87A1A1S13Z0A1A4").

Definition C5c : axst := ltac2:(tb__ "0|1|
S41S3fS3cS51Z3c7e0S0S8S2S10A2M0S3S2S10U8S11Sb4A1A4S0G0S3S2S10UaS11Pb4A1A4S0G0S3S2S10UbS11PabA1A4S1G0A1A3A3A3S1S14A1S5S7S12S3dS3eA3A6A2").
Definition run5c : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Zdb004S1S31A1A3S6aS5A5G0R1Ll;S1S34A1X4x2").
Definition E5m1 : axst := leaf 0 run5c.
Definition MSENT : Z := 0xdb004.
Definition MSRET : Z := 0xdb0f8.

Definition C5m1 : axst := ltac2:(tb__ "0|1|
S3cS84S43S0S8S2S10A2M0S3S2S10UaS4fA4S0G0S3S2S10UcS58A4S1G0A1A3A3S1S14A1S9S1S12A1A6").
Definition C5d : axst := ltac2:(tb__ "0|0|
S42U3S4bS3cS6dS44S40S1S14A1S9S1S12A1A6A3").
Definition run5d : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Zdb004S1S31A1A3S6bS5A5G0R1Ll;S1S34A1X4x2").
Definition E5m2 : axst := leaf 0 run5d.
Definition C5m2 : axst := ltac2:(tb__ "0|1|
S3cS85S43S0S8S2S10A2M0S3S2S10UaS4eA4S0G0S3S2S10UcS5aA4S1G0A1A3A3S1S14A1S9S1S12A1A6").
Definition C5e : axst := ltac2:(tb__ "0|0|
S42U0S5bS3cS6eS44S40S1S14A1S9S1S12A1A6A3").
Definition run5e : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Z3c80cS1S31A1A3S6cS5A5G0R1Ll;S1S34A1X4x2").
Definition E5j : axst := leaf 0 run5e.

Definition C6 : axst := ltac2:(tb__ "0|0|
S41S3fS42U3S4bS3cS86Z3c80cS94S1S14A1S5S7S12S3dS3eA3A6A3A2").

Definition run6 : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Z5f9f8S0S31Z3c82cS1S31A1A3A3S6fS5A5G0R1Ll;S1S34A1X4x2").
Definition E6s : axst := leaf 0 run6.
Definition E6l : axst := leaf 1 run6.
Definition lenx : sv := LUe.
Definition C6l : axst := ltac2:(tb__ "0|1|
S3cS89Z5f9f8S0S8S2S10A2M0S3S2S10U8S46A4S1G0A1A3S1S14A1S9S1S12A1A6").
Definition run6l : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Zdb004S1S31A1A3S71S5A5G0R1Ll;S1S34A1X4x2").
Definition E6m : axst := leaf 0 run6l.
Definition C6m : axst := ltac2:(tb__ "0|1|
S3cS8aS43S0S8S2S10A2M0S3S2S10UaS49A4S0G0S3S2S10UcS46A4S1G0A1A3A3S1S14A1S9S1S12A1A6").

Definition C6b : axst := ltac2:(tb__ "0|0|
S42U2S9cS3cS72S44S40S1S14A1S9S1S12A1A6A3").
Definition run6b : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Z3c82cS1S31A1A3S70S5A5G0R1Ll;S1S34A1X4x2").
Definition E6j : axst := leaf 0 run6b.

Definition C7 : axst := ltac2:(tb__ "0|0|
S41S3fS3cS88Z3c82cS57S1S14A1S5S7S12S3dS3eA3A6A2").
Definition run7 : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Z3c8bcS0S31Z3ca04S1S31A1A3A3S73S5A5G0R1Ll;S1S34A1X4x2").
Definition E7c1 : axst := leaf 0 run7.
Definition E7c2 : axst := leaf 1 run7.
Definition E7p : axst := leaf 2 run7.
Definition creg7a : sv := ltac2:(tb__ "0|0|
Sb9S10UbS1aS36S52A1A1S13Z0A1A4").
Definition creg7b : sv := ltac2:(tb__ "0|0|
Sb9S10UbS1aS36S8bA1A1S13Z0A1A4").

Definition C7p : axst := ltac2:(tb__ "0|1|
S3cS8cZ3c8bcS0S8S2S10A2M0S3S2S10UaS4dA4S1G0A1A3S1S14A1S9S0S12S17S13Z1A1S59A2S1S12A1A3A6").
Definition run7p : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Z3ca04S1S31A1A3S74S5A5G0R1Ll;S1S34A1X4x2").
Definition E7q1 : axst := leaf 0 run7p.
Definition E7q2 : axst := leaf 1 run7p.
Definition creg7c : sv := ltac2:(tb__ "0|0|
Sb9S10UbS1aS36S53A1A1S13Z0A1A4").
Definition creg7d : sv := ltac2:(tb__ "0|0|
Sb9S10UbS1aS36S8dA1A1S13Z0A1A4").

Definition HAVOC_C8 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S8S2S10A2M0S3S2S10U5S11Pa5A1A4S0G0S3S2S10U6S11Pa6A1A4S0G0S3S2S10U7S11Pa7A1A4S0G0S3S2S10UbS11Sb3A1A4S0G0S3S2S10UcS11PacA1A4S0G0S3S2S10UdS11PadA1A4S0G0S3S2S10UeS11PaeA1A4S0G0S3S2S10UfS11PafA1A4S0G0S3S2S10U10S11Pb0A1A4S0G0S3S2S10U11S11Pb1A1A4S0G0S3S2S10U1cS11PbcA1A4S0G0S3S2S10U1dS11PbdA1A4S0G0S3S2S10U1eS11PbeA1A4S0G0S3S2S10U1fS11PbfA1A4S1G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C8 : axst := ltac2:(tb__ "0|0|
S41S3fS3cS52Z3ca04S56S1S14A1S5S7S12S3dS3eA3A6A2").
Definition C8p : axst := ltac2:(tb__ "0|0|
S41S3fS3cS53Z3ca04S56S1S14A1S5S7S12S3dS3eA3A6A2").
Definition run8 : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Zdb004S0S31Z3ca54S1S31A1A3A3S75S5A5G0R1Ll;S1S34A1X4x2").
Definition run8p : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Zdb004S0S31Z3ca54S1S31A1A3A3S76S5A5G0R1Ll;S1S34A1X4x2").

Definition E8n : axst := leaf 0 run8.
Definition E8pn : axst := leaf 0 run8p.

Definition C9 : axst := ltac2:(tb__ "0|0|
S41S3fS3cS8eZ3ca54S40S1S14A1S5S7S12S3dS3eA3A6A2").
Definition C9p : axst := ltac2:(tb__ "0|0|
S41S3fS3cS8fZ3ca54S40S1S14A1S5S7S12S3dS3eA3A6A2").

Definition F_rza : list sprop := ltac2:(tb__ "0|0|
S0S12S17S13Z20A1S11Sb2A1A2S1S12A1A3").
Definition F_rzb : list sprop := ltac2:(tb__ "0|0|
S0S12S17S11Sb2A1S13Z10A1A2S1S12A1A3").
Definition C9a : axst := ax_add_facts F_rza C9.
Definition C9b : axst := ax_add_facts F_rzb C9.
Definition C9pa : axst := ax_add_facts F_rza C9p.
Definition C9pb : axst := ax_add_facts F_rzb C9p.
Definition run9a : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Zdb004S1S31A1A3S77S5A5G0R1Ll;S1S34A1X4x2").
Definition run9b : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Zdb004S1S31A1A3S78S5A5G0R1Ll;S1S34A1X4x2").
Definition run9pa : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Zdb004S1S31A1A3S7dS5A5G0R1Ll;S1S34A1X4x2").
Definition run9pb : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S0S31Zdb004S1S31A1A3S7eS5A5G0R1Ll;S1S34A1X4x2").
Definition E9ma : axst := leaf 0 run9a.
Definition E9mb : axst := leaf 0 run9b.
Definition E9mpa : axst := leaf 0 run9pa.
Definition E9mpb : axst := leaf 0 run9pb.

Definition C9ma : axst := ltac2:(tb__ "0|1|
S3cS90S43S0S8S2S10A2M0S3S2S10UaS45A4S0G0S3S2S10UcS11PcA1A4S1G0A1A3A3S1S14A1S9S1S12A1A6").
Definition C9mb : axst := ltac2:(tb__ "0|1|
S3cS91S43S0S8S2S10A2M0S3S2S10UaS45A4S0G0S3S2S10UcS11PcA1A4S1G0A1A3A3S1S14A1S9S1S12A1A6").
Definition C9mpa : axst := ltac2:(tb__ "0|1|
S3cS92S43S0S8S2S10A2M0S3S2S10UaS45A4S0G0S3S2S10UcS11PcA1A4S1G0A1A3A3S1S14A1S9S1S12A1A6").
Definition C9mpb : axst := ltac2:(tb__ "0|1|
S3cS93S43S0S8S2S10A2M0S3S2S10UaS45A4S0G0S3S2S10UcS11PcA1A4S1G0A1A3A3S1S14A1S9S1S12A1A6").

Definition O_UBz : sobj := ltac2:(tb__ "0|0|
S18S45S13Z0A1S11PcA1S1S15A1S27A5").
Definition C10a : axst := ltac2:(tb__ "0|0|
S41S3fS42U5S47S3cS79S44S40S1S14A1S5S7S12S7S12S3dS3eA3S54A3A6A3A2").
Definition C10b : axst := ltac2:(tb__ "0|0|
S41S3fS42U5S47S3cS7aS44S40S1S14A1S5S7S12S7S12S3dS3eA3S55A3A6A3A2").
Definition C10pa : axst := ltac2:(tb__ "0|0|
S41S3fS42U5S47S3cS7bS44S40S1S14A1S5S7S12S7S12S3dS3eA3S54A3A6A3A2").
Definition C10pb : axst := ltac2:(tb__ "0|0|
S41S3fS42U5S47S3cS7cS44S40S1S14A1S5S7S12S7S12S3dS3eA3S55A3A6A3A2").

Definition run10a : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S1S31A1S5eS5A5G0R1Ll;S1S34A1X4x2").
Definition run10b : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S1S31A1S5fS5A5G0R1Ll;S1S34A1X4x2").
Definition run10pa : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S1S31A1S60S5A5G0R1Ll;S1S34A1X4x2").
Definition run10pb : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35Sa6Ufa0S1S31A1S61S5A5G0R1Ll;S1S34A1X4x2").
End W.

Definition showL (L : leafA) : ltac2:(tb__ "0|0|
S8S31Sc5A2") := ltac2:(tb__ "0|0|
S3S31Sc5S23S36S39VL;A1A1A1S3aVL;A1A4").

