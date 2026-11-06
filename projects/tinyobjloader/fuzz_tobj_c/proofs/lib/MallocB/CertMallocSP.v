(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "option"; "true"; "list"; "app"; "prod"; "false"; "bool"; "None"; "andb"; "S"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "sprop"; "sobj"; "cell"; "SAlu"; "SPUle"; "mkObj"; "DUnknown"; "ss_regs"; "mkSS"; "mkCell"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_objs"; "ss_pc"; "ss_resv"; "sstate"; "SPAlign"; "FcsrFrm0"; "c_off"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "DZero"; "SMd"; "SPUlt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "sym_runA"; "ax_S"; "ax_setS"; "axst"; "la_state"; "la_reason"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP.W"; "upd"; "F_cls"; "F_pop"; "LIVE"; "HAVOC_CALLER"; "prune_sw"; "set_obj_from_end"; "MSENT"; "MSRET"; "LUe"; "pc_base"; "ube"; "BU"; "E2b"; "O_L"; "O_UB"; "ab_e"; "BP"; "BR"; "BSH"; "C2_ru"; "C9"; "C9p"; "E5s1"; "E7c1"; "E7q1"; "HAVOC_C8"; "HAVOC_JOIN"; "LLe"; "LPe"; "LRe"; "O_R"; "O_st"; "choff"; "C1g"; "C1g_regs"; "C2p"; "C2p0"; "C2r"; "C3"; "C5"; "C5b"; "C5c"; "C5d"; "C5e"; "C5m1"; "C5m2"; "C6"; "C6b"; "C6l"; "C6m"; "C7"; "C7p"; "C8"; "C8ma"; "C8mpa"; "C8p"; "C9a"; "C9b"; "C9pa"; "C9pb"; "DUMMY"; "E2a"; "E3p"; "E4d"; "E5f"; "E5m1"; "E5m2"; "E5n"; "E5s2"; "E6j"; "E6l"; "E6m"; "E7c2"; "E7p"; "E7q2"; "E8a"; "E8pa"; "HAVOC_JOIN6"; "LTe"; "M48"; "O_H"; "O_P"; "O_T"; "O_U"; "O_Uz"; "O_pcc"; "O_pcc0"; "O_pck"; "O_pcs"; "PIECES"; "call_cell"; "live_cell"; "prune_call"; "uee"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "gsv"; "shb"; "GW"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "ALU_SLL"; "ALU_SRL"; "ALU_AND"; "aluop"; "mulop"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "V_RZ"; "V_CLS"; "V_SIZE"; "V_ND"; "V_CH"; "V_CNT"; "F_gen"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "TP_A"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "ltb"; "pow"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "cut_regs"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "mkA"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "F_s1"; "RT_m1"; "V_TSZ"; "rup8"; "sw_s1"; "vSB"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
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
S0S13S17S12Z10A1S11Sa7A1M0A2S0S13S17G0S12Z400A1A2S0S13S26Sa7Z4A2S0S13S17S12Z18A1S11SaaA1M1A2S0S13S17G1S12Z10000A1A2S0S13S26SaaZ3A2S0S13S17S16S9fS11PcA1M2G0A3G1A2S0S13S17G2S12Zfc00A1A2S1S13A1A3A3A3A3A3A3A3A3").

Section W.
Variable W : list ulink.
Variable st : ustop.
Variable tmax : Z.
Let FACTS : list sprop := ltac2:(tb__ "0|1|
S7S13S7S13S7S13S7S13Sc3VW;Vst;A2Sc2Sc1A1A3SbeA3Sc9A3S7S13S0S13S17S12Z1A1S11ScbA1M0A2S0S13S17G0S12Vtmax;A1A2S1S13A1A3A3SadA3A3").
Let OBJS (sw : sobj) (extra : list sobj) : list sobj := ltac2:(tb__ "0|0|
S7S14S7S14S0S14Vsw;S7S14Sc4VW;A1Sc0A3A3ScaA3Vextra;A3").

Definition DUMMY : leafA := ltac2:(tb__ "0|1|
S3bSbfS1bZ0S1S10A1M0G0S27SbS10A1S1S14A1S1S13A1SbdS9A9S1S8S10S10A2A1A2SbcA2").
Definition leaf (i : nat) (l : list leafA) : axst := ltac2:(tb__ "0|0|
S39SaeS34Vi;Vl;S79A4A1").

Definition upd (E : axst) (pc : Z) (ru : list (nat * sv)) (objs : list sobj) (reset : bool) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S36VE;A1S25S37VE;S1bVpc;Sb8S1aR1A1Vru;A2S1fR1A1S1eR1A1S24R1A1S7S14S22R1A1Vobjs;A3S7S13SaS6S13A1Lreset;Vreset;VFACTS;S1dR1A1Xax2Vfacts;A3S21R1A1S20R1A1A9A2TS;").

Definition C1g_regs : list sv := ltac2:(tb__ "0|7|
Sb8Sb9S9eA1S0S8S2S10A2M0S3S2S10U1S12Z3c614A1A4S0G0S3S2S10U2S16S9fS11PaA1M1S12N8e0A1A3A4S0G0S3S2S10U4S12Sb3A1A4S0G0S3S2S10U8S12Z1A1M2A4S0G0S3S2S10U9S11PcA1M3A4S0G0S3S2S10UaS12Zeaa58A1M4A4S0G0S3S2S10UbS16S9fSb2S12Zd0A1A3A4S0G0S3S2S10UcS11SaaA1M5A4S0G0S3S2S10UdS12Z8A1M6A4S0G0S3S2S10U12G6A4S0G0S3S2S10U13G5A4S0G0S3S2S10U14S11Sa7A1A4S0G0S3S2S10U15G3A4S0G0S3S2S10U16G4A4S0G0S3S2S10U17S16S9fG1S12N850A1A3A4S0G0S3S2S10U18S12Zfffffffffffffff8A1A4S0G0S3S2S10U19S12Z7A1A4S0G0S3S2S10U1aSb2A4S0G0S3S2S10U1bG2A4S1G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition C1g : axst := ltac2:(tb__ "0|0|
SbfS1bZ40bacS5fSbaS27SbS10A1VOBJS;ScdS1S14A1A2VFACTS;SbdS9A9S1S8S10S10A2A1A2").
Definition run2 : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Z40d40S1S31A1A3S5eS5A5G0R1Ll;S1S34A1X4x2").
Definition E2a : axst := leaf 0 run2.
Definition E2b : axst := leaf 1 run2.
Definition creg_a : sv := ltac2:(tb__ "0|0|
SaeS10U8S1aS36S7aA1A1S12Z0A1A4").
Definition creg_b : sv := ltac2:(tb__ "0|0|
SaeS10U8S1aS36S49A1A1S12Z0A1A4").

Definition pc_base : sv := ltac2:(tb__ "0|0|
S16S9fS16S9fSb2S12Zd0A1A3S2fSa6S11Sa8A1S12Z50A1A3A3").
Definition choff : sv := ltac2:(tb__ "0|0|
S16S9fS16Sa1S16S9fS11SacA1S12N1A1A3S12Z2A1A3S12Z10A1A3").

Definition O_pcc : sobj := ltac2:(tb__ "0|2|
S18S46S12Z0A1M0S12Z4M1A1S0S15S1cG0G1S11SacA1A3S1S15A1A3S19A5").
Definition O_pcs : sobj := ltac2:(tb__ "0|2|
S18S46S12Z8M0A1M1S12Z10A1S0S15S1cG1G0S11Sa9A1A3S1S15A1A3S19A5").
Definition O_pck : sobj := ltac2:(tb__ "0|0|
S18S46S5dS12Z50A1S0S15S1cS5dZ4S11SabA1A3S1S15A1A3S19A5").

Definition O_pcc0 : sobj := ltac2:(tb__ "0|2|
S18S46S12Z0A1M0S12Z4M1A1S0S15S1cG0G1G0A3S1S15A1A3S19A5").
Definition O_st : sobj := ltac2:(tb__ "0|0|
S18Sb2S12Zad0A1S12Zc60A1S1S15A1S19A5").
Definition F_cls : list sprop := ltac2:(tb__ "0|2|
S0S13S17S12Z1A1S11Sa8A1M0A2S0S13S17G0S12Z1eA1A2S0S13S17S11SaaA1S11Sa9A1M1A2S0S13S17G1S12Z10000A1A2S0S13S26Sa9Z4A2S1S13A1A3A3A3A3A3").
Definition F_pop : list sprop := ltac2:(tb__ "0|1|
S0S13S17S12Z1A1S11SacA1M0A2S0S13S17G0S12Z10A1A2S0S13S30S11SabA1S12Sb6Z2Z1cA2A1A2S1S13A1A3A3A3").
Definition C2_ru : list (nat * sv) := ltac2:(tb__ "0|1|
S0S8S2S10A2M0S3S2S10U5S11Pa5A1A4S0G0S3S2S10U6S11Pa6A1A4S0G0S3S2S10U7S11Pa7A1A4S0G0S3S2S10U8S11Sa8A1A4S0G0S3S2S10UcS11PacA1A4S0G0S3S2S10UeS11PaeA1A4S0G0S3S2S10UfS11PafA1A4S0G0S3S2S10U10S11Pb0A1A4S0G0S3S2S10U11S11Pb1A1A4S1G0A1A3A3A3A3A3A3A3A3A3").

Definition C2p0 : axst := ltac2:(tb__ "0|0|
S3cS49Z40d40S50S0S14S92S0S14S95S0S14S94S0S14S5cS1S14A1A3A3A3A3S5S1S13A1A6").
Definition C2r0 : axst := ltac2:(tb__ "0|0|
S3cS49Z40d40S50S0S14S93S0S14S5cS1S14A1A3A3S5S1S13A1A6").
Definition C2p : axst := ltac2:(tb__ "0|0|
Sb1S7S13S3dS3eA3S61A2").
Definition C2r : axst := ax_add_facts F_cls C2r0.
Definition run3p : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Z40e58S0S31Z3c614S1S31A1A3A3S60S5A5G0R1Ll;S1S34A1X4x2").
Definition run3r : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Z40e58S0S31Z3c614S1S31A1A3A3S62S5A5G0R1Ll;S1S34A1X4x2").
Definition E3p : axst := leaf 0 run3p.
Definition E3r : axst := leaf 0 run3r.

Definition ab_e : sv := ltac2:(tb__ "0|0|
S16S9fS16Sa1S11SabA1S12Z4A1A3S16S9fS16Sa1S11Sa8A1S12Z20A1A3SceA3A3").
Definition ube : sv := ltac2:(tb__ "0|0|
S16S9fS4cS11Sa7A1A3").
Definition uee : sv := SAlu ALU_ADD ube (SVar 12).
Definition M48 : Z := 281474976710648.
Definition n8e : sv := ltac2:(tb__ "0|0|
S16Sa3S11PcA1S12S8cA1A3").
Definition LLe : sv := ltac2:(tb__ "0|0|
S16Sa2S11Sa7A1S12Z3A1A3").
Definition LUe : sv := SAlu ALU_SRL n8e (SLit 3).
Definition LPe : sv := ltac2:(tb__ "0|1|
S16Sa2S16S9fS16Sa3S11PcA1S12Z7A1M0A3G0A3S12Z3A1A3").
Definition LRe : sv := ltac2:(tb__ "0|0|
S16Sa2S16Sa0S16Sa0S11Sa9A1S11Sa7A1A3SccA3S12Z3A1A3").
Definition LTe : sv := ltac2:(tb__ "0|0|
S16Sa0S16Sa0S11Sa9A1S11Sa7A1A3S11PcA1A3").
Definition BSH : sv := ltac2:(tb__ "0|0|
S16S9fS9cS4cA1S9dA3").
Definition BU : sv := ltac2:(tb__ "0|0|
S16S9fS9cS47A1S9dA3").
Definition BP : sv := SAlu ALU_ADD BU LUe.
Definition BR : sv := SAlu ALU_ADD BP LPe.
Definition O_H : sobj := ltac2:(tb__ "0|0|
S18S4cS12Z0A1S11Sa7A1S1S15A1S19A5").
Definition O_UB : sobj := ltac2:(tb__ "0|0|
S18S47S12Z0A1S11PcA1S1S15A1S19A5").
Definition O_T : sobj := ltac2:(tb__ "0|0|
S18S9aS12Z0A1S8bS1S15A1S19A5").
Definition O_L : sobj := ltac2:(tb__ "0|0|
S18S4fS12Z0A1S58S1S15A1S19A5").
Definition O_U : sobj := ltac2:(tb__ "0|0|
S18S48S12Z0A1S45S1S15A1S19A5").
Definition O_Uz : sobj := ltac2:(tb__ "0|0|
S18S48S12Z0A1S45S1S15A1S2eA5").
Definition O_P : sobj := ltac2:(tb__ "0|0|
S18S4dS12Z0A1S59S1S15A1S19A5").
Definition O_R : sobj := ltac2:(tb__ "0|0|
S18S4eS12Z0A1S5aS1S15A1S19A5").
Definition PIECES : list sobj := ltac2:(tb__ "0|0|
S0S14S8dS0S14S4bS0S14S8fS0S14S4aS0S14S90S0S14S8eS0S14S5bS1S14A1A3A3A3A3A3A3A3").
Definition C3 : axst := ltac2:(tb__ "0|0|
S3cS7bZ3c614S1S8S2S10A2A1S96S9S1S13A1A6").
Definition run4 : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Z7e9e4S1S31A1A3S63S5A5G0R1Ll;S1S34A1X4x2").
Definition E4d : axst := leaf 0 run4.

Definition HAVOC_CALLER : list (nat * sv) := ltac2:(tb__ "0|1|
S0S8S2S10A2M0S3S2S10U5S11Pa5A1A4S0G0S3S2S10U6S11Pa6A1A4S0G0S3S2S10U7S11Pa7A1A4S0G0S3S2S10UbS11PabA1A4S0G0S3S2S10UcS11PacA1A4S0G0S3S2S10UdS11PadA1A4S0G0S3S2S10UeS11PaeA1A4S0G0S3S2S10UfS11PafA1A4S0G0S3S2S10U10S11Pb0A1A4S0G0S3S2S10U11S11Pb1A1A4S0G0S3S2S10U1cS11PbcA1A4S0G0S3S2S10U1dS11PbdA1A4S0G0S3S2S10U1eS11PbeA1A4S0G0S3S2S10U1fS11PbfA1A4S1G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition HAVOC_JOIN : list (nat * sv) := ltac2:(tb__ "0|1|
S7S8S2S10A2M0S40S0G0S3S2S10U1S11Pa9A1A4S0G0S3S2S10U8S11Pa8A1A4S0G0S3S2S10UaS11Pb4A1A4S0G0S3S2S10U19S11Pb9A1A4S1G0A1A3A3A3A3A3").
Definition HAVOC_JOIN6 : list (nat * sv) := ltac2:(tb__ "0|1|
S7S8S2S10A2M0S57S0G0S3S2S10U16S11Pb6A1A4S1G0A1A3A3").

Definition set_obj_from_end (k : nat) (o : sobj) (E : axst) : axst := ltac2:(tb__ "0|0|
S36VE;A1S25S22R1A1S6S14A1Sb7Sb7SeS14R1A2U1A2Vk;A2S2S37VE;S1bS23R3A1S1aR3A1S1fR3A1S1eR3A1S24R3A1S7S14SafS14R1R2A3S7S14S0S14Vo;S1S14A1A3Sb0S14SdR1A1R2A3A3A3S1dR3A1S21R3A1S20R3A1A9A2Ti;Tobjs;TS;").

Definition live_cell (lo : Z) (c : cell) : bool := ltac2:(tb__ "0|3|
S10SaLx;S28Vc;A1S31Sb4Vlo;R1A2Lz;S32S5Li;Sa4S10S10S5Lb;La;M0Lop;M1G1Sa5G0Lop;M2G2SaS33S10S5La;Lw;Lsgn;S32S10S31S5Lk;Li;Ll;X10x8").
Definition prune_sw (lo : Z) (E : axst) : axst := ltac2:(tb__ "0|2|
S36VE;A1S25S6S14A1M0S38Lx;S22R1A1VE;S14G0S37VE;S1bS23R3A1S1aR3A1S1fR3A1S1eR3A1S24R3A1S0S14S18S29R2A1S2dR2A1S2cR2A1Sc6S15S6S15A1Sc8S15A1S15Sc5S98Vlo;R1A2M1A1Lc;S15Sc7G1A1Lx;S2aR2A1A6S2bR2A1A5R1A3S1dR3A1S21R3A1S20R3A1A9A2Lrest;Lo;X6x2TS;").
Definition LIVE : Z := -2272.

Definition call_cell (c : cell) : bool := ltac2:(tb__ "0|3|
S10SaLx;S28Vc;A1S31ScSb4S3fR1A2SfScSb4N840R1A2Sb5R1N48A2A2A1A2Lz;S32S5Li;Sa4S10S10S5Lb;La;M0Lop;M1G1Sa5G0Lop;M2G2SaS33S10S5La;Lw;Lsgn;S32S10S31S5Lk;Li;Ll;X10x8").
Definition prune_call (E : axst) : axst := ltac2:(tb__ "0|2|
S36VE;A1S25S6S14A1M0S38Lx;S22R1A1VE;S14G0S37VE;S1bS23R3A1S1aR3A1S1fR3A1S1eR3A1S24R3A1S0S14S18S29R2A1S2dR2A1S2cR2A1Sc6S15S6S15A1Sc8S15A1S15Sc5S97R1A1M1A1Lc;S15Sc7G1A1Lx;S2aR2A1A6S2bR2A1A5R1A3S1dR3A1S21R3A1S20R3A1A9A2Lrest;Lo;X6x2TS;").
Definition C5 : axst := ltac2:(tb__ "0|1|
S99S3cS7cZ7ec58S0S8S2S10A2M0S3S2S10UaS11PaaA1A4S0G0S3S2S10U1S12Z3c720A1A4S40A3A3S1S14A1S9S1S13A1A6A1").
Definition run5 : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Z3c774S0S31Z3c80cS1S31A1A3A3S64S5A5G0R1Ll;S1S34A1X4x2").
Definition E5n : axst := leaf 0 run5.
Definition E5f : axst := leaf 1 run5.

Definition C5b : axst := ltac2:(tb__ "0|2|
S3cS7dZ3c774S0S8S2S10A2M0S3S2S10U8S11Sa8A1M1A4S0G0S3S2S10UaG1A4S1G0A1A3A3S1S14A1S9S1S13A1A6").
Definition run5b : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Z3c7e0S1S31A1A3S65S5A5G0R1Ll;S1S34A1X4x2").
Definition E5s1 : axst := leaf 0 run5b.
Definition E5s2 : axst := leaf 1 run5b.
Definition sreg1 : sv := ltac2:(tb__ "0|0|
SaeS10U8S1aS36S53A1A1S12Z0A1A4").
Definition sreg2 : sv := ltac2:(tb__ "0|0|
SaeS10U8S1aS36S81A1A1S12Z0A1A4").

Definition C5c : axst := ltac2:(tb__ "0|1|
S41S3fS3cS53Z3c7e0S0S8S2S10A2M0S3S2S10U8S11Sa9A1A4S0G0S3S2S10UaS11Pb4A1A4S0G0S3S2S10UbS11PabA1A4S1G0A1A3A3A3S1S14A1S5S7S13S3dS3eA3A6A2").
Definition run5c : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Zdb004S1S31A1A3S66S5A5G0R1Ll;S1S34A1X4x2").
Definition E5m1 : axst := leaf 0 run5c.
Definition MSENT : Z := 0xdb004.
Definition MSRET : Z := 0xdb0f8.

Definition C5m1 : axst := ltac2:(tb__ "0|1|
S3cS7eS43S0S8S2S10A2M0S3S2S10UaS4fA4S0G0S3S2S10UcS58A4S1G0A1A3A3S1S14A1S9S1S13A1A6").
Definition C5d : axst := ltac2:(tb__ "0|0|
S42U3S4aS3cS69S44S40S1S14A1S9S1S13A1A6A3").
Definition run5d : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Zdb004S1S31A1A3S67S5A5G0R1Ll;S1S34A1X4x2").
Definition E5m2 : axst := leaf 0 run5d.
Definition C5m2 : axst := ltac2:(tb__ "0|1|
S3cS7fS43S0S8S2S10A2M0S3S2S10UaS4eA4S0G0S3S2S10UcS5aA4S1G0A1A3A3S1S14A1S9S1S13A1A6").
Definition C5e : axst := ltac2:(tb__ "0|0|
S42U0S5bS3cS6aS44S40S1S14A1S9S1S13A1A6A3").
Definition run5e : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Z3c80cS1S31A1A3S68S5A5G0R1Ll;S1S34A1X4x2").
Definition E5j : axst := leaf 0 run5e.

Definition C6 : axst := ltac2:(tb__ "0|0|
S41S3fS42U3S4aS3cS80Z3c80cS8aS1S14A1S5S7S13S3dS3eA3A6A3A2").

Definition run6 : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Z5f9f8S0S31Z3c82cS1S31A1A3A3S6bS5A5G0R1Ll;S1S34A1X4x2").
Definition E6s : axst := leaf 0 run6.
Definition E6l : axst := leaf 1 run6.
Definition lenx : sv := LUe.
Definition C6l : axst := ltac2:(tb__ "0|1|
S3cS83Z5f9f8S0S8S2S10A2M0S3S2S10U8S45A4S1G0A1A3S1S14A1S9S1S13A1A6").
Definition run6l : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Zdb004S1S31A1A3S6dS5A5G0R1Ll;S1S34A1X4x2").
Definition E6m : axst := leaf 0 run6l.
Definition C6m : axst := ltac2:(tb__ "0|1|
S3cS84S43S0S8S2S10A2M0S3S2S10UaS48A4S0G0S3S2S10UcS45A4S1G0A1A3A3S1S14A1S9S1S13A1A6").

Definition C6b : axst := ltac2:(tb__ "0|0|
S42U2S91S3cS6eS44S40S1S14A1S9S1S13A1A6A3").
Definition run6b : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Z3c82cS1S31A1A3S6cS5A5G0R1Ll;S1S34A1X4x2").
Definition E6j : axst := leaf 0 run6b.

Definition C7 : axst := ltac2:(tb__ "0|0|
S41S3fS3cS82Z3c82cS57S1S14A1S5S7S13S3dS3eA3A6A2").
Definition run7 : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Z3c8bcS0S31Z3ca04S1S31A1A3A3S6fS5A5G0R1Ll;S1S34A1X4x2").
Definition E7c1 : axst := leaf 0 run7.
Definition E7c2 : axst := leaf 1 run7.
Definition E7p : axst := leaf 2 run7.
Definition creg7a : sv := ltac2:(tb__ "0|0|
SaeS10UbS1aS36S54A1A1S12Z0A1A4").
Definition creg7b : sv := ltac2:(tb__ "0|0|
SaeS10UbS1aS36S85A1A1S12Z0A1A4").

Definition C7p : axst := ltac2:(tb__ "0|1|
S3cS86Z3c8bcS0S8S2S10A2M0S3S2S10UaS4dA4S1G0A1A3S1S14A1S9S0S13S17S12Z1A1S59A2S1S13A1A3A6").
Definition run7p : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Z3ca04S1S31A1A3S70S5A5G0R1Ll;S1S34A1X4x2").
Definition E7q1 : axst := leaf 0 run7p.
Definition E7q2 : axst := leaf 1 run7p.
Definition creg7c : sv := ltac2:(tb__ "0|0|
SaeS10UbS1aS36S55A1A1S12Z0A1A4").
Definition creg7d : sv := ltac2:(tb__ "0|0|
SaeS10UbS1aS36S87A1A1S12Z0A1A4").

Definition HAVOC_C8 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S8S2S10A2M0S3S2S10U5S11Pa5A1A4S0G0S3S2S10U6S11Pa6A1A4S0G0S3S2S10U7S11Pa7A1A4S0G0S3S2S10UbS11Sa8A1A4S0G0S3S2S10UcS11PacA1A4S0G0S3S2S10UdS11PadA1A4S0G0S3S2S10UeS11PaeA1A4S0G0S3S2S10UfS11PafA1A4S0G0S3S2S10U10S11Pb0A1A4S0G0S3S2S10U11S11Pb1A1A4S0G0S3S2S10U1cS11PbcA1A4S0G0S3S2S10U1dS11PbdA1A4S0G0S3S2S10U1eS11PbeA1A4S0G0S3S2S10U1fS11PbfA1A4S1G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C8 : axst := ltac2:(tb__ "0|0|
S41S3fS3cS54Z3ca04S56S1S14A1S5S7S13S3dS3eA3A6A2").
Definition C8p : axst := ltac2:(tb__ "0|0|
S41S3fS3cS55Z3ca04S56S1S14A1S5S7S13S3dS3eA3A6A2").
Definition run8 : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Zdb004S0S31Z3ca54S1S31A1A3A3S71S5A5G0R1Ll;S1S34A1X4x2").
Definition run8p : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S0S31Zdb004S0S31Z3ca54S1S31A1A3A3S74S5A5G0R1Ll;S1S34A1X4x2").
Definition E8a : axst := leaf 0 run8.
Definition E8b : axst := leaf 1 run8.
Definition E8pa : axst := leaf 0 run8p.
Definition E8pb : axst := leaf 1 run8p.

Definition C8ma : axst := ltac2:(tb__ "0|1|
S3cS88S43S0S8S2S10A2M0S3S2S10UaS47A4S1G0A1A3S1S14A1S9S1S13A1A6").
Definition C8mpa : axst := ltac2:(tb__ "0|1|
S3cS89S43S0S8S2S10A2M0S3S2S10UaS47A4S1G0A1A3S1S14A1S9S1S13A1A6").

Definition C9 : axst := ltac2:(tb__ "0|0|
S41S3fS42U5S4bS3cS72S44S40S1S14A1S5S7S13S3dS3eA3A6A3A2").
Definition C9p : axst := ltac2:(tb__ "0|0|
S41S3fS42U5S4bS3cS73S44S40S1S14A1S5S7S13S3dS3eA3A6A3A2").

Definition C9a : axst := ltac2:(tb__ "0|0|
Sb1S0S13S17S12Z20A1S11Sa7A1A2S1S13A1A3S51A2").
Definition C9b : axst := ltac2:(tb__ "0|0|
Sb1S0S13S17S11Sa7A1S12Z10A1A2S1S13A1A3S51A2").
Definition C9pa : axst := ltac2:(tb__ "0|0|
Sb1S0S13S17S12Z20A1S11Sa7A1A2S1S13A1A3S52A2").
Definition C9pb : axst := ltac2:(tb__ "0|0|
Sb1S0S13S17S11Sa7A1S12Z10A1A2S1S13A1A3S52A2").
Definition run9a : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S1S31A1S75S5A5G0R1Ll;S1S34A1X4x2").
Definition run9b : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S1S31A1S76S5A5G0R1Ll;S1S34A1X4x2").
Definition run9pa : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S1S31A1S77S5A5G0R1Ll;S1S34A1X4x2").
Definition run9pb : list leafA := ltac2:(tb__ "0|1|
S4S6S34A1M0A1G0Lx;S35S9bUfa0S1S31A1S78S5A5G0R1Ll;S1S34A1X4x2").
End W.

Definition showL (L : leafA) : ltac2:(tb__ "0|0|
S8S31SbbA2") := ltac2:(tb__ "0|0|
S3S31SbbS23S36S39VL;A1A1A1S3aVL;A1A4").

