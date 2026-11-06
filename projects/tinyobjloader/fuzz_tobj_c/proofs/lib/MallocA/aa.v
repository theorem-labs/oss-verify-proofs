(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From Stdlib Require NArith PArith Lia FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_laws2.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.

(* [comment removed for export] *)
Module SegQI_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "nat"; "true"; "pair"; "prod"; "false"; "list"; "app"; "None"; "Some"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "sobj"; "SAlu"; "SVar"; "ss_next"; "ss_lenient"; "SPUle"; "cell"; "ss_facts"; "SPBranch"; "SPAlign"; "mkCell"; "DUnknown"; "mkObj"; "SExt"; "SPNot"; "mkSS"; "sprop_below"; "sprop_eqb"; "SPUlt"; "FcsrFrm0"; "SMd"; "ss_fcsr"; "ss_fregs"; "ss_objs"; "ss_regs"; "ss_resv"; "sstate"; "SMdW"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "axwf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "add"; "leaf"; "NPRE"; "vSB"; "vMX"; "vPK"; "vST"; "DEPTH_Q"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states"; "vCLS"; "updQ"; "vSZ"; "NXI"; "QI1"; "C5a"; "C5b"; "MSENTQ"; "PSENT"; "QCENTI"; "QI0"; "QI2"; "QI3"; "vN8"; "C1a"; "C1b"; "E1ba"; "E1bb"; "PreQI"; "bgv"; "s5a"; "s5b"; "C0a"; "C0b"; "C2a"; "C2b"; "C3a"; "C3b"; "C4a"; "C4b"; "C6a"; "C6b"; "E1aa"; "E1ab"; "F_QI"; "LENq"; "R5a"; "R5b"; "XF"; "run1a"; "run1b"; "E0a"; "E0b"; "E2a"; "E2b"; "E3a"; "E3b"; "E4a"; "E4b"; "E5a"; "E5b"; "E6a"; "E6b"; "QIRET"; "T5a"; "T5b"; "T5fa"; "T5fb"; "dI0"; "dI1a"; "dI1b"; "dI2"; "dI3"; "dI4"; "dI5"; "dI6"; "run0a"; "run0b"; "run2a"; "run2b"; "run3a"; "run3b"; "run4a"; "run4b"; "run5a"; "run5b"; "run6a"; "run6b"; "run7a"; "run7b"; "vAB"; "vHW"; "E1aa'"; "E1ab'"; "E1ba'"; "E1bb'"; "E7a"; "E7b"; "O_cb"; "O_entI"; "O_hdrI"; "O_ish"; "O_rie"; "O_slotI"; "O_stq"; "PostQI"; "RTI"; "XOBJ"; "cacheI"; "dmS"; "entI"; "hw'"; "optR"; "regsI"; "updF"; "vMU"; "vNlo"; "BSHq"; "NXQI"; "OBJS_I"; "O_mag"; "QIENT"; "cls2T"; "clsQCT"; "clsT"; "cptrT"; "kAllocBegMagic"; "lenT"; "nT"; "post_ruI"; "qT"; "rup8T"; "s2T"; "sh255T"; "sh3T"; "slotI"; "szBigT"; "szSmallT"; "vSTK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "sdiff"; "one_at"; "diffs_below"; "entsI"; "two_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "memset_entryA"; "Posts_memsetA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SRL"; "ALU_SLL"; "ALU_AND"; "ALU_SUB"; "BC_GEU"; "BC_EQ"; "M_MUL"; "ALU_OR"; "ALU_SLTU"; "ALU_SRA"; "ALU_XOR"; "BC_NE"; "M_DIVU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "vRIS"; "O_insta"; "O_insta2"; "O_rms";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kSpaceSize"; "HIGH_SHADOW_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "mkA"; "stack_win"; "pre_facts"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "O_ctx98"; "O_rt1a"; "O_rt1b"; "O_self_tsd"; "O_tsd0"; "O_tsda"; "O_tsdb"; "O_tsdc"; "TP_A"; "vT"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Open Scope Z_scope.

Definition QIENT : Z := 0x3e5d0.
Definition QI0 : Z := 0x3e624.
Definition QI1 : Z := 0x3e680.
Definition QI2 : Z := 0x3e6bc.
Definition QI3 : Z := 0x3e6f8.
Definition PSENT : Z := 0x5f5bc.
Definition MSENTQ : Z := 0xde378.
Definition QCENTI : Z := 0x3e9d4.
Definition QIRET : Z := 0x3ea74.
Definition NXI : positive := 200%positive.
Definition NXQI : positive := 260%positive.

Definition vMU := SVar 138. Definition vHW := SVar 139. Definition vNlo := SVar 141. Definition vSTK := SVar 142. Definition vN8 := SVar 145.
Definition vCLS : sv := SVar V_CLS. Definition vSZ : sv := SVar V_SIZE.
Definition cacheI : sv := add vT (SLit 208).

Definition O_cb : sobj := ltac2:(tb__ "0|4|
Se0S16PcA1Z0M0Z10S0S6S6SdS3A2M1S11A2M2S5G1S11S5SdS3G0U8M3A4Sa2A4S0G2S5G1S11S5SdS3Z8G3A4Sc0A4S2G2A1A3A3A4").
Definition O_rie : sobj := ltac2:(tb__ "0|1|
S20S38Se4S15ScaS40S12Z7A1A3A2S12Z30A1M0S12Z38A1S0S1aS1eG0Z8Sa9A3S2S1aA1A3S1fA5").
Definition O_hdrI (w : sv) : sobj := ltac2:(tb__ "0|4|
Se0S16PdA1Z0M0Z8S0S6S6SdS3A2M1S11A2M2S5G1S11S5SdS3G0U4M3A4Vw;A4S0G2S5G1S11S5SdS3Z4G3A4SaaA4S2G2A1A3A3A4").
Definition BSHq : sv := ltac2:(tb__ "0|0|
S38S15Sc9S38S16PdA1S12Z10A1A2S12Z3A1A3S12Z7fff8000A1A2").
Definition LENq : sv := SAlu ALU_SRL vN8 (SLit 3).
Definition O_ish : sobj := ltac2:(tb__ "0|0|
S20SabS12Z0A1S63S2S1aA1S1fA5").
Definition entI : sv := ltac2:(tb__ "0|0|
S38Sa2S28ScfS40S12Z50A1A3A2").
Definition O_entI (k : sv) : sobj := ltac2:(tb__ "0|3|
S20Sa4S12Z0A1M0S12Z10A1S0S1aS1eG0Z4M1Vk;A3S0S1aS1eS12G1A1G1S3cA3S0S1aS1eS12Z8M2A1G2S42A3S2S1aA1A3A3A3S1fA5").
Definition slotI : sv := ltac2:(tb__ "0|0|
S38Sa4S15ScaS3dS12Z2A1A3A2").
Definition O_slotI (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20SbdS12Z10A1S12Z14A1Vcells;S1fA5").
Definition O_stq (v : sv) : sobj := ltac2:(tb__ "0|0|
S20SfbS12Zad0A1S12Zc60A1S0S1aS1eS12Zae0A1Z8Vv;A3S2S1aA1A3S1fA5").
Definition RTI : list sobj := ltac2:(tb__ "0|0|
S0S14Se5S0S14Se6S0S14Se7S0S14Sf7S0S14Sf8S0S14Sf9S0S14Sf5S0S14Sf6S0S14Sf2S0S14Sf3S0S14Sf4S2S14A1A3A3A3A3A3A3A3A3A3A3A3").

Definition vAB := SVar 146.
Definition kAllocBegMagic : Z := 0xCC6E96B9CC6E96B9.
Definition O_mag (w : sv) : sobj := ltac2:(tb__ "0|4|
Se0S90Z0M0Z10S0S6S6SdS3A2M1S11A2M2S5G1S11S5SdS3G0U8M3A4Vw;A4S0G2S5G1S11S5SdS3Z8G3A4S16PdA1A4S2G2A1A3A3A4").
Definition bgv (vb : bool) : sv := if vb then vAB else SVar 13.
Definition XOBJ (vb : bool) (w : sv) : list sobj := ltac2:(tb__ "0|1|
S1S8S14A1Lvb;Vvb;S0S14SaeVw;A1S2S14A1M0A3G0X1x2").
Definition XF (vb : bool) : list sprop := ltac2:(tb__ "0|1|
S1S8S13A1Lvb;Vvb;S0S13S1dP92Z4A2S0S13S19S3bS90A2S0S13S26S90S16PdA1A2S2S13A1M0A3A3A3G0X1x2").

Definition F_QI : list sprop := ltac2:(tb__ "0|9|
S9S13SedS3fA1S9S13Sf0S0S13S1dPdM0Z4M1A2S0S13S1dPcZ3M2A2S0S13S1dP9bZ10M3A2S0S13S19S12Se9A1S3bA2S0S13S19S3bS12SeeSeeZ7fffff800000M4Se8A2Z1000A2A1A2S0S13S1cSceSe4S38S3bS12Se8A1A2M5A3S0S13S19S12Z1A1S40A2S0S13S19S40S12Z1eA1A2S0S13S19S12G3A1M6S42A2S0S13S19S42S12Z10000A1A2S0S13S1dSf1G1A2S0S13S19S3bS16G0A1M7A2S0S13S26G7G5A2S0S13S22S1cSd4S15ScbS21S4Q20S91A3S12ZffA1A3S12G2A1A3A1S0S13S22S1cSceS3cS12Z0A1A3A1S0S13S26S3dS3cA2S0S13S19S3cS12Z100A1A2S0S13S19S12Z8A1S4dA2S0S13S19S4dS12SefZ2Z28A2A1A2S0S13S1dP91G2A2S0S13S19S38S38G7G6A2S4dA2M8G5A2S0S13S19G8S12G4A1A2S2S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition regsI : list sv := ltac2:(tb__ "0|1|
Sd7Sd9S0S6S3S11A2M0S5S3S11U4S12SfaA1A4S2G0A1A3A2").
Definition OBJS_I (hw : sv) (k : sv) (slot : list cell) (st : sv) : list sobj := ltac2:(tb__ "0|0|
S9S14S0S14SecSeaA3S9S14Sa0S0S14S98S0S14S9cS0S14S9aVhw;A1S0S14S9bS0S14S99Vk;A1S0S14S9dVslot;A1S0S14S9eVst;A1S2S14A1A3A3A3A3A3A3A3A3A3").
Definition PreQI (vb : bool) : axst := ltac2:(tb__ "0|0|
SebS23SafSa7Sd8S27SaS11A1S9S14SadS91S3dS2S1aA1S3eA4Sa1Vvb;S12Sb4A1A2A3S9S13S62S66Vvb;A1A3S3aS7A9S2S6S11S11A2A1A2").

Definition updQ (E : axst) (pc : Z) (ru : list (nat * sv)) : axst := ltac2:(tb__ "0|0|
S31VE;A1S2eS34VE;S23Vpc;Sd7S2cR1A1Vru;A2S2aR1A1S29R1A1S2dR1A1S2bR1A1S1bR1A1S17R1A1S18R1A1A9A2TS;").
Definition updF (E : axst) (pc : Z) (ru : list (nat * sv)) (F : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|0|
S31VE;A1S2eS34VE;S23Vpc;Sd7S2cR1A1Vru;A2S2aR1A1S29R1A1S2dR1A1S2bR1A1VF;Vnx;S18R1A1A9A2TS;").

Definition dmS : sv := SAlu ALU_SUB (SVar 13) vSB.
Definition clsT : sv := ltac2:(tb__ "0|0|
S15ScbS15Sc9Sa3S12Z20A1A3S12Z1fA1A3").
Definition cls2T : sv := SAlu ALU_SRL dmS (SLit 32).
Definition szBigT : sv := ltac2:(tb__ "0|3|
S38S15ScbS15Sd2S15ScaS40S12Z3fA1M0A3G0A3S15Sc9S15ScaS12Z200A1S15Sc9S38S40S12N10A1A2S12Z1A1M1A3A3M2G1A3A3G2A2").
Definition szSmallT : sv := SAlu ALU_SLL vCLS (SLit 5).
Definition qT : sv := ltac2:(tb__ "0|1|
S15Sc9S15ScaS2fSd5Sa3S42A3S12Z20A1M0A3G0A3").
Definition s2T : sv := ltac2:(tb__ "0|1|
S15ScbS38S15Sd1Sa9S38S28ScfS42Sb8A3M0S42A2A3S12N1A1A2S38S38S15ScaS40S12Z20A1A3S3bA2G0A2A3").
Definition m8T : sv := SAlu ALU_SLL (SVar 13) (SLit 3).
Definition sh3T : sv := SAluW ALU_SLL (SLit 3) m8T.
Definition sh255T : sv := SAluW ALU_SLL (SLit 255) m8T.
Definition hw' : sv := ltac2:(tb__ "0|0|
S15Sd3S21S4Q20S91A3S12Z3A1A3").
Definition nT : sv := ltac2:(tb__ "0|0|
S15Sd0S15ScaS21S7Q10S15Sc9Sa5S12Z10A1A3A3S12Z20A1A3S21S7Q20SaaA3A3").
Definition rup8T : sv := ltac2:(tb__ "0|0|
S15ScbS38Sb6S12Z7A1A2S12Zfffffffffffffff8A1A3").
Definition lenT : sv := ltac2:(tb__ "0|2|
S15SccS38S15Sc9S38S38S38S16PdA1S12Z10A1A2M0S4dA2S12N8A1A2S12Z3A1M1A3S12Z1A1A2S15Sc9G0G1A3A3").
Definition clsQCT (vb : bool) : sv := ltac2:(tb__ "0|0|
S15Sc9S15ScaS15SccS53Vvb;A1S3bA3S12Z1bA1A3S12Z3bA1A3").
Definition cptrT (vb : bool) : sv := ltac2:(tb__ "0|0|
S15Sc9S15SccS15SccS53Vvb;A1S15ScaS40S12Z20A1A3A3S3bA3S12Z4A1A3").

Definition dI0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11Sb2S40A4S0G0S5S11S11Sb0S40A4S2G0A1A3A3").
Definition dI1a : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11SbeS42A4S2G0A1A3").
Definition dI1b : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11SbfS42A4S2G0A1A3").
Definition dI2 (vb : bool) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11SbaS53Vvb;A1A4S2G0A1A3").
Definition dI3 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11SbcS12Z3A1A4S0G0S5S11S11SbbS12ZffA1A4S2G0A1A3A3").
Definition dI4 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11Sb9S4dA4S2G0A1A3").
Definition dI5 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11Sb5S63A4S2G0A1A3").
Definition dI6 (vb : bool) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11Sb1Vvb;A1S40A4S2G0A1A3").

Definition optR (o : option (list sobj)) : list sobj := match o with Some r => r | None => [] end.

Definition post_ruI : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S3S11A2M0S5S3S11U0S16Pb8A1A4S0G0S5S3S11U5S16Pb9A1A4S0G0S5S3S11U6S16PbaA1A4S0G0S5S3S11U7S16PbbA1A4S0G0S5S3S11UaS16PbcA1A4S0G0S5S3S11UbS16PbdA1A4S0G0S5S3S11UcS16PbeA1A4S0G0S5S3S11UdS16PbfA1A4S0G0S5S3S11UeS16Pc0A1A4S0G0S5S3S11UfS16Pc1A1A4S0G0S5S3S11U10S16Pc2A1A4S0G0S5S3S11U11S16Pc3A1A4S0G0S5S3S11U1cS16Pc4A1A4S0G0S5S3S11U1dS16Pc5A1A4S0G0S5S3S11U1eS16Pc6A1A4S0G0S5S3S11U1fS16Pc7A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition PostQI (vb : bool) : axst := ltac2:(tb__ "0|1|
SebS23S75Sd7Sa7Sb7A2Sd8S27SaS11A1S0S14S9bS9S14S0S14SecSeaA3S9S14Sa0S9S14S0S14S98S0S14S9cS0S14S9aSa5A1S0S14S99S38S3dS12Z1A1A2A1S0S14S9dS0S1aS1eS12Z10A1Z4Sb3Vvb;A1A3S2S1aA1A3A1S0S14S9eS38S3eS15SccS12Z0A1M0S42A3A2A1S2S14A1A3A3A3A3A3A3Sa1Vvb;G0A2A3A3A3A3S9S13S62S66Vvb;A1A3SacS7A9S2S6S11S11A2A1A2").

Lemma preQI_wf : ltac2:(tb__ "0|2|
S1S10SfS1S36S52R1A1M0A1S4A3S10SfS1S30S31G0A1M1A1S4A3S10SfSeS17G1A1S3aA3SfS1S18G1A1S7A3A2A2A2Fvb;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma dI_below : ltac2:(tb__ "0|0|
S1S10SfS1Sc3S3aS7aA2S4A3S10SfS1Sc3S3aS7bA2S4A3S10SfS1Sc3S3aS7cA2S4A3S10SfS1Sc3S3aS7dR1A1A2S4A3S10SfS1Sc3S3aS7eA2S4A3S10SfS1Sc3S3aS7fA2S4A3S10SfS1Sc3S3aS80A2S4A3SfS1Sc3S3aS81R1A1A2S4A3A2A2A2A2A2A2A2Fvb;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run0a : list leafA := ltac2:(tb__ "0|0|
S37U12cS0SdS4aS0SdZ3e63cS2SdA1A3A3S52S7A1A3").
Definition E0a : axst := leaf 0 run0a.
Definition C0a : axst := ltac2:(tb__ "0|1|
S41S69S4aS0S6S3S11A2M0S5S3S11UcS40A4S0G0S5S3S11UdS40A4S2G0A1A3A3A3").
Definition run1a : list leafA := ltac2:(tb__ "0|0|
S37U12cS0SdS44S0SdZ3e63cS0SdZ3e810S0SdZ3e804S2SdA1A3A3A3A3S56A3").
Definition E1aa : axst := leaf 0 run1a.
Definition E1ba : axst := leaf 1 run1a.
Definition E1aa' : axst := ltac2:(tb__ "0|1|
S41S60S44S0S6S3S11A2M0S5S3S11UfS42A4S2G0A1A3A3").
Definition E1ba' : axst := ltac2:(tb__ "0|1|
S41S50S44S0S6S3S11A2M0S5S3S11UfS42A4S2G0A1A3A3").
Definition C1a : axst := ltac2:(tb__ "0|1|
Sa8S50S44S0S6S3S11A2M0S5S3S11UfS42A4S0G0S5S3S11U10S16Pb9A1A4S0G0S5S3S11U11S16PbaA1A4S2G0A1A3A3A3S9S13S62S66S7A1A3S43A5").
Definition run2a : list leafA := ltac2:(tb__ "0|0|
S37U12cS0SdS4bS2SdA1A3S4eA3").
Definition E2a : axst := leaf 0 run2a.
Definition C2a : axst := ltac2:(tb__ "0|1|
S41S6bS4bS0S6S3S11A2M0S5S3S11U12S53S7A1A4S2G0A1A3A3").
Definition run3a : list leafA := ltac2:(tb__ "0|0|
S37U258S0SdS4cS0SdZ3e818S0SdZ3e83cS0SdZ3e73cS2SdA1A3A3A3A3S58A3").
Definition E3a : axst := leaf 0 run3a.
Definition C3a : axst := ltac2:(tb__ "0|1|
S41S6dS4cS0S6S3S11A2M0S5S3S11UdS12Z3A1A4S0G0S5S3S11UeS12ZffA1A4S2G0A1A3A3A3").
Definition run4a : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdS48S0SdZ3e818S2SdA1A3A3S5aA3").
Definition E4a : axst := leaf 0 run4a.
Definition C4a : axst := ltac2:(tb__ "0|1|
S41S6fS48S0S6S3S11A2M0S5S3S11UbS4dA4S2G0A1A3A3").
Definition run5a : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdS47S0SdZ3e73cS0SdZ5fa44S0SdZ5fa24S0SdZ5fa64S0SdZ5fa84S0SdZ5fa04S2SdA1A3A3A3A3A3A3A3S5cA3").
Definition E5a : axst := leaf 0 run5a.
Definition C5a : axst := ltac2:(tb__ "0|1|
S41S71S47S0S6S3S11A2M0S5S3S11UcS63A4S2G0A1A3A3").
Definition s5a : wsub := ltac2:(tb__ "0|0|
Se2P1S31S45A1S31Sc6A1A3").
Definition R5a : list sobj := ltac2:(tb__ "0|0|
Sa6SdaS45Sc6S54A3A1").
Definition T5a : axst := ltac2:(tb__ "0|0|
SdbS54Sc6Sd6SddSc7A1A1S45S64A5").
Definition T5fa : axst := ltac2:(tb__ "0|0|
Se3S76S1bS31S45A1A1A2").
Definition run6a : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdS49S0SdZ3e7b8S0SdZ3e7d8S2SdA1A3A3A3S78A3").
Definition E6a : axst := leaf 0 run6a.
Definition C6a : axst := ltac2:(tb__ "0|1|
S41S73S49S0S6S3S11A2M0S5S3S11UcS40A4S2G0A1A3A3").
Definition run7a : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdZ3eb64S0SdZ3eabcS0SdZ3ea78S0SdZ3ea98S2SdA1A3A3A3A3S5eA3").
Definition E7a : axst := leaf 0 run7a.

Lemma run0a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U12cS0SdS4aS0SdZ3e63cS2SdA1A3A3S52S7A1A3S82A3"). Proof. unfold run0a. reflexivity. Qed.
Lemma chk0a : ltac2:(tb__ "0|0|
SfS1Sc2S82S4aA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd0a : ltac2:(tb__ "0|0|
SfS1Sc1S69S56S7aA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run1a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U12cS0SdS44S0SdZ3e63cS0SdZ3e810S0SdZ3e804S2SdA1A3A3A3A3S56A3S67A3"). Proof. unfold run1a. reflexivity. Qed.
Lemma chk1a : ltac2:(tb__ "0|0|
SfS1Sc5S67S44A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd1aa : ltac2:(tb__ "0|0|
SfS1Sc1S60S92S7bA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd1ba : ltac2:(tb__ "0|0|
SfS1Sc1S50S94S7cA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent1aa : ltac2:(tb__ "0|0|
SfS1Sc4S92S4eA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent1ba : ltac2:(tb__ "0|0|
SfS1Sc4S94S4eA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma br1aa : ltac2:(tb__ "0|0|
SfS1SdeS13S25S1cScdS40S12Z11A1A3A1S1bS31S60A1A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma br1ba : ltac2:(tb__ "0|0|
SfS1SdeS13S25S22S1cScdS40S12Z11A1A3A1A1S1bS31S50A1A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run2a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U12cS0SdS4bS2SdA1A3S4eA3S84A3"). Proof. unfold run2a. reflexivity. Qed.
Lemma chk2a : ltac2:(tb__ "0|0|
SfS1Sc2S84S4bA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd2a : ltac2:(tb__ "0|0|
SfS1Sc1S6bS58S7dS7A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run3a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U258S0SdS4cS0SdZ3e818S0SdZ3e83cS0SdZ3e73cS2SdA1A3A3A3A3S58A3S86A3"). Proof. unfold run3a. reflexivity. Qed.
Lemma chk3a : ltac2:(tb__ "0|0|
SfS1Sc2S86S4cA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd3a : ltac2:(tb__ "0|0|
SfS1Sc1S6dS5aS7eA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run4a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdS48S0SdZ3e818S2SdA1A3A3S5aA3S88A3"). Proof. unfold run4a. reflexivity. Qed.
Lemma chk4a : ltac2:(tb__ "0|0|
SfS1Sc2S88S48A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd4a : ltac2:(tb__ "0|0|
SfS1Sc1S6fS5cS7fA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run5a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdS47S0SdZ3e73cS0SdZ5fa44S0SdZ5fa24S0SdZ5fa64S0SdZ5fa84S0SdZ5fa04S2SdA1A3A3A3A3A3A3A3S5cA3S8aA3"). Proof. unfold run5a. reflexivity. Qed.
Lemma chk5a : ltac2:(tb__ "0|0|
SfS1Sc2S8aS47A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd5a : ltac2:(tb__ "0|0|
SfS1Sc1S71S45S80A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma He5a : ltac2:(tb__ "0|1|
SfScS8S14A1M0A1SdaS45Sc6S54A3SbG0S64A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk5a : ltac2:(tb__ "0|0|
SfS1SdcS45Sc6S54S64Se1S33S32S35Sc8A4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT5a : ltac2:(tb__ "0|0|
SfS32SdbS54Sc6Sd6SddSc7A1A1S45S64A5S76A3"). Proof. unfold T5a. reflexivity. Qed.
Lemma FBC5a : ltac2:(tb__ "0|1|
SfS1SdfS13S24S17S31S45A1M0A1A1S1bG0A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT5a : ltac2:(tb__ "0|0|
SfS1SdfS13S24S17S31S76A1A1A1S1bS31S45A1A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run6a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdS49S0SdZ3e7b8S0SdZ3e7d8S2SdA1A3A3A3S78A3S8cA3"). Proof. unfold run6a. reflexivity. Qed.
Lemma chk6a : ltac2:(tb__ "0|0|
SfS1Sc2S8cS49A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd6a : ltac2:(tb__ "0|0|
SfS1Sc1S73S5eS81S7A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run7a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdZ3eb64S0SdZ3eabcS0SdZ3ea78S0SdZ3ea98S2SdA1A3A3A3A3S5eA3S8eA3"). Proof. unfold run7a. reflexivity. Qed.
Lemma chk7a : ltac2:(tb__ "0|0|
SfS1Sc2S8eS75A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent7a : ltac2:(tb__ "0|0|
SfS1Sc4S96S9fS7A1A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nxC0a : ltac2:(tb__ "0|1|
S10SfSeS17S31S56A1M0A1S3aA3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC1a : ltac2:(tb__ "0|1|
S10SfSeS17S31S4eA1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC2a : ltac2:(tb__ "0|1|
S10SfSeS17S31S58A1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC3a : ltac2:(tb__ "0|1|
S10SfSeS17S31S5aA1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC4a : ltac2:(tb__ "0|1|
S10SfSeS17S31S5cA1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC5a : ltac2:(tb__ "0|1|
S10SfSeS17S31S45A1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxT5fa : ltac2:(tb__ "0|1|
S10SfSeS17S31S78A1M0A1Pf0A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC6a : ltac2:(tb__ "0|1|
S10SfSeS17S31S5eA1M0A1Pf2A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma E0a_def : ltac2:(tb__ "0|0|
SfS32S39U0S82A2S69A3"). Proof. unfold E0a. reflexivity. Qed.
Lemma E1aa_def : ltac2:(tb__ "0|0|
SfS32S39U0S67A2S60A3"). Proof. unfold E1aa. reflexivity. Qed.
Lemma E1ba_def : ltac2:(tb__ "0|0|
SfS32S39U1S67A2S50A3"). Proof. unfold E1ba. reflexivity. Qed.
Lemma E2a_def : ltac2:(tb__ "0|0|
SfS32S39U0S84A2S6bA3"). Proof. unfold E2a. reflexivity. Qed.
Lemma E3a_def : ltac2:(tb__ "0|0|
SfS32S39U0S86A2S6dA3"). Proof. unfold E3a. reflexivity. Qed.
Lemma E4a_def : ltac2:(tb__ "0|0|
SfS32S39U0S88A2S6fA3"). Proof. unfold E4a. reflexivity. Qed.
Lemma E5a_def : ltac2:(tb__ "0|0|
SfS32S39U0S8aA2S71A3"). Proof. unfold E5a. reflexivity. Qed.
Lemma E6a_def : ltac2:(tb__ "0|0|
SfS32S39U0S8cA2S73A3"). Proof. unfold E6a. reflexivity. Qed.
Lemma E7a_def : ltac2:(tb__ "0|0|
SfS32S39U0S8eA2S96A3"). Proof. unfold E7a. reflexivity. Qed.

Definition run0b : list leafA := ltac2:(tb__ "0|0|
S37U12cS0SdS4aS0SdZ3e63cS2SdA1A3A3S52S4A1A3").
Definition E0b : axst := leaf 0 run0b.
Definition C0b : axst := ltac2:(tb__ "0|1|
S41S6aS4aS0S6S3S11A2M0S5S3S11UcS40A4S0G0S5S3S11UdS40A4S2G0A1A3A3A3").
Definition run1b : list leafA := ltac2:(tb__ "0|0|
S37U12cS0SdS44S0SdZ3e63cS0SdZ3e810S0SdZ3e804S2SdA1A3A3A3A3S57A3").
Definition E1ab : axst := leaf 0 run1b.
Definition E1bb : axst := leaf 1 run1b.
Definition E1ab' : axst := ltac2:(tb__ "0|1|
S41S61S44S0S6S3S11A2M0S5S3S11UfS42A4S2G0A1A3A3").
Definition E1bb' : axst := ltac2:(tb__ "0|1|
S41S51S44S0S6S3S11A2M0S5S3S11UfS42A4S2G0A1A3A3").
Definition C1b : axst := ltac2:(tb__ "0|1|
Sa8S51S44S0S6S3S11A2M0S5S3S11UfS42A4S0G0S5S3S11U10S16Pb9A1A4S0G0S5S3S11U11S16PbaA1A4S2G0A1A3A3A3S9S13S62S66S4A1A3S43A5").
Definition run2b : list leafA := ltac2:(tb__ "0|0|
S37U12cS0SdS4bS2SdA1A3S4fA3").
Definition E2b : axst := leaf 0 run2b.
Definition C2b : axst := ltac2:(tb__ "0|1|
S41S6cS4bS0S6S3S11A2M0S5S3S11U12S53S4A1A4S2G0A1A3A3").
Definition run3b : list leafA := ltac2:(tb__ "0|0|
S37U258S0SdS4cS0SdZ3e818S0SdZ3e83cS0SdZ3e73cS2SdA1A3A3A3A3S59A3").
Definition E3b : axst := leaf 0 run3b.
Definition C3b : axst := ltac2:(tb__ "0|1|
S41S6eS4cS0S6S3S11A2M0S5S3S11UdS12Z3A1A4S0G0S5S3S11UeS12ZffA1A4S2G0A1A3A3A3").
Definition run4b : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdS48S0SdZ3e818S2SdA1A3A3S5bA3").
Definition E4b : axst := leaf 0 run4b.
Definition C4b : axst := ltac2:(tb__ "0|1|
S41S70S48S0S6S3S11A2M0S5S3S11UbS4dA4S2G0A1A3A3").
Definition run5b : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdS47S0SdZ3e73cS0SdZ5fa44S0SdZ5fa24S0SdZ5fa64S0SdZ5fa84S0SdZ5fa04S2SdA1A3A3A3A3A3A3A3S5dA3").
Definition E5b : axst := leaf 0 run5b.
Definition C5b : axst := ltac2:(tb__ "0|1|
S41S72S47S0S6S3S11A2M0S5S3S11UcS63A4S2G0A1A3A3").
Definition s5b : wsub := ltac2:(tb__ "0|0|
Se2P1S31S46A1S31Sc6A1A3").
Definition R5b : list sobj := ltac2:(tb__ "0|0|
Sa6SdaS46Sc6S55A3A1").
Definition T5b : axst := ltac2:(tb__ "0|0|
SdbS55Sc6Sd6SddSc7A1A1S46S65A5").
Definition T5fb : axst := ltac2:(tb__ "0|0|
Se3S77S1bS31S46A1A1A2").
Definition run6b : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdS49S0SdZ3e7b8S0SdZ3e7d8S2SdA1A3A3A3S79A3").
Definition E6b : axst := leaf 0 run6b.
Definition C6b : axst := ltac2:(tb__ "0|1|
S41S74S49S0S6S3S11A2M0S5S3S11UcS40A4S2G0A1A3A3").
Definition run7b : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdZ3eb64S0SdZ3eabcS0SdZ3ea78S0SdZ3ea98S2SdA1A3A3A3A3S5fA3").
Definition E7b : axst := leaf 0 run7b.

Lemma run0b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U12cS0SdS4aS0SdZ3e63cS2SdA1A3A3S52S4A1A3S83A3"). Proof. unfold run0b. reflexivity. Qed.
Lemma chk0b : ltac2:(tb__ "0|0|
SfS1Sc2S83S4aA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd0b : ltac2:(tb__ "0|0|
SfS1Sc1S6aS57S7aA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run1b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U12cS0SdS44S0SdZ3e63cS0SdZ3e810S0SdZ3e804S2SdA1A3A3A3A3S57A3S68A3"). Proof. unfold run1b. reflexivity. Qed.
Lemma chk1b : ltac2:(tb__ "0|0|
SfS1Sc5S68S44A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd1ab : ltac2:(tb__ "0|0|
SfS1Sc1S61S93S7bA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd1bb : ltac2:(tb__ "0|0|
SfS1Sc1S51S95S7cA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent1ab : ltac2:(tb__ "0|0|
SfS1Sc4S93S4fA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent1bb : ltac2:(tb__ "0|0|
SfS1Sc4S95S4fA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma br1ab : ltac2:(tb__ "0|0|
SfS1SdeS13S25S1cScdS40S12Z11A1A3A1S1bS31S61A1A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma br1bb : ltac2:(tb__ "0|0|
SfS1SdeS13S25S22S1cScdS40S12Z11A1A3A1A1S1bS31S51A1A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run2b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U12cS0SdS4bS2SdA1A3S4fA3S85A3"). Proof. unfold run2b. reflexivity. Qed.
Lemma chk2b : ltac2:(tb__ "0|0|
SfS1Sc2S85S4bA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd2b : ltac2:(tb__ "0|0|
SfS1Sc1S6cS59S7dS4A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run3b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U258S0SdS4cS0SdZ3e818S0SdZ3e83cS0SdZ3e73cS2SdA1A3A3A3A3S59A3S87A3"). Proof. unfold run3b. reflexivity. Qed.
Lemma chk3b : ltac2:(tb__ "0|0|
SfS1Sc2S87S4cA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd3b : ltac2:(tb__ "0|0|
SfS1Sc1S6eS5bS7eA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run4b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdS48S0SdZ3e818S2SdA1A3A3S5bA3S89A3"). Proof. unfold run4b. reflexivity. Qed.
Lemma chk4b : ltac2:(tb__ "0|0|
SfS1Sc2S89S48A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd4b : ltac2:(tb__ "0|0|
SfS1Sc1S70S5dS7fA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run5b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdS47S0SdZ3e73cS0SdZ5fa44S0SdZ5fa24S0SdZ5fa64S0SdZ5fa84S0SdZ5fa04S2SdA1A3A3A3A3A3A3A3S5dA3S8bA3"). Proof. unfold run5b. reflexivity. Qed.
Lemma chk5b : ltac2:(tb__ "0|0|
SfS1Sc2S8bS47A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd5b : ltac2:(tb__ "0|0|
SfS1Sc1S72S46S80A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma He5b : ltac2:(tb__ "0|1|
SfScS8S14A1M0A1SdaS46Sc6S55A3SbG0S65A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk5b : ltac2:(tb__ "0|0|
SfS1SdcS46Sc6S55S65Se1S33S32S35Sc8A4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT5b : ltac2:(tb__ "0|0|
SfS32SdbS55Sc6Sd6SddSc7A1A1S46S65A5S77A3"). Proof. unfold T5b. reflexivity. Qed.
Lemma FBC5b : ltac2:(tb__ "0|1|
SfS1SdfS13S24S17S31S46A1M0A1A1S1bG0A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT5b : ltac2:(tb__ "0|0|
SfS1SdfS13S24S17S31S77A1A1A1S1bS31S46A1A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run6b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdS49S0SdZ3e7b8S0SdZ3e7d8S2SdA1A3A3A3S79A3S8dA3"). Proof. unfold run6b. reflexivity. Qed.
Lemma chk6b : ltac2:(tb__ "0|0|
SfS1Sc2S8dS49A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd6b : ltac2:(tb__ "0|0|
SfS1Sc1S74S5fS81S4A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run7b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdZ3eb64S0SdZ3eabcS0SdZ3ea78S0SdZ3ea98S2SdA1A3A3A3A3S5fA3S8fA3"). Proof. unfold run7b. reflexivity. Qed.
Lemma chk7b : ltac2:(tb__ "0|0|
SfS1Sc2S8fS75A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent7b : ltac2:(tb__ "0|0|
SfS1Sc4S97S9fS4A1A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nxC0b : ltac2:(tb__ "0|1|
S10SfSeS17S31S57A1M0A1S3aA3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC1b : ltac2:(tb__ "0|1|
S10SfSeS17S31S4fA1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC2b : ltac2:(tb__ "0|1|
S10SfSeS17S31S59A1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC3b : ltac2:(tb__ "0|1|
S10SfSeS17S31S5bA1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC4b : ltac2:(tb__ "0|1|
S10SfSeS17S31S5dA1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC5b : ltac2:(tb__ "0|1|
S10SfSeS17S31S46A1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxT5fb : ltac2:(tb__ "0|1|
S10SfSeS17S31S79A1M0A1Pf0A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC6b : ltac2:(tb__ "0|1|
S10SfSeS17S31S5fA1M0A1Pf2A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma E0b_def : ltac2:(tb__ "0|0|
SfS32S39U0S83A2S6aA3"). Proof. unfold E0b. reflexivity. Qed.
Lemma E1ab_def : ltac2:(tb__ "0|0|
SfS32S39U0S68A2S61A3"). Proof. unfold E1ab. reflexivity. Qed.
Lemma E1bb_def : ltac2:(tb__ "0|0|
SfS32S39U1S68A2S51A3"). Proof. unfold E1bb. reflexivity. Qed.
Lemma E2b_def : ltac2:(tb__ "0|0|
SfS32S39U0S85A2S6cA3"). Proof. unfold E2b. reflexivity. Qed.
Lemma E3b_def : ltac2:(tb__ "0|0|
SfS32S39U0S87A2S6eA3"). Proof. unfold E3b. reflexivity. Qed.
Lemma E4b_def : ltac2:(tb__ "0|0|
SfS32S39U0S89A2S70A3"). Proof. unfold E4b. reflexivity. Qed.
Lemma E5b_def : ltac2:(tb__ "0|0|
SfS32S39U0S8bA2S72A3"). Proof. unfold E5b. reflexivity. Qed.
Lemma E6b_def : ltac2:(tb__ "0|0|
SfS32S39U0S8dA2S74A3"). Proof. unfold E6b. reflexivity. Qed.
Lemma E7b_def : ltac2:(tb__ "0|0|
SfS32S39U0S8fA2S97A3"). Proof. unfold E7b. reflexivity. Qed.
End SegQI_states.

(* [comment removed for export] *)
Module InvReveal.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_depot"; "ageom"; "qbatch"; "DG"; "class_state"; "dFB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "image_byte"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal"; "bext"; "cellZ_e"; "cell_ok_e"; "filled_e"; "present_e"; "@Corelib.Init.Datatypes"; "list"; "app"; "option"; "None"; "nat"; "Some"; "bool"; "prod"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "view"; "present"; "cell_ok"; "filled"; "acell"; "cells_ok"; "maskv"; "restrictv"; "rtc_inv"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "band_page"; "AInvA"; "alloc_magic_ok"; "bandtp_inv"; "batch_repr"; "class_repr"; "depot_wf"; "fs_inv"; "ia_inv"; "inv3"; "live_block_repr"; "misc_inv"; "present_but"; "primary_repr"; "q_item_ok"; "qhdr_repr"; "qlinks"; "quarantine_repr"; "rest_inv"; "secondary_repr"; "shadow_unpoisoned"; "thread_inv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD"; "AInvX"; "rest_inv_nd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "prim_credit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "cellZ"; "depot_mem"; "depot_vm"; "FBPAGES"; "fpage"; "@Corelib.Init.Peano"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition bext (m m' : bview) : Prop := ltac2:(tb__ "0|2|
S0SfQ8A1M0SbS18G0A1M1Vm;R2A1S1bG0R1A2A3SbG1Vm';R3A1S1bG0R2A2A3F_;Fb;Fz;").

Lemma bext_refl : ltac2:(tb__ "0|0|
S1fS11R1R1A2Fm;").
Proof. intros m z b H. exact H. Qed.
Lemma bext_trans : ltac2:(tb__ "0|1|
S1fS1fS1fS11R3R2A2M0G0S11R5R3A2F_;F_;Fm3;Fm2;Fm1;").
Proof. intros m1 m2 m3 H1 H2 z b H. exact (H2 z b (H1 z b H)). Qed.
Lemma bext_restrictv : ltac2:(tb__ "0|0|
S0S1cF_;S1fS1fS11R2R1A2S11S27R4R3A2S27R4R2A2A2F_;Fm';Fm;FP;").
Proof. intros P m m' H z b. unfold restrictv. destruct (P z); [apply H | intros X; exact X]. Qed.
Lemma bext_maskv : ltac2:(tb__ "0|0|
S0S1cF_;S1fS1fS11R2R1A2S11S26R4R3A2S26R4R2A2A2F_;Fm';Fm;FP;").
Proof. intros P m m' H z b. unfold maskv. destruct (P z); [intros X; exact X | apply H]. Qed.
Lemma bext_def : ltac2:(tb__ "0|3|
S1fS1fS0S11R3R2A2SdSbS18SfQ8A1M0A1M1R4R2A1S19G0A1M2A3A1SdSbG1R4R3A1G2A3A1F_;F_;Fz;Fm';Fm;").
Proof. intros m m' z H Hz. destruct (m z) as [b|] eqn:E; [|exact (fun X => Hz eq_refl)]. rewrite (H z b E). discriminate. Qed.

Section Atoms.
Variables (m m' : bview).
Hypothesis EXT : bext m m'.
Lemma cell_ok_e : ltac2:(tb__ "0|0|
S24S22Vm;R1A2S22Vm';R2A2F_;Fc;").
Proof. intros c H k Hk. exact (EXT _ _ (H k Hk)). Qed.
Lemma cells_ok_e : ltac2:(tb__ "0|0|
S16S24A1S25Vm;R1A2S25Vm';R2A2F_;Fcs;").
Proof. intros cs H. unfold cells_ok in *. apply Forall_forall. intros c Hc. apply cell_ok_e. exact (proj1 (Forall_forall _ _) H c Hc). Qed.
Lemma cellZ_e : ltac2:(tb__ "0|0|
S0S1aS0S4bVm;R3R2R1A4S4bVm';R4R3R2A4F_;Fv;Fw;Fa;").
Proof. intros a w v H. unfold cellZ in *. apply cell_ok_e. exact H. Qed.
Lemma present_e : ltac2:(tb__ "0|0|
S0S0S21Vm;R2R1A3S21Vm';R3R2A3F_;Fhi;Flo;").
Proof. intros lo hi H z Hz. destruct (H z Hz) as [b Hb]. exists b. exact (EXT _ _ Hb). Qed.
Lemma filled_e : ltac2:(tb__ "0|0|
S0S0S0S23Vm;R3R2R1A4S23Vm';R4R3R2A4F_;Fv;Fhi;Flo;").
Proof. intros lo hi v H z Hz. exact (EXT _ _ (H z Hz)). Qed.
End Atoms.

Section Components.
Variables (m m' : bview).
Hypothesis EXT : bext m m'.
Let CE : ltac2:(tb__ "0|0|
S24S22Vm;R1A2S22Vm';R2A2F_;Fc;") := ltac2:(tb__ "0|0|
S13Vm;Vm';VEXT;A3"). Let CZ : ltac2:(tb__ "0|0|
S0S1aS0S4bVm;R3R2R1A4S4bVm';R4R3R2A4F_;Fv;Fw;Fa;") := ltac2:(tb__ "0|0|
S12Vm;Vm';VEXT;A3"). Let PE : ltac2:(tb__ "0|0|
S0S0S21Vm;R2R1A3S21Vm';R3R2A3F_;Fhi;Flo;") := ltac2:(tb__ "0|0|
S15Vm;Vm';VEXT;A3"). Let FE : ltac2:(tb__ "0|0|
S0S0S0S23Vm;R3R2R1A4S23Vm';R4R3R2A4F_;Fv;Fhi;Flo;") := ltac2:(tb__ "0|0|
S14Vm;Vm';VEXT;A3").

Lemma shadow_unpoisoned_e : ltac2:(tb__ "0|0|
S0S0S40Vm;R2R1A3S40Vm';R3R2A3F_;Fn;Fb;").
Proof. intros b n [H1 H2]. split; [intros g Hg; exact (EXT _ _ (H1 g Hg)) | intros Hn; exact (EXT _ _ (H2 Hn))]. Qed.

Lemma alloc_magic_ok_e : ltac2:(tb__ "0|0|
S0S0S2eVm;R2R1A3S2eVm';R3R2A3F_;Fn;Fb;").
Proof. intros b n [H|[H1 H2]]; [left; exact H | right; split; apply CE; assumption]. Qed.

Lemma present_but_e : ltac2:(tb__ "0|0|
S0S0S16S1dS0S0A2A1S38Vm;R3R2R1A4S38Vm';R4R3R2A4F_;FL;Fhi;Flo;").
Proof. intros lo hi L H z Hz Hn. destruct (H z Hz Hn) as [b Hb]. exists b. exact (EXT _ _ Hb). Qed.

Ltac bleaf :=
  first [ intros H; exact H
        | intros H; exact (EXT _ _ H)
        | intros H; exact (cell_ok_e m m' EXT _ H)
        | intros H; exact (cellZ_e m m' EXT _ _ _ H)
        | intros H; exact (present_e m m' EXT _ _ H)
        | intros H; exact (present_but_e _ _ _ H)
        | intros H; exact (filled_e m m' EXT _ _ _ H)
        | intros H; exact (cells_ok_e m m' EXT _ H)
        | intros H; exact (shadow_unpoisoned_e _ _ H)
        | intros H; exact (alloc_magic_ok_e _ _ H) ].
Ltac bmono :=
  lazymatch goal with
  | |- (_ /\ _) -> (_ /\ _) => let HA := fresh "HA" in let HB := fresh "HB" in intros [HA HB]; split; [revert HA; bmono | revert HB; bmono]
  | |- (exists x, _) -> (exists y, _) => let x := fresh "x" in let Hx := fresh "Hx" in intros [x Hx]; exists x; revert Hx; bmono
  | |- (_ \/ _) -> (_ \/ _) => let H := fresh "HH" in intros [H|H]; [left | right]; revert H; bmono
  | |- (forall a, _) -> (forall b, _) => let H := fresh "HH" in let a := fresh "a" in intros H a; specialize (H a); revert H; bmono
  | |- _ => bleaf
  end.

Lemma rtc_inv_e : ltac2:(tb__ "0|0|
S3S28Vm;R1A2S28Vm';R2A2F_;FG;").
Proof. intros G H. unfold rtc_inv in *. exact (cells_ok_e m m' EXT _ H). Qed.

Lemma thread_inv_e : ltac2:(tb__ "0|0|
S3S41Vm;R1A2S41Vm';R2A2F_;FG;").
Proof. intros G. unfold thread_inv. bmono. Qed.

Lemma misc_inv_e : ltac2:(tb__ "0|0|
S37Vm;A1S37Vm';A1F_;").
Proof. unfold misc_inv. bmono. Qed.

Lemma ia_inv_e : ltac2:(tb__ "0|0|
S1S34Vm;R1A2S34Vm';R2A2F_;FA;").
Proof. intros A. unfold ia_inv. destruct (aa_internal_inited A); bmono. Qed.

Lemma live_block_repr_e : ltac2:(tb__ "0|0|
S1S36Vm;R1A2S36Vm';R2A2F_;FA;").
Proof. intros A. unfold live_block_repr. bmono. Qed.

Lemma class_repr_e : ltac2:(tb__ "0|0|
S3S1S0S6S31Vm;R4R3R2R1A5S31Vm';R5R4R3R2A5F_;Fcs;Fc;FA;FG;").
Proof. intros G A c cs. unfold class_repr. bmono. Qed.

Lemma primary_repr_e : ltac2:(tb__ "0|0|
S1S39Vm;R1A2S39Vm';R2A2F_;FA;").
Proof. intros A (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. intros c Hc. apply class_repr_e. exact (H4 c Hc). Qed.

Lemma secondary_repr_e : ltac2:(tb__ "0|0|
S1S3fVm;R1A2S3fVm';R2A2F_;FA;").
Proof. intros A. unfold secondary_repr. bmono. Qed.

Lemma q_item_ok_e : ltac2:(tb__ "0|0|
S1S1dS0S0A2S3aVm;R2R1A3S3aVm';R3R2A3F_;Fit;FA;").
Proof. intros A it. unfold q_item_ok. bmono. Qed.

Lemma batch_repr_e : ltac2:(tb__ "0|0|
S1S4S30Vm;R2R1A3S30Vm';R3R2A3F_;Fb;FA;").
Proof.
  intros A b H. unfold batch_repr in H |- *. destruct H as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  split; [exact B1|]. split; [exact (CE _ B2)|]. split; [exact (CE _ B3)|]. split; [exact B4|]. split; [exact B5|]. split; [exact (PE _ _ B6)|].
  split; [|exact B8]. intros i it Hi. destruct (B7 i it Hi) as [X1 X2]. split; [exact (CE _ X1) | exact (q_item_ok_e _ _ X2)].
Qed.

Lemma qlinks_e : ltac2:(tb__ "0|0|
S16S4A1S3cVm;R1A2S3cVm';R2A2F_;Fl;").
Proof. induction l as [|b r IH]; intros H; [exact I|]. destruct H as [H1 H2]. split; [exact (CE _ H1) | exact (IH H2)]. Qed.

Lemma qhdr_repr_e : ltac2:(tb__ "0|0|
S0S16S4A1S3bVm;R2R1A3S3bVm';R3R2A3F_;Fl;Fhdr;").
Proof. intros hdr l. unfold qhdr_repr. bmono. Qed.

Lemma quarantine_repr_e : ltac2:(tb__ "0|0|
S1S3dVm;R1A2S3dVm';R2A2F_;FA;").
Proof.
  intros A H. unfold quarantine_repr in H |- *. destruct H as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  split; [apply Forall_forall; intros b Hb; apply batch_repr_e; exact (proj1 (Forall_forall _ _) Q1 b Hb)|].
  split; [exact (qlinks_e _ Q2)|]. split; [exact (qlinks_e _ Q3)|]. split; [exact (qhdr_repr_e _ _ Q4)|]. split; [exact (qhdr_repr_e _ _ Q5)|].
  split; [exact (CE _ Q6)|]. split; [exact (CE _ Q7)|]. split; [exact Q8 | exact Q9].
Qed.

Lemma depot_mem_e : ltac2:(tb__ "0|0|
S5S4cR1Vm;A2S4cR2Vm';A2F_;FG;").
Proof.
  intros G H. destruct H as [HN HF Hmu Hal Htab Hl1 Hm1 Hnb Hlk Hfl Hfb Hfz Hfbs Hfp Hflo Hfh Hdj].
  constructor.
  - split; [exact (proj1 HN) | exact (CZ _ _ _ (proj2 HN))].
  - destruct HF as (F1 & F2 & F3 & F4). split; [exact F1|]. split; [exact F2|]. split; [exact F3 | exact (CZ _ _ _ F4)].
  - exact (CZ _ _ _ Hmu).
  - exact (PE _ _ Hal).
  - intros i Hi. destruct (Htab i Hi) as (w & Hw & Hr). exists w. split; [exact (CZ _ _ _ Hw) | exact Hr].
  - exact Hl1.
  - intros j Hj. exact (CZ _ _ _ (Hm1 j Hj)).
  - intros b Hb. destruct (Hnb b Hb) as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [exact A2|]. split; [exact A3 | exact (PE _ _ A4)].
  - intros s Hs. destruct (Hlk s Hs) as (h & l & Hh & Hl & Hr). exists h, l. split; [exact (CZ _ _ _ Hh)|]. split; [exact (CZ _ _ _ Hl) | exact Hr].
  - exact Hfl.
  - intros b Hb. destruct (Hfb b Hb) as (A1 & A2 & A3 & A4). split; [exact (CZ _ _ _ A1)|]. split; [exact A2|]. split; [exact (PE _ _ A3) | exact (CZ _ _ _ A4)].
  - intros b Hb. destruct (Hfz b Hb) as (A1 & A2 & A3). split; [exact (FE _ _ _ A1)|]. split; [exact (PE _ _ A2) | exact (FE _ _ _ A3)].
  - exact Hfbs.
  - intros b Hb. destruct (Hfp b Hb) as [A1 A2]. split; [exact A1 | exact (PE _ _ A2)].
  - exact Hflo.
  - exact Hfh.
  - exact Hdj.
Qed.

Lemma depot_wf_e : ltac2:(tb__ "0|0|
S1S32Vm;R1A2S32Vm';R2A2F_;FA;").
Proof. intros A H. unfold depot_wf in *. exact (depot_mem_e _ H). Qed.

Lemma rest_inv_e : ltac2:(tb__ "0|0|
S1S3eVm;R1A2S3eVm';R2A2F_;FA;").
Proof.
  intros A (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  split; [exact R1|]. split; [exact (live_block_repr_e _ R2)|]. split; [exact (primary_repr_e _ R3)|]. split; [exact (secondary_repr_e _ R4)|].
  split; [exact (quarantine_repr_e _ R5)|]. split; [exact (depot_wf_e _ R6)|]. split; [exact (ia_inv_e _ R7)|].
  split; [exact (thread_inv_e _ R8) | exact (misc_inv_e R9)].
Qed.

Lemma rest_inv_nd_e : ltac2:(tb__ "0|0|
S1S48Vm;R1A2S48Vm';R2A2F_;FA;").
Proof.
  intros A (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  split; [exact R1|]. split; [exact (live_block_repr_e _ R2)|]. split; [exact (primary_repr_e _ R3)|]. split; [exact (secondary_repr_e _ R4)|].
  split; [exact (quarantine_repr_e _ R5)|]. split; [exact I|]. split; [exact (ia_inv_e _ R7)|].
  split; [exact (thread_inv_e _ R8) | exact (misc_inv_e R9)].
Qed.

Lemma fs_inv_e : ltac2:(tb__ "0|0|
S1S33Vm;R1A2S33Vm';R2A2F_;FA;").
Proof. intros A. unfold fs_inv. bmono. Qed.

Lemma bandtp_inv_e : ltac2:(tb__ "0|0|
S16SfQ40A1A1S2fVm;R1A2S2fVm';R2A2F_;Ftp;").
Proof. intros tp H. eapply bandtp_mono; [|exact H]. intros z _ Hz. exact (bext_def m m' z EXT Hz). Qed.
End Components.

Section WithSegs.
Variable segs : list Segment.

Lemma fpage_not_band : ltac2:(tb__ "0|0|
S1S1aS0S35R3A1S50R3S1eS0S7S2R4A1A1A2A2ScS2aZ0R3A2S2bR3S4eA2A2SdS2cS4fS2R6A1R5R4A3A1A1F_;F_;F_;Fk;Fb;FA;").
Proof.
  intros A b k HI3 Hb Hk HB. destruct HI3 as (_ & _ & _ & _ & X5 & _).
  set (bb := nth b (dFB (aa_depot A)) 0).
  assert (Hin : In (bb, FBSZ) (dblocks (aa_depot A))).
  { unfold dblocks. apply in_or_app. right. apply in_map_iff. exists bb. split; [reflexivity|]. apply nth_In. exact Hb. }
  destruct (X5 _ Hin) as (DI & _). cbn [fst snd] in DI. destruct DI as (_ & _ & _ & _ & WB).
  pose proof (band_page_band _ HB) as R. unfold fpage in R. fold bb in R.
  unfold FBSZ, FBPAGES, PG, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
Qed.

Lemma depot_vm_grow_band : ltac2:(tb__ "0|3|
S1S42S16SfQ40M0A1M1A1M2G2S35R4A1S4dS2R5A1R4R3A3G1S44G1R1R4A3S2cS10G0R2A2A1F_;Fp;S4dS2R7A1R6S17G1R4R5A3A3F_;F_;F_;Ftp1;Ftp;Fmd;FA;").
Proof.
  intros A md tp tp1 HI3 [D1 D2 D3 D4 D5 D6] Hb. constructor; try assumption.
  intros b k Hbk Hk. rewrite in_app_iff. split.
  - intros [H|H]; [|exact (proj1 (D4 b k Hbk Hk) H)]. exfalso. apply (fpage_not_band A b k HI3 Hbk Hk).
    pose proof (Hb _ H) as X. rewrite u64_lit in X; [exact X|].
    destruct HI3 as (_ & _ & _ & _ & X5 & _).
    assert (Hin : In (nth b (dFB (aa_depot A)) 0, FBSZ) (dblocks (aa_depot A))).
    { unfold dblocks. apply in_or_app. right. apply in_map_iff. exists (nth b (dFB (aa_depot A)) 0). split; [reflexivity|]. apply nth_In. exact Hbk. }
    destruct (X5 _ Hin) as (DI & _). cbn [fst snd] in DI. destruct DI as (D0 & _ & DT & _). pose proof (topG_range (aa_geom A)).
    unfold fpage, FBSZ, FBPAGES, PG in *. lia.
  - intros H. right. exact (proj2 (D4 b k Hbk Hk) H).
Qed.

Theorem AInvA_ext : ltac2:(tb__ "0|4|
S1S9S9S16SfQ40M0A1M1A1M2G2S42S2dVsegs;R6R5R3R1A5S11S20Vsegs;S8R6A1A2S20Vsegs;S8R5A1A2A2G1S44G1R1R5A3ScS2cS10G0R2A2M3A1S21S20Vsegs;S8R8A1A2G3S29G3S46A2A3A2F_;Fp;S2aS29S45R4S17G1R5R6A3A2S4aR9A1A2S49R9A1A2S2dVsegs;RaR8S17G1R6R7A3R5A5F_;F_;F_;F_;Fmd;Ftp1;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp tp1 md (HG & HR & HF & HRest & HM & HI3 & HB) EXT Htp1 Hpaid.
  split; [exact HG|]. split; [exact (rtc_inv_e _ _ EXT _ HR)|].
  split; [exact (fs_inv_e _ _ (bext_restrictv _ _ _ EXT) _ HF)|].
  split; [exact (rest_inv_e _ _ (bext_maskv _ _ _ EXT) _ HRest)|].
  split.
  { unfold model_inv, ledger_inv in HM |- *.
    destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    refine (conj V1 (conj Hpaid (conj V3 (conj V4 (conj V5 (conj V6 (conj V7 (conj L1 (conj L2 (conj L3 (conj L4 (conj _ (conj L6 (conj L7 (conj L8 L9))))))))))))))).
    apply depot_vm_grow_band; [exact HI3 | exact L5 |]. intros p Hp. exact (proj1 (Htp1 p Hp)). }
  split; [exact HI3|].
  apply (bandtp_grow _ tp); [exact (bandtp_inv_e _ _ EXT _ HB)|].
  intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [|left; exact Hp]. right. intros _. exact (proj2 (Htp1 p Hp)).
Qed.

Theorem AInvX_ext : ltac2:(tb__ "0|4|
S1S9S9S16SfQ40M0A1M1A1M2G2S42S47R6R5R3R1A4S11S20S43S8R6A1A2S20S43S8R5A1A2A2G1S44G1R1R5A3ScS2cS10G0R2A2M3A1S21S20S43S8R8A1A2G3S29G3S46A2A3A2F_;Fp;S2aS29S45R4S17G1R5R6A3A2S4aR9A1A2S49R9A1A2S47RaR8S17G1R6R7A3R5A4F_;F_;F_;F_;Fmd;Ftp1;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp tp1 md (HG & HR & HF & HRest & HM & HI3 & HB) EXT Htp1 Hpaid.
  split; [exact HG|]. split; [exact (rtc_inv_e _ _ EXT _ HR)|].
  split; [exact (fs_inv_e _ _ (bext_restrictv _ _ _ EXT) _ HF)|].
  split; [exact (rest_inv_nd_e _ _ (bext_maskv _ _ _ EXT) _ HRest)|].
  split.
  { unfold model_inv_nd, ledger_inv_nd in HM |- *.
    destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    exact (conj V1 (conj Hpaid (conj V3 (conj V4 (conj V5 (conj V6 (conj V7 (conj L1 (conj L2 (conj L3 (conj L4 (conj I (conj I (conj L7 (conj L8 L9))))))))))))))). }
  split; [exact HI3|].
  apply (bandtp_grow _ tp); [exact (bandtp_inv_e _ _ EXT _ HB)|].
  intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [|left; exact Hp]. right. intros _. exact (proj2 (Htp1 p Hp)).
Qed.

Lemma view_bext : ltac2:(tb__ "0|4|
S9S9SfQ40A1SeSbS18SfQ8A1M0A1M1S8R2R1A2S8R3R1A2M2A3ScSbG1G2S19G0A1M3A3SbG1SaVsegs;R1A2G3A3A2A2Fa;S11S20Vsegs;S8R3A1A2S20Vsegs;S8R2A1A2A2F_;Frho';Frho;").
Proof.
  intros rho rho' H z b Hz.
  destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|]; [|rewrite view_out in Hz by lia; discriminate | rewrite view_out in Hz by lia; discriminate].
  rewrite view_in in Hz |- * by lia. unfold rd_of in Hz |- *.
  destruct (H (Z_to_bv 64 z)) as [E|[E1 E2]].
  - rewrite E. exact Hz.
  - rewrite E1, E2 in Hz. discriminate.
Qed.

Theorem AInvA_reveal : ltac2:(tb__ "0|8|
S1S9S9S16SfQ40M0A1M1A1M2G2S42S2dVsegs;R6R5R3R1A5G1SeSbS18SfQ8A1M3A1M4S8R6R1A2S8R7R1A2M5A3ScSbG4G5S19G3A1M6A3SbG4SaVsegs;R1A2G6A3A2A2Fa;G1S44G1R1R5A3ScS2cS10G0R2A2M7A1S21S20Vsegs;S8R8A1A2G7S29G7S46A2A3A2F_;Fp;S2aS29S45R4S17G1R5R6A3A2S4aR9A1A2S49R9A1A2S2dVsegs;RaR8S17G1R6R7A3R5A5F_;F_;F_;F_;Fmd;Ftp1;Ftp;Frho';Frho;FA;").
Proof. intros A rho rho' tp tp1 md HA H Htp1 Hpaid. exact (AInvA_ext A rho rho' tp tp1 md HA (view_bext rho rho' H) Htp1 Hpaid). Qed.

End WithSegs.

Theorem AInvX_reveal : ltac2:(tb__ "0|8|
S1S9S9S16SfQ40M0A1M1A1M2G2S42S47R6R5R3R1A4G1SeSbS18SfQ8A1M3A1M4S8R6R1A2S8R7R1A2M5A3ScSbG4G5S19G3A1M6A3SbG4SaS43R1A2G6A3A2A2Fa;G1S44G1R1R5A3ScS2cS10G0R2A2M7A1S21S20S43S8R8A1A2G7S29G7S46A2A3A2F_;Fp;S2aS29S45R4S17G1R5R6A3A2S4aR9A1A2S49R9A1A2S47RaR8S17G1R6R7A3R5A4F_;F_;F_;F_;Fmd;Ftp1;Ftp;Frho';Frho;FA;").
Proof. intros A rho rho' tp tp1 md HA H Htp1 Hpaid. exact (AInvX_ext A rho rho' tp tp1 md HA (view_bext segsA rho rho' H) Htp1 Hpaid). Qed.
End InvReveal.

(* [comment removed for export] *)
Module InvKf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cache_inited"; "aa_cls"; "aa_fs_busy"; "aa_fs_hint"; "aa_geom"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "mkAA"; "DG"; "aa_depot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvKf"; "bumpKf"; "@Corelib.Init.Datatypes"; "list"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD"; "AInvX"; "with_depot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition bumpKf (A : AA) : AA := ltac2:(tb__ "0|0|
SfS8VA;A1S5VA;A1S4VA;A1SeVA;A1SbVA;A1SaVA;A1SdVA;A1ScVA;A1S11VA;A1S7VA;A1S6VA;A1S9VA;A1S3VA;A1S2VA;A1S1aS1VA;A1Z1A2Af").

Lemma AInvX_bumpKf : ltac2:(tb__ "0|0|
S0S15S13S1bQ40A1A1S14S17R4R3R2R1A4S17S12R5A1R4R3R2A4F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB).
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [|exact (conj HI3 HB)].
  unfold model_inv_nd, ledger_inv_nd, gap_ok, gapN_ok, gapS_ok, blocks_left, budget_boundD in HM |- *.
  rewrite (PrimCredit.prim_credit_same A (bumpKf A) eq_refl).
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec bumpKf] in HM |- *.
  destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & _ & L6 & L7 & L8 & L9).
  split; [exact V1|]. split; [unfold BETA1 in *; set (pc := PrimCredit.prim_credit A) in *; clearbody pc; clear -V2 V6; lia|]. split; [exact V3|]. split; [exact V4|]. split; [exact V5|].
  split; [clear -V6; lia|]. split; [exact V7|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact I|].
  split; [exact I|]. split; [exact L7|].
  split; [exact L8|exact L9].
Qed.

Theorem AInvA_bumpKf : ltac2:(tb__ "0|0|
S0S15S13S1bQ40A1A1S14S16S19R4R3R2R1A5S16S19S12R5A1R4R3R2A5F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA. destruct (AInvA_X A rho tp md HA) as (HX & HD & L6).
  apply X_AInvA; [exact (AInvX_bumpKf A rho tp md HX) | exact HD | cbn [aa_depot aa_Km aa_Kf bumpKf]; lia].
Qed.

Lemma bumpKf_with_depot : ltac2:(tb__ "0|0|
S0S10S1cS0S12S18R2R1A2A1SfS8R2A1S5R2A1S4R2A1SeR2A1SbR2A1SaR2A1SdR2A1ScR2A1R1S7R2A1S6R2A1S9R2A1S3R2A1S2R2A1S1aS1R2A1Z1A2AfA3FG;FA;").
Proof. reflexivity. Qed.
End InvKf.

(* [comment removed for export] *)
Module DepotK.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "@Corelib.Init.Datatypes"; "list"; "app"; "length"; "prod"; "pair"; "bool"; "true"; "cons"; "nat"; "option"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "mul"; "ge"; "modulo"; "pow"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "event"; "vm_maps"; "vm_reserved"; "vm_noaccess"; "alloc_top"; "vm_limit"; "region_free"; "vm_init_sp"; "with_vmmaps"; "VmMaps"; "page_in_ranges"; "vm_add_lazy"; "m_vm_lazy"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK.DepotK"; "KD"; "AK"; "hcD"; "TOPr"; "dfp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "DG"; "dFB"; "dNB"; "aa_geom"; "aa_depot"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_ptr_committed"; "aa_sec"; "dFP"; "sec_chunk"; "aa_cls"; "aa_live"; "dN"; "topG"; "AA"; "ag_top"; "ageom"; "class_state"; "depot_state"; "sc_map_beg"; "sc_map_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rl"; "rm"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "NBSZ"; "FBSZ"; "dep_cost"; "dblocks"; "sumZ"; "DNMAX"; "DFPw"; "FBPAGES"; "G_fblk"; "G_ins"; "G_nblk"; "G_page"; "depot_inv"; "droom"; "dtrans"; "fpage"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD"; "AInvX"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "PG"; "dyn_in"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "band_page"; "in_maps"; "secondary_repr"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "prim_credit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "U0"; "acost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "BETA1"; "Q1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_laws2"; "KD_laws2"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA SummaryA LedgerA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts Placement.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_laws2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_laws2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section DepotK.
Let segs : list Segment := segsA.
Variables (A0 : AA) (Kc : KcA) (rhoE : valuation) (nreq : Z).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HB : budget_ok_alloc A0 nreq.
Hypothesis Hn : 0 <= nreq.
Hypothesis HKm0 : 0 <= aa_Km A0.

Definition AK (G : DG) : AA := bumpK (with_depot A0 G).

Definition TOPr (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S3S12S41S35VA0;A1A1M0S11S29Q40M1S4aVrho;PaA2A2S2cG1S4aVrho;S75A2A2A2A2S12G0S29G1S4aVrho;PcA2A2A2A2").

Definition dfp_ok (G : DG) : Prop := ltac2:(tb__ "0|3|
S3S2SfS9S0S3cVG;A1M0A2S9S0S33VG;A1A2M1A3SfS6aR1G1A2S12Z0M2S62S0R2G0G2A4A2F_;Fb;A2").
Definition KD (G : DG) : jpredA := ltac2:(tb__ "0|0|
S49S7S2aQ40A1A1S7S1cA1S1bS3S60S2eVG;A1VrhoE;R3R1A4S3VKc;R2R1A2S3S31VG;A1S30R4A1A2A2A2Lmd;Ltr;Ltp;Lrho;").

Definition hcD : Z := ltac2:(tb__ "0|0|
S19S72S11S11S11S11S73S74S39VA0;A1A1A2S15S76S11S11S38VA0;A1Z1A2S37VA0;A1A2A2A2S77A2S3aVA0;A1A2A2").

Lemma AK_proj : ltac2:(tb__ "0|1|
S32S3S2S44S35S2eR1A1M0A1S35VA0;A1A3S3S2S7S45A1S3eG0A1S3eVA0;A1A3S3S2S7S3dA1S3bG0A1S3bVA0;A1A3S3S2S7SaS0S0A2A1S3fG0A1S3fVA0;A1A3S3S2S46S36G0A1R1A3S3S2S0S39G0A1S39VA0;A1A3S3S2S0S38G0A1S11S38VA0;A1Z1A2A3S3S2S0S37G0A1S37VA0;A1A3S2S0S3aG0A1S3aVA0;A1A3A2A2A2A2A2A2A2A2FG;").
Proof. intros G. repeat split; reflexivity. Qed.

Lemma AK_credit : ltac2:(tb__ "0|0|
S32S2S0S6bS2eR1A1A1S6bVA0;A1A3FG;").
Proof. intros G. apply PrimCredit.prim_credit_same. reflexivity. Qed.

Lemma KD_room : ltac2:(tb__ "0|0|
S32S49S7S2aQ40A1A1S7S1cA1S1bS2dR5R4R3R2R1A5S16S11S4fR2R4A2S52R6A1A2S2fA2F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof.
  intros G rho tp tr md ((_ & _ & _ & _ & HM & _) & _).
  destruct HM as (_ & V2 & V3 & _). unfold headroom, hcD. rewrite V3.
  rewrite AK_credit in V2. pose proof (PrimCredit.prim_credit_nonneg A0) as PCN.
  unfold budget_boundD in V2. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed AK bumpK with_depot] in V2. lia.
Qed.

Lemma KD_reserved : ltac2:(tb__ "0|1|
S32S49S7S2aQ40A1M0A1S7S1cA1S1bS2dR5R4R3R2R1A5S2S7SaG0G0A2A1S1eS1aR2A1A1S6fVsegs;A1A3F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof. intros G rho tp tr md ((_ & _ & _ & _ & HM & _) & _). destruct HM as (_ & _ & _ & _ & _ & _ & _ & L1 & _). exact L1. Qed.

Lemma KD_noacc : ltac2:(tb__ "0|5|
S32S49S7S2aQ40M0A1M1A1S7S1cA1S1bG1G1S0S2dR8R7R6R5R4A5S4dSaG1G1A2M2SbG1G1R4R3A4S1fS1aR5A1A1A3S3S12S29G0R5A2M3R3A2S13R3S11G3S29G0R4A2A2A2A2S5G1G1S5G1G1S3S4dG2SbG1G1R2R1A4S1dS1aR9A1A1A3S3S12S29G0R2A2M4R6A2S13R6S11G4S29G0R1A2A2A2A2A2Lm;A2Lb;A2F_;F_;F_;Fx;Fn;Fa;Fmd;Ftr;Ftp;Frho;FG;").
Proof.
  intros G rho tp tr md a n x ((_ & _ & _ & _ & HM & _) & _) Hin Hx. destruct HM as ((V1 & _) & _).
  destruct (V1 (a, n) x Hin Hx) as ([b m] & Hbm & Hr). exists b, m. exact (conj Hbm Hr).
Qed.

Lemma KD_top : ltac2:(tb__ "0|0|
S32S49S7S2aQ40A1A1S7S1cA1S1bS2dR5R4R3R2R1A5S2S0S20S1aR2A1A1S43S35VA0;A1A1A3F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof. intros G rho tp tr md ((_ & _ & _ & _ & HM & _) & _). destruct HM as (_ & _ & _ & _ & _ & _ & V7 & _). exact V7. Qed.

Lemma KD_Kc : ltac2:(tb__ "0|0|
S32S49S7S2aQ40A1A1S7S1cA1S1bS2dR5R4R3R2R1A5VKc;R3R2A2F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof. intros G rho tp tr md (_ & HK & _). exact HK. Qed.

Lemma KD_view : ltac2:(tb__ "0|2|
S32S49S49S7S2aQ40A1M0A1S7S1cA1S1bS1S2G0S4aR5R1A2S4aR6R1A2A3Fi;S1S2S7S2aQ8A1M1A1S4bR6R1A2S4bR7R1A2A3Fl;S0S6S56R9R1A2A1S2S10G1A1S6cVsegs;S4cR8A1R2A3S6cVsegs;S4cR9A1R2A3A3F_;Fz;S2dR9R8R6R5R4A5S2dRaR8R7R6R5A5F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FG;").
Proof. intros G rho rho' tp tr md Hw _ _ (HX & HK & HL & HT). unfold KD, TOPr in *. rewrite !Hw. exact (conj HX (conj HK (conj HL HT))). Qed.

Lemma KD_stable : ltac2:(tb__ "0|0|
S1S6eP10R1A2S32S71Vsegs;R3S2dR1A1A3FG;F_;Fn;").
Proof.
  intros n Hn16 G rho rho' tp tr md md' Hag Hme (HX & HK & HL & HT). split; [exact (AInvX_mat (AK G) rhoE tp md md' HX Hme)|].
  split; [|split; [exact HL | destruct Hag as (Hw & _ & _); unfold TOPr, V_DEPTH in *; rewrite <- (Hw 10%positive), <- (Hw 15%positive), <- (Hw 12%positive) by lia; exact HT]].
  destruct Hme as ((mat' & ->) & _). rewrite with_vm_backing_with_vm. apply HKc. exact HK.
Qed.

Lemma AInvX_depot_cost : ltac2:(tb__ "0|5|
S32S32S7S2aQ40M0A1M1A1M2G2S1bS2S7S0A1M3S34R4A1S34R5A1A3S2G3S33R5A1S33R6A1A3S12S11S4eR3R4A2S52R7A1A2S11S4eR3R5A2S52R6A1A2A2G1S4dG1R1R6A3S4S4dG1R2R8A3S6S67S29G0R2A2A1A1A2F_;Fq;S60S2eR9A1M4VrhoE;R7R5A4S60G4VrhoE;R7R6A4F_;F_;F_;F_;F_;Fmd;Ftp';Ftp;FG';FG;").
Proof.
  intros G G' tp tp' md EN EF HP HTP (HG & HR & HF & HRest & HM & HI3 & HBT).
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [|split].
  - unfold model_inv_nd, ledger_inv_nd, gap_ok, gapN_ok, gapS_ok, blocks_left, budget_boundD in HM |- *.
    rewrite !AK_credit in HM |- *.
    cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec AK bumpK with_depot] in HM |- *. rewrite EN, EF.
    destruct HM as (V1 & V2 & VR). split; [exact V1|]. split; [clear -V2 HP; lia | exact VR].
  - unfold inv3 in HI3 |- *. cbn [aa_geom aa_sec aa_live aa_depot aa_q_thread aa_q_global aa_cls AK bumpK with_depot] in HI3 |- *.
    unfold dblocks in HI3 |- *. rewrite EN, EF. exact HI3.
  - eapply bandtp_grow; [exact HBT|]. intros q Hq. destruct (HTP q Hq) as [H|H]; [left; exact H | right; intros Hb; exfalso; exact (H Hb)].
Qed.

Lemma u64_of_Z0 : ltac2:(tb__ "0|1|
S0S3S12Z0R1A2S13R1S18Z2Z40A2A2A2S2S0S29Q40M0S2bG0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64). apply Z.mod_small. exact Hz. Qed.

Lemma KD_trans_page : ltac2:(tb__ "0|3|
S32S7S2aQ40M0A1M1A1S1bSfG1S49S7S1cA1S6aR4S9S0S33R7A1A2A2S13S62S0R5S3cR8A1Z0M2A4S57A2S2G1R5S2bG0S5fR9R6S62S0R6S3cR9A1G2A4A3A2A3S2dRaR5R9R4R8A5S2dS5bRbR8A2R6SeG1R7RaA3R5R9A5F_;F_;F_;F_;Ftr;Frho;Fp;Fb;Fmd;Ftp;FG;").
Proof.
  intros G tp md b p rho tr Hb Hk Hp (HX & HK & [HL HNN] & HT). subst p. split; [|split; [exact HK | split; [| exact HT]]].
  2:{ split; [unfold G_page; cbn [dFP dFB]; rewrite length_list_upd; exact HL|].
      intros b' Hb'. unfold G_page in Hb' |- *. cbn [dFP dFB] in Hb' |- *.
      destruct (Nat.eq_dec b' b) as [->|Hne].
      - rewrite Model.nth_list_upd_same by (rewrite HL; exact Hb). pose proof (HNN b Hb). lia.
      - rewrite Model.nth_list_upd_other by (intros E; exact (Hne (eq_sym E))). exact (HNN b' Hb'). }
  apply (AInvX_depot_cost G (G_page G b) tp (_ :: tp) md); [reflexivity | reflexivity | | | exact HX].
  - rewrite (dep_cost_G_page G b) by (rewrite HL; exact Hb). pose proof (paid_cons_le md (Z_to_bv 64 (fpage G b (nth b (dFP G) 0))) tp). unfold PG. unfold page_size in *. lia.
  -
    intros q [<-|Hq]; [right | left; exact Hq].
    destruct HX as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & _ & _ & X5 & _).
    cbn [aa_geom aa_depot AK bumpK with_depot] in X5.
    destruct (X5 (nth b (dFB G) 0, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists (nth b (dFB G) 0); split; [reflexivity | apply nth_In; exact Hb])) as (DI & _).
    cbn [fst snd] in DI. destruct DI as (D1 & _ & D3 & _ & D5). pose proof (topG_range (aa_geom A0)) as TG. pose proof (HNN b Hb) as K0.
    unfold fpage. rewrite u64_of_Z0 by (unfold FBSZ, FBPAGES, PG in *; lia).
    intros HBP. apply band_page_band in HBP. unfold FBSZ, FBPAGES, PG in *. clear -D5 HBP K0 Hk D1 D3 TG. lia.
Qed.

Lemma apart_in_maps : ltac2:(tb__ "0|3|
S25S2aQ40M0A1M1G1S0S0S2ScS22S8SaG1G1A2S1eR5A1S1dR5A1A3R4R3A3SdA3S68R6R3R2A3S4S12S11S29G0R6A2M2S29G0R5A2A2R4A2S12R3G2A2A2F_;F_;Fhi;Flo;Fn;Fa;FV;").
Proof.
  intros V a n lo hi Hfree (e & Hin & H1 & H2).
  destruct (apart_of_region_free _ a n Hfree e ltac:(apply in_or_app; right; exact Hin)) as [X|X]; cbn [fst snd] in X; [left | right]; lia.
Qed.

Lemma sec_dyn : ltac2:(tb__ "0|0|
S6dS42S3dS69R3R2A2S4dS3dR2S3bR3A1A3S65S41S35R4A1A1S47R3A1S48R3A1A3F_;F_;Fch;FA;Fm;").
Proof.
  intros m A ch (HS & _) Hin. apply In_nth_error in Hin as (i & Hi).
  destruct (HS i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & DI & _). exact DI.
Qed.

Lemma u64_of_Z : ltac2:(tb__ "0|1|
S0S3S12Z0R1A2S13R1S18Z2Z40A2A2A2S2S0S29Q40M0S2bG0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64). apply Z.mod_small. exact Hz. Qed.

Lemma AInvX_grant : ltac2:(tb__ "0|e|
S32S32S7S2aQ40M0A1M1A1S1bS1bG1G1S0S2S7SaG1G1A2M2A1M3S1dS1aR4A1A1SeG2SbG1G1R3R2A4S1dS1aR5A1M4A1A3A3S2G3S1fG4A1S1fS1aR6A1M5A1A3S2G3S1eG5A1S1eS1aR7A1M6A1A3S2S0S21G6A1S21S1aR8A1M7A1A3S2S0S20G7A1S20S1aR9A1A1A3G1S2ScS26R1S28RbA1M8A2SdA3S2ScS26R2G8A2SdA3F_;Fp;S2S0S29G0R8A2R7A3S13Z0R8A2S12S63S29G0RbA2A2S12S11S29G0RcA2RaA2S20S1aReA1A1A2S2ScS22S8G2S1eS1aRfA1M9A1S1dG9A1A3RdRcA3SdA3S12S11S4eRfR11A2S52R13A1A2S11S4eR10R11A2S52R12A1A2A2SaS0S0A2MaS4dGaR1S53R14A1A3S4S4dGaR2S53R16A1A3S2GaR2SbS0S0S29G0R11A2RfA4A3A2F_;Fbn;S2S0S11S14S9S0S34R14A1A2A1S14S9S0S33R14A1A2A1A2S11S11S14S9S0S34R15A1A2A1MbS14S9S0S33R15A1A2A1McA2Z1A2A3S2S0S11S15S50GbA2S15S51GcA2A2S11S11S15S50S14S9S0S34R16A1A2A1A2S15S51S14S9S0S33R16A1A2A1A2A2RfA2A3S60S2eR17A1MdVrhoE;R15R14A4S60GdVrhoE;R16R14A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FL;Fn;Fa;Fmd';Fmd;Ftp;FG';FG;").
Proof.
  intros G G' tp md md' a n L Hvm Hna Hrs Hlm Htop Hlz HnL HL Himg Hceil Hfree Hpaid Hblk Hcnt Hsz (HG & HR & HF & HRest & HM & HI3 & HBT).
  cbn [aa_geom AK bumpK with_depot] in HG, HR, HF, HRest.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|].
  unfold model_inv_nd, ledger_inv_nd in HM. rewrite AK_credit in HM.
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec AK bumpK with_depot] in HM.
  destruct HM as (VG & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & _ & _ & L7 & L8 & L9).
  set (G0g := aa_geom A0) in *.
  assert (APT : forall lo sz, in_maps (m_vmmaps md) lo (lo + sz) -> sepZ (bv_unsigned a, L) (lo, sz)).
  { intros lo sz Him. destruct (apart_in_maps _ a n lo (lo + sz) Hfree Him) as [X|X]; unfold sepZ; cbn [fst snd]; lia. }
  assert (INM : forall lo hi, in_maps (m_vmmaps md) lo hi -> in_maps (m_vmmaps md') lo hi).
  { intros lo hi (e & Hin & He). exists e. split; [rewrite Hvm; right; exact Hin | exact He]. }
  split; [|split; [|exact HBT]].
  -
    unfold model_inv_nd, ledger_inv_nd. rewrite AK_credit.
    cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec AK bumpK with_depot].
    destruct VG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
    split.
    { unfold vm_geom. cbn [aa_geom aa_sec AK bumpK with_depot]. fold G0g. rewrite Hna.
      split; [|split; [apply INM; exact G2 | split; [apply INM; exact G3 | split; [apply INM; exact G4 | split; [apply INM; exact G5 | split; [apply INM; exact G6 | split; [apply INM; exact G7 | split]]]]]]].
      - intros e x He Hx. destruct (G1 e x He Hx) as (e' & He' & Hx'). exists e'. split; [rewrite Hvm; right; exact He' | exact Hx'].
      - intros ch Hch. rewrite Hvm. right. exact (G8 ch Hch).
      - intros p Hal Hw. destruct (G9 p Hal Hw) as [P1 P2]. split; [apply Hlz; exact P1 | exact P2]. }
    split.
    { unfold budget_boundD in V2 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed AK bumpK with_depot] in V2 |- *. clear -V2 Hpaid. lia. }
    split; [rewrite Hlm; exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [exact V6|]. split; [rewrite Htop; exact V7|].
    split; [rewrite Hrs; exact L1|]. split; [rewrite Hvm; apply band_covered_cons; exact L2|].
    split.
    { rewrite Hrs, Hvm. apply maps_disjoint_insert; [exact L3|]. intros e' He'. exact (apart_of_region_free _ a n Hfree e' He'). }
    split.
    { unfold gap_ok, gapN_ok, gapS_ok, blocks_left, ledger in L4 |- *. cbn [aa_V aa_depot AK bumpK with_depot] in L4 |- *.
      rewrite Hrs, Hvm. destruct L4 as [N4 S4].
      pose proof (hwN_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IN.
      pose proof (hwS_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IS. cbn [snd] in IS. rewrite HnL in IS.
      split; [clear -N4 IN Hcnt; unfold GN in *; lia | clear -S4 IS Hsz; lia]. }
    split; [exact I|]. split; [exact I|]. split; [exact L7 | split; [| rewrite Hna; exact L9]].

    destruct L8 as (L8p & L8a & L8b). split; [|split; [exact (INM _ _ L8a) | exact (INM _ _ L8b)]].
    intros b s Hbs. rewrite Hvm in Hbs. destruct Hbs as [E|Hbs]; [injection E as <- <-; rewrite HnL; exact HL | exact (L8p b s Hbs)].
  -
    unfold inv3 in HI3 |- *. cbn [aa_geom aa_sec aa_live aa_depot aa_q_thread aa_q_global aa_cls AK bumpK with_depot] in HI3 |- *. fold G0g in HI3 |- *.
    destruct HI3 as (X1 & X2 & X3 & X4 & X5 & X6).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [|exact X6].
    intros bn Hbn. destruct (Hblk bn Hbn) as [Hold | ->]; [exact (X5 bn Hold)|].
    destruct VG as (_ & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). fold G0g in G2, G3, G4, G5, G6, G7.
    cbn [fst snd]. split.
    {
      pose proof (geom_top _ HG) as TG. fold G0g in TG.
      assert (BC : band_covered (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) Geometry.SHADOW_BAND_LO Geometry.SHADOW_BAND_HI).
      { apply band_covered_app_r. exact L2. }
      pose proof (grant_avoids_band _ _ _ a n BC ltac:(unfold Geometry.SHADOW_BAND_LO, Geometry.SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; lia) Hfree ltac:(lia)) as W.
      rewrite HnL in W. unfold dyn_in. unfold IMG_HI in *. rewrite TG. rewrite <- V7. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; lia | exact W]. }
    split; [apply APT; exact G3|]. split; [apply APT; exact G4|]. split; [apply APT; exact G5|]. split; [apply APT; exact G6|].
    split; [apply APT; replace (ag_spacebeg G0g + (kSpaceSize + 4096)) with (ag_spacebeg G0g + kSpaceSize + 4096) by lia; exact G2|]. split; [apply APT; exact G7|].
    intros ch Hch.
    destruct HRest as (_ & _ & _ & HSR & _). pose proof (sec_dyn _ _ ch HSR Hch) as DI. cbn [aa_geom AK bumpK with_depot] in DI. fold G0g in DI.
    destruct DI as (D1 & D2 & D3 & _). pose proof (topG_range G0g) as TGR.
    pose proof (apart_of_region_free _ a n Hfree (Z_to_bv 64 (sc_map_beg ch), Z_to_bv 64 (sc_map_size ch)) ltac:(apply in_or_app; right; exact (G8 ch Hch))) as X.
    unfold apartW in X. cbn [fst snd] in X. rewrite !u64_of_Z in X by lia. unfold sepZ. cbn [fst snd]. lia.
Qed.

Lemma sumZ_app : ltac2:(tb__ "0|1|
S7S0A1M0G0S2S0S54S8S0R2R1A3A1S11S54R2A1S54R1A1A2A3Fl2;Fl1;").
Proof. induction l1; intros l2; cbn; [reflexivity | rewrite IHl1; unfold sumZ; cbn; lia]. Qed.

Lemma in_dblocks_app : ltac2:(tb__ "0|4|
S32SaS0S0A2M0S7S0A1M1G1S4dG0R3S8G0S61S0G0S0SbS0S0R1S50A4Lb;M2S8S0S34R4A1R2A3A4S61S0G0S0SbS0S0R1S51A4Lb;M3S8S0S33R4A1R1A3A4A3A3S4S4dG0R4S53R5A1A3S4dG0R4S8G0S61S0G0G2R3A4S61S0G0G3R2A4A3A3A2F_;Fl2;Fl1;Fbn;FG;").
Proof.
  intros G bn l1 l2 H. unfold dblocks. rewrite !map_app in H.
  apply in_app_or in H as [H|H]; apply in_app_or in H as [H|H].
  - left. apply in_or_app. left. exact H.
  - right. apply in_or_app. left. exact H.
  - left. apply in_or_app. right. exact H.
  - right. apply in_or_app. right. exact H.
Qed.

Lemma KD_trans_fblk : ltac2:(tb__ "0|5|
S32S7S2aQ40M0A1M1A1S1bS25G1G1S49S7S1cA1S2S7SaG1G1A2M2A1M3S1dR5A1SeG2SbG1G1R4R3A4S1dS1aR6A1A1A3A3S2G3S1fR6A1S1fS1aR7A1A1A3S2G3S1eR7A1S1eS1aR8A1A1A3S2S0S21R8A1S21S1aR9A1A1A3S2G1S23R9A1S23S1aRaA1A1A3S2S0S29G0R8A2S51A3S2S0S17S29G0RaA2S64A2Z0A3S12S63S29G0RbA2A2S12S11S29G0RcA2S51A2S20S1aReA1A1A2S2ScS22S8G2S1eS1aRfA1M4A1S1dG4A1A3RdRcA3SdA3S12S4eS27ReRdS24RfR10A2A3R11A2S4eR10R11A2A2S2dR13RdR12RcR11A5S2dS58R14S29G0R10A2A2ReR13RdS27R10RfS24R11R12A2A3A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftr;Frho;Fn;Fa;Fh';Fmd;Ftp;FG;").
Proof.
  intros G tp md h' a n rho tr Hvm Hna Hrs Hlm Hsp HnL Hal Himg Hceil Hfree Hpaid (HX & HK & HL & HT).
  split; [|split; [|split; [|exact HT]]].
  - apply (AInvX_grant G (G_fblk G (bv_unsigned a)) tp md _ a n FBSZ); rewrite ?m_vmmaps_vm_add_lazy, ?m_vmmaps_with_vmmaps, ?m_vm_lazy_vm_add_lazy, ?m_vm_lazy_with_vmmaps;
      try assumption.
    + apply alloc_top_same. exact Hsp.
    + intros p Hp. rewrite page_in_ranges_app, Hp. apply orb_true_r.
    + unfold FBSZ; lia.
    + unfold dep_cost, dep_pages, G_fblk. cbn [dNB dFP]. rewrite sumZ_app. cbn [sumZ fold_right]. lia.
    + intros bn Hbn. unfold G_fblk in Hbn. cbn [dNB dFB] in Hbn. unfold dblocks in Hbn. cbn [dNB dFB] in Hbn.
      rewrite <- (app_nil_r (dNB G)) in Hbn.
      destruct (in_dblocks_app G bn [] [bv_unsigned a] Hbn) as [X|X]; [left; exact X | right]. cbn in X. destruct X as [X|[]]. symmetry. exact X.
    + unfold G_fblk. cbn [dNB dFB]. rewrite length_app. cbn [length]. lia.
    + unfold G_fblk. cbn [dNB dFB]. rewrite length_app. cbn [length]. lia.
  - unfold vm_add_lazy. rewrite with_vm_backing_with_vm. apply HKc.
    replace (with_vmmaps h' md) with (with_vm (mkVmState h' (m_vm_lazy md) (m_vm_materialized md)) md) by (destruct md; reflexivity).
    apply HKc. exact HK.
  - destruct HL as [HL HNN]. split; [unfold G_fblk; cbn [dFP dFB]; rewrite !length_app; cbn [length]; lia|].
    intros b Hb. unfold G_fblk in Hb |- *. cbn [dFP dFB] in Hb |- *. rewrite length_app in Hb. cbn [length] in Hb.
    destruct (Nat.lt_ge_cases b (length (dFB G))) as [Hlt|Hge].
    + rewrite app_nth1 by (rewrite HL; exact Hlt). exact (HNN b Hlt).
    + rewrite app_nth2 by (rewrite HL; exact Hge). replace (b - length (dFP G))%nat with 0%nat by (rewrite HL; lia). cbn. lia.
Qed.

Lemma KD_trans_nblk : ltac2:(tb__ "0|5|
S32S7S2aQ40M0A1M1A1S1bS25G1G1S49S7S1cA1S2S7SaG1G1A2M2A1M3S1dR5A1SeG2SbG1G1R4R3A4S1dS1aR6A1A1A3A3S2G3S1fR6A1S1fS1aR7A1A1A3S2G3S1eR7A1S1eS1aR8A1A1A3S2S0S21R8A1S21S1aR9A1A1A3S2G1S23R9A1S23S1aRaA1A1A3S2S0S29G0R8A2S50A3S2S0S17S29G0RaA2S64A2Z0A3S12S63S29G0RbA2A2S12S11S29G0RcA2S50A2S20S1aReA1A1A2S2ScS22S8G2S1eS1aRfA1M4A1S1dG4A1A3RdRcA3SdA3S12S4eS24RfR10A2R11A2S11S4eR10R11A2S50A2A2S2dR13RdR12RcR11A5S2dS5aR14S29G0R10A2A2ReR13RdS24R11R12A2A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftr;Frho;Fn;Fa;Fh';Fmd;Ftp;FG;").
Proof.
  intros G tp md h' a n rho tr Hvm Hna Hrs Hlm Hsp HnL Hal Himg Hceil Hfree Hpaid (HX & HK & HL & HT).
  split; [|split; [|split; [|exact HT]]].
  - apply (AInvX_grant G (G_nblk G (bv_unsigned a)) tp md _ a n NBSZ); rewrite ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps; try assumption.
    + apply alloc_top_same. exact Hsp.
    + intros p Hp. exact Hp.
    + unfold NBSZ; lia.
    + unfold dep_cost, dep_pages, G_nblk. cbn [dNB dFP]. rewrite length_app. cbn [length]. lia.
    + intros bn Hbn. unfold G_nblk in Hbn. cbn [dNB dFB] in Hbn. unfold dblocks in Hbn. cbn [dNB dFB] in Hbn.
      rewrite <- (app_nil_r (dFB G)) in Hbn.
      destruct (in_dblocks_app G bn [bv_unsigned a] [] Hbn) as [X|X]; [left; exact X | right]. cbn in X. destruct X as [X|[]]. symmetry. exact X.
    + unfold G_nblk. cbn [dNB dFB]. rewrite length_app. cbn [length]. lia.
    + unfold G_nblk. cbn [dNB dFB]. rewrite length_app. cbn [length]. lia.
  - replace (with_vmmaps h' md) with (with_vm (mkVmState h' (m_vm_lazy md) (m_vm_materialized md)) md) by (destruct md; reflexivity).
    apply HKc. exact HK.
  - unfold dfp_ok, G_nblk. cbn [dFP dFB]. exact HL.
Qed.

Lemma KD_trans_ins : ltac2:(tb__ "0|0|
S32S7S2aQ40A1A1S1bS0S49S7S1cA1S2dR6R2R5R1R4A5S2dS59R7R4A2R3R6R2R5A5F_;Ftr;Frho;FdF';Fmd;Ftp;FG;").
Proof.
  intros G tp md dF' rho tr (HX & HK & HL & HT). split; [|split; [exact HK | split; [unfold dfp_ok, G_ins; cbn [dFP dFB]; exact HL | exact HT]]].
  apply (AInvX_depot_cost G (G_ins G dF') tp tp md); [reflexivity | reflexivity | | intros q Hq; left; exact Hq | exact HX].
  unfold dep_cost, dep_pages, G_ins. cbn [dNB dFP]. lia.
Qed.

Theorem KD_trans : ltac2:(tb__ "0|1|
S32S7S2aQ40A1A1M0S1bS32G0S1bS49S7S1cA1S5eR8R7R6R5R4R3A6S2dR9R3R8R2R7A5S2dR7R4R6R3R5A5F_;F_;Ftr;Frho;Fmd';Ftp';FG';Fmd;Ftp;FG;").
Proof.
  intros G tp md G' tp' md' rho tr HT HK. destruct HT.
  - eapply KD_trans_page; eassumption.
  - apply KD_trans_fblk; assumption.
  - eapply KD_trans_nblk; eassumption.
  - apply KD_trans_ins; assumption.
Qed.

Lemma KD_place : ltac2:(tb__ "0|2|
S32S49S7S2aQ40M0A1M1A1S7S1cA1S1bS0S2dR6R5R4R3R2A5S5cVsegs;R7R6R3R5A5S12S40R8A1S55A2S4S2S0R4S50A3S2S0R4S51A3A2S5G1G1S70S2bG0Z0A2R7S2bG0R6A2R1A4La;A2F_;F_;F_;F_;FL;Fmd;Ftr;Ftp;Frho;FG;").
Proof.
  intros G rho tp tr md L ((HG & _ & _ & _ & HM & _) & _) [DM _] HDN HL.
  cbn [aa_geom AK bumpK with_depot] in HG.
  destruct HM as (_ & _ & _ & V4 & V5 & V6 & V7 & _ & _ & _ & L4 & _).
  pose proof (dm_map1_len _ _ DM) as [_ M2]. pose proof (dm_fb_len _ _ DM) as [[_ F2] _].
  pose proof (dm_N _ _ DM) as [[N1 _] _]. pose proof (dm_F _ _ DM) as (F0 & _ & F32 & _).
  apply (depot_place (AK G) md L).
  - exact L4.
  - cbn [aa_V AK bumpK with_depot]. cbn [aa_V aa_Km aa_Kf AK bumpK with_depot] in V4, V5, V6. pose proof (budget_ok_alloc_limit _ _ HB) as HBl.
    pose proof (VCAP_limit_alloc (aa_V A0) (aa_Km A0) (aa_Kf A0) nreq ltac:(lia) HKm0 V6 HBl) as VC. lia.
  - cbn [aa_depot AK bumpK with_depot]. unfold nblk in M2. unfold NBMAX, DNMAX in *.
    destruct (Z.eqb_spec (dN G + 1) 0); [lia|].
    pose proof (Z.div_le_mono (dN G + 1) (2 ^ 28 + 2) 65536 ltac:(lia) ltac:(lia)) as DV. change ((2 ^ 28 + 2) / 65536) with 4096 in DV. lia.
  - cbn [aa_depot AK bumpK with_depot]. unfold fblk in F2. unfold FBMAX.
    pose proof (Z.div_le_mono (dF G + 1048576 - 1) (2 ^ 32 - 2 ^ 21 + 1048576 - 1) 1048576 ltac:(lia) ltac:(lia)) as DV.
    change ((2 ^ 32 - 2 ^ 21 + 1048576 - 1) / 1048576) with 4094 in DV. lia.
  - rewrite V7. cbn [aa_geom AK bumpK with_depot]. pose proof (geom_top _ HG) as TG. pose proof (topG_range (aa_geom A0)). rewrite GAPC_eq. unfold alloc_ceiling_lo. lia.
  - exact HL.
Qed.

Theorem KD_laws : ltac2:(tb__ "0|0|
S1S6eP10R1A2S78Vsegs;S2dR2S2fA4F_;Fn;").
Proof.
  intros n Hn16. constructor.
  - exact (KD_stable n Hn16).
  - exact KD_view.
  - exact KD_trans.
  - intros G rho tp tr md HK _. exact (KD_room G rho tp tr md HK).
  - exact KD_reserved.
  - exact KD_noacc.
  - exact KD_place.
Qed.

Lemma KD_intro : ltac2:(tb__ "0|0|
S7S2aQ40A1A1S7S1cA1S1bS66Vsegs;VA0;VrhoE;R3R1A5VKc;R3R2A2S49S30R1A1S2dS36VA0;A1R2R7R6R5A5F_;Frho;F_;F_;Fmd;Ftr;Ftp;").
Proof.
  intros tp tr md HA HK rho HT. destruct (AInvA_X A0 rhoE tp md HA) as (HX & HD & _).
  split; [|split; [exact HK | split; [split; [exact (proj2 (dm_fb_len _ _ (proj1 HD))) | intros b Hb; exact (proj1 (proj1 (dm_fp _ _ (proj1 HD) b Hb)))] | exact HT]]].
  unfold AK. replace (with_depot A0 (aa_depot A0)) with A0 by (destruct A0; reflexivity). exact (AInvX_bumpK A0 rhoE tp md HX).
Qed.

Lemma dN_entry : ltac2:(tb__ "0|0|
S7S2aQ40A1A1S1bS66Vsegs;VA0;VrhoE;R2R1A5S12S11S40S36VA0;A1A1Z1A2S55A2F_;Fmd;Ftp;").
Proof.
  intros tp md HA. destruct (AInvA_X A0 rhoE tp md HA) as ((_ & _ & _ & _ & HM & _) & _ & L6).
  destruct HM as (_ & _ & _ & V4 & V5 & V6 & _). pose proof (budget_ok_alloc_limit _ _ HB) as HBl.
  pose proof (limit_ok_alloc_K (aa_V A0) (aa_Km A0) (aa_Kf A0) nreq ltac:(lia) HBl). unfold DNMAX. lia.
Qed.

Lemma QMAX_Q1 : QMAX - Q1 = 2813952.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma hcD_entry : ltac2:(tb__ "0|1|
S7S2aQ40A1A1S1bS66Vsegs;VA0;VrhoE;R2R1A5S16S2fS11S52S36VA0;A1M0A1S5dG0A1A2A2F_;Fmd;Ftp;").
Proof.
  intros tp md HA. destruct (AInvA_X A0 rhoE tp md HA) as ((_ & _ & _ & _ & HM & _) & HD & L6).
  destruct HM as (_ & _ & _ & V4 & V5 & V6 & _ & _ & _ & _ & _ & _ & _ & L7 & _).
  pose proof (dep_cost_bound segs _ _ _ _ HD) as DC. pose proof (dm_F _ _ (proj1 HD)) as (F0 & F11 & F32 & _). pose proof (dm_N _ _ (proj1 HD)) as [[N1 _] _].
  assert (FB : fblk (dF (aa_depot A0)) <= 4094).
  { unfold fblk. pose proof (Z.div_le_mono (dF (aa_depot A0) + 1048576 - 1) (2 ^ 32 - 2 ^ 21 + 1048576 - 1) 1048576 ltac:(lia) ltac:(lia)) as DV.
    change ((2 ^ 32 - 2 ^ 21 + 1048576 - 1) / 1048576) with 4094 in DV. lia. }
  pose proof (budget_ok_alloc_limit _ _ HB) as HBl. unfold limit_ok_alloc in HBl. unfold hcD.
  pose proof (acost_mono (aa_V A0) (aa_V A0 + nreq) ltac:(lia)) as AM.
  pose proof QMAX_Q1 as CL.
  assert (DR : droom (aa_depot A0) <= PG + NBSZ) by (unfold droom; destruct ((dN (aa_depot A0) + 1) mod 65536 =? 0); unfold PG, NBSZ; lia).
  unfold DEPC, PG, NBSZ, BETA1, BETA_M, BETA_F, kPtrArrayCommit, LIMIT in *.
  set (q1 := Q1) in *. set (qm := QMAX) in *. set (u0 := U0) in *. set (dc := dep_cost (aa_depot A0)) in *. set (dr := droom (aa_depot A0)) in *.
  set (av := acost (aa_V A0)) in *. set (avn := acost (aa_V A0 + nreq)) in *. set (fb := fblk (dF (aa_depot A0))) in *.
  clearbody q1 qm u0 dc dr av avn fb. lia.
Qed.
End DepotK.

End DepotK.

(* [comment removed for export] *)
Module CertMallocSS.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "nil"; "app"; "prod"; "option"; "false"; "list"; "None"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SVar"; "SPUle"; "sobj"; "SAlu"; "FcsrFrm0"; "SPAlign"; "SPBranch"; "SPUlt"; "mkSS"; "DZero"; "SPNot"; "cell"; "mkObj"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_setS"; "sym_runA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_MS"; "V_NS"; "msx"; "V_NCH"; "V_NRES"; "V_PAB"; "RT_sec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS.W"; "CS1"; "nxS"; "regs_ss"; "ES1"; "ES1f"; "SS0"; "SSa_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayReserve"; "IMG_HI"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "ERRNO_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_regs"; "E_s1"; "F_fam"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Stdlib.PArith.BinPos.Pos"; "succ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymCall ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition V_NS : positive := 141%positive.
Definition V_MS : positive := 142%positive.
Definition V_PAB : positive := 145%positive.
Definition V_NRES : positive := 146%positive.
Definition V_NCH : positive := 147%positive.

Definition N_sec : list carve_spec := ltac2:(tb__ "0|d|
S1S5S5S5ScSbA2M0SbA2M1S8S5S5SbS2A2M2ScA2M3A1M4A2M5S0G1G4S0G0SbS0ScSbSeZ0A1M6S1dA4S1eS1dZ40A2M7A4S1G3S0G2ScS0SbS2S1dU8M8A4SeS3dA1A4S1G3S0G2ScS0SbS2S1eS1dZ8A2G8A4SfS2dA1M9A4S1G3S0G2ScS0SbS2S1eS1dZ10A2G8A4G9A4S1G3S0G2ScS0SbS2S1eS1dZ18A2G8A4SeS3bA1A4S1G3S0G2ScS0SbS2S1eS1dZ30A2G8A4SfS2cA1A4S1G3S0G2ScS0SbS2S1eS1dZ38A2G8A4SfS2bA1A4S3G3A1MaA3A3A3A3A3A3A4S1G5S0G1G4S0G0SbS0ScSbG6G7A4Zee040MbA4GaA4S1G5S0G1G4S0G0SbS0ScSbG6GbA4Zee044A4S1G3S0G2ScS0SbS2GbU4A4G6A4GaA3A4S1G5S0G1G4S0G0SbS0ScSbG6Zee048A4Zee070A4GaA4S1G5S0G1G4S0G0SbS0ScSbG6Ze9b28McA4Ze9b30A4S1G3S0G2ScS0SbS2GcG8A4SeZ1a36fA1A4GaA3A4S1G5S0G1G4S0G0SbS0ScSbG6Z173660A4Z173662A4S1G3S0G2ScS0SbS2Z173661U1A4SeZ1A1A4GaA3A4S1G5S0G1G4S0G0SbS0ScSbG6S3eA4S1eS3eZ4A2A4GaA4S1G5S0G1G4S0G0SbS0ScSbS48Zad0A4Zc60A4GaA4S3G5A1A3A3A3A3A3A3A3A3").
Definition RT_sec : list sobj := map carve_obj N_sec.
Definition O_seci : sobj := nth 0 RT_sec O_st. Definition O_secs : sobj := nth 1 RT_sec O_st. Definition O_secm : sobj := nth 2 RT_sec O_st.
Definition O_secg : sobj := nth 3 RT_sec O_st. Definition O_san : sobj := nth 4 RT_sec O_st. Definition O_oom : sobj := nth 5 RT_sec O_st.
Definition O_errno : sobj := nth 6 RT_sec O_st.

Definition msx : sv := ltac2:(tb__ "0|0|
S12S21S12S23S12S21SfS29A1SeZfffA1A3SeZfffffffffffff000A1A3SeZ1000A1A3").
Definition F_sgen : list sprop := ltac2:(tb__ "0|6|
S1SdS14S29Z3A2S1SdS10SeZ10c08A1SfS29A1M0A2S1SdS16G0SeS1eS1fZ2M1Z27A2Z1008A2A1A2S1SdS14S28ZcA2S1SdS10S12S21G0SeZ1000A1A3SfS28A1M2A2S1SdS10G2S12S21G0SeZ1fffA1A3A2S1SdS16G2SeS1fG1Z28A2A1M3A2S1SdS15S22G2S2aA3S1SdS10SeS3cA1SfS2dA1M4A2S1SdS10G4SeS20Z7fffff800000S3bA2A1A2S1SdS10SfS2bA1SfS2cA1M5A2S1SdS10G5SeS1fG1Z14A2A1A2S1SdS10G0S2aA2S1SdS10S2aG3A2S1SdS19S15S22S12S21SfPaA1SeN998A1A3SeZ0A1A3A1S3SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Section W.
Variable W : list ulink.
Variable st : ustop.
Variable tmax : Z.

Let FACTS1 : list sprop := ltac2:(tb__ "0|0|
S4SdS4SdS4SdS4SdS4cVW;Vst;A2S4bS4aA1A3S39A3S44A3S43Vtmax;Z8A2A3").
Let OBJS1 : list sobj := ltac2:(tb__ "0|0|
S4S11S1S11S46S4S11S4dVW;A1S49A3A3S45A3").

Definition regs_ss : list sv := ltac2:(tb__ "0|2|
S37S41Z8A1S1S5S2ScA2M0S0S2ScUcSfS29A1M1A4S1G0S0S2ScU13G1A4S3G0A1A3A3A2").
Definition SSa_S : sstate := ltac2:(tb__ "0|0|
S17Z40a18S31S36S13S9ScA1VOBJS1;VFACTS1;S38S7A9").
Definition SSa : axst := ltac2:(tb__ "0|0|
S25S42VW;Vst;Vtmax;Z8A4S35A2").
Definition SSb_S : sstate := ltac2:(tb__ "0|0|
S17Z40a18S31S36S13S9ScA1S4S11VOBJS1;S2eA3VFACTS1;S38S7A9").
Definition SSb : axst := ax_setS SSa SSb_S.
Definition SS0 : axst := ax_add_facts F_sgen SSb.
Definition runS1 : list leafA := ltac2:(tb__ "0|1|
S6S8S24A1M0A1G0Lx;S26S3aUfa0S1SbZ7050cS3SbA1A3S34SaA5G0R1Ll;S3S24A1X6x2").
Definition ES1 : axst := leaf 0 runS1.

Definition CS1 : axst := ltac2:(tb__ "0|1|
S47VW;Vst;Vtmax;S32Z7050cS1S5S2ScA2M0S0S2ScUbSfS28A1A4S3G0A1A3S3S11A1S7S3SdA1A9").

Definition ES1f : axst := ltac2:(tb__ "0|0|
S40S2fSeS20S1fZ2Z40A2ZcA2A1A2").
Definition runSf : list leafA := ltac2:(tb__ "0|1|
S6S8S24A1M0A1G0Lx;S26S3aUfa0S1SbZ5e398S3SbA1A3S33SaA5G0R1Ll;S3S24A1X6x2").
Definition ESn : axst := leaf 0 runSf.

Definition nxS : positive := ss_next (ax_S CS1).
Definition ES1g : axst := ltac2:(tb__ "0|2|
S25S2fS3fS27S2fA1M0SfS30A1M1S4S11S1cG0A1S1S11S1bG1SeZ0A1SfS28A1S3S1aA1S18A5S3S11A1A3A3S4eS30A1A4A2").
End W.

Goal map (fun L => (ss_pc (ax_S (la_state L)), la_reason L)) (runS1 (Wcan 0) UStopLe 2) = [(0x7050c, RsCut)]
  /\ nth 11 (ss_regs (ax_S (ES1 (Wcan 0) UStopLe 2))) (SLit 0) = SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SVar V_NS) (SLit 4095)) (SLit 18446744073709547520)) (SLit 8191)) (SLit 18446744073709547520)
  /\ nth 17 (ss_regs (ax_S (ES1 (Wcan 0) UStopLe 2))) (SLit 0) = SLit 222.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal map (fun L => (ss_pc (ax_S (la_state L)), la_reason L)) (runSf (Wcan 0) UStopLe 2) = [(0x5e398, RsCut)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End CertMallocSS.

(* [comment removed for export] *)
Module InvFoot.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "of_nat"; "div"; "pow"; "leb"; "mul"; "modulo"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "sec_chunk"; "aa_sec"; "ageom"; "aa_cls"; "aa_live"; "qbatch"; "class_state"; "ag_spacebeg"; "sc_map_beg"; "aa_cache_inited"; "ag_pab"; "sc_map_size"; "aa_depot"; "ag_thread"; "topG"; "aa_internal_inited"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "cs_allocated_user"; "cs_empty"; "qb_addr"; "sc_size"; "@Corelib.Init.Datatypes"; "list"; "option"; "bool"; "prod"; "true"; "Some"; "andb"; "false"; "nat"; "negb"; "orb"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "c_addr"; "cell_ok"; "acell"; "c_w"; "view"; "rtc_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "primary_repr"; "secondary_repr"; "batch_repr"; "alloc_magic_ok"; "class_repr"; "ia_inv"; "inv3"; "live_block_repr"; "misc_inv"; "nthZ"; "q_item_ok"; "qhdr_repr"; "qlinks"; "quarantine_repr"; "thread_inv"; "geom_ok"; "live_sep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "IMG_LO"; "kSpaceSize"; "rz"; "is_primary"; "kPtrArrayReserve"; "ClassID"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Size"; "needed"; "region_beg"; "FS_total"; "Sh"; "round_up"; "PG"; "dyn_in"; "dyn_ok"; "kQuarantineBatchSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "STORE"; "MAP1"; "DFPw"; "dfp_static"; "MAP1N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD"; "AInvX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qall"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot"; "dstatw"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot.Zones"; "prim_okb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dstatw (z : Z) : Prop := ltac2:(tb__ "0|0|
S1S67Vz;A1S1S3S1S5S6S64Z10A2Vz;A2S7Vz;S6S64Z18A2A2A2A1S3S1S5S65Vz;A2S7Vz;S6S65Z8A2A2A2A1A2A2").
Lemma dstat_range : ltac2:(tb__ "0|0|
SfS67R1A1S1S5S64R2A2S7R2S6S65SdZ8S68A2A2A2A2F_;Fz;").
Proof. intros z Hz. unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in *. lia. Qed.
Lemma dstat_img : ltac2:(tb__ "0|0|
SfS67R1A1S1S5S52R2A2S7R2S51A2A2F_;Fz;").
Proof. intros z Hz. pose proof (dstat_range z Hz). unfold STORE, MAP1, MAP1N, IMG_LO, IMG_HI in *. lia. Qed.

Section Zones.
Variables (Gg : ageom) (secs : list sec_chunk) (m m' : bview).

Hypothesis AGimg : ltac2:(tb__ "0|0|
SfS1S5S52R1A2S7R1S51A2A2S3S70R2A1A1S0S2dS37Q8A1A1Vm';R3A1Vm;R3A1A3F_;F_;Fz;").
Hypothesis AGsp : ltac2:(tb__ "0|1|
SfS1S5S19VGg;A1M0R1A2S7R1S6S6G0S53A2Z1000A2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis AGth : ltac2:(tb__ "0|1|
SfS1S5S1fVGg;A1M0R1A2S7R1S6G0Z1000A2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis AGctx : ltac2:(tb__ "0|1|
SfS1S5S25VGg;A1M0R1A2S7R1S6G0Z1000A2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis AGdtls : ltac2:(tb__ "0|1|
SfS1S5S26VGg;A1M0R1A2S7R1S6G0Z1000A2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis AGfs : ltac2:(tb__ "0|1|
SfS1S5S27VGg;A1M0R1A2S7R1S6G0S5dA2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis AGpab : ltac2:(tb__ "0|1|
SfS1S5S1cVGg;A1M0R1A2S7R1S6G0S56A2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis AGsec : ltac2:(tb__ "0|1|
S12SfS6dS12R2Vsecs;A3S1S5S1aR3A1M0R2A2S7R2S6G0S1dR3A1A2A2A2S0S2dS37Q8A1A1Vm';R3A1Vm;R3A1A3F_;F_;Fz;Fch;").
Hypothesis AGband : ltac2:(tb__ "0|0|
SfS1S5S59R1A2S7R1S58A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis HG : geom_ok Gg.

Lemma AGlow : ltac2:(tb__ "0|0|
SfS5S52R1A2S7R2S64A2S0S2dS37Q8A1A1Vm';R3A1Vm;R3A1A3F_;F_;Fz;").
Proof. intros z H1 H2. apply AGimg; [unfold STORE, IMG_LO, IMG_HI in *; lia|]. intros [D _]. pose proof (dstat_range z D). lia. Qed.
Lemma AGhigh : ltac2:(tb__ "0|0|
SfS5S6S65SdZ8S68A2A2R1A2S7R2S51A2S0S2dS37Q8A1A1Vm';R3A1Vm;R3A1A3F_;F_;Fz;").
Proof. intros z H1 H2. apply AGimg; [unfold MAP1, MAP1N, IMG_LO, IMG_HI in *; lia|]. intros [D _]. pose proof (dstat_range z D). lia. Qed.
Lemma cell_ok_low : ltac2:(tb__ "0|0|
S3cS5S52S3aR1A1A2S5S6S3aR2A1S9S3dR2A1A1A2S64A2S3bVm;R3A2S3bVm';R4A2F_;F_;F_;Fc;").
Proof. intros c H1 H2. apply cell_ok_agree. intros k Hk. apply AGlow; lia. Qed.
Lemma cell_ok_sp : ltac2:(tb__ "0|1|
S3cS5S19VGg;A1M0S3aR1A1A2S5S6S3aR2A1S9S3dR2A1A1A2S6S6G0S53A2Z1000A2A2S3bVm;R3A2S3bVm';R4A2F_;F_;F_;Fc;").
Proof. intros c H1 H2. apply cell_ok_agree. intros k Hk. apply AGsp; lia. Qed.
Lemma cell_ok_th : ltac2:(tb__ "0|1|
S3cS5S1fVGg;A1M0S3aR1A1A2S5S6S3aR2A1S9S3dR2A1A1A2S6G0Z1000A2A2S3bVm;R3A2S3bVm';R4A2F_;F_;F_;Fc;").
Proof. intros c H1 H2. apply cell_ok_agree. intros k Hk. apply AGth; lia. Qed.
Lemma cell_ok_pab : ltac2:(tb__ "0|1|
S3cS5S1cVGg;A1M0S3aR1A1A2S5S6S3aR2A1S9S3dR2A1A1A2S6G0S56A2A2S3bVm;R3A2S3bVm';R4A2F_;F_;F_;Fc;").
Proof. intros c H1 H2. apply cell_ok_agree. intros k Hk. apply AGpab; lia. Qed.
Lemma cell_ok_sec : ltac2:(tb__ "0|0|
S12S3cS6dS12R2Vsecs;A3S5S1aR3A1S3aR2A1A2S5S6S3aR3A1S9S3dR3A1A1A2S6S1aR4A1S1dR4A1A2A2S3bVm;R4A2S3bVm';R5A2F_;F_;F_;F_;Fc;Fch;").
Proof. intros ch c Hch H1 H2. apply cell_ok_agree. intros k Hk. apply (AGsec ch); [exact Hch | lia]. Qed.
Lemma cell_ok_band : ltac2:(tb__ "0|0|
S3cS5S59S3aR1A1A2S5S6S3aR2A1S9S3dR2A1A1A2S58A2S3bVm;R3A2S3bVm';R4A2F_;F_;F_;Fc;").
Proof. intros c H1 H2. apply cell_ok_agree. intros k Hk. apply AGband; lia. Qed.

Lemma AGsh : ltac2:(tb__ "0|0|
SfSfSfS5Z0R3A2S7R3SbZ2Z2fA2A2S1S5S5eR5A1R3A2S5R3S5eR4A1A2A2S0S2dS37Q8A1A1Vm';R4A1Vm;R4A1A3F_;F_;F_;Fz;Fy;Fx;").
Proof.
  intros x y z Hx Hy Hz. apply AGband. pose proof (Sh_in_band x) as SX. pose proof (Sh_in_band y) as SY.
  unfold Sh in *. pose proof (Z.div_le_mono 0 x 8 ltac:(lia) Hx).
  assert (x < 2 ^ 47 \/ 2 ^ 47 <= x) as [L|L] by lia.
  - specialize (SX ltac:(lia)). assert (y < 2 ^ 47) by lia. destruct (Z_lt_le_dec y 0).
    + pose proof (Z.div_le_mono y x 8 ltac:(lia) ltac:(lia)). lia.
    + specialize (SY ltac:(lia)). lia.
  - pose proof (Z.div_le_mono x z 8 ltac:(lia)). pose proof (Z.div_le_mono (2 ^ 47) x 8 ltac:(lia) L). lia.
Qed.

Lemma rtc_inv_z : ltac2:(tb__ "0|0|
S3fVm;VGg;A2S3fVm';VGg;A2F_;").
Proof.
  intros HR. unfold rtc_inv in *. eapply cells_ok_frame; [|exact HR]. intros z Hz.
  unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin).
  unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
  unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
  - unfold rtc_cells_img in Hc.
    repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y;
      first [ apply AGlow; unfold IMG_LO, STORE; lia
            | apply AGhigh; unfold MAP1, MAP1N, IMG_HI; lia
            | apply AGimg; [unfold IMG_LO, IMG_HI; lia | intros (_ & N1 & N2); unfold STORE, MAP1 in N1, N2; lia] ] |]).
    destruct Hc.
  - unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc. pose proof (geom_nums _ HG) as (F1 & F2 & _). rewrite FS_total_val in F2.
    repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y;
      first [ apply AGth; lia | apply AGctx; lia | apply AGdtls; lia | apply AGfs; rewrite FS_total_val; lia ] |]).
    destruct Hc.
Qed.

Lemma thread_inv_z : ltac2:(tb__ "0|0|
S4eVm;VGg;A2S4eVm';VGg;A2F_;").
Proof.
  intros [T1 T2]. split; [rewrite AGth by lia; exact T1|]. eapply present_agree; [|exact T2]. intros z Hz. apply AGth. lia.
Qed.

Lemma misc_inv_z : ltac2:(tb__ "0|0|
S48Vm;A1S48Vm';A1F_;").
Proof.
  intros (H1 & H2 & H3). split; [|split].
  - eapply cells_ok_frame; [|exact H1]. intros z Hz. unfold cells_footb in Hz.
    apply existsb_exists in Hz as (c & Hc & Hin). unfold in_cellb in Hin. apply andb_prop in Hin as [X Y].
    apply Z.leb_le in X. apply Z.ltb_lt in Y. unfold rtc_extra in Hc.
    destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn in X, Y; apply AGlow; unfold IMG_LO, STORE; lia.
  - intros z Hz. rewrite AGlow by (unfold IMG_LO, STORE; lia). exact (H2 z Hz).
  - intros z Hz. rewrite AGhigh by (unfold ERRNO_A, MAP1, MAP1N, IMG_HI in *; lia). exact (H3 z Hz).
Qed.

Lemma ia_inv_z : ltac2:(tb__ "0|0|
S10S10S0S2eS21R1A1S21R2A1A3S45Vm;R3A2S45Vm';R3A2F_;F_;FA';FA;").
Proof.
  intros A A' EI H. unfold ia_inv in *. rewrite EI. unfold IA_MAP1, IA_MAP1_SZ, IA_BEG, IA_END in *.
  assert (AG : forall z, 0xf2600 <= z < 0x180e8c -> m' z = m z) by (intros z Hz; apply AGlow; unfold IMG_LO, STORE; lia).
  rewrite !AG by lia. destruct H as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  destruct (aa_internal_inited A); destruct H4 as [H5 H6]; (split; [exact H5|]); intros z Hz; rewrite AG by lia; exact (H6 z Hz).
Qed.

Lemma class_repr_z : ltac2:(tb__ "0|0|
S10S10SfS18S1S5Z1R2A2S5R2Z1eA2A2S0S2eS1bR4A1S1bR5A1A3S0S2cS2fSfSfA2A1S16R5A1S16R6A1A3S0S2cS17A1S6cR6A1S6cR7A1A3S44Vm;VGg;R8R6R5A5S44Vm';VGg;R8R7R6A5F_;F_;F_;F_;F_;Fcs;Fc;FA';FA;").
Proof.
  intros A A' c cs Hc Hci Hlv Hq P4.
  pose proof (geom_nums Gg HG) as (_ & _ & _ & T1 & T2 & _ & _ & _ & _ & _ & S1 & S2 & S0 & TG).
  unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2.
  unfold class_repr in P4 |- *. rewrite Hci.
  set (ri := region_info (ag_spacebeg Gg) c) in *. set (fa := free_array (ag_spacebeg Gg) c) in *.
  assert (RI : ag_spacebeg Gg <= ri /\ ri + 128 <= ag_spacebeg Gg + 2 ^ 37 + 4096) by (unfold ri, region_info; rewrite kSpaceSize_val; unfold kRegionInfoStride; lia).
  set (rb := region_beg (ag_spacebeg Gg) c) in *.
  assert (RB : ag_spacebeg Gg <= rb /\ rb + 2 ^ 32 <= ag_spacebeg Gg + 2 ^ 37) by (unfold rb, region_beg, kRegionSize; lia).
  assert (FA : fa = rb + kUserSpaceSize) by (unfold fa, free_array, rb; reflexivity).
  unfold live_ids. rewrite Hlv, Hq.
  destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & C9 & PR & N7 & PU & PS & PE & ND & LV & CI & CN & TI10 & CV10 & MC10 & FC10).
  unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *. rewrite kSpaceSize_val in *.
  assert (CS : forall cc, rb <= c_addr cc -> c_addr cc + Z.of_nat (c_w cc) <= rb + 2 ^ 32 -> cell_ok m cc -> cell_ok m' cc).
  { intros cc H1 H2. apply cell_ok_sp; rewrite ?kSpaceSize_val; lia. }
  assert (CR : forall cc, ri <= c_addr cc -> c_addr cc + Z.of_nat (c_w cc) <= ri + 128 -> cell_ok m cc -> cell_ok m' cc).
  { intros cc H1 H2. apply cell_ok_sp; rewrite ?kSpaceSize_val; lia. }
  split; [apply CR; [cbn [c_addr]; unfold RI_mutex; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_mutex; lia | exact C1]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_num_freed; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_num_freed; lia | exact C2]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_mapped_free_array; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_mapped_free_array; lia | exact C3]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_allocated_user; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_allocated_user; lia | exact C4]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_allocated_meta; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_allocated_meta; lia | exact C5]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_mapped_user; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_mapped_user; lia | exact C6]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_mapped_meta; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_mapped_meta; lia | exact C7]|].
  split; [apply CR; [cbn [c_addr]; unfold RI_exhausted; lia | cbn [c_addr c_w Z.of_nat]; unfold RI_exhausted; lia | exact C8]|].
  split; [eapply present_agree; [|exact PRI]; intros z Hz; apply AGsp; unfold kRegionInfoStride in Hz; rewrite ?kSpaceSize_val; lia|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split.
  { intros i x Hi. assert (Li : (i < length (cs_free_array cs))%nat) by (apply nth_error_Some; rewrite Hi; discriminate). apply CS; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact (C9 i x Hi)]. }
  split; [eapply present_agree; [|exact PR]; intros z Hz; apply AGsp; rewrite ?kSpaceSize_val; lia|].
  split; [exact N7|].
  split; [eapply present_but_agree; [|exact PU]; intros z Hz _; apply AGsp; rewrite ?kSpaceSize_val; lia|].
  split; [eapply present_agree; [|exact PS]; intros z Hz; apply (AGsh rb (rb + cs_mapped_user cs)); lia|].
  split; [eapply present_agree; [|exact PE]; intros z Hz; apply AGth; lia|].
  split; [exact ND|]. split; [exact LV|].
  split.
  - intros Hx. destruct (CI Hx) as (D1 & D2 & D3 & D4 & D5).
    split; [apply cell_ok_th; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact D1]|].
    split; [apply cell_ok_th; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact D2]|].
    split; [apply cell_ok_th; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact D3]|]. split; [|exact D5].
    intros i x Hi. assert (Li : (i < length (cs_cache cs))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    pose proof (max_count_le c) as MC.
    apply cell_ok_th; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact (D4 i x Hi)].
  - split; [|exact (conj TI10 (conj CV10 (conj MC10 FC10)))].
    intros Hx. destruct (CN Hx) as [D1 D2]. split; [exact D1|]. eapply filled_agree; [|exact D2]. intros z Hz. apply AGth. lia.
Qed.

Lemma primary_repr_z : ltac2:(tb__ "0|1|
S10S10S0S14S11R2A1M0VGg;A3S0S14G0S11R3A1A3S0S2cS18A1S15R3A1S15R4A1A3S0S2eS1bR4A1S1bR5A1A3S0S2cS2fSfSfA2A1S16R5A1S16R6A1A3S0S2cS17A1S6cR6A1S6cR7A1A3S40Vm;R8A2S40Vm';R8A2F_;F_;F_;F_;F_;F_;F_;FA';FA;").
Proof.
  intros A A' EG Eg Ec Eci El Eq (P1 & P2 & P3 & P4). unfold primary_repr. rewrite Eg, Ec, EG in *.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. intros c Hc. apply (class_repr_z A A' c _ Hc Eci El Eq (P4 c Hc)).
Qed.

Lemma secondary_repr_z : ltac2:(tb__ "0|1|
S10S10S0S14S11R2A1VGg;A3S0S2cS12A1M0S13R3A1Vsecs;A3S0S14S11R3A1S11R4A1A3S0G0S13R4A1S13R5A1A3S0SfS22R5A1S22R6A1A3S0S2cS2fSfSfA2A1S16R6A1S16R7A1A3S41Vm;R8A2S41Vm';R8A2F_;F_;F_;F_;F_;F_;F_;FA';FA;").
Proof.
  intros A A' EG ESS Eg Es Ep El (S1 & SP & S2 & S3 & S4 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold secondary_repr. rewrite Eg, Es, Ep, El, EG, ESS in *.
  pose proof (topG_range Gg) as TGR.
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (nth_error_In _ _ Hi) as Hch. pose proof D10 as (X1 & X2 & X3 & _).
    assert (Li : (i < length secs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    split; [eapply (cell_ok_sec ch); [exact Hch | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; unfold PG in *; lia | exact D1]|].
    split; [eapply (cell_ok_sec ch); [exact Hch | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; unfold PG in *; lia | exact D2]|].
    split; [eapply (cell_ok_sec ch); [exact Hch | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; unfold PG in *; lia | exact D3]|].
    split; [eapply (cell_ok_sec ch); [exact Hch | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; unfold PG in *; lia | exact D4]|].
    split; [apply cell_ok_pab; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; unfold kPtrArrayReserve in *; lia | exact D5]|].
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [eapply present_but_agree; [|exact D13]; intros z Hz _; apply (AGsec ch); [exact Hch | lia]|].
    eapply present_agree; [|exact D14]. intros z Hz. apply (AGsh (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch)); lia. }
  split; [eapply present_agree; [|exact SP]; intros z Hz; apply AGpab; unfold kPtrArrayReserve in *; lia|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
  unfold SEC_INST in *.
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I1]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I2]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I3]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I4]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I5]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I6]|].
  split; [eapply present_agree; [|exact I7]; intros z Hz; apply AGlow; unfold IMG_LO, STORE; lia|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact I8]|].
  eapply present_agree; [|exact I9]; intros z Hz; apply AGlow; unfold IMG_LO, STORE; lia.
Qed.

Definition prim_okb (n : Z) : bool := ltac2:(tb__ "0|1|
S36S35S55Vn;A1A1S32ScZ1S57S5bVn;A1A1M0A2ScG0Z1eA2A2A2").
Lemma prim_okb_all : ltac2:(tb__ "0|1|
SfS1S5Z1M0R1A2S7R1S6G0Z10000A2A2A2S0S2eS72R2A1S30A3F_;Fn;").
Proof. intros n Hn. apply (forall_rangeZ_ok prim_okb 1 65536); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma round_up_ge8 : ltac2:(tb__ "0|0|
SfS5R1S5fR1Z8A2A2Fz;").
Proof. intros z. unfold round_up. pose proof (Z.div_mod (z + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (z + 8 - 1) 8 ltac:(lia)). lia. Qed.
Lemma primary_cls : ltac2:(tb__ "0|2|
SfS5Z1M0R1A2S0S2eS55R2A1S30A3S1S5G0S57S5bR3A1A1M1A2S5G1Z1eA2A2F_;F_;Fn;").
Proof.
  intros n Hn HP. destruct (Z_lt_le_dec n (1 + 65536)) as [L|L].
  - pose proof (prim_okb_all n ltac:(lia)) as H. unfold prim_okb in H. rewrite HP in H. cbn [negb orb] in H.
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  - exfalso. unfold is_primary, needed, kMaxSize, kChunkHeader2Size in HP. apply Z.leb_le in HP.
    pose proof (round_up_ge8 (Z.max n 16)). unfold rz in HP. rewrite Z.shiftl_mul_pow2 in HP by (unfold rz_log; repeat destruct (_ <=? _); lia).
    assert (0 < 2 ^ rz_log n) by (apply Z.pow_pos_nonneg; [lia | unfold rz_log; repeat destruct (_ <=? _); lia]). lia.
Qed.

Lemma Size_pos : ltac2:(tb__ "0|0|
SfS1S5Z1R1A2S5R1Z1eA2A2S7Z0S5aR2A1A2F_;Fc;").
Proof. intros c Hc. pose proof (forall_rangeZ_ok (fun c => 0 <? Size c) 1 30 c ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(lia)) as H. apply Z.ltb_lt in H. exact H. Qed.

Lemma prim_below_in_space : ltac2:(tb__ "0|1|
S10SfSfSfSfS40Vm;R5A2S0S14S11R6A1VGg;A3S1S5Z1R6A2S5R6Z1eA2A2S5S5cS19VGg;A1M0R7A2S8R6S54R5A1A2A2S5S6S8S8R7S54R6A1A2S5cG0R8A2A2S5aR8A1A2S28S49S18S15R9A1R8S29A4A1A2S1S5S8R8S54R7A1A2R6A2S7R6R8A2A2S1S5G0R7A2S7R7S6S6G0S53A2Z1000A2A2A2F_;F_;F_;F_;F_;F_;Fz;Fn;Fu;Fc;FA;").
Proof.
  intros A c u n z (_ & _ & _ & P4) EG Hc R1 R2 Hz. rewrite EG in P4.
  destruct (P4 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _).
  pose proof (rz_bound n). unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *. rewrite kSpaceSize_val.
  unfold region_beg, kRegionSize in R1, R2 |- *.
  pose proof (Size_pos c Hc). nia.
Qed.

Lemma alloc_magic_ok_z : ltac2:(tb__ "0|0|
SfSfSfS1S5S8R3S54R2A1A2R1A2S7R1R3A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;S43Vm;R3R2A3S43Vm';R4R3A3F_;F_;Fn;Fu;").
Proof.
  intros u n AG [H|[H1 H2]]; [left; exact H|right]. pose proof (rz_bound n) as RZ.
  split; (eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply AG; lia|assumption]).
Qed.

Lemma div8_superadd : ltac2:(tb__ "0|2|
SfSfS5Z0R2A2M0G0S5S6SaR4Z8M1A2SaR3G1A2A2SaS6R4R3A2G1A2A2F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. apply Z.div_le_lower_bound; [lia|].
  pose proof (Z.mul_div_le a 8 ltac:(lia)). pose proof (Z.mul_div_le b 8 ltac:(lia)). lia.
Qed.

Lemma chunk_zone : ltac2:(tb__ "0|4|
S10SfSfS0S14S11R3A1VGg;A3S0S2cS12A1S13R4A1Vsecs;A3S40Vm;R5A2S41Vm;R6A2S5S6S51Z800M0A2R6A2S5Z1R6A2S0S2eS55R7A1S30A3S57S5bR8A1A1SfS5cS19VGg;A1R1A2SfS1S5R1S8RbS54RaA1A2M1A2S1S0SfSeS8G1R1A2M2S5aR2A1M3A2Z0A3S5S6G2G3A2S28S49S18S15RcA1R2S29A4A1A2A2A2Trb;Tc;F_;S0S2eS55R8A1S33A3S4S12S12S1S6dS12R1S13RcA1A3S1S0SfRbS6S6S1aR1A1S60A2G0A2A3S0SfS2bR1A1S6S5fRaZ8A2Z1000A2A3A2A2Lch;A2F_;S1SfS1S5G1R1A2S7R1RbA2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;S7S6S6RaR9A2Z7A2SbZ2Z2fA2A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fn;Fu;FA;").
Proof.
  intros A u n EG ES HP HS Hu Hn QP QS. pose proof (rz_bound n) as RZ. pose proof (topG_range Gg) as TGR.
  pose proof (geom_nums Gg HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2.
  destruct (is_primary n) eqn:EP.
  - destruct (QP eq_refl) as (R1 & R2 & R3). pose proof (primary_cls n ltac:(lia) EP) as Hc.
    destruct HP as (_ & _ & _ & P4). rewrite EG in P4. destruct (P4 _ Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _).
    pose proof (Size_pos _ Hc) as SP. unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *. unfold region_beg, kRegionSize in R1, R3.
    assert (NS : n <= 65536).
    { unfold is_primary, needed, kMaxSize, kChunkHeader2Size in EP. apply Z.leb_le in EP. pose proof (round_up_ge8 (Z.max n 16)). lia. }
    split; [|nia]. intros z Hz. apply AGsp. rewrite kSpaceSize_val. nia.
  - destruct (QS eq_refl) as (ch & Hch & Eu & Esz). rewrite ES in Hch.
    destruct HS as (HS1 & _). rewrite ES, EG in HS1. destruct (In_nth_error _ _ Hch) as (i & Hi).
    destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & _ & _ & D11 & D12 & _).
    pose proof (round_up_ge8 n). unfold PG in *.
    split; [|lia]. intros z Hz. apply (AGsec ch); [exact Hch | lia].
Qed.

Lemma q_item_ok_z : ltac2:(tb__ "0|1|
S10S10S2fSfSfA2S0S14S11R3A1VGg;A3S0S2cS12A1M0S13R4A1Vsecs;A3S0S14S11R4A1S11R5A1A3S0S2cS18A1S15R5A1S15R6A1A3S0G0S13R6A1S13R7A1A3S40Vm;R8A2S41Vm;R9A2S4aVm;RaR8A3S4aVm';RaR9A3F_;F_;F_;F_;F_;F_;F_;F_;Fit;FA';FA;").
Proof.
  intros A A' it EG ES Eg Ec Es HP HS HQ. unfold q_item_ok in HQ |- *. cbn zeta in HQ |- *. rewrite Eg, Ec, Es.
  destruct HQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  pose proof (rz_bound (snd it)) as RZ.
  destruct (chunk_zone A (fst it) (snd it) EG ES HP HS Q1 Q2 ltac:(intros E; rewrite <- EG; exact (Q9 E)) Q10) as [BEL UB].
  split; [exact Q1|]. split; [exact Q2|].
  split; [rewrite BEL by lia; exact Q3|].
  split; [eapply present_agree; [|exact Q4]; intros z Hz; apply BEL; lia|].
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BEL; lia|exact Q5]|].
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BEL; lia|exact Q6]|].
  split; [eapply present_agree; [|exact Q7]; intros z Hz; apply BEL; lia|].
  split; [eapply alloc_magic_ok_z; [exact BEL | exact Q8]|].
  split; [exact Q9|]. split; [exact Q10|].
  eapply present_agree; [|exact Q11]. intros z Hz. unfold IMG_HI in Q1.
  apply (AGsh (fst it) (fst it + snd it + 7)); [lia | exact UB |].
  pose proof (div8_superadd (fst it) (snd it + 7) ltac:(lia) ltac:(lia)). unfold Sh in *. rewrite <- Z.add_assoc. lia.
Qed.

Lemma batch_in_space : ltac2:(tb__ "0|2|
S10S17SfS0S14S11R3A1VGg;A3S40Vm;R4A2S42Vm;R5R4A3S1S5S2aR5A1M0R4A2S7R4S6G0S63A2A2A2S1S5S19VGg;A1M1R5A2S7R5S6S6G1S53A2Z1000A2A2A2F_;F_;F_;F_;Fz;Fb;FA;").
Proof.
  intros A b z EG (_ & _ & _ & P4) (_ & _ & _ & _ & _ & _ & _ & (x & Ex & X0 & _ & XB)) Hz. rewrite EG in P4, Ex.
  destruct (P4 24 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _).
  unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *. unfold region_beg, kRegionSize in Ex. rewrite kSpaceSize_val. lia.
Qed.

Lemma batch_repr_z : ltac2:(tb__ "0|1|
S10S10S17S0S14S11R3A1VGg;A3S0S2cS12A1M0S13R4A1Vsecs;A3S0S14S11R4A1S11R5A1A3S0S2cS18A1S15R5A1S15R6A1A3S0G0S13R6A1S13R7A1A3S40Vm;R8A2S41Vm;R9A2S42Vm;RaR8A3S42Vm';RaR9A3F_;F_;F_;F_;F_;F_;F_;F_;Fb;FA';FA;").
Proof.
  intros A A' b EG ES Eg Ec Es HP HS HB. pose proof HB as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
  assert (BS : forall z, qb_addr b <= z < qb_addr b + kQuarantineBatchSize -> m' z = m z).
  { intros z Hz. apply AGsp. exact (batch_in_space A b z EG HP HB Hz). }
  unfold batch_repr. rewrite Eg, Ec. unfold kQuarantineBatchSize, kQuarantineBatchCount in *.
  split; [exact B0|].
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BS; lia | exact B1]|].
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BS; lia | exact B2]|].
  split; [exact B3|]. split; [exact B4|].
  split; [eapply present_agree; [|exact B5]; intros z Hz; apply BS; lia|].
  split; [|exact B7].
  intros i it Hi. destruct (B6 i it Hi) as [I1 I2]. assert (Li : (i < length (qb_items b))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BS; lia | exact I1]|].
  exact (q_item_ok_z A A' it EG ES Eg Ec Es HP HS I2).
Qed.

Lemma qlinks_z : ltac2:(tb__ "0|0|
S10S2cS17A1S0S14S11R2A1VGg;A3S40Vm;R3A2S71S17S42Vm;R4A2R3A3S4cVm;R4A2S4cVm';R5A2F_;F_;F_;F_;Fl;FA;").
Proof.
  intros A l EG HP. induction l as [|b r IH]; intros HF H; [exact I|]. cbn in H |- *. destruct H as [H1 H2].
  apply Forall_cons_iff in HF as [Hb Hr].
  split; [|exact (IH Hr H2)].
  eapply (cell_ok_agree m m'); [|exact H1]. cbn [c_addr c_w]. intros k Hk. apply AGsp. apply (batch_in_space A b _ EG HP Hb). unfold kQuarantineBatchSize. lia.
Qed.

Lemma qhdr_repr_z : ltac2:(tb__ "0|0|
SfS2cS17A1SfS1S5R3R1A2S7R1S6R3Z20A2A2A2S0S2dS37Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;S4bVm;R3R2A3S4bVm';R4R3A3F_;F_;Fl;Fhdr;").
Proof.
  intros hdr l AG (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply AG; lia | exact Q1]|].
  split; [intros Hl; destruct (Q2 Hl) as [X Y]; split; (eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply AG; lia | assumption])|].
  split; [eapply present_agree; [|exact Q3]; intros z Hz; apply AG; lia|].
  eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply AG; lia | exact Q4].
Qed.

Lemma quarantine_repr_z : ltac2:(tb__ "0|2|
S10S10S0S14S11R2A1VGg;A3S0S2cS12A1M0S13R3A1Vsecs;A3S0S14S11R3A1S11R4A1A3S0S2cS18A1S15R4A1S15R5A1A3S0G0S13R5A1S13R6A1A3S0S2cS17A1M1S24R6A1S24R7A1A3S0G1S23R7A1S23R8A1A3S40Vm;R9A2S41Vm;RaA2S4dVm;RbA2S4dVm';RbA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;").
Proof.
  intros A A' EG ES Eg Ec Es E1 E2 HP HS (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). unfold quarantine_repr. rewrite Eg, E1, E2.
  pose proof (proj1 (Forall_app _ _ _) Q1) as [HB1 HB2].
  split; [apply Forall_forall; intros b Hb; apply (batch_repr_z A A' b EG ES Eg Ec Es HP HS); exact (proj1 (Forall_forall _ _) Q1 b Hb)|].
  split; [exact (qlinks_z A _ EG HP HB1 Q2)|]. split; [exact (qlinks_z A _ EG HP HB2 Q3)|].
  split; [apply qhdr_repr_z; [intros z Hz; apply AGth; rewrite EG in Hz; lia | exact Q4]|].
  unfold QG in *.
  split; [apply qhdr_repr_z; [intros z Hz; apply AGlow; unfold IMG_LO, STORE; lia | exact Q5]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact Q6]|].
  split; [apply cell_ok_low; [cbn [c_addr]; unfold IMG_LO; lia | cbn [c_addr c_w Z.of_nat]; unfold STORE; lia | exact Q7]|].
  split; [exact Q8|]. exact Q9.
Qed.

Lemma live_block_repr_z : ltac2:(tb__ "0|0|
S10S10S0S14S11R2A1VGg;A3S0S2cS12A1S13R3A1Vsecs;A3S0S2cS2fSfSfA2A1S16R3A1S16R4A1A3S50R5A1S46R6A1S40Vm;R7A2S41Vm;R8A2S47Vm;R9A2S47Vm';R9A2F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;").
Proof.
  intros A A' EG ES El Hsep HI3 HP HS Hlive b n Hin. rewrite El in Hin.
  destruct (Hlive b n Hin) as (L1 & L2 & L3 & L4 & L5 & L6). destruct (Hsep b n Hin) as (S1 & S2 & S3 & _).
  pose proof (rz_bound n) as RZ. destruct HI3 as (_ & LIV3 & _).
  assert (CZ : (forall z, b - rz n <= z < b -> m' z = m z) /\ b + n + 7 < 2 ^ 47).
  { apply (chunk_zone A b n EG ES HP HS ltac:(unfold IMG_HI in *; lia) ltac:(lia)).
    - intros EP. destruct HP as (_ & _ & _ & P4). rewrite EG in P4.
      pose proof (primary_cls n ltac:(lia) EP) as Hc. pose proof (P4 _ Hc) as X. cbn zeta.
      destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
      exact (LV b n Hin EP eq_refl).
    - intros EP. destruct (LIV3 b n Hin) as [X|X]; [rewrite EP in X; discriminate X | exact X]. }
  destruct CZ as [BEL UB].
  split; [rewrite BEL by lia; exact L1|].
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BEL; lia | exact L2]|].
  split; [eapply (cell_ok_agree m m'); [cbn [c_addr c_w]; intros k Hk; apply BEL; lia | exact L3]|].
  split.
  - destruct L4 as [L4a L4b]. unfold IMG_HI in *. pose proof (div8_superadd b (n + 7) ltac:(lia) ltac:(lia)) as D8.
    pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono n (n + 7) 8 ltac:(lia) ltac:(lia)).
    split.
    + intros g Hg. rewrite (AGsh b (b + n + 7)); [exact (L4a g Hg) | lia | exact UB | unfold Sh in *; rewrite <- Z.add_assoc; lia].
    + intros Hn. rewrite (AGsh b (b + n + 7)); [exact (L4b Hn) | lia | exact UB | unfold Sh in *; rewrite <- Z.add_assoc; lia].
  - split; [eapply alloc_magic_ok_z; [exact BEL | exact L5]|].
    destruct L6 as (t & Ht & Hm4). exists t. split; [rewrite BEL by lia; exact Ht | exact Hm4].
Qed.
End Zones.

Section Frame.
Let segs : list Segment := segsA.

Lemma view_agree : ltac2:(tb__ "0|4|
S37Q40M0A1S2dS37Q8A1A1M1F_;M2G2SfS1S5Z0R1A2S7R1SbZ2Z40A2A2A2S0G1R3S38G0R2A2M3A1R4G3A1A3F_;S0G1S3eVsegs;R3R2A3S3eVsegs;R4R2A3A3F_;Fz;Ff';Ff;").
Proof.
  intros f f' z H. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
  - rewrite !view_in by lia. unfold rd_of. rewrite H by lia. reflexivity.
  - rewrite !view_out by lia. reflexivity.
  - rewrite !view_out by lia. reflexivity.
Qed.

Lemma zones_not_DFPw : ltac2:(tb__ "0|9|
S10SfS4fS11R2A1A1S46R3A1S34S12S0S2dS12A1S6eS12S13R6A1R2A3S31S12R1A2A3S61S20S11R7A1A1S1aR2A1S1dR2A1A3F_;Fch;Fi;S62S20S11R5A1M0A1S1cG0A1S56A3S11R6A1S14S2S1S1S5S52R6A2S7R6S51A2A2S3S70R6A1A1A2S2S1S5S19R1A1M1R6A2S7R6S6S6G1S53A2Z1000M2A2A2A2S2S1S5S1fR1A1M3R6A2S7R6S6G3G2A2A2A2S2S1S5S25R1A1M4R6A2S7R6S6G4G2A2A2A2S2S1S5S26R1A1M5R6A2S7R6S6G5G2A2A2A2S2S1S5S27R1A1M6R6A2S7R6S6G6S5dA2A2A2S2S1S5S1cR1A1M7R6A2S7R6S6G7S56A2A2A2S2S4S12S12S1S6dS12R1S13R8A1A3S1S5S1aR1A1M8R7A2S7R7S6G8S1dR1A1A2A2A2A2Lch;A2S2S1S5S59R6A2S7R6S58A2A2S5S20R1A1R6A2A2A2A2A2A2A2A2A2A2S3S66S1eR8A1R7A2A1F_;TG;F_;F_;F_;F_;Fz;FA;").
Proof.
  intros A z HG HI3 HSEC HPAB. cbn zeta. intros HZ HD. destruct HI3 as (_ & _ & _ & _ & DEP3 & _).
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1.
  pose proof (geom_bands _ HG) as (FB & TB & CB & DB & TI & CI & DI).
  pose proof (dyn_ok_big _ _ _ HPAB ltac:(unfold kPtrArrayReserve; lia)) as PB. destruct HPAB as [_ (_ & _ & P3 & _ & P5)].
  assert (BLK : forall b L, In (b, L) (dblocks (aa_depot A)) -> b <= z < b + L -> False).
  { intros b L Hb Hbz. destruct (DEP3 (b, L) Hb) as (DI' & ST & SC & SD & SF & SS & SP & SX). cbn [fst snd] in *.
    unfold sepZ in ST, SC, SD, SF, SS, SP. cbn [fst snd] in ST, SC, SD, SF, SS, SP.
    assert (HL : 0xf000 < L).
    { unfold dblocks in Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_map_iff in Hb as (x & E & _); injection E as <- <-; unfold NBSZ, FBSZ; lia. }
    pose proof (dyn_in_big _ _ _ DI' HL) as BI. destruct DI' as (_ & _ & W3 & _ & W5).
    destruct HZ as [[HZ ND]|[HZ|[HZ|[HZ|[HZ|[HZ|[HZ|[(ch & Hch & HZ)|[HZ|HZ]]]]]]]]];

      first [ clear - Hbz HZ BI; lia | clear - Hbz HZ ST; lia | clear - Hbz HZ SC; lia | clear - Hbz HZ SD; lia
            | clear - Hbz HZ SF; rewrite ?FS_total_val in *; lia | clear - Hbz HZ SS; lia | clear - Hbz HZ SP; lia | clear - Hbz HZ SP PB P3 P5; lia
            | clear - Hbz HZ W3 W5 BI; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; lia
            | pose proof (SX ch Hch) as X; unfold sepZ in X; cbn [fst snd] in X; clear - Hbz HZ X; lia
            | lia
            | pose proof (SX ch Hch) as X; unfold sepZ in X; cbn [fst snd] in X; lia
            | rewrite FS_total_val in *; lia
            | unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; lia ]. }
  destruct HD as [(Hs & N1 & N2)|[(b & Hb & Hbz)|(b & Hb & Hbz)]].
  - pose proof (dstat_img z Hs) as ZI. unfold IMG_LO, IMG_HI in ZI.
    destruct HZ as [[HZ ND]|[HZ|[HZ|[HZ|[HZ|[HZ|[HZ|[(ch & Hch & HZ)|[HZ|HZ]]]]]]]]].
    + apply ND. exact (conj Hs (conj N1 N2)).
    + unfold IMG_HI in *. lia.
    + unfold IMG_LO, IMG_HI in TI. lia.
    + unfold IMG_LO, IMG_HI in CI. lia.
    + unfold IMG_LO, IMG_HI in DI. lia.
    + unfold IMG_HI in F1. lia.
    + unfold IMG_HI in PB. lia.
    + destruct (In_nth_error _ _ Hch) as (i & Hi). pose proof (dyn_in_big _ _ _ (HSEC i ch Hi)) as CB'.
      destruct (HSEC i ch Hi) as (_ & X2 & _ & X4 & _). unfold IMG_LO, IMG_HI in X4, CB'. lia.
    + unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HZ. lia.
    + lia.
  - apply (BLK b NBSZ); [|exact Hbz]. unfold dblocks. apply in_or_app. left. apply in_map_iff. exists b. auto.
  - apply (BLK b FBSZ); [|exact Hbz]. unfold dblocks. apply in_or_app. right. apply in_map_iff. exists b. auto.
Qed.

Theorem AInvX_frameV : ltac2:(tb__ "0|0|
S10S6aS6aS2cS37Q40A1A1S6fS6bR5R4R2R1A4SfS3S66S1eR7A1R1A2A1S0S2dS37Q8A1A1S3eVsegs;S69R6A1R2A3S3eVsegs;S69R7A1R2A3A3F_;Fz;S6bR7R5R4R3A4F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp md HX AV. unfold AInvX in HX |- *. cbn zeta in HX |- *.
  set (G := aa_geom A) in *. set (m := view segsA (rm rho)) in *. set (m' := view segsA (rm rho')) in *.
  destruct HX as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (R1 & R2 & R3 & R4 & R5 & _ & R7 & R8 & R9).
  assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG G) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct R4 as [S1 _]. destruct (S1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG G) (ag_pab G) kPtrArrayReserve) by (destruct R4 as (_ & _ & _ & _ & S4 & _); exact S4).
  pose proof (fun z HZ => AV z (zones_not_DFPw A z HG HI3 HSEC HPAB HZ)) as ZN. cbn beta in ZN.

  set (mk := maskv (fs_footb G) m) in *. set (mk' := maskv (fs_footb G) m').
  assert (MK : forall z, m' z = m z -> mk' z = mk z) by (intros z E; unfold mk, mk', maskv; rewrite E; reflexivity).
  assert (Zimg : forall z, IMG_LO <= z < IMG_HI -> ~ dstatw z -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zsp : forall z, ag_spacebeg G <= z < ag_spacebeg G + kSpaceSize + 4096 -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zth : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zctx : forall z, ag_ctx G <= z < ag_ctx G + 0x1000 -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zdtls : forall z, ag_dtls G <= z < ag_dtls G + 0x1000 -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zfs : forall z, ag_fsb G <= z < ag_fsb G + FS_total -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zpab : forall z, ag_pab G <= z < ag_pab G + kPtrArrayReserve -> m' z = m z) by (intros; apply ZN; tauto).
  assert (Zsec : forall ch z, In ch (aa_sec A) -> sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch -> m' z = m z).
  { intros ch z Hch Hz. apply ZN. do 7 right. left. exists ch. exact (conj Hch Hz). }
  assert (Zband : forall z, SHADOW_BAND_LO <= z < SHADOW_BAND_HI -> m' z = m z) by (intros; apply ZN; tauto).
  split; [exact HG|].
  split.
  { eapply (rtc_inv_z G m m'); first [ eassumption | intros; first [ apply Zimg; assumption | apply Zth; assumption | apply Zctx; assumption | apply Zdtls; assumption | apply Zfs; assumption ] ]. }
  split.
  {
    replace (restrictv (fs_footb G) m') with (restrictv (fs_footb G) m); [exact HF|].
    apply functional_extensionality. intros z. unfold restrictv. destruct (fs_footb G z) eqn:E; [|reflexivity].
    symmetry. apply AV. intros HD. pose proof (fs_footb_DFP A z HG HI3 (DFPw_DFP _ _ HD)) as X. unfold G in E. rewrite X in E. discriminate E. }
  split; [|split; [exact HM | split; [exact HI3 | eapply bandtp_agree; [exact Zband | exact HB]]]].
  split; [exact R1|].

  Ltac zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband :=
    first [ eassumption | reflexivity
          | intros; apply MK; first [ apply Zsp; assumption | apply Zth; assumption | apply Zctx; assumption | apply Zdtls; assumption
                                    | apply Zfs; assumption | apply Zpab; assumption | apply Zband; assumption
                                    | eapply Zsec; eassumption | apply Zimg; assumption ] ].
  split; [eapply (live_block_repr_z G (aa_sec A) mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (primary_repr_z G mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (secondary_repr_z G (aa_sec A) mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (quarantine_repr_z G (aa_sec A) mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [exact I|].
  split; [eapply (ia_inv_z mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (thread_inv_z G mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  eapply (misc_inv_z mk mk'); zarg MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband.
Qed.

Theorem AInvX_frameD : ltac2:(tb__ "0|2|
S10S6aS6aS2cS37Q40M0A1M1A1S6fS6bR5R4R2R1A4G1S3S66S1eR7A1S39G0R1A2A2A1S0S2dS37Q8A1A1S69R6R2A2S69R7R2A2A3F_;Fa;S6bR7R5R4R3A4F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp md HX Hrm. apply (AInvX_frameV A rho rho' tp md HX).
  intros z Hz. apply view_agree. intros Hr. apply Hrm. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64%N) with (2 ^ 64). rewrite Z.mod_small by exact Hr. exact Hz.
Qed.
End Frame.
End InvFoot.

