(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "prod"; "app"; "false"; "list"; "bool"; "andb"; "true"; "None"; "length"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "sprop"; "SVar"; "SAlu"; "SPUle"; "ss_objs"; "mkSS"; "ss_facts"; "cell"; "SPBranch"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "sstate"; "SPAlign"; "SPNot"; "ss_pc"; "FcsrFrm0"; "ss_lenient"; "ss_next"; "c_off"; "mkObj"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "sv_eqb"; "ob_cells"; "c_width"; "odefault"; "DUnknown"; "SAluW"; "mkCell"; "tfact"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "add"; "vF"; "runA"; "NXD"; "RETPC"; "extN"; "vSt"; "vD"; "vNB"; "O_trD"; "v12"; "vB"; "vM"; "vS"; "F_D"; "O_bd"; "O_slotN"; "O_stc"; "PCE2"; "RT_D"; "bd_addr"; "idN"; "vP"; "vW"; "CSDFLAG"; "DIEGATE"; "DPMCELL"; "MLIMCELL"; "O_tf"; "PCJ"; "upd"; "EB"; "EFf"; "F_N"; "F_e2"; "F_f"; "F_n"; "F_nb"; "F_tw"; "Jh"; "NBh"; "NPRE"; "O_fr"; "O_nid"; "O_nn"; "O_tw"; "bd1_addr"; "carved4b"; "find_ru"; "node_addr"; "post_ru"; "prune0"; "vHS"; "vL"; "vN"; "ALLOCSP"; "C1f"; "DEPTH_D"; "DUMMY"; "E2h"; "FXE"; "F_NZ"; "F_S"; "F_a"; "F_af"; "F_d"; "F_dj"; "F_f2"; "FindNZ"; "FindZ"; "I3"; "I4"; "NX1"; "NXP"; "O_alloc"; "O_bdM"; "O_die"; "O_dpm"; "O_flag"; "O_frN"; "O_mlim"; "O_mtM"; "O_mu"; "O_nh"; "O_nl"; "O_nnE"; "O_pg"; "O_slot"; "O_stb"; "O_stb1"; "O_stcM"; "PACKOFF"; "PreD1"; "T1"; "dropo"; "e2h_ru"; "fr_addr"; "jh_ru"; "leaf"; "mkC1"; "mkC1R"; "mkCONT"; "mkFAIL"; "mkFAILf"; "mkFindB"; "mkI3b"; "mkI5d"; "mkI5e2"; "mkI5f"; "mkIn"; "mkOK"; "mkOKf"; "nbh_ru"; "nn_addr"; "objsXE"; "prune_cells"; "ruT"; "run_nz"; "set_cell0"; "set_cell_lit"; "slotN_addr"; "slot_addr"; "stc_addr"; "vAL"; "vH"; "vID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "leafA"; "la_state"; "axst"; "entailsA"; "mkLeafA"; "sym_runA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "eqb"; "mul"; "leb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SRL"; "ALU_SLL"; "BC_EQ"; "ALU_AND"; "BC_NE"; "aluop"; "mulop"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "STORE"; "NIDS"; "NODESMU"; "DEPOT"; "MAP1"; "NBSZ"; "FBSZ"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "mkA"; "A_globals"; "stack_win"; "pre_facts"; "@Corelib.Lists.ListDef"; "firstn"; "nth"; "map"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "ENOMEM"; "errno_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "mmap_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@stdpp.bitvector.definitions"; "bv_unsigned";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.Lists.List"; "filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SysCallA GlueA GlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Definition DEPTH_D : Z := 1536.
Definition SZMAX : Z := 10.
Definition SZMAXT : Z := 30.

Definition CSDFLAG : Z := 0x17fcd8.
Definition PGCELL : Z := 0x17db60.
Definition DIEGATE : Z := 0x17fbdc.
Definition RETPC : Z := 0x7ec58.
Definition NPRE : positive := 160%positive.
Definition NXD : positive := 260%positive.
Definition NXP : positive := 210%positive.
Definition NX1 : positive := 230%positive.

Definition add (a b : sv) : sv := SAlu ALU_ADD a b.
Definition v12 := SVar 12.
Definition vW := SVar 170. Definition vP := SVar 171. Definition vB := SVar 172. Definition vH := SVar 173. Definition vL := SVar 174.
Definition vS := SVar 175. Definition vN := SVar 177. Definition vNB := SVar 178. Definition vF := SVar 179. Definition vD := SVar 180.
Definition vSt := SVar 181. Definition vHS := SVar 182. Definition vID := SVar 185.

Definition DUMMY : leafA := ltac2:(tb__ "0|1|
SbbSd8S16Z0S3SeA1M0G0S22SbSeA1S3SfA1S3S11A1S3aS6A9S3S4SeSeA2A1A2Se8A2").
Definition leaf (i : nat) (l : list leafA) : axst := ltac2:(tb__ "0|0|
Sb8SddSb7Vi;Vl;S71A4A1").
Definition runA (fuel : nat) (cuts : list Z) (A : axst) : list leafA := ltac2:(tb__ "0|1|
SdS7Sb7A1M0A1G0Lx;SbcSeaVfuel;Vcuts;VA;SaA5G0R1Ll;S3Sb7A1Xdx2").

Definition upd (E : axst) (pc : Z) (ru : list (nat * sv)) (objs : list sobj) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
Sb5VE;A1S1eSb6VE;S16Vpc;ScbS1cR1A1Vru;A2S1bR1A1S1aR1A1S1dR1A1S5SfS15R1A1Vobjs;A3S5S11S17R1A1Vfacts;A3S3aS6A9A2TS;").

Definition extN (A : axst) (objs : list sobj) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
Sb5VA;A1S1eSb6VA;S16S21R1A1S1cR1A1S1bR1A1S1aR1A1S1dR1A1S5SfS15R1A1Vobjs;A3S5S11S17R1A1Vfacts;A3S3aS23R1A1A9A2TS;").

Definition dropo (E : axst) (k : nat) : axst := ltac2:(tb__ "0|1|
Sb5VE;A1S1eSb6VE;S16S21R1A1S1cR1A1S1bR1A1S1aR1A1S1dR1A1SdcSfSd5ScSfS15R1A1M0A2Vk;A2G0A3S17R1A1S24R1A1S23R1A1A9A2TS;").
Definition nocells (o : sobj) : sobj := ltac2:(tb__ "0|0|
S26S27Vo;A1S2aVo;A1S29Vo;A1S3S18A1S28Vo;A1A5").

Definition O_trD : sobj := ltac2:(tb__ "0|0|
S26S41S10Z0A1S10Z7f8A1S3S18A1S2fA5").
Definition O_flag : sobj := ltac2:(tb__ "0|3|
S36S10Z0A1M0S4fSbdS4fZ4A2S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1S4fU4A4G0A4S3G2A1A3A4").
Definition O_pg : sobj := O_pgb.
Definition O_die : sobj := ltac2:(tb__ "0|3|
S36S10Z0A1M0S50SbdS50Z4A2S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1S50U4A4G0A4S3G2A1A3A4").
Definition DPMCELL : Z := 0x17fcec.
Definition MLIMCELL : Z := 0x17fc78.
Definition O_dpm : sobj := ltac2:(tb__ "0|3|
S36S10Z0A1M0S51SbdS51Z1A2S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1S51U1A4G0A4S3G2A1A3A4").
Definition O_mlim : sobj := ltac2:(tb__ "0|3|
S36S10Z0A1M0S52SbdS52Z8A2S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1S52U8A4G0A4S3G2A1A3A4").
Definition RT_D : list sobj := ltac2:(tb__ "0|0|
S0SfS85S0SfS8dS0SfS83S0SfS84S0SfS87S3SfA1A3A3A3A3A3").
Definition F_D : list sprop := ltac2:(tb__ "0|0|
S5S11SdbS70A1S0S11S1fPcZ3A2S0S11S14S10Z7fff7f800000A1S41A2S0S11S14S41S10SbfSbeZ2Z40A2Z840A2A1A2S3S11A1A3A3A3A3").
Definition PreD (sz : Z) : axst := ltac2:(tb__ "0|1|
Sd8S16Z7e9e4ScbScdS0S4S1SeA2M0S2S1SeUaS41A4S0G0S2S1SeUbS10Vsz;A1A4S3G0A1A3A3A2SccS22SbSeA1S5SfS0SfSdaS0SfS40S3SfA1A3A3S5SfSd9S4aA3A3S45S60S6A9S3S4SeSeA2A1A2").

Definition PreD1 (sz : Z) : axst := ltac2:(tb__ "0|1|
Sd8S16Z7e9e4ScbScdS0S4S1SeA2M0S2S1SeUaS41A4S0G0S2S1SeUbS10Vsz;A1A4S3G0A1A3A3A2SccS22SbSeA1S5SfS0SfSdaS0SfS40S3SfA1A3A3S5SfSd9S4aA3A3S45S7fS6A9S3S4SeSeA2A1A2").

Definition post_ru : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S1SeA2M0S2S1SeU1S12PbA1A4S0G0S2S1SeU2S12PaA1A4S0G0S2S1SeU8S12P1cA1A4S0G0S2S1SeU9S12P1dA1A4S0G0S2S1SeUaSb4A4S0G0S2S1SeU12S12P26A1A4S0G0S2S1SeU13S12P27A1A4S0G0S2S1SeU14S12P28A1A4S0G0S2S1SeU15S12P29A1A4S0G0S2S1SeU16S12P2aA1A4S0G0S2S1SeU17S12P2bA1A4S0G0S2S1SeU18S12P2cA1A4S0G0S2S1SeU19S12P2dA1A4S0G0S2S1SeU1aS12P2eA1A4S0G0S2S1SeU1bS12P2fA1A4S0G0S2S1SeU7S12Pc4A1A4S0G0S2S1SeU11S12PbcA1A4S0G0S2S1SeU1cS12Pc7A1A4S0G0S2S1SeU1dS12P31A1A4S0G0S2S1SeU1eS12P32A1A4S0G0S2S1SeU1fS12P33A1A4S0G0S2S1SeU5S12PbaA1A4S0G0S2S1SeU6S12PbbA1A4S0G0S2S1SeUbS12PbdA1A4S0G0S2S1SeUcS12PbeA1A4S0G0S2S1SeUdS12PbfA1A4S0G0S2S1SeUeS12Pc0A1A4S0G0S2S1SeUfS12Pc1A1A4S0G0S2S1SeU10S12Pc2A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition PostD (sz : Z) : axst := ltac2:(tb__ "0|0|
Sd8S16S3bScbScdS69A2SccS22SbSeA1S5SfS0SfSdaS0SfS40S3SfA1A3A3S5SfSd9S4aA3A3S45S80S6A9S3S4SeSeA2A1A2").

Definition F_tw : list sprop := ltac2:(tb__ "0|2|
S0S11S14S4eS10SbfSbeZ2M0Z1fA2Z1A2A1A2S0S11S1fPabG0A2S0S11S14S10Sd1A1S4dA2S0S11S14S4dS10SbfSbdSd1Sc1Z4M1SbeG0Z14A2A2A2G1A2A1A2S3S11A1A3A3A3A3").
Definition O_tw (w : sv) : sobj := ltac2:(tb__ "0|3|
S36S4dZ0M0Z4S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U4A4Vw;A4S3G2A1A3A4").
Definition ruT : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S1SeA2M0S2S1SeUaS12Pb7A1A4S0G0S2S1SeU12S4dA4S0G0S2S1SeU13S6bA4S3G0A1A3A3A3").
Definition mkT1 (E1 : axst) : axst := ltac2:(tb__ "0|0|
S55VE1;Z7eb04SabS0SfS64S4eA1S3SfA1A3S5dA5").

Definition F_S : list sprop := ltac2:(tb__ "0|0|
S0S11S14S44S10SbfSbeZ2Z1fA2Z1A2A1A2S3S11A1A3").
Definition find_ru (cur : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S1SeA2M0S2S1SeUaS12Pb0A1A4S0G0S2S1SeUbVcur;A4S0G0S2S1SeUcS12Pb8A1A4S0G0S2S1SeU19S4eA4S3G0A1A3A3A3A3").
Definition mkFindB (L2 : axst) : axst := ltac2:(tb__ "0|0|
S55VL2;Z7eb24S67S44A1S3SfA1S75A5").
Definition slot_addr : sv := ltac2:(tb__ "0|0|
S37S13Sc4S30Sc3S44S10Z10A1A3S10Z3A1A3S10Sd2A1A2").
Definition node_addr : sv := ltac2:(tb__ "0|0|
S37S42S13Sc4S13Sc6S44S10ZffffA1A3S10Z4A1A3A2").
Definition O_slot : sobj := ltac2:(tb__ "0|3|
S36Sb0Z0M0Z8S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U8A4S42A4S3G2A1A3A4").
Definition O_nh : sobj := ltac2:(tb__ "0|3|
S36S68Z0M0Z8S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U8A4Sb3A4S3G2A1A3A4").
Definition O_nl : sobj := ltac2:(tb__ "0|3|
S36S68Z8M0ZcS0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U4A4S6cA4S3G2A1A3A4").
Definition F_NZ : list sprop := ltac2:(tb__ "0|1|
S0S11S20S19Sc5S44S10Z0A1M0A3A1S0S11S20S19Sc5S42G0A3A1S0S11S1fPacZ4A2S0S11S14S10Sd7A1S42A2S0S11S14S42S10Z7fffff800000A1A2S0S11S14S6cS10SbfSbeZ2Z1fA2Z1A2A1A2S3S11A1A3A3A3A3A3A3").
Definition mkFindNZ (L2 : axst) : axst := ltac2:(tb__ "0|0|
S3cS9fVL2;A1S0SfS8eS0SfS8aS0SfS8bS3SfA1A3A3A3S74A3").
Definition O_nid (v : sv) : sobj := ltac2:(tb__ "0|2|
S36S10Z0A1ScfSbdScfZ4A2S0S4S4S33S1A2M0SeA2M1S2G0SeS2S33S1ScfU4A4Vv;A4S3G1A1A3A4").
Definition F_N : list sprop := ltac2:(tb__ "0|1|
S0S11S14S6dS10SbfSbeZ2M0Z1fA2G0A2A1A2S3S11A1A3").
Definition mkFindZ (L2 : axst) : axst := ltac2:(tb__ "0|0|
S55VL2;Z7eb24S67S10Z0A1A1S0SfS62S6dA1S3SfA1A3S58A5").

Definition mkCONT (C : axst) : axst := dropo C 3.

Definition idN : sv := add vN (SLit 1).
Definition slotN_addr : sv := ltac2:(tb__ "0|0|
S37S13Sc4S13Sc3S4cS10Z10A1A3S10Z3A1A3S10Sd2A1A2").
Definition O_slotN (v : sv) : sobj := ltac2:(tb__ "0|3|
S36SafZ0M0Z8S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U8A4Vv;A4S3G2A1A3A4").
Definition F_nb : list sprop := ltac2:(tb__ "0|0|
S0S11S20S19Sc5S3fS10Z0A1A3A1S0S11S1fPb2ZcA2S0S11S14S10Sd7A1S3fA2S0S11S14S3fS10Z7fffff800000A1A2S3S11A1A3A3A3A3").
Definition mkI4 (I3 : axst) : axst := ltac2:(tb__ "0|0|
S3cVI3;S0SfS47S3fA1S3SfA1A3S5cA3").

Definition nbh_ru : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S1SeA2M0S2S1SeU1S12Pc8A1A4S0G0S2S1SeUbS12Pc9A1A4S0G0S2S1SeUcS12PcaA1A4S0G0S2S1SeUdS12PcbA1A4S0G0S2S1SeUeS12PccA1A4S0G0S2S1SeUfS12PcdA1A4S0G0S2S1SeU11S12PbcA1A4S3G0A1A3A3A3A3A3A3A3").

Definition prune_cells (lo : Z) (o : sobj) : sobj := ltac2:(tb__ "0|3|
S26S27Vo;A1S2aVo;A1S29Vo;A1SebS18S18SeS8Lx;S25R1A1S33Sc2Vlo;R1A2Lz;S34SaLi;Sc8SeSeSaLb;La;M0Lop;M1G1Sc9G0Lop;M2G2S8S35SeSaLa;Lw;Lsgn;S34SeS33SaLk;Li;Ll;Xex8Lc;S2cVo;A1A3S28Vo;A1A5").
Definition prune0 (lo : Z) (objs : list sobj) : list sobj := ltac2:(tb__ "0|1|
S7SfA1M0G0Lobjs;Vobjs;S3SfA1SfG0S0SfSaaVlo;R2A2R1A3Lrest;Lo;X7x2").
Definition mkNBh (NB : axst) : axst := ltac2:(tb__ "0|0|
Sb5VNB;A1S1eSb6VNB;S16Z7ebecScbS1cR1A1Sa7A2S1bR1A1S1aR1A1S1dR1A1S6aN70S15R1A1A2S17R1A1S3aS6A9A2TS;").

Definition nn_addr : sv := ltac2:(tb__ "0|0|
S37S3fS13Sc4S13Sc6S4cS10ZffffA1A3S10Z4A1A3A2").
Definition bd_addr : sv := ltac2:(tb__ "0|0|
S37S13Sc4S13Sc3S38S10Z14A1A3S10Z4A1A3S10SceA1A2").
Definition fr_addr : sv := ltac2:(tb__ "0|0|
S37S3eS13Sc3S13Sc4S38S10Z2cA1A3S10Z29A1A3A2").
Definition stc_addr : sv := ltac2:(tb__ "0|0|
S37S13Sc6S13Sc3S38S10Z10A1A3S10Zfffffffffffffff0A1A3S10SceA1A2").
Definition O_nn : sobj := carved nn_addr 0 16 [].
Definition O_tf (v : sv) : sobj := ltac2:(tb__ "0|2|
S36S10Z0A1SceSbdSceZ8A2S0S4S4S33S1A2M0SeA2M1S2G0SeS2S33S1SceU8A4Vv;A4S3G1A1A3A4").
Definition O_bd (v : sv) : sobj := ltac2:(tb__ "0|3|
S36S4bZ10M0Z18S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U8A4Vv;A4S3G2A1A3A4").
Definition O_fr (sz : Z) : sobj := ltac2:(tb__ "0|0|
S36S97Z0Sc1Z8SbdVsz;Z1A2A2S3S4S4S33S1A2SeA2A1A4").
Definition O_stc (v : sv) : sobj := ltac2:(tb__ "0|3|
S36Sb1Z18M0Z1cS0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U4A4Vv;A4S3G2A1A3A4").

Definition O_mu : sobj := ltac2:(tb__ "0|3|
S36S10Z0A1M0Sd0SbdSd0Z4A2S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1Sd0U4A4G0A4S3G2A1A3A4").
Definition mkI3b (I3 : axst) : axst := ltac2:(tb__ "0|0|
S3cVI3;S0SfS47S10Z0A1A1S0SfS89S3SfA1A3A3S3S11A1A3").
Definition F_a : list sprop := ltac2:(tb__ "0|1|
S0S11S1fS3aZcA2S0S11S14S10Sd7A1S12S3aA1M0A2S0S11S14G0S10SbfZ7fffff800000Sd3A2A1A2S3S11A1A3A3A3").
Definition mkOK (EB : axst) : axst := ltac2:(tb__ "0|2|
Sd6Sb6VEB;Se2Sb5VEB;A1M0S12S24G0A1M1A1S5SfS15G0A1S0SfSe3G1Sd3A2S3SfA1A3A3Se5G1A1A4A2S5S11S17G0A1S76A3A2").
Definition F_f : list sprop := ltac2:(tb__ "0|0|
S0S11S20S19Sc5S13ScaS12PaA1S10Nc0A1A3S10Z0A1A3A1S3S11A1A3").
Definition mkFAIL (EB : axst) : axst := ltac2:(tb__ "0|0|
Sd6Se4VEB;S10Se6Q40Se1Se0A1A2A1A2S5S11S17Sb5VEB;A1A1S5aA3A2").
Definition mkNBj (NBb : axst) : axst := ltac2:(tb__ "0|0|
S95VNBb;U3A2Sb9Sb5R1A1S1eSb6R2S16S21R1A1S1cR1A1S1bR1A1S1aR1A1S1dR1A1S5SfS15R1A1S0SfS47S12S3aA1A1S3SfA1A3A3S5S11S17R1A1S3S11A1A3S24R1A1S23R1A1A9A2TS;TD;").

Definition PCJ : Z := 0x7c538.
Definition PCE2 : Z := 0x7c574.
Definition F_n (sz : Z) : list sprop := ltac2:(tb__ "0|3|
S0S11S14S38S10SbfSbeZ2M0Z20A2SbeG0Z14M1A2A2A1A2S0S11S20S19Sc7S13Sc3S38S10G1A1M2A3S13Sc3S37S38S10Vsz;A1A2G2A3A3A1S3S11A1A3A3").
Definition mkIn (sz : Z) (NB : axst) : axst := ltac2:(tb__ "0|0|
S3cVNB;S0SfS63S0SfS53S38A1S3SfA1A3A3S5bVsz;A1A3").

Definition jh_ru : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S1SeA2M0S2S1SeU6S12Pc8A1A4S0G0S2S1SeU7S12Pc4A1A4S0G0S2S1SeUeS12Pc9A1A4S0G0S2S1SeU10S12PcaA1A4S0G0S2S1SeU1cS12Pc7A1A4S3G0A1A3A3A3A3A3").
Definition set_cell_lit (off : Z) (v : sv) (o : sobj) : sobj := ltac2:(tb__ "0|3|
S26S27Vo;A1S2aVo;A1S29Vo;A1SdeS18S18S18SeS18Lx;S25R1A1S33S8S18L_;Sc0R1Voff;A2S31S25R2A1S2dR2A1Vv;A3R2X8x2Lz;S34R2Li;Sc8SeSeR4Lb;La;M0Lop;M1G1Sc9G0Lop;M2G2S8S35SeR4La;Lw;Lsgn;S34SeS33R4Lk;Li;Ll;Xex8Lc;S2cVo;A1A4S28Vo;A1A5").
Definition set_cell0 (off : Z) (v : sv) (objs : list sobj) : list sobj := ltac2:(tb__ "0|1|
S7SfA1M0G0Lobjs;Vobjs;S3SfA1SfG0S0SfSaeVoff;Vv;R2A3R1A3Lrest;Lo;X7x2").
Definition PACKOFF : Z := -136.
Definition mkJh (Js : axst) : axst := ltac2:(tb__ "0|0|
Sb5VJs;A1S1eSb6VJs;S16S54ScbS1cR1A1S98A2S1bR1A1S1aR1A1S1dR1A1SadS92S12PcbA1S15R1A1A3S17R1A1S3aS6A9A2TS;").

Definition F_e2 : list sprop := ltac2:(tb__ "0|0|
S0S11S20S19Sc5S3eS10Z0A1A3A1S0S11S1fPb4ZcA2S0S11S14S10Sd7A1S3eA2S0S11S14S3eS10Z7fffff800000A1A2S0S11S14S3dS10SbfSbeZ2Z20A2Z1A2A1A2S3S11A1A3A3A3A3A3").
Definition mkI5e2 (sz : Z) (J : axst) : axst := ltac2:(tb__ "0|0|
S3cVJ;S0SfS46S3eA1S0SfS61Vsz;A1S0SfS48S3dA1S3SfA1A3A3A3S59A3").

Definition e2h_ru : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S1SeA2M0S2S1SeU1S12PccA1A4S0G0S2S1SeUbS12PcdA1A4S0G0S2S1SeUcS12Pd0A1A4S0G0S2S1SeUdS12Pd1A1A4S0G0S2S1SeUeS12Pc9A1A4S0G0S2S1SeUfS12Pb8A1A4S3G0A1A3A3A3A3A3A3").
Definition ALLOCSP : Z := -224.
Definition mkE2h (E : axst) : axst := ltac2:(tb__ "0|0|
Sb5VE;A1S1eSb6VE;S16S49ScbS1cR1A1S96A2S1bR1A1S1aR1A1S1dR1A1S6aS6eS15R1A1A2S17R1A1S3aS6A9A2TS;").

Definition vM : sv := SVar 206.
Definition vAL : sv := SVar 207.
Definition O_alloc (v : sv) : sobj := ltac2:(tb__ "0|3|
S36S10Z0A1SbdSceZ8A2M0SbdSceZ10A2S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U8A4Vv;A4S3G2A1A3A4").
Definition O_bdM (v : sv) : sobj := ltac2:(tb__ "0|3|
S36S43Z10M0Z18S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U8A4Vv;A4S3G2A1A3A4").
Definition O_stcM (v : sv) : sobj := ltac2:(tb__ "0|3|
S36S43Z18M0Z1cS0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U4A4Vv;A4S3G2A1A3A4").
Definition O_mtM : sobj := ltac2:(tb__ "0|3|
S36S43Z1cM0Z20S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U4A4S10Z0A1A4S3G2A1A3A4").
Definition O_mtxZ : sobj := ltac2:(tb__ "0|4|
S36S4bZ1cM0Z20S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U1A4S10Z0A1M3A4S0G2S2G1SeS2S33S1Z1dU3A4G3A4S3G2A1A3A3A4").
Definition ZPG : sobj := zero_obj_at (SVar NXD).
Definition F_f2 : list sprop := ltac2:(tb__ "0|0|
S0S11S14S3dS10SbfSbeZ2Z20A2Z1A2A1A2S3S11A1A3").
Definition mkI5f (sz : Z) (J : axst) : axst := ltac2:(tb__ "0|0|
S3cVJ;S0SfS46S10Z0A1A1S0SfS48S3dA1S0SfS81Sb2A1S3SfA1A3A3A3S7aA3").
Definition mkC1R (C : axst) : axst := ltac2:(tb__ "0|3|
Sb5VC;A1S1eScSfS15R1A1A2S1Sb6VC;S16S21R2A1ScbS1cR2A1S0S4S1SeA2M0S2S1SeU8S37S43S10Z1cA1A2M1A4S0G0S2S1SeU9S37S43S10Z10A1A2A4S0G0S2S1SeUcG1A4S3G0A1A3A3A3A2S1bR2A1S1aR2A1S1dR2A1S5SfSdcSfSd5R1U3A2S15R2A1M2A3S0SfS82S10Z0A1A1S0SfS91S3dA1S0SfSddSfSd5R1U1A2G2S40A4S3SfA1A3A3A3A3S17R2A1S3aS23R2A1A9A2Tn;TS;").
Definition mkC1 (C : axst) : axst := ltac2:(tb__ "0|0|
S3cS9bVC;A1S0SfS88S3SfA1A3S0S11S1fPceZ3A2S3S11A1A3A3").
Definition F_af : list sprop := ltac2:(tb__ "0|2|
S0S11S1fS3aZcA2S0S11S14S10Sd7A1S12S3aA1M0A2S0S11S14G0S10SbfZ7fffff800000M1Sd4A2A1A2S0S11S20S19Sc5G0S10Z0A1A3A1S0S11S14G0S10G1A1A2S3S11A1A3A3A3A3A3").
Definition mkOKf (E : axst) : axst := ltac2:(tb__ "0|2|
Sd6Sb6VE;Se2Sb5VE;A1M0S12S24G0A1M1A1S15G0A1Se5G1A1A4A2S5S11S17G0A1S77A3A2").
Definition mkFAILf (E : axst) : axst := ltac2:(tb__ "0|0|
Sd6Se4VE;S10Se6Q40Se1Se0A1A2A1A2S5S11S17Sb5VE;A1A1S5aA3A2").

Definition O_frN (sz : Z) : sobj := ltac2:(tb__ "0|0|
S36S37S12S3aA1S13Sc3S13Sc4S38S10Z2cA1A3S10Z29A1A3A2Z0Sc1Z8SbdVsz;Z1A2A2S3S4S4S33S1A2SeA2A1A4").
Definition mkC3j (sz : Z) (C : axst) : axst := ltac2:(tb__ "0|0|
Sb5VC;A1S1eScSfS15R1A1A2S1Sb6VC;S16S21R2A1S1cR2A1S1bR2A1S1aR2A1S1dR2A1S5SfSdcSfSd5R1U4A2S15R2A1A3S0SfS46S12S3aA1A1S0SfS86Vsz;A1S0SfS48S3dA1S3SfA1A3A3A3A3S17R2A1S24R2A1S23R2A1A9A2Tn;TS;").

Definition bd1_addr (sz : Z) : sv := ltac2:(tb__ "0|0|
S37S13Sc4S13Sc3S37S38S10Vsz;A1A2S10Z14A1A3S10Z4A1A3S10SceA1A2").
Definition O_stb (v : sv) : sobj := ltac2:(tb__ "0|3|
S36S4bZ18M0Z1cS0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U4A4Vv;A4S3G2A1A3A4").
Definition O_stb1 (sz : Z) (v : sv) : sobj := ltac2:(tb__ "0|3|
S36S65Vsz;A1Z18M0Z1cS0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U4A4Vv;A4S3G2A1A3A4").
Definition F_d (sz : Z) : list sprop := ltac2:(tb__ "0|6|
S0S11S14S38S10SbfSbeZ2M0Z20A2M1SbeG0Z15A2A2A1A2S0S11S19Sc7S13Sc3S38S10Z14A1M2A3S13Sc3S37S38S10Vsz;A1A2G2A3A3S0S11S19Sc5S13Sc3S37S38S10SbdVsz;Z1M3A2M4A1A2G2A3S13Sc3S37S38S10SbdG4Vsz;A2A1A2G2A3A3S0S11S14S3dS10SbfG1G3A2A1M5A2S0S11S14S12Pc6A1G5A2S3S11A1A3A3A3A3A3").
Definition mkI5d (sz : Z) (NB : axst) : axst := ltac2:(tb__ "0|0|
S3cVNB;S0SfS63S0SfS53S38A1S0SfS8fS3dA1S0SfS90Vsz;S12Pc6A1A2S3SfA1A3A3A3A3S78Vsz;A1A3").
Definition F_dj (sz : Z) : list sprop := ltac2:(tb__ "0|4|
S0S11S14S37S38S10SbdVsz;Z1A2A1A2M0S10SbfSbeZ2M1Z20A2SbeG1Z14M2A2A2A1A2S0S11S20S19Sc7S13Sc3G0S10G2A1M3A3S13Sc3S37G0S10Vsz;A1A2G3A3A3A1S3S11A1A3A3").
Definition mkDj (sz : Z) (D : axst) : axst := ltac2:(tb__ "0|2|
Sd6Sb6VD;Se9Sb5VD;A1M0SdcSfSd5ScSfS15G0A1M1A2U2A2G1A3A2A2S5S11S17G0A1S79Vsz;A1A3A2").

Definition run1 (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39U320S0S33Z7eb04S3S33A1A3S93Vsz;A1A3").
Definition E1 (sz : Z) : axst := leaf 0 (run1 sz).
Definition T1 (sz : Z) : axst := mkT1 (E1 sz).
Definition run2 (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39U64S0S33Z7eb24S3S33A1A3S94Vsz;A1A3").
Definition L2 (sz : Z) : axst := leaf 0 (run2 sz).
Definition FindB (sz : Z) : axst := mkFindB (L2 sz).
Definition FindNZ (sz : Z) : axst := mkFindNZ (L2 sz).
Definition run_nz (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39U64S0S33Z7eb24S0S33S3bS3S33A1A3A3S7bVsz;A1A3").
Definition CONT (sz : Z) : axst := ltac2:(tb__ "0|0|
S9cS99U0SacVsz;A1A2A1").
Definition FOUND (sz : Z) : axst := leaf 1 (run_nz sz).
Definition FindZ (sz : Z) : axst := mkFindZ (L2 sz).
Definition run_z (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39U12cS0S33Z7ebe4S3S33A1A3S7cVsz;A1A3").
Definition I3 (sz : Z) : axst := leaf 0 (run_z sz).
Definition I4 (sz : Z) : axst := mkI4 (I3 sz).
Definition run_nb (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39U14S0S33Z7ebecS3S33A1A3S7eVsz;A1A3").
Definition NB (sz : Z) : axst := leaf 0 (run_nb sz).
Definition NBh (sz : Z) : axst := mkNBh (NB sz).
Definition run_b1 (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39Ubb8S0S33Z7ebecS0S33Z6bf18S3S33A1A3A3Sa0S7dVsz;A1A1A3").
Definition EB (sz : Z) : axst := leaf 0 (run_b1 sz).
Definition run_b2 (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39UbbaS0S33Z7ebecS0S33Z6bf18S3S33A1A3A3Sa5S56Vsz;A1A1A3").
Definition NBb (sz : Z) : axst := leaf 0 (run_b2 sz).
Definition run_bf (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39Ubb9S0S33Z7ebecS0S33Z6bf18S3S33A1A3A3S9dS56Vsz;A1A1A3").
Definition SPINb (sz : Z) : axst := leaf 0 (run_bf sz).

Definition run_n (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39U12cS0S33S54S3S33A1A3Sa4Vsz;S5fVsz;A1A2A3").
Definition Js (sz : Z) : axst := leaf 0 (run_n sz).
Definition Jh (sz : Z) : axst := mkJh (Js sz).
Definition run_e1 (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39U12dS0S33S49S3S33A1A3Sa2Vsz;S5eVsz;A1A2A3").
Definition E2s (sz : Z) : axst := leaf 0 (run_e1 sz).
Definition E2h (sz : Z) : axst := mkE2h (E2s sz).
Definition run_e2 (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39U5dcS0S33S3bS3S33A1A3S72Vsz;A1A3").
Definition run_f1 (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39UbbbS0S33Z7cf1cS0S33Z6bf18S0S33S3bS3S33A1A3A3A3Sa3Vsz;S5eVsz;A1A2A3").
Definition C1f (sz : Z) : axst := leaf 0 (run_f1 sz).
Definition run_f2 (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39UbbcS0S33Z6bf18S0S33S3bS3S33A1A3A3S9aS6fVsz;A1A1A3").
Definition EFf (sz : Z) : axst := leaf 0 (run_f2 sz).
Definition run_f4 (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39UbbdS0S33S49S0S33Z6bf18S0S33S3bS3S33A1A3A3A3Sa6S57Vsz;A1A1A3").
Definition C3f (sz : Z) : axst := leaf 0 (run_f4 sz).
Definition run_ff (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39UbbfS0S33S49S0S33Z6bf18S0S33S3bS3S33A1A3A3A3S9eS57Vsz;A1A1A3").
Definition run_d (sz : Z) : list leafA := ltac2:(tb__ "0|0|
S39Ubc0S0S33S54S0S33Z6bf18S0S33S3bS3S33A1A3A3A3Sa1Vsz;S5fVsz;A1A2A3").
Definition D1 (sz : Z) : axst := leaf 0 (run_d sz).

Definition O_nnE : sobj := ltac2:(tb__ "0|4|
S36Sa8Z0M0Z10S0S4S4S33S1A2M1SeA2M2S2G1SeS2S33S1G0U8A4S6bA4S0G2S2G1SeS2S33S1Z8U4M3A4S4eA4S0G2S2G1SeS2S33S1ZcG3A4S12Pc3A1A4S3G2A1A3A3A3A4").
Definition objsXE (sz : Z) : list sobj := ltac2:(tb__ "0|1|
S5SfS0SfSdaS0SfS40S3SfA1M0A3A3S5SfSd9S5SfS4aS0SfS64S4cA1S0SfS62S4cA1S0SfS47S3fA1S0SfS8cS0SfS53S37S38S10SbdVsz;Z1A2A1A2A1S0SfS46S3eA1S0SfS61Vsz;A1S0SfS48S12Pc5A1A1G0A3A3A3A3A3A3A3A3A3A3A3").
Definition FXE (sz : Z) : list sprop := ltac2:(tb__ "0|0|
S5S11S45S5S11S5dS5S11S58S5S11S5cS5S11S5bVsz;A1S59A3A3A3A3A3").
Definition XE (sz : Z) : axst := ltac2:(tb__ "0|0|
Sd8S16S3bScbScdS69A2SccS22SbSeA1Sa9Vsz;A1S73Vsz;A1S3aS6A9S3S4SeSeA2A1A2").

Definition single_at (l : list leafA) (pc : Z) : bool := ltac2:(tb__ "0|1|
S7Sb7A1M0S8Ll;Vl;S6Sb7G0G0S8Ll0;R1Sc0S21Sb5Sb8R2A1A1A1Vpc;A2Sb7G0S6Ll2;Ll1;X7x2Ll0;LL;X7x2").
Definition ents (L T : axst) : bool := ltac2:(tb__ "0|0|
SbaVL;VT;Se7S60Sb5VL;A1Sb5VT;A1A3A3").

Definition carved4b (o : sobj) (base : sv) : bool := ltac2:(tb__ "0|3|
S9S9S9S9S2bS27Vo;A1Vbase;A2S2bS2aVo;A1S10Z18A1M0A2A2S2bS29Vo;A1S10Z1cA1A2A2S7S18A1M1S8Lx;S2cVo;A1S6S18G1G1S8Ll;R1S9S2bS25R2A1G0A2Sc0S2dR2A1Z4A2A2S18G1S6Ll0;Lc0;X7x2Ll;Lc;X7x2A2S2eS8Lx;S28Vo;A1SaS6S6S34S6Ll;M2G2S33SeS7S4S33S33A2A1S7S32A1S6Ltmpl;Lflds;Lcnt;Lesz;X2ex6A2").
Definition d1_tail_ok (sz : Z) (D : axst) : bool := ltac2:(tb__ "0|1|
S15Sb5VD;A1A1S7SfA1M0G0S8Lx;SdfSfSd5ScSfR1A2U2A2R1A3S6SfG0G0S8Ll;R1S6SfG0G0S8Ll0;R1S9S66R4S4bA2S66R2S65Vsz;A1A2A2SfG0S6Ll1;Ls;X7x2Ll0;Lo2;X7x2Ll;Lo1;X7x2Tobjs;").
