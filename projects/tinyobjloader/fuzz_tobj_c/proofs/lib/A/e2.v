(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Init KxA.
From Stdlib Require Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartLib.

(* [comment removed for export] *)
Module Asan_memcpy48_iface.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "pair"; "prod"; "nat"; "app"; "list"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sprop"; "sv"; "SPUle"; "SLit"; "sobj"; "cell"; "DUnknown"; "SAlu"; "mkObj"; "valuation"; "FcsrFrm0"; "SPAlign"; "mkSS"; "mkCell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface"; "c8x"; "thunk_alloc48"; "thunk_calloc48"; "thunk_free48"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "J_pure_pre"; "JL_pure"; "KcA"; "Kc_ok"; "memx_depth"; "pre_facts"; "stack_win"; "NPOSTM"; "ae_asan_memcpy"; "ae_ret_asan_memcpy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface.WithSegs.Contracts"; "L_memcpy48"; "Pre_memcpy48"; "memcpy48_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition thunk_alloc48 : Z := 0x8c86c. Definition thunk_calloc48 : Z := 0x8c878. Definition thunk_free48 : Z := 0x8c88c.
Definition c8x (o : Z) (v : sv) : cell := ltac2:(tb__ "0|0|
S17SdVo;A1Z8Vv;A3").
Definition al48_cells : list cell := ltac2:(tb__ "0|2|
S0SfS18Z0M0SdS19A1A2S0SfS18Z8SdS1aA1A2S0SfS18Z10SdG0A1M1A2S0SfS18Z18SdS1bA1A2S0SfS18Z20G1A2S0SfS18Z28G1A2S1SfA1A3A3A3A3A3A3").

Section WithSegs.
Variable segs : list Segment.
Section Contracts.
Variable E : aentry.
Variable AInvA : ltac2:(tb__ "0|0|
S2fS13S6S30Q40A1A1S3aOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).

Definition memcpy48_facts : list sprop := ltac2:(tb__ "0|12|
S0SaScS9P35A1M0S9PcM1A1M2A2S0SaScS11S1cG2SdZ30A1M3A3S11S1cG0S9P36A1M4A3M5A2S0SaScS9P37A1M6S9PdM7A1M8A2S0SaScS11S1cG8G3A3S11S1cG6S9P38A1M9A3MaA2S0SaScSdS3eA1MbG0A2S0SaScG5SdS39S38Z2McZ2fA2MdZ8A2A1MeA2S0SaScG4SdS38GcZ28A2A1MfA2S0SaScG0GeA2S0SaScG2SdGdA1M10A2S0SaScS9PaA1G10A2S0SaScGbG6A2S0SaScGaGeA2S0SaScG9GfA2S0SaScG6GeA2S0SaScG8G10A2S0SaS15G1Z3M11A2S0SaS15G7G11A2S1SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition Pre_memcpy48 (cs : list cell) : axst := ltac2:(tb__ "0|4|
S35S16S2dVE;A1S22S24S0S3S4SbA2M0S2S4SbUcSdZ30A1M1A4S1G0A1A3A2S21S14S7SbA1S5SeS0SeS2bS0SeS12S9PcA1SdZ0A1M2G1S1SfA1S10A5S0SeS12S9PdA1G2G1Vcs;S10A5S1SeA1A3A3A3S34A3S5SaS33S2aS29A1A3S20S8A9S0S3SbSbA2M3S2SbSbS9P35A1S9P36A1A4S0G3S2SbSbS9P37A1S9P38A1A4S1G3A1A3A3A2").
Definition L_memcpy48 (cs : list cell) : axst := ltac2:(tb__ "0|5|
S35S16S2eVE;A1S22S23S20A1S0S3S4SbA2M0S2S4SbUaS9PcA1M1A4S1G0A1A3A2S21S14S7SbA1S5SeS0SeS2bS0SeS12G1SdZ0A1M2SdZ30A1M3Vcs;S10A5S0SeS12S9PdA1G2G3Vcs;S10A5S1SeA1A3A3A3S34A3S2aS29A1S2cS8A9S0S3SbSbA2M4S2SbSbS9P35A1S9P36A1A4S0G4S2SbSbS9P37A1S9P38A1A4S1G4A1A3A3A2").

Definition memcpy48_contractA (cs : list cell) : Prop := ltac2:(tb__ "0|1|
S3dOF_;S2fS27S13S6S30Q40A1A1S28R3A1S37Vsegs;R6S25VAInvA;R5R4A3A3S3cVsegs;R7S36Vsegs;S25VAInvA;R6R5A3S32Vcs;A1R4R3A5S1fVsegs;S20R4R3S0S3S1dS1eA2M0S2S1dS1eS31Vcs;A1S26VAInvA;VCST;VXGL;R6R5A5A4S1G0A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;").
Definition memcpy48_contractA_ex (cs : list cell) : Prop := ltac2:(tb__ "0|1|
S2fS27S13S6S30Q40A1A1S28R3A1S3bVsegs;S36Vsegs;S25VAInvA;R5R4A3S32Vcs;A1R3R2A5S1fVsegs;S20R3R2S0S3S1dS1eA2M0S2S1dS1eS31Vcs;A1S26VAInvA;VCST;VXGL;R5R4A5A4S1G0A1A3A5A3F_;Ftp;Frho;FKc;FA;").
End Contracts.
End WithSegs.

Goal swf (ax_S (Pre_memcpy48 AE_A al48_cells)) = true /\ axwf (Pre_memcpy48 AE_A al48_cells) = true
     /\ swf (ax_S (L_memcpy48 AE_A al48_cells)) = true /\ axwf (L_memcpy48 AE_A al48_cells) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Asan_memcpy48_iface.

(* [comment removed for export] *)
Module Asan_memcpyR_iface.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "pair"; "prod"; "nat"; "app"; "list"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SVar"; "SPUle"; "sobj"; "valuation"; "DUnknown"; "FcsrFrm0"; "SAlu"; "cell"; "mkObj"; "mkSS"; "SPAlign"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "J_pure_pre"; "JL_pure"; "KcA"; "Kc_ok"; "memx_depth"; "pre_facts"; "stack_win"; "NPOSTM"; "ae_asan_memcpy"; "ae_ret_asan_memcpy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpyR_iface.WithSegs.Contracts"; "L_memcpyR"; "Pre_memcpyR"; "memcpyR_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Section Contracts.
Variable E : aentry.
Variable AInvA : ltac2:(tb__ "0|0|
S29SfS6S2aQ40A1A1S35OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).

Definition memcpyR_facts (n : Z) : list sprop := ltac2:(tb__ "0|9|
S0SbSdScP35A1M0ScPcM1A1M2A2S0SbSdS12S2bG2SaVn;A1A3S12S2bG0ScP36A1M3A3M4A2S0SbSdSaS39A1G0A2S0SbSdG4SaS34S33Z2M5Z2fA2M6Z8A2A1M7A2S0SbSdG3SaS33G5Z28A2A1A2S0SbSdG0G7A2S0SbSdG2SaG6A1M8A2S0SbSdScPaA1G8A2S0SbS16G1Z3A2S1SbA1A3A3A3A3A3A3A3A3A3").

Definition Pre_memcpyR (src n : Z) : axst := ltac2:(tb__ "0|4|
S30S15S27VE;A1S1cS1eS0S3S4S9A2M0S2S4S9UbSaVsrc;A1M1A4S0G0S2S4S9UcSaVn;A1M2A4S1G0A1A3A3A2S1bS11S7S9A1S5SeS0SeS25S0SeS14ScPcA1SaZ0A1G2S1S13A1S10A5S1SeA1A3A3S2fA3S5SbS2eVn;A1S24S23A1A3S1aS8A9S0S3S9S9A2M3S2S9S9ScP35A1ScP36A1A4S0G3S2S9S9G1G2A4S1G3A1A3A3A2").
Definition L_memcpyR (src n : Z) : axst := ltac2:(tb__ "0|4|
S30S15S28VE;A1S1cS1dS1aA1S0S3S4S9A2M0S2S4S9UaScPcA1M1A4S1G0A1A3A2S1bS11S7S9A1S5SeS0SeS25S0SeS14G1SaZ0A1SaVn;A1M2S1S13A1S10A5S1SeA1A3A3S2fA3S24S23A1S26S8A9S0S3S9S9A2M3S2S9S9ScP35A1ScP36A1A4S0G3S2S9S9SaVsrc;A1G2A4S1G3A1A3A3A2").

Definition memcpyR_contractA (src n : Z) : Prop := ltac2:(tb__ "0|1|
S38OF_;S29S21SfS6S2aQ40A1A1S22R3A1S32Vsegs;R6S1fVAInvA;R5R4A3A3S37Vsegs;R7S31Vsegs;S1fVAInvA;R6R5A3S2dVsrc;Vn;A2R4R3A5S19Vsegs;S1aR4R3S0S3S17S18A2M0S2S17S18S2cVsrc;Vn;A2S20VAInvA;VCST;VXGL;R6R5A5A4S1G0A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;").
Definition memcpyR_contractA_ex (src n : Z) : Prop := ltac2:(tb__ "0|1|
S29S21SfS6S2aQ40A1A1S22R3A1S36Vsegs;S31Vsegs;S1fVAInvA;R5R4A3S2dVsrc;Vn;A2R3R2A5S19Vsegs;S1aR3R2S0S3S17S18A2M0S2S17S18S2cVsrc;Vn;A2S20VAInvA;VCST;VXGL;R5R4A5A4S1G0A1A3A5A3F_;Ftp;Frho;FKc;FA;").
End Contracts.
End WithSegs.

Definition white_hv : Z := 142880.
Definition white_lo : Z := 142240.
Goal swf (ax_S (Pre_memcpyR AE_A white_hv 12)) = true /\ axwf (Pre_memcpyR AE_A white_hv 12) = true
     /\ swf (ax_S (L_memcpyR AE_A white_hv 12)) = true /\ axwf (L_memcpyR AE_A white_hv 12) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Asan_memcpyR_iface.

(* [comment removed for export] *)
Module MuslMallocIface.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "bool"; "prod"; "true"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sprop"; "cell"; "SPUle"; "sobj"; "mkObj"; "DUnknown"; "mkCell"; "DImage"; "SPAlign"; "SAlu"; "FcsrFrm0"; "mkSS"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface"; "vRND"; "vSP"; "vXB"; "vAUXV"; "addk"; "vXL"; "vUID"; "D_M"; "O_auxp"; "O_auxv"; "O_errno"; "O_flg"; "O_mctx"; "O_nlk"; "O_pgsz"; "O_rand"; "O_real"; "O_ssp"; "O_stk"; "O_vml"; "Pre_M"; "Pre_M_S"; "X_M"; "aux_svs_M"; "facts_M"; "malloc_entry"; "objs_M"; "regs_M"; "vHWCAP"; "vRND0"; "vRND1"; "vSSP"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "of_N"; "add"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init"; "phA"; "@Corelib.Init.Logic"; "eq"; "and"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "ph_addr"; "ph_ent"; "ph_num"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "O_got"; "O_rtc"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axwf"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "cells_from"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "pre_regs"; "setregs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts Init Code KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition malloc_stub : Z := 0xd5170.
Definition malloc_entry : Z := 0xd5b00.
Definition malloc_ret_null : Z := 0xd5b58.
Definition malloc_ret_ok : Z := 0xd6860.
Definition D_M : Z := 2816.

Definition vSP : sv := SVar 10.  Definition vAUXV : sv := SVar 16.  Definition vRND : sv := SVar 17.
Definition vXB : sv := SVar 52.  Definition vXL : sv := SVar 53.  Definition vUID : sv := SVar 18.
Definition vHWCAP : sv := SVar 19.  Definition vRND0 : sv := SVar 54.  Definition vRND1 : sv := SVar 55.
Definition addk (e : sv) (k : Z) : sv := ltac2:(tb__ "0|0|
S14S3fVe;S9Vk;A1A3").

Definition O_stk : sobj := ltac2:(tb__ "0|0|
SfS19S9S3bS1fA1A1S9Z0A1S1ScA1S10A5").
Definition O_mctx : sobj := ltac2:(tb__ "0|0|
SfS9Z0A1S9Z6448c0A1S9Z644c68A1S1ScA1S12A5").
Definition O_nlk : sobj := ltac2:(tb__ "0|0|
SfS9Z0A1S9Z64484bA1S9Z64484cA1S1ScA1S12A5").
Definition O_auxp : sobj := ltac2:(tb__ "0|1|
SfS9Z0A1S9Z644850A1M0S9Z644858A1S0ScS11G0Z8S1bA3S1ScA1A3S10A5").
Definition O_pgsz : sobj := ltac2:(tb__ "0|1|
SfS9Z0A1S9Z644878A1M0S9Z644880A1S0ScS11G0Z8S9Z1000A1A3S1ScA1A3S10A5").
Definition vSSP : sv := SVar 15.
Definition O_ssp : sobj := ltac2:(tb__ "0|1|
SfS9Z0A1S9Z6445f8A1M0S9Z644600A1S0ScS11G0Z8S37A3S1ScA1A3S10A5").
Definition O_errno : sobj := ltac2:(tb__ "0|0|
SfS9Z0A1S9Z624514A1S9Z624518A1S1ScA1S10A5").
Definition O_vml : sobj := ltac2:(tb__ "0|0|
SfS9Z0A1S9Z645dd8A1S9Z645de8A1S1ScA1S12A5").

Definition aux_svs_M : list sv := ltac2:(tb__ "0|1|
S0SaS9Z3A1S0SaS9S39S40S3cA1A1A1S0SaS9Z4A1S0SaS9S39S41S3cA1A1A1S0SaS9Z5A1S0SaS9S39S42S3cA1A1A1S0SaS9Z10A1S0SaS34S0SaS9Z6A1S0SaS9Z1000A1S0SaS9ZbA1S0SaS1eS0SaS9ZcA1S0SaS1eS0SaS9Z17A1S0SaS9Z0A1M0S0SaS9Z19A1S0SaS18S0SaG0S0SaG0S1SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition O_auxv : sobj := ltac2:(tb__ "0|1|
SfS1bS9Z0M0A1S9Za0A1S48G0S2fA2S10A5").

Definition O_rand : sobj := ltac2:(tb__ "0|2|
SfS18S9Z0A1M0S9Z10A1S0ScS11G0Z8M1S35A3S0ScS11S9G1A1G1S36A3S1ScA1A3A3S10A5").
Definition O_flg : sobj := ltac2:(tb__ "0|3|
SfS9Z0A1S9Zf20d8A1M0S9Zf20daA1S0ScS11G0Z1M1S9G1A1M2A3S0ScS11S9Zf20d9A1G1G2A3S1ScA1A3A3S12A5").
Definition O_real : sobj := ltac2:(tb__ "0|0|
SfS9Z0A1S9Ze9ac8A1S9Ze9af8A1S1ScA1S12A5").

Definition objs_M : list sobj := ltac2:(tb__ "0|0|
S0SeS2aS0SeS24S0SeS25S0SeS20S0SeS26S0SeS29S0SeS22S0SeS2bS0SeS21S0SeS27S0SeS23S0SeS28S0SeS43S0SeS44S1SeA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition facts_M : list sprop := ltac2:(tb__ "0|8|
S0SbS13PaZ4A2S0SbSdS9Z7fff7fff0000A1S19A2S0SbSdS19S9S38Z2M0Z2fA2M1A1M2A2S0SbS13P10Z3M3A2S0SbSdS9Z7fff80000000A1M4S1bA2S0SbSdS1bS9S3aG1S38G0Z16A2A2A1M5A2S0SbSdS1cS19Z40A2S1bA2S0SbS13P11G3A2S0SbSdG4S18A2S0SbSdS18G5A2S0SbSdS1cS19Z140A2S18A2S0SbS13P34Z6M6A2S0SbS13P35G6A2S0SbSdS1cS1aZ200A2S19A2S0SbSdS19S14S3fS1aS1dA3M7A2S0SbSdS1aS18A2S0SbSdS1cS18Z10A2G7A2S0SbSdS1dS9S38G0Z28A2A1A2S0SbSdS9Z7fff7f000000A1S1aA2S0SbSdS1aS9S38G0Z30A2A1A2S0SbSdG7G2A2S1SbA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition X_M : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SaSaA2M0S3SaSaS1aS1dA4S1G0A1A3").
Definition axM (S : sstate) : axst := ltac2:(tb__ "0|0|
S47VS;S2eS9S45A1A3").

Definition regs_M : list sv := ltac2:(tb__ "0|1|
S4cS4bS0S5S2SaA2M0S3S2SaU3S9Z10800A1A4S0G0S3S2SaU4S9Z6245b8A1A4S0G0S3S2SaUaS9Z28A1A4S1G0A1A3A3A3A2").

Definition Pre_M_S : sstate := ltac2:(tb__ "0|0|
S16S31S33S4aS15S7SaA1S32S30S49S8A9").
Definition Pre_M : axst := axM Pre_M_S.

Lemma Pre_M_wf : ltac2:(tb__ "0|0|
S3eS3dS4S17S2dA1S6A3S3dS4S46S2cA1S6A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End MuslMallocIface.

(* [comment removed for export] *)
Module StartALib.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "iff"; "or"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "sv"; "eval"; "rw"; "ss_lenient"; "ob_base"; "ss_next"; "obj_range"; "ss_objs"; "SLit"; "rm"; "agree_below"; "mkObj"; "ranges_disjoint"; "ss_pc"; "sstate"; "DZero"; "mem_match"; "ob_hi"; "ob_lo"; "obj_holds"; "outside_all"; "pairwise_disjoint"; "rl"; "ss_facts"; "cell"; "holds"; "ob_cells"; "ob_dflt"; "sprop"; "sv_eqb"; "@Corelib.Init.Datatypes"; "list"; "nil"; "cons"; "bool"; "true"; "prod"; "false"; "option"; "app"; "Some"; "pair"; "andb"; "nat"; "orb"; "fst"; "negb"; "snd"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "mkLeafA"; "sym_runA"; "mkAX"; "ax_X"; "la_state"; "ax_base"; "ax_setS"; "axwf"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "leb"; "ge"; "modulo"; "mul"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "RMH"; "agree_vars"; "ARGF"; "SHB"; "axA"; "cfg1_okA"; "eblk_clear_b"; "obj_clear_e"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "RsSymJump"; "set_objs"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vm_lazy"; "m_vmmaps"; "page_size"; "m_vm_materialized"; "vm_backing_used"; "vm_noaccess"; "vm_limit"; "vm_maps"; "event"; "page_in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "etriple"; "assn"; "w_cfg"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib.Rebase"; "rebase_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "ivs_wf"; "covered"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "same_but_objs"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "le"; "leb"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib"; "lit_of"; "Kx"; "high_clear_b"; "img_clear_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "forallb_lazy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "enomem_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "leaf_matches1A"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Restrict"; "restrict"; "wx_segs_nowrap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "MI";
"headroom"; "hid"; "paid"; "virt"; "vmd"; "vms"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition SHB : Z := 0x7fff8000.
Definition axA (S : sstate) : axst := ltac2:(tb__ "0|0|
S41VS;S2aS2eSbSbA2A1S13S58A1A3").

Lemma axwf_axA : ltac2:(tb__ "0|0|
S19S0S2cS46S59R1A1A1S2dA3FS;").
Proof. intros S. reflexivity. Qed.

Lemma restrict_false : ltac2:(tb__ "0|0|
S61S0S61S91S3aQ40A1S2fL_;R1A2R1A3Fms;").
Proof.
  intros ms. unfold restrict. destruct ms; cbn. f_equal.
Qed.

Lemma hid_nolazy : ltac2:(tb__ "0|2|
S62S29S3aQ40A1M0A1S0S29S2eG0G0A2M1A1S63R2A1S2aG1A1A3S0G0S2cFa;S95R3R2A2G0S2fLa;A3F_;Ftp;Fmd;").
Proof.
  intros md tp H. apply functional_extensionality. intros a. unfold hid. rewrite H. reflexivity.
Qed.

Lemma vms_nolazy : ltac2:(tb__ "0|2|
S62S29S3aQ40A1M0A1S61S0S29S2eG0G0A2M1A1S63R3A1S2aG1A1A3S0S61S99R4R3R2A3R2A3F_;Fms;Ftp;Fmd;").
Proof. intros md tp ms H. unfold vms. rewrite (hid_nolazy md tp H). apply restrict_false. Qed.

Lemma vmd_nolazy : ltac2:(tb__ "0|2|
S62S0S29S2eS3aQ40A1M0G0A2M1A1S63R1A1S2aG1A1A3S0S29G0A1S66R2A1S2aG0A1A3S0S62S98R3A1R3A3F_;F_;Fmd;").
Proof.
  intros md H1 H2. unfold vmd. rewrite <- H1, <- H2. apply with_vm_backing_id.
Qed.

Lemma virt_nolazy : ltac2:(tb__ "0|3|
S29S3aQ40A1M0A1M1S6dS0S29S2eG0G0A2M2A1S63S7fS71R1A1A1A1S2aG2A1A3S0G1S66S7fS71R2A1A1A1S2aG0A1A3S0S6dS97R4R3A2R3A3F_;F_;Fw;Ftp;").
Proof.
  intros tp [tr [ms md]] H1 H2. unfold virt. cbn in *. rewrite (vms_nolazy md tp ms H1), (vmd_nolazy md H1 H2). reflexivity.
Qed.

Lemma paid_nil : ltac2:(tb__ "0|0|
S62S0S6S96R1S2aS3aQ40A1A1A2S67R1A1A3Fmd;").
Proof. intros md. unfold paid, unpaid. cbn. lia. Qed.

Lemma MI_nil : ltac2:(tb__ "0|3|
S29S8aA1S62S92R2A1S0S29S2eS3aQ40A1M0G0A2M1A1S63R2A1S2aG1A1A3S0S29G0A1S66R3A1S2aG0A1M2A3S48S67R4A1S69S64R4A1A1A2S74S6aS64R5A1A1A1S74S68S64R6A1A1A1S93R8R7G2A3F_;F_;F_;F_;F_;F_;Fmd;Fsegs;").
Proof. intros segs md. apply MI_intro_nolazy. Qed.

Theorem SP_SPA : ltac2:(tb__ "0|3|
S62S6S19S9S6dS0S29S2eS3aQ40A1M0G0A2M1A1S63R5A1S2aG1A1A3S0S29G0A1S66R6A1S2aG0A1M2A3S48S67R7A1R6A2S48R7S69S64R8A1A1A2S74S6aS64R9A1A1A1S74S68S64RaA1A1A1S90S8S83RbA1R9R8R7A5S50S8S8bRcRbA2S59RaA1R9G2R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Frho;FS;FB;Fm;").
Proof.
  intros m B S rho [tr [ms md]] Hl Hm HuB HB Hw1 Hw2 [Hsm HK]. cbn in HK. unfold liftK, Kx in HK. destruct HK as [-> ->].
  assert (Hu : vm_backing_used m <= vm_limit (m_vmmaps m)) by lia.
  split; [|split; [reflexivity|split; [reflexivity| cbn; rewrite paid_nil; exact HuB]]].
  split; [|split; [|split; [|split]]].
  - cbn. rewrite (virt_nolazy [] ([], mkCfg ms m) Hl Hm). exact Hsm.
  - cbn. apply MI_nil; [apply wx_segs_nowrap_A | assumption | assumption | assumption | assumption | assumption].
  - reflexivity.
  - unfold shadow_ok. cbn. constructor.
  - cbn. intros a Ha. rewrite (hid_nolazy m [] Hl) in Ha. discriminate.
Qed.

Lemma triple_spinA : ltac2:(tb__ "0|1|
S6dOF_;S51S3eS9S29S3aQ40A1A1S70S54S8R6R5A3S53S8S10S3dR5A1A1R6A3S0S2cSeS3dR6A1A1S2fA3S0S30S29S3cA1M0A1S40S8U2S2bS6S18S3dR7A1A1S2aS6A1A3R7S2dA5S32G0S2bS3cS3fR7S5eA2S2aS3cA1A3A2A3S6eS8RaS50S8R9R8R7R6A5R5A4F_;F_;F_;F_;FQ;Ftp;Frho;FA;FJ;Fok;").
Proof.
  intros ok J A rho tp Q Hok Hst Hstrict Hrun.
  apply (@triple_conseq segsA ok (fun w => exists rho', agree_below (ss_next (ax_S A)) rho rho' /\ SPA segsA J A rho' tp w) _ Q Q);
    [ intros w Hw; exists rho; split; [apply agree_below_refl | exact Hw] | intros w Hw; exact Hw | ].
  apply triple_loop. apply triple1_ex. intros rho'. apply triple1_pure. intros Hag.
  eapply triple1_conseq; [intros w Hw; exact Hw | | eapply sym_run_soundA; [exact Hrun | exact Hok | exact Hstrict | exact Hst]].
  intros w (L & rho'' & Hin & Hag' & Hsm & Hk). destruct Hin as [<-|[]]. left.
  exists rho''. split; [eapply agree_below_trans; eauto | split; assumption].
Qed.

Section NodeSeg.
Variable ok : assn.
Variables (J J' : jpredA).
Hypothesis OKJ : ok_frameA segsA ok J.
Hypothesis OKJ' : ok_frameA segsA ok J'.
Hypothesis STJ : ltac2:(tb__ "0|0|
S7S53S8R1VJ;A3Fn;").
Hypothesis STJ' : ltac2:(tb__ "0|0|
S7S53S8R1VJ';A3Fn;").

Lemma fail_arm_safe : ltac2:(tb__ "0|5|
S3eS3eS35S6S9S29S3aQ40A1A1S70S0S2cSeS3dR7A1A1S2fA3M0G0S0S6S18S3dR8A1A1R6A3S0S30S29S3cA1M1A1M2S40S8R8S2bS6R7S2aS6A1M3A3RaS2dA5S32G1S2bS3cS3fR9S5eA2S2aS3cA1M4A3A2A3S0G2S40S8U2S2bS6R8G3A3RaS2dA5S32G1S2bS3cS3fRaS5eA2G4A3A2A3S6eS8Vok;S50S8VJ;RcR8R7A5R6A4F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fp;Ffuel;FSPIN;FF;").
Proof using OKJ STJ.
  intros F SPIN fuel p rho tp Q HlF HlS Hpc Hrun Hspin.
  eapply triple_seq.
  { apply triple1_triple. eapply sym_run_soundA; [exact Hrun | exact OKJ | exact HlF | apply STJ]. }
  apply triple_ex; intros L. apply triple_ex; intros rho'. apply triple_pure; intros HinL. apply triple_pure; intros Hag.
  destruct HinL as [<-|[]]. cbn [la_state].
  apply (triple_spinA ok J SPIN rho' tp Q OKJ (STJ _) HlS). rewrite Hpc. exact Hspin.
Qed.

Lemma node_seg : ltac2:(tb__ "0|a|
S3eS3eS3eS3eS9S9S29S3aQ40A1A1M0G0S35S6S35S6S72S8Vok;S50S8VJ;RcR8R6A5S6dS4S50S8VJ;S41S87S3dRdA1S88A2S2aS2eSbSbA2M1A1M2S13S58A1M3A3R9R7R1A6S50S8VJ';RcR8R6R1A6A2Lw;A4S0S29G1A1S42RdA1G2A3S0SbS44ReA1G3A3S0S2cSeS3dRfA1M4A1S2fA3S0S2cSeS3dReA1A1S2fA3S0S6S18G4A1R8A3S0S30S29S3cA1M5A1M6S40S8RaS2bS6R9S2aS6A1M7A3S41S87S3dR12A1S88A2G2G3A3S2dA5S32G5S2bS3cS3fR10S5eA2S2aS3cA1M8A3A2A3S0G6S40S8U2S2bS6RaG7A3M9R11S2dA5S32G5S2bS3cS3fR11S5eA2G8A3A2A3S0S2cSeS3dR13A1A1S2fA3S0G6S40S8RbG9R14S2dA5S32G5S2bS3cS3fR12S5eA2G8A3A2A3S6eS8Vok;S50S8VJ;R16R12R10A5S52S8VJ';S10S3dR15A1A1R11RfS2bS3cS3fR13S5eA2G8A3A6A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fcutpc;Ffuel;Fp;FfuelF;Ftp2;Ftp;Frho2;Frho;FE';FSPIN;FSok;FE;").
Proof using OKJ OKJ' STJ STJ'.
  intros E Sok SPIN E' rho rho2 tp tp2 fuelF p fuel cutpc Hnode HX Hb HlE HlS Hpc HrunF Hspin HlO HrunO.
  eapply triple_seq; [apply triple1_triple; exact Hnode|].
  apply triple_disj.
  - eapply (fail_arm_safe _ SPIN fuelF p); [cbn; unfold S_ret_lit, S_after; cbn; exact HlE | exact HlS | exact Hpc | exact HrunF | exact Hspin].
  - apply triple1_triple. eapply sym_run_soundA; [exact HrunO | exact OKJ' | exact HlO | apply STJ'].
Qed.
End NodeSeg.

Lemma enode_seg : ltac2:(tb__ "0|3|
S51S51S3eS3eS3eS9S9S29S3aQ40A1A1M0G0S35S6S7S53S8R1RbA3Fn;S6fS8S50S8RcRaR7R5A5S50S8RbR9R6R4A5A3S0S2cSeS3dRaA1A1S2fA3S0S30S29S3cA1M1A1S40S8R5S2bS6R4S2aS6A1A3RbS2dA5S32G1S2bS3cS3fRaS5eA2S2aS3cA1M2A3A2A3S6fS8S50S8RfRdRaR8A5S52S8ReS10S3dRcA1A1R9R7S2bS3cS3fRbS5eA2G2A3A6A3F_;F_;F_;F_;Fcutpc;Ffuel;Ftp2;Ftp;Frho2;Frho;FE';FSok;FE;FJ';FJ;").
Proof.
  intros J J' E Sok E' rho rho2 tp tp2 fuel cutpc STJ' Hnode HlO HrunO.
  eapply etriple_seq; [exact Hnode|].
  eapply sym_run_etripleA; [exact HlO | apply STJ' | exact HrunO].
Qed.

Section Rebase.
Variable segs : list Segment.

Definition rebase_obj (eb : sv) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S16Veb;S1dVo;A1S1cVo;A1S25Vo;A1S26Vo;A1A5").

Lemma obj_range_rebase : ltac2:(tb__ "0|0|
S9SbSaS0S3aQ40A1ScR3R2A2ScR3SfR1A1A2A3S0S2eS6S6A2S11R4S73R3R2A2A2S11R4R2A2A3F_;Fo;Feb;Frho;").
Proof. intros rho eb o H. unfold obj_range, obj_lo_of, obj_hi_of, rebase_obj. cbn. rewrite H. reflexivity. Qed.

Lemma obj_holds_rebase : ltac2:(tb__ "0|0|
S9S61SbSaS0S3aQ40A1ScR4R2A2ScR4SfR1A1A2A3S1eVsegs;R5R4R2A4S1eVsegs;R6R5S73R4R3A2A4F_;F_;Fo;Feb;Fms;Frho;").
Proof.
  intros rho ms eb o H Ho. unfold obj_holds, obj_lo_of, obj_hi_of, rebase_obj in *. cbn in *. rewrite H.
  destruct Ho as (A1 & A2 & A3 & A4 & A5). split; [exact A1|]. split; [exact A2|]. split; [|split; [exact A4|exact A5]].
  apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) A3 c Hc) as X.
  unfold cell_holds, oaddr in *. rewrite H. exact X.
Qed.

Lemma outside_all_rebase_last : ltac2:(tb__ "0|2|
S9S29SaA1SaSbS3aQ40A1M0S0G0ScR5R2A2ScR5SfR3A1A2A3S3S1fR6S31SaR5S2bSaS73R3R4A2S2aSaA1M1A3A3R2A3S1fR6S31SaR5S2bSaR4G1A3A3R2A3A2F_;Fa;Feb;Fo;Fobjs;Frho;").
Proof.
  intros rho objs o eb a H. unfold outside_all. rewrite !Forall_app.
  pose proof (obj_range_rebase rho eb o H) as R.
  split; intros [X Y]; split; try exact X; inversion Y; subst; constructor; try assumption; cbn zeta in *;
    [rewrite <- R | rewrite R]; assumption.
Qed.

Lemma pairwise_disjoint_rebase_last : ltac2:(tb__ "0|1|
S9S29SaA1SaSbS0S3aQ40A1ScR4R1A2ScR4SfR2A1A2A3S20R5S31SaR4S2bSaR3S2aSaA1M0A3A3A2S20R6S31SaR5S2bSaS73R3R4A2G0A3A3A2F_;F_;Feb;Fo;Fobjs;Frho;").
Proof.
  intros rho objs o eb H. induction objs as [|x rest IH]; cbn; intros [A1 A2].
  - split; [constructor|exact I].
  - split; [|apply IH; exact A2].
    rewrite Forall_app in A1 |- *. destruct A1 as [B1 B2]. split; [exact B1|].
    inversion B2; subst. constructor; [|constructor]. rewrite (obj_range_rebase rho eb o H). assumption.
Qed.

Lemma mem_match_rebase_last : ltac2:(tb__ "0|1|
S9S29SaA1SaSbS61S0S3aQ40A1ScR5R2A2ScR5SfR3A1A2A3S1bVsegs;R6S31SaR5S2bSaR4S2aSaA1M0A3A3R2A4S1bVsegs;R7S31SaR6S2bSaS73R4R5A2G0A3A3R3A4F_;F_;Fms;Feb;Fo;Fobjs;Frho;").
Proof.
  intros rho objs o eb ms H (A1 & A2 & A3). split; [|split].
  - rewrite Forall_app in A1 |- *. destruct A1 as [B1 B2]. split; [exact B1|].
    inversion B2; subst. constructor; [|constructor]. apply obj_holds_rebase; assumption.
  - apply pairwise_disjoint_rebase_last; assumption.
  - intros a Ha. apply A3. apply (outside_all_rebase_last rho objs o eb a H). exact Ha.
Qed.

Lemma SPA_prepay_zero_at : ltac2:(tb__ "0|d|
S51S9S3eS3aQ40M0A1M1SbS29G1A1S29S6bA1M2S61S62S50Vsegs;R9R7R8R4S33G2S80R3S81R2R1A2A4A6S0S29S2eSbSbA2M3A1S42R8A1S2aG3A1A3S0S6S4cS3bG0R8A2S65A2Z0M4A3S0S2cS6cR9S63R4A1A2S2dA3S2S76G1RaR8A3A1S6S1S48G4R1A2S49R1S65A2A2S0S2cS75S68S64R8A1A1S47S3bG0RdA2R2A2A2S2fA3F_;Fj;S4bS94R7RaA2S65A2S7eSaSaS17S11R10R1A2S33S6S6S3bG0ReA2M5S47G5S65A2A4A2Lo;S12S3dReA1A1A3S0S2cS7aS3dRfA1M6S60G6S31SaS12G6A1S2bSaS16RdS13G4A1M7S13S65A1M8S2aS23A1M9S1aA5S2aSaA1MaA3A3A2A2S2dA3S0G1ScR11ReA2RfA3R13R12ReRdRbA4R14R13S2bG1R11RfA3MbReRcA4F_;S50Vsegs;R14S45R12S60S3dR12A1McS31SaS12GcA1S2bSaS16R10G7G8G9S1aA5GaA3A3A2A2R13GbS33G2S80ReS81RdRcA2A4A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Feb;Fp;FA;Frho;FJ;").
Proof using .
  intros J rho A p eb tp tr ms md Hsp HX Hal Hlz Hnin Hacc Hroom Hdisj Hsame Hev HJ.
  pose proof (SPA_prepay_zero segs J rho A p tp tr ms md Hsp Hal Hlz Hnin Hacc Hroom Hdisj HJ) as H1.
  change (mkObj eb (SLit 0) (SLit page_size) [] DZero) with (rebase_obj eb (zero_page_obj p)).
  change (ax_setS A (set_objs (ax_S A) (ss_objs (ax_S A) ++ [rebase_obj eb (zero_page_obj p)])))
    with (ax_setS (ax_setS A (set_objs (ax_S A) (ss_objs (ax_S A) ++ [zero_page_obj p])))
                  (set_objs (ax_S A) (ss_objs (ax_S A) ++ [rebase_obj eb (zero_page_obj p)]))).
  apply (SPA_reobj segs J rho (ax_setS A (set_objs (ax_S A) (ss_objs (ax_S A) ++ [zero_page_obj p])))
           (set_objs (ax_S A) (ss_objs (ax_S A) ++ [rebase_obj eb (zero_page_obj p)])) (p :: tp)).
  - exact Hsame.
  - reflexivity.
  - exact H1.
  - destruct H1 as [(Hsm & _) _]. cbn [ax_S ax_setS] in Hsm. unfold virt. cbn [w_cfg cfg_ms snd fst].
    destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmm & _). cbn [fst snd cfg_ms set_objs ss_objs] in Hmm.
    apply mem_match_rebase_last; [|exact Hmm]. cbn. rewrite Hev. symmetry. apply Z_to_bv_bv_unsigned.
  - unfold xshadow_outside. cbn. rewrite HX. constructor.
Qed.
End Rebase.

Definition eblk_clear_b (Ge : list (sv * Z)) (o : sobj) : bool := ltac2:(tb__ "0|3|
S30S6A1S2cLx;M0S82S1dVo;A1A1S6G0S82S1cVo;A1A1S6S77S2eSbS6A2M1G1S34S34S34S34S28SfVo;A1S37SbS6R1A3A2S4aZ0R3A2A2S4aR3R2A2A2S4aR2S39SbS6R1A3M2A2A2S4aG2S4eZ2Z3eA2A2A2Lg;VGe;A3Lhi;S2fX30x2Llo;S2fX30x2").

Definition obj_clear_e (facts : list sprop) (Ge : list (sv * Z)) (o : sobj) : bool := ltac2:(tb__ "0|0|
S36S36S85Vo;A1S84Vfacts;Vo;A2A2S5bVGe;Vo;A2A2").

Definition objs_clear_e (Ge : list (sv * Z)) (S : sstate) : bool := ltac2:(tb__ "0|0|
S78SaS5cS22VS;A1VGe;A2S12VS;A1A3").

Lemma eblk_clear_sound : ltac2:(tb__ "0|5|
S9S29S2eSbS6A2M0A1S3aQ40M1A1S6SaSbS6S76G0S33SbS6R2R1A4R6A3S6S1S48S3bG1R7A2M2R1A2S49R1S47G2R6A2A2A2S2S1S48S3bG1ScRaR5A2A2M3R2A2S49R2S47G3R4A2A2A2A1F_;Fx;F_;Fsz;Fe;S0S2cS5bR5R2A2S2dA3S17S11R7R3A2S33S6S6S3bG1R5A2M4S47G4R4A2A4A2F_;F_;Fo;Fn;Fa;FGe;Frho;").
Proof.
  intros rho Ge a n o HG Hb. unfold eblk_clear_b in Hb.
  destruct (lit_of (ob_lo o)) as [lo|] eqn:Elo; [|discriminate].
  destruct (lit_of (ob_hi o)) as [hi|] eqn:Ehi; [|discriminate].
  apply lit_of_sound in Elo. apply lit_of_sound in Ehi.
  apply existsb_exists in Hb as ([e sz] & Hin & Hg). cbn [fst snd] in Hg.
  apply andb_prop in Hg as [Hg H4]. apply andb_prop in Hg as [Hg H3]. apply andb_prop in Hg as [Hg H2]. apply andb_prop in Hg as [H0 H1].
  apply sv_eqb_sound in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite H0, Elo, Ehi.
  rewrite !soff_lit_small by lia.
  eapply pointwise_clear_disjoint; [exact (HG e sz Hin) | lia | lia].
Qed.

Lemma objs_clear_e_sound : ltac2:(tb__ "0|7|
S9S29S2eSbS6A2M0A1S19S3aQ40M1A1S6S7eS27S24R5A1S22R3A1A3S0S2cS5dR5R4A2S2dA3S48Z0R3A2S4S48S47S3bG1R5A2R4A2M2Z7fff7f800000A2S48G2S4fS3bG1SdR8P1A2A2Z800000A2A2A2S6S1S48S3bG1R7A2M3R1A2S49R1S47G3R6A2A2A2S2S1S48Z10000R2A2S49R2Z646000A2A2A1F_;Fx;SbS6S76G0S33SbS6R2R1A4RbA3S6S1S48S3bG1RbA2M4R1A2S49R1S47G4RaA2A2A2S2S1S48S3bG1ScRfR5A2A2M5R2A2S49R2S47G5R4A2A2A2A1F_;Fx;F_;Fsz;Fe;SaS76SaR1S12RaA1A3S17S11RdR2A2S33S6S6S3bG1RaA2M6S47G6R9A2A4A2F_;Fo;F_;F_;F_;F_;F_;F_;Fn;Fa;FS;FGe;Frho;").
Proof.
  intros rho Ge S a n HF Hb Hn Hceil Hpw HG o Hin.
  pose proof (proj1 (forallb_forall _ _) Hb o Hin) as Ho. unfold obj_clear_e in Ho.
  apply Bool.orb_prop in Ho as [Ho|Ho]; [apply Bool.orb_prop in Ho as [Ho|Ho]|].
  - eapply img_clear_sound; eauto.
  - eapply high_clear_sound; eauto.
  - eapply eblk_clear_sound; eauto.
Qed.

Definition agree_vars (n : positive) (rho rho' : valuation) : Prop := ltac2:(tb__ "0|0|
S1S7S7bR1Vn;A2S0S3aQ40A1SdVrho';R2A2SdVrho;R2A2A3F_;Fi;S7S0S29S3aQ8A1A1S21Vrho';R1A2S21Vrho;R1A2A3Fl;A2").
Lemma agree_vars_refl : ltac2:(tb__ "0|0|
S7S9S56R2R1R1A3Frho;Fn;").
Proof. intros n rho. split; intros; reflexivity. Qed.
Lemma agree_vars_below : ltac2:(tb__ "0|0|
S7S9S9S9S56R4R3R2A3S15R5R3R2A3S56R6R5R3A3F_;F_;Frho'';Frho';Frho;Fn;").
Proof.
  intros n rho rho' rho'' [A1 A2] (B1 & B2 & B3). split.
  - intros i Hi. rewrite <- (B1 i Hi). apply A1. exact Hi.
  - intros l. rewrite <- (B2 l). apply A2.
Qed.
Lemma agree_vars_set_rm : ltac2:(tb__ "0|0|
S7S9S9S3aQ40A1S30S3aQ8A1A1F_;S56R4R3R2A3S56R5R4S79R3R2A2A3F_;Ff;Frho';Frho;Fn;").
Proof. intros n rho rho' f [A1 A2]. split; [intros i Hi; cbn; apply A1; exact Hi | intros l; cbn; apply A2]. Qed.
Lemma agree_vars_le : ltac2:(tb__ "0|0|
S7S7S9S9S7cR3R4A2S56R5R3R2A3S56R5R4R3A3F_;F_;Frho';Frho;Fn';Fn;").
Proof. intros n n' rho rho' Hle [A1 A2]. split; [intros i Hi; apply A1; lia | exact A2]. Qed.

Lemma LQA1 : ltac2:(tb__ "0|0|
S51S7S9S29S3aQ40A1A1S3eS6dS3S52S8R6R5R4R3S2bS3cS3fR2S5eA2S2aS3cA1A3R1A7S5S9S9S1S15R6R5R1A3S50S8R7R3R1R4R2A6A2Lrho';A2A2Fw;FE;Ftp;Frho;Fn;FJ;").
Proof.
  intros J n rho tp E w. split.
  - intros (L & rho' & Hin & Hag & Hsm & Hk). destruct Hin as [<-|[]]. exists rho'. split; [exact Hag|split; assumption].
  - intros (rho' & Hag & [Hsm Hk]). exists (mkLeafA E RsCut), rho'. split; [left; reflexivity|]. split; [exact Hag|split; assumption].
Qed.

Definition ARGF (rho : valuation) (a : word) : Prop := ltac2:(tb__ "0|3|
S1S48S47S3bQ40M0SdVrho;P1A2A2Z10A2M1S3bG0Va;A2M2A2S4S49G2S47G1S4dZ8S3bG0SdVrho;P2A2A2A2A2A2S1S48S47S47S3bG0SdVrho;P4A2A2S3bG0SdVrho;P5A2A2A2Z1A2G2A2S49G2S3bG0SdVrho;P6A2A2A2A2A2A2").
Definition RMH (rho rho' : valuation) : Prop := ltac2:(tb__ "0|0|
S3aQ40A1S57Vrho;R1A2S0S30S3aQ8A1A1S14Vrho';R2A2S14Vrho;R2A2A3F_;Fa;").
Lemma ARGF_ext : ltac2:(tb__ "0|1|
S9S9S3aQ40A1M0S7S7bR1P7A2S0G0SdR4R2A2SdR5R2A2A3F_;Fi;S3S57R3R2A2S57R4R2A2A2F_;Fa;Frho';Frho;").
Proof. intros rho rho' a E. unfold ARGF. rewrite !E by lia. tauto. Qed.
Lemma RMH_refl : ltac2:(tb__ "0|0|
S9S55R1R1A2Frho;").
Proof. intros rho a _. reflexivity. Qed.
Lemma RMH_trans : ltac2:(tb__ "0|0|
S9S9S9S55R3R2A2S7S7bR1P7A2S0S3aQ40A1SdR5R2A2SdR6R2A2A3F_;Fi;S55R4R3A2S55R6R4A2F_;F_;F_;Frho'';Frho';Frho;").
Proof. intros rho rho' rho'' H1 E H2 a Ha. rewrite (H2 a) by (apply (proj2 (ARGF_ext rho rho' a E)); exact Ha). apply H1. exact Ha. Qed.
Lemma RMH_below : ltac2:(tb__ "0|0|
S7S9S9S9S55R3R2A2S15R5R3R2A3S55R5R3A2F_;F_;Frho'';Frho';Frho;Fn;").
Proof. intros n rho rho' rho'' H1 (_ & _ & M) a Ha. rewrite <- (M a). apply H1. exact Ha. Qed.
Lemma RMH_set_rw : ltac2:(tb__ "0|0|
S9S9S7S3aQ40A1S55R4R3A2S55R5S8dR4R3R2A3A2F_;Fv;Fi;Frho';Frho;").
Proof. intros rho rho' i v H a Ha. cbn. apply H. exact Ha. Qed.
Lemma RMH_set_rm : ltac2:(tb__ "0|2|
S9S9S3aQ40A1M0S30S3aQ8A1A1M1Fx;S55R3R2A2G0S57R5R1A2S0G1R4R2A1S14R5R2A2A3F_;Fa;S55R5S79R4R3A2A2F_;F_;Ff;Frho';Frho;").
Proof. intros rho rho' f H Hf a Ha. cbn. rewrite (Hf a Ha). apply H. exact Ha. Qed.
Lemma RMH_unmap : ltac2:(tb__ "0|2|
S9S9S3aQ40M0A1M1G1S55R4R3A2S48S47S3bG0R3A2S3bG0R2A2A2S47S3bG0SdR5P1A2A2Z10A2A2S55R6S79R5S8cS14R5A1R4R3A3A2A2F_;F_;Fn;Fa0;Frho';Frho;").
Proof.
  intros rho rho' a0 n H Hn. apply RMH_set_rm; [exact H|]. intros a [Ha _]. rewrite unmap_range_at.
  destruct (in_range a0 n a) eqn:E; [|reflexivity]. apply in_range_spec in E. lia.
Qed.
Lemma RMH_absorb : ltac2:(tb__ "0|0|
S9S9S29SaA1S61S55R4R3A2S3aQ40A1S57R6R1A2S2S8eR6R5R2A3A1F_;Fa;S55R6S8fR5R4R3A3A2F_;F_;Fms;FR;Frho';Frho;").
Proof.
  intros rho rho' R ms H HR a Ha. unfold rho_absorb. cbn [rm].
  destruct (in_ranges_dec rho' R a) as [Hi|]; [exfalso; exact (HR a Ha Hi) | apply H; exact Ha].
Qed.

Definition cfg1_okA (fuel : nat) (cutpcs : list Z) (g : positive) (S T : axst) : bool := ltac2:(tb__ "0|2|
S34S34S7dVg;S10S3dVS;A1M0A1A2S38SeG0A1A1A2S30S29S3cA1M1A1S2cLx;S40S8Vfuel;Vcutpcs;VS;S2dA5G1S86S3cS3cS89Vg;S43R1A1VT;A3LL;R1A3Lleaves;S2fX30x2A2").

Lemma cfg1_post : ltac2:(tb__ "0|0|
S51S7S3eS3eS9S29S3aQ40A1A1S29S3cA1S6dS7S53S8R1R9A3Fn;S7cR8S10S3dR7A1A1A2S0S2cS86S3cS3cS89RaS43R1A1R8A3LL;R4A3S2dA3S52S8RbS10S3dR9A1A1R7R6R5R4A7S52S8RcRbR8R7S2bS3cS3fR9S5fA2S2aS3cA1A3R5A7F_;F_;F_;F_;Fw;Fleaves;Ftp;Frho;FT;FS;Fg;FJ;").
Proof.
  intros J g S T rho tp leaves w Hst Hg Hm (L & rho' & HinL & Hag & Hsm & Hk).
  rewrite forallb_lazy_eq in Hm. pose proof (proj1 (forallb_forall _ _) Hm L HinL) as HL.
  apply leaf_matches1A_true in HL as [Hid He].
  exists (mkLeafA T RsSymJump), (rho_sub rho' (infer_sub g (ax_S (la_state L)) (ax_S T))). split; [left; reflexivity|].
  split.
  - eapply agree_below_trans; [eapply agree_below_le; [exact Hg | exact Hag] | apply rho_sub_agree; exact Hid].
  - exact (SPA_entails segsA J g (la_state L) T _ rho' tp w He Hid (Hst g) (conj Hsm Hk)).
Qed.

Lemma run_cfg1 : ltac2:(tb__ "0|0|
S6dOF_;S51S35S29S6A1S7S3eS3eS9S29S3aQ40A1A1S54S8R9R8A3S7S53S8R1RaA3Fn;S0S2cS5aR9R8R7R6R5A5S2dA3S6eS8RcS50S8RbR7R5R4A5S52S8RbR8R5R4S2bS3cS3fR6S5fA2S2aS3cA1A3A6A4F_;F_;F_;Ftp;Frho;FT;FS;Fg;Fcutpcs;Ffuel;FJ;Fok;").
Proof.
  intros ok J fuel cutpcs g S T rho tp Hok Hst Hchk. unfold cfg1_okA in Hchk.
  apply andb_prop in Hchk as [Hgl Hchk]. apply andb_prop in Hgl as [Hg Hlen]. apply Pos.leb_le in Hg.
  destruct (ss_lenient (ax_S S)) eqn:HlS; [discriminate|].
  destruct (sym_runA segsA fuel cutpcs S true) as [leaves|] eqn:Hrun; [|discriminate].
  eapply triple_conseq; [intros w Hw; exact Hw | | apply triple1_triple; eapply sym_run_soundA; [exact Hrun | exact Hok | exact HlS | apply Hst]].
  intros w Hw. eapply cfg1_post; eauto.
Qed.

Lemma erun_cfg1 : ltac2:(tb__ "0|0|
S51S35S29S6A1S7S3eS3eS9S29S3aQ40A1A1S7S53S8R1R9A3Fn;S0S2cS5aR8R7R6R5R4A5S2dA3S6fS8S50S8RaR6R4R3A5S52S8RaR7R4R3S2bS3cS3fR5S5fA2S2aS3cA1A3A6A3F_;F_;Ftp;Frho;FT;FS;Fg;Fcutpcs;Ffuel;FJ;").
Proof.
  intros J fuel cutpcs g S T rho tp Hst Hchk. unfold cfg1_okA in Hchk.
  apply andb_prop in Hchk as [Hgl Hchk]. apply andb_prop in Hgl as [Hg Hlen]. apply Pos.leb_le in Hg.
  destruct (ss_lenient (ax_S S)) eqn:HlS; [discriminate|].
  destruct (sym_runA segsA fuel cutpcs S true) as [leaves|] eqn:Hrun; [|discriminate].
  eapply etriple_conseq; [intros w Hw; exact Hw | | eapply sym_run_etripleA; [exact HlS | apply Hst | exact Hrun]].
  intros w Hw. eapply cfg1_post; eauto.
Qed.
End StartALib.

