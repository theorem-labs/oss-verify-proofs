(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From Stdlib Require Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double nn Asan_set_shadow_iface Lib_tess_polygon_states.

(* [comment removed for export] *)
Module Start6States.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "false"; "app"; "bool"; "true"; "list"; "prod"; "Some"; "option"; "length"; "nat"; "pair"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "SAlu"; "sobj"; "sprop"; "SVar"; "cell"; "ss_objs"; "SExt"; "mkObj"; "DZero"; "SPUle"; "ss_pc"; "ss_regs"; "mkSS"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_resv"; "swf"; "SPAlign"; "SPEq"; "ss_next"; "c_val"; "mkCell"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States"; "R16b"; "R16pre"; "SITE16"; "c1"; "F16c"; "O_lowpg"; "O_ss"; "R16m"; "R16r"; "a0_16"; "ES17"; "LOWPG"; "PB"; "PE"; "R16c"; "SSB"; "byte_cells17"; "classes16"; "is_zero_cell16"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_AND"; "aluop"; "mulop"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "mul"; "add"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "mkAX"; "sym_runA"; "FE"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Start5bStates"; "S_s15ok"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "list_set"; "@Stdlib.Lists.List"; "In"; "filter"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Start5bStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition SITE16 : Z := 0x78840.
Definition RA16 : Z := 0x68264.
Definition run15b__R : option (list leafA) := ltac2:(tb__ "0|0|
S52S59U7d0S0S2dS34S1S2dA1A3S5aS5A5").
Local Strategy expand [run15b__R].
Definition R16pre : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 S_s15ok (ro1__)))) run15b__R).
Lemma run15b : ltac2:(tb__ "0|1|
S30S9S6S50A1M0A1S52S59U7d0S0S2dS34S1S2dA1A3S5aS5A5S8G0S0S50S58S33S5eA2S1S50A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run15b__R <: run15b__R = Some [mkLeafA R16pre RsCut]). Qed.
Definition a0_16 : sv := ltac2:(tb__ "0|0|
S10S47S10S45S13P1A1SeZf5fA1A3SeZfffffffffffff000A1A3").
Lemma R16pre_at : ltac2:(tb__ "0|2|
S31S30S2dS1aS4fS33A1M0A1S34A3S31S30S2eS25G0A1P4fA3S31S30SfS5bSfUaS1bG0A1SeZ0A1A4S3bA3S31S30S6S7SfSfA2M1A1S54S33A1S1G1A1A3S31S30SfS55S33A1SeS4eA1A3S30SbSaS11S15G0A1A2U18A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition c1 (t : Z) : Z := 8388608 + 4096 * t.
Definition PB (t : Z) : Z := if t =? 0 then 0x7fff8000 else 0x7fff9000.
Definition PE : Z := 0x800f8000.
Definition LEN16 (t : Z) : Z := if t =? 0 then 1048576 else 1044480.
Definition F16c (t : Z) : list sprop := ltac2:(tb__ "0|9|
S3S12S0S12S23P4fM0ZfA2S0S12S23P50M1ZcA2S1S12A1M2A3A3S3S12S53G1S13G0A1M3A2S0S12S19SeS4aZ7fff7f800000S4bZ1000Vt;A2A2A1G3A2S0S12S19G3SeS4aS4dZ2Z2fA2S35Vt;A1M4A2A1A2S0S12S19S10S45S13P1A1M5SeS4aNa0G4A2A1A3G3A2S0S12S19G3S10S45G5SeS4aZf5fG4A2A1A3A2S0S12S24S10S47S10S45S13G1A1M6SeS3eVt;A1A1A3SeZfffA1M7A3SeZ0A1M8A2S0S12S24S10S47S10S45G6SeS3fA1A3G7A3G8A2G2A3A3A3A3A3A3A3A3").

Definition SSB (t : Z) : sv := ltac2:(tb__ "0|0|
S10S45S13P50A1SeS4cZ7fff8000S4bZ200Vt;A2A2A1A3").
Definition O_ss (t : Z) : sobj := ltac2:(tb__ "0|0|
S17S41Vt;A1SeZ0A1SeZ100000A1S1S14A1S18A5").

Definition LOWPG : Z := 0x800bc000.
Definition O_lowpg : sobj := mkObj (SLit LOWPG) (SLit 0) (SLit 0x4600) [] DZero.

Definition ES17 : list sv := ltac2:(tb__ "0|2|
S0SfS16S2Q8M0S13P22A1M1A3S0SfS16S2G0S10S46G1SeZ8A1A3A3S0SfS16S2G0S10S46G1SeZ10A1A3A3S0SfS16S2G0S10S46G1SeZ18A1A3A3S0SfS16S2G0S10S46G1SeZ20A1A3A3S0SfS10S46G1SeZ28A1A3S0SfS10S46G1SeZ30A1A3S0SfS10S46G1SeZ38A1A3S1SfA1A3A3A3A3A3A3A3A3").
Fixpoint byte_cells17 (off : Z) (es : list sv) : list cell :=
  match es with [] => [] | e :: r => byte_cells17 (off + 1) r ++ [mkCell (SLit off) 1 e] end.
Definition o21m : sobj := ltac2:(tb__ "0|1|
S17S13P24A1SeZ0A1M0SeZ1000A1S0S14S27G0Z8S13P22A1A3S1S14A1A3S18A5").

Definition R16b : sstate := Eval vm_compute in
  (let St := ax_S R16pre in mkSS (ss_pc St) (ss_regs St) (ss_fregs St) (ss_fcsr St) (ss_resv St) (ss_objs St) (ss_facts St) 81%positive (ss_lenient St)).

Definition R16r (t : Z) : sstate := ltac2:(tb__ "0|0|
S1cS1aS32A1S5fSfS1bS32A1UaS10S45S13P4fA1SeS35Vt;A1A1A3A4S1fS32A1S1eS32A1S21S32A1S15S32A1S3S12S36Vt;A1S1dS32A1A3P51S20S32A1A9").

Definition R16m (t : Z) : sstate := replace_obj_at (R16r t) 21 o21m.

Definition R16c (t : Z) : axst := ltac2:(tb__ "0|1|
S51S1cS1aS32A1S1bS3aVt;A1M0A1S1fS32A1S1eS32A1S21S32A1S3S11S15S39Vt;A1A1S0S11S37S0S11S38Vt;A1S1S11A1A3A3A3S1dG0A1P51S20S32A1A9S1S7SfSfA2A1SeS4eA1A3").

Definition classes16 : list Z := ltac2:(tb__ "0|0|
S0S2dZ0S0S2dZ1S0S2dZ2S0S2dZ3S0S2dZ4S0S2dZ5S0S2dZ6S0S2dZ7S1S2dA1A3A3A3A3A3A3A3A3").

Definition is_zero_cell16 (c : cell) : bool := ltac2:(tb__ "0|4|
SfS4Lx;S26Vc;A1S2dS2dS4Lz;R1S5S2eS2Lp;M0G0X2dx3Lz;S2eS2Li;S48SfSfS2Lb;La;M1Lop;M2G2S49G1Lop;M3G3S4S2fSfS2La;Lw;Lsgn;S2eSfS2dS2Lk;Li;Ll;Xfx8").
Definition dzc16 (o : sobj) : sobj := ltac2:(tb__ "0|0|
S17S28Vo;A1S2cVo;A1S2bVo;A1S61S14S14SdS44R1A1A1Lc;S29Vo;A1A3S2aVo;A1A5").

Lemma R16b_eq : ltac2:(tb__ "0|1|
S30S57S56S33S1cS1aS4fS33A1M0A1S1bG0A1S1fG0A1S1eG0A1S21G0A1S15G0A1S1dG0A1P51S20G0A1A9A2S51S32S1S7SfSfA2A1SeS4eA1A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma sd16 : ltac2:(tb__ "0|a|
S2dS60S2dR1S43A3S31S30S9S7S6S7SfSfA2M0A1M1S6S12A1M2A2M3A1S5dS32S3aR2A1M4A2S8G3ScG1G2S0G0ScSfSfS3bS10S45S13P4fA1SeS35R2A1A1A3A4S1G0A1A3S36R2A1A4A2A3S31S30S4S22G4A1S5A3S31S30S4S22S39R2A1M5A1S5A3S31S30S4S22S4fS40R2A1A1M6A1S5A3S31S30S9S11A1S62S11S15G4A1U15A3S8S11S17S13P24A1SeZ0M7A1SeZ1000A1S3S14S42G7S3cA2S1S14A1A3S18A5A2A3S31S30S4S5cG4G5A2S5A3S31S30S6S11A1S15G6A1S3S11S3S11S15G5A1M8S0S11S37S1S11A1M9A3A3S0S11S38R2A1G9A3A3A3S31S30S2eS25G5A1P51A3S30SbSaS11G8A2U18A3A2A2A2A2A2A2A2A2F_;Ft;").
Proof.
  intros t Ht. destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2).
Qed.
End Start6States.

(* [comment removed for export] *)
Module StartNodes2E.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "rw"; "SVar"; "eval"; "rm"; "ss_next"; "ss_pc"; "valuation"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_base"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "pair"; "prod"; "Some"; "list"; "option"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "alloc_top"; "m_vmmaps"; "map_has"; "map_remove"; "region_free"; "vm_init_sp"; "vm_maps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes2"; "munmap_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA MmapFixedA MmapFixedA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib KxA Placement.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section MunmapE.

Variables (E : axst) (v : positive) (lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)) (nxt : positive).
Let n : word := Z_to_bv 64 lenZ.

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S6S12VE;A1S7S2bA1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S1eS1fA1S32S17SeS11VE;A1A1A2S1cS1fS20A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S6S8S11VE;A1Z11A2S7Zd7A1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S6S8S11VE;A1ZaA2SaVv;A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S6S8S11VE;A1ZbA2S7VlenZ;A1A3").
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hsmall : lenZ < 2 ^ 62.
Hypothesis Hnxt : ltac2:(tb__ "0|0|
S34SdS11VE;A1A1Vnxt;A2").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S18S2cVGl;S11VE;A1A2S19A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Local Notation munmap_ok := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes2.munmap_ok E nxt) (only parsing).
Local Notation n_valM := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes2.n_valM lenZ Hpos Hsmall) (only parsing).
Local Notation mmap_n_lit := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes2.mmap_n_lit lenZ Hnl Hpos Hsmall) (only parsing).

Theorem munmap_enode : ltac2:(tb__ "0|8|
SfS1dS5Q40M0A1M1A1S9R2Vv;A2G1S0S10S16S4G0R1A2Z1000A2Z0A3S3S14S13S4G0R2A2M2VlenZ;A2Z10000A2S14Z643000G2A2A2S14S13S4G0R3A2VlenZ;A2S24S25Vm;A1M3A1A2S0S10S4G0S9R6P1A2A2S4G0S29G3A1A2A3S0S18S26S2aG3A1M4R5Vn;A3S19A3G1S23S1bG1G1A2S1aG1G1R7R1A4G4A3S0G1R2Vn;A3F_;Fs;S0S18S28S27G4R7A2R7Vn;A3S19A3S6S10S23S1bS6S10A2S1aS6S10R2R1A4VGl;A3S10S1S14S4G0RcA2M5R1A2S15R1S13G5VlenZ;A2A2A2S2S1S14S4G0SbRfR5A2A2M6R2A2S15R2S13G6R4A2A2A2A1F_;Fx;F_;Fsz;Fe;S2eS17S22S17S21Vm;VB;A2VE;RbRaA5S22S17S21S2fVm;R9Vn;A3VB;A2S2dVE;Vnxt;A2S31RbS30ScRbA1R9Vn;A3A2S33S4G0R9A2M7S13G7VlenZ;A2RaA3A5A3F_;F_;F_;F_;F_;F_;F_;F_;Ta;Ftp;Frho;").
Proof using All.
  intros rho tp a Hal Hlo Hceil Hv1 Hhas Huniq Hfree HG. pose proof (alloc_top_lt (m_vmmaps m)) as CL. pose proof n_valM as Nv.
  destruct mmap_n_lit as [MN MNZ]. change (bv_unsigned n = lenZ) in Nv. change (mmap_n (Z_to_bv 64 lenZ) = n) in MN.
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & _).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & _).
  rewrite R10 in G0. rewrite R11 in G1. cbn [eval] in G0, G1. change (rw rho v) with a in G0.
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros E0. apply (f_equal bv_unsigned) in E0. rewrite u64_of_lit in E0 by lia. rewrite u64_of_lit in E0 by lia. lia. }
  assert (Hwrap : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE).
  { rewrite G0, G1, MNZ. unfold TASK_SIZE. pose proof (alloc_top_bounds _ Htop) as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB. lia. }
  assert (Hhas' : map_has (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, G1, MN, Evm. exact Hhas. }
  assert (Hal' : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0; exact Hal).
  exists ([], mkCfg (after_sys_mem ms (Z_to_bv 64 0) (unmap_range (ms_mem ms) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1))))
                    (munmap_model md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)))).
  split; [exact (wstep_munmap_exact_introA segsA ms md _ Hh H215 Hal' Hlen Hwrap Hhas' [] Hp)|].
  rewrite G0, G1, MN.
  set (h' := munmap_vm (m_vmmaps md) a n).
  assert (Emd : munmap_model md a n = vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps h' md)) by reflexivity.
  rewrite Emd. split.
  + unfold munmap_ok. rewrite <- Nv.
    replace (mkAX (S_after (ax_S E) (SLit 0) (ss_objs (ax_S E)) nxt) [] (SLit SHB)) with (ax_setS E (S_after (ax_S E) (SLit 0) (ss_objs (ax_S E)) nxt))
      by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
    apply (smatchA_after_munmap segsA rho _ tp E [] ms md [] h' a n (Z_to_bv 64 0) (SLit 0) nxt Hsp).
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * rewrite Evm. exact Huniq.
    * rewrite Evm. exact Hfree.
    * exact Hal.
    * rewrite Nv. exact Hnl.
    * rewrite Nv. unfold two_pow_64 in CL. lia.
    * intros o Ho. rewrite Nv.
      apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear ltac:(lia) ltac:(right; revert Hceil; unfold alloc_top; rewrite stack_max_size_val, <- Hv1; intros Hceil; exact Hceil)); [|exact HG|exact Ho].
      intros x Hx. lia.
    * rewrite HX. intros rr y [].
    * apply agree_below_refl.
    * exact Hnxt.
    * reflexivity.
    * reflexivity.
  + cbn [w_tr w_cfg fst snd cfg_model]. split; [reflexivity|]. split.
    * unfold munmap_model, with_mmap_destroyed. unfold h'. rewrite Evm. apply erase_mat_cong_forget. exact Hem.
    *
      pose proof HMI as (HW & HT & Hmat & Hsub & HpaidMI & Hlc & Hivs & Hlm & Htm).
      pose proof (used_munmap_le md h' a n Hivs ltac:(rewrite Evm; exact Hfree) eq_refl eq_refl) as U1.
      set (md1 := with_vmmaps h' md) in *.
      set (lo := bv_unsigned a) in *. set (hi := lo + bv_unsigned n) in *.
      assert (Wl1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact (proj2 (proj2 Hivs))).
      assert (HT' : List.NoDup (tp_forget lo (lo + lenZ) tp)) by (unfold tp_forget; apply List.NoDup_filter; exact HT).
      assert (U2 : (length (unpaid (vm_forget_range lo hi md1) (tp_forget lo (lo + lenZ) tp)) <= length (unpaid md tp))%nat).
      { apply List.NoDup_incl_length; [unfold unpaid; apply List.NoDup_filter; exact HT'|].
        intros p Hpp. assert (Hp' : In p (unpaid (vm_forget_range lo hi md1) tp)).
        { unfold unpaid in Hpp |- *. apply filter_In in Hpp as [Hpp Hb]. apply filter_In. split; [|exact Hb].
          unfold tp_forget in Hpp. apply filter_In in Hpp as [Hpp _]. exact Hpp. }
        pose proof (unpaid_forget_incl md1 lo hi tp p Wl1 Hp') as Hq. unfold md1 in Hq. rewrite (unpaid_ext md (with_vmmaps h' md) tp) in Hq by reflexivity. exact Hq. }
      unfold paid in Hpaid |- *. pose proof page_size_pos. nia.
Qed.
End MunmapE.
End StartNodes2E.

(* [comment removed for export] *)
Module Start5.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "not"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sv"; "sprop"; "eval"; "rm"; "agree_below"; "holds"; "ss_facts"; "SVar"; "rl"; "sobj"; "DZero"; "SLit"; "SPUle"; "ob_dflt"; "odefault"; "sprop_below"; "sprop_eqb"; "ss_next"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "sub"; "mul"; "div"; "of_nat"; "to_nat"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "vm_reserved"; "vm_limit"; "vm_init_sp"; "alloc_top"; "event"; "region_free"; "Model"; "vm_noaccess"; "lazy_interior"; "m_vm_lazy"; "map_has"; "map_remove"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.Seg5"; "TP12"; "m12"; "vals12"; "B12x"; "rm_same_band"; "G12b"; "Post5"; "m13"; "stackshadow_zero"; "G12"; "m15"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "cons"; "list"; "app"; "bool"; "nil"; "true"; "option"; "Some"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "munmap_model"; "init_sp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "mkLeafA"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.Seg5.S13a.S13"; "m14"; "G13b"; "@Stdlib.Lists.List"; "In"; "existsb"; "filter"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.Seg5.S13a"; "m13"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4"; "TP11"; "B12"; "m8"; "n9"; "Z11"; "ZD11"; "bandav"; "G11c"; "n7"; "m10"; "m11"; "m9"; "priZ"; "spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "agree_vars"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS"; "RMH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.Seg5.S12b"; "q12"; "n12"; "rm_same_band"; "TP12"; "e12"; "G12b"; "shZ"; "stackshadow_zero"; "B12x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Start5CallStates"; "E_s13g"; "IP12f"; "E_s13"; "R12"; "s12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start5States"; "L12r"; "L12x"; "C12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "E_k12d"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Start5bStates"; "E_s14"; "E_s15"; "E_s15u"; "S_s15ok"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.Seg5.S13a.S13.S14"; "m15"; "G14b"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "pages_rev"; "unknown_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes2"; "munmap_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "zero_page_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA MmapA MmapFixedA SummaryA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib KxA Placement PlacementA Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.StartNodes2E.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Start5bStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Seg5.

Variables (m : Model) (a1 a2 : word) (B : Z).
Hypothesis Hres : ltac2:(tb__ "0|1|
S1S4aS47S6Q40A1M0G0A2A1S2bS29Vm;A1A1S94S1dA1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|3|
S1S4aS47S6Q40M0A1M1G1A2M2A1S2aS29Vm;A1A1S49G2S48G1G1Va2;S5G0Z38e000A2A4S49G2S48G1G1Va1;S5G0Z10000A2A4S49G2S48G1G1S5G0Z2008fff7000A2S5G0Zdfff0001000A2A4S49G2S48G1G1S5G0Z8fff7000A2S5G0Z20000000000A2A4S49G2S48G1G1S5G0Z7fff7000A2S5G0Z10000000A2A4S4dG2A1A3A3A3A3A3A3").
Hypothesis Hna : ltac2:(tb__ "0|3|
S1S4aS47S6Q40M0A1M1G1A2M2A1S32S29Vm;A1A1S49G2S48G1G1S5G0Z8fff7000A2S5G0Z20000000000A2A4S4dG2A1A3A3").
Hypothesis Hlz : ltac2:(tb__ "0|3|
S1S4aS47S6Q40M0A1M1G1A2M2A1S34Vm;A1S4bG2S33S5G0Z2008fff7000A2S5G0Zdfff0001000A2A2S4bG2S33S5G0Z8fff7000A2S5G0Z20000000000A2A2S33S5G0Z7fff7000A2S5G0Z10000000A2A2A3A3A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Ha1 : ltac2:(tb__ "0|2|
S0S1fZ643000S7Q40Va1;A2M0A2S0S3S1fS1eG0Z10000A2M1S64A2S1fS63G0A2A2S1fG1S2eS29Vm;A1A1A2A2A2").
Hypothesis Ha2 : ltac2:(tb__ "0|2|
S0S1fZ643000S7Q40Va2;A2M0A2S0S3S1fS1eG0Z38e000A2M1S64A2S1fS63G0A2A2S1fG1S2eS29Vm;A1A1A2A2A2").
Hypothesis HBlim : ltac2:(tb__ "0|0|
S1fS1eVB;Z1000000A2S2cS29Vm;A1A1A2").
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S45S8S4aS6Q40A1A1S4aS2fA1M0S31R5R4R3R2R1A4S1G0R3S4dS2fA1A3F_;Fmd;Ftr;Ftp;Frho;S46S1dVok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S45S8S4aS6Q40A1A1S4aS2fA1M0S31R5R4R3R2R1A4S1G0R3S4dS2fA1A3F_;Fmd;Ftr;Ftp;Frho;Sa3S1dVok;R2A3F_;FJ;").
Variables (P b4 b5 b6 : word).
Hypothesis HPL : ltac2:(tb__ "0|0|
S53S5Q40Z0A2Vm;S6fVP;A4").
Hypothesis HPL4 : ltac2:(tb__ "0|0|
S53S5Q40Z0A2S69Vm;VP;A2S6aVb4;A4").
Hypothesis HPL5 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2S72Vm;VP;Vb4;A3S5G0Z1000A2Vb5;A4").
Hypothesis HPL6 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2S70Vm;VP;Vb4;Vb5;A4S5G0Z10000A2Vb6;A4").

Let mE : Model := ltac2:(tb__ "0|0|
S71Vm;VP;Vb4;Vb5;Vb6;A5").
Local Notation P_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.P_facts m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_range := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.RI_range m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.RI_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation SB_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.SB_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation a12_off_P := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.a12_off_P m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation b4_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b4_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4) (only parsing).
Local Notation b5_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b5_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5) (only parsing).
Local Notation b6_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b6_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5 b6 HPL6) (only parsing).
Local Notation RIw := (RI P) (only parsing).

Lemma OKFx : ltac2:(tb__ "0|0|
S31S27S46S1dVok;S37R2R1A2A3FBB;Fmm;").
Proof using OKF. clear -OKF. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.

Definition vals12 (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S0S1S6Q40M0A1M1S9Vrho;P1bA2Va1;A3S0S1G1S9Vrho;P1cA2Va2;A3S0S1G1S9Vrho;P1dA2VP;A3S0S1G1S9Vrho;P1eA2S74VP;A1M2A3S0S1S27S23Z8S7G0S9Vrho;P1fA2A2A2S7G0G2A2A3S0S1G1S9Vrho;P20A2Vb4;A3S0S1G1S9Vrho;P21A2Vb5;A3S0S1G1S9Vrho;P22A2Vb6;A3S1S27S7G0S9Vrho;P1A2A2S7G0S2dS29Vm;A1A1A2A3A2A2A2A2A2A2A2A2").

Lemma vals12_agree : ltac2:(tb__ "0|0|
S28S8S8Sa4P23R3A2S3aR3A1S28Sa5R1R6A2S1S6Q40A1S9R5R2A2S9R6R2A2A3F_;Fi;S3aR4A1F_;F_;F_;Frho';Frho;Fn;").
Proof.
  clear. intros n rho rho' Hn (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9) A.
  unfold vals12. rewrite !A by lia. repeat split; assumption.
Qed.

Lemma mE_ledger : ltac2:(tb__ "0|7|
S0S1S4aS47S6Q40M0A1M1G1A2M2A1M3S2bS29VmE;A1M4A1S2bS29Vm;A1M5A1A3S0S1G3S2aG4A1S49G2S48G1G1Vb6;S5G0Z10000A2A4S49G2S48G1G1Vb5;S5G0Z1000A2A4S49G2S48G1G1Vb4;S6aA4M6S49G2S48G1G1VP;S6fA4S2aG5A1A3A3A3A3A3S0S1S27S2cG4A1S2cG5A1A3S0S1G1S2dG4A1S2dG5A1A3S1G3S32G4A1S49G2G6S32S29S69Vm;VP;A2A1A1A3A3A2A2A2A2").
Proof.
  clear. pose proof (m10_ledger m P b4 b5) as (L1 & L2 & L3 & L4 & L5).
  unfold mE, m11, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps. cbn [vm_reserved vm_maps vm_limit vm_init_sp vm_noaccess].
  rewrite L1, L2, L3, L4, L5. repeat split; reflexivity.
Qed.
Lemma top_mE : ltac2:(tb__ "0|0|
S1S27S2eS29VmE;A1A1S2eS29Vm;A1A1A3").
Proof. clear. pose proof mE_ledger as (_ & _ & _ & L4 & _). unfold alloc_top. rewrite L4. reflexivity. Qed.
Lemma init_sp_ok_mE : init_sp_ok (m_vmmaps mE).
Proof using Htop. clear -Htop. pose proof mE_ledger as (_ & _ & _ & L4 & _). unfold init_sp_ok in *. rewrite L4. exact Htop. Qed.
Lemma band_mE : ltac2:(tb__ "0|2|
S65S4bS47S6Q40A1M0G0A2S2bS29VmE;A1M1A1S2aG1A1A3S64S63A3").
Proof using Hmaps. clear -Hmaps. pose proof mE_ledger as (L1 & L2 & _). pose proof (m10_ledger m P b4 b5) as (K1 & K2 & _).
  rewrite L1, L2, <- K1, <- K2. apply (band_covered_after_grant (m10 m P b4 b5)). exact (band_m10 m a1 a2 Hmaps P b4 b5). Qed.

Lemma HG11c : ltac2:(tb__ "0|6|
S8S27S3aR2A1S4aS47S6Q40M0A1M1G1A2M2A1M3S2G3G3S1G3R2S4bG2R1S2aS29VmE;A1A1A3A3Ll;A2SaS27S5fS47SaS27A2S48SaS27R2R1A4S6eA3S3S2G1G1S2G1G1S0S5fG2S48G1G1R2R1A4R7A3S0S1fS7G0R2A2M4S7G0ScRaR5A2A2M5A2S1fS1eG5R4A2S1eG4S7G0R1A2A2A2A2A2Ls;A2Lb;A2S1fS1eS7G0ScR8R3A2A2R2A2R7A2A2F_;Fsz;Fe;F_;Fmaps;F_;FLB;Frho;").
Proof using HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim HPL4 HPL5 HPL6. intros rho LB (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & _) maps [l ->] e sz Hin.
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV. pose proof SB_val as SB.
  unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB. pose proof (urange P) as UP. pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB.
  pose proof mE_ledger as (_ & L2 & _). rewrite L2, Hmaps. left.
  unfold G11c in Hin.
  destruct Hin as [[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]]]; cbn [eval].
  - rewrite H27. exists a1, (Z_to_bv 64 0x10000). split; [apply in_app_iff; right; cbn [In]; tauto|]. rewrite u64_of_lit by lia. lia.
  - rewrite H28. exists a2, (Z_to_bv 64 0x38e000). split; [apply in_app_iff; right; cbn [In]; tauto|]. rewrite u64_of_lit by lia. lia.
  - exists P, n7. split; [apply in_app_iff; right; cbn [In]; tauto|].
    assert (Eri : bv_unsigned (eval rho ri30) = bv_unsigned RIw).
    { unfold ri30. cbn [eval]. rewrite H30. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
      change (bv_wrap 64 137438953472) with (2 ^ 37). rewrite RV. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
    change (eval rho ri30) with (eval rho ri30). fold ri30. rewrite Eri. unfold n7. rewrite u64_of_lit by lia. lia.
  - exists (Z_to_bv 64 0x2008fff7000), (Z_to_bv 64 0xdfff0001000). split; [apply in_app_iff; right; cbn [In]; tauto|].
    change (eval rho shRI_base) with (pRI rho).
    assert (Up : bv_unsigned (pRI rho) = bv_unsigned (rw rho 31%positive) + 0x47fff8000).
    { unfold pRI, shRI_base. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
      change (bv_wrap 64 19327320064) with 19327320064. apply bv_wrap_small. change (bv_modulus 64) with (2^64). pose proof (urange (rw rho 31%positive)). lia. }
    rewrite !u64_of_lit by lia. lia.
  - rewrite H33. exists b5, (Z_to_bv 64 4096). split; [apply in_app_iff; right; cbn [In]; tauto|]. rewrite u64_of_lit by lia. lia.
  - rewrite H34. exists b6, (Z_to_bv 64 65536). split; [apply in_app_iff; right; cbn [In]; tauto|]. rewrite u64_of_lit by lia. lia.
Qed.

Definition m12 (b7 : word) : Model := eager_model 4096 mE b7.
Definition G12 : list (sv * Z) := G11c.
Lemma clear12 : ltac2:(tb__ "0|0|
S1S4cS76S41S5aS8dA1A2S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma seg12a : ltac2:(tb__ "0|4|
S8S3aR1A1S58S1dVok;S43S1dS37VmE;S68VB;A1M0A2S8dR2S67R2A1A5S56S2S6Q40M1A1M2G2S0S53S5G1Z0A2VmE;S5G1Z1000M3A2R1A4S44S1dS37S39R1A1S1eG0G3A2A2P25S8cR4P24R1A3S67R4A1S49S59S5bS89S81A2S4dS59A1A3R2A7A2Lb7;A2Lw;A4F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 Ha1 Ha2 Hmaps Hna Hres Htop Hlz OKF OKP.
  intros rho HV. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1). pose proof mE_ledger as (M1 & M2 & M3 & M4 & M5).
  eapply triple_seq.
  { apply triple1_triple.
    apply (eager_rw_node ok OKF OKP E_k12d 4096 mE (B12 B) G12 37%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear12.
    + rewrite M1. exact Hres.
    + exact init_sp_ok_mE.
    + exact band_mE.
    + rewrite M3. unfold B12, B11. lia.
    + apply (HG11c rho _ HV). exists []. reflexivity.
    + rewrite M4. exact Hv1. }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA mE (B12 B)) (OKFx _ _) (fun n => stableA_KxA segsA n mE (B12 B)) _ SPIN12 200%nat SPIN_MMAPORDIE);
      [reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact run12_fail | exact spin12].
  - apply triple_ex; intros b7. apply triple_pure; intros HPL7.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b7; split; [exact HPL7|exact Hw] |].
    apply triple1_triple.
    assert (N : ss_next (ax_S E_k12d) = 36%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    change (eager_ok E_k12d 4096 37) with S_s12ok. rewrite N.
    eapply sym_run_soundA; [exact run12a | apply OKFx | reflexivity | apply stableA_KxA].
Qed.

Section S12b.
Variable b7 : word.
Hypothesis HPL7 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2VmE;S5G0Z1000A2Vb7;A4").

Definition shZ (rho : valuation) : Z := ltac2:(tb__ "0|0|
S1eS24S7Q40S9Vrho;P1A2A2Z8A2Z7fff8000A2").
Definition q12 (rho : valuation) : Z := ltac2:(tb__ "0|0|
S22S7eVrho;A1Z20000A2S27S22R1S21R1Z1000A2A2Ts;").
Definition e12 (rho : valuation) : Z := ltac2:(tb__ "0|0|
S22S7eVrho;A1Z9A2S27S22R1S21R1Z1000A2A2Ts;").
Definition n12 (rho : valuation) : nat := ltac2:(tb__ "0|0|
S26S1eS24S22S7cVrho;A1S78Vrho;A1A2Z1000A2Z1A2A1").
Definition TP12 (rho : valuation) : list word := ltac2:(tb__ "0|0|
S4bS6Q40A1S9aS78Vrho;A1S79Vrho;A1A2S67Vrho;A1A3").

Definition stackshadow_zero (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S27S0S1fS78Vrho;A1M0R1A2S20R1S1eG0S23Z1000S25S79Vrho;A1A1A2A2A2A2S1S4fS6Q8M1A1M2A1SdVrho;S5Q40R2A2A2S50G2S5G1Z0A2A2A3F_;Fz;").
Definition B12x : Z := ltac2:(tb__ "0|1|
S1eS1eS68VB;A1Z1000M0A2S23G0Z21A2A2").

Lemma q12_ext : ltac2:(tb__ "0|1|
S8S8S1S6Q40A1S9R1P1M0A2S9R2G0A2A3S0S1S27S78R2A1S78R3A1A3S0S1S27S7cR2A1S7cR3A1A3S1S52S79R2A1S79R3A1A3A2A2F_;Frho';Frho;").
Proof. clear. intros rho rho' H. unfold n12, q12, e12, shZ. rewrite H. repeat split; reflexivity. Qed.
Lemma TP12_agree : ltac2:(tb__ "0|0|
S8S8S75P24R2R1A3S1S4aS6Q40A1A1S7bR2A1S7bR3A1A3F_;Frho';Frho;").
Proof.
  clear. intros rho rho' HA. pose proof HA as [A _]. destruct (q12_ext rho rho' (A 1%positive ltac:(lia))) as (E1 & E2 & E3).
  unfold TP12. rewrite E1, E3, (TP11_agree rho rho' HA). reflexivity.
Qed.
Lemma stackshadow_zero_ext : ltac2:(tb__ "0|3|
S8S8S1S6Q40A1M0S9R1P1M1A2S9R2G1A2A3G0S1S4fS6Q8A1A1SdR3R1A2SdR4R1A2A3Fa;S7fR4A1M2G2F_;F_;F_;Frho';Frho;").
Proof.
  clear. intros rho rho' H Hrm Hz. destruct (q12_ext rho rho' H) as (E1 & E2 & E3). unfold stackshadow_zero. rewrite E1, E3.
  intros z Hzz. rewrite Hrm. apply Hz. exact Hzz.
Qed.

Definition rm_same_band (rho rho' : valuation) : Prop := ltac2:(tb__ "0|2|
S6Q40M0A1S0S1fS64S7G0R1A2M1A2S20G1S63A2A2S1S4fS6Q8A1A1SdVrho';R2A2SdVrho;R2A2A3F_;Fa;").
Lemma rm_same_band_refl : ltac2:(tb__ "0|0|
S8S7aR1R1A2Frho;").
Proof. clear. intros rho a _. reflexivity. Qed.
Lemma rm_same_band_trans : ltac2:(tb__ "0|1|
S8S8S8S7aR3R2A2M0G0S7aR5R3A2F_;F_;Fr3;Fr2;Fr1;").
Proof. clear. intros r1 r2 r3 A1 A2 a Ha. rewrite (A2 a Ha). apply A1. exact Ha. Qed.
Lemma rm_same_band_agree : ltac2:(tb__ "0|0|
S28S8S8SeR3R2R1A3S7aR3R2A2F_;Fr2;Fr1;Fn;").
Proof. clear. intros n r1 r2 (_ & _ & R) a _. symmetry. apply R. Qed.

Lemma lazy_m12 : ltac2:(tb__ "0|2|
S1S4aS47S6Q40A1M0G0A2M1A1S34S39Vb7;A1A1S4bG1S33Vb4;S6aA2S34S69Vm;VP;A2A1A3A3").
Proof. clear. unfold m12, eager_model. rewrite m_vm_lazy_with_vmmaps. apply lazy_m11. Qed.
Lemma noacc_m12 : ltac2:(tb__ "0|2|
S1S4aS47S6Q40A1M0G0A2M1A1S32S29S39Vb7;A1A1A1S49G1S48G0G0Vb4;S6aA4S32S29S69Vm;VP;A2A1A1A3A3").
Proof. clear. unfold m12, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps. cbn [vm_noaccess]. apply mE_ledger. Qed.
Lemma m12_ledger : ltac2:(tb__ "0|6|
S0S1S4aS47S6Q40M0A1M1G1A2M2A1M3S2bS29S39Vb7;A1A1M4A1S2bS29Vm;A1M5A1A3S0S1G3S2aG4A1S49G2S48G1G1Vb7;S5G0Z1000A2A4S2aS29VmE;A1A1A3A3S0S1S27S2cG4A1S2cG5A1A3S1G1S2dG4A1S2dG5A1A3A2A2A2").
Proof.
  clear. pose proof mE_ledger as (L1 & L2 & L3 & L4 & L5).
  unfold m12, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps. cbn [vm_reserved vm_maps vm_limit vm_init_sp]. rewrite L1, L3, L4. repeat split; reflexivity.
Qed.
Lemma limit_m12 : ltac2:(tb__ "0|0|
S1S27S2cS29S39Vb7;A1A1A1S2cS29Vm;A1A1A3").
Proof. clear. apply m12_ledger. Qed.
Lemma init_sp_ok_m12 : init_sp_ok (m_vmmaps (m12 b7)).
Proof using Htop. clear -Htop. pose proof m12_ledger as (_ & _ & _ & L4). unfold init_sp_ok in *. rewrite L4. exact Htop. Qed.
Lemma band_m12 : ltac2:(tb__ "0|2|
S65S4bS47S6Q40A1M0G0A2S2bS29S39Vb7;A1A1M1A1S2aG1A1A3S64S63A3").
Proof using Hmaps. clear -Hmaps. pose proof m12_ledger as (L1 & L2 & _). pose proof mE_ledger as (K1 & _).
  rewrite L1, L2, <- K1. apply (band_covered_after_grant mE). exact band_mE. Qed.

Lemma b7_facts : ltac2:(tb__ "0|5|
S0S1fZ1000M0S7Q40M1Vb7;A2M2A2S0S6dG2G0A2S0S1fS1eG2G0A2S2eS29Vm;A1A1A2S0S1S27S21G2G0A2Z0A3S1S4cS30S4bS47S6G1A1M3G3A2S2bS29VmE;A1M4A1S2aG4A1A3Vb7;S5G1G0A2A3S4eA3A2A2A2A2").
Proof using HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. pose proof mE_ledger as (L1 & L2 & L3 & L4 & L5).
  pose proof (place_LB_A mE 4096 b7 init_sp_ok_mE ltac:(rewrite L1; exact Hres) band_mE ltac:(lia) ltac:(reflexivity) HPL7) as (PLB & Pimg & Pband & Ptop & _).
  pose proof HPL7 as (Hal & _ & _ & Hfree). rewrite top_mE in Ptop.
  assert (Hn : mmap_n (Z_to_bv 64 4096) = Z_to_bv 64 4096) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Hn in Hfree.
  change (LB_of 4096) with 0x1000 in PLB. split; [exact PLB|]. split; [exact (bandav_intro _ _ Pband)|]. repeat split; assumption.
Qed.

Definition G12b : list (sv * Z) := ltac2:(tb__ "0|1|
S4bS47SaS27A2M0S6eS49G0S48SaS27S11P24A1Z1000A4S4dG0A1A3A3").
Lemma clear_L12u : ltac2:(tb__ "0|0|
S1S4cS76S7dS9bS5aS89A1U0A2A2S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L12r_len : ltac2:(tb__ "0|4|
S0S99U0M0S51S13S1cS5aS89A1M1A1M2A2A2S0S1S18S17S83S13G0G2Sa1S5Q40Z0A2A1A4A1S14A3S0S1S28S1bG1A1P25A3S1S4aS47SaSaA2M3A1S5cS89A1S4dG3A1A3A2A2A2").
Proof. vm_compute. repeat split; reflexivity || lia. Qed.

Lemma G12b_clear_band : ltac2:(tb__ "0|3|
S8S27S27S3aR3A1S1S6Q40M0A1S9R4P24A2Vb7;A3S1fS64R4A2S1fS1eR5R4A2S63A2S1fZ0R5A2S3S1fS1eR7R6A2S73R8A1M1A2S1fS1eG1Z200A2R7A2A2SaS27S5fS47SaS27A2S48SaS27R2R1A4S7dA3S27S0S1fRcR1A2S20R1S1eRcRbA2A2A2S4S0S1fS7G0ScReR5A2A2M2R2A2S20R2S1eG2R4A2A2A2A1F_;Fx;F_;Fsz;Fe;F_;F_;F_;F_;F_;F_;Fn;Fq;Frho;").
Proof using HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps Ha1 Ha2.
  clear HBlim. intros rho q n (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1) H36 Hq0 Hq1 Hn Hqp e sz Hin x Hx.
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV.
  unfold SHADOW_BAND_HI in PLB. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in Hq0, Hq1. pose proof (urange P) as UP. unfold alloc_ceiling_hi in Phi.
  pose proof (bandav_intro _ _ (proj1 (proj2 Ha1))) as HA1. pose proof (bandav_intro _ _ (proj1 (proj2 Ha2))) as HA2.
  pose proof b5_facts as (_ & _ & F5b & _). pose proof (bandav_intro _ _ F5b) as F5band. clear F5b.
  pose proof b6_facts as (_ & F6band & _). pose proof b7_facts as (_ & F7band & _).
  clear Ha1 Ha2.
  unfold G12b, G11c in Hin. apply in_app_iff in Hin.
  destruct Hin as [[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]]]|[[= <- <-]|[]]]; cbn [eval].
  - rewrite H27. clear -HA1 Hx Hq0 Hq1. unfold bandav in HA1. lia.
  - rewrite H28. clear -HA2 Hx Hq0 Hq1. unfold bandav in HA2. lia.
  - change (eval rho ri30) with (eval rho ri30).
    assert (Eri : bv_unsigned (eval rho ri30) = bv_unsigned RIw).
    { unfold ri30. cbn [eval]. rewrite H30. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
      change (bv_wrap 64 137438953472) with (2 ^ 37). rewrite RV. apply bv_wrap_small. change (bv_modulus 64) with (2^64).
      pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.SB_val m a1 a2 Hres Hmaps Htop P HPL). pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)). lia. }
    rewrite Eri. clear -R1 PLB Hx Hq1. lia.
  - change (eval rho shRI_base) with (pRI rho).
    replace (bv_unsigned (pRI rho)) with (priZ rho); [clear -Hqp Hx; lia|].
    unfold pRI, shRI_base, priZ. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (bv_wrap 64 19327320064) with 19327320064. symmetry. apply bv_wrap_small. change (bv_modulus 64) with (2^64).
    pose proof (urange (rw rho 31%positive)). pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.SB_val m a1 a2 Hres Hmaps Htop P HPL). pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)).
    lia.
  - rewrite H33. clear -F5band Hx Hq0 Hq1. unfold bandav in F5band. lia.
  - rewrite H34. clear -F6band Hx Hq0 Hq1. unfold bandav in F6band. lia.
  - rewrite H36. clear -F7band Hx Hq0 Hq1. unfold bandav in F7band. lia.
Qed.

Lemma prep12 : ltac2:(tb__ "0|9|
S8S56S3aR2A1S1S6Q40M0A1M1S9R3P24A2Vb7;A3S43S1dS37S39Vb7;A1M2S1eS68VB;A1Z1000M3A2A2S89R4S67R4A1R3A6S2S8S8S0S28S1G1S9R2R1A2S9R7R1A2A3Fi;S0S28S1S4aS6Q8A1M4A1S12R2R1A2S12R7R1A2A3Fl;S0S7fR1A1S0G1S2G1G1S0S5fG1R1S67R8A1A3S0S1fS7G0R1A2M5S7G0R2A2M6A2S20G6S1eG5G3A2A2A2A2Lp;A2S1S4fG4A1SdR3R2A2SdR8R2A2A3M7F_;Fa;S0G1S1fS63G5A2G7F_;Fa;S0G1S5fG1R1S67R7A1A3M8S1fS1eG6G3A2S78R8A1A2F_;Fp;S0S1fS1eS78R6A1G3A2S63A2S0G1G8S1fS64G6A2F_;Fp;S43S1dS37G2S80A2S8aR1S7bR6A1R5A6A2A2A2A2A2A2A2A2Lrho';A2F_;F_;F_;Fw;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 Ha1 Ha2 Hmaps Hna Hres Htop Hlz.
  intros rho [tr [ms md]] HV H36 Hsp. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3).
  pose proof RI_val as RV. pose proof SB_val as SB. pose proof (urange P) as UP. unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB.
  pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB. set (rP := bv_unsigned P mod 65536) in *.
  pose proof b4_facts as (F4lo & F4band' & F4top & F4al & _). pose proof (bandav_intro _ _ F4band') as F4band. clear F4band'.
  pose proof b6_facts as (F6lo & F6band & F6top & F6al & _). pose proof b7_facts as (F7lo & F7band & F7top & F7al & _).
  pose proof Hsp as [Hsm (Htr & Hem & Hpaid)]. cbn [w_tr w_cfg cfg_model fst snd] in Htr, Hem, Hpaid.
  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF. cbn [ax_S] in HF.
  destruct L12r_facts1 as (X1 & X2 & X3). destruct L12r_len as (LEN & DZ & NX & XN).
  pose proof (fact_of_state _ _ rho X1 HF) as A1. pose proof (fact_of_state _ _ rho X2 HF) as A2. pose proof (fact_of_state _ _ rho X3 HF) as A3.
  cbn [holds eval] in A1, A2, A3. rewrite Z_to_bv_unsigned in A2, A3.
  change (bv_wrap 64 0x7fff80000000) with 0x7fff80000000 in A2. change (bv_wrap 64 0x7fffffffff20) with 0x7fffffffff20 in A3.
  destruct A1 as [_ A1]. change (2 ^ 4) with 16 in A1.
  pose proof (erase_mat_eq_fields md (m12 b7) Hem) as (Evm & Elz & _).

  assert (Htopv : alloc_top (m_vmmaps m) = bv_unsigned (rw rho 1%positive) - 0x800000).
  { unfold alloc_top. rewrite stack_max_size_val, <- Hv1. reflexivity. }

  set (v1 := bv_unsigned (rw rho 1%positive)) in *.
  apply Z.mod_divide in A1 as [k1 Hk1]; [|lia].
  assert (Hsh : shZ rho = 2 * k1 + 0x7fff8000) by (unfold shZ; fold v1; rewrite Hk1; replace (k1 * 16) with (2 * k1 * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
  pose proof (Z.mod_pos_bound (shZ rho - 131072) 4096 ltac:(lia)) as Qm. pose proof (Z.mod_pos_bound (shZ rho - 9) 4096 ltac:(lia)) as Em.
  assert (Hq : q12 rho <= shZ rho - 131072 < q12 rho + 4096) by (unfold q12; lia).
  assert (He : e12 rho <= shZ rho - 9 < e12 rho + 4096) by (unfold e12; lia).
  assert (Hqal : q12 rho mod 4096 = 0) by (unfold q12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  assert (Heal : e12 rho mod 4096 = 0) by (unfold e12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  apply Z.mod_divide in Hqal as [tq Htq]; [|lia]. apply Z.mod_divide in Heal as [te Hte]; [|lia].
  assert (Hn : Z.of_nat (n12 rho) = te - tq + 1).
  { unfold n12. rewrite Htq, Hte. replace (te * 4096 - tq * 4096) with ((te - tq) * 4096) by lia. rewrite Z_div_mult by lia. rewrite Z2Nat.id; lia. }
  assert (Hrange : q12 rho + 4096 * Z.of_nat (n12 rho) = e12 rho + 4096) by (rewrite Hn; lia).
  assert (Hqlo : 0x2008fff7000 <= q12 rho) by lia.
  assert (Hehi : e12 rho + 4096 <= 0x10007fff8000) by lia.
  assert (Hn33 : Z.of_nat (n12 rho) <= 33) by lia.
  clearbody rP. clear Qm Em.

  set (J' := fun (r : valuation) (_ : list word) (tr0 : list event) (md0 : Model) => KxA (m12 b7) B12x r (TP12 rho) tr0 md0).
  assert (Hsp1 : SPA segsA J' (ax_setS L12r (unknown_obj_at (ax_S L12r) 0)) rho (TP11 rho) (tr, mkCfg ms md)).
  { apply SPA_obj_to_unknown; [exact LEN | exact XN | exact DZ | exact same_L12u |].
    split; [exact Hsm|]. subst J'. cbv beta. unfold KxA. cbn [w_tr w_cfg cfg_model fst snd].
    split; [exact Htr|]. split; [exact Hem|]. unfold TP12, B12x.
    pose proof (paid_app_le md (pages_rev (q12 rho) (n12 rho)) (TP11 rho)) as PL. rewrite length_pages_rev in PL. unfold page_size in PL. lia. }

  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp1) as HF1. cbn [ax_S ax_setS] in HF1.
  assert (V35 : 8 * bv_unsigned (rw rho 35%positive) = bv_unsigned b6 /\ bv_unsigned (rw rho 35%positive) <= 2 ^ 61 - 1).
  { destruct (L12r_facts35) as [Y1 Y2].
    pose proof (fact_of_state _ _ rho Y1 HF) as E1. pose proof (fact_of_state _ _ rho Y2 HF) as E2.
    cbn [holds eval] in E2. rewrite Z_to_bv_unsigned in E2. change (bv_wrap 64 (2 ^ 61 - 1)) with (2 ^ 61 - 1) in E2.
    cbn [holds] in E1. apply (f_equal bv_unsigned) in E1.
    change (bv_unsigned (eval rho (SAlu ALU_SLL (SVar 35%positive) (SLit 3)))) with (SymSoundV.U rho (StepA.g8 35%positive)) in E1.
    rewrite (StepA.U_g8 rho 35%positive) in E1 by (unfold SymSoundV.U; cbn [eval]; exact E2). unfold SymSoundV.U in E1. cbn [eval] in E1. rewrite H34 in E1. split; [exact E1 | exact E2]. }
  assert (Upr : bv_unsigned (pRI rho) = priZ rho).
  { unfold pRI, shRI_base, priZ. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (bv_wrap 64 19327320064) with 19327320064. apply bv_wrap_small. change (bv_modulus 64) with (2^64). pose proof (urange (rw rho 31%positive)). lia. }
  assert (LOW : forall p, In p (TP11 rho) -> bv_unsigned p + 4096 <= q12 rho).
  { intros p Hp. unfold TP11 in Hp. pose proof (Z.mod_pos_bound (sbZ rho) 4096 ltac:(lia)) as Q1m.
    assert (HS : sbZ rho = bv_unsigned (rw rho 35%positive) + 0x7fff8000) by reflexivity.
    assert (HP : priZ rho = bv_unsigned (rw rho 31%positive) + 0x47fff8000) by reflexivity.
    destruct (q1Z rho =? priZ rho);
      repeat (destruct Hp as [<-|Hp]; [first [rewrite u64_of_lit by (unfold q1Z; lia) | rewrite Upr]; unfold q1Z; lia|]); destruct Hp. }
  assert (LOWB : forall p, In p (TP11 rho) -> SHADOW_BAND_LO <= bv_unsigned p).
  { intros p Hp. unfold TP11 in Hp. pose proof (Z.mod_pos_bound (sbZ rho) 4096 ltac:(lia)) as Q1m. unfold SHADOW_BAND_LO.
    assert (HS : sbZ rho = bv_unsigned (rw rho 35%positive) + 0x7fff8000) by reflexivity.
    assert (HP : priZ rho = bv_unsigned (rw rho 31%positive) + 0x47fff8000) by reflexivity. pose proof (urange (rw rho 35%positive)). pose proof (urange (rw rho 31%positive)).
    destruct (q1Z rho =? priZ rho);
      repeat (destruct Hp as [<-|Hp]; [first [rewrite u64_of_lit by (unfold q1Z; lia) | rewrite Upr]; unfold q1Z; lia|]); destruct Hp. }
  destruct (SPA_prepay_pages_rm J' (ax_setS L12r (unknown_obj_at (ax_S L12r) 0)) (q12 rho) (n12 rho) rho (TP11 rho) tr ms md Hsp1)
    as (rho1 & Hsp2 & Hrw1 & Hrl1 & Hz1 & Ho1).
  - intros r r' t t' X; exact X.
  - rewrite Htq. apply Z_mod_mult.
  - lia.
  - lia.
  - intros k Hk. rewrite Elz, lazy_m12, page_in_ranges_app. apply orb_true_intro. right.
    apply (high_shadow_lazy_m8 m a1 a2 Hres Hmaps Hlz Htop P HPL); unfold pageZ; rewrite u64_of_lit by lia; unfold SHADOW_BAND_HI; lia.
  - intros k Hk Hin. pose proof (LOW _ Hin) as X. unfold pageZ in X. rewrite u64_of_lit in X by lia. lia.
  - intros z Hz. rewrite Evm, noacc_m12. unfold covered. cbn [existsb]. apply Bool.orb_false_iff. split.
    + unfold in_iv, ivB, ivS, in_rng, n9. cbn [fst snd]. rewrite u64_of_lit by lia. apply andb_false_iff.
      clear -F4band Hz Hqlo Hehi Hrange. unfold bandav in F4band. destruct F4band as [F|F]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
    + apply (shadow_acc_m8 m a1 a2 Hres Hmaps Hna Hlz Htop P HPL). unfold SHADOW_BAND_HI, SHADOW_BAND_LO, SHADOW_RW_LO_END. lia.
  - destruct Hsp1 as [_ HK]. subst J'. cbv beta in HK. destruct HK as (_ & _ & HP). cbn [w_tr w_cfg cfg_model fst snd] in HP.
    unfold headroom. rewrite Evm, limit_m12. unfold TP12, B12x in HP.
    pose proof (paid_app_ge md (pages_rev (q12 rho) (n12 rho)) (TP11 rho)) as PG. unfold B12, B11, page_size in *. lia.
  - apply Forall_forall. intros o Ho.
    pose proof (objs_clear_e_sound rho G12b (unknown_obj_at (ax_S L12r) 0) (Z_to_bv 64 (q12 rho)) (4096 * Z.of_nat (n12 rho)) HF1 clear_L12u ltac:(lia)
                  ltac:(rewrite u64_of_lit by lia; lia) ltac:(intros x Hx; rewrite u64_of_lit in Hx by lia; lia)) as X.
    rewrite u64_of_lit in X by lia. apply X; [|exact Ho].
    apply (G12b_clear_band rho (q12 rho) (4096 * Z.of_nat (n12 rho)) HV H36); unfold SHADOW_BAND_LO, SHADOW_BAND_HI; try lia.
    right. pose proof (LOW (pRI rho) ltac:(unfold TP11; destruct (q1Z rho =? priZ rho); cbn [In]; tauto)) as LP. rewrite Upr in LP. lia.
  -
    exists rho1. split; [exact Hrw1|]. split; [exact Hrl1|]. split.
    { destruct (q12_ext rho rho1 (Hrw1 1%positive)) as (E1 & E2 & E3). unfold stackshadow_zero. rewrite E1, E3. exact Hz1. }
    split.
    { intros a (p & Hp & Ha). apply Ho1. pose proof (LOW p Hp). lia. }
    split.
    { intros a Ha. apply Ho1. unfold SHADOW_BAND_HI in Ha. rewrite Hrange. lia. }
    split; [exact LOW|]. split; [unfold SHADOW_BAND_HI; lia|]. split; [exact LOWB|].
    rewrite <- L12x_eq.
    change (mkAX (unknown_obj_at (ax_S L12r) 0) [rX12] (SLit SHB)) with (ax_setX (ax_setS L12r (unknown_obj_at (ax_S L12r) 0)) (rX12 :: ax_X (ax_setS L12r (unknown_obj_at (ax_S L12r) 0)))).
    pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp2) as HF2. cbn [ax_S ax_setS] in HF2.
    assert (Hsp3 : SPA segsA J' (ax_setX (ax_setS L12r (unknown_obj_at (ax_S L12r) 0)) (rX12 :: ax_X (ax_setS L12r (unknown_obj_at (ax_S L12r) 0)))) rho1 (TP12 rho) (tr, mkCfg ms md)).
    2:{ destruct Hsp3 as [S3 K3]. split; [exact S3 | exact K3]. }
    apply SPA_x_publish; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Hsp2].
    cbn [ax_S ax_setS ax_base].
    assert (EB : bv_unsigned (eval rho1 (fst rX12)) = v1 - 1048576).
    { cbn [fst rX12 eval]. unfold alu64, alu. rewrite bv_add_unsigned, (Hrw1 1%positive), Z_to_bv_unsigned. fold v1.
      change (bv_wrap 64 (-1048576)) with 18446744073708503040.
      unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
      replace (v1 + 18446744073708503040) with ((v1 - 1048576) + 1 * 18446744073709551616) by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    assert (EL : bv_unsigned (eval rho1 (snd rX12)) = 1048576 - 64) by (cbn [snd rX12 eval]; rewrite u64_of_lit by lia; reflexivity).
    assert (ESH : bv_unsigned (eval rho1 (ax_base L12r)) = 0x7fff8000).
    { replace (ax_base L12r) with (SLit SHB) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). cbn [eval]. rewrite u64_of_lit by (unfold SHB; lia). reflexivity. }
    rewrite ESH.
    apply (xr_ok_of_zero rho1 _ _ rX12 (q12 rho) (q12 rho + 4096 * Z.of_nat (n12 rho))); rewrite ?EB, ?EL.
    + rewrite Hk1. replace (k1 * 16 - 1048576) with ((2 * k1 - 131072) * 8) by lia. apply Z_mod_mult.
    + lia.
    + lia.
    + lia.
    + rewrite Htq. replace (tq * 4096) with (tq * 512 * 8) by lia. apply Z_mod_mult.
    + rewrite Hrange, Hte. replace (te * 4096 + 4096) with ((te + 1) * 512 * 8) by lia. apply Z_mod_mult.
    + intros a Ha. rewrite Hrange.
      pose proof (Z.div_le_mono (v1 - 1048576) a 8 ltac:(lia) ltac:(lia)) as Dlo.
      pose proof (Z.div_le_mono a (v1 - 65) 8 ltac:(lia) ltac:(lia)) as Dhi.
      assert (D1 : (v1 - 1048576) / 8 = 2 * k1 - 131072) by (rewrite Hk1; replace (k1 * 16 - 1048576) with ((2 * k1 - 131072) * 8) by lia; apply Z_div_mult; lia).
      assert (D2 : (v1 - 65) / 8 < 2 * k1 - 8) by (rewrite Hk1; apply Z.div_lt_upper_bound; lia).
      lia.
    + exact Hz1.
    + intros z Hz. apply Forall_forall. intros o Ho.
      assert (R : forall o', obj_range rho1 o' = obj_range rho o').
      { intros o'. unfold obj_range, obj_lo_of, obj_hi_of, soff. rewrite !(eval_ext_rwrl rho rho1) by assumption. reflexivity. }
      cbv zeta. rewrite R.
      pose proof (objs_clear_e_sound rho G12b (unknown_obj_at (ax_S L12r) 0) (Z_to_bv 64 (q12 rho)) (4096 * Z.of_nat (n12 rho)) HF1 clear_L12u ltac:(lia)
                    ltac:(rewrite u64_of_lit by lia; lia) ltac:(intros x Hx; rewrite u64_of_lit in Hx by lia; lia)) as X.
      rewrite u64_of_lit in X by lia. rewrite u64_of_lit by lia.
      enough (D : ranges_disjoint (obj_range rho o) (q12 rho, q12 rho + 4096 * Z.of_nat (n12 rho))).
      { unfold ranges_disjoint in D. destruct (obj_range rho o) as [lo' hi']. cbn [fst snd] in D |- *. lia. }
      apply X; [|exact Ho].
      apply (G12b_clear_band rho (q12 rho) (4096 * Z.of_nat (n12 rho)) HV H36); unfold SHADOW_BAND_LO, SHADOW_BAND_HI; try lia.
      right. pose proof (LOW (pRI rho) ltac:(unfold TP11; destruct (q1Z rho =? priZ rho); cbn [In]; tauto)) as LP. rewrite Upr in LP. lia.
Qed.
End S12b.

Section S12c.
Variable b7 : word.
Hypothesis HPL7 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2VmE;S5G0Z1000A2Vb7;A4").

Lemma holds_all_agree : ltac2:(tb__ "0|1|
S28S8S8S4aSbA1S1S4cS62SbS19R4A1R1A3S4eA3SeR5R4R3A3S82SbSfR5A1M0R3A3S82SbG0R4A3F_;F_;F_;Ffs;Frho';Frho;Fn;").
Proof.
  clear. intros n rho rho' fs Hb Hag HF. apply Forall_forall. intros f Hf.
  apply (proj1 (holds_agree n rho rho' f Hag (proj1 (forallb_forall _ _) Hb f Hf))). exact (proj1 (Forall_forall _ _) HF f Hf).
Qed.

Lemma shape12 : ltac2:(tb__ "0|1|
S8S56S82SbSfR2A1S10S5aS8aA1A1A3S43S1dS37S39Vb7;A1S3bA2M0S8aR3S38R3A1R2A6S43S1dG0S8bR4S38R4A1R3A6F_;F_;Fw;Frho;").
Proof.
  clear. intros rho w HFx Hw.
  replace C12 with (ax_setS (ax_setS L12x C12d) (replace_obj_at C12d 13 o12rtc2b)) by (unfold C12; rewrite <- C12e_eq; reflexivity).
  apply (SPA_add_img_cell (KxA (m12 b7) B12x) rho (ax_setS L12x C12d) 13 o12rtc2a 0xeeda0 0xeedb8 0xeeda8 8 0 (TP12 rho) w o12rtc2a_nth
           eq_refl eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (proj2 rtc2_clear) (proj2 rtc2_img)).
  - cbn [ax_S ax_setS]. exact same_C12e.
  - rewrite <- C12d_eq.
    apply (SPA_add_img_cell (KxA (m12 b7) B12x) rho (ax_setS L12x C12c) 13 o12rtc2 0xeeda0 0xeedb8 0xeedb0 8 0 (TP12 rho) w o12rtc2_nth
             eq_refl eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (proj1 rtc2_clear) (proj1 rtc2_img)).
    + cbn [ax_S ax_setS]. exact same_C12d.
    + apply (SPA_split_chain segsA (KxA (m12 b7) B12x) rho splits12 L12x C12c (TP12 rho) w split12_ok Hw).
Qed.

Lemma unshape12 : ltac2:(tb__ "0|1|
S8S8S56S82SbSfR3A1S10S5aS8aA1A1A3SeP25R4R3A3S43S1dS37S39Vb7;A1S3bA2M0Sa2S88S9dS9cS8bS87A5R4S38R5A1R3A6S43S1dG0S85R5S38R6A1R4A6F_;F_;F_;Fw;Frho';Frho;").
Proof.
  clear. intros rho rho' w HFx Hag Hw. rewrite IP12_eq in Hw. rewrite <- IP12f_eq. apply SPA_refacts.
  - apply SPA_x_sub; [intros r []| exact Hw].
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros HF'. apply Forall_app. split; [exact HF'|].
    apply (holds_all_agree 37%positive rho rho' _ C12e_facts_below Hag).
    replace (ss_facts C12e) with (ss_facts (ax_S L12x)) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). exact HFx.
Qed.

Lemma call12 : ltac2:(tb__ "0|1|
S8S3aR1A1S1S6Q40A1S9R2P24A2Vb7;A3S58S1dVok;S43S1dS37S39Vb7;A1S3bA2M0S8aR3S38R3A1A5S56S2S8S8S0SeP25R5R1A3S43S1dG0S85R1S38R5A1R2A6A2Lrho';A2Lw;A4F_;F_;Frho;").
Proof using OKF.
  clear Ha1 Ha2 HBlim HPL HPL4 HPL5 HPL6 HPL7 Htop. intros rho HV H36.
  apply triple_factsA. intros HFx.
  eapply triple_conseq; [intros w Hw; exact (shape12 rho w HFx Hw) | intros w Hw; exact Hw |].
  apply (call_pureA segsA ok C12 Pre_rip Posts_rip s12 R12 (m12 b7) B12x (TP12 rho) rho _ OKF entails12 callcheck12).
  - intros J rho1 tp1 HokJ HstJ. exact (region_sum ok J rho1 tp1 HokJ HstJ).
  - intros L rho' [<-|[]] Hag. cbn [la_state].
    replace (ss_next (ax_S C12)) with 37%positive in Hag by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply triple_refl].
    exists rho'. split; [exact Hag|]. exact (unshape12 rho rho' w HFx Hag Hw).
Qed.
Lemma ecall12 : ltac2:(tb__ "0|1|
S8S3aR1A1S1S6Q40A1S9R2P24A2Vb7;A3S57S1dS43S1dS37S39Vb7;A1S3bA2M0S8aR3S38R3A1A5S56S2S8S8S0SeP25R5R1A3S43S1dG0S85R1S38R5A1R2A6A2Lrho';A2Lw;A3F_;F_;Frho;").
Proof.
  clear. intros rho HV H36.
  apply etriple_factsA. intros HFx.
  eapply etriple_conseq; [intros w Hw; exact (shape12 rho w HFx Hw) | intros w Hw; exact Hw |].
  apply (ecall_pureA segsA C12 Pre_rip Posts_rip s12 R12 (m12 b7) B12x (TP12 rho) rho _ entails12 callcheck12).
  - intros J rho1 tp1 HstJ. exact (region_sum_ex J rho1 tp1 HstJ).
  - intros L rho' [<-|[]] Hag. cbn [la_state].
    replace (ss_next (ax_S C12)) with 37%positive in Hag by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply etriple_refl].
    exists rho'. split; [exact Hag|]. exact (unshape12 rho rho' w HFx Hag Hw).
Qed.

Lemma E_s13_facts1 : ltac2:(tb__ "0|0|
S1S4cS60SbS1aS16S15Z7fff80000000A1S11P1A1A2A1S10S5aS86A1A1A3S4eA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma seg12d_post : ltac2:(tb__ "0|3|
S8S4aS2fA1M0S97S31S44S1dS37S39Vb7;A1S3bA2M1P4dM2R4S38R4A1S49S59S5bS86S81A2S4dS59A1A3S48G0S92R3S93R2R1A2A4A7S2S8S8S0S75G2R6R1A3S0S3cR6R1A2S0S77R6R1A2S43S1dG1S84R1S38R6A1S48G0S92R5S93R4R3A2A4A6A2A2A2Lrho';A2F_;Fmd;Fms;Ftr;Frho;").
Proof.
  clear. intros rho tr ms md Hw.
  apply (proj1 (LQA1 _ _ _ _ _ _)) in Hw as (rho1 & Hag & Hsp).
  pose proof E_s13g_at as (_ & _ & _ & LENb & LEN & LENe & X13).

  assert (H1 : SPA segsA (KxA (m12 b7) B12x) (ax_setS E_s13 T13a) rho1 (TP12 rho) (tr, mkCfg ms md)).
  { rewrite <- T13a_eq. apply SPA_move_last; [rewrite LEN; lia | exact X13 | rewrite T13a_eq; exact same_T13a | exact Hsp]. }
  pose proof (SPA_unobj segsA (KxA (m12 b7) B12x) rho1 (ax_setS E_s13 T13a) (ss_objs T13b) [ostk13] (TP12 rho) tr ms md T13a_split H1 ltac:(intros X; exact X)) as H2.
  cbv zeta in H2. rewrite ax_S_ax_setS, ax_setS_ax_setS, T13b_eq in H2.
  set (rho2 := rho_absorb rho1 [ostk13] (vms md (TP12 rho) ms)) in *.

  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF. cbn [ax_S] in HF.
  assert (A2 : 0x7fff80000000 <= bv_unsigned (rw rho1 1%positive)).
  { pose proof (fact_of_state (ax_S E_s13) _ rho1 E_s13_facts1 HF) as A.
    cbn [holds eval] in A. rewrite u64_of_lit in A by lia. exact A. }
  assert (Rng : obj_range rho1 ostk13 = (bv_unsigned (rw rho1 1%positive) - 3104, bv_unsigned (rw rho1 1%positive) - 3024)).
  { unfold obj_range, obj_lo_of, obj_hi_of, soff, ostk13. cbn [ob_base ob_lo ob_hi eval]. unfold alu64, alu.
    rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 (-3024)) with (2 ^ 64 - 3024).
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). pose proof (urange (rw rho1 1%positive)).
    replace (bv_unsigned (rw rho1 1%positive) + (2 ^ 64 - 3024)) with ((bv_unsigned (rw rho1 1%positive) - 3024) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by lia.
    replace (bv_signed (Z_to_bv 64 (-80))) with (-80) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    replace (bv_signed (Z_to_bv 64 0)) with 0 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). f_equal; lia. }
  assert (DEF : forall a, bv_unsigned (rw rho1 1%positive) - 3104 <= a < bv_unsigned (rw rho1 1%positive) - 3024 -> rm rho2 (Z_to_bv 64 a) <> None).
  { intros a Ha. unfold rho2. apply (SPA_released_defined (KxA (m12 b7) B12x) (ax_setS E_s13 T13a) rho1 (TP12 rho) tr ms md (ss_objs T13b) ostk13 T13a_split eq_refl);
      [rewrite Rng; cbn [fst]; lia | exact H1 | rewrite Rng; cbn [fst snd]; exact Ha]. }

  assert (H3 : SPA segsA (KxA (m12 b7) B12x) (ax_setS E_s13 T13c) rho2 (TP12 rho) (tr, mkCfg ms md)).
  { rewrite <- T13c_eq.
    apply (SPA_move_last segsA (KxA (m12 b7) B12x) rho2 (ax_setS E_s13 T13b) 3); [cbn [ax_S ax_setS]; rewrite LENb; lia | exact X13 | cbn [ax_S ax_setS]; rewrite T13c_eq; exact same_T13c | exact H2]. }
  assert (H4 : SPA segsA (KxA (m12 b7) B12x) (ax_setS E_s13 T13d) rho2 (TP12 rho) (tr, mkCfg ms md)).
  { rewrite <- T13d_eq.
    apply (SPA_carve_unknown (KxA (m12 b7) B12x) rho2 (ax_setS E_s13 T13c) (TP12 rho) tr ms md (SVar 1%positive) (-3104) (-3024) (ss_next T13c) H3).
    - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    - cbn [ax_S ax_setS]. lia.
    - lia. - lia. - lia.
    - cbn [eval]. unfold rho2. rewrite rw_absorb. pose proof (urange (rw rho1 1%positive)). lia.
    - cbn [eval]. unfold rho2. rewrite rw_absorb. pose proof (urange (rw rho1 1%positive)). lia.
    -
      cbn [ax_S ax_setS eval].
      replace (bv_unsigned (rw rho2 1%positive)) with (bv_unsigned (rw rho1 1%positive)) by (unfold rho2; rewrite rw_absorb; reflexivity).
      destruct H1 as [Hsm1 _]. pose proof (smatchA_smatch segsA _ _ _ _ Hsm1) as S1. unfold virt in S1. cbn [w_tr w_cfg fst snd cfg_ms cfg_model ax_S ax_setS] in S1.
      pose proof (smatch_mm segsA _ _ _ _ _ S1) as (_ & PD & _). rewrite T13a_split in PD.
      apply pairwise_disjoint_app_inv in PD as (_ & _ & CR).
      apply Forall_forall. intros o Ho.
      assert (Ho' : In o (ss_objs T13b)).
      { rewrite <- T13c_eq in Ho. unfold move_obj_last in Ho. cbn [ss_objs set_objs] in Ho.
        rewrite !in_app_iff in Ho. destruct Ho as [Ho|[Ho|Ho]]; [eapply In_firstn_In; exact Ho | eapply In_skipn_In; exact Ho | eapply In_skipn_In; eapply In_firstn_In; exact Ho]. }
      pose proof (CR o ostk13 Ho' (or_introl eq_refl)) as D. rewrite Rng in D.
      replace (obj_range rho2 o) with (obj_range rho1 o) by (unfold obj_range, obj_lo_of, obj_hi_of, soff, rho2; rewrite !eval_absorb; reflexivity).
      unfold ranges_disjoint in D |- *. destruct (obj_range rho1 o) as [lo' hi']. cbn [fst snd] in D |- *. lia.
    - cbn [eval]. replace (bv_unsigned (rw rho2 1%positive)) with (bv_unsigned (rw rho1 1%positive)) by (unfold rho2; rewrite rw_absorb; reflexivity).
      intros a Ha. apply DEF. lia.
    - cbn [ax_X ax_setS]. rewrite X13. intros rr y j []. }
  pose proof (SPA_merge segsA (KxA (m12 b7) B12x) rho2 (ax_setS E_s13 T13d) 23 T13e (TP12 rho) _ T13e_eq H4) as H5. rewrite ax_setS_ax_setS in H5.
  assert (H6 : SPA segsA (KxA (m12 b7) B12x) (ax_setS E_s13 T13f) rho2 (TP12 rho) (tr, mkCfg ms md)).
  { rewrite <- T13f_eq.
    apply (SPA_move_last segsA (KxA (m12 b7) B12x) rho2 (ax_setS E_s13 T13e) 3); [cbn [ax_S ax_setS]; rewrite LENe; lia | exact X13 | cbn [ax_S ax_setS]; rewrite T13f_eq; exact same_T13f | exact H5]. }
  pose proof (SPA_merge segsA (KxA (m12 b7) B12x) rho2 (ax_setS E_s13 T13f) 22 T13g (TP12 rho) _ T13g_eq H6) as H7. rewrite ax_setS_ax_setS in H7.
  exists rho2. split; [|split; [|split]].
  - destruct Hag as (V & L & _). unfold rho2. split; [intros i Hi; rewrite rw_absorb; symmetry; apply V; exact Hi | intros l; rewrite rl_absorb; symmetry; apply L].
  - destruct Hag as (_ & _ & R). intros a Ha. unfold rho2. rewrite rm_absorb_outside; [symmetry; apply R|].
    intros (o & [<-|[]] & Hr). rewrite Rng in Hr. cbn [fst snd] in Hr. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in Ha. lia.
  -
    pose proof Hag as (V & _ & _). unfold rho2. apply RMH_absorb; [eapply RMH_below; [apply RMH_refl | exact Hag]|].
    intros a [Ha _] (o & [<-|[]] & Hr). rewrite Rng in Hr. cbn [fst snd] in Hr. rewrite <- (V 1%positive) in Hr by lia. lia.
  - replace E_s13g with (ax_setS E_s13 T13g) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). exact H7.
Qed.

Lemma seg12d : ltac2:(tb__ "0|1|
S8S58S1dVok;S43S1dS37S39Vb7;A1S3bA2M0S85R1S38R1A1A5S56S2S8S8S0S75P4dR3R1A3S0S3cR3R1A2S0S77R3R1A2S43S1dG0S84R1S38R3A1R2A6A2A2A2Lrho';A2Lw;A4Frho;").
Proof using OKF.
  clear Ha1 Ha2 HBlim HPL HPL4 HPL5 HPL6 HPL7 Htop. intros rho.
  eapply triple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply triple1_triple. eapply sym_run_soundA; [exact run12c | apply OKFx | reflexivity | apply stableA_KxA]. }
  intros [tr [ms md]] Hw. replace (ss_next (ax_S IP12f)) with 77%positive in Hw by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  exact (seg12d_post rho tr ms md Hw).
Qed.
Lemma eseg12d : ltac2:(tb__ "0|1|
S8S57S1dS43S1dS37S39Vb7;A1S3bA2M0S85R1S38R1A1A5S56S2S8S8S0S75P4dR3R1A3S0S3cR3R1A2S0S77R3R1A2S43S1dG0S84R1S38R3A1R2A6A2A2A2Lrho';A2Lw;A3Frho;").
Proof.
  clear. intros rho.
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run12c]. }
  intros [tr [ms md]] Hw. replace (ss_next (ax_S IP12f)) with 77%positive in Hw by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  exact (seg12d_post rho tr ms md Hw).
Qed.
End S12c.

Section S13a.
Variable b7 : word.
Hypothesis HPL7 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2VmE;S5G0Z1000A2Vb7;A4").
Definition m13 (b8 : word) : Model := eager_model 4096 (m12 b7) b8.
Lemma clear13 : ltac2:(tb__ "0|0|
S1S4cS76S3dS5aS84A1A2S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma blocks12b : ltac2:(tb__ "0|6|
S8S27S3aR2A1S1S6Q40M0A1M1S9R3P24A2Vb7;A3S4aS47G1G1A2M2A1M3S2G3G3S1G3R2S4bG2R1S2aS29S39Vb7;A1A1A1A3A3Ll;A2SaS27S5fS47SaS27A2S48SaS27R2R1A4S3dA3S3S2G1G1S2G1G1S0S5fG2S48G1G1R2R1A4R7A3S0S1fS7G0R2A2M4S7G0ScRbR5A2A2M5A2S1fS1eG5R4A2S1eG4S7G0R1A2A2A2A2A2Ls;A2Lb;A2S1fS1eS7G0ScR9R3A2A2R2A2R8A2A2F_;Fsz;Fe;F_;Fmaps;F_;F_;FLB;Frho;").
Proof using HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim HPL4 HPL5 HPL6 HPL7. intros rho LB HV H36 maps [l ->] e sz Hin.
  pose proof (m12_ledger b7) as (_ & M2 & _).
  unfold G12b in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|[[= <- <-]|[]]].
  - apply (HG11c rho LB HV); [|exact Hin]. rewrite M2. exists (l ++ [(b7, Z_to_bv 64 4096)]). rewrite <- app_assoc. reflexivity.
  - left. cbn [eval]. rewrite H36. exists b7, (Z_to_bv 64 4096). split; [apply in_app_iff; right; rewrite M2; left; reflexivity|]. rewrite u64_of_lit by lia. lia.
Qed.

Lemma seg13 : ltac2:(tb__ "0|4|
S8S3aR1A1S1S6Q40M0A1M1S9R2P24A2Vb7;A3S58S1dVok;S43S1dS37S39Vb7;A1M2S3bA2S84R3S38R3A1A5S56S2G1G1S0S53S5G0Z0A2G2S5G0Z1000M3A2R1A4S44S1dS37S66R1A1S1eS3bG3A2A2P4eS8cR5P4dR1A3S38R5A1S49S59S5bS8eS81A2S4dS59A1A3R2A7A2Lb8;A2Lw;A4F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 Ha1 Ha2 Hmaps Hna Hres Htop Hlz OKF OKP.
  intros rho HV H36. pose proof (m12_ledger b7) as (M1 & M2 & M3 & M4). pose proof HV as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1).
  eapply triple_seq.
  { apply triple1_triple.
    apply (eager_rw_node ok OKF OKP E_s13g 4096 (m12 b7) B12x G12b 78%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear13.
    + rewrite M1. exact Hres.
    + exact (init_sp_ok_m12 b7).
    + exact (band_m12 b7).
    + rewrite M3. unfold B12x, B12, B11. lia.
    + apply (blocks12b rho _ HV H36). exists []. reflexivity.
    + rewrite M4. exact Hv1. }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA (m12 b7) B12x) (OKFx _ _) (fun n => stableA_KxA segsA n (m12 b7) B12x) _ SPIN13 200%nat SPIN_MMAPORDIE);
      [reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact run13_fail | exact spin13].
  - apply triple_ex; intros b8. apply triple_pure; intros HPL8.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b8; split; [exact HPL8|exact Hw] |].
    apply triple1_triple.
    assert (N : ss_next (ax_S E_s13g) = 77%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    change (eager_ok E_s13g 4096 78) with S_s13ok. rewrite N.
    eapply sym_run_soundA; [exact run13_ok | apply OKFx | reflexivity | apply stableA_KxA].
Qed.

Hypothesis Hw13 : ltac2:(tb__ "0|2|
S2S6Q40M0A1M1G1S53S5G0Z0A2S39Vb7;A1S5G0Z1000A2R1A4La;A2").
Lemma eseg13 : ltac2:(tb__ "0|4|
S8S3aR1A1S1S6Q40M0A1M1S9R2P24A2Vb7;A3S57S1dS43S1dS37S39Vb7;A1M2S3bA2S84R3S38R3A1A5S56S2G1G1S0S53S5G0Z0A2G2S5G0Z1000M3A2R1A4S44S1dS37S66R1A1S1eS3bG3A2A2P4eS8cR5P4dR1A3S38R5A1S49S59S5bS8eS81A2S4dS59A1A3R2A7A2Lb8;A2Lw;A3F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 Hmaps Hres Htop Hlz Hw13.
  clear Ha1 Ha2. intros rho HV H36. pose proof (m12_ledger b7) as (M1 & M2 & M3 & M4). pose proof HV as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1).
  eapply etriple_seq.
  { apply (eager_rw_enode E_s13g 4096 (m12 b7) B12x G12b 78%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear13.
    + rewrite M1. exact Hres.
    + exact (init_sp_ok_m12 b7).
    + exact (band_m12 b7).
    + rewrite M3. unfold B12x, B12, B11. lia.
    + exact Hw13.
    + apply (blocks12b rho _ HV H36). exists []. reflexivity.
    + rewrite M4. exact Hv1. }
  apply etriple_ex; intros b8. intros w [HPL8 Hsp]. revert w Hsp.
  assert (N : ss_next (ax_S E_s13g) = 77%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  change (etriple segsA (SPA segsA (KxA (m13 b8) (B12x + 4096)) (eager_ok E_s13g 4096 78) (rho_set_rw rho (ss_next (ax_S E_s13g)) b8) (TP12 rho))
           (fun w => exists b0, mmap_place_ok_none (Z_to_bv 64 0) (m12 b7) (Z_to_bv 64 4096) b0
              /\ LQA segsA (KxA (m13 b0) (B12x + 4096)) 78 (rho_set_rw rho 77 b0) (TP12 rho) [mkLeafA E_s14 RsCut] w)).
  rewrite N. change (eager_ok E_s13g 4096 78) with S_s13ok.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b8; split; [exact HPL8|exact Hw] |].
  rewrite <- N. eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run13_ok].
Qed.

Section S13.
Variable b8 : word.
Hypothesis HPL8 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2S39Vb7;A1S5G0Z1000A2Vb8;A4").
Definition m14 (b9 : word) : Model := eager_model 4096 (m13 b8) b9.
Definition G13b : list (sv * Z) := ltac2:(tb__ "0|1|
S4bS47SaS27A2M0S3dS49G0S48SaS27S11P4dA1Z1000A4S4dG0A1A3A3").

Lemma m13_ledger : ltac2:(tb__ "0|6|
S0S1S4aS47S6Q40M0A1M1G1A2M2A1M3S2bS29S66Vb8;A1A1M4A1S2bS29Vm;A1M5A1A3S0S1G3S2aG4A1S49G2S48G1G1Vb8;S5G0Z1000A2A4S2aS29S39Vb7;A1A1A1A3A3S0S1S27S2cG4A1S2cG5A1A3S1G1S2dG4A1S2dG5A1A3A2A2A2").
Proof.
  clear. pose proof (m12_ledger b7) as (L1 & L2 & L3 & L4).
  unfold m13, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps. cbn [vm_reserved vm_maps vm_limit vm_init_sp]. rewrite L1, L3, L4. repeat split; reflexivity.
Qed.
Lemma init_sp_ok_m13 : init_sp_ok (m_vmmaps (m13 b8)).
Proof using Htop. clear -Htop. pose proof m13_ledger as (_ & _ & _ & L4). unfold init_sp_ok in *. rewrite L4. exact Htop. Qed.
Lemma band_m13 : ltac2:(tb__ "0|2|
S65S4bS47S6Q40A1M0G0A2S2bS29S66Vb8;A1A1M1A1S2aG1A1A3S64S63A3").
Proof using Hmaps. clear -Hmaps. pose proof m13_ledger as (L1 & L2 & _). pose proof (m12_ledger b7) as (K1 & _).
  rewrite L1, L2, <- K1. apply (band_covered_after_grant (m12 b7)). exact (band_m12 b7). Qed.
Lemma b8_facts : ltac2:(tb__ "0|5|
S0S1fZ1000M0S7Q40M1Vb8;A2M2A2S0S6dG2G0A2S0S1fS1eG2G0A2S2eS29Vm;A1A1A2S0S1S27S21G2G0A2Z0A3S1S4cS30S4bS47S6G1A1M3G3A2S2bS29S39Vb7;A1A1M4A1S2aG4A1A3Vb8;S5G1G0A2A3S4eA3A2A2A2A2").
Proof using HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. pose proof (m12_ledger b7) as (L1 & L2 & L3 & L4).
  pose proof (place_LB_A (m12 b7) 4096 b8 (init_sp_ok_m12 b7) ltac:(rewrite L1; exact Hres) (band_m12 b7) ltac:(lia) ltac:(reflexivity) HPL8) as (PLB & Pimg & Pband & Ptop & _).
  pose proof HPL8 as (Hal & _ & _ & Hfree). revert Ptop. unfold alloc_top. rewrite L4. intros Ptop.
  assert (Hn : mmap_n (Z_to_bv 64 4096) = Z_to_bv 64 4096) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Hn in Hfree.
  change (LB_of 4096) with 0x1000 in PLB. split; [exact PLB|]. split; [exact (bandav_intro _ _ Pband)|]. repeat split; assumption.
Qed.

Lemma blocks13b : ltac2:(tb__ "0|6|
S8S27S3aR2A1S1S6Q40M0A1M1S9R3P24A2Vb7;A3S1G1S9R4P4dA2Vb8;A3S4aS47G1G1A2M2A1M3S2G3G3S1G3R2S4bG2R1S2aS29S66Vb8;A1A1A1A3A3Ll;A2SaS27S5fS47SaS27A2S48SaS27R2R1A4S5eA3S3S2G1G1S2G1G1S0S5fG2S48G1G1R2R1A4R7A3S0S1fS7G0R2A2M4S7G0ScRcR5A2A2M5A2S1fS1eG5R4A2S1eG4S7G0R1A2A2A2A2A2Ls;A2Lb;A2S1fS1eS7G0ScRaR3A2A2R2A2R9A2A2F_;Fsz;Fe;F_;Fmaps;F_;F_;F_;FLB;Frho;").
Proof using HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim HPL4 HPL5 HPL6 HPL7 HPL8. intros rho LB HV H36 H77 maps [l ->] e sz Hin. pose proof m13_ledger as (_ & M2 & _).
  unfold G13b in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|[[= <- <-]|[]]].
  - apply (blocks12b rho LB HV H36); [|exact Hin]. rewrite M2. exists (l ++ [(b8, Z_to_bv 64 4096)]). rewrite <- app_assoc. reflexivity.
  - left. cbn [eval]. rewrite H77. exists b8, (Z_to_bv 64 4096). split; [apply in_app_iff; right; rewrite M2; left; reflexivity|]. rewrite u64_of_lit by lia. lia.
Qed.

Lemma clear14 : ltac2:(tb__ "0|0|
S1S4cS76S5eS5aS8eA1A2S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma seg14 : ltac2:(tb__ "0|5|
S8S3aR1A1S1S6Q40M0A1M1S9R2P24A2Vb7;A3S1G1S9R3P4dA2Vb8;A3S58S1dVok;S43S1dS37S66Vb8;A1M2S1eS3bZ1000M3A2M4A2S8eR4S38R4A1A5S56S2G1G1S0S53S5G0Z0A2G2S5G0G3A2R1A4S44S1dS37S5dR1A1S1eG4G3A2A2P4fS8cR6P4eR1A3S38R6A1S49S59S5bS8fS81A2S4dS59A1A3R2A7A2Lb9;A2Lw;A4F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 Ha1 Ha2 Hmaps Hna Hres Htop Hlz OKF OKP.
  intros rho HV H36 H77. pose proof m13_ledger as (M1 & M2 & M3 & M4). pose proof HV as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1).
  eapply triple_seq.
  { apply triple1_triple.
    apply (eager_rw_node ok OKF OKP E_s14 4096 (m13 b8) (B12x + 4096) G13b 79%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear14.
    + rewrite M1. exact Hres.
    + exact init_sp_ok_m13.
    + exact band_m13.
    + rewrite M3. unfold B12x, B12, B11. lia.
    + apply (blocks13b rho _ HV H36 H77). exists []. reflexivity.
    + rewrite M4. exact Hv1. }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA (m13 b8) (B12x + 4096)) (OKFx _ _) (fun n => stableA_KxA segsA n (m13 b8) (B12x + 4096)) _ SPIN14 200%nat SPIN_MMAPORDIE);
      [reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact run14_fail | exact spin14].
  - apply triple_ex; intros b9. apply triple_pure; intros HPL9.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b9; split; [exact HPL9|exact Hw] |].
    apply triple1_triple.
    assert (N : ss_next (ax_S E_s14) = 78%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    change (eager_ok E_s14 4096 79) with S_s14ok. rewrite N.
    eapply sym_run_soundA; [exact run14_ok | apply OKFx | reflexivity | apply stableA_KxA].
Qed.

Hypothesis Hw14 : ltac2:(tb__ "0|2|
S2S6Q40M0A1M1G1S53S5G0Z0A2S66Vb8;A1S5G0Z1000A2R1A4La;A2").
Lemma eseg14 : ltac2:(tb__ "0|5|
S8S3aR1A1S1S6Q40M0A1M1S9R2P24A2Vb7;A3S1G1S9R3P4dA2Vb8;A3S57S1dS43S1dS37S66Vb8;A1M2S1eS3bZ1000M3A2M4A2S8eR4S38R4A1A5S56S2G1G1S0S53S5G0Z0A2G2S5G0G3A2R1A4S44S1dS37S5dR1A1S1eG4G3A2A2P4fS8cR6P4eR1A3S38R6A1S49S59S5bS8fS81A2S4dS59A1A3R2A7A2Lb9;A2Lw;A3F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 Hmaps Hres Htop Hlz Hw14.
  clear Ha1 Ha2. intros rho HV H36 H77. pose proof m13_ledger as (M1 & M2 & M3 & M4). pose proof HV as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1).
  eapply etriple_seq.
  { apply (eager_rw_enode E_s14 4096 (m13 b8) (B12x + 4096) G13b 79%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear14.
    + rewrite M1. exact Hres.
    + exact init_sp_ok_m13.
    + exact band_m13.
    + rewrite M3. unfold B12x, B12, B11. lia.
    + exact Hw14.
    + apply (blocks13b rho _ HV H36 H77). exists []. reflexivity.
    + rewrite M4. exact Hv1. }
  apply etriple_ex; intros b9. intros w [HPL9 Hsp]. revert w Hsp.
  assert (N : ss_next (ax_S E_s14) = 78%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  change (etriple segsA (SPA segsA (KxA (m14 b9) (B12x + 4096 + 4096)) (eager_ok E_s14 4096 79) (rho_set_rw rho (ss_next (ax_S E_s14)) b9) (TP12 rho))
           (fun w => exists b0, mmap_place_ok_none (Z_to_bv 64 0) (m13 b8) (Z_to_bv 64 4096) b0
              /\ LQA segsA (KxA (m14 b0) (B12x + 4096 + 4096)) 79 (rho_set_rw rho 78 b0) (TP12 rho) [mkLeafA E_s15 RsCut] w)).
  rewrite N. change (eager_ok E_s14 4096 79) with S_s14ok.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b9; split; [exact HPL9|exact Hw] |].
  rewrite <- N. eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run14_ok].
Qed.

Section S14.
Variable b9 : word.
Hypothesis HPL9 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2S66Vb8;A1S5G0Z1000A2Vb9;A4").
Definition m15 : Model := ltac2:(tb__ "0|0|
S54S5dVb9;A1Vb9;S5Q40Z1000A2A3").
Definition G14b : list (sv * Z) := ltac2:(tb__ "0|1|
S4bS47SaS27A2M0S5eS49G0S48SaS27S11P4eA1Z1000A4S4dG0A1A3A3").

Lemma m14_ledger : ltac2:(tb__ "0|6|
S0S1S4aS47S6Q40M0A1M1G1A2M2A1M3S2bS29S5dVb9;A1A1M4A1S2bS29Vm;A1M5A1A3S0S1G3S2aG4A1S49G2S48G1G1Vb9;S5G0Z1000A2A4S2aS29S66Vb8;A1A1A1A3A3S0S1S27S2cG4A1S2cG5A1A3S1G1S2dG4A1S2dG5A1A3A2A2A2").
Proof.
  clear. pose proof m13_ledger as (L1 & L2 & L3 & L4).
  unfold m14, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps. cbn [vm_reserved vm_maps vm_limit vm_init_sp]. rewrite L1, L3, L4. repeat split; reflexivity.
Qed.
Lemma init_sp_ok_m14 : ltac2:(tb__ "0|0|
S55S29S5dVb9;A1A1A1").
Proof using Htop. clear -Htop. pose proof m14_ledger as (_ & _ & _ & L4). unfold init_sp_ok in *. rewrite L4. exact Htop. Qed.
Lemma band_m14 : ltac2:(tb__ "0|2|
S65S4bS47S6Q40A1M0G0A2S2bS29S5dVb9;A1A1M1A1S2aG1A1A3S64S63A3").
Proof using Hmaps. clear -Hmaps. pose proof m14_ledger as (L1 & L2 & _). pose proof m13_ledger as (K1 & _).
  rewrite L1, L2, <- K1. apply (band_covered_after_grant (m13 b8)). exact band_m13. Qed.
Lemma b9_facts : ltac2:(tb__ "0|6|
S0S1fZ1000M0S7Q40M1Vb9;A2M2A2S0S3S1fS1eG2G0A2M3Z10000A2S1fZ643000G2A2A2S0S6dG2G0A2S0S1fG3S2eS29Vm;A1A1A2S0S1S27S21G2G0A2Z0A3S1S4cS30S4bS47S6G1A1M4G4A2S2bS29S66Vb8;A1A1M5A1S2aG5A1A3Vb9;S5G1G0A2A3S4eA3A2A2A2A2A2").
Proof using HPL9 HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. pose proof m13_ledger as (L1 & L2 & L3 & L4).
  pose proof (place_LB_A (m13 b8) 4096 b9 init_sp_ok_m13 ltac:(rewrite L1; exact Hres) band_m13 ltac:(lia) ltac:(reflexivity) HPL9) as (PLB & Pimg & Pband & Ptop & _).
  pose proof HPL9 as (Hal & _ & _ & Hfree). revert Ptop. unfold alloc_top. rewrite L4. intros Ptop.
  assert (Hn : mmap_n (Z_to_bv 64 4096) = Z_to_bv 64 4096) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Hn in Hfree.
  change (LB_of 4096) with 0x1000 in PLB. split; [exact PLB|]. split; [exact Pimg|]. split; [exact (bandav_intro _ _ Pband)|]. repeat split; assumption.
Qed.

Lemma clear15 : ltac2:(tb__ "0|0|
S1S4cS76S96S5aS90A1A2S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma region_free_filter : ltac2:(tb__ "0|2|
S47S6Q40A1M0G0A2M1S4cF_;S4aG1A1G0G0S1S4cS30R3R2R1A3S4eA3S1S4cS30S61G1R5R4A3R3R2A3S4eA3F_;Fk;Fa;Fl;Ff;").
Proof.
  clear. intros f l a k. induction l as [|[b sz] l IH]; cbn; intros H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. destruct (f (b, sz)); cbn; [rewrite H1; cbn|]; apply IH; exact H2.
Qed.
Lemma tp_forget_id : ltac2:(tb__ "0|4|
S27S27S4aS6Q40M0A1M1A1M2G1S5fG1R1R2A3S3S20S7G0R2A2M3R5A2S1fR4G3A2A2F_;Fp;S1G2S98R4R3R2A3R2A3F_;Ftp;Fhi;Flo;").
Proof.
  clear. intros lo hi tp H. unfold tp_forget. induction tp as [|p tp IH]; cbn; [reflexivity|].
  unfold page_outside_range at 1. replace ((lo <=? bv_unsigned p) && (bv_unsigned p <? hi))%bool with false.
  2:{ symmetry. destruct (H p (or_introl eq_refl)) as [X|X]; apply andb_false_iff; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
  cbn. rewrite IH; [reflexivity|]. intros q Hq. apply H. right. exact Hq.
Qed.

Lemma TP12_band : ltac2:(tb__ "0|3|
S8S82SbSfR1A1S10S5aS90A1A1A3S3aR2A1S6Q40M0A1M1S5fG1R1S38R4A1A3S0S1fS64S7G0R2A2M2A2S1fS1eG2Z1000A2S63A2A2F_;Fp;F_;F_;Frho;").
Proof using HPL HPL6 HPL4 HPL5 Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim HPL7 HPL8 HPL9.
  intros rho HF HV p Hp. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1). destruct E_s15u_facts as (X1 & X2 & X3 & X4).
  pose proof (fact_of_state _ _ rho X1 HF) as A1. pose proof (fact_of_state _ _ rho X2 HF) as A2.
  pose proof (fact_of_state _ _ rho X3 HF) as A3. pose proof (fact_of_state _ _ rho X4 HF) as A4.
  cbn [holds eval] in A1, A3. rewrite Z_to_bv_unsigned in A1, A3.
  change (bv_wrap 64 0x7fffffffff20) with 0x7fffffffff20 in A1. change (bv_wrap 64 (2 ^ 61 - 1)) with (2 ^ 61 - 1) in A3.
  cbn [holds] in A2. apply (f_equal bv_unsigned) in A2.
  change (bv_unsigned (eval rho (SAlu ALU_SLL (SVar 35%positive) (SLit 3)))) with (SymSoundV.U rho (StepA.g8 35%positive)) in A2.
  rewrite (StepA.U_g8 rho 35%positive) in A2 by (unfold SymSoundV.U; cbn [eval]; exact A3). unfold SymSoundV.U in A2. cbn [eval] in A2. rewrite H34 in A2.
  pose proof b6_facts as (F6lo & _ & F6top & _).
  pose proof P_facts as (Pal & Pceil & _ & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof SB_val as SB.
  unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB.
  pose proof (urange P) as UP. pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB.
  pose proof (urange (rw rho 31%positive)) as U31.
  assert (Htopv : alloc_top (m_vmmaps m) = bv_unsigned (rw rho 1%positive) - 0x800000) by (unfold alloc_top; rewrite stack_max_size_val, <- Hv1; reflexivity).
  assert (Upr : bv_unsigned (pRI rho) = priZ rho).
  { unfold pRI, shRI_base, priZ. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (bv_wrap 64 19327320064) with 19327320064. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
  assert (Hpri : 0x2008fff7000 <= priZ rho /\ priZ rho + 12288 <= 0x10007fff8000) by (unfold priZ; lia).
  assert (Hsh : shZ rho <= 0x10007fff7fe4).
  { unfold shZ. pose proof (Z.div_le_mono (bv_unsigned (rw rho 1%positive)) 0x7fffffffff20 8 ltac:(lia) A1). change (0x7fffffffff20 / 8) with 17592186044388 in H. lia. }
  assert (Hsh0 : 0x7fff8000 + 0xFFFF0000000 <= shZ rho).
  { assert (HX1 : 0x7fff80000000 <= bv_unsigned (rw rho 1%positive)) by (rewrite Hv1; unfold init_sp_ok, sp_window_lo in Htop; lia).
    unfold shZ. pose proof (Z.div_le_mono 0x7fff80000000 (bv_unsigned (rw rho 1%positive)) 8 ltac:(lia) HX1). change (0x7fff80000000 / 8) with 0xFFFF0000000 in H. lia. }
  pose proof (Z.mod_pos_bound (shZ rho - 131072) 4096 ltac:(lia)) as Qm. pose proof (Z.mod_pos_bound (shZ rho - 9) 4096 ltac:(lia)) as Em.
  pose proof (Z.mod_pos_bound (sbZ rho) 4096 ltac:(lia)) as Q1m.
  assert (Eq12 : q12 rho = shZ rho - 131072 - (shZ rho - 131072) mod 4096) by reflexivity.
  assert (Ee12 : e12 rho = shZ rho - 9 - (shZ rho - 9) mod 4096) by reflexivity.
  assert (Eq1 : q1Z rho = sbZ rho - sbZ rho mod 4096) by reflexivity.
  assert (Esb : sbZ rho = bv_unsigned (rw rho 35%positive) + 0x7fff8000) by reflexivity.
  assert (Hsb : 0x7fff8000 + 820736 <= sbZ rho /\ sbZ rho + 8192 <= 0x7fff8000 + (bv_unsigned (rw rho 1%positive) - 0x800000) / 8).
  { rewrite Esb. split; [lia|].
    pose proof (Z.div_le_mono (bv_unsigned b6 + 65536) (bv_unsigned (rw rho 1%positive) - 0x800000) 8 ltac:(lia) ltac:(lia)).
    rewrite <- A2 in H. replace (8 * bv_unsigned (rw rho 35%positive) + 65536) with ((bv_unsigned (rw rho 35%positive) + 8192) * 8) in H by lia.
    rewrite Z.div_mul in H by lia. lia. }
  assert (Hq : q12 rho <= shZ rho - 131072 < q12 rho + 4096) by (unfold q12; lia).
  assert (He : e12 rho <= shZ rho - 9 < e12 rho + 4096) by (unfold e12; lia).
  assert (Hqal : q12 rho mod 4096 = 0) by (unfold q12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  assert (Heal : e12 rho mod 4096 = 0) by (unfold e12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  apply Z.mod_divide in Hqal as [tq Htq]; [|lia]. apply Z.mod_divide in Heal as [te Hte]; [|lia].
  assert (Hn : Z.of_nat (n12 rho) = te - tq + 1).
  { unfold n12. rewrite Htq, Hte. replace (te * 4096 - tq * 4096) with ((te - tq) * 4096) by lia. rewrite Z_div_mult by lia. rewrite Z2Nat.id; lia. }
  pose proof (Z.div_le_mono (bv_unsigned (rw rho 1%positive) - 0x800000) 0x7fffff7fff20 8 ltac:(lia) ltac:(lia)) as DV.
  change (0x7fffff7fff20 / 8) with 17592184995812 in DV.
  unfold TP12, TP11 in Hp. unfold SHADOW_BAND_LO, SHADOW_BAND_HI.
  set (r1 := (shZ rho - 131072) mod 4096) in *. clearbody r1.
  set (r2 := (shZ rho - 9) mod 4096) in *. clearbody r2.
  set (r3 := sbZ rho mod 4096) in *. clearbody r3.
  set (dv := (bv_unsigned (rw rho 1%positive) - 0x800000) / 8) in *. clearbody dv.
  set (sh := shZ rho) in *. clearbody sh. set (sb := sbZ rho) in *. clearbody sb.
  set (q := q12 rho) in *. clearbody q. set (ee := e12 rho) in *. clearbody ee. set (q1 := q1Z rho) in *. clearbody q1.
  set (pr := priZ rho) in *. clearbody pr. pose proof (urange (pRI rho)) as Upr0. rewrite Upr in Upr0.
  clear HF A4 Htopv F6top Pceil SB.
  apply in_app_iff in Hp as [Hp|Hp].
  - apply In_pages_rev in Hp as (k & Hk & ->). unfold pageZ. rewrite !u64_of_lit by lia. lia.
  - destruct (q1 =? pr); cbn [In] in Hp; decompose [or] Hp; subst; try contradiction;
      first [rewrite !Upr | rewrite !u64_of_lit by lia | idtac]; lia.
Qed.

Lemma post15 : ltac2:(tb__ "0|8|
S8S8S56S75P4fM0R3R2A3S3cR4R3A2S77R5R4A2S1S6Q40M1A1S9R5P4eM2A2Vb9;A3S82SbSfR6A1S10S5aS90A1A1A3S3aR7A1S43S1dS37S54S5dVb9;A1S9R8G2A2M3S5G1Z1000M4A2M5A3S1eS1eS3bG4A2G4A2M6A2S9eS90G0A2Sa0R8S9fSdR8A1G3G5A3A2S98S7G1G3A2M7S1eG7G4A2S38R9A1A3R7A6S2S8S8S0S75G0RbR1A3S0S3cRbR1A2S0S77RbR1A2S43S1dS37S95G6A2S91R1S38RbA1R9A6A2A2A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;Fw;Frho1;Frho;").
Proof using HPL9 HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. intros rho rho1 w Hag1 RS1 RM1 H78' HF1 HV1 Hw. pose proof Hag1 as [A1 L1]. pose proof b9_facts as (K1 & Kimg & Kband & K3 & K2 & K4).
  exists (set_rm rho1 (unmap_range (rm rho1) (rw rho1 78%positive) (Z_to_bv 64 4096))).
  split; [split; [intros i Hi; cbn; apply A1; exact Hi | intros l; cbn; apply L1]|].
  split.
  { intros a Ha. cbn [rm set_rm]. rewrite H78'. rewrite unmap_range_at.
    unfold SysStep.in_range. rewrite u64_of_lit by lia.
    match goal with |- (if ?c then _ else _) = _ => replace c with false end; [apply RS1; exact Ha|].
    symmetry. clear -Ha Kband. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in Ha. unfold bandav in Kband.
    apply andb_false_iff. destruct Kband as [K|K]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]. }
  split.
  { apply RMH_unmap; [exact RM1|]. rewrite H78', u64_of_lit by lia.
    pose proof HV1 as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1). pose proof Hag1 as [A1' _]. rewrite <- (A1' 1%positive) by lia. rewrite Hv1.
    revert K3. unfold alloc_top. rewrite stack_max_size_val. intros K3. lia. }
  rewrite H78' in Hw. rewrite (tp_forget_id) in Hw.
  2:{ intros p Hp. pose proof (TP12_band rho1 HF1 HV1 p) as X.
      rewrite (TP12_agree rho rho1) in X by (split; [intros i Hi; apply A1; lia | exact L1]). specialize (X Hp).
      clear -X Kband. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in X. unfold bandav in Kband. lia. }
  unfold m15. rewrite H78'. exact Hw.
Qed.

Lemma has15 : ltac2:(tb__ "0|0|
S1S4cS35S2aS29S5dVb9;A1A1A1Vb9;S5Q40Z1000A2A3S4eA3").
Proof. clear. pose proof m14_ledger as (_ & M2 & _). rewrite M2. cbn [map_has existsb fst snd]. rewrite !(proj2 (Fs.bv_eqb_eq _ _) eq_refl). reflexivity. Qed.
Lemma uniq15 : ltac2:(tb__ "0|2|
S6Q40M0A1M1S5fS47G1G1A2S48G1G1Vb9;R1A4S2aS29S5dVb9;A1A1A1A3S1G1R2S5G0Z1000A2A3F_;Fsz;").
Proof using HPL9 HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps Ha1 Ha2.
  clear HBlim. pose proof m14_ledger as (M1 & M2 & M3 & M4). pose proof b9_facts as (K1 & Kimg & Kband & K3 & K2 & K4).
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof b4_facts as (F4lo & _). pose proof b5_facts as (F5lo & _).
  pose proof b6_facts as (F6lo & _). pose proof (b7_facts b7 HPL7) as (F7lo & _). pose proof b8_facts as (F8lo & _).
  rewrite M2. intros sz [[= <-]|Hin]; [reflexivity|]. exfalso.
  pose proof (region_free_In _ _ _ _ _ (region_free_app_r _ _ _ _ K4) Hin) as OV.
  unfold iv_overlap in OV. apply andb_false_iff in OV. rewrite u64_of_lit in OV by lia.
  pose proof m13_ledger as (_ & N2 & _). pose proof (m12_ledger b7) as (_ & O2 & _). pose proof mE_ledger as (_ & Q2 & _).
  rewrite N2, O2, Q2, Hmaps in Hin. pose proof (urange b9) as U9. clear Ha1 Ha2 Kband Kimg.
  destruct Hin as [[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[]]]]]]]]]]]];
    try (rewrite u64_of_lit in OV by lia); unfold n9, n7 in OV; try (rewrite u64_of_lit in OV by lia); destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
Qed.
Lemma free15 : ltac2:(tb__ "0|0|
S1S4cS30S36S2aS29S5dVb9;A1A1A1Vb9;A2Vb9;S5Q40Z1000A2A3S4eA3").
Proof using HPL9 HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. pose proof m14_ledger as (_ & M2 & _). pose proof b9_facts as (_ & _ & _ & _ & _ & K4).
  rewrite M2. cbn [map_remove List.filter fst]. rewrite (proj2 (Fs.bv_eqb_eq _ _) eq_refl). cbn [negb].
  apply region_free_filter. exact (region_free_app_r _ _ _ _ K4).
Qed.
Lemma blocks15 : ltac2:(tb__ "0|4|
S8S3aR1A1S1S6Q40M0A1M1S9R2P24A2Vb7;A3S1G1S9R3P4dA2Vb8;A3SaS27S5fS47SaS27A2S48SaS27R2R1A4S5eA3S27S0S1fS7G0Vb9;A2M2R1A2S20R1S1eG2Z1000A2A2A2S4S0S1fS7G0ScR9R5A2A2M3R2A2S20R2S1eG3R4A2A2A2A1F_;Fx;F_;Fsz;Fe;F_;F_;F_;Frho;").
Proof using HPL9 HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. intros rho HV H36 H77 e sz Hin x Hx. pose proof b9_facts as (_ & _ & _ & _ & _ & K4).
  destruct (blocks13b rho 0 HV H36 H77 (vm_maps (m_vmmaps (m13 b8))) ltac:(exists []; reflexivity) e sz Hin) as [(b & s' & Hb & Hlo & Hhi)|Hlow].
  - pose proof (region_free_In _ _ _ _ _ (region_free_app_r _ _ _ _ K4) Hb) as OV.
    unfold iv_overlap in OV. apply andb_false_iff in OV. rewrite u64_of_lit in OV by lia.
    destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
  - pose proof (urange (eval rho e)). lia.
Qed.

Lemma rel15 : ltac2:(tb__ "0|3|
S8S4aS2fA1M0S97S31S3aR4A1S1S6Q40A1S9R5P4eA2Vb9;A3S43S1dS37S5dVb9;A1S1eS1eS3bZ1000M1A2G1A2A2M2S8fR6S38R6A1S48G0S92R5S93R4R3A2A4A6S2S8S8S0S75P4fR8R1A3S0S3cR8R1A2S0S77R8R1A2S43S1dG2S90R1S38R8A1S48G0S92R7S93R6R5A2A4A6A2A2A2Lrho1;A2F_;F_;F_;Fmd;Fms;Ftr;Frho;").
Proof using HPL9 HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. intros rho tr ms md HV H78 Hw. pose proof b9_facts as (K1 & Kimg & Kband & K3 & K2 & K4).
  pose proof HV as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1).
  exists (rho_absorb rho [last (ss_objs (ax_S E_s15)) (mmap_obj 78%positive 4096)] (vms md (TP12 rho) ms)).
  assert (SH : ob_base (last (ss_objs (ax_S E_s15)) (mmap_obj 78%positive 4096)) = SVar 78%positive
               /\ ob_lo (last (ss_objs (ax_S E_s15)) (mmap_obj 78%positive 4096)) = SLit 0
               /\ ob_hi (last (ss_objs (ax_S E_s15)) (mmap_obj 78%positive 4096)) = SLit 4096) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2).
  destruct SH as (B1 & B2 & B3).
  split; [split; intros; reflexivity|]. split.
  { intros a Ha. apply rm_absorb_outside. intros (o & [<-|[]] & Hr). revert Hr.
    unfold obj_range, obj_lo_of, obj_hi_of. rewrite B1, B2, B3. cbn [eval fst snd].
    rewrite H78, !soff_lit_small by lia. clear -Ha Kband. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in Ha. unfold bandav in Kband. lia. }
  split.
  { apply RMH_absorb; [apply RMH_refl|]. intros a [Ha _] (o & [<-|[]] & Hr). revert Hr.
    unfold obj_range, obj_lo_of, obj_hi_of. rewrite B1, B2, B3. cbn [eval fst snd].
    rewrite H78, !soff_lit_small by lia. revert K3. unfold alloc_top. rewrite stack_max_size_val, <- Hv1. intros K3 Hr. lia. }
  rewrite <- E_s15u_eq.
  apply (SPA_unobj segsA (KxA (m14 b9) (B12x + 4096 + 4096)) rho E_s15 (ss_objs (ax_S E_s15u)) _ (TP12 rho) tr ms md E_s15_split Hw). intros X; exact X.
Qed.

Lemma seg15 : ltac2:(tb__ "0|3|
S8S3aR1A1S1S6Q40A1M0S9R2P24A2Vb7;A3S1G0S9R3P4dA2Vb8;A3S1G0S9R4P4eA2Vb9;A3S58S1dVok;S43S1dS37S5dVb9;A1S1eS1eS3bZ1000M1A2G1A2M2A2S8fR5S38R5A1A5S56S2S8S8S0S75P4fR7R1A3S0S3cR7R1A2S0S77R7R1A2S43S1dS37S95G2A2S91R1S38R7A1R2A6A2A2A2Lrho';A2Lw;A4F_;F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hmaps Hna Hres Htop Hlz OKF OKP.
  intros rho HV H36 H77 H78. pose proof m14_ledger as (M1 & M2 & M3 & M4). pose proof b9_facts as (K1 & Kimg & Kband & K3 & K2 & K4).
  pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  apply (@triple_conseq segsA ok (fun w => exists rho1, agree_vars 79%positive rho rho1 /\ rm_same_band rho rho1 /\ RMH rho rho1 /\ SPA segsA (KxA (m14 b9) (B12x + 4096 + 4096)) E_s15u rho1 (TP12 rho) w)
                         (SPA segsA (KxA (m14 b9) (B12x + 4096 + 4096)) E_s15 rho (TP12 rho))
                         (fun w => exists rho', agree_vars 79%positive rho rho' /\ rm_same_band rho rho' /\ RMH rho rho' /\ SPA segsA (KxA m15 (B12x + 4096 + 4096)) S_s15ok rho' (TP12 rho) w)
                         (fun w => exists rho', agree_vars 79%positive rho rho' /\ rm_same_band rho rho' /\ RMH rho rho' /\ SPA segsA (KxA m15 (B12x + 4096 + 4096)) S_s15ok rho' (TP12 rho) w));
    [intros [tr [ms md]] Hw; exact (rel15 rho tr ms md HV H78 Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho1. apply triple_pure; intros Hag1. apply triple_pure; intros RS1. apply triple_pure; intros RM1. pose proof Hag1 as [A1 L1].
  assert (H78' : rw rho1 78%positive = b9) by (rewrite (A1 78%positive) by lia; exact H78).
  assert (HV1 : vals12 rho1) by (eapply (vals12_agree 79%positive rho rho1); [lia | exact HV | intros i Hi; apply A1; exact Hi]).
  apply triple_factsA. intros HF1.
  eapply triple_conseq; [intros w Hw; exact Hw | | apply triple1_triple;
    apply (munmap_node ok OKF OKP E_s15u 78%positive 4096 (m14 b9) (B12x + 4096 + 4096) G13b 79%positive
             eq_refl eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)
             eq_refl ltac:(lia) ltac:(lia) ltac:(vm_compute; intros XX; discriminate XX) clear15 init_sp_ok_m14 rho1 (TP12 rho))].
  - cbv beta. intros w Hw. exact (post15 rho rho1 w Hag1 RS1 RM1 H78' HF1 HV1 Hw).
  - rewrite H78'. exact K2.
  - rewrite H78'. exact Kimg.
  - rewrite H78'. revert K3. unfold alloc_top. rewrite M4. intros K3. exact K3.
  - rewrite (A1 1%positive) by lia. rewrite M4. exact Hv1.
  - rewrite H78'. exact has15.
  - rewrite H78'. exact uniq15.
  - rewrite H78'. exact free15.
  - rewrite H78'. exact (blocks15 rho1 HV1 ltac:(rewrite (A1 36%positive) by lia; exact H36) ltac:(rewrite (A1 77%positive) by lia; exact H77)).
Qed.
Lemma eseg15 : ltac2:(tb__ "0|3|
S8S3aR1A1S1S6Q40A1M0S9R2P24A2Vb7;A3S1G0S9R3P4dA2Vb8;A3S1G0S9R4P4eA2Vb9;A3S57S1dS43S1dS37S5dVb9;A1S1eS1eS3bZ1000M1A2G1A2M2A2S8fR5S38R5A1A5S56S2S8S8S0S75P4fR7R1A3S0S3cR7R1A2S0S77R7R1A2S43S1dS37S95G2A2S91R1S38R7A1R2A6A2A2A2Lrho';A2Lw;A3F_;F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hmaps Hna Hres Htop Hlz.
  intros rho HV H36 H77 H78. pose proof m14_ledger as (M1 & M2 & M3 & M4). pose proof b9_facts as (K1 & Kimg & Kband & K3 & K2 & K4).
  pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  apply (@etriple_conseq segsA (fun w => exists rho1, agree_vars 79%positive rho rho1 /\ rm_same_band rho rho1 /\ RMH rho rho1 /\ SPA segsA (KxA (m14 b9) (B12x + 4096 + 4096)) E_s15u rho1 (TP12 rho) w)
                         (SPA segsA (KxA (m14 b9) (B12x + 4096 + 4096)) E_s15 rho (TP12 rho))
                         (fun w => exists rho', agree_vars 79%positive rho rho' /\ rm_same_band rho rho' /\ RMH rho rho' /\ SPA segsA (KxA m15 (B12x + 4096 + 4096)) S_s15ok rho' (TP12 rho) w)
                         (fun w => exists rho', agree_vars 79%positive rho rho' /\ rm_same_band rho rho' /\ RMH rho rho' /\ SPA segsA (KxA m15 (B12x + 4096 + 4096)) S_s15ok rho' (TP12 rho) w));
    [intros [tr [ms md]] Hw; exact (rel15 rho tr ms md HV H78 Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho1. apply etriple_pure; intros Hag1. apply etriple_pure; intros RS1. apply etriple_pure; intros RM1. pose proof Hag1 as [A1 L1].
  assert (H78' : rw rho1 78%positive = b9) by (rewrite (A1 78%positive) by lia; exact H78).
  assert (HV1 : vals12 rho1) by (eapply (vals12_agree 79%positive rho rho1); [lia | exact HV | intros i Hi; apply A1; exact Hi]).
  apply etriple_factsA. intros HF1.
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    apply (munmap_enode E_s15u 78%positive 4096 (m14 b9) (B12x + 4096 + 4096) G13b 79%positive
             eq_refl eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)
             eq_refl ltac:(lia) ltac:(lia) ltac:(vm_compute; intros XX; discriminate XX) clear15 init_sp_ok_m14 rho1 (TP12 rho))].
  - cbv beta. intros w Hw. exact (post15 rho rho1 w Hag1 RS1 RM1 H78' HF1 HV1 Hw).
  - rewrite H78'. exact K2.
  - rewrite H78'. exact Kimg.
  - rewrite H78'. revert K3. unfold alloc_top. rewrite M4. intros K3. exact K3.
  - rewrite (A1 1%positive) by lia. rewrite M4. exact Hv1.
  - rewrite H78'. exact has15.
  - rewrite H78'. exact uniq15.
  - rewrite H78'. exact free15.
  - rewrite H78'. exact (blocks15 rho1 HV1 ltac:(rewrite (A1 36%positive) by lia; exact H36) ltac:(rewrite (A1 77%positive) by lia; exact H77)).
Qed.
End S14.
End S13.
End S13a.

Lemma stackshadow_zero_band_ext : ltac2:(tb__ "0|4|
S8S8S1S6Q40M0A1S9R1P1M1A2S9R2G1A2A3S0S1fZ7fff80000000S7G0S9R3G1A2A2M2A2S1fG2Z800000000000A2A2S3cR4R3A2S40R5A1M3G3F_;F_;F_;F_;Frho';Frho;").
Proof.
  clear. intros rho rho' H1 Hx RS Hz. destruct (q12_ext rho rho' H1) as (E1 & E2 & E3). unfold stackshadow_zero. rewrite E1, E3.
  intros z Hzz.
  pose proof (Z.mod_pos_bound (shZ rho - 131072) 4096 ltac:(lia)) as Qm. pose proof (Z.mod_pos_bound (shZ rho - 9) 4096 ltac:(lia)) as Em.
  assert (Hsh : shZ rho <= 0x10007fff8000).
  { unfold shZ. pose proof (Z.div_le_mono (bv_unsigned (rw rho 1%positive)) 0x800000000000 8 ltac:(lia) ltac:(lia)). change (0x800000000000 / 8) with 17592186044416 in H. lia. }
  assert (Hsh0 : 0x7fff8000 + 0xFFFF0000000 <= shZ rho).
  { unfold shZ. pose proof (Z.div_le_mono 0x7fff80000000 (bv_unsigned (rw rho 1%positive)) 8 ltac:(lia) ltac:(lia)). change (0x7fff80000000 / 8) with 0xFFFF0000000 in H. lia. }
  assert (Hq : q12 rho <= shZ rho - 131072 < q12 rho + 4096) by (unfold q12; lia).
  assert (He : e12 rho <= shZ rho - 9 < e12 rho + 4096) by (unfold e12; lia).
  assert (Hqal : q12 rho mod 4096 = 0) by (unfold q12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  assert (Heal : e12 rho mod 4096 = 0) by (unfold e12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  apply Z.mod_divide in Hqal as [tq Htq]; [|lia]. apply Z.mod_divide in Heal as [te Hte]; [|lia].
  assert (Hn : Z.of_nat (n12 rho) = te - tq + 1).
  { unfold n12. rewrite Htq, Hte. replace (te * 4096 - tq * 4096) with ((te - tq) * 4096) by lia. rewrite Z_div_mult by lia. rewrite Z2Nat.id; lia. }
  rewrite (RS (Z_to_bv 64 z)) by (rewrite u64_of_lit by lia; unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia). apply Hz. exact Hzz.
Qed.

Definition Post5 (rho : valuation) : assn := ltac2:(tb__ "0|6|
S56S2S6Q40M0A1M1G1S2G1G1S2G1G1S2S8S8S0S53S5G0Z0A2M2VmE;S5G0Z1000M3A2M4R4A4S0S53G2S39R4A1G4R3A4S0S53G2S3fR4R3A2G4R2A4S0S75P24M5Vrho;R1A3S0S1G1S9R1G5A2R4A3S0S1G1S9R1P4dA2R3A3S0S1G1S9R1P4eA2R2A3S0S40R1A1S0S6bR1A1S0S6cR1A1S0S77Vrho;R1A2S43S1dS37S42R4R3R2A3S1eS1eS3bG3A2G3A2A2S91R1S38R1A1R5A6A2A2A2A2A2A2A2A2A2A2A2Lrho';A2Lb9;A2Lb8;A2Lb7;A2Lw;").

Theorem start5_sum_A : ltac2:(tb__ "0|0|
S8S3aR1A1S6bR2A1S6cR3A1S58S1dVok;S43S1dS37VmE;S68VB;A1A2S8dR4S67R4A1A5S3eR4A1A4F_;F_;F_;Frho;").
Proof using All.
  intros rho HV HZ HD. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  assert (HX1 : 0x7fff80000000 <= bv_unsigned (rw rho 1%positive) <= 0x800000000000) by (rewrite Hv1; unfold init_sp_ok, sp_window_lo, sp_window_hi in Htop; lia).

  eapply triple_seq; [apply (seg12a rho HV)|].
  apply triple_ex; intros b7. apply triple_pure; intros HPL7.
  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho1. apply triple_pure; intros Hag1. pose proof Hag1 as (V1 & L1 & R1).
  assert (E1 : forall i, (i < 36)%positive -> rw rho1 i = rw rho i) by (intros i Hi; rewrite <- (V1 i) by lia; rewrite rho_set_rw_other by lia; reflexivity).
  assert (HV1 : vals12 rho1) by (eapply (vals12_agree 36%positive rho rho1); [lia | exact HV | exact E1]).
  assert (H36a : rw rho1 36%positive = b7) by (rewrite <- (V1 36%positive) by lia; apply rho_set_rw_at).
  assert (AV1 : agree_vars 36 rho rho1) by (split; [exact E1 | intros l; symmetry; apply L1]).
  assert (HZ1 : Z11 rho1) by (apply (Z11_ext rho rho1); [apply E1; lia | apply E1; lia | intros a; symmetry; apply R1 | exact HZ]).
  assert (HD1 : ZD11 rho1) by (apply (ZD11_ext rho rho1); [apply E1; lia | apply E1; lia | intros a; symmetry; apply R1 | exact HD]).
  rewrite <- (TP11_agree rho rho1 AV1).

  eapply triple_conseq; [intros w Hw; exact (prep12 b7 HPL7 rho1 w HV1 H36a Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho2. apply triple_pure; intros Hrw2. apply triple_pure; intros Hrl2. apply triple_pure; intros Hz2.
  apply triple_pure; intros Hrm2. apply triple_pure; intros HI2. apply triple_pure; intros LOW2. apply triple_pure; intros Q12K. apply triple_pure; intros LOWB2.
  assert (HV2 : vals12 rho2) by (eapply (vals12_agree 36%positive rho1 rho2); [lia | exact HV1 | intros i Hi; apply Hrw2]).
  assert (H36b : rw rho2 36%positive = b7) by (rewrite Hrw2; exact H36a).
  assert (AV2 : agree_vars 36 rho1 rho2) by (split; [intros i Hi; apply Hrw2 | exact Hrl2]).
  rewrite <- (TP12_agree rho1 rho2 AV2).

  eapply triple_seq; [apply (call12 b7 rho2 HV2 H36b)|].
  apply triple_ex; intros rho3. apply triple_pure; intros Hag3. pose proof Hag3 as (V3 & L3 & R3).
  assert (E3 : forall i, (i < 37)%positive -> rw rho3 i = rw rho2 i) by (intros i Hi; symmetry; apply V3; exact Hi).
  assert (AV3 : agree_vars 36 rho2 rho3) by (split; [intros i Hi; apply E3; lia | intros l; symmetry; apply L3]).
  rewrite <- (TP12_agree rho2 rho3 AV3).

  eapply triple_seq; [apply (seg12d b7 rho3)|].
  apply triple_ex; intros rho4. apply triple_pure; intros AV4. apply triple_pure; intros RS4. apply triple_pure; intros RM4.
  pose proof AV4 as [E4 L4].
  assert (HV4 : vals12 rho4) by (eapply (vals12_agree 37%positive rho2 rho4); [lia | exact HV2 | intros i Hi; rewrite E4 by lia; apply E3; lia]).
  assert (H36d : rw rho4 36%positive = b7) by (rewrite E4 by lia; rewrite E3 by lia; exact H36b).
  assert (AV4' : agree_vars 36 rho3 rho4) by (eapply agree_vars_le; [|exact AV4]; lia).
  rewrite <- (TP12_agree rho3 rho4 AV4').

  eapply triple_seq; [apply (seg13 b7 HPL7 rho4 HV4 H36d)|].
  apply triple_ex; intros b8. apply triple_pure; intros HPL8.
  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho5. apply triple_pure; intros Hag5. pose proof Hag5 as (V5 & L5 & R5).
  assert (E5 : forall i, (i < 77)%positive -> rw rho5 i = rw rho4 i) by (intros i Hi; rewrite <- (V5 i) by lia; rewrite rho_set_rw_other by lia; reflexivity).
  assert (HV5 : vals12 rho5) by (eapply (vals12_agree 77%positive rho4 rho5); [lia | exact HV4 | exact E5]).
  assert (H36e : rw rho5 36%positive = b7) by (rewrite E5 by lia; exact H36d).
  assert (H77e : rw rho5 77%positive = b8) by (rewrite <- (V5 77%positive) by lia; apply rho_set_rw_at).
  assert (AV5 : agree_vars 36 rho4 rho5) by (split; [intros i Hi; apply E5; lia | intros l; rewrite <- (L5 l); reflexivity]).
  rewrite <- (TP12_agree rho4 rho5 AV5).

  eapply triple_seq; [apply (seg14 b7 HPL7 b8 HPL8 rho5 HV5 H36e H77e)|].
  apply triple_ex; intros b9. apply triple_pure; intros HPL9.
  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho6. apply triple_pure; intros Hag6. pose proof Hag6 as (V6 & L6 & R6).
  assert (E6 : forall i, (i < 78)%positive -> rw rho6 i = rw rho5 i) by (intros i Hi; rewrite <- (V6 i) by lia; rewrite rho_set_rw_other by lia; reflexivity).
  assert (HV6 : vals12 rho6) by (eapply (vals12_agree 78%positive rho5 rho6); [lia | exact HV5 | exact E6]).
  assert (H36f : rw rho6 36%positive = b7) by (rewrite E6 by lia; exact H36e).
  assert (H77f : rw rho6 77%positive = b8) by (rewrite E6 by lia; exact H77e).
  assert (H78f : rw rho6 78%positive = b9) by (rewrite <- (V6 78%positive) by lia; apply rho_set_rw_at).
  assert (AV6 : agree_vars 36 rho5 rho6) by (split; [intros i Hi; apply E6; lia | intros l; rewrite <- (L6 l); reflexivity]).
  rewrite <- (TP12_agree rho5 rho6 AV6).

  eapply triple_conseq; [intros w Hw; exact Hw | | apply (seg15 b7 HPL7 b8 HPL8 b9 HPL9 rho6 HV6 H36f H77f H78f)].
  intros w (rho7 & AV7 & RS7 & RM7 & Hsp7). pose proof AV7 as [E7 L7].
  exists b7, b8, b9, rho7. split; [exact HPL7|]. split; [exact HPL8|]. split; [exact HPL9|].
  assert (CH : forall i, (i < 36)%positive -> rw rho7 i = rw rho i).
  { intros i Hi. rewrite E7 by lia. rewrite E6, E5, E4, E3 by lia. rewrite Hrw2. apply E1. exact Hi. }
  split.
  { split; [exact CH|]. intros l. rewrite L7, <- (L6 l). cbn. rewrite <- (L5 l). cbn. rewrite L4, <- (L3 l), Hrl2, <- (L1 l). reflexivity. }
  split; [rewrite E7 by lia; exact H36f|]. split; [rewrite E7 by lia; exact H77f|]. split; [rewrite E7 by lia; exact H78f|].
  assert (HX2 : 0x7fff80000000 <= bv_unsigned (rw rho2 1%positive) <= 0x800000000000) by (rewrite Hrw2, E1 by lia; exact HX1).
  split.
  { apply (stackshadow_zero_band_ext rho6 rho7); [apply E7; lia | rewrite E6, E5, E4, E3 by lia; exact HX2 | exact RS7 |].
    apply (stackshadow_zero_ext rho5 rho6); [apply E6; lia | intros a; symmetry; apply R6 |].
    apply (stackshadow_zero_ext rho4 rho5); [apply E5; lia | intros a; symmetry; apply R5 |].
    apply (stackshadow_zero_band_ext rho3 rho4); [apply E4; lia | rewrite E3 by lia; exact HX2 | exact RS4 |].
    apply (stackshadow_zero_ext rho2 rho3); [apply E3; lia | intros a; symmetry; apply R3 | exact Hz2]. }
  split.
  {
    assert (ZBAND : forall r (r' : valuation), agree_vars 36 rho1 r -> rw r' 31%positive = rw r 31%positive -> rw r' 35%positive = rw r 35%positive ->
              rm_same_band r r' -> Z11 r -> Z11 r').
    { intros r r' AVr E31 E35 RS HZr a p Hp Ha H64 N1 N2.
      assert (ET : TP11 r' = TP11 r) by (unfold TP11, q1Z, sbZ, priZ, pRI, shRI_base; cbn [eval]; rewrite E31, E35; reflexivity).
      rewrite ET in Hp. unfold priZ, sbZ in N1, N2. rewrite E31 in N1. rewrite E35 in N2.
      rewrite (RS (Z_to_bv 64 a)).
      - exact (HZr a p Hp Ha H64 N1 N2).
      -
        rewrite (TP11_agree rho1 r AVr) in Hp. pose proof (LOW2 p Hp). pose proof (LOWB2 p Hp). pose proof (urange p). rewrite u64_of_lit by lia. lia. }
    assert (Z2 : Z11 rho2).
    { intros a p Hp Ha H64 N1 N2. unfold priZ, sbZ in N1, N2. rewrite !Hrw2 in N1, N2.
      rewrite (TP11_agree rho1 rho2 AV2) in Hp. pose proof (urange p).
      rewrite (Hrm2 (Z_to_bv 64 a)) by (exists p; split; [exact Hp | rewrite u64_of_lit by lia; lia]). exact (HZ1 a p Hp Ha H64 N1 N2). }
    assert (Z3 : Z11 rho3) by (apply (Z11_ext rho2 rho3); [apply E3; lia | apply E3; lia | intros a; symmetry; apply R3 | exact Z2]).
    assert (AV13 : agree_vars 36 rho1 rho3) by (split; [intros i Hi; rewrite E3 by lia; apply Hrw2 | intros l; rewrite <- (L3 l); apply Hrl2]).
    assert (Z4 : Z11 rho4) by (apply (ZBAND rho3 rho4 AV13); [apply E4; lia | apply E4; lia | exact RS4 | exact Z3]).
    assert (Z5 : Z11 rho5) by (apply (Z11_ext rho4 rho5); [apply E5; lia | apply E5; lia | intros a; symmetry; apply R5 | exact Z4]).
    assert (Z6 : Z11 rho6) by (apply (Z11_ext rho5 rho6); [apply E6; lia | apply E6; lia | intros a; symmetry; apply R6 | exact Z5]).
    assert (AV16 : agree_vars 36 rho1 rho6).
    { split; [intros i Hi; rewrite E6, E5, E4, E3 by lia; apply Hrw2 | intros l; rewrite <- (L6 l); cbn; rewrite <- (L5 l); cbn; rewrite L4, <- (L3 l); apply Hrl2]. }
    apply (ZBAND rho6 rho7 AV16); [apply E7; lia | apply E7; lia | exact RS7 | exact Z6]. }
  split.
  {
    assert (ZDBAND : forall r (r' : valuation), agree_vars 36 rho1 r -> rw r' 31%positive = rw r 31%positive -> rw r' 35%positive = rw r 35%positive ->
              rm_same_band r r' -> ZD11 r -> ZD11 r').
    { intros r r' AVr E31 E35 RS HZr a p Hp Ha H64 N1.
      assert (ET : TP11 r' = TP11 r) by (unfold TP11, q1Z, sbZ, priZ, pRI, shRI_base; cbn [eval]; rewrite E31, E35; reflexivity).
      rewrite ET in Hp. unfold priZ in N1. rewrite E31 in N1.
      rewrite (RS (Z_to_bv 64 a)).
      - exact (HZr a p Hp Ha H64 N1).
      - rewrite (TP11_agree rho1 r AVr) in Hp. pose proof (LOW2 p Hp). pose proof (LOWB2 p Hp). pose proof (urange p). rewrite u64_of_lit by lia. lia. }
    assert (ZD2 : ZD11 rho2).
    { intros a p Hp Ha H64 N1. unfold priZ in N1. rewrite !Hrw2 in N1.
      rewrite (TP11_agree rho1 rho2 AV2) in Hp. pose proof (urange p).
      rewrite (Hrm2 (Z_to_bv 64 a)) by (exists p; split; [exact Hp | rewrite u64_of_lit by lia; lia]). exact (HD1 a p Hp Ha H64 N1). }
    assert (ZD3 : ZD11 rho3) by (apply (ZD11_ext rho2 rho3); [apply E3; lia | apply E3; lia | intros a; symmetry; apply R3 | exact ZD2]).
    assert (AV13d : agree_vars 36 rho1 rho3) by (split; [intros i Hi; rewrite E3 by lia; apply Hrw2 | intros l; rewrite <- (L3 l); apply Hrl2]).
    assert (ZD4 : ZD11 rho4) by (apply (ZDBAND rho3 rho4 AV13d); [apply E4; lia | apply E4; lia | exact RS4 | exact ZD3]).
    assert (ZD5 : ZD11 rho5) by (apply (ZD11_ext rho4 rho5); [apply E5; lia | apply E5; lia | intros a; symmetry; apply R5 | exact ZD4]).
    assert (ZD6 : ZD11 rho6) by (apply (ZD11_ext rho5 rho6); [apply E6; lia | apply E6; lia | intros a; symmetry; apply R6 | exact ZD5]).
    assert (AV16d : agree_vars 36 rho1 rho6).
    { split; [intros i Hi; rewrite E6, E5, E4, E3 by lia; apply Hrw2 | intros l; rewrite <- (L6 l); cbn; rewrite <- (L5 l); cbn; rewrite L4, <- (L3 l); apply Hrl2]. }
    apply (ZDBAND rho6 rho7 AV16d); [apply E7; lia | apply E7; lia | exact RS7 | exact ZD6]. }
  split.
  {
    assert (E6lo : forall i, (i < 7)%positive -> rw rho6 i = rw rho i) by (intros i Hi; rewrite E6, E5, E4, E3 by lia; rewrite Hrw2; apply E1; lia).
    assert (E3lo : forall i, (i < 7)%positive -> rw rho3 i = rw rho i) by (intros i Hi; rewrite E3 by lia; rewrite Hrw2; apply E1; lia).
    eapply RMH_trans; [| exact E6lo | exact RM7].
    intros a Ha. pose proof (proj1 Ha) as HaLo.
    rewrite <- (R6 a). cbn [rho_set_rw rm]. rewrite <- (R5 a). cbn [rho_set_rw rm].
    rewrite (RM4 a) by (apply (proj2 (ARGF_ext rho rho3 a E3lo)); exact Ha).
    rewrite <- (R3 a). rewrite (HI2 a) by (unfold SHADOW_BAND_HI; clear -HaLo HX1; lia).
    rewrite <- (R1 a). reflexivity. }
  rewrite (TP12_agree rho6 rho7) by (eapply agree_vars_le; [|exact AV7]; lia). exact Hsp7.
Qed.

Hypothesis Hwit12 : ltac2:(tb__ "0|2|
S2S6Q40M0A1M1G1S53S5G0Z0A2VmE;S5G0Z1000A2R1A4La;A2").
Hypothesis Hwit13 : ltac2:(tb__ "0|4|
S6Q40M0A1M1S53S5G0Z0A2M2VmE;S5G0Z1000A2M3R1A4S2G1G1S53G2S39R3A1G3R1A4La;A2F_;Fb7;").
Hypothesis Hwit14 : ltac2:(tb__ "0|4|
S6Q40M0A1M1G1S53S5G0Z0A2M2VmE;S5G0Z1000A2M3R2A4S53G2S39R3A1G3R2A4S2G1G1S53G2S3fR5R4A2G3R1A4La;A2F_;F_;Fb8;Fb7;").

Lemma eseg12a : ltac2:(tb__ "0|4|
S8S3aR1A1S57S1dS43S1dS37VmE;S68VB;A1M0A2S8dR2S67R2A1A5S56S2S6Q40M1A1M2G2S0S53S5G1Z0A2VmE;S5G1Z1000M3A2R1A4S44S1dS37S39R1A1S1eG0G3A2A2P25S8cR4P24R1A3S67R4A1S49S59S5bS89S81A2S4dS59A1A3R2A7A2Lb7;A2Lw;A3F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 Hmaps Hres Htop Hlz Hwit12.
  clear Ha1 Ha2. intros rho HV. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1). pose proof mE_ledger as (M1 & M2 & M3 & M4 & M5).
  eapply etriple_seq.
  { apply (eager_rw_enode E_k12d 4096 mE (B12 B) G12 37%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear12.
    + rewrite M1. exact Hres.
    + exact init_sp_ok_mE.
    + exact band_mE.
    + rewrite M3. unfold B12, B11. lia.
    + exact Hwit12.
    + apply (HG11c rho _ HV). exists []. reflexivity.
    + rewrite M4. exact Hv1. }
  apply etriple_ex; intros b7. intros w [HPL7 Hsp]. revert w Hsp.
  assert (N : ss_next (ax_S E_k12d) = 36%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  change (etriple segsA (SPA segsA (KxA (m12 b7) (B12 B + 4096)) (eager_ok E_k12d 4096 37) (rho_set_rw rho (ss_next (ax_S E_k12d)) b7) (TP11 rho))
           (fun w => exists b0, mmap_place_ok_none (Z_to_bv 64 0) mE (Z_to_bv 64 4096) b0
              /\ LQA segsA (KxA (m12 b0) (B12 B + 4096)) 37 (rho_set_rw rho 36 b0) (TP11 rho) [mkLeafA L12r RsCut] w)).
  rewrite N. change (eager_ok E_k12d 4096 37) with S_s12ok.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b7; split; [exact HPL7|exact Hw] |].
  rewrite <- N. eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run12a].
Qed.

Theorem start5_sum_ex_A : ltac2:(tb__ "0|0|
S8S3aR1A1S6bR2A1S6cR3A1S57S1dS43S1dS37VmE;S68VB;A1A2S8dR4S67R4A1A5S3eR4A1A3F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 Ha1 Ha2 Hmaps Hna Hres Htop Hlz Hwit12 Hwit13 Hwit14.
  intros rho HV HZ HD. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  assert (HX1 : 0x7fff80000000 <= bv_unsigned (rw rho 1%positive) <= 0x800000000000) by (rewrite Hv1; unfold init_sp_ok, sp_window_lo, sp_window_hi in Htop; lia).
  eapply etriple_seq; [apply (eseg12a rho HV)|].
  apply etriple_ex; intros b7. apply etriple_pure; intros HPL7.
  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho1. apply etriple_pure; intros Hag1. pose proof Hag1 as (V1 & L1 & R1).
  assert (E1 : forall i, (i < 36)%positive -> rw rho1 i = rw rho i) by (intros i Hi; rewrite <- (V1 i) by lia; rewrite rho_set_rw_other by lia; reflexivity).
  assert (HV1 : vals12 rho1) by (eapply (vals12_agree 36%positive rho rho1); [lia | exact HV | exact E1]).
  assert (H36a : rw rho1 36%positive = b7) by (rewrite <- (V1 36%positive) by lia; apply rho_set_rw_at).
  assert (AV1 : agree_vars 36 rho rho1) by (split; [exact E1 | intros l; symmetry; apply L1]).
  assert (HZ1 : Z11 rho1) by (apply (Z11_ext rho rho1); [apply E1; lia | apply E1; lia | intros a; symmetry; apply R1 | exact HZ]).
  assert (HD1 : ZD11 rho1) by (apply (ZD11_ext rho rho1); [apply E1; lia | apply E1; lia | intros a; symmetry; apply R1 | exact HD]).
  rewrite <- (TP11_agree rho rho1 AV1).
  eapply etriple_conseq; [intros w Hw; exact (prep12 b7 HPL7 rho1 w HV1 H36a Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho2. apply etriple_pure; intros Hrw2. apply etriple_pure; intros Hrl2. apply etriple_pure; intros Hz2.
  apply etriple_pure; intros Hrm2. apply etriple_pure; intros HI2. apply etriple_pure; intros LOW2. apply etriple_pure; intros Q12K. apply etriple_pure; intros LOWB2.
  assert (HV2 : vals12 rho2) by (eapply (vals12_agree 36%positive rho1 rho2); [lia | exact HV1 | intros i Hi; apply Hrw2]).
  assert (H36b : rw rho2 36%positive = b7) by (rewrite Hrw2; exact H36a).
  assert (AV2 : agree_vars 36 rho1 rho2) by (split; [intros i Hi; apply Hrw2 | exact Hrl2]).
  rewrite <- (TP12_agree rho1 rho2 AV2).
  eapply etriple_seq; [apply (ecall12 b7 rho2 HV2 H36b)|].
  apply etriple_ex; intros rho3. apply etriple_pure; intros Hag3. pose proof Hag3 as (V3 & L3 & R3).
  assert (E3 : forall i, (i < 37)%positive -> rw rho3 i = rw rho2 i) by (intros i Hi; symmetry; apply V3; exact Hi).
  assert (AV3 : agree_vars 36 rho2 rho3) by (split; [intros i Hi; apply E3; lia | intros l; symmetry; apply L3]).
  rewrite <- (TP12_agree rho2 rho3 AV3).
  eapply etriple_seq; [apply (eseg12d b7 rho3)|].
  apply etriple_ex; intros rho4. apply etriple_pure; intros AV4. apply etriple_pure; intros RS4. apply etriple_pure; intros RM4.
  pose proof AV4 as [E4 L4].
  assert (HV4 : vals12 rho4) by (eapply (vals12_agree 37%positive rho2 rho4); [lia | exact HV2 | intros i Hi; rewrite E4 by lia; apply E3; lia]).
  assert (H36d : rw rho4 36%positive = b7) by (rewrite E4 by lia; rewrite E3 by lia; exact H36b).
  assert (AV4' : agree_vars 36 rho3 rho4) by (eapply agree_vars_le; [|exact AV4]; lia).
  rewrite <- (TP12_agree rho3 rho4 AV4').
  eapply etriple_seq; [apply (eseg13 b7 HPL7 (Hwit13 b7 HPL7) rho4 HV4 H36d)|].
  apply etriple_ex; intros b8. apply etriple_pure; intros HPL8.
  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho5. apply etriple_pure; intros Hag5. pose proof Hag5 as (V5 & L5 & R5).
  assert (E5 : forall i, (i < 77)%positive -> rw rho5 i = rw rho4 i) by (intros i Hi; rewrite <- (V5 i) by lia; rewrite rho_set_rw_other by lia; reflexivity).
  assert (HV5 : vals12 rho5) by (eapply (vals12_agree 77%positive rho4 rho5); [lia | exact HV4 | exact E5]).
  assert (H36e : rw rho5 36%positive = b7) by (rewrite E5 by lia; exact H36d).
  assert (H77e : rw rho5 77%positive = b8) by (rewrite <- (V5 77%positive) by lia; apply rho_set_rw_at).
  assert (AV5 : agree_vars 36 rho4 rho5) by (split; [intros i Hi; apply E5; lia | intros l; rewrite <- (L5 l); reflexivity]).
  rewrite <- (TP12_agree rho4 rho5 AV5).
  eapply etriple_seq; [apply (eseg14 b7 HPL7 b8 HPL8 (Hwit14 b7 b8 HPL7 HPL8) rho5 HV5 H36e H77e)|].
  apply etriple_ex; intros b9. apply etriple_pure; intros HPL9.
  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho6. apply etriple_pure; intros Hag6. pose proof Hag6 as (V6 & L6 & R6).
  assert (E6 : forall i, (i < 78)%positive -> rw rho6 i = rw rho5 i) by (intros i Hi; rewrite <- (V6 i) by lia; rewrite rho_set_rw_other by lia; reflexivity).
  assert (HV6 : vals12 rho6) by (eapply (vals12_agree 78%positive rho5 rho6); [lia | exact HV5 | exact E6]).
  assert (H36f : rw rho6 36%positive = b7) by (rewrite E6 by lia; exact H36e).
  assert (H77f : rw rho6 77%positive = b8) by (rewrite E6 by lia; exact H77e).
  assert (H78f : rw rho6 78%positive = b9) by (rewrite <- (V6 78%positive) by lia; apply rho_set_rw_at).
  assert (AV6 : agree_vars 36 rho5 rho6) by (split; [intros i Hi; apply E6; lia | intros l; rewrite <- (L6 l); reflexivity]).
  rewrite <- (TP12_agree rho5 rho6 AV6).
  eapply etriple_conseq; [intros w Hw; exact Hw | | apply (eseg15 b7 HPL7 b8 HPL8 b9 HPL9 rho6 HV6 H36f H77f H78f)].
  intros w (rho7 & AV7 & RS7 & RM7 & Hsp7). pose proof AV7 as [E7 L7].
  exists b7, b8, b9, rho7. split; [exact HPL7|]. split; [exact HPL8|]. split; [exact HPL9|].
  assert (CH : forall i, (i < 36)%positive -> rw rho7 i = rw rho i).
  { intros i Hi. rewrite E7 by lia. rewrite E6, E5, E4, E3 by lia. rewrite Hrw2. apply E1. exact Hi. }
  split.
  { split; [exact CH|]. intros l. rewrite L7, <- (L6 l). cbn. rewrite <- (L5 l). cbn. rewrite L4, <- (L3 l), Hrl2, <- (L1 l). reflexivity. }
  split; [rewrite E7 by lia; exact H36f|]. split; [rewrite E7 by lia; exact H77f|]. split; [rewrite E7 by lia; exact H78f|].
  assert (HX2 : 0x7fff80000000 <= bv_unsigned (rw rho2 1%positive) <= 0x800000000000) by (rewrite Hrw2, E1 by lia; exact HX1).
  split.
  { apply (stackshadow_zero_band_ext rho6 rho7); [apply E7; lia | rewrite E6, E5, E4, E3 by lia; exact HX2 | exact RS7 |].
    apply (stackshadow_zero_ext rho5 rho6); [apply E6; lia | intros a; symmetry; apply R6 |].
    apply (stackshadow_zero_ext rho4 rho5); [apply E5; lia | intros a; symmetry; apply R5 |].
    apply (stackshadow_zero_band_ext rho3 rho4); [apply E4; lia | rewrite E3 by lia; exact HX2 | exact RS4 |].
    apply (stackshadow_zero_ext rho2 rho3); [apply E3; lia | intros a; symmetry; apply R3 | exact Hz2]. }
  split.
  { assert (ZBAND : forall r (r' : valuation), agree_vars 36 rho1 r -> rw r' 31%positive = rw r 31%positive -> rw r' 35%positive = rw r 35%positive ->
              rm_same_band r r' -> Z11 r -> Z11 r').
    { intros r r' AVr E31 E35 RS HZr a p Hp Ha H64 N1 N2.
      assert (ET : TP11 r' = TP11 r) by (unfold TP11, q1Z, sbZ, priZ, pRI, shRI_base; cbn [eval]; rewrite E31, E35; reflexivity).
      rewrite ET in Hp. unfold priZ, sbZ in N1, N2. rewrite E31 in N1. rewrite E35 in N2.
      rewrite (RS (Z_to_bv 64 a)).
      - exact (HZr a p Hp Ha H64 N1 N2).
      - rewrite (TP11_agree rho1 r AVr) in Hp. pose proof (LOW2 p Hp). pose proof (LOWB2 p Hp). pose proof (urange p). rewrite u64_of_lit by lia. lia. }
    assert (Z2 : Z11 rho2).
    { intros a p Hp Ha H64 N1 N2. unfold priZ, sbZ in N1, N2. rewrite !Hrw2 in N1, N2.
      rewrite (TP11_agree rho1 rho2 AV2) in Hp. pose proof (urange p).
      rewrite (Hrm2 (Z_to_bv 64 a)) by (exists p; split; [exact Hp | rewrite u64_of_lit by lia; lia]). exact (HZ1 a p Hp Ha H64 N1 N2). }
    assert (Z3 : Z11 rho3) by (apply (Z11_ext rho2 rho3); [apply E3; lia | apply E3; lia | intros a; symmetry; apply R3 | exact Z2]).
    assert (AV13 : agree_vars 36 rho1 rho3) by (split; [intros i Hi; rewrite E3 by lia; apply Hrw2 | intros l; rewrite <- (L3 l); apply Hrl2]).
    assert (Z4 : Z11 rho4) by (apply (ZBAND rho3 rho4 AV13); [apply E4; lia | apply E4; lia | exact RS4 | exact Z3]).
    assert (Z5 : Z11 rho5) by (apply (Z11_ext rho4 rho5); [apply E5; lia | apply E5; lia | intros a; symmetry; apply R5 | exact Z4]).
    assert (Z6 : Z11 rho6) by (apply (Z11_ext rho5 rho6); [apply E6; lia | apply E6; lia | intros a; symmetry; apply R6 | exact Z5]).
    assert (AV16 : agree_vars 36 rho1 rho6).
    { split; [intros i Hi; rewrite E6, E5, E4, E3 by lia; apply Hrw2 | intros l; rewrite <- (L6 l); cbn; rewrite <- (L5 l); cbn; rewrite L4, <- (L3 l); apply Hrl2]. }
    apply (ZBAND rho6 rho7 AV16); [apply E7; lia | apply E7; lia | exact RS7 | exact Z6]. }
  split.
  {
    assert (ZDBAND : forall r (r' : valuation), agree_vars 36 rho1 r -> rw r' 31%positive = rw r 31%positive -> rw r' 35%positive = rw r 35%positive ->
              rm_same_band r r' -> ZD11 r -> ZD11 r').
    { intros r r' AVr E31 E35 RS HZr a p Hp Ha H64 N1.
      assert (ET : TP11 r' = TP11 r) by (unfold TP11, q1Z, sbZ, priZ, pRI, shRI_base; cbn [eval]; rewrite E31, E35; reflexivity).
      rewrite ET in Hp. unfold priZ in N1. rewrite E31 in N1.
      rewrite (RS (Z_to_bv 64 a)).
      - exact (HZr a p Hp Ha H64 N1).
      - rewrite (TP11_agree rho1 r AVr) in Hp. pose proof (LOW2 p Hp). pose proof (LOWB2 p Hp). pose proof (urange p). rewrite u64_of_lit by lia. lia. }
    assert (ZD2 : ZD11 rho2).
    { intros a p Hp Ha H64 N1. unfold priZ in N1. rewrite !Hrw2 in N1.
      rewrite (TP11_agree rho1 rho2 AV2) in Hp. pose proof (urange p).
      rewrite (Hrm2 (Z_to_bv 64 a)) by (exists p; split; [exact Hp | rewrite u64_of_lit by lia; lia]). exact (HD1 a p Hp Ha H64 N1). }
    assert (ZD3 : ZD11 rho3) by (apply (ZD11_ext rho2 rho3); [apply E3; lia | apply E3; lia | intros a; symmetry; apply R3 | exact ZD2]).
    assert (AV13d : agree_vars 36 rho1 rho3) by (split; [intros i Hi; rewrite E3 by lia; apply Hrw2 | intros l; rewrite <- (L3 l); apply Hrl2]).
    assert (ZD4 : ZD11 rho4) by (apply (ZDBAND rho3 rho4 AV13d); [apply E4; lia | apply E4; lia | exact RS4 | exact ZD3]).
    assert (ZD5 : ZD11 rho5) by (apply (ZD11_ext rho4 rho5); [apply E5; lia | apply E5; lia | intros a; symmetry; apply R5 | exact ZD4]).
    assert (ZD6 : ZD11 rho6) by (apply (ZD11_ext rho5 rho6); [apply E6; lia | apply E6; lia | intros a; symmetry; apply R6 | exact ZD5]).
    assert (AV16d : agree_vars 36 rho1 rho6).
    { split; [intros i Hi; rewrite E6, E5, E4, E3 by lia; apply Hrw2 | intros l; rewrite <- (L6 l); cbn; rewrite <- (L5 l); cbn; rewrite L4, <- (L3 l); apply Hrl2]. }
    apply (ZDBAND rho6 rho7 AV16d); [apply E7; lia | apply E7; lia | exact RS7 | exact ZD6]. }
  split.
  { assert (E6lo : forall i, (i < 7)%positive -> rw rho6 i = rw rho i) by (intros i Hi; rewrite E6, E5, E4, E3 by lia; rewrite Hrw2; apply E1; lia).
    assert (E3lo : forall i, (i < 7)%positive -> rw rho3 i = rw rho i) by (intros i Hi; rewrite E3 by lia; rewrite Hrw2; apply E1; lia).
    eapply RMH_trans; [| exact E6lo | exact RM7].
    intros a Ha. pose proof (proj1 Ha) as HaLo.
    rewrite <- (R6 a). cbn [rho_set_rw rm]. rewrite <- (R5 a). cbn [rho_set_rw rm].
    rewrite (RM4 a) by (apply (proj2 (ARGF_ext rho rho3 a E3lo)); exact Ha).
    rewrite <- (R3 a). rewrite (HI2 a) by (unfold SHADOW_BAND_HI; clear -HaLo HX1; lia).
    rewrite <- (R1 a). reflexivity. }
  rewrite (TP12_agree rho6 rho7) by (eapply agree_vars_le; [|exact AV7]; lia). exact Hsp7.
Qed.

End Seg5.
End Start5.

(* [comment removed for export] *)
Module Lib_builder_defs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "pair"; "prod"; "nat"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "cell"; "sv"; "SAlu"; "DUnknown"; "SPAlign"; "mkObj"; "SVar"; "SPBranch"; "sobj"; "ss_objs"; "mkSS"; "ob_base"; "ob_hi"; "ob_lo"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "vDp"; "two47"; "B32"; "KLG"; "spm"; "vUD"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "kb4"; "vAL"; "vc"; "vb"; "piece"; "vE"; "PHI4"; "c1"; "c4"; "vLINE"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "batom"; "ASv"; "bitem"; "BI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "vB"; "vL"; "pB"; "two26"; "vI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.RA.ReallocAddr"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_vec_reserve.

Definition vE : sv := Lib_scan_double.vE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition vb : sv := SVar 12.  Definition vc : sv := SVar 13.
Definition vERR : sv := SVar 53. Definition vND : sv := SVar 54. Definition vNC : sv := SVar 55. Definition vNK : sv := SVar 56.
Definition vLINE : sv := SVar 57. Definition vAL : sv := SVar 58.

Definition kb4 (k : sv) : sv := SMd M_MUL (SLit 4) k.
Definition cb4 (c : sv) : sv := SMd M_MUL c (SLit 4).

Definition c4 (o : Z) (v : sv) : cell := mkCell (SLit o) 4 v.
Definition c1 (o : Z) (v : sv) : cell := mkCell (SLit o) 1 v.
Definition piece (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
SeS2cS7Vlo;A1S7Vhi;A1Vcells;ScA5").
Definition P_alloc : sobj := ltac2:(tb__ "0|1|
S2dZ0M0Z8S0S9S20G0S2aA2S1S9A1A3A3").
Definition P_st (err : sv) : sobj := ltac2:(tb__ "0|1|
S2dZ60M0Z78S0S9S31G0Verr;A2S0S9S20Z68S32A2S0S9S30Z70S7Z1A1A2S1S9A1A3A3A3A3").
Definition V184 (d c k : sv) : sobj := ltac2:(tb__ "0|1|
S2dZb8M0Zd8S0S9S20G0Vd;A2S0S9S20Zc0Vc;A2S0S9S20Zc8Vk;A2S0S9S20Zd0S7Z4A1A2S1S9A1A3A3A3A3A3").

Definition O_al : sobj := ltac2:(tb__ "0|2|
SeS2aS7Z0M0A1M1S7Z30A1S0S9S20G0S7S40A1A2S0S9S20Z8S7S41A1A2S0S9S20Z10G1A2S0S9S20Z18S7S42A1A2S0S9S20Z20G1A2S0S9S20Z28S26A2S1S9A1A3A3A3A3A3A3ScA5").

Definition O_c0 (cur : sv) : sobj := ltac2:(tb__ "0|1|
SeS2bS7Z0M0A1S7Z8A1S0S9S20G0S3aVcur;A1A2S1S9A1A3ScA5").
Definition O_c8 : sobj := ltac2:(tb__ "0|1|
SeS2bS7Z8M0A1S7Z10A1S0S9S20G0S3aS2eA1A2S1S9A1A3ScA5").

Definition O_dat (d k : sv) : sobj := ltac2:(tb__ "0|0|
SeVd;S7Z0A1S29Vk;A1S1S9A1ScA5").

Definition vec4_facts (d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|3|
S0S6SdVdv;Z4A2S0S6S8Vd;SfP1eA1M0A2S0S6S8SbS27Vd;S29Vk;A1M1A3G0A2S0S6S8Vd;S7S22A1A2S0S6S8Vc;Vk;A2S0S6S8Vk;S7S23A1M2A2S0S6S8G1G2A2S1S6A1A3A3A3A3A3A3A3").

Definition builder_facts (DW : Z) : list sprop := ltac2:(tb__ "0|8|
S0S6SdPaM0Z5A2S0S6S8SfG0A1M1S7S22A1M2A2S0S6S8SbS27SfP1eA1M3S7VDW;A1A3G1A2S0S6S8G3SbS27S25Z80A1M4S21A3A2S0S6S8G3G4A2S0S6S10S28S7N1100A1S21A3S0S6S10S28S21S7S46S47Z2Z26A2A1A1A3S0S6SdPcZ4A2S0S6S8S7S44A1M5S2cA2S0S6S8SbS27S2cS7Z518A1A3G3A2S0S6S8S2cG2A2S0S6SdPdZ3M6A2S0S6S8G3S2bA2S0S6S8SbS27S2bS7Z10A1A3G2A2S0S6S8S2bG2A2S0S6SdP3aG6A2S0S6S8G5S2aA2S0S6S8SbS27S2aS7Z30A1A3G3A2S0S6S8S2aG2A2S0S6S8S3cS2eA2S0S6S8S2eS39A2S0S6S8S39S7S3bA1A2S0S6S8S38G2A2S0S6S8S7Z1A1S38A2S0S6S8SbS27S38S39A3G2A2S0S6S8S7Z7fff7f800000A1M7G3A2S0S6S8G3S7Z7fffff800000A1A2S0S6S8G7G1A2S1S6A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition PHI4 (w k : sv) : bitem := ltac2:(tb__ "0|2|
S37Z1Z0M0S0S3S33S34A2M1S2S33S34Z6S35S29Vw;A1A1A4S0G1S2S33S34N4S35S29Vk;A1A1A4S0G1S2S33S34Z20S35S7Z4A1A1A4S1G1A1A3A3A3G0A4").
Definition bd_cnt (c k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S36S2fVc;Vk;A2S0S36S24Vk;A1S1S36A1A3A3").
Definition tv_vec (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3SaSaA2M0S2SaSaVd;S29Vk;A1A4S1G0A1A3").

Definition havoc_reg (A : axst) (r : nat) : axst := ltac2:(tb__ "0|2|
S3dVA;A1S1fS3eVA;S13S1cR1A1S43S1dR1A1S0S3S4SaA2M0S2S4SaVr;SfS1bR1A1M1A1A4S1G0A1A3A2S19R1A1S18R1A1S1eR1A1S12R1A1S17R1A1S45G1A1S1aR1A1A9A2TS;").
Definition shape (A : axst) : ltac2:(tb__ "0|0|
S5S3S3SaSaA2SaA2A1") := ltac2:(tb__ "0|1|
S3fS11S3S3SaSaA2M0SaA2S11S2G0SaS2SaSaS14R1A1S16R1A1A4S15R1A1A4Lo;S12S3dVA;A1A1A4").
End Lib_builder_defs.

(* [comment removed for export] *)
Module Lib_arena_alloc_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "O_got"; "O_rtc"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "pair"; "prod"; "cons"; "nil"; "app"; "Some"; "option"; "None"; "fst"; "length"; "nat"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "valuation"; "SLit"; "sprop_eqb"; "SPUle"; "sv"; "SVar"; "SAlu"; "holds"; "ss_facts"; "ss_objs"; "SPBranch"; "ss_next"; "DUnknown"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BIc"; "KU"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "sub"; "mul"; "lt"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Stdlib.Lists.List"; "existsb"; "In"; "removelast"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "emeasA"; "AK0"; "JA"; "JLA"; "ejcertA"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc"; "vCAP"; "vHD"; "s_m"; "E_m"; "R_m"; "X_fit"; "nd0"; "vAR"; "vU"; "P_fail"; "P_ok"; "SZ"; "X_sret1"; "X_sret2"; "ndF"; "ndK"; "ndO"; "p_fit"; "vDp"; "Pre_aa"; "Pre_m"; "X_nofit1"; "X_open"; "X_sret"; "base_fit"; "cutsE"; "exitsE"; "ndS"; "sel_sret"; "spm"; "C_open"; "FUEL_aa"; "O_W"; "T_mnull"; "T_mok0"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_nohead"; "X_sret3"; "cutpcs_aa"; "fit_facts"; "ndMok"; "need_fit"; "nofit_fact"; "p_new"; "pad_fit"; "tv0"; "two40"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_arena_alloc_pf"; "P0_aa"; "objsN"; "ohN"; "ohF"; "otN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "J_alloc_pre"; "L_malloc_null"; "L_malloc_ok"; "Posts_malloc"; "Pre_malloc"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_arena_alloc_pf.Sum"; "Posts_aa"; "JL"; "basez"; "baseF"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXSplit"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA";
"ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "carve_stateA"; "e32"; "drop_lastA"; "open_stateA"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_arena_alloc_pf.Sum.X"; "openF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import AAAddr RA.ReallocAddr.

Lemma ejcertA_ok : ltac2:(tb__ "0|0|
S0SbS48S7S87S6aS74P64S64S65A7ScA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma C_open_eq : ltac2:(tb__ "0|0|
S0S4Sb7S61S4cA2S69A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S0S4Sb2S5fS4eS4dS4fS94S90S10S92A1S91A3A5S6cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S0S4Sb2S5fS4eS4dS4fS95S90S10S92A1S91A3A5S6dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_nofit2_eq : ltac2:(tb__ "0|0|
S0S4Sb1S60SfS19S78S23S5S60A1A1A3A2S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition ohF : sobj := Eval vm_compute in last (ss_objs (ax_S X_fit)) O_W.
Lemma objsF_eq : ltac2:(tb__ "0|1|
S0SaS1aA1S24S5S50A1A1M0S11S1aS3eS1aG0A2SfS1aS8dS10S1aA1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_fit3_eq : ltac2:(tb__ "0|0|
S0S4Sb1Sb4S50S5cS1cS56A1A3S11S19S75S23S5S50A1A1A3A2S6eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sret1_eq : ltac2:(tb__ "0|0|
S0S13S4A1SafS62SfSacSadS67A1SfSacSaeSbbS16S17S67A2U1A2S1cZ18A1A2S10SacA1A3A3A2S12S4S57A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition ohN : sobj := Eval vm_compute in nth (length (ss_objs (ax_S X_sret1)) - 2) (ss_objs (ax_S X_sret1)) O_W.
Definition otN : sobj := Eval vm_compute in nth (length (ss_objs (ax_S X_sret1)) - 1) (ss_objs (ax_S X_sret1)) O_W.
Definition objsN : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sret1))).
Lemma objsN_eq : ltac2:(tb__ "0|1|
S0SaS1aA1S24S5S57A1A1S11S1aS11S1aS8bSfS1aS8cS10S1aA1M0A3A3SfS1aS8eG0A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sret2_eq : ltac2:(tb__ "0|0|
S0S4Sb6S57S11S1aS8bSfS1aS8cS10S1aA1A3A3A2S58A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsN2_eq : ltac2:(tb__ "0|0|
S0SaS1aA1S24S5S58A1A1S11S1aS8bSfS1aS8cS10S1aA1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sret3_eq : ltac2:(tb__ "0|0|
S0S4Sb4S58S79S1cS56A1A3S73A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition bd_m2 : list bitem := ltac2:(tb__ "0|2|
SfS2fS30Z1M0Z0M1Zf0A3SfS2fS30G1G0S35S33S45Z160A2S36Z2S31A2A2A3S10S2fA1A3A3").

Definition P0_aa (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := True.

Section Sum.
Let HTOP : InitState.segs_top segs <= IMG_HI := HTOP_ok.
Variable AInv : ltac2:(tb__ "0|0|
Sb0S1bSaS3fQ40A1A1Sa2OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S9bS7VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S18SbaVCST;R1A2S1S32Z0R2A2S37R2Sb9A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S18SbaVXGL;R1A2S1S32Z0R2A2S37R2Sb9A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
SaSeSeS18S18A2S18A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 3 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S47VAInv;VCST;VXGL;VKc;S8aVFB;VFF;A2VFB;VFF;VBX;S42Vnd;Aa").
Definition Posts_aa : list (axst * jpostA) := ltac2:(tb__ "0|1|
SfSeS4S7eA2M0SdS4S7eS54Sa5S59A1A4SfG0SdS4S7eS55Sa5S5aA1A4S10G0A1A3A3").

Definition PD_aa : list (axst * ndesc) := ltac2:(tb__ "0|1|
SfSeS4S41A2M0SdS4S41S54S59A4SfG0SdS4S41S55S5aA4S10G0A1A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S46VAInv;VCST;VXGL;S87VKc;Vrho0;S8aVFB;VFF;A2VFB;VFF;VBX;S42Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
SeS4S41A2SbfFn;") := ltac2:(tb__ "0|0|
S49VAInv;VCST;VXGL;S87VKc;Vrho0;S8aVFB;VFF;A2VFB;VFF;VBX;S42Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S7fS7S87Vrho0;Vtp0;Sa4A5").

Definition baseF (F : list sprop) : Prop := ltac2:(tb__ "0|5|
S1S0SbS3cS19S1dS1eS20PaA1M0S1cS7dA1M1A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS20P1eA1M2S21S88S68Z40M3A1M4S5dA3A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eG2G4A2A1VF;A3ScA3S1S0SbS3cS19S1dS25S89S1cN1000A1S5dA3A1VF;A3ScA3S1S0SbS3cS19S1dS25S89S5dS1cS38S7cA1A1A3A1VF;A3ScA3S1S0SbS3cS19S1dS1eS1cZ1000A1S52A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS21S88S52S1cG3A1A3G2A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS52G1A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS4cG2A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eG2G0A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS1cZ7fff7f800000A1G2A2A1VF;A3ScA3S0SbS3cS19S1dS1eG2S1cZ7fffff800000A1A2A1VF;A3ScA3A2A2A2A2A2A2A2A2A2A2A2").
Record basez (rho : valuation) : Prop := BZ {
  bz_sp : bv_unsigned (rw rho V_TOP) + 64 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_win : forall a, fst (obj_range rho O_W) <= a < snd (obj_range rho O_W) -> bv_unsigned (rw rho V_TOP) <= a < uval rho (SVar 10) - 64;
  bz_ar : 4096 <= uval rho vAR /\ uval rho vAR + 64 <= bv_unsigned (rw rho V_TOP);
  bz_hd : uval rho vHD <= bv_unsigned (rw rho V_TOP);

  bz_top : 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
S1bS18S1S32Z0R1A2S32R1S2eR2S20PaA1M0A2A2A2S0S18S2eR3S68R2A1A2S35S2eR3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RA.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma basez_of : ltac2:(tb__ "0|0|
S1bSaS19A1Sa8S19S22R2A1R1A3Sa7R2A1Sa6R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & BT1 & BT2).
  pose proof (holds_mem _ _ _ HF BT1) as HT1. pose proof (holds_mem _ _ _ HF BT2) as HT2. zf HT1. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  pose proof (holds_mem _ _ _ HF B7) as H7. pose proof (holds_mem _ _ _ HF B8) as H8. pose proof (holds_mem _ _ _ HF B9) as H9.
  pose proof (holds_mem _ _ _ HF B10) as H10.
  zf H1. zf H2. zf H3. zf H6. zf H7. zf H8. zf H9. zf H10.
  apply (proj1 (holds_bge _ _ _)) in H4. apply (proj1 (holds_bge _ _ _)) in H5.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  unfold two47, RA.two47, two40, RA.two40 in *.
  rewrite !uval_lit in H1, H6, H8, HT1, HT2 by lia.
  change (uval rho (SLit (-4096))) with (bv_unsigned (eval rho (SLit (-4096)))) in H4. rewrite U_lit in H4. change ((-4096) mod M64v) with 18446744073709547520 in H4.
  change (uval rho (SLit (- 2 ^ 40))) with (bv_unsigned (eval rho (SLit (- 2 ^ 40)))) in H5. rewrite U_lit in H5.
  change ((- 2 ^ 40) mod M64v) with 18446742974197923840 in H5.
  rewrite uval_add_small in H7 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H7 by lia.
  rewrite uval_spm in H3 by lia.

  pose proof (uval_range rho vDp) as RD.
  destruct (Zsigned_spec (uval rho vDp)) as [[L1 E1]|[L1 E1]]; rewrite E1 in H4, H5;
    [destruct (Zsigned_spec 18446744073709547520) as [[? E2]|[? E2]]; rewrite E2 in H4; lia|].
  destruct (Zsigned_spec 18446744073709547520) as [[? E2]|[? E2]]; rewrite E2 in H4; [lia|].
  destruct (Zsigned_spec 18446742974197923840) as [[? E3]|[? E3]]; rewrite E3 in H5; [lia|].
  assert (EA : uval rho (SAlu ALU_ADD (spm 64) vDp) = uval rho (SVar 10) - 64 + (uval rho vDp - 2 ^ 64)).
  { unfold uval at 1. rewrite U_add. change (bv_unsigned (eval rho (spm 64))) with (uval rho (spm 64)). change (bv_unsigned (eval rho vDp)) with (uval rho vDp).
    rewrite uval_spm by lia. unfold M64v.
    replace (uval rho (SVar 10) - 64 + uval rho vDp) with ((uval rho (SVar 10) - 64 + (uval rho vDp - 2 ^ 64)) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite EA in H2.
  constructor; try lia.
  intros a Hr. unfold obj_range, obj_lo_of, obj_hi_of, O_W in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. change (bv_unsigned (eval rho (spm 64))) with (uval rho (spm 64)) in Hr. rewrite uval_spm in Hr by lia.
  unfold soff in Hr. rewrite bv_signed_U in Hr. change (bv_unsigned (eval rho vDp)) with (uval rho vDp) in Hr. rewrite E1 in Hr. lia.
Qed.

Lemma objs_ok_gen : ltac2:(tb__ "0|5|
S1bSaS1aA1Sa6R2A1S1aS3dS1aR1R3A3S2S1S0S1fS28R2A1M0S20PaA1A3S1S0S1fS2bR2A1M1S1cN40A1A3S1S0S1fS2aR2A1M2S1cZ0A1M3A3S0S2cS29R2A1S27A3M4A2A2A2S2S0S1aR2S6bA3S2S1S0S1fG0S52A3S1S0S1fG1G3A3S1S0S1fG2S1cZ40A1A3G4A2A2A2S2S0S1aR2S8A3S0S1aR2S9A3A2A2A2A2F_;Fo;S0S18Sc0Vrho0;A1S40Q40S2dR4S98A2A2A3Sb8VCST;Vrho0;VFB;VFF;R5S7bS10SeSeS1fS18A2S1fA2A1R4A8F_;F_;F_;Fobjs;Frho;").
Proof.
  intros rho objs BZ Hcls ET o a Ho Hr. destruct BZ as [Bsp Bwin Bar Bhd Btop].
  destruct (Hcls o Ho) as [(Hb & Hl & Hh & Hd)|[->|[(Hb & Hl & Hh & Hd)|[->| ->]]]].
  - left. left. destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi ob_dflt] in Hb, Hl, Hh, Hd. subst.
    apply range_lit' in Hr; [|lia|lia]. lia.
  - left. left. pose proof (Bwin a Hr). lia.
  - left. right; right; left. exists (uval rho vAR), 64. split.
    + apply In_FBx. right. exists (vAR, SLit 64). split; [left; reflexivity|]. split; [unfold tnz; cbn [fst]; unfold uval in Bar; lia|].
      unfold tvv. cbn [fst snd]. unfold uval. rewrite U_lit. reflexivity.
    + destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi ob_dflt] in Hb, Hl, Hh, Hd. subst. apply range_lit' in Hr; [|lia|lia]. lia.
  - right. unfold obj_range, obj_lo_of, obj_hi_of, O_got in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr. unfold GOT_LO, GOT_HI in Hr.
    rewrite lit_unsigned, !soff_lit_small in Hr by lia. unfold IMG_HI. change (0 mod 2 ^ 64) with 0 in Hr. lia.
  - right. unfold obj_range, obj_lo_of, obj_hi_of, O_rtc in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr. unfold RTC_LO, RTC_HI in Hr.
    rewrite lit_unsigned, !soff_lit_small in Hr by lia. unfold IMG_HI. change (0 mod 2 ^ 64) with 0 in Hr. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S18SaS3fQ40A1A1S83F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S3aS4S1bSaS3fQ40A1A1S83Sa8S19S22R3A1S23S5R4A1A1A3VTR;S39S7R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S83S83S83S84R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
S83S83S84S3R3R1A1A1Fw;VTR;R3R2A2F_;FQ;FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S3aS3aS4S4S9fSaS1aA1M0SaSeS4S7eA2M1A1SaSeS1fS1fA2M2A1S83S1bSaS3fQ40A1A1M3G2S3dG2R1R5A3S3dG2R2S6RbA1A3F_;Fr;S0S13G0A1S82RaR9R8A3S12G0R7A2A3S0SbS81RbRaR9R8Sa9G1S4S15S4S7eA2R7A4A5ScA3S1bG3VTR;S39S7RfRdR2R1A5S7fS7S26S5RdA1A1R2R1RaA5A2Ftp1;Frho1;SaSa3A1M4Sa1Sa2S3bS7R9R8R10SdG4SaaR3SabR2R1A2A4A5R13RaR9R4R2A4R13S9eS9dRbRfS8fR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S4S7eG4Sa1Sa2S1bG3G4Sa1Sa2S3dG1SdS4S7eRaR9A4R14A3S3bS7R12R11R19SdG4SaaR9SabR8R7A2A4A5R1cR13R12RaR8A4SbdS26S5R1aA1A1S9eS9dR14R18S8fR9R13RaA3A3R19A2R8A3S3bS7R9R8ReSdG4SaaR7SabR6R5A2A4A5ReS9eS9dR16R1aS8fRbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sc1R17S8fRcR16RdA3R1bR1cR1dR10R1eR19RbA9S1bSbeR18S8fRdR17ReA3R1cR1dS5R1eA1S5R1fA1S5R11A1R1RcA9VTR;S39S7S80R11S9eS9dR19R1dS8fReR18RfA3A3R1eA2R18RdRcA5Sc2R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S39S7R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CMALLOC : ltac2:(tb__ "0|1|
Sb0S1bSaS3fQ40A1A1VTR;S39S7S93VAInv;S10S92A1M0S91R3VKc;S20PcA1A6S97S90G0S91A3R2R1A5S7fS7S87R2R1S96S90VAInv;VCST;VXGL;G0S91R3VKc;A8A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S4S41SeS18S1fA2M0S1bSaS3fQ40A1A1M1S18G1S3dSeSeS4S41A2M2G0A2SdG2G0SdS4S41R7R6A4R5A4S64A3S1S32Z0S44SdG2G0SdS4S41R8R7A4R6A4R5A2M3A2S37G3R3A2A2VTR;S39S7VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S4S41S1bSaS3fQ40A1A1M0S18G0S3dSeS4S7eA2SdS4S7eR6Sa5R5A1A4Sa4A3VTR;S39S7VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.

Lemma X_X_open : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0S32S36Z5bS34Z2Z40A2A2R2A2VTR;S39S7VJAv;S51A1S61R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndO) C_open rho' tp w)).
  { intros w Hw.
    destruct (JA_open segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] CH vHD true X_open rho tp w) as (rho' & _ & Hw');
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Hw |].
    - intros Ai rho1 tp1 md1 HF _ HavS _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho HavS eq_refl) as ET. split.
      + apply objs_ok_gen; [eapply basez_of; [exact HF | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]| |exact ET].
        intros o Ho. cbn in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; auto 10.
      + intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Ha. rewrite uval_lit in Ha by lia.
        pose proof (basez_of rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as [_ _ [B1 B2] _ [BT1 BT2]]. unfold vAR in *. lia.
    - exists rho'. rewrite <- C_open_eq. exact Hw'. }
  apply TR_exw. intros rho'. apply (REENTER C_open ndO (90, z0)); [right; left; reflexivity | meas].
Qed.

Lemma X_X_nohead : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0S32S36Z51S34Z2Z40A2A2R2A2VTR;S39S7VJAv;S51A1S72R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_slow ndS (80, z0) (rho_sub rho s_nohead)); [do 2 right; left; reflexivity | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc X_nohead C_slow s_nohead (NDA tv0 [] (CH ++ E0) (AHead vHD false)) ndS);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  apply (JA_pot_out0 segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HBX); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Hw].
Qed.

Lemma X_P_fail : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0VTR;S39S7VJAv;S59A1S54R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. left. reflexivity. Qed.
Lemma X_P_ok : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0VTR;S39S7VJAv;S5aA1S55R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. right. left. reflexivity. Qed.

Lemma site_m : ltac2:(tb__ "0|1|
S1bSb3VAInv;VCST;VXGL;S87Vrho0;S8aVFB;VFF;A2VFB;VFF;S4eS4dS4fR1S66S14S18A1Sb0Sa1S1S1S32Z1S2eR3Sa0S4dPcA2A2M0A2S37G0S34Z2Z27A2A2A2S9cS10S92A1S91S9eS9dR3S4fR1A3S4dA2A3A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr nd_bd ndS] in HN, HD, HZ, HFR.
  split; [|split; [|split; [|exact I]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (fun _ => false) R_m None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros o a Ho Hb Hr. discriminate Hb.
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (ss_objs (ax_S E_m)) (fun _ => false) (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros r a Hr Hb Ha. discriminate Hb.
    + exact I.
  - change (wsub_get s_m 12) with (SLit 65568). rewrite uval_lit by lia. lia.
Qed.

Lemma X_E_m : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0S32S36Z42S34Z2Z40A2A2R2A2VTR;S39S7VJAv;S66A1S4eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (malloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_m s_m R_m rho tp ndS bd_m (FAM b tp0) CMALLOC).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply payA_of_bud_pay. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndS]. fold Pre_m. rewrite T_mnull_eq. apply (REENTER T_mnull ndM (65, z0)); [do 3 right; left; reflexivity | meas].
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndS]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok ndMok (65, z0)); [do 4 right; left; reflexivity | meas]].
    intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. apply (holds_mem _ _ _ HF). OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma and16_eq : and_hmask 18446744073709551600 = Some 16. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fit_arith : ltac2:(tb__ "0|9|
S1bS32S2eR1S4cA2Z7fffff800000A2S32S2eR2S53A2S2eR2S4bA2A2S32S2eR3S4bA2S35S34Z2Z28A2Z21A2A2S1S0S18S2eR4S63A2M0S33S33S2eR4S4cA2M1Z20M2A2S2eR4S53A2M3A2A3S1S1S32G0S2eR4S5cA2M4A2S32G4S33G0ZfM5A2M6A2A2S1S0S18S2eR4S7aA2M7S35G4G0A2A3S1S0S18S2eR4S77A2S33S33G3Z48M8A2G7A2A3S1S0S18S2eR4S21S88S63S1cG5A1A3A2G6A3S1S0S18S2eR4S21S88S5cS1cS56A1A3A2S33G4G8A2A3S0S18S2eR4S21S88S4cSb5S4bA1A3A2S33G1S33S2eR4S4bA2G2A2A2A3A2A2A2A2A2A2F_;F_;F_;Frho;").
Proof.
  intros rho Hh Hu Hc. unfold SZ.
  pose proof (uval_range rho vHD) as R1. pose proof (uval_range rho vU) as R2. pose proof (uval_range rho vCAP) as R3.
  assert (EB : uval rho base_fit = uval rho vHD + 32 + uval rho vU).
  { unfold base_fit. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (E15 : uval rho (SAlu ALU_ADD base_fit (SLit 15)) = uval rho base_fit + 15).
  { rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (EP : uval rho base_fit <= uval rho p_fit <= uval rho base_fit + 15).
  { assert (Ep : p_fit = SAlu ALU_AND (SAlu ALU_ADD base_fit (SLit 15)) (SLit 18446744073709551600)) by reflexivity. rewrite Ep.
    unfold uval at 2 3. rewrite (U_and_hmask rho _ _ 16 and16_eq). change (bv_unsigned (eval rho (SAlu ALU_ADD base_fit (SLit 15)))) with (uval rho (SAlu ALU_ADD base_fit (SLit 15))).
    rewrite E15. pose proof (Z.mod_pos_bound (uval rho base_fit + 15) 16 ltac:(lia)). lia. }
  assert (EPAD : uval rho pad_fit = uval rho p_fit - uval rho base_fit).
  { unfold pad_fit. unfold uval at 1. rewrite U_sub. change (bv_unsigned (eval rho p_fit)) with (uval rho p_fit). change (bv_unsigned (eval rho base_fit)) with (uval rho base_fit).
    unfold M64v. apply Z.mod_small. lia. }
  split; [exact EB|]. split; [exact EP|]. split; [exact EPAD|]. split; [|split; [exact E15|split]].
  - unfold need_fit, SZ.
    assert (E1 : uval rho (SAlu ALU_ADD pad_fit (SLit 72)) = uval rho pad_fit + 72) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite E1; lia). rewrite E1. lia.
  - unfold SZ. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
  - unfold e32. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
Qed.

Definition openF (F : list sprop) : Prop := ltac2:(tb__ "0|1|
S1S0SbS3cS19S1dS1eS4cS20P1eA1M0A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS53S4bA2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS4bS1cS35S34Z2Z28A2Z21A2A1A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS1cZ10000A1S4bA2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS21S88S4cSb5S4bA1A3G0A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS1cZ1000A1S4cA2A1VF;A3ScA3S0SbS3cS19S1dS1eG0S1cZ7fffff800000A1A2A1VF;A3ScA3A2A2A2A2A2A2").
Lemma openz : ltac2:(tb__ "0|4|
S1bSaS19A1Sa8S19S22R2A1R1A3SbcR2A1S1S32S2eR4S4cA2M0Z7fffff800000M1A2S1S32S2eR4S53A2S2eR4S4bA2M2A2S1S32G2S35S34Z2Z28A2Z21A2A2S1S32Z10000G2A2S1S32S33G0S33G2Z20A2A2S2eR4S20P1eA1A2M3A2S1S32Z1000G0A2S32G3G1A2A2A2A2A2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & BT).
  pose proof (holds_mem _ _ _ HF BT) as HT2. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  rewrite !uval_lit in H3, H4, H6, HT2 by lia.
  destruct (fit_arith rho ltac:(lia) H2 H3) as (_ & _ & _ & _ & _ & _ & E7). rewrite E7 in H5. lia.
Qed.

Lemma X_X_nofitO : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0VTR;S39S7VJAv;S5bA1S71R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_facts. intros HF. apply TR_false. intros w _.
  destruct (openz rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3) as (EB & EP & EPAD & _).
  assert (HO : existsb (sprop_eqb (SPBranch BC_LTU (SLit 18446744073709551543) pad_fit)) (ss_facts (ax_S X_nofitO)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (holds_mem _ _ _ HF HO) as H0. zf H0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in H0.
  rewrite uval_lit in H0 by lia. lia.
Qed.

Lemma X_X_nofit : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0S32S36Z51S34Z2Z40A2A2R2A2VTR;S39S7VJAv;S5bA1S6fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  destruct (openz rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3) as (EB & EP & EPAD & EN & _).
  assert (HN : existsb (sprop_eqb (SPNot (SPBranch BC_GEU vCAP need_fit))) (ss_facts (ax_S X_nofit)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (holds_mem _ _ _ HF HN) as H0. zf H0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in H0. rewrite EN in H0.

  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndS) C_slow rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (JA_close_np segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_open vHD vNX vCAP vU X_nofit
                  (removelast (ss_objs (ax_S X_nofit))) (O_hdr vHD vNX vCAP vU) rho tp tr ms md) as CL.
    specialize (CL ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(vm_compute; left; reflexivity) eq_refl Hw).
    set (rho1 := rho_absorb rho [O_hdr vHD vNX vCAP vU] (vms md tp ms)) in CL.
    assert (CL2 : SPA segs (JAv (NDA tv0 [] bd_open am_np)) X_nofit2 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_nofit2_eq. change (drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit)))) with X_nofit1 in CL.
      apply (SPA_refacts_JA segs _ rho1 X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1))); [exact CL | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
      intros tr' md' _ HF1. constructor; [|exact HF1].
      apply (proj2 (holds_ule _ _ _)). rewrite U_lit. change (65449 mod M64v) with 65449.
      assert (EU : eval rho1 vU = eval rho vU) by (unfold rho1; apply eval_absorb). rewrite EU. change (bv_unsigned (eval rho vU)) with (uval rho vU). lia. }
    exists (rho_sub rho1 s_nofit).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc X_nofit2 C_slow s_nofit (NDA tv0 [] bd_open am_np) ndS);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact CL2]. }
  apply TR_exw. intros rho'. apply (REENTER C_slow ndS (80, z0)); [do 2 right; left; reflexivity | meas].
Qed.

Lemma X_X_fit : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0VTR;S39S7VJAv;S5bA1S50R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_facts. intros HF.
  destruct (openz rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3) as (EB & EP & EPAD & EN & E15 & E72 & EHC).
  assert (HY : existsb (sprop_eqb (SPBranch BC_GEU vCAP need_fit)) (ss_facts (ax_S X_fit)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (holds_mem _ _ _ HF HY) as H0. zf H0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in H0. rewrite EN in H0.
  eapply TR_pre; [|apply (X_P_ok (rho_sub rho s_fit) tp b tp0)].
  intros w Hw.
  apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc X_fit3 P_ok s_fit (NDA tv0 [] bd_open (AOpen vHD vNX vCAP [(p_fit, SLit SZ)])) ndK);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  rewrite <- X_fit3_eq. apply (SPA_refacts_JA segs _ rho (carve_stateA X_fit p_fit (SLit SZ)) (fit_facts ++ ss_facts (ax_S X_fit))); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HNP tv0 [] bd_open vHD vNX vCAP p_fit (SLit SZ) X_fit rho tp w);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | | | exact Hw].
    + intros r HFr. destruct (openz r _ HFr ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
      destruct (fit_arith r Y1 Y2 Y3) as (EB' & EP' & EPAD' & EN' & _).
      pose proof (holds_mem _ _ _ HFr HY) as H1. zf H1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H1. rewrite EN' in H1.
      unfold SZ. rewrite uval_lit by lia. pose proof (uval_range r vU). lia.
    + intros Ai rho1 tp1 md1 HF' _ HavS _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho HavS eq_refl) as ET. split.
      * intros o a Ho Hr.
        rewrite objsF_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
        -- destruct (objs_ok_gen rho (removelast (ss_objs (ax_S X_fit))) (basez_of rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc))
                      ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; auto 10)
                      ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
        -- right; right. unfold ohF in Hr. apply range_lit' in Hr; [|lia|lia]. unfold vHD. lia.
      * intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Ha.
        -- assert (E32 : uval rho (e32 vCAP) = uval rho vCAP + 32)
             by (unfold e32; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
           change (SAlu ALU_ADD (SVar 102) (SLit 32)) with (e32 vCAP) in Ha. change (SVar 15) with vHD in Ha.
           rewrite E32 in Ha. pose proof (uval_range rho vHD). lia.
        -- rewrite uval_lit in Ha by lia. pose proof (basez_of rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as [_ _ [B1 B2] _ [BT1 BT2]]. unfold vAR in *. lia.
  - intros tr md _ HF2. apply Forall_app. split; [|exact HF2].
    unfold fit_facts. pose proof (uval_range rho vU). pose proof (uval_range rho vHD).
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
      rewrite ?E15, ?E72, ?EHC; rewrite ?uval_lit by lia; lia.
Qed.

Lemma X_X_sret : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0VTR;S39S7VJAv;S76A1S62R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_facts. intros HF.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndK) P_ok rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_sret X_sret1 tp _ X_sret1_eq Hw) as H1.
    pose proof (JA_push_open segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HBX HNP tv_m [] bd_m bd_m2 0 blkN vHD (SLit 65536) (SLit 72)
                  X_sret1 objsN ohN otN rho tp tr ms md objsN_eq eq_refl) as H2.
    specialize (H2 ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)
                   ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) H1).
    rewrite X_sret2_eq in H2. cbn [remove_nth fst blkN] in H2.
    set (rho1 := rho_absorb rho [otN] (vms md tp ms)) in H2.
    assert (HF1 : Forall (holds rho1) (ss_facts (ax_S X_sret2))) by exact (smatchA_facts segs _ _ _ _ (proj1 H2)).
    assert (H3 : SPA segs (JAv (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD (SLit 65536) [(p_new, SLit SZ)]))) X_sret3 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_sret3_eq.
      apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HNP tv0 [] bd_m2 (SVar pN) vHD (SLit 65536) p_new (SLit SZ) X_sret2 rho1 tp _);
        [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | | | exact H2].
      - intros r HFr.
        assert (HE : existsb (sprop_eqb (SPUle (SAlu ALU_ADD (SVar pN) (SLit 65568)) (SLit 140737479966720))) (ss_facts (ax_S X_sret2)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
        assert (HE' : existsb (sprop_eqb (SPUle (SVar pN) (SLit 140737479966720))) (ss_facts (ax_S X_sret2)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
        pose proof (holds_mem _ _ _ HFr HE) as HE1. zf HE1. pose proof (holds_mem _ _ _ HFr HE') as HE2. zf HE2.
        repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in HE1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in HE2.
        rewrite uval_lit in HE2 by lia.
        rewrite uval_add_small in HE1 by (rewrite uval_lit by lia; lia). rewrite !uval_lit in HE1 by lia.
        pose proof (uval_range r (SVar pN)) as RP. unfold p_new, SZ.
        rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite !uval_lit by lia. lia.
      - intros Ai rho2 tp2 md2 HF' _ HavS _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho1 HavS eq_refl) as ET. split.
        + intros o a Ho Hr. rewrite objsN2_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
          * destruct (objs_ok_gen rho1 objsN (basez_of rho1 _ HF' ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc))
                      ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; auto 10)
                      ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
          * right; right. unfold ohN in Hr. apply range_lit' in Hr; [|lia|lia].
            unfold pN. lia.
        + intros r a Hr Ha.
          assert (HX : In r [(SVar 12, SLit 64); (SVar pN, SLit 65568)]) by exact Hr. clear Hr.
          pose proof (basez_of rho1 _ HF' ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as [_ _ [B1 B2] _ [BT1 BT2]].
          destruct HX as [<-|[<-|[]]]; cbn [fst snd] in Ha.
          * rewrite uval_lit in Ha by lia. unfold vAR in *. lia.
          * assert (HE' : existsb (sprop_eqb (SPUle (SAlu ALU_ADD (SVar pN) (SLit 65568)) (SLit 140737479966720))) (ss_facts (ax_S X_sret2)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
            assert (HE'' : existsb (sprop_eqb (SPUle (SVar pN) (SLit 140737479966720))) (ss_facts (ax_S X_sret2)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
            pose proof (holds_mem _ _ _ HF1 HE') as HE1. zf HE1. pose proof (holds_mem _ _ _ HF1 HE'') as HE2. zf HE2.
            repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in HE1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in HE2.
            rewrite uval_lit in HE2 by lia.
            rewrite uval_add_small in HE1 by (rewrite uval_lit by lia; lia). rewrite !uval_lit in HE1 by lia.
            rewrite uval_lit in Ha by lia. pose proof (uval_range rho1 (SVar pN)). lia. }
    exists (rho_sub rho1 s_sret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc X_sret3 P_ok s_sret (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD (SLit 65536) [(p_new, SLit SZ)])) ndK);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact H3]. }
  apply TR_exw. intros rho'. apply X_P_ok.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S4S41SeS18S1fA2M0S1bSaS3fQ40A1A1M1G1S3dSeSeS4S41A2M2G0A2SdG2G0SdS4S41R6R5A4R4A4S65A3VTR;S39S7VJAv;R6A1R7R4R3A5VFAM;S44SdG2G0SdS4S41R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X_open. meas.
  - apply X_X_nohead. meas.
  - apply X_X_nofitO.
  - apply X_X_nofit. meas.
  - apply X_X_fit.
  - apply X_E_m. meas.
  - apply X_X_sret.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S4aS7VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S99S7S90VAInv;VCST;VXGL;A5").

Theorem arena_alloc_sum : ltac2:(tb__ "0|0|
SaS3fQ40A1A1S86S7Vok;S39S7S43VAInv;VCST;VXGL;VKc;S8aVFB;VFF;A2VFB;VFF;VBX;S42S51AaS5eVrho0;R1A5S7fS7S87Vrho0;R1Sa4A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc ALA FUEL_aa cutpcs_aa 100
                (map edropA cutsE) (map edropA exitsE) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertA_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0' & Hin). cbn in E0'. injection E0' as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_false segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok))
         with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_aa FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_aa P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S9aS7S90VAInv;VCST;VXGL;A5").

Theorem arena_alloc_sum_ex : ltac2:(tb__ "0|0|
SaS3fQ40A1A1S85S7S39S7S43VAInv;VCST;VXGL;VKc;S8aVFB;VFF;A2VFB;VFF;VBX;S42S51AaS5eVrho0;R1A5S7fS7S87Vrho0;R1Sa4A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc ALA FUEL_aa cutpcs_aa 100 cutsE exitsE (Q tp0) ejcertA_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_false segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_aa FB FF) FB FF BX PTrue rho0 tp0 nd Posts_aa P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_arena_alloc_pf.

(* [comment removed for export] *)
Module Lib_tess_polygon_cstates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "nil"; "prod"; "app"; "length"; "None"; "S"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "SAlu"; "sprop"; "SPUle"; "sobj"; "DUnknown"; "cell"; "mkObj"; "ss_objs"; "FcsrFrm0"; "mkSS"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ANone"; "NDA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates"; "ndF"; "z0"; "nd0"; "vext"; "E_sm0"; "Pre_f8"; "Pre_sf"; "v153"; "vfin"; "vnw"; "BAD"; "C_body0"; "C_fin"; "C_pro"; "C_pro2"; "C_s1"; "E_f8a"; "E_f8a0"; "E_f8b"; "E_f8b0"; "E_ms0"; "E_r2"; "E_r2_0"; "E_s00"; "E_s00_0"; "E_sc3"; "E_sc3_0"; "E_sc4"; "E_sc4_0"; "E_sfI"; "E_sfI0"; "E_sfK"; "E_sfK0"; "Pre_00"; "Pre_sm"; "T_r2"; "T_sc3"; "T_sc4"; "T_sfI"; "T_sfK"; "ilast"; "sel_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXSelect"; "AXSplit"; "AXRebase"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "ALU_ADD"; "ALU_SUB"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_states"; "vF"; "C_b6cI"; "C_b6cK"; "C_c84"; "FUEL_pg"; "K708"; "K830"; "Kaa4"; "Kb08"; "Kb14"; "Kb64"; "Kbbp"; "Kcm"; "Kd10"; "Kd60"; "Ke1"; "Ke2"; "Ke3"; "Kext"; "Kfin"; "Knw"; "Knw2"; "Kproj"; "Ktail"; "P_inv"; "P_ok"; "Pre_pg"; "X_pg"; "cutpcs_pg"; "n3x4"; "pNXT"; "pPRV"; "pRFX"; "pSCR"; "vFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_scale2d"; "Pre_sc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "SHB"; "leavesA_at"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.Lib_tess_run2d_states"; "Pre_r2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface Lib_tess_scale2d.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.Lib_tess_run2d_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessPolygonAddr.

Definition BAD : axst := ltac2:(tb__ "0|1|
S7eS16Z0S3SaA1M0G0S15S7SaA1S3S10A1S3SeA1P1S9A9S3S4SaSaA2A1A2").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leafP_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S56S18Vk;S7dS5bS73VS;Vpc;A4S2aA4").
Definition ilast (A : axst) : nat := ltac2:(tb__ "0|0|
S54S6S10S14S19VA;A1A1A2U1A2").

Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S5S2S55U0Vi;A2S5S2S55S8Vi;A1M0S54S6S10S14S19VA;A1A1A2G0A2A2S1S2Vi;S3S2A1A3A3A3").
Definition objs_butlast (A : axst) : list sobj := removelast (ss_objs (ax_S A)).

Definition Pre_sm : axst := Pre_stack_malloc AE_A 6.
Definition L_sm : axst := L_stack_malloc AE_A 6.
Definition Pre_f8 : axst := Pre_set_shadow AE_A 248.
Definition L_f8 : axst := L_set_shadow 248.
Definition Pre_00 : axst := Pre_set_shadow AE_A 0.
Definition L_00 : axst := L_set_shadow 0.
Definition Pre_sf : axst := Pre_stack_free AE_A 6.
Definition L_sf : axst := L_stack_free AE_A 6.

Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S1dS3S4SaSaA2A1S3S4S4SaS1eA2SaA2A1S3S7bA1S1cA4").
Definition ndF : ndesc := ltac2:(tb__ "0|2|
S1dS3S4SaSaA2A1S1S4S4SaS1eA2M0SaA2M1S0G0SaS0SaS1eS57Z6A4S79A4S3G1A1A3S3S7bA1S1cA4").
Definition X_pgF : list (sv * sv) := ltac2:(tb__ "0|0|
S1S4SaSaA2S0SaSaS57SbZ0A1A4S72A3").

Definition E_sm0 : axst := Eval vm_compute in leafP_at Pre_pg pg_sm 0.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S1S4S1fSaA2S0S1fSaPfScP13A1A4S50PaS19S24A1S19S42A1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Definition T_sm0 : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.

Definition T_sm1 : axst := Eval vm_compute in optAp (apply_axforms T_sm0 [AXSelect (sel_last T_sm0 3)]).
Definition C_pro0 : axst := Eval vm_compute in frame_open_stateA T_sm1 (objs_butlast T_sm1) X_pg 110 4096.
Definition C_pro : axst := ax_setX C_pro0 X_pgF.

Definition E_f8a0 : axst := Eval vm_compute in leafP_at C_pro pg_f8 0.
Definition O_dummy : sobj := ltac2:(tb__ "0|1|
S13SbZ0A1M0G0G0S3S12A1S11A5").
Definition shc_f8a : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S E_f8a0)) O_dummy).
Definition E_f8a1 : axst := Eval vm_compute in shadow_release_stateA E_f8a0 (objs_butlast E_f8a0) 110 [].

Definition E_f8a2 : axst := Eval vm_compute in shadow_reopen_stateA E_f8a1 X_pg gF 4 260.
Definition xf_shcall (A : axst) : list axform := ltac2:(tb__ "0|0|
S1S4aS4fS48VA;A1S83S7cZ4A2A2S3S4aA1A3").
Definition E_f8a : axst := Eval vm_compute in optAp (apply_axforms E_f8a2 (xf_shcall E_f8a2)).
Definition s_f8a : wsub := ltac2:(tb__ "0|0|
S1S4S1fSaA2S0S1fSaPfScP13A1A4S50PaS19S30A1S19S25A1A3A3").
Definition R_f8a : list sobj := Eval vm_compute in optR (entails_frA E_f8a Pre_f8 s_f8a).
Definition T_f8a0 : axst := Eval vm_compute in T_afterA Pre_f8 E_f8a s_f8a R_f8a L_f8.

Definition xf_shback (A : axst) : list axform := ltac2:(tb__ "0|1|
S1S4aS4eU1M0A1S1S4aS4cS49VA;G0A2A1S3S4aA1A3A3").
Definition T_f8a1 : axst := Eval vm_compute in optAp (apply_axforms T_f8a0 (xf_shback T_f8a0)).
Definition T_f8a2 : axst := Eval vm_compute in shadow_release_stateA T_f8a1 (objs_butlast T_f8a1) 110 [].
Definition C_pro2 : axst := Eval vm_compute in shadow_reopen_stateA T_f8a2 (ax_X T_f8a2) gF 260 276.

Definition E_ms0 : axst := Eval vm_compute in leafP_at C_pro2 pg_rel 0.
Definition shc_ms : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S E_ms0)) O_dummy).
Definition E_ms1 : axst := Eval vm_compute in shadow_release_stateA E_ms0 (objs_butlast E_ms0) 110 [].
Definition E_ms : axst := Eval vm_compute in optAp (apply_axforms E_ms1 [AXSplit 7 (SLit 16)]).
Definition C_body0 : axst := E_ms.

Definition E_s00_0 : axst := Eval vm_compute in leafP_at C_c84 pg_s00 0.
Definition E_s00_1 : axst := Eval vm_compute in shadow_reopen_stateA E_s00_0 (ax_X E_s00_0) gF 4 260.
Definition E_s00 : axst := Eval vm_compute in optAp (apply_axforms E_s00_1 (xf_shcall E_s00_1)).
Definition s_s00 : wsub := ltac2:(tb__ "0|0|
S1S4S1fSaA2S0S1fSaPfScP13A1A4S50PaS19S37A1S19S41A1A3A3").
Definition R_s00 : list sobj := Eval vm_compute in optR (entails_frA E_s00 Pre_00 s_s00).
Definition T_s00_0 : axst := Eval vm_compute in T_afterA Pre_00 E_s00 s_s00 R_s00 L_00.
Definition T_s00_1 : axst := Eval vm_compute in optAp (apply_axforms T_s00_0 (xf_shback T_s00_0)).
Definition C_s1 : axst := Eval vm_compute in shadow_release_stateA T_s00_1 (objs_butlast T_s00_1) 110 [].

Definition T_pure (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S80S17S19VCl;A1A1S81Vs;VPre;VL;VCl;VR;A5A2").
Definition reshapeA (A : axst) (i : nat) (o : sobj) : axst := ltac2:(tb__ "0|0|
S1aVA;S82S19VA;A1Vi;Vo;A3A2").

Definition O_pp2d_lit (k : Z) : sobj := ltac2:(tb__ "0|0|
S13S78SbZ0A1SdS51SbVk;A1SbZ4A1A3S3S12A1S11A5").

Definition xf_wback : list axform := ltac2:(tb__ "0|1|
S1S4aS4cS1S2U5S1S2U0M0S1S2U1S1S2U2S1S2U3S1S2U4S1S2U6S1S2U7S1S2U8S1S2U9S1S2UaS1S2UbS1S2UcS1S2UdS1S2UeS1S2UfS3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S1S4aS4bG0A1S3S4aA1A3A3").

Definition E_sc3_0 : axst := Eval vm_compute in leafP_at K830 pg_scale2d 0.
Definition E_sc3_1 : axst := Eval vm_compute in reshapeA E_sc3_0 7 (O_pp2d_lit 3).
Definition E_sc3 : axst := Eval vm_compute in optAp (apply_axforms E_sc3_1 [AXSplit 1 (SLit (-16))]).
Definition s_sc3 : wsub := ltac2:(tb__ "0|0|
S50PaS19S39A1S19S7aA1A3").
Definition R_sc3 : list sobj := Eval vm_compute in optR (entails_frA E_sc3 Pre_sc s_sc3).
Definition T_sc3_0 : axst := Eval vm_compute in T_pure Pre_sc E_sc3 s_sc3 R_sc3 P_sc.
Definition T_sc3_1 : axst := Eval vm_compute in reshapeA T_sc3_0 1 (O_pp2d []).
Definition T_sc3 : axst := Eval vm_compute in optAp (apply_axforms T_sc3_1 xf_wback).

Definition E_sc4_0 : axst := Eval vm_compute in leafP_at K708 pg_scale2d 0.
Definition E_sc4_1 : axst := Eval vm_compute in reshapeA E_sc4_0 7 (O_pp2d_lit 4).
Definition E_sc4 : axst := Eval vm_compute in optAp (apply_axforms E_sc4_1 [AXSplit 1 (SLit (-16))]).
Definition s_sc4 : wsub := ltac2:(tb__ "0|0|
S50PaS19S3bA1S19S7aA1A3").
Definition R_sc4 : list sobj := Eval vm_compute in optR (entails_frA E_sc4 Pre_sc s_sc4).
Definition T_sc4_0 : axst := Eval vm_compute in T_pure Pre_sc E_sc4 s_sc4 R_sc4 P_sc.
Definition T_sc4_1 : axst := Eval vm_compute in reshapeA T_sc4_0 1 (O_pp2d []).
Definition T_sc4 : axst := Eval vm_compute in optAp (apply_axforms T_sc4_1 xf_wback).

Definition E_r2_0 : axst := Eval vm_compute in leafP_at K708 pg_run2d 0.
Definition xf_r2call : list axform := ltac2:(tb__ "0|2|
S1S4aS4dU1M0SbNc0A1A2S1S4aS4dU0SbNf0M1A1A2S1S4aS4dG0SbNd0A1A2S1S4aS4fG0G1A2S3S4aA1A3A3A3A3").
Definition E_r2_1 : axst := Eval vm_compute in optAp (apply_axforms E_r2_0 xf_r2call).

Definition r2_ptr_facts : list sprop := ltac2:(tb__ "0|1|
S1SeSfS75SbZ800000000000A1M0A2S1SeSfS76G0A2S1SeSfS77G0A2S3SeA1A3A3A3").
Definition E_r2 : axst := ax_add_facts r2_ptr_facts E_r2_1.
Definition s_r2 : wsub := ltac2:(tb__ "0|0|
S50PaS19S35A1S19S7fA1A3").
Definition R_r2 : list sobj := Eval vm_compute in optR (entails_frA E_r2 Pre_r2 s_r2).
Definition T_r2_0 : axst := Eval vm_compute in T_pure Pre_r2 E_r2 s_r2 R_r2 P_ret.

Definition xf_r2back : list axform := ltac2:(tb__ "0|3|
S1S4aS4eU1M0A1S1S4aS4cS1S2U9S1S2G0S1S2UaS1S2UbS1S2U0M1S1S2U2S1S2U3S1S2U4S1S2U5S1S2U6S1S2U7S1S2U8S1S2UcS1S2UdS1S2UeS1S2UfS1S2U10S1S2U11S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S1S4aS4bG1A1M2S1S4aG2S1S4aS4bG0A1S3S4aA1A3A3A3A3A3").
Definition T_r2 : axst := Eval vm_compute in optAp (apply_axforms T_r2_0 xf_r2back).

Definition E_f8b0 : axst := Eval vm_compute in leafP_at Ktail pg_f8 0.
Definition E_f8b1 : axst := Eval vm_compute in shadow_reopen_stateA E_f8b0 (ax_X E_f8b0) gF 4 260.
Definition E_f8b : axst := Eval vm_compute in optAp (apply_axforms E_f8b1 (xf_shcall E_f8b1)).
Definition s_f8b : wsub := ltac2:(tb__ "0|0|
S1S4S1fSaA2S0S1fSaPfScP13A1A4S50PaS19S32A1S19S25A1A3A3").
Definition R_f8b : list sobj := Eval vm_compute in optR (entails_frA E_f8b Pre_f8 s_f8b).
Definition T_f8b0 : axst := Eval vm_compute in T_afterA Pre_f8 E_f8b s_f8b R_f8b L_f8.
Definition T_f8b1 : axst := Eval vm_compute in optAp (apply_axforms T_f8b0 (xf_shback T_f8b0)).
Definition C_fin : axst := Eval vm_compute in shadow_release_stateA T_f8b1 (objs_butlast T_f8b1) 110 [].

Definition E_sfI0 : axst := Eval vm_compute in leafP_at C_b6cI pg_sf 0.
Definition E_sfK0 : axst := Eval vm_compute in leafP_at C_b6cK pg_sf 0.

Definition E_sfI : axst := Eval vm_compute in flag_carve_stateA E_sfI0 120.
Definition E_sfK : axst := Eval vm_compute in flag_carve_stateA E_sfK0 120.
Definition s_sfI : wsub := ltac2:(tb__ "0|1|
S1S4S1fSaA2M0S0S1fSaP10ScP78A1A4S1G0S0S1fSaPfScP13A1A4S50PaS19S3dA1S19S26A1A3A3A3").
Definition s_sfK : wsub := ltac2:(tb__ "0|1|
S1S4S1fSaA2M0S0S1fSaP10ScP78A1A4S1G0S0S1fSaPfScP13A1A4S50PaS19S3fA1S19S26A1A3A3A3").
Definition R_sfI : list sobj := Eval vm_compute in optR (entails_frA E_sfI Pre_sf s_sfI).
Definition R_sfK : list sobj := Eval vm_compute in optR (entails_frA E_sfK Pre_sf s_sfK).

Definition T_sfI : axst := Eval vm_compute in T_afterA3 Pre_sf E_sfI s_sfI R_sfI L_sf X_pg.
Definition T_sfK : axst := Eval vm_compute in T_afterA3 Pre_sf E_sfK s_sfK R_sfK L_sf X_pg.

Definition z0 : sv := SLit 0.

Definition vfin : sv := ltac2:(tb__ "0|0|
SdS53S74ScP96A1A3").
Definition vnw (k : Z) : sv := ltac2:(tb__ "0|0|
SdS52SdS51ScP99A1SbZ1A1A3SbVk;A1A3").
Definition vext (k : Z) : sv := ltac2:(tb__ "0|0|
SdS52SdS51ScP99A1SbZ2A1A3SbVk;A1A3").
Definition v153 : sv := SVar 153.
Definition cutsE : list edescA := ltac2:(tb__ "0|c|
S1S4S4S18S1bA2M0S4S1eSaA2M1A2M2S0G0G1S0S18S1bS71S22A4S0S1eSaZ64S21A4A4S1G2S0G0G1S0S18S1bS2dS20A4S0S1eSaZ60S21A4A4S1G2S0G0G1S0S18S1bS2eS20A4S0S1eSaZ5eS21A4A4S1G2S0G0G1S0S18S1bS2bS20A4S0S1eSaZ5cS21A4A4S1G2S0G0G1S0S18S1bS6aS20A4S0S1eSaZ5aS28A4A4S1G2S0G0G1S0S18S1bS5aS20A4S0S1eSaZ58S21A4A4S1G2S0G0G1S0S18S1bS58S20A4S0S1eSaZ14S21A4M3A4S1G2S0G0G1S0S18S1bS2fS20A4S0S1eSaZ56S21A4A4S1G2S0G0G1S0S18S1bS63S20A4S0S1eSaZ54S28A4A4S1G2S0G0G1S0S18S1bS6bS20A4S0S1eSaZ52M4S29Z0M5A1A4A4S1G2S0G0G1S0S18S1bS6cS20A4S0S1eSaG4S29N1M6A1A4A4S1G2S0G0G1S0S18S1bS69S20A4S0S1eSaZ50M7S23G5A1A4A4S1G2S0G0G1S0S18S1bS66S20A4S0S1eSaG7S23G6A1A4A4S1G2S0G0G1S0S18S1bS67S20A4S0S1eSaG7S23N2A1A4A4S1G2S0G0G1S0S18S1bS68S20A4S0S1eSaG7S23N3A1A4A4S1G2S0G0G1S0S18S1bS6dS20A4S0S1eSaZ4eS27A4A4S1G2S0G0G1S0S18S1bS62S20A4S0S1eSaZ4cS27A4A4S1G2S0G0G1S0S18S1bS5cS20A4S0S1eSaZ46S21A4A4S1G2S0G0G1S0S18S1bS5dS20A4S0S1eSaZ44S21A4A4S1G2S0G0G1S0S18S1bS44S20A4S0S1eSaZ3cS21A4M8A4S1G2S0G0G1S0S18S1bS45S20A4G8A4S1G2S0G0G1S0S18S1bS43S20A4G8A4S1G2S0G0G1S0S18S1bS5eS20A4S0S1eSaZ3aS21A4A4S1G2S0G0G1S0S18S1bS5fS20A4S0S1eSaZ38S21A4A4S1G2S0G0G1S0S18S1bS60S20A4S0S1eSaZ36S21A4M9A4S1G2S0G0G1S0S18S1bS64S20A4G9A4S1G2S0G0G1S0S18S1bS61S20A4S0S1eSaZ34S21A4MaA4S1G2S0G0G1S0S18S1bS65S20A4GaA4S1G2S0G0G1S0S18S1bS6eS20A4S0S1eSaZ32S21A4A4S1G2S0G0G1S0S18S1bS2cS20A4S0S1eSaZ28S21A4A4S1G2S0G0G1S0S18S1bS59S20A4G3A4S1G2S0G0G1S0S18S1bS46S22A4S0S1eSaZaS21A4MbA4S1G2S0G0G1S0S18S1bS47S22A4GbA4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|6|
S1S4S4S18S1bA2M0S4S1eSaA2M1A2M2S0G0G1S0S18S1bS24S22A4S0S1eSaZ62S21A4A4S1G2S0G0G1S0S18S1bS31S20A4S0S1eSaZ5fS21A4A4S1G2S0G0G1S0S18S1bS34S20A4S0S1eSaZ5dS21A4A4S1G2S0G0G1S0S18S1bS38S20A4S0S1eSaZ57S21A4A4S1G2S0G0G1S0S18S1bS3aS20A4S0S1eSaZ42S21A4M3A4S1G2S0G0G1S0S18S1bS3cS20A4G3A4S1G2S0G0G1S0S18S1bS36S20A4G3A4S1G2S0G0G1S0S18S1bS33S20A4S0S1eSaZ2dS21A4A4S1G2S0G0G1S0S18S1bS3eS20A4S0S1eSaZfS21A4M4A4S1G2S0G0G1S0S18S1bS40S20A4G4A4S1G2S0G0G1S0S18S1bS6fS22A4S0S1eSaZ0S21A4M5A4S1G2S0G0G1S0S18S1bS70S22A4G5A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3").
End Lib_tess_polygon_cstates.

