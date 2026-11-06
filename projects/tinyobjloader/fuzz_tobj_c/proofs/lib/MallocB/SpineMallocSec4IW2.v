(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "leafA"; "ax_setS"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "true"; "list"; "app"; "option"; "prod"; "Some"; "pair"; "None"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "ss_next"; "reg_sv"; "SLit"; "SVar"; "ss_facts"; "valuation"; "SPBranch"; "ss_objs"; "swf"; "sprop_below"; "SPNot"; "rm"; "rw"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IW2.INST"; "CS3c"; "X3a3c"; "X3bc"; "U2c"; "L3bc"; "X3ac"; "CO3bc"; "G3c"; "L3ac"; "T4ac"; "T4bc"; "sLa"; "sLb"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "s4a0"; "s4a1"; "s4b0"; "s4b1"; "run3"; "run3a"; "run4a"; "run4b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IW2"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "genL"; "Bw"; "F_l2"; "F_g3"; "O_1"; "O_2"; "x11e3"; "O_blk"; "O_w"; "a0e3"; "carveS"; "@Stdlib.Lists.List"; "incl"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_NCH"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "SKEL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "KcA"; "Kc_ok"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4"; "slink4"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Definition U2c : axst := Eval vm_compute in (U2p D2c).
Lemma WU2_0 : ltac2:(tb__ "0|0|
S0SaS21S3S2bA1A1SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DU2_0 : ltac2:(tb__ "0|4|
S0SeSfScSfS16S16A2M0A1M1ScS17A1M2A2M3A1S69S3S43A1S3S2bA1A2S10G3S11G1G2S9G0A1S49A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXU2_0 : ltac2:(tb__ "0|0|
S0S15S19S3S2bA1A1S19S3S43A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HU2_0 : ltac2:(tb__ "0|0|
S0S4S7S43S3S2bA1A2S2bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run3 : option (list leafA) := Eval vm_compute in (runT2 U2c).
Lemma run3__runeq : ltac2:(tb__ "0|1|
S0ScSeScS6A1A1M0A1S56S41Ufa0S8S14Z706a0S8S14Z410f0S9S14A1A3A3S8S4S2bS9S4A1A3A4S8G0S3dS9G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run3]). Qed.
Definition X3ac : axst := Eval vm_compute in (leafS 0 run3).
Definition X3bc : axst := Eval vm_compute in (leafS 1 run3).
Lemma Cert3_0 : ltac2:(tb__ "0|1|
S0SaS54S41Ufa0S8S14Z706a0S8S14Z410f0S9S14A1A3A3VGS0;S8S4S2bS9S4A1M0A3S8S4S2dS8S4S2aG0A3A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [0x706a0; 0x410f0] GS0 [U2c] [X3ac; X3bc] [run3]); [exact run3__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Definition CS3c : axst := Eval vm_compute in (CS3a X3ac).
Lemma WC3_0 : ltac2:(tb__ "0|0|
S0SaS21S3S28A1A1SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DC3_0 : ltac2:(tb__ "0|4|
S0SeSfScSfS16S16A2M0A1M1ScS17A1M2A2M3A1S69S3S2dA1S3S28A1A2S10G3S11G1G2S8G0S11S16S16S4fS47A4S9G0A1A3S9S17A1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC3_0 : ltac2:(tb__ "0|0|
S0S15S19S3S28A1A1S19S3S2dA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC3_0 : ltac2:(tb__ "0|0|
S0S4S7S2dS3S28A1A2S28A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FX3a_0 : ltac2:(tb__ "0|0|
S51S17SdS17S8S17S1fS58S1cS61A1S1cS62A1A3S9S17A1A3S49A3S1dS3S2dA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IC3_0 : ltac2:(tb__ "0|0|
S0SeS59A1S79S41S26S3S28A1A1A2S10S59S5aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R17_0 : ltac2:(tb__ "0|0|
S0S16S1aS3S28A1Z11A2S1bZdeA1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R10_0 : ltac2:(tb__ "0|0|
S0S16S1aS3S28A1ZaA2S47A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma BBw_0 : ltac2:(tb__ "0|0|
S0SaS27S19S3S28A1A1S47A2SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R11_0 : ltac2:(tb__ "0|0|
S0S16S1aS3S28A1ZbA2S1bZ20000A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R12_0 : ltac2:(tb__ "0|0|
S0S16S1aS3S28A1ZcA2S1bZ3A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R13_0 : ltac2:(tb__ "0|0|
S0S16S1aS3S28A1ZdA2S1bZ32A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R14_0 : ltac2:(tb__ "0|0|
S0S16S1aS3S28A1ZeA2S1bZffffffffffffffffA1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R15_0 : ltac2:(tb__ "0|0|
S0S16S1aS3S28A1ZfA2S1bZ0A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC3_0 : ax_X CS3c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK3_0 : ltac2:(tb__ "0|2|
S0ScSfSfS16S16A2S16A2M0A1S53S18G0S57S20S3S28A1A1A4S53S18G0S57SdS18S8S18S4bS42A1S8S18S4aS42A1S9S18A1M1A3A3SdS18S68U2S42A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC3_0 : ltac2:(tb__ "0|0|
S51S17SdS17S6cVW;Vst;A2S6bS6aA1A3S1dS3S28A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FCS3_0 : ltac2:(tb__ "0|0|
S51S17SdS17S8S17S1fS58S1cS61A1S1cS62A1A3S9S17A1A3S49A3S1dS3S28A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXS3_0 : ltac2:(tb__ "0|0|
S0SaS80VGS0;S19S3S28A1A1A2SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition G3c : axst := Eval vm_compute in (G3a CS3c).
Lemma HG3_0 : ltac2:(tb__ "0|1|
S0S4S7S28S78S3S28A1M0S47SdS18S20G0A1S8S18S4dS9S18A1A3A3S19G0A1A4A2S2fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run3a : option (list leafA) := Eval vm_compute in (runT3a G3c).
Lemma run3a__runeq : ltac2:(tb__ "0|1|
S0ScSeScS6A1A1M0A1S56S41Ufa0S8S14Z410f0S9S14A1A3S8S4S2fS9S4A1A3A4S8G0S3eS9G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run3a]). Qed.
Definition X3a3c : axst := Eval vm_compute in (leafS 0 run3a).
Lemma Cert3a_0 : ltac2:(tb__ "0|1|
S0SaS54S41Ufa0S8S14Z410f0S9S14A1A3VGS0;S8S4S2fS9S4A1M0A3S8S4S29G0A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [0x410f0] GS0 [G3c] [X3a3c] [run3a]); [exact run3a__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Definition sLa : wsub := Eval vm_compute in (subL W st tmax X3a3c).
Definition L3ac : axst := Eval vm_compute in (L3 X3a3c).
Lemma ELa_0 : ltac2:(tb__ "0|0|
S0SaS5S29S46S29A1S33A3SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IDa_0 : ltac2:(tb__ "0|0|
S0SaS44S33VGS0;A2SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma GLa_0 : ltac2:(tb__ "0|0|
S0S16S45S33S19S3S29A1A1A2S4cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBLa_0 : ltac2:(tb__ "0|0|
S0SaS52S17S22S19S3S46S29A1A1A1A1S48S19S3S29A1A1A1A3SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HL3a_0 : ltac2:(tb__ "0|0|
S0S4S55S48S19S3S29A1A1A1S46S29A1A2S30A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sLb : wsub := Eval vm_compute in (subL W st tmax X3bc).
Definition L3bc : axst := Eval vm_compute in (L3 X3bc).
Lemma ELb_0 : ltac2:(tb__ "0|0|
S0SaS5S2aS46S2aA1S34A3SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IDb_0 : ltac2:(tb__ "0|0|
S0SaS44S34VGS0;A2SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma GLb_0 : ltac2:(tb__ "0|0|
S0S16S45S34S19S3S2aA1A1A2S4cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBLb_0 : ltac2:(tb__ "0|0|
S0SaS52S17S22S19S3S46S2aA1A1A1A1S48S19S3S2aA1A1A1A3SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HL3b_0 : ltac2:(tb__ "0|0|
S0S4S55S48S19S3S2aA1A1A1S46S2aA1A2S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition CO3bc : axst := Eval vm_compute in (carveS L3bc O_w).
Lemma HCOb_0 : ltac2:(tb__ "0|0|
S0S4S50S2cS4eA2S2eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCOb_0 : ltac2:(tb__ "0|0|
S0SaS21S3S2eA1A1SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XCb_0 : ax_X L3bc = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SKb_0 : ltac2:(tb__ "0|2|
S0ScSfSfS16S16A2S16A2M0A1S53S18G0S57S20S3S2cA1A1A4S53S18G0S57SdS18S8S18S4bS42A1S8S18S4aS42A1S9S18A1M1A3A3SdS18S68U2S42A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FCb_0 : ltac2:(tb__ "0|0|
S51S17SdS17S6cVW;Vst;A2S6bS6aA1A3S1dS3S2cA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FXb_0 : ltac2:(tb__ "0|0|
S51S17S8S17S23S1fS58S1cS61A1S1cS62A1A3A1S9S17A1A3S1dS3S2cA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run4a : option (list leafA) := Eval vm_compute in (runT4 L3ac).
Lemma run4a__runeq : ltac2:(tb__ "0|1|
S0ScSeScS6A1A1M0A1S56S41Ufa0S8S14Z3c614S9S14A1A3S8S4S30S9S4A1A3A4S8G0S3fS9G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run4a]). Qed.
Definition Y4a0c : axst := Eval vm_compute in (leafS 0 run4a).
Definition Y4a1c : axst := Eval vm_compute in (leafS 1 run4a).
Definition T4ac : axst := Eval vm_compute in (dropF Y4a0c).
Lemma Cert4a_0 : ltac2:(tb__ "0|1|
S0SaS54S41Ufa0S8S14Z3c614S9S14A1A3VGS0;S8S4S30S9S4A1M0A3S8S4S35S8S4S36G0A3A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [0x3c614] GS0 [L3ac] [Y4a0c; Y4a1c] [run4a]); [exact run4a__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition s4a0 : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y4a0c) (ax_S T4ac)).
Definition s4a1 : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y4a1c) (ax_S T4ac)).
Lemma E4a0_0 : ltac2:(tb__ "0|0|
S0SaS5S35S31S39A3SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma I4a0_0 : ltac2:(tb__ "0|0|
S0SaS44S39VGS0;A2SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E4a1_0 : ltac2:(tb__ "0|0|
S0SaS5S36S31S3aA3SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma I4a1_0 : ltac2:(tb__ "0|0|
S0SaS44S3aVGS0;A2SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run4b : option (list leafA) := Eval vm_compute in (runT4 CO3bc).
Lemma run4b__runeq : ltac2:(tb__ "0|1|
S0ScSeScS6A1A1M0A1S56S41Ufa0S8S14Z3c614S9S14A1A3S8S4S2eS9S4A1A3A4S8G0S40S9G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run4b]). Qed.
Definition Y4b0c : axst := Eval vm_compute in (leafS 0 run4b).
Definition Y4b1c : axst := Eval vm_compute in (leafS 1 run4b).
Definition T4bc : axst := Eval vm_compute in (dropF Y4b0c).
Lemma Cert4b_0 : ltac2:(tb__ "0|1|
S0SaS54S41Ufa0S8S14Z3c614S9S14A1A3VGS0;S8S4S2eS9S4A1M0A3S8S4S37S8S4S38G0A3A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [0x3c614] GS0 [CO3bc] [Y4b0c; Y4b1c] [run4b]); [exact run4b__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition s4b0 : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y4b0c) (ax_S T4bc)).
Definition s4b1 : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y4b1c) (ax_S T4bc)).
Lemma E4b0_0 : ltac2:(tb__ "0|0|
S0SaS5S37S32S3bA3SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma I4b0_0 : ltac2:(tb__ "0|0|
S0SaS44S3bVGS0;A2SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E4b1_0 : ltac2:(tb__ "0|0|
S0SaS5S38S32S3cA3SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma I4b1_0 : ltac2:(tb__ "0|0|
S0SaS44S3cVGS0;A2SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Theorem sec_g3_2h : ltac2:(tb__ "0|7|
S5dOF_;S63S6dS1eS75Q40M0A1M1S5cS7eVW;Vst;A2S6eR5A1S60S41R8S5fR6A1A3S7aS41R9S5fR7A1A3S70S6fS73S13S66S65R9A1A2A1Z1A2S74Z2Z14A2A2S76G0S25R8PcA2A2S14S76G0R8A2S14S7dR2A1S14S14S1S72S7bR3A1M2R1A2S70R1S6fG2S71R2Z8A2A2A2A2S2S0SeS75Q8A1M3A1S24RdS77G0R2A2A2S12G3A1A3A1F_;Fz;S1eS1eScG1A1M4S7fS64R11A1R6R5RfR3A5S5bS41R13S5eS41S67U2M5Vst;S42S63S7cR1A1LX;R12R11R4RfA8S31R3R2A5ReA4F_;FtY;FrY;Frho'';S1eG4S5bS41R12S5eS41S67G5Vst;S42S63R1LX;M6R11R10RfReA8S32R2R1A5RdA4FtY;FrY;S1eG4S5bS41R13S5eS41S67G5Vst;S42G6R12R11R10RfA8S43R2R1A5ReA4FtX;FrX;F_;F_;F_;TL;Tua;Tnv;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HUS HKc Hokl Hokpl Hok nv ua L RUNDEF HCa HCb rX tX.
  exact (sec_g3 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           D2c U2c X3ac X3bc CS3c G3c X3a3c L3ac L3bc CO3bc T4ac T4bc Y4a0c Y4a1c Y4b0c Y4b1c sLa sLb s4a0 s4a1 s4b0 s4b1
           WU2_0 DU2_0 NXU2_0 HU2_0 Cert3_0
           WC3_0 DC3_0 NXC3_0 HC3_0 FX3a_0 IC3_0 R17_0 R10_0 BBw_0 R11_0 R12_0 R13_0 R14_0 R15_0 XC3_0 SK3_0 FC3_0 FCS3_0 NXS3_0 HG3_0 Cert3a_0
           ELa_0 IDa_0 GLa_0 FBLa_0 HL3a_0 ELb_0 IDb_0 GLb_0 FBLb_0 HL3b_0
           HCOb_0 WCOb_0 XCb_0 SKb_0 FCb_0 FXb_0
           Cert4a_0 E4a0_0 I4a0_0 E4a1_0 I4a1_0 Cert4b_0 E4b0_0 I4b0_0 E4b1_0 I4b1_0
           ok A Kc rho a Q ltac:(intros E; discriminate E) HUS HKc Hokl Hokpl Hok RUNDEF HCa HCb rX tX).
Qed.
End INST.
