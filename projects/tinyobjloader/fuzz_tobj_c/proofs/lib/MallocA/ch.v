(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.

(* [comment removed for export] *)
Module SpineMallocSec5JE.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_next"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "list"; "true"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I"; "nx0"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU"; "DPENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I"; "U4ac"; "U4bc"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "@Stdlib.Lists.List"; "In"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4I"; "T4ac"; "T4bc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineMallocSec5J OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSecE2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineMallocSecE3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.
Lemma NXE5a_0 : ltac2:(tb__ "0|0|
S2S9S2eVGS0;S6S1fS27A1A1A2SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert5a_0 : ltac2:(tb__ "0|3|
S2S9S10S1Ufa0S7S0S20S8S0A1A3VGS0;S7SeSfS27Z1S4Z0M0A1M1A3S8SeA1M2A3S7SeSfS2bG0G1A3G2A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [DPENT] GS0 [mkVNA U4ac 1 (SLit 0)] [mkVNA X5ac 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I.run5a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I.run5a__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g41_0ha : ltac2:(tb__ "0|6|
S19S15S3S1eQ40M0A1M1S12OF_;S2S18Vst;S17A3S2SaS14A1VW;S8S14A1A3F_;S26VW;Vst;A2S16R6A1S1aS3S3SaG1A1M2SdS0S0A2M3S2dG3R1S24R5A1A3S23R2ScS0S0S1dG0RbA2S25S1dG0S5RcPcA2A2A1A4A2F_;Fbn;S22R5RbR4A3S11S1S13S1S1bU0M4Vst;S1cS21S19S2fR1A1LX;M5R6A2ReRdR5RbA8S29R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S3G2S11S1S13S1S1bG4Vst;S1cG5RbRaR9R8A8S30R2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc HCONT.
  eapply esec_g41 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := (fun X : AA => bumpP X)) (T4 := T4ac) (U4 := U4ac) (X5 := X5ac) (C5 := C5ac)
    (WU4 := WU4a_0) (DU4 := DU4a_0) (NXU4 := NXU4a_0) (HU4 := HU4a_0) (Cert5 := Cert5a_0)
    (NXE5 := NXE5a_0) (ECert5 := ECert5a_0) (HDSE := depot_call_SE_0ha);
    [exact HW | exact HUS | exact HKc | exact HCONT].
Qed.
Lemma NXE5b_0 : ltac2:(tb__ "0|0|
S2S9S2eVGS0;S6S1fS28A1A1A2SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert5b_0 : ltac2:(tb__ "0|3|
S2S9S10S1Ufa0S7S0S20S8S0A1A3VGS0;S7SeSfS28Z1S4Z0M0A1M1A3S8SeA1M2A3S7SeSfS2cG0G1A3G2A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [DPENT] GS0 [mkVNA U4bc 1 (SLit 0)] [mkVNA X5bc 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I.run5b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I.run5b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g41_0hb : ltac2:(tb__ "0|6|
S19S15S3S1eQ40M0A1M1S12OF_;S2S18Vst;S17A3S2SaS14A1VW;S8S14A1A3F_;S26VW;Vst;A2S16R6A1S1aS3S3SaG1A1M2SdS0S0A2M3S2dG3R1S24R5A1A3S23R2ScS0S0S1dG0RbA2S25S1dG0S5RcPcA2A2A1A4A2F_;Fbn;S22R5RbR4A3S11S1S13S1S1bU0M4Vst;S1cS21S19R1LX;M5R6A2ReRdR5RbA8S2aR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S3G2S11S1S13S1S1bG4Vst;S1cG5RbRaR9R8A8S31R2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc HCONT.
  eapply esec_g41 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := (fun X : AA => X)) (T4 := T4bc) (U4 := U4bc) (X5 := X5bc) (C5 := C5bc)
    (WU4 := WU4b_0) (DU4 := DU4b_0) (NXU4 := NXU4b_0) (HU4 := HU4b_0) (Cert5 := Cert5b_0)
    (NXE5 := NXE5b_0) (ECert5 := ECert5b_0) (HDSE := depot_call_SE_0hb);
    [exact HW | exact HUS | exact HKc | exact HCONT].
Qed.
End INST.
End SpineMallocSec5JE.

(* [comment removed for export] *)
Module CDepotCallI.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.CDepotCallM"; "T4_i"; "nobj_i"; "s4_i"; "R4_i"; "sd_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_stopJ"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "list"; "nat"; "prod"; "cons"; "Some"; "option"; "pair"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "ss_facts"; "sstate"; "ss_next"; "SVar"; "sobj"; "ss_objs"; "SPUle"; "sprop_below"; "SAlu"; "rw"; "valuation"; "SExt"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.CDepotCallW"; "isSome"; "X4"; "omrg"; "X4r"; "permW"; "T4d"; "oreb"; "T40"; "T4a"; "T4b"; "T4c"; "T4m1"; "T4m2"; "T4m3"; "X4a"; "X4b"; "X4c"; "X4f"; "F_call"; "in_famb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E4d"; "C5"; "F_gen"; "V_CNT"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.CDepotCallI.INST"; "pm__15"; "pm__16"; "pm__10"; "pm__11"; "pm__12"; "pm__13"; "pm__14"; "pm__17"; "pm__18"; "pm__19"; "pm__20"; "pm__21"; "pm__22"; "pm__23"; "pm__24"; "pm__9"; "pm__0"; "pm__1"; "pm__2"; "pm__25"; "pm__26"; "pm__3"; "pm__4"; "pm__5"; "pm__6"; "pm__7"; "pm__8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "coveredb"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.CDepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.CDepotCallM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let st : ustop := UStopLe. Let tmax : Z := 2.
Ltac memo_rw t M := lazymatch goal with |- context [t] => pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta | _ => fail "memo_rw: stage term not found" t end.
Ltac vmc := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NXE_i : ltac2:(tb__ "0|0|
S0S15S7eS6fS26S3S45S10U0A1Vst;Vtmax;A3A1A1A2S16A3").
Proof.  memo_rw (E4d (Wcan 0) st tmax) mE. vmc. Qed.
Lemma FBE_i : ltac2:(tb__ "0|0|
S0S15S49S22S2bS26S3S45S10U0A1Vst;Vtmax;A3A1A1A1S43A3S16A3").
Proof.  memo_rw (E4d (Wcan 0) st tmax) mE. vmc. Qed.
Lemma XE4_i : ltac2:(tb__ "0|1|
S0S18S1aS21S21A2M0A1S5S45S10U0A1Vst;Vtmax;A3A1S17G0A1A3").
Proof.  memo_rw (E4d (Wcan 0) st tmax) mE. vmc. Qed.
Lemma F192_i : ltac2:(tb__ "0|1|
S4aS22S1bS22S2aS23Z1A1S27Pc0A1M0A2S1bS22S2aG0S23Vtmax;A1A2S17S22A1A3A3S24S3S45S10U0A1Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E4d (Wcan 0) st tmax) mE. vmc. Qed.
Lemma FDEP_i : ltac2:(tb__ "0|0|
S4aS22S12S11A1S24S3S45S10U0A1Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E4d (Wcan 0) st tmax) mE. vmc. Qed.
Lemma FUNW_i : ltac2:(tb__ "0|1|
S4aS22S13S10U0A1M0Vst;A2S24S3S45G0Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E4d (Wcan 0) st tmax) mE. vmc. Qed.
Lemma FGEN4_i : ltac2:(tb__ "0|0|
S4aS22S47S24S3S45S10U0A1Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E4d (Wcan 0) st tmax) mE. vmc. Qed.
Lemma YP4_i : ltac2:(tb__ "0|0|
S4bS22S2aS23Z1A1S27S48A1A2S24S3S45S10U0A1Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E4d (Wcan 0) st tmax) mE. vmc. Qed.

Ltac PM_sub0 t := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSP.CallocMemoSP_subst t.
Ltac PM_all0 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSP.CallocMemoSP_all.
Definition pm__0 : axst := ltac:(let t := eval cbv delta [X4f] in (X4f 0%nat UStopLe 2) in let t := eval cbv beta zeta in t in let t := PM_sub0 t in exact t).
Lemma pm__0_eq : ltac2:(tb__ "0|0|
S0S4S42U0SfZ2A3S64A3"). Proof. cbv delta [X4f pm__0]; cbv beta zeta. PM_all0. reflexivity. Qed.
Ltac PM_sub1 t := let t := lazymatch (eval pattern (X4f 0%nat UStopLe 2) in t) with ?P _ => eval cbv beta in (P pm__0) end in PM_sub0 t.
Ltac PM_all1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__0_eq; PM_all0.
Definition pm__1 : axst := ltac:(let t := eval cbv delta [X4r] in (X4r 0%nat UStopLe 2 1) in let t := eval cbv beta zeta in t in let t := PM_sub1 t in exact t).
Lemma pm__1_eq : ltac2:(tb__ "0|0|
S0S4S34U0SfZ2Z1A4S65A3"). Proof. cbv delta [X4r pm__1]; cbv beta zeta. PM_all1. reflexivity. Qed.
Ltac PM_sub2 t := let t := lazymatch (eval pattern (X4r 0%nat UStopLe 2 1) in t) with ?P _ => eval cbv beta in (P pm__1) end in PM_sub1 t.
Ltac PM_all2 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__1_eq; PM_all1.
Definition pm__2 : axst := ltac:(let t := eval cbv delta [X4r] in (X4r 0%nat UStopLe 2 2) in let t := eval cbv beta zeta in t in let t := PM_sub2 t in exact t).
Lemma pm__2_eq : ltac2:(tb__ "0|1|
S0S4S34U0SfZ2M0G0A4S66A3"). Proof. cbv delta [X4r pm__2]; cbv beta zeta. PM_all2. reflexivity. Qed.
Ltac PM_sub3 t := let t := lazymatch (eval pattern (X4r 0%nat UStopLe 2 2) in t) with ?P _ => eval cbv beta in (P pm__2) end in PM_sub2 t.
Ltac PM_all3 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__2_eq; PM_all2.
Definition pm__3 : axst := ltac:(let t := eval cbv delta [X4a] in (X4a 0%nat UStopLe 2 1) in let t := eval cbv beta zeta in t in let t := PM_sub3 t in exact t).
Lemma pm__3_eq : ltac2:(tb__ "0|0|
S0S4S3fU0SfZ2Z1A4S69A3"). Proof. cbv delta [X4a pm__3]; cbv beta zeta. PM_all3. reflexivity. Qed.
Ltac PM_sub4 t := let t := lazymatch (eval pattern (X4a 0%nat UStopLe 2 1) in t) with ?P _ => eval cbv beta in (P pm__3) end in PM_sub3 t.
Ltac PM_all4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__3_eq; PM_all3.
Definition pm__4 : axst := ltac:(let t := eval cbv delta [X4a] in (X4a 0%nat UStopLe 2 2) in let t := eval cbv beta zeta in t in let t := PM_sub4 t in exact t).
Lemma pm__4_eq : ltac2:(tb__ "0|1|
S0S4S3fU0SfZ2M0G0A4S6aA3"). Proof. cbv delta [X4a pm__4]; cbv beta zeta. PM_all4. reflexivity. Qed.
Ltac PM_sub5 t := let t := lazymatch (eval pattern (X4a 0%nat UStopLe 2 2) in t) with ?P _ => eval cbv beta in (P pm__4) end in PM_sub4 t.
Ltac PM_all5 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__4_eq; PM_all4.
Definition pm__5 : axst := ltac:(let t := eval cbv delta [X4b] in (X4b 0%nat UStopLe 2 1) in let t := eval cbv beta zeta in t in let t := PM_sub5 t in exact t).
Lemma pm__5_eq : ltac2:(tb__ "0|0|
S0S4S40U0SfZ2Z1A4S6bA3"). Proof. cbv delta [X4b pm__5]; cbv beta zeta. PM_all5. reflexivity. Qed.
Ltac PM_sub6 t := let t := lazymatch (eval pattern (X4b 0%nat UStopLe 2 1) in t) with ?P _ => eval cbv beta in (P pm__5) end in PM_sub5 t.
Ltac PM_all6 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__5_eq; PM_all5.
Definition pm__6 : axst := ltac:(let t := eval cbv delta [X4b] in (X4b 0%nat UStopLe 2 2) in let t := eval cbv beta zeta in t in let t := PM_sub6 t in exact t).
Lemma pm__6_eq : ltac2:(tb__ "0|1|
S0S4S40U0SfZ2M0G0A4S6cA3"). Proof. cbv delta [X4b pm__6]; cbv beta zeta. PM_all6. reflexivity. Qed.
Ltac PM_sub7 t := let t := lazymatch (eval pattern (X4b 0%nat UStopLe 2 2) in t) with ?P _ => eval cbv beta in (P pm__6) end in PM_sub6 t.
Ltac PM_all7 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__6_eq; PM_all6.
Definition pm__7 : axst := ltac:(let t := eval cbv delta [X4c] in (X4c 0%nat UStopLe 2 1) in let t := eval cbv beta zeta in t in let t := PM_sub7 t in exact t).
Lemma pm__7_eq : ltac2:(tb__ "0|0|
S0S4S41U0SfZ2Z1A4S6dA3"). Proof. cbv delta [X4c pm__7]; cbv beta zeta. PM_all7. reflexivity. Qed.
Ltac PM_sub8 t := let t := lazymatch (eval pattern (X4c 0%nat UStopLe 2 1) in t) with ?P _ => eval cbv beta in (P pm__7) end in PM_sub7 t.
Ltac PM_all8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__7_eq; PM_all7.
Definition pm__8 : axst := ltac:(let t := eval cbv delta [X4c] in (X4c 0%nat UStopLe 2 2) in let t := eval cbv beta zeta in t in let t := PM_sub8 t in exact t).
Lemma pm__8_eq : ltac2:(tb__ "0|1|
S0S4S41U0SfZ2M0G0A4S6eA3"). Proof. cbv delta [X4c pm__8]; cbv beta zeta. PM_all8. reflexivity. Qed.
Ltac PM_sub9 t := let t := lazymatch (eval pattern (X4c 0%nat UStopLe 2 2) in t) with ?P _ => eval cbv beta in (P pm__8) end in PM_sub8 t.
Ltac PM_all9 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__8_eq; PM_all8.
Definition pm__9 : axst := ltac:(let t := eval cbv delta [X4] in (X4 0%nat UStopLe 2 1) in let t := eval cbv beta zeta in t in let t := PM_sub9 t in exact t).
Lemma pm__9_eq : ltac2:(tb__ "0|0|
S0S4S32U0SfZ2Z1A4S63A3"). Proof. cbv delta [X4 pm__9]; cbv beta zeta. PM_all9. reflexivity. Qed.
Ltac PM_sub10 t := let t := lazymatch (eval pattern (X4 0%nat UStopLe 2 1) in t) with ?P _ => eval cbv beta in (P pm__9) end in PM_sub9 t.
Ltac PM_all10 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__9_eq; PM_all9.
Definition pm__10 : axst := ltac:(let t := eval cbv delta [X4] in (X4 0%nat UStopLe 2 2) in let t := eval cbv beta zeta in t in let t := PM_sub10 t in exact t).
Lemma pm__10_eq : ltac2:(tb__ "0|1|
S0S4S32U0SfZ2M0G0A4S56A3"). Proof. cbv delta [X4 pm__10]; cbv beta zeta. PM_all10. reflexivity. Qed.
Ltac PM_sub11 t := let t := lazymatch (eval pattern (X4 0%nat UStopLe 2 2) in t) with ?P _ => eval cbv beta in (P pm__10) end in PM_sub10 t.
Ltac PM_all11 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__10_eq; PM_all10.
Definition pm__11 : axst := ltac2:(tb__ "0|0|
S74SaZ1A1S24S3S63A1A1A2").
Lemma pm__11_eq : ltac2:(tb__ "0|0|
S0S4S38U0SfZ2SaZ1A5S57A3"). Proof. cbv delta [T40 pm__11]; cbv beta zeta. PM_all11. reflexivity. Qed.
Ltac PM_sub12 t := let t := lazymatch (eval pattern (T40 0%nat UStopLe 2 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__11) end in PM_sub11 t.
Ltac PM_all12 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__11_eq; PM_all11.
Definition pm__12 : axst := ltac2:(tb__ "0|0|
S74SaZ2A1S24S3S56A1A1A2").
Lemma pm__12_eq : ltac2:(tb__ "0|1|
S0S4S38U0SfZ2M0SaG0A5S58A3"). Proof. cbv delta [T40 pm__12]; cbv beta zeta. PM_all12. reflexivity. Qed.
Ltac PM_sub13 t := let t := lazymatch (eval pattern (T40 0%nat UStopLe 2 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__12) end in PM_sub12 t.
Ltac PM_all13 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__12_eq; PM_all12.
Definition pm__13 : axst := ltac2:(tb__ "0|0|
S37S57U0A2").
Lemma pm__13_eq : ltac2:(tb__ "0|0|
S0S4S39U0SfZ2SaZ1A5S59A3"). Proof. cbv delta [T4a pm__13]; cbv beta zeta. PM_all13. reflexivity. Qed.
Ltac PM_sub14 t := let t := lazymatch (eval pattern (T4a 0%nat UStopLe 2 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__13) end in PM_sub13 t.
Ltac PM_all14 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__13_eq; PM_all13.
Definition pm__14 : axst := ltac2:(tb__ "0|0|
S37S58U0A2").
Lemma pm__14_eq : ltac2:(tb__ "0|1|
S0S4S39U0SfZ2M0SaG0A5S5aA3"). Proof. cbv delta [T4a pm__14]; cbv beta zeta. PM_all14. reflexivity. Qed.
Ltac PM_sub15 t := let t := lazymatch (eval pattern (T4a 0%nat UStopLe 2 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__14) end in PM_sub14 t.
Ltac PM_all15 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__14_eq; PM_all14.
Definition pm__15 : axst := ltac2:(tb__ "0|0|
S37S59U1A2").
Lemma pm__15_eq : ltac2:(tb__ "0|0|
S0S4S3aU0SfZ2SaZ1A5S54A3"). Proof. cbv delta [T4b pm__15]; cbv beta zeta. PM_all15. reflexivity. Qed.
Ltac PM_sub16 t := let t := lazymatch (eval pattern (T4b 0%nat UStopLe 2 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__15) end in PM_sub15 t.
Ltac PM_all16 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__15_eq; PM_all15.
Definition pm__16 : axst := ltac2:(tb__ "0|0|
S37S5aU1A2").
Lemma pm__16_eq : ltac2:(tb__ "0|1|
S0S4S3aU0SfZ2M0SaG0A5S55A3"). Proof. cbv delta [T4b pm__16]; cbv beta zeta. PM_all16. reflexivity. Qed.
Ltac PM_sub17 t := let t := lazymatch (eval pattern (T4b 0%nat UStopLe 2 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__16) end in PM_sub16 t.
Ltac PM_all17 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__16_eq; PM_all16.
Definition pm__17 : axst := ltac2:(tb__ "0|1|
S6S54S73S3S54A1M0S71S29G0A1S35SbA1A2A2A2").
Lemma pm__17_eq : ltac2:(tb__ "0|0|
S0S4S3bU0SfZ2SaSbZ1A6S5bA3"). Proof. cbv delta [T4c pm__17]; cbv beta zeta. PM_all17. reflexivity. Qed.
Ltac PM_sub18 t := let t := lazymatch (eval pattern (T4c 0%nat UStopLe 2 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__17) end in PM_sub17 t.
Ltac PM_all18 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__17_eq; PM_all17.
Definition pm__18 : axst := ltac2:(tb__ "0|1|
S6S55S73S3S55A1M0S71S29G0A1S35SbA1A2A2A2").
Lemma pm__18_eq : ltac2:(tb__ "0|1|
S0S4S3bU0SfZ2M0SaSbG0A6S5cA3"). Proof. cbv delta [T4c pm__18]; cbv beta zeta. PM_all18. reflexivity. Qed.
Ltac PM_sub19 t := let t := lazymatch (eval pattern (T4c 0%nat UStopLe 2 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__18) end in PM_sub18 t.
Ltac PM_all19 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__18_eq; PM_all18.
Definition pm__19 : axst := ltac2:(tb__ "0|0|
S33S5bU0A2").
Lemma pm__19_eq : ltac2:(tb__ "0|0|
S0S4S3cU0SfZ2SaSbZ1A6S5dA3"). Proof. cbv delta [T4m1 pm__19]; cbv beta zeta. PM_all19. reflexivity. Qed.
Ltac PM_sub20 t := let t := lazymatch (eval pattern (T4m1 0%nat UStopLe 2 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__19) end in PM_sub19 t.
Ltac PM_all20 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__19_eq; PM_all19.
Definition pm__20 : axst := ltac2:(tb__ "0|0|
S33S5cU0A2").
Lemma pm__20_eq : ltac2:(tb__ "0|1|
S0S4S3cU0SfZ2M0SaSbG0A6S5eA3"). Proof. cbv delta [T4m1 pm__20]; cbv beta zeta. PM_all20. reflexivity. Qed.
Ltac PM_sub21 t := let t := lazymatch (eval pattern (T4m1 0%nat UStopLe 2 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__20) end in PM_sub20 t.
Ltac PM_all21 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__20_eq; PM_all20.
Definition pm__21 : axst := ltac2:(tb__ "0|0|
S33S5dU0A2").
Lemma pm__21_eq : ltac2:(tb__ "0|0|
S0S4S3dU0SfZ2SaSbZ1A6S5fA3"). Proof. cbv delta [T4m2 pm__21]; cbv beta zeta. PM_all21. reflexivity. Qed.
Ltac PM_sub22 t := let t := lazymatch (eval pattern (T4m2 0%nat UStopLe 2 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__21) end in PM_sub21 t.
Ltac PM_all22 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__21_eq; PM_all21.
Definition pm__22 : axst := ltac2:(tb__ "0|0|
S33S5eU0A2").
Lemma pm__22_eq : ltac2:(tb__ "0|1|
S0S4S3dU0SfZ2M0SaSbG0A6S60A3"). Proof. cbv delta [T4m2 pm__22]; cbv beta zeta. PM_all22. reflexivity. Qed.
Ltac PM_sub23 t := let t := lazymatch (eval pattern (T4m2 0%nat UStopLe 2 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__22) end in PM_sub22 t.
Ltac PM_all23 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__22_eq; PM_all22.
Definition pm__23 : axst := ltac2:(tb__ "0|0|
S33S5fU0A2").
Lemma pm__23_eq : ltac2:(tb__ "0|0|
S0S4S3eU0SfZ2SaSbZ1A6S61A3"). Proof. cbv delta [T4m3 pm__23]; cbv beta zeta. PM_all23. reflexivity. Qed.
Ltac PM_sub24 t := let t := lazymatch (eval pattern (T4m3 0%nat UStopLe 2 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__23) end in PM_sub23 t.
Ltac PM_all24 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__23_eq; PM_all23.
Definition pm__24 : axst := ltac2:(tb__ "0|0|
S33S60U0A2").
Lemma pm__24_eq : ltac2:(tb__ "0|1|
S0S4S3eU0SfZ2M0SaSbG0A6S62A3"). Proof. cbv delta [T4m3 pm__24]; cbv beta zeta. PM_all24. reflexivity. Qed.
Ltac PM_sub25 t := let t := lazymatch (eval pattern (T4m3 0%nat UStopLe 2 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__24) end in PM_sub24 t.
Ltac PM_all25 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__24_eq; PM_all24.
Definition pm__25 : axst := ltac2:(tb__ "0|0|
S33S61U0A2").
Lemma pm__25_eq : ltac2:(tb__ "0|0|
S0S4S36U0SfZ2SaSbZ1A6S67A3"). Proof. cbv delta [T4d pm__25]; cbv beta zeta. PM_all25. reflexivity. Qed.
Ltac PM_sub26 t := let t := lazymatch (eval pattern (T4d 0%nat UStopLe 2 T4_i nobj_i 1) in t) with ?P _ => eval cbv beta in (P pm__25) end in PM_sub25 t.
Ltac PM_all26 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__25_eq; PM_all25.
Definition pm__26 : axst := ltac2:(tb__ "0|0|
S33S62U0A2").
Lemma pm__26_eq : ltac2:(tb__ "0|1|
S0S4S36U0SfZ2M0SaSbG0A6S68A3"). Proof. cbv delta [T4d pm__26]; cbv beta zeta. PM_all26. reflexivity. Qed.
Ltac PM_sub27 t := let t := lazymatch (eval pattern (T4d 0%nat UStopLe 2 T4_i nobj_i 2) in t) with ?P _ => eval cbv beta in (P pm__26) end in PM_sub26 t.
Ltac PM_all27 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__26_eq; PM_all26.
Lemma WX4r_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S30S3S34U0Vst;Vtmax;R2A4A1A1S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX4r_i : ltac2:(tb__ "0|5|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S1dS1aS18S1aS21S21A2M0A1M1S18S22A1M2A2M3A1S76S3S42U0M4Vst;Vtmax;A3A1S3S34G4Vst;Vtmax;R2A4A1A2S1cG3S1eG1G2S1bG0S1eS21S21S2fS1fQ20S27Pc0A1A3S23R2A1A4S17G0A1A3S17S22A1A4A2A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S31S25S4eS3S34U0M0Vst;Vtmax;R2A4A1G0S23Nf10A1A3A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S31S25S4eS3S3fU0Vst;Vtmax;R2A4A1U1S23N910A1A3A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S31S25S4eS3S40U0Vst;Vtmax;R2A4A1U2S23N848A1A3A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S31S25S4eS3S41U0Vst;Vtmax;R2A4A1U3S23N50A1A3A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HER_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S1dS18S28A1M0A1S79S32U0Vst;Vtmax;R2A4S51R2A1ScR2A1A3S1cG0SdR2A1A2A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S4S7aScR2A1S51R2A1S50R2A1S32U0Vst;Vtmax;R2A4SdR2A1A5SaR2A1A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S18S1aS21S21A2M0A1S5S32U0Vst;Vtmax;R2A4A1S17G0A1A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S49S22S2bS26S3S32U0Vst;Vtmax;R2A4A1M0A1A1S24G0A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S78S32U0Vst;Vtmax;R2A4S51R2A1ScR2A1SdR2A1S1bS4S50R2A1S17S4A1A3A5S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S9S26S3S32U0M0Vst;Vtmax;R2A4A1A1S26S3S45S10G0A1Vst;Vtmax;A3A1A1A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S21S52ScR2A1PaM0A2S2cS70S27G0A1S23N910A1A3A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc ]. Qed.
Lemma WG15_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S21S52ScR2A1PfA2S23N600A1A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc ]. Qed.
Lemma WG12_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S21S52ScR2A1PcA2S2cS70S27PaA1S23N848A1A3A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc ]. Qed.
Lemma FAM4_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S49S28S44U0A1SdR2A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc ]. Qed.
Lemma NEWO_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S18S28A1S77S3S51R2A1A1S3S50R2A1A1A2S17S28A1A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc ]. Qed.
Lemma XPost_i : ltac2:(tb__ "0|1|
S8S0S18S1aS21S21A2M0A1S5S50R1A1A1S17G0A1A3Fsz;").
Proof. intros sz. reflexivity. Qed.
Lemma FBT4_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S49S22S2bS26S3SaR2A1A1A1A1S24S3S32U0Vst;Vtmax;R2A4A1A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S18S1aS21S21A2M0A1S5SaR2A1A1S17G0A1A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc ]. Qed.
Lemma RB1_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S31S25S4fS3S38U0M0Vst;Vtmax;SaR2A5A1G0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S31S25S4fS3S39U0Vst;Vtmax;SaR2A5A1U1A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_nd_i : ltac2:(tb__ "0|0|
S0S15S72S35SbA1A1S16A3").
Proof.   vmc. Qed.
Lemma PERM_lt_i : ltac2:(tb__ "0|0|
S0S15S49S19S19S7dR1SbA2Li;S35SbA1A3S16A3").
Proof.   vmc. Qed.
Lemma PERM_cov_i : ltac2:(tb__ "0|0|
S0S15S49S19S19S4cS19S7cR1A1S35SbA1A3Li;S75U0SbA2A3S16A3").
Proof.   vmc. Qed.
Lemma PERM_len_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S19S20S28S29S3S3aU0Vst;Vtmax;SaR2A5A1A1A2SbA3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S31S25S4dS3S3bU0M0Vst;Vtmax;SaSbR2A6A1G0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S31S25S4dS3S3cU0M0Vst;Vtmax;SaSbR2A6A1G0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S31S25S4dS3S3dU0M0Vst;Vtmax;SaSbR2A6A1G0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S31S25S4dS3S3eU0M0Vst;Vtmax;SaSbR2A6A1G0A2A2S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S7S36U0M0Vst;Vtmax;SaSbR2A6S46S10G0A1Vst;Vtmax;A3SeR2A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5_i : ltac2:(tb__ "0|0|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S53SeR2A1S6fA2S16A3F_;Fsz;").
Proof. apply by_casesN; [> vmc | vmc ]. Qed.
Lemma R4cov_i : ltac2:(tb__ "0|1|
S8S1S2Z1R1A2S2R1Vtmax;A2A2S0S15S7bS24S3S36U0Vst;Vtmax;SaSbR2A6A1M0A1SdR2A1S29G0A1A3S16A3F_;Fsz;").
Proof. apply by_casesN; (cbv beta zeta delta [st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Htmax_i : 1 <= tmax <= SZMAX.
Proof. unfold SZMAX. subst tmax. lia. Qed.
Lemma HUS_i : stopJ_stable (Wcan 0) st.
Proof. apply stopJ_stable_le. Qed.
Lemma HUSr_i : ltac2:(tb__ "0|1|
S2eS2eS9S7fR1S6fA2S0S80Q40A1S2dR3R2A2S2dR4R2A2A3F_;Fi;S14S10U0A1Vst;R3A3M0G0F_;F_;Fr';Fr;").
Proof. intros r r' _ H. exact H. Qed.

End INST.
End CDepotCallI.

(* [comment removed for export] *)
Module CDepotCallH.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "prod"; "@Corelib.Init.Logic"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE"; "HDE_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "HD_stmt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.CDepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.CDepotCallM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.CDepotCallI.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let st : ustop := UStopLe. Let tmax : Z := 2.

Theorem depot_call_HD_0 : ltac2:(tb__ "0|1|
S1S2S0S0A2A1M0G0SeR2A1S10R2A1S0SfR5R1A2S3S11R2A1A1F_;Fa;S4OF_;SdSbS6S5ScR3A1S8SaR6S7R4A1A3S12SaR7S7R5A1A3S14U0Vst;Vtmax;S9RdRcR7A3R8R7R6R5R4A9F_;F_;F_;FQ;Frho;FKc;FA;Fok;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTD.
  exact (depot_call_HD 0%nat st tmax HUS_i HUSr_i CST XGL HCST HXGL HCSTD Htmax_i NXE_i FBE_i XE4_i F192_i FDEP_i FUNW_i FGEN4_i YP4_i WX4r_i DX4r_i SPL1_i SPL2_i SPL3_i SPL4_i
           s4_i R4_i T4_i HER_i HT4_i XX4_i FBX4_i Hchk4_i NX4_i WG10_i WG15_i WG12_i FAM4_i NEWO_i XPost_i FBT4_i XT4_i RB1_i RB2_i
           nobj_i PERM_nd_i PERM_lt_i PERM_cov_i PERM_len_i MRG1_i MRG2_i MRG3_i MRG4_i sd_i ENT5_i SID5_i R4cov_i).
Qed.

Theorem depot_call_HDE_0 : ltac2:(tb__ "0|1|
S1S2S0S0A2A1M0G0SeR2A1S10R2A1S0SfR5R1A2S3S11R2A1A1F_;Fa;SdSbS6S4OF_;ScR3A1S13U0Vst;Vtmax;S9RaR9R5A3R5R4R3R2A8F_;FQ;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTD.
  exact (depot_call_HDE 0%nat st tmax HUS_i HUSr_i CST XGL HCST HXGL HCSTD Htmax_i NXE_i FBE_i XE4_i F192_i FDEP_i FUNW_i FGEN4_i YP4_i WX4r_i DX4r_i SPL1_i SPL2_i SPL3_i SPL4_i
           s4_i R4_i T4_i HER_i HT4_i XX4_i FBX4_i Hchk4_i NX4_i WG10_i WG15_i WG12_i FAM4_i NEWO_i XPost_i FBT4_i XT4_i RB1_i RB2_i
           nobj_i PERM_nd_i PERM_lt_i PERM_cov_i PERM_len_i MRG1_i MRG2_i MRG3_i MRG4_i sd_i ENT5_i SID5_i R4cov_i).
Qed.
End INST.
End CDepotCallH.

(* [comment removed for export] *)
Module CallocGlueZ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "soff"; "ss_objs"; "sstate"; "DZero"; "cell"; "eval"; "mkObj"; "mkSS"; "obj_range"; "ranges_disjoint"; "rm"; "smatch"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "valuation"; "ss_next"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "nil"; "pair"; "true"; "Some"; "app"; "cons"; "list"; "option"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "xwords_clear"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma smatch_carve_zero_sym : ltac2:(tb__ "0|8|
S1dSbS28S36A1M0S34S35S8S8S8S1S14Vsegs;R9R8S23G0S2eR7S2fR6R5A2A4A4S10S19R9A1S1aR9A1S17R9A1S16R9A1S1bR9A1S26S7SaR9A1S27S7SfR5R4R3S22SdA1ScA5S22S7A1A3A3S15R9A1R2S18R9A1A9SbS1fS21S1cR1A1S24A3S2cQ40M1SeRcR7A2A2S0S9RdR7A2S0S9ReR7A2S0S3R2R1A2S4S6R2R3A2S5Z2M2Z3fA2A2S3Z0M3S2R5R4A2A2S3S2R6R4A2S5G2Z40A2A2S2dS7S7S12S11R14R1A2S23S0S0S2R8R7A2S2R8R6A2A4A2Lo';SaR12A1A3S0S20S3S2R9R8A2R1A2S4R1S2R9R7A2A2A2S20S1fS21S33Vsegs;S13R16A1M4S2aG1R2A2M5A3S24A3S1fS29S2bQ8M6A1M7A1S32Vsegs;G4G5A3S25G7S2aG6G3A2A2A3A2F_;Fa;S14Vsegs;R15RbS23G0S2eR13S2fR12R11A2A4A4F_;F_;F_;F_;F_;F_;Thi;Tlo;Tb;F_;TS';F_;Fnx;Fehi;Felo;Fbase;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md base elo ehi nx Hsm S' Hwf' b lo hi Hs1 Hs2 Hlo Hhi Hdisj Hbytes.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  set (newo := mkObj base elo ehi [] DZero).
  assert (Hnr : obj_range rho newo = (b + lo, b + hi)) by reflexivity.
  assert (Hout : forall a, b + lo <= a < b + hi -> outside_all rho (ss_objs S) (Z_to_bv 64 a)).
  { intros a Ha. apply Forall_forall. intros o Ho. cbn zeta. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D. rewrite u64_lit by lia. lia. }
  assert (MEM : forall a, b + lo <= a < b + hi -> ms_mem ms (Z_to_bv 64 a) = rm rho (Z_to_bv 64 a)).
  { intros a Ha. exact (Hfr _ (Hout a Ha)). }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf'|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    subst newo. unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt dflt_writable]. fold b. fold lo. fold hi.
    split; [lia|]. split.
    { intros off Hoff _. destruct (Hbytes (b + off) ltac:(lia)) as [Hw Hb].
      unfold wview. rewrite (MEM (b + off)) by lia.
      pose proof (wview_of_views segs (rm rho) (Z_to_bv 64 (b + off)) Hw (ex_intro _ _ Hb)) as X. unfold wview in X. exact X. }
    split; [constructor|]. split; [|exact I].
    intros off Hoff _. unfold dflt_holds, rd, ms_read_byte. rewrite (MEM (b + off)) by lia.
    destruct (Hbytes (b + off) ltac:(lia)) as [_ Hb]. unfold rd_of in Hb.
    destruct (rm rho (Z_to_bv 64 (b + off))) as [x|]; [exact Hb|]. rewrite <- Hb. first [apply Hrom | symmetry; apply Hrom].
  - apply pairwise_disjoint_app1; [exact Hpd|]. apply Forall_forall. intros o Ho. first [rewrite Hnr | subst newo; rewrite Hnr]. exact (proj1 (Forall_forall _ _) Hdisj o Ho).
  - intros x Hx. apply outside_all_app in Hx as [Hx1 Hx2]. apply Hfr. exact Hx1.
Qed.

Lemma SPA_carve_zero_sym : ltac2:(tb__ "0|9|
S31S1dS3aS28S2bQ40M0A1A1S37S8S8S8S1S30Vsegs;R9R7R8R6R5A6S38R8A1SbS10S19R1A1S1aR1A1S17R1A1S16R1A1S1bR1A1S26S7SaR1A1S27S7SfR6R5R4S22SdA1ScA5S22S7A1A3A3S15R1A1R3S18R1A1A9SbS1fS21S1cR1A1S24A3S3cS1eR3A1R5A2S2cG0SeRdR9A2A2S0S9ReR9A2S0S9RfR9A2S0S3R2R1A2S4S6R2R3A2S5Z2M1Z3fA2A2S3Z0M2S2R5R4A2A2S3S2R6R4A2S5G1Z40A2A2S2dS7S7S12S11R15R1A2S23S0S0S2R8R7A2S2R8R6A2A4A2Lo';SaRbA1A3S0S20S3S2R9R8A2M3R1A2S4R1S2R9R7A2M4A2A2S20S1fS21S33Vsegs;S13R17A1M5S2aG0R2A2M6A3S24A3S1fS29S2bQ8M7A1M8A1S32Vsegs;G5G6A3S25G8S2aG7G2A2A2A3A2F_;Fa;S3bR16R15G3G4A4S30Vsegs;R18S39R16RdA2R17R15R14A6F_;F_;F_;F_;F_;F_;F_;Thi;Tlo;Tb;F_;F_;TS';TS;F_;Fnx;Fehi;Felo;Fbase;Fw;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp [tr [ms md]] base elo ehi nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S S' Hwf' Hnx b lo hi Hs1 Hs2 Hlo Hhi Hdisj Hbytes Hxs.
  subst S' S. split; [|exact Hk].
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    apply (smatch_carve_zero_sym rho (ax_S A) tr (vms md tp ms) (vmd md) base elo ehi nx Hsm Hwf' Hs1 Hs2 Hlo Hhi Hdisj Hbytes).
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta.
    change (obj_range rho (mkObj base elo ehi [] DZero)) with (b + lo, b + hi). cbn [fst snd].
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2. exact (Hxs rr y j Hr Hy Hj).
Qed.
End WithSegs.
End CallocGlueZ.

(* [comment removed for export] *)
Module SpineCallocSec7.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "or"; "@Corelib.Init.Datatypes"; "nat"; "cons"; "list"; "bool"; "app"; "nil"; "true"; "length"; "pair"; "prod"; "andb"; "Some"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "rw"; "valuation"; "cell"; "sprop"; "sv"; "SVar"; "rl"; "rm"; "ss_facts"; "eval"; "holds"; "ss_objs"; "SLit"; "SPBranch"; "SPNot"; "odefault"; "ss_next"; "swf"; "DUnknown"; "DZero"; "SAlu"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_geom"; "aa_ptr_committed"; "aa_depot"; "ageom"; "aa_Kf"; "aa_V"; "aa_cache_inited"; "aa_cls"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_live"; "aa_q_global"; "aa_q_thread"; "class_state"; "qbatch"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "add"; "div"; "mul"; "eqb"; "leb"; "ltb"; "modulo"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "mkAX"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "A_globals"; "unwind_objs"; "V_RES"; "base_sv"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Corelib.Lists.ListDef"; "seq"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV"; "O_UBs"; "UBs"; "F_par"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7.SEC7.FIN"; "idxsU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7"; "idxsF"; "S2F"; "KUB"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "Lc_ok"; "JLc_ok"; "PFc"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NCH"; "V_NRES"; "nxS";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9"; "sw9"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayCommit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "GS"; "JGs"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require MallocInv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Placement StartLib StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require EnsureMapA CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.EnsureMapA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.CRebuildS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.CallocGlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition idxsF (nW : nat) (partial : bool) : list nat := ltac2:(tb__ "0|3|
S8S4S5S4U5S8S4S66U6M0VnW;A2S5S4S55G0VnW;A2S5S4S55U7VnW;A2S9S4A1M1A3A3A3A3S8S4S66S55U8M2VnW;A2U1eA2S8S4S5S4U0S5S4U1S5S4U2S5S4U3S5S4U4G1A3A3A3A3A3S8S4S66S55U26VnW;A2G2A2S8S4S5S4S55U2eVnW;A2S5S4S55U2fVnW;A2S5S4S55U30VnW;A2G1A3A3A3S7S6S4A1Lpartial;Vpartial;S5S4S55U31VnW;A2G1A3G1X7x2A3A3A3A3A3").
Definition KEPTF (W : list ulink) (swc : list cell) : list sobj := ltac2:(tb__ "0|0|
S5S13S9dVswc;A1S8S13S60VW;A1S5fA3A3").

Definition KUB (W : list ulink) (swc : list cell) (nx : positive) : list sobj := ltac2:(tb__ "0|0|
S8S13S5S13S9dVswc;A1S60VW;A1A3S8S13S5S13S68Vnx;A1S9S13A1A3S5fA3A3").
Definition S2F (F : axst) (K : list sobj) : sstate := ltac2:(tb__ "0|1|
S56VF;A1S30S29S2dR1A1S7fS2eR1A1S5SdS4S18A2M0ScS4S18U4S19P18A1A4S9G0A1A3A2S2bR1A1S2aR1A1S2fR1A1VK;S1cR1A1S24R1A1S2cR1A1A9TS;").
Definition XF_of (F : axst) (K : list sobj) (nx : positive) : axst := ltac2:(tb__ "0|1|
S59S8bVF;VK;A2S5SdS18S18A2M0ScS18S18S69Vnx;A1S19PcA1A4S9G0A1A3S62A3").

Definition bx_ok (BX : AA -> AA) : Prop := ltac2:(tb__ "0|3|
S35S1S0S3cS39VBX;R1A1M0A1S39R1A1A3S1S0S6S47A1S40G0A1S40R1A1A3S1S0S7S3fG0A1S3fR1A1A3S1S0S6S37A1S36G0A1S36R1A1A3S1S0S6SdS11S11A2A1M1S44G0A1S44R1A1A3S1S0S6S48A1M2S46G0A1S46R1A1A3S1S0G2S45G0A1S45R1A1A3S1S0S6S11A1S42G0A1S42R1A1A3S1S0S6G1A1S41G0A1S41R1A1A3S1S0S7S43G0A1S43R1A1A3S1S0S11S3eG0A1S3eR1A1A3S1S0S11S38G0A1S4eS38R1A1Z1A2A3S0S11S3dG0A1S3dR1A1A3A2A2A2A2A2A2A2A2A2A2A2A2FX;").

Section SEC7.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S12S9cVW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S7SabSa3Vnx;A2SaA3").
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S11S87VCST;R1A2S87Sa7R2A2S2F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S11S87VCST;R1A2S87Sa8R2A2S2F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
SaaVnW;Vst;Vnx;VBX;A4").

Section FIN.
Variable BX : AA -> AA.
Hypothesis BXok : bx_ok BX.
Variables (blk : Z) (dpx : odefault) (NRESe : sv) (FXP : list sprop).
Hypothesis Hdpx : ltac2:(tb__ "0|0|
S3S0S23Vdpx;S26A3S0S23Vdpx;S27A3A2").

Hypothesis HPATH : ltac2:(tb__ "0|4|
S35S5cS15S4aQ40M0A1M1S15S6G1A1S6S91A1S90VJG;VBX;R8R7R6R5R4R3R2R1A9S67S17S1eR5A1VFXP;A3VBX;S5bRaS49G0S14R8PcA2A2A2A1S35S1S1S4cZ8M2Vblk;A2S4cVblk;Z20000A2A2S1S4cS4eS50G2S4dSbS37S36RbA1A2A1A2Vblk;A2S3aR1A1M3A2S0G1S1dR7VNRESe;A2S4bG0S4fG3G2A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variable partial : bool.
Variable F : axst.
Variables swc c1 c2 c4 c5 mc xc : list cell.
Variable tyb : Z.
Let K : list sobj := KEPTF W swc.
Let RS : list sobj := ltac2:(tb__ "0|0|
S6bVnx;Vc1;Vc2;Vc4;Vc5;Vmc;Vxc;Vblk;Vdpx;Vpartial;Aa").
Let R : list sobj := RT_m1 ++ RS.
Hypothesis SELF : ltac2:(tb__ "0|0|
S0S6S13A1S98S1fS56VF;A1A1S8aVnW;Vpartial;A2A2S8S13VK;VR;A3A3").
Hypothesis NDF : ltac2:(tb__ "0|0|
S0S7S97S8aVnW;Vpartial;A2A1SaA3").
Hypothesis BNDF : ltac2:(tb__ "0|0|
S0S7S32S4S4S9fR1SbS13S1fS56VF;A1A1A2A2Li;S8aVnW;Vpartial;A2A3SaA3").
Hypothesis COVF : ltac2:(tb__ "0|0|
S0S7S32S4S4S33S4S9eR1A1S8aVnW;Vpartial;A2A3Li;S66U0SbS13S1fS56VF;A1A1A2A2A3SaA3").
Hypothesis XFn : ax_X F = [].
Hypothesis BFb : ax_base F = base_sv.
Hypothesis FPF : ltac2:(tb__ "0|0|
S34S17S8S17S65VW;Vst;A2S64S63A1A3S1cS56VF;A1A1A3").
Hypothesis FXF : ltac2:(tb__ "0|0|
S34S17VFXP;S1cS56VF;A1A1A3").
Hypothesis FPAR : ltac2:(tb__ "0|0|
S31S17S7S17Lpartial;Vpartial;S22S6aA1S6aX7x2S1cS56VF;A1A1A3").

Hypothesis Hc1 : ltac2:(tb__ "0|0|
S1S31S16S70Vc1;A3S1S31S16S6cVc1;A3S1S31S16S6dVc1;A3S1S31S16S71Vc1;A3S1S31S16S6fVNRESe;A1Vc1;A3S31S16S6eVc1;A3A2A2A2A2A2").
Hypothesis Hmc : ltac2:(tb__ "0|0|
S1S31S16S75Vnx;A1Vmc;A3S1S31S16S76Vmc;A3S1S31S16S77Vmc;A3S1S31S16S73Vmc;A3S1S31S16S74Vmc;A3S1S31S16S72Vnx;A1Vmc;A3S1S31S16S7aVmc;A3S1S31S16S7bVtyb;A1Vmc;A3S1S31S16S79Vmc;A3S31S16S78Vmc;A3A2A2A2A2A2A2A2A2A2").
Hypothesis Htyb : ltac2:(tb__ "0|0|
S0S7SeSeS52Z0Vtyb;A2S53Vtyb;Z100A2A2S51S54Vtyb;Z4A2Z1A2A2SaA3").
Hypothesis Hxc : In (xc_map nx) xc.

Let KU : list sobj := ltac2:(tb__ "0|0|
S8cVW;Vswc;Vnx;A3").
Definition idxsU (n : nat) : list nat := ltac2:(tb__ "0|2|
S8S4S5S4U0S66U1M0Vn;A2A3S8S4S5S4S55Vn;U3A2S9S4A1M1A3S5S4S55Vn;G0A2S5S4S55Vn;U2A2G1A3A3A3A3").
Hypothesis WCU : ltac2:(tb__ "0|0|
S0S7S25S99S56VF;A1S8S13VK;S5S13S68Vnx;A1S9S13A1A3A3A2A1SaA3").
Hypothesis SELU : ltac2:(tb__ "0|0|
S0S6S13A1S98S8S13VK;S5S13S68Vnx;A1S9S13A1A3A3S89VnW;A1A2VKU;A3").
Hypothesis NDU : ltac2:(tb__ "0|0|
S0S7S97S89VnW;A1A1SaA3").
Hypothesis BNDU : ltac2:(tb__ "0|0|
S0S7S32S4S4S9fR1SbS13S8S13VK;S5S13S68Vnx;A1S9S13A1A3A3A2A2Li;S89VnW;A1A3SaA3").
Hypothesis COVU : ltac2:(tb__ "0|0|
S0S7S32S4S4S33S4S9eR1A1S89VnW;A1A3Li;S66U0SbS13S8S13VK;S5S13S68Vnx;A1S9S13A1A3A3A2A2A3SaA3").
Hypothesis W9 : ltac2:(tb__ "0|0|
S0S7S25S8bVF;VKU;A2A1SaA3").
Hypothesis D9 : ltac2:(tb__ "0|4|
S0S10SdS6SdS18S18A2M0A1M1S6S17A1M2A2M3A1Sa0S99S56VF;A1VKU;A2S8bVF;VKU;A2A2SfG3ScG1G2S5G0ScS18S18S20Sa4A1S19P18A1A4S9G0A1A3S9S17A1A4A2A3").
Hypothesis XB9 : ltac2:(tb__ "0|0|
S0S7S5aS24S56VF;A1A1ScS18S18S69Vnx;A1S19PcA1A4A2SaA3").
Variable s9 : wsub.
Hypothesis ENT9 : ltac2:(tb__ "0|0|
S0S7S58S8dVF;VKU;Vnx;A3S92VW;Vst;A2Vs9;A3SaA3").
Hypothesis SID9 : wsub_idc s9 = true.
Hypothesis G110 : ltac2:(tb__ "0|0|
S0S18Sa1Vs9;S61A2S69Vnx;A1A3").

Theorem sec_finish_P : ltac2:(tb__ "0|6|
S35S5cS15S15S4aQ40M0A1M1S15S6G1A1M2G2S7cS6SdS57S84A2M3A1S31G3ScS57S84S92VW;Vst;A2S93VCST;VXGL;RaR9A4A4R1A3S85VW;Vst;A2S5dRbA1S12S0G1S14RbR1A2S14RcR1A2A3Fi;S12S0S6S4aQ8A1A1S1aRcR1A2S1aRdR1A2A3Fl;S5eVCST;VXGL;RfRfS1bRdA1S1bRcA1A6S4cS4dSbS37S36R10A1A2A1S38R10A1A2SdS11S11A2M4S31G4R1S88S3bVBX;S5bR12S49G0S14RfPcM5A2A2A2A1A1A1A3S86R2ScS11S11S49G0RfA2S8eS49G0S14R10G5A2A2A1A4A2F_;Fbn;S80Vsegs;VJG;VBX;R12R11RfReA5VF;RdRbRaA6S83Vsegs;S7eR11RdRaRbA6F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Fw;Ftp;Ftp0;FrhoE;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a rhoE tp0 tp w Posts HPin HW HKc HLw HLl HKEPT0 HL9 HDB H.
  destruct w as [tr [ms md]].
  pose proof H as [HsmA HJ]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (SPA_facts_hold segs _ rhoE F tp _ H) as HFacts.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (E12 & Enx & E141 & E142 & E151 & E152 & E155 & E145 & E146 & E147 & Erm & Erl).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  assert (HFX : Forall (holds rhoE) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HFacts p (FXF p Hp))).
  pose proof (HPATH A Kc rho a rhoE tp tr md HJ HFX) as (Hblk & HROOM & ENRES).
  pose proof (msx_val nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as EMSX.
  cbn zeta in *.
  set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *. set (L := secmapsize nv) in *.
  set (As := BX (bumpV A nv)) in *.
  destruct (BXok (bumpV A nv)) as (Bg & Bc & Bci & Bs & Bl & Bqt & Bqg & Bfh & Bfb & Bii & BV & BKm & BKf). fold As in Bg, Bc, Bci, Bs, Bl, Bqt, Bqg, Bfh, Bfb, Bii, BV, BKm, BKf.
  cbn [aa_geom aa_cls aa_cache_inited aa_sec aa_live aa_q_thread aa_q_global aa_fs_hint aa_fs_busy aa_internal_inited aa_V aa_Km aa_Kf bumpV] in Bg, Bc, Bci, Bs, Bl, Bqt, Bqg, Bfh, Bfb, Bii, BV, BKm, BKf.
  pose proof HJ as ((Hagw & Hagl & Hagm) & Ha & HA & HP & HK & Htp & HU & _ & Htop & HBud). fold nv As in HA. fold nv ua L in HP.
  set (G := aa_geom A) in *. set (T := ag_thread G). set (idx := Z.of_nat (length (aa_sec A))) in *. set (ub := ua + 6144). set (pw := ag_pab G + 8 * idx).
  assert (E153 : rw rhoE 153%positive = Z_to_bv 64 (ag_stack_top G)). { rewrite <- (Hagw 153%positive) by (unfold GW; lia). reflexivity. }
  assert (E154 : rw rhoE 154%positive = Z_to_bv 64 (ag_stack_bottom G)). { rewrite <- (Hagw 154%positive) by (unfold GW; lia). reflexivity. }
  assert (E156 : rw rhoE 156%positive = Z_to_bv 64 (ag_spacebeg G + kSpaceSize)). { rewrite <- (Hagw 156%positive) by (unfold GW; lia). reflexivity. }
  assert (ErmF : rm rhoE = rm rho). { apply functional_extensionality. intros x. exact (Erm x). }
  pose proof HA as (HG & HR & HFs & HRest & HM & HI3 & HBt). rewrite Bg in HG. fold G in HG.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & _). fold T in G4, G5. pose proof (topG_range G) as ACV.
  pose proof (urange a) as Ra. fold ua in Ra. unfold IMG_HI in IMG. unfold PG in AL, SMM.

  set (KJ := (fun (_ : valuation) (_ : list word) (t : list event) (m : Model) => Kc t m) : jpredA).
  assert (HaK : SPA segs KJ F rhoE tp (tr, {| cfg_ms := ms; cfg_model := md |})) by (split; [exact HsmA | exact HK]).
  pose proof (SPA_select segs KJ rhoE F (idxsF nW partial) tp _ HaK NDF
                ltac:(intros i Hi; apply Nat.ltb_lt; exact (proj1 (forallb_forall _ _) BNDF i Hi))
                ltac:(intros i Hi; pose proof (proj1 (forallb_forall _ _) COVF i ltac:(apply in_seq; lia)) as X;
                      apply existsb_exists in X as (i' & Hi' & E); apply Nat.eqb_eq in E; subst i'; exact Hi')) as Hsel.
  rewrite SELF in Hsel. clear HaK.

  pose proof (SPA_unobj segs KJ rhoE (ax_setS F (set_objs (ax_S F) (K ++ R))) K R tp tr ms md eq_refl Hsel (fun k => k)) as Hb.
  cbn zeta in Hb. set (rho3 := rho_absorb rhoE R (vms md tp ms)) in *.
  pose proof (proj1 (proj1 Hsel)) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S ax_setS] in Hsm1.
  set (v3 := view segs (rm rho3)). set (vE := view segs (rm rhoE)).
  assert (AO : forall o, In o R -> _) by (intros o Ho; exact (absorb_obj rhoE _ tr (vms md tp ms) (vmd md) K R o Hsm1 eq_refl Ho)).
  assert (INRS : forall o, In o RS -> In o R) by (intros o Ho; unfold R; apply in_or_app; right; exact Ho).

  assert (AOC : forall o c bZ offZ V, In o RS -> In c (ob_cells o) ->
            bv_unsigned (eval rhoE (ob_base o)) = bZ -> soff rhoE (c_off c) = offZ -> eval rhoE (SymState.c_val c) = Z_to_bv 64 V ->
            0 <= bZ + offZ -> bZ + offZ + c_width c <= 2 ^ 64 ->
            cell_ok v3 (mkACell (bZ + offZ) (Z.to_nat (c_width c)) V)).
  { intros o c bZ offZ V Ho Hc Eb Eo Ev B1 B2. destruct (AO o (INRS o Ho)) as (_ & CO & _). destruct (CO c Hc) as (_ & _ & CJ).
    rewrite Eb, Eo, Ev in CJ. intros k Hk. cbn [c_addr c_w RtCells.c_val] in *. unfold v3. rewrite view_in by (clear -B1 B2 Hk; lia). exact (CJ k Hk). }
  assert (AOP : forall o z, In o RS -> (ob_dflt o = DUnknown \/ ob_dflt o = DZero) -> fst (obj_range rhoE o) <= z < snd (obj_range rhoE o) -> exists bb, v3 z = Some bb).
  { intros o z Ho DD Hz. destruct (AO o (INRS o Ho)) as (Bo & _ & Po & _). unfold obj_range in Hz. cbn [fst snd] in Hz.
    unfold v3. rewrite view_in by (clear -Bo Hz; unfold obj_lo_of, obj_hi_of in *; lia).
    replace z with (bv_unsigned (eval rhoE (ob_base o)) + (z - bv_unsigned (eval rhoE (ob_base o)))) by (clear; lia).
    apply Po; [exact DD | clear -Hz; unfold obj_lo_of, obj_hi_of in *; lia]. }
  assert (AOZ : forall o z, In o RS -> ob_dflt o = DZero -> ob_cells o = [] -> fst (obj_range rhoE o) <= z < snd (obj_range rhoE o) ->
                        rd_of segs (rm rho3) (Z_to_bv 64 z) = Some (Z_to_bv 8 0)).
  { intros o z Ho DZ NC Hz. destruct (AO o (INRS o Ho)) as (Bo & _ & _ & Zo). unfold obj_range in Hz. cbn [fst snd] in Hz.
    replace z with (bv_unsigned (eval rhoE (ob_base o)) + (z - bv_unsigned (eval rhoE (ob_base o)))) by (clear; lia).
    apply Zo; [exact DZ | clear -Hz; unfold obj_lo_of, obj_hi_of in *; lia |]. rewrite NC. intros HX. inversion HX. }

  assert (EVnx : bv_unsigned (eval rhoE (SVar nx)) = ua) by (cbn [eval]; rewrite Enx; reflexivity).
  assert (UAB : 6578176 <= ua /\ ua + L <= 140737479966720 /\ 73728 <= L) by (clear -IMG TOP SMB; lia).
  assert (LB : nv + 8192 <= L).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  assert (WZ : forall w : word, w = Z_to_bv 64 (bv_unsigned w)) by (intros w0; symmetry; apply Z_to_bv_bv_unsigned).

  assert (IN_Mlo : In (O_Mlo nx mc) RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (IN_seci : In (O_seciF c1) RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (IN_secm : In O_secmF RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (IN_px : In (O_pxF blk dpx xc) RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (IN_4z : In (O_4z nx) RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  destruct Hmc as (M0 & M8 & M16 & M24 & M4096 & M4104 & M6128 & M6129 & M6130 & M6132).
  destruct Hc1 as (I0 & I8 & I16 & I24 & I48 & I56).
  assert (SOL : forall z, 0 <= z < 2 ^ 62 -> soff rhoE (SLit z) = z) by (intros z Hz; apply soff_lit_small; lia).

  assert (C0 : cell_ok v3 (mkACell ua 8 ua)).
  { replace ua with (ua + 0) at 1 by (clear; lia). apply (AOC (O_Mlo nx mc) (mc_map nx) ua 0 ua IN_Mlo M0 EVnx (SOL 0 ltac:(clear; lia))); [cbn [SymState.c_val mc_map eval]; rewrite Enx; apply WZ | clear -UAB; lia | cbn [c_width mc_map]; clear -UAB; lia]. }
  assert (C8 : cell_ok v3 (mkACell (ua + 8) 8 L)).
  { apply (AOC (O_Mlo nx mc) mc_ms ua 8 L IN_Mlo M8 EVnx (SOL 8 ltac:(clear; lia))); [cbn [SymState.c_val mc_ms]; rewrite (WZ (eval rhoE msx)), EMSX; reflexivity | clear -UAB; lia | cbn [c_width mc_ms]; clear -UAB; lia]. }
  assert (C16 : cell_ok v3 (mkACell (ua + 16) 8 (secneeded nv))).
  { apply (AOC (O_Mlo nx mc) mc_ns ua 16 (secneeded nv) IN_Mlo M16 EVnx (SOL 16 ltac:(clear; lia))); [cbn [SymState.c_val mc_ns eval]; exact E141 | clear -UAB; lia | cbn [c_width mc_ns]; clear -UAB; lia]. }
  assert (C24 : cell_ok v3 (mkACell (ua + 24) 8 idx)).
  { apply (AOC (O_Mlo nx mc) mc_idx ua 24 idx IN_Mlo M24 EVnx (SOL 24 ltac:(clear; lia))); [cbn [SymState.c_val mc_idx eval]; exact E147 | clear -UAB; lia | cbn [c_width mc_idx]; clear -UAB; lia]. }
  assert (VMG0 : cell_ok v3 (mkACell (ua + 4096) 8 kAllocBegMagic)).
  { apply (AOC (O_Mlo nx mc) mc_magic ua 4096 kAllocBegMagic IN_Mlo M4096 EVnx (SOL 4096 ltac:(clear; lia))); [reflexivity | clear -UAB; lia | cbn [c_width mc_magic]; clear -UAB; lia]. }
  assert (VMG8 : cell_ok v3 (mkACell (ua + 4104) 8 (ub - 16))).
  { apply (AOC (O_Mlo nx mc) (mc_cptr nx) ua 4104 (ub - 16) IN_Mlo M4104 EVnx (SOL 4104 ltac:(clear; lia))); [| clear -UAB; lia | cbn [c_width mc_cptr]; clear -UAB; lia].
    cbn [SymState.c_val mc_cptr]. apply bv_eq. cbn [eval]. rewrite Enx, add_val, !u64_lit by (unfold ub; clear -UAB; lia). fold ua. rewrite Z.mod_small by (clear -UAB; lia). unfold ub. clear. lia. }

  assert (EN12 : eval rhoE (SVar 12) = Z_to_bv 64 nv) by (cbn [eval]; rewrite E12; apply WZ).
  assert (B1E : forall z, 0 <= z < 256 -> nth 0 (enc_bytes 1 (Z_to_bv 64 z)) (Z_to_bv 8 0) = Z_to_bv 8 z).
  { intros z Hz. rewrite (ReprGlue.nth_enc_bytes 1 0 z ltac:(clear; lia) ltac:(clear; lia)). apply f_equal. unfold MallocInv.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by (clear -Hz; lia). reflexivity. }
  assert (VH2 : v3 (ub - 16) = Some (Z_to_bv 8 2)).
  { pose proof (AOC (O_Mlo nx mc) mc_state ua 6128 2 IN_Mlo M6128 EVnx (SOL 6128 ltac:(clear; lia)) eq_refl ltac:(clear -UAB; lia) ltac:(cbn [c_width mc_state]; clear -UAB; lia)) as X.
    specialize (X 0%nat ltac:(cbn; clear; lia)). cbn [c_addr c_w RtCells.c_val c_width mc_state Z.of_nat] in X. rewrite Z.add_0_r in X.
    replace (ub - 16) with (ua + 6128) by (unfold ub; clear; lia). rewrite X. apply f_equal. exact (B1E 2 ltac:(clear; lia)). }
  assert (VH1 : exists t, v3 (ub - 15) = Some t /\ bv_unsigned t mod 4 = 1).
  { apply andb_prop in Htyb as [Ht1 Ht2]. apply andb_prop in Ht1 as [Ht0 Ht1]. apply Z.leb_le in Ht0. apply Z.ltb_lt in Ht1. apply Z.eqb_eq in Ht2.
    pose proof (AOC (O_Mlo nx mc) (mc_type tyb) ua 6129 tyb IN_Mlo M6129 EVnx (SOL 6129 ltac:(clear; lia)) eq_refl ltac:(clear -UAB; lia) ltac:(cbn [c_width mc_type]; clear -UAB; lia)) as X.
    specialize (X 0%nat ltac:(cbn; clear; lia)). cbn [c_addr c_w RtCells.c_val c_width mc_type Z.of_nat] in X. rewrite Z.add_0_r in X.
    exists (Z_to_bv 8 tyb). split.
    - replace (ub - 15) with (ua + 6129) by (unfold ub; clear; lia). rewrite X. apply f_equal. exact (B1E tyb (conj Ht0 Ht1)).
    - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small tyb 256) by (clear -Ht0 Ht1; lia). exact Ht2. }
  assert (VHN : cell_ok v3 (mkACell (ub - 12) 4 (nv mod 2 ^ 32))).
  { pose proof (AOC (O_Mlo nx mc) mc_size ua 6132 nv IN_Mlo M6132 EVnx (SOL 6132 ltac:(clear; lia)) EN12 ltac:(clear -UAB; lia) ltac:(cbn [c_width mc_size]; clear -UAB; lia)) as X.
    intros k Hk. specialize (X k Hk). cbn [c_addr c_w RtCells.c_val c_width mc_size] in X, Hk |- *. change (Z.to_nat 4) with 4%nat in X, Hk.
    replace (ub - 12 + Z.of_nat k) with (ua + 6132 + Z.of_nat k) by (unfold ub; clear; lia). rewrite X. apply f_equal.
    rewrite !(ReprGlue.nth_enc_bytes 4 k) by (first [exact Hk | clear; lia]). apply f_equal. unfold MallocInv.le_byte. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by (clear; lia). reflexivity. }
  assert (VH0 : cell_ok v3 (mkACell (ub - 14) 2 (nv / 2 ^ 32))).
  { assert (EV : eval rhoE (SAlu ALU_SRL (SVar 12) (SLit 32)) = Z_to_bv 64 (nv / 2 ^ 32)).
    { apply bv_eq. cbn [eval]. rewrite E12, srl_val. fold nv. change (32 mod 64) with 32. rewrite Z.shiftr_div_pow2 by (clear; lia).
      symmetry. apply u64_lit. pose proof (Z.div_pos nv (2 ^ 32) ltac:(clear -HN; lia) ltac:(clear; lia)). pose proof (Z.div_lt_upper_bound nv (2 ^ 32) (2 ^ 7) ltac:(clear; lia) ltac:(clear -HN; lia)). lia. }
    pose proof (AOC (O_Mlo nx mc) mc_sizehi ua 6130 (nv / 2 ^ 32) IN_Mlo M6130 EVnx (SOL 6130 ltac:(clear; lia)) EV ltac:(clear -UAB; lia) ltac:(cbn [c_width mc_sizehi]; clear -UAB; lia)) as X.
    replace (ub - 14) with (ua + 6130) by (unfold ub; clear; lia). exact X. }

  assert (EV0 : bv_unsigned (eval rhoE (SLit 0)) = 0) by reflexivity.
  assert (SECB : 0 <= SEC_INST /\ 0xee044 <= 2 ^ 62) by (unfold SEC_INST; clear; lia).
  assert (CI0 : cell_ok v3 (mkACell SEC_INST 8 PG)).
  { pose proof (AOC (O_seciF c1) ic_pg 0 SEC_INST PG IN_seci I0 EV0 (SOL SEC_INST ltac:(unfold SEC_INST; clear; lia)) eq_refl ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (CI8 : cell_ok v3 (mkACell (SEC_INST + 8) 8 (ag_pab G))).
  { pose proof (AOC (O_seciF c1) ic_c1 0 (SEC_INST + 8) (ag_pab G) IN_seci I8 EV0 (SOL (SEC_INST + 8) ltac:(unfold SEC_INST; clear; lia)) ltac:(cbn [SymState.c_val ic_c1 eval]; exact E145) ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (CI16 : cell_ok v3 (mkACell (SEC_INST + 16) 8 (ag_pab G))).
  { pose proof (AOC (O_seciF c1) ic_c2 0 (SEC_INST + 16) (ag_pab G) IN_seci I16 EV0 (SOL (SEC_INST + 16) ltac:(unfold SEC_INST; clear; lia)) ltac:(cbn [SymState.c_val ic_c2 eval]; exact E145) ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (CI24 : cell_ok v3 (mkACell (SEC_INST + 24) 8 kPtrArrayReserve)).
  { pose proof (AOC (O_seciF c1) ic_rs 0 (SEC_INST + 24) kPtrArrayReserve IN_seci I24 EV0 (SOL (SEC_INST + 24) ltac:(unfold SEC_INST; clear; lia)) eq_refl ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (C48 : cell_ok v3 (mkACell (SEC_INST + 48) 8 (aa_ptr_committed As / 8))).
  { pose proof (AOC (O_seciF c1) (ic_nres NRESe) 0 (SEC_INST + 48) (aa_ptr_committed As / 8) IN_seci I48 EV0 (SOL (SEC_INST + 48) ltac:(unfold SEC_INST; clear; lia)) ENRES ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  pose proof (Zle_0_nat (length (aa_sec A))) as IDX0. fold idx in IDX0.
  pose proof HRest as (_ & _ & _ & HSRs & _). pose proof (pab_facts _ As HSRs) as (P1 & P2 & P3 & P4 & P5). rewrite Bg in P1, P2, P3. rewrite Bs in P4. fold G in P1, P2, P3. fold idx in P4.
  unfold IMG_HI in P1. unfold kPtrArrayReserve in P2, P4.
  assert (C56 : cell_ok v3 (mkACell (SEC_INST + 56) 8 (idx + 1))).
  { assert (EV : eval rhoE (SAlu ALU_ADD (SVar V_NCH) (SLit 1)) = Z_to_bv 64 (idx + 1)).
    { apply bv_eq. cbn [eval]. rewrite E147, add_val, !u64_lit by (clear -IDX0 P4; lia). fold idx. apply Z.mod_small. clear -IDX0 P4. lia. }
    pose proof (AOC (O_seciF c1) ic_nch 0 (SEC_INST + 56) (idx + 1) IN_seci I56 EV0 (SOL (SEC_INST + 56) ltac:(unfold SEC_INST; clear; lia)) EV ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (CMU : cell_ok v3 (mkACell 0xee040 4 0)).
  { pose proof (AOC O_secmF (mkCell (SLit 0xee040) 1 (SLit 0)) 0 0xee040 0 IN_secm ltac:(cbn; left; reflexivity) EV0 (SOL 0xee040 ltac:(clear; lia)) eq_refl ltac:(clear; lia) ltac:(cbn; clear; lia)) as X1.
    pose proof (AOC O_secmF (mkCell (SLit 0xee041) 3 (SLit 0)) 0 0xee041 0 IN_secm ltac:(cbn; right; left; reflexivity) EV0 (SOL 0xee041 ltac:(clear; lia)) eq_refl ltac:(clear; lia) ltac:(cbn; clear; lia)) as X3.
    assert (ZB : forall w k, (k < w)%nat -> (w <= 8)%nat -> nth k (enc_bytes w (Z_to_bv 64 0)) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { intros w0 k0 H1 H2. rewrite (ReprGlue.nth_enc_bytes w0 k0 0 H1 H2). apply f_equal. unfold MallocInv.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. }
    intros k Hk. cbn [c_addr c_w RtCells.c_val] in Hk |- *. rewrite (ZB 4%nat k Hk ltac:(clear; lia)).
    destruct k as [|k].
    - specialize (X1 0%nat ltac:(cbn; clear; lia)). cbn [c_addr c_w RtCells.c_val c_width] in X1. change (Z.to_nat 1) with 1%nat in X1. rewrite (ZB 1%nat 0%nat ltac:(clear; lia) ltac:(clear; lia)) in X1.
      replace (0xee040 + Z.of_nat 0) with (0 + 0xee040 + Z.of_nat 0) by (clear; lia). exact X1.
    - specialize (X3 k ltac:(cbn; clear -Hk; lia)). cbn [c_addr c_w RtCells.c_val c_width] in X3. change (Z.to_nat 3) with 3%nat in X3. rewrite (ZB 3%nat k ltac:(clear -Hk; lia) ltac:(clear; lia)) in X3.
      replace (0xee040 + Z.of_nat (S k)) with (0 + 0xee041 + Z.of_nat k) by (clear; lia). exact X3. }

  assert (EBw : bv_unsigned (eval rhoE Bw) = pw).
  { unfold Bw, pw. cbn [eval]. rewrite E145, E147, add_val, sll_val. fold G idx. rewrite !u64_lit by (clear -P1 P2 P4 IDX0 ACV; lia).
    change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 3) with 8.
    rewrite (Z.mod_small (idx * 8)) by (clear -IDX0 P4; lia). rewrite Z.mod_small by (clear -P1 P2 P4 IDX0 ACV; lia). clear. lia. }
  assert (PWB : ag_pab G <= pw /\ pw + blk <= ag_pab G + 8388608) by (unfold pw; clear -IDX0 HROOM P4; lia).
  assert (CPW : cell_ok v3 (mkACell pw 8 ua)).
  { pose proof (AOC (O_pxF blk dpx xc) (xc_map nx) pw 0 ua IN_px Hxc EBw (SOL 0 ltac:(clear; lia)) ltac:(cbn [SymState.c_val xc_map eval]; rewrite Enx; apply WZ)
                  ltac:(clear -PWB P1; lia) ltac:(cbn [c_width xc_map]; clear -PWB P2 ACV Hblk; lia)) as X.
    rewrite Z.add_0_r in X. exact X. }

  destruct (site8_vals nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (EB4 & EL4 & _). cbn zeta in EB4, EL4. fold nv ua in EB4, EL4.
  assert (ESHub : Sh ub = Sh ua + 768).
  { unfold Sh, ub. replace (ua + 6144) with (ua + 768 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear. lia. }
  pose proof (Z.div_pos nv 8 ltac:(clear -HN; lia) ltac:(clear; lia)) as NP. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(clear; lia) ltac:(clear -HN; lia)) as NU.
  assert (SHB : 2147450880 <= Sh ua /\ Sh ua + L / 8 <= 17594333495296).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_pos ua 8 ltac:(clear -UAB; lia) ltac:(clear; lia)) as D0.
    pose proof (Z.div_le_mono (ua + L) 140737479966720 8 ltac:(clear; lia) ltac:(clear -UAB; lia)) as D1. change (140737479966720 / 8) with 17592184995840 in D1.
    assert (DS : ua / 8 + L / 8 <= (ua + L) / 8) by (apply Z.div_le_lower_bound; [clear; lia|]; pose proof (Z.mul_div_le ua 8 ltac:(clear; lia)); pose proof (Z.mul_div_le L 8 ltac:(clear; lia)); lia).
    clear -D0 D1 DS. lia. }
  assert (L8B : nv / 8 + 1024 <= L / 8).
  { pose proof (Z.div_le_mono (nv + 8192) L 8 ltac:(clear; lia) LB) as D. replace (nv + 8192) with (nv + 1024 * 8) in D by (clear; lia). rewrite Z.div_add in D by (clear; lia). exact D. }
  assert (VZ : forall g, 0 <= g < nv / 8 -> v3 (Sh ub + g) = Some (Z_to_bv 8 0)).
  { intros g Hg. destruct (AO _ (INRS _ IN_4z)) as (_ & _ & _ & ZO). cbn [ob_base ob_cells ob_lo ob_hi ob_dflt O_4z] in ZO. specialize (ZO eq_refl g).
    unfold obj_lo_of, obj_hi_of in ZO. cbn [ob_lo ob_hi ob_cells ob_base O_4z] in ZO. rewrite soff_lit_small in ZO by (clear; lia).
    rewrite (soff_of_val rhoE (a2e8 nx) (nv / 8) EL4) in ZO by (clear -NP NU; lia). rewrite EB4 in ZO.
    unfold v3. rewrite view_in by (rewrite ESHub; clear -SHB Hg L8B; lia). rewrite ESHub.
    apply ZO; [exact Hg|]. intros HC. unfold covered in HC. apply Exists_exists in HC as (cc & Hcc & _). exact Hcc. }
  pose proof (nmod8_of_par nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (PAR0 & PAR1). fold nv in PAR0, PAR1.
  pose proof (proj1 (Forall_forall _ _) HFacts _ FPAR) as HPARF.
  destruct (site9_vals nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (_ & EBP9). cbn zeta in EBP9. fold nv ua in EBP9.
  assert (VP : nv mod 8 <> 0 -> v3 (Sh ub + nv / 8) = Some (Z_to_bv 8 (nv mod 8))).
  { intros Hm. destruct partial eqn:EP; [|exfalso; exact (Hm (PAR0 HPARF))].
    assert (IN_P : In (O_Pf9 nx) RS) by (unfold RS, RSF; try rewrite EP; cbn [app In]; repeat (first [left; reflexivity | right])).
    assert (EV : eval rhoE (SAlu ALU_AND (SVar 12) (SLit 7)) = Z_to_bv 64 (nv mod 8)).
    { apply bv_eq. cbn [eval]. rewrite E12, and_val. fold nv. rewrite (u64_lit 7) by (clear; lia). rewrite land_7 by (clear -HN; lia). symmetry. apply u64_lit. pose proof (Z.mod_pos_bound nv 8 ltac:(clear; lia)). lia. }
    pose proof (AOC (O_Pf9 nx) (mkCell (SLit 0) 1 (SAlu ALU_AND (SVar 12) (SLit 7))) (Sh ua + 768 + nv / 8) 0 (nv mod 8) IN_P ltac:(cbn; left; reflexivity) EBP9 (SOL 0 ltac:(clear; lia)) EV
                  ltac:(clear -SHB NP; lia) ltac:(cbn [c_width]; clear -SHB L8B; lia)) as X.
    specialize (X 0%nat ltac:(cbn; clear; lia)). cbn [c_addr c_w RtCells.c_val c_width Z.of_nat] in X. rewrite !Z.add_0_r in X.
    rewrite ESHub. rewrite X. apply f_equal. apply B1E. pose proof (Z.mod_pos_bound nv 8 ltac:(clear; lia)). lia. }

  destruct (site7_vals nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (_ & _ & EBR & EL3b & V512 & VM). cbn zeta in EBR, EL3b, V512, VM. fold nv ua L in EBR, EL3b, V512, VM.
  destruct (site3_vals nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (EB3 & _ & EL3). fold ua in EB3.
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (EB1 & EL1 & _). fold ua in EB1.
  assert (EUB : bv_unsigned (eval rhoE (UBs nx)) = ub).
  { unfold UBs. cbn [eval]. rewrite Enx, add_val, !u64_lit by (clear; lia). fold ua. rewrite Z.mod_small by (clear -UAB; lia). reflexivity. }
  assert (EVT : bv_unsigned (eval rhoE vT) = T) by (unfold vT; cbn [eval]; rewrite E151; apply u64_lit; fold G T; clear -G4 G5 ACV; lia).
  assert (RG_Mlo : obj_range rhoE (O_Mlo nx mc) = (ua, ua + 6144)) by (unfold O_Mlo; rewrite obj_range_mk by (clear; lia); rewrite EVnx; f_equal; clear; lia).
  assert (RG_fill : obj_range rhoE (O_fill nx) = (ub, ub + 4096)) by (unfold O_fill; rewrite obj_range_mk by (clear; lia); rewrite EVnx; unfold ub; f_equal; clear; lia).
  assert (RG_Mhi : obj_range rhoE (O_Mhi nx) = (ua + 10240, ua + L)).
  { unfold O_Mhi, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_of_val rhoE (SVar V_MS) L) by (first [cbn [eval]; rewrite E142; apply u64_lit; clear -UAB; lia | clear -UAB; lia]). rewrite EVnx. reflexivity. }
  assert (RG_1 : obj_range rhoE (O_1 nx) = (Sh ua, Sh ua + 512)) by (unfold O_1, L1; rewrite obj_range_mk by (clear; lia); rewrite EB1; f_equal; clear; lia).
  assert (RG_3 : obj_range rhoE (O_3 nx) = (Sh ua + 512, Sh ua + 768)) by (unfold O_3, L3; rewrite obj_range_mk by (clear; lia); rewrite EB3; f_equal; clear; lia).
  assert (RG_4z : obj_range rhoE (O_4z nx) = (Sh ua + 768, Sh ua + 768 + nv / 8)).
  { unfold O_4z, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_of_val rhoE (a2e8 nx) (nv / 8) EL4) by (clear -NP NU; lia). rewrite EB4. f_equal. clear. lia. }
  set (v8 := secneeded nv / 8) in *.
  assert (RG_3b : obj_range rhoE (O_3b nx) = (Sh ua + v8 + 256, Sh ua + L / 8)).
  { unfold O_3b, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_of_val rhoE L3b (L / 8 - v8 - 256) EL3b) by (clear -V512 VM SHB; lia). rewrite EBR. f_equal; clear; lia. }
  assert (RG_P : obj_range rhoE (O_Pf9 nx) = (Sh ua + 768 + nv / 8, Sh ua + 768 + nv / 8 + 1)) by (unfold O_Pf9; rewrite obj_range_mk by (clear; lia); rewrite EBP9; f_equal; clear; lia).
  assert (RG_px : obj_range rhoE (O_pxF blk dpx xc) = (pw, pw + blk)) by (unfold O_pxF; rewrite obj_range_mk by (clear -Hblk; lia); rewrite EBw; f_equal; clear; lia).
  assert (RG_st : obj_range rhoE (O_stF c5) = (T + 2768, T + 3168)) by (unfold O_stF; rewrite obj_range_mk by (clear; lia); rewrite EVT; reflexivity).
  assert (RG_seci : obj_range rhoE (O_seciF c1) = (SEC_INST, SEC_INST + 64)) by (unfold O_seciF; rewrite obj_range_mk by (unfold SEC_INST; clear; lia); reflexivity).
  assert (RG_secs : obj_range rhoE (O_secsF c2) = (SEC_INST + 64, 0xee040)) by (unfold O_secsF; rewrite obj_range_mk by (unfold SEC_INST; clear; lia); reflexivity).
  assert (RG_secm : obj_range rhoE O_secmF = (0xee040, 0xee044)) by (unfold O_secmF; rewrite obj_range_mk by (clear; lia); reflexivity).
  assert (RG_secg : obj_range rhoE (O_secgF c4) = (0xee048, 0xee070)) by (unfold O_secgF; rewrite obj_range_mk by (clear; lia); reflexivity).
  assert (RG_san : obj_range rhoE O_san = (0xe9b28, 0xe9b30)).
  { change O_san with (mkObj (SLit 0) (SLit 0xe9b28) (SLit 0xe9b30) (ob_cells O_san) DUnknown). rewrite obj_range_mk by (clear; lia). reflexivity. }
  assert (RG_oom : obj_range rhoE O_oom = (0x173660, 0x173662)).
  { change O_oom with (mkObj (SLit 0) (SLit 0x173660) (SLit 0x173662) (ob_cells O_oom) DUnknown). rewrite obj_range_mk by (clear; lia). reflexivity. }
  assert (RG_errno : obj_range rhoE O_errno = (ERRNO_A, ERRNO_A + 4)).
  { change O_errno with (mkObj (SLit 0) (SLit ERRNO_A) (SLit (ERRNO_A + 4)) (ob_cells O_errno) DUnknown). rewrite obj_range_mk by (unfold ERRNO_A; clear; lia). reflexivity. }

  assert (PARB : if partial then nv mod 8 <> 0 else nv mod 8 = 0) by (destruct partial; [exact (PAR1 HPARF) | exact (PAR0 HPARF)]).
  assert (EV8 : v8 = 768 - 256 + nv / 8 + (if partial then 1 else 0)).
  { unfold v8. rewrite ENS. replace (round_up nv 8 + 4096) with (round_up nv 8 + 512 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia).
    unfold round_up. rewrite Z.div_mul by (clear; lia). pose proof (Z.div_mod nv 8 ltac:(clear; lia)) as DN. pose proof (Z.mod_pos_bound nv 8 ltac:(clear; lia)) as MN.
    destruct partial.
    - replace ((nv + 8 - 1) / 8) with (nv / 8 + 1) by (apply Z.div_unique with (nv mod 8 - 1); clear -DN MN PARB; lia). clear. lia.
    - replace ((nv + 8 - 1) / 8) with (nv / 8) by (apply Z.div_unique with 7; clear -DN MN PARB; lia). clear. lia. }

  assert (DUK : forall o, In o RS -> ob_dflt o = DUnknown \/ ob_dflt o = DZero).
  { intros o Ho. unfold RS, RSF in Ho. apply in_app_or in Ho as [Ho|Ho]; [|apply in_app_or in Ho as [Ho|Ho]; [|apply in_app_or in Ho as [Ho|Ho]]].
    - cbn [In] in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [ob_dflt O_fill O_4z O_3b O_3 O_1]; first [left; reflexivity | right; reflexivity].
    - cbn [In] in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; left; reflexivity.
    - cbn [In] in Ho. destruct Ho as [<-|[<-|[<-|[]]]]; cbn [ob_dflt O_Mlo O_Mhi O_pxF]; [right; reflexivity | right; reflexivity | exact Hdpx].
    - destruct partial; cbn [In] in Ho; [destruct Ho as [<-|[]]; left; reflexivity | destruct Ho]. }
  assert (INL : forall o, In o ([O_fill nx; O_4z nx; O_3b nx; O_3 nx; O_1 nx] ++ [O_seciF c1; O_secsF c2; O_secmF; O_secgF c4; O_san; O_oom; O_errno; O_stF c5] ++ [O_Mlo nx mc; O_Mhi nx; O_pxF blk dpx xc]) -> In o RS).
  { intros o Ho. unfold RS, RSF. apply in_app_or in Ho as [Ho|Ho]; [apply in_or_app; left; exact Ho|].
    apply in_app_or in Ho as [Ho|Ho]; apply in_or_app; right; apply in_or_app; [left; exact Ho | right; apply in_or_app; left; exact Ho]. }
  assert (PRESo : forall o z, In o RS -> fst (obj_range rhoE o) <= z < snd (obj_range rhoE o) -> exists bb, v3 z = Some bb) by (intros o z Ho Hz; exact (AOP o z Ho (DUK o Ho) Hz)).
  assert (PRES : forall z, chg_s G ua L pw blk z -> exists b, v3 z = Some b).
  { intros z [X|[X|[[X|X]|X]]].
    - unfold zimg in X. destruct X as [X|[X|[X|X]]].
      + destruct (Z_lt_dec z (SEC_INST + 64)) as [L1|L1]; [|destruct (Z_lt_dec z 0xee040) as [L2|L2]].
        * apply (PRESo (O_seciF c1) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_seci; cbn [fst snd]; clear -X L1; lia].
        * apply (PRESo (O_secsF c2) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_secs; cbn [fst snd]; clear -X L1 L2; lia].
        * apply (PRESo O_secmF z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_secm; cbn [fst snd]; clear -X L2; lia].
      + apply (PRESo (O_secgF c4) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_secg; cbn [fst snd]; exact X].
      + apply (PRESo O_oom z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_oom; cbn [fst snd]; clear -X; lia].
      + apply (PRESo O_errno z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_errno; cbn [fst snd]; exact X].
    - apply (PRESo (O_stF c5) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_st; cbn [fst snd]; exact X].
    - destruct (Z_lt_dec z (ua + 6144)) as [L1|L1]; [|destruct (Z_lt_dec z (ua + 10240)) as [L2|L2]].
      + apply (PRESo (O_Mlo nx mc) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_Mlo; cbn [fst snd]; clear -X L1; lia].
      + apply (PRESo (O_fill nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_fill; cbn [fst snd]; unfold ub; clear -L1 L2; lia].
      + apply (PRESo (O_Mhi nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_Mhi; cbn [fst snd]; clear -X L2; lia].
    - destruct (Z_lt_dec z (Sh ua + 512)) as [L1|L1]; [|destruct (Z_lt_dec z (Sh ua + 768)) as [L2|L2]; [|destruct (Z_lt_dec z (Sh ua + 768 + nv / 8)) as [L3|L3]]].
      + apply (PRESo (O_1 nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_1; cbn [fst snd]; clear -X L1; lia].
      + apply (PRESo (O_3 nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_3; cbn [fst snd]; clear -L1 L2; lia].
      + apply (PRESo (O_4z nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_4z; cbn [fst snd]; clear -L2 L3; lia].
      + destruct (Z_lt_dec z (Sh ua + v8 + 256)) as [L4|L4].
        *
          destruct partial eqn:EP; [|exfalso; clear -L3 L4 EV8; lia].
          apply (PRESo (O_Pf9 nx) z); [unfold RS, RSF; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; left; reflexivity | rewrite RG_P; cbn [fst snd]; clear -L3 L4 EV8; lia].
        * apply (PRESo (O_3b nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_3b; cbn [fst snd]; clear -X L4; lia].
    - apply (PRESo (O_pxF blk dpx xc) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_px; cbn [fst snd]; exact X]. }

  set (K_san := ((SLit 0, 0xe9b28, 0xe9b30, [(0xe9b28, 8%nat, SLit 0x1a36f)]) : carve_spec)).
  assert (ESAN : carve_obj K_san = O_san) by reflexivity.
  assert (SM_san : spec_small K_san) by (unfold K_san, spec_small; split; [lia|]; split; [lia|]; split; [lia|]; unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia).
  assert (INR : forall x : word, in_ranges rhoE R x ->
            (exists k, In k (N_m1 ++ [K_san]) /\ fst (spec_range rhoE k) <= bv_unsigned x < snd (spec_range rhoE k))
            \/ chg_s G ua L pw blk (bv_unsigned x) \/ bv_unsigned x = 0x173661).
  { intros x (o & HoR & Hr). unfold R in HoR. apply in_app_or in HoR as [HoR|HoR].
    - left. rewrite <- N_m1_ok in HoR. apply in_map_iff in HoR as (k & <- & Hk). exists k. split; [apply in_or_app; left; exact Hk|].
      rewrite (carve_range rhoE k (proj1 (Forall_forall _ _) N_m1_small k Hk)) in Hr. exact Hr.
    - set (z := bv_unsigned x) in *.
      assert (RUNZ : Sh ua <= z < Sh ua + L / 8 -> chg_s G ua L pw blk z) by (intros X; right; right; left; right; exact X).
      assert (MAPZ : ua <= z < ua + L -> chg_s G ua L pw blk z) by (intros X; right; right; left; left; exact X).
      assert (IMGZ : zimg z -> chg_s G ua L pw blk z) by (intros X; left; exact X).
      unfold RS, RSF in HoR. apply in_app_or in HoR as [HoR|HoR]; [|apply in_app_or in HoR as [HoR|HoR]; [|apply in_app_or in HoR as [HoR|HoR]]].
      + cbn [In] in HoR. destruct HoR as [<-|[<-|[<-|[<-|[<-|[]]]]]]; right; left.
        * rewrite RG_fill in Hr. cbn [fst snd] in Hr. apply MAPZ. unfold ub in Hr. clear -Hr LB HN. lia.
        * rewrite RG_4z in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr L8B. lia.
        * rewrite RG_3b in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr V512. lia.
        * rewrite RG_3 in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr L8B NP. lia.
        * rewrite RG_1 in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr L8B NP. lia.
      + cbn [In] in HoR. destruct HoR as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
        * right; left. apply IMGZ. rewrite RG_seci in Hr. cbn [fst snd] in Hr. unfold zimg, SEC_INST in *. clear -Hr. lia.
        * right; left. apply IMGZ. rewrite RG_secs in Hr. cbn [fst snd] in Hr. unfold zimg, SEC_INST in *. clear -Hr. lia.
        * right; left. apply IMGZ. rewrite RG_secm in Hr. cbn [fst snd] in Hr. unfold zimg, SEC_INST in *. clear -Hr. lia.
        * right; left. apply IMGZ. rewrite RG_secg in Hr. cbn [fst snd] in Hr. unfold zimg in *. clear -Hr. lia.
        * left. exists K_san. split; [apply in_or_app; right; left; reflexivity|]. rewrite <- (carve_range rhoE K_san SM_san), ESAN. exact Hr.
        * rewrite RG_oom in Hr. cbn [fst snd] in Hr. destruct (Z.eq_dec z 0x173660) as [E0|NE0]; [right; left; apply IMGZ; unfold zimg; clear -E0; lia | right; right; clear -Hr NE0; lia].
        * right; left. apply IMGZ. rewrite RG_errno in Hr. cbn [fst snd] in Hr. unfold zimg. clear -Hr. lia.
        * right; left. right; left. rewrite RG_st in Hr. exact Hr.
      + cbn [In] in HoR. destruct HoR as [<-|[<-|[<-|[]]]]; right; left.
        * rewrite RG_Mlo in Hr. cbn [fst snd] in Hr. apply MAPZ. clear -Hr UAB. lia.
        * rewrite RG_Mhi in Hr. cbn [fst snd] in Hr. apply MAPZ. clear -Hr. lia.
        * rewrite RG_px in Hr. right; right; right. exact Hr.
      + destruct partial; cbn [In] in HoR; [|destruct HoR]. destruct HoR as [<-|[]]. right; left. rewrite RG_P in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr L8B NP. lia. }

  pose proof HRest as (Hsep & _ & _ & _ & _ & _ & _ & _ & HMIs).
  assert (HAg : AInv As rhoE tp md) by exact HA.
  assert (NK : forall k, In k (N_m1 ++ [K_san]) -> In (carve_obj k) R /\ spec_small k /\ spec_covered k
            /\ cells_in_view rhoE (rd_of segs (rm rhoE)) (fst (spec_range rhoE k) - (let '(_, lo, _, _) := k in lo)) (let '(_, _, _, cs) := k in cs)).
  { intros k Hk. apply in_app_or in Hk as [Hk|Hk].
    - split; [unfold R; apply in_or_app; left; rewrite <- N_m1_ok; apply in_map; exact Hk|].
      split; [exact (proj1 (Forall_forall _ _) N_m1_small k Hk)|].
      split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_m1_coverb k Hk)|].
      pose proof (proj1 (Forall_forall _ _) (N_m1_civ AInvA_die As rhoE tp md HAg ltac:(rewrite Bg; exact E151) ltac:(rewrite Bg; exact E152) ltac:(rewrite Bg; exact E153) ltac:(rewrite Bg; exact E154)
                                               ltac:(rewrite Bg; exact E155) ltac:(rewrite Bg; exact E156)) k Hk) as CV. cbn beta in CV.
      destruct k as [[[base lo] hi] cs]. cbn [spec_range fst]. replace (bv_unsigned (eval rhoE base) + lo - lo) with (bv_unsigned (eval rhoE base)) by (clear; lia). exact CV.
    - destruct Hk as [<-|[]].
      split; [unfold R; apply in_or_app; right; rewrite ESAN; apply INL; cbn [app In]; repeat (first [left; reflexivity | right])|].
      split; [exact SM_san|].
      split; [apply coverb_sound; reflexivity|].
      destruct HMIs as (HMIc & _ & _). pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HMIc))))) as HSAN.
      assert (CSAN : cell_ok (view segs (rm rhoE)) (mkACell (0 + 0xe9b28) 8 0x1a36f)).
      { intros j Hj. specialize (HSAN j Hj). cbn [c_addr c_w RtCells.c_val] in HSAN, Hj |- *. rewrite Bg in HSAN. fold G in HSAN.
        rewrite maskv_out in HSAN by (apply (fs_footb_img G _ HG); clear -Hj; lia). exact HSAN. }
      cbn [spec_range fst K_san]. replace (bv_unsigned (eval rhoE (SLit 0)) + 0xe9b28 - 0xe9b28) with 0 by (cbn [eval]; rewrite u64_lit by (clear; lia); clear; lia).
      unfold cells_in_view. apply Forall_cons; [|apply Forall_nil].
      exact (civ_cell rhoE (rm rhoE) 0 0xe9b28 8 0x1a36f (SLit 0x1a36f) CSAN eq_refl ltac:(clear; lia) ltac:(cbn; clear; lia)). }
  assert (VO : forall z, ~ chg_s G ua L pw blk z -> v3 z = vE z).
  { intros z Hz. unfold v3, vE. destruct (Z_le_dec 0 z) as [l|n]; [destruct (Z_lt_dec z (2 ^ 64)) as [l0|n]|].
    2,3: rewrite !view_out by (clear -n; lia) || rewrite !view_out by (clear -n l; lia); reflexivity.
    rewrite !view_in by (clear -l l0; lia).
    destruct (in_ranges_dec rhoE R (Z_to_bv 64 z)) as [Hin|Hout].
    - destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc|E1]]; rewrite ?u64_lit in * by (clear -l l0; lia).
      + unfold rho3. exact (absorb_specs_view rhoE _ tr (vms md tp ms) (vmd md) K R (N_m1 ++ [K_san]) (rd_of segs (rm rhoE)) Hsm1 eq_refl NK z k Hk Hr).
      + exfalso. exact (Hz Hc).
      +
        assert (IN_oom : In O_oom R) by (apply INRS; apply INL; cbn [app In]; repeat (first [left; reflexivity | right])).
        destruct (AO _ IN_oom) as (_ & CE & _ & _). change (ob_cells O_oom) with [mkCell (SLit 0x173661) 1 (SLit 1)] in CE.
        destruct (CE _ (or_introl eq_refl)) as (_ & _ & CEj). pose proof (CEj 0%nat ltac:(cbn; clear; lia)) as X. clear CEj.
        change (ob_base O_oom) with (SLit 0) in X. cbn [c_off c_width SymState.c_val eval] in X. change (Z.to_nat 1) with 1%nat in X. change (Z.of_nat 0) with 0 in X.
        rewrite soff_lit_small, (u64_lit 0), Z.add_0_r in X by (clear; lia). rewrite Z.add_0_l in X. rewrite E1. unfold rho3.
        transitivity (Some (nth 0 (enc_bytes 1 (Z_to_bv 64 1)) (Z_to_bv 8 0))); [exact X|]. symmetry.
        destruct HMIs as (HMIc & _ & _). pose proof (Forall_inv HMIc) as C9. specialize (C9 0%nat ltac:(cbn; clear; lia)).
        cbn [c_addr c_w RtCells.c_val Z.of_nat] in C9. rewrite Z.add_0_r in C9. rewrite Bg in C9. fold G in C9.
        rewrite maskv_out in C9 by (apply (fs_footb_img G _ HG); clear; lia). rewrite view_in in C9 by (clear; lia). exact C9.
    - unfold rho3, rd_of. rewrite rm_absorb_out by exact Hout. reflexivity. }
  assert (RMO : forall x, 0 <= x < 2 ^ 64 -> ~ rt_zoneM G x -> ~ chg_s G ua L pw blk x -> ~ in_rangesZ IMG_S x -> rm rho3 (Z_to_bv 64 x) = rm rhoE (Z_to_bv 64 x)).
  { intros x Bx Hz1 Hz2 Hz4. unfold rho3. apply rm_absorb_out. intros Hin.
    destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc|E1]]; rewrite ?u64_lit in * by exact Bx.
    - apply in_app_or in Hk as [Hk|Hk].
      + apply Hz1. exact (N_m1_zone G rhoE k x HG E151 E152 Hk Hr).
      + destruct Hk as [<-|[]]. apply Hz4. cbn [spec_range fst snd K_san eval] in Hr. rewrite (u64_lit 0) in Hr by (clear; lia).
        unfold IMG_S, in_rangesZ. exists 0xe9b28, 8. split; [right; right; left; reflexivity | clear -Hr; lia].
    - exact (Hz2 Hc).
    - apply Hz4. unfold IMG_S, in_rangesZ. exists 0x173660, 2. split; [right; right; right; left; reflexivity | clear -E1; lia]. }
  assert (RWR : Forall (fun o => dflt_writable (ob_dflt o) = true) R).
  { unfold R. apply Forall_app. split.
    - pose proof (R9_writable [] [] []) as X. unfold R9 in X. apply Forall_app in X. exact (proj1 X).
    - apply Forall_forall. intros o Ho. destruct (DUK o Ho) as [E|E]; rewrite E; reflexivity. }
  assert (DEFM : forall x, IMG_HI <= x < 2 ^ 64 -> rm rhoE (Z_to_bv 64 x) <> None -> rm rho3 (Z_to_bv 64 x) <> None).
  { intros x Bx Hd. destruct (in_ranges_dec rhoE R (Z_to_bv 64 x)) as [Hin|Hout].
    - unfold rho3. apply (absorb_defined rhoE _ tr (vms md tp ms) (vmd md) K R (Z_to_bv 64 x) Hsm1 eq_refl RWR Hin). rewrite u64_lit by (unfold IMG_HI in Bx; clear -Bx; lia). exact (proj1 Bx).
    - unfold rho3. rewrite rm_absorb_out by exact Hout. exact Hd. }
  assert (DEFB : forall x, SHADOW_BAND_LO <= x < SHADOW_BAND_HI -> rm rhoE (Z_to_bv 64 x) <> None -> rm rho3 (Z_to_bv 64 x) <> None).
  { intros x Bx. apply DEFM. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI in *. clear -Bx. lia. }

  assert (HPDs : pendS As ua L md).
  { destruct HP as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12). unfold pendS. rewrite Bg, Bs. fold G.
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|].
    split; [exact Q9|]. split; [exact Q10|]. split; [exact Q11|]. exact HDB. }
  assert (HKMs : idx + 1 <= aa_Km As) by (rewrite BKm; unfold idx; clear -HL9; lia).
  pose proof (sec_rebuild As rhoE rho3 tp md nv ua blk HA HN) as RB. cbn zeta in RB. rewrite Bg, Bs in RB. fold G idx L ub pw v3 vE in RB.
  specialize (RB HPDs (proj1 Hblk) HROOM HKMs C0 C8 C16 C24 CPW CI0 CI8 CI16 CI24 C48 C56 CMU VH2 VHN VH0 VH1 VMG0 VMG8 VZ VP PRES VO DEFB).
  pose proof (sec_kept CST XGL HCST HXGL HCSTM HCSTS As rhoE rho3 tp md nv ua blk HA HN) as KP. cbn zeta in KP. rewrite Bg, Bs in KP. fold G idx L pw in KP.
  specialize (KP HPDs (proj1 Hblk) HROOM RMO DEFB).

  set (A1 := ax_setS (ax_setS F (set_objs (ax_S F) (K ++ R))) (set_objs (ax_S (ax_setS F (set_objs (ax_S F) (K ++ R)))) K)) in Hb.
  assert (EV3 : forall e, eval rho3 e = eval rhoE e) by (intros e; unfold rho3; apply eval_absorb).
  assert (OR3 : forall o, obj_range rho3 o = obj_range rhoE o) by (intros o; unfold obj_range, obj_lo_of, obj_hi_of, soff; rewrite !EV3; reflexivity).
  assert (HFXP : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rhoE p) by (intros p Hp; exact (proj1 (Forall_forall _ _) HFacts p (FPF p Hp))).
  assert (Hhigh : holds rhoE F_sp_high) by (apply HFXP; apply in_or_app; right; unfold pre_facts; cbn [app In]; right; left; reflexivity).
  destruct (sw_range_gen segs rhoE (set_objs (ax_S F) (K ++ R)) _ (sw9 swc) Hsm1 ltac:(cbn; left; reflexivity) eq_refl Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG G <= fst (obj_range rhoE (sw9 swc))) by (rewrite (sw_lo_gen rhoE (sw9 swc) eq_refl); exact Htop).
  assert (LNK : Forall (fun o => topG G + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG G)); [|clear -SW0 SW2 SW3; lia|clear -ACV; lia]. apply Forall_forall. intros p Hp. apply HFXP. apply in_or_app. left. exact (chain_pre_factsS W st p HW Hp). }
  pose proof HP as (_ & _ & _ & PDI & _). destruct PDI as (_ & _ & PDT & _ & PDB). fold G in PDT. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in PDB.

  assert (KDISJ : forall lo hi, 6578176 <= lo -> hi <= topG G -> Forall (fun o' => ranges_disjoint (obj_range rhoE o') (lo, hi)) K).
  { intros lo hi Hlo Hhi. unfold K, KEPTF. constructor.
    - unfold ranges_disjoint. right; right; right. cbn [fst snd]. clear -SW0 Hhi. lia.
    - apply Forall_app. split.
      + eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B1 & L1 & H1). cbn [ob_base ob_lo ob_hi] in B1, L1, H1. subst olo ohi.
        unfold ranges_disjoint. rewrite obj_range_mk by (clear; lia). cbn [fst snd]. right; right; right. clear -B1 Hhi. lia.
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil;
          unfold ranges_disjoint; rewrite obj_range_mk by (clear; lia); cbn [fst snd eval]; rewrite u64_lit by (clear; lia); right; right; left; clear -Hlo; lia. }
  assert (RM3 : forall z, ua <= z < ua + L \/ Sh ua <= z < Sh ua + L / 8 -> rm rho3 (Z_to_bv 64 z) <> None).
  { intros z Hz. assert (CZ : chg_s G ua L pw blk z) by (right; right; left; exact Hz). destruct (PRES z CZ) as [bb Hbb].
    assert (BZ : 0x646000 <= z < 2 ^ 64) by (destruct Hz as [Hz|Hz]; [clear -Hz UAB; lia | clear -Hz SHB; lia]).
    unfold v3 in Hbb. rewrite view_in in Hbb by (clear -BZ; lia). rewrite (rd_off_image _ _ _ BZ Hbb). discriminate. }
  assert (Hcv : SPA segs KJ (ax_setS A1 (set_objs (ax_S F) (K ++ [O_UBs nx]))) rho3 tp (tr, {| cfg_ms := ms; cfg_model := md |})).
  { pose proof (SPA_carve_zero_sym segs KJ rho3 A1 tp _ (UBs nx) (SLit 0) (SVar 12) (ss_next (ax_S A1)) Hb) as CV. cbn zeta in CV.
    rewrite !EV3 in CV. unfold soff in CV. rewrite !EV3 in CV. fold (soff rhoE (SLit 0)) (soff rhoE (SVar 12)) in CV.
    rewrite (SOL 0 ltac:(clear; lia)), EUB in CV. rewrite (soff_of_val rhoE (SVar 12) nv) in CV by (first [rewrite EN12; apply u64_lit; clear -HN; lia | clear -HN; lia]).
    apply CV; clear CV.
    - exact WCU.
    - apply Pos.le_refl.
    - clear -HN. lia.
    - clear -HN. lia.
    - unfold ub. clear -UAB. lia.
    - unfold ub. clear -UAB LB. lia.
    - change (ss_objs (ax_S A1)) with K. eapply Forall_impl; [|exact (KDISJ (ub + 0) (ub + nv) ltac:(unfold ub; clear -UAB; lia) ltac:(unfold ub; clear -LB PDT; lia))].
      intros o Ho. rewrite OR3. exact Ho.
    - intros z Hz. pose proof (RM3 z ltac:(left; unfold ub in Hz; clear -Hz LB; lia)) as D.
      assert (ZZ : rd_of segs (rm rho3) (Z_to_bv 64 z) = Some (Z_to_bv 8 0)).
      { destruct (Z_lt_dec z (ua + 10240)) as [L2|L2].
        - apply (AOZ (O_fill nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity | rewrite RG_fill; cbn [fst snd]; unfold ub in *; clear -Hz L2; lia].
        - apply (AOZ (O_Mhi nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity | rewrite RG_Mhi; cbn [fst snd]; unfold ub in *; clear -Hz L2 LB; lia]. }
      split; [|exact ZZ]. unfold wok_of. destruct (rm rho3 (Z_to_bv 64 z)) as [x|]; [reflexivity | exfalso; exact (D eq_refl)].
    - intros rr y j Hin. change (ax_X A1) with (ax_X F) in Hin. rewrite XFn in Hin. destruct Hin. }

  pose proof (SPA_select segs KJ rho3 _ (idxsU nW) tp _ Hcv NDU
                ltac:(intros i Hi; apply Nat.ltb_lt; exact (proj1 (forallb_forall _ _) BNDU i Hi))
                ltac:(intros i Hi; pose proof (proj1 (forallb_forall _ _) COVU i ltac:(apply in_seq; exact (conj (Nat.le_0_l i) Hi))) as X;
                      apply existsb_exists in X as (i' & Hi' & E); apply Nat.eqb_eq in E; subst i'; exact Hi')) as Hsu.
  cbn [ax_S ax_setS ss_objs set_objs] in Hsu. rewrite SELU in Hsu. clear Hcv.

  match type of Hsu with SPA _ _ ?AU _ _ _ => set (A2 := AU) in Hsu end.
  assert (Hc : SPA segs KJ (ax_setS A2 (S2F F KU)) rho3 tp (tr, {| cfg_ms := ms; cfg_model := md |})).
  { eapply SPA_restate; [exact W9 | exact D9 | reflexivity | | constructor | exact Hsu].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; clear; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. pose proof (geom_old _ HG) as HGt. destruct HGt as (_ & _ & _ & G4' & _). unfold G in G4'. rewrite G4'. reflexivity. }
  clear Hsu.

  assert (EUB3 : bv_unsigned (eval rho3 (UBs nx)) = ub) by (rewrite EV3; exact EUB).
  assert (E12_3 : bv_unsigned (eval rho3 (SVar 12)) = nv) by (rewrite EV3, EN12; apply u64_lit; clear -HN; lia).
  assert (RGUB : obj_range rhoE (O_UBs nx) = (ub, ub + nv)).
  { unfold O_UBs, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_of_val rhoE (SVar 12) nv) by (first [rewrite EN12; apply u64_lit; clear -HN; lia | clear -HN; lia]). rewrite EUB. f_equal. clear. lia. }
  assert (OUTK : forall z, SHADOW_OFF <= z < 17594333495296 -> outside_all rho3 KU (Z_to_bv 64 z)).
  { intros z Hz. unfold SHADOW_OFF in Hz. unfold KU, KUB, outside_all. rewrite u64_lit by (clear -Hz; lia). apply Forall_app. split; [constructor|apply Forall_app; split].
    - cbn zeta. rewrite OR3. clear -SW0 SW3 Hz ACV. lia.
    - eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B1 & L1 & H1). cbn [ob_base ob_lo ob_hi] in B1, L1, H1. subst olo ohi.
      cbn zeta. rewrite OR3, obj_range_mk by (clear; lia). cbn [fst snd]. clear -B1 Hz ACV. lia.
    - constructor; [|constructor]. cbn zeta. rewrite OR3, RGUB. cbn [fst snd]. unfold ub. clear -Hz PDB LB UAB. lia.
    - unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil; cbn zeta;
        rewrite obj_range_mk by (clear; lia); cbn [fst snd eval]; rewrite u64_lit by (clear; lia); clear -Hz; lia. }
  assert (UA8 : exists q, ua = 4096 * q) by (exists (ua / 4096); pose proof (Z.div_mod ua 4096 ltac:(clear; lia)) as X; rewrite AL, Z.add_0_r in X; exact X).
  destruct UA8 as [qu Hqu].
  assert (L8q : exists q, L = 4096 * q) by (exists (L / 4096); pose proof (Z.div_mod L 4096 ltac:(clear; lia)) as X; rewrite SMM, Z.add_0_r in X; exact X).
  destruct L8q as [ql Hql].
  assert (ESHua : Sh ua = 512 * qu + SHADOW_OFF) by (unfold Sh; rewrite Hqu; replace (4096 * qu) with (512 * qu * 8) by (clear; lia); rewrite Z.div_mul by (clear; lia); reflexivity).
  assert (EL8 : L / 8 = 512 * ql) by (rewrite Hql; replace (4096 * ql) with (512 * ql * 8) by (clear; lia); apply Z.div_mul; clear; lia).
  assert (Hd : SPA segs KJ (ax_setX (ax_setS A2 (S2F F KU)) ((UBs nx, SVar 12) :: ax_X (ax_setS A2 (S2F F KU)))) rho3 tp (tr, {| cfg_ms := ms; cfg_model := md |})).
  { apply SPA_x_publish; [exact XB9 | | exact Hc].
    change (ax_base (ax_setS A2 (S2F F KU))) with (ax_base F). rewrite BFb. change (ss_objs (ax_S (ax_setS A2 (S2F F KU)))) with KU.
    unfold xr_ok. cbn [fst snd]. rewrite EUB3, E12_3. unfold base_sv. cbn [eval]. rewrite u64_lit by (unfold SHADOW_OFF; clear; lia).
    split; [unfold ub; rewrite Hqu; apply Z.mod_divide; [clear; lia|]; exists (512 * qu + 768); clear; lia|].
    split; [unfold ub; clear -UAB LB; lia|].
    intros x Hx.
    pose proof (Z.div_mod x 8 ltac:(clear; lia)) as DMa. pose proof (Z.mod_pos_bound x 8 ltac:(clear; lia)) as MBa.
    pose proof (Z.div_mod nv 8 ltac:(clear; lia)) as DMn. pose proof (Z.mod_pos_bound nv 8 ltac:(clear; lia)) as MBn.
    set (pa := x / 8) in *.
    assert (PA : 512 * qu + 768 <= pa /\ 8 * pa <= x /\ pa <= 512 * qu + 768 + nv / 8 /\ (pa = 512 * qu + 768 + nv / 8 -> nv mod 8 <> 0)).
    { unfold ub in Hx. rewrite Hqu in Hx. clear -Hx DMa MBa DMn MBn. lia. }
    assert (SHA : SHADOW_OFF + pa = Sh ub + (pa - 512 * qu - 768)) by (rewrite ESHub, ESHua; clear; lia).
    assert (INRUN : Sh ua <= SHADOW_OFF + pa < Sh ua + L / 8) by (rewrite ESHua; clear -PA L8B; lia).
    split; [clear -INRUN SHB; lia|].
    split; [unfold shadow_addr; fold pa; apply OUTK; clear -INRUN SHB; unfold SHADOW_OFF in *; lia|].
    split.
    { intros j Hj. unfold word_byte.
      assert (WIN : Sh ua <= (SHADOW_OFF + pa) / 8 * 8 + j < Sh ua + L / 8).
      { pose proof (Z.div_mod (SHADOW_OFF + pa) 8 ltac:(clear; lia)) as DMs. pose proof (Z.mod_pos_bound (SHADOW_OFF + pa) 8 ltac:(clear; lia)) as MBs.
        rewrite ESHua, EL8 in INRUN |- *. unfold SHADOW_OFF in *.
        assert (Q1 : 64 * qu + 268431360 <= (2147450880 + pa) / 8) by (apply Z.div_le_lower_bound; [clear; lia | clear -INRUN; lia]).
        assert (Q2 : (2147450880 + pa) / 8 < 64 * qu + 268431360 + 64 * ql) by (apply Z.div_lt_upper_bound; [clear; lia | clear -INRUN; lia]).
        clear -Q1 Q2 Hj. lia. }
      split; [apply OUTK; clear -WIN SHB; unfold SHADOW_OFF in *; lia | apply RM3; right; exact WIN]. }
    destruct (Z_lt_dec (pa - 512 * qu - 768) (nv / 8)) as [LT|GE].
    - exists (Z_to_bv 8 0). split; [|left; reflexivity].
      unfold shadow_addr. fold pa. rewrite SHA. pose proof (VZ (pa - 512 * qu - 768) ltac:(clear -LT PA; lia)) as X. unfold v3 in X.
      rewrite view_in in X by (rewrite <- SHA; clear -INRUN SHB; lia).
      refine (rd_off_image _ _ _ _ X). rewrite <- SHA. clear -INRUN SHB. lia.
    - assert (EQ : pa - 512 * qu - 768 = nv / 8 /\ nv mod 8 <> 0) by (split; [clear -GE PA; lia | apply (proj2 (proj2 (proj2 PA))); clear -GE PA; lia]).
      destruct EQ as [EQ NZ]. exists (Z_to_bv 8 (nv mod 8)). split.
      + unfold shadow_addr. fold pa. rewrite SHA, EQ. pose proof (VP NZ) as X. unfold v3 in X.
        rewrite view_in in X by (rewrite <- EQ, <- SHA; clear -INRUN SHB; lia).
        refine (rd_off_image _ _ _ _ X). rewrite <- EQ, <- SHA. clear -INRUN SHB. lia.
      + right. split.
        * rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small (nv mod 8) 256) by (clear -MBn; lia).
          unfold ub. rewrite Hqu. replace (4096 * qu + 6144 + nv) with (nv + (512 * qu + 768) * 8) by (clear; lia). rewrite Z_mod_plus_full. reflexivity.
        * fold pa. unfold ub. rewrite Hqu. replace (4096 * qu + 6144 + nv) with (nv + (512 * qu + 768) * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear -EQ. lia. }
  clear Hc.

  change (ax_setX (ax_setS A2 (S2F F KU)) ((UBs nx, SVar 12) :: ax_X (ax_setS A2 (S2F F KU))))
    with (mkAX (S2F F KU) ((UBs nx, SVar 12) :: ax_X F) (ax_base F)) in Hd.
  rewrite XFn, BFb in Hd. change (mkAX (S2F F KU) [(UBs nx, SVar 12)] base_sv) with (XF_of F KU nx) in Hd.
  pose proof (smatchA_entails segs (XF_of F KU nx) (Lc_ok W st) s9 rho3 tp _ ENT9 (proj1 Hd)) as Hsm4.
  set (rho4 := rho_sub rho3 s9) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoE k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ (wsub_idc_below _ SID9) Hk). cbn [eval]. unfold rho3. cbn [rho_absorb rw]. reflexivity. }
  assert (E110 : bv_unsigned (rw rho4 V_RES) = ub). { unfold rho4. cbn [rho_sub rw]. rewrite G110. exact EUB3. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 s9).
  pose proof (rhoM_agree A rho) as (RMw & RMl & RMm).
  assert (LOWE : forall k, (k < NF)%positive -> rw rhoE k = rw rho0 k).
  { intros k Hk. rewrite <- (Hagw k) by (unfold GW, NF in *; clear -Hk; lia). rewrite <- (RMw k Hk). exact (HLw k). }

  assert (CLE : forall x, client_addrA CST As x <-> client_addrA CST A x).
  { intros x. unfold client_addrA, client_mut_addrA, aa_frames, frame_flag. rewrite Bl, Bfb, Bg. cbn [aa_live aa_fs_busy aa_geom bumpV]. split; intros X; exact X. }
  assert (CLE' : forall x, client_addrA CST A x -> client_addrA CST (secA As ua nv) x).
  { intros x Hx. apply (proj2 (CLE x)) in Hx. unfold client_addrA, client_mut_addrA, aa_frames, frame_flag in Hx |- *. cbn [aa_live aa_fs_busy aa_geom secA].
    destruct Hx as [[X|[X|[X|X]]]|X]; [left; left; exact X | left; right; left | left; right; right; left; exact X | left; right; right; right; exact X | right; exact X].
    destruct X as (b & n & Hbn & Hb0). exists b, n. split; [right; exact Hbn | exact Hb0]. }
  apply (LQPA_intro segs NF rho0 tp0 _ (Lc_ok W st) (JLc_ok CST XGL A Kc) rho4 tp _ KJ).
  - exact HPin.
  - split; [exact Hsm4 | exact HK].
  - split.
    + intros i Hi. rewrite (Hlow i Hi), (LOWE i Hi). reflexivity.
    + intros l. unfold rho4. cbn [rho_sub rl]. unfold rho3. cbn [rho_absorb rl]. rewrite (Erl l). symmetry. exact (HLl l).
  - intros _. unfold JLc_ok. split.
    2:{ split; unfold rho4; cbn [rho_sub rw]; [rewrite (wsub_idc_143 _ SID9) | rewrite (wsub_idc_144 _ SID9)]; cbn [eval]; unfold rho3; cbn [rho_absorb rw].
        - rewrite <- (Hagw 143%positive) by (unfold GW; clear; lia). rewrite (rhoM_of_keep A rho 143%positive) by tauto. exact (HLw 143%positive).
        - rewrite <- (Hagw 144%positive) by (unfold GW; clear; lia). rewrite (rhoM_of_keep A rho 144%positive) by tauto. exact (HLw 144%positive). }
    unfold JL_malloc_ok. cbn [w_tr w_cfg cfg_model].
    exists (secA As ua nv), [], (aa_live A). cbn [app].
    assert (E12_0 : bv_unsigned (rw rho0 12%positive) = nv) by (rewrite <- (HLw 12%positive); reflexivity).
    split; [unfold AInv, AInvA in RB |- *; rewrite Erm4; exact RB|].
    split; [cbn [aa_live secA]; rewrite Bl, E110, E12_0; reflexivity|].
    split; [reflexivity|].
    split; [unfold aa_frames; cbn [aa_fs_busy secA]; rewrite Bfb; reflexivity|].
    split; [cbn [aa_V secA]; rewrite BV, E12_0; reflexivity|].
    split; [cbn [aa_Km secA]; rewrite BKm; reflexivity|]. split; [cbn [aa_Kf secA]; rewrite BKf; reflexivity|]. split; [cbn [aa_geom secA]; exact Bg|].
    split.
    {
      destruct HKEPT0 as [K01 K02]. destruct KP as [KP1 KP2]. rewrite Erm4. split.
      - intros x Bx Hcl.
        assert (EQ0 : rm rho (Z_to_bv 64 x) = rm rho0 (Z_to_bv 64 x)).
        { apply (K01 x Bx). destruct Hcl as [(X & _ & NE)|(X & _ & DEF)]; [left; exact (conj X (conj X NE)) | right; exact (conj X (conj X DEF))]. }
        assert (Hcl' : (client_addrA CST As x /\ client_addrA CST (secA As ua nv) x /\ ~ errno_addrA x)
                       \/ (client_shadowA CST XGL As x /\ client_shadowA CST XGL (secA As ua nv) x /\ rm rhoE (Z_to_bv 64 x) <> None)).
        { destruct Hcl as [(X & Y & NE)|(X & Y & DEF)].
          - left. split; [apply (proj2 (CLE x)); exact X | exact (conj Y NE)].
          - right. split; [|split; [exact Y | rewrite ErmF, EQ0; exact DEF]].
            destruct X as [(y & Y1 & Y2)|Y']; [left; exists y; split; [apply (proj2 (CLE y)); exact Y1 | exact Y2] | right; exact Y']. }
        rewrite (KP1 x Bx Hcl'). rewrite ErmF. exact EQ0.
      - intros xx jj Hx Hj Hdef. apply (KP2 xx jj); [| exact Hj |].
        + destruct Hx as [[X Y]|X]; [left; split; [apply (proj2 (CLE xx)); exact X | exact Y] | right; exact X].
        + rewrite ErmF. apply (K02 xx jj); [| exact Hj | exact Hdef].
          destruct Hx as [[X Y]|X]; [left; exact (conj X X) | right; exact X]. }
    split; [exact HK|].

    intros c0 Hc0 Hor Hfr. unfold class_fresh in Hfr |- *. cbn [aa_cls secA]. rewrite Bc. exact Hfr.
Qed.

Theorem sec_finish : ltac2:(tb__ "0|5|
S35S5cS15S15S4aQ40M0A1M1S15S6G1A1M2G2S7cS85VW;Vst;A2S5dR9A1S12S0G1S14R9R1A2S14RaR1A2A3Fi;S12S0S6S4aQ8A1A1S1aRaR1A2S1aRbR1A2A3Fl;S5eVCST;VXGL;RdRdS1bRbA1S1bRaA1A6S4cS4dSbS37S36ReA1A2A1S38ReA1A2SdS11S11A2M3S31G3R1S88S3bVBX;S5bR10S49G0S14RdPcM4A2A2A2A1A1A1A3S86R2ScS11S11S49G0RdA2S8eS49G0S14ReG4A2A2A1A4A2F_;Fbn;S80Vsegs;VJG;VBX;R10RfRdRcA5VF;RbR9R8A6S83Vsegs;S7eRfRbS94VCST;VXGL;VW;Vst;R11R10A6R9A6F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Ftp0;FrhoE;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a rhoE tp0 tp w. apply sec_finish_P. unfold PFc. right. left. reflexivity.
Qed.

Variable DF9 : axst.
Hypothesis CertF : ltac2:(tb__ "0|1|
S0S7Sa2Sa6Ufa0S9S11A1Sa9Vnx;A1S5S57VDF9;S9S57A1M0A3S5S57VF;G0A3A6SaA3").
Theorem sec_g48_P : ltac2:(tb__ "0|6|
S7cOF_;S35S5cS15S15S4aQ40M0A1M1S6G1A1M2S6SdS57S84A2M3A1S31G3ScS57S84S92VW;Vst;A2S93VCST;VXGL;R7R6A4A4R1A3S85VW;Vst;A2S8fVW;Vst;A2S5dR9A1S82Vsegs;RcS81RaA1A3S12S0G1S14RaR1A2S14RbR1A2A3Fi;S12S0S6S4aQ8A1A1S1aRbR1A2S1aRcR1A2A3Fl;S5eVCST;VXGL;ReReS1bRcA1S1bRbA1A6S4cS4dSbS37S36RfA1A2A1S38RfA1A2SdS11S11A2M4S31G4R1S88S3bVBX;S5bR11S49G0S14RePcM5A2A2A2A1A1A1A3S86R2ScS11S11S49G0ReA2S8eS49G0S14RfG5A2A2A1A4A2F_;Fbn;S15G2S7dVsegs;R14S80Vsegs;VJG;VBX;R13R12R10RfA5VDF9;R2R1A5S83Vsegs;S7eR11ReRdA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT0 HL9 HDB rhoX tpX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  apply (cfg_soundA segs 4000%nat [] (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx) [DF9] [F] (JG BX A Kc rho a) ok _ tpX Hokf HST CertF); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | | apply triple_refl].
  intros w Hw. exact (sec_finish_P A Kc rho0 rho a rE tp0 tpX w Posts HPin HW HKc HLw HLl HKEPT0 HL9 HDB Hw).
Qed.
Theorem sec_g48 : ltac2:(tb__ "0|5|
S7cOF_;S35S5cS15S15S4aQ40M0A1M1S6G1A1M2S85VW;Vst;A2S8fVW;Vst;A2S5dR7A1S82Vsegs;RaS81R8A1A3S12S0G1S14R8R1A2S14R9R1A2A3Fi;S12S0S6S4aQ8A1A1S1aR9R1A2S1aRaR1A2A3Fl;S5eVCST;VXGL;RcRcS1bRaA1S1bR9A1A6S4cS4dSbS37S36RdA1A2A1S38RdA1A2SdS11S11A2M3S31G3R1S88S3bVBX;S5bRfS49G0S14RcPcM4A2A2A2A1A1A1A3S86R2ScS11S11S49G0RcA2S8eS49G0S14RdG4A2A2A1A4A2F_;Fbn;S15G2S7dVsegs;R12S80Vsegs;VJG;VBX;R11R10ReRdA5VDF9;R2R1A5S83Vsegs;S7eRfRcS94VCST;VXGL;VW;Vst;R11R10A6A5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0. apply sec_g48_P. unfold PFc. right. left. reflexivity.
Qed.
End FIN.

Lemma hpath_a : ltac2:(tb__ "0|6|
S35S35Fx;S35S5cS15S4aQ40M0A1M1S15S6G1A1S6S91A1S90S35S0S3cS39RaR1A1A1S39R1A1A3FX;S35S0S6S37A1S36RbR1A1A1S36R1A1A3FX;S35S0S11S3aRcR1A1A1S4eS3aR1A1M2Sa5A2A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S67S17S1eR8A1S5S17S21S95S19S9aA1S19S9bA1M3A3S9S17A1A3A3ReS5bRdS49G0S14RbPcA2A2A2A1S35S1S1S4cZ8M4Z20000M5A2S4cG5G5A2A2S1S4cS4eS50G4S4dSbS37S36ReA1A2A1A2G5A2G2A2S0G1S1dRaS28S96G3S20Z4000A1A3A2S4bG0S4fG2G4A2A2A3A2A2TAs;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HF. apply Forall_inv in HF. cbn zeta.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & _ & _ & _ & _ & E145 & E146 & E147 & _).
  destruct HJ as (_ & _ & HA & _). pose proof (AInvA_pab _ _ _ _ HA) as X. rewrite BXg, BXs, BXp in X. cbn [aa_geom aa_sec aa_ptr_committed bumpV] in X. cbn zeta in X.
  destruct X as (P1 & P2 & P3 & P4 & P5 & P6 & _).
  rewrite BXp. cbn [aa_ptr_committed bumpV].
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *.
  pose proof (topG_range G) as TG. pose proof (Zle_0_nat (length (aa_sec A))) as NN.
  assert (EDV : (c + kPtrArrayCommit) / 8 = c / 8 + 16384) by (change kPtrArrayCommit with (16384 * 8); apply Z.div_add; lia).
  unfold kPtrArrayReserve, kPtrArrayCommit, PG, IMG_HI in *.
  assert (C17 : c mod 2 ^ 17 = 0).
  { pose proof (Z.mod_add c 1 (2 ^ 17) ltac:(lia)) as MA. rewrite <- MA. rewrite <- P6. f_equal. }
  pose proof (Z.div_mod c (2 ^ 17) ltac:(lia)) as X. rewrite C17, Z.add_0_r in X.
  pose proof (Z.div_mod c 8 ltac:(lia)) as X8.
  assert (C8 : c mod 8 = 0) by (rewrite X; replace (2 ^ 17 * (c / 2 ^ 17)) with ((2 ^ 14 * (c / 2 ^ 17)) * 8) by lia; apply Z_mod_mult).
  rewrite C8, Z.add_0_r in X8.
  cbn [holds eval] in HF. rewrite E147, E146 in HF. fold c in HF.
  assert (C0 : 0 <= c).
  { destruct (Z_lt_le_dec c 0) as [Hneg|]; [exfalso | assumption].
    assert (Ec : c = - 2 ^ 17) by (clear -X Hneg P5 NN; lia).
    assert (En : Z.of_nat (length (aa_sec A)) = 0) by (clear -Ec P5 NN; lia).
    rewrite En, Ec in HF. vm_compute in HF. discriminate HF. }
  pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_le_mono c (2 ^ 23) 8 ltac:(clear -P5; lia) ltac:(clear -P5; lia)) as DM. cbn in DM.
  rewrite bt_eq_lit in HF by (clear -DP DM NN P5; lia). apply Z.eqb_eq in HF.
  assert (HcN : 8 * Z.of_nat (length (aa_sec A)) = c) by (rewrite HF; clear -X8; lia).
  split; [lia|]. split; [clear -HcN; lia|].
  apply bv_eq. cbn [eval]. rewrite E146. fold c. rewrite add_val, !u64_lit by (clear -DP DM; lia). rewrite Z.mod_small by (clear -DP DM; lia).
  rewrite EDV. reflexivity.
Qed.

Lemma hpath_b : ltac2:(tb__ "0|5|
S35S35Fx;S35S5cS15S4aQ40M0A1M1S15S6G1A1S6S91A1S90S35S0S3cS39RaR1A1A1S39R1A1A3FX;S35S0S6S37A1S36RbR1A1A1S36R1A1A3FX;S35S0S11S3aRcR1A1A1S3aR1A1M2A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S67S17S1eR8A1S5S17S22S21S95S19S9aA1S19S9bA1M3A3A1S9S17A1A3A3ReS5bRdS49G0S14RbPcA2A2A2A1S35S1S1S4cZ8M4G4A2S4cG4Z20000A2A2S1S4cS4eS50G4S4dSbS37S36ReA1A2A1A2G4A2G2A2S0G1S1dRaG3A2S4bG0S4fG2G4A2A2A3A2A2TAs;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HF. apply Forall_inv in HF. cbn zeta.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & _ & _ & _ & _ & E145 & E146 & E147 & _).
  pose proof (site_b nW st tmax nx Hnx Pret_ms Pret_ms Pret_ms Pret_ms eq_refl eq_refl BX A Kc rho a r tp tr md BXg BXs BXp HJ HF) as (_ & B1 & B2 & _). cbn zeta in B1, B2.
  rewrite BXp. cbn [aa_ptr_committed bumpV].
  split; [lia|]. split; [clear -B2; lia|]. cbn [eval]. exact E146.
Qed.
End SEC7.
End SpineCallocSec7.

(* [comment removed for export] *)
Module SpineCallocSec6L.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "nil"; "cons"; "prod"; "option"; "Some"; "app"; "pair"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "la_state"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "holds"; "sobj"; "sv"; "ss_next"; "ss_facts"; "SLit"; "SPBranch"; "sprop_below"; "swf"; "SVar"; "rw"; "DUnknown"; "SAlu"; "SPUle"; "cell"; "eval"; "mkObj"; "obj_range"; "rm"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ageom"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec6L.SEC6L"; "F_low"; "F_g7L"; "F_g8L"; "F_g9L"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_GEU"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV"; "F_A"; "L3"; "B3"; "END8"; "RUE"; "UE9"; "a2e6"; "@Stdlib.Lists.List"; "forallb"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_MS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "O_1"; "O_2"; "Pret_ms"; "carveS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "SKEL0"; "range_noband"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Placement StartLib StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require EnsureMapA CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.EnsureMapA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SEC6L.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S41S67VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S4S5cS6cVnx;A2S5A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
S6fVnW;Vst;Vnx;VBX;A4").

Definition F_low : sprop := ltac2:(tb__ "0|0|
S23S22S43S1fVnx;A1S1fS66A1A3S1bZ7fff7000A1A2").

Lemma low_FA : ltac2:(tb__ "0|1|
S2aS2aFx;S2aS30S15S2dQ40A1M0S15S3G0A1S3S3cA1S3bS2aS0S2cS2bRaR1A1A1S2bR1A1A3FX;VJG;RaR9R8R7R6R5R4R3R2A9S16R6S35A2S39S14S16R7A1S4fVnx;A1A3F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg HJ HL.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & Enx & _ & E142 & _ & _ & E155 & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _). cbn zeta in *.
  destruct HJ as (_ & _ & HA & HP & _).
  pose proof (proj1 HA) as HG. rewrite BXg in HG. cbn [aa_geom bumpV] in HG.
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  pose proof (urange a) as Ra. unfold IMG_HI in IMG.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *. set (SB := ag_spacebeg (aa_geom A)) in *.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (RSB : 0 <= SB < 2 ^ 64) by (clear -S1 S2 TG; lia).
  assert (RL : 0 <= L < 2 ^ 64) by (clear -SMB HN; lia).
  unfold F_low in HL. cbn [holds eval] in HL. rewrite Enx, E142, add_val in HL. fold ua L in HL.
  rewrite (u64_lit L RL) in HL. rewrite Z.mod_small in HL by (clear -IMG HTOP SMB; lia). rewrite u64_lit in HL by (clear; lia).
  unfold F_A. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite Enx, E142, E155, add_val. fold ua L SB.
  rewrite (u64_lit L RL), (u64_lit SB RSB). rewrite Z.mod_small by (clear -IMG HTOP SMB; lia). clear -HL S1. lia.
Qed.

Definition F_g7L : list sprop := ltac2:(tb__ "0|0|
S7S14S1cS42S1bZ7fff7fffA1S53Vnx;A1A3S6S14A1A3").
Definition F_g8L : list sprop := ltac2:(tb__ "0|0|
S7S14S1cS42S1bZ7fff7fffA1S52Vnx;A1A3S6S14A1A3").
Definition F_g9L : list sprop := ltac2:(tb__ "0|0|
S7S14S1cS42S1bZ7fff7fffA1S54Vnx;A1A3S6S14A1A3").

Lemma low_end : ltac2:(tb__ "0|2|
S2aS2aF_;S2aS30S15S2dQ40M0A1M1S15S3G1A1S3S3cA1S3bVJG;R9R8R7R6R5R4R3R2R1A9S16R5S35A2S48S49S2eG0R7A2S5aS2eG0S20R8PcA2A2A1A2Z7fff7000A2F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ HL.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & Enx & _ & E142 & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _). cbn zeta in *.
  pose proof (urange a) as Ra. unfold IMG_HI in IMG.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *.
  assert (RL : 0 <= L < 2 ^ 64) by (clear -SMB HN; lia).
  unfold F_low in HL. cbn [holds eval] in HL. rewrite Enx, E142, add_val in HL. fold ua L in HL.
  rewrite (u64_lit L RL) in HL. rewrite Z.mod_small in HL by (clear -IMG HTOP SMB; lia). rewrite u64_lit in HL by (clear; lia). exact HL.
Qed.

Lemma geu_intro : ltac2:(tb__ "0|0|
S15S40S18S1S48Z0R2A2S4aR2S4cZ2Z40A2A2A2S48S2eQ40S25R4R2A2A2R3A2S16R5S1cS42S1bR4A1R3A3A2F_;F_;Fe;Fc;Fr;").
Proof.
  intros r c e Hc H. cbn [holds eval branch_taken]. apply Bool.negb_true_iff. unfold bv_ltu. apply Z.ltb_ge. rewrite u64_lit by exact Hc. exact H.
Qed.

Lemma F_g7L_hold : ltac2:(tb__ "0|1|
S2aS2aF_;S2aS30S15S2dQ40A1M0S15S3G0A1S3S3cA1S3bVJG;R9R8R7R6R5R4R3R2R1A9S16R5S35A2S39S14S16R6A1S36A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ HL. pose proof (low_end BX A Kc rho a r tp tr md HJ HL) as LE.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & AL & IMG & HTOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. unfold IMG_HI in IMG.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). unfold PG in *. lia. }
  unfold F_g7L. apply Forall_cons; [|apply Forall_nil]. apply geu_intro; [clear; lia|]. unfold RUE. cbn [eval].
  rewrite and_val, !add_val, Enx, E12, !u64_lit by lia. fold ua nv.
  rewrite (Z.mod_small (ua + 6144)) by (clear -Ra HTOP SMB; lia). rewrite (Z.mod_small (ua + 6144 + nv)) by (clear -Ra HTOP LB HN SMB; lia).
  rewrite (Z.mod_small (ua + 6144 + nv + 7)) by (clear -Ra HTOP LB HN SMB; lia).
  rewrite (land_m8E nW st tmax nx Hnx) by (clear -Ra HTOP LB HN SMB; lia). pose proof (Z.mod_pos_bound (ua + 6144 + nv + 7) 8 ltac:(lia)) as MB. clear -MB LE LB. lia.
Qed.

Lemma F_g8L_hold : ltac2:(tb__ "0|1|
S2aS2aF_;S2aS30S15S2dQ40A1M0S15S3G0A1S3S3cA1S3bVJG;R9R8R7R6R5R4R3R2R1A9S16R5S35A2S39S14S16R6A1S37A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ HL. pose proof (low_end BX A Kc rho a r tp tr md HJ HL) as LE.
  destruct (site8_vals nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & EE). cbn zeta in EE.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & TOP & ENS & EMS & _). cbn zeta in *.
  set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  unfold F_g8L. apply Forall_cons; [|apply Forall_nil]. apply geu_intro; [clear; lia|]. rewrite EE. clear -LE LB MN. lia.
Qed.

Lemma F_g9L_hold : ltac2:(tb__ "0|1|
S2aS2aF_;S2aS30S15S2dQ40A1M0S15S3G0A1S3S3cA1S3bVJG;R9R8R7R6R5R4R3R2R1A9S16R5S35A2S39S14S16R6A1S38A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ HL. pose proof (low_end BX A Kc rho a r tp tr md HJ HL) as LE.
  destruct (site9_vals nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (EU & _). cbn zeta in EU.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & TOP & ENS & EMS & _). cbn zeta in *.
  set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  unfold F_g9L. apply Forall_cons; [|apply Forall_nil]. apply geu_intro; [clear; lia|]. rewrite EU. clear -LE LB MN. lia.
Qed.

Section HINT.
Variable BX : AA -> AA.
Variables (D D' : axst) (F : list sprop).
Hypothesis WD : ltac2:(tb__ "0|0|
S0S4S1eSeVD';A1A1S5A3").
Hypothesis DD : ltac2:(tb__ "0|4|
S0S9S8S3S8S18S18A2M0A1M1S3S14A1M2A2M3A1S59SeVD;A1SeVD';A1A2SaG3ScG1G2S6G0A1VF;A4A2A3").
Hypothesis NXD : ltac2:(tb__ "0|0|
S0S41S19SeVD';A1A1S19SeVD;A1A1A3").
Hypothesis HD : ltac2:(tb__ "0|0|
S0SfS10VD;SeVD';A1A2VD';A3").
Hypothesis FLOW : ltac2:(tb__ "0|0|
S57S14S35S1aSeVD;A1A1A3").
Hypothesis FH : ltac2:(tb__ "0|1|
S2aS30S15S2dQ40A1M0S15S3G0A1S3S3cA1S3bVJG;VBX;R8R7R6R5R4R3R2R1A9S16R5S35A2S39S14S16R6A1VF;A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").

Lemma hint_low : ltac2:(tb__ "0|1|
S2aS30S15S2dQ40A1M0S15S3G0A1S45S3dVsegs;VJG;VBX;R7R6R5R4A5VD;R3R2R1A6S3dVsegs;VJG;VBX;R8R7R6R5A5VD';R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw.
  pose proof (proj1 (Forall_forall _ _) (SPA_facts_hold segsA _ rhoX D tp w Hw) _ FLOW) as HL.
  destruct w as [tr [ms md]]. rewrite <- HD.
  eapply SPA_restate; [exact WD | exact DD | exact NXD | constructor | | exact Hw].
  exact (FH A Kc rho a rhoX tp tr md (proj2 Hw) HL).
Qed.

Lemma hint_low_triple : ltac2:(tb__ "0|2|
S45OF_;S2aS30S15S2dQ40A1M0S46S15S3G0A1M1S44Vsegs;R8S3dVsegs;VJG;VBX;R7R6R5R4A5VD';R2R1A5R3A4FtY;FrY;S15G1S44Vsegs;R9S3dVsegs;VJG;VBX;R8R7R6R5A5VD;R2R1A5R4A4FtX;FrX;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HC rX tX.
  eapply triple_conseq; [intros w Hw; exact (hint_low A Kc rho a rX tX w Hw) | intros w Hw; exact Hw | exact (HC rX tX)].
Qed.
End HINT.

Section G43L.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S2aS0S2cS2bVBX;R1A1A1S2bR1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S2aS30S15S2dQ40A1M0S15S3G0A1S3S3cA1S3bVJG;VBX;R8R7R6R5R4R3R2R1A9S39S14S16R5A1VFXP;A3S3S17A1S0S3S8S8S18S18A2S18A2M1A1S3aS17G1S47R1A4S3aS17G1S47VPX;A4A3S39S17S17S71S27R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (C5 C5A Y6A E6 CT6 CO6 T6 : axst) (sA s6 : wsub) (R6 : list sobj).
Let D6 : axst := ltac2:(tb__ "0|0|
S60VT6;S1aSeVCO6;A1A1A2").
Hypothesis FLOW : ltac2:(tb__ "0|0|
S57S14S35S1aSeVC5;A1A1A3").
Hypothesis HC5A : ltac2:(tb__ "0|0|
S0SfS5eS4fVnx;A1VC5;A2VC5A;A3").
Hypothesis FBA : ltac2:(tb__ "0|0|
S0S4S56S14S1dS19SeVC5;A1A1A1S4fVnx;A1A3S5A3").
Hypothesis Cert6A : ltac2:(tb__ "0|1|
S0S4S5fS6eUfa0S7S40S65S6S40A1A3VGS;S7SfVC5A;S6SfA1M0A3S7SfVY6A;G0A3A6S5A3").
Hypothesis E6A : ltac2:(tb__ "0|0|
S0S4S11VY6A;VE6;VsA;A3S5A3").
Hypothesis I6A : ltac2:(tb__ "0|0|
S0S4S5dVsA;VGS;A2S5A3").
Hypothesis WC6 : ltac2:(tb__ "0|0|
S0S4S1eSeVCT6;A1A1S5A3").
Hypothesis DF6 : ltac2:(tb__ "0|4|
S0S9S8S3S8S18S18A2M0A1M1S3S14A1M2A2M3A1S59SeVE6;A1SeVCT6;A1A2SaG3ScG1G2S7G0ScS18S18S55Vnx;A1S50A4S6G0A1A3S6S14A1A4A2A3").
Hypothesis NX6 : ltac2:(tb__ "0|0|
S0S41S19SeVCT6;A1A1S19SeVE6;A1A1A3").
Hypothesis HC6 : ltac2:(tb__ "0|0|
S0SfS10VE6;SeVCT6;A1A2VCT6;A3").
Hypothesis SK6 : ltac2:(tb__ "0|1|
S0S3S8S8S18S18A2S18A2M0A1S3aS17G0S47S29SeVCT6;A1A1A4S3aS17G0S47SbS17S7S17S69Vnx;A1S7S17S68Vnx;A1S6S17A1A3A3SbS17S70VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC6 : ltac2:(tb__ "0|0|
S58S14SbS14S34VW;Vst;A2S33S32A1A3S1aSeVCT6;A1A1A3").
Hypothesis FX6 : ltac2:(tb__ "0|0|
S58S14VFXP;S1aSeVCT6;A1A1A3").
Hypothesis XC6 : ax_X CT6 = [].
Hypothesis HCO6 : ltac2:(tb__ "0|0|
S0SfS6bVCT6;S26S51Vnx;A1S1bZ0A1S50S6S24A1S21A5A2VCO6;A3").
Hypothesis WCO6 : ltac2:(tb__ "0|0|
S0S4S1eSeVCO6;A1A1S5A3").
Hypothesis He6 : ltac2:(tb__ "0|1|
S0S9S3S17A1M0A1S62VCO6;S4dVs6;A3SaG0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0S4S61VCO6;S4dVs6;VR6;S3aS13SfS12S4eA4A5S5A3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0SfS63Vs6;S4dS6aVCO6;VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0S4S56S14S1dS19SeVCO6;A1M0A1A1S1aG0A1A3S5A3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0S4S56S14S1dS19SeVT6;A1A1A1S1aSeVCO6;A1A1A3S5A3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S0S4S5cVGS;S19SeVCO6;A1A1A2S5A3").

Theorem sec_g43_low : ltac2:(tb__ "0|5|
S45OF_;S2aS30S15S2dQ40M0A1M1S46S64VW;Vst;A2S5bVW;Vst;A2S31R6A1S3fVsegs;R9S3eR7A1A3S40S1S48S6dS2eG0R7A2A1M2R1A2S4aR1S49G2S4bS5aS2eG0S20R8PcA2A2A1Z8A2A2A2A2S2S0S9S2dQ8A1M3A1S28R9S2fG0R2A2A2SdG3A1A3A1F_;Fz;S15S3G1A1M4S44Vsegs;RdS3dVsegs;VJG;VBX;RcRbRaR9A5VD6;R2R1A5R8A4FtpY;FrhoY;S15G4S44Vsegs;ReS3dVsegs;VJG;VBX;RdRcRbRaA5VC5;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCONT rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  assert (SL : slink (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }
  assert (TAIL : forall rE tE, triple segs ok (SPA segs (JG BX A Kc rho a) E6 rE tE) Q).
  { intros rE tE.
    apply (ms_step nW st tmax nx Hnx NXG BX BXg E6 CT6 CO6 T6 (B3 nx) L3 [O_2 nx; O_1 nx] PX Pre_memsetA Pret_ms Posts_memsetA s6 R6 eq_refl
             (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl
             (RS6 nW st tmax nx Hnx BX E6 CT6 WC6 DF6 NX6 HC6) (HBL6 nW st tmax nx Hnx BX PX FXP PX_noband E6 CT6 NX6 FX6)
             SK6 FC6 XC6 HCO6 WCO6 He6 Hchk6 HT6 FBC6 FBT6 NXC6
             ok A Kc rho rho a tE Q HW HUS HKc Hokl SL).
    intros rhoY tpY. exact (HCONT rhoY tpY). }
  apply (triple_conseq (P:=SPA segs (JG BX A Kc rho a) C5A rX tX) (SPA segs (JG BX A Kc rho a) C5 rX tX) (Q:=Q)); [intros w Hw | intros w Hw; exact Hw |].
  { pose proof (proj1 (Forall_forall _ _) (SPA_facts_hold segsA _ rX C5 tX w Hw) _ FLOW) as HL.
    destruct w as [tr [ms md]]. rewrite <- HC5A.
    split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_A nx) _ _ (proj1 Hw) (low_FA BX A Kc rho a rX tX tr md BXg (proj2 Hw) HL) FBA). }
  apply (cfg_soundA segs 4000%nat [MSENT] GS [C5A] [Y6A] (JG BX A Kc rho a) ok Q tX Hokf HST Cert6A); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact (join4 nW st tmax nx Hnx NXG BX A Kc rho a Y6A E6 sA rE tX w HUS HKc E6A I6A Hw) | intros w Hw; right; exact Hw |].
  apply TAIL.
Qed.
End G43L.
End SEC6L.
End SpineCallocSec6L.

