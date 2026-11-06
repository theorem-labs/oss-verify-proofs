(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "pow"; "of_nat"; "divide"; "lt"; "mul"; "sub"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "rl"; "@Corelib.Init.Datatypes"; "cons"; "prod"; "list"; "nil"; "app"; "pair"; "bool"; "length"; "true"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_reserved"; "vm_init_sp"; "vm_limit"; "vm_maps"; "lazy_interior"; "vm_brk"; "Model"; "event"; "vm_start_brk"; "alloc_top"; "m_vm_lazy"; "region_free"; "vm_noaccess"; "VmMaps"; "mkVmMapsFull"; "vm_mmap_base"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6"; "x1"; "m16"; "n17"; "topZ"; "v79Z"; "v80Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop"; "GPe"; "HSe"; "LWe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "gw_sizes"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7"; "r6of"; "out18"; "out18_model"; "Q18"; "TP18"; "ZX18"; "out18_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop.TopA"; "mB"; "mA1"; "mS"; "PostMain"; "BS"; "Bmain"; "Lmain"; "Mmain"; "WTOT"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start2"; "n5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start3"; "n6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib"; "Kx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M"; "ranges_apart"; "minv8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF"; "arg_layout"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartStates"; "S_ctor"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4"; "m10"; "m11"; "m8"; "m9"; "n7"; "n9"; "priZ"; "spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5"; "m12"; "m13"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8"; "L24"; "MAIN_of"; "TPmain"; "m22"; "m23a"; "m24"; "rhoOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out"; "L18"; "X18"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS"; "RMH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.StartBD"; "BDT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA
  MmapA MmapFixedA MmapFixedA2 MmapBrkA MmapNodesA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Init Code StartLib KxA Placement PlacementA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartNodes3E.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ne.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start4Fail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ns.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ob.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require os.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start2States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start3States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start4FailStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4FailCut OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start4Fail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Start5bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o2.Start6Aux OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.MuslMalloc40States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.MuslMalloc40Post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.MuslMalloc40 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.StartBD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Start8RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.Start8States0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8StatesA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oe.Start8StatesB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.StartWit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac klia := unfold kHighMemBeg in *; repeat match goal with H : context [Z.modulo _ _] |- _ => clear H end; lia.
Ltac blia := unfold SHADOW_BAND_LO, SHADOW_BAND_HI, SHADOW_RW_LO_END, SHADOW_RW_HI_BEG, kHighMemBeg in *; lia.

Definition HSe : word * word := ltac2:(tb__ "0|2|
S18SeQ40M0A1M1G1SdG0Z2008fff7000A2SdG0Zdfff0001000A2A4").
Definition GPe : word * word := ltac2:(tb__ "0|2|
S18SeQ40M0A1M1G1SdG0Z8fff7000A2SdG0Z20000000000A2A4").
Definition LWe : word * word := ltac2:(tb__ "0|2|
S18SeQ40M0A1M1G1SdG0Z7fff7000A2SdG0Z10000000A2A4").

Lemma apart_base : ltac2:(tb__ "0|2|
S52S17S14SeQ40A1M0G0A2M1S4eS30A1S13G1S38S13G1S37S13G1S39S16G1A1A3A3A3A3A1").
Proof.
  rewrite segments_reserved_A. unfold HSe, GPe, LWe. cbn [List.app ranges_apart].
  repeat split; try exact I; repeat (apply Forall_cons; [unfold apartW; cbn [fst snd]; rewrite !u64_of_lit by lia; lia|]); apply Forall_nil.
Qed.

Section TopA.

Variables (m : Model) (B : Z).
Hypothesis Hh0 : m_halted m = None.
Hypothesis Hlz : m_vm_lazy m = [].
Hypothesis Hmt : m_vm_materialized m = [].
Hypothesis Hres : ltac2:(tb__ "0|1|
S1S15S14SeQ40A1M0G0A2A1S1dS1cVm;A1A1S4eS30A1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|2|
S1S15S14SeQ40A1M0G0A2M1A1S20S1cVm;A1A1S16G1A1A3").
Hypothesis Hna : ltac2:(tb__ "0|2|
S1S15S14SeQ40A1M0G0A2M1A1S29S1cVm;A1A1S16G1A1A3").
Hypothesis HusedB : vm_backing_used m <= B.
Hypothesis HBlim : ltac2:(tb__ "0|0|
S4S5S5VB;Z39e000A2Z1000000A2S1fS1cVm;A1A1A2").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hsb : ltac2:(tb__ "0|1|
S1SeQ40A1S25S1cVm;A1M0A1S22G0A1A3").
Hypothesis Hbrk : ltac2:(tb__ "0|1|
S0S4Z643000SfQ40S22S1cVm;A1A1A2M0A2S4G0Z80643000A2A2").
Hypothesis Hbal : ltac2:(tb__ "0|0|
S9Z1000SfQ40S22S1cVm;A1A1A2A2").
Variable ok : assn.
Hypothesis OK0 : ltac2:(tb__ "0|0|
S57S30Vok;S51Vm;A1A3").
Hypothesis OKF : ltac2:(tb__ "0|1|
S58S11S15SeQ40A1A1S15S24A1M0S23R5R4R3R2R1A4S1G0R3S16S24A1A3F_;Fmd;Ftr;Ftp;Frho;S5aS30Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S58S11S15SeQ40A1A1S15S24A1M0S23R5R4R3R2R1A4S1G0R3S16S24A1A3F_;Fmd;Ftr;Ftp;Frho;S74S30Vok;R2A3F_;FJ;").

Definition mB : Model := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1.m4 m.
Definition mA1 (a1 : word) : Model := m5 mB a1.
Definition mS (a1 a2 : word) : Model := m6 (mA1 a1) a2.
Definition BS : Z := B + 0x10000 + 0x38e000.

Lemma mB_vmmaps : ltac2:(tb__ "0|4|
S1S2aS1cS45A1S2bS1dS1cVm;A1M0A1S13S14SeQ40A1M1G1A2M2S38S13G2S37S13G2S39S16G2A1M3A3A3A3S13G2S37G3A3S25G0A1S22G0A1S1fG0A1S2cG0A1S1eG0A1A8A3").
Proof. clear - Hmaps Hna. unfold mB, HSe, GPe, LWe. rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1.m4_vmmaps m Hmaps), Hna. reflexivity. Qed.

Lemma mB_lazy : ltac2:(tb__ "0|3|
S1S15S14SeQ40M0A1M1G1A2M2A1S27S45A1S17G2S21SdG0Z2008fff7000A2SdG0Zdfff0001000A2A2S17G2S21SdG0Z8fff7000A2SdG0Z20000000000A2A2S21SdG0Z7fff7000A2SdG0Z10000000A2A2A3A3A3").
Proof.
  clear - Hlz. unfold mB, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1.m4, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1.m3, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1.m2, lazy_rw_model, lazy_none_model.
  repeat (rewrite m_vm_lazy_vm_add_lazy || rewrite m_vm_lazy_with_vmmaps). rewrite Hlz, app_nil_r. reflexivity.
Qed.

Lemma mS_fields : ltac2:(tb__ "0|8|
SeQ40M0A1M1G1S0S1S15S14G1G1A2M2A1M3S1dS1cS47R2R1A2M4A1M5A1S1dS1cVm;A1M6A1A3S0S1G3S20G5A1S13G2S18G1G1R1SdG0Z38e000A2A4S13G2S18G1G1R2SdG0Z10000A2A4S13G2S38S13G2S37S13G2S39S16G2A1M7A3A3A3A3A3A3S0S1G3S29G5A1S13G2S37G7A3A3S0S1G3S27G4A1S17G2S21SdG0Z2008fff7000A2SdG0Zdfff0001000A2A2S17G2S21SdG0Z8fff7000A2SdG0Z20000000000A2A2S21SdG0Z7fff7000A2SdG0Z10000000A2A2A3A3A3S0S1S2dS1fG5A1S1fG6A1A3S0S1G1S1eG5A1S1eG6A1A3S0S1G1S22G5A1S22G6A1A3S1G1S25G5A1S25G6A1A3A2A2A2A2A2A2A2Fa2;Fa1;").
Proof.
  clear - Hmaps Hna Hlz. intros a1 a2. unfold mS, mA1, m6, m5, eager_model, eager_h.
  repeat (rewrite m_vmmaps_with_vmmaps || rewrite m_vm_lazy_with_vmmaps); cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_init_sp vm_brk vm_start_brk].
  repeat (rewrite m_vmmaps_with_vmmaps || rewrite m_vm_lazy_with_vmmaps); cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_init_sp vm_brk vm_start_brk].
  rewrite mB_vmmaps, mB_lazy. cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_init_sp vm_brk vm_start_brk].
  repeat split; reflexivity.
Qed.

Lemma mA1_fields : ltac2:(tb__ "0|6|
SeQ40M0A1M1S0S1S15S14G1G1A2M2A1M3S1dS1cS46R1A1A1M4A1S1dS1cVm;A1M5A1A3S0S1G3S20G4A1S13G2S18G1G1R1SdG0Z10000A2A4S13G2S38S13G2S37S13G2S39S16G2A1A3A3A3A3A3S0S1S2dS1fG4A1S1fG5A1A3S1G1S1eG4A1S1eG5A1A3A2A2A2Fa1;").
Proof.
  clear - Hmaps Hna. intros a1. unfold mA1, m5, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps. cbn [vm_reserved vm_maps vm_limit vm_init_sp].
  rewrite mB_vmmaps. cbn [vm_reserved vm_maps vm_limit vm_init_sp]. repeat split; reflexivity.
Qed.

Lemma band_B : ltac2:(tb__ "0|2|
S3dS17S14SeQ40A1M0G0A2S1dS1cS45A1M1A1S20G1A1A3S3bS3aA3").
Proof.
  clear - Hmaps Hna. rewrite mB_vmmaps. cbn [vm_reserved vm_maps]. unfold HSe, GPe, LWe.
  apply (shadow_band_covered _ (Z_to_bv 64 0x7fff7000) (Z_to_bv 64 0x10000000) (Z_to_bv 64 0x8fff7000) (Z_to_bv 64 0x20000000000) (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000));
    try (apply in_app_iff; right; cbn [In]; tauto);
    unfold SHADOW_BAND_LO, SHADOW_RW_LO_END, SHADOW_RW_HI_BEG, SHADOW_BAND_HI; rewrite ?u64_of_lit by lia; lia.
Qed.
Lemma band_A1 : ltac2:(tb__ "0|2|
SeQ40A1M0S3dS17S14G0G0A2S1dS1cS46R1A1A1M1A1S20G1A1A3S3bS3aA3Fa1;").
Proof.
  clear - Hmaps Hna. intros a1. pose proof (mA1_fields a1) as (R & M & _). rewrite R, M.
  pose proof band_B as X. rewrite mB_vmmaps in X. cbn [vm_reserved vm_maps] in X. apply band_covered_app_cons. exact X.
Qed.

Lemma a1_facts : ltac2:(tb__ "0|7|
SeQ40M0A1M1S2fSdG0Z0M2A2S45S4fR1A4S0S4Z643000SfG0R2A2M3A2S0S3S4S5G3Z10000M4A2M5S3bA2S4S3aG3A2A2S0S4G5S26S1cVm;A1A1A2S0S1S2dS6G3Z1000A2G2A3S1S19S28S17S14G1G1A2M6S4eS30A1S13G6S38S13G6S37S13G6S39S16G6A1A3A3A3A3R2SdG0G4A2A3S1bA3A2A2A2A2F_;Fa1;").
Proof.
  clear - Hmaps Hna Hres Htop. intros a1 Hpl.
  assert (T : init_sp_ok (m_vmmaps mB)) by (unfold init_sp_ok in *; rewrite mB_vmmaps; exact Htop).
  pose proof (place_LB_A mB 0x10000 a1 T ltac:(rewrite mB_vmmaps; exact Hres) band_B ltac:(lia) ltac:(reflexivity) Hpl) as (P1 & P2 & P3 & P4 & _).
  change (LB_of 0x10000) with 0x643000 in P1. unfold alloc_top in P4 |- *. rewrite mB_vmmaps in P4. cbn [vm_init_sp] in P4.
  pose proof Hpl as (Pal & _ & _ & Pfree). rewrite mB_vmmaps, Hres in Pfree. cbn [vm_reserved vm_maps] in Pfree.
  replace (mmap_n n5) with (Z_to_bv 64 0x10000) in Pfree by (symmetry; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  unfold page_size in Pal. repeat split; try assumption.
Qed.

Lemma a2_facts : ltac2:(tb__ "0|7|
SeQ40M0A1M1G1S2fSdG0Z0M2A2S46R2A1S50R1A4S0S4Z643000SfG0R2A2M3A2S0S3S4S5G3Z38e000M4A2M5S3bA2S4S3aG3A2A2S0S4G5S26S1cVm;A1A1A2S0S1S2dS6G3Z1000A2G2A3S1S19S28S17S14G1G1A2M6S4eS30A1S13G6S18G1G1R3SdG0Z10000A2A4S13G6S38S13G6S37S13G6S39S16G6A1A3A3A3A3A3R2SdG0G4A2A3S1bA3A2A2A2A2F_;Fa2;Fa1;").
Proof.
  clear - Hmaps Hna Hres Htop. intros a1 a2 Hpl. pose proof (mA1_fields a1) as (R & M & L & I).
  assert (T : init_sp_ok (m_vmmaps (mA1 a1))) by (unfold init_sp_ok in *; rewrite I; exact Htop).
  pose proof (place_LB_A (mA1 a1) 0x38e000 a2 T ltac:(rewrite R; exact Hres) (band_A1 a1) ltac:(lia) ltac:(reflexivity) Hpl) as (P1 & P2 & P3 & P4 & _).
  change (LB_of 0x38e000) with 0x643000 in P1. unfold alloc_top in P4 |- *. rewrite I in P4.
  pose proof Hpl as (Pal & _ & _ & Pfree). rewrite R, M, Hres in Pfree.
  replace (mmap_n n6) with (Z_to_bv 64 0x38e000) in Pfree by (symmetry; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  unfold page_size in Pal. repeat split; try assumption.
Qed.

Lemma apart_S : ltac2:(tb__ "0|4|
SeQ40M0A1M1G1S2fSdG0Z0A2M2S45S4fR2A4S2fG2S46R3A1S50R2A4S52S17S14G1G1A2S1dS1cS47R4R3A2A1M3A1S20G3A1A3A1F_;F_;Fa2;Fa1;").
Proof.
  clear - Hmaps Hna Hlz Hres Htop. intros a1 a2 G2 G3. pose proof (mS_fields a1 a2) as (R & M & _). rewrite R, M, Hres.
  pose proof (a1_facts a1 G2) as (_ & _ & _ & _ & F1). pose proof (a2_facts a1 a2 G3) as (_ & _ & _ & _ & F2).
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F2 He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F1 He)].
  exact apart_base.
Qed.

Definition Mmain (a1 a2 P b4 b5 b6 b7 b8 b9 : word) (x : Z) (b10 : word) (o : out18) (b12 b13 b14 : word) : Model := ltac2:(tb__ "0|0|
S6bS40S47Va1;Va2;A2VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;AbVb12;Vb13;Vb14;A4").
Definition Lmain (a1 a2 P b4 b5 b6 b7 b8 b9 : word) (x : Z) (b10 : word) (o : out18) (b12 b13 b14 : word) : list (word * word) := ltac2:(tb__ "0|0|
S66S6dS47Va1;Va2;A2VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;AbVb12;Vb13;Vb14;A4").
Definition Bmain : Z := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.Bmain BS.

Definition PostMain (rho : valuation) : assn := ltac2:(tb__ "0|15|
S73S2SeQ40M0A1M1G1S2G1G1S2G1G1S2G1G1S2G1G1S2G1G1S2G1G1S2G1G1S2G1G1S2S2dS2dS2G1G1S2S3fS3fS2S19S19S2G1G1S2G1G1S2G1G1S2S11S11S0S2fSdG0Z0M2A2M3S45S4fR11A4S0S2fG3S46R11A1S50R10A4S0S2fG3S47R11R10A2M4S60RfA4S0S2fG3S5eG4RfA2S61ReA4S0S2fG3S5fG4RfReA3SdG0Z1000M5A2M6RdA4S0S2fG3S5cG4RfReRdA4SdG0Z10000A2RcA4S0S2fG3S5dG4RfReRdRcA5G6RbA4S0S2fG3S64G4RfReRdRcRbA6G6RaA4S0S2fG3S65G4RfReRdRcRbRaA7G6R9A4S0S1S2dR8S31Vrho;A1A3S0S2fG3S32G4RfReRdRcRbRaR9R8A9SdG0S33A2R7A4S0S44G4RfReRdRcRbRaR9R8R7R6AbS0S2fG3S40G4RfReRdRcRbRaR9R8R7R6AbM7SdG0Z100000M8A2R4A4S0S2fG3S69G7R4A2SdG0Z800000M9A2R3A4S0S2fG3S6aG7R4R3A3G6R2A4S0S53S4bR11R10RfReRdRcRbRaR9R8R7R6R4R3R2AfS1fS1cVm;A1MaA1S1eGaA1S41R8A1S4cR11R10RfReRdRcRbRaR9R8R7R6R4R3R2AfMbA5S0S0S4Z643000McSfG0R4A2MdA2S0S3S4S5GdG8A2MeS3bA2S4S3aGdA2A2S0S1S2dS6GdG5A2G2A3S4GeScR8G9A2MfA2A2A2A2S0S0S4GcSfG0R3A2M10A2S0S3S4S5G10G9A2M11S3bA2S4S3aG10A2A2S0S1S2dS6G10G5A2G2A3S4G11GfA2A2A2A2S0S0S4G5SfG0R2A2M12A2S0S3S4S5G12G5A2M13S3bA2S4S3aG12A2A2S0S1S2dS6G12G5A2G2A3S4G13GfA2A2A2A2S0S2eS75R1P19A2S1G1S10R3R2A2S10Vrho;R2A2A3F_;Fi;S0S2eS1S15SeQ8A1A1S12R2R1A2S12Vrho;R1A2A3Fl;S0S6fVrho;R1A2S0S43R8S3eVrho;A1R1A3S0S70S42R8R1A2S62R1A1R1A3S0S6cG4R11R10RfReRdRcRbRaR9R8R7R1AdS0S1G1S10R1P1bA2R11A3S0S1G1S10R1P1cA2R10A3S0S1G1S10R1P1dA2RfA3S0S1G1S10R1P1eA2S63RfA1M14A3S0S1S2dSbZ8SfG0S10R1P1fA2A2A2SfG0G14A2A3S0S1G1S10R1P20A2ReA3S0S1G1S10R1P21A2RdA3S0S1G1S10R1P22A2RcA3S0S1G1S10R1P24A2RbA3S0S1G1S10R1P4dA2RaA3S0S1G1S10R1P4eA2R9A3S0S1G1S10R1P4fA2SdG0S35R8A1A2A3S0S1G1S10R1P50A2SdG0S36R8A1A2A3S0S1G1S10R1P51A2SdG0S34R8A1A2A3S0S1G1S10R1P53A2R7A3S0S1G1S10R1P9fA2R4A3S0S1G1S10R1Pa0A2R3A3S0S1G1S10R1Pa1A2R2A3S59S30S5bGbS4aA2S67R5A1R1S68R8R3R1A3R12A6A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lrho';A2Lb14;A2Lb13;A2Lb12;A2Lv;A2Lo;A2Lb10;A2Lx;A2Lb9;A2Lb8;A2Lb7;A2Lb6;A2Lb5;A2Lb4;A2LP;A2La2;A2La1;A2Lw;").

Lemma BS_lim : ltac2:(tb__ "0|0|
S4S5S49Z1000000A2S1fS1cVm;A1A1A2").
Proof. clear - HBlim. unfold BS. lia. Qed.

Theorem startA_main : ltac2:(tb__ "0|5|
S11S1S2dSfQ40M0S10R1P1M1A2A2SfG0S1eS1cVm;A1A1A2A3S4SfG0S10R2G1A2A2SfG0S10R2P4A2A2A2S4SfG0S10R3G1A2A2SfG0S10R3P6A2A2A2S0S4Z7fff80000000S31R4A1M2A2S4G2S7Z2Z2fA2M3A2A2S1S2dS6S31R5A1Z10M4A2Z0A3S4S5S31R6A1Z50A2S3eR6A1A2S4S5S3eR7A1G4A2G3A2S4S5S3eR8A1G4A2S5S31R8A1Z2228cfA2A2S54R9A1S72S30Vok;S56S30S51Vm;A1S55RaA4S48RaA1A4F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;").
Proof.
  intros rho Hv1 H14 H16r Hx H16 R1 R2 R3 HAL.
  assert (HB0 : B <= vm_limit (m_vmmaps m)) by (pose proof BS_lim; unfold BS in *; lia).

  eapply triple_seq; [exact (start1_sum_A m B Hh0 Hlz Hmt Hres Hmaps Hna HusedB HB0 Htop ok OK0 OKF OKP rho H14 H16r (proj1 Hx))|].
  apply triple_ex; intros rho1. apply triple_pure; intros AG1. apply triple_pure; intros RM1.
  pose proof AG1 as [V1 L1].
  assert (Hv1a : bv_unsigned (rw rho1 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps mB))) by (rewrite (V1 1%positive) by lia; rewrite mB_vmmaps; exact Hv1).
  assert (TB : init_sp_ok (m_vmmaps mB)) by (clear - Htop Hmaps Hna; unfold init_sp_ok in *; rewrite mB_vmmaps; exact Htop).
  assert (RB : vm_reserved (m_vmmaps mB) = segments_reserved segsA) by (rewrite mB_vmmaps; exact Hres).

  change (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1.m4 m) with mB.
  eapply triple_seq; [exact (start2_sum_A mB B RB TB band_B ltac:(rewrite mB_vmmaps; cbn [vm_limit]; pose proof BS_lim; unfold BS in *; lia) ok OKF OKP rho1 Hv1a)|].
  apply triple_ex; intros a1. apply triple_ex; intros rho2. apply triple_pure; intros G2. apply triple_pure; intros AG2.
  pose proof AG2 as (V2 & L2 & M2).
  assert (H27b : rw rho2 27%positive = a1) by (rewrite <- (V2 27%positive) by lia; apply rho_set_rw_at).
  assert (E2lo : forall i, (i < 25)%positive -> rw rho2 i = rw rho i) by (intros i Hi; rewrite <- (V2 i) by lia; rewrite rho_set_rw_other by lia; apply V1; lia).
  pose proof (mA1_fields a1) as (RA & MA & LA & IA).
  assert (Hv1b : bv_unsigned (rw rho2 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps (mA1 a1)))) by (rewrite (E2lo 1%positive) by lia; rewrite IA; exact Hv1).
  assert (TA : init_sp_ok (m_vmmaps (mA1 a1))) by (clear - Htop IA; unfold init_sp_ok in *; rewrite IA; exact Htop).

  change (m5 mB a1) with (mA1 a1).
  eapply triple_seq; [exact (start3_sum_A (mA1 a1) a1 (B + 0x10000) ltac:(rewrite RA; exact Hres) ltac:(rewrite MA; left; reflexivity) TA (band_A1 a1)
                              ltac:(rewrite LA; pose proof BS_lim; unfold BS in *; lia) ok OKF OKP rho2 H27b Hv1b)|].
  apply triple_ex; intros a2. apply triple_ex; intros rho3. apply triple_pure; intros G3. apply triple_pure; intros AG3.
  pose proof AG3 as (V3 & L3 & M3).
  assert (H28c : rw rho3 28%positive = a2) by (rewrite <- (V3 28%positive) by lia; apply rho_set_rw_at).
  assert (H27c : rw rho3 27%positive = a1) by (rewrite <- (V3 27%positive) by lia; rewrite rho_set_rw_other by lia; exact H27b).
  assert (E3lo : forall i, (i < 25)%positive -> rw rho3 i = rw rho i) by (intros i Hi; rewrite <- (V3 i) by lia; rewrite rho_set_rw_other by lia; apply E2lo; exact Hi).

  change (m6 (mA1 a1) a2) with (mS a1 a2). change (B + 0x10000 + 0x38e000) with BS.
  pose proof (mS_fields a1 a2) as (RS & MS & NS & LS & LMS & IS & KS & SKS).
  assert (SRES : vm_reserved (m_vmmaps (mS a1 a2)) = segments_reserved segsA) by (rewrite RS; exact Hres).
  assert (SMAPS : vm_maps (m_vmmaps (mS a1 a2)) = [(a2, Z_to_bv 64 0x38e000); (a1, Z_to_bv 64 0x10000);
            (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000); (Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000); (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000)])
    by (rewrite MS; reflexivity).
  assert (SNA : vm_noaccess (m_vmmaps (mS a1 a2)) = [(Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000)]) by (rewrite NS; reflexivity).
  assert (STOP : init_sp_ok (m_vmmaps (mS a1 a2))) by (clear - Htop IS; unfold init_sp_ok in *; rewrite IS; exact Htop).
  pose proof (a1_facts a1 G2) as (F1lo & F1band & F1top & F1al & F1free). pose proof (a2_facts a1 a2 G3) as (F2lo & F2band & F2top & F2al & F2free).
  assert (SA1 : 0x643000 <= bv_unsigned a1 /\ (bv_unsigned a1 + 0x10000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned a1) /\ bv_unsigned a1 + 0x10000 <= alloc_top (m_vmmaps (mS a1 a2))).
  { unfold alloc_top in *. rewrite IS. repeat split; assumption. }
  assert (SA2 : 0x643000 <= bv_unsigned a2 /\ (bv_unsigned a2 + 0x38e000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned a2) /\ bv_unsigned a2 + 0x38e000 <= alloc_top (m_vmmaps (mS a1 a2))).
  { unfold alloc_top in *. rewrite IS. repeat split; assumption. }
  assert (SBLIM : BS + 0x1000000 <= vm_limit (m_vmmaps (mS a1 a2))) by (rewrite LMS; exact BS_lim).
  assert (SSB : vm_start_brk (m_vmmaps (mS a1 a2)) = vm_brk (m_vmmaps (mS a1 a2))) by (rewrite KS, SKS; exact Hsb).
  assert (SBRK : 0x643000 <= bv_unsigned (vm_brk (m_vmmaps (mS a1 a2))) <= 0x80643000) by (rewrite KS; exact Hbrk).
  assert (SBAL : (4096 | bv_unsigned (vm_brk (m_vmmaps (mS a1 a2))))) by (rewrite KS; exact Hbal).
  assert (Hv1c : bv_unsigned (rw rho3 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps (mS a1 a2)))) by (rewrite (E3lo 1%positive) by lia; rewrite IS; exact Hv1).
  assert (HF8 : forall mm BB r tp Q, triple segsA ok (SPA segsA (KxA mm BB) (fail_state E_k8x) r tp) Q) by (intros; apply (s8_fail_safe ok OKF)).

  eapply triple_seq; [exact (start4_sum_A (mS a1 a2) a1 a2 BS SRES SMAPS SNA LS STOP SA1 SA2 SBLIM ok OKF OKP HF8 rho3 H27c H28c Hv1c)|].
  apply triple_ex; intros P. apply triple_ex; intros rho4.
  apply triple_pure; intros HPL. apply triple_pure; intros AG4. apply triple_pure; intros RM4. apply triple_pure; intros H29. apply triple_pure; intros H30.
  unfold Post4b. apply triple_ex; intros b4. apply triple_ex; intros b5. apply triple_ex; intros b6. apply triple_ex; intros hi. apply triple_ex; intros rho5.
  apply triple_pure; intros HPL4. apply triple_pure; intros HPL5. apply triple_pure; intros HPL6. apply triple_pure; intros Hcls. apply triple_pure; intros AG5.
  apply triple_pure; intros RM5. apply triple_pure; intros V31. apply triple_pure; intros H32. apply triple_pure; intros H33. apply triple_pure; intros H34. apply triple_pure; intros HZ11. apply triple_pure; intros HZD5.
  pose proof AG4 as [V4 L4]. pose proof AG5 as [V5 L5].
  assert (E5lo : forall i, (i < 29)%positive -> rw rho5 i = rw rho3 i) by (intros i Hi; rewrite (V5 i), (V4 i) by lia; reflexivity).
  assert (HV5 : vals12 (mS a1 a2) a1 a2 P b4 b5 b6 rho5).
  { unfold vals12. rewrite (E5lo 27%positive), (E5lo 28%positive), (E5lo 1%positive) by lia. rewrite (V5 29%positive), (V5 30%positive) by lia.
    repeat split; assumption. }

  eapply triple_seq; [exact (start5_sum_A (mS a1 a2) a1 a2 BS SRES SMAPS SNA LS STOP SA1 SA2 SBLIM ok OKF OKP P b4 b5 b6 HPL HPL4 HPL5 HPL6 rho5 HV5 HZ11 HZD5)|].
  apply triple_ex; intros b7. apply triple_ex; intros b8. apply triple_ex; intros b9. apply triple_ex; intros rho6.
  apply triple_pure; intros HPL7. apply triple_pure; intros HPL8. apply triple_pure; intros HPL9. apply triple_pure; intros AG6.
  apply triple_pure; intros H36. apply triple_pure; intros H77. apply triple_pure; intros H78. apply triple_pure; intros HSSZ. apply triple_pure; intros HZ11c. apply triple_pure; intros HZD6. apply triple_pure; intros RM6.
  pose proof AG6 as [V6 L6].
  assert (HV6 : vals12 (mS a1 a2) a1 a2 P b4 b5 b6 rho6) by (eapply (vals12_agree _ _ _ _ _ _ _ 36%positive rho5 rho6); [lia | exact HV5 | intros i Hi; apply V6; exact Hi]).

  eapply triple_seq; [exact (start6_sum_A (mS a1 a2) a1 a2 BS SRES SMAPS SNA LS STOP SA1 SA2 SBLIM ok OKF OKP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9
                              rho6 HV6 H36 H77 H78 HSSZ HZ11c (RMH_refl rho6))|].
  cbv zeta. apply triple_ex; intros b10. apply triple_ex; intros rho7.
  apply triple_pure; intros HPL10. apply triple_pure; intros AG7. apply triple_pure; intros H79. apply triple_pure; intros H80. apply triple_pure; intros H81.
  apply triple_pure; intros H83. apply triple_pure; intros HRM6. apply triple_pure; intros RM7. apply triple_pure; intros HXF.
  pose proof AG7 as [V7 L7]. pose proof HXF as (Hxx & H16x & V35).
  set (x := x1 rho6) in *.
  assert (Ex : x = x1 rho).
  { subst x. unfold x1. rewrite (V6 1%positive), (E5lo 1%positive), (E3lo 1%positive) by lia. reflexivity. }
  assert (HV7 : vals12 (mS a1 a2) a1 a2 P b4 b5 b6 rho7) by (eapply (vals12_agree _ _ _ _ _ _ _ 79%positive rho6 rho7); [lia | exact HV6 | intros i Hi; apply V7; exact Hi]).
  assert (H36d : rw rho7 36%positive = b7) by (rewrite (V7 36%positive) by lia; exact H36).
  assert (H77d : rw rho7 77%positive = b8) by (rewrite (V7 77%positive) by lia; exact H77).
  assert (H78d : rw rho7 78%positive = b9) by (rewrite (V7 78%positive) by lia; exact H78).
  assert (Ex7 : x1 rho7 = x) by (subst x; unfold x1; rewrite (V7 1%positive) by lia; reflexivity).
  assert (Hxtop : alloc_top (m_vmmaps (mS a1 a2)) = x - 8388608).
  { unfold alloc_top. rewrite stack_max_size_val, <- Hv1c, <- (E5lo 1%positive), <- (V6 1%positive) by lia. subst x. reflexivity. }
  assert (Er6 : Start7.r6of rho7 = Start7.r6of rho).
  { unfold Start7.r6of. rewrite (V7 6%positive), (V6 6%positive), (E5lo 6%positive), (E3lo 6%positive) by lia. reflexivity. }
  assert (V35d : 8 * bv_unsigned (rw rho7 35%positive) = bv_unsigned b6) by (rewrite (V7 35%positive) by lia; exact V35).
  assert (HSZ : Start7.SZ18 x rho7).
  { apply (Start7.SZ18_of_RM6 (mS a1 a2) a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL HPL4 HPL5 HPL6 x Hxx H16x Hxtop rho6 rho7 HV6 eq_refl V35 HSSZ HRM6).
    - intros i Hi. apply V7. lia.
    - exact L7. }

  replace (TP17 rho6) with (TP17 rho7) by (unfold TP17; rewrite (TP16_ext rho6 rho7 (agree_vars_le 79 36 rho6 rho7 ltac:(lia) AG7)); reflexivity).
  eapply triple_seq.
  { exact (Start7.seg18 (mS a1 a2) a1 a2 BS SRES SMAPS SNA LS STOP SA1 SA2 SBLIM SSB SBRK SBAL ok OKF OKP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
             rho7 HV7 H36d H77d H78d H83 Ex7 ltac:(rewrite Er6, Ex; exact R1) ltac:(rewrite Er6; exact R2) ltac:(rewrite Er6, Ex; exact R3) HSZ
             (arg_layout_ext rho rho7 ltac:(intros i Hi; rewrite (V7 i), (V6 i), (E5lo i), (E3lo i) by lia; reflexivity) HAL)). }
  apply triple_ex; intros o. apply triple_ex; intros rho8.
  apply triple_pure; intros Ho. apply triple_pure; intros V8. apply triple_pure; intros L8. apply triple_pure; intros H84. apply triple_pure; intros H85. apply triple_pure; intros HZX.
  apply triple_pure; intros RM8. apply triple_pure; intros RL8. apply triple_pure; intros RH8.

  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.minv8_out18 (mS a1 a2) a1 a2 SRES SMAPS SNA LS STOP SA1 SA2 SBRK P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
                (apart_S a1 a2 G2 G3) o Ho) as HMI.
  assert (HL0 : forall e, In e (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.LmE (mS a1 a2) P b4 b5 b6 b7 b8 b10) -> In e (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.L18 (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o)).
  { intros e He. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.L18. apply in_app_iff. right. exact He. }
  assert (HR7 : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK (mS a1 a2) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 rho7).
  { unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK. split; [exact HV7|]. split; [exact H36d|]. split; [exact H77d|]. split; [exact H78d|]. split; [exact H83|].
    split; [exact Ex7|]. split; [exact V35d|]. rewrite Er6, Ex. split; [exact R1|]. split; [exact R2 | exact R3]. }
  assert (HR8 : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK (mS a1 a2) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 rho8).
  { unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK. split; [eapply (vals12_agree _ _ _ _ _ _ _ 84%positive rho7 rho8); [lia | exact HV7 | intros i Hi; apply V8; exact Hi]|].
    rewrite !(V8 36%positive), !(V8 77%positive), !(V8 78%positive), !(V8 83%positive), !(V8 35%positive) by lia.
    split; [exact H36d|]. split; [exact H77d|]. split; [exact H78d|]. split; [exact H83|].
    split; [unfold x1; rewrite (V8 1%positive) by lia; exact Ex7|]. split; [exact V35d|].
    unfold Start7.r6of. rewrite (V8 6%positive) by lia. unfold Start7.r6of in Er6. rewrite Er6. unfold Start7.r6of in R1, R2, R3. rewrite Ex.
    split; [exact R1|]. split; [exact R2 | exact R3]. }
  rewrite <- (Start7.TP18_ext x rho7 rho8 V8 L8).
  eapply triple_conseq; [intros w Hw; exact Hw | |].
  2:{ exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.seg22 (mS a1 a2) a1 a2 BS SRES SMAPS STOP SA1 SA2 SBLIM ok OKF OKP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
               (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.L18 (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) HMI HL0 rho8 HR8). }

  intros w (v & b12 & b13 & b14 & rho9 & HPL12 & HPL13 & HPL14 & V9 & H159 & H160 & H161 & L9 & M9 & Hsp).
  exists a1, a2, P, b4, b5, b6, b7, b8, b9, x, b10, o, v, b12, b13, b14, rho9.
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.MI_main (mS a1 a2) x Hxtop (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.L18 (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) HMI
                b12 b13 b14 HPL12 HPL13 HPL14) as (MIm & F12 & F13 & F14).
  unfold Start7.TOPz in F12, F13, F14. rewrite LMS, IS in MIm.
  assert (CH : forall i, (i < 25)%positive -> rw rho9 i = rw rho i).
  { intros i Hi. rewrite (V9 i), (V8 i), (V7 i), (V6 i), (E5lo i), (E3lo i) by lia. reflexivity. }
  assert (CH7 : forall i, (i < 84)%positive -> rw rho9 i = rw rho7 i) by (intros i Hi; rewrite (V9 i), (V8 i) by lia; reflexivity).
  assert (RM9 : RMH rho rho9).
  {
    assert (E8lo : forall i, (i < 7)%positive -> rw rho8 i = rw rho i) by (intros i Hi; rewrite (V8 i), (V7 i), (V6 i), (E5lo i), (E3lo i) by lia; reflexivity).
    intros a Ha. pose proof Ha as [HaLo _]. unfold x1 in Hx.
    rewrite (M9 a) by (rewrite Hv1 in HaLo; pose proof Hxtop as T; unfold alloc_top in T; rewrite IS, stack_max_size_val in T; lia).
    rewrite (RM8 a) by (apply (proj2 (ARGF_ext rho rho7 a ltac:(intros i Hi; rewrite (V7 i), (V6 i), (E5lo i), (E3lo i) by lia; reflexivity))); exact Ha).
    rewrite (RM7 a) by (apply (proj2 (ARGF_ext rho rho6 a ltac:(intros i Hi; rewrite (V6 i), (E5lo i), (E3lo i) by lia; reflexivity))); exact Ha).
    rewrite (RM6 a) by (apply (proj2 (ARGF_ext rho rho5 a ltac:(intros i Hi; rewrite (E5lo i), (E3lo i) by lia; reflexivity))); exact Ha).
    rewrite (RM5 a) by (apply (proj2 (ARGF_ext rho rho4 a ltac:(intros i Hi; rewrite (V4 i), (E3lo i) by lia; reflexivity))); exact Ha).
    rewrite (RM4 a) by (apply (proj2 (ARGF_ext rho rho3 a ltac:(intros i Hi; rewrite (E3lo i) by lia; reflexivity))); exact Ha).
    rewrite <- M3, rho_set_rw_rm, <- M2, rho_set_rw_rm. apply RM1. exact Ha. }
  assert (ZX9 : ZX18 x (Start7.r6of rho) rho9).
  {
    pose proof (Start7.arith18 x Hxx H16x (Start7.r6of rho) ltac:(rewrite Ex; exact R1) R2 ltac:(rewrite Ex; exact R3)) as AR.
    destruct AR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W14 & _ & _ & _ & Q18K & _ & _ & _ & _ & _ & QLO).
    intros z Hz. rewrite (M9 (Z_to_bv 64 z)).
    - rewrite <- Er6 in Hz. exact (HZX z Hz).
    - rewrite u64_of_lit by (unfold kHighMemBeg in *; lia). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, kHighMemBeg in *. lia. }
  assert (BD9 : BDT (Start7.TP18 x rho9) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho9) rho9).
  {
    assert (Er66 : Start7.r6of rho6 = Start7.r6of rho) by (unfold Start7.r6of; rewrite (V6 6%positive), (E5lo 6%positive), (E3lo 6%positive) by lia; reflexivity).
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.priZ_facts (mS a1 a2) a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL rho6 HV6) as (PR1 & PR2 & PR3 & _).
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.sbZ_facts' (mS a1 a2) a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL HPL4 HPL5 HPL6 rho6 HV6 V35) as SB1.
    change (x1 rho6) with x in PR1, SB1.
    pose proof (TP11_pages x rho6 eq_refl Hxx H16x (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.Upri (mS a1 a2) a1 a2 P b4 b5 b6 rho6 HV6) PR1 PR2 PR3 SB1) as HT11.
    assert (HG : forall a, SHADOW_BAND_LO <= a < kHighMemBeg -> Start7.grp_out o a).
    { intros a Ha. destruct o as [o0|o1|o1 g]; cbn [Start7.grp_out]; [exact I | exact I |].
      pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.X18_facts (mS a1 a2) a1 a2 SRES SMAPS SNA LS STOP SA1 SA2 SBRK P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
                    (apart_S a1 a2 G2 G3) (Start7.O18c o1 g) g OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.pgw Ho ltac:(left; reflexivity)) as (_ & _ & _ & _ & GB).
      pose proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.pgw_n as (_ & PG & _). rewrite PG in GB. clear - Ha GB. blia. }
    pose proof (BD12 rho6 HZD6 HSSZ) as B6.
    pose proof (BD17 x rho6 rho7 eq_refl Hxx H16x HT11 B6 HRM6) as B7.
    pose proof (BD18 x rho6 rho7 rho8 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho6) eq_refl Hxx H16x
                  ltac:(rewrite Er66, Ex; exact R1) ltac:(rewrite Er66; exact R2) ltac:(rewrite Er66, Ex; exact R3) HT11 B7
                  (lowb_adapter x rho7 rho7 rho8 o (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho6) Hxx (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ_ext rho6 rho7 (V7 31%positive ltac:(lia))) HG RL8)
                  (band_adapter x (Start7.r6of rho6) rho7 rho8 Hxx ltac:(rewrite Er66, <- Er6; exact RH8))
                  ltac:(rewrite Er66, <- Er6; exact HZX)) as B8.
    pose proof (BD_frame (Start7.TP18 x rho6) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho6) rho8 rho9 (bv_unsigned b13) (bv_unsigned b13 + 8388608)
                  (TP18_pages x rho6 eq_refl Hxx H16x ltac:(rewrite Er66, Ex; exact R1) ltac:(rewrite Er66; exact R2) ltac:(rewrite Er66, Ex; exact R3) HT11)
                  (proj1 (proj2 F13)) M9 B8) as B9.
    assert (AG69 : agree_vars 36 rho6 rho9) by (split; [intros i Hi; rewrite (V9 i), (V8 i), (V7 i) by lia; reflexivity | intros l; rewrite L9, L8, L7; reflexivity]).
    rewrite (TP18_ext36 x rho6 rho9 AG69), (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ_ext rho6 rho9 ltac:(rewrite (V9 31%positive), (V8 31%positive), (V7 31%positive) by lia; reflexivity)). exact B9. }
  assert (HR9 : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK (mS a1 a2) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 rho9)
    by (apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK_agree (mS a1 a2) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 159%positive rho8 rho9); [lia | exact HR8 | intros i Hi; exact (V9 i Hi)]).
  assert (LL : forall l, rl rho9 l = rl rho l).
  { intros l. rewrite L9, L8, L7, L6, L5, L4, <- L3, rho_set_rw_rl, <- L2, rho_set_rw_rl. apply L1. }
  split; [exact G2|]. split; [exact G3|]. split; [exact HPL|]. split; [exact HPL4|]. split; [exact HPL5|]. split; [exact HPL6|].
  split; [exact HPL7|]. split; [exact HPL8|]. split; [exact HPL9|]. split; [exact Ex|]. split; [exact HPL10|]. split; [exact Ho|].
  split; [exact HPL12|]. split; [exact HPL13|]. split; [exact HPL14|].
  split; [exact MIm|]. split; [exact F12|]. split; [exact F13|]. split; [exact F14|].
  split; [exact CH|]. split; [exact LL|]. split; [exact RM9|]. split; [exact ZX9|]. split; [exact BD9|]. split; [exact HR9|].
  split; [rewrite CH7, V7, V6, E5lo by lia; exact H27c|]. split; [rewrite CH7, V7, V6, E5lo by lia; exact H28c|].
  split; [rewrite CH7, V7, V6, V5 by lia; exact H29|]. split; [rewrite CH7, V7, V6, V5 by lia; exact H30|]. split; [rewrite CH7, V7, V6 by lia; exact V31|].
  split; [rewrite CH7, V7, V6 by lia; exact H32|]. split; [rewrite CH7, V7, V6 by lia; exact H33|]. split; [rewrite CH7, V7, V6 by lia; exact H34|].
  split; [rewrite CH7, V7 by lia; exact H36|]. split; [rewrite CH7, V7 by lia; exact H77|]. split; [rewrite CH7, V7 by lia; exact H78|].
  split; [rewrite CH7 by lia; exact H79|]. split; [rewrite CH7 by lia; exact H80|]. split; [rewrite CH7 by lia; exact H81|].
  split; [rewrite CH7 by lia; exact H83|].
  split; [exact H159|]. split; [exact H160|]. split; [exact H161|].
  unfold Mmain, TPmain, Bmain. rewrite (Start7.TP18_ext x rho8 rho9); [exact Hsp | intros i Hi; exact (V9 i ltac:(lia)) | intros l; exact (L9 l)].
Qed.

Definition WTOT : Z := 21990232555520.

Lemma wit_of : ltac2:(tb__ "0|6|
S23S15S14SeQ40M0A1M1G1A2M2A1M3S2dS1G3S1dS1cR3A1A1S1dS1cVm;A1M4A1A3S1G3S20S1cR4A1A1R3A3S1G1S1eS1cR5A1A1S1eG4A1A3SaZ0M5R4A2S1S2dS6R5Z1000A2G5A3S4R6S7Z2Z26A2A2S4S3cR8A1S4dA2S4S8S1aG2R9A2A1Z40A2S2G1G1S2fSdG0G5A2RcSdG0RaA2R1A4La;A2F_;F_;F_;F_;F_;F_;F_;F_;Flen;FL;Fmd;").
Proof.
  clear - Hres Htop. intros md L len HR HM HI Hpos Hal Hlen Htot Hcnt.
  apply (place_witness md L len WTOT); try assumption.
  - rewrite HR. exact Hres.
  - unfold init_sp_ok in *. rewrite HI. exact Htop.
  - unfold WTOT. lia.
Qed.

Lemma gw_LS : ltac2:(tb__ "0|3|
SeQ40M0A1M1G1S1S2dS3cS13S14G1G1A2M2S18G1G1R1SdG0Z38e000A2A4S13G2S18G1G1R2SdG0Z10000A2A4S13G2S38S13G2S37S13G2S39S16G2A1A3A3A3A3A3A1Z10000039f000A3Fa2;Fa1;").
Proof. clear. intros. unfold HSe, GPe, LWe. cbn [gw_sizes snd]. rewrite !u64_of_lit by lia. reflexivity. Qed.

Lemma X18_small : ltac2:(tb__ "0|2|
S23SeQ40A1M0G0G0G0G0G0G0S2dG0S3fS0S4S3cS6eRbRaR9R8R7R6R5R4R3R2R1AbM1A1Z4000A2S4S8S1aS14G0G0A2G1A2A1Z2A2A2Fo;Fb10;Fx;Fb9;Fb8;Fb7;Fb6;Fb5;Fb4;FP;Fmm;").
Proof.
  clear. intros. destruct o as [[|a]|o1|o1 g]; [| |destruct o1|destruct o1]; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.X18, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.X1_18, n8w, n2w, pgw;
    cbn [gw_sizes length snd Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?u64_of_lit by lia; lia.
Qed.

Ltac gwlia := unfold HSe, GPe, LWe, n7, n9, n17; cbn [gw_sizes length snd List.app]; rewrite ?u64_of_lit by lia; unfold WTOT; lia.

Theorem startA_main_ex : ltac2:(tb__ "0|5|
S11S1S2dSfQ40M0S10R1P1M1A2A2SfG0S1eS1cVm;A1A1A2A3S4SfG0S10R2G1A2A2SfG0S10R2P4A2A2A2S4SfG0S10R3G1A2A2SfG0S10R3P6A2A2A2S0S4Z7fff80000000S31R4A1M2A2S4G2S7Z2Z2fA2M3A2A2S1S2dS6S31R5A1Z10M4A2Z0A3S4S5S31R6A1Z50A2S3eR6A1A2S4S5S3eR7A1G4A2G3A2S4S5S3eR8A1G4A2S5S31R8A1Z2228cfA2A2S54R9A1S71S30S56S30S51Vm;A1S55RaA4S48RaA1A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;").
Proof.
  intros rho Hv1 H14 H16r Hx H16 R1 R2 R3 HAL.
  assert (HB0 : B <= vm_limit (m_vmmaps m)) by (pose proof BS_lim; unfold BS in *; lia).

  eapply etriple_seq; [exact (start1_sum_ex_A m B Hlz Hmt Hres Hmaps Hna HusedB HB0 Htop rho H14 H16r (proj1 Hx))|].
  apply etriple_ex; intros rho1. apply etriple_pure; intros AG1. apply etriple_pure; intros RM1.
  pose proof AG1 as [V1 L1].
  assert (Hv1a : bv_unsigned (rw rho1 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps mB))) by (rewrite (V1 1%positive) by lia; rewrite mB_vmmaps; exact Hv1).
  assert (TB : init_sp_ok (m_vmmaps mB)) by (clear - Htop Hmaps Hna; unfold init_sp_ok in *; rewrite mB_vmmaps; exact Htop).
  assert (RB : vm_reserved (m_vmmaps mB) = segments_reserved segsA) by (rewrite mB_vmmaps; exact Hres).

  change (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1.m4 m) with mB.
  assert (Wt2 : exists a, mmap_place_ok_none (Z_to_bv 64 0) mB n5 a).
  { apply (wit_of mB [HSe; GPe; LWe] 0x10000); try (rewrite mB_vmmaps; reflexivity); try lia; try reflexivity; gwlia. }
  eapply etriple_seq; [exact (start2_sum_ex_A mB B RB TB band_B ltac:(rewrite mB_vmmaps; cbn [vm_limit]; pose proof BS_lim; unfold BS in *; lia) Wt2 rho1 Hv1a)|].
  apply etriple_ex; intros a1. apply etriple_ex; intros rho2. apply etriple_pure; intros G2. apply etriple_pure; intros AG2.
  pose proof AG2 as (V2 & L2 & M2).
  assert (H27b : rw rho2 27%positive = a1) by (rewrite <- (V2 27%positive) by lia; apply rho_set_rw_at).
  assert (E2lo : forall i, (i < 25)%positive -> rw rho2 i = rw rho i) by (intros i Hi; rewrite <- (V2 i) by lia; rewrite rho_set_rw_other by lia; apply V1; lia).
  pose proof (mA1_fields a1) as (RA & MA & LA & IA).
  assert (Hv1b : bv_unsigned (rw rho2 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps (mA1 a1)))) by (rewrite (E2lo 1%positive) by lia; rewrite IA; exact Hv1).
  assert (TA : init_sp_ok (m_vmmaps (mA1 a1))) by (clear - Htop IA; unfold init_sp_ok in *; rewrite IA; exact Htop).

  change (m5 mB a1) with (mA1 a1).
  assert (Wt3 : exists a, mmap_place_ok_none (Z_to_bv 64 0) (mA1 a1) n6 a).
  { apply (wit_of (mA1 a1) _ 0x38e000 RA MA IA); try lia; try reflexivity; gwlia. }
  eapply etriple_seq; [exact (start3_sum_ex_A (mA1 a1) a1 (B + 0x10000) ltac:(rewrite RA; exact Hres) ltac:(rewrite MA; left; reflexivity) TA (band_A1 a1)
                              ltac:(rewrite LA; pose proof BS_lim; unfold BS in *; lia) Wt3 rho2 H27b Hv1b)|].
  apply etriple_ex; intros a2. apply etriple_ex; intros rho3. apply etriple_pure; intros G3. apply etriple_pure; intros AG3.
  pose proof AG3 as (V3 & L3 & M3).
  assert (H28c : rw rho3 28%positive = a2) by (rewrite <- (V3 28%positive) by lia; apply rho_set_rw_at).
  assert (H27c : rw rho3 27%positive = a1) by (rewrite <- (V3 27%positive) by lia; rewrite rho_set_rw_other by lia; exact H27b).
  assert (E3lo : forall i, (i < 25)%positive -> rw rho3 i = rw rho i) by (intros i Hi; rewrite <- (V3 i) by lia; rewrite rho_set_rw_other by lia; apply E2lo; exact Hi).

  change (m6 (mA1 a1) a2) with (mS a1 a2). change (B + 0x10000 + 0x38e000) with BS.
  pose proof (mS_fields a1 a2) as (RS & MS & NS & LS & LMS & IS & KS & SKS).
  assert (SRES : vm_reserved (m_vmmaps (mS a1 a2)) = segments_reserved segsA) by (rewrite RS; exact Hres).
  assert (SMAPS : vm_maps (m_vmmaps (mS a1 a2)) = [(a2, Z_to_bv 64 0x38e000); (a1, Z_to_bv 64 0x10000);
            (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000); (Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000); (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000)])
    by (rewrite MS; reflexivity).
  assert (SNA : vm_noaccess (m_vmmaps (mS a1 a2)) = [(Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000)]) by (rewrite NS; reflexivity).
  assert (STOP : init_sp_ok (m_vmmaps (mS a1 a2))) by (clear - Htop IS; unfold init_sp_ok in *; rewrite IS; exact Htop).
  pose proof (a1_facts a1 G2) as (F1lo & F1band & F1top & F1al & F1free). pose proof (a2_facts a1 a2 G3) as (F2lo & F2band & F2top & F2al & F2free).
  assert (SA1 : 0x643000 <= bv_unsigned a1 /\ (bv_unsigned a1 + 0x10000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned a1) /\ bv_unsigned a1 + 0x10000 <= alloc_top (m_vmmaps (mS a1 a2))).
  { unfold alloc_top in *. rewrite IS. repeat split; assumption. }
  assert (SA2 : 0x643000 <= bv_unsigned a2 /\ (bv_unsigned a2 + 0x38e000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned a2) /\ bv_unsigned a2 + 0x38e000 <= alloc_top (m_vmmaps (mS a1 a2))).
  { unfold alloc_top in *. rewrite IS. repeat split; assumption. }
  assert (SBLIM : BS + 0x1000000 <= vm_limit (m_vmmaps (mS a1 a2))) by (rewrite LMS; exact BS_lim).
  assert (SSB : vm_start_brk (m_vmmaps (mS a1 a2)) = vm_brk (m_vmmaps (mS a1 a2))) by (rewrite KS, SKS; exact Hsb).
  assert (SBRK : 0x643000 <= bv_unsigned (vm_brk (m_vmmaps (mS a1 a2))) <= 0x80643000) by (rewrite KS; exact Hbrk).
  assert (SBAL : (4096 | bv_unsigned (vm_brk (m_vmmaps (mS a1 a2))))) by (rewrite KS; exact Hbal).
  assert (Hv1c : bv_unsigned (rw rho3 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps (mS a1 a2)))) by (rewrite (E3lo 1%positive) by lia; rewrite IS; exact Hv1).

  set (LS5 := [(a2, Z_to_bv 64 0x38e000); (a1, Z_to_bv 64 0x10000); HSe; GPe; LWe]).
  assert (MS5 : vm_maps (m_vmmaps (mS a1 a2)) = LS5) by (rewrite MS; reflexivity). pose proof (gw_LS a1 a2) as GW5. fold LS5 in GW5.
  assert (Wt7 : exists P, mmap_place_ok_none (Z_to_bv 64 0) (mS a1 a2) n7 P).
  { unfold n7. apply (wit_of (mS a1 a2) LS5 _ RS MS5 IS); try lia; try reflexivity; subst LS5; gwlia. }
  assert (Wt9 : forall P, mmap_place_ok_none (Z_to_bv 64 0) (mS a1 a2) n7 P -> exists a, mmap_place_ok_none (Z_to_bv 64 0) (m8 (mS a1 a2) P) n9 a).
  { intros P HPL. pose proof (m8_ledger (mS a1 a2) P) as (R8 & M8 & _ & I8 & _). unfold n9.
    apply (wit_of (m8 (mS a1 a2) P) ((P, n7) :: LS5) _ ltac:(rewrite R8; exact RS) ltac:(rewrite M8, MS5; reflexivity) ltac:(rewrite I8; exact IS)); try lia; try reflexivity; subst LS5; gwlia. }
  assert (Wt10 : forall P b4, mmap_place_ok_none (Z_to_bv 64 0) (mS a1 a2) n7 P -> mmap_place_ok_none (Z_to_bv 64 0) (m8 (mS a1 a2) P) n9 b4 ->
                exists a, mmap_place_ok_none (Z_to_bv 64 0) (m9 (mS a1 a2) P b4) (Z_to_bv 64 4096) a).
  { intros P b4 HPL HPL4. pose proof (m9_ledger (mS a1 a2) P b4) as (R9 & M9 & _ & I9 & _).
    apply (wit_of (m9 (mS a1 a2) P b4) ((b4, n9) :: (P, n7) :: LS5) _ ltac:(rewrite R9; exact RS) ltac:(rewrite M9, MS5; reflexivity) ltac:(rewrite I9; exact IS)); try lia; try reflexivity; subst LS5; gwlia. }
  assert (Wt11 : forall P b4 b5, mmap_place_ok_none (Z_to_bv 64 0) (mS a1 a2) n7 P -> mmap_place_ok_none (Z_to_bv 64 0) (m8 (mS a1 a2) P) n9 b4 ->
                mmap_place_ok_none (Z_to_bv 64 0) (m9 (mS a1 a2) P b4) (Z_to_bv 64 4096) b5 ->
                exists a, mmap_place_ok_none (Z_to_bv 64 0) (m10 (mS a1 a2) P b4 b5) (Z_to_bv 64 65536) a).
  { intros P b4 b5 HPL HPL4 HPL5. pose proof (m10_ledger (mS a1 a2) P b4 b5) as (R10 & M10 & _ & I10 & _).
    apply (wit_of (m10 (mS a1 a2) P b4 b5) ((b5, Z_to_bv 64 4096) :: (b4, n9) :: (P, n7) :: LS5) _ ltac:(rewrite R10; exact RS) ltac:(rewrite M10, MS5; reflexivity) ltac:(rewrite I10; exact IS));
      try lia; try reflexivity; subst LS5; gwlia. }

  eapply etriple_seq; [exact (start4_sum_ex_A (mS a1 a2) a1 a2 BS SRES SMAPS SNA LS STOP SA1 SA2 SBLIM Wt7 Wt9 Wt10 Wt11 rho3 H27c H28c Hv1c)|].
  apply etriple_ex; intros P. apply etriple_ex; intros rho4.
  apply etriple_pure; intros HPL. apply etriple_pure; intros AG4. apply etriple_pure; intros RM4. apply etriple_pure; intros H29. apply etriple_pure; intros H30.
  unfold Post4b. apply etriple_ex; intros b4. apply etriple_ex; intros b5. apply etriple_ex; intros b6. apply etriple_ex; intros hi. apply etriple_ex; intros rho5.
  apply etriple_pure; intros HPL4. apply etriple_pure; intros HPL5. apply etriple_pure; intros HPL6. apply etriple_pure; intros Hcls. apply etriple_pure; intros AG5.
  apply etriple_pure; intros RM5. apply etriple_pure; intros V31. apply etriple_pure; intros H32. apply etriple_pure; intros H33. apply etriple_pure; intros H34. apply etriple_pure; intros HZ11. apply etriple_pure; intros HZD5.
  pose proof AG4 as [V4 L4]. pose proof AG5 as [V5 L5].
  assert (E5lo : forall i, (i < 29)%positive -> rw rho5 i = rw rho3 i) by (intros i Hi; rewrite (V5 i), (V4 i) by lia; reflexivity).
  assert (HV5 : vals12 (mS a1 a2) a1 a2 P b4 b5 b6 rho5).
  { unfold vals12. rewrite (E5lo 27%positive), (E5lo 28%positive), (E5lo 1%positive) by lia. rewrite (V5 29%positive), (V5 30%positive) by lia.
    repeat split; assumption. }

  pose proof (mE_ledger (mS a1 a2) P b4 b5 b6) as (R11 & M11 & _ & I11 & _).
  set (LS11 := (b6, Z_to_bv 64 65536) :: (b5, Z_to_bv 64 4096) :: (b4, n9) :: (P, n7) :: LS5).
  assert (MS11 : vm_maps (m_vmmaps (m11 (mS a1 a2) P b4 b5 b6)) = LS11) by (rewrite M11, MS5; reflexivity).
  assert (Wt12 : exists a, mmap_place_ok_none (Z_to_bv 64 0) (m11 (mS a1 a2) P b4 b5 b6) (Z_to_bv 64 4096) a).
  { apply (wit_of _ LS11 _ ltac:(rewrite R11; exact RS) MS11 ltac:(rewrite I11; exact IS)); try lia; try reflexivity; subst LS11 LS5; gwlia. }
  assert (Wt13 : forall b7, mmap_place_ok_none (Z_to_bv 64 0) (m11 (mS a1 a2) P b4 b5 b6) (Z_to_bv 64 4096) b7 ->
                exists a, mmap_place_ok_none (Z_to_bv 64 0) (m12 (mS a1 a2) P b4 b5 b6 b7) (Z_to_bv 64 4096) a).
  { intros b7 HPL7. pose proof (m12_ledger (mS a1 a2) P b4 b5 b6 b7) as (R12 & M12 & _ & I12).
    apply (wit_of _ ((b7, Z_to_bv 64 4096) :: LS11) _ ltac:(rewrite R12; exact RS) ltac:(rewrite M12, MS11; reflexivity) ltac:(rewrite I12; exact IS)); try lia; try reflexivity; subst LS11 LS5; gwlia. }
  assert (Wt14 : forall b7 b8, mmap_place_ok_none (Z_to_bv 64 0) (m11 (mS a1 a2) P b4 b5 b6) (Z_to_bv 64 4096) b7 ->
                mmap_place_ok_none (Z_to_bv 64 0) (m12 (mS a1 a2) P b4 b5 b6 b7) (Z_to_bv 64 4096) b8 ->
                exists a, mmap_place_ok_none (Z_to_bv 64 0) (m13 (mS a1 a2) P b4 b5 b6 b7 b8) (Z_to_bv 64 4096) a).
  { intros b7 b8 HPL7 HPL8. pose proof (m13_ledger (mS a1 a2) P b4 b5 b6 b7 b8) as (R13 & M13 & _ & I13). pose proof (m12_ledger (mS a1 a2) P b4 b5 b6 b7) as (_ & M12 & _).
    apply (wit_of _ ((b8, Z_to_bv 64 4096) :: (b7, Z_to_bv 64 4096) :: LS11) _ ltac:(rewrite R13; exact RS) ltac:(rewrite M13, M12, MS11; reflexivity) ltac:(rewrite I13; exact IS));
      try lia; try reflexivity; subst LS11 LS5; gwlia. }

  eapply etriple_seq; [exact (start5_sum_ex_A (mS a1 a2) a1 a2 BS SRES SMAPS SNA LS STOP SA1 SA2 SBLIM P b4 b5 b6 HPL HPL4 HPL5 HPL6 Wt12 Wt13 Wt14 rho5 HV5 HZ11 HZD5)|].
  apply etriple_ex; intros b7. apply etriple_ex; intros b8. apply etriple_ex; intros b9. apply etriple_ex; intros rho6.
  apply etriple_pure; intros HPL7. apply etriple_pure; intros HPL8. apply etriple_pure; intros HPL9. apply etriple_pure; intros AG6.
  apply etriple_pure; intros H36. apply etriple_pure; intros H77. apply etriple_pure; intros H78. apply etriple_pure; intros HSSZ. apply etriple_pure; intros HZ11c. apply etriple_pure; intros HZD6. apply etriple_pure; intros RM6.
  pose proof AG6 as [V6 L6].
  assert (HV6 : vals12 (mS a1 a2) a1 a2 P b4 b5 b6 rho6) by (eapply (vals12_agree _ _ _ _ _ _ _ 36%positive rho5 rho6); [lia | exact HV5 | intros i Hi; apply V6; exact Hi]).

  assert (Wt17 : forall xx, exists a, mmap_place_ok_none (Z_to_bv 64 0) (m16 (mS a1 a2) P b4 b5 b6 b7 b8 b9 xx) (Z_to_bv 64 n17) a).
  { intros xx. pose proof (m16_fields (mS a1 a2) P b4 b5 b6 b7 b8 b9 xx) as (R16 & M16 & _ & I16 & _).
    pose proof (Start7.mE_fields (mS a1 a2) P b4 b5 b6 b7 b8 b9 xx b7) as (_ & MM & _).
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.maps_mE_eq (mS a1 a2) a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 xx b7) as ME.
    rewrite MM in ME. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.LmE in ME. cbn [List.app] in ME. pose proof (f_equal (@List.tl _) ME) as ME'. cbn [List.tl] in ME'.
    unfold n17. apply (wit_of _ _ _ ltac:(rewrite R16; exact RS) ME' ltac:(rewrite I16; exact IS)); try lia; try reflexivity; rewrite SMAPS; gwlia. }

  eapply etriple_seq; [exact (start6_sum_ex_A (mS a1 a2) a1 a2 BS SRES SMAPS SNA LS STOP SA1 SA2 SBLIM P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 Wt17
                              rho6 HV6 H36 H77 H78 HSSZ HZ11c (RMH_refl rho6))|].
  cbv zeta. apply etriple_ex; intros b10. apply etriple_ex; intros rho7.
  apply etriple_pure; intros HPL10. apply etriple_pure; intros AG7. apply etriple_pure; intros H79. apply etriple_pure; intros H80. apply etriple_pure; intros H81.
  apply etriple_pure; intros H83. apply etriple_pure; intros HRM6. apply etriple_pure; intros RM7. apply etriple_pure; intros HXF.
  pose proof AG7 as [V7 L7]. pose proof HXF as (Hxx & H16x & V35).
  set (x := x1 rho6) in *.
  assert (Ex : x = x1 rho).
  { subst x. unfold x1. rewrite (V6 1%positive), (E5lo 1%positive), (E3lo 1%positive) by lia. reflexivity. }
  assert (HV7 : vals12 (mS a1 a2) a1 a2 P b4 b5 b6 rho7) by (eapply (vals12_agree _ _ _ _ _ _ _ 79%positive rho6 rho7); [lia | exact HV6 | intros i Hi; apply V7; exact Hi]).
  assert (H36d : rw rho7 36%positive = b7) by (rewrite (V7 36%positive) by lia; exact H36).
  assert (H77d : rw rho7 77%positive = b8) by (rewrite (V7 77%positive) by lia; exact H77).
  assert (H78d : rw rho7 78%positive = b9) by (rewrite (V7 78%positive) by lia; exact H78).
  assert (Ex7 : x1 rho7 = x) by (subst x; unfold x1; rewrite (V7 1%positive) by lia; reflexivity).
  assert (Hxtop : alloc_top (m_vmmaps (mS a1 a2)) = x - 8388608).
  { unfold alloc_top. rewrite stack_max_size_val, <- Hv1c, <- (E5lo 1%positive), <- (V6 1%positive) by lia. subst x. reflexivity. }
  assert (Er6 : Start7.r6of rho7 = Start7.r6of rho).
  { unfold Start7.r6of. rewrite (V7 6%positive), (V6 6%positive), (E5lo 6%positive), (E3lo 6%positive) by lia. reflexivity. }
  assert (V35d : 8 * bv_unsigned (rw rho7 35%positive) = bv_unsigned b6) by (rewrite (V7 35%positive) by lia; exact V35).
  assert (HSZ : Start7.SZ18 x rho7).
  { apply (Start7.SZ18_of_RM6 (mS a1 a2) a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL HPL4 HPL5 HPL6 x Hxx H16x Hxtop rho6 rho7 HV6 eq_refl V35 HSSZ HRM6).
    - intros i Hi. apply V7. lia.
    - exact L7. }

  replace (TP17 rho6) with (TP17 rho7) by (unfold TP17; rewrite (TP16_ext rho6 rho7 (agree_vars_le 79 36 rho6 rho7 ltac:(lia) AG7)); reflexivity).
  eapply etriple_seq.
  { exact (Start7.eseg18 (mS a1 a2) a1 a2 BS SRES SMAPS SNA LS STOP SA1 SA2 SBLIM SSB SBRK SBAL ok OKF OKP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
             rho7 HV7 H36d H77d H78d H83 Ex7 ltac:(rewrite Er6, Ex; exact R1) ltac:(rewrite Er6; exact R2) ltac:(rewrite Er6, Ex; exact R3) HSZ
             (arg_layout_ext rho rho7 ltac:(intros i Hi; rewrite (V7 i), (V6 i), (E5lo i), (E3lo i) by lia; reflexivity) HAL)). }
  apply etriple_ex; intros o. apply etriple_ex; intros rho8.
  apply etriple_pure; intros Ho. apply etriple_pure; intros V8. apply etriple_pure; intros L8. apply etriple_pure; intros H84. apply etriple_pure; intros H85. apply etriple_pure; intros HZX.
  apply etriple_pure; intros RM8. apply etriple_pure; intros RL8. apply etriple_pure; intros RH8.

  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.minv8_out18 (mS a1 a2) a1 a2 SRES SMAPS SNA LS STOP SA1 SA2 SBRK P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
                (apart_S a1 a2 G2 G3) o Ho) as HMI.
  assert (HL0 : forall e, In e (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.LmE (mS a1 a2) P b4 b5 b6 b7 b8 b10) -> In e (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.L18 (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o)).
  { intros e He. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.L18. apply in_app_iff. right. exact He. }
  assert (HR7 : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK (mS a1 a2) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 rho7).
  { unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK. split; [exact HV7|]. split; [exact H36d|]. split; [exact H77d|]. split; [exact H78d|]. split; [exact H83|].
    split; [exact Ex7|]. split; [exact V35d|]. rewrite Er6, Ex. split; [exact R1|]. split; [exact R2 | exact R3]. }
  assert (HR8 : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK (mS a1 a2) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 rho8).
  { unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK. split; [eapply (vals12_agree _ _ _ _ _ _ _ 84%positive rho7 rho8); [lia | exact HV7 | intros i Hi; apply V8; exact Hi]|].
    rewrite !(V8 36%positive), !(V8 77%positive), !(V8 78%positive), !(V8 83%positive), !(V8 35%positive) by lia.
    split; [exact H36d|]. split; [exact H77d|]. split; [exact H78d|]. split; [exact H83|].
    split; [unfold x1; rewrite (V8 1%positive) by lia; exact Ex7|]. split; [exact V35d|].
    unfold Start7.r6of. rewrite (V8 6%positive) by lia. unfold Start7.r6of in Er6. rewrite Er6. unfold Start7.r6of in R1, R2, R3. rewrite Ex.
    split; [exact R1|]. split; [exact R2 | exact R3]. }

  pose proof (X18_small (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) as [XG XL].
  assert (GW18 : gw_sizes (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.L18 (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) <= 17592189841408 + 137459060736 + 16384
            /\ Z.of_nat (length (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.L18 (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o)) <= 14).
  { unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.L18, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.LmE. rewrite gw_sizes_app, length_app, Nat2Z.inj_add. rewrite SMAPS.
    unfold n7, n9, n17. cbn [gw_sizes length snd List.app Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite ?u64_of_lit by lia. lia. }
  destruct GW18 as [GW18 GL18].
  assert (Wt22 : exists a, mmap_place_ok_none (Z_to_bv 64 0) (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) (Z_to_bv 64 1048576) a).
  { apply (wit_of _ _ _ ltac:(rewrite (mi_res HMI); symmetry; exact Hres) (mi_maps HMI) ltac:(rewrite (mi_isp HMI), IS; reflexivity)); try lia; try reflexivity; unfold WTOT; lia. }
  assert (Wt23 : forall b12, mmap_place_ok_none (Z_to_bv 64 0) (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) (Z_to_bv 64 1048576) b12 ->
             exists a, mmap_place_ok_none (Z_to_bv 64 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m22 (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) b12) (Z_to_bv 64 8388608) a).
  { intros b12 HPL12. pose proof (minv8_eager _ _ _ _ _ 1048576 b12 HMI ltac:(lia) eq_refl ltac:(lia) HPL12) as MI2.
    apply (wit_of _ _ _ ltac:(rewrite (mi_res MI2); symmetry; exact Hres) (mi_maps MI2) ltac:(rewrite (mi_isp MI2), IS; reflexivity)); try lia; try reflexivity.
    - rewrite gw_sizes_cons, u64_of_lit by lia. unfold WTOT. lia.
    - cbn [length]. lia. }
  assert (Wt24 : forall b12 b13, mmap_place_ok_none (Z_to_bv 64 0) (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) (Z_to_bv 64 1048576) b12 ->
             mmap_place_ok_none (Z_to_bv 64 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m22 (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) b12) (Z_to_bv 64 8388608) b13 ->
             exists a, mmap_place_ok_none (Z_to_bv 64 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m23a (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) b12 b13) (Z_to_bv 64 4096) a).
  { intros b12 b13 HPL12 HPL13. pose proof (minv8_eager _ _ _ _ _ 1048576 b12 HMI ltac:(lia) eq_refl ltac:(lia) HPL12) as MI2.
    pose proof (minv8_null_rw _ _ _ _ _ 8388608 b13 MI2 ltac:(lia) eq_refl ltac:(lia) HPL13) as MI3.
    apply (wit_of _ _ _ ltac:(rewrite (mi_res MI3); symmetry; exact Hres) (mi_maps MI3) ltac:(rewrite (mi_isp MI3), IS; reflexivity)); try lia; try reflexivity.
    - rewrite !gw_sizes_cons, !u64_of_lit by lia. unfold WTOT. lia.
    - cbn [length]. lia. }
  rewrite <- (Start7.TP18_ext x rho7 rho8 V8 L8).
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.eseg22 (mS a1 a2) a1 a2 BS SRES SMAPS STOP SA1 SA2 SBLIM P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
               (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.L18 (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) HMI HL0 Wt22 Wt23 Wt24 rho8 HR8). }

  intros w (v & b12 & b13 & b14 & rho9 & HPL12 & HPL13 & HPL14 & V9 & H159 & H160 & H161 & L9 & M9 & Hsp).
  exists a1, a2, P, b4, b5, b6, b7, b8, b9, x, b10, o, v, b12, b13, b14, rho9.
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.MI_main (mS a1 a2) x Hxtop (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.L18 (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) HMI
                b12 b13 b14 HPL12 HPL13 HPL14) as (MIm & F12 & F13 & F14).
  unfold Start7.TOPz in F12, F13, F14. rewrite LMS, IS in MIm.
  assert (CH : forall i, (i < 25)%positive -> rw rho9 i = rw rho i).
  { intros i Hi. rewrite (V9 i), (V8 i), (V7 i), (V6 i), (E5lo i), (E3lo i) by lia. reflexivity. }
  assert (CH7 : forall i, (i < 84)%positive -> rw rho9 i = rw rho7 i) by (intros i Hi; rewrite (V9 i), (V8 i) by lia; reflexivity).
  assert (RM9 : RMH rho rho9).
  {
    assert (E8lo : forall i, (i < 7)%positive -> rw rho8 i = rw rho i) by (intros i Hi; rewrite (V8 i), (V7 i), (V6 i), (E5lo i), (E3lo i) by lia; reflexivity).
    intros a Ha. pose proof Ha as [HaLo _]. unfold x1 in Hx.
    rewrite (M9 a) by (rewrite Hv1 in HaLo; pose proof Hxtop as T; unfold alloc_top in T; rewrite IS, stack_max_size_val in T; lia).
    rewrite (RM8 a) by (apply (proj2 (ARGF_ext rho rho7 a ltac:(intros i Hi; rewrite (V7 i), (V6 i), (E5lo i), (E3lo i) by lia; reflexivity))); exact Ha).
    rewrite (RM7 a) by (apply (proj2 (ARGF_ext rho rho6 a ltac:(intros i Hi; rewrite (V6 i), (E5lo i), (E3lo i) by lia; reflexivity))); exact Ha).
    rewrite (RM6 a) by (apply (proj2 (ARGF_ext rho rho5 a ltac:(intros i Hi; rewrite (E5lo i), (E3lo i) by lia; reflexivity))); exact Ha).
    rewrite (RM5 a) by (apply (proj2 (ARGF_ext rho rho4 a ltac:(intros i Hi; rewrite (V4 i), (E3lo i) by lia; reflexivity))); exact Ha).
    rewrite (RM4 a) by (apply (proj2 (ARGF_ext rho rho3 a ltac:(intros i Hi; rewrite (E3lo i) by lia; reflexivity))); exact Ha).
    rewrite <- M3, rho_set_rw_rm, <- M2, rho_set_rw_rm. apply RM1. exact Ha. }
  assert (ZX9 : ZX18 x (Start7.r6of rho) rho9).
  {
    pose proof (Start7.arith18 x Hxx H16x (Start7.r6of rho) ltac:(rewrite Ex; exact R1) R2 ltac:(rewrite Ex; exact R3)) as AR.
    destruct AR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A14w & _ & _ & _ & Q18K & _ & _ & _ & _ & _ & QLO).
    intros z Hz. rewrite (M9 (Z_to_bv 64 z)).
    - rewrite <- Er6 in Hz. exact (HZX z Hz).
    - rewrite u64_of_lit by (unfold kHighMemBeg in *; lia). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, kHighMemBeg in *. lia. }
  assert (BD9 : BDT (Start7.TP18 x rho9) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho9) rho9).
  {
    assert (Er66 : Start7.r6of rho6 = Start7.r6of rho) by (unfold Start7.r6of; rewrite (V6 6%positive), (E5lo 6%positive), (E3lo 6%positive) by lia; reflexivity).
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.priZ_facts (mS a1 a2) a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL rho6 HV6) as (PR1 & PR2 & PR3 & _).
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.sbZ_facts' (mS a1 a2) a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL HPL4 HPL5 HPL6 rho6 HV6 V35) as SB1.
    change (x1 rho6) with x in PR1, SB1.
    pose proof (TP11_pages x rho6 eq_refl Hxx H16x (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.Upri (mS a1 a2) a1 a2 P b4 b5 b6 rho6 HV6) PR1 PR2 PR3 SB1) as HT11.
    assert (HG : forall a, SHADOW_BAND_LO <= a < kHighMemBeg -> Start7.grp_out o a).
    { intros a Ha. destruct o as [o0|o1|o1 g]; cbn [Start7.grp_out]; [exact I | exact I |].
      pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.X18_facts (mS a1 a2) a1 a2 SRES SMAPS SNA LS STOP SA1 SA2 SBRK P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
                    (apart_S a1 a2 G2 G3) (Start7.O18c o1 g) g OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.pgw Ho ltac:(left; reflexivity)) as (_ & _ & _ & _ & GB).
      pose proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.pgw_n as (_ & PG & _). rewrite PG in GB. clear - Ha GB. blia. }
    pose proof (BD12 rho6 HZD6 HSSZ) as B6.
    pose proof (BD17 x rho6 rho7 eq_refl Hxx H16x HT11 B6 HRM6) as B7.
    pose proof (BD18 x rho6 rho7 rho8 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho6) eq_refl Hxx H16x
                  ltac:(rewrite Er66, Ex; exact R1) ltac:(rewrite Er66; exact R2) ltac:(rewrite Er66, Ex; exact R3) HT11 B7
                  (lowb_adapter x rho7 rho7 rho8 o (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho6) Hxx (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ_ext rho6 rho7 (V7 31%positive ltac:(lia))) HG RL8)
                  (band_adapter x (Start7.r6of rho6) rho7 rho8 Hxx ltac:(rewrite Er66, <- Er6; exact RH8))
                  ltac:(rewrite Er66, <- Er6; exact HZX)) as B8.
    pose proof (BD_frame (Start7.TP18 x rho6) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho6) rho8 rho9 (bv_unsigned b13) (bv_unsigned b13 + 8388608)
                  (TP18_pages x rho6 eq_refl Hxx H16x ltac:(rewrite Er66, Ex; exact R1) ltac:(rewrite Er66; exact R2) ltac:(rewrite Er66, Ex; exact R3) HT11)
                  (proj1 (proj2 F13)) M9 B8) as B9.
    assert (AG69 : agree_vars 36 rho6 rho9) by (split; [intros i Hi; rewrite (V9 i), (V8 i), (V7 i) by lia; reflexivity | intros l; rewrite L9, L8, L7; reflexivity]).
    rewrite (TP18_ext36 x rho6 rho9 AG69), (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ_ext rho6 rho9 ltac:(rewrite (V9 31%positive), (V8 31%positive), (V7 31%positive) by lia; reflexivity)). exact B9. }
  assert (HR9 : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK (mS a1 a2) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 rho9)
    by (apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK_agree (mS a1 a2) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 159%positive rho8 rho9); [lia | exact HR8 | intros i Hi; exact (V9 i Hi)]).
  assert (LL : forall l, rl rho9 l = rl rho l).
  { intros l. rewrite L9, L8, L7, L6, L5, L4, <- L3, rho_set_rw_rl, <- L2, rho_set_rw_rl. apply L1. }
  split; [exact G2|]. split; [exact G3|]. split; [exact HPL|]. split; [exact HPL4|]. split; [exact HPL5|]. split; [exact HPL6|].
  split; [exact HPL7|]. split; [exact HPL8|]. split; [exact HPL9|]. split; [exact Ex|]. split; [exact HPL10|]. split; [exact Ho|].
  split; [exact HPL12|]. split; [exact HPL13|]. split; [exact HPL14|].
  split; [exact MIm|]. split; [exact F12|]. split; [exact F13|]. split; [exact F14|].
  split; [exact CH|]. split; [exact LL|]. split; [exact RM9|]. split; [exact ZX9|]. split; [exact BD9|]. split; [exact HR9|].
  split; [rewrite CH7, V7, V6, E5lo by lia; exact H27c|]. split; [rewrite CH7, V7, V6, E5lo by lia; exact H28c|].
  split; [rewrite CH7, V7, V6, V5 by lia; exact H29|]. split; [rewrite CH7, V7, V6, V5 by lia; exact H30|]. split; [rewrite CH7, V7, V6 by lia; exact V31|].
  split; [rewrite CH7, V7, V6 by lia; exact H32|]. split; [rewrite CH7, V7, V6 by lia; exact H33|]. split; [rewrite CH7, V7, V6 by lia; exact H34|].
  split; [rewrite CH7, V7 by lia; exact H36|]. split; [rewrite CH7, V7 by lia; exact H77|]. split; [rewrite CH7, V7 by lia; exact H78|].
  split; [rewrite CH7 by lia; exact H79|]. split; [rewrite CH7 by lia; exact H80|]. split; [rewrite CH7 by lia; exact H81|].
  split; [rewrite CH7 by lia; exact H83|].
  split; [exact H159|]. split; [exact H160|]. split; [exact H161|].
  unfold Mmain, TPmain, Bmain. rewrite (Start7.TP18_ext x rho8 rho9); [exact Hsp | intros i Hi; exact (V9 i ltac:(lia)) | intros l; exact (L9 l)].
Qed.

End TopA.
