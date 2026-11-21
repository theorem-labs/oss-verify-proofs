(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start state per CONFIG_RSEQ, a section flag passed down; the launch model's channel reader as a premise of the start-up, LPS 08b1429; wit_of and the witnesses it gives name Linux's own address, place_ok_linux, written as plain text; the reserved ledger is the image's entries then the vDSO/vvar pair, with the pair in the ledger and the ledger's entries apart as premises the launch proves, a1_facts and a2_facts written as plain text; the break's page alignment passed to o9's minv8_out18 and X18_facts, LPS b07fadb; segment 7 runs per CONFIG_RSEQ, the flag passed to it, with the random bytes' 16-byte alignment, which its join of the two exits reads, a premise the launch proves, startA_main and startA_main_ex written as plain text; the launch's head equation, ARG_HGAP, passed to segment 7 the same way, and PostMain giving the memory map's presence on the dropped auxv tail, written as plain text). *)

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
(* LPS 727298f3: the start state [S_ctor] is made per CONFIG_RSEQ (StartStates.v); [rq] is this
   run's value, the launch's [kb_rseq (in_kernel inp)] (StartMain.v). *)
Variable rq : bool.
Hypothesis Hh0 : m_halted m = None.
Hypothesis Hlz : m_vm_lazy m = [].
Hypothesis Hmt : m_vm_materialized m = [].
(* LPS 727298f3: the reserved ledger is the image's entries then the vDSO/vvar pair (Fw/SysSpec.v [vdso_pair_ok]). *)
Hypothesis Hres : exists V, vm_reserved (m_vmmaps m) = segments_reserved segsA ++ V /\ vdso_pair_ok V.
Hypothesis Hmaps : ltac2:(tb__ "0|2|
S1S15S14SeQ40A1M0G0A2M1A1S20S1cVm;A1A1S16G1A1A3").
Hypothesis Hna : ltac2:(tb__ "0|2|
S1S15S14SeQ40A1M0G0A2M1A1S29S1cVm;A1A1S16G1A1A3").
Hypothesis HusedB : vm_backing_used m <= B.
Hypothesis HBlim : ltac2:(tb__ "0|0|
S4S5S5VB;Z39e000A2Z1000000A2S1fS1cVm;A1A1A2").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
(* LPS 08b1429: the launch model's channel reader; [MI] carries it from here on. *)
Hypothesis Hrdm : m_channel_reader m = true.
Hypothesis Hsb : ltac2:(tb__ "0|1|
S1SeQ40A1S25S1cVm;A1M0A1S22G0A1A3").
Hypothesis Hbrk : ltac2:(tb__ "0|1|
S0S4Z643000SfQ40S22S1cVm;A1A1A2M0A2S4G0Z80643000A2A2").
Hypothesis Hbal : ltac2:(tb__ "0|0|
S9Z1000SfQ40S22S1cVm;A1A1A2A2").
(* LPS 727298f3: the launch's vDSO/vvar pair is in the reserved ledger (State.v
   [vm_reserved_init_model]); Start7's [seg18] reads it. *)
Hypothesis Hvdr : forall e, In e (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m))) -> In e (vm_reserved (m_vmmaps m)).
(* LPS 727298f3: the reserved ledger's entries are apart from each other, the vDSO/vvar pair's two
   included (StartMain.v [resv_apart_M1], from the launch); [apart_S] reads it. *)
Hypothesis Hrap : ranges_apart (vm_reserved (m_vmmaps m)).
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

(* LPS 727298f3: the grant is free of the whole reserved ledger (the image's entries, then the vDSO/vvar
   pair), not only of the image's entries; [apart_S] reads it.  Statement written as plain text. *)
Lemma a1_facts : forall a1 : word, mmap_place_ok_none (Z_to_bv 64 0) mB n5 a1 ->
  0x643000 <= bv_unsigned a1 /\ (bv_unsigned a1 + 0x10000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned a1) /\
  bv_unsigned a1 + 0x10000 <= alloc_top (m_vmmaps m) /\ bv_unsigned a1 mod 4096 = 0 /\
  region_free (vm_reserved (m_vmmaps m) ++ [HSe; GPe; LWe]) a1 (Z_to_bv 64 0x10000) = true.
Proof.
  clear - Hmaps Hna Hres Htop. intros a1 Hpl.
  assert (T : init_sp_ok (m_vmmaps mB)) by (unfold init_sp_ok in *; rewrite mB_vmmaps; exact Htop).
  pose proof (place_LB_A mB 0x10000 a1 T ltac:(rewrite mB_vmmaps; exact Hres) band_B ltac:(lia) ltac:(reflexivity) Hpl) as (P1 & P2 & P3 & P4 & _).
  change (LB_of 0x10000) with 0x643000 in P1. unfold alloc_top in P4 |- *. rewrite mB_vmmaps in P4. cbn [vm_init_sp] in P4.
  pose proof Hpl as (Pal & _ & _ & Pfree). rewrite mB_vmmaps in Pfree. cbn [vm_reserved vm_maps] in Pfree.
  replace (mmap_n n5) with (Z_to_bv 64 0x10000) in Pfree by (symmetry; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  unfold page_size in Pal. repeat split; try assumption.
Qed.

(* LPS 727298f3: as [a1_facts], the grant free of the whole reserved ledger.  Statement written as plain text. *)
Lemma a2_facts : forall a1 a2 : word, mmap_place_ok_none (Z_to_bv 64 0) (mA1 a1) n6 a2 ->
  0x643000 <= bv_unsigned a2 /\ (bv_unsigned a2 + 0x38e000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned a2) /\
  bv_unsigned a2 + 0x38e000 <= alloc_top (m_vmmaps m) /\ bv_unsigned a2 mod 4096 = 0 /\
  region_free (vm_reserved (m_vmmaps m) ++ [(a1, Z_to_bv 64 0x10000); HSe; GPe; LWe]) a2 (Z_to_bv 64 0x38e000) = true.
Proof.
  clear - Hmaps Hna Hres Htop. intros a1 a2 Hpl. pose proof (mA1_fields a1) as (R & M & L & I).
  assert (T : init_sp_ok (m_vmmaps (mA1 a1))) by (unfold init_sp_ok in *; rewrite I; exact Htop).
  pose proof (place_LB_A (mA1 a1) 0x38e000 a2 T ltac:(rewrite R; exact Hres) (band_A1 a1) ltac:(lia) ltac:(reflexivity) Hpl) as (P1 & P2 & P3 & P4 & _).
  change (LB_of 0x38e000) with 0x643000 in P1. unfold alloc_top in P4 |- *. rewrite I in P4.
  pose proof Hpl as (Pal & _ & _ & Pfree). rewrite R, M in Pfree.
  replace (mmap_n n6) with (Z_to_bv 64 0x38e000) in Pfree by (symmetry; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  unfold page_size in Pal. repeat split; try assumption.
Qed.

(* LPS 727298f3: the reserved ledger (the image's entries, then the vDSO/vvar pair) is apart from the
   initial maps and within itself: the image's entries by [apart_base], the ledger within itself by
   [Hrap], and the pair from the maps because each pair entry starts at or above [VDSO_FLOOR]
   (Fw/SysSpec.v [vdso_pair_ok]), where the high shadow [HSe] ends; [GPe] and [LWe] end below it. *)
Lemma apart_res : ranges_apart (vm_reserved (m_vmmaps m) ++ [HSe; GPe; LWe]).
Proof.
  clear - Hres Hrap. pose proof Hres as (V & EV & _ & HV).
  pose proof (proj1 (ranges_apart_app _ _) apart_base) as (_ & B2 & B3).
  apply (proj2 (ranges_apart_app _ _)). split; [exact Hrap|]. split; [exact B2|].
  intros e1 e2 He1 He2. rewrite EV in He1. apply in_app_iff in He1 as [He1|He1]; [exact (B3 e1 e2 He1 He2)|].
  destruct (HV e1 He1) as (Hfl & _). destruct e1 as [b s]. cbn [fst] in Hfl. unfold VDSO_FLOOR in Hfl.
  unfold apartW. right. unfold HSe, GPe, LWe in He2.
  destruct He2 as [<-|[<-|[<-|[]]]]; cbn [fst snd]; rewrite !u64_of_lit by lia; lia.
Qed.

Lemma apart_S : ltac2:(tb__ "0|4|
SeQ40M0A1M1G1S2fSdG0Z0A2M2S45S4fR2A4S2fG2S46R3A1S50R2A4S52S17S14G1G1A2S1dS1cS47R4R3A2A1M3A1S20G3A1A3A1F_;F_;Fa2;Fa1;").
Proof.
  (* LPS 727298f3: the ledger is not rewritten to the image's entries; the grants are free of the whole
     ledger ([a1_facts], [a2_facts]) and the ledger is apart from the initial maps ([apart_res]). *)
  clear - Hmaps Hna Hlz Hres Htop Hrap. intros a1 a2 G2 G3. pose proof (mS_fields a1 a2) as (R & M & _). rewrite R, M.
  pose proof (a1_facts a1 G2) as (_ & _ & _ & _ & F1). pose proof (a2_facts a1 a2 G3) as (_ & _ & _ & _ & F2).
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F2 He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F1 He)].
  exact apart_res.
Qed.

Definition Mmain (a1 a2 P b4 b5 b6 b7 b8 b9 : word) (x : Z) (b10 : word) (o : out18) (b12 b13 b14 : word) : Model := ltac2:(tb__ "0|0|
S6bS40S47Va1;Va2;A2VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;AbVb12;Vb13;Vb14;A4").
Definition Lmain (a1 a2 P b4 b5 b6 b7 b8 b9 : word) (x : Z) (b10 : word) (o : out18) (b12 b13 b14 : word) : list (word * word) := ltac2:(tb__ "0|0|
S66S6dS47Va1;Va2;A2VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;AbVb12;Vb13;Vb14;A4").
Definition Bmain : Z := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.Bmain BS.

(* LPS 727298f3: the start-up's post also gives the memory map's presence on [ARG_TAIL] (B/n1.v), the auxv
   tail segment 7's join dropped (B/Start7.v [Post18]); otherwise main's decoded statement.  Written as
   plain text. *)
Definition PostMain (rho : valuation) : assn :=
  (fun (w : (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.world)) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun (a1 : (@stdpp.bitvector.definitions.bv 64%N)) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun (a2 : (@stdpp.bitvector.definitions.bv 64%N)) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun (P : (@stdpp.bitvector.definitions.bv 64%N)) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun (b4 : (@stdpp.bitvector.definitions.bv 64%N)) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun (b5 : (@stdpp.bitvector.definitions.bv 64%N)) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun (b6 : (@stdpp.bitvector.definitions.bv 64%N)) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun (b7 : (@stdpp.bitvector.definitions.bv 64%N)) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun (b8 : (@stdpp.bitvector.definitions.bv 64%N)) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun (b9 : (@stdpp.bitvector.definitions.bv 64%N)) => (@Corelib.Init.Logic.ex (@Corelib.Numbers.BinNums.Z) (fun (x : (@Corelib.Numbers.BinNums.Z)) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun (b10 : (@stdpp.bitvector.definitions.bv 64%N)) => (@Corelib.Init.Logic.ex (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.out18) (fun (o : (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.out18)) => (@Corelib.Init.Logic.ex (@Corelib.Init.Datatypes.bool) (fun (v : (@Corelib.Init.Datatypes.bool)) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun (b12 : (@stdpp.bitvector.definitions.bv 64%N)) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun (b13 : (@stdpp.bitvector.definitions.bv 64%N)) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun (b14 : (@stdpp.bitvector.definitions.bv 64%N)) => (@Corelib.Init.Logic.ex (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.valuation) (fun (rho' : (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.valuation)) => (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.mmap_place_ok_none (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z) (@mB) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start2.n5) a1) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.mmap_place_ok_none (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z) (@mA1 a1) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start3.n6) a2) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.mmap_place_ok_none (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z) (@mS a1 a2) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.n7) P) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.mmap_place_ok_none (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.m8 (@mS a1 a2) P) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.n9) b4) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.mmap_place_ok_none (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.m9 (@mS a1 a2) P b4) (@stdpp.bitvector.definitions.Z_to_bv 64%N 4096%Z) b5) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.mmap_place_ok_none (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.m10 (@mS a1 a2) P b4 b5) (@stdpp.bitvector.definitions.Z_to_bv 64%N 65536%Z) b6) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.mmap_place_ok_none (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.m11 (@mS a1 a2) P b4 b5 b6) (@stdpp.bitvector.definitions.Z_to_bv 64%N 4096%Z) b7) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.mmap_place_ok_none (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.m12 (@mS a1 a2) P b4 b5 b6 b7) (@stdpp.bitvector.definitions.Z_to_bv 64%N 4096%Z) b8) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.mmap_place_ok_none (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.m13 (@mS a1 a2) P b4 b5 b6 b7 b8) (@stdpp.bitvector.definitions.Z_to_bv 64%N 4096%Z) b9) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) x (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.x1 rho)) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.mmap_place_ok_none (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.m16 (@mS a1 a2) P b4 b5 b6 b7 b8 b9 x) (@stdpp.bitvector.definitions.Z_to_bv 64%N (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.n17)) b10) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.out18_ok (@mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.mmap_place_ok_none (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.out18_model (@mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) (@stdpp.bitvector.definitions.Z_to_bv 64%N 1048576%Z) b12) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.mmap_place_ok_none (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m22 (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.out18_model (@mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) b12) (@stdpp.bitvector.definitions.Z_to_bv 64%N 8388608%Z) b13) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.mmap_place_ok_none (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m23a (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.out18_model (@mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) b12 b13) (@stdpp.bitvector.definitions.Z_to_bv 64%N 4096%Z) b14) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M.minv8 (@Lmain a1 a2 P b4 b5 b6 b7 b8 b9 x b10 o b12 b13 b14) (@LinuxProcessSemantics.LinuxProcessSem.State.vm_limit (@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps m)) (@LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp (@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps m)) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.Q18 x) (@Mmain a1 a2 P b4 b5 b6 b7 b8 b9 x b10 o b12 b13 b14)) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le 6565888%Z (@stdpp.bitvector.definitions.bv_unsigned 64%N b12)) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b12) 1048576%Z) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement.SHADOW_BAND_LO)) (@Stdlib.ZArith.BinInt.Z.le (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement.SHADOW_BAND_HI) (@stdpp.bitvector.definitions.bv_unsigned 64%N b12))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@Stdlib.ZArith.BinInt.Z.modulo (@stdpp.bitvector.definitions.bv_unsigned 64%N b12) 4096%Z) 0%Z) (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b12) 1048576%Z) (@Stdlib.ZArith.BinInt.Z.sub x 8388608%Z))))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le 6565888%Z (@stdpp.bitvector.definitions.bv_unsigned 64%N b13)) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b13) 8388608%Z) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement.SHADOW_BAND_LO)) (@Stdlib.ZArith.BinInt.Z.le (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement.SHADOW_BAND_HI) (@stdpp.bitvector.definitions.bv_unsigned 64%N b13))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@Stdlib.ZArith.BinInt.Z.modulo (@stdpp.bitvector.definitions.bv_unsigned 64%N b13) 4096%Z) 0%Z) (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b13) 8388608%Z) (@Stdlib.ZArith.BinInt.Z.sub x 8388608%Z))))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le 4096%Z (@stdpp.bitvector.definitions.bv_unsigned 64%N b14)) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b14) 4096%Z) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement.SHADOW_BAND_LO)) (@Stdlib.ZArith.BinInt.Z.le (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement.SHADOW_BAND_HI) (@stdpp.bitvector.definitions.bv_unsigned 64%N b14))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@Stdlib.ZArith.BinInt.Z.modulo (@stdpp.bitvector.definitions.bv_unsigned 64%N b14) 4096%Z) 0%Z) (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N b14) 4096%Z) (@Stdlib.ZArith.BinInt.Z.sub x 8388608%Z))))) (@Corelib.Init.Logic.and (forall (i : (@Corelib.Numbers.BinNums.positive)), ((@Stdlib.PArith.BinPos.Pos.lt i 25%positive) -> (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' i) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho i)))) (@Corelib.Init.Logic.and (forall (l : (@Corelib.Numbers.BinNums.positive)), (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rl rho' l) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rl rho l))) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS.RMH rho rho') (@Corelib.Init.Logic.and (forall a : bv 64, ARG_TAIL rho a -> rm rho' a <> None) (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.ZX18 x (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.r6of rho) rho') (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.StartBD.BDT (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.TP18 x rho') (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho') rho') (@Corelib.Init.Logic.and (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK (@mS a1 a2) a1 a2 P b4 b5 b6 b7 b8 b9 x b10 rho') (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 27%positive) a1) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 28%positive) a2) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 29%positive) P) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 30%positive) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.spacebeg P)) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@Stdlib.ZArith.BinInt.Z.mul 8%Z (@stdpp.bitvector.definitions.bv_unsigned 64%N (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 31%positive))) (@stdpp.bitvector.definitions.bv_unsigned 64%N (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.spacebeg P))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 32%positive) b4) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 33%positive) b5) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 34%positive) b6) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 36%positive) b7) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 77%positive) b8) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 78%positive) b9) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 79%positive) (@stdpp.bitvector.definitions.Z_to_bv 64%N (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.v79Z x))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 80%positive) (@stdpp.bitvector.definitions.Z_to_bv 64%N (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.v80Z x))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 81%positive) (@stdpp.bitvector.definitions.Z_to_bv 64%N (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.topZ x))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 83%positive) b10) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 159%positive) b12) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 160%positive) b13) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.rw rho' 161%positive) b14) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA.SPA (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts.segsA) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA.KxA (@Mmain a1 a2 P b4 b5 b6 b7 b8 b9 x b10 o b12 b13 b14) (@Bmain)) (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.MAIN_of v) rho' (@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.TPmain x b13 rho') w)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Lemma BS_lim : ltac2:(tb__ "0|0|
S4S5S49Z1000000A2S1fS1cVm;A1A1A2").
Proof. clear - HBlim. unfold BS. lia. Qed.

(* LPS 727298f3: the last premise, the random bytes' 16-byte alignment, is proved at the launch
   (StartMain.v [rand16_of_Jinit]); segment 7's join of its two CONFIG_RSEQ exits reads it
   (B/StartRegen3.v [K18_join]).  Written as plain text. *)
Theorem startA_main : forall rho : valuation,
  bv_unsigned (rw rho 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m)) ->
  bv_unsigned (rw rho 1%positive) <= bv_unsigned (rw rho 4%positive) ->
  bv_unsigned (rw rho 1%positive) <= bv_unsigned (rw rho 6%positive) ->
  140735340871680 <= OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.x1 rho <= 2 ^ 47 ->
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.x1 rho mod 16 = 0 ->
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.x1 rho + 80 <= OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.r6of rho ->
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.r6of rho + 16 <= 2 ^ 47 ->
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.r6of rho + 16 <= OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.x1 rho + 2238671 ->
  arg_layout rho ->
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.r6of rho mod 16 = 0 ->
  ARG_HGAP rq rho ->
  triple segsA ok (SP segsA (Kx m) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartStates.S_ctor rq) rho) (PostMain rho).
Proof.
  intros rho Hv1 H14 H16r Hx H16 R1 R2 R3 HAL HR16 HGP.
  assert (HB0 : B <= vm_limit (m_vmmaps m)) by (pose proof BS_lim; unfold BS in *; lia).

  eapply triple_seq; [exact (start1_sum_A m B rq Hh0 Hlz Hmt Hres Hmaps Hna HusedB HB0 Htop Hrdm ok OK0 OKF OKP rho H14 H16r (proj1 Hx))|].
  apply triple_ex; intros rho1. apply triple_pure; intros AG1. apply triple_pure; intros RM1.
  pose proof AG1 as [V1 L1].
  assert (Hv1a : bv_unsigned (rw rho1 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps mB))) by (rewrite (V1 1%positive) by lia; rewrite mB_vmmaps; exact Hv1).
  assert (TB : init_sp_ok (m_vmmaps mB)) by (clear - Htop Hmaps Hna; unfold init_sp_ok in *; rewrite mB_vmmaps; exact Htop).
  assert (RB : exists V, vm_reserved (m_vmmaps mB) = segments_reserved segsA ++ V /\ vdso_pair_ok V) by (rewrite mB_vmmaps; exact Hres).

  change (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1.m4 m) with mB.
  eapply triple_seq; [exact (start2_sum_A mB B rq RB TB band_B ltac:(rewrite mB_vmmaps; cbn [vm_limit]; pose proof BS_lim; unfold BS in *; lia) ok OKF OKP rho1 Hv1a)|].
  apply triple_ex; intros a1. apply triple_ex; intros rho2. apply triple_pure; intros G2. apply triple_pure; intros AG2.
  pose proof AG2 as (V2 & L2 & M2).
  assert (H27b : rw rho2 27%positive = a1) by (rewrite <- (V2 27%positive) by lia; apply rho_set_rw_at).
  assert (E2lo : forall i, (i < 25)%positive -> rw rho2 i = rw rho i) by (intros i Hi; rewrite <- (V2 i) by lia; rewrite rho_set_rw_other by lia; apply V1; lia).
  pose proof (mA1_fields a1) as (RA & MA & LA & IA).
  assert (Hv1b : bv_unsigned (rw rho2 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps (mA1 a1)))) by (rewrite (E2lo 1%positive) by lia; rewrite IA; exact Hv1).
  assert (TA : init_sp_ok (m_vmmaps (mA1 a1))) by (clear - Htop IA; unfold init_sp_ok in *; rewrite IA; exact Htop).

  change (m5 mB a1) with (mA1 a1).
  eapply triple_seq; [exact (start3_sum_A (mA1 a1) a1 (B + 0x10000) rq ltac:(rewrite RA; exact Hres) ltac:(rewrite MA; left; reflexivity) TA (band_A1 a1)
                              ltac:(rewrite LA; pose proof BS_lim; unfold BS in *; lia) ok OKF OKP rho2 H27b Hv1b)|].
  apply triple_ex; intros a2. apply triple_ex; intros rho3. apply triple_pure; intros G3. apply triple_pure; intros AG3.
  pose proof AG3 as (V3 & L3 & M3).
  assert (H28c : rw rho3 28%positive = a2) by (rewrite <- (V3 28%positive) by lia; apply rho_set_rw_at).
  assert (H27c : rw rho3 27%positive = a1) by (rewrite <- (V3 27%positive) by lia; rewrite rho_set_rw_other by lia; exact H27b).
  assert (E3lo : forall i, (i < 25)%positive -> rw rho3 i = rw rho i) by (intros i Hi; rewrite <- (V3 i) by lia; rewrite rho_set_rw_other by lia; apply E2lo; exact Hi).

  change (m6 (mA1 a1) a2) with (mS a1 a2). change (B + 0x10000 + 0x38e000) with BS.
  pose proof (mS_fields a1 a2) as (RS & MS & NS & LS & LMS & IS & KS & SKS).
  assert (SRES : exists V, vm_reserved (m_vmmaps (mS a1 a2)) = segments_reserved segsA ++ V /\ vdso_pair_ok V) by (rewrite RS; exact Hres).
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
  assert (SVDR : forall e, In e (vdso_reserved (m_kernel (mS a1 a2)) (vdso_top (m_vmmaps (mS a1 a2)))) -> In e (vm_reserved (m_vmmaps (mS a1 a2))))
    by (intros e He; rewrite RS; exact (Hvdr e He)).
  assert (Hv1c : bv_unsigned (rw rho3 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps (mS a1 a2)))) by (rewrite (E3lo 1%positive) by lia; rewrite IS; exact Hv1).
  assert (HF8 : forall mm BB r tp Q, triple segsA ok (SPA segsA (KxA mm BB) (fail_state (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartRegenS2.Start4R.E_k8x rq)) r tp) Q) by (intros; apply (s8_fail_safe ok OKF rq)).

  eapply triple_seq; [exact (start4_sum_A (mS a1 a2) a1 a2 BS rq SRES SMAPS SNA LS STOP SA1 SA2 SBLIM ok OKF OKP HF8 rho3 H27c H28c Hv1c)|].
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

  eapply triple_seq; [exact (start5_sum_A (mS a1 a2) a1 a2 BS rq SRES SMAPS SNA LS STOP SA1 SA2 SBLIM ok OKF OKP P b4 b5 b6 HPL HPL4 HPL5 HPL6 rho5 HV5 HZ11 HZD5)|].
  apply triple_ex; intros b7. apply triple_ex; intros b8. apply triple_ex; intros b9. apply triple_ex; intros rho6.
  apply triple_pure; intros HPL7. apply triple_pure; intros HPL8. apply triple_pure; intros HPL9. apply triple_pure; intros AG6.
  apply triple_pure; intros H36. apply triple_pure; intros H77. apply triple_pure; intros H78. apply triple_pure; intros HSSZ. apply triple_pure; intros HZ11c. apply triple_pure; intros HZD6. apply triple_pure; intros RM6.
  pose proof AG6 as [V6 L6].
  assert (HV6 : vals12 (mS a1 a2) a1 a2 P b4 b5 b6 rho6) by (eapply (vals12_agree _ _ _ _ _ _ _ 36%positive rho5 rho6); [lia | exact HV5 | intros i Hi; apply V6; exact Hi]).

  eapply triple_seq; [exact (start6_sum_A (mS a1 a2) a1 a2 BS rq SRES SMAPS SNA LS STOP SA1 SA2 SBLIM ok OKF OKP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9
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
  { exact (Start7.seg18 (mS a1 a2) a1 a2 BS rq SRES SMAPS SNA LS STOP SA1 SA2 SBLIM SSB SBRK SBAL SVDR ok OKF OKP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
             rho7 HV7 H36d H77d H78d H83 Ex7 ltac:(rewrite Er6, Ex; exact R1) ltac:(rewrite Er6; exact R2) ltac:(rewrite Er6, Ex; exact R3) HSZ
             (arg_layout_ext rho rho7 ltac:(intros i Hi; rewrite (V7 i), (V6 i), (E5lo i), (E3lo i) by lia; reflexivity) HAL)
             ltac:(rewrite Er6; exact HR16)
             (proj2 (ARG_HGAP_ext rq rho rho7 ltac:(intros i Hi; rewrite (V7 i), (V6 i), (E5lo i), (E3lo i) by lia; reflexivity)) HGP)). }
  apply triple_ex; intros o. apply triple_ex; intros rho8.
  apply triple_pure; intros Ho. apply triple_pure; intros V8. apply triple_pure; intros L8. apply triple_pure; intros H84. apply triple_pure; intros H85. apply triple_pure; intros HZX.
  apply triple_pure; intros RM8. apply triple_pure; intros TL8. apply triple_pure; intros RL8. apply triple_pure; intros RH8.

  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.minv8_out18 (mS a1 a2) a1 a2 SRES SMAPS SNA LS STOP SA1 SA2 SBRK SBAL P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
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
  (* LPS 727298f3: the memory map's presence on the dropped auxv tail, from segment 7's post, kept by
     segment 22's calls, whose windows lie below the stack (as for [RM9]). *)
  assert (TL9 : forall a : word, ARG_TAIL rho a -> rm rho9 a <> None).
  { intros a Ha. pose proof Ha as [HaLo _]. unfold x1 in Hx.
    pose proof (urange (rw rho 2%positive)) as U2. pose proof (urange (rw rho 3%positive)) as U3.
    rewrite (M9 a) by (rewrite Hv1 in HaLo; pose proof Hxtop as T; unfold alloc_top in T; rewrite IS, stack_max_size_val in T; lia).
    apply (TL8 a). apply (proj2 (ARG_TAIL_ext rho rho7 a ltac:(intros i Hi; rewrite (V7 i), (V6 i), (E5lo i), (E3lo i) by lia; reflexivity))). exact Ha. }
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
      pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.X18_facts (mS a1 a2) a1 a2 SRES SMAPS SNA LS STOP SA1 SA2 SBRK SBAL P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
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
  split; [exact CH|]. split; [exact LL|]. split; [exact RM9|]. split; [exact TL9|]. split; [exact ZX9|]. split; [exact BD9|]. split; [exact HR9|].
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

(* LPS 727298f3: the witness is Linux's own address ([place_ok_linux], Fw/SysSpec.v), where a granted
   NULL-hint mmap now goes.  Decoded from this file's [tbs__] table, the conclusion restated; written as
   plain text.  The ledger premise is the prefix form (the image's entries then the vDSO/vvar pair,
   Fw/SysSpec.v [vdso_pair_ok]), which n9's [place_witness] takes and Start8M's [mi_res] gives. *)
Lemma wit_of : (forall (md : LinuxProcessSemantics.LinuxProcessSem.State.Model), (forall (L : (Corelib.Init.Datatypes.list (Corelib.Init.Datatypes.prod (stdpp.bitvector.definitions.bv 64) (stdpp.bitvector.definitions.bv 64)))), (forall (len : Corelib.Numbers.BinNums.Z), ((exists V, LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved (LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps md) = LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts.segsA ++ V /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.vdso_pair_ok V) -> ((@Corelib.Init.Logic.eq (Corelib.Init.Datatypes.list (Corelib.Init.Datatypes.prod (stdpp.bitvector.definitions.bv 64) (stdpp.bitvector.definitions.bv 64))) (LinuxProcessSemantics.LinuxProcessSem.State.vm_maps (LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps md)) L) -> ((@Corelib.Init.Logic.eq (stdpp.bitvector.definitions.bv 64) (LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp (LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps md)) (LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp (LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps m))) -> ((Stdlib.ZArith.BinInt.Z.lt 0 len) -> ((@Corelib.Init.Logic.eq Corelib.Numbers.BinNums.Z (Stdlib.ZArith.BinInt.Z.modulo len 4096) 0) -> ((Stdlib.ZArith.BinInt.Z.le len (Stdlib.ZArith.BinInt.Z.pow 2 38)) -> ((Stdlib.ZArith.BinInt.Z.le (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement.gw_sizes L) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop.TopA.WTOT) -> ((Stdlib.ZArith.BinInt.Z.le (Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (Corelib.Init.Datatypes.prod (stdpp.bitvector.definitions.bv 64) (stdpp.bitvector.definitions.bv 64)) L)) 64) -> (exists a : stdpp.bitvector.definitions.bv 64, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux md (stdpp.bitvector.definitions.Z_to_bv 64 len) a)))))))))))).
Proof.
  clear - Htop. intros md L len HR HM HI Hpos Hal Hlen Htot Hcnt.
  apply (place_witness md L len WTOT); try assumption.
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

(* LPS 727298f3: as [startA_main], the random bytes' 16-byte alignment last.  Written as plain text. *)
Theorem startA_main_ex : forall rho : valuation,
  bv_unsigned (rw rho 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m)) ->
  bv_unsigned (rw rho 1%positive) <= bv_unsigned (rw rho 4%positive) ->
  bv_unsigned (rw rho 1%positive) <= bv_unsigned (rw rho 6%positive) ->
  140735340871680 <= OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.x1 rho <= 2 ^ 47 ->
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.x1 rho mod 16 = 0 ->
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.x1 rho + 80 <= OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.r6of rho ->
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.r6of rho + 16 <= 2 ^ 47 ->
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.r6of rho + 16 <= OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.x1 rho + 2238671 ->
  arg_layout rho ->
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.r6of rho mod 16 = 0 ->
  ARG_HGAP rq rho ->
  etriple segsA (SP segsA (Kx m) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartStates.S_ctor rq) rho) (PostMain rho).
Proof.
  intros rho Hv1 H14 H16r Hx H16 R1 R2 R3 HAL HR16 HGP.
  assert (HB0 : B <= vm_limit (m_vmmaps m)) by (pose proof BS_lim; unfold BS in *; lia).

  eapply etriple_seq; [exact (start1_sum_ex_A m B rq Hlz Hmt Hres Hmaps Hna HusedB HB0 Htop Hrdm rho H14 H16r (proj1 Hx))|].
  apply etriple_ex; intros rho1. apply etriple_pure; intros AG1. apply etriple_pure; intros RM1.
  pose proof AG1 as [V1 L1].
  assert (Hv1a : bv_unsigned (rw rho1 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps mB))) by (rewrite (V1 1%positive) by lia; rewrite mB_vmmaps; exact Hv1).
  assert (TB : init_sp_ok (m_vmmaps mB)) by (clear - Htop Hmaps Hna; unfold init_sp_ok in *; rewrite mB_vmmaps; exact Htop).
  assert (RB : exists V, vm_reserved (m_vmmaps mB) = segments_reserved segsA ++ V /\ vdso_pair_ok V) by (rewrite mB_vmmaps; exact Hres).

  change (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1.m4 m) with mB.
  (* LPS 727298f3: each witness below names Linux's own address ([place_ok_linux], Fw/SysSpec.v), where a
     granted NULL-hint mmap now goes; [wit_of] gives it from a free gap in Linux's bottom-up window. *)
  assert (Wt2 : exists a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux mB n5 a).
  { apply (wit_of mB [HSe; GPe; LWe] 0x10000 RB); try (rewrite mB_vmmaps; reflexivity); try lia; try reflexivity; gwlia. }
  eapply etriple_seq; [exact (start2_sum_ex_A mB B rq RB TB band_B ltac:(rewrite mB_vmmaps; cbn [vm_limit]; pose proof BS_lim; unfold BS in *; lia) Wt2 rho1 Hv1a)|].
  apply etriple_ex; intros a1. apply etriple_ex; intros rho2. apply etriple_pure; intros G2. apply etriple_pure; intros AG2.
  pose proof AG2 as (V2 & L2 & M2).
  assert (H27b : rw rho2 27%positive = a1) by (rewrite <- (V2 27%positive) by lia; apply rho_set_rw_at).
  assert (E2lo : forall i, (i < 25)%positive -> rw rho2 i = rw rho i) by (intros i Hi; rewrite <- (V2 i) by lia; rewrite rho_set_rw_other by lia; apply V1; lia).
  pose proof (mA1_fields a1) as (RA & MA & LA & IA).
  assert (Hv1b : bv_unsigned (rw rho2 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps (mA1 a1)))) by (rewrite (E2lo 1%positive) by lia; rewrite IA; exact Hv1).
  assert (TA : init_sp_ok (m_vmmaps (mA1 a1))) by (clear - Htop IA; unfold init_sp_ok in *; rewrite IA; exact Htop).

  change (m5 mB a1) with (mA1 a1).
  assert (Wt3 : exists a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux (mA1 a1) n6 a).
  { apply (wit_of (mA1 a1) _ 0x38e000 ltac:(rewrite RA; exact Hres) MA IA); try lia; try reflexivity; gwlia. }
  eapply etriple_seq; [exact (start3_sum_ex_A (mA1 a1) a1 (B + 0x10000) rq ltac:(rewrite RA; exact Hres) ltac:(rewrite MA; left; reflexivity) TA (band_A1 a1)
                              ltac:(rewrite LA; pose proof BS_lim; unfold BS in *; lia) Wt3 rho2 H27b Hv1b)|].
  apply etriple_ex; intros a2. apply etriple_ex; intros rho3. apply etriple_pure; intros G3. apply etriple_pure; intros AG3.
  pose proof AG3 as (V3 & L3 & M3).
  assert (H28c : rw rho3 28%positive = a2) by (rewrite <- (V3 28%positive) by lia; apply rho_set_rw_at).
  assert (H27c : rw rho3 27%positive = a1) by (rewrite <- (V3 27%positive) by lia; rewrite rho_set_rw_other by lia; exact H27b).
  assert (E3lo : forall i, (i < 25)%positive -> rw rho3 i = rw rho i) by (intros i Hi; rewrite <- (V3 i) by lia; rewrite rho_set_rw_other by lia; apply E2lo; exact Hi).

  change (m6 (mA1 a1) a2) with (mS a1 a2). change (B + 0x10000 + 0x38e000) with BS.
  pose proof (mS_fields a1 a2) as (RS & MS & NS & LS & LMS & IS & KS & SKS).
  assert (SRES : exists V, vm_reserved (m_vmmaps (mS a1 a2)) = segments_reserved segsA ++ V /\ vdso_pair_ok V) by (rewrite RS; exact Hres).
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
  assert (SVDR : forall e, In e (vdso_reserved (m_kernel (mS a1 a2)) (vdso_top (m_vmmaps (mS a1 a2)))) -> In e (vm_reserved (m_vmmaps (mS a1 a2))))
    by (intros e He; rewrite RS; exact (Hvdr e He)).
  assert (Hv1c : bv_unsigned (rw rho3 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps (mS a1 a2)))) by (rewrite (E3lo 1%positive) by lia; rewrite IS; exact Hv1).

  set (LS5 := [(a2, Z_to_bv 64 0x38e000); (a1, Z_to_bv 64 0x10000); HSe; GPe; LWe]).
  assert (MS5 : vm_maps (m_vmmaps (mS a1 a2)) = LS5) by (rewrite MS; reflexivity). pose proof (gw_LS a1 a2) as GW5. fold LS5 in GW5.
  assert (Wt7 : exists P, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux (mS a1 a2) n7 P).
  { unfold n7. apply (wit_of (mS a1 a2) LS5 _ SRES MS5 IS); try lia; try reflexivity; subst LS5; gwlia. }
  assert (Wt9 : forall P, mmap_place_ok_none (Z_to_bv 64 0) (mS a1 a2) n7 P -> exists a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux (m8 (mS a1 a2) P) n9 a).
  { intros P HPL. pose proof (m8_ledger (mS a1 a2) P) as (R8 & M8 & _ & I8 & _). unfold n9.
    apply (wit_of (m8 (mS a1 a2) P) ((P, n7) :: LS5) _ ltac:(rewrite R8; exact SRES) ltac:(rewrite M8, MS5; reflexivity) ltac:(rewrite I8; exact IS)); try lia; try reflexivity; subst LS5; gwlia. }
  assert (Wt10 : forall P b4, mmap_place_ok_none (Z_to_bv 64 0) (mS a1 a2) n7 P -> mmap_place_ok_none (Z_to_bv 64 0) (m8 (mS a1 a2) P) n9 b4 ->
                exists a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux (m9 (mS a1 a2) P b4) (Z_to_bv 64 4096) a).
  { intros P b4 HPL HPL4. pose proof (m9_ledger (mS a1 a2) P b4) as (R9 & M9 & _ & I9 & _).
    apply (wit_of (m9 (mS a1 a2) P b4) ((b4, n9) :: (P, n7) :: LS5) _ ltac:(rewrite R9; exact SRES) ltac:(rewrite M9, MS5; reflexivity) ltac:(rewrite I9; exact IS)); try lia; try reflexivity; subst LS5; gwlia. }
  assert (Wt11 : forall P b4 b5, mmap_place_ok_none (Z_to_bv 64 0) (mS a1 a2) n7 P -> mmap_place_ok_none (Z_to_bv 64 0) (m8 (mS a1 a2) P) n9 b4 ->
                mmap_place_ok_none (Z_to_bv 64 0) (m9 (mS a1 a2) P b4) (Z_to_bv 64 4096) b5 ->
                exists a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux (m10 (mS a1 a2) P b4 b5) (Z_to_bv 64 65536) a).
  { intros P b4 b5 HPL HPL4 HPL5. pose proof (m10_ledger (mS a1 a2) P b4 b5) as (R10 & M10 & _ & I10 & _).
    apply (wit_of (m10 (mS a1 a2) P b4 b5) ((b5, Z_to_bv 64 4096) :: (b4, n9) :: (P, n7) :: LS5) _ ltac:(rewrite R10; exact SRES) ltac:(rewrite M10, MS5; reflexivity) ltac:(rewrite I10; exact IS));
      try lia; try reflexivity; subst LS5; gwlia. }

  eapply etriple_seq; [exact (start4_sum_ex_A (mS a1 a2) a1 a2 BS rq SRES SMAPS SNA LS STOP SA1 SA2 SBLIM Wt7 Wt9 Wt10 Wt11 rho3 H27c H28c Hv1c)|].
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
  assert (Wt12 : exists a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux (m11 (mS a1 a2) P b4 b5 b6) (Z_to_bv 64 4096) a).
  { apply (wit_of _ LS11 _ ltac:(rewrite R11; exact SRES) MS11 ltac:(rewrite I11; exact IS)); try lia; try reflexivity; subst LS11 LS5; gwlia. }
  assert (Wt13 : forall b7, mmap_place_ok_none (Z_to_bv 64 0) (m11 (mS a1 a2) P b4 b5 b6) (Z_to_bv 64 4096) b7 ->
                exists a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux (m12 (mS a1 a2) P b4 b5 b6 b7) (Z_to_bv 64 4096) a).
  { intros b7 HPL7. pose proof (m12_ledger (mS a1 a2) P b4 b5 b6 b7) as (R12 & M12 & _ & I12).
    apply (wit_of _ ((b7, Z_to_bv 64 4096) :: LS11) _ ltac:(rewrite R12; exact SRES) ltac:(rewrite M12, MS11; reflexivity) ltac:(rewrite I12; exact IS)); try lia; try reflexivity; subst LS11 LS5; gwlia. }
  assert (Wt14 : forall b7 b8, mmap_place_ok_none (Z_to_bv 64 0) (m11 (mS a1 a2) P b4 b5 b6) (Z_to_bv 64 4096) b7 ->
                mmap_place_ok_none (Z_to_bv 64 0) (m12 (mS a1 a2) P b4 b5 b6 b7) (Z_to_bv 64 4096) b8 ->
                exists a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux (m13 (mS a1 a2) P b4 b5 b6 b7 b8) (Z_to_bv 64 4096) a).
  { intros b7 b8 HPL7 HPL8. pose proof (m13_ledger (mS a1 a2) P b4 b5 b6 b7 b8) as (R13 & M13 & _ & I13). pose proof (m12_ledger (mS a1 a2) P b4 b5 b6 b7) as (_ & M12 & _).
    apply (wit_of _ ((b8, Z_to_bv 64 4096) :: (b7, Z_to_bv 64 4096) :: LS11) _ ltac:(rewrite R13; exact SRES) ltac:(rewrite M13, M12, MS11; reflexivity) ltac:(rewrite I13; exact IS));
      try lia; try reflexivity; subst LS11 LS5; gwlia. }

  eapply etriple_seq; [exact (start5_sum_ex_A (mS a1 a2) a1 a2 BS rq SRES SMAPS SNA LS STOP SA1 SA2 SBLIM P b4 b5 b6 HPL HPL4 HPL5 HPL6 Wt12 Wt13 Wt14 rho5 HV5 HZ11 HZD5)|].
  apply etriple_ex; intros b7. apply etriple_ex; intros b8. apply etriple_ex; intros b9. apply etriple_ex; intros rho6.
  apply etriple_pure; intros HPL7. apply etriple_pure; intros HPL8. apply etriple_pure; intros HPL9. apply etriple_pure; intros AG6.
  apply etriple_pure; intros H36. apply etriple_pure; intros H77. apply etriple_pure; intros H78. apply etriple_pure; intros HSSZ. apply etriple_pure; intros HZ11c. apply etriple_pure; intros HZD6. apply etriple_pure; intros RM6.
  pose proof AG6 as [V6 L6].
  assert (HV6 : vals12 (mS a1 a2) a1 a2 P b4 b5 b6 rho6) by (eapply (vals12_agree _ _ _ _ _ _ _ 36%positive rho5 rho6); [lia | exact HV5 | intros i Hi; apply V6; exact Hi]).

  assert (Wt17 : forall xx, exists a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux (m16 (mS a1 a2) P b4 b5 b6 b7 b8 b9 xx) (Z_to_bv 64 n17) a).
  { intros xx. pose proof (m16_fields (mS a1 a2) P b4 b5 b6 b7 b8 b9 xx) as (R16 & M16 & _ & I16 & _).
    pose proof (Start7.mE_fields (mS a1 a2) P b4 b5 b6 b7 b8 b9 xx b7) as (_ & MM & _).
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.maps_mE_eq (mS a1 a2) a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 xx b7) as ME.
    rewrite MM in ME. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.LmE in ME. cbn [List.app] in ME. pose proof (f_equal (@List.tl _) ME) as ME'. cbn [List.tl] in ME'.
    unfold n17. apply (wit_of _ _ _ ltac:(rewrite R16; exact SRES) ME' ltac:(rewrite I16; exact IS)); try lia; try reflexivity; rewrite SMAPS; gwlia. }

  eapply etriple_seq; [exact (start6_sum_ex_A (mS a1 a2) a1 a2 BS rq SRES SMAPS SNA LS STOP SA1 SA2 SBLIM P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 Wt17
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
  { exact (Start7.eseg18 (mS a1 a2) a1 a2 BS rq SRES SMAPS SNA LS STOP SA1 SA2 SBLIM SSB SBRK SBAL SVDR ok OKF OKP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
             rho7 HV7 H36d H77d H78d H83 Ex7 ltac:(rewrite Er6, Ex; exact R1) ltac:(rewrite Er6; exact R2) ltac:(rewrite Er6, Ex; exact R3) HSZ
             (arg_layout_ext rho rho7 ltac:(intros i Hi; rewrite (V7 i), (V6 i), (E5lo i), (E3lo i) by lia; reflexivity) HAL)
             ltac:(rewrite Er6; exact HR16)
             (proj2 (ARG_HGAP_ext rq rho rho7 ltac:(intros i Hi; rewrite (V7 i), (V6 i), (E5lo i), (E3lo i) by lia; reflexivity)) HGP)). }
  apply etriple_ex; intros o. apply etriple_ex; intros rho8.
  apply etriple_pure; intros Ho. apply etriple_pure; intros V8. apply etriple_pure; intros L8. apply etriple_pure; intros H84. apply etriple_pure; intros H85. apply etriple_pure; intros HZX.
  apply etriple_pure; intros RM8. apply etriple_pure; intros TL8. apply etriple_pure; intros RL8. apply etriple_pure; intros RH8.

  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.minv8_out18 (mS a1 a2) a1 a2 SRES SMAPS SNA LS STOP SA1 SA2 SBRK SBAL P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
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
  assert (Wt22 : exists a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) (Z_to_bv 64 1048576) a).
  { apply (wit_of _ _ _ (mi_res HMI) (mi_maps HMI) ltac:(rewrite (mi_isp HMI), IS; reflexivity)); try lia; try reflexivity; unfold WTOT; lia. }
  assert (Wt23 : forall b12, mmap_place_ok_none (Z_to_bv 64 0) (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) (Z_to_bv 64 1048576) b12 ->
             exists a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m22 (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) b12) (Z_to_bv 64 8388608) a).
  { intros b12 HPL12. pose proof (minv8_eager _ _ _ _ _ 1048576 b12 HMI ltac:(lia) eq_refl ltac:(lia) HPL12) as MI2.
    apply (wit_of _ _ _ (mi_res MI2) (mi_maps MI2) ltac:(rewrite (mi_isp MI2), IS; reflexivity)); try lia; try reflexivity.
    - rewrite gw_sizes_cons, u64_of_lit by lia. unfold WTOT. lia.
    - cbn [length]. lia. }
  assert (Wt24 : forall b12 b13, mmap_place_ok_none (Z_to_bv 64 0) (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) (Z_to_bv 64 1048576) b12 ->
             mmap_place_ok_none (Z_to_bv 64 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m22 (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) b12) (Z_to_bv 64 8388608) b13 ->
             exists a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m23a (Start7.out18_model (mS a1 a2) P b4 b5 b6 b7 b8 b9 x b10 o) b12 b13) (Z_to_bv 64 4096) a).
  { intros b12 b13 HPL12 HPL13. pose proof (minv8_eager _ _ _ _ _ 1048576 b12 HMI ltac:(lia) eq_refl ltac:(lia) HPL12) as MI2.
    pose proof (minv8_null_rw _ _ _ _ _ 8388608 b13 MI2 ltac:(lia) eq_refl ltac:(lia) HPL13) as MI3.
    apply (wit_of _ _ _ (mi_res MI3) (mi_maps MI3) ltac:(rewrite (mi_isp MI3), IS; reflexivity)); try lia; try reflexivity.
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
  (* LPS 727298f3: the memory map's presence on the dropped auxv tail, from segment 7's post, kept by
     segment 22's calls, whose windows lie below the stack (as for [RM9]). *)
  assert (TL9 : forall a : word, ARG_TAIL rho a -> rm rho9 a <> None).
  { intros a Ha. pose proof Ha as [HaLo _]. unfold x1 in Hx.
    pose proof (urange (rw rho 2%positive)) as U2. pose proof (urange (rw rho 3%positive)) as U3.
    rewrite (M9 a) by (rewrite Hv1 in HaLo; pose proof Hxtop as T; unfold alloc_top in T; rewrite IS, stack_max_size_val in T; lia).
    apply (TL8 a). apply (proj2 (ARG_TAIL_ext rho rho7 a ltac:(intros i Hi; rewrite (V7 i), (V6 i), (E5lo i), (E3lo i) by lia; reflexivity))). exact Ha. }
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
      pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.X18_facts (mS a1 a2) a1 a2 SRES SMAPS SNA LS STOP SA1 SA2 SBRK SBAL P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxx H16x Hxtop HPL10
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
  split; [exact CH|]. split; [exact LL|]. split; [exact RM9|]. split; [exact TL9|]. split; [exact ZX9|]. split; [exact BD9|]. split; [exact HR9|].
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
