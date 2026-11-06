(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_028.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7 Start8M fv Start8States0.

(* [comment removed for export] *)
Module Start8Out.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "m_vm_lazy"; "vm_limit"; "vm_init_sp"; "vm_maps"; "VmMaps"; "vm_noaccess"; "vm_brk"; "event"; "maps_subtract"; "vm_reserved"; "Model"; "alloc_top"; "lazy_interior"; "vm_start_brk"; "mkVmMapsFull"; "vm_mmap_base"; "page_in_ranges"; "region_free"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "True"; "ex"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "list"; "nil"; "app"; "bool"; "true"; "false"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "divide"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7"; "mE"; "Q18"; "out18"; "TOPz"; "out18_ok"; "out18_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes"; "n8w"; "pgw"; "brk0w"; "brk0"; "n2w"; "mg"; "mf_exp"; "mf_res"; "mg_dead"; "mg_ok"; "a4"; "mgrant"; "n3w"; "reqw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8Out.Seg8M"; "LmE"; "X1_18"; "L18"; "X18"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "mmap_n"; "mmap_none_vm"; "mmap_fixed_dead_vm"; "mmap_fixed_ok_vm"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post"; "out1"; "out1_ok"; "out0"; "O1_dead"; "O1_ok"; "out1_model"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8M"; "minv8"; "ranges_apart"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_LO"; "SHADOW_BAND_HI"; "SHADOW_RW_LO_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4"; "n7"; "n9"; "m8"; "RI"; "m10"; "m11"; "m9"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5"; "m13"; "m12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6"; "n17"; "m16"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code StartLib KxA Placement PlacementA SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7States Start7 Start8M.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.StartNodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Start5bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6Aux OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.MuslMalloc40States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.MuslMalloc40 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma filter_all_true : forall {T} (f : T -> bool) (l : list T), (forall e, In e l -> f e = true) -> List.filter f l = l.
Proof.
  intros T f l H. induction l as [|e l IH]; [reflexivity|]. cbn [List.filter]. rewrite (H e (or_introl eq_refl)). rewrite IH; [reflexivity|].
  intros e' He'. apply H. right. exact He'.
Qed.

Section Seg8M.

Variables (m : Model) (a1 a2 : word) (B : Z).
Hypothesis Hres : ltac2:(tb__ "0|1|
S16S1eS1dS1Q40A1M0G0A2A1SdS3Vm;A1A1S5bS53A1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|3|
S16S1eS1dS1Q40M0A1M1G1A2M2A1S7S3Vm;A1A1S1cG2S1bG1G1Va2;S0G0Z38e000A2A4S1cG2S1bG1G1Va1;S0G0Z10000A2A4S1cG2S1bG1G1S0G0Z2008fff7000A2S0G0Zdfff0001000A2A4S1cG2S1bG1G1S0G0Z8fff7000A2S0G0Z20000000000A2A4S1cG2S1bG1G1S0G0Z7fff7000A2S0G0Z10000000A2A4S1fG2A1A3A3A3A3A3A3").
Hypothesis Hna : ltac2:(tb__ "0|3|
S16S1eS1dS1Q40M0A1M1G1A2M2A1S9S3Vm;A1A1S1cG2S1bG1G1S0G0Z8fff7000A2S0G0Z20000000000A2A4S1fG2A1A3A3").
Hypothesis Hlz : ltac2:(tb__ "0|3|
S16S1eS1dS1Q40M0A1M1G1A2M2A1S4Vm;A1S20G2S10S0G0Z2008fff7000A2S0G0Zdfff0001000A2A2S20G2S10S0G0Z8fff7000A2S0G0Z20000000000A2A2S10S0G0Z7fff7000A2S0G0Z10000000A2A2A3A3A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Ha1 : ltac2:(tb__ "0|2|
S17S24Z646000S2Q40Va1;A2M0A2S17S18S24S25G0Z10000A2M1S50A2S24S51G0A2A2S24G1SfS3Vm;A1A1A2A2A2").
Hypothesis Ha2 : ltac2:(tb__ "0|2|
S17S24Z646000S2Q40Va2;A2M0A2S17S18S24S25G0Z38e000A2M1S50A2S24S51G0A2A2S24G1SfS3Vm;A1A1A2A2A2").
Hypothesis HBlim : ltac2:(tb__ "0|0|
S24S25VB;Z1000000A2S5S3Vm;A1A1A2").
Hypothesis Hsb : ltac2:(tb__ "0|1|
S16S1Q40A1S11S3Vm;A1M0A1SaG0A1A3").
Hypothesis Hbrk : ltac2:(tb__ "0|1|
S17S24Z646000S2Q40SaS3Vm;A1A1A2M0A2S24G0Z80646000A2A2").
Hypothesis Hbal : ltac2:(tb__ "0|0|
S27Z1000S2Q40SaS3Vm;A1A1A2A2").
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S64S61S1eS1Q40A1A1S1eSbA1M0SeR5R4R3R2R1A4S16G0R3S1fSbA1A3F_;Fmd;Ftr;Ftp;Frho;S65S53Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S64S61S1eS1Q40A1A1S1eSbA1M0SeR5R4R3R2R1A4S16G0R3S1fSbA1A3F_;Fmd;Ftr;Ftp;Frho;S66S53Vok;R2A3F_;FJ;").
Variables (P b4 b5 b6 : word).
Hypothesis HPL : ltac2:(tb__ "0|0|
S41S0Q40Z0A2Vm;S54VP;A4").
Hypothesis HPL4 : ltac2:(tb__ "0|0|
S41S0Q40Z0A2S56Vm;VP;A2S55Vb4;A4").
Hypothesis HPL5 : ltac2:(tb__ "0|1|
S41S0Q40M0Z0A2S5aVm;VP;Vb4;A3S0G0Z1000A2Vb5;A4").
Hypothesis HPL6 : ltac2:(tb__ "0|1|
S41S0Q40M0Z0A2S58Vm;VP;Vb4;Vb5;A4S0G0Z10000A2Vb6;A4").
Variables (b7 b8 b9 : word).
Hypothesis HPL7 : ltac2:(tb__ "0|1|
S41S0Q40M0Z0A2S59Vm;VP;Vb4;Vb5;Vb6;A5S0G0Z1000A2Vb7;A4").
Hypothesis HPL8 : ltac2:(tb__ "0|1|
S41S0Q40M0Z0A2S5eVm;VP;Vb4;Vb5;Vb6;Vb7;A6S0G0Z1000A2Vb8;A4").
Hypothesis HPL9 : ltac2:(tb__ "0|1|
S41S0Q40M0Z0A2S5dVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;A7S0G0Z1000A2Vb9;A4").
Variables (x : Z) (b10 : word).
Hypothesis Hx : 0x7fff80000000 <= x <= 2 ^ 47.
Hypothesis H16 : x mod 16 = 0.
Hypothesis Hxtop : ltac2:(tb__ "0|0|
S16S4dSfS3Vm;A1A1S28Vx;Z800000A2A3").
Hypothesis HPL10 : ltac2:(tb__ "0|1|
S41S0Q40M0Z0A2S60Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;A9S0G0S5fA2Vb10;A4").

Hypothesis Hapart0 : ltac2:(tb__ "0|2|
S4fS20S1dS1Q40A1M0G0A2SdS3Vm;A1M1A1S7G1A1A3A1").

Local Notation mE := (Start7.mE m P b4 b5 b6 b7 b8 b9 x b10).
Local Notation TOPz := (Start7.TOPz x).
Local Notation Q18 := (Start7.Q18 x).
Local Notation out18_ok := (Start7.out18_ok m P b4 b5 b6 b7 b8 b9 x b10).
Local Notation out18_model := (Start7.out18_model m P b4 b5 b6 b7 b8 b9 x b10).
Local Notation P_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.P_facts m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_range := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.RI_range m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation b4_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b4_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4) (only parsing).
Local Notation b5_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b5_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5) (only parsing).
Local Notation b6_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b6_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5 b6 HPL6) (only parsing).
Local Notation b7_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.b7_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7) (only parsing).
Local Notation b8_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.b8_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7 b8 HPL8) (only parsing).
Local Notation b9_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.b9_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7 b8 HPL8 b9 HPL9) (only parsing).
Local Notation mF_vmmaps := (Start6.mF_vmmaps m P b4 b5 b6 b7 b8 b9) (only parsing).
Local Notation m16_fields := (Start6.m16_fields m P b4 b5 b6 b7 b8 b9) (only parsing).
Local Notation W9 := (Start6.W9 m a1 a2 Hres Hmaps Hna Htop P b4 HPL HPL4) (only parsing).
Local Notation low_shadow_lazy_mF := (Start6.low_shadow_lazy_mF m a1 a2 Hres Hmaps Hlz Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9) (only parsing).
Local Notation low_shadow_acc_mF := (Start6.low_shadow_acc_mF m a1 a2 Hres Hmaps Hna Hlz Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9) (only parsing).
Local Notation mE_fields := (Start7.mE_fields m P b4 b5 b6 b7 b8 b9 x b10) (only parsing).
Local Notation top_mE := (Start7.top_mE m P b4 b5 b6 b7 b8 b9 x b10 Hxtop) (only parsing).
Local Notation init_sp_ok_mE := (Start7.init_sp_ok_mE m Htop P b4 b5 b6 b7 b8 b9 x b10) (only parsing).
Local Notation b10_facts := (Start7.b10_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxtop HPL10) (only parsing).
Local Notation band_mE := (Start7.band_mE m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10) (only parsing).
Local Notation CAx := (Start7.CAx x Hx H16) (only parsing).
Local Notation lazy_mE_facts := (Start7.lazy_mE_facts m a1 a2 Hres Hmaps Hlz Htop P b4 b5 b6 HPL HPL4 b7 b8 b9 x b10 Hx H16) (only parsing).
Local Notation high_shadow_lazy_mE := (Start7.high_shadow_lazy_mE m a1 a2 Hres Hmaps Hlz Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx H16) (only parsing).
Local Notation noacc_mF_wf := (Start7.noacc_mF_wf m a1 a2 Hres Hmaps Hna Htop P b4 b5 b6 HPL HPL4 b7 b8 b9) (only parsing).
Local Notation high_shadow_acc_mE := (Start7.high_shadow_acc_mE m a1 a2 Hres Hmaps Hna Hlz Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx H16) (only parsing).
Local Notation brk0_mE := (Start7.brk0_mE m Hbrk P b4 b5 b6 b7 b8 b9 x b10 Hx H16 Hxtop) (only parsing).
Local Notation out18_Wok := (Start7.out18_Wok m a1 a2 Hres Hmaps Htop Hbrk P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx H16 Hxtop HPL10) (only parsing).

Ltac klia := unfold kHighMemBeg in *; repeat match goal with H : context [Z.modulo _ _] |- _ => clear H end; lia.

Definition LmE : list (word * word) := ltac2:(tb__ "0|4|
S20S1dS1Q40M0A1M1G1A2M2S1cG2S1bG1G1Vb10;S0G0S5fA2A4S1cG2S1bG1G1Vb8;S0G0Z1000A2M3A4S1cG2S1bG1G1Vb7;G3A4S1cG2S1bG1G1Vb6;S0G0Z10000A2A4S1cG2S1bG1G1Vb5;G3A4S1cG2S1bG1G1Vb4;S55A4S1cG2S1bG1G1VP;S54A4S1fG2A1A3A3A3A3A3A3A3S7S3Vm;A1A1A3").

Lemma maps_m13 : ltac2:(tb__ "0|4|
S16S1eS1dS1Q40M0A1M1G1A2M2A1S7S3S5dVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;A7A1A1S20G2S1cG2S1bG1G1Vb8;S0G0Z1000A2M3A4S1cG2S1bG1G1Vb7;G3A4S1cG2S1bG1G1Vb6;S0G0Z10000A2A4S1cG2S1bG1G1Vb5;G3A4S1cG2S1bG1G1Vb4;S55A4S1cG2S1bG1G1VP;S54A4S1fG2A1A3A3A3A3A3A3S7S3Vm;A1A1A3A3").
Proof.
  clear. pose proof (m13_ledger m P b4 b5 b6 b7 b8) as (_ & L2 & _). pose proof (m12_ledger m P b4 b5 b6 b7) as (_ & O2 & _). pose proof (mE_ledger m P b4 b5 b6) as (_ & Q2 & _).
  rewrite L2, O2, Q2. reflexivity.
Qed.

Lemma maps_mE_eq : ltac2:(tb__ "0|1|
S16S1eS1dS1Q40A1M0G0A2A1S7S3S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaA1A1S3dA3").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop.
  clear Hna Hlz Ha1 Ha2 HBlim Hsb Hbrk Hbal OKF OKP Hx H16 Hxtop HPL10 Hapart0.
  pose proof mE_fields as (_ & MM & _). rewrite MM. pose proof (m16_fields x) as (_ & M6 & _). rewrite M6. unfold LmE. cbn [List.app]. f_equal.
  pose proof (m13_ledger m P b4 b5 b6 b7 b8) as (R13 & _).
  pose proof b9_facts as (_ & _ & _ & _ & _ & K4). rewrite R13, maps_m13 in K4.
  unfold map_remove. cbn [List.filter fst]. rewrite (proj2 (bv_eqb_eq b9 b9) eq_refl). cbn [negb]. rewrite maps_m13.
  apply filter_all_true. intros [e s] Hin. cbn [fst].
  assert (Hs : 0 < bv_unsigned s).
  { rewrite Hmaps in Hin. cbn [List.app In] in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]; injection E as <- <-; unfold n9, n7; rewrite ?u64_of_lit by lia; lia. }
  rewrite (region_free_In_neq _ b9 (Z_to_bv 64 4096) e s (region_free_app_r _ _ _ _ K4) Hin Hs ltac:(rewrite u64_of_lit by lia; lia)). reflexivity.
Qed.

Lemma LmE_pos : ltac2:(tb__ "0|2|
S1Q40M0A1M1G1S5cS1dG1G1A2S1bG1G1R2R1A4S3dA3S26Z0S2G0R2A2A2F_;Fs;Fb;").
Proof using Hmaps.
  clear - Hmaps. intros b s Hin. unfold LmE in Hin. rewrite Hmaps in Hin. cbn [List.app In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <-; unfold n17, n9, n7; rewrite ?u64_of_lit by lia; lia.
Qed.

Lemma LmE_wf : ivs_wf LmE.
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hmaps Hres Htop Hxtop Hx.
  clear Hna Hlz HBlim Hsb Hbrk Hbal OKF OKP Hapart0.
  intros [b s] Hin. pose proof (alloc_top_lt (m_vmmaps m)) as TL. unfold two_pow_64 in TL.
  pose proof P_facts as (_ & Pceil & _). pose proof b4_facts as (_ & _ & C4 & _). pose proof b5_facts as (_ & _ & _ & C5 & _).
  pose proof b6_facts as (_ & _ & C6 & _). pose proof b7_facts as (_ & _ & C7 & _). pose proof b8_facts as (_ & _ & C8 & _).
  pose proof b10_facts as (_ & _ & C10 & _). unfold Start7.TOPz in C10.
  unfold iv_wf, ivB, ivS. cbn [fst snd]. unfold LmE in Hin. rewrite Hmaps in Hin. cbn [List.app In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <-; unfold n17, n9, n7 in *; rewrite ?u64_of_lit by lia; lia.
Qed.

Lemma apart_mE : ltac2:(tb__ "0|1|
S4fS20S1dS1Q40A1M0G0A2S5bS53A1S3dA3A1").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop Hxtop Hapart0.
  clear Hna Hlz Ha1 Ha2 HBlim Hsb Hbrk Hbal OKF OKP.
  pose proof P_facts as (_ & _ & F7 & _). pose proof b4_facts as (_ & _ & _ & _ & F4). pose proof b5_facts as (_ & _ & _ & _ & _ & F5).
  pose proof b6_facts as (_ & _ & _ & _ & F6). pose proof b7_facts as (_ & _ & _ & _ & F7b). pose proof b8_facts as (_ & _ & _ & _ & F8).
  pose proof b10_facts as (_ & _ & _ & _ & F10).
  pose proof (m8_ledger m P) as (R8 & M8 & _). pose proof (m9_ledger m P b4) as (R9 & M9 & _). pose proof (m10_ledger m P b4 b5) as (R10 & M10 & _).
  pose proof (mE_ledger m P b4 b5 b6) as (R11 & M11 & _). pose proof (m12_ledger m P b4 b5 b6 b7) as (R12 & M12 & _).
  pose proof (m16_fields x) as (R16 & M16 & _). pose proof mE_fields as (_ & MM & _).
  rewrite R8, M8, Hres in F4. rewrite R9, M9, Hres in F5. rewrite R10, M10, Hres in F6. rewrite R11, M11, Hres in F7b. rewrite R12, M12, M11, Hres in F8.
  rewrite Hres in F7. rewrite Hres in Hapart0.

  assert (M16' : vm_maps (m_vmmaps (m16 m P b4 b5 b6 b7 b8 b9 x)) = [(b8, Z_to_bv 64 4096); (b7, Z_to_bv 64 4096); (b6, Z_to_bv 64 65536); (b5, Z_to_bv 64 4096); (b4, n9); (P, n7)] ++ vm_maps (m_vmmaps m)).
  { pose proof maps_mE_eq as E. rewrite MM in E. unfold LmE in E. cbn [List.app] in E. injection E as E'. exact E'. }
  rewrite R16, M16', Hres in F10.
  unfold LmE. cbn [List.app].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F10 He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F8 He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F7b He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F6 He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F5 He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F4 He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F7 He)].
  exact Hapart0.
Qed.

Lemma low_lazy_mE : ltac2:(tb__ "0|1|
S1Q40M0A1S24S50S2G0R1A2A2S24S25S2G0R2A2Z1000A2S52A2S16S21S14R3S4S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaA1A2S22A3F_;F_;Fp;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hlz Hmaps Hres Htop Hx H16.
  clear Hna Ha1 Ha2 HBlim Hsb Hbrk Hbal OKF OKP Hxtop HPL10 Hapart0.
  intros p Hlo Hhi. pose proof mE_fields as (_ & _ & _ & _ & LZ & _). rewrite LZ.
  pose proof (m16_fields x) as (_ & _ & _ & _ & LZ6 & _). rewrite LZ6.
  apply low_shadow_lazy_mF; assumption.
Qed.

Lemma low_acc_mE : ltac2:(tb__ "0|0|
S4dS17S24S50R1A2S26R1S52A2A2S16S21S62S9S3S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaA1A1R2A2S23A3F_;Fz;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hlz Hna Hmaps Hres Htop Hx H16.
  clear Ha1 Ha2 HBlim Hsb Hbrk Hbal OKF OKP Hxtop HPL10 Hapart0.
  intros z Hz. pose proof mE_fields as (_ & _ & _ & _ & _ & NA & _). rewrite NA.
  pose proof (m16_fields x) as (_ & _ & _ & _ & _ & NA6). rewrite NA6.
  exact (low_shadow_acc_mF z Hz).
Qed.

Lemma noacc_wf8 : ltac2:(tb__ "0|5|
S17S16S1eS1dS1Q40M0A1M1G1A2M2A1S9S3S56Vm;VP;A2A1A1ScS1cG2S1bG1G1VP;S54A4S1cG2S1bG1G1S0G0Z8fff7000A2S0G0Z20000000000A2A4S1fG2A1A3A3M3S2G0S57VP;A1A2M4S25G4Z1000A2A3A3S63G3A1A2").
Proof using HPL Hna Hmaps Hres Htop.
  clear - HPL Hna Hmaps Hres Htop.
  pose proof P_facts as (Pal & Pceil & _). pose proof (alloc_top_lt (m_vmmaps m)) as TL. unfold two_pow_64 in TL.
  split.
  - rewrite (m8_vmmaps m P). unfold h8, mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite (mP_vmmaps m P). cbn [vm_noaccess]. rewrite Hna.
    replace (bv_unsigned pg) with 4096 by (symmetry; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). reflexivity.
  - apply ivs_wf_cons; [|apply ivs_wf_cons; [|apply ivs_wf_nil]]; unfold iv_wf, ivB, ivS; cbn [fst snd]; [unfold n7|]; rewrite ?u64_of_lit by lia; lia.
Qed.

Lemma namaps_mE : ltac2:(tb__ "0|3|
S4dS16S21S62S9S3S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaA1A1R1A2S22A3S1aS1Q40M0A1M1G1S1aG1G1S17S5cS1dG1G1A2S1bG1G1R2R1A4S3dA3S17S24S2G0R2A2M2R4A2S26R4S25G2S2G0R1A2A2A2A2A2Ls;A2Lb;A2F_;Fz;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hlz Hna Hmaps Hres Htop Hx H16.
  clear Ha1 Ha2 HBlim Hsb Hbrk Hbal OKF OKP Hxtop HPL10 Hapart0.
  intros z Hz. pose proof noacc_mF_wf as WF. pose proof mE_fields as (_ & _ & _ & _ & _ & NA & _). rewrite NA in Hz.
  pose proof (m16_fields x) as (_ & _ & _ & _ & _ & NA6). rewrite NA6 in Hz. unfold Start6.mF in NA6, Hz, WF.
  pose proof mF_vmmaps as (_ & _ & NAF & _). unfold Start6.mF in NAF. rewrite NAF in Hz. unfold Start6.b9lo in Hz.
  destruct (maps_subtract_sem _ (bv_unsigned b9) (bv_unsigned b9 + 4096) W9 ltac:(lia)) as (_ & _ & Cv9). rewrite Cv9 in Hz. apply andb_prop in Hz as [Hz _].
  apply covered_cons_iff8 in Hz as [Hz|Hz].
  - unfold ivB, ivS in Hz. cbn [fst snd] in Hz. exists b4, n9. split; [unfold LmE; cbn [List.app In]; tauto | lia].
  - pose proof noacc_wf8 as [E8 W7]. rewrite E8 in Hz. pose proof P_facts as (Pal & Pceil & _).
    destruct (maps_subtract_sem _ (bv_unsigned (RI P)) (bv_unsigned (RI P) + 4096) W7 ltac:(lia)) as (_ & _ & Cv7). rewrite Cv7 in Hz. apply andb_prop in Hz as [Hz _].
    apply covered_cons_iff8 in Hz as [Hz|Hz]; [|apply covered_cons_iff8 in Hz as [Hz|Hz]; [|discriminate]]; unfold ivB, ivS in Hz; cbn [fst snd] in Hz.
    + exists P, n7. split; [unfold LmE; cbn [List.app In]; tauto | lia].
    + exists (Z_to_bv 64 0x8fff7000), (Z_to_bv 64 0x20000000000). split; [unfold LmE; rewrite Hmaps; cbn [List.app In]; tauto | lia].
Qed.

Theorem minv8_mE : ltac2:(tb__ "0|1|
S4eS3dS5S3Vm;A1M0A1S6G0A1S2aVx;A1S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaA5").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbrk Hbal OKF OKP.
  pose proof mE_fields as (MR & MM & ML & MB & LZ & NA & K1 & K2). pose proof lazy_mE_facts as [WL _].
  constructor.
  - rewrite MR. exact Hres.
  - exact maps_mE_eq.
  - exact ML.
  - exact MB.
  - exact init_sp_ok_mE.
  - rewrite <- Hres, <- MR, <- maps_mE_eq. exact band_mE.
  - exact apart_mE.
  - exact LmE_pos.
  - exact LmE_wf.
  - exact low_lazy_mE.
  - exact low_acc_mE.
  - intros p H1 H2. apply high_shadow_lazy_mE; [exact H1 | unfold SHADOW_BAND_HI in H2; unfold kHighMemBeg; exact H2].
  - intros z Hz. apply high_shadow_acc_mE. unfold SHADOW_RW_HI_BEG, SHADOW_BAND_HI in Hz. unfold kHighMemBeg. exact Hz.
  - intros z Hz. exact (namaps_mE z Hz).
  - rewrite NA. pose proof (m16_fields x) as (_ & _ & _ & _ & _ & NA6). rewrite NA6. unfold Start6.mF. exact noacc_mF_wf.
  - exact WL.
  -
    rewrite NA. pose proof (m16_fields x) as (_ & _ & _ & _ & _ & NA6). rewrite NA6. pose proof mF_vmmaps as (_ & _ & NAF & _). rewrite NAF.
    assert (N9 : bv_unsigned n9 = 0x800000) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    apply ivs_pos_subtract. apply ivs_pos_cons; [rewrite N9; lia|]. pose proof noacc_wf8 as [E8 _]. rewrite E8. apply ivs_pos_subtract.
    apply ivs_pos_cons; [unfold n7; rewrite u64_of_lit by lia; lia|]. apply ivs_pos_cons; [rewrite u64_of_lit by lia; lia | apply ivs_pos_nil].
Qed.

Definition X1_18 (o : out1) : list (word * word) := ltac2:(tb__ "0|7|
S47S1eS1dS1Q40M0A1M1G1A2M2A1Lo;Vo;S1cG2S1bG1G1S31S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM3A1S33A4S1fG2A1M4A3M5G5S1cG2S1bG1G1S0G0S25S32G3A1Z1000M6A2A2S0G0G6A2A4G4A3G1S1cG2S1bG1G1R1S2fA4G4A3La;X47x4").
Definition X18 (o : out18) : list (word * word) := ltac2:(tb__ "0|4|
S2bS1eS1dS1Q40A1M0G0A2M1A1M2Lo;Vo;S49S49G2Lo0;R1S1fG1A1M3G0S1cG1S1bG0G0R1S2fA4G3A3La;X49x2Lo0;S47S3eR1A1Lo1;S47G0S1cG1S1bG0G0R1S30A4S3eR2A1A3Lg;Lo1;X2bx3").
Definition L18 (o : out18) : list (word * word) := X18 o ++ LmE.

Lemma pgw_n : ltac2:(tb__ "0|4|
S17S16S1Q40M0A1M1S42S30A1S30A3S17S16S4dS2G0S30A2Z1000M2A3S17S16G1S42S2fA1S2fA3S17S16S4dS2G0S2fA2Z2000M3A3S17S16S4dS2G0S33A2G3A3S17S16G1S2fS0G0G3A2A3S16G1S30S0G0G2A2A3A2A2A2A2A2A2").
Proof. clear. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma brk_mE : ltac2:(tb__ "0|4|
S17S24Z646000S32S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0A1M1A2S17S24G1Z80646000A2S17S16S4dS2Q40M2S31G0A1M3A2G1A3S16S1G2A1G3SaS3Vm;A1A1A3A2A2A2").
Proof using Hbrk Hx H16 Hxtop.
  clear - Hbrk Hx H16 Hxtop. pose proof brk0_mE as (B1 & B2 & B3). repeat split; try assumption; try reflexivity.
Qed.

Lemma mg_shape : ltac2:(tb__ "0|5|
S17S16S8S3S34S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0A1M1A1S12SdS3G0A1M2A1S1cS1dS1Q40A1M3G3A2M4S1bG3G3S31G0A1S33A4S7G2A1A3S9G2A1S11G2A1S3cG0A1S5G2A1S13G2A1S6G2A1A8A3S16S1eG4A1S4G1A1S4G0A1A3A2").
Proof using Hbrk Hx H16 Hxtop. clear - Hbrk Hx H16 Hxtop. pose proof brk_mE as (H1 & H2 & _). split; [exact (mg_vmmaps mE H1 H2) | unfold mg; apply m_vm_lazy_with_vmmaps]. Qed.

Lemma mg_ok_shape : ltac2:(tb__ "0|4|
S17S16S8S3S38S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0A1M1A1S45S3S34G0A1A1S31G0A1S30A3A3S16S1eS1dS1Q40A1M2G2A2A1S4G1A1ScS4G0A1S32G0A1M3S25G3Z1000A2A3A3A2").
Proof using Hbrk Hx H16 Hxtop.
  clear - Hbrk Hx H16 Hxtop. unfold mg_ok. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps, m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps.
  split; [reflexivity|]. rewrite (proj2 mg_shape). reflexivity.
Qed.
Lemma mg_dead_shape : ltac2:(tb__ "0|4|
S17S16S8S3S37S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0A1M1A1S44S3S34G0A1A1S31G0A1S30A3A3S16S1eS1dS1Q40A1M2G2A2A1S4G1A1ScS4G0A1S32G0A1M3S25G3Z1000A2A3A3A2").
Proof using Hbrk Hx H16 Hxtop.
  clear - Hbrk Hx H16 Hxtop. unfold mg_dead. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps, m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps.
  split; [reflexivity|]. rewrite (proj2 mg_shape). reflexivity.
Qed.
Lemma mf_res_shape : ltac2:(tb__ "0|3|
S1Q40A1M0S17S16S8S3S36S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM1R1A2M2A1S43S3G1A1S2fR1A3A3S16S1eS1dG0G0A2A1S4G2A1S4G1A1A3A2Fa;").
Proof. clear. intros a. split; [apply mf_res_vmmaps | unfold mf_res; apply m_vm_lazy_with_vmmaps]. Qed.
Lemma mf_exp_shape : ltac2:(tb__ "0|5|
S1Q40M0A1M1S43S3S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM2A1S2fR1A3S8S17S16S8S3S35G2R2A2M3A1S12SdR1A1S7R1A1ScS9R1A1S2G0S39R2A1A2M4S25G4S2G0S30A2A2A3S11R1A1SaR1A1S5R1A1S13R1A1S6R1A1A8A3S16S1eS1dG1G1A2A1S4G3A1S4G2A1A3A2Th;Fa;").
Proof.
  clear. intros a h. unfold mf_exp, mprotect_model_next. rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps, mf_res_vmmaps. subst h.
  split; [reflexivity | unfold mf_res; apply m_vm_lazy_with_vmmaps].
Qed.
Lemma mgrant_shape : ltac2:(tb__ "0|2|
SeS1Q40A1M0S17S16S8S3S3aR2R1A2M1A1S46S3R2A1S30R1A3A3S16S1eS1dG0G0A2A1S4G1A1S4R2A1A3A2Fg;Fmx;").
Proof. clear. intros. unfold mgrant. rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps. split; reflexivity. Qed.

Lemma grow_facts : ltac2:(tb__ "0|4|
S47S48S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0R1A2S47OLo1;R2S17S16S21S15S20S1dS1Q40A1M1G1A2S5bS53A1S3dA3S31G0A1S3bA3S22A3S17S24S25S32G0A1Z2000A2M2S50A2S24G2S2cVx;A1A2A2A2M3G3G3G1S19La;X47x4F_;Fo1;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hbrk Hmaps Hres Htop Hx H16 Hxtop.
  clear Hna Hlz Ha1 Ha2 HBlim Hsb Hbal OKF OKP Hapart0.
  intros o1 Ho. pose proof mE_fields as (MR & _). pose proof brk_mE as (B1 & B2 & B3 & _).
  assert (GEN : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0 mE + 8192 <= alloc_top (m_vmmaps mE) /\ State.region_free (vm_reserved (m_vmmaps mE) ++ vm_maps (m_vmmaps mE)) (brk0w mE) n3w = true ->
                State.region_free (segments_reserved segsA ++ LmE) (brk0w mE) n3w = true
                /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0 mE + 8192 <= SHADOW_BAND_LO /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0 mE + 8192 <= TOPz).
  { intros [A1 A2]. rewrite top_mE in A1.
    pose proof (grant_avoids_band _ SHADOW_BAND_LO SHADOW_BAND_HI (brk0w mE) n3w band_mE ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) A2 ltac:(rewrite n3w_val; lia)) as A4.
    rewrite n3w_val, B3 in A4. rewrite MR, Hres, maps_mE_eq in A2. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *.
    split; [exact A2|]. split; lia. }
  destruct o1; cbn [out1_ok] in Ho; [apply GEN; exact Ho | apply GEN; exact Ho | apply GEN; exact Ho | exact I].
Qed.

Lemma place8k : ltac2:(tb__ "0|3|
S1Q40M0A1S41S0G0Z0A2M1S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM2S2fR1A4S41G1G2S0G0Z2000A2R2A4F_;Fa;").
Proof. clear. intros a H. pose proof pgw_n as (_ & _ & _ & _ & _ & E & _). rewrite E in H. exact H. Qed.

Local Notation limv := (vm_limit (m_vmmaps m)).
Local Notation ispv := (vm_init_sp (m_vmmaps m)).

Lemma minv8_mg : ltac2:(tb__ "0|4|
S47S48S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0R1A2S47OLo1;R2S4eS1cS1dS1Q40A1M1G1A2S1bG1G1S31G0A1S33A4S3dA3S5S3Vm;A1M2A1S6G2A1S2aVx;A1S34G0A1A5M3G3G3G1S19La;X47x4F_;Fo1;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hbrk Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbal OKF OKP.
  intros o1 Ho. pose proof (grow_facts o1 Ho) as GF. pose proof mg_shape as [SH LZ]. pose proof pgw_n as (_ & _ & _ & _ & N2 & _). pose proof brk_mE as (B1 & B2 & B3 & _).
  assert (GEN : State.region_free (segments_reserved segsA ++ LmE) (brk0w mE) n3w = true /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0 mE + 8192 <= SHADOW_BAND_LO /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0 mE + 8192 <= TOPz ->
                minv8 ((brk0w mE, n2w) :: LmE) limv ispv Q18 (mg mE)).
  { intros (G1 & G2 & G3).
    apply (minv8_cons_low LmE limv ispv Q18 mE (mg mE) (brk0w mE) n2w n3w minv8_mE G1).
    all: rewrite ?SH, ?LZ; try reflexivity; rewrite ?N2, ?n3w_val, ?B3; try lia. }
  destruct o1; cbv beta iota; cbv beta iota in GF; [apply GEN; exact GF | apply GEN; exact GF | apply GEN; exact GF | exact I].
Qed.

Lemma minv8_mg_ok : ltac2:(tb__ "0|3|
S48S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0S4bA2S4eS1cS1dS1Q40A1M1G1A2S1bG1G1S31G0A1S33A4S3dA3S5S3Vm;A1M2A1S6G2A1S2aVx;A1S38G0A1A5F_;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hbrk Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbal OKF OKP.
  intros Ho. pose proof (grow_facts O1_ok Ho) as GF. cbv beta iota in GF. destruct GF as (G1 & G2 & G3).
  pose proof (minv8_mg O1_ok Ho) as MI. cbv beta iota in MI.
  pose proof mg_ok_shape as [SH LZ]. pose proof mg_shape as [SHg LZg]. pose proof pgw_n as (_ & PG & _ & _ & N2 & _). pose proof brk_mE as (B1 & B2 & B3 & _).
  pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & _).
  apply (minv8_guard _ limv ispv Q18 (mg mE) (mg_ok mE) (brk0w mE) pgw (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0 mE) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0 mE + 4096) MI).
  all: rewrite ?SH, ?LZ, ?LZg; unfold mmap_fixed_ok_vm; cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_init_sp]; rewrite ?PG, ?N2;
       unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0, Start7.Q18 in *; unfold SHADOW_BAND_LO in *; try reflexivity; try lia.
  exists (brk0w mE), n2w. split; [left; reflexivity | rewrite ?PG, ?N2; lia].
Qed.

Lemma minv8_mg_dead : ltac2:(tb__ "0|5|
S48S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0S4aA2S4eS1cS1dS1Q40M1A1M2G2A2S1bG2G2S0G1S25S32G0A1Z1000M3A2A2S0G1G3A2A4S3dA3S5S3Vm;A1M4A1S6G4A1S2aVx;A1S37G0A1A5F_;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hbrk Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbal OKF OKP.
  intros Ho. pose proof (grow_facts O1_dead Ho) as GF. cbv beta iota in GF. destruct GF as (G1 & G2 & G3).
  pose proof (minv8_mg O1_dead Ho) as MI. cbv beta iota in MI.
  pose proof mg_dead_shape as [SH LZ]. pose proof mg_shape as [SHg LZg]. pose proof pgw_n as (_ & PG & _ & _ & N2 & _). pose proof brk_mE as (B1 & B2 & B3 & _).
  pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & _).
  assert (E4096 : Z_to_bv 64 4096 = Z_to_bv 64 (bv_unsigned (brk0w mE) + bv_unsigned n2w - (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0 mE + 4096)))
    by (f_equal; rewrite N2; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0; lia).
  rewrite E4096 at 1.
  apply (minv8_dead LmE limv ispv Q18 (mg mE) (mg_dead mE) (brk0w mE) n2w (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0 mE + 4096) MI).
  all: rewrite ?SH, ?LZ, ?LZg; unfold mmap_fixed_dead_vm; cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_init_sp]; rewrite ?PG, ?N2;
       unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.brk0, Start7.Q18 in *; unfold SHADOW_BAND_LO in *; try reflexivity; try lia.
Qed.

Lemma minv8_mf_res : ltac2:(tb__ "0|4|
S1Q40M0A1M1S41S0G0Z0A2S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM2S2fR1A4S4eS1cS1dG1G1A2S1bG1G1R2S2fA4S3dA3S5S3Vm;A1M3A1S6G3A1S2aVx;A1S36G2R2A2A5F_;Fa;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbrk Hbal OKF OKP.
  intros a Hpl. pose proof (mf_res_shape a) as [SH LZ]. pose proof pgw_n as (_ & _ & N8 & _).
  apply (minv8_reserve LmE limv ispv Q18 mE (mf_res mE a) 8192 a minv8_mE).
  all: rewrite ?SH, ?LZ; unfold mmap_none_vm; cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_init_sp]; rewrite ?N8; try reflexivity; try lia.
  exact (place8k a Hpl).
Qed.

Lemma minv8_mf_exp : ltac2:(tb__ "0|4|
S1Q40M0A1M1S41S0G0Z0A2S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM2S2fR1A4S4eS1cS1dG1G1A2S1bG1G1R2S2fA4S3dA3S5S3Vm;A1M3A1S6G3A1S2aVx;A1S35G2R2A2A5F_;Fa;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbrk Hbal OKF OKP.
  intros a Hpl. pose proof (mf_exp_shape a) as [SH LZ]. cbv zeta in SH. pose proof (mf_res_shape a) as [SHr LZr].
  apply (minv8_expose _ limv ispv Q18 (mf_res mE a) (mf_exp mE a) (bv_unsigned (a4 a)) (bv_unsigned (a4 a) + bv_unsigned pgw) (minv8_mf_res a Hpl)).
  all: rewrite ?SH, ?SHr, ?LZ, ?LZr; cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_init_sp]; try reflexivity.
  pose proof (urange pgw). lia.
Qed.

Lemma minv8_out1 : ltac2:(tb__ "0|3|
S47S48S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0R1A2S4eS20S1dS1Q40A1M1G1A2S3eR2A1S3dA3S5S3Vm;A1M2A1S6G2A1S2aVx;A1S4cG0R2A2A5F_;Fo1;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hbrk Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbal OKF OKP.
  intros o1 Ho. destruct o1 as [| | |a]; cbn [out1_model X1_18 List.app].
  - pose proof (minv8_mg O1_kept Ho) as MI. exact MI.
  - exact (minv8_mg_ok Ho).
  - exact (minv8_mg_dead Ho).
  - exact (minv8_mf_exp a Ho).
Qed.

Theorem minv8_out18 : ltac2:(tb__ "0|1|
S2bS2dVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;R1AbS4eS3fR2A1S5S3Vm;A1M0A1S6G0A1S2aVx;A1S2eVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;R2AbA5F_;Fo;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hbrk Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbal OKF OKP.
  intros o Ho. unfold L18. destruct o as [[|a]|o1|o1 g]; cbn [Start7.out18_model Start7.out18_ok out0_model X18 List.app] in Ho |- *.
  - exact minv8_mE.
  - exact (minv8_mf_res a Ho).
  - exact (minv8_out1 o1 Ho).
  - destruct Ho as [Ho Hg]. pose proof (minv8_out1 o1 Ho) as MI.
    pose proof (mgrant_shape (out1_model mE o1) g) as [SH LZ]. pose proof pgw_n as (PG & _ & _ & _ & _ & _ & E4).
    rewrite E4 in Hg |- *.
    apply (minv8_cong _ _ _ _ (eager_model 4096 (out1_model mE o1) g)).
    + rewrite SH. unfold eager_model. rewrite m_vmmaps_with_vmmaps. unfold mmap_rw_vm, eager_h. rewrite <- E4, PG. reflexivity.
    + rewrite LZ. unfold eager_model. rewrite m_vm_lazy_with_vmmaps. reflexivity.
    + apply minv8_eager; [exact MI | lia | reflexivity | lia | exact Hg].
Qed.

Lemma X18_facts : ltac2:(tb__ "0|6|
S2bS1Q40M0A1M1G1S2dVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;R3AbS5cS1dG1G1A2S1bG1G1R3R2A4S40R4A1A3S17S18S16S4dS2G0R3A2M2Z2000A3S16S4dG2Z1000M3A3A2S17S24G3S2G0R4A2M4A2S17S24S25G4G2A2M5S2cVx;A1A2S17S18S24G5Z10000A2S24Z646000G4A2A2S18S24G5S50A2S24S51G4A2A2A2A2A2A2F_;F_;Fs;Fb;Fo;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hbrk Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbal OKF OKP.
  intros o b s Ho Hin. pose proof (out18_Wok o Ho) as W. pose proof pgw_n as (_ & PG & _ & N8 & N2 & _). pose proof brk_mE as (B1 & B2 & B3 & _).
  assert (W1 : forall o1, out1_ok mE o1 -> In (b, s) (X1_18 o1) ->
            (bv_unsigned s = 8192 \/ bv_unsigned s = 4096) /\ 0x1000 <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= TOPz
            /\ (bv_unsigned b + bv_unsigned s <= 0x10000 \/ 0x646000 <= bv_unsigned b) /\ (bv_unsigned b + bv_unsigned s <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned b)).
  { intros o1 Ho1 Hin1. pose proof (out18_Wok (O18b o1) Ho1) as Wb. cbn [Start7.out18_W out1_W fst snd] in Wb.
    destruct o1 as [| | |a]; cbn [X1_18 In out1_base] in Hin1, Wb.
    - destruct Hin1 as [[= <- <-]|[]]. rewrite N2. unfold Start7.Wok in Wb. rewrite B3 in *. destruct Wb as [Wb|Wb]; [lia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. lia.
    - destruct Hin1 as [[= <- <-]|[]]. rewrite N2. unfold Start7.Wok in Wb. rewrite B3 in *. destruct Wb as [Wb|Wb]; [lia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. lia.
    - destruct Hin1 as [[= <- <-]|[]]. rewrite !u64_of_lit by lia. unfold Start7.Wok in Wb. rewrite B3 in *. destruct Wb as [Wb|Wb]; [lia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. lia.
    - destruct Hin1 as [[= <- <-]|[]]. rewrite N8. unfold Start7.Wok in Wb. destruct Wb as [Wb|Wb]; [lia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. lia. }
  destruct o as [[|a]|o1|o1 g]; cbn [X18 Start7.out18_ok out0_ok] in Hin, Ho.
  - destruct Hin.
  - destruct Hin as [[= <- <-]|[]]. rewrite N8. cbn [Start7.out18_W out0_W fst snd] in W. unfold Start7.Wok in W. destruct W as [W|W]; [lia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. lia.
  - exact (W1 o1 Ho Hin).
  - destruct Ho as [Ho Hg]. destruct Hin as [[= <- <-]|Hin]; [|exact (W1 o1 Ho Hin)].
    pose proof pgw_n as (_ & _ & _ & _ & _ & _ & E4). rewrite E4 in Hg. rewrite PG.
    pose proof (minv8_place _ _ _ _ _ 4096 g (minv8_out1 o1 Ho) ltac:(lia) eq_refl ltac:(lia) Hg) as (P1 & P2 & P3 & P4 & _).
    change (LB_of 4096) with 0x1000 in P1.
    assert (UI : bv_unsigned ispv = x) by (unfold alloc_top in Hxtop; rewrite stack_max_size_val in Hxtop; lia).
    unfold Start7.TOPz. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. lia.
Qed.

End Seg8M.
End Start8Out.

(* [comment removed for export] *)
Module Start8CallDefs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "cell"; "DZero"; "SVar"; "c_off"; "c_val"; "enc_bytes"; "mkObj"; "ob_cells"; "sobj"; "ss_fregs"; "ss_objs"; "ss_regs"; "sv_eqb"; "@Corelib.Init.Datatypes"; "nat"; "pair"; "cons"; "app"; "nil"; "option"; "prod"; "Some"; "list"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Lists.ListDef"; "nth"; "map"; "seq"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Nat"; "add"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs"; "cellv22"; "AFL1V"; "AFL2V"; "odummy22"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueD"; "subcell_val"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "image_bytes"; "@Stdlib.Lists.List"; "find"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "of_nat"; "sub"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CompleteA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start8States0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.Start8RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8States0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition splits22 : list (nat * sv) := ltac2:(tb__ "0|3|
S11S15SfS0A2M0S10SfS0U2aS1N11c0A1A4S11G0S10SfS0U2bS1N70A1A4S11G0S10SfS0UfM1S1Z173648A1A4S11G0S10SfS0U10M2S1Z173658A1A4S11G0S10SfS0UbS1Ze9b30A1A4S11G0S10SfS0UcS1Ze9b38A1A4S11G0S10SfS0UdS1Zec560A1A4S11G0S10SfS0UeS1Zedd20A1A4S11G0S10SfS0G1S1Zeebf8A1A4S11G0S10SfS0G2S1Zeec24A1A4S11G0S10SfS0U11S1Zeec30A1A4S11G0S10SfS0U12S1Zeec70A1A4S11G0S10SfS0U13S1Zeecc0A1A4S11G0S10SfS0U14S1Zf0c5cA1A4S11G0S10SfS0U15S1Zf0c5dA1A4S13G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition odummy22 : sobj := ltac2:(tb__ "0|1|
S8S1Z0A1M0G0G0S13S2A1S3A5").
Definition ob22 (St : sstate) (i : nat) : sobj := ltac2:(tb__ "0|0|
S1aSaVi;ScVSt;A1S24A4").
Definition cellv22 (o : sobj) (off : Z) : sv := ltac2:(tb__ "0|0|
S14S2A1S0Lx;S28S2S2SeS5R1A1S1Voff;A1A2Lc;S9Vo;A1A3S2S6R1A1Lc;S1Z0A1X14x2").

Definition mk_s22 (St : sstate) (win : sobj) : wsub := ltac2:(tb__ "0|5|
S12S15S18S0A2M0S11G0S10S18S0P1S4P1bA1A4S11G0S10S18S0P2S1aS0U8SdVSt;A1M1S1Z0A1M2A4A4S11G0S10S18S0P3S21Vwin;N78A2A4S13G0A1A3A3A3S12G0S1bSfG0SfS10S18S0S20S1fU4R1A2A1S21Vwin;S2bN80S29Z8S2aR1A1A2A2A2A4Lk;S1cU0M3UcA2A4S12G0S1bSfG0SfS10S18S0S20S1fU14R1A2A1S1aS0R1SbVSt;A1G2A4A4Lr;S1cG3U20A2M4A4S1bSfG0SfS10S18S0S20S1fU3cR1A2A1S1aS0R1G1G2A4A4Lr;G4A4A3A3A3").
Definition AFL1V : Z := 72340168526266369.
Definition AFL2V : Z := 72340172838010881.
Lemma subcell_vals22 : ltac2:(tb__ "0|1|
S1eS1dS19S25S22Z0Z4A3Z1M0A3S1dS19S25S23Z5G0A3G0A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma gl_img22 : ltac2:(tb__ "0|2|
S1dS14S17S2dQ8A1A1M0A1S27S26Zeec78U8M1A3S16G0S7G1S2cQ40Z0A2A2A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition PGA : word := Z_to_bv 64 0x7fffc000.
Definition PGB : word := Z_to_bv 64 0x80015000.
Definition MAINPC : Z := 0x8c390.
End Start8CallDefs.

(* [comment removed for export] *)
Module Start8StatesA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "list"; "option"; "Some"; "app"; "prod"; "bool"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "sym_runA"; "mkLeafA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "@Corelib.Init.Decimal"; "D0"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "sobj"; "ss_objs"; "SVar"; "ss_next"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8StatesA"; "E23A"; "E24A"; "EGA"; "GPC"; "S23okA"; "S22okA"; "S24okA"; "SPIN22A"; "SPIN23A"; "SPIN24A"; "S23ok0A"; "E23A_R"; "E24A_R"; "EGA_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "fail_state"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8States0"; "E22A"; "F22"; "F23"; "F24"; "o13p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "axA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "mmap_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7States Start8States0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8States0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition S22okA : axst := ltac2:(tb__ "0|2|
S40S41S3bS42S12S3aA1M0S20P9fM1A1SaS1eS1fG0A1S4S1eS43G1Z100000A2S5S1eA1A3A3Pa0A4A2A1").
Lemma S22okA_eq : eager_ok E22A 0x100000 160%positive = S22okA.
Proof. reflexivity. Qed.
Definition E23A_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z7050cS4S0Z6bd84S5S0A1A3A3S2eS6A5").
Local Strategy expand [E23A_run__R].
Definition E23A_R : option (list leafA) := Eval vm_compute in ((fun ro1__ : option (list leafA) => ro1__) E23A_run__R).
Lemma E23A_run : ltac2:(tb__ "0|0|
S2S8S7SfA1A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z7050cS4S0Z6bd84S5S0A1A3A3S2eS6A5S34A3").
Proof. exact (@eq_refl (option (list leafA)) E23A_run__R <: E23A_run__R = E23A_R). Qed.
Definition E23A : axst := Eval vm_compute in (match E23A_R with Some (l :: _) => la_state l | _ => S22okA end).
Lemma run23A : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z7050cS4S0Z6bd84S5S0A1A3A3S2eS6A5S9G0S4SfS11S29S26A2S5SfA1A3A2A3").
Proof. rewrite E23A_run. reflexivity. Qed.
Definition run22A_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23U12cS4S0Z6bd84S5S0A1A3S37S3aA1S6A5").
Local Strategy expand [run22A_fail__R].
Definition SPIN22A : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => (leaf1 (fail_state E22A) (ro2__))) run22A_fail__R).
Lemma run22A_fail : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U12cS4S0Z6bd84S5S0A1A3S37S3aA1S6A5S9G0S4SfS11S30S26A2S5SfA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run22A_fail__R <: run22A_fail__R = Some [mkLeafA SPIN22A RsCut]). Qed.
Lemma spin22A : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U2S4S0Z6bd84S5S0A1A3S30S6A5S9G0S4SfS11S30S26A2S5SfA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E23A_at : ltac2:(tb__ "0|4|
S3S2S0S22S12S29A1M0A1M1Z7050cA3S3S2S1S21G0A1Pa0A3S3S2S8S38A1S27S23G1A2S9S38S39A2A3S3S2S7SbS1bS1bA2M2A1S13S29A1S5G2A1A3S3S2S1bS14S29A1S1cS3fA1A3S3S2S1bS1dG0Z11A2S1cZdeA1A3S3S2S1bS1dG0ZaA2S1cZ0A1M3A3S3S2S1bS1dG0ZbA2S1cZ800000A1A3S3S2S1bS1dG0ZcA2S1cZ3A1A3S3S2S1bS1dG0ZdA2S1cZ4022A1A3S3S2S1bS1dG0ZeA2S1cZffffffffffffffffA1A3S2S1bS1dG0ZfA2G3A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition S23ok0A : axst := ltac2:(tb__ "0|1|
S40S41S3cS42S12S29A1M0S20Pa0A1S1fG0A1Pa1A4A2A1").
Lemma S23ok0A_eq : null_rw_ok E23A 0x800000 161%positive = S23ok0A.
Proof. reflexivity. Qed.
Definition S23okA : axst := Eval vm_compute in set_objs' S23ok0A (ss_objs (ax_S S23ok0A) ++ [o13p]).
Lemma S23okA_eq : ltac2:(tb__ "0|2|
S3S2S16S15S33S28S12S33A1M0SaS1eS1fG0A1S4S1eS3eS5S1eA1A3A3A2M1A2S2dA3S2ScS44G0G1A2S6A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E24A_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z7050cS4S0Z6bd84S5S0A1A3A3S2dS6A5").
Local Strategy expand [E24A_run__R].
Definition E24A_R : option (list leafA) := Eval vm_compute in ((fun ro3__ : option (list leafA) => ro3__) E24A_run__R).
Lemma E24A_run : ltac2:(tb__ "0|0|
S2S8S7SfA1A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z7050cS4S0Z6bd84S5S0A1A3A3S2dS6A5S35A3").
Proof. exact (@eq_refl (option (list leafA)) E24A_run__R <: E24A_run__R = E24A_R). Qed.
Definition E24A : axst := Eval vm_compute in (match E24A_R with Some (l :: _) => la_state l | _ => S23okA end).
Lemma run24A : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z7050cS4S0Z6bd84S5S0A1A3A3S2dS6A5S9G0S4SfS11S2aS26A2S5SfA1A3A2A3").
Proof. rewrite E24A_run. reflexivity. Qed.
Definition run23A_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23U12cS4S0Z6bd84S5S0A1A3S37S29A1S6A5").
Local Strategy expand [run23A_fail__R].
Definition SPIN23A : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => (leaf1 (fail_state E23A) (ro4__))) run23A_fail__R).
Lemma run23A_fail : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U12cS4S0Z6bd84S5S0A1A3S37S29A1S6A5S9G0S4SfS11S31S26A2S5SfA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run23A_fail__R <: run23A_fail__R = Some [mkLeafA SPIN23A RsCut]). Qed.
Lemma spin23A : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U2S4S0Z6bd84S5S0A1A3S31S6A5S9G0S4SfS11S31S26A2S5SfA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E24A_at : ltac2:(tb__ "0|4|
S3S2S0S22S12S2aA1M0A1M1Z7050cA3S3S2S1S21G0A1Pa1A3S3S2S8S38A1S27S23G1A2S9S38S39A2A3S3S2S7SbS1bS1bA2M2A1S13S2aA1S5G2A1A3S3S2S1bS14S2aA1S1cS3fA1A3S3S2S1bS1dG0Z11A2S1cZdeA1A3S3S2S1bS1dG0ZaA2S1cZ0A1M3A3S3S2S1bS1dG0ZbA2S1cZ1000A1A3S3S2S1bS1dG0ZcA2S1cZ3A1A3S3S2S1bS1dG0ZdA2S1cZ22A1A3S3S2S1bS1dG0ZeA2S1cZffffffffffffffffA1A3S2S1bS1dG0ZfA2G3A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition S24okA : axst := ltac2:(tb__ "0|2|
S40S41S3dS42S12S2aA1M0S20Pa1M1A1SaS1eS1fG0A1S4S1eS43G1Z1000A2S5S1eA1A3A3Pa2A4A2A1").
Lemma S24okA_eq : eager_ok E24A 4096 162%positive = S24okA.
Proof. reflexivity. Qed.
Definition GPC : Z := 0x49fec.
Definition EGA_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0S2cS4S0Z7050cS4S0Z6bd84S5S0A1A3A3A3S2fS6A5").
Local Strategy expand [EGA_run__R].
Definition EGA_R : option (list leafA) := Eval vm_compute in ((fun ro5__ : option (list leafA) => ro5__) EGA_run__R).
Lemma EGA_run : ltac2:(tb__ "0|0|
S2S8S7SfA1A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0S2cS4S0Z7050cS4S0Z6bd84S5S0A1A3A3A3S2fS6A5S36A3").
Proof. exact (@eq_refl (option (list leafA)) EGA_run__R <: EGA_run__R = EGA_R). Qed.
Definition EGA : axst := Eval vm_compute in (match EGA_R with Some (l :: _) => la_state l | _ => S24okA end).
Lemma runGA : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0S2cS4S0Z7050cS4S0Z6bd84S5S0A1A3A3A3S2fS6A5S9G0S4SfS11S2bS26A2S5SfA1A3A2A3").
Proof. rewrite EGA_run. reflexivity. Qed.
Definition run24A_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23U12cS4S0Z6bd84S5S0A1A3S37S2aA1S6A5").
Local Strategy expand [run24A_fail__R].
Definition SPIN24A : axst := Eval vm_compute in ((fun ro6__ : option (list leafA) => (leaf1 (fail_state E24A) (ro6__))) run24A_fail__R).
Lemma run24A_fail : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U12cS4S0Z6bd84S5S0A1A3S37S2aA1S6A5S9G0S4SfS11S32S26A2S5SfA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run24A_fail__R <: run24A_fail__R = Some [mkLeafA SPIN24A RsCut]). Qed.
Lemma spin24A : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U2S4S0Z6bd84S5S0A1A3S32S6A5S9G0S4SfS11S32S26A2S5SfA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma EGA_at : ltac2:(tb__ "0|2|
S3S2S0S22S12S2bA1M0A1S2cA3S3S2S1S21G0A1Pa2A3S3S2S7SbS1bS1bA2M1A1S13S2bA1S5G1A1A3S3S2S1bS14S2bA1S1cS3fA1A3S2SeSdS1eS1fG0A1A2U31A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start8StatesA.

