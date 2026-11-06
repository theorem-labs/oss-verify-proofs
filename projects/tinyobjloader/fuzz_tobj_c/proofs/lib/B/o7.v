(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From Stdlib Require Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2 o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_fuzz_iface2 nl ot.

(* [comment removed for export] *)
Module StartGlueE.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA"; "bump_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "axwf"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "smatch"; "swf"; "valuation"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma smatch_set_next : ltac2:(tb__ "0|0|
SeSfSbS5S4S13A1S12A2S6S2SdS0R3R2A2A1S3A3ScS1R5R4R2A4ScS1R6S0R5R4A2R3A4F_;F_;Fw;Fnx;FS;Frho;").
Proof.
  intros rho S nx [tr [ms md]] Hwf' Hsm.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  unfold smatch, bump_next in *. cbn [fst snd cfg_ms cfg_model ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in *.
  split; [exact Hwf'|]. repeat (split; [assumption|]). exact Hfacts.
Qed.

Lemma SPA_set_next : ltac2:(tb__ "0|0|
S11SeS9SbS4S15Q40A1A1S14S6S2SdS0S7R4A1R3A2A1S3A3S6S2SaS8R5S0S7R5A1R4A2A2A1S3A3S10S1R8R6R7R4R3A6S10S1R9S8R7S0S7R7A1R6A2A2R8R5R4A6F_;F_;F_;Fw;Ftp;Fnx;FA;Frho;FJ;").
Proof.
  intros J rho A nx tp w Hwf' Hax' [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  split; [|split; [exact HMI | split; [exact Hax' | split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [ax_S ax_setS]. apply smatch_set_next; assumption.
  - unfold shadow_ok in Hsh |- *. cbn [ax_S ax_setS ax_X ax_base bump_next ss_objs] in Hsh |- *. exact Hsh.
Qed.
End StartGlueE.

(* [comment removed for export] *)
Module Start6.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "mul"; "pow"; "sub"; "div"; "eqb"; "ge"; "of_nat"; "opp"; "to_nat"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "rm"; "sprop"; "sv"; "holds"; "rl"; "ss_facts"; "SLit"; "eval"; "sprop_eqb"; "sobj"; "SVar"; "SAlu"; "SPUle"; "agree_below"; "ss_objs"; "SPAlign"; "SPEq"; "ext_low"; "mkSS"; "obj_range"; "ranges_disjoint"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "pair"; "cons"; "prod"; "true"; "nil"; "option"; "Some"; "app"; "false"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "vm_noaccess"; "vm_maps"; "m_vm_lazy"; "alloc_top"; "vm_reserved"; "event"; "maps_subtract"; "page_in_ranges"; "vm_limit"; "lazy_interior"; "vm_init_sp"; "page_size"; "map_remove"; "page_mem"; "vm_add_lazy"; "vm_forget_range"; "with_vmmaps"; "VmMaps"; "iv_subtract"; "region_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.Seg6"; "mF"; "x1"; "vals"; "B16L"; "m16"; "b9lo"; "BF"; "n17"; "TP16"; "enspage"; "LOWPGw"; "TP17"; "B17"; "G17"; "Post16"; "Post17"; "Post6"; "XF16"; "m17"; "n16"; "RM16"; "RM6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "erase_mat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5"; "TP12"; "stackshadow_zero"; "m13"; "G14b"; "G13b"; "m12"; "m15"; "vals12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6"; "HPz"; "tcls"; "v80Z"; "q12x"; "LIMz"; "v79Z"; "PEz"; "topZ"; "e12x"; "shx"; "Ktr"; "PBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States"; "LOWPG"; "classes16"; "R16pre"; "R16c"; "LEN16"; "O_lowpg"; "PB"; "R16m"; "c1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "init_sp_ok"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "mkLeafA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4"; "Z11"; "m8"; "n9"; "pRI"; "priZ"; "sbZ"; "bandav"; "m10"; "m11"; "m9"; "n7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "SHADOW_RW_LO_END"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Start6JStates"; "E_s17"; "M16_of"; "CF16"; "F17_of"; "IP16_of"; "IPr_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Start5bStates"; "S_s15ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "agree_vars"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS"; "RMH";
"@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "withX0"; "pages_rev"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates"; "E18"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "@LinuxProcessSemantics.Riscv.Prelude"; "bv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "shRI_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes"; "LB_of"; "eager_model"].
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
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA
  MmapA MmapFixedA MmapFixedA2 MmapNodesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib KxA Placement PlacementA Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Start5bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o2.Start6Aux OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.StartGlueE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition Tq (x : Z) : Z := (x + 3935) / 4096.
Definition topZ (x : Z) : Z := 4096 * Tq x.
Definition tcls (x : Z) : Z := Tq x mod 8.
Definition v79Z (x : Z) : Z := ltac2:(tb__ "0|0|
SdSdS86Vx;A1Z800000A2SbZ1000S80Vx;A1A2A2").
Definition v80Z (x : Z) : Z := v79Z x / 8.
Definition shx (x : Z) : Z := x / 8 + 0x7fff8000.
Definition e12x (x : Z) : Z := ltac2:(tb__ "0|0|
SdS88Vx;A1Z9A2S5SdR1SaR1Z1000A2A2Ts;").
Definition q12x (x : Z) : Z := ltac2:(tb__ "0|0|
SdS88Vx;A1Z20000A2S5SdR1SaR1Z1000A2A2Ts;").
Definition HPz (x : Z) : Z := v80Z x + 0x7fff8000.
Definition PEz (x : Z) : Z := v80Z x + PE.
Definition PBz (x : Z) : Z := ltac2:(tb__ "0|0|
S8S81Vx;A1S91S80Vx;A1A1A2").
Definition LIMz (x : Z) : Z := ltac2:(tb__ "0|0|
SdS8SeSdVx;SaVx;Z1000A2A2Z8A2Z7fff8000A2Z100000A2").

Lemma class_arith : ltac2:(tb__ "0|e|
S5S1S7Z7fff80000000M0R1A2S7R1ScZ2Z2fA2M1A2A2S0S5SaR2Z10A2Z0M2A3S80R3A1S5S84R4A1S5S81R5A1S5S1S1S7G2R3A2S7R3Z7A2A2S1S0S5SaR2Z8000A2G2A3S1S0S5SbR1Z8A2R2A3S1S0S5SaR1Z1000M3A2G2A3S1S7G2R1A2S1S7SdZ7fff7f800000SbG3R3A2A2R2A2S1S7S8R2S93R3A1A2M4G1A2S1S1S7SdR6Za0A2S86R6A1M5A2S7G5S8R6Zf5fA2M6A2A2S1S0S5G5G4A3S1S0S5SaG5G3A2G2A3S1S7G0G5A2S1S0S5SdG6SaG6G3A2A2G5A3S1S0S5SaS7fR6A1M7G3A2G2A3S1S0S5SaS85R6A1M8G3A2G2A3S1S0S5SaS8aR6A1M9G3A2G2A3S1S0S5G9S37S5L_;SfR3G2A2G7S8G7G3A2MaX37x2A3S1S0S5S8G9S8fR3A1A2G8A3S1S0S5G8S8G7Z100000A2A3S1S7Z10006fef8000MbG7A2S1S7G8Z10007fff8000A2S1S1S7S87R6A1McG8A2S7G8S8GcG3A2A2A2S1S7GaS82R6A1A2S1S0S5SaGcG3A2G2A3S1S7S83R6A1MdS8G7SbZ200R3A2A2A2S7GbGdA2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2TV80;TV79;Tt;F_;F_;Fx;").
Proof.
  intros x Hx H16 t V79 V80.
  pose proof (Z.div_mod (x + 3935) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x + 3935) 4096 ltac:(lia)) as M1.
  set (r1 := (x + 3935) mod 4096) in *. set (T := Tq x) in *. unfold Tq in T. fold T in D1.
  pose proof (Z.div_mod T 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound T 8 ltac:(lia)) as M2.
  set (G := T / 8) in *. unfold tcls in t. fold T in t. change (T mod 8) with t in D2, M2 |- *.
  assert (X8 : x mod 8 = 0) by (apply Z.mod_divide in H16 as [k Hk]; [|lia]; rewrite Hk; replace (k * 16) with ((2 * k) * 8) by lia; apply Z_mod_mult).
  pose proof (Z.div_mod x 8 ltac:(lia)) as D3. rewrite X8 in D3. set (x8 := x / 8) in *.
  pose proof (Z.div_mod x 4096 ltac:(lia)) as D6. pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as M6.
  set (r6 := x mod 4096) in *. set (x4 := x / 4096) in *.
  assert (HL : LIMz x = 512 * x4 + 0x7fff8000 - 1048576).
  { unfold LIMz. fold r6. replace (x - r6) with (x4 * 512 * 8) by lia. rewrite Z_div_mult by lia. lia. }
  assert (Htop : topZ x = 4096 * T) by reflexivity.
  assert (HV79 : V79 = 32768 * (G - 256)) by (subst V79; unfold v79Z, tcls; fold T; fold t; rewrite Htop; lia).
  assert (HV80 : V80 = 4096 * (G - 256)) by (subst V80; unfold v80Z; fold V79; rewrite HV79; replace (32768 * (G - 256)) with ((4096 * (G - 256)) * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
  assert (Hsh : shx x = x8 + 0x7fff8000) by reflexivity.
  pose proof (Z.div_mod (shx x - 9) 4096 ltac:(lia)) as D4. pose proof (Z.mod_pos_bound (shx x - 9) 4096 ltac:(lia)) as M4.
  set (r4 := (shx x - 9) mod 4096) in *. set (m4 := (shx x - 9) / 4096) in *.
  pose proof (Z.div_mod (shx x - 131072) 4096 ltac:(lia)) as D5. pose proof (Z.mod_pos_bound (shx x - 131072) 4096 ltac:(lia)) as M5.
  set (r5 := (shx x - 131072) mod 4096) in *. set (m5 := (shx x - 131072) / 4096) in *.
  assert (He : e12x x = (shx x - 9) - r4) by reflexivity.
  assert (Hq : q12x x = (shx x - 131072) - r5) by reflexivity.
  assert (HHP : HPz x = V80 + 0x7fff8000) by reflexivity.
  assert (HPE : PEz x = V80 + 0x800f8000) by reflexivity.
  assert (HPB : PBz x = V80 + PB t) by reflexivity.

  assert (HT : T = x4 \/ T = x4 + 1) by lia.
  clearbody t V79 V80 T G x8 r1 r4 m4 r5 m5 r6 x4.
  assert (A1 : V79 mod 32768 = 0) by (rewrite HV79; replace (32768 * (G - 256)) with ((G - 256) * 32768) by lia; apply Z_mod_mult).
  assert (A2 : V80 mod 4096 = 0) by (rewrite HV80; replace (4096 * (G - 256)) with ((G - 256) * 4096) by lia; apply Z_mod_mult).
  assert (A3 : topZ x mod 4096 = 0) by (rewrite Htop; replace (4096 * T) with (T * 4096) by lia; apply Z_mod_mult).
  assert (A4 : HPz x mod 4096 = 0) by (rewrite HHP, HV80; replace (4096 * (G - 256) + 2147450880) with ((G - 256 + 524280) * 4096) by lia; apply Z_mod_mult).
  assert (A5 : PEz x mod 4096 = 0) by (rewrite HPE, HV80; replace (4096 * (G - 256) + 2148499456) with ((G - 256 + 524536) * 4096) by lia; apply Z_mod_mult).
  assert (A6 : PBz x mod 4096 = 0).
  { rewrite HPB, HV80. unfold PB. destruct (Z.eqb_spec t 0).
    + replace (4096 * (G - 256) + 2147450880) with ((G - 256 + 524280) * 4096) by lia. apply Z_mod_mult.
    + replace (4096 * (G - 256) + 2147454976) with ((G - 256 + 524281) * 4096) by lia. apply Z_mod_mult. }
  assert (A7 : e12x x mod 4096 = 0) by (rewrite He; replace (shx x - 9 - r4) with (m4 * 4096) by lia; apply Z_mod_mult).
  assert (A8 : PBz x = (if t =? 0 then HPz x else HPz x + 4096)) by (rewrite HPB, HHP; unfold PB; destruct (Z.eqb_spec t 0); lia).
  assert (A9 : PBz x + LEN16 t = PEz x) by (rewrite HPB, HPE; unfold PB, PE, LEN16; destruct (Z.eqb_spec t 0); lia).
  unfold PE, c1 in *.
  assert (A10 : e12x x <= PEz x <= e12x x + 4096) by lia.
  assert (A11 : HPz x + 4096 <= q12x x) by lia.
  assert (A12 : LIMz x <= HPz x + 512 * t) by (rewrite HL, HHP, HV80; first [lia | nia]).
  assert (A13 : 0x10006fef8000 <= LIMz x) by (rewrite HL; lia).
  repeat split; try assumption; try lia.
Qed.

Lemma class_arith_B : ltac2:(tb__ "0|3|
S5S1S7Z7fff80000000R1A2S7R1ScZ2Z2fA2A2A2S0S5SaR2Z10A2Z0M0A3S3S0S5S80R3A1G0A3A1S1S7S8S85R4A1Z1000A2Z10007fff8000A2S1S7Z200M1SbG1S80R4A1A2M2A2S7G2Ze00A2A2A2F_;F_;F_;Fx;").
Proof.
  intros x Hx H16 Ht.
  pose proof (Z.div_mod (x + 3935) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x + 3935) 4096 ltac:(lia)) as M1.
  set (r1 := (x + 3935) mod 4096) in *. set (T := Tq x) in *. unfold Tq in T. fold T in D1.
  pose proof (Z.div_mod T 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound T 8 ltac:(lia)) as M2.
  set (G := T / 8) in *. set (t := T mod 8) in *.
  assert (Htop : topZ x = 4096 * T) by reflexivity. assert (Htc : tcls x = t) by reflexivity. rewrite Htc in Ht |- *.
  assert (HV79 : v79Z x = (4096 * (G - 256)) * 8) by (unfold v79Z; rewrite Htop, Htc; lia).
  assert (HV80 : v80Z x = 4096 * (G - 256)) by (unfold v80Z; rewrite HV79; apply Z_div_mult; lia).
  unfold PEz, PE. rewrite HV80. clearbody r1 T G t. lia.
Qed.

Lemma aligned_end_LIM : ltac2:(tb__ "0|0|
S5S5S7Z0R2A2S7SbZ1000R3A2SdR2Z800000A2A2S7S8SbZ200R4A2Z7fff8000A2S83R3A1A2F_;F_;Fx;Fk;").
Proof.
  intros k x H0 Hle. unfold LIMz.
  pose proof (Z.div_mod x 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as M.
  set (x4 := x / 4096) in *. set (r := x mod 4096) in *.
  replace (x - r) with (x4 * 512 * 8) by lia. rewrite Z_div_mult by lia. lia.
Qed.

Lemma site_arith : ltac2:(tb__ "0|6|
S5S1S7Z7fff80000000R1A2S7R1ScZ2Z2fA2A2A2S0S5SaR2Z10A2Z0M0A3S80R3A1S5S1S0S5SaS82R4A1M1Z1000M2A2G0A3S1S7S8S7fR4A1M3G2A2G1A2S1S7SdG1G3A2SbG2Ze0A2A2S1S2S5S5S1S1S7G0R1A2S7R1ZdfA2A2S0S5S82R5A1S8S8S7fR5A1G2A2SbG2R1A2A2A3A2Ln;A2S1S7G1S85R4A1M4A2S1S7S8G4SbZ200R1A2A2S8S87R4A1G2A2M5A2S7G5Z10007fff9000A2A2A2A2A2A2A2Tt;F_;F_;Fx;").
Proof.
  intros x Hx H16 t.
  pose proof (Z.div_mod (x + 3935) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x + 3935) 4096 ltac:(lia)) as M1.
  set (r1 := (x + 3935) mod 4096) in *. set (T := Tq x) in *. unfold Tq in T. fold T in D1.
  pose proof (Z.div_mod T 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound T 8 ltac:(lia)) as M2.
  set (G := T / 8) in *. unfold tcls in t. fold T in t. change (T mod 8) with t in D2, M2 |- *.
  assert (X8 : x mod 8 = 0) by (apply Z.mod_divide in H16 as [k Hk]; [|lia]; rewrite Hk; replace (k * 16) with ((2 * k) * 8) by lia; apply Z_mod_mult).
  pose proof (Z.div_mod x 8 ltac:(lia)) as D3. rewrite X8 in D3. set (x8 := x / 8) in *.
  assert (Htop : topZ x = 4096 * T) by reflexivity.
  assert (HV79 : v79Z x = 32768 * (G - 256)) by (unfold v79Z, tcls; fold T; fold t; rewrite Htop; lia).
  assert (HV80 : v80Z x = 4096 * (G - 256)) by (unfold v80Z; rewrite HV79; replace (32768 * (G - 256)) with ((4096 * (G - 256)) * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
  assert (Hsh : shx x = x8 + 0x7fff8000) by reflexivity.
  pose proof (Z.div_mod (shx x - 9) 4096 ltac:(lia)) as D4. pose proof (Z.mod_pos_bound (shx x - 9) 4096 ltac:(lia)) as M4.
  set (r4 := (shx x - 9) mod 4096) in *. set (m4 := (shx x - 9) / 4096) in *.
  pose proof (Z.div_mod (shx x - 131072) 4096 ltac:(lia)) as D5. pose proof (Z.mod_pos_bound (shx x - 131072) 4096 ltac:(lia)) as M5.
  set (r5 := (shx x - 131072) mod 4096) in *. set (m5 := (shx x - 131072) / 4096) in *.
  assert (He : e12x x = (shx x - 9) - r4) by reflexivity.
  assert (Hq : q12x x = (shx x - 131072) - r5) by reflexivity.
  assert (HHP : HPz x = v80Z x + 0x7fff8000) by reflexivity.
  assert (HPE : PEz x = v80Z x + 0x800f8000) by reflexivity.
  clearbody t T G x8 r1 r4 m4 r5 m5.
  assert (A1 : q12x x mod 4096 = 0) by (rewrite Hq; replace (shx x - 131072 - r5) with (m5 * 4096) by lia; apply Z_mod_mult).
  split; [exact A1|].
  assert (Q : q12x x = 4096 * m5) by lia.
  assert (HP : HPz x = 4096 * (G - 256 + 524280)) by lia.
  assert (E : e12x x = 4096 * m4) by lia.
  split; [lia|]. split; [lia|]. split; [exists (m5 - (G - 256 + 524280) - 1); lia|].
  split; [lia|]. split; [lia|]. lia.
Qed.

Lemma page_in_ranges_subtract : ltac2:(tb__ "0|3|
S15Q40M0A1M1S36S3aG1G1A2A1S5S5Sb4R3A1S7R3R2A2S0S37S4dR6R5A2S3bA3S4S7S8S16G0R7A2M2S51A2R5A2S7R4G2A2A2S0S37S4dR8S4cR7R6R5A3A2S3bA3F_;F_;F_;F_;Fhi;Flo;Fl;Fp;").
Proof.
  intros p l lo hi Hwf Hlh Hin Hd. apply page_in_ranges_spec in Hin as ([a sz] & Hr & Hpr). apply page_in_range_spec in Hpr. cbn [fst snd] in Hpr.
  pose proof (Hwf _ Hr) as W. unfold iv_wf, ivB, ivS in W. cbn [fst snd] in W.
  pose proof (urange a) as Ra. pose proof (urange sz) as Rs. pose proof (urange p) as Rp. pose proof page_size_pos as PS.
  apply page_in_ranges_spec.
  assert (IN : forall q, In q (iv_subtract a sz lo hi) -> In q (maps_subtract l lo hi)).
  { clear - Hr. induction l as [|[a' sz'] l IH]; [destruct Hr|]. intros q Hq. cbn [maps_subtract]. apply in_app_iff.
    destruct Hr as [[= <- <-]|Hr]; [left; exact Hq | right; exact (IH Hr q Hq)]. }
  destruct Hd as [Hd|Hd].
  - exists (a, Z_to_bv 64 (Z.min (bv_unsigned sz) (lo - bv_unsigned a))). split.
    + apply IN. unfold iv_subtract. cbv zeta. apply in_app_iff. left. rewrite (proj2 (Z.ltb_lt _ _)) by lia. left. reflexivity.
    + apply page_in_range_spec. cbn [fst snd]. rewrite u64_of_lit by lia. lia.
  - exists (Z_to_bv 64 (Z.max (bv_unsigned a) hi), Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)). split.
    + apply IN. unfold iv_subtract. cbv zeta. apply in_app_iff. right. rewrite (proj2 (Z.ltb_lt _ _)) by lia. left. reflexivity.
    + apply page_in_range_spec. cbn [fst snd]. rewrite !u64_of_lit by lia. lia.
Qed.

Lemma covered_subtract_false : ltac2:(tb__ "0|1|
S36S3aS15Q40A1M0G0A2A1S5S5S5Sb4R4A1S7R4R3A2S0S37Sb3R6R3A2S40A3S0S37Sb3S4cR7R6R5A3R4A2S40A3F_;F_;F_;Fz;Fhi;Flo;Fl;").
Proof.
  intros l lo hi z Hwf Hlh Hc. destruct (maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & Cv). rewrite Cv, Hc. reflexivity.
Qed.

Lemma in_maps_subtract_of : ltac2:(tb__ "0|2|
S36S3aS15Q40A1M0G0A2M1A1G0G0S5S5G1S41G1S38G0G0R5R4A4R6A3S41G1R2S58R6R5R4R3A4A3S41G1R3S4cR8R5R4A3A3F_;F_;Fq;Fhi;Flo;Fsz;Fa;Fl;").
Proof.
  induction l as [|[a' s'] l IH]; intros a sz lo hi q Hin Hq; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [[= <- <-]|Hin]; [left; exact Hq | right; exact (IH _ _ _ _ _ Hin Hq)].
Qed.

Lemma erase_mat_cong_rereserve : ltac2:(tb__ "0|1|
S45S45S57S15Q40A1M0G0S5S5S0S45S76R7A1S76R6A1A3S0S45S76S54R5R4S55R3R2S56R6R8A2A3A3A1S76S54R5R4S55R3R2S56R6R7A2A3A3A1A3F_;Fhi;Flo;Fn;Fa;Fh;Fm;Fmd;").
Proof.
  intros md m h a n lo hi H. rewrite (erase_mat_shape md m H).
  destruct m as [fd' [maps' lz' mat'] io' fs' proc' lim' tm' sch' sg']. reflexivity.
Qed.

Definition Ktr : jpredA := fun _ _ tr _ => tr = [].
Lemma stableA_Ktr : ltac2:(tb__ "0|0|
S6S5eS35R1S89A3Fn;").
Proof. intros n rho rho' tp tr md md' _ _ H. exact H. Qed.

Lemma ensure_page : ltac2:(tb__ "0|e|
S5cS9aS5S5S5S18S36S15Q40M0A1M1A1M2S36S4bA1M3Sc5S45S5aS35RaR9R5R4S38G3SbaR3SbbR2R1A2A4A6S18S18G2G2RfR4R2R8R6A4R10R4R2R9R7A4F_;Ft';Ft;Fr';Fr;S0S5SaRaZ1000M4A2Z0M5A3S7Z643000RbA2S7S8RcG4A2ScZ2Z40A2A2S7RdRcA2S7RcS8ReG4A2A2S0S37S4dS14G0RfA2S48R8A1A2S3bA3S5S1S7R11R1A2S9R1S8R11G4A2A2A2S0S37Sb3S46S44RbA1A1R2A2S40A3F_;Fz;S10Sc3RaRdA2S51A2S3S41G1S14G0R12A2ReA3A1S96S22S22S2dS2cR11R1A2S38S5S5R14S8R14G4A2A4A2Lo;S27S97R14A1A1A3F_;S41G1S14G0R13A2RfA3S5S1S7R14R1A2S9R1R13A2A2S0S3dS15Q8M6A1M7A1M8S19R13S14G0R2A2M9A2S3eG7S14G6G5A2A2MaA3F_;Fa;F_;S2S18S18S2G2G2S1S5aS35R18R17R2R1S38G3SbaR11SbbR10RfA2A4A6S1S6S0G1S17R3R1A2S17R14R1A2A3Fi;S1S6S0S36G7A1S1dR3R1A2S1dR14R1A2A3Fl;S1S5S1S7R16R1A2S9R1R15A2A2S0G8S19R4G9A2GaA3F_;Fa;S1G1S3S1S7R17S16G0R1A2MbA2S9GbS8R17G4A2A2A2A1S0G8S19R4R2A2S19R15R2A2A3F_;Fa;S1S3S41G1S14G0R16A2McR12A3MdA1S5S1S7R18R1A2S9R1S8R18G4A2A2A2S0G8S19R5G9A2GaA3F_;Fa;F_;S1GdG1S0G8S19R4R1A2S19R15R1A2A3Fa;F_;S0G2R1S37G2L_;S53GcR12A2R12S39G1GcR12A3X37x2A3A2A2A2A2A2A2A2Ltp';A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fzhi;Fzlo;Fp;FA;FJ;").
Proof.
  intros J A p zlo zhi rho tp tr ms md Hsp HJ Hal Hlo Hhi Hzlo Hzhi Hlz Hacc Hroom Hdisj Hz.
  destruct (page_mem (Z_to_bv 64 p) tp) eqn:PM.
  - apply page_mem_In in PM. exists rho, tp. split; [exact Hsp|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
    split; [exact (Hz PM)|]. split; [intros; reflexivity|]. split; [intros X; exfalso; exact (X PM) |]. split; [intros; reflexivity | reflexivity].
  - apply page_mem_false in PM.
    destruct (SPA_prepay_pages_rm J A p 1%nat rho tp tr ms md Hsp HJ Hal Hlo ltac:(cbn; lia)
                ltac:(intros k Hk; replace k with 0%nat by lia; unfold pageZ; rewrite Z.mul_0_r, Z.add_0_r; exact Hlz)
                ltac:(intros k Hk; replace k with 0%nat by lia; unfold pageZ; rewrite Z.mul_0_r, Z.add_0_r; exact PM)
                ltac:(intros z Hz'; apply Hacc; cbn in Hz'; lia) ltac:(cbn; unfold page_size in *; lia))
      as (rho' & Hsp' & Hrw & Hrl & Hz' & Ho').
    { apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) (Hdisj PM) o Ho) as D. unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *. lia. }
    exists rho', (Z_to_bv 64 p :: tp). cbn [pages_rev app] in Hsp'. unfold pageZ in Hsp'. replace (p + 4096 * Z.of_nat 0) with p in Hsp' by lia.
    split; [exact Hsp'|]. split; [exact Hrw|]. split; [exact Hrl|]. split; [intros a Ha; apply Hz'; lia|]. split; [|split; [|split; [|reflexivity]]].
    + intros a Ha. apply Ho'. lia.
    + intros _ a Ha. apply Hz'. lia.
    + intros X. exfalso. exact (PM X).
Qed.

Section Seg6.

Variables (m : Model) (a1 a2 : word) (B : Z).
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S36S3aS15Q40A1M0G0A2A1S4aS44Vm;A1A1SbcS35A1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|3|
S0S36S3aS15Q40M0A1M1G1A2M2A1S47S44Vm;A1A1S39G2S38G1G1Va2;S14G0Z38e000A2A4S39G2S38G1G1Va1;S14G0Z10000A2A4S39G2S38G1G1S14G0Z2008fff7000A2S14G0Zdfff0001000A2A4S39G2S38G1G1S14G0Z8fff7000A2S14G0Z20000000000A2A4S39G2S38G1G1S14G0Z7fff7000A2S14G0Z10000000A2A4S3cG2A1A3A3A3A3A3A3").
Hypothesis Hna : ltac2:(tb__ "0|3|
S0S36S3aS15Q40M0A1M1G1A2M2A1S46S44Vm;A1A1S39G2S38G1G1S14G0Z8fff7000A2S14G0Z20000000000A2A4S3cG2A1A3A3").
Hypothesis Hlz : ltac2:(tb__ "0|3|
S0S36S3aS15Q40M0A1M1G1A2M2A1S48Vm;A1S3fG2S4fS14G0Z2008fff7000A2S14G0Zdfff0001000A2A2S3fG2S4fS14G0Z8fff7000A2S14G0Z20000000000A2A2S4fS14G0Z7fff7000A2S14G0Z10000000A2A2A3A3A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Ha1 : ltac2:(tb__ "0|2|
S1S7Z643000S16Q40Va1;A2M0A2S1S4S7S8G0Z10000A2M1SaaA2S7Sa9G0A2A2S7G1S49S44Vm;A1A1A2A2A2").
Hypothesis Ha2 : ltac2:(tb__ "0|2|
S1S7Z643000S16Q40Va2;A2M0A2S1S4S7S8G0Z38e000A2M1SaaA2S7Sa9G0A2A2S7G1S49S44Vm;A1A1A2A2A2").
Hypothesis HBlim : ltac2:(tb__ "0|0|
S7S8VB;Z1000000A2S4eS44Vm;A1A1A2").
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S5cS18S36S15Q40A1A1S36S4bA1M0S45R5R4R3R2R1A4S0G0R3S3cS4bA1A3F_;Fmd;Ftr;Ftp;Frho;S5dS35Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S5cS18S36S15Q40A1A1S36S4bA1M0S45R5R4R3R2R1A4S0G0R3S3cS4bA1A3F_;Fmd;Ftr;Ftp;Frho;Sc1S35Vok;R2A3F_;FJ;").
Variables (P b4 b5 b6 : word).
Hypothesis HPL : ltac2:(tb__ "0|0|
S94S14Q40Z0A2Vm;Sa8VP;A4").
Hypothesis HPL4 : ltac2:(tb__ "0|0|
S94S14Q40Z0A2S9fVm;VP;A2Sa0Vb4;A4").
Hypothesis HPL5 : ltac2:(tb__ "0|1|
S94S14Q40M0Z0A2Sa7Vm;VP;Vb4;A3S14G0Z1000A2Vb5;A4").
Hypothesis HPL6 : ltac2:(tb__ "0|1|
S94S14Q40M0Z0A2Sa5Vm;VP;Vb4;Vb5;A4S14G0Z10000A2Vb6;A4").
Variables (b7 b8 b9 : word).
Hypothesis HPL7 : ltac2:(tb__ "0|1|
S94S14Q40M0Z0A2Sa6Vm;VP;Vb4;Vb5;Vb6;A5S14G0Z1000A2Vb7;A4").
Hypothesis HPL8 : ltac2:(tb__ "0|1|
S94S14Q40M0Z0A2S7cVm;VP;Vb4;Vb5;Vb6;Vb7;A6S14G0Z1000A2Vb8;A4").
Hypothesis HPL9 : ltac2:(tb__ "0|1|
S94S14Q40M0Z0A2S79Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;A7S14G0Z1000A2Vb9;A4").

Definition mF : Model := ltac2:(tb__ "0|0|
S7dVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;A8").
Definition BF : Z := B12x B + 4096 + 4096.
Definition vals : valuation -> Prop := ltac2:(tb__ "0|0|
S7eVm;Va1;Va2;VP;Vb4;Vb5;Vb6;A7").
Definition b9lo : Z := bv_unsigned b9.
Local Notation P_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.P_facts m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_range := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.RI_range m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.RI_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation SB_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.SB_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation b4_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b4_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4) (only parsing).
Local Notation b5_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b5_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5) (only parsing).
Local Notation b6_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b6_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5 b6 HPL6) (only parsing).
Local Notation b7_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.b7_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7) (only parsing).
Local Notation b8_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.b8_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7 b8 HPL8) (only parsing).
Local Notation b9_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.b9_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7 b8 HPL8 b9 HPL9) (only parsing).
Local Notation RIw := (RI P) (only parsing).

Lemma OKFx : ltac2:(tb__ "0|0|
S45S5S5dS35Vok;S75R2R1A2A3FBB;Fmm;").
Proof using OKF. clear -OKF. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.
Lemma OKPx : ltac2:(tb__ "0|0|
S45S5Sc1S35Vok;S75R2R1A2A3FBB;Fmm;").
Proof using OKP. clear -OKP. intros. apply OKP. intros; eapply KxA_nil; eassumption. Qed.

Lemma mF_vmmaps : ltac2:(tb__ "0|9|
S1S0S36S3aS15Q40M0A1M1G1A2M2A1M3S4aS44S5fA1M4A1S4aS44Vm;A1M5A1A3S1S0G3S47G4A1S52S39G2S38G1G1Vb9;S14G0Z1000M6A2A4S47S44S79Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;A7A1A1A3Vb9;A2A3S1S0G3S46G4A1S4cS39G2S38G1G1Vb4;Sa0A4S46S44S9fVm;VP;A2M7A1A1A3S64S8S64G6A2M8A3A3S1S0S5S4eG4A1S4eG5A1A3S1S0G1S50G4A1S50G5A1A3S0G3S48S5fA1S4cS3fG2S4fVb4;Sa0A2S48G7A1A3S64G8A3A3A2A2A2A2A2").
Proof.
  clear. pose proof (m14_ledger m P b4 b5 b6 b7 b8 b9) as (L1 & L2 & L3 & L4).
  pose proof (lazy_m12 m P b4 b5 b6 b7) as LZ12. pose proof (noacc_m12 m P b4 b5 b6 b7) as NA12.
  unfold mF, m15, munmap_model, with_mmap_destroyed, munmap_vm.
  rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps, BackingAlgebra.m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps.
  cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_init_sp]. rewrite L1, L2, L3, L4. unfold b9lo. rewrite (u64_of_lit 4096) by lia.
  repeat split; reflexivity.
Qed.
Lemma top_mF : ltac2:(tb__ "0|0|
S0S5S49S44S5fA1A1S49S44Vm;A1A1A3").
Proof. pose proof mF_vmmaps as (_ & _ & _ & _ & L5 & _). unfold alloc_top. rewrite L5. reflexivity. Qed.

Lemma plfacts : ltac2:(tb__ "0|1|
S1S7Z1000M0S64A2S1S0S5SaS64G0A2Z0A3S1Sa4S64G0A2S7S8S64G0A2S49S44Vm;A1A1A2A2A2A2").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. pose proof b9_facts as (K1 & _ & Kband & Ktop & Kal & _). unfold b9lo. repeat split; try assumption; lia.
Qed.

Lemma W8 : ltac2:(tb__ "0|0|
Sb4S46S44S9fVm;VP;A2A1A1A1").
Proof using HPL Hres Htop Hmaps Hna.
  clear Ha1 Ha2 HBlim HPL4 HPL5 HPL6 HPL7 HPL8 HPL9.
  pose proof P_facts as (Pal & Pceil & _). pose proof RI_range as (R1 & R2 & R3). pose proof (alloc_top_lt (m_vmmaps m)) as TL. unfold two_pow_64 in TL.
  rewrite (m8_vmmaps m P). unfold h8, mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite (mP_vmmaps m P). cbn [vm_noaccess]. rewrite Hna.
  apply maps_subtract_wf; [|pose proof (urange (pg)); lia].
  apply ivs_wf_cons; [|apply ivs_wf_cons; [|apply ivs_wf_nil]]; unfold iv_wf, ivB, ivS; cbn [fst snd]; [unfold n7|]; rewrite ?u64_of_lit by lia; lia.
Qed.
Lemma W9 : ltac2:(tb__ "0|1|
Sb4S39S3aS15Q40A1M0G0A2S38G0G0Vb4;Sa0A4S46S44S9fVm;VP;A2A1A1A3A1").
Proof using HPL HPL4 Hres Htop Hmaps Hna.
  clear Ha1 Ha2 HBlim HPL5 HPL6 HPL7 HPL8 HPL9. apply ivs_wf_cons; [|exact W8].
  pose proof b4_facts as (F4lo & _ & F4top & _). pose proof (alloc_top_lt (m_vmmaps m)) as TL. unfold two_pow_64 in TL.
  unfold iv_wf, ivB, ivS, n9. cbn [fst snd]. rewrite u64_of_lit by lia. lia.
Qed.

Lemma high_shadow_lazy_mF : ltac2:(tb__ "0|1|
S15Q40M0A1S7Z2008fff7000S16G0R1A2A2S7S8S16G0R2A2Z1000A2Sa9A2S0S37S4dR3S48S5fA1A2S3bA3F_;F_;Fp;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps Hlz.
  clear Ha1 Ha2 HBlim. intros p Hlo Hhi. pose proof mF_vmmaps as (_ & _ & _ & _ & _ & LZ). rewrite LZ. pose proof plfacts as (K1 & K2 & K3 & K4).
  pose proof b4_facts as (F4lo & F4band & F4top & F4al & _). pose proof (alloc_top_lt (m_vmmaps m)) as TL. unfold two_pow_64 in TL.
  apply page_in_ranges_subtract.
  - intros q Hq. apply in_app_iff in Hq as [Hq|Hq].
    + rewrite (lazy_interior_lit b4 n9 F4al) in Hq by (unfold n9; rewrite u64_of_lit by lia; lia). destruct Hq as [<-|[]].
      unfold iv_wf, ivB, ivS, n9. cbn [fst snd]. rewrite u64_of_lit by lia. lia.
    + revert q Hq. change (ivs_wf (m_vm_lazy (m8 m P))). rewrite (lazy_m8 m P). apply maps_subtract_wf; [|pose proof (urange pg); lia].
      rewrite (lazy_mP m a1 a2 Hres Hmaps Hlz Htop P HPL). pose proof P_facts as (Pal & Pceil & _).
      repeat (apply ivs_wf_cons; [unfold iv_wf, ivB, ivS; cbn [fst snd]; first [unfold n7 | idtac]; rewrite ?u64_of_lit by lia; lia|]). apply ivs_wf_nil.
  - lia.
  - rewrite page_in_ranges_app. apply orb_true_intro. right. apply (high_shadow_lazy_m8 m a1 a2 Hres Hmaps Hlz Htop P HPL); assumption.
  - unfold SHADOW_BAND_HI in Hhi. unfold bandav in K3. unfold page_size. lia.
Qed.

Lemma high_shadow_acc_mF : ltac2:(tb__ "0|0|
S5S1S7Z2008fff7000R1A2S9R1Sa9A2A2S0S37Sb3S46S44S5fA1A1R2A2S40A3F_;Fz;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps Hlz Hna.
  clear Ha1 Ha2 HBlim. intros z Hz. pose proof mF_vmmaps as (_ & _ & NA & _). rewrite NA. pose proof plfacts as (K1 & K2 & K3 & K4).
  pose proof b4_facts as (F4lo & F4band & F4top & F4al & _).
  apply covered_subtract_false; [exact W9 | lia |].
  unfold covered. cbn [existsb]. apply Bool.orb_false_iff. split.
  - unfold in_iv, ivB, ivS, in_rng, n9. cbn [fst snd]. rewrite u64_of_lit by lia. unfold SHADOW_BAND_HI, SHADOW_BAND_LO in *.
    apply andb_false_iff. destruct F4band as [F|F]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
  - apply (shadow_acc_m8 m a1 a2 Hres Hmaps Hna Hlz Htop P HPL). left. exact Hz.
Qed.

Lemma low_shadow_lazy_mF : ltac2:(tb__ "0|1|
S15Q40M0A1S7SaaS16G0R1A2A2S7S8S16G0R2A2Z1000A2SabA2S0S37S4dR3S48S5fA1A2S3bA3F_;F_;Fp;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps Hlz.
  clear Ha1 Ha2 HBlim. intros p Hlo Hhi. pose proof mF_vmmaps as (_ & _ & _ & _ & _ & LZ). rewrite LZ. pose proof plfacts as (K1 & K2 & K3 & K4).
  pose proof b4_facts as (F4lo & F4band & F4top & F4al & _). pose proof (alloc_top_lt (m_vmmaps m)) as TL. unfold two_pow_64 in TL.
  apply page_in_ranges_subtract.
  - intros q Hq. apply in_app_iff in Hq as [Hq|Hq].
    + rewrite (lazy_interior_lit b4 n9 F4al) in Hq by (unfold n9; rewrite u64_of_lit by lia; lia). destruct Hq as [<-|[]].
      unfold iv_wf, ivB, ivS, n9. cbn [fst snd]. rewrite u64_of_lit by lia. lia.
    + revert q Hq. change (ivs_wf (m_vm_lazy (m8 m P))). rewrite (lazy_m8 m P). apply maps_subtract_wf; [|pose proof (urange pg); lia].
      rewrite (lazy_mP m a1 a2 Hres Hmaps Hlz Htop P HPL). pose proof P_facts as (Pal & Pceil & _).
      repeat (apply ivs_wf_cons; [unfold iv_wf, ivB, ivS; cbn [fst snd]; first [unfold n7 | idtac]; rewrite ?u64_of_lit by lia; lia|]). apply ivs_wf_nil.
  - lia.
  - rewrite page_in_ranges_app. apply orb_true_intro. right. apply (low_shadow_lazy_m8 m a1 a2 Hres Hmaps Hlz Htop P HPL); assumption.
  - unfold SHADOW_BAND_LO, SHADOW_RW_LO_END in *. unfold bandav in K3. unfold page_size. lia.
Qed.

Lemma low_shadow_acc_mF : ltac2:(tb__ "0|0|
S5S1S7SaaR1A2S9R1SabA2A2S0S37Sb3S46S44S5fA1A1R2A2S40A3F_;Fz;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps Hlz Hna.
  clear Ha1 Ha2 HBlim. intros z Hz. pose proof mF_vmmaps as (_ & _ & NA & _). rewrite NA. pose proof plfacts as (K1 & K2 & K3 & K4).
  pose proof b4_facts as (F4lo & F4band & F4top & F4al & _).
  apply covered_subtract_false; [exact W9 | lia |].
  unfold covered. cbn [existsb]. apply Bool.orb_false_iff. split.
  - unfold in_iv, ivB, ivS, in_rng, n9. cbn [fst snd]. rewrite u64_of_lit by lia. unfold SHADOW_BAND_HI, SHADOW_BAND_LO, SHADOW_RW_LO_END in *.
    apply andb_false_iff. destruct F4band as [F|F]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
  - apply (shadow_acc_m8 m a1 a2 Hres Hmaps Hna Hlz Htop P HPL). right. exact Hz.
Qed.

Definition x1 (rho : valuation) : Z := bv_unsigned (rw rho 1%positive).

Lemma Upri : ltac2:(tb__ "0|0|
S18S61R1A1S0S5S16Q40Sa1R2A1A2Sa2R2A1A3F_;Frho;").
Proof.
  clear. intros rho (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1). pose proof (urange (spacebeg P)) as USB.
  unfold pRI, shRI_base, priZ. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 19327320064) with 19327320064. apply bv_wrap_small. change (bv_modulus 64) with (2^64). pose proof (urange (rw rho 31%positive)). lia.
Qed.
Lemma priZ_facts : ltac2:(tb__ "0|1|
S18S61R1A1S1S7S8Sa2R2A1M0Z200A2S83S60R2A1A1A2S1S0S5SaG0Z1000A2Z0A3S1S7Z2008fff7000G0A2S41S15Q40A1Sa1R2A1S77R2A1A3A2A2A2F_;Frho;").
Proof using HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim HPL4 HPL5 HPL6 HPL7 HPL8 HPL9. intros rho HV. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV. pose proof SB_val as SB.
  unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB. pose proof (urange P) as UP.
  assert (Htopv : alloc_top (m_vmmaps m) = x1 rho - 0x800000) by (unfold alloc_top, x1; rewrite stack_max_size_val, <- Hv1; reflexivity).
  pose proof (Z.div_mod (bv_unsigned P) 65536 ltac:(lia)) as DP. pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB.
  set (q := bv_unsigned P / 65536) in *. set (r := bv_unsigned P mod 65536) in *.
  assert (HSB : bv_unsigned (spacebeg P) = 65536 * (q + 1)) by (rewrite SB; lia).
  split; [|split; [|split]].
  -
    pose proof (aligned_end_LIM (16 * (q + 1) + 33554432 + 1) (x1 rho) ltac:(lia) ltac:(rewrite Htopv in Pceil; rewrite RV, HSB in R2; lia)) as X.
    unfold priZ. lia.
  - unfold priZ. replace (bv_unsigned (rw rho 31%positive) + 19327320064) with ((2 * (q + 1) + 4718584) * 4096) by lia. apply Z_mod_mult.
  - unfold priZ. lia.
  - unfold TP12. apply in_app_iff. right. unfold TP11. destruct (q1Z rho =? priZ rho); cbn [In]; tauto.
Qed.

Lemma blocks16 : ltac2:(tb__ "0|4|
S18S61R1A1S0S15Q40M0A1M1S17R2P24A2Vb7;A3S0G1S17R3P4dA2Vb8;A3S0G1S17R4P4eA2Vb9;A3S1bS5S41S3aS1bS5A2S38S1bS5R2R1A4S7aA3S4S4S7S8S16G0S20R8R3A2A2M2R2A2M3SaaA2S7Sa9G2A2A2S1S0S1bR3ScaA3S1S0S5R2Z200A3S1S7G3S83S60R8A1A1A2S7Z2008fff7000G2A2A2A2A2A2F_;Fsz;Fe;F_;F_;F_;F_;Frho;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps Ha1 Ha2.
  clear HBlim. intros rho (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1) H36 H77 H78 e sz Hin.
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV. pose proof SB_val as SB.
  pose proof (urange P) as UP. pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB.
  pose proof b5_facts as (_ & _ & F5b & _). pose proof b6_facts as (_ & F6band & _). pose proof b7_facts as (_ & F7band & _).
  pose proof b8_facts as (_ & F8band & _). pose proof plfacts as (_ & _ & F9band & _).
  assert (Htopv : alloc_top (m_vmmaps m) = x1 rho - 0x800000) by (unfold alloc_top, x1; rewrite stack_max_size_val, <- Hv1; reflexivity).
  unfold G14b, G13b, G12b, G11c in Hin. rewrite !in_app_iff in Hin. cbn [In] in Hin.
  destruct Hin as [[[[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]]]|[[= <- <-]|[]]]|[[= <- <-]|[]]]|[[= <- <-]|[]]]; cbn [eval].
  - left. rewrite H27. exact (proj1 (proj2 Ha1)).
  - left. rewrite H28. exact (proj1 (proj2 Ha2)).
  - left. right. unfold ri30. cbn [eval]. rewrite H30. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 137438953472) with (2 ^ 37).
    unfold alloc_ceiling_hi in Phi. rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). unfold SHADOW_BAND_HI in *. lia.
  - right. split; [reflexivity|]. split; [reflexivity|]. change (eval rho shRI_base) with (pRI rho).
    rewrite (Upri rho ltac:(repeat split; assumption)).
    pose proof (priZ_facts rho ltac:(repeat split; assumption)) as (X1 & _ & X3 & _). lia.
  - left. rewrite H33. clear -F5b. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. lia.
  - left. rewrite H34. clear -F6band. unfold bandav in F6band. unfold SHADOW_BAND_LO, SHADOW_BAND_HI. lia.
  - left. rewrite H36. clear -F7band. unfold bandav in F7band. unfold SHADOW_BAND_LO, SHADOW_BAND_HI. lia.
  - left. rewrite H77. clear -F8band. unfold bandav in F8band. unfold SHADOW_BAND_LO, SHADOW_BAND_HI. lia.
  - left. rewrite H78. clear -F9band. unfold bandav, b9lo in F9band. unfold SHADOW_BAND_LO, SHADOW_BAND_HI. lia.
Qed.

Definition rho16 (rho : valuation) : valuation := ltac2:(tb__ "0|2|
Sc0Sc0Vrho;P4fS14Q40M0S84S60Vrho;A1M1A1A2A3P50S14G0S81G1A1A2A3").

Definition enspage (p : word) (tp : list word) : list word := ltac2:(tb__ "0|1|
S37S36S15Q40A1M0A1L_;S53Vp;Vtp;A2Vtp;S39G0Vp;Vtp;A3X37x2").
Definition n16 (x : Z) : nat := ltac2:(tb__ "0|0|
S13SdSeSdS82Vx;A1S7fVx;A1A2Z1000A2Z1A2A1").
Definition TP16 (rho : valuation) : list word := ltac2:(tb__ "0|2|
S60Vrho;A1S5S3fS15Q40M0A1SbeS8S7fR1A1M1Z1000A2S72R1A1A2S68S14G0G1A2S77Vrho;A1A2A3Tx;").
Definition LOWPGw : word := Z_to_bv 64 LOWPG.
Fixpoint enspagesZ (p : Z) (n : nat) (tp : list word) : list word :=
  match n with
  | O => tp
  | S n' => enspagesZ (p + 4096) n' (enspage (Z_to_bv 64 p) tp)
  end.
Definition TP17 (rho : valuation) : list word := enspagesZ LOWPG 5 (TP16 rho).
Lemma paid_enspage_le : ltac2:(tb__ "0|1|
S45S15Q40A1M0S36G0A1S7Sc2R3S68R2R1A2A2S8Sc2R3R1A2S51A2A2Ftp;Fp;Fmd;").
Proof. intros md p tp. unfold enspage. destruct (page_mem p tp); [pose proof page_size_pos; lia | apply paid_cons_le]. Qed.
Lemma In_enspage : ltac2:(tb__ "0|1|
S15Q40A1M0G0S36G0A1S41G0R3R1A3S41G0R4S68R3R2A2A3F_;Ftp;Fp;Fq;").
Proof. intros q p tp H. unfold enspage. destruct (page_mem p tp); [exact H | right; exact H]. Qed.
Lemma In_enspage_inv : ltac2:(tb__ "0|1|
S15Q40A1M0G0S36G0A1S41G0R3S68R2R1A2A3S4S0G0R4R3A3S41G0R4R2A3A2F_;Ftp;Fp;Fq;").
Proof. intros q p tp H. unfold enspage in H. destruct (page_mem p tp); [right; exact H | destruct H as [<-|H]; [left; reflexivity | right; exact H]]. Qed.
Lemma In_enspagesZ_inv : forall n p tp q, In q (enspagesZ p n tp) ->
  (exists k, (k < n)%nat /\ q = Z_to_bv 64 (p + 4096 * Z.of_nat k)) \/ In q tp.
Proof using.
  induction n as [|n IH]; intros p tp q H; cbn [enspagesZ] in H; [right; exact H|].
  destruct (IH _ _ _ H) as [(k & Hk & ->)|H'].
  - left. exists (S k). split; [lia|]. f_equal. lia.
  - apply In_enspage_inv in H' as [->|H']; [left; exists O; split; [lia|]; f_equal; lia | right; exact H'].
Qed.
Lemma In_enspagesZ_tp : forall n p tp q, In q tp -> In q (enspagesZ p n tp).
Proof using.
  induction n as [|n IH]; intros p tp q H; cbn [enspagesZ]; [exact H|]. apply IH. apply In_enspage. exact H.
Qed.
Lemma paid_enspagesZ_le : forall md n p tp, paid md (enspagesZ p n tp) <= paid md tp + page_size * Z.of_nat n.
Proof using.
  intros md n. induction n as [|n IH]; intros p tp; cbn [enspagesZ]; [lia|].
  pose proof (IH (p + 4096) (enspage (Z_to_bv 64 p) tp)). pose proof (paid_enspage_le md (Z_to_bv 64 p) tp). lia.
Qed.
Lemma In_TP17 : forall rho q, In q (TP17 rho) ->
  (exists k, (k < 5)%nat /\ q = Z_to_bv 64 (LOWPG + 4096 * Z.of_nat k) /\ bv_unsigned q = LOWPG + 4096 * Z.of_nat k)
  \/ In q (TP16 rho).
Proof using.
  intros rho q H. unfold TP17 in H. apply In_enspagesZ_inv in H as [(k & Hk & ->)|H]; [left | right; exact H].
  exists k. split; [exact Hk|]. split; [reflexivity|]. apply u64_of_lit. unfold LOWPG. lia.
Qed.

Lemma ensure_pages : forall (J : jpredA) (A : axst) (n : nat) (p zhi : Z) (rho : valuation) (tp : list word) (tr : list event) (ms : machine_state) (md : Model),
  SPA segsA J A rho tp (tr, mkCfg ms md) ->
  (forall r r' t t', J r t tr md -> J r' t' tr md) ->
  p mod 4096 = 0 -> 0x643000 <= p -> p + 4096 * Z.of_nat n <= 2 ^ 64 -> zhi <= p + 4096 * Z.of_nat n ->
  (forall k, (k < n)%nat -> page_in_ranges (Z_to_bv 64 (p + 4096 * Z.of_nat k)) (m_vm_lazy md) = true) ->
  (forall z, p <= z < p + 4096 * Z.of_nat n -> covered (vm_noaccess (m_vmmaps md)) z = false) ->
  headroom md tp >= page_size * Z.of_nat n ->
  (forall k, (k < n)%nat -> ~ In (Z_to_bv 64 (p + 4096 * Z.of_nat k)) tp ->
     Forall (fun o => ranges_disjoint (obj_range rho o) (p + 4096 * Z.of_nat k, p + 4096 * Z.of_nat k + 4096)) (ss_objs (ax_S A))) ->
  (forall k, (k < n)%nat -> In (Z_to_bv 64 (p + 4096 * Z.of_nat k)) tp ->
     forall a, p + 4096 * Z.of_nat k <= a < p + 4096 * Z.of_nat k + 4096 -> a < zhi -> rm rho (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
  exists rho', SPA segsA J A rho' (enspagesZ p n tp) (tr, mkCfg ms md) /\
    (forall i, rw rho' i = rw rho i) /\ (forall l, rl rho' l = rl rho l) /\
    (forall a, p <= a < zhi -> rm rho' (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) /\
    (forall a, ~ (p <= bv_unsigned a < p + 4096 * Z.of_nat n) -> rm rho' a = rm rho a) /\
    (forall k, (k < n)%nat -> ~ In (Z_to_bv 64 (p + 4096 * Z.of_nat k)) tp ->
       forall a, p + 4096 * Z.of_nat k <= a < p + 4096 * Z.of_nat k + 4096 -> rm rho' (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) /\
    (forall k, (k < n)%nat -> In (Z_to_bv 64 (p + 4096 * Z.of_nat k)) tp ->
       forall a, p + 4096 * Z.of_nat k <= bv_unsigned a < p + 4096 * Z.of_nat k + 4096 -> rm rho' a = rm rho a).
Proof using.
  intros J A n. induction n as [|n IH]; intros p zhi rho tp tr ms md Hsp HJ Hal Hlo Hhi Hzhi Hlzk Hacc Hroom Hdisj Hz.
  - exists rho. cbn [enspagesZ]. split; [exact Hsp|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
    split; [intros a Ha; exfalso; lia|]. split; [intros; reflexivity|]. split; intros k Hk; exfalso; lia.
  - assert (E0 : p + 4096 * Z.of_nat 0 = p) by lia.
    destruct (ensure_page J A p p (Z.min zhi (p + 4096)) rho tp tr ms md Hsp HJ Hal Hlo ltac:(lia) ltac:(lia) ltac:(lia))
      as (rho1 & tp1 & H1 & Hrw1 & Hrl1 & Hz1 & Ho1 & Hf1 & Hs1 & Etp1).
    { pose proof (Hlzk O ltac:(lia)) as X. rewrite E0 in X. exact X. }
    { intros z Hz'. apply Hacc. lia. }
    { unfold page_size in *. lia. }
    { intros Hn. pose proof (Hdisj O ltac:(lia)) as X. rewrite E0 in X. exact (X Hn). }
    { intros Hin a Ha. pose proof (Hz O ltac:(lia)) as X. rewrite E0 in X. apply (X Hin); lia. }
    assert (Etp : tp1 = enspage (Z_to_bv 64 p) tp) by (rewrite Etp1; reflexivity).
    assert (Hrng : forall o, obj_range rho1 o = obj_range rho o).
    { intros o. unfold obj_range, obj_lo_of, obj_hi_of, soff. rewrite !(eval_ext_rwrl rho rho1) by assumption. reflexivity. }
    assert (ES : forall k, p + 4096 + 4096 * Z.of_nat k = p + 4096 * Z.of_nat (S k)) by (intros k; lia).
    assert (NEQ : forall k, (k < n)%nat -> Z_to_bv 64 (p + 4096 * Z.of_nat (S k)) <> Z_to_bv 64 p).
    { intros k Hk E. apply (f_equal bv_unsigned) in E. rewrite !u64_of_lit in E by lia. lia. }
    destruct (IH (p + 4096) zhi rho1 tp1 tr ms md H1 HJ) as (rho2 & H2 & Hrw2 & Hrl2 & Hz2 & Ho2 & Hf2 & Hs2).
    { replace (p + 4096) with (p + 1 * 4096) by lia. rewrite Z_mod_plus_full. exact Hal. }
    { lia. } { lia. } { lia. }
    { intros k Hk. rewrite ES. apply Hlzk. lia. }
    { intros z Hz'. apply Hacc. lia. }
    { rewrite Etp. unfold headroom in *. pose proof (paid_enspage_le md (Z_to_bv 64 p) tp). unfold page_size in *. lia. }
    { intros k Hk Hn. rewrite ES. rewrite ES in Hn. rewrite Etp in Hn.
      assert (Hn0 : ~ In (Z_to_bv 64 (p + 4096 * Z.of_nat (S k))) tp) by (intros X; apply Hn; apply In_enspage; exact X).
      pose proof (Hdisj (S k) ltac:(lia) Hn0) as X. apply Forall_forall. intros o Ho. cbv beta. rewrite (Hrng o). exact (proj1 (Forall_forall _ _) X o Ho). }
    { intros k Hk Hin a Ha Hza. rewrite ES in Hin, Ha. rewrite Etp in Hin.
      apply In_enspage_inv in Hin as [E|Hin]; [exfalso; exact (NEQ k Hk E)|].
      rewrite (Ho1 (Z_to_bv 64 a)) by (rewrite u64_of_lit by lia; lia). exact (Hz (S k) ltac:(lia) Hin a Ha Hza). }
    exists rho2. rewrite Etp in H2. cbn [enspagesZ]. split; [exact H2|].
    split; [intros i; rewrite Hrw2; apply Hrw1|]. split; [intros l; rewrite Hrl2; apply Hrl1|].
    split.
    { intros a Ha. destruct (Z_lt_dec a (p + 4096)) as [L|L].
      - rewrite (Ho2 (Z_to_bv 64 a)) by (rewrite u64_of_lit by lia; lia). apply Hz1. lia.
      - apply Hz2. lia. }
    split.
    { intros a Ha. rewrite Ho2 by lia. apply Ho1. lia. }
    split.
    { intros k Hk Hn a Ha. destruct k as [|k].
      - rewrite E0 in Hn, Ha. rewrite (Ho2 (Z_to_bv 64 a)) by (rewrite u64_of_lit by lia; lia). apply Hf1; [exact Hn | lia].
      - rewrite <- ES in Hn, Ha. apply (Hf2 k ltac:(lia)); [|exact Ha]. rewrite ES, Etp. intros X.
        apply In_enspage_inv in X as [E|X]; [exact (NEQ k ltac:(lia) E) | exact (Hn ltac:(rewrite ES; exact X))]. }
    { intros k Hk Hin a Ha. destruct k as [|k].
      - rewrite E0 in Hin, Ha. rewrite Ho2 by lia. apply Hs1. exact Hin.
      - rewrite <- ES in Hin, Ha. rewrite (Hs2 k ltac:(lia)); [| rewrite Etp; apply In_enspage; exact Hin | exact Ha].
        apply Ho1. lia. }
Qed.
Definition B16 : Z := BF + 4096 * 224.
Definition B16L : Z := B16 + 4096 * 5.

Lemma n16_val : ltac2:(tb__ "0|2|
S5S1S7Z7fff80000000R1A2S7R1ScZ2Z2fA2A2A2S0S5SaR2Z10A2Z0A3S1S0S5S8S8S7fR3A1Z1000M0A2SbG0S11S72R3A1A1M1A2A2S82R3A1A3S7G1ZdfA2A2F_;F_;Fx;").
Proof.
  intros x Hx H16. destruct (site_arith x Hx H16) as (_ & _ & _ & (n & Hn & En) & _). unfold n16. rewrite En.
  replace (HPz x + 4096 + 4096 * n - HPz x) with ((n + 1) * 4096) by lia. rewrite Z_div_mult by lia. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma R16pre_facts1 : ltac2:(tb__ "0|3|
S1S0S37S42S1aS21S28P1M0Z4A2A1S1eS97S8dA1A1M1A3S3bA3S1S0S37S42S1aS21S25S1fZ7fff80000000A1S23G0A1M2A2A1G1A3S3bA3S0S37S42S1aS21S25G2S1fZ7fffffffff20A1A2A1G1A3S3bA3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma R16pre_facts35 : ltac2:(tb__ "0|2|
S1S0S37S42S1aS21S29S24Sc8S23P23A1M0S1fZ3A1A3S23P22A1A2A1S1eS97S8dA1A1M1A3S3bA3S0S37S42S1aS21S25G0S1fSdScZ2Z3dA2Z1A2A1A2A1G1A3S3bA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma v35_val16 : ltac2:(tb__ "0|3|
S18S15Q40M0A1M1S96S1aS1cR2A1S1eS97S8dA1A1A3S0G1S17R3P22A2R2A3S1S0S5SbZ8S16G0S17R4P23A2A2M2A2S16G0R3A2A3S7G2SdScZ2Z3dA2Z1A2A2A2F_;F_;Fb;Frho;").
Proof.
  clear. intros rho b HF H34. destruct R16pre_facts35 as [X1 X2].
  pose proof (fact_of_state _ _ rho X1 HF) as E1. pose proof (fact_of_state _ _ rho X2 HF) as E2.
  cbn [holds eval] in E2. rewrite Z_to_bv_unsigned in E2. change (bv_wrap 64 (2 ^ 61 - 1)) with (2 ^ 61 - 1) in E2.
  cbn [holds] in E1.
  apply (f_equal bv_unsigned) in E1. change (bv_unsigned (eval rho (SAlu ALU_SLL (SVar 35%positive) (SLit 3)))) with (SymSoundV.U rho (g8 35%positive)) in E1.
  rewrite (StepA.U_g8 rho 35%positive) in E1 by (unfold SymSoundV.U; cbn [eval]; exact E2).
  unfold SymSoundV.U in E1. cbn [eval] in E1. rewrite H34 in E1. split; [exact E1 | exact E2].
Qed.

Lemma clear16 : ltac2:(tb__ "0|1|
S5S41S5R1S8cA3S1S0S37Sb7S7aS92R2A1M0A2S3bA3S0S37S34S2bS31G0A1S32G0A1S2fG0A1S2eG0A1S33G0A1S3fS22S27G0A1S39S22S90S3cS22A1A3A3S1eG0A1P51S30G0A1A9A1S3bA3A2F_;Ft;").
Proof. clear. intros t Ht. destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; split; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma x1_facts : ltac2:(tb__ "0|1|
S18S96S1aS1cR1A1S1eS97S8dA1A1A3S1S1S7Z7fff80000000S60R2A1M0A2S7G0ScZ2Z2fA2A2A2S0S5SaG0Z10A2Z0A3A2F_;Frho;").
Proof.
  clear. intros rho HF. destruct R16pre_facts1 as (X1 & X2 & X3).
  pose proof (fact_of_state _ _ rho X1 HF) as A1. pose proof (fact_of_state _ _ rho X2 HF) as A2. pose proof (fact_of_state _ _ rho X3 HF) as A3.
  cbn [holds eval] in A1, A2, A3. rewrite Z_to_bv_unsigned in A2, A3.
  change (bv_wrap 64 0x7fff80000000) with 0x7fff80000000 in A2. change (bv_wrap 64 0x7fffffffff20) with 0x7fffffffff20 in A3.
  destruct A1 as [_ A1]. change (2 ^ 4) with 16 in A1. unfold x1. repeat split; try assumption. lia.
Qed.

Lemma U_add_slit : ltac2:(tb__ "0|4|
S18S6S5S1S7S12ScZ2M0Z3fA2M1A1R1A2S9R1G1A2A2S1S7Z0S8S16Q40M2S17R4R3A2A2R2A2M3A2S9G3ScG0Z40A2A2A2S0S5S16G2S20R5S24Sc6S23R4A1S1fR3A1A3A2A2S8S16G2S17R5R4A2A2R3A2A3F_;F_;Fc;Fv;Frho;").
Proof.
  clear. intros rho v c Hc Hr. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (urange (rw rho v)) as U.
  destruct (Z.lt_ge_cases c 0).
  - replace (c mod 2 ^ 64) with (c + 2 ^ 64) by (rewrite <- (Z_mod_plus_full c 1 (2 ^ 64)); symmetry; apply Z.mod_small; lia).
    replace (bv_unsigned (rw rho v) + (c + 2 ^ 64)) with ((bv_unsigned (rw rho v) + c) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite (Z.mod_small c) by lia. apply Z.mod_small. lia.
Qed.

Lemma U_and_4095 : ltac2:(tb__ "0|1|
S18S1bS0S5S16Q40M0S20R2S24Sc7R1S1fZfffA1A3A2A2SaS16G0S20R2R1A2A2Z1000A2A3Fe;Frho;").
Proof.
  clear. intros rho e. cbn [eval]. rewrite and_val. rewrite u64_of_lit by lia. change 4095 with (Z.ones 12). rewrite Z.land_ones by (pose proof (bv_unsigned_in_range 64 (eval rho e)); lia). reflexivity.
Qed.

Lemma U_zext8 : ltac2:(tb__ "0|1|
S15Q40M0A1S0S5S16G0S2aS40Q8R1A3A2SaS16G0R1A2Z100A2A3Fv;").
Proof.
  clear. intros v. unfold ext_low, zext. rewrite bv_zero_extend_unsigned', bv_extract_unsigned. unfold bv_wrap.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. change (bv_modulus 8) with 256.
  apply Z.mod_small. change (bv_modulus 64) with (2 ^ 64). pose proof (Z.mod_pos_bound (bv_unsigned v) 256 ltac:(lia)). lia.
Qed.

Lemma sbZ_facts' : ltac2:(tb__ "0|1|
S18S61R1A1S0S5SbZ8S16Q40M0S17R2P23A2A2A2S16G0Vb6;A2A3S7S8Sa3R3A1Z2000A2S83S60R3A1A1A2F_;F_;Frho;").
Proof using HPL HPL4 HPL5 HPL6 Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim HPL7 HPL8 HPL9. intros rho HV V1. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  pose proof b6_facts as (F6lo & F6band & F6top & F6al & _).
  assert (Htopv : alloc_top (m_vmmaps m) = x1 rho - 0x800000) by (unfold alloc_top, x1; rewrite stack_max_size_val, <- Hv1; reflexivity).
  apply Z.mod_divide in F6al as [j Hj]; [|lia].
  pose proof (aligned_end_LIM (j + 16) (x1 rho) ltac:(lia) ltac:(lia)) as X. unfold sbZ. lia.
Qed.
Lemma sbZ_facts : ltac2:(tb__ "0|0|
S18S61R1A1S96S1aS1cR2A1S1eS97S8dA1A1A3S7S8Sa3R3A1Z2000A2S83S60R3A1A1A2F_;F_;Frho;").
Proof using HPL HPL4 HPL5 HPL6 Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim HPL7 HPL8 HPL9. intros rho HV HF. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  destruct (v35_val16 rho b6 HF H34) as [V1 V2]. exact (sbZ_facts' rho HV V1).
Qed.

Lemma ZK16 : ltac2:(tb__ "0|5|
S18S5S5S5S61R4A1S96S1aS1cR5A1S1eS97S8dA1A1A3S78R6A1S9eR7A1S41S15Q40M0A1S14G0R7A2S77R8A1A3S7Z0M1R8A2S7S8R9Z1000M2A2ScZ2Z40A2A2S0S5SaRaG2A2G1A3S7RbRaA2S7RaS8RcG2A2A2S7S83S60ReA1A1RcA2S5S1S7ReR1A2S9R1RdA2A2S0S3dS15Q8M3A1M4A1S19R11S14G0R2A2A2S3eG4S14G3G1A2A2A3F_;Fa;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fzhi;Fzlo;Fq;Frho;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps Ha1 Ha2.
  clear HBlim. intros rho q zlo zhi HV HF Hz HZ11 Hin Hq0 Hq64 Hqal Hzlo Hzhi Hlim a Ha.
  pose proof (priZ_facts rho HV) as (PR1 & PR2 & PR3 & PR4). pose proof (sbZ_facts rho HV HF) as SB1.
  unfold TP12 in Hin. apply in_app_iff in Hin as [Hin|Hin].
  -
    apply Hz. destruct (x1_facts rho HF) as [Hx H16].
    apply In_pages_rev in Hin as (k & Hk & Ek). apply (f_equal bv_unsigned) in Ek. unfold pageZ in Ek.
    assert (Hsh : shZ rho <= 0x10007fff8000).
    { unfold shZ. pose proof (Z.div_le_mono (bv_unsigned (rw rho 1%positive)) 0x800000000000 8 ltac:(lia) ltac:(unfold x1 in Hx; lia)). change (0x800000000000 / 8) with 17592186044416 in H. lia. }
    assert (Hsh0 : 0x7fff8000 + 0xFFFF0000000 <= shZ rho).
    { unfold shZ. pose proof (Z.div_le_mono 0x7fff80000000 (bv_unsigned (rw rho 1%positive)) 8 ltac:(lia) ltac:(unfold x1 in Hx; lia)). change (0x7fff80000000 / 8) with 0xFFFF0000000 in H. lia. }
    pose proof (Z.mod_pos_bound (shZ rho - 131072) 4096 ltac:(lia)) as Qm. pose proof (Z.mod_pos_bound (shZ rho - 9) 4096 ltac:(lia)) as Em.
    assert (Hq : q12 rho <= shZ rho - 131072 < q12 rho + 4096) by (unfold q12; lia).
    assert (He : e12 rho <= shZ rho - 9 < e12 rho + 4096) by (unfold e12; lia).
    assert (Hqal' : q12 rho mod 4096 = 0) by (unfold q12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
    assert (Heal : e12 rho mod 4096 = 0) by (unfold e12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
    apply Z.mod_divide in Hqal' as [tq Htq]; [|lia]. apply Z.mod_divide in Heal as [te Hte]; [|lia].
    assert (Hn : Z.of_nat (n12 rho) = te - tq + 1).
    { unfold n12. rewrite Htq, Hte. replace (te * 4096 - tq * 4096) with ((te - tq) * 4096) by lia. rewrite Z_div_mult by lia. rewrite Z2Nat.id; lia. }
    pose proof (proj1 (Nat2Z.inj_lt _ _) Hk) as HkZ. rewrite Hn in HkZ. rewrite Htq in *. rewrite !u64_of_lit in Ek by lia. lia.
  -
    apply (HZ11 a (Z_to_bv 64 q) Hin); [rewrite u64_of_lit by lia; lia | lia | lia | lia].
Qed.

Lemma ss_zero_range : ltac2:(tb__ "0|2|
S18S78R1A1S60R2A1S5S1S7Z7fff80000000R1A2S7R1ScZ2Z2fA2A2A2S5S1S7S82R3A1R1A2S9R1S8S87R3A1Z1000A2A2A2S0S3dS15Q8M0A1M1A1S19R6S14Q40R2A2A2S3eG1S14G0Z0A2A2A3F_;Fa;F_;Tx;F_;Frho;").
Proof.
  clear. intros rho Hz x Hx a Ha. apply Hz.
  assert (Eq : q12 rho = q12x x) by reflexivity. assert (Ee : e12 rho = e12x x) by reflexivity.
  assert (Hsh : shx x <= 0x10007fff8000).
  { unfold shx. pose proof (Z.div_le_mono x 0x800000000000 8 ltac:(lia) ltac:(lia)). change (0x800000000000 / 8) with 17592186044416 in H. lia. }
  assert (Hsh0 : 0x7fff8000 + 0xFFFF0000000 <= shx x).
  { unfold shx. pose proof (Z.div_le_mono 0x7fff80000000 x 8 ltac:(lia) ltac:(lia)). change (0x7fff80000000 / 8) with 0xFFFF0000000 in H. lia. }
  pose proof (Z.mod_pos_bound (shx x - 131072) 4096 ltac:(lia)) as Qm. pose proof (Z.mod_pos_bound (shx x - 9) 4096 ltac:(lia)) as Em.
  assert (Hq : q12x x <= shx x - 131072 < q12x x + 4096) by (unfold q12x; cbv zeta; lia).
  assert (He : e12x x <= shx x - 9 < e12x x + 4096) by (unfold e12x; cbv zeta; lia).
  assert (Hqal' : q12x x mod 4096 = 0) by (unfold q12x; cbv zeta; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  assert (Heal : e12x x mod 4096 = 0) by (unfold e12x; cbv zeta; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  apply Z.mod_divide in Hqal' as [tq Htq]; [|lia]. apply Z.mod_divide in Heal as [te Hte]; [|lia].
  assert (Hn : Z.of_nat (n12 rho) = te - tq + 1).
  { unfold n12. rewrite Eq, Ee, Htq, Hte. replace (te * 4096 - tq * 4096) with ((te - tq) * 4096) by lia. rewrite Z_div_mult by lia. rewrite Z2Nat.id; lia. }
  rewrite Eq, Hn. lia.
Qed.

Lemma TP12_split : ltac2:(tb__ "0|3|
S18S61R1A1S0S5SbZ8S16Q40M0S17R2P23A2A2A2S16G0Vb6;A2A3S60R3A1S5S1S7Z7fff80000000R1A2S7R1ScZ2Z2fA2A2A2S0S5SaR2Z10A2Z0A3S15G0A1M1S41G1R1S77R7A1A3S4S7S16G0R2A2M2S7fR5A1A2S7S82R5A1G2A2A2F_;Fp;F_;F_;Tx;F_;F_;Frho;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps Ha1 Ha2.
  clear HBlim. intros rho HV V35 x Hx H16 p Hp.
  pose proof (class_arith x Hx H16) as CA. cbv zeta in CA.
  destruct CA as (Ct & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CHPal & _ & _ & _ & _ & CPEHP & CHPlo & CPEhi & _ & CHPq & _ & CLIM & _).
  pose proof (priZ_facts rho HV) as (PR1 & PR2 & PR3 & PR4). fold x in PR1. pose proof (sbZ_facts' rho HV V35) as SB1. fold x in SB1.
  pose proof (Upri rho HV) as UP.
  unfold TP12 in Hp. apply in_app_iff in Hp as [Hp|Hp].
  - right. apply In_pages_rev in Hp as (k & Hk & ->). unfold pageZ. change (q12 rho) with (q12x x).
    assert (Hsh : shx x <= 0x10007fff8000).
    { unfold shx. pose proof (Z.div_le_mono x 0x800000000000 8 ltac:(lia) ltac:(lia)). change (0x800000000000 / 8) with 17592186044416 in H. lia. }
    assert (Hsh0 : 0x7fff8000 + 0xFFFF0000000 <= shx x).
    { unfold shx. pose proof (Z.div_le_mono 0x7fff80000000 x 8 ltac:(lia) ltac:(lia)). change (0x7fff80000000 / 8) with 0xFFFF0000000 in H. lia. }
    pose proof (Z.mod_pos_bound (shx x - 131072) 4096 ltac:(lia)) as Qm. pose proof (Z.mod_pos_bound (shx x - 9) 4096 ltac:(lia)) as Em.
    assert (Hq : q12x x <= shx x - 131072 < q12x x + 4096) by (unfold q12x; cbv zeta; lia).
    assert (He : e12x x <= shx x - 9 < e12x x + 4096) by (unfold e12x; cbv zeta; lia).
    assert (Hqal' : q12x x mod 4096 = 0) by (unfold q12x; cbv zeta; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
    assert (Heal : e12x x mod 4096 = 0) by (unfold e12x; cbv zeta; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
    apply Z.mod_divide in Hqal' as [tq Htq]; [|lia]. apply Z.mod_divide in Heal as [te Hte]; [|lia].
    assert (Hn : Z.of_nat (n12 rho) = te - tq + 1).
    { unfold n12. change (e12 rho) with (e12x x). change (q12 rho) with (q12x x). rewrite Htq, Hte. replace (te * 4096 - tq * 4096) with ((te - tq) * 4096) by lia. rewrite Z_div_mult by lia. rewrite Z2Nat.id; lia. }
    pose proof (proj1 (Nat2Z.inj_lt _ _) Hk) as HkZ. rewrite Hn in HkZ. rewrite u64_of_lit by lia. lia.
  - left.
    assert (SB0 : 0x7fff8000 <= sbZ rho) by (unfold sbZ; pose proof (urange (rw rho 35%positive)); lia).
    pose proof (Z.mod_pos_bound (sbZ rho) 4096 ltac:(lia)) as MQ.
    assert (QB : q1Z rho <= sbZ rho < q1Z rho + 4096) by (unfold q1Z; lia).
    assert (QAL : q1Z rho mod 4096 = 0).
    { unfold q1Z. pose proof (Z.div_mod (sbZ rho) 4096 ltac:(lia)) as D. replace (sbZ rho - sbZ rho mod 4096) with ((sbZ rho / 4096) * 4096) by lia. apply Z_mod_mult. }
    clear MQ.
    apply Z.mod_divide in PR2 as [kp Hkp]; [|lia]. apply Z.mod_divide in CHPal as [kh Hkh]; [|lia]. apply Z.mod_divide in QAL as [kq Hkq]; [|lia].
    assert (KP : kp <= kh) by lia.
    assert (KQ : kq + 2 <= kh) by lia.
    unfold TP11 in Hp. destruct (Z.eqb_spec (q1Z rho) (priZ rho)) as [EQ|NE].
    + assert (KPQ : kp = kq) by lia.
      destruct Hp as [<-|[<-|[<-|[]]]]; [rewrite u64_of_lit by lia; lia | rewrite u64_of_lit by lia; lia | rewrite UP; lia].
    + destruct Hp as [<-|[<-|[<-|[<-|[]]]]]; [rewrite u64_of_lit by lia; lia | rewrite u64_of_lit by lia; lia | rewrite u64_of_lit by lia; lia | rewrite UP; lia].
Qed.

Lemma LZ_of_Z11 : forall rho, vals rho -> 8 * bv_unsigned (rw rho 35%positive) = bv_unsigned b6 -> Z11 rho ->
  let x := x1 rho in 140735340871680 <= x <= 2 ^ 47 -> x mod 16 = 0 ->
  forall q a, In q (TP12 rho) -> bv_unsigned q <= a < bv_unsigned q + 4096 -> LOWPG <= a < LOWPG + 0x4600 ->
  rm rho (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps Ha1 Ha2.
  clear HBlim. intros rho HV V35 HZ11. cbv zeta. intros Hx H16 q a Hin12 Hqa Ha. set (x := x1 rho).
  pose proof (class_arith x Hx H16) as CA. cbv zeta in CA.
  destruct CA as (Ct & C79al & C80x8 & C80al & C80nn & C79lo & C79hi & Ctop1 & Ctop2 & Ctopal & Ctoplo & Cand & CHPal & CPEal & CPBal & CPB & CLEN & CPEHP & CHPlo & CPEhi & CPEe & CHPq & Ce12al & CLIM & CLIM0).
  pose proof (priZ_facts rho HV) as (PR1 & PR2 & PR3 & PR4). pose proof (sbZ_facts' rho HV V35) as SB1.
  pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  pose proof b6_facts as (F6lo & _).
  unfold LOWPG in Ha.
  unfold TP12 in Hin12. apply in_app_iff in Hin12 as [Hst|H11].
  { exfalso. apply In_pages_rev in Hst as (k & Hk & ->). unfold pageZ in Hqa.
    assert (Hsh0 : 0x7fff8000 + 0xFFFF0000000 <= shZ rho).
    { unfold shZ. fold (x1 rho). fold x. pose proof (Z.div_le_mono 0x7fff80000000 x 8 ltac:(lia) ltac:(lia)). change (0x7fff80000000 / 8) with 0xFFFF0000000 in H. lia. }
    assert (Hsh : shZ rho <= 0x10007fff8000).
    { unfold shZ. fold (x1 rho). fold x. pose proof (Z.div_le_mono x 0x800000000000 8 ltac:(lia) ltac:(lia)). change (0x800000000000 / 8) with 17592186044416 in H. lia. }
    pose proof (Z.mod_pos_bound (shZ rho - 131072) 4096 ltac:(lia)) as Qm. pose proof (Z.mod_pos_bound (shZ rho - 9) 4096 ltac:(lia)) as Em.
    assert (Hq : q12 rho <= shZ rho - 131072 < q12 rho + 4096) by (unfold q12; lia).
    assert (He : e12 rho <= shZ rho - 9 < e12 rho + 4096) by (unfold e12; lia).
    assert (Hqal' : q12 rho mod 4096 = 0) by (unfold q12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
    assert (Heal : e12 rho mod 4096 = 0) by (unfold e12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
    apply Z.mod_divide in Hqal' as [tq Htq]; [|lia]. apply Z.mod_divide in Heal as [te Hte]; [|lia].
    assert (Hn : Z.of_nat (n12 rho) = te - tq + 1).
    { unfold n12. rewrite Htq, Hte. replace (te * 4096 - tq * 4096) with ((te - tq) * 4096) by lia. rewrite Z_div_mult by lia. rewrite Z2Nat.id; lia. }
    pose proof (proj1 (Nat2Z.inj_lt _ _) Hk) as HkZ. rewrite Hn in HkZ. rewrite Htq in *. rewrite !u64_of_lit in Hqa by lia. lia. }
  apply (HZ11 a q H11); [lia | lia | lia |]. unfold sbZ. lia.
Qed.

Lemma prep16 : forall (rho : valuation) (w : world), vals rho -> rw rho 36%positive = b7 -> rw rho 77%positive = b8 -> rw rho 78%positive = b9 ->
  stackshadow_zero rho -> Z11 rho -> SPA segsA (KxA mF BF) R16pre rho (TP12 rho) w ->
  let x := x1 rho in let t := tcls x in
  exists rho' : valuation,
    (forall i, (i < 79)%positive -> rw rho' i = rw rho i) /\
    rw rho' 79%positive = Z_to_bv 64 (v79Z x) /\
    rw rho' 80%positive = Z_to_bv 64 (v80Z x) /\
    (forall l, rl rho' l = rl rho l) /\
    (forall a : word, ~ (HPz x <= bv_unsigned a < q12x x) -> ~ (LOWPG <= bv_unsigned a < LOWPG + 0x5000) -> rm rho' a = rm rho a) /\
    (forall a, HPz x + 512 * t <= a < PEz x + 512 * t -> rm rho' (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) /\
    (forall a, HPz x <= a < HPz x + 512 * t ->
       (In (Z_to_bv 64 (HPz x)) (TP12 rho) -> rm rho' (Z_to_bv 64 a) = rm rho (Z_to_bv 64 a)) /\
       (~ In (Z_to_bv 64 (HPz x)) (TP12 rho) -> rm rho' (Z_to_bv 64 a) = Some (Z_to_bv 8 0))) /\
    (forall k, (k < 5)%nat -> ~ In (Z_to_bv 64 (LOWPG + 4096 * Z.of_nat k)) (TP16 rho) ->
       forall a, LOWPG + 4096 * Z.of_nat k <= a < LOWPG + 4096 * Z.of_nat k + 4096 -> rm rho' (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) /\
    (forall k, (k < 5)%nat -> In (Z_to_bv 64 (LOWPG + 4096 * Z.of_nat k)) (TP16 rho) ->
       forall a : word, LOWPG + 4096 * Z.of_nat k <= bv_unsigned a < LOWPG + 4096 * Z.of_nat k + 4096 -> rm rho' a = rm rho a) /\
    8 * bv_unsigned (rw rho 35%positive) = bv_unsigned b6 /\
    SPA segsA (KxA mF B16L) (R16c t) rho' (TP17 rho) w.
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hlz Hmaps Hna Hres Htop.
  intros rho [tr [ms md]] HV H36 H77 H78 Hz HZ11 Hsp x t.
  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF. cbn [ax_S] in HF.
  destruct (x1_facts rho HF) as [Hx H16].
  pose proof (class_arith x Hx H16) as CA. cbv zeta in CA.
  destruct CA as (Ct & C79al & C80x8 & C80al & C80nn & C79lo & C79hi & Ctop1 & Ctop2 & Ctopal & Ctoplo & Cand & CHPal & CPEal & CPBal & CPB & CLEN & CPEHP & CHPlo & CPEhi & CPEe & CHPq & Ce12al & CLIM & CLIM0).
  fold t in Ct, C79lo, C79hi, Ctop2, CPB, CLEN, CLIM.
  destruct (site_arith x Hx H16) as (SQal & SQlo & SQhi & _ & SQPE & SEND & SE12). fold t in SEND.
  destruct (n16_val x Hx H16) as [N16 N16b].
  assert (PEND : PEz x + 512 * t <= 0x10007fff8000).
  { destruct (Z.eq_dec t 0) as [E0|NE0]; [rewrite E0; lia | destruct (class_arith_B x Hx H16 NE0) as [K1 K2]; fold t in K2; lia]. }
  assert (V35 : 8 * bv_unsigned (rw rho 35%positive) = bv_unsigned b6).
  { destruct HV as (_ & _ & _ & _ & _ & _ & _ & H34 & _). exact (proj1 (v35_val16 rho b6 HF H34)). }
  pose proof Hsp as [Hsm (Htr & Hem & Hpaid)]. cbn [w_tr w_cfg cfg_model fst snd] in Htr, Hem, Hpaid. subst tr.
  pose proof (erase_mat_eq_fields md mF Hem) as (Evm & Elz & _).
  pose proof R16pre_at as (Rpc & Rnx & Ra0 & RX & Rb & Rlen).
  set (V79 := v79Z x) in *. set (V80 := v80Z x) in *.
  assert (R79 : 0 <= V79 < 2 ^ 64) by (unfold c1 in C79hi; lia).
  assert (R80 : 0 <= V80 < 2 ^ 64) by lia.
  set (rho2 := rho_set_rw (rho_set_rw rho 79%positive (Z_to_bv 64 V79)) 80%positive (Z_to_bv 64 V80)).
  assert (E79 : rw rho2 79%positive = Z_to_bv 64 V79) by (unfold rho2; rewrite rho_set_rw_other by lia; apply rho_set_rw_at).
  assert (E80 : rw rho2 80%positive = Z_to_bv 64 V80) by (unfold rho2; apply rho_set_rw_at).
  assert (Elow : forall i, (i < 79)%positive -> rw rho2 i = rw rho i) by (intros i Hi; unfold rho2; rewrite !rho_set_rw_other by lia; reflexivity).
  assert (U79 : bv_unsigned (rw rho2 79%positive) = V79) by (rewrite E79; apply u64_of_lit; lia).
  assert (U80 : bv_unsigned (rw rho2 80%positive) = V80) by (rewrite E80; apply u64_of_lit; lia).
  assert (U1 : bv_unsigned (rw rho2 1%positive) = x) by (rewrite Elow by lia; reflexivity).
  assert (Hag : agree_below 79 rho rho2).
  { unfold rho2. eapply agree_below_trans; [apply (agree_below_set_rw _ 79%positive); lia | apply (agree_below_set_rw _ 80%positive); lia]. }
  assert (Htin : In t classes16) by (unfold classes16; cbn [In]; lia).
  destruct (sd16 t Htin) as (SD & SWFr & SWFm & SWFc & N21 & SB21 & OBJc & NXm & LENm).

  assert (H1 : SPA segsA (KxA mF BF) (mkAX (R16r t) [] (SLit SHB)) rho2 (TP12 rho) ([], mkCfg ms md)).
  { change (mkAX (R16r t) [] (SLit SHB)) with (ax_setS R16pre (R16r t)).
    eapply (SPA_ghosts (KxA mF BF) rho rho2 R16pre (R16r t) 81%positive (TP12 rho) _ _ (F16c t)).
    - intros r r' t0 tr0 md0 X; exact X.
    - rewrite Rnx. exact Hag.
    - rewrite Rnx. cbv. intros XX; discriminate XX.
    - exact SWFr.
    - change (bump_next (ax_S R16pre) 81) with R16b. exact SD.
    - reflexivity.
    - constructor; [|constructor]. cbn [fst snd]. apply bv_eq.
      unfold a0_16. change (SLit 18446744073709547520) with (SLit M4096). rewrite U_and_m4096.
      rewrite (U_add_slit rho2 1%positive 3935) by lia. rewrite (U_add_slit rho2 79%positive (c1 t)) by (unfold c1 in *; lia).
      rewrite U1, U79. lia.
    - unfold F16c, FE. unfold c1 in *.
      assert (G8v : bv_unsigned (eval rho2 (g8 80%positive)) = V79).
      { change (bv_unsigned (eval rho2 (g8 80%positive))) with (SymSoundV.U rho2 (g8 80%positive)). rewrite StepA.U_g8; unfold SymSoundV.U; cbn [eval]; rewrite U80; lia. }
      repeat apply Forall_cons; try apply Forall_nil; cbn [holds].
      + split; [lia|]. rewrite U79. exact C79al.
      + split; [lia|]. rewrite U80. exact C80al.
      + apply bv_eq. fold (g8 80%positive). rewrite G8v. cbn [eval]. rewrite U79. reflexivity.
      + cbn [eval]. rewrite U80, u64_of_lit by lia. lia.
      + fold (g8 80%positive). rewrite G8v. cbn [eval]. rewrite U79. lia.
      + fold (g8 80%positive). rewrite G8v. cbn [eval]. rewrite U79. lia.
      + cbn [eval]. rewrite U79, u64_of_lit by lia. lia.
      + cbn [eval]. rewrite U79, u64_of_lit by lia. lia.
      + rewrite (U_add_slit rho2 1%positive) by lia. cbn [eval]. rewrite U1, U79. lia.
      + rewrite (U_add_slit rho2 1%positive) by lia. cbn [eval]. rewrite U1, U79. lia.
      + apply bv_eq. rewrite U_and_4095, (U_add_slit rho2 80%positive) by (unfold PB; destruct (t =? 0); lia). rewrite U80. cbn [eval]. rewrite u64_of_lit by lia.
        fold t. change (V80 + PB t) with (PBz x) in |- *. rewrite CPBal. reflexivity.
      + apply bv_eq. rewrite U_and_4095, (U_add_slit rho2 80%positive) by (unfold PE; lia). rewrite U80. cbn [eval]. rewrite u64_of_lit by lia.
        change (V80 + PE) with (PEz x). rewrite CPEal. reflexivity.
    - exact Hsp. }
  pose proof mF_vmmaps as (MR & MM & MN & ML & MI5 & MLZ).
  assert (UHP : bv_unsigned (Z_to_bv 64 (HPz x)) = HPz x) by (apply u64_of_lit; lia).

  set (J' := fun (r : valuation) (_ : list word) (tr0 : list event) (md0 : Model) => KxA mF B16L r (TP17 rho) tr0 md0).
  assert (PAIDF : paid md (TP17 rho) <= B16L).
  { destruct H1 as [_ (_ & _ & HP1)]. cbn [w_cfg cfg_model snd] in HP1. unfold TP17, TP16. fold x.
    pose proof (paid_enspagesZ_le md 5 LOWPG (pages_rev (HPz x + 4096) (n16 x) ++ enspage (Z_to_bv 64 (HPz x)) (TP12 rho))) as P1.
    pose proof (paid_app_le md (pages_rev (HPz x + 4096) (n16 x)) (enspage (Z_to_bv 64 (HPz x)) (TP12 rho))) as P2. rewrite length_pages_rev in P2.
    pose proof (paid_enspage_le md (Z_to_bv 64 (HPz x)) (TP12 rho)) as P3. unfold B16L, B16, page_size in *. lia. }
  assert (PAID12 : paid md (TP12 rho) <= BF) by (destruct H1 as [_ (_ & _ & HP1)]; exact HP1).
  assert (LIM : BF + 4096 * 230 <= vm_limit (m_vmmaps m)) by (unfold BF, B12x, B12, B11; lia).
  assert (H2 : SPA segsA J' (mkAX (R16r t) [] (SLit SHB)) rho2 (TP12 rho) ([], mkCfg ms md)).
  { destruct H1 as [Hsm1 _]. split; [exact Hsm1|]. subst J'. cbv beta. split; [reflexivity|]. split; [exact Hem | exact PAIDF]. }

  assert (H2m : SPA segsA J' (mkAX (R16m t) [] (SLit SHB)) rho2 (TP12 rho) ([], mkCfg ms md)).
  { pose proof (SPA_merge8 J' rho2 (mkAX (R16r t) [] (SLit SHB)) 21 (SVar 36%positive) (SLit 0) (SLit 4096) DZero 0 ES17 (SVar 34%positive) [] (TP12 rho) ([], mkCfg ms md)
                  N21 eq_refl ltac:(lia) ltac:(lia)) as M.
    specialize (M ltac:(intros _ k e Hk; cbn [eval];
      destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; cbn in Hk; [..|destruct k; discriminate]; injection Hk as <-; cbn [eval];
      rewrite ?U_zext8, ?srl_val; change (0 mod 64) with 0 || idtac; rewrite ?Z.shiftr_0_r, ?Zmod_mod; try reflexivity;
      repeat match goal with |- context [(?a mod 64)] => let v := eval compute in (a mod 64) in change (a mod 64) with v end; rewrite ?Zmod_mod; reflexivity)).
    exact (M SB21 H2). }
  pose proof (SPA_facts_hold segsA _ _ _ _ _ H2m) as HF2. cbn [ax_S] in HF2.
  destruct (clear16 t Htin) as (CLR & SWFl).
  pose proof (priZ_facts rho HV) as (PR1 & PR2 & PR3 & PR4). fold x in PR1.

  assert (DISJ : forall r lo hi, Forall (holds r) (ss_facts (R16m t)) -> (forall i, (i < 79)%positive -> rw r i = rw rho i) ->
              0x10006fef8000 <= lo -> lo <= hi -> hi <= 0x10007fff8000 ->
              (LIMz x <= lo \/ (exists q, q mod 4096 = 0 /\ q <= lo /\ hi <= q + 4096 /\ ~ In (Z_to_bv 64 q) (TP12 rho))) ->
              Forall (fun o => ranges_disjoint (obj_range r o) (lo, hi)) (ss_objs (R16m t))).
  { intros r lo hi HFr Hr Hq0 Hlh Hq1 Hcase. apply Forall_forall. intros o Ho.
    pose proof (objs_clear_e_sound r G14b (R16m t) (Z_to_bv 64 lo) (hi - lo) HFr CLR ltac:(lia)
                  ltac:(rewrite u64_of_lit by lia; lia) ltac:(intros y Hy; rewrite u64_of_lit in Hy by lia; lia)) as X.
    rewrite u64_of_lit in X by lia. replace (lo + (hi - lo)) with hi in X by lia. apply X; [|exact Ho].
    intros e sz Hin y Hy.
    assert (HVr : vals r) by (eapply (vals12_agree _ _ _ _ _ _ _ 79%positive rho r); [lia | exact HV | exact Hr]).
    assert (Exr : x1 r = x) by (unfold x1; rewrite Hr by lia; reflexivity).
    destruct (blocks16 r HVr ltac:(rewrite Hr by lia; exact H36) ltac:(rewrite Hr by lia; exact H77) ltac:(rewrite Hr by lia; exact H78) e sz Hin)
      as [Hband|(-> & -> & L1 & L2)]; [unfold SHADOW_BAND_LO, SHADOW_BAND_HI in Hband; lia|].
    rewrite Exr in L1. change (eval r shRI_base) with (pRI r) in *. rewrite (Upri r HVr) in *.
    assert (Epr : priZ r = priZ rho) by (unfold priZ; rewrite Hr by lia; reflexivity). rewrite Epr in *.
    destruct Hcase as [Hc|(q & Hqal & Hq2 & Hq3 & Hc)]; [lia|].
    intros Hyy. apply Hc. replace q with (priZ rho).
    - rewrite <- (Upri rho HV), Z_to_bv_bv_unsigned. exact PR4.
    - apply Z.mod_divide in Hqal as [kq Hkq]; [|lia]. pose proof PR2 as PA. apply Z.mod_divide in PA as [kp Hkp]; [|lia].
      first [ clear - Hkq Hkp Hy Hyy Hq2 Hq3 Hlh L1 L2; nia | nia ]. }

  assert (DISJL : forall r, Forall (holds r) (ss_facts (R16m t)) -> (forall i, (i < 79)%positive -> rw r i = rw rho i) ->
              forall lo hi, LOWPG <= lo -> lo <= hi -> hi <= LOWPG + 0x5000 ->
              Forall (fun o => ranges_disjoint (obj_range r o) (lo, hi)) (ss_objs (R16m t))).
  { intros r HFr Hr lo hi Hl1 Hl2 Hl3. unfold LOWPG in *. apply Forall_forall. intros o Ho.
    pose proof (objs_clear_e_sound r G14b (R16m t) (Z_to_bv 64 lo) (hi - lo) HFr CLR ltac:(lia)
                  ltac:(rewrite u64_of_lit by lia; lia) ltac:(intros y Hy; rewrite u64_of_lit in Hy by lia; lia)) as X.
    rewrite u64_of_lit in X by lia. replace (lo + (hi - lo)) with hi in X by lia. apply X; [|exact Ho].
    intros e sz Hin y Hy.
    assert (HVr : vals r) by (eapply (vals12_agree _ _ _ _ _ _ _ 79%positive rho r); [lia | exact HV | exact Hr]).
    destruct (blocks16 r HVr ltac:(rewrite Hr by lia; exact H36) ltac:(rewrite Hr by lia; exact H77) ltac:(rewrite Hr by lia; exact H78) e sz Hin)
      as [Hband|(-> & -> & L1 & L2)]; [unfold SHADOW_BAND_LO, SHADOW_BAND_HI in Hband; lia | lia]. }

  assert (ZK : forall q zlo zhi, In (Z_to_bv 64 q) (TP12 rho) -> 0 <= q -> q + 4096 <= 2 ^ 64 -> q mod 4096 = 0 -> q <= zlo -> zhi <= q + 4096 -> LIMz x <= zlo ->
            forall a, zlo <= a < zhi -> rm rho (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  { intros q zlo zhi Hin Hq0 Hq64 Hqal Hzlo Hzhi Hlim. exact (ZK16 rho q zlo zhi HV HF Hz HZ11 Hin Hq0 Hq64 Hqal Hzlo Hzhi Hlim). }

  destruct (ensure_page J' (mkAX (R16m t) [] (SLit SHB)) (HPz x) (HPz x + 512 * t) (HPz x + 4096) rho2 (TP12 rho) [] ms md H2m) as (rho3 & tp3 & H3 & Hrw3 & Hrl3 & Hz3 & Ho3 & Hf3 & Hs3 & Etp3).
  { intros r r' t0 t' X; exact X. }
  { exact CHPal. } { lia. } { lia. } { lia. } { lia. }
  { rewrite Elz. apply high_shadow_lazy_mF; rewrite u64_of_lit by lia; [lia | unfold SHADOW_BAND_HI; lia]. }
  { intros z Hz'. rewrite Evm. apply high_shadow_acc_mF. unfold SHADOW_BAND_HI. lia. }
  { unfold headroom. rewrite Evm, ML. unfold page_size. lia. }
  { intros Hnin. cbn [ax_S]. apply (DISJ rho2 (HPz x) (HPz x + 4096) HF2 Elow); [lia | lia | lia |].
    right. exists (HPz x). split; [exact CHPal|]. split; [lia|]. split; [lia | exact Hnin]. }
  { intros Hin a Ha. unfold rho2. rewrite !rho_set_rw_rm. apply (ZK (HPz x) (HPz x + 512 * t) (HPz x + 4096) Hin); lia. }
  assert (ETP3 : tp3 = enspage (Z_to_bv 64 (HPz x)) (TP12 rho)) by (rewrite Etp3; reflexivity).
  pose proof (SPA_facts_hold segsA _ _ _ _ _ H3) as HF3. cbn [ax_S] in HF3.
  assert (Elow3 : forall i, (i < 79)%positive -> rw rho3 i = rw rho i) by (intros i Hi; rewrite Hrw3; apply Elow; exact Hi).
  assert (PAID3 : paid md tp3 <= BF + 4096) by (rewrite ETP3; pose proof (paid_enspage_le md (Z_to_bv 64 (HPz x)) (TP12 rho)); unfold page_size in *; lia).

  destruct (SPA_prepay_pages_rm J' (mkAX (R16m t) [] (SLit SHB)) (HPz x + 4096) (n16 x) rho3 tp3 [] ms md H3) as (rho4 & H4 & Hrw4 & Hrl4 & Hz4 & Ho4).
  { intros r r' t0 t' X; exact X. }
  { replace (HPz x + 4096) with (HPz x + 1 * 4096) by lia. rewrite Z_mod_plus_full. exact CHPal. }
  { lia. } { lia. }
  { intros k Hk. rewrite Elz. pose proof (proj1 (Nat2Z.inj_lt _ _) Hk) as HkZ. apply high_shadow_lazy_mF; unfold pageZ; rewrite u64_of_lit by lia; [lia | unfold SHADOW_BAND_HI; lia]. }
  { intros k Hk Hin. pose proof (proj1 (Nat2Z.inj_lt _ _) Hk) as HkZ. rewrite ETP3 in Hin. apply In_enspage_inv in Hin as [E|Hin].
    - apply (f_equal bv_unsigned) in E. unfold pageZ in E. rewrite UHP, u64_of_lit in E by lia. lia.
    - destruct (TP12_split rho HV V35 Hx H16 _ Hin) as [L|L]; fold x in L; unfold pageZ in L; rewrite u64_of_lit in L by lia; lia. }
  { intros z Hz'. rewrite Evm. apply high_shadow_acc_mF. unfold SHADOW_BAND_HI. lia. }
  { unfold headroom. rewrite Evm, ML. unfold page_size. lia. }
  { cbn [ax_S]. apply (DISJ rho3 (HPz x + 4096) (HPz x + 4096 + 4096 * Z.of_nat (n16 x)) HF3 Elow3); [lia | lia | lia | left; lia]. }
  rewrite N16 in Hz4, Ho4.
  pose proof (SPA_facts_hold segsA _ _ _ _ _ H4) as HF4. cbn [ax_S] in HF4.
  assert (Elow4 : forall i, (i < 79)%positive -> rw rho4 i = rw rho i) by (intros i Hi; rewrite Hrw4; apply Elow3; exact Hi).
  assert (ETP4 : pages_rev (HPz x + 4096) (n16 x) ++ tp3 = TP16 rho) by (rewrite ETP3; reflexivity).
  rewrite ETP4 in H4.
  assert (PAID4 : paid md (TP16 rho) <= BF + 4096 * 224).
  { rewrite <- ETP4. pose proof (paid_app_le md (pages_rev (HPz x + 4096) (n16 x)) tp3) as P2. rewrite length_pages_rev in P2. unfold page_size in *. lia. }

  assert (IN16_12 : forall q, In q (TP16 rho) -> bv_unsigned q < LOWPG + 0x5000 -> In q (TP12 rho)).
  { intros q Hin Hlt. rewrite <- ETP4 in Hin. apply in_app_iff in Hin as [Hin|Hin].
    - exfalso. apply In_pages_rev in Hin as (k & Hk & ->). pose proof (proj1 (Nat2Z.inj_lt _ _) Hk) as HkZ.
      unfold pageZ in Hlt. rewrite u64_of_lit in Hlt by lia. unfold LOWPG in Hlt. lia.
    - rewrite ETP3 in Hin. apply In_enspage_inv in Hin as [->|Hin]; [|exact Hin].
      exfalso. rewrite UHP in Hlt. unfold LOWPG in Hlt. lia. }
  destruct (ensure_pages J' (mkAX (R16m t) [] (SLit SHB)) 5 LOWPG (LOWPG + 0x4600) rho4 (TP16 rho) [] ms md H4) as (rho5 & H5 & Hrw5 & Hrl5 & Hz5 & Ho5 & Hf5 & Hs5).
  { intros r r' t0 t' X; exact X. }
  { reflexivity. } { unfold LOWPG; lia. } { unfold LOWPG; lia. } { lia. }
  { intros k Hk. rewrite Elz. apply low_shadow_lazy_mF; rewrite u64_of_lit by (unfold LOWPG; lia); unfold LOWPG, SHADOW_BAND_LO, SHADOW_RW_LO_END; lia. }
  { intros z Hz'. rewrite Evm. apply low_shadow_acc_mF. unfold LOWPG, SHADOW_BAND_LO, SHADOW_RW_LO_END in *. lia. }
  { unfold headroom. rewrite Evm, ML. unfold page_size. lia. }
  { intros k Hk _. cbn [ax_S]. apply (DISJL rho4 HF4 Elow4); lia. }
  { intros k Hk Hin a Ha Hza.
    rewrite (Ho4 (Z_to_bv 64 a)) by (rewrite u64_of_lit by (unfold LOWPG in *; lia); unfold LOWPG in *; lia).
    rewrite (Ho3 (Z_to_bv 64 a)) by (rewrite u64_of_lit by (unfold LOWPG in *; lia); unfold LOWPG in *; lia).
    unfold rho2. rewrite !rho_set_rw_rm.
    assert (UK : bv_unsigned (Z_to_bv 64 (LOWPG + 4096 * Z.of_nat k)) = LOWPG + 4096 * Z.of_nat k) by (apply u64_of_lit; unfold LOWPG; lia).
    apply (LZ_of_Z11 rho HV V35 HZ11 Hx H16 _ a (IN16_12 _ Hin ltac:(rewrite UK; unfold LOWPG; lia))); [rewrite UK; lia | lia]. }
  change (enspagesZ LOWPG 5 (TP16 rho)) with (TP17 rho) in H5.
  pose proof (SPA_facts_hold segsA _ _ _ _ _ H5) as HF5. cbn [ax_S] in HF5.
  assert (Elow5 : forall i, (i < 79)%positive -> rw rho5 i = rw rho i) by (intros i Hi; rewrite Hrw5; apply Elow4; exact Hi).
  assert (U80e : bv_unsigned (rw rho5 80%positive) = V80) by (rewrite Hrw5, Hrw4, Hrw3; exact U80).

  assert (EbL : bv_unsigned (eval rho5 (SLit LOWPG)) = LOWPG) by (cbn [eval]; apply u64_of_lit; unfold LOWPG; lia).
  pose proof (SPA_carve_zero segsA J' rho5 (mkAX (R16m t) [] (SLit SHB)) (TP17 rho) [] ms md (SLit LOWPG) 0 0x4600 81%positive H5) as H6.
  cbn [ax_S ax_X ax_base] in H6. rewrite EbL in H6. fold O_lowpg in H6.
  specialize (H6 SWFl ltac:(rewrite NXm; apply Pos.le_refl) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold LOWPG; lia) ltac:(unfold LOWPG; lia)
                 (DISJL rho5 HF5 Elow5 (LOWPG + 0) (LOWPG + 0x4600) ltac:(lia) ltac:(lia) ltac:(lia))
                 ltac:(intros a Ha; apply Hz5; lia) ltac:(intros rr y j [])).

  assert (EbS : bv_unsigned (eval rho5 (SSB t)) = HPz x + 512 * t).
  { unfold SSB. rewrite (U_add_slit rho5 80%positive) by lia. rewrite U80e. unfold HPz. fold V80. lia. }
  assert (ZSS : forall a, HPz x + 512 * t <= a < PEz x + 512 * t -> rm rho5 (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  { intros a Ha. rewrite (Ho5 (Z_to_bv 64 a)) by (rewrite u64_of_lit by lia; unfold LOWPG; lia).
    destruct (Z_lt_dec a (HPz x + 4096)) as [A1|A1].
    - rewrite (Ho4 (Z_to_bv 64 a)) by (rewrite u64_of_lit by lia; lia). apply Hz3. lia.
    - destruct (Z_lt_dec a (q12x x)) as [A2|A2]; [apply Hz4; lia|].
      rewrite (Ho4 (Z_to_bv 64 a)) by (rewrite u64_of_lit by lia; lia).
      rewrite (Ho3 (Z_to_bv 64 a)) by (rewrite u64_of_lit by lia; lia).
      unfold rho2. rewrite !rho_set_rw_rm. apply (ss_zero_range rho Hz Hx). fold x. lia. }
  match type of H6 with SPA _ _ ?A _ _ _ => set (A6 := A) in H6 end.
  pose proof (SPA_carve_zero segsA J' rho5 A6 (TP17 rho) [] ms md (SSB t) 0 1048576 81%positive H6) as H7.
  subst A6. cbn [ax_S ax_setS ax_X ax_base ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_lenient] in H7. rewrite EbS in H7.
  assert (ER16c : R16c t = mkAX (mkSS (ss_pc (R16m t)) (ss_regs (R16m t)) (ss_fregs (R16m t)) (ss_fcsr (R16m t)) (ss_resv (R16m t))
                                    ((ss_objs (R16m t) ++ [O_lowpg]) ++ [mkObj (SSB t) (SLit 0) (SLit 1048576) [] DZero])
                                    (ss_facts (R16m t)) 81%positive (ss_lenient (R16m t))) [] (SLit SHB)).
  { unfold R16c, R16m, replace_obj_at. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_facts ss_lenient ss_objs]. rewrite <- app_assoc. reflexivity. }
  assert (H8 : SPA segsA J' (R16c t) rho5 (TP17 rho) ([], mkCfg ms md)).
  { rewrite ER16c. apply H7.
    - pose proof SWFc as SW. rewrite ER16c in SW. exact SW.
    - cbn [ss_next]. apply Pos.le_refl.
    - lia. - lia. - lia. - lia. - lia.
    - apply Forall_app. split.
      + replace (HPz x + 512 * t + 1048576) with (PEz x + 512 * t) by lia. replace (HPz x + 512 * t + 0) with (HPz x + 512 * t) by lia.
        apply (DISJ rho5 (HPz x + 512 * t) (PEz x + 512 * t) HF5 Elow5); [lia | lia | lia | left; exact CLIM].
      + constructor; [|constructor]. unfold obj_range, obj_lo_of, obj_hi_of, O_lowpg. cbn [ob_base ob_lo ob_hi]. rewrite EbL, !soff_lit_small by lia.
        unfold ranges_disjoint, LOWPG. cbn [fst snd]. lia.
    - intros a Ha. apply ZSS. lia.
    - intros rr y j []. }
  exists rho5. split; [exact Elow5|]. split; [rewrite Hrw5, Hrw4, Hrw3; exact E79|]. split; [rewrite Hrw5, Hrw4, Hrw3; exact E80|].
  split; [intros l; rewrite Hrl5, Hrl4, Hrl3; reflexivity|].
  split.
  { intros a N1 N2. rewrite (Ho5 a) by lia. rewrite (Ho4 a) by lia. rewrite (Ho3 a) by lia. unfold rho2. rewrite !rho_set_rw_rm. reflexivity. }
  split; [exact ZSS|].
  split.
  { intros a Ha. assert (A5 : rm rho5 (Z_to_bv 64 a) = rm rho3 (Z_to_bv 64 a)).
    { rewrite (Ho5 (Z_to_bv 64 a)) by (rewrite u64_of_lit by lia; unfold LOWPG; lia). apply Ho4. rewrite u64_of_lit by lia. lia. }
    rewrite A5. split; intros Hm.
    - rewrite (Hs3 Hm (Z_to_bv 64 a)). unfold rho2. rewrite !rho_set_rw_rm. reflexivity.
    - apply (Hf3 Hm). lia. }
  split; [exact Hf5|].
  split.
  { intros k Hk Hin a Ha. rewrite (Hs5 k Hk Hin a Ha). rewrite (Ho4 a) by (unfold LOWPG in Ha; lia). rewrite (Ho3 a) by (unfold LOWPG in Ha; lia).
    unfold rho2. rewrite !rho_set_rw_rm. reflexivity. }
  split; [exact V35|].
  destruct H8 as [Hsm8 HK8]. split; [exact Hsm8|]. subst J'. cbv beta in HK8. exact HK8.
Qed.

Lemma run16 : ltac2:(tb__ "0|1|
S5S18S36S15Q40A1A1S41S5R3S8cA3S9dS35Vok;S5aS35S75S5fS62A2M0SbdS8eR4A1A1R3R2A5S5bS35G0P51R3R2S39S98S99SaeR4A1Sb8A2S3cS98A1A3A6A4F_;Ftp;Frho;Ft;").
Proof using OKF.
  intros t rho tp Ht. destruct (cls16 t Ht) as (RUN & _). apply triple1_triple.
  apply (sym_run_soundA segsA _ _ _ _ ok _ rho tp RUN); [apply OKFx | reflexivity | apply stableA_KxA].
Qed.

Lemma call16 : ltac2:(tb__ "0|1|
S5S18S36S15Q40A1A1S41S5R3S8cA3S9dS35Vok;S5aS35S75S5fS62A2M0SaeR4A1R3R2A5S9bS2S18S18S1S26P51R5R1A3S5aS35G0Sb1R6A1R1R4R2A6A2Lrho';A2Lw;A4F_;Ftp;Frho;Ft;").
Proof using OKF.
  intros t rho tp Ht. destruct (cls16 t Ht) as (_ & FR & CC & IPE & NX & _).
  apply (call_pureA segsA ok (M16_of t) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.Pre_mszA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.Posts_mszA (s16_of t) (R16_of t) mF B16L tp rho _ OKF FR CC).
  - intros J rho1 tp1 HokJ HstJ. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.memsetZ_sumA ok J HokJ HstJ rho1 tp1).
  - intros L rho' [<-|[]] Hag. cbn [la_state]. rewrite NX in Hag. rewrite IPE.
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply triple_refl].
    exists rho'. split; [exact Hag | exact Hw].
Qed.

Lemma unshape16 : ltac2:(tb__ "0|b|
S5S18S18S36S15Q40M0A1M1A1S9bS41S5R5S8cA3S60R5A1S5S0S5S80R1A1R7A3S1S7Z7fff80000000R2A2S7R2ScZ2Z2fA2A2A2S0S5SaR3Z10A2Z0M2A3S26P51R9R8A3S0G1S17RaP50A2S14G0S81R5A1A2A3S96S1aS1cRbA1S1eS97SaeRcA1A1A1A3S5aS35S75S5fS62A2M3Sb1RdA1RbRaR9A6S2S18S18S1S6S0G1S17R2R1A2S17ReR1A2A3Fi;S1S6S0S36S15Q8M4A1M5A1S1dR2R1A2S1dReR1A2A3Fl;S1G1S3S1S7S8S7fRaA1SbZ200R10A2M6A2M7S16G0R1A2M8A2S9G8S8S85RaA1G6A2M9A2A2A1S0S3dG5A1MaS19R3R2A2S19RfR2A2A3F_;Fa;S1S5S1S7G7R1A2S9R1G9A2A2S0GaS19R3S14G0R2A2A2S3eG5S14G4G2A2A2A3F_;Fa;S5aS35G3Sb2RfA1R1RcRbA6A2A2A2A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;Tx;F_;Fw;Ftp;Frho;Frho0;Ft;").
Proof.
  intros t rho0 rho tp [tr [ms md]] Ht x Htc Hx H16 Hag E80 HF0 Hsp.
  pose proof (class_arith x Hx H16) as CA. cbv zeta in CA.
  destruct CA as (Ct & C79al & C80x8 & C80al & C80nn & C79lo & C79hi & Ctop1 & Ctop2 & Ctopal & Ctoplo & Cand & CHPal & CPEal & CPBal & CPB & CLEN & CPEHP & CHPlo & CPEhi & _).
  rewrite Htc in *.
  destruct (cls16 t Ht) as (_ & _ & _ & _ & NX & _ & MV & SB & OBJ & LEN & IPRE & FB & FB81 & _ & NXI & _).
  assert (R80 : 0 <= v80Z x < 2 ^ 61) by (unfold c1 in C79hi; lia).
  assert (U80 : bv_unsigned (rw rho 80%positive) = v80Z x).
  { destruct Hag as (V & _). rewrite <- (V 80%positive) by lia. rewrite E80. apply u64_of_lit. lia. }

  pose proof (SPA_move_lastX (KxA mF B16L) rho (IP16_of t) 0 tp _ ltac:(rewrite LEN; lia) ltac:(rewrite MV; exact SB) Hsp) as H1.
  rewrite MV in H1.
  assert (RS : obj_range rho (O_ss t) = (HPz x + 512 * t, PEz x + 512 * t)).
  { unfold obj_range, obj_lo_of, obj_hi_of, O_ss, SSB. cbn [ob_base ob_lo ob_hi]. rewrite (U_add_slit rho 80%positive) by lia.
    rewrite U80, !soff_lit_small by lia. unfold HPz, PEz, PE. f_equal; lia. }
  assert (ZS : forall a, HPz x + 512 * t <= a < PEz x + 512 * t -> ms_mem (vms md tp ms) (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  { intros a Ha. apply (SPA_dzero_bytes_A (KxA mF B16L) _ rho tp tr ms md (O_ss t) H1);
      [cbn [ax_S ax_setS]; rewrite OBJ; apply in_app_iff; right; left; reflexivity | reflexivity | reflexivity | rewrite RS; cbn [fst]; lia | rewrite RS; cbn [fst snd]; exact Ha]. }

  pose proof (SPA_unobj segsA (KxA mF B16L) rho (ax_setS (IP16_of t) (IPm_of t)) (R16_of t) [O_ss t] tp tr ms md
                ltac:(cbn [ax_S ax_setS]; exact OBJ) H1 ltac:(intros X; exact X)) as H2. cbv zeta in H2.
  cbn [ax_S ax_setS] in H2.
  set (rho' := rho_absorb rho [O_ss t] (vms md tp ms)) in *.

  pose proof (SPA_refacts segsA (KxA mF B16L) rho' _ (ss_facts (ax_S (M16_of t))) tp _ H2) as H3.
  cbn [ax_S ax_setS set_objs ss_next] in H3.
  specialize (H3 ltac:(rewrite <- MV; exact FB)).
  specialize (H3 ltac:(intros _; apply Forall_forall; intros f Hf; unfold rho'; apply (proj2 (holds_absorb rho [O_ss t] (vms md tp ms) f));
                        exact (proj1 (Forall_forall _ _) (holds_all_agree 81%positive rho0 rho _ FB81 Hag HF0) f Hf))).
  rewrite IPRE in H3.
  exists rho'. split; [intros; apply rw_absorb|]. split; [intros; apply rl_absorb|]. split.
  - intros a Ha. apply rm_absorb_outside. intros (o & [<-|[]] & Hr). rewrite RS in Hr. cbn [fst snd] in Hr. lia.
  - split; [|exact H3]. intros a Ha. unfold rho'. rewrite rm_absorb_inside; [apply ZS; exact Ha|].
    exists (O_ss t). split; [left; reflexivity|]. rewrite RS. cbn [fst snd]. rewrite u64_of_lit by lia. lia.
Qed.

Lemma run17x : ltac2:(tb__ "0|1|
S5S18S36S15Q40A1A1S41S5R3S8cA3S9dS35Vok;S5aS35S75S5fS62A2M0Sb2R4A1R3R2A5S5bS35G0P79R3R2S39S98S99Sb0R4A1Sb8A2S3cS98A1A3A6A4F_;Ftp;Frho;Ft;").
Proof using OKF.
  intros t rho tp Ht. destruct (cls16 t Ht) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RUN & _). apply triple1_triple.
  pose proof (sym_run_soundA segsA _ _ _ _ ok (KxA mF B16L) rho tp RUN) as S.
  replace (ss_next (ax_S (IPr_of t))) with 121%positive in S; [apply S; [apply OKFx | | apply stableA_KxA]|].
  - destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; reflexivity.
  - destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma CF16_holds : ltac2:(tb__ "0|2|
S18S60R1A1S5S1S7Z7fff80000000R1A2S7R1ScZ2Z2fA2A2A2S0S5SaR2Z10A2Z0A3S0S15Q40M0A1M1S17R4P4fA2S14G0S84R3A1A2A3S0G1S17R5P50A2S14G0S81R4A1A2A3S0G1S17R6P51A2S14G0S86R5A1A2A3S96S1aS1cR7A1SafA3F_;F_;F_;F_;F_;Tx;Frho;").
Proof.
  clear. intros rho x Hx H16 E79 E80 E81.
  pose proof (class_arith x Hx H16) as CA. cbv zeta in CA.
  destruct CA as (Ct & C79al & C80x8 & C80al & C80nn & C79lo & C79hi & Ctop1 & Ctop2 & Ctopal & Ctoplo & _).
  unfold c1 in *.
  assert (U79 : bv_unsigned (rw rho 79%positive) = v79Z x) by (rewrite E79; apply u64_of_lit; lia).
  assert (U80 : bv_unsigned (rw rho 80%positive) = v80Z x) by (rewrite E80; apply u64_of_lit; lia).
  assert (U81 : bv_unsigned (rw rho 81%positive) = topZ x) by (rewrite E81; apply u64_of_lit; lia).
  assert (U1 : bv_unsigned (rw rho 1%positive) = x) by reflexivity.
  assert (G8v : bv_unsigned (eval rho (g8 80%positive)) = v79Z x).
  { change (bv_unsigned (eval rho (g8 80%positive))) with (SymSoundV.U rho (g8 80%positive)). rewrite StepA.U_g8; unfold SymSoundV.U; cbn [eval]; rewrite U80; lia. }
  unfold CF16, FE. repeat apply Forall_cons; try apply Forall_nil; cbn [holds].
  - split; [lia|]. rewrite U79. exact C79al.
  - split; [lia|]. rewrite U80. exact C80al.
  - apply bv_eq. fold (g8 80%positive). rewrite G8v. cbn [eval]. rewrite U79. reflexivity.
  - cbn [eval]. rewrite U80, u64_of_lit by lia. lia.
  - fold (g8 80%positive). rewrite G8v. cbn [eval]. rewrite U79. lia.
  - fold (g8 80%positive). rewrite G8v. cbn [eval]. rewrite U79. lia.
  - cbn [eval]. rewrite U79, u64_of_lit by lia. lia.
  - cbn [eval]. rewrite U79, u64_of_lit by lia. lia.
  - rewrite (U_add_slit rho 1%positive) by lia. cbn [eval]. rewrite U1, U79. lia.
  - rewrite (U_add_slit rho 1%positive) by lia. cbn [eval]. rewrite U1, U79. lia.
  - split; [lia|]. rewrite U81. exact Ctopal.
  - rewrite (U_add_slit rho 1%positive) by lia. cbn [eval]. rewrite U1, U81. lia.
  - rewrite (U_add_slit rho 1%positive) by lia. cbn [eval]. rewrite U1, U81. lia.
  - cbn [eval]. rewrite U81, u64_of_lit by lia. lia.
  - cbn [eval]. rewrite U81, u64_of_lit by lia. lia.
Qed.

Lemma forallb_CF16_holds : ltac2:(tb__ "0|0|
S18S36S1aA1S0S37S43S1aS1aS42S1aS21R1A1SafA3Lf;R1A3S3bA3S96S1aS1cR3A1SafA3S96S1aS1cR4A1R3A3F_;F_;Fnf;Frho;").
Proof.
  clear. intros rho nf Hb HF. apply Forall_forall. intros f Hf. pose proof (proj1 (forallb_forall _ _) Hb f Hf) as X. cbv beta in X.
  apply existsb_exists in X as (g & Hg & E). apply sprop_eqb_sound in E. subst g. exact (proj1 (Forall_forall _ _) HF f Hg).
Qed.

Lemma join17 : ltac2:(tb__ "0|5|
S5S18S36S15Q40M0A1M1A1S9bS41S5R4S8cA3S60R4A1S5S0S5S80R1A1R6A3S1S7Z7fff80000000R2A2S7R2ScZ2Z2fA2A2A2S0S5SaR3Z10A2Z0A3S0G1S17R8P4fA2S14G0S84R4A1A2A3S0G1S17R9P50A2S14G0S81R5A1A2A3S5aS35S75S5fS62A2M2Sb0RbA1RaR9R8A6S2S18S18S1S6Sc4R1P51M3A2S0G1S17R3R2A2S17ReR2A2A3F_;Fi;S1S0G1S17R1G3A2S14G0S86R8A1A2A3S1S6S0S36S15Q8A1M4A1S1dR2R1A2S1dRdR1A2A3Fl;S1G1S0S3dG4A1S19R2R1A2S19RdR1A2A3Fa;S5aS35G2SadR1RbRaA6A2A2A2A2Lrho';A2F_;F_;F_;F_;F_;F_;Tx;F_;Fw;Ftp;Frho;Ft;").
Proof.
  intros t rho tp w Ht x Htc Hx H16 E79 E80 Hsp.
  pose proof (class_arith x Hx H16) as CA. cbv zeta in CA.
  destruct CA as (Ct & C79al & C80x8 & C80al & C80nn & C79lo & C79hi & Ctop1 & Ctop2 & Ctopal & Ctoplo & Cand & CHPal & CPEal & CPBal & CPB & CLEN & CPEHP & CHPlo & CPEhi & _).
  rewrite Htc in *.
  assert (R79 : 0 <= v79Z x < 2 ^ 64) by (unfold c1 in C79hi; lia).
  assert (U79 : bv_unsigned (rw rho 79%positive) = v79Z x) by (rewrite E79; apply u64_of_lit; lia).
  destruct (sd17 t Ht) as (nf & SD & NF & SWFx & SWFn & AXW).
  destruct (cls16 t Ht) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FX & FB).

  pose proof (SPA_noX (KxA mF B16L) rho (F17_of t) tp w Hsp) as H0.
  pose proof (SPA_set_next (KxA mF B16L) rho (StartDefsA.noX (F17_of t)) 81%positive tp w SWFn AXW H0) as H1.
  set (rho' := rho_set_rw (rho_set_rw rho 81%positive (Z_to_bv 64 (topZ x))) 82%positive (Z_to_bv 64 0)).
  assert (E81 : rw rho' 81%positive = Z_to_bv 64 (topZ x)) by (unfold rho'; rewrite rho_set_rw_other by lia; apply rho_set_rw_at).
  assert (Elow : forall i, (i < 81)%positive -> rw rho' i = rw rho i) by (intros i Hi; unfold rho'; rewrite !rho_set_rw_other by lia; reflexivity).
  exists rho'. split; [exact Elow|]. split; [exact E81|]. split; [intros l; reflexivity|]. split; [intros a; unfold rho'; rewrite !rho_set_rw_rm; reflexivity|].
  replace E_s17 with (ax_setS (ax_setS (StartDefsA.noX (F17_of t)) (bump_next (ax_S (StartDefsA.noX (F17_of t))) 81%positive)) (ax_S E_s17))
    by (unfold StartDefsA.noX, ax_setS; cbn [ax_X ax_base]; rewrite FB; reflexivity).
  eapply (SPA_ghosts (KxA mF B16L) rho rho' _ (ax_S E_s17) 83%positive tp _ (DX17 t) nf).
  - intros r r' t0 tr0 md0 X; exact X.
  - cbn [ax_S ax_setS bump_next ss_next]. unfold rho'.
    eapply agree_below_trans; [apply (agree_below_set_rw _ 81%positive); lia | apply (agree_below_set_rw _ 82%positive); lia].
  - cbn [ax_S ax_setS bump_next ss_next]. cbv. intros XX; discriminate XX.
  - exact SWFx.
  - cbn [ax_S ax_setS StartDefsA.noX]. exact SD.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  -
    assert (U81 : bv_unsigned (rw rho' 81%positive) = topZ x) by (rewrite E81; apply u64_of_lit; unfold c1 in *; lia).
    assert (U79' : bv_unsigned (rw rho' 79%positive) = v79Z x) by (rewrite Elow by lia; exact U79).
    assert (EB : eval rho' (ebot16 t) = eval rho' (SAlu ALU_ADD (SVar 81%positive) (SLit (-8388608)))).
    { apply bv_eq. rewrite (U_add_slit rho' 81%positive) by (unfold c1 in *; lia). rewrite U81. unfold ebot16.
      destruct (Z.eqb_spec t 0) as [E0|NE0].
      - cbn [eval]. rewrite U79'. unfold c1 in Ctop2. rewrite E0 in Ctop2. lia.
      - rewrite (U_add_slit rho' 79%positive) by (unfold c1 in *; lia). rewrite U79'. unfold c1 in Ctop2. lia. }
    assert (ET : eval rho' (SAlu ALU_ADD (SVar 79%positive) (SLit (c1 t))) = eval rho' (SVar 81%positive)).
    { apply bv_eq. rewrite (U_add_slit rho' 79%positive) by (unfold c1 in *; lia). cbn [eval]. rewrite U79', U81. lia. }
    unfold DX17. repeat constructor; cbn [fst snd]; assumption.
  - apply (forallb_CF16_holds rho' nf NF). assert (Ex : x1 rho' = x) by (unfold x1; rewrite Elow by lia; reflexivity).
    apply CF16_holds; rewrite ?Ex; [exact Hx | exact H16 | rewrite Elow by lia; exact E79 | rewrite Elow by lia; exact E80 | exact E81].
  - exact H1.
Qed.

Definition RM16 (rho rho' : valuation) : Prop :=
  let x := x1 rho in let t := tcls x in
  (forall a : word, ~ (HPz x <= bv_unsigned a < PEz x + 512 * t) -> ~ (LOWPG <= bv_unsigned a < LOWPG + 0x5000) -> rm rho' a = rm rho a) /\
  (forall a, HPz x + 512 * t <= a < PEz x + 512 * t -> rm rho' (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) /\
  (forall a, HPz x <= a < HPz x + 512 * t ->
     (In (Z_to_bv 64 (HPz x)) (TP12 rho) -> rm rho' (Z_to_bv 64 a) = rm rho (Z_to_bv 64 a)) /\
     (~ In (Z_to_bv 64 (HPz x)) (TP12 rho) -> rm rho' (Z_to_bv 64 a) = Some (Z_to_bv 8 0))) /\
  (forall k, (k < 5)%nat -> ~ In (Z_to_bv 64 (LOWPG + 4096 * Z.of_nat k)) (TP16 rho) ->
     forall a, LOWPG + 4096 * Z.of_nat k <= a < LOWPG + 4096 * Z.of_nat k + 4096 -> rm rho' (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) /\
  (forall k, (k < 5)%nat -> In (Z_to_bv 64 (LOWPG + 4096 * Z.of_nat k)) (TP16 rho) ->
     forall a : word, LOWPG + 4096 * Z.of_nat k <= bv_unsigned a < LOWPG + 4096 * Z.of_nat k + 4096 -> rm rho' a = rm rho a).

Definition XF16 (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S1S1S7Z7fff80000000S60Vrho;A1M0A2S7G0ScZ2Z2fA2A2A2S1S0S5SaG0Z10A2Z0A3S0S5SbZ8S16Q40M1S17Vrho;P23A2A2A2S16G1Vb6;A2A3A2A2").

Definition Post16 (rho : valuation) : assn := ltac2:(tb__ "0|3|
S9bS60Vrho;A1S5S2S18S18S1Sb6P4fM0Vrho;R1A3S1S0S15Q40M1A1M2S17R1G0A2S14G1S84R2A1A2A3S1S0G2S17R1P50A2S14G1S81R2A1A2A3S1S0G2S17R1P51A2S14G1S86R2A1A2A3S1S73Vrho;R1A2S1S70Vrho;A1S5aS35S75S5fS62A2SadR1S6aVrho;A1R3A6A2A2A2A2A2A2Lrho';A2Tx;Lw;").

Lemma TP16_ext : ltac2:(tb__ "0|0|
S18S18Sb6P24R2R1A3S0S36S15Q40A1A1S67R2A1S67R3A1A3F_;Frho';Frho;").
Proof.
  clear. intros rho rho' HA. unfold TP16, x1. rewrite (proj1 HA 1%positive) by lia. rewrite (TP12_agree rho rho' HA). reflexivity.
Qed.

Theorem seg16 : ltac2:(tb__ "0|1|
S18S61R1A1S0S15Q40A1M0S17R2P24A2Vb7;A3S0G0S17R3P4dA2Vb8;A3S0G0S17R4P4eA2Vb9;A3S78R5A1S9eR6A1S9dS35Vok;S5aS35S75S5fS65A2Sb5R7S77R7A1A5S6dR7A1A4F_;F_;F_;F_;F_;F_;Frho;").
Proof using All.
  intros rho HV H36 H77 H78 Hz HZ11.

  eapply triple_seq.
  { apply triple1_triple. eapply sym_run_soundA; [exact run15b | apply OKFx | reflexivity | apply stableA_KxA]. }
  apply triple_ex; intros L. apply triple_ex; intros rho1. apply triple_pure; intros HinL. apply triple_pure; intros Hag1.
  destruct HinL as [<-|[]]. cbn [la_state]. replace (ss_next (ax_S S_s15ok)) with 79%positive in Hag1 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof Hag1 as (V1 & L1 & R1).
  assert (AV1 : agree_vars 79 rho rho1) by (split; [intros i Hi; symmetry; apply V1; exact Hi | intros l; symmetry; apply L1]).
  assert (HV1 : vals rho1) by (eapply (vals12_agree _ _ _ _ _ _ _ 79%positive rho rho1); [lia | exact HV | exact (proj1 AV1)]).
  assert (H36a : rw rho1 36%positive = b7) by (rewrite <- (V1 36%positive) by lia; exact H36).
  assert (H77a : rw rho1 77%positive = b8) by (rewrite <- (V1 77%positive) by lia; exact H77).
  assert (H78a : rw rho1 78%positive = b9) by (rewrite <- (V1 78%positive) by lia; exact H78).
  assert (Hz1 : stackshadow_zero rho1) by (apply (stackshadow_zero_ext rho rho1); [symmetry; apply V1; lia | intros a; symmetry; apply R1 | exact Hz]).
  assert (HZ1 : Z11 rho1) by (apply (Z11_ext rho rho1); [symmetry; apply V1; lia | symmetry; apply V1; lia | intros a; symmetry; apply R1 | exact HZ11]).
  assert (Ex1 : x1 rho1 = x1 rho) by (unfold x1; rewrite <- (V1 1%positive) by lia; reflexivity).
  assert (ET1 : TP16 rho1 = TP16 rho) by (apply TP16_ext; eapply agree_vars_le; [|exact AV1]; lia).
  assert (ET17 : TP17 rho1 = TP17 rho) by (unfold TP17; rewrite ET1; reflexivity).
  assert (ET12 : TP12 rho1 = TP12 rho) by (apply TP12_agree; eapply agree_vars_le; [|exact AV1]; lia).
  rewrite <- ET12.

  apply triple_factsA. intros HF1. destruct (x1_facts rho1 HF1) as [Hx H16].
  eapply triple_conseq; [intros w Hw; exact (prep16 rho1 w HV1 H36a H77a H78a Hz1 HZ1 Hw) | intros w Hw; exact Hw |].
  cbv zeta. apply triple_ex; intros rho2. apply triple_pure; intros E2low. apply triple_pure; intros E279. apply triple_pure; intros E280.
  apply triple_pure; intros L2. apply triple_pure; intros R2. apply triple_pure; intros Z2. apply triple_pure; intros HD2.
  apply triple_pure; intros LF2. apply triple_pure; intros LS2. apply triple_pure; intros V35.
  set (x := x1 rho1) in *. set (t := tcls x) in *.
  assert (Ht : In t classes16).
  { pose proof (Z.mod_pos_bound (Tq x) 8 ltac:(lia)) as M8. unfold classes16. cbn [In]. subst t. unfold tcls. lia. }
  rewrite ET17.

  eapply triple_conseq; [intros w Hw; exact (SPA_X0 (KxA mF B16L) rho2 (R16c t) (TP17 rho) w eq_refl Hw) | intros w Hw; exact Hw |].
  eapply triple_seq; [apply (run16 t rho2 (TP17 rho) Ht)|].
  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho3. apply triple_pure; intros Hag3. pose proof Hag3 as (V3 & L3 & R3).
  assert (Ex3 : x1 rho3 = x) by (unfold x1; rewrite <- (V3 1%positive) by lia; rewrite E2low by lia; reflexivity).

  apply triple_factsA. intros HF3.
  eapply triple_seq; [apply (call16 t rho3 (TP17 rho) Ht)|].
  apply triple_ex; intros rho4. apply triple_pure; intros Hag4. pose proof Hag4 as (V4 & L4 & R4).

  eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw |].
  { apply (unshape16 t rho3 rho4 (TP17 rho) w Ht); rewrite ?Ex3; [subst t; reflexivity | exact Hx | exact H16 | exact Hag4 | | exact HF3 | exact Hw].
    rewrite <- (V3 80%positive) by lia. exact E280. }
  cbv zeta. rewrite Ex3. apply triple_ex; intros rho5. apply triple_pure; intros RW5. apply triple_pure; intros RL5.
  apply triple_pure; intros RO5. apply triple_pure; intros RZ5.

  eapply triple_seq; [apply (run17x t rho5 (TP17 rho) Ht)|].
  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho6. apply triple_pure; intros Hag6. pose proof Hag6 as (V6 & L6 & R6).
  assert (E6low : forall i, (i < 81)%positive -> rw rho6 i = rw rho3 i).
  { intros i Hi. rewrite <- (V6 i) by lia. rewrite RW5. symmetry. apply V4. exact Hi. }
  assert (Ex6 : x1 rho6 = x) by (unfold x1; rewrite E6low by lia; exact Ex3).

  eapply triple_conseq; [intros w Hw | | apply triple_refl].
  { apply (join17 t rho6 (TP17 rho) w Ht); rewrite ?Ex6; [subst t; reflexivity | exact Hx | exact H16 | | | exact Hw].
    - rewrite E6low by lia. rewrite <- (V3 79%positive) by lia. exact E279.
    - rewrite E6low by lia. rewrite <- (V3 80%positive) by lia. exact E280. }
  cbv zeta. rewrite Ex6. intros w (rho7 & E7low & E781 & L7 & R7 & Hsp7).

  unfold Post16. cbv zeta. rewrite <- Ex1. fold x. exists rho7.
  assert (E7 : forall i, (i < 79)%positive -> rw rho7 i = rw rho1 i).
  { intros i Hi. rewrite E7low by lia. rewrite E6low by lia. rewrite <- (V3 i) by lia. apply E2low. exact Hi. }
  assert (RM7 : forall a, rm rho7 a = rm rho5 a) by (intros a; rewrite R7, <- (R6 a); reflexivity).
  assert (RM34 : forall a, rm rho4 a = rm rho2 a) by (intros a; rewrite <- (R4 a), <- (R3 a); reflexivity).
  split.
  { split; [intros i Hi; rewrite E7 by lia; symmetry; apply V1; lia|].
    intros l. rewrite L7, <- (L6 l), RL5, <- (L4 l), <- (L3 l), L2. symmetry. apply L1. }
  split; [rewrite E7low by lia; rewrite E6low by lia; rewrite <- (V3 79%positive) by lia; exact E279|].
  split; [rewrite E7low by lia; rewrite E6low by lia; rewrite <- (V3 80%positive) by lia; exact E280|].
  split; [exact E781|].
  pose proof (class_arith x Hx H16) as CA. cbv zeta in CA.
  destruct CA as (Ct & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CHPal & CPEal & _ & _ & _ & CPEHP & CHPlo & CPEhi & _).
  destruct (site_arith x Hx H16) as (_ & SQlo & _ & _ & SQPE & _). fold t in Ct.
  split.
  { unfold RM16. cbv zeta. rewrite <- Ex1. fold x. fold t. rewrite <- ET12, <- ET1.
    split; [|split; [|split; [|split]]].
    - intros a N1 N2. rewrite RM7, (RO5 a) by lia. rewrite RM34. rewrite (R2 a) by lia. symmetry. apply R1.
    - intros a Ha. rewrite RM7. apply RZ5. exact Ha.
    - intros a Ha. rewrite RM7, (RO5 (Z_to_bv 64 a)) by (rewrite u64_of_lit by lia; lia). rewrite RM34.
      destruct (HD2 a Ha) as [E1 E2]. split; intros Hm; [rewrite (E1 Hm); symmetry; apply R1 | exact (E2 Hm)].
    - intros k Hk Hnin a Ha. rewrite RM7, (RO5 (Z_to_bv 64 a)) by (rewrite u64_of_lit by (unfold LOWPG in Ha; lia); unfold LOWPG in Ha; lia). rewrite RM34.
      apply (LF2 k Hk Hnin a Ha).
    - intros k Hk Hin a Ha. rewrite RM7, (RO5 a) by (unfold LOWPG in Ha; lia). rewrite RM34. rewrite (LS2 k Hk Hin a Ha). symmetry. apply R1. }
  split.
  { unfold XF16. rewrite <- Ex1. split; [exact Hx|]. split; [exact H16|]. rewrite <- (V1 35%positive) in V35 by lia. exact V35. }
  exact Hsp7.
Qed.

Definition n17 : Z := 0xb09000.

Definition m16 (x : Z) : Model := mF.
Definition m17 (x : Z) (b10 : word) : Model := ltac2:(tb__ "0|0|
SccS66S63Vx;A1Vb10;A3").
Definition B17 : Z := B16L + n17.
Definition G17 : list (sv * Z) := G13b ++ [(SLit LOWPG, 0x4600)].

Lemma region_free_In_neq : ltac2:(tb__ "0|4|
S36S3aS15Q40M0A1M1G1A2M2A1G1G1G1G1S0S37S59R5R4R3A3S3bA3S41G2S38G1G1R3R2A4R6A3S9Z0M3S16G0R3A2A2S9G3S16G0R6A2A2S0S37Sc9G0R6R8A3S40A3F_;F_;F_;F_;Fs;Fe;Fn;Fb;Fl;").
Proof.
  clear. intros l b n e s Hf Hin Hs Hn. destruct (bv_eqb e b) eqn:E; [|reflexivity]. exfalso. apply Fs.bv_eqb_eq in E. subst e.
  pose proof (region_free_In _ _ _ _ _ Hf Hin) as OV. unfold iv_overlap in OV. apply andb_false_iff in OV.
  pose proof (urange b). pose proof (urange s). pose proof (urange n).
  destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
Qed.

Lemma m16_fields : ltac2:(tb__ "0|7|
S5S1S0S36S3aS15Q40M0A1M1G1A2M2A1M3S4aS44S63R1A1M4A1M5A1S4aS44Vm;A1M6A1A3S1S0G3S47G5A1S52S39G2S38G1G1Vb9;S14G0Z1000A2A4S47S44S79Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;A7A1A1A3Vb9;A2A3S1S0S5S4eG5A1S4eG6A1A3S1S0G1S50G5A1S50G6A1A3S1S0G3S48G4A1S48S5fA1A3S0G3S46G5A1S46S44S5fA1A1A3A2A2A2A2A2Fx;").
Proof.
  intros x. pose proof mF_vmmaps as (MR & MM & MN & ML & MI5 & MLZ). unfold m16. repeat split; assumption.
Qed.
Lemma top_m16 : ltac2:(tb__ "0|0|
S5S0S5S49S44S63R1A1A1A1S49S44Vm;A1A1A3Fx;").
Proof. intros x. pose proof (m16_fields x) as (_ & _ & _ & L4 & _). unfold alloc_top. rewrite L4. reflexivity. Qed.
Lemma init_sp_ok_m16 : ltac2:(tb__ "0|0|
S5S95S44S63R1A1A1A1Fx;").
Proof using Htop. intros x. pose proof (m16_fields x) as (_ & _ & _ & L4 & _). unfold init_sp_ok in *. rewrite L4. exact Htop. Qed.

Lemma maps16_keep : ltac2:(tb__ "0|3|
S5S15Q40M0A1M1G1S41S3aG1G1A2M2S38G1G1R2R1A4S47S44S79Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;A7A1A1A3S9Z0S16G0R2A2A2S41G2S38G1G1R4R3A4S47S44S63R5A1A1A1A3F_;F_;Fs;Fe;Fx;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. intros x e s Hin Hs. pose proof (m16_fields x) as (_ & MM & _). rewrite MM. unfold map_remove. cbn [List.filter fst].
  rewrite (proj2 (Fs.bv_eqb_eq b9 b9) eq_refl). cbn [negb]. apply filter_In. split; [exact Hin|]. cbn [fst].
  pose proof b9_facts as (_ & _ & _ & _ & _ & K4).
  rewrite (region_free_In_neq _ b9 (Z_to_bv 64 4096) e s (region_free_app_r _ _ _ _ K4) Hin Hs ltac:(rewrite u64_of_lit by lia; lia)). reflexivity.
Qed.

Lemma band_m16 : ltac2:(tb__ "0|2|
S5SacS3fS3aS15Q40A1M0G0A2S4aS44S63R1A1A1M1A1S47G1A1A3SaaSa9A3Fx;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. intros x. pose proof (m16_fields x) as (MR & MM & _). rewrite MR.
  pose proof (m13_ledger m P b4 b5 b6 b7 b8) as (L1 & L2 & _).
  apply (band_covered_transfer (vm_reserved (m_vmmaps (m13 m P b4 b5 b6 b7 b8)) ++ vm_maps (m_vmmaps (m13 m P b4 b5 b6 b7 b8)))).
  - exact (band_m13 m a1 a2 Hmaps P b4 b5 b6 b7 b8).
  - intros b s y Hin Hy Hbs. apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; rewrite <- L1; exact Hin | right].
    apply maps16_keep; [exact Hin | lia].
Qed.

Lemma blocks17 : ltac2:(tb__ "0|4|
S5S18S61R1A1S0S15Q40M0A1M1S17R2P24A2Vb7;A3S0G1S17R3P4dA2Vb8;A3S1bS5S41S3aS1bS5A2S38S1bS5R2R1A4S6cA3S4S2G1G1S2G1G1S1S41S3aG1G1A2S38G1G1R2R1A4S47S44S63RaA1A1A1A3S1S7S16G0R2A2M2S16G0S20R9R5A2A2M3A2S7S8G3R4A2S8G2S16G0R1A2A2A2A2A2Ls;A2Lb;A2S7S8S16G0S20R7R3A2A2R2A2ScbS66A1A2A2F_;Fsz;Fe;F_;F_;F_;Frho;Fx;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hres Htop Hmaps Ha1 Ha2.
  clear HBlim. intros x rho HV H36 H77 e sz Hin. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV. pose proof SB_val as SB.
  pose proof (urange P) as UP. pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB. unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB.
  pose proof (priZ_facts rho HV) as (PR1 & PR2 & PR3 & PR4).
  pose proof (m13_ledger m P b4 b5 b6 b7 b8) as (_ & L2 & _). pose proof (m12_ledger m P b4 b5 b6 b7) as (_ & O2 & _). pose proof (mE_ledger m P b4 b5 b6) as (_ & Q2 & _).
  assert (IN13 : forall e0 s0, In (e0, s0) ((b8, Z_to_bv 64 4096) :: (b7, Z_to_bv 64 4096) :: (b6, Z_to_bv 64 65536) :: (b5, Z_to_bv 64 4096) :: (b4, n9) :: (P, n7)
                                  :: vm_maps (m_vmmaps m)) -> 0 < bv_unsigned s0 -> In (e0, s0) (vm_maps (m_vmmaps (m16 x)))).
  { intros e0 s0 Hi Hs. apply maps16_keep; [|exact Hs]. rewrite L2, O2, Q2. exact Hi. }
  rewrite Hmaps in IN13.
  left.
  unfold G17, G13b, G12b, G11c in Hin. rewrite !in_app_iff in Hin. cbn [In] in Hin.
  destruct Hin as [[[[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]]]|[[= <- <-]|[]]]|[[= <- <-]|[]]]|[[= <- <-]|[]]]; cbn [eval].
  - exists a1, (Z_to_bv 64 0x10000). rewrite H27. split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|]. rewrite u64_of_lit by lia. lia.
  - exists a2, (Z_to_bv 64 0x38e000). rewrite H28. split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|]. rewrite u64_of_lit by lia. lia.
  - exists P, n7. split; [apply IN13; [cbn [In]; tauto | unfold n7; rewrite u64_of_lit by lia; lia]|].
    unfold ri30. cbn [eval]. rewrite H30. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 137438953472) with (2 ^ 37).
    rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). unfold n7. rewrite u64_of_lit by lia. lia.
  - exists (Z_to_bv 64 0x2008fff7000), (Z_to_bv 64 0xdfff0001000). split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|].
    change (eval rho shRI_base) with (pRI rho). rewrite (Upri rho HV). rewrite !u64_of_lit by lia.

    assert (HX : LIMz (x1 rho) <= 0x10007fff8000 - 1048576 + 0).
    { unfold LIMz. pose proof (Z.mod_pos_bound (x1 rho) 4096 ltac:(lia)).
      assert (x1 rho <= 0x800000000000) by (unfold x1 in *; rewrite Hv1; unfold init_sp_ok, sp_window_lo, sp_window_hi in Htop; lia).
      pose proof (Z.div_le_mono (x1 rho - x1 rho mod 4096) 0x800000000000 8 ltac:(lia) ltac:(lia)). change (0x800000000000 / 8) with 17592186044416 in *. lia. }
    lia.
  - exists b5, (Z_to_bv 64 4096). rewrite H33. split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|]. rewrite u64_of_lit by lia. lia.
  - exists b6, (Z_to_bv 64 65536). rewrite H34. split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|]. rewrite u64_of_lit by lia. lia.
  - exists b7, (Z_to_bv 64 4096). rewrite H36. split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|]. rewrite u64_of_lit by lia. lia.
  - exists b8, (Z_to_bv 64 4096). rewrite H77. split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|]. rewrite u64_of_lit by lia. lia.
  - exists (Z_to_bv 64 0x7fff7000), (Z_to_bv 64 0x10000000). split; [apply IN13; [cbn [In]; tauto | rewrite u64_of_lit by lia; lia]|].
    unfold LOWPG. rewrite !u64_of_lit by lia. lia.
Qed.

Lemma clear17 : ltac2:(tb__ "0|0|
S0S37Sb7S6cS97SadA1A2S3bA3").
Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Post17 (rho : valuation) (x : Z) (tp : list word) : assn := ltac2:(tb__ "0|3|
S9bS2S15Q40M0A1M1G1S2S18S18S1S94S14G0Z0A2S63Vx;A1S14G0S66A2R2A4S1Sb6P53M2Vrho;R1A3S1S0G1S17R1G2A2R2A3S1G1S0S3dS15Q8A1A1S19R2R1A2S19Vrho;R1A2A3Fa;S5aS35S75S71Vx;R2A2S6bA2SbfR1Vtp;R3A6A2A2A2A2Lrho';A2Lb10;A2Lw;").

Theorem seg17 : ltac2:(tb__ "0|1|
S18S36S15Q40A1M0A1S61R2A1S0G0S17R3P24A2Vb7;A3S0G0S17R4P4dA2Vb8;A3S0G0S17R5P4eA2Vb9;A3S60R6A1S5S9dS35Vok;S5aS35S75S63R1A1S62A2SadR7R6A5S6eR7R1R6A3A4Tx;F_;F_;F_;F_;Ftp;Frho;").
Proof using All.
  intros rho tp HV H36 H77 H78 x.
  pose proof (m16_fields x) as (MR & MM & ML & MB & _).
  eapply triple_seq.
  { apply triple1_triple.
    apply (eager_rw_node ok OKF OKP E_s17 n17 (m16 x) B16L G17 84%positive).
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
    + exact clear17.
    + rewrite MR. exact Hres.
    + exact (init_sp_ok_m16 x).
    + exact (band_m16 x).
    + rewrite ML. unfold B16L, B16, BF, B12x, B12, B11, n17. lia.
    + exact (blocks17 x rho HV H36 H77).
    + rewrite MB. destruct HV as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1'). exact Hv1'. }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA (m16 x) B16L) (OKFx _ _) (fun n => stableA_KxA segsA n (m16 x) B16L) _ SPIN17 300%nat SPIN_MMAPORDIE);
      [reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact run17_fail | exact spin17].
  - apply triple_ex; intros b10. apply triple_pure; intros HPL10.
    eapply triple_seq.
    { apply triple1_triple.
      assert (N : ss_next (ax_S E_s17) = 83%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      change (eager_ok E_s17 n17 84) with S_s17ok. rewrite N.
      eapply sym_run_soundA; [exact run17b | apply OKFx | reflexivity | apply stableA_KxA]. }
    eapply triple_conseq; [intros w Hw; exact Hw | | apply triple_refl].
    intros w Hw. apply (proj1 (LQA1 _ _ _ _ _ w)) in Hw as (rho2 & Hag2 & Hsp2).
    replace (ss_next (ax_S S_s17ok)) with 84%positive in Hag2 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). pose proof Hag2 as (V2 & L2 & R2).
    exists b10, rho2. split; [exact HPL10|]. split.
    { split; [intros i Hi | intros l].
      - rewrite <- (V2 i) by lia. rewrite rho_set_rw_other by lia. reflexivity.
      - rewrite <- (L2 l). reflexivity. }
    split; [rewrite <- (V2 83%positive) by lia; apply rho_set_rw_at|].
    split; [intros a; rewrite <- (R2 a); reflexivity|].
    unfold m17, B17. exact Hsp2.
Qed.

Definition RM6 (rho rho' : valuation) : Prop := RM16 rho rho'.

Definition Post6 (rho : valuation) : assn := ltac2:(tb__ "0|3|
S9bS60Vrho;A1S5S2S15Q40M0A1M1G1S2S18S18S1S94S14G0Z0A2S63R3A1S14G0S66A2R2A4S1Sb6P4fM2Vrho;R1A3S1S0G1S17R1G2A2S14G0S84R3A1A2A3S1S0G1S17R1P50A2S14G0S81R3A1A2A3S1S0G1S17R1P51A2S14G0S86R3A1A2A3S1S0G1S17R1P53A2R2A3S1S74Vrho;R1A2S1Sb9Vrho;R1A2S1S70Vrho;A1S5aS35S75S71R3R2A2S6bA2SbfR1S6aVrho;A1R4A6A2A2A2A2A2A2A2A2A2Lrho';A2Lb10;A2Tx;Lw;").

Theorem start6_sum_A : ltac2:(tb__ "0|1|
S18S61R1A1S0S15Q40A1M0S17R2P24A2Vb7;A3S0G0S17R3P4dA2Vb8;A3S0G0S17R4P4eA2Vb9;A3S78R5A1S9eR6A1Sb9R7R7A2S9dS35Vok;S5aS35S75S5fS65A2Sb5R8S77R8A1A5S6fR8A1A4F_;F_;F_;F_;F_;F_;F_;Frho;").
Proof using All.
  intros rho HV H36 H77 H78 Hz HZ11 _.
  eapply triple_seq; [exact (seg16 rho HV H36 H77 H78 Hz HZ11)|].
  unfold Post16. cbv zeta. apply triple_ex; intros rhoA. apply triple_pure; intros HagA. apply triple_pure; intros E79. apply triple_pure; intros E80.
  apply triple_pure; intros E81. apply triple_pure; intros RMA. apply triple_pure; intros XF. pose proof XF as (HxA & H16A & V35).
  pose proof HagA as [VA LA].
  assert (ExA : x1 rhoA = x1 rho) by (unfold x1; rewrite (VA 1%positive) by lia; reflexivity).
  assert (HVA : vals rhoA) by (unfold vals; eapply (vals12_agree _ _ _ _ _ _ _ 79%positive rho rhoA); [lia | exact HV | exact VA]).
  assert (H36A : rw rhoA 36%positive = b7) by (rewrite (VA 36%positive) by lia; exact H36).
  assert (H77A : rw rhoA 77%positive = b8) by (rewrite (VA 77%positive) by lia; exact H77).
  assert (H78A : rw rhoA 78%positive = b9) by (rewrite (VA 78%positive) by lia; exact H78).
  pose proof (class_arith (x1 rho) HxA H16A) as CA. cbv zeta in CA.
  destruct CA as (Ct & C79al & C80x8 & C80al & C80nn & C79lo & C79hi & Ctop1 & Ctop2 & Ctopal & Ctoplo & Cand & CHPal & CPEal & CPBal & CPB & CLEN & CPEHP & CHPlo & CPEhi & CPEe & CHPq & Ce12al & CLIM & CLIM0).
  change (KxA mF B16L) with (KxA (m16 (x1 rhoA)) B16L).
  eapply triple_conseq; [intros w Hw; exact Hw | | apply (seg17 rhoA (TP17 rho) HVA H36A H77A H78A)].
  intros w (b10 & rho' & HPL10 & Hag' & E83 & Hrm' & Hsp'). unfold Post6. cbv zeta. rewrite ExA in HPL10, Hsp'.
  exists b10, rho'. pose proof Hag' as [V' L'].
  split; [exact HPL10|].
  split; [split; [intros i Hi; rewrite (V' i) by lia; apply VA; exact Hi | intros l; rewrite (L' l); apply LA]|].
  split; [rewrite (V' 79%positive) by lia; exact E79|].
  split; [rewrite (V' 80%positive) by lia; exact E80|].
  split; [rewrite (V' 81%positive) by lia; exact E81|].
  split; [exact E83|].
  pose proof RMA as (RM1 & RM2 & RM3 & RM4 & RM5). cbv zeta in RM1.
  split.
  { unfold RM6, RM16. cbv zeta. split; [|split; [|split; [|split]]].
    - intros a N1 N2. rewrite Hrm'. exact (RM1 a N1 N2).
    - intros a Ha. rewrite Hrm'. exact (RM2 a Ha).
    - intros a Ha. rewrite Hrm'. exact (RM3 a Ha).
    - intros k Hk Hnin a Ha. rewrite Hrm'. exact (RM4 k Hk Hnin a Ha).
    - intros k Hk Hin a Ha. rewrite Hrm'. exact (RM5 k Hk Hin a Ha). }
  split.
  {
    intros a [Ha _].
    assert (Hhi : PEz (x1 rho) + 4096 <= bv_unsigned (rw rho 1%positive)) by (clear -CPEhi HxA; unfold x1 in *; lia).
    rewrite Hrm'. apply RM1; [clear -Ha Hhi Ct; lia | clear -Ha Hhi CHPlo CPEHP; unfold LOWPG; lia]. }
  split; [exact XF|].
  exact Hsp'.
Qed.

Hypothesis Hwit17 : ltac2:(tb__ "0|2|
S5S2S15Q40M0A1M1G1S94S14G0Z0A2S63R2A1S14G0S66A2R1A4La;A2Fx;").

Lemma erun16 : ltac2:(tb__ "0|1|
S5S18S36S15Q40A1A1S41S5R3S8cA3S9cS35S5aS35S75S5fS62A2M0SbdS8eR4A1A1R3R2A5S5bS35G0P51R3R2S39S98S99SaeR4A1Sb8A2S3cS98A1A3A6A3F_;Ftp;Frho;Ft;").
Proof.
  intros t rho tp Ht. destruct (cls16 t Ht) as (RUN & _). eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact RUN].
Qed.

Lemma ecall16 : ltac2:(tb__ "0|1|
S5S18S36S15Q40A1A1S41S5R3S8cA3S9cS35S5aS35S75S5fS62A2M0SaeR4A1R3R2A5S9bS2S18S18S1S26P51R5R1A3S5aS35G0Sb1R6A1R1R4R2A6A2Lrho';A2Lw;A3F_;Ftp;Frho;Ft;").
Proof.
  intros t rho tp Ht. destruct (cls16 t Ht) as (_ & FR & CC & IPE & NX & _).
  apply (ecall_pureA segsA (M16_of t) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.Pre_mszA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.Posts_mszA (s16_of t) (R16_of t) mF B16L tp rho _ FR CC).
  - intros J rho1 tp1 HstJ. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.memsetZ_sumA_ex J HstJ rho1 tp1).
  - intros L rho' [<-|[]] Hag. cbn [la_state]. rewrite NX in Hag. rewrite IPE.
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply etriple_refl].
    exists rho'. split; [exact Hag | exact Hw].
Qed.

Lemma erun17x : ltac2:(tb__ "0|1|
S5S18S36S15Q40A1A1S41S5R3S8cA3S9cS35S5aS35S75S5fS62A2M0Sb2R4A1R3R2A5S5bS35G0P79R3R2S39S98S99Sb0R4A1Sb8A2S3cS98A1A3A6A3F_;Ftp;Frho;Ft;").
Proof.
  intros t rho tp Ht. destruct (cls16 t Ht) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RUN & _).
  pose proof (fun H1 H2 => sym_run_etripleA segsA _ _ _ _ (KxA mF B16L) rho tp H1 H2 RUN) as S.
  replace (ss_next (ax_S (IPr_of t))) with 121%positive in S; [apply S; [|apply stableA_KxA]|].
  - destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; reflexivity.
  - destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Theorem eseg16 : ltac2:(tb__ "0|1|
S18S61R1A1S0S15Q40A1M0S17R2P24A2Vb7;A3S0G0S17R3P4dA2Vb8;A3S0G0S17R4P4eA2Vb9;A3S78R5A1S9eR6A1S9cS35S5aS35S75S5fS65A2Sb5R7S77R7A1A5S6dR7A1A3F_;F_;F_;F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hlz Hmaps Hna Hres Htop.
  intros rho HV H36 H77 H78 Hz HZ11.

  eapply etriple_seq.
  { eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run15b]. }
  apply etriple_ex; intros L. apply etriple_ex; intros rho1. apply etriple_pure; intros HinL. apply etriple_pure; intros Hag1.
  destruct HinL as [<-|[]]. cbn [la_state]. replace (ss_next (ax_S S_s15ok)) with 79%positive in Hag1 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof Hag1 as (V1 & L1 & R1).
  assert (AV1 : agree_vars 79 rho rho1) by (split; [intros i Hi; symmetry; apply V1; exact Hi | intros l; symmetry; apply L1]).
  assert (HV1 : vals rho1) by (eapply (vals12_agree _ _ _ _ _ _ _ 79%positive rho rho1); [lia | exact HV | exact (proj1 AV1)]).
  assert (H36a : rw rho1 36%positive = b7) by (rewrite <- (V1 36%positive) by lia; exact H36).
  assert (H77a : rw rho1 77%positive = b8) by (rewrite <- (V1 77%positive) by lia; exact H77).
  assert (H78a : rw rho1 78%positive = b9) by (rewrite <- (V1 78%positive) by lia; exact H78).
  assert (Hz1 : stackshadow_zero rho1) by (apply (stackshadow_zero_ext rho rho1); [symmetry; apply V1; lia | intros a; symmetry; apply R1 | exact Hz]).
  assert (HZ1 : Z11 rho1) by (apply (Z11_ext rho rho1); [symmetry; apply V1; lia | symmetry; apply V1; lia | intros a; symmetry; apply R1 | exact HZ11]).
  assert (Ex1 : x1 rho1 = x1 rho) by (unfold x1; rewrite <- (V1 1%positive) by lia; reflexivity).
  assert (ET1 : TP16 rho1 = TP16 rho) by (apply TP16_ext; eapply agree_vars_le; [|exact AV1]; lia).
  assert (ET17 : TP17 rho1 = TP17 rho) by (unfold TP17; rewrite ET1; reflexivity).
  assert (ET12 : TP12 rho1 = TP12 rho) by (apply TP12_agree; eapply agree_vars_le; [|exact AV1]; lia).
  rewrite <- ET12.

  apply etriple_factsA. intros HF1. destruct (x1_facts rho1 HF1) as [Hx H16].
  eapply etriple_conseq; [intros w Hw; exact (prep16 rho1 w HV1 H36a H77a H78a Hz1 HZ1 Hw) | intros w Hw; exact Hw |].
  cbv zeta. apply etriple_ex; intros rho2. apply etriple_pure; intros E2low. apply etriple_pure; intros E279. apply etriple_pure; intros E280.
  apply etriple_pure; intros L2. apply etriple_pure; intros R2. apply etriple_pure; intros Z2. apply etriple_pure; intros HD2.
  apply etriple_pure; intros LF2. apply etriple_pure; intros LS2. apply etriple_pure; intros V35.
  set (x := x1 rho1) in *. set (t := tcls x) in *.
  assert (Ht : In t classes16).
  { pose proof (Z.mod_pos_bound (Tq x) 8 ltac:(lia)) as M8. unfold classes16. cbn [In]. subst t. unfold tcls. lia. }
  rewrite ET17.

  eapply etriple_conseq; [intros w Hw; exact (SPA_X0 (KxA mF B16L) rho2 (R16c t) (TP17 rho) w eq_refl Hw) | intros w Hw; exact Hw |].
  eapply etriple_seq; [apply (erun16 t rho2 (TP17 rho) Ht)|].
  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho3. apply etriple_pure; intros Hag3. pose proof Hag3 as (V3 & L3 & R3).
  assert (Ex3 : x1 rho3 = x) by (unfold x1; rewrite <- (V3 1%positive) by lia; rewrite E2low by lia; reflexivity).

  apply etriple_factsA. intros HF3.
  eapply etriple_seq; [apply (ecall16 t rho3 (TP17 rho) Ht)|].
  apply etriple_ex; intros rho4. apply etriple_pure; intros Hag4. pose proof Hag4 as (V4 & L4 & R4).

  eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw |].
  { apply (unshape16 t rho3 rho4 (TP17 rho) w Ht); rewrite ?Ex3; [subst t; reflexivity | exact Hx | exact H16 | exact Hag4 | | exact HF3 | exact Hw].
    rewrite <- (V3 80%positive) by lia. exact E280. }
  cbv zeta. rewrite Ex3. apply etriple_ex; intros rho5. apply etriple_pure; intros RW5. apply etriple_pure; intros RL5.
  apply etriple_pure; intros RO5. apply etriple_pure; intros RZ5.

  eapply etriple_seq; [apply (erun17x t rho5 (TP17 rho) Ht)|].
  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho6. apply etriple_pure; intros Hag6. pose proof Hag6 as (V6 & L6 & R6).
  assert (E6low : forall i, (i < 81)%positive -> rw rho6 i = rw rho3 i).
  { intros i Hi. rewrite <- (V6 i) by lia. rewrite RW5. symmetry. apply V4. exact Hi. }
  assert (Ex6 : x1 rho6 = x) by (unfold x1; rewrite E6low by lia; exact Ex3).

  eapply etriple_conseq; [intros w Hw | | apply etriple_refl].
  { apply (join17 t rho6 (TP17 rho) w Ht); rewrite ?Ex6; [subst t; reflexivity | exact Hx | exact H16 | | | exact Hw].
    - rewrite E6low by lia. rewrite <- (V3 79%positive) by lia. exact E279.
    - rewrite E6low by lia. rewrite <- (V3 80%positive) by lia. exact E280. }
  cbv zeta. rewrite Ex6. intros w (rho7 & E7low & E781 & L7 & R7 & Hsp7).

  unfold Post16. cbv zeta. rewrite <- Ex1. fold x. exists rho7.
  assert (E7 : forall i, (i < 79)%positive -> rw rho7 i = rw rho1 i).
  { intros i Hi. rewrite E7low by lia. rewrite E6low by lia. rewrite <- (V3 i) by lia. apply E2low. exact Hi. }
  assert (RM7 : forall a, rm rho7 a = rm rho5 a) by (intros a; rewrite R7, <- (R6 a); reflexivity).
  assert (RM34 : forall a, rm rho4 a = rm rho2 a) by (intros a; rewrite <- (R4 a), <- (R3 a); reflexivity).
  split.
  { split; [intros i Hi; rewrite E7 by lia; symmetry; apply V1; lia|].
    intros l. rewrite L7, <- (L6 l), RL5, <- (L4 l), <- (L3 l), L2. symmetry. apply L1. }
  split; [rewrite E7low by lia; rewrite E6low by lia; rewrite <- (V3 79%positive) by lia; exact E279|].
  split; [rewrite E7low by lia; rewrite E6low by lia; rewrite <- (V3 80%positive) by lia; exact E280|].
  split; [exact E781|].
  pose proof (class_arith x Hx H16) as CA. cbv zeta in CA.
  destruct CA as (Ct & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CHPal & CPEal & _ & _ & _ & CPEHP & CHPlo & CPEhi & _).
  destruct (site_arith x Hx H16) as (_ & SQlo & _ & _ & SQPE & _). fold t in Ct.
  split.
  { unfold RM16. cbv zeta. rewrite <- Ex1. fold x. fold t. rewrite <- ET12, <- ET1.
    split; [|split; [|split; [|split]]].
    - intros a N1 N2. rewrite RM7, (RO5 a) by lia. rewrite RM34. rewrite (R2 a) by lia. symmetry. apply R1.
    - intros a Ha. rewrite RM7. apply RZ5. exact Ha.
    - intros a Ha. rewrite RM7, (RO5 (Z_to_bv 64 a)) by (rewrite u64_of_lit by lia; lia). rewrite RM34.
      destruct (HD2 a Ha) as [E1 E2]. split; intros Hm; [rewrite (E1 Hm); symmetry; apply R1 | exact (E2 Hm)].
    - intros k Hk Hnin a Ha. rewrite RM7, (RO5 (Z_to_bv 64 a)) by (rewrite u64_of_lit by (unfold LOWPG in Ha; lia); unfold LOWPG in Ha; lia). rewrite RM34.
      apply (LF2 k Hk Hnin a Ha).
    - intros k Hk Hin a Ha. rewrite RM7, (RO5 a) by (unfold LOWPG in Ha; lia). rewrite RM34. rewrite (LS2 k Hk Hin a Ha). symmetry. apply R1. }
  split.
  { unfold XF16. rewrite <- Ex1. split; [exact Hx|]. split; [exact H16|]. rewrite <- (V1 35%positive) in V35 by lia. exact V35. }
  exact Hsp7.
Qed.

Theorem eseg17 : ltac2:(tb__ "0|1|
S18S36S15Q40A1M0A1S61R2A1S0G0S17R3P24A2Vb7;A3S0G0S17R4P4dA2Vb8;A3S0G0S17R5P4eA2Vb9;A3S60R6A1S5S9cS35S5aS35S75S63R1A1S62A2SadR7R6A5S6eR7R1R6A3A3Tx;F_;F_;F_;F_;Ftp;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hlz Hmaps Hna Hres Htop Hwit17.
  intros rho tp HV H36 H77 H78 x.
  pose proof (m16_fields x) as (MR & MM & ML & MB & _).
  eapply etriple_seq.
  { apply (eager_rw_enode E_s17 n17 (m16 x) B16L G17 84%positive).
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
    + exact clear17.
    + rewrite MR. exact Hres.
    + exact (init_sp_ok_m16 x).
    + exact (band_m16 x).
    + rewrite ML. unfold B16L, B16, BF, B12x, B12, B11, n17. lia.
    + exact (Hwit17 x).
    + exact (blocks17 x rho HV H36 H77).
    + rewrite MB. destruct HV as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1'). exact Hv1'. }
  - apply etriple_ex; intros b10. apply etriple_pure; intros HPL10.
    eapply etriple_seq.
    { assert (N : ss_next (ax_S E_s17) = 83%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
      change (eager_ok E_s17 n17 84) with S_s17ok. rewrite N.
      eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run17b]. }
    eapply etriple_conseq; [intros w Hw; exact Hw | | apply etriple_refl].
    intros w Hw. apply (proj1 (LQA1 _ _ _ _ _ w)) in Hw as (rho2 & Hag2 & Hsp2).
    replace (ss_next (ax_S S_s17ok)) with 84%positive in Hag2 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). pose proof Hag2 as (V2 & L2 & R2).
    exists b10, rho2. split; [exact HPL10|]. split.
    { split; [intros i Hi | intros l].
      - rewrite <- (V2 i) by lia. rewrite rho_set_rw_other by lia. reflexivity.
      - rewrite <- (L2 l). reflexivity. }
    split; [rewrite <- (V2 83%positive) by lia; apply rho_set_rw_at|].
    split; [intros a; rewrite <- (R2 a); reflexivity|].
    unfold m17, B17. exact Hsp2.
Qed.

Theorem start6_sum_ex_A : ltac2:(tb__ "0|1|
S18S61R1A1S0S15Q40A1M0S17R2P24A2Vb7;A3S0G0S17R3P4dA2Vb8;A3S0G0S17R4P4eA2Vb9;A3S78R5A1S9eR6A1Sb9R7R7A2S9cS35S5aS35S75S5fS65A2Sb5R8S77R8A1A5S6fR8A1A3F_;F_;F_;F_;F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hlz Hmaps Hna Hres Htop Hwit17.
  intros rho HV H36 H77 H78 Hz HZ11 _.
  eapply etriple_seq; [exact (eseg16 rho HV H36 H77 H78 Hz HZ11)|].
  unfold Post16. cbv zeta. apply etriple_ex; intros rhoA. apply etriple_pure; intros HagA. apply etriple_pure; intros E79. apply etriple_pure; intros E80.
  apply etriple_pure; intros E81. apply etriple_pure; intros RMA. apply etriple_pure; intros XF. pose proof XF as (HxA & H16A & V35).
  pose proof HagA as [VA LA].
  assert (ExA : x1 rhoA = x1 rho) by (unfold x1; rewrite (VA 1%positive) by lia; reflexivity).
  assert (HVA : vals rhoA) by (unfold vals; eapply (vals12_agree _ _ _ _ _ _ _ 79%positive rho rhoA); [lia | exact HV | exact VA]).
  assert (H36A : rw rhoA 36%positive = b7) by (rewrite (VA 36%positive) by lia; exact H36).
  assert (H77A : rw rhoA 77%positive = b8) by (rewrite (VA 77%positive) by lia; exact H77).
  assert (H78A : rw rhoA 78%positive = b9) by (rewrite (VA 78%positive) by lia; exact H78).
  pose proof (class_arith (x1 rho) HxA H16A) as CA. cbv zeta in CA.
  destruct CA as (Ct & C79al & C80x8 & C80al & C80nn & C79lo & C79hi & Ctop1 & Ctop2 & Ctopal & Ctoplo & Cand & CHPal & CPEal & CPBal & CPB & CLEN & CPEHP & CHPlo & CPEhi & CPEe & CHPq & Ce12al & CLIM & CLIM0).
  change (KxA mF B16L) with (KxA (m16 (x1 rhoA)) B16L).
  eapply etriple_conseq; [intros w Hw; exact Hw | | apply (eseg17 rhoA (TP17 rho) HVA H36A H77A H78A)].
  intros w (b10 & rho' & HPL10 & Hag' & E83 & Hrm' & Hsp'). unfold Post6. cbv zeta. rewrite ExA in HPL10, Hsp'.
  exists b10, rho'. pose proof Hag' as [V' L'].
  split; [exact HPL10|].
  split; [split; [intros i Hi; rewrite (V' i) by lia; apply VA; exact Hi | intros l; rewrite (L' l); apply LA]|].
  split; [rewrite (V' 79%positive) by lia; exact E79|].
  split; [rewrite (V' 80%positive) by lia; exact E80|].
  split; [rewrite (V' 81%positive) by lia; exact E81|].
  split; [exact E83|].
  pose proof RMA as (RM1 & RM2 & RM3 & RM4 & RM5). cbv zeta in RM1.
  split.
  { unfold RM6, RM16. cbv zeta. split; [|split; [|split; [|split]]].
    - intros a N1 N2. rewrite Hrm'. exact (RM1 a N1 N2).
    - intros a Ha. rewrite Hrm'. exact (RM2 a Ha).
    - intros a Ha. rewrite Hrm'. exact (RM3 a Ha).
    - intros k Hk Hnin a Ha. rewrite Hrm'. exact (RM4 k Hk Hnin a Ha).
    - intros k Hk Hin a Ha. rewrite Hrm'. exact (RM5 k Hk Hin a Ha). }
  split.
  {
    intros a [Ha _].
    assert (Hhi : PEz (x1 rho) + 4096 <= bv_unsigned (rw rho 1%positive)) by (clear -CPEhi HxA; unfold x1 in *; lia).
    rewrite Hrm'. apply RM1; [clear -Ha Hhi Ct; lia | clear -Ha Hhi CHPlo CPEHP; unfold LOWPG; lia]. }
  split; [exact XF|].
  exact Hsp'.
Qed.

End Seg6.
End Start6.

(* [comment removed for export] *)
Module DrvR_tstates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "la_state"; "xr_eqb"; "mkLeafA"; "ax_setS"; "la_reason"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nat"; "option"; "Some"; "true"; "prod"; "bool"; "nil"; "pair"; "length"; "app"; "false"; "andb"; "negb"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "sv"; "ss_objs"; "sstate"; "sprop"; "sv_eqb"; "SAlu"; "ss_facts"; "ss_next"; "ss_pc"; "SPBranch"; "SPNot"; "mkSS"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "set_objs"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvR_tstates"; "selA"; "x4set"; "splitA"; "x4_okb"; "pcs"; "app_objs"; "fw_rtc"; "fw_u2"; "fw_u1"; "fw_undo1"; "E_oom"; "E_ov1"; "E_ref"; "E_sh0"; "E_sh1"; "E_shZ"; "U_ov1"; "U_ref"; "U_sh0"; "U_sh1"; "U_shZ"; "fw_undo2L"; "mergeA"; "CF_ov1"; "CF_sh0"; "CF_sh1"; "CF_shZ"; "C_oom"; "C_ov1"; "C_ref"; "C_sh0"; "C_sh1"; "C_shZ"; "T_oom"; "T_ov1"; "T_ref"; "T_sh0"; "T_sh1"; "T_shZ"; "U_oom"; "V_ov1"; "V_sh0"; "V_sh1"; "V_shZ"; "addX"; "fb_siteR"; "fw_siteL"; "RF_ov1"; "RF_sh0"; "RF_sh1"; "RF_shZ"; "R_oom"; "R_ov1"; "R_ref"; "R_sh0"; "R_sh1"; "R_shZ"; "V_oom"; "V_ref"; "exS_idxs"; "ex_carvedR"; "ex_img"; "fp_rtc"; "sF_ov1"; "sF_sh0"; "sF_sh1"; "sF_shZ"; "s_oom"; "s_ov1"; "s_ref"; "s_sh0"; "s_sh1"; "s_shZ"; "LV_fov1"; "LV_fsh0"; "LV_fsh1"; "LV_fshZ"; "LV_xoom"; "LV_xov1"; "LV_xref"; "LV_xsh0"; "LV_xsh1"; "LV_xshZ"; "TF_ov1"; "TF_sh0"; "TF_sh1"; "TF_shZ"; "W_ov1"; "W_sh0"; "W_sh1"; "W_shZ"; "exS_rb"; "ex_fin"; "ex_img_okb"; "ex_okb"; "firstA"; "fp_hints"; "fp_u1"; "fp_u2"; "s_exR"; "CX_oom"; "CX_ov1"; "CX_ref"; "CX_sh0"; "CX_sh1"; "CX_shZ"; "F_ov1"; "F_sh0"; "F_sh1"; "F_shZ"; "X_oom"; "X_ov1"; "X_ref"; "X_sh0"; "X_sh1"; "X_shZ"; "ex_siteD"; "ex_siteS"; "fp_site"; "fp_undo1"; "fp_undo2"; "fw_siteM"; "fw_undo2M"; "ms16_at"; "s_fpc"; "x4d_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXRebase"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface"; "Pre_fw"; "xblk"; "P_fw"; "Posts_fw"; "EBUF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.DrvR_states"; "CUTS_R"; "T_after"; "ax_of"; "optS"; "Loom"; "Lov1"; "Lref"; "Lsh0"; "Lsh1"; "LshZ"; "has_tpfact"; "optR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "PreF"; "vTP"; "PostF"; "locate"; "DEEP"; "sp0"; "vCap"; "dropX"; "spM"; "vB"; "s_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "TP"; "free_stub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@Corelib.Lists.ListDef"; "map"; "seq"; "firstn"; "@Stdlib.Lists.List"; "existsb"; "In"; "flat_map"; "forallb"; "@Corelib.Init.Nat"; "sub";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "exit_entry"; "FERR"; "Pre_exit0"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "add"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface"; "Pre_ref"; "P_ref"; "Posts_ref"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_OR"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR"; "CAP0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf"; "O_realm"; "O_rtc3w"; "ms16"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sprop_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "img_cell_apply"; "img_cell_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform DrvGlueA DrvGlueB SysStepA SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_hdr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.HandoffMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.DrvR_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr TAddr RAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition app_objs (l : list sobj) (A : axst) : axst := ltac2:(tb__ "0|1|
SaVA;S35S3VA;A1M0S17S1cS1fG0A1Vl;A3A2A2").

Definition addX (r : sv * sv) (A : axst) : axst := ltac2:(tb__ "0|2|
S13S2L_;SdfS12S1eS1eA2M0S8Vr;A1S6VA;A1M1A3VA;SefVA;ScG0Vr;G1A3A2X13x2").
Definition selA (idxs : list nat) (A : axst) : axst := ltac2:(tb__ "0|1|
SaVA;S35S3VA;A1M0Sf9S1fG0A1Vidxs;A2A2A2").
Definition firstA (n : nat) (A : axst) : axst := ltac2:(tb__ "0|1|
SaVA;S35S3VA;A1M0SdeS1cVn;S1fG0A1A3A2A2").
Definition mergeA (i : nat) (A : axst) : axst := ltac2:(tb__ "0|0|
Sc1VA;SdbS3VA;A1Vi;A2A2").
Definition splitA (i : nat) (mid : sv) (A : axst) : axst := ltac2:(tb__ "0|0|
Sc1VA;SdaS3VA;A1Vi;Vmid;A3A2").
Definition pcs (l : list leafA) : ltac2:(tb__ "0|0|
SdS12S31S33A2A1") := ltac2:(tb__ "0|0|
SdcS4S12S31S33A2S4S15S31S33S26S3S7R1A1A1A1SbR1A1A4LL;Vl;A4").

Definition x4set (e : sv) (A : axst) : axst := ltac2:(tb__ "0|0|
S3VA;A1S20SaVA;S29S26R1A1S36S1eS2eR1A1U4Ve;A4S2cR1A1S2bR1A1S2fR1A1S1fR1A1S24R1A1S25R1A1S2dR1A1A9A2TS;").
Definition x4d_okb (d : list (sv * sv)) : bool := ltac2:(tb__ "0|3|
SdS12S1eS1eA2M0A1M1S13Ld;Vd;S11G0G1G0S13Lp;R2S1eS1eG1S13Ll;R3S1bS19S22R2ScbA2S22R1S1dSd5A1M2A2A2S19S22R2G2A2S22R1ScbA2A2A2G0G1S18Ll0;Lp0;Xdx2Lb;La;X12x1Ll;Lp;Xdx2").
Definition x4_okb (A : axst) (e : sv) : bool := ltac2:(tb__ "0|4|
S19S19S30S3S38Ve;VA;A2A1M0A1SfS12SdS12S1eS1eA2A1M1SdS21A1M2A2M3A1S13Lx;Sf8S3VA;A1G0A2G3G3S13Lp;R1G1G2G2S13Ll;R1Sb4R2A1S21G2S18Ll0;Ls;Xdx2Ll;Ld;X12x1Lp;S18Xfx2A2Sc8VA;A1A2").

Definition fw_rtc : list sobj := [O_rtc3w].
Definition fw_siteL (msg len : Z) (E : axst) : axst := ltac2:(tb__ "0|0|
S63SbaVmsg;Vlen;A2S3cS3dS39U0S1dN9e0A1S38S1dSd5A1VE;A2A3A2A2").
Definition fw_siteM (msg len : Z) (E : axst) : axst := ltac2:(tb__ "0|0|
S63SbaVmsg;Vlen;A2S3cS3dS39U0S1dN960A1S38S1dSd5A1VE;A2A3A2A2").
Definition s_fwc (msg len : Z) (C : axst) : wsub := ltac2:(tb__ "0|0|
SeeP1S3VC;A1S3Sb9Vmsg;Vlen;A2A1A3").

Definition fw_u1 (n : nat) : list nat := ltac2:(tb__ "0|2|
S17SeScSeU0ScSeU1S14SeA1M0A3A3S17SeSddU3M1Se3Vn;G1A2A2ScSeU2G0A3A3A3").
Definition fw_undo1 (T : axst) : axst := ltac2:(tb__ "0|0|
S16S1cS1fS3VT;A1A1A2SeS96Se3R1U1A2S37S3fR1A1VT;A2A2Tn;").
Definition fw_u2 (n : nat) : list nat := ltac2:(tb__ "0|1|
S17SeScSeU6ScSeU0S14SeA1A3A3S17SeSddU1U5A2SddU7M0Se3Vn;G0A2A2A3A3").
Definition fw_undo2L (U : axst) : axst := ltac2:(tb__ "0|1|
S16S1cS1fS3VU;A1A1A2SeS4dU0M0S37S3eR1A1Sc0Sb7VU;ScSb5Sb6G0A1S14Sb5A1A3A2VU;A2A2A2Tn;").
Definition fw_undo2M (U : axst) : axst := ltac2:(tb__ "0|0|
S16S1cS1fS3VU;A1A1A2SeS4dU0S37S3eR1A1VU;A2A2Tn;").

Definition E_oom : axst := Eval vm_compute in nthA G_cut LV_oom 0.
Lemma run_oom1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeSc2S11A5S10G0ScS4S9S41S34A2S14S4A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_oom : axst := Eval vm_compute in fw_siteM 0x14d9d 19 E_oom.
Lemma oom_pipe : ltac2:(tb__ "0|6|
S1S0S13S3aS41S1dSd5A1M0A2S11A3S1S0SfS20A1SdaS3S38G0S41A2M1A1U0M2S1dN960A1M3A3S10S20S3S39G2G3G1A3A1A2A3S1S0S13SdfS12S1eS1eA2S8SbaZ14d9dM4Z13M5A2A1S6S41A1A3S11A3S0S2Sb0G4G5S41A3S52A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_oom : wsub := Eval vm_compute in s_fwc 0x14d9d 19 C_oom.
Definition R_oom : list sobj := Eval vm_compute in optR (entails_frA C_oom (Pre_fw 0x14d9d 19) s_oom).
Lemma fr_oom : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S52Sb9Z14d9dZ13A2S7aA3S10G0S6aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_oom : ltac2:(tb__ "0|0|
S0S13Sd8S52Sb9Z14d9dZ13A2S7aS6aSdcS4S2S7SbcA4A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_oom : axst := Eval vm_compute in T_after (Pre_fw 0x14d9d 19) C_oom s_oom R_oom P_fw.
Definition U_oom : axst := Eval vm_compute in fw_undo1 T_oom.
Definition V_oom : axst := Eval vm_compute in fw_undo2M U_oom.
Lemma T_oom_eqs : ltac2:(tb__ "0|1|
S1S0S2SbfSb9Z14d9dZ13A2S52S7aS6aSbbA5S58A3S1S0S2S40S58A1S5eA3S1S0SdS1cA1S1fS3S37S3fS16S1cS1fS3S58A1A1A2A1S58A2A1A1S17S1cS1fS3S5eA1A1M0S3dA3A3S1S0SfS20A1SdbS3S37S3eS16S1cG0A2A1S5eA2A1U0A2S10S20S3S70A1A2A3S0S2Sb1S5eA1S70A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition LV_xoom : list leafA := Eval vm_compute in runR 20 V_oom.
Lemma run_xoom : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeS70S11A5S10G0S84A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_xoom_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS84A1ScG0S15S31S33Se4S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_oom : axst := Eval vm_compute in nthA V_oom LV_xoom 0.

Definition fp_rtc : list sobj := ltac2:(tb__ "0|0|
ScS1cSf6ScS1cSf5S14S1cA1A3A3").
Definition s_fpc (C : axst) : wsub := ltac2:(tb__ "0|0|
SeeP1S3VC;A1S3SebA1A3").
Definition fp_hints (C : axst) : list sprop := ltac2:(tb__ "0|1|
Se1S21S21S21SfS21A1SdS21A1Lx;SfaSb3VC;A1R1A2S21ScS21R1S14S21A1M0A3Lq;G0Xfx2Lp;ScS21Sf7Z918A1G0A3A4").

Definition ms16_at (b : sv) (d : Z) : sprop := ltac2:(tb__ "0|0|
S28S27Sf3S23Sf1S23Sf2S1dZ28A1S23Sf0Vb;S1dSe7Vd;A1A1A3A3S1dZfA1A3S1dZ0A1A3A1").
Definition fp_site (E : axst) : axst := ltac2:(tb__ "0|0|
S63S15S1eS1eS1dZ1a780A1S1dZ80A1A4S3cS75S39U0S1dNa80A1S38S1dSd5A1VE;A2A3A2A2S2SfbS97R1A1R1A2TC;").
Definition E_ref : axst := Eval vm_compute in nthA R1c LV_ref 0.
Lemma run_ref1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeSc4S11A5S10G0ScS4S9S43S34A2S14S4A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_ref : axst := Eval vm_compute in fp_site E_ref.
Lemma ref_pipe : ltac2:(tb__ "0|6|
S1S0S13S3aS43S1dSd5A1M0A2S11A3S1S0SfS20A1SdaS3S38G0S43A2M1A1U0M2S1dNa80A1M3A3S10S20S3S39G2G3G1A3M4A1A2A3S1S0S13SdfS12S1eS1eA2S8S15S1eS1eS1dZ1a780A1S1dZ80A1A4M5A1S6S43A1A3S18A3S1S0S2SadS43A1S54A3S0SdS21A1S97S63G5S3cS75G4A2A2A1ScS21Sb2ScfZ998A2S14S21A1A3A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_ref : wsub := Eval vm_compute in s_fpc C_ref.
Definition R_ref : list sobj := Eval vm_compute in optR (entails_frA C_ref Pre_ref s_ref).
Lemma fr_ref : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S54SebS7cA3S10G0S6cA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_ref : ltac2:(tb__ "0|0|
S0S13Sd8S54SebS7cS6cSdcS4S2S7SedA4A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_ref : axst := Eval vm_compute in T_after Pre_ref C_ref s_ref R_ref P_ref.

Definition fp_u1 (n : nat) : list nat := ltac2:(tb__ "0|2|
S17SeScSeU0ScSeU1ScSeU3ScSeU4S14SeA1M0A3A3A3A3S17SeSddU6M1Se3Vn;G1A2A2ScSeU2ScSeU5G0A3A3A3A3").
Definition fp_undo1 (T : axst) : axst := ltac2:(tb__ "0|0|
S16S1cS1fS3VT;A1A1A2SeS96Se3R1U2A2S37S98R1A1VT;A2A2Tn;").
Definition fp_u2 (n : nat) : list nat := ltac2:(tb__ "0|1|
S17SeScSeU7ScSeU0S14SeA1A3A3S17SeSddU1U6A2SddU8M0Se3Vn;G0A2A2A3A3").
Definition fp_undo2 (U : axst) : axst := ltac2:(tb__ "0|1|
S16S1cS1fS3VU;A1A1A2SeS4dU0M0S37S99R1A1Sc0Sb7VU;ScSb5Sb6G0A1S14Sb5A1A3A2VU;A2A2A2Tn;").
Definition U_ref : axst := Eval vm_compute in fp_undo1 T_ref.
Definition V_ref : axst := Eval vm_compute in fp_undo2 U_ref.
Lemma T_ref_eqs : ltac2:(tb__ "0|4|
S1S0S2SbfSebS54S7cS6cSecA5S5aA3S1S0S2SaeS5aA1S48A3S1S0SdS1cA1S1fS3S37S98S16S1cS1fS3S5aA1A1A2A1S5aA2A1A1S17S1cS1fS3S48A1A1M0S75A3A3S1S0SfS2A1Sb7S48ScSb5Sb6U0M1A1S14Sb5A1A3A2M2S10S2Sc0G2S48A2M3A2A3S1S0SfS20A1SdbS3S37S99S16S1cG0A2A1G3A2A1G1A2S10S20S3S71A1A2A3S0S2SafS48A1S71A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition LV_xref : list leafA := Eval vm_compute in runR 20 V_ref.
Lemma run_xref : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeS71S11A5S10G0S86A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_xref_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS86A1ScG0S15S31S33Se4S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_ref : axst := Eval vm_compute in nthA V_ref LV_xref 0.

Definition fw_undoL (T : axst) : axst := ltac2:(tb__ "0|0|
S38ScbS4cS40VT;A1A1A2").

Definition fb_siteR (xb : sv * sv) (cap : sv) (F : axst) : axst := ltac2:(tb__ "0|0|
Sd1Vxb;Sd1S15S1eS1eSd3Vcap;A4VF;A2A2").
Definition s_fbR (cap : sv) (C : axst) : wsub := ltac2:(tb__ "0|1|
ScS12S32S1eA2M0S15S32S1ePfS1dSe7SceA1A1A4ScG0S15S32S1ePcSd3A4ScG0S15S32S1ePdVcap;A4SeeP1S3VC;A1S3ScaA1A3A3A3A3").

Definition E_sh1 : axst := Eval vm_compute in nthA R1c LV_sh1 0.
Lemma run_sh11 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeSc6S11A5S10G0ScS4S9S45S34A2S14S4A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_sh1 : axst := Eval vm_compute in fw_siteL 0x21447 31 E_sh1.
Lemma sh1_pipe : ltac2:(tb__ "0|6|
S1S0S13S3aS45S1dSd5A1M0A2S11A3S1S0SfS20A1SdaS3S38G0S45A2M1A1U0M2S1dN9e0A1M3A3S10S20S3S39G2G3G1A3A1A2A3S1S0S13SdfS12S1eS1eA2S8SbaZ21447M4Z1fM5A2A1S6S45A1A3S18A3S0S2S65G4G5S45A3S56A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_sh1 : wsub := Eval vm_compute in s_fwc 0x21447 31 C_sh1.
Definition R_sh1 : list sobj := Eval vm_compute in optR (entails_frA C_sh1 (Pre_fw 0x21447 31) s_sh1).
Lemma fr_sh1 : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S56Sb9Z21447Z1fA2S7eA3S10G0S6eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_sh1 : ltac2:(tb__ "0|0|
S0S13Sd8S56Sb9Z21447Z1fA2S7eS6eSdcS4S2S7SbcA4A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_sh1 : axst := Eval vm_compute in T_after (Pre_fw 0x21447 31) C_sh1 s_sh1 R_sh1 P_fw.
Definition U_sh1 : axst := Eval vm_compute in fw_undo1 T_sh1.
Definition V_sh1 : axst := Eval vm_compute in fw_undo2L U_sh1.
Definition W_sh1 : axst := Eval vm_compute in x4set vTP V_sh1.
Lemma T_sh1_eqs : ltac2:(tb__ "0|4|
S1S0S2SbfSb9Z21447Z1fA2S56S7eS6eSbbA5S5cA3S1S0S2S40S5cA1S4aA3S1S0SdS1cA1S1fS3S37S3fS16S1cS1fS3S5cA1A1A2A1S5cA2A1A1S17S1cS1fS3S4aA1A1M0S3dA3A3S1S0SfS2A1Sb7S4aScSb5Sb6U0M1A1S14Sb5A1A3A2M2S10S2Sc0G2S4aA2M3A2A3S1S0SfS20A1SdbS3S37S3eS16S1cG0A2A1G3A2A1G1A2S10S20S3S61A1A2A3S1S0S2S4cS4aA1S61A3S1S0S13S3aS61ScbA2S11A3S0S2S38ScbS61A2S90A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition LV_fsh1 : list leafA := Eval vm_compute in runR 20 W_sh1.
Lemma run_fsh1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeS90S11A5S10G0S82A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_fsh1_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS82A1ScG0S15S31S33Sd6S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition F_sh1 : axst := Eval vm_compute in nthA W_sh1 LV_fsh1 0.
Definition CF_sh1 : axst := Eval vm_compute in fb_siteR (xblk 0x21447 31) vCap F_sh1.
Lemma CF_sh1_eq : ltac2:(tb__ "0|0|
S0S2S64SbaZ21447Z1fA2Sd0Sa3A3S50A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sF_sh1 : wsub := Eval vm_compute in s_fbR vCap CF_sh1.
Definition RF_sh1 : list sobj := Eval vm_compute in optR (entails_frA CF_sh1 PreF sF_sh1).
Lemma frF_sh1 : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S50ScaS78A3S10G0S68A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ccF_sh1 : ltac2:(tb__ "0|0|
S0S13Sd9S50ScaS78S68ScS2SccS14S2A1A3A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition TF_sh1 : axst := Eval vm_compute in T_after PreF CF_sh1 sF_sh1 RF_sh1 PostF.
Lemma TF_sh1_eq : ltac2:(tb__ "0|0|
S0S2SbfScaS50S78S68SccA5S8cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition LV_xsh1 : list leafA := Eval vm_compute in runR 60 TF_sh1.
Lemma run_xsh1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U3cSbeS8cS11A5S10G0S88A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_xsh1_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS88A1ScG0S15S31S33Se4S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_sh1 : axst := Eval vm_compute in nthA W_sh1 LV_xsh1 0.

Definition E_ov1 : axst := Eval vm_compute in nthA R1c LV_ov1 0.
Lemma run_ov11 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeSc3S11A5S10G0ScS4S9S42S34A2S14S4A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_ov1 : axst := Eval vm_compute in fw_siteL 0x160cd 31 E_ov1.
Lemma ov1_pipe : ltac2:(tb__ "0|6|
S1S0S13S3aS42S1dSd5A1M0A2S11A3S1S0SfS20A1SdaS3S38G0S42A2M1A1U0M2S1dN9e0A1M3A3S10S20S3S39G2G3G1A3A1A2A3S1S0S13SdfS12S1eS1eA2S8SbaZ160cdM4Z1fM5A2A1S6S42A1A3S18A3S0S2S65G4G5S42A3S53A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_ov1 : wsub := Eval vm_compute in s_fwc 0x160cd 31 C_ov1.
Definition R_ov1 : list sobj := Eval vm_compute in optR (entails_frA C_ov1 (Pre_fw 0x160cd 31) s_ov1).
Lemma fr_ov1 : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S53Sb9Z160cdZ1fA2S7bA3S10G0S6bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_ov1 : ltac2:(tb__ "0|0|
S0S13Sd8S53Sb9Z160cdZ1fA2S7bS6bSdcS4S2S7SbcA4A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_ov1 : axst := Eval vm_compute in T_after (Pre_fw 0x160cd 31) C_ov1 s_ov1 R_ov1 P_fw.
Definition U_ov1 : axst := Eval vm_compute in fw_undo1 T_ov1.
Definition V_ov1 : axst := Eval vm_compute in fw_undo2L U_ov1.
Definition W_ov1 : axst := Eval vm_compute in x4set vTP V_ov1.
Lemma T_ov1_eqs : ltac2:(tb__ "0|4|
S1S0S2SbfSb9Z160cdZ1fA2S53S7bS6bSbbA5S59A3S1S0S2S40S59A1S47A3S1S0SdS1cA1S1fS3S37S3fS16S1cS1fS3S59A1A1A2A1S59A2A1A1S17S1cS1fS3S47A1A1M0S3dA3A3S1S0SfS2A1Sb7S47ScSb5Sb6U0M1A1S14Sb5A1A3A2M2S10S2Sc0G2S47A2M3A2A3S1S0SfS20A1SdbS3S37S3eS16S1cG0A2A1G3A2A1G1A2S10S20S3S5fA1A2A3S1S0S2S4cS47A1S5fA3S1S0S13S3aS5fScbA2S11A3S0S2S38ScbS5fA2S8eA3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition LV_fov1 : list leafA := Eval vm_compute in runR 20 W_ov1.
Lemma run_fov1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeS8eS11A5S10G0S80A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_fov1_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS80A1ScG0S15S31S33Sd6S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition F_ov1 : axst := Eval vm_compute in nthA W_ov1 LV_fov1 0.
Definition CF_ov1 : axst := Eval vm_compute in fb_siteR (xblk 0x160cd 31) vCap F_ov1.
Lemma CF_ov1_eq : ltac2:(tb__ "0|0|
S0S2S64SbaZ160cdZ1fA2Sd0Sa1A3S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sF_ov1 : wsub := Eval vm_compute in s_fbR vCap CF_ov1.
Definition RF_ov1 : list sobj := Eval vm_compute in optR (entails_frA CF_ov1 PreF sF_ov1).
Lemma frF_ov1 : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S4eScaS76A3S10G0S66A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ccF_ov1 : ltac2:(tb__ "0|0|
S0S13Sd9S4eScaS76S66ScS2SccS14S2A1A3A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition TF_ov1 : axst := Eval vm_compute in T_after PreF CF_ov1 sF_ov1 RF_ov1 PostF.
Lemma TF_ov1_eq : ltac2:(tb__ "0|0|
S0S2SbfScaS4eS76S66SccA5S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition LV_xov1 : list leafA := Eval vm_compute in runR 60 TF_ov1.
Lemma run_xov1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U3cSbeS8aS11A5S10G0S85A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_xov1_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS85A1ScG0S15S31S33Se4S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_ov1 : axst := Eval vm_compute in nthA W_ov1 LV_xov1 0.

Definition E_sh0 : axst := Eval vm_compute in nthA R1c LV_sh0 0.
Lemma run_sh01 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeSc5S11A5S10G0ScS4S9S44S34A2S14S4A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_sh0 : axst := Eval vm_compute in fw_siteL 0x21447 31 E_sh0.
Lemma sh0_pipe : ltac2:(tb__ "0|6|
S1S0S13S3aS44S1dSd5A1M0A2S11A3S1S0SfS20A1SdaS3S38G0S44A2M1A1U0M2S1dN9e0A1M3A3S10S20S3S39G2G3G1A3A1A2A3S1S0S13SdfS12S1eS1eA2S8SbaZ21447M4Z1fM5A2A1S6S44A1A3S18A3S0S2S65G4G5S44A3S55A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_sh0 : wsub := Eval vm_compute in s_fwc 0x21447 31 C_sh0.
Definition R_sh0 : list sobj := Eval vm_compute in optR (entails_frA C_sh0 (Pre_fw 0x21447 31) s_sh0).
Lemma fr_sh0 : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S55Sb9Z21447Z1fA2S7dA3S10G0S6dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_sh0 : ltac2:(tb__ "0|0|
S0S13Sd8S55Sb9Z21447Z1fA2S7dS6dSdcS4S2S7SbcA4A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_sh0 : axst := Eval vm_compute in T_after (Pre_fw 0x21447 31) C_sh0 s_sh0 R_sh0 P_fw.
Definition U_sh0 : axst := Eval vm_compute in fw_undo1 T_sh0.
Definition V_sh0 : axst := Eval vm_compute in fw_undo2L U_sh0.
Definition W_sh0 : axst := Eval vm_compute in x4set vTP V_sh0.
Lemma T_sh0_eqs : ltac2:(tb__ "0|4|
S1S0S2SbfSb9Z21447Z1fA2S55S7dS6dSbbA5S5bA3S1S0S2S40S5bA1S49A3S1S0SdS1cA1S1fS3S37S3fS16S1cS1fS3S5bA1A1A2A1S5bA2A1A1S17S1cS1fS3S49A1A1M0S3dA3A3S1S0SfS2A1Sb7S49ScSb5Sb6U0M1A1S14Sb5A1A3A2M2S10S2Sc0G2S49A2M3A2A3S1S0SfS20A1SdbS3S37S3eS16S1cG0A2A1G3A2A1G1A2S10S20S3S60A1A2A3S1S0S2S4cS49A1S60A3S1S0S13S3aS60ScbA2S11A3S0S2S38ScbS60A2S8fA3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition LV_fsh0 : list leafA := Eval vm_compute in runR 20 W_sh0.
Lemma run_fsh0 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeS8fS11A5S10G0S81A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_fsh0_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS81A1ScG0S15S31S33Sd6S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition F_sh0 : axst := Eval vm_compute in nthA W_sh0 LV_fsh0 0.
Definition CF_sh0 : axst := Eval vm_compute in fb_siteR (xblk 0x21447 31) vCap F_sh0.
Lemma CF_sh0_eq : ltac2:(tb__ "0|0|
S0S2S64SbaZ21447Z1fA2Sd0Sa2A3S4fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sF_sh0 : wsub := Eval vm_compute in s_fbR vCap CF_sh0.
Definition RF_sh0 : list sobj := Eval vm_compute in optR (entails_frA CF_sh0 PreF sF_sh0).
Lemma frF_sh0 : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S4fScaS77A3S10G0S67A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ccF_sh0 : ltac2:(tb__ "0|0|
S0S13Sd9S4fScaS77S67ScS2SccS14S2A1A3A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition TF_sh0 : axst := Eval vm_compute in T_after PreF CF_sh0 sF_sh0 RF_sh0 PostF.
Lemma TF_sh0_eq : ltac2:(tb__ "0|0|
S0S2SbfScaS4fS77S67SccA5S8bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition LV_xsh0 : list leafA := Eval vm_compute in runR 60 TF_sh0.
Lemma run_xsh0 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U3cSbeS8bS11A5S10G0S87A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_xsh0_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS87A1ScG0S15S31S33Se4S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_sh0 : axst := Eval vm_compute in nthA W_sh0 LV_xsh0 0.

Definition E_shZ : axst := Eval vm_compute in nthA R1c LV_shZ 0.
Lemma run_shZ1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeSc7S11A5S10G0ScS4S9S46S34A2S14S4A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_shZ : axst := Eval vm_compute in fw_siteL 0x21447 31 E_shZ.
Lemma shZ_pipe : ltac2:(tb__ "0|6|
S1S0S13S3aS46S1dSd5A1M0A2S11A3S1S0SfS20A1SdaS3S38G0S46A2M1A1U0M2S1dN9e0A1M3A3S10S20S3S39G2G3G1A3A1A2A3S1S0S13SdfS12S1eS1eA2S8SbaZ21447M4Z1fM5A2A1S6S46A1A3S18A3S0S2S65G4G5S46A3S57A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_shZ : wsub := Eval vm_compute in s_fwc 0x21447 31 C_shZ.
Definition R_shZ : list sobj := Eval vm_compute in optR (entails_frA C_shZ (Pre_fw 0x21447 31) s_shZ).
Lemma fr_shZ : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S57Sb9Z21447Z1fA2S7fA3S10G0S6fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_shZ : ltac2:(tb__ "0|0|
S0S13Sd8S57Sb9Z21447Z1fA2S7fS6fSdcS4S2S7SbcA4A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_shZ : axst := Eval vm_compute in T_after (Pre_fw 0x21447 31) C_shZ s_shZ R_shZ P_fw.
Definition U_shZ : axst := Eval vm_compute in fw_undo1 T_shZ.
Definition V_shZ : axst := Eval vm_compute in fw_undo2L U_shZ.
Definition W_shZ : axst := Eval vm_compute in x4set vTP V_shZ.
Lemma T_shZ_eqs : ltac2:(tb__ "0|4|
S1S0S2SbfSb9Z21447Z1fA2S57S7fS6fSbbA5S5dA3S1S0S2S40S5dA1S4bA3S1S0SdS1cA1S1fS3S37S3fS16S1cS1fS3S5dA1A1A2A1S5dA2A1A1S17S1cS1fS3S4bA1A1M0S3dA3A3S1S0SfS2A1Sb7S4bScSb5Sb6U0M1A1S14Sb5A1A3A2M2S10S2Sc0G2S4bA2M3A2A3S1S0SfS20A1SdbS3S37S3eS16S1cG0A2A1G3A2A1G1A2S10S20S3S62A1A2A3S1S0S2S4cS4bA1S62A3S1S0S13S3aS62ScbA2S11A3S0S2S38ScbS62A2S91A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition LV_fshZ : list leafA := Eval vm_compute in runR 20 W_shZ.
Lemma run_fshZ : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeS91S11A5S10G0S83A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_fshZ_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS83A1ScG0S15S31S33Sd6S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition F_shZ : axst := Eval vm_compute in nthA W_shZ LV_fshZ 0.
Definition CF_shZ : axst := Eval vm_compute in fb_siteR (xblk 0x21447 31) (SLit CAP0) F_shZ.
Lemma CF_shZ_eq : ltac2:(tb__ "0|0|
S0S2S64SbaZ21447Z1fA2S1dSf4A1Sa4A3S51A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sF_shZ : wsub := Eval vm_compute in s_fbR (SLit CAP0) CF_shZ.
Definition RF_shZ : list sobj := Eval vm_compute in optR (entails_frA CF_shZ PreF sF_shZ).
Lemma frF_shZ : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S51ScaS79A3S10G0S69A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ccF_shZ : ltac2:(tb__ "0|0|
S0S13Sd9S51ScaS79S69ScS2SccS14S2A1A3A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition TF_shZ : axst := Eval vm_compute in T_after PreF CF_shZ sF_shZ RF_shZ PostF.
Lemma TF_shZ_eq : ltac2:(tb__ "0|0|
S0S2SbfScaS51S79S69SccA5S8dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition LV_xshZ : list leafA := Eval vm_compute in runR 60 TF_shZ.
Lemma run_xshZ : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U3cSbeS8dS11A5S10G0S89A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_xshZ_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS89A1ScG0S15S31S33Se4S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_shZ : axst := Eval vm_compute in nthA W_shZ LV_xshZ 0.

Definition lc_objR (c : Z * Z * list (Z * nat * Z)) : sobj := ltac2:(tb__ "0|5|
S12S12S31S31A2M0SdS12S12S31SeA2M1S31A2M2A1M3A2S1cLc;Vc;G0G3G0S1cLp;R2S31S31SffS1dZ0A1R2R1SdcG2S12G1S1eA2M4G2G2G4Lc;R1G1S31G1G4Ly;R2S31SeS15G1S1eS15S31SeR2R1A4S1dR3A1A4Lk;La;X12x1Lv;Ly;X12x1Lc;R3A4A4Lhi;Llo;X12x1Lcs;Lp;X12x1").
Definition ex_carvedR : list sobj := map lc_objR N_ex.

Definition ex_img (A : axst) : axst := ltac2:(tb__ "0|1|
ScdS1fS3VA;A1M0A1S1dZ0A1S1dSe5A1A3SeSaVA;SfdG0R1Se8Se5Z8cA2Z4SeaSe9Z2Z20A2Z1A2A5A2Tie;").
Definition ex_img_okb (A : axst) : bool := ltac2:(tb__ "0|1|
ScdS1fS3VA;A1M0A1S1dZ0A1S1dSe5A1A3SeSfeSb8G0R1Se8Se5Z8cA2Z4SeaSe9Z2Z20A2Z1A2A6Tie;").

Definition ex_fin (A : axst) : axst := ltac2:(tb__ "0|1|
SefS38S1dSd5A1S3cS73S74SefVA;S14S12S1eS1eA2A1M0A2A1A2A2G0A2").

Definition ex_siteD (cut : Z) (E : axst) : axst := ltac2:(tb__ "0|0|
S93S39U0S1dVcut;A1VE;A3A1").

Definition exS_rb (E : axst) : axst := ltac2:(tb__ "0|0|
ScdS1fS3VE;A1A1Sd2S1dSe7SceA1A1A3SeSc0Sb7VE;ScSb5Sb6R1A1S14Sb5A1A3A2VE;A2Tiw;").
Definition exS_idxs (E1 : axst) : list nat := ltac2:(tb__ "0|2|
S1fS3VE1;A1A1SdS1cA1S16S1cR1A2SeScdR2ScfS1dSe7Se8SceZ80A2A1A1A3SeScdR3ScfS1dN80A1A3SeS17SeScSeR2ScSeR1S14SeA1M0A3A3S102SeSdSeA1S104SeA1SeS101S1aSdfSeS100R1A1ScSeR3ScSeR2G0A3A3A3A1M1A1Li;SeS103G1A1Lx;SddU0R3A2A6A3Tim;Tiw;Tn;Tobjs;").
Definition ex_siteS (E : axst) : axst := ltac2:(tb__ "0|1|
S92VE;A1S2S93S39U0M0S1dN430A1S4dG0S37S72R1A1R1A2A2A3A1TE1;").

Definition s_exR (w : Z) (C : axst) : wsub := ltac2:(tb__ "0|2|
S17S12S32S1eA2M0ScG0S15S32S1eP11S1dVw;A1A4ScG0S15S32S1eP12S1dZ0M1A1A4S14G0A1A3A3Sd4VC;G1Z2A3A3").
Definition exR (w : Z) (C : axst) : list sobj := ltac2:(tb__ "0|0|
Sc9Sd7VC;Se6Z0Z2A2S9aVw;VC;A2A3A1").
Definition ex_okb (w : Z) (C : axst) : bool := ltac2:(tb__ "0|4|
SfSdS1cA1M0A1S13Lx;Sd7VC;Se6Z0Z2A2M1S9aVw;VC;A2M2A3G0S19Sd8VC;G1G2R1S14S2A1A5Se2S21S2aS25S3VC;A1M3A1A1S24G3A1A3A2LR;S18Xfx2").

Definition CX_oom : axst := Eval vm_compute in ex_siteD (-1024) X_oom.
Definition CX_ref : axst := Eval vm_compute in ex_siteD (-1152) X_ref.
Definition CX_sh1 : axst := Eval vm_compute in ex_siteS X_sh1.
Definition CX_ov1 : axst := Eval vm_compute in ex_siteS X_ov1.
Definition CX_sh0 : axst := Eval vm_compute in ex_siteS X_sh0.
Definition CX_shZ : axst := Eval vm_compute in ex_siteS X_shZ.
Lemma exD_pipe : ltac2:(tb__ "0|4|
S12S12S12S2S31A2M0S31A2M1S2A2M2Se0G2R1ScG2S15G1S2S15G0S31S15S2S31Sa5N400A4SbdA4S9bA4ScG2S15G1S2S15G0S31S15S2S31Sa7N480A4Z0A4S9dA4S14G2A1A3A3A3G2OLp;R2G1S2G1OLp0;R2G0S31G0OLp1;R2S2S31S39U0M3S1dR1A1R2A3S2S74R1A1S2S3cS73R1A2S2S1S0SfS20A1SdaS3R5A1G3S1dR4A1A3S10S20S3R3A1A2A3S1S0S13S94R3A1S11A3S1S0S13S3aR1S1dSd5A1A2S11A3S1S0S2SabR4R5A2R8A3S0S13S95R6R8A2S11A3A2A2A2A2TA3;TA2;TA1;Lcut;LE;X12x1Lw;Lp1;X12x1LC;Lp0;X12x1F_;Fp;").
Proof. intros p Hp. repeat (destruct Hp as [<-|Hp]; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2|]). destruct Hp. Qed.
Lemma exS_pipe : ltac2:(tb__ "0|5|
S12S2S2A2M0Se0G0R1ScG0S15S2S2Sa9S9fA4ScG0S15S2S2Sa6S9cA4ScG0S15S2S2Sa8S9eA4ScG0S15S2S2SaaSa0A4S14G0A1A3A3A3A3A3G0OLp;R2S2S2ScdS1fS3R2A1A1Sd2S1dSe7SceA1A1A3SeS92R3A1S2S37S72R1A1R1A2S2S4dU0M1R1A2S2S39G1S1dN430A1M2R1A3S2S74R1A1S2S3cS73R1A2S2S1S0SfS2A1Sb7R9ScSb5Sb6R7A1S14Sb5A1A3A2S10S2R6A2A3S1S0S13SfcS16S1cS1fS3R6A1A1A2S72R6A1A2S11A3S1S0SfS20A1M3SdbS3R5A1G1A2S10S20S3R4A1M4A2A3S1S0G3SdaG4G1G2A3S10S20S3R3A1A2A3S1S0S13S94R3A1S11A3S1S0S13S3aR1S1dSd5A1A2S11A3S1S0S2SacR9A1R8A3S0S13S95SbdR8A2S11A3A2A2A2A2A2A2A2TA3;TA2;TA1;TA0';TA0;TE1;Tiw;LC;LE;X12x1F_;Fp;").
Proof. intros p Hp. repeat (destruct Hp as [<-|Hp]; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2|]). destruct Hp. Qed.
End DrvR_tstates.

(* [comment removed for export] *)
Module DrvTLX.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "or"; "True"; "not"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "nat"; "prod"; "nil"; "cons"; "false"; "pair"; "option"; "Some"; "app"; "length"; "andb"; "None"; "orb"; "fst"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_next"; "sprop"; "ss_facts"; "valuation"; "sstate"; "SLit"; "ss_objs"; "ss_lenient"; "holds"; "sprop_eqb"; "SPUle"; "SPBranch"; "SVar"; "sprop_below"; "SPNot"; "cell"; "mkObj"; "DUnknown"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "SAlu"; "agree_below"; "obj_hi_of"; "obj_lo_of"; "obj_range"; "rm"; "rw"; "eval"; "obj_wf"; "sv_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "ax_X"; "ax_base"; "la_state"; "sym_runA"; "mkAX"; "entailsA"; "mkLeafA"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "ExitEv"; "FdEntry"; "WriteEv"; "m_fs"; "FdChannel"; "fd_lookup"; "m_fds"; "VmState"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "LQA"; "smatchA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_below"; "ANone"; "NDA"; "ndesc"; "PTrue"; "nd_tv"; "nd_am"; "ok_frameKA"; "JAi"; "nd_bd"; "nd_fr"; "tvinA"; "JA"; "am_eqb"; "am_subst"; "amode"; "apot"; "bxa"; "fr_sub_eqb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "tcons"; "assn"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "pow"; "lt"; "sub"; "opp"; "div"; "land"; "modulo"; "of_nat"; "ltb"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvTLX.TLX.LoopE"; "CfzE"; "CpfE"; "keptE"; "ndE1"; "Cpf0E"; "P1cE"; "ndE0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvTLX.TLX.LoopP"; "Cfz"; "Cpf"; "kept"; "ndL1"; "Cpf0"; "P1c"; "ndL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "wsub_get"; "rho_absorb"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvT_states"; "s_fz"; "vP"; "CUTS_L"; "FUEL_L"; "J_E"; "PreP"; "pf_hints"; "s_m"; "s_pf"; "O_srcT"; "s_fp"; "O_WloT"; "PreM"; "pf_u1"; "s_fn"; "CUTS_T"; "PreFN"; "s_mc"; "O_WfzT"; "O_payE"; "PostFN"; "WDP"; "X_payE"; "cnt_reg"; "AND3"; "FUEL_T0"; "FUEL_T1"; "FUEL_T2"; "O_cstkB"; "PostsM"; "mc_hints"; "mc_rtc"; "pf_rtc"; "sel_buf"; "sel_rtc_last"; "sel_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "vPlen"; "vB"; "vCap"; "nd_T"; "vClen"; "vLen"; "S_T"; "bd_T"; "tv_T"; "PreF"; "sp0"; "CUTS_X"; "FUEL_X"; "PostF"; "calls_of"; "dropX"; "flags_of"; "spT"; "vFlg"; "ATOPHI"; "facts_T"; "hdr_word"; "locate"; "@Stdlib.Lists.List"; "forallb"; "In"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvTLX.TLX.ExitFreeP"; "CP"; "keptX"; "ndJX"; "ndLX";
"@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ"; "lcarve"; "lc_obj"; "JAK"; "carve_okb"; "uncarve_okb"; "JA_carve"; "JA_uncarve"; "pure_callJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite"; "sp0_factsb"; "drv_xrb"; "kept_nzb"; "robjs_checkD"; "xrs_checkD"; "drv_objb"; "ex_pipe"; "fb_pipe"; "site_ok_drv"; "xrs_okF_drv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa"; "KV_T"; "BX0"; "KP_T"; "HKVrng_T"; "JT"; "P0T"; "CST_drv"; "HCSTKV_T"; "HKP_T"; "HKV_T"; "JT_tv_band_free"; "JTi"; "SH0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bd_subst"; "bitem"; "bud_le"; "bsumV"; "bd_below"; "bud_pay"; "BIc"; "KU"; "LARGE_MIN"; "SECCAP"; "uval"; "BUD"; "bx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvTLX.TLX.SegMC"; "B3h"; "Cmc"; "ndM"; "B3c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "robj_tracked"; "tnz"; "tvz"; "T0"; "tvd"; "tvv"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "BC_EQ"; "branch_cond"; "mulop"; "BC_LT"; "BC_NE"; "ALU_AND"; "ALU_OR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvTLX.TLX"; "N_pf"; "EVk"; "N_mc"; "O_srcM"; "edge_okb"; "kept"; "ms16_shape"; "mc_needb"; "plen_factsb"; "ndE0"; "backedge_okb"; "cntg_b"; "cntl_b"; "exit1_b"; "exitc_b"; "ms16_shapeb"; "ndM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "Pre_fz"; "bd_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "wsub_dom_below"; "pos_add_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "xr_tracked"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit"; "ch1"; "supported"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "AE_A"; "Kc_ok"; "L_malloc_ok"; "UStopLe"; "ulink"; "V_RES"; "alloc_contractsA"; "band_free"; "with_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvTLX"; "bd_E"; "bd_M"; "CKM"; "CVM"; "bd_L"; "cnt_word"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "acell"; "cells_ok"; "mkACell"; "view"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "PEND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_iface2"; "P_fz"; "PD_fz"; "fuzz_one_sumT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config";
"mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvTLX.TLX.ExitFreeE"; "ndJE"; "ndEX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "Pre_mc0"; "P_icpt"; "Posts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "TR_INIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf.PFAddr"; "PW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf"; "P_pf"; "Posts_pf"; "kok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.FZAddr"; "fz_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pd_okA"; "pdescA"; "xrs_inclb"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "MAX_INPUT"; "CK0"; "CK_DIV"; "CV"; "CV0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "img_cell_apply"; "img_cell_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC"; "add_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceS"; "alloc_roomA"; "malloc_contractA_strong"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA DrvGlueA DrvGlueB DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT Lib_fuzz_iface2 DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nl.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nl.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nl.DrvBox.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ot.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition CVM : Z := ltac2:(tb__ "0|0|
S7bS7cS182S17fA2S183A2").
Definition CKM : Z := ltac2:(tb__ "0|0|
S7bS81S17fS181A2S180A2").
Definition bd_L (k : Z) : list bitem := ltac2:(tb__ "0|3|
SdS104S109Z1M0Z0M1S7cS7fZ4Vk;A2M2S15cA2A3SdS104S109G1G0S7cS10aS7bS7cG2S15bA2Z2A2A2A3ScS104A1A3A3").
Definition bd_E (k : Z) : list bitem := ltac2:(tb__ "0|3|
SdS104S109Z1M0Z0M1S7cS7fZ4Vk;A2M2S15cA2A3SdS104S109G1G0S7cS10aS7bS7cG2S15bA2G0A2A2A3ScS104A1A3A3").
Definition bd_J : list bitem := [BIc 0 1 KU].
Definition bd_M : list bitem := bd_L 0.

Lemma bd_L_cap : ltac2:(tb__ "0|0|
S19S21S7aS7bS7cS10bZ2A2S7fS106S15dR2A1R1A2S106S15dS7bR2Z1A2A1R1A2A2A2S10cA2Frho;Fk;").
Proof. intros k rho. unfold bd_L, bsumV, bival, BIc. cbn [lfval bi_f bi_c bi_v bi_k]. unfold SECCAP, LARGE_MIN, Model.SEC_SLACK, CVM, CV, MAX_INPUT, CV0. lia. Qed.
Lemma bd_E_cap : ltac2:(tb__ "0|0|
S19S21S7aS7bS7cS10bZ2A2S7fS106S159R2A1R1A2S106S159S7bR2Z1A2A1R1A2A2A2S10cA2Frho;Fk;").
Proof. intros k rho. unfold bd_E, bsumV, bival, BIc. cbn [lfval bi_f bi_c bi_v bi_k]. unfold SECCAP, LARGE_MIN, Model.SEC_SLACK, CVM, CV, MAX_INPUT, CV0. lia. Qed.

Definition cnt_word (u : Z) : Z := ltac2:(tb__ "0|1|
S82S83S81Vu;S7dZ2M0Z10A2A2S7dG0Z8A2A2Z3A2").

Lemma eval_AND3 : ltac2:(tb__ "0|1|
S21S0S19S50Q40M0S3dR1Sb6A2A2S15eS50G0S3cR1P2dA2A2A1A3Frho;").
Proof.
  intros rho. unfold AND3, vH. cbn [eval]. rewrite and_val, lit_unsigned. change (3 mod 2 ^ 64) with 3.
  rewrite (U_zext_w 8) by (cbv; discriminate). rewrite srl_val. change (16 mod 64) with 16.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma cnt_word_hdr : ltac2:(tb__ "0|2|
S9S4eQ8M0A1M1A1S19S0S19S83R1S7dZ2Z20A2A2Sd7R2A1A3S0S19S15eR2A1S82S50G0S8aG1U2R3S4fG0Z0A2A4A2Z3A2A3F_;Fu;FF;").
Proof.
  intros F u Hu. unfold cnt_word, hdr_word in *.
  pose proof (bv_unsigned_in_range 8 (nth 0 F (Z_to_bv 8 0))) as R0. pose proof (bv_unsigned_in_range 8 (nth 1 F (Z_to_bv 8 0))) as R1.
  pose proof (bv_unsigned_in_range 8 (nth 2 F (Z_to_bv 8 0))) as R2. pose proof (bv_unsigned_in_range 8 (nth 3 F (Z_to_bv 8 0))) as R3.
  change (bv_modulus 8) with 256 in *.
  set (b0 := bv_unsigned (nth 0 F (Z_to_bv 8 0))) in *. set (b1 := bv_unsigned (nth 1 F (Z_to_bv 8 0))) in *.
  set (b2 := bv_unsigned (nth 2 F (Z_to_bv 8 0))) in *. set (b3 := bv_unsigned (nth 3 F (Z_to_bv 8 0))) in *.
  change (2 ^ 8) with 256 in *. f_equal.
  pose proof (Z.div_mod u (2 ^ 32) ltac:(lia)) as Hd. rewrite Hu in Hd.
  pose proof (Z.mod_pos_bound u (2 ^ 32) ltac:(lia)) as Hm.
  change (2 ^ 32) with 4294967296 in *. change (2 ^ 16) with 65536 in *.
  assert (E : u / 65536 = (65536 * (u / 4294967296) + 256 * b3 + b2) + (b0 + 256 * b1) / 65536).
  { rewrite Hd at 1. rewrite <- (Z.div_add_l _ 65536) by lia. f_equal. lia. }
  assert (S : (b0 + 256 * b1) / 65536 = 0) by (apply Z.div_small; lia).
  rewrite E, S, Z.add_0_r.
  replace (65536 * (u / 4294967296) + 256 * b3 + b2) with (b2 + (256 * (u / 4294967296) + b3) * 256) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section TLX.
Variable AInv : ltac2:(tb__ "0|0|
S146S21S9S4eQ40A1A1S52OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S19S15fVCST;R1A2S1S7aZ0R2A2S7eR2S16aA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S19S15fVXGL;R1A2S1S7aZ0R2A2S7eR2S16aA2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S19S15fSfcR1A2S15fVCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Variable ok : world -> Prop.
Variable Spec : list event -> Prop.
Hypothesis HOKJ : ltac2:(tb__ "0|0|
S5cS21S9S4eQ40A1A1S9S51A1S52R5R4R3R2R1A4S78VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;S5dS4cVok;R2A3F_;FJ;").
Hypothesis HOKP : ltac2:(tb__ "0|0|
S5cS21S9S4eQ40A1A1S9S51A1S52R5R4R3R2R1A4S78VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;S184S4cVok;R2A3F_;FJ;").
Hypothesis Hokh : ok_halted ok Spec.
Hypothesis AC : ltac2:(tb__ "0|0|
S156S4cS150VAInv;VCST;VXGL;A5").

Hypothesis MS : ltac2:(tb__ "0|0|
S189S4cS150VAInv;VCST;VXGL;A5").

Variable rhoT : valuation.
Variable F : list byte.
Variable T0 : list event.
Variable MD : Model -> Prop.
Hypothesis HMDvm : ltac2:(tb__ "0|0|
S52S5aVMD;R2A1VMD;S158R2R3A2A1F_;Fv;Fmd;").
Hypothesis HMDfd1 : ltac2:(tb__ "0|0|
S52VMD;R1A1S0S10S54A1S58S59R2A1S14aA2S11S54S57S14aA1A2A3F_;Fmd;").

Let KcT := KcT T0 MD.
Let P0T := P0T F.
Let JT (k : nat) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
SfaVAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;S65Vk;Vnd;Aa").
Let JTi (k : nat) (nd : ndesc) (Ai : AA) (kc : Z) : jpredA := ltac2:(tb__ "0|0|
S101VAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;S65Vk;Vnd;VAi;Vkc;Ac").

Let HKV : ltac2:(tb__ "0|1|
S14fS64S146S19S21S9S4eQ40A1A1S9S51A1S52S69VAInv;VCST;VXGL;S4dR8VrhoT;SfbVF;A1ScSbS19S19A2M0A1ScSbG0S19A2A1Sf7S65R7R6R5R4R3R2R1A12S161S163S4cS3bR5A1A2Sf6A2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc;") := ltac2:(tb__ "0|0|
SffVAInv;VCST;VXGL;VALA;VHCSTdrv;VHLPP;VrhoT;VF;S65A9").
Let HKP := HKP_T AInv CST XGL HCSTdrv rhoT F PTrue.
Let HCK := HCSTKV_T AInv CST HCSTok HLPP.
Let carveT : ltac2:(tb__ "0|3|
S14fS64S43S21S9S4eQ40A1A1S77S9Se2A1S1aS5bS4cSe4VAInv;VCST;VXGL;S4dVrhoT;VP0T;ScSbS19S19A2M0A1M1ScSbG0S19A2A1M2Sf7S65R8R7AcR6R5R4R3A6S41R7A1S22S30S33R1A1S34R1A1S32R1A1S31R1A1S35R1A1S12S1dS24R1A1S86Se2S1dSe3R4A4A3S20R1A1R3S25R1A1A9S22S0S7S40R1A1S8A3S0S7S74S1eR3A1R5A2S8A3S0S1cS45RbA1S23S169A1A3S0S7Se5S20R5A1S24R5A1S44RcA1Sf6Sf8S66RdA1R8A7S8A3S5bS4cSe4VAInv;VCST;VXGL;S4dVrhoT;VP0T;G1G2Sf7S65RfReAcS4bRdR5A2RcRbRaA6F_;F_;F_;F_;TS';TS;F_;Fnx;FN;Fw;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
Se7VAInv;VCST;VXGL;VALA;S4dVrhoT;VP0T;ScSbS19S19A2M0A1ScSbG0S19A2A1Sf7S65Sf6VHKV;Sf9Sf8VHKP;A10").
Let uncarveT : ltac2:(tb__ "0|5|
S14fS64S43S21S9S4eQ40A1A1S9S51A1M0S164S52S9S1dA1M1S9Se2A1S151RaA1S0G1S24S41R9A1A1S12S1dR3S86Se2S1dSe3R2A4A3A3S0S7Se6Sf6R3A2S8A3S0S70S67RcA1S62A3S0S7S61S1eS41RcA1A1RdA2S8A3S5bS4cSe4VAInv;VCST;VXGL;S4dVrhoT;VP0T;ScSbS19S19A2M2A1M3ScSbG2S19A2A1M4Sf7S65RfReAcRdRcRbSfG0S16bRaS16cR9R8A2A4A6S5bS4cSe4VAInv;VCST;VXGL;S4dVrhoT;VP0T;G3G4Sf7S65R10RfAcS4bReSeaS41ReA1R8A2A2S9cRdS86Se2S1dSe3R7A4S17aR9RcRaA3A3RcSfG0S16bRbS16cRaR9A2A4A6F_;F_;F_;F_;F_;F_;FN;Fobjs;Fmd;Fms;Ftr;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
Se8VAInv;VCST;VXGL;VALA;VHLV;S4dVrhoT;VP0T;ScSbS19S19A2M0A1ScSbG0S19A2A1Sf7S65Sf6VHKV;Sf9VHCK;A10").
Let pcallT := pure_callJ AInv CST XGL ALA NF rhoT P0T [] [] BX0 PTrue ok.

Let site_ok_drv := site_ok_drv AInv CST XGL ALA HCSTdrv rhoT P0T.
Let robjs_okF_drv := robjs_okF_drv CST HCSTdrv rhoT.
Let xrs_okF_drv := xrs_okF_drv CST XGL HCSTdrv rhoT.
Let kept_in_FBx := kept_in_FBx CST.
Let JT_tv_band_free : ltac2:(tb__ "0|1|
S146OF_;SaS64S21S9S4eQ40A1A1S9S51A1S52SbS1cS1cA2M0SfaVAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;R8R7R6R5R4R3R2AeSdaG0R2S66R7A1A3S118R7R3A2S157S10dR8S17S1cS1cR4A3A2S10dR8S18S1cS1cR4A3A2A2F_;F_;F_;Ft;Fmd;Ftr;Ftp;Frho;Fnd;Fk;FPA;") := ltac2:(tb__ "0|0|
S100VAInv;VCST;VXGL;VALA;VrhoT;VF;VT0;VMD;A8").

Definition EVk (k : nat) : list event := match k with O => [] | _ => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.EVS 2 end.

Lemma JT_Kc : ltac2:(tb__ "0|1|
SaS64S21S9S4eQ40A1A1S9S51A1M0S52VJT;R6R5R4R3R2R1A6S1VMD;R2A1S0G0R3S12S51VT0;S126R7A1A3A3A2F_;Fmd;Ftr;Ftp;Frho;Fnd;Fk;").
Proof. intros k nd rho tp tr md (Ai & kc & _ & [H1 H2] & _). split; [exact H1 | exact H2]. Qed.

Lemma JT_stable : ltac2:(tb__ "0|0|
SaS64S1aS75S4dR1A2S0S7S61R2R3A2S8A3S60S4cR3VJT;R5R4A2A3F_;F_;Fn;Fnd;Fk;").
Proof. intros k nd n Hn Hb. apply (stableA_JA segs AInv CST XGL NF _ rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm k) ALA n nd Hn Hb). Qed.

Variable Htc : ltac2:(tb__ "0|0|
SaS78VSpec;S12S51VT0;S126R1A1A3A2Fk;").

Lemma JT_tcons : ltac2:(tb__ "0|0|
SaS64S21S9S4eQ40A1A1S9S51A1S52VJT;R6R5R4R3R2R1A6S78VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;Fnd;Fk;").
Proof. intros k nd rho tp tr md H. destruct (JT_Kc _ _ _ _ _ _ H) as [_ ->]. apply Htc. Qed.

Lemma okKT : ltac2:(tb__ "0|0|
SaS68S4cVKcT;R1A1Vok;A3Fk;").
Proof. intros k. split; [apply HOKJ | apply HOKP]; intros rho tp tr md [_ ->]; apply Htc. Qed.

Lemma JT_okframe : ltac2:(tb__ "0|0|
SaS64S5dS4cVok;VJT;R2R1A2A3Fnd;Fk;").
Proof. intros k nd. apply HOKJ. apply JT_tcons. Qed.

Lemma JT_run : ltac2:(tb__ "0|1|
SaS64SaS9S19A1S43S9S42A1M0S21S9S4eQ40A1A1S79S0S10G0A1S47S4cR7R6R5S8A5S11G0R4A2A3S0S7S25S41R6A1A1SeA3S0S7S74S4dS1eS41R7A1A1A2S8A3S0S7S61S1eS41R8A1A1RbA2S8A3S42S21SdaS42R2RaA3S37S1eS41RcA1A1RaR2A3S76S4cVok;S5bS4cVJT;R11R10A2S46R4A1R3RaA5R9A4F_;F_;Frho';FL;S76S4cVok;S5bS4cVJT;ReRdA2RaR8R7A5R6A4F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fleaves;FA;Fcuts;Ffuel;Fnd;Fk;").
Proof.
  intros k nd fuel cuts A leaves rho tp Q Hrun Hlen Hnf Hnb H. apply Pos.leb_le in Hnf.
  eapply (runA_tr segs ok fuel cuts A leaves (JT k nd) rho tp Q Hrun Hlen (JT_okframe k nd) (JT_stable k nd _ Hnf Hnb) H).
Qed.

Lemma JT_entails : ltac2:(tb__ "0|0|
SaS43S43S99S64S64S21S9S4eQ40A1A1S77S0S7S49R8R7R6A3S8A3S0S7S9aR7S4dA2S8A3S0S7S74S4dS1eS41RaA1A1A2S8A3S0S7S61S1eS41RbA1A1R8A2S8A3S0S7S116RaS66R9A1S66R8A1A3S8A3S0S7S73RbS6bRaA1S6bR9A1A3S8A3S0S7S105S20S41ReA1A1S103RcS6aRaA1A2S6aRbA1A3S8A3S0S7S6eS6fRdS67RbA1A2S67RcA1A2S8A3S5bS4cVJT;R11RdA2R10RbRaR9A6S5bS4cVJT;R12RdA2R10S9dRcRfA2RbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fndj;Fndi;Fs;FT;FL;Fk;").
Proof.
  intros k L T s ndi ndj rho tp w. apply (SPA_entails_JA segs AInv CST XGL ALA NF (KcT k) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm k)).
Qed.

Lemma JT_factsT : ltac2:(tb__ "0|0|
SaS64S21S9S4eQ40A1A1S9S51A1S52VJT;R6R5R4R3R2R1A6S87S1fS26R5A1Sd6A3S5F_;F_;Fmd;Ftr;Ftp;Frho;Fnd;Fk;").
Proof. intros; exact I. Qed.

Lemma triple_JT_pre : ltac2:(tb__ "0|0|
SaS64S43S21S9S4eQ40A1A1S79VP0T;VrhoT;A1S13fS4dVrhoT;R4A3S76S4cVok;S5bS4cVJT;R8R7A2R6R5R4A5R3A4F_;F_;S76S4cVok;S5bS4cVJT;R7R6A2R5R4R3A5R2A4F_;FQ;Ftp;Frho;FA;Fnd;Fk;").
Proof.
  intros k nd A rho tp Q H n Hg w [Hsm HJ]. pose proof HJ as (Ai & kc & Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _).
  exact (H HP0 Hav n Hg w (conj Hsm HJ)).
Qed.

Definition exitc_b (k : Z) (facts : list sprop) : bool := ltac2:(tb__ "0|5|
S14SdbS1fS27S2cS29S11eSc6S23Z0A1M0A3A1A1Vfacts;A3S7S7L_;S85Vk;Z3M1A2SdbS1fS27S2cS29S122Sb5S8S7bVk;Z1M2A2A2G0A3A1A1Vfacts;A3S14SdbS1fS27S28S23G2A1M3Sb5S8G1A2M4A2A1Vfacts;A3SdbS1fS27S28G4G3A2A1Vfacts;A3A2X7x2A2").
Lemma exitc_sound : ltac2:(tb__ "0|0|
S19S21S9S1fA1S1S7aZ0R3A2S7aR3Z3A2A2S87S1fS26R3A1R2A3S0S7S133R5R3A2S8A3VP0T;VrhoT;A1S13fS4dVrhoT;R6A3S0S19Sd0VF;A1S7bR8Z1A2A3F_;F_;F_;F_;F_;Ffacts;Frho;Fk;").
Proof.
  intros k rho facts Hk HF H ((_ & _ & HC & _ & HH & _) & _) [Hav _].
  unfold exitc_b in H. apply andb_prop in H as [H1 H2].
  apply (holds_mem rho facts) in H1; [|exact HF]. apply holds_nbeq in H1. unfold vClen in H1. cbn [eval] in H1.
  rewrite lit_unsigned in H1. change (0 mod 2 ^ 64) with 0 in H1.
  rewrite <- (Hav 43%positive) in H1 by (unfold NF; lia). rewrite HC in H1.
  unfold calls_of. rewrite (proj2 (Z.eqb_neq _ _) H1).
  rewrite <- (cnt_word_hdr F (bv_unsigned (rw rhoT 45%positive)) HH). rewrite (Hav 45%positive) by (unfold NF; lia).
  rewrite <- eval_AND3. pose proof (eval_AND3 rho) as EA.
  assert (RA : 0 <= bv_unsigned (eval rho AND3) <= 3).
  { rewrite EA. unfold cnt_word. split; [apply Z.land_nonneg; right; lia|].
    change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (Z.ones 2) with 3. pose proof (Z.mod_pos_bound ((bv_unsigned (rw rho 35) / 2 ^ 16) mod 2 ^ 8) (2 ^ 2) ltac:(lia)). lia. }
  destruct (k <? 3) eqn:K3.
  - apply Z.ltb_lt in K3. apply (holds_mem rho facts) in H2; [|exact HF]. apply holds_nbne in H2.
    unfold cnt_reg in H2. cbn [eval] in H2. rewrite lit_unsigned in H2. change (0 mod 2 ^ 64) with 0 in H2.
    destruct (k + 1 =? 1) eqn:K1.
    + apply Z.eqb_eq in K1. cbn [eval] in H2. lia.
    + apply Z.eqb_neq in K1. cbn [eval] in H2. rewrite U_add, U_lit, <- M64v_eq in H2.
      replace (1 - (k + 1)) with (- k) in H2 by lia.
      rewrite <- (Z.mod_add (- k) 1 (2 ^ 64)) in H2 by lia. rewrite (Z.mod_small (- k + 1 * 2 ^ 64)) in H2 by lia.
      destruct (Z_le_gt_dec k (bv_unsigned (eval rho AND3))) as [LE|GT].
      * replace (bv_unsigned (eval rho AND3) + (- k + 1 * 2 ^ 64)) with ((bv_unsigned (eval rho AND3) - k) + 1 * 2 ^ 64) in H2 by lia.
        rewrite Z.mod_add in H2 by lia. rewrite Z.mod_small in H2 by lia. lia.
      * rewrite Z.mod_small in H2 by lia. lia.
  - apply Z.ltb_ge in K3. assert (k = 3) by lia. subst k.
    apply andb_prop in H2 as [H2 H3]. apply (holds_mem rho facts) in H2; [|exact HF]. apply (holds_mem rho facts) in H3; [|exact HF].
    apply (proj1 (holds_ule _ _ _)) in H2. apply (proj1 (holds_ule _ _ _)) in H3. unfold cnt_reg, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf.add in H2, H3. cbn [Z.eqb Pos.eqb eval] in H2, H3.
    rewrite add_val, !lit_unsigned in H2, H3. change (1 mod 2 ^ 64) with 1 in H2, H3. change ((1 - 3) mod 2 ^ 64) with (2 ^ 64 - 2) in H2, H3.
    destruct (Z_le_gt_dec 2 (bv_unsigned (eval rho AND3))) as [LE|GT].
    + replace (bv_unsigned (eval rho AND3) + (2 ^ 64 - 2)) with ((bv_unsigned (eval rho AND3) - 2) + 1 * 2 ^ 64) in H2, H3 by lia.
      rewrite Z.mod_add in H2, H3 by lia. rewrite Z.mod_small in H2, H3 by lia. lia.
    + rewrite Z.mod_small in H2, H3 by lia. lia.
Qed.

Definition exit1_b (facts : list sprop) : bool := ltac2:(tb__ "0|0|
SdbS1fS27S29S11eSc6S23Z0A1A3A1Vfacts;A3").
Lemma exit1_sound : ltac2:(tb__ "0|0|
S21S9S1fA1S87S1fS26R2A1R1A3S0S7S132R2A1S8A3VP0T;VrhoT;A1S13fS4dVrhoT;R5A3S0S19Sd0VF;A1S7bZ0Z1A2A3F_;F_;F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H ((_ & _ & HC & _) & _) [Hav _].
  apply (holds_mem rho facts) in H; [|exact HF]. apply (proj1 (holds_beq _ _ _)) in H. unfold vClen in H. cbn [eval] in H.
  rewrite lit_unsigned in H. change (0 mod 2 ^ 64) with 0 in H.
  rewrite <- (Hav 43%positive) in H by (unfold NF; lia). rewrite HC in H.
  unfold calls_of. rewrite H. reflexivity.
Qed.

Definition cntg_b (facts : list sprop) : bool := ltac2:(tb__ "0|0|
SdbS1fS27S29S121Sd4S23Z0A1A3A1Vfacts;A3").
Definition cntl_b (facts : list sprop) : bool := ltac2:(tb__ "0|0|
SdbS1fS27S2cS29S121Sd4S23Z0A1A3A1A1Vfacts;A3").
Lemma flags_range : 0 <= flags_of F < 256.
Proof. unfold flags_of. pose proof (bv_unsigned_in_range 8 (nth 1 F (Z_to_bv 8 0))). change (bv_modulus 8) with 256 in *. lia. Qed.
Lemma cntg_sound : ltac2:(tb__ "0|0|
S21S9S1fA1S87S1fS26R2A1R1A3S0S7S130R2A1S8A3VP0T;VrhoT;A1S13fS4dVrhoT;R5A3S7aZ80Sd2VF;A1A2F_;F_;F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H ((_ & _ & _ & _ & _ & HS) & _) [Hav _]. pose proof flags_range as FR.
  apply (holds_mem rho facts) in H; [|exact HF]. apply (proj1 (holds_blt _ _ _)) in H. unfold vFlg in H. cbn [eval] in H.
  rewrite lit_unsigned, (Z.mod_small 0) in H by lia. rewrite <- (Hav 46%positive) in H by (unfold NF; lia). rewrite HS in H.
  pose proof (Zsigned_spec 0) as Z0.
  destruct (flags_of F <? 128) eqn:E; [|apply Z.ltb_ge in E; exact E].
  apply Z.ltb_lt in E. exfalso. pose proof (Zsigned_spec (flags_of F)) as ZS. lia.
Qed.
Lemma cntl_sound : ltac2:(tb__ "0|0|
S21S9S1fA1S87S1fS26R2A1R1A3S0S7S131R2A1S8A3VP0T;VrhoT;A1S13fS4dVrhoT;R5A3S7eSd2VF;A1Z80A2F_;F_;F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H ((_ & _ & _ & _ & _ & HS) & _) [Hav _]. pose proof flags_range as FR.
  apply (holds_mem rho facts) in H; [|exact HF]. apply (proj1 (holds_nblt _ _ _)) in H. unfold vFlg in H. cbn [eval] in H.
  rewrite lit_unsigned, (Z.mod_small 0) in H by lia. rewrite <- (Hav 46%positive) in H by (unfold NF; lia). rewrite HS in H.
  pose proof (Zsigned_spec 0) as Z0.
  destruct (flags_of F <? 128) eqn:E; [apply Z.ltb_lt in E; exact E|].
  apply Z.ltb_ge in E. exfalso. pose proof (Zsigned_spec (flags_of F + 2 ^ 64 - 256)) as ZS. lia.
Qed.

Lemma P0T_SH : ltac2:(tb__ "0|0|
S21VP0T;R1A1S102R2A1F_;Fr;").
Proof. intros r [_ H]. exact H. Qed.
Lemma KtcT : ltac2:(tb__ "0|0|
SaS9S51A1S52VKcT;R3R2R1A3S78VSpec;R3A2F_;Fmd;Ftr;Fk;").
Proof. intros k tr md [_ ->]. apply (Htc k). Qed.
Lemma HKfd1_T : ltac2:(tb__ "0|0|
SaS9S51A1S52VKcT;R3R2R1A3S0S10S54A1S58S59R2A1S14aA2S11S54S57S14aA1A2A3F_;Fmd;Ftr;Fk;").
Proof. intros k tr md [H _]. apply HMDfd1. exact H. Qed.
Lemma HSPEC_T : ltac2:(tb__ "0|5|
SaS19S19S52VMD;R1A1VSpec;S12S51S12S51VT0;S126R5A1A3S12S51S86S4eQ8A1M0S51S55S14aA1M1S165R4A1A4SdS51S53S4fQ40M2R3A2S56R2A1M3A2ScS51A1M4A3A3A3A1F_;Fmd;S9S51A1S52VKcT;R6R2R1A3VSpec;S12S51R3S12S51S86G0S51G1S165R6A1A4SdS51S53S4fG2R5A2G3A2G4A3A3A3A1F_;Fmd;Ftr;F_;Fc;Fn;Fk;").
Proof. intros k n c H tr md [Hmd ->]. exact (H md Hmd). Qed.

Lemma X_exit_pipe : ltac2:(tb__ "0|2|
SaS64S19S19S43S9S1dA1M0S0S10G0A1Sf2R5R2R4R3A4S11G0R1A2A3SdaSbS19S19A2SfS19S19R5R4A4S14bA3S52VMD;R1A1VSpec;S12S51S12S51VT0;S126RaA1A3S12S51S86S4eQ8A1S51S55S14aA1S165R8A1A4SdS51S53S4fQ40M1R7A2S56R2A1A2ScS51A1A3A3A3A1F_;Fmd;S21S9S4eG1A1A1S76S4cVok;S5bS4cVJT;RbRaA2R7R2R1A5S77S2L_;A4Ftp;Frho;F_;F_;F_;FR;FE;Fc;Fn;FndX;Fkx;").
Proof.
  intros kx ndX n c E R Hp Hs HS.
  exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite.X_exit_pipe AInv CST XGL ALA HCSTdrv HLPP ok Spec HOKJ HOKP Hokh (KcT kx) (Kc_okT T0 MD HMDvm kx) rhoT P0T P0T_SH PTrue
           ndX n c E R Hp Hs (HSPEC_T kx n c HS) (HKfd1_T kx)).
Qed.

Lemma X_join : ltac2:(tb__ "0|6|
SaS9S104A1M0G0S19S1cS19S43S9S1dA1M1S0S10S43A1Sf3R7R6Sa2R5R4A2A3S11S43R2A2A3S0S10G1A1Sf2S63ScSbS1cS1cA2M2A1M3ScSbSbS1cS19A2S1cA2A1M4R7S62A4R3R6R4A4S11G1R2A2A3SdaSbS19S19A2SfS19S19R7R5A4S14bA3S52VMD;R1A1VSpec;S12S51S12S51VT0;S126RdA1A3S12S51S86S4eQ8A1S51S55S14aA1S165RaA1A4SdS51S53S4fQ40M5R8A2S56R2A1A2ScS51A1A3A3A3A1F_;Fmd;S21S9S4eG5A1A1S76S4cVok;S5bS4cVJT;ReS63SdG2SfS1cS1cSc3Sc4A4G3A3G4RdS62A4A2Sa2RbRaA2R2R1A5S77S2L_;A4Ftp;Frho;F_;F_;F_;F_;FR;FEx;Fc;Fst;Fn;FbdX;FbdJ;Fkx;").
Proof.
  intros kx bdJ bdX n st c Ex R Hfb Hex Hs HS.
  exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite.X_join AInv CST XGL ALA HCST HXGL HCSTdrv HLPP ok Spec HOKJ HOKP Hokh AC (KcT kx) (Kc_okT T0 MD HMDvm kx) rhoT P0T P0T_SH (KtcT kx) PTrue (fun _ _ _ _ => I)
           bdJ bdX (J_E n st) n c Ex R Hfb Hex Hs (HSPEC_T kx n c HS) (HKfd1_T kx)).
Qed.

Definition N_pf : list lcarve := ltac2:(tb__ "0|e|
SdSbSbS19S19A2M0S9SbSbS19SaA2M1S19A2M2A1M3A2M4SfG0G3SfS19S19Z800c0330M5Z800c0340A4SdG2SfG1S19SfS19SaG5U8M6A4Z0M7A4SdG2SfG1S19SfS19SaZ800c0338G6A4G7A4ScG2A1M8A3A3A4SdG4SfG0G3SfS19S19Zeed98M9Zeed9aA4SdG2SfG1S19SfS19SaG9U1MaA4Z1MbA4SdG2SfG1S19SfS19SaZeed99GaA4GbA4G8A3A3A4SdG4SfG0G3SfS19S19Zeeda0McZeedb8A4SdG2SfG1S19SfS19SaGcG6A4Z7fffffffffffA4SdG2SfG1S19SfS19SaZeeda8G6A4G7A4SdG2SfG1S19SfS19SaZeedb0G6A4G7A4G8A3A3A3A4SdG4SfG0G3SfS19S19Ze6778MdZe6788A4SdG2SfG1S19SfS19SaGdG6A4Zdac00A4SdG2SfG1S19SfS19SaZe6780G6A4Zdb004A4G8A3A3A4ScG4A1A3A3A3A3").
Lemma N_pf_eq : ltac2:(tb__ "0|0|
S0S9S1dA1S86Se2S1dSe3S125A4SbeA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition ms16_shape (x : sv) : sprop := ltac2:(tb__ "0|0|
S2cS29S11eS36S123S36S124S23Z28A1Vx;A3S23ZfA1A3S23Z0A1A3A1").
Lemma ms16_holds : ltac2:(tb__ "0|0|
S21S1cS26R2S12bR1A1A2Fx;Frho;").
Proof.
  intros rho x. unfold ms16_shape. cbn [holds eval branch_taken]. intros HB.
  unfold bv_eqb in HB. apply Z.eqb_eq in HB.
  assert (U0 : bv_unsigned (alu64 ALU_AND (alu64 ALU_OR (Z_to_bv 64 40) (eval rho x)) (Z_to_bv 64 15)) = 0).
  { rewrite HB. rewrite lit_unsigned. reflexivity. }
  rewrite and_val, or_val_A, !lit_unsigned in U0. change (40 mod 2 ^ 64) with 40 in U0. change (15 mod 2 ^ 64) with 15 in U0.
  assert (T : Z.testbit (Z.land (Z.lor 40 (bv_unsigned (eval rho x))) 15) 3 = true).
  { rewrite Z.land_spec, Z.lor_spec. reflexivity. }
  rewrite U0 in T. cbn in T. discriminate.
Qed.

Section LoopP.
Variable k : Z.
Variables kx kx' : nat.
Variables bd0 bd1 : list bitem.
Hypothesis Hcapbd : ltac2:(tb__ "0|0|
S21S7aS7bS7cS10bZ2A2S7fS106Vbd0;R1A2S106Vbd1;R1A2A2A2S10cA2Frho;").
Definition kept : list (sv * sv) := ltac2:(tb__ "0|1|
SdSbS1cS1cA2M0SfS1cS1cS2aS9fA1Sc2A4SdG0SfS1cS1cSc3Sc4A4ScG0A1A3A3").
Definition ndL0 : ndesc := ltac2:(tb__ "0|0|
S63S94ScSbSbS1cS19A2S1cA2A1Vbd0;S62A4").
Definition ndL1 : ndesc := ltac2:(tb__ "0|0|
S63S94ScSbSbS1cS19A2S1cA2A1Vbd1;S62A4").
Variable L : axst.
Variable Lnext : axst.
Variables (Efz : axst) (S1 S2 : sstate) (Rfz : list sobj) (TT : axst) (U1 U3 : sstate) (Tfz : axst).
Variables (Epf : axst) (P1 : sstate) (Rpf : list sobj) (TP : axst) (Q1 Q2 Q4 : sstate) (Upf : axst).
Variable leaves : list leafA.
Variable iw : nat.

Hypothesis HLwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VL;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S98A2S8A3A2A2").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSa1Sa0VL;S8A5S11G0SdS42S4aVEfz;SebA2ScS42A1A3A2A3").

Hypothesis F1 : ltac2:(tb__ "0|0|
S0S10S22A1S114S41VEfz;A1Viw;S23S80S178A1A1A3S11S22VS1;A2A3").
Hypothesis F2n : ltac2:(tb__ "0|0|
S0S10S1dA1SdcS1dS24VS1;A1Viw;A3S11S1dSa9A2A3").
Hypothesis F2e : ltac2:(tb__ "0|0|
S0S22S14eVS1;Viw;Sb0A3VS2;A3").
Hypothesis F2s : ltac2:(tb__ "0|0|
S0S7S14dVS1;VS2;A2S8A3").
Hypothesis HspfE : ltac2:(tb__ "0|0|
S0S7SecS20S41VEfz;A1A1A1S8A3").
Definition Cfz : axst := ltac2:(tb__ "0|0|
S48VS2;S44VEfz;A1S45VEfz;A1A3").
Hypothesis F3n : ltac2:(tb__ "0|1|
S1S0S1aS1eVS2;A1S1eS41VEfz;A1M0A1A3S0S9S1fA1S20VS2;A1S20G0A1A3A2").

Hypothesis HFZ : ltac2:(tb__ "0|1|
S77OF_;S68S4cVKcT;Vkx;A1M0R1A3S168VAInv;VCST;VXGL;G0R2A5F_;Fok';").
Hypothesis Fxk : ltac2:(tb__ "0|1|
S0S7S17dS44S92A1M0G0A2S8A3").
Hypothesis Ffr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S137S92S13dS9eS92A1A3S11G0VRfz;A2A3").
Hypothesis Fcc : ltac2:(tb__ "0|0|
S0S7S138S92S13dS9eS92A1VRfz;SdS43S166ScS43A1A3A5S8A3").
Hypothesis Ftp : ltac2:(tb__ "0|0|
S0S7S143S4dS9eS92A1A2S8A3").
Hypothesis Fdom : ltac2:(tb__ "0|0|
S0S7S140S9eS92A1S4dA2S8A3").
Hypothesis Fnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41VEfz;A1A1A2S8A3").
Hypothesis Fnb : ltac2:(tb__ "0|2|
S1S0S7S61S1eS41VEfz;A1A1M0S63S12SbS1cS1cA2M1S94ScG1A1A3ScSbSbS1cS19A2S1cA2A1Vbd0;S62A4A2S8A3S0S7S107G0Vbd1;A2S8A3A2").
Hypothesis Fpay : ltac2:(tb__ "0|1|
S0S7S108S20S41S92A1A1S23Z0M0A1G0Vbd0;S12S104S103S9eS92A1S13eA2Vbd1;A3A5S8A3").
Hypothesis Fpd : ltac2:(tb__ "0|0|
S0S7Sd9S17cS17bS13dS4dS9eS92A1S1eS41S92A1A1A4S167A3S8A3").
Hypothesis FspfC : ltac2:(tb__ "0|0|
S0S7SecS20S41S92A1A1A1S8A3").
Hypothesis Fknz : ltac2:(tb__ "0|0|
S0S7SeeS20S41S92A1A1S94A2S8A3").
Hypothesis Fro : ltac2:(tb__ "0|0|
S0S7Sd9S1dS1dS16Sf1S20S41S92A1A1R1A2S117S94S15SaA1R1A3A2Lo;VRfz;A3S8A3").
Hypothesis Fxr : ltac2:(tb__ "0|1|
S0S7Sd9SbS1cS1cA2M0G0S16SedR1A1S144S94S15SaA1R1A3A2Lr;S44S92A1A3S8A3").
Hypothesis Fa0 : ltac2:(tb__ "0|1|
S1S1S0S1cS9bS9eS92A1M0PcA2S2aS9fA1A3S0S1cS9bG0PaA2Sd3A3A2S0S1cS9bG0PdA2Sc2A3A2").
Hypothesis FTT : ltac2:(tb__ "0|0|
S0S43S142S13dS92S9eS92A1VRfz;S166A5VTT;A3").

Hypothesis U1n : ltac2:(tb__ "0|0|
S0S10S1dA1SdcS1dS24S41VTT;A1A1U1A3S11S1dS2eS14cSccS23N1f0A1A2S23S80Sb3A1A1S23Z0A1ScS2dA1S2fA5A2A3").
Hypothesis U1e : ltac2:(tb__ "0|0|
S0S22S14eS41VTT;A1U1Sa9A3VU1;A3").
Hypothesis U1s : ltac2:(tb__ "0|0|
S0S7S14dS41VTT;A1VU1;A2S8A3").
Hypothesis U1f : ltac2:(tb__ "0|0|
S0S7SecS20S41VTT;A1A1A1S8A3").
Hypothesis U2 : ltac2:(tb__ "0|2|
S0S7S13cS13S1dS24VU1;A1A2M0S12SaSdSaU1SdSaU0ScSaA1A3A3S88U2M1Se1G0G1A2A2A3A2S8A3").
Hypothesis U3e : ltac2:(tb__ "0|3|
S0S10S22A1S115SeaVU1;S136S24VU1;A1M0S12SaSdSaU1SdSaU0M1ScSaA1A3A3S88U2M2Se1S13S1dG0A2G2A2A2A3A2A2G1A2S11S22VU3;A2A3").
Hypothesis UT : ltac2:(tb__ "0|0|
S0S43S48VU3;S44VTT;A1S45VTT;A1A3VTfz;A3").

Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VTfz;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S95A2S8A3A2A2").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSa1Sa0VTfz;S8A5S11G0SdS42S4aVEpf;SebA2ScS42A1A3A2A3").

Hypothesis P1e : ltac2:(tb__ "0|0|
S0S10S22A1S114S41VEpf;A1U0S23S80S174A1A1A3S11S22VP1;A2A3").
Definition P1c : sstate := ltac2:(tb__ "0|0|
S30S33VP1;A1S34VP1;A1S32VP1;A1S31VP1;A1S35VP1;A1S12S1dS24VP1;A1S86Se2S1dSe3S125A4A3S20VP1;A1S1eVP1;A1S25VP1;A1A9").
Hypothesis P2w : swf P1c = true.
Hypothesis P2c : ltac2:(tb__ "0|0|
S0S7Se5S20VP1;A1S24VP1;A1S44VEpf;A1Sf6Sf8S66S95A1S125A7S8A3").
Hypothesis P2n : ltac2:(tb__ "0|0|
S0S1aS1eVP1;A1S1eS41VEpf;A1A1A3").
Hypothesis HbE : ltac2:(tb__ "0|0|
S0S1cS45VEpf;A1S23S169A1A3").
Definition Cpf0 : axst := ltac2:(tb__ "0|0|
S48S97S44VEpf;A1S45VEpf;A1A3").
Definition Cpf : axst := ltac2:(tb__ "0|0|
S172Sa4S96Vk;A2S96A2").
Hypothesis P3b : ltac2:(tb__ "0|0|
S0S7Sd9S1fS2bS1eS97A1A1S12S1fSa4S96Vk;A2S20S97A1A3A3S8A3").
Hypothesis P3h : ltac2:(tb__ "0|0|
S1fSdaS1fR1Sa4S96Vk;A2A3S3S1cS1cS0S1fR3S12bR1A1A3Lx;A2F_;Fq;").

Hypothesis Pfr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S137S93Sa3Vk;A1Sa6S93Vk;A2A3S11G0VRpf;A2A3").
Hypothesis Pcc : ltac2:(tb__ "0|0|
S0S7S139S93Sa3Vk;A1Sa6S93Vk;A2VRpf;S86S42S43S46S176Vk;A1A4A5S8A3").
Hypothesis Pnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41S93A1A1A2S8A3").
Hypothesis Pnb : ltac2:(tb__ "0|0|
S0S7S61S1eS41S93A1A1S95A2S8A3").
Hypothesis Pfb : ltac2:(tb__ "0|1|
S0S7Sd9S1fS2bS1eS41S93A1M0A1A1S20G0A1A3S8A3").
Hypothesis Pk : ltac2:(tb__ "0|2|
S4S1S0S19Vk;Z0A3S1S0SaVkx;U0A3S0SaVkx';U1M0A3M1A2A2S1S177Vk;A1S1S0SaVkx;G0A3G1A2A2A2").
Hypothesis PTP : ltac2:(tb__ "0|0|
S0S43S142Sa3Vk;A1S93Sa6S93Vk;A2VRpf;S175Vk;A1A5VTP;A3").

Hypothesis Q1e : ltac2:(tb__ "0|1|
S0S7S13cS13S1dS24S41VTP;A1A1A2M0SabG0A1A2S8A3").
Hypothesis Q1o : ltac2:(tb__ "0|1|
S0S9S1dA1S136S24S41VTP;A1A1M0SabS13S1dG0A2A1A2S24VQ1;A1A3").
Hypothesis Q1d : ltac2:(tb__ "0|0|
S0S22SeaS41VTP;A1S24VQ1;A1A2VQ1;A3").
Hypothesis Q1s : ltac2:(tb__ "0|1|
S0S9S1dA1S24VQ1;A1M0S12S1dS89S1dSe1S13S1dG0A2U4A2G0A3S86Se2S1dSe3S125A4A3A3").
Hypothesis Q2e : ltac2:(tb__ "0|1|
S0S22SeaVQ1;S89S1dSe1S13S1dS24VQ1;A1M0A2U4A2G0A3A2VQ2;A3").
Hypothesis Q2u : ltac2:(tb__ "0|0|
S0S7Se6Sf6S125A2S8A3").
Hypothesis Q2n : ltac2:(tb__ "0|0|
S0S7S61S1eVQ1;A1S95A2S8A3").
Hypothesis Q3e : ltac2:(tb__ "0|2|
S0S7S13cS13S1dS24VQ2;A1A2M0S12SaSdSaU8SdSaU0ScSaA1A3A3S12SaS88U1U7A2S88U9M1Se1G0G1A2A2A3A3A2S8A3").
Hypothesis Q4e : ltac2:(tb__ "0|3|
S0S10S22A1S115SeaVQ2;S136S24VQ2;A1M0S12SaSdSaU8SdSaU0M1ScSaA1A3A3S12SaS88U1U7A2S88U9M2Se1S13S1dG0A2G2A2A2A3A3A2A2G1A2S11S22VQ4;A2A3").
Hypothesis QU : ltac2:(tb__ "0|0|
S0S43S48VQ4;S44VTP;A1S45VTP;A1A3VUpf;A3").

Hypothesis HUwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VUpf;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S95A2S8A3A2A2").
Hypothesis Hrun3 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSa1Sa0VUpf;S8A5S11G0Vleaves;A2A3").
Hypothesis Hleaves : ltac2:(tb__ "0|3|
S42SdaS42R1Vleaves;A3S4S3S99S99S1S0S7S49S46R3A1M0VLnext;R1A3S8A3S1S0S7S9aR1S4dA2S8A3S1S0S7S74S4dS1eS41G0A1M1A1M2A2S8A3S1S0S7S61G2S95A2S8A3S1S0S7S116R1S94S94A3S8A3S0S7S105S20G1A1S103R1Vbd1;A2Vbd1;A3S8A3A2A2A2A2A2Ls;A2S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx';S95A2S46R4A1R2R1A5S77S2L_;A4Ftp;Frho;A2F_;FLf;").
Hypothesis Hnext : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx';S95A2VLnext;R2R1A5S77S2L_;A4Ftp;Frho;").

Lemma X_loopP : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx;S98A2VL;R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct HLwf as (W1 & W2 & W3). destruct Fnb as [Fnb1 Fnb2]. destruct Fa0 as [[Fa12 Fa10] Fa13]. destruct F3n as [F3nx F3f].
  destruct HTwf as (V1 & V2 & V3). destruct HUwf as (Y1 & Y2 & Y3).

  eapply JT_run; [exact Hrun1 | exact W2 | exact W1 | exact W3 |].
  intros Lf rho1 [<-|[]] Hag1. cbn [la_state].
  apply triple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho1 sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF | exact HspfE]. }

  eapply (triple_conseq (P := SPA segs (JT kx ndL0) Cfz rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof (SPA_split segs (JT kx ndL0) rho1 Efz iw (SLit (- fz_frame)) S1 tp w F1 HS) as HS1.
    unfold Cfz. rewrite <- F2e. change (mkAX (set_obj_at S1 iw O_WfzT) (ax_X Efz) (ax_base Efz)) with (ax_setS (mkAX S1 (ax_X Efz) (ax_base Efz)) (set_obj_at S1 iw O_WfzT)).
    apply (SPA_reslice segs (JT kx ndL0) rho1 (mkAX S1 (ax_X Efz) (ax_base Efz)) iw O_WloT O_WfzT tp w F2n); try reflexivity.
    - cbn [ax_S]. rewrite F2e. exact F2s.
    - unfold O_WloT, O_WfzT, spT. rewrite !obj_range_lits by (unfold WDP, DEEP, fz_frame; lia).
      rewrite !U_add_lit by (unfold fz_frame; try lia; rewrite U_add_lit by lia; lia). unfold WDP, DEEP, fz_frame. f_equal; lia.
    - unfold O_WfzT, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold WDP, DEEP, fz_frame; lia). unfold WDP, DEEP, fz_frame; lia.
    - exact HS1. }

  assert (HnxC : ss_next (ax_S Cfz) = ss_next (ax_S Efz)) by (unfold Cfz; cbn [ax_S]; exact F3nx).
  unfold ndL0, kept.

  assert (Fnbc : bd_below (ss_next (ax_S Efz)) (bd_subst (s_fz Cfz) bd_fz) = true).
  { pose proof (proj1 (Pos.leb_le _ _) Fnx) as Hnf. unfold NF in Hnf. unfold bd_fz, bd_subst, bi_subst, lf_subst, bd_below, vLEN. cbn [map forallb bi_f fst snd atom_subst asv sv_subst].
    rewrite Fa13. unfold vPlen. cbn [sv_below]. try (assert (E : (44 <? ss_next (ax_S Efz))%positive = true) by (apply Pos.ltb_lt; lia); rewrite E). reflexivity. }
  apply (box_open_T segs AInv CST XGL ALA NF (KcT kx) rhoT P0T [] [] PTrue ok BX0 [(SVar vP, vPlen); (vB, vCap)] [] bd0 (bd_subst (s_fz Cfz) bd_fz) bd1 Cfz rho1 tp _ (BXnn_mk00 0) Fpay).
  { intros _. pose proof (Hcapbd rho1) as HC. assert (LMP : 0 <= LARGE_MIN) by (unfold LARGE_MIN; lia). cbn [length]. lia. }
  intros BXc HBXc Hback.
  rewrite <- (app_nil_r [(SVar vP, vPlen); (vB, vCap)]).
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJACP.client_callA_P segs AInv CST XGL ALA HCST HXGL DrvJ.segs_topA NF (KcT kx) rhoT P0T [] [] BXc PTrue (Kc_okT T0 MD HMDvm kx) HBXc
           (P0_fz CST) PTrue (fun _ H => H) (fun _ _ _ H => H) Pre_fz nd_fz0 PD_fz NF eq_refl eq_refl eq_refl
           (fun ok' FBc FFc BXc rho2 tp2 Hok HB => HFZ ok' Hok FBc FFc BXc rho2 tp2 HB) eq_refl
           ok Cfz (s_fz Cfz) Rfz (ax_X Cfz) rho1 tp [(SVar vP, vPlen); (vB, vCap)] [] [] (bd_subst (s_fz Cfz) bd_fz) [] ANone (fun _ => False)
           (okKT kx) Fxk Ffr Fcc Ftp Fdom).
  - rewrite HnxC. exact Fnx.
  - rewrite HnxC. pose proof (nd_below_split _ _ Fnb1) as (N1 & N2 & _ & N4). pose proof (nd_below_len _ _ Fnb1) as N5. cbn [nd_tv nd_fr nd_bd nd_am] in N1, N2, N4, N5. apply nd_below_intro; cbn [nd_tv nd_fr nd_bd nd_am]; [exact N1 | exact N2 | exact Fnbc | exact N4 | exact N5].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply payA_self. reflexivity.
  - rewrite HnxC. unfold Cfz in Fpd. cbn [ax_S] in Fpd. rewrite F3nx in Fpd. exact Fpd.
  -
    intros Ai ms HF' HP0 Hav HB HFF HN HD HZ HFR HM HTPA HTok HKz HMz. rewrite app_nil_r in HN, HD, HZ.
    split; [eapply robjs_okF_drv; [exact HF' | exact FspfC | exact (T0_of_site _ _ _ HTPA HTok) | exact Fknz | exact Fro]|].
    split; [eapply xrs_okF_drv; [exact HF' | exact FspfC | exact (T0_of_site _ _ _ HTPA HTok) | exact Fknz | exact Fxr]|].
    unfold P0_fz. split; [|split; [intros c; reflexivity | exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ot.DrvTPres.fz_site_PRES CST XGL rhoT rho1 Rfz ms _ _ (P0T_SH _ HP0) Hav HKz HMz HF' FspfC Fa10 Ftp)]].
    intros a Ha. unfold uval, vDAT, vLEN in Ha. cbn [eval] in Ha. rewrite !rw_call' in Ha. rewrite Fa12, Fa13 in Ha.
    eapply (kept_in_FBx _ rho1 (ss_facts (ax_S Cfz)) [(SVar vP, vPlen); (vB, vCap)] (SVar vP, vPlen) a HF' Fknz); [left; reflexivity|].
    unfold tvv. cbn [fst snd]. exact Ha.
  -
    intros d rho' tp' [<-|[]] Hag'. cbn [fst snd nd_tv nd_bd nd_am nd_fz1 import_tv bd_subst am_subst map app].
    unfold T_afterA3. rewrite import_postA3_full. fold (T_afterA Pre_fz Cfz (s_fz Cfz) Rfz P_fz). rewrite FTT.
    fold kept. fold ndL1.

    eapply (triple_conseq (P := SPA segs (JT kx ndL1) TT rho' tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { exact (box_close segs AInv CST XGL NF (KcT kx) rhoT P0T [] [] PTrue BX0 BXc bd1 kept [] [] ANone (ss_next (ax_S Cfz)) TT rho1 rho' tp' w (BXnn_mk00 0) Hback Hag' ltac:(rewrite HnxC; exact Fnb2) HS). }

    apply triple_factsA. intros HF2.
    assert (Hsp' : 0x7fff80000000 <= bv_unsigned (eval rho' sp0) <= 2 ^ 47 - 224).
    { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF2 | exact U1f]. }
    eapply (triple_conseq (P := SPA segs (JT kx ndL1) Tfz rho' tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { assert (HS1 : SPA segs (JT kx ndL1) (ax_setS TT U1) rho' tp' w).
      { rewrite <- U1e. apply (SPA_reslice segs (JT kx ndL1) rho' TT 1 _ O_WloT tp' w U1n); try reflexivity.
        - rewrite U1e. exact U1s.
        - unfold O_WloT, spT. rewrite !obj_range_lits by (unfold WDP, DEEP, fz_frame; lia).
          rewrite !U_add_lit by (unfold fz_frame; try lia; rewrite U_add_lit by lia; lia). unfold WDP, DEEP, fz_frame. f_equal; lia.
        - unfold O_WloT, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP, fz_frame; lia). unfold DEEP, fz_frame; lia.
        - exact HS. }
      pose proof (AxXform.SPA_select segs (JT kx ndL1) rho' (mkAX U1 (ax_X TT) (ax_base TT)) _ tp' w U2 HS1) as HS2.
      pose proof (SPA_merge segs (JT kx ndL1) rho' (mkAX (set_objs U1 (select (ss_objs U1) ([1; 0] ++ seq 2 (length (ss_objs U1) - 2))%nat)) (ax_X TT) (ax_base TT)) 0 U3 tp' w U3e HS2) as HS3.
      rewrite <- UT. exact HS3. }

    eapply JT_run; [exact Hrun2 | exact V2 | exact V1 | exact V3 |].
    intros Lf rho2 [<-|[]] Hag2. cbn [la_state].
    apply triple_factsA. intros HF3.

    eapply (triple_conseq (P := SPA segs (JT kx ndL1) Cpf rho2 tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { pose proof (SPA_split segs (JT kx ndL1) rho2 Epf 0 (SLit (- PW)) P1 tp' w P1e HS) as HS1.
      assert (HS2 : SPA segs (JT kx ndL1) Cpf0 rho2 tp' w).
      { pose proof (carveT (KcT kx) ndL1 (mkAX P1 (ax_X Epf) (ax_base Epf)) rho2 tp' w N_pf (ss_next P1) HS1) as X.
        cbn zeta in X. cbn [ax_S ax_setS ax_X ax_base] in X. apply X; [exact P2w | apply Pos.leb_refl | exact HbE | exact P2c]. }
      unfold Cpf, ax_add_facts.
      change (ax_setS Cpf0 (add_facts (pf_hints Cpf0 k) (ax_S Cpf0))) with (ax_with_facts Cpf0 (pf_hints Cpf0 k ++ ss_facts (ax_S Cpf0))).
      apply (SPA_refacts_JA segs); [exact HS2 | exact P3b |].
      intros tr md HJ HFc. apply Forall_app. split; [|exact HFc]. apply Forall_forall. intros q Hq.
      destruct (P3h q Hq) as [x ->]. apply ms16_holds. }

    assert (HnxP : ss_next (ax_S Cpf) = ss_next (ax_S Epf)).
    { unfold Cpf, Cpf0, ax_add_facts. cbn [ax_S ss_next add_facts P1c]. exact P2n. }
    set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => JT kx ndL1 rho2 t tr md).
    assert (JpK : forall r t tr md, Jp r t tr md -> MD md /\ tr = T0 ++ EVk kx) by (intros r t tr md HJ; exact (JT_Kc _ _ _ _ _ _ HJ)).
    assert (HstJp : stableA segs NF Jp).
    { intros r r' t tr md md' Hag Hme HJ. unfold Jp in HJ |- *. destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF (KcT kx) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm kx) ALA (ss_next (ax_S Cpf)) ndL1 Ai kc rho2 rho2 t tr md md');
        [apply Pos.leb_le; exact Pnx | exact Pnb | apply agree_below_refl | exact Hme | exact HJi]. }
    assert (HokJp : ok_frameA segs ok Jp).
    { apply HOKJ. intros r t tr md HJ. destruct (JpK _ _ _ _ HJ) as [_ ->]. apply Htc. }
    assert (CONT : forall Lf rho3, In Lf (Posts_pf k) -> agree_below (ss_next (ax_S Cpf)) rho2 rho3 ->
              triple segs ok (SPA segs (JT kx' ndL1) (ax_add_facts (ss_facts (ax_S Cpf)) (import_postA (s_pf Cpf k) (PreP k) (la_state Lf) Cpf Rpf)) rho3 tp') (fun _ => False)).
    { intros Lf rho3 HinL Hag3. unfold Posts_pf in HinL. destruct HinL as [<-|[]]. cbn [la_state].
      fold (T_afterA (PreP k) Cpf (s_pf Cpf k) Rpf (P_pf k)). rewrite PTP.

      eapply (triple_conseq (P := fun w => exists rho4, SPA segs (JT kx' ndL1) Upf rho4 tp' w)); [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct w as [tr [ms md]].
        pose proof (AxXform.SPA_select segs (JT kx' ndL1) rho3 TP _ tp' _ Q1e HS) as HS1. rewrite Q1o, Q1d in HS1.
        pose proof (uncarveT (KcT kx') ndL1 (mkAX Q1 (ax_X TP) (ax_base TP)) rho3 tp' tr ms md _ N_pf (Kc_okT T0 MD HMDvm kx') Q1s Q2u eq_refl Q2n HS1) as HS2.
        cbn [ax_S ax_setS ax_X ax_base] in HS2. rewrite Q2e in HS2.
        set (rho4 := rho_absorb rho3 (map lc_obj N_pf) (vms md tp' ms)) in HS2. exists rho4.
        pose proof (AxXform.SPA_select segs (JT kx' ndL1) rho4 (mkAX Q2 (ax_X TP) (ax_base TP)) _ tp' _ Q3e HS2) as HS3.
        pose proof (SPA_merge segs (JT kx' ndL1) rho4 (mkAX (set_objs Q2 (select (ss_objs Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs Q2) - 9))%nat)) (ax_X TP) (ax_base TP)) 0 Q4 tp' _ Q4e HS3) as HS4.
        rewrite <- QU. exact HS4. }
      apply triple_ex. intros rho4.

      eapply JT_run; [exact Hrun3 | exact Y2 | exact Y1 | exact Y3 |].
      intros Lf rho5 HinLf Hag5.
      destruct (Hleaves Lf HinLf) as [(s5 & E1 & E2 & E3 & E4 & E5 & E6)|HX]; [|apply HX].
      eapply (triple_conseq (P := SPA segs (JT kx' ndL1) Lnext (rho_sub rho5 s5) tp')); [intros w HS | intros w' Hw'; exact Hw' | apply Hnext].
      apply (JT_entails kx' (la_state Lf) Lnext s5 ndL1 ndL1 rho5 tp' w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS). }
    destruct Pk as [(Ek & Ekx & Ekx')|(Hkok & Ekx & Ekx')].
    +
      subst kx kx'. unfold PreP in *. rewrite Ek in *. cbn [Z.eqb] in *.
      apply (pcallT (KcT 0) (KcT 1) Cpf Pre_pf0 (s_pf Cpf 0) Rpf (Posts_pf 0) rho2 tp' ndL1 Jp (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.Kw Jp 2) (fun _ => False) (Kc_okT T0 MD HMDvm 1)).
      * intros rho6 tp6. apply (printf0_sum ok Jp HstJp).
        -- intros r t tr md HJ. apply HMDfd1. exact (proj1 (JpK _ _ _ _ HJ)).
        -- intros n'. apply HOKJ. intros r t tr md (tr0 & HJ & ->). destruct (JpK _ _ _ _ HJ) as [_ ->].
           destruct (Htc 1%nat) as (tf & Htf & Hpre). exists tf. split; [exact Htf|]. eapply is_prefix_trans; [|exact Hpre].
           cbn [EVk]. rewrite app_nil_r. apply is_prefix_app_mono.
           unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.EVS. change (firstn 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.MSG0) with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.MSG0. clear. generalize OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.MSG0 as l. intros l.
           induction n' as [|n' IH] in l |- *; [apply is_prefix_nil|]. destruct l; cbn; [exact I|]. split; [reflexivity | apply IH].
        -- intros n'. apply HOKP. intros r t tr md (tr0 & HJ & ->). destruct (JpK _ _ _ _ HJ) as [_ ->].
           destruct (Htc 1%nat) as (tf & Htf & Hpre). exists tf. split; [exact Htf|]. eapply is_prefix_trans; [|exact Hpre].
           cbn [EVk]. rewrite app_nil_r. apply is_prefix_app_mono.
           unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.EVS. change (firstn 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.MSG0) with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.MSG0. clear. generalize OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.MSG0 as l. intros l.
           induction n' as [|n' IH] in l |- *; [apply is_prefix_nil|]. destruct l; cbn; [exact I|]. split; [reflexivity | apply IH].
      * exact Pfr.
      * exact Pcc.
      * exact Pnx.
      * exact Pnb.
      * exact Pfb.
      * intros tr ms md Hsm HJ. exact HJ.
      * intros rhoL tr' md' (tr0 & HJ & ->). unfold Jp in HJ. destruct HJ as (Ai & kc & Hav & [Hmd Htr] & REST).
        exists Ai, kc. split; [exact Hav|]. split; [|exact REST]. split; [exact Hmd|]. rewrite Htr. cbn [EVk]. rewrite app_nil_r. reflexivity.
      * exact CONT.
    +
      subst kx kx'.
      assert (EP : PreP k = Pre_pf k).
      { unfold PreP. destruct Hkok as [->|[->| ->]]; reflexivity. }
      rewrite EP in *.
      apply (pcallT (KcT 1) (KcT 1) Cpf (Pre_pf k) (s_pf Cpf k) Rpf (Posts_pf k) rho2 tp' ndL1 Jp Jp (fun _ => False) (Kc_okT T0 MD HMDvm 1)).
      * intros rho6 tp6. apply (printf_sum ok Jp HokJp HstJp k rho6 tp6 Hkok).
      * exact Pfr.
      * exact Pcc.
      * exact Pnx.
      * exact Pnb.
      * exact Pfb.
      * intros tr ms md Hsm HJ. exact HJ.
      * intros rhoL tr' md' HJ. exact HJ.
      * exact CONT.
Qed.
End LoopP.

Section LoopE.
Variable k : Z.
Variables kx kx' : nat.
Variables bd0 bd1 : list bitem.
Hypothesis Hcapbd : ltac2:(tb__ "0|0|
S21S7aS7bS7cS10bZ2A2S7fS106Vbd0;R1A2S106Vbd1;R1A2A2A2S10cA2Frho;").
Definition keptE : list (sv * sv) := ltac2:(tb__ "0|1|
SdSbS1cS1cA2M0SfS1cS1cSc3Sc4A4ScG0A1A3").
Definition ndE0 : ndesc := ltac2:(tb__ "0|0|
S63S8dScSbSbS1cS19A2S1cA2A1Vbd0;S62A4").
Definition ndE1 : ndesc := ltac2:(tb__ "0|0|
S63S8dScSbSbS1cS19A2S1cA2A1Vbd1;S62A4").
Variable L : axst.
Variable Lnext : axst.
Variables (Efz : axst) (S1 S2 S3 : sstate) (Rfz : list sobj) (TT : axst) (U1 U3 U4 : sstate) (Tfz : axst).
Variables (bE : sv) (dE : odefault).
Variables (Epf : axst) (P1 : sstate) (Rpf : list sobj) (TP : axst) (Q1 Q2 Q4 : sstate) (Upf : axst).
Variable leaves : list leafA.
Variable iw : nat.

Hypothesis HLwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VL;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S91A2S8A3A2A2").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSa1Sa0VL;S8A5S11G0SdS42S4aVEfz;SebA2ScS42A1A3A2A3").

Hypothesis F1 : ltac2:(tb__ "0|0|
S0S10S22A1S114S41VEfz;A1Viw;S23S80S178A1A1A3S11S22VS1;A2A3").
Hypothesis F2n : ltac2:(tb__ "0|0|
S0S10S1dA1SdcS1dS24VS1;A1Viw;A3S11S1dSa9A2A3").
Hypothesis F2e : ltac2:(tb__ "0|0|
S0S22S14eVS1;Viw;Sb0A3VS2;A3").
Hypothesis F2s : ltac2:(tb__ "0|0|
S0S7S14dVS1;VS2;A2S8A3").
Hypothesis HspfE : ltac2:(tb__ "0|0|
S0S7SecS20S41VEfz;A1A1A1S8A3").

Hypothesis F2a : ltac2:(tb__ "0|0|
S0S22S187VS2;Sb1A2VS3;A3").
Hypothesis F2w : swf S3 = true.
Hypothesis F2o : ltac2:(tb__ "0|0|
S0S7S3eS1eVS2;A1Sb1A2S8A3").
Definition CfzE : axst := ltac2:(tb__ "0|1|
S48VS3;S12SbS1cS1cA2M0S44VEfz;A1SdG0Sb4ScG0A1A3A3S45VEfz;A1A3").
Hypothesis F3n : ltac2:(tb__ "0|1|
S1S0S1aS1eVS3;A1S1eS41VEfz;A1M0A1A3S0S9S1fA1S20VS3;A1S20G0A1A3A2").

Hypothesis HFZ : ltac2:(tb__ "0|1|
S77OF_;S68S4cVKcT;Vkx;A1M0R1A3S168VAInv;VCST;VXGL;G0R2A5F_;Fok';").
Hypothesis Fxk : ltac2:(tb__ "0|1|
S0S7S17dS44S8bA1M0G0A2S8A3").
Hypothesis Ffr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S137S8bS13dS9eS8bA1A3S11G0VRfz;A2A3").
Hypothesis Fcc : ltac2:(tb__ "0|0|
S0S7S138S8bS13dS9eS8bA1VRfz;SdS43S166ScS43A1A3A5S8A3").
Hypothesis Ftp : ltac2:(tb__ "0|0|
S0S7S143S4dS9eS8bA1A2S8A3").
Hypothesis Fdom : ltac2:(tb__ "0|0|
S0S7S140S9eS8bA1S4dA2S8A3").
Hypothesis Fnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41VEfz;A1A1A2S8A3").
Hypothesis Fnb : ltac2:(tb__ "0|2|
S1S0S7S61S1eS41VEfz;A1A1M0S63S12SbS1cS1cA2M1S8dScG1A1A3ScSbSbS1cS19A2S1cA2A1Vbd0;S62A4A2S8A3S0S7S107G0Vbd1;A2S8A3A2").
Hypothesis Fpay : ltac2:(tb__ "0|1|
S0S7S108S20S41S8bA1A1S23Z0M0A1G0Vbd0;S12S104S103S9eS8bA1S13eA2Vbd1;A3A5S8A3").
Hypothesis Fpd : ltac2:(tb__ "0|0|
S0S7Sd9S17cS17bS13dS4dS9eS8bA1S1eS41S8bA1A1A4S167A3S8A3").
Hypothesis FspfC : ltac2:(tb__ "0|0|
S0S7SecS20S41S8bA1A1A1S8A3").
Hypothesis Fknz : ltac2:(tb__ "0|0|
S0S7SeeS20S41S8bA1A1S8dA2S8A3").
Hypothesis Fro : ltac2:(tb__ "0|0|
S0S7Sd9S1dS1dS16Sf1S20S41S8bA1A1R1A2S117S8dS15SaA1R1A3A2Lo;VRfz;A3S8A3").
Hypothesis Fxr : ltac2:(tb__ "0|1|
S0S7Sd9SbS1cS1cA2M0G0S16SedR1A1S144S8dS15SaA1R1A3A2Lr;S44S8bA1A3S8A3").
Hypothesis Fa0 : ltac2:(tb__ "0|1|
S1S0S1cS9bS9eS8bA1M0PdA2S23Z0A1A3S0S1cS9bG0PaA2Sd3A3A2").
Hypothesis FTT : ltac2:(tb__ "0|0|
S0S43S142S13dS8bS9eS8bA1VRfz;S166A5VTT;A3").

Hypothesis U1n : ltac2:(tb__ "0|0|
S0S10S1dA1SdcS1dS24S41VTT;A1A1U1A3S11S1dS2eS14cSccS23N1f0A1A2S23S80Sb3A1A1S23Z0A1ScS2dA1S2fA5A2A3").
Hypothesis U1e : ltac2:(tb__ "0|0|
S0S22S14eS41VTT;A1U1Sa9A3VU1;A3").
Hypothesis U1s : ltac2:(tb__ "0|0|
S0S7S14dS41VTT;A1VU1;A2S8A3").
Hypothesis U1f : ltac2:(tb__ "0|0|
S0S7SecS20S41VTT;A1A1A1S8A3").
Hypothesis U2 : ltac2:(tb__ "0|2|
S0S7S13cS13S1dS24VU1;A1A2M0S12SaSdSaU1SdSaU0ScSaA1A3A3S88U2M1Se1G0G1A2A2A3A2S8A3").
Hypothesis U3e : ltac2:(tb__ "0|3|
S0S10S22A1S115SeaVU1;S136S24VU1;A1M0S12SaSdSaU1SdSaU0M1ScSaA1A3A3S88U2M2Se1S13S1dG0A2G2A2A2A3A2A2G1A2S11S22VU3;A2A3").

Hypothesis U4n : ltac2:(tb__ "0|1|
S0S10S1dA1SdcS1dS24VU3;A1U1A3S11S1dS2eVbE;S23Z0A1M0G0ScS2dA1VdE;A5A2A3").
Hypothesis U4e : drop_obj_at U3 1 = U4.
Hypothesis UT : ltac2:(tb__ "0|0|
S0S43Sd1Sb4S48VU4;S44VTT;A1S45VTT;A1A3A2VTfz;A3").

Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VTfz;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S8eA2S8A3A2A2").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSa1Sa0VTfz;S8A5S11G0SdS42S4aVEpf;SebA2ScS42A1A3A2A3").

Hypothesis P1e : ltac2:(tb__ "0|0|
S0S10S22A1S114S41VEpf;A1U0S23S80S174A1A1A3S11S22VP1;A2A3").
Definition P1cE : sstate := ltac2:(tb__ "0|0|
S30S33VP1;A1S34VP1;A1S32VP1;A1S31VP1;A1S35VP1;A1S12S1dS24VP1;A1S86Se2S1dSe3S125A4A3S20VP1;A1S1eVP1;A1S25VP1;A1A9").
Hypothesis P2w : swf P1cE = true.
Hypothesis P2c : ltac2:(tb__ "0|0|
S0S7Se5S20VP1;A1S24VP1;A1S44VEpf;A1Sf6Sf8S66S8eA1S125A7S8A3").
Hypothesis P2n : ltac2:(tb__ "0|0|
S0S1aS1eVP1;A1S1eS41VEpf;A1A1A3").
Hypothesis HbE : ltac2:(tb__ "0|0|
S0S1cS45VEpf;A1S23S169A1A3").
Definition Cpf0E : axst := ltac2:(tb__ "0|0|
S48S90S44VEpf;A1S45VEpf;A1A3").
Definition CpfE : axst := ltac2:(tb__ "0|0|
S172Sa4S8fVk;A2S8fA2").
Hypothesis P3b : ltac2:(tb__ "0|0|
S0S7Sd9S1fS2bS1eS90A1A1S12S1fSa4S8fVk;A2S20S90A1A3A3S8A3").
Hypothesis P3h : ltac2:(tb__ "0|0|
S1fSdaS1fR1Sa4S8fVk;A2A3S3S1cS1cS0S1fR3S12bR1A1A3Lx;A2F_;Fq;").

Hypothesis Pfr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S137S8cSa3Vk;A1Sa6S8cVk;A2A3S11G0VRpf;A2A3").
Hypothesis Pcc : ltac2:(tb__ "0|0|
S0S7S139S8cSa3Vk;A1Sa6S8cVk;A2VRpf;S86S42S43S46S176Vk;A1A4A5S8A3").
Hypothesis Pnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41S8cA1A1A2S8A3").
Hypothesis Pnb : ltac2:(tb__ "0|0|
S0S7S61S1eS41S8cA1A1S8eA2S8A3").
Hypothesis Pfb : ltac2:(tb__ "0|1|
S0S7Sd9S1fS2bS1eS41S8cA1M0A1A1S20G0A1A3S8A3").
Hypothesis Pk : ltac2:(tb__ "0|2|
S4S1S0S19Vk;Z0A3S1S0SaVkx;U0A3S0SaVkx';U1M0A3M1A2A2S1S177Vk;A1S1S0SaVkx;G0A3G1A2A2A2").
Hypothesis PTP : ltac2:(tb__ "0|0|
S0S43S142Sa3Vk;A1S8cSa6S8cVk;A2VRpf;S175Vk;A1A5VTP;A3").

Hypothesis Q1e : ltac2:(tb__ "0|1|
S0S7S13cS13S1dS24S41VTP;A1A1A2M0SabG0A1A2S8A3").
Hypothesis Q1o : ltac2:(tb__ "0|1|
S0S9S1dA1S136S24S41VTP;A1A1M0SabS13S1dG0A2A1A2S24VQ1;A1A3").
Hypothesis Q1d : ltac2:(tb__ "0|0|
S0S22SeaS41VTP;A1S24VQ1;A1A2VQ1;A3").
Hypothesis Q1s : ltac2:(tb__ "0|1|
S0S9S1dA1S24VQ1;A1M0S12S1dS89S1dSe1S13S1dG0A2U4A2G0A3S86Se2S1dSe3S125A4A3A3").
Hypothesis Q2e : ltac2:(tb__ "0|1|
S0S22SeaVQ1;S89S1dSe1S13S1dS24VQ1;A1M0A2U4A2G0A3A2VQ2;A3").
Hypothesis Q2u : ltac2:(tb__ "0|0|
S0S7Se6Sf6S125A2S8A3").
Hypothesis Q2n : ltac2:(tb__ "0|0|
S0S7S61S1eVQ1;A1S8eA2S8A3").
Hypothesis Q3e : ltac2:(tb__ "0|2|
S0S7S13cS13S1dS24VQ2;A1A2M0S12SaSdSaU8SdSaU0ScSaA1A3A3S12SaS88U1U7A2S88U9M1Se1G0G1A2A2A3A3A2S8A3").
Hypothesis Q4e : ltac2:(tb__ "0|3|
S0S10S22A1S115SeaVQ2;S136S24VQ2;A1M0S12SaSdSaU8SdSaU0M1ScSaA1A3A3S12SaS88U1U7A2S88U9M2Se1S13S1dG0A2G2A2A2A3A3A2A2G1A2S11S22VQ4;A2A3").
Hypothesis QU : ltac2:(tb__ "0|0|
S0S43S48VQ4;S44VTP;A1S45VTP;A1A3VUpf;A3").

Hypothesis HUwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VUpf;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S8eA2S8A3A2A2").
Hypothesis Hrun3 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSa1Sa0VUpf;S8A5S11G0Vleaves;A2A3").
Hypothesis Hleaves : ltac2:(tb__ "0|3|
S42SdaS42R1Vleaves;A3S4S3S99S99S1S0S7S49S46R3A1M0VLnext;R1A3S8A3S1S0S7S9aR1S4dA2S8A3S1S0S7S74S4dS1eS41G0A1M1A1M2A2S8A3S1S0S7S61G2S8eA2S8A3S1S0S7S116R1S8dS8dA3S8A3S0S7S105S20G1A1S103R1Vbd1;A2Vbd1;A3S8A3A2A2A2A2A2Ls;A2S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx';S8eA2S46R4A1R2R1A5S77S2L_;A4Ftp;Frho;A2F_;FLf;").
Hypothesis Hnext : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx';S8eA2VLnext;R2R1A5S77S2L_;A4Ftp;Frho;").

Lemma X_loopE : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx;S91A2VL;R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct HLwf as (W1 & W2 & W3). destruct Fnb as [Fnb1 Fnb2]. destruct Fa0 as [Fa13 Fa10]. destruct F3n as [F3nx F3f].
  destruct HTwf as (V1 & V2 & V3). destruct HUwf as (Y1 & Y2 & Y3).

  eapply JT_run; [exact Hrun1 | exact W2 | exact W1 | exact W3 |].
  intros Lf rho1 [<-|[]] Hag1. cbn [la_state].
  apply triple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho1 sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF | exact HspfE]. }

  eapply (triple_conseq (P := SPA segs (JT kx ndE0) CfzE rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof (SPA_split segs (JT kx ndE0) rho1 Efz iw (SLit (- fz_frame)) S1 tp w F1 HS) as HS1.
    assert (HS2 : SPA segs (JT kx ndE0) (mkAX S2 (ax_X Efz) (ax_base Efz)) rho1 tp w).
    { rewrite <- F2e. change (mkAX (set_obj_at S1 iw O_WfzT) (ax_X Efz) (ax_base Efz)) with (ax_setS (mkAX S1 (ax_X Efz) (ax_base Efz)) (set_obj_at S1 iw O_WfzT)).
      apply (SPA_reslice segs (JT kx ndE0) rho1 (mkAX S1 (ax_X Efz) (ax_base Efz)) iw O_WloT O_WfzT tp w F2n); try reflexivity.
      - cbn [ax_S]. rewrite F2e. exact F2s.
      - unfold O_WloT, O_WfzT, spT. rewrite !obj_range_lits by (unfold WDP, DEEP, fz_frame; lia).
        rewrite !U_add_lit by (unfold fz_frame; try lia; rewrite U_add_lit by lia; lia). unfold WDP, DEEP, fz_frame. f_equal; lia.
      - unfold O_WfzT, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold WDP, DEEP, fz_frame; lia). unfold WDP, DEEP, fz_frame; lia.
      - exact HS1. }
    assert (HS3 : SPA segs (JT kx ndE0) (mkAX S3 (ax_X Efz) (ax_base Efz)) rho1 tp w).
    { rewrite <- F2a. change (mkAX (add_obj S2 O_payE) (ax_X Efz) (ax_base Efz)) with (ax_setS (mkAX S2 (ax_X Efz) (ax_base Efz)) (add_obj (ax_S (mkAX S2 (ax_X Efz) (ax_base Efz))) O_payE)).
      apply (SPA_add_empty segs (JT kx ndE0) rho1 (mkAX S2 (ax_X Efz) (ax_base Efz)) O_payE tp w); [cbn [ax_S]; rewrite F2a; exact F2w | reflexivity | reflexivity | cbn [ax_S]; exact F2o | | exact HS2].
      intros _. unfold O_payE, obj_hi_of, obj_lo_of. cbn [ob_hi ob_lo ob_base eval]. rewrite !soff_lit_small by lia. rewrite lit_unsigned. unfold EMPTY. cbn. lia. }
    pose proof (SPA_x_publish_empty segs (JT kx ndE0) rho1 (mkAX S3 (ax_X Efz) (ax_base Efz)) EMPTY tp w ltac:(unfold EMPTY; lia) eq_refl HS3) as HS4.
    unfold CfzE. change (mkAX S3 (ax_X Efz ++ [X_payE]) (ax_base Efz)) with (ax_setX (ax_setX (mkAX S3 (ax_X Efz) (ax_base Efz)) ((SLit EMPTY, SLit 0) :: ax_X (mkAX S3 (ax_X Efz) (ax_base Efz)))) (ax_X Efz ++ [X_payE])).
    apply SPA_x_sub; [| exact HS4]. cbn [ax_X ax_setX]. intros r Hr. apply in_app_or in Hr as [Hr|[<-|[]]]; [right; exact Hr | left; reflexivity]. }

  assert (HnxC : ss_next (ax_S CfzE) = ss_next (ax_S Efz)) by (unfold CfzE; cbn [ax_S]; exact F3nx).
  unfold ndE0, keptE.

  assert (Fnbc : bd_below (ss_next (ax_S Efz)) (bd_subst (s_fz CfzE) bd_fz) = true).
  { pose proof (proj1 (Pos.leb_le _ _) Fnx) as Hnf. unfold NF in Hnf. unfold bd_fz, bd_subst, bi_subst, lf_subst, bd_below, vLEN. cbn [map forallb bi_f fst snd atom_subst asv sv_subst].
    rewrite Fa13. unfold vPlen. cbn [sv_below]. try (assert (E : (44 <? ss_next (ax_S Efz))%positive = true) by (apply Pos.ltb_lt; lia); rewrite E). reflexivity. }
  apply (box_open_T segs AInv CST XGL ALA NF (KcT kx) rhoT P0T [] [] PTrue ok BX0 [(vB, vCap)] [] bd0 (bd_subst (s_fz CfzE) bd_fz) bd1 CfzE rho1 tp _ (BXnn_mk00 0) Fpay).
  { intros _. pose proof (Hcapbd rho1) as HC. assert (LMP : 0 <= LARGE_MIN) by (unfold LARGE_MIN; lia). cbn [length]. lia. }
  intros BXc HBXc Hback.
  rewrite <- (app_nil_r [(vB, vCap)]).
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJACP.client_callA_P segs AInv CST XGL ALA HCST HXGL DrvJ.segs_topA NF (KcT kx) rhoT P0T [] [] BXc PTrue (Kc_okT T0 MD HMDvm kx) HBXc
           (P0_fz CST) PTrue (fun _ H => H) (fun _ _ _ H => H) Pre_fz nd_fz0 PD_fz NF eq_refl eq_refl eq_refl
           (fun ok' FBc FFc BXc rho2 tp2 Hok HB => HFZ ok' Hok FBc FFc BXc rho2 tp2 HB) eq_refl
           ok CfzE (s_fz CfzE) Rfz (ax_X CfzE) rho1 tp [(vB, vCap)] [] [] (bd_subst (s_fz CfzE) bd_fz) [] ANone (fun _ => False)
           (okKT kx) Fxk Ffr Fcc Ftp Fdom).
  - rewrite HnxC. exact Fnx.
  - rewrite HnxC. pose proof (nd_below_split _ _ Fnb1) as (N1 & N2 & _ & N4). pose proof (nd_below_len _ _ Fnb1) as N5. cbn [nd_tv nd_fr nd_bd nd_am] in N1, N2, N4, N5. apply nd_below_intro; cbn [nd_tv nd_fr nd_bd nd_am]; [exact N1 | exact N2 | exact Fnbc | exact N4 | exact N5].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply payA_self. reflexivity.
  - rewrite HnxC. unfold CfzE in Fpd. cbn [ax_S] in Fpd. rewrite F3nx in Fpd. exact Fpd.
  -
    intros Ai ms HF' HP0 Hav HB HFF HN HD HZ HFR HM HTPA HTok HKz HMz. rewrite app_nil_r in HN, HD, HZ.
    split; [eapply robjs_okF_drv; [exact HF' | exact FspfC | exact (T0_of_site _ _ _ HTPA HTok) | exact Fknz | exact Fro]|].
    split; [eapply xrs_okF_drv; [exact HF' | exact FspfC | exact (T0_of_site _ _ _ HTPA HTok) | exact Fknz | exact Fxr]|].
    unfold P0_fz. split; [|split; [intros c; reflexivity | exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ot.DrvTPres.fz_site_PRES CST XGL rhoT rho1 Rfz ms _ _ (P0T_SH _ HP0) Hav HKz HMz HF' FspfC Fa10 Ftp)]].
    intros a Ha. exfalso. unfold uval, vDAT, vLEN in Ha. cbn [eval] in Ha. rewrite !rw_call' in Ha. rewrite Fa13 in Ha.
    cbn [eval] in Ha. rewrite lit_unsigned in Ha. change (0 mod 2 ^ 64) with 0 in Ha. lia.
  -
    intros d rho' tp' [<-|[]] Hag'. cbn [fst snd nd_tv nd_bd nd_am nd_fz1 import_tv bd_subst am_subst map app].
    unfold T_afterA3. rewrite import_postA3_full. fold (T_afterA Pre_fz CfzE (s_fz CfzE) Rfz P_fz). rewrite FTT.
    fold keptE. fold ndE1.

    eapply (triple_conseq (P := SPA segs (JT kx ndE1) TT rho' tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { exact (box_close segs AInv CST XGL NF (KcT kx) rhoT P0T [] [] PTrue BX0 BXc bd1 keptE [] [] ANone (ss_next (ax_S CfzE)) TT rho1 rho' tp' w (BXnn_mk00 0) Hback Hag' ltac:(rewrite HnxC; exact Fnb2) HS). }

    apply triple_factsA. intros HF2.
    assert (Hsp' : 0x7fff80000000 <= bv_unsigned (eval rho' sp0) <= 2 ^ 47 - 224).
    { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF2 | exact U1f]. }
    eapply (triple_conseq (P := SPA segs (JT kx ndE1) Tfz rho' tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { assert (HS1 : SPA segs (JT kx ndE1) (ax_setS TT U1) rho' tp' w).
      { rewrite <- U1e. apply (SPA_reslice segs (JT kx ndE1) rho' TT 1 _ O_WloT tp' w U1n); try reflexivity.
        - rewrite U1e. exact U1s.
        - unfold O_WloT, spT. rewrite !obj_range_lits by (unfold WDP, DEEP, fz_frame; lia).
          rewrite !U_add_lit by (unfold fz_frame; try lia; rewrite U_add_lit by lia; lia). unfold WDP, DEEP, fz_frame. f_equal; lia.
        - unfold O_WloT, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP, fz_frame; lia). unfold DEEP, fz_frame; lia.
        - exact HS. }
      pose proof (AxXform.SPA_select segs (JT kx ndE1) rho' (mkAX U1 (ax_X TT) (ax_base TT)) _ tp' w U2 HS1) as HS2.
      pose proof (SPA_merge segs (JT kx ndE1) rho' (mkAX (set_objs U1 (select (ss_objs U1) ([1; 0] ++ seq 2 (length (ss_objs U1) - 2))%nat)) (ax_X TT) (ax_base TT)) 0 U3 tp' w U3e HS2) as HS3.
      pose proof (SPA_drop_empty segs (JT kx ndE1) rho' (mkAX U3 (ax_X TT) (ax_base TT)) 1 _ tp' w U4n
                    ltac:(intros _; unfold obj_hi_of, obj_lo_of; cbn [ob_hi ob_lo]; apply Z.le_refl) HS3) as HS4.
      cbn [ax_S ax_setS ax_X ax_base] in HS4. rewrite U4e in HS4.
      rewrite <- UT. unfold dropX. apply SPA_x_sub; [cbn [ax_X]; apply In_dropX | exact HS4]. }

    eapply JT_run; [exact Hrun2 | exact V2 | exact V1 | exact V3 |].
    intros Lf rho2 [<-|[]] Hag2. cbn [la_state].
    apply triple_factsA. intros HF3.

    eapply (triple_conseq (P := SPA segs (JT kx ndE1) CpfE rho2 tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { pose proof (SPA_split segs (JT kx ndE1) rho2 Epf 0 (SLit (- PW)) P1 tp' w P1e HS) as HS1.
      assert (HS2 : SPA segs (JT kx ndE1) Cpf0E rho2 tp' w).
      { pose proof (carveT (KcT kx) ndE1 (mkAX P1 (ax_X Epf) (ax_base Epf)) rho2 tp' w N_pf (ss_next P1) HS1) as X.
        cbn zeta in X. cbn [ax_S ax_setS ax_X ax_base] in X. apply X; [exact P2w | apply Pos.leb_refl | exact HbE | exact P2c]. }
      unfold CpfE, ax_add_facts.
      change (ax_setS Cpf0E (add_facts (pf_hints Cpf0E k) (ax_S Cpf0E))) with (ax_with_facts Cpf0E (pf_hints Cpf0E k ++ ss_facts (ax_S Cpf0E))).
      apply (SPA_refacts_JA segs); [exact HS2 | exact P3b |].
      intros tr md HJ HFc. apply Forall_app. split; [|exact HFc]. apply Forall_forall. intros q Hq.
      destruct (P3h q Hq) as [x ->]. apply ms16_holds. }

    assert (HnxP : ss_next (ax_S CpfE) = ss_next (ax_S Epf)).
    { unfold CpfE, Cpf0E, ax_add_facts. cbn [ax_S ss_next add_facts P1cE]. exact P2n. }
    set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => JT kx ndE1 rho2 t tr md).
    assert (JpK : forall r t tr md, Jp r t tr md -> MD md /\ tr = T0 ++ EVk kx) by (intros r t tr md HJ; exact (JT_Kc _ _ _ _ _ _ HJ)).
    assert (HstJp : stableA segs NF Jp).
    { intros r r' t tr md md' Hag Hme HJ. unfold Jp in HJ |- *. destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF (KcT kx) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm kx) ALA (ss_next (ax_S CpfE)) ndE1 Ai kc rho2 rho2 t tr md md');
        [apply Pos.leb_le; exact Pnx | exact Pnb | apply agree_below_refl | exact Hme | exact HJi]. }
    assert (HokJp : ok_frameA segs ok Jp).
    { apply HOKJ. intros r t tr md HJ. destruct (JpK _ _ _ _ HJ) as [_ ->]. apply Htc. }
    assert (CONT : forall Lf rho3, In Lf (Posts_pf k) -> agree_below (ss_next (ax_S CpfE)) rho2 rho3 ->
              triple segs ok (SPA segs (JT kx' ndE1) (ax_add_facts (ss_facts (ax_S CpfE)) (import_postA (s_pf CpfE k) (PreP k) (la_state Lf) CpfE Rpf)) rho3 tp') (fun _ => False)).
    { intros Lf rho3 HinL Hag3. unfold Posts_pf in HinL. destruct HinL as [<-|[]]. cbn [la_state].
      fold (T_afterA (PreP k) CpfE (s_pf CpfE k) Rpf (P_pf k)). rewrite PTP.

      eapply (triple_conseq (P := fun w => exists rho4, SPA segs (JT kx' ndE1) Upf rho4 tp' w)); [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct w as [tr [ms md]].
        pose proof (AxXform.SPA_select segs (JT kx' ndE1) rho3 TP _ tp' _ Q1e HS) as HS1. rewrite Q1o, Q1d in HS1.
        pose proof (uncarveT (KcT kx') ndE1 (mkAX Q1 (ax_X TP) (ax_base TP)) rho3 tp' tr ms md _ N_pf (Kc_okT T0 MD HMDvm kx') Q1s Q2u eq_refl Q2n HS1) as HS2.
        cbn [ax_S ax_setS ax_X ax_base] in HS2. rewrite Q2e in HS2.
        set (rho4 := rho_absorb rho3 (map lc_obj N_pf) (vms md tp' ms)) in HS2. exists rho4.
        pose proof (AxXform.SPA_select segs (JT kx' ndE1) rho4 (mkAX Q2 (ax_X TP) (ax_base TP)) _ tp' _ Q3e HS2) as HS3.
        pose proof (SPA_merge segs (JT kx' ndE1) rho4 (mkAX (set_objs Q2 (select (ss_objs Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs Q2) - 9))%nat)) (ax_X TP) (ax_base TP)) 0 Q4 tp' _ Q4e HS3) as HS4.
        rewrite <- QU. exact HS4. }
      apply triple_ex. intros rho4.

      eapply JT_run; [exact Hrun3 | exact Y2 | exact Y1 | exact Y3 |].
      intros Lf rho5 HinLf Hag5.
      destruct (Hleaves Lf HinLf) as [(s5 & E1 & E2 & E3 & E4 & E5 & E6)|HX]; [|apply HX].
      eapply (triple_conseq (P := SPA segs (JT kx' ndE1) Lnext (rho_sub rho5 s5) tp')); [intros w HS | intros w' Hw'; exact Hw' | apply Hnext].
      apply (JT_entails kx' (la_state Lf) Lnext s5 ndE1 ndE1 rho5 tp' w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS). }
    destruct Pk as [(Ek & Ekx & Ekx')|(Hkok & Ekx & Ekx')].
    +
      subst kx kx'. unfold PreP in *. rewrite Ek in *. cbn [Z.eqb] in *.
      apply (pcallT (KcT 0) (KcT 1) CpfE Pre_pf0 (s_pf CpfE 0) Rpf (Posts_pf 0) rho2 tp' ndE1 Jp (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.Kw Jp 2) (fun _ => False) (Kc_okT T0 MD HMDvm 1)).
      * intros rho6 tp6. apply (printf0_sum ok Jp HstJp).
        -- intros r t tr md HJ. apply HMDfd1. exact (proj1 (JpK _ _ _ _ HJ)).
        -- intros n'. apply HOKJ. intros r t tr md (tr0 & HJ & ->). destruct (JpK _ _ _ _ HJ) as [_ ->].
           destruct (Htc 1%nat) as (tf & Htf & Hpre). exists tf. split; [exact Htf|]. eapply is_prefix_trans; [|exact Hpre].
           cbn [EVk]. rewrite app_nil_r. apply is_prefix_app_mono.
           unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.EVS. change (firstn 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.MSG0) with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.MSG0. clear. generalize OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.MSG0 as l. intros l.
           induction n' as [|n' IH] in l |- *; [apply is_prefix_nil|]. destruct l; cbn; [exact I|]. split; [reflexivity | apply IH].
        -- intros n'. apply HOKP. intros r t tr md (tr0 & HJ & ->). destruct (JpK _ _ _ _ HJ) as [_ ->].
           destruct (Htc 1%nat) as (tf & Htf & Hpre). exists tf. split; [exact Htf|]. eapply is_prefix_trans; [|exact Hpre].
           cbn [EVk]. rewrite app_nil_r. apply is_prefix_app_mono.
           unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.EVS. change (firstn 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.MSG0) with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.MSG0. clear. generalize OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0.MSG0 as l. intros l.
           induction n' as [|n' IH] in l |- *; [apply is_prefix_nil|]. destruct l; cbn; [exact I|]. split; [reflexivity | apply IH].
      * exact Pfr.
      * exact Pcc.
      * exact Pnx.
      * exact Pnb.
      * exact Pfb.
      * intros tr ms md Hsm HJ. exact HJ.
      * intros rhoL tr' md' (tr0 & HJ & ->). unfold Jp in HJ. destruct HJ as (Ai & kc & Hav & [Hmd Htr] & REST).
        exists Ai, kc. split; [exact Hav|]. split; [|exact REST]. split; [exact Hmd|]. rewrite Htr. cbn [EVk]. rewrite app_nil_r. reflexivity.
      * exact CONT.
    +
      subst kx kx'.
      assert (EP : PreP k = Pre_pf k).
      { unfold PreP. destruct Hkok as [->|[->| ->]]; reflexivity. }
      rewrite EP in *.
      apply (pcallT (KcT 1) (KcT 1) CpfE (Pre_pf k) (s_pf CpfE k) Rpf (Posts_pf k) rho2 tp' ndE1 Jp Jp (fun _ => False) (Kc_okT T0 MD HMDvm 1)).
      * intros rho6 tp6. apply (printf_sum ok Jp HokJp HstJp k rho6 tp6 Hkok).
      * exact Pfr.
      * exact Pcc.
      * exact Pnx.
      * exact Pnb.
      * exact Pfb.
      * intros tr ms md Hsm HJ. exact HJ.
      * intros rhoL tr' md' HJ. exact HJ.
      * exact CONT.
Qed.
End LoopE.

Section ExitFreeP.
Variable kx : nat.
Variable n : Z.
Variables bd1 bdJ : list bitem.
Definition keptX : list (sv * sv) := ltac2:(tb__ "0|1|
SdSbS1cS1cA2M0SfS1cS1cS2aS9fA1Sc2A4SdG0SfS1cS1cSc3Sc4A4ScG0A1A3A3").
Definition ndLX : ndesc := ltac2:(tb__ "0|0|
S63SdeScSbSbS1cS19A2S1cA2A1Vbd1;S62A4").
Definition ndJX : ndesc := ltac2:(tb__ "0|1|
S63SdSbS1cS1cA2M0SfS1cS1cSc3Sc4A4ScG0A1A3ScSbSbS1cS19A2S1cA2A1VbdJ;S62A4").
Variables (LX : axst) (R : list sobj) (T : axst) (leaves : list leafA).
Definition CP : axst := ltac2:(tb__ "0|0|
Sd1SfS1cS1cS2aS9fA1Sc2A4VLX;A2").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S137SddScbSa8SddA1A3S11G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S0S7S138SddScbSa8SddA1VR;SdS43ScfScS43A1A3A5S8A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S0S7S143S4dSa8SddA1A2S8A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41VLX;A1A1A2S8A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S1S0S7S61S1eS41VLX;A1A1M0Se0A2S8A3S0S7S107G0VbdJ;A2S8A3A2").
Hypothesis Hs12 : ltac2:(tb__ "0|1|
S1S0S1cS9bSa8SddA1M0PcA2S2aS9fA1A3S0S1cS9bG0PdA2Sc2A3A2").
Hypothesis Hpay : ltac2:(tb__ "0|0|
S0S7S108S20S41SddA1A1S23Z0A1S10aVbd1;VbdJ;A5S8A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S0S7SecS20S41SddA1A1A1S8A3").
Hypothesis Hro : ltac2:(tb__ "0|0|
S0S7SefS20S41SddA1A1SdeS11SaU0A2VR;A4S8A3").
Hypothesis Hxr : ltac2:(tb__ "0|1|
S0S7Sf0S20S41SddA1M0A1SdeS11SaU0A2S24G0A1SedS44SddA1A6S8A3").
Hypothesis HvP : ltac2:(tb__ "0|0|
S0S7SdbS1fS27S28S23Z1000A1S2aS9fA1A2A1S20S41SddA1A1A3S8A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S43S142ScbSddSa8SddA1VR;ScfA5VT;A3").
Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VT;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1SdfA2S8A3A2A2").
Hypothesis Hrun : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSceScdVT;S8A5S11G0Vleaves;A2A3").
Hypothesis Hleaves : ltac2:(tb__ "0|5|
S42SdaS42R1Vleaves;A3S3S99S99S1S0S7S49S46R3A1M0Sa2Vn;S23Z0A1A2R1A3S8A3S1S0S7S9aR1S4dA2S8A3S1S0S7S74S4dS1eS41G0A1M1A1M2A2S8A3S1S0S7S61G2SdfA2S8A3S1S0S7S116R1SdSbS1cS1cA2M3SfS1cS1cSc3Sc4A4ScG3A1A3M4G4A3S8A3S0S7S105S20G1A1S103R1VbdJ;A2VbdJ;A3S8A3A2A2A2A2A2Ls;A2F_;FLf;").

Variable CondJ : Prop.
Hypothesis Hcond : ltac2:(tb__ "0|0|
S21S87S1fS26R1A1S20S41VLX;A1A1A3VP0T;VrhoT;A1S13fS4dVrhoT;R3A3VCondJ;F_;F_;F_;Frho;").
Hypothesis HJ : ltac2:(tb__ "0|0|
VCondJ;S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx;SdfA2Sa2Vn;S23Z0A1A2R2R1A5S77S2L_;A4Ftp;Frho;F_;").

Lemma X_freeP : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx;Se0A2VLX;R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct Hnb as [Hnb1 Hnb2]. destruct Hs12 as [Hs12a Hs13]. destruct HTwf as (V1 & V2 & V3).
  apply triple_factsA. intros HF. apply triple_JT_pre. intros HP0' Hav'. pose proof (Hcond rho HF HP0' Hav') as HC.
  eapply (triple_conseq (P := SPA segs (JT kx ndLX) CP rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { unfold CP, dropX. apply SPA_x_sub; [|exact HS]. apply In_dropX. }
  assert (HnxC : ss_next (ax_S CP) = ss_next (ax_S LX)) by reflexivity.
  unfold ndLX, keptX.
  apply (free_callA segs AE_A AInv CST XGL ALA HCST HXGL NF (KcT kx) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm kx) ok [] UStopLe CP (s_fp CP) R rho tp
           (NDA [(SVar vP, vPlen); (vB, vCap)] [] bd1 ANone) 0%nat (SVar vP, vPlen) bdJ (fun _ => False) free_shape_nil (okKT kx) AC Hfr Hcc HcT).
  - rewrite HnxC. exact Hnx.
  - rewrite HnxC. exact Hnb1.
  - rewrite HnxC. exact Hnb2.
  - reflexivity.
  - apply payA_of_bud_pay. exact Hpay.
  - intros A A' _ _. exact I.
  - apply (site_ok_drv (NDA [(SVar vP, vPlen); (vB, vCap)] [] bd1 ANone) CP (s_fp CP) R rho (Some 0%nat) (Some (uval rho (wsub_get (s_fp CP) 12%positive)))); try assumption.
    + intros Ai HF' HN HZ. exists (SVar vP, vPlen). split; [reflexivity|]. rewrite Hs12a.
      assert (Hnz : tnz rho (SVar vP, vPlen)).
      { unfold tnz. cbn [fst]. pose proof (holds_mem _ _ _ HF' HvP) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X.
        rewrite Z.mod_small in X by lia. unfold uval in *. lia. }
      split; [exact Hnz | reflexivity].
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. split; [|split; [| exact I]].
      * unfold tnz. cbn [fst]. pose proof (holds_mem _ _ _ HF' HvP) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X.
        rewrite Z.mod_small in X by lia. lia.
      * rewrite Hs12a, Hs13. reflexivity.
  - intros rho' tp'. unfold PreF, PostF in HT. rewrite HT. cbn [nd_tv nd_fr nd_am remove_nth]. fold ndJX.
    eapply JT_run; [exact Hrun | exact V2 | exact V1 | exact V3 |].
    intros Lf rho2 HinLf Hag2. destruct (Hleaves Lf HinLf) as (s5 & E1 & E2 & E3 & E4 & E5 & E6).
    eapply (triple_conseq (P := SPA segs (JT kx ndJX) (J_E n (SLit 0)) (rho_sub rho2 s5) tp')); [intros w HS | intros w' Hw'; exact Hw' | apply (HJ HC)].
    apply (JT_entails kx (la_state Lf) (J_E n (SLit 0)) s5 ndJX ndJX rho2 tp' w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS).
Qed.
End ExitFreeP.

Section ExitFreeE.
Variable kx : nat.
Variable n : Z.
Variables bd1 bdJ : list bitem.
Definition ndEX : ndesc := ltac2:(tb__ "0|1|
S63SdSbS1cS1cA2M0SfS1cS1cSc3Sc4A4ScG0A1A3ScSbSbS1cS19A2S1cA2A1Vbd1;S62A4").
Definition ndJE : ndesc := ltac2:(tb__ "0|1|
S63SdSbS1cS1cA2M0SfS1cS1cSc3Sc4A4ScG0A1A3ScSbSbS1cS19A2S1cA2A1VbdJ;S62A4").
Variables (LX : axst) (R : list sobj) (T : axst) (leaves : list leafA).
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S137VLX;SaeSacVLX;A1A3S11G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S0S7S138VLX;SaeSacVLX;A1VR;SdS43Sb2ScS43A1A3A5S8A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S0S7S143S4dSacVLX;A1A2S8A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41VLX;A1A1A2S8A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S1S0S7S61S1eS41VLX;A1A1M0S16eA2S8A3S0S7S107G0VbdJ;A2S8A3A2").
Hypothesis Hpay : ltac2:(tb__ "0|1|
S0S7S108S20S41VLX;A1A1S23Z0M0A1G0Vbd1;VbdJ;A5S8A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S0S7SecS20S41VLX;A1A1A1S8A3").
Hypothesis Hro : ltac2:(tb__ "0|1|
S0S7SefS20S41VLX;A1A1SdSbS1cS1cA2M0SfS1cS1cSc3Sc4A4ScG0A1A3S15SaA1VR;A4S8A3").
Hypothesis Hxr : ltac2:(tb__ "0|2|
S0S7Sf0S20S41VLX;A1M0A1SdSbS1cS1cA2M1SfS1cS1cSc3Sc4A4ScG1A1A3S15SaA1S24G0A1SedS44VLX;A1A6S8A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S43S142SaeVLX;SacVLX;A1VR;Sb2A5VT;A3").
Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VT;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S16dA2S8A3A2A2").
Hypothesis Hrun : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSceScdVT;S8A5S11G0Vleaves;A2A3").
Hypothesis Hleaves : ltac2:(tb__ "0|5|
S42SdaS42R1Vleaves;A3S3S99S99S1S0S7S49S46R3A1M0Sa2Vn;S23Z0A1A2R1A3S8A3S1S0S7S9aR1S4dA2S8A3S1S0S7S74S4dS1eS41G0A1M1A1M2A2S8A3S1S0S7S61G2S16dA2S8A3S1S0S7S116R1SdSbS1cS1cA2M3SfS1cS1cSc3Sc4A4ScG3A1A3M4G4A3S8A3S0S7S105S20G1A1S103R1VbdJ;A2VbdJ;A3S8A3A2A2A2A2A2Ls;A2F_;FLf;").
Variable CondJ : Prop.
Hypothesis Hcond : ltac2:(tb__ "0|0|
S21S87S1fS26R1A1S20S41VLX;A1A1A3VP0T;VrhoT;A1S13fS4dVrhoT;R3A3VCondJ;F_;F_;F_;Frho;").
Hypothesis HJ : ltac2:(tb__ "0|0|
VCondJ;S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx;S16dA2Sa2Vn;S23Z0A1A2R2R1A5S77S2L_;A4Ftp;Frho;F_;").

Lemma X_freeE : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx;S16eA2VLX;R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct Hnb as [Hnb1 Hnb2]. destruct HTwf as (V1 & V2 & V3).
  apply triple_factsA. intros HF. apply triple_JT_pre. intros HP0' Hav'. pose proof (Hcond rho HF HP0' Hav') as HC.
  unfold ndEX.
  apply (free_null_callA segs AE_A AInv CST XGL ALA HCST HXGL NF (KcT kx) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm kx) ok [] UStopLe LX (s_fn LX) R rho tp
           (NDA [(vB, vCap)] [] bd1 ANone) bdJ (fun _ => False) eq_refl (okKT kx) AC Hfr Hcc HcT Hnx Hnb1 Hnb2).
  - apply payA_of_bud_pay. exact Hpay.
  - intros A A' _. exact I.
  - apply (site_ok_drv (NDA [(vB, vCap)] [] bd1 ANone) LX (s_fn LX) R rho None None); try assumption.
    + intros Ai HF' HN HZ. exact I.
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. exact I.
  - intros rho' tp'. unfold PreFN, PostFN in HT. rewrite HT. cbn [nd_tv nd_fr nd_am]. fold ndJE.
    eapply JT_run; [exact Hrun | exact V2 | exact V1 | exact V3 |].
    intros Lf rho2 HinLf Hag2. destruct (Hleaves Lf HinLf) as (s5 & E1 & E2 & E3 & E4 & E5 & E6).
    eapply (triple_conseq (P := SPA segs (JT kx ndJE) (J_E n (SLit 0)) (rho_sub rho2 s5) tp')); [intros w HS | intros w' Hw'; exact Hw' | apply (HJ HC)].
    apply (JT_entails kx (la_state Lf) (J_E n (SLit 0)) s5 ndJE ndJE rho2 tp' w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS).
Qed.
End ExitFreeE.

Definition N_mc : list lcarve := ltac2:(tb__ "0|d|
SdSbSbS19S19A2M0S9SbSbS19SaA2M1S19A2M2A1M3A2M4SfG0G3SfS19S19Zeed98M5Zeed9aA4SdG2SfG1S19SfS19SaG5U1M6A4Z1M7A4SdG2SfG1S19SfS19SaZeed99G6A4G7A4ScG2A1M8A3A3A4SdG4SfG0G3SfS19S19Zeeda0M9Zeedb8A4SdG2SfG1S19SfS19SaG9U8MaA4Z7fffffffffffA4SdG2SfG1S19SfS19SaZeeda8GaA4Z0MbA4SdG2SfG1S19SfS19SaZeedb0GaA4GbA4G8A3A3A3A4SdG4SfG0G3SfS19S19Ze6778McZe6780A4SdG2SfG1S19SfS19SaGcGaA4Zdac00A4G8A3A4ScG4A1A3A3A3").
Lemma N_mc_eq : ltac2:(tb__ "0|0|
S0S9S1dA1S86Se2S1dSe3S127A4SbdA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition mc_needb (facts : list sprop) : bool := ltac2:(tb__ "0|2|
Sd9S1fS1fSdbS1fS27R1A1Vfacts;A3Lf;SdS1fS28S14cS14cSc6Sc2A2S23Z6A1A2M0Sc7A2SdS1fS28Sc7G0A2SdS1fS28Sc6S23Z7fffA1A2SdS1fS28Sc2S23S7dZ2Z1aA2A1M1A2SdS1fS28Sc7Sc4A2SdS1fS28Sc4G1A2SdS1fS28Sc3S23Sd5A1A2ScS1fA1A3A3A3A3A3A3A3A3").
Definition O_srcM : sobj := ltac2:(tb__ "0|0|
S2eSc3S14cSc6S23Z6A1A2Sc7ScS2dA1S2fA5").

Lemma mc_src_range : ltac2:(tb__ "0|5|
S21S9S1fA1S87S1fS26R2A1R1A3S0S7S12cR2A1S8A3S1S0SbS19S19A2S3aR4Sa7A2S3aR4S128A2A3S1S1S7aZ0S39R4Sa7A2M0A2S7aG0S38R4Sa7A2M1A2A2S1S7eS7fG1G0A2S7dZ2Z3fA2M2A2S1S7aS39R4S128A2M3S38R4S128A2M4A2S7eS7fG4G3A2G2A2A2A2A2A2F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF Hn. unfold mc_needb in Hn. cbn [forallb] in Hn.
  repeat (apply andb_prop in Hn as [?X Hn]).
  repeat match goal with H : existsb (sprop_eqb _) facts = true |- _ => apply (holds_mem rho facts) in H; [|exact HF] end.
  unfold vB, vClen, vPlen, vLen, vCap in *. cbn [holds eval] in *. rewrite ?U_add, ?U_lit, <- ?M64v_eq in *.
  pose proof (urange (rw rho 40%positive)) as R30. pose proof (urange (rw rho 41%positive)) as R31. pose proof (urange (rw rho 42%positive)) as R32.
  pose proof (urange (rw rho 43%positive)) as R33. pose proof (urange (rw rho 44%positive)) as R34.
  unfold ACEIL, ATOPHI in *.
  rewrite ?(Z.mod_small 6), ?(Z.mod_small 32767), ?(Z.mod_small (2 ^ 26)), ?(Z.mod_small 140737479966720) in * by lia.
  repeat match goal with H : context [((?a + ?b) mod 2 ^ 64)] |- _ => rewrite (Z.mod_small (a + b) (2 ^ 64)) in H by lia end.
  unfold obj_range, obj_lo_of, obj_hi_of, O_srcT, O_srcM. cbn [ob_base ob_lo ob_hi].
  rewrite !soff_snorm. unfold U. unfold vB, vClen, vPlen, vLen. cbn [eval]. rewrite ?U_add, ?U_lit, <- ?M64v_eq. cbn [eval].
  cbn [eval] in *. rewrite ?lit_unsigned in *.
  change (32767 mod 2 ^ 64) with 32767 in *. change (2 ^ 26 mod 2 ^ 64) with (2 ^ 26) in *.
  change (140737479966720 mod 2 ^ 64) with 140737479966720 in *. change (6 mod 2 ^ 64) with 6 in *. change (0 mod 2 ^ 64) with 0 in *.
  rewrite (Z.mod_small (bv_unsigned (rw rho 43%positive) + bv_unsigned (rw rho 44%positive))) in * by lia.
  rewrite (Z.mod_small (bv_unsigned (rw rho 43%positive) + bv_unsigned (rw rho 44%positive) + 6)) in * by lia.
  rewrite (Z.mod_small (bv_unsigned (rw rho 43%positive) + 6)) in * by lia.
  rewrite (Z.mod_small (bv_unsigned (rw rho 40%positive) + (bv_unsigned (rw rho 43%positive) + 6))) in * by lia.
  rewrite !snorm_small by lia. split; [f_equal; lia|]. repeat split; lia.
Qed.

Section SegMC.
Variable bd0 : list bitem.
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S63S12aScSbSbS1cS19A2S1cA2A1Vbd0;S62A4").
Variables (TM Emc : axst) (W1 W2 B1 B2 B3 RS : sstate) (i0 i1 i2 : nat) (Rmc : list sobj) (TMC : axst).
Variables (V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 : sstate) (Umc Lp : axst) (sLP : wsub) (LP0 : axst)  .

Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VTM;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S112A2S8A3A2A2").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSb8SadVTM;S8A5S11G0SdS42S4aVEmc;SebA2ScS42A1A3A2A3").

Hypothesis M1 : ltac2:(tb__ "0|0|
S0S10S22A1S114S41VEmc;A1U0S23N870A1A3S11S22VW1;A2A3").
Hypothesis M2 : ltac2:(tb__ "0|0|
S0S10S22A1S114VW1;U0S23N8c0A1A3S11S22VW2;A2A3").
Hypothesis M3 : ltac2:(tb__ "0|0|
S0S10S22A1S114VW2;Vi0;S23Z6A1A3S11S22VB1;A2A3").
Hypothesis M4 : ltac2:(tb__ "0|0|
S0S10S22A1S114VB1;Vi1;S14cSc6S23Z6A1A2A3S11S22VB2;A2A3").
Hypothesis M5 : ltac2:(tb__ "0|0|
S0S10S22A1S114VB2;Vi2;Sc7A3S11S22VB3;A2A3").

Hypothesis M6b : ltac2:(tb__ "0|0|
S0S7Sd9S1fS2bS1eVB3;A1A1S12S1fSbcS20VB3;A1A3A3S8A3").
Hypothesis M6z : ltac2:(tb__ "0|0|
S0S7SeeS20VB3;A1S12aA2S8A3").
Definition B3h : sstate := add_facts mc_hints B3.
Definition B3c : sstate := ltac2:(tb__ "0|0|
S30S33S110A1S34S110A1S32S110A1S31S110A1S35S110A1S12S1dS24S110A1S86Se2S1dSe3S127A4A3S20S110A1S1eS110A1S25S110A1A9").
Hypothesis M6w : swf B3c = true.
Hypothesis M6c : ltac2:(tb__ "0|0|
S0S7Se5S20S110A1S24S110A1S44VEmc;A1Sf6Sf8S66S112A1S127A7S8A3").
Hypothesis M6x : ltac2:(tb__ "0|1|
S1S0S1aS1eVB3;A1S1eS41VEmc;A1M0A1A3S0S9S1fA1S20VB3;A1S20G0A1A3A2").
Hypothesis HbE : ltac2:(tb__ "0|0|
S0S1cS45VEmc;A1S23S169A1A3").
Hypothesis M7n : ltac2:(tb__ "0|0|
S0S10S1dA1SdcS1dS24S113A1Vi2;A3S11S1dS128A2A3").
Hypothesis M7e : ltac2:(tb__ "0|0|
S0S22S14eS113Vi2;Sa7A3VRS;A3").
Hypothesis M7s : ltac2:(tb__ "0|0|
S0S7S14dS113VRS;A2S8A3").
Hypothesis M7f : ltac2:(tb__ "0|1|
S1S0S7S12cS20S41VEmc;A1M0A1A1S8A3S0S1aS1eVRS;A1S1eG0A1A3A2").
Definition Cmc : axst := ltac2:(tb__ "0|0|
S48VRS;S44VEmc;A1S45VEmc;A1A3").

Hypothesis Cfr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S137S111S16fSafS111A1A3S11G0VRmc;A2A3").
Hypothesis Ccc : ltac2:(tb__ "0|0|
S0S7S139S111S16fSafS111A1VRmc;S86S42S43S46S171A4A5S8A3").
Hypothesis Cnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41S111A1A1A2S8A3").
Hypothesis Cnb : ltac2:(tb__ "0|0|
S0S7S61S1eS41S111A1A1S112A2S8A3").
Hypothesis Cfb : ltac2:(tb__ "0|1|
S0S7Sd9S1fS2bS1eS41S111A1M0A1A1S20G0A1A3S8A3").
Hypothesis ChB : ltac2:(tb__ "0|0|
S0S7SdbS1fS27S28S23Z1000A1Sc3A2A1S20S41S111A1A1A3S8A3").
Hypothesis CT : ltac2:(tb__ "0|0|
S0S43S142S16fS111SafS111A1VRmc;S170A5VTMC;A3").

Hypothesis V1e : ltac2:(tb__ "0|4|
S1S0S7S13cS13S1dS24S41VTMC;A1M0A1M1A2M2Sc0G2A1M3A2S8A3S0S22SeaG0S136G1G3A2A2VV1;A3A2").
Hypothesis V2e : ltac2:(tb__ "0|2|
S1S0S9S1dA1S24VV1;A1M0S12S1dS89S1dSe1S13S1dG0A2U3A2G0A3M1S86Se2S1dSe3S127A4A3A3S1S0S22SeaVV1;G1A2VV2;A3S1S0S7Se6Sf6S127A2S8A3S0S7S61S1eVV1;A1S112A2S8A3A2A2A2").
Hypothesis V3e : ltac2:(tb__ "0|1|
S1S0S10S1dA1SdcS1dS24VV2;A1U3M0A3S11S1dSa7A2A3S1S0S22S14eVV2;G0S128A3VV3;A3S1S0S7S14dVV2;VV3;A2S8A3S0S7S12cS20VV2;A1A1S8A3A2A2A2").
Hypothesis V4e : ltac2:(tb__ "0|1|
S1S0S10S1dA1SdcS1dS24VV3;A1U1M0A3S11S1dS2eS14cSccS23N940A1A2S23N50A1S23Z0A1ScS2dA1S2fA5A2A3S1S0S22S14eVV3;G0SbaA3VV4;A3S1S0S7S14dVV3;VV4;A2S8A3S0S7SecS20VV3;A1A1S8A3A2A2A2").
Hypothesis V5e : ltac2:(tb__ "0|3|
S1S0S7S13cS13S1dS24VV4;A1M0A2M1Sc1G1A1M2A2S8A3S0S22SeaVV4;S136G0G2A2A2VV5;A3A2").
Hypothesis V6e : ltac2:(tb__ "0|0|
S0S10S22A1S115VV5;U0A2S11S22VV6;A2A3").
Hypothesis V7e : ltac2:(tb__ "0|0|
S0S10S22A1S115VV6;U0A2S11S22VV7;A2A3").
Hypothesis V8e : ltac2:(tb__ "0|2|
S1S0S7S13cS13S1dS24VV7;A1M0A2SbfG0A1M1A2S8A3S0S22SeaVV7;S136G0G1A2A2VV8;A3A2").
Hypothesis V9e : ltac2:(tb__ "0|2|
S1S0S10S22A1M0S115VV8;U0M1A2S11S22VV9;A2A3S1S0G0S115VV9;G1A2S11S22VV10;A2A3S0G0S115VV10;G1A2S11S22VV11;A2A3A2A2").
Hypothesis VU : ltac2:(tb__ "0|0|
S0S43S48VV11;S44VTMC;A1S45VTMC;A1A3VUmc;A3").

Hypothesis HUwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VUmc;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S112A2S8A3A2A2").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSb9SadVUmc;S8A5S11G0SdS42S4aVLp;SebA2ScS42A1A3A2A3").
Hypothesis HLp : ltac2:(tb__ "0|2|
S1S0S7S49VLp;VLP0;VsLP;A3S8A3S1S0S7S9aVsLP;S4dA2S8A3S1S0S7S74S4dS1eS41VLp;A1M0A1M1A2S8A3S1S0S7S61G1S112A2S8A3S1S0S7S116VsLP;S12aS12aA3S8A3S0S7S105S20G0A1S103VsLP;Vbd0;A2Vbd0;A3S8A3A2A2A2A2A2").
Hypothesis Hnext : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0S112A2VLP0;R2R1A5S77S2L_;A4Ftp;Frho;").

Lemma X_mc : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0S112A2VTM;R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct HTwf as (W1' & W2' & W3'). destruct M6x as [M6nx M6fx]. destruct M7f as [M6f1 M7nx]. destruct HUwf as (Y1 & Y2 & Y3).
  destruct V1e as [V1a V1b]. destruct V2e as (V2a & V2b & V2c & V2d). destruct V3e as (V3a & V3b & V3c & V3d). destruct V4e as (V4a & V4b & V4c & V4d).
  destruct V5e as [V5a V5b]. destruct V8e as [V8a V8b]. destruct V9e as (V9a & V9b & V9c). destruct HLp as (E1 & E2 & E3 & E4 & E5 & E6).

  eapply JT_run; [exact Hrun1 | exact W2' | exact W1' | exact W3' |].
  intros Lf rho1 [<-|[]] Hag1. cbn [la_state].
  apply triple_factsA. intros HF.
  destruct (mc_src_range rho1 _ HF M6f1) as (RG & (L1 & L2) & L3 & L4 & L5).

  eapply (triple_conseq (P := SPA segs (JT 0 ndM) Cmc rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof (SPA_split segs (JT 0 ndM) rho1 Emc 0 (SLit (-2160)) W1 tp w M1 HS) as HS1.
    pose proof (SPA_split segs (JT 0 ndM) rho1 (mkAX W1 (ax_X Emc) (ax_base Emc)) 0 (SLit (-2240)) W2 tp w M2 HS1) as HS2.
    pose proof (SPA_split segs (JT 0 ndM) rho1 (mkAX W2 (ax_X Emc) (ax_base Emc)) i0 (SLit 6) B1 tp w M3 HS2) as HS3.
    pose proof (SPA_split segs (JT 0 ndM) rho1 (mkAX B1 (ax_X Emc) (ax_base Emc)) i1 (add vClen (SLit 6)) B2 tp w M4 HS3) as HS4.
    pose proof (SPA_split segs (JT 0 ndM) rho1 (mkAX B2 (ax_X Emc) (ax_base Emc)) i2 vLen B3 tp w M5 HS4) as HS5.
    assert (HS5h : SPA segs (JT 0 ndM) (mkAX B3h (ax_X Emc) (ax_base Emc)) rho1 tp w).
    { unfold B3h. change (mkAX (add_facts mc_hints B3) (ax_X Emc) (ax_base Emc)) with (ax_with_facts (mkAX B3 (ax_X Emc) (ax_base Emc)) (mc_hints ++ ss_facts B3)).
    apply (SPA_refacts_JA segs); [exact HS5 | exact M6b |].
    intros tr md HJ HFc. apply Forall_app. split; [|exact HFc].

    assert (Hnz : tnz rho1 (SVar vP, vPlen)).
    { unfold tnz. cbn [fst]. unfold kept_nzb in M6z. cbn [forallb fst] in M6z. apply andb_prop in M6z as [Z1 _].
      pose proof (holds_mem _ _ _ HFc Z1) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X. rewrite Z.mod_small in X by lia.
      unfold uval, vP in *. cbn [fst eval] in X |- *. lia. }
    pose proof (JA_tv_facts segs AInv CST XGL NF (KcT 0) rhoT P0T [] [] BX0 PTrue ALA ndM rho1 tp tr md (SVar vP, vPlen) eq_refl HJ ltac:(left; reflexivity) Hnz) as TF.
    unfold tv_factsA in TF. cbn [fst snd] in TF.
    inversion TF as [| ? ? T1 TF2]; subst. inversion TF2 as [| ? ? _ TF3]; subst. inversion TF3 as [| ? ? T3 TF4]; subst.
    inversion TF4 as [| ? ? _ TF5]; subst. inversion TF5 as [| ? ? _ TF6]; subst. inversion TF6 as [| ? ? T6 TF7]; subst.
    inversion TF7 as [| ? ? T7 TF8]; subst. inversion TF8 as [| ? ? T8 _]; subst.
    unfold mc_hints. constructor; [exact T1 | constructor; [exact T3 | constructor; [exact T6 | constructor; [exact T8 | constructor; [exact T7 | constructor]]]]]. }
    assert (HS6 : SPA segs (JT 0 ndM) (mkAX B3c (ax_X Emc) (ax_base Emc)) rho1 tp w).
    { pose proof (carveT (KcT 0) ndM (mkAX B3h (ax_X Emc) (ax_base Emc)) rho1 tp w N_mc (ss_next B3h) HS5h) as X.
      cbn zeta in X. cbn [ax_S ax_setS ax_X ax_base] in X. apply X; [exact M6w | apply Pos.leb_refl | exact HbE | exact M6c]. }
    unfold Cmc. rewrite <- M7e. change (mkAX (set_obj_at B3c i2 O_srcT) (ax_X Emc) (ax_base Emc)) with (ax_setS (mkAX B3c (ax_X Emc) (ax_base Emc)) (set_obj_at B3c i2 O_srcT)).
    apply (SPA_reslice segs (JT 0 ndM) rho1 (mkAX B3c (ax_X Emc) (ax_base Emc)) i2 O_srcM O_srcT tp w M7n); try reflexivity.
    - cbn [ax_S]. rewrite M7e. exact M7s.
    - exact RG.
    - exact L2.
    - exact L3.
    - exact HS6. }

  assert (HnxC : ss_next (ax_S Cmc) = ss_next (ax_S Emc)) by exact M7nx.
  apply triple_factsA. intros HFC.
  set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => JT 0 ndM rho1 t tr md /\ clsZ r 15 16 /\ clsZ r 19 52).
  assert (JpK : forall r t tr md, Jp r t tr md -> MD md /\ tr = T0 ++ EVk 0) by (intros r t tr md (HJ & _); exact (JT_Kc _ _ _ _ _ _ HJ)).
  assert (HstJp : stableA segs NF Jp).
  { intros r r' t tr md md' Hag Hme (HJ & C1 & C2). unfold Jp. split; [|split].
    - destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF (KcT 0) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm 0) ALA (ss_next (ax_S Cmc)) ndM Ai kc rho1 rho1 t tr md md');
        [apply Pos.leb_le; exact Cnx | exact Cnb | apply agree_below_refl | exact Hme | exact HJi].
    - unfold clsZ in C1 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact C1.
    - unfold clsZ in C2 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact C2. }
  assert (HokJp : ok_frameA segs ok Jp).
  { apply HOKJ. intros r t tr md HJ. destruct (JpK _ _ _ _ HJ) as [_ ->]. apply Htc. }
  apply (pcallT (KcT 0) (KcT 0) Cmc Pre_mc0 (s_mc Cmc) Rmc Posts_mc rho1 tp ndM Jp Jp (fun _ => False) (Kc_okT T0 MD HMDvm 0)).
  - intros rho6 tp6. apply (memcpy_icpt_sum ok Jp rho6 tp6 HokJp HstJp).
    + intros r t tr md (_ & C1 & _). exact C1.
    + intros r t tr md (_ & _ & C2). exact C2.
  - exact Cfr.
  - exact Ccc.
  - exact Cnx.
  - exact Cnb.
  - exact Cfb.
  -
    intros tr ms md Hsm HJ. unfold Jp. split; [exact HJ|].
    assert (Hnz : tnz rho1 (SVar vP, vPlen)).
    { unfold tnz. cbn [fst]. unfold kept_nzb in M6z. cbn [forallb fst] in M6z. apply andb_prop in M6z as [Z1 _]. rewrite M6fx in Z1.
      pose proof (holds_mem _ _ _ HF Z1) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X. rewrite Z.mod_small in X by lia.
      unfold uval, vP in X |- *. cbn [fst eval] in X |- *. lia. }
    assert (HnzB : tnz rho1 (vB, vCap)).
    { unfold tnz, vB. cbn [fst eval]. pose proof (holds_mem _ _ _ HFC ChB) as X. unfold vB in X. cbn [holds eval] in X.
      rewrite lit_unsigned, Z.mod_small in X by lia. lia. }
    split; apply band_free_clsZ; rewrite !rw_call'.
    + change (wsub_get (s_mc Cmc) 15%positive) with (SVar vP). change (wsub_get (s_mc Cmc) 16%positive) with vPlen.
      exact (JT_tv_band_free _ 0 ndM rho1 tp tr md (SVar vP, vPlen) HJ ltac:(left; reflexivity) Hnz).
    + change (wsub_get (s_mc Cmc) 19%positive) with vB. change (wsub_get (s_mc Cmc) 52%positive) with vCap.
      exact (JT_tv_band_free _ 0 ndM rho1 tp tr md (vB, vCap) HJ ltac:(right; left; reflexivity) HnzB).
  - intros rhoL tr' md' (HJ & _). exact HJ.
  -
    intros Lf rho3 HinL Hag3. unfold Posts_mc in HinL. destruct HinL as [<-|[]]. cbn [la_state].
    fold (T_afterA Pre_mc0 Cmc (s_mc Cmc) Rmc P_icpt). rewrite CT.
    eapply (triple_conseq (P := fun w => exists rho4, SPA segs (JT 0 ndM) Umc rho4 tp w)); [intros w HS | intros w' Hw'; exact Hw' |].
    { destruct w as [tr [ms md]].
      pose proof (AxXform.SPA_select segs (JT 0 ndM) rho3 TMC _ tp _ V1a HS) as HS1. rewrite V1b in HS1.
      pose proof (uncarveT (KcT 0) ndM (mkAX V1 (ax_X TMC) (ax_base TMC)) rho3 tp tr ms md _ N_mc (Kc_okT T0 MD HMDvm 0) V2a V2c eq_refl V2d HS1) as HS2.
      cbn [ax_S ax_setS ax_X ax_base] in HS2. rewrite V2b in HS2.
      set (rho4 := rho_absorb rho3 (map lc_obj N_mc) (vms md tp ms)) in HS2. exists rho4.
      destruct HS2 as [HS2a HS2b]. pose proof (conj HS2a HS2b : SPA segs (JT 0 ndM) (mkAX V2 (ax_X TMC) (ax_base TMC)) rho4 tp (tr, mkCfg ms md)) as HS2. clear HS2a HS2b.
      assert (HF4 : Forall (holds rho4) (ss_facts V2)) by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (proj1 HS2))))))))))))).
      destruct (mc_src_range rho4 _ HF4 V3d) as (RG' & _ & _ & L4' & L5').
      assert (HS3 : SPA segs (JT 0 ndM) (mkAX V3 (ax_X TMC) (ax_base TMC)) rho4 tp (tr, mkCfg ms md)).
      { rewrite <- V3b. change (mkAX (set_obj_at V2 3 O_srcM) (ax_X TMC) (ax_base TMC)) with (ax_setS (mkAX V2 (ax_X TMC) (ax_base TMC)) (set_obj_at V2 3 O_srcM)).
        apply (SPA_reslice segs (JT 0 ndM) rho4 (mkAX V2 (ax_X TMC) (ax_base TMC)) 3 O_srcT O_srcM tp _ V3a); try reflexivity.
        - cbn [ax_S]. rewrite V3b. exact V3c.
        - symmetry. exact RG'.
        - exact L4'.
        - exact L5'.
        - exact HS2. }
      assert (HF5 : Forall (holds rho4) (ss_facts V3)) by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (proj1 HS3))))))))))))).
      assert (Hsp4 : 0x7fff80000000 <= bv_unsigned (eval rho4 sp0) <= 2 ^ 47 - 224).
      { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF5 | exact V4d]. }
      assert (HS4 : SPA segs (JT 0 ndM) (mkAX V4 (ax_X TMC) (ax_base TMC)) rho4 tp (tr, mkCfg ms md)).
      { rewrite <- V4b. change (mkAX (set_obj_at V3 1 O_cstkB) (ax_X TMC) (ax_base TMC)) with (ax_setS (mkAX V3 (ax_X TMC) (ax_base TMC)) (set_obj_at V3 1 O_cstkB)).
        apply (SPA_reslice segs (JT 0 ndM) rho4 (mkAX V3 (ax_X TMC) (ax_base TMC)) 1 _ O_cstkB tp _ V4a); try reflexivity.
        - cbn [ax_S]. rewrite V4b. exact V4c.
        - unfold O_cstkB, spT. rewrite !obj_range_lits by lia. rewrite !U_add_lit by (try lia; rewrite U_add_lit by lia; lia). f_equal; lia.
        - unfold O_cstkB, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by lia. lia.
        - exact HS3. }
      pose proof (AxXform.SPA_select segs (JT 0 ndM) rho4 (mkAX V4 (ax_X TMC) (ax_base TMC)) _ tp _ V5a HS4) as HS5. cbn [ax_S ax_X ax_base] in HS5. rewrite V5b in HS5.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V5 (ax_X TMC) (ax_base TMC)) 0 V6 tp _ V6e HS5) as HS6.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V6 (ax_X TMC) (ax_base TMC)) 0 V7 tp _ V7e HS6) as HS7.
      pose proof (AxXform.SPA_select segs (JT 0 ndM) rho4 (mkAX V7 (ax_X TMC) (ax_base TMC)) _ tp _ V8a HS7) as HS8. cbn [ax_S ax_X ax_base] in HS8. rewrite V8b in HS8.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V8 (ax_X TMC) (ax_base TMC)) 0 V9 tp _ V9a HS8) as HS9.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V9 (ax_X TMC) (ax_base TMC)) 0 V10 tp _ V9b HS9) as HS10.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V10 (ax_X TMC) (ax_base TMC)) 0 V11 tp _ V9c HS10) as HS11.
      rewrite <- VU. exact HS11. }
    apply triple_ex. intros rho4.

    eapply JT_run; [exact Hrun2 | exact Y2 | exact Y1 | exact Y3 |].
    intros Lf rho5 [<-|[]] Hag5. cbn [la_state].
    eapply (triple_conseq (P := SPA segs (JT 0 ndM) LP0 (rho_sub rho5 sLP) tp)); [intros w HS | intros w' Hw'; exact Hw' | apply Hnext].
    apply (JT_entails 0%nat Lp LP0 sLP ndM ndM rho5 tp w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS).
Qed.
End SegMC.

Definition edge_okb (Lnext : axst) (tv : list (sv * sv)) (bdi bdj : list bitem) (Lf : axst) : bool := ltac2:(tb__ "0|2|
S179S4dS41VLf;A1M0S41VLnext;A1A3S99S14S14S14S14S14S49VLf;VLnext;R1A3S9aR1S4dA2A2S74S4dS1eG0A1M1A2A2S61G1S63Vtv;ScSbSbS1cS19A2S1cA2A1Vbdi;S62A4A2A2S116R1Vtv;Vtv;A3A2S105S20G0A1S103R1Vbdj;A2Vbdi;A3A2Ts;").
Lemma edge_okb_sound : ltac2:(tb__ "0|3|
S43S9SbS1cS1cA2A1S9S104A1M0G0S43S0S7S129R5R4R3R2R1A5S8A3S3S99S99S1S0S7S49R3R7R1A3S8A3S1S0S7S9aR1S4dA2S8A3S1S0S7S74S4dS1eS41R3A1M1A1M2A2S8A3S1S0S7S61G2S63R6ScSbSbS1cS19A2S1cA2A1R5S62A4A2S8A3S1S0S7S116R1R6R6A3S8A3S0S7S105S20G1A1S103R1R4A2R5A3S8A3A2A2A2A2A2Ls;A2F_;FLf;Fbdj;Fbdi;Ftv;FLnext;").
Proof.
  intros Lnext tv bdi bdj Lf H. unfold edge_okb in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  eexists. repeat split; eassumption.
Qed.
Lemma JT_edge : ltac2:(tb__ "0|4|
SaS43S9SbS1cS1cA2A1S9S104A1M0G0S43S21S9S4eQ40A1A1M1S0S7S129R7R6R5R4R3A5S8A3S21G1S76S4cVok;S5bS4cVJT;RbS63R9ScSbSbS1cS19A2S1cA2A1M2R7S62A4A2RaR2R1A5S77S2L_;M3A4Ftp';Frho';S76S4cVok;S5bS4cVJT;RaS63R8G2R7S62A4A2R5R4R3A5G3A4F_;F_;Ftp;Frho;FLf;Fbdj;Fbdi;Ftv;FLnext;Fk;").
Proof.
  intros k Lnext tv bdi bdj Lf rho tp H Hn. destruct (edge_okb_sound _ _ _ _ _ H) as (s5 & E1 & E2 & E3 & E4 & E5 & E6).
  eapply (triple_conseq (P := SPA segs (JT k (NDA tv [] bdj ANone)) Lnext (rho_sub rho s5) tp)); [intros w HS | intros w' Hw'; exact Hw' | apply Hn].
  apply (JT_entails k Lf Lnext s5 (NDA tv [] bdi ANone) (NDA tv [] bdj ANone) rho tp w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS).
Qed.

Definition plen_factsb (facts : list sprop) : bool := ltac2:(tb__ "0|1|
S14SdbS1fS27S28Sc2S23S7dZ2Z1aA2A1A2A1Vfacts;A3S16SdbS1fS27S29S122Sc2S23Z0A1M0A3A1Vfacts;A3SdbS1fS27S2cS29S11eSc2G0A3A1A1Vfacts;A3A2A2").
Lemma plen_facts_sound26 : ltac2:(tb__ "0|1|
S21S9S1fA1S87S1fS26R2A1R1A3S0S7S12dR2A1S8A3S1S7aZ1S10dR4Sc2A2M0A2S7aG0S7dZ2Z1aA2A2A2F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H. unfold plen_factsb in H. apply andb_prop in H as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as A1. cbn [holds] in A1. unfold vPlen in A1. cbn [eval] in A1. rewrite lit_unsigned in A1.
  change ((2 ^ 26) mod 2 ^ 64) with (2 ^ 26) in A1.
  assert (NZ : bv_unsigned (rw rho 44%positive) <> 0).
  { apply orb_prop in H2 as [H2|H2]; pose proof (holds_mem _ _ _ HF H2) as A2; cbn [holds] in A2; unfold vPlen in A2; cbn [eval] in A2;
      unfold branch_taken, bv_eqb in A2; rewrite lit_unsigned in A2; change (0 mod 2 ^ 64) with 0 in A2.
    - intros E. rewrite E in A2. cbn in A2. discriminate.
    - intros E. apply A2. rewrite E. reflexivity. }
  unfold uval, vPlen. cbn [eval]. pose proof (urange (rw rho 44%positive)). lia.
Qed.
Lemma plen_facts_sound : ltac2:(tb__ "0|1|
S21S9S1fA1S87S1fS26R2A1R1A3S0S7S12dR2A1S8A3S1S7aZ1S10dR4Sc2A2M0A2S7eG0S7dZ2Z27A2A2A2F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H. unfold plen_factsb in H. apply andb_prop in H as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as A1. cbn [holds] in A1. unfold vPlen in A1. cbn [eval] in A1. rewrite lit_unsigned in A1.
  change ((2 ^ 26) mod 2 ^ 64) with (2 ^ 26) in A1.
  assert (NZ : bv_unsigned (rw rho 44%positive) <> 0).
  { apply orb_prop in H2 as [H2|H2]; pose proof (holds_mem _ _ _ HF H2) as A2; cbn [holds] in A2; unfold vPlen in A2; cbn [eval] in A2;
      unfold branch_taken, bv_eqb in A2; rewrite lit_unsigned in A2; change (0 mod 2 ^ 64) with 0 in A2.
    - intros E. rewrite E in A2. cbn in A2. discriminate.
    - intros E. apply A2. rewrite E. reflexivity. }
  unfold uval, vPlen. cbn [eval]. pose proof (urange (rw rho 44%positive)). lia.
Qed.

Lemma room_T : ltac2:(tb__ "0|0|
S146S19S21S19S1S7aZ1R1A2S7aR1S7dZ2Z1aA2A2A2S10eSc9S72S10fSf7A1S71S62R3A2R4A3S149R5A1S148R5A1S147R5A1R3A6S188R6R3A2F_;F_;Fn;Frho;Fkc;FA;").
Proof.
  intros A kc rho n Hn HB. apply BUD_room in HB as (B0 & B1 & BV & BK). pose proof (apot_range ANone rho) as AR.
  unfold bxa, BX0 in B0, B1, BV, BK. cbn [fst snd bx2] in B0, B1, BV, BK.
  assert (EV : bsumV bd_T rho = V_T) by (unfold bd_T; cbn [bsumV]; unfold bival, BIc; cbn [lfval bi_f bi_c bi_v bi_k]; lia).
  assert (EK : bsumK bd_T rho = KU * K_T) by (unfold bd_T; cbn [bsumK]; unfold bival, BIc; cbn [lfval bi_f bi_c bi_v bi_k]; lia).
  rewrite EV in BV. rewrite EK in BK.
  unfold alloc_roomA. unfold V_T, K_T, VMAX, KMAX, V_DRV, K_DRV, NCALLS, CV, CV0, CK_DIV, CK0, MAX_INPUT, KU in BV, BK |- *. lia.
Qed.

Section MallocSite.

Variables (Em : axst) (R : list sobj) (Tk : axst).
Hypothesis Mfr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S137VEm;SaaSa5VEm;A1A3S11G0VR;A2A3").
Hypothesis Mcc : ltac2:(tb__ "0|0|
S0S7S138VEm;SaaSa5VEm;A1VR;SbbA5S8A3").
Hypothesis McT : ltac2:(tb__ "0|0|
S0S7S143S4dSa5VEm;A1A2S8A3").
Hypothesis Mnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41VEm;A1A1A2S8A3").
Hypothesis Mnb : ltac2:(tb__ "0|1|
S1S0S7S61S1eS41VEm;A1A1M0Sc5A2S8A3S0S7S107G0S15aA2S8A3A2").
Hypothesis Ms12 : ltac2:(tb__ "0|0|
S0S1cS9bSa5VEm;A1PcA2Sc2A3").
Hypothesis Msv : ltac2:(tb__ "0|0|
S0S7S3fS1eS41VEm;A1A1Sc2A2S8A3").
Hypothesis Mres : ltac2:(tb__ "0|1|
S1S0S1cS9bS13bSa5VEm;A1SaaS152S150ScS154A1S153A3VEm;A4S155A2S2aS141S1eS41VEm;A1A1UaA2M0A1A3S0S1aG0S9fA3A2").
Hypothesis Mpay : ltac2:(tb__ "0|0|
S0S7S108S20S41VEm;A1A1Sc2S10aSc9S15aA5S8A3").
Hypothesis Mspf : ltac2:(tb__ "0|0|
S0S7SecS20S41VEm;A1A1A1S8A3").
Hypothesis Mro : ltac2:(tb__ "0|0|
S0S7SefS20S41VEm;A1A1ScaS15SaA1VR;A4S8A3").
Hypothesis Mxr : ltac2:(tb__ "0|1|
S0S7Sf0S20S41VEm;A1M0A1ScaS15SaA1S24G0A1SedS44VEm;A1A6S8A3").
Hypothesis Msz : ltac2:(tb__ "0|0|
S0S7S12dS20S41VEm;A1A1A1S8A3").
Hypothesis MTk : ltac2:(tb__ "0|0|
S0S43S142SaaVEm;Sa5VEm;A1VR;S152S150ScS154A1S153A3A5VTk;A3").

Hypothesis HMC : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0S135S15aA1A2VTk;R2R1A5S77S2L_;A4Ftp;Frho;").

Lemma X_msite : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0Sc5A2VEm;R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct Mnb as [Mnb1 Mnb2]. destruct Mres as [Mres1 Mres2].
  apply triple_factsA. intros HF.
  pose proof (plen_facts_sound rho _ HF Msz) as HSZ. pose proof (plen_facts_sound26 rho _ HF Msz) as HSZ26.
  unfold nd_T. unfold PostsM in Mcc.
  apply (malloc_callA_S segs AE_A AInv CST XGL ALA HCST HXGL NF (KcT 0) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm 0) PTrue ok [] UStopLe Em (s_m Em) R rho tp
           (NDA tv_T [] bd_T ANone) bd_M (fun _ => False) malloc_shape_nil (okKT 0) MS Mfr (call_checkPA_drop1 _ _ _ _ _ _ Mcc) McT Mnx Mnb1 Mnb2).
  - rewrite Ms12. exact Msv.
  - exact Mres1.
  - rewrite Ms12. apply payA_of_bud_pay. exact Mpay.
  - intros A A' _ _. exact I.
  - intros A kc _ _ HB. rewrite Ms12. cbn [nd_bd nd_am] in HB. exact (room_T A kc rho _ HSZ26 HB).
  - reflexivity.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - apply (site_ok_drv (NDA tv_T [] bd_T ANone) Em (s_m Em) R rho None None); try assumption.
    + intros Ai HF' HN HZ. exact I.
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. rewrite Ms12. split; [exact HSZ | exact I].
  -
    intros rho' tp'. unfold PreM in MTk. rewrite MTk, Mres2, Ms12. cbn [nd_tv nd_fr nd_am]. fold kept. fold (ndM bd_M). apply HMC.
Qed.
End MallocSite.

Section SegT0.
Variables (S1 S2 : sstate) (EmA LeA LeB EmB : axst).
Hypothesis T1 : ltac2:(tb__ "0|0|
S0S10S22A1S114S41Sc8A1U0S23Nd0A1A3S11S22VS1;A2A3").

Hypothesis T2 : ltac2:(tb__ "0|4|
S1S0S7S186S4cVS1;Sd8S24VS1;A1S23Z0M0A1S23S173A1A3M1S7bS173Z4A2M2Z1M3G0A6S8A3S0S22S185VS1;G1G2G3G0A5VS2;A3A2").
Hypothesis T1w : ltac2:(tb__ "0|1|
S1S0S7S74S4dS1eVS2;A1M0A2S8A3S1S0S7S25VS2;A1SeA3S0S7S61G0Sc5A2S8A3A2A2").
Hypothesis Trun : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSb7SadS48VS2;S44Sc8A1S45Sc8A1A3S8A5S11G0SdS42S4aVEmA;SebA2SdS42S4aVLeA;SebA2SdS42S4aVLeB;SebA2SdS42S4aVEmB;SebA2ScS42A1A3A3A3A3A2A3").
Hypothesis HmA : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0Sc5A2VEmA;R2R1A5S77S2L_;A4Ftp;Frho;").
Hypothesis HmB : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0Sc5A2VEmB;R2R1A5S77S2L_;A4Ftp;Frho;").
Variables LEA LEB : axst.
Hypothesis HeA : ltac2:(tb__ "0|0|
S0S7S129VLEA;ScaSc9S159Z0A1VLeA;A5S8A3").
Hypothesis HeB : ltac2:(tb__ "0|0|
S0S7S129VLEB;ScaSc9S159Z0A1VLeB;A5S8A3").
Hypothesis HLEA : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0S12eS159Z0A1A1A2VLEA;R2R1A5S77S2L_;A4Ftp;Frho;").
Hypothesis HLEB : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0S12eS159Z0A1A1A2VLEB;R2R1A5S77S2L_;A4Ftp;Frho;").

Lemma X_T0 : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0Sc5A2Sc8R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct T1w as (W1' & W2' & W3').
  eapply (triple_conseq (P := SPA segs (JT 0 nd_T) (mkAX S1 (ax_X S_T) (ax_base S_T)) rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { exact (SPA_split segs (JT 0 nd_T) rho S_T 0 (SLit (-208)) S1 tp w T1 HS). }
  eapply (triple_conseq (P := SPA segs (JT 0 nd_T) (mkAX S2 (ax_X S_T) (ax_base S_T)) rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { destruct T2 as [T2a T2b]. rewrite <- T2b. exact (SPA_img_cell segs (JT 0 nd_T) rho (mkAX S1 (ax_X S_T) (ax_base S_T)) _ _ 1 0 tp w T2a HS). }
  eapply JT_run; [exact Trun | exact W2' | exact W1' | exact W3' |].
  intros Lf rho1 Hin Hag1. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [la_state].
  - apply HmA.
  - unfold nd_T. exact (JT_edge 0%nat LEA tv_T bd_T (bd_E 0) LeA rho1 tp HeA HLEA).
  - unfold nd_T. exact (JT_edge 0%nat LEB tv_T bd_T (bd_E 0) LeB rho1 tp HeB HLEB).
  - apply HmB.
Qed.
End SegT0.

Definition ms16_shapeb (q : sprop) : bool :=
  match q with
  | SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAlu ALU_OR (SLit 40) x) (SLit 15)) (SLit 0)) => true
  | _ => false
  end.
Lemma ms16_shapeb_sound : ltac2:(tb__ "0|0|
S1fS0S7S134R1A1S8A3S3S1cS1cS0S1fR3S12bR1A1A3Lx;A2F_;Fq;").
Proof.
  intros q H. unfold ms16_shapeb in H.
  repeat match type of H with
         | (match ?e with _ => _ end) = true => destruct e eqn:?; try discriminate
         end.
  subst. eexists. reflexivity.
Qed.

Definition backedge_okb (Lnext : axst) (tv : list (sv * sv)) (bd1 : list bitem) (Lf : axst) : bool := ltac2:(tb__ "0|2|
S179S4dS41VLf;A1M0S41VLnext;A1A3S99S14S14S14S14S14S49VLf;VLnext;R1A3S9aR1S4dA2A2S74S4dS1eG0A1M1A2A2S61G1S63Vtv;ScSbSbS1cS19A2S1cA2A1Vbd1;S62A4A2A2S116R1Vtv;Vtv;A3A2S105S20G0A1S103R1Vbd1;A2Vbd1;A3A2Ts;").
Lemma backedge_okb_sound : ltac2:(tb__ "0|2|
S43S9SbS1cS1cA2A1S9S104A1S43S0S7S12fR4R3R2R1A4S8A3S3S99S99S1S0S7S49R3R6R1A3S8A3S1S0S7S9aR1S4dA2S8A3S1S0S7S74S4dS1eS41R3A1M0A1M1A2S8A3S1S0S7S61G1S63R5ScSbSbS1cS19A2S1cA2A1R4S62A4A2S8A3S1S0S7S116R1R5R5A3S8A3S0S7S105S20G0A1S103R1R4A2R4A3S8A3A2A2A2A2A2Ls;A2F_;FLf;Fbd1;Ftv;FLnext;").
Proof.
  intros Lnext tv bd1 Lf H. unfold backedge_okb in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  eexists. repeat split; eassumption.
Qed.
End TLX.
End DrvTLX.

