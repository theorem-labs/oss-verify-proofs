(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "mul"; "pow"; "sub"; "div"; "eqb"; "ge"; "of_nat"; "opp"; "to_nat"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "rm"; "sprop"; "sv"; "holds"; "rl"; "ss_facts"; "SLit"; "eval"; "sprop_eqb"; "sobj"; "SVar"; "SAlu"; "SPUle"; "agree_below"; "ss_objs"; "SPAlign"; "SPEq"; "ext_low"; "mkSS"; "obj_range"; "ranges_disjoint"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "pair"; "cons"; "prod"; "true"; "nil"; "option"; "Some"; "app"; "false"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "vm_noaccess"; "vm_maps"; "m_vm_lazy"; "alloc_top"; "vm_reserved"; "event"; "maps_subtract"; "page_in_ranges"; "vm_limit"; "lazy_interior"; "vm_init_sp"; "page_size"; "map_remove"; "page_mem"; "vm_add_lazy"; "vm_forget_range"; "with_vmmaps"; "VmMaps"; "iv_subtract"; "region_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6.Seg6"; "mF"; "x1"; "vals"; "B16L"; "m16"; "b9lo"; "BF"; "n17"; "TP16"; "enspage"; "LOWPGw"; "TP17"; "B17"; "G17"; "Post16"; "Post17"; "Post6"; "XF16"; "m17"; "n16"; "RM16"; "RM6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "erase_mat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5"; "TP12"; "stackshadow_zero"; "m13"; "G14b"; "G13b"; "m12"; "m15"; "vals12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6"; "HPz"; "tcls"; "v80Z"; "q12x"; "LIMz"; "v79Z"; "PEz"; "topZ"; "e12x"; "shx"; "Ktr"; "PBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States"; "LOWPG"; "classes16"; "R16pre"; "R16c"; "LEN16"; "O_lowpg"; "PB"; "R16m"; "c1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "init_sp_ok"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "mkLeafA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4"; "Z11"; "m8"; "n9"; "pRI"; "priZ"; "sbZ"; "bandav"; "m10"; "m11"; "m9"; "n7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "SHADOW_RW_LO_END"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates"; "E_s17"; "M16_of"; "CF16"; "F17_of"; "IP16_of"; "IPr_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Start5bStates"; "S_s15ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "agree_vars"; "RMH"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg";
"segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates"; "E18"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "withX0"; "pages_rev"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "@LinuxProcessSemantics.Riscv.Prelude"; "bv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "shRI_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes"; "LB_of"; "eager_model"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartLib KxA Placement PlacementA Code SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.StartNodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Start5bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.Start6Run0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.Start6Run1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6Aux OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
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
S5cS9aS5S5S5S18S36S15Q40M0A1M1A1M2S36S4bA1M3Sc5S45S5aS35RaR9R5R4S38G3SbaR3SbbR2R1A2A4A6S18S18G2G2RfR4R2R8R6A4R10R4R2R9R7A4F_;Ft';Ft;Fr';Fr;S0S5SaRaZ1000M4A2Z0M5A3S7Z646000RbA2S7S8RcG4A2ScZ2Z40A2A2S7RdRcA2S7RcS8ReG4A2A2S0S37S4dS14G0RfA2S48R8A1A2S3bA3S5S1S7R11R1A2S9R1S8R11G4A2A2A2S0S37Sb3S46S44RbA1A1R2A2S40A3F_;Fz;S10Sc3RaRdA2S51A2S3S41G1S14G0R12A2ReA3A1S96S22S22S2dS2cR11R1A2S38S5S5R14S8R14G4A2A4A2Lo;S27S97R14A1A1A3F_;S41G1S14G0R13A2RfA3S5S1S7R14R1A2S9R1R13A2A2S0S3dS15Q8M6A1M7A1M8S19R13S14G0R2A2M9A2S3eG7S14G6G5A2A2MaA3F_;Fa;F_;S2S18S18S2G2G2S1S5aS35R18R17R2R1S38G3SbaR11SbbR10RfA2A4A6S1S6S0G1S17R3R1A2S17R14R1A2A3Fi;S1S6S0S36G7A1S1dR3R1A2S1dR14R1A2A3Fl;S1S5S1S7R16R1A2S9R1R15A2A2S0G8S19R4G9A2GaA3F_;Fa;S1G1S3S1S7R17S16G0R1A2MbA2S9GbS8R17G4A2A2A2A1S0G8S19R4R2A2S19R15R2A2A3F_;Fa;S1S3S41G1S14G0R16A2McR12A3MdA1S5S1S7R18R1A2S9R1S8R18G4A2A2A2S0G8S19R5G9A2GaA3F_;Fa;F_;S1GdG1S0G8S19R4R1A2S19R15R1A2A3Fa;F_;S0G2R1S37G2L_;S53GcR12A2R12S39G1GcR12A3X37x2A3A2A2A2A2A2A2A2Ltp';A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fzhi;Fzlo;Fp;FA;FJ;").
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
S1S7Z646000S16Q40Va1;A2M0A2S1S4S7S8G0Z10000A2M1SaaA2S7Sa9G0A2A2S7G1S49S44Vm;A1A1A2A2A2").
Hypothesis Ha2 : ltac2:(tb__ "0|2|
S1S7Z646000S16Q40Va2;A2M0A2S1S4S7S8G0Z38e000A2M1SaaA2S7Sa9G0A2A2S7G1S49S44Vm;A1A1A2A2A2").
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
Local Notation P_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.P_facts m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_range := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.RI_range m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.RI_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation SB_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.SB_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation b4_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b4_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4) (only parsing).
Local Notation b5_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b5_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5) (only parsing).
Local Notation b6_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b6_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5 b6 HPL6) (only parsing).
Local Notation b7_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.b7_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7) (only parsing).
Local Notation b8_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.b8_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7 b8 HPL8) (only parsing).
Local Notation b9_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.b9_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7 b8 HPL8 b9 HPL9) (only parsing).
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
S60Vrho;A1S5S3fS15Q40M0A1SbfS8S7fR1A1M1Z1000A2S72R1A1A2S68S14G0G1A2S77Vrho;A1A2A3Tx;").
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
  p mod 4096 = 0 -> 0x646000 <= p -> p + 4096 * Z.of_nat n <= 2 ^ 64 -> zhi <= p + 4096 * Z.of_nat n ->
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
S5S41S5R1S8cA3S1S0S37Sb8S7aS92R2A1M0A2S3bA3S0S37S34S2bS31G0A1S32G0A1S2fG0A1S2eG0A1S33G0A1S3fS22S27G0A1S39S22S90S3cS22A1A3A3S1eG0A1P51S30G0A1A9A1S3bA3A2F_;Ft;").
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
  forall q a, In q (TP12 rho) -> bv_unsigned q <= a < bv_unsigned q + 4096 -> LOWPG <= a < LOWPG + 0x4c00 ->
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
  destruct (ensure_pages J' (mkAX (R16m t) [] (SLit SHB)) 5 LOWPG (LOWPG + 0x4c00) rho4 (TP16 rho) [] ms md H4) as (rho5 & H5 & Hrw5 & Hrl5 & Hz5 & Ho5 & Hf5 & Hs5).
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
  pose proof (SPA_carve_zero segsA J' rho5 (mkAX (R16m t) [] (SLit SHB)) (TP17 rho) [] ms md (SLit LOWPG) 0 0x4c00 81%positive H5) as H6.
  cbn [ax_S ax_X ax_base] in H6. rewrite EbL in H6. fold O_lowpg in H6.
  specialize (H6 SWFl ltac:(rewrite NXm; apply Pos.le_refl) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold LOWPG; lia) ltac:(unfold LOWPG; lia)
                 (DISJL rho5 HF5 Elow5 (LOWPG + 0) (LOWPG + 0x4c00) ltac:(lia) ltac:(lia) ltac:(lia))
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
S5S18S36S15Q40A1A1S41S5R3S8cA3S9dS35Vok;S5aS35S75S5fS62A2M0SbeS8eR4A1A1R3R2A5S5bS35G0P51R3R2S39S98S99SaeR4A1Sb9A2S3cS98A1A3A6A4F_;Ftp;Frho;Ft;").
Proof using OKF.
  intros t rho tp Ht. destruct (cls16 t Ht) as (RUN & _). apply triple1_triple.
  apply (sym_run_soundA segsA _ _ _ _ ok _ rho tp RUN); [apply OKFx | reflexivity | apply stableA_KxA].
Qed.

Lemma call16 : ltac2:(tb__ "0|1|
S5S18S36S15Q40A1A1S41S5R3S8cA3S9dS35Vok;S5aS35S75S5fS62A2M0SaeR4A1R3R2A5S9bS2S18S18S1S26P51R5R1A3S5aS35G0Sb1R6A1R1R4R2A6A2Lrho';A2Lw;A4F_;Ftp;Frho;Ft;").
Proof using OKF.
  intros t rho tp Ht. destruct (cls16 t Ht) as (_ & FR & CC & IPE & NX & _).
  apply (call_pureA segsA ok (M16_of t) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ.Pre_mszA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ.Posts_mszA (s16_of t) (R16_of t) mF B16L tp rho _ OKF FR CC).
  - intros J rho1 tp1 HokJ HstJ. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ.memsetZ_sumA ok J HokJ HstJ rho1 tp1).
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
S5S18S36S15Q40A1A1S41S5R3S8cA3S9dS35Vok;S5aS35S75S5fS62A2M0Sb2R4A1R3R2A5S5bS35G0P79R3R2S39S98S99Sb0R4A1Sb9A2S3cS98A1A3A6A4F_;Ftp;Frho;Ft;").
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
Definition G17 : list (sv * Z) := G13b ++ [(SLit LOWPG, 0x4c00)].

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
S0S37Sb8S6cS97SadA1A2S3bA3").
Proof. clear. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Post17 (rho : valuation) (x : Z) (tp : list word) : assn := ltac2:(tb__ "0|3|
S9bS2S15Q40M0A1M1G1S2S18S18S1S94S14G0Z0A2S63Vx;A1S14G0S66A2R2A4S1Sb6P53M2Vrho;R1A3S1S0G1S17R1G2A2R2A3S1G1S0S3dS15Q8A1A1S19R2R1A2S19Vrho;R1A2A3Fa;S5aS35S75S71Vx;R2A2S6bA2SbdR1Vtp;R3A6A2A2A2A2Lrho';A2Lb10;A2Lw;").

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
S9bS60Vrho;A1S5S2S15Q40M0A1M1G1S2S18S18S1S94S14G0Z0A2S63R3A1S14G0S66A2R2A4S1Sb6P4fM2Vrho;R1A3S1S0G1S17R1G2A2S14G0S84R3A1A2A3S1S0G1S17R1P50A2S14G0S81R3A1A2A3S1S0G1S17R1P51A2S14G0S86R3A1A2A3S1S0G1S17R1P53A2R2A3S1S74Vrho;R1A2S1Sb7Vrho;R1A2S1S70Vrho;A1S5aS35S75S71R3R2A2S6bA2SbdR1S6aVrho;A1R4A6A2A2A2A2A2A2A2A2A2Lrho';A2Lb10;A2Tx;Lw;").

Theorem start6_sum_A : ltac2:(tb__ "0|1|
S18S61R1A1S0S15Q40A1M0S17R2P24A2Vb7;A3S0G0S17R3P4dA2Vb8;A3S0G0S17R4P4eA2Vb9;A3S78R5A1S9eR6A1Sb7R7R7A2S9dS35Vok;S5aS35S75S5fS65A2Sb5R8S77R8A1A5S6fR8A1A4F_;F_;F_;F_;F_;F_;F_;Frho;").
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
S5S18S36S15Q40A1A1S41S5R3S8cA3S9cS35S5aS35S75S5fS62A2M0SbeS8eR4A1A1R3R2A5S5bS35G0P51R3R2S39S98S99SaeR4A1Sb9A2S3cS98A1A3A6A3F_;Ftp;Frho;Ft;").
Proof.
  intros t rho tp Ht. destruct (cls16 t Ht) as (RUN & _). eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact RUN].
Qed.

Lemma ecall16 : ltac2:(tb__ "0|1|
S5S18S36S15Q40A1A1S41S5R3S8cA3S9cS35S5aS35S75S5fS62A2M0SaeR4A1R3R2A5S9bS2S18S18S1S26P51R5R1A3S5aS35G0Sb1R6A1R1R4R2A6A2Lrho';A2Lw;A3F_;Ftp;Frho;Ft;").
Proof.
  intros t rho tp Ht. destruct (cls16 t Ht) as (_ & FR & CC & IPE & NX & _).
  apply (ecall_pureA segsA (M16_of t) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ.Pre_mszA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ.Posts_mszA (s16_of t) (R16_of t) mF B16L tp rho _ FR CC).
  - intros J rho1 tp1 HstJ. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ.memsetZ_sumA_ex J HstJ rho1 tp1).
  - intros L rho' [<-|[]] Hag. cbn [la_state]. rewrite NX in Hag. rewrite IPE.
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply etriple_refl].
    exists rho'. split; [exact Hag | exact Hw].
Qed.

Lemma erun17x : ltac2:(tb__ "0|1|
S5S18S36S15Q40A1A1S41S5R3S8cA3S9cS35S5aS35S75S5fS62A2M0Sb2R4A1R3R2A5S5bS35G0P79R3R2S39S98S99Sb0R4A1Sb9A2S3cS98A1A3A6A3F_;Ftp;Frho;Ft;").
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
S18S61R1A1S0S15Q40A1M0S17R2P24A2Vb7;A3S0G0S17R3P4dA2Vb8;A3S0G0S17R4P4eA2Vb9;A3S78R5A1S9eR6A1Sb7R7R7A2S9cS35S5aS35S75S5fS65A2Sb5R8S77R8A1A5S6fR8A1A3F_;F_;F_;F_;F_;F_;F_;Frho;").
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
