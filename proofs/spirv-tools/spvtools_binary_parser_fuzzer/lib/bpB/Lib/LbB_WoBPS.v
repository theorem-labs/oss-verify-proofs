From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HCommon.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Call LbB_Conv LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwStm.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_WoBPR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition bp_x0_pre (R : bvmap 5 word) (m : mem) (sf : Z) : Prop :=
  getr R 19 = wz sf
  /\ wr_at asegs m sf 476
  /\ 0 <= sf
  /\ sf + 512 <= 2 ^ 47.

Definition bp_x0 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (sf : Z),
    bp_x0_pre R m sf ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 3260)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 3384)) fc None M' (seg_rom asegs))
      /\ munch [((sf + 344), (sf + 374))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sf + 373) 1 18446744073709551608
      /\ fldA M' (sf + 372) 1 18446744073709551608
      /\ fldA M' (sf + 371) 1 18446744073709551608
      /\ fldA M' (sf + 370) 1 18446744073709551608
      /\ fldA M' (sf + 369) 1 18446744073709551608
      /\ fldA M' (sf + 368) 1 18446744073709551608
      /\ fldA M' (sf + 363) 1 18446744073709551608
      /\ fldA M' (sf + 362) 1 18446744073709551608
      /\ fldA M' (sf + 361) 1 18446744073709551608
      /\ fldA M' (sf + 360) 1 18446744073709551608
      /\ fldA M' (sf + 367) 1 18446744073709551608
      /\ fldA M' (sf + 366) 1 18446744073709551608
      /\ fldA M' (sf + 365) 1 18446744073709551608
      /\ fldA M' (sf + 364) 1 18446744073709551608
      /\ fldA M' (sf + 355) 1 18446744073709551608
      /\ fldA M' (sf + 354) 1 18446744073709551608
      /\ fldA M' (sf + 353) 1 18446744073709551608
      /\ fldA M' (sf + 352) 1 18446744073709551608
      /\ fldA M' (sf + 359) 1 18446744073709551608
      /\ fldA M' (sf + 358) 1 18446744073709551608
      /\ fldA M' (sf + 357) 1 18446744073709551608
      /\ fldA M' (sf + 356) 1 18446744073709551608
      /\ fldA M' (sf + 347) 1 18446744073709551608
      /\ fldA M' (sf + 346) 1 18446744073709551608
      /\ fldA M' (sf + 345) 1 18446744073709551608
      /\ fldA M' (sf + 344) 1 18446744073709551608
      /\ fldA M' (sf + 351) 1 18446744073709551608
      /\ fldA M' (sf + 350) 1 18446744073709551608
      /\ fldA M' (sf + 349) 1 18446744073709551608
      /\ fldA M' (sf + 348) 1 18446744073709551608
      /\ getr R' 10 = wz 18446744073709551608
      /\ getr R' 19 = wz sf
      /\ (forall r, In r [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bp_x0_bp : bp_x0 (0xea7c4).
Proof.
  intros R F fc m sf P.
  destruct P as (P0 & P1 & P2 & P3). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WoBPR.bx0_E R sf) LbB_WoBPR.bx0_sr R) by (unfold LbB_WoBPR.bx0_E, LbB_WoBPR.bx0_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WoBPR.bx0_E R sf) m LbB_WoBPR.bx0_A_knF) by (unfold LbB_WoBPR.bx0_E; knowB).
  destruct (LbB_WoBPR.bx0_A_run fx R m (seg_rom asegs) sf ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WoBPR.bx0_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WoBPR.bx0_E R sf) in *. unfold LbB_WoBPR.bx0_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fld_postB_at 3%nat|].
  split; [fld_postB_at 4%nat|].
  split; [fld_postB_at 5%nat|].
  split; [fld_postB_at 6%nat|].
  split; [fld_postB_at 7%nat|].
  split; [fld_postB_at 8%nat|].
  split; [fld_postB_at 9%nat|].
  split; [fld_postB_at 10%nat|].
  split; [fld_postB_at 11%nat|].
  split; [fld_postB_at 12%nat|].
  split; [fld_postB_at 13%nat|].
  split; [fld_postB_at 14%nat|].
  split; [fld_postB_at 15%nat|].
  split; [fld_postB_at 16%nat|].
  split; [fld_postB_at 17%nat|].
  split; [fld_postB_at 18%nat|].
  split; [fld_postB_at 19%nat|].
  split; [fld_postB_at 20%nat|].
  split; [fld_postB_at 21%nat|].
  split; [fld_postB_at 22%nat|].
  split; [fld_postB_at 23%nat|].
  split; [fld_postB_at 24%nat|].
  split; [fld_postB_at 25%nat|].
  split; [fld_postB_at 26%nat|].
  split; [fld_postB_at 27%nat|].
  split; [fld_postB_at 28%nat|].
  split; [fld_postB_at 29%nat|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  keptB HR HR' ([1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bp_x1_pre (R : bvmap 5 word) (m : mem) (sf : Z) : Prop :=
  getr R 19 = wz sf
  /\ wr_at asegs m sf 476
  /\ 0 <= sf
  /\ sf + 512 <= 2 ^ 47.

Definition bp_x1 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (sf : Z),
    bp_x1_pre R m sf ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 6428)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 6448)) fc None M' (seg_rom asegs))
      /\ munch [((sf + 278), (sf + 282))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sf + 281) 1 18446744073709551608
      /\ fldA M' (sf + 280) 1 18446744073709551608
      /\ fldA M' (sf + 279) 1 18446744073709551608
      /\ fldA M' (sf + 278) 1 18446744073709551608
      /\ getr R' 10 = wz 18446744073709551608
      /\ getr R' 19 = wz sf
      /\ (forall r, In r [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bp_x1_bp : bp_x1 (0xea7c4).
Proof.
  intros R F fc m sf P.
  destruct P as (P0 & P1 & P2 & P3). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WoBPR.bx1_E R sf) LbB_WoBPR.bx1_sr R) by (unfold LbB_WoBPR.bx1_E, LbB_WoBPR.bx1_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WoBPR.bx1_E R sf) m LbB_WoBPR.bx1_A_knF) by (unfold LbB_WoBPR.bx1_E; knowB).
  destruct (LbB_WoBPR.bx1_A_run fx R m (seg_rom asegs) sf ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WoBPR.bx1_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WoBPR.bx1_E R sf) in *. unfold LbB_WoBPR.bx1_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fld_postB_at 3%nat|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  keptB HR HR' ([1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bp_x2_pre (R : bvmap 5 word) (m : mem) (sf : Z) : Prop :=
  getr R 19 = wz sf
  /\ wr_at asegs m sf 476
  /\ 0 <= sf
  /\ sf + 512 <= 2 ^ 47.

Definition bp_x2 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (sf : Z),
    bp_x2_pre R m sf ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 6448)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 6460)) fc None M' (seg_rom asegs))
      /\ munch [((sf + 216), (sf + 218))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sf + 217) 1 18446744073709551608
      /\ fldA M' (sf + 216) 1 18446744073709551608
      /\ getr R' 10 = wz 18446744073709551608
      /\ getr R' 19 = wz sf
      /\ (forall r, In r [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bp_x2_bp : bp_x2 (0xea7c4).
Proof.
  intros R F fc m sf P.
  destruct P as (P0 & P1 & P2 & P3). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WoBPR.bx2_E R sf) LbB_WoBPR.bx2_sr R) by (unfold LbB_WoBPR.bx2_E, LbB_WoBPR.bx2_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WoBPR.bx2_E R sf) m LbB_WoBPR.bx2_A_knF) by (unfold LbB_WoBPR.bx2_E; knowB).
  destruct (LbB_WoBPR.bx2_A_run fx R m (seg_rom asegs) sf ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WoBPR.bx2_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WoBPR.bx2_E R sf) in *. unfold LbB_WoBPR.bx2_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  keptB HR HR' ([1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.
