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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmBMR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition bmR_x_pre (R : bvmap 5 word) (m : mem) (q sp words n x : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 10 = wz words
  /\ getr R 11 = wz n
  /\ getr R 18 = wz ((32 * q) + 3456)
  /\ getr R 19 = wz ((4 * q) + ASHADOW_BASE)
  /\ getr R 20 = wz (32 * q)
  /\ getr R 25 = wz ((32 * q) + 1728)
  /\ ACONST m
  /\ fldA m words 4 x
  /\ wr_at asegs m (32 * q + 1728) 16
  /\ fldA m (4 * q + 2147451096) 1 0
  /\ fldA m (4 * q + 2147451097) 1 0
  /\ wr_at asegs m (sp - 16) 16
  /\ 227200 <= q <= 2 ^ 42
  /\ 2 ^ 45 + 16 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ 16 <= words <= 2 ^ 47
  /\ words mod 16 = 0
  /\ 5 <= n <= 2 ^ 24
  /\ 0 <= x <= 2 ^ 32 - 1
  /\ (words + 4 <= (32 * q + 1728) \/ (32 * q + 1728) + 16 <= words)
  /\ (words + 4 <= (sp - 16) \/ (sp - 16) + 16 <= words)
  /\ ((32 * q + 1728) + 16 <= (sp - 16) \/ (sp - 16) + 16 <= (32 * q + 1728))
  /\ ((sp - 16) + 16 <= (32 * q) \/ (32 * q) + 4096 <= (sp - 16))
  /\ (words + 4 <= (32 * q) \/ (32 * q) + 4096 <= words)
  /\ sh0 m words
  /\ 2 ^ 45 + 16 <= sp
  /\ sp <= 2 ^ 47
  /\ 0x6e6000 + 0x9000 <= 32 * q
  /\ 32 * q + 4096 <= 2 ^ 47
  /\ (32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)
  /\ 0 <= x < 2 ^ 32.

Definition bmR_x00 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp words n x : Z),
    bmR_x_pre R m q sp words n x -> (x mod 256 <> 3) -> (x mod 256 <> 7) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 4784)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 4812)) fc None M' (seg_rom asegs))
      /\ munch [((sp - 8), sp); ((32 * q + 1728), (32 * q + 1744))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sp - 8) 8 (E + 4808)
      /\ fldA M' (32 * q + 1736) 8 n
      /\ fldA M' (32 * q + 1728) 8 words
      /\ getr R' 1 = wz (E + 4808)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz 18446744073709551612
      /\ getr R' 11 = wz ((32 * q) + 3544)
      /\ getr R' 14 = wz ASHADOW_BASE
      /\ getr R' 17 = wz 3
      /\ getr R' 18 = wz ((32 * q) + 3456)
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ getr R' 24 = wz ((32 * q) + 3544)
      /\ getr R' 25 = wz ((32 * q) + 1728)
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_x00_bp : bmR_x00 (0xea7c4).
Proof.
  intros R F fc m q sp words n x P Q0 Q1.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.bm_E R q sp words n x) LbB_PmBMR.bm_sr R) by (unfold LbB_PmBMR.bm_E, LbB_PmBMR.bm_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.bm_E R q sp words n x) m LbB_PmBMR.bm_00_knF) by (unfold LbB_PmBMR.bm_E; knowB).
  destruct (LbB_PmBMR.bm_00_run fx R m (seg_rom asegs) q sp words n x ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.bm_00_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.bm_E R q sp words n x) in *. unfold LbB_PmBMR.bm_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 1; 1]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (17%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_x01 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp words n x : Z),
    bmR_x_pre R m q sp words n x -> (x mod 256 = 7) -> ((x / 256) mod 256 <> 35) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 4784)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 4812)) fc None M' (seg_rom asegs))
      /\ munch [((sp - 8), sp); ((32 * q + 1728), (32 * q + 1744))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sp - 8) 8 (E + 4808)
      /\ fldA M' (32 * q + 1736) 8 n
      /\ fldA M' (32 * q + 1728) 8 words
      /\ getr R' 1 = wz (E + 4808)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz 18446744073709551612
      /\ getr R' 11 = wz ((32 * q) + 3544)
      /\ getr R' 14 = wz ASHADOW_BASE
      /\ getr R' 16 = wz 35
      /\ getr R' 17 = wz 7
      /\ getr R' 18 = wz ((32 * q) + 3456)
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ getr R' 24 = wz ((32 * q) + 3544)
      /\ getr R' 25 = wz ((32 * q) + 1728)
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_x01_bp : bmR_x01 (0xea7c4).
Proof.
  intros R F fc m q sp words n x P Q0 Q1.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.bm_E R q sp words n x) LbB_PmBMR.bm_sr R) by (unfold LbB_PmBMR.bm_E, LbB_PmBMR.bm_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.bm_E R q sp words n x) m LbB_PmBMR.bm_01_knF) by (unfold LbB_PmBMR.bm_E; knowB).
  destruct (LbB_PmBMR.bm_01_run fx R m (seg_rom asegs) q sp words n x ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.bm_01_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.bm_E R q sp words n x) in *. unfold LbB_PmBMR.bm_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 1; 1]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (17%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_x02 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp words n x : Z),
    bmR_x_pre R m q sp words n x -> (x mod 256 = 7) -> ((x / 256) mod 256 = 35) -> ((x / 65536) mod 256 <> 2) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 4784)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 4812)) fc None M' (seg_rom asegs))
      /\ munch [((sp - 8), sp); ((32 * q + 1728), (32 * q + 1744))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sp - 8) 8 (E + 4808)
      /\ fldA M' (32 * q + 1736) 8 n
      /\ fldA M' (32 * q + 1728) 8 words
      /\ getr R' 1 = wz (E + 4808)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz 18446744073709551612
      /\ getr R' 11 = wz ((32 * q) + 3544)
      /\ getr R' 14 = wz ASHADOW_BASE
      /\ getr R' 15 = wz 2
      /\ getr R' 16 = wz 35
      /\ getr R' 17 = wz 7
      /\ getr R' 18 = wz ((32 * q) + 3456)
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ getr R' 24 = wz ((32 * q) + 3544)
      /\ getr R' 25 = wz ((32 * q) + 1728)
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_x02_bp : bmR_x02 (0xea7c4).
Proof.
  intros R F fc m q sp words n x P Q0 Q1 Q2.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.bm_E R q sp words n x) LbB_PmBMR.bm_sr R) by (unfold LbB_PmBMR.bm_E, LbB_PmBMR.bm_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.bm_E R q sp words n x) m LbB_PmBMR.bm_02_knF) by (unfold LbB_PmBMR.bm_E; knowB).
  destruct (LbB_PmBMR.bm_02_run fx R m (seg_rom asegs) q sp words n x ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.bm_02_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.bm_E R q sp words n x) in *. unfold LbB_PmBMR.bm_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 1; 1]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (15%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (17%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_x03 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp words n x : Z),
    bmR_x_pre R m q sp words n x -> (x mod 256 = 7) -> ((x / 256) mod 256 = 35) -> ((x / 65536) mod 256 = 2) -> (x / 16777216 <> 3) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 4784)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 4812)) fc None M' (seg_rom asegs))
      /\ munch [((sp - 8), sp); ((32 * q + 1728), (32 * q + 1744))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sp - 8) 8 (E + 4808)
      /\ fldA M' (32 * q + 1736) 8 n
      /\ fldA M' (32 * q + 1728) 8 words
      /\ getr R' 1 = wz (E + 4808)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz 18446744073709551612
      /\ getr R' 11 = wz ((32 * q) + 3544)
      /\ getr R' 13 = wz 3
      /\ getr R' 14 = wz ASHADOW_BASE
      /\ getr R' 15 = wz 2
      /\ getr R' 16 = wz 35
      /\ getr R' 17 = wz 7
      /\ getr R' 18 = wz ((32 * q) + 3456)
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ getr R' 24 = wz ((32 * q) + 3544)
      /\ getr R' 25 = wz ((32 * q) + 1728)
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_x03_bp : bmR_x03 (0xea7c4).
Proof.
  intros R F fc m q sp words n x P Q0 Q1 Q2 Q3.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.bm_E R q sp words n x) LbB_PmBMR.bm_sr R) by (unfold LbB_PmBMR.bm_E, LbB_PmBMR.bm_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.bm_E R q sp words n x) m LbB_PmBMR.bm_03_knF) by (unfold LbB_PmBMR.bm_E; knowB).
  destruct (LbB_PmBMR.bm_03_run fx R m (seg_rom asegs) q sp words n x ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.bm_03_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.bm_E R q sp words n x) in *. unfold LbB_PmBMR.bm_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 1; 1]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (15%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (17%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_x10 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp words n x : Z),
    bmR_x_pre R m q sp words n x -> (x mod 256 = 3) -> ((x / 256) mod 256 <> 2) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 4784)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 4812)) fc None M' (seg_rom asegs))
      /\ munch [((sp - 8), sp); ((32 * q + 1728), (32 * q + 1744))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sp - 8) 8 (E + 4808)
      /\ fldA M' (32 * q + 1736) 8 n
      /\ fldA M' (32 * q + 1728) 8 words
      /\ getr R' 1 = wz (E + 4808)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz 18446744073709551612
      /\ getr R' 11 = wz ((32 * q) + 3544)
      /\ getr R' 14 = wz ASHADOW_BASE
      /\ getr R' 16 = wz 2
      /\ getr R' 17 = wz 3
      /\ getr R' 18 = wz ((32 * q) + 3456)
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ getr R' 24 = wz ((32 * q) + 3544)
      /\ getr R' 25 = wz ((32 * q) + 1728)
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_x10_bp : bmR_x10 (0xea7c4).
Proof.
  intros R F fc m q sp words n x P Q0 Q1.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.bm_E R q sp words n x) LbB_PmBMR.bm_sr R) by (unfold LbB_PmBMR.bm_E, LbB_PmBMR.bm_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.bm_E R q sp words n x) m LbB_PmBMR.bm_10_knF) by (unfold LbB_PmBMR.bm_E; knowB).
  destruct (LbB_PmBMR.bm_10_run fx R m (seg_rom asegs) q sp words n x ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.bm_10_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.bm_E R q sp words n x) in *. unfold LbB_PmBMR.bm_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 1; 1]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (17%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_x20 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp words n x : Z),
    bmR_x_pre R m q sp words n x -> (x mod 256 = 3) -> ((x / 256) mod 256 = 2) -> ((x / 65536) mod 256 <> 35) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 4784)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 4812)) fc None M' (seg_rom asegs))
      /\ munch [((sp - 8), sp); ((32 * q + 1728), (32 * q + 1744))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sp - 8) 8 (E + 4808)
      /\ fldA M' (32 * q + 1736) 8 n
      /\ fldA M' (32 * q + 1728) 8 words
      /\ getr R' 1 = wz (E + 4808)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz 18446744073709551612
      /\ getr R' 11 = wz ((32 * q) + 3544)
      /\ getr R' 14 = wz ASHADOW_BASE
      /\ getr R' 15 = wz 35
      /\ getr R' 16 = wz 2
      /\ getr R' 17 = wz 3
      /\ getr R' 18 = wz ((32 * q) + 3456)
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ getr R' 24 = wz ((32 * q) + 3544)
      /\ getr R' 25 = wz ((32 * q) + 1728)
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_x20_bp : bmR_x20 (0xea7c4).
Proof.
  intros R F fc m q sp words n x P Q0 Q1 Q2.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.bm_E R q sp words n x) LbB_PmBMR.bm_sr R) by (unfold LbB_PmBMR.bm_E, LbB_PmBMR.bm_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.bm_E R q sp words n x) m LbB_PmBMR.bm_20_knF) by (unfold LbB_PmBMR.bm_E; knowB).
  destruct (LbB_PmBMR.bm_20_run fx R m (seg_rom asegs) q sp words n x ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.bm_20_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.bm_E R q sp words n x) in *. unfold LbB_PmBMR.bm_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 1; 1]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (15%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (17%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_x30 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp words n x : Z),
    bmR_x_pre R m q sp words n x -> (x mod 256 = 3) -> ((x / 256) mod 256 = 2) -> ((x / 65536) mod 256 = 35) -> (x / 16777216 <> 7) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 4784)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 4812)) fc None M' (seg_rom asegs))
      /\ munch [((sp - 8), sp); ((32 * q + 1728), (32 * q + 1744))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sp - 8) 8 (E + 4808)
      /\ fldA M' (32 * q + 1736) 8 n
      /\ fldA M' (32 * q + 1728) 8 words
      /\ getr R' 1 = wz (E + 4808)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz 18446744073709551612
      /\ getr R' 11 = wz ((32 * q) + 3544)
      /\ getr R' 13 = wz 7
      /\ getr R' 14 = wz ASHADOW_BASE
      /\ getr R' 15 = wz 35
      /\ getr R' 16 = wz 2
      /\ getr R' 17 = wz 3
      /\ getr R' 18 = wz ((32 * q) + 3456)
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ getr R' 24 = wz ((32 * q) + 3544)
      /\ getr R' 25 = wz ((32 * q) + 1728)
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_x30_bp : bmR_x30 (0xea7c4).
Proof.
  intros R F fc m q sp words n x P Q0 Q1 Q2 Q3.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.bm_E R q sp words n x) LbB_PmBMR.bm_sr R) by (unfold LbB_PmBMR.bm_E, LbB_PmBMR.bm_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.bm_E R q sp words n x) m LbB_PmBMR.bm_30_knF) by (unfold LbB_PmBMR.bm_E; knowB).
  destruct (LbB_PmBMR.bm_30_run fx R m (seg_rom asegs) q sp words n x ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.bm_30_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.bm_E R q sp words n x) in *. unfold LbB_PmBMR.bm_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 1; 1]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (15%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (17%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_p_pre (R : bvmap 5 word) (m : mem) (q sp : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 19 = wz ((4 * q) + ASHADOW_BASE)
  /\ getr R 20 = wz (32 * q)
  /\ wr_at asegs m (4 * q + 2147450932) 218
  /\ 227200 <= q <= 2 ^ 42
  /\ 2 ^ 45 + 16 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ 2 ^ 45 + 16 <= sp
  /\ sp <= 2 ^ 47
  /\ 0x6e6000 + 0x9000 <= 32 * q
  /\ 32 * q + 4096 <= 2 ^ 47
  /\ (32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q).

Definition bmR_p (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp : Z),
    bmR_p_pre R m q sp ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 4812)) fc None m (seg_rom asegs)) (MS R' F (wz AASAN_MEMSET) fc None M' (seg_rom asegs))
      /\ munch [((4 * q + 2147450932), (4 * q + 2147450935)); ((4 * q + 2147450948), (4 * q + 2147450951)); ((4 * q + 2147451100), (4 * q + 2147451150))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (4 * q + 2147450950) 1 0
      /\ fldA M' (4 * q + 2147450949) 1 0
      /\ fldA M' (4 * q + 2147450948) 1 0
      /\ fldA M' (4 * q + 2147450934) 1 0
      /\ fldA M' (4 * q + 2147450933) 1 0
      /\ fldA M' (4 * q + 2147450932) 1 0
      /\ fldA M' (4 * q + 2147451149) 1 0
      /\ fldA M' (4 * q + 2147451148) 1 0
      /\ fldA M' (4 * q + 2147451143) 1 0
      /\ fldA M' (4 * q + 2147451142) 1 0
      /\ fldA M' (4 * q + 2147451141) 1 0
      /\ fldA M' (4 * q + 2147451140) 1 0
      /\ fldA M' (4 * q + 2147451147) 1 0
      /\ fldA M' (4 * q + 2147451146) 1 0
      /\ fldA M' (4 * q + 2147451145) 1 0
      /\ fldA M' (4 * q + 2147451144) 1 0
      /\ fldA M' (4 * q + 2147451135) 1 0
      /\ fldA M' (4 * q + 2147451134) 1 0
      /\ fldA M' (4 * q + 2147451133) 1 0
      /\ fldA M' (4 * q + 2147451132) 1 0
      /\ fldA M' (4 * q + 2147451139) 1 0
      /\ fldA M' (4 * q + 2147451138) 1 0
      /\ fldA M' (4 * q + 2147451137) 1 0
      /\ fldA M' (4 * q + 2147451136) 1 0
      /\ fldA M' (4 * q + 2147451127) 1 0
      /\ fldA M' (4 * q + 2147451126) 1 0
      /\ fldA M' (4 * q + 2147451125) 1 0
      /\ fldA M' (4 * q + 2147451124) 1 0
      /\ fldA M' (4 * q + 2147451131) 1 0
      /\ fldA M' (4 * q + 2147451130) 1 0
      /\ fldA M' (4 * q + 2147451129) 1 0
      /\ fldA M' (4 * q + 2147451128) 1 0
      /\ fldA M' (4 * q + 2147451119) 1 0
      /\ fldA M' (4 * q + 2147451118) 1 0
      /\ fldA M' (4 * q + 2147451117) 1 0
      /\ fldA M' (4 * q + 2147451116) 1 0
      /\ fldA M' (4 * q + 2147451123) 1 0
      /\ fldA M' (4 * q + 2147451122) 1 0
      /\ fldA M' (4 * q + 2147451121) 1 0
      /\ fldA M' (4 * q + 2147451120) 1 0
      /\ fldA M' (4 * q + 2147451111) 1 0
      /\ fldA M' (4 * q + 2147451110) 1 0
      /\ fldA M' (4 * q + 2147451109) 1 0
      /\ fldA M' (4 * q + 2147451108) 1 0
      /\ fldA M' (4 * q + 2147451115) 1 0
      /\ fldA M' (4 * q + 2147451114) 1 0
      /\ fldA M' (4 * q + 2147451113) 1 0
      /\ fldA M' (4 * q + 2147451112) 1 0
      /\ fldA M' (4 * q + 2147451103) 1 0
      /\ fldA M' (4 * q + 2147451102) 1 0
      /\ fldA M' (4 * q + 2147451101) 1 0
      /\ fldA M' (4 * q + 2147451100) 1 0
      /\ fldA M' (4 * q + 2147451107) 1 0
      /\ fldA M' (4 * q + 2147451106) 1 0
      /\ fldA M' (4 * q + 2147451105) 1 0
      /\ fldA M' (4 * q + 2147451104) 1 0
      /\ getr R' 1 = wz (E + 5056)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz ((32 * q) + 416)
      /\ getr R' 11 = wz 0
      /\ getr R' 12 = wz 16
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ getr R' 24 = wz ((32 * q) + 416)
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_p_bp : bmR_p (0xea7c4).
Proof.
  intros R F fc m q sp P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.bp_E R q sp) LbB_PmBMR.bp_sr R) by (unfold LbB_PmBMR.bp_E, LbB_PmBMR.bp_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.bp_E R q sp) m LbB_PmBMR.bp_A_knF) by (unfold LbB_PmBMR.bp_E; knowB).
  destruct (LbB_PmBMR.bp_A_run fx R m (seg_rom asegs) q sp ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.bp_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.bp_E R q sp) in *. unfold LbB_PmBMR.bp_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [1; 1; 1; 0; 0; 0; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2]%nat|].
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
  split; [fld_postB_at 30%nat|].
  split; [fld_postB_at 31%nat|].
  split; [fld_postB_at 32%nat|].
  split; [fld_postB_at 33%nat|].
  split; [fld_postB_at 34%nat|].
  split; [fld_postB_at 35%nat|].
  split; [fld_postB_at 36%nat|].
  split; [fld_postB_at 37%nat|].
  split; [fld_postB_at 38%nat|].
  split; [fld_postB_at 39%nat|].
  split; [fld_postB_at 40%nat|].
  split; [fld_postB_at 41%nat|].
  split; [fld_postB_at 42%nat|].
  split; [fld_postB_at 43%nat|].
  split; [fld_postB_at 44%nat|].
  split; [fld_postB_at 45%nat|].
  split; [fld_postB_at 46%nat|].
  split; [fld_postB_at 47%nat|].
  split; [fld_postB_at 48%nat|].
  split; [fld_postB_at 49%nat|].
  split; [fld_postB_at 50%nat|].
  split; [fld_postB_at 51%nat|].
  split; [fld_postB_at 52%nat|].
  split; [fld_postB_at 53%nat|].
  split; [fld_postB_at 54%nat|].
  split; [fld_postB_at 55%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_tc_pre (R : bvmap 5 word) (m : mem) (q sp ic pc : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 18 = wz ((32 * q) + 3456)
  /\ getr R 19 = wz ((4 * q) + ASHADOW_BASE)
  /\ getr R 20 = wz (32 * q)
  /\ getr R 24 = wz ((32 * q) + 416)
  /\ fldA m (32 * q + 3536) 8 ic
  /\ fldA m (32 * q + 3464) 8 pc
  /\ wr_at asegs m (32 * q + 432) 8
  /\ wr_at asegs m (4 * q + 2147450940) 3
  /\ wr_at asegs m (32 * q + 480) 2
  /\ wr_at asegs m (32 * q + 544) 2
  /\ 227200 <= q <= 2 ^ 42
  /\ 2 ^ 45 + 16 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ 16 <= pc <= 2 ^ 47
  /\ pc mod 16 = 0
  /\ 2 ^ 45 + 16 <= sp
  /\ sp <= 2 ^ 47
  /\ 0x6e6000 + 0x9000 <= 32 * q
  /\ 32 * q + 4096 <= 2 ^ 47
  /\ (32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)
  /\ 0 <= ic < 2 ^ 64.

Definition bmR_tc (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp ic pc : Z),
    bmR_tc_pre R m q sp ic pc ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 5056)) fc None m (seg_rom asegs)) (MS R' F (wz 1010964) fc None M' (seg_rom asegs))
      /\ munch [((32 * q + 432), (32 * q + 440)); ((32 * q + 480), (32 * q + 482)); ((32 * q + 544), (32 * q + 546)); ((4 * q + 2147450940), (4 * q + 2147450943))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (32 * q + 544) 2 0
      /\ fldA M' (32 * q + 480) 2 0
      /\ fldA M' (4 * q + 2147450942) 1 0
      /\ fldA M' (4 * q + 2147450941) 1 0
      /\ fldA M' (4 * q + 2147450940) 1 0
      /\ fldA M' (32 * q + 432) 8 ic
      /\ getr R' 1 = wz (E + 5136)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz ((32 * q) + 1760)
      /\ getr R' 11 = wz ((32 * q) + 416)
      /\ getr R' 12 = wz pc
      /\ getr R' 13 = wz ((32 * q) + 480)
      /\ getr R' 14 = wz 18446744073709551612
      /\ getr R' 15 = wz ((32 * q) + 544)
      /\ getr R' 18 = wz ((32 * q) + 1760)
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ getr R' 24 = wz ((32 * q) + 416)
      /\ getr R' 25 = wz ((32 * q) + 480)
      /\ getr R' 26 = wz ((32 * q) + 544)
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 16; 17; 21; 22; 23; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_tc_bp : bmR_tc (0xea7c4).
Proof.
  intros R F fc m q sp ic pc P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.tc_E R q sp ic pc) LbB_PmBMR.tc_sr R) by (unfold LbB_PmBMR.tc_E, LbB_PmBMR.tc_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.tc_E R q sp ic pc) m LbB_PmBMR.tc_A_knF) by (unfold LbB_PmBMR.tc_E; knowB).
  destruct (LbB_PmBMR.tc_A_run fx R m (seg_rom asegs) q sp ic pc ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.tc_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.tc_E R q sp ic pc) in *. unfold LbB_PmBMR.tc_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [2; 1; 3; 3; 3; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fld_postB_at 3%nat|].
  split; [fld_postB_at 4%nat|].
  split; [fld_postB_at 5%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (15%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  split; [rrwB HR' (26%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 16; 17; 21; 22; 23; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_ts_pre (R : bvmap 5 word) (m : mem) (q sp : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 18 = wz ((32 * q) + 1760)
  /\ getr R 19 = wz ((4 * q) + ASHADOW_BASE)
  /\ getr R 20 = wz (32 * q)
  /\ getr R 25 = wz ((32 * q) + 480)
  /\ getr R 26 = wz ((32 * q) + 544)
  /\ fldA m (32 * q + 544) 1 0
  /\ fldA m (32 * q + 480) 1 0
  /\ wr_at asegs m (4 * q + 2147450932) 19
  /\ 227200 <= q <= 2 ^ 42
  /\ 2 ^ 45 + 16 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ 2 ^ 45 + 16 <= sp
  /\ sp <= 2 ^ 47
  /\ 0x6e6000 + 0x9000 <= 32 * q
  /\ 32 * q + 4096 <= 2 ^ 47
  /\ (32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q).

Definition bmR_ts (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp : Z),
    bmR_ts_pre R m q sp ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 5136)) fc None m (seg_rom asegs)) (MS R' F (wz 1008288) fc None M' (seg_rom asegs))
      /\ munch [((4 * q + 2147450932), (4 * q + 2147450935)); ((4 * q + 2147450940), (4 * q + 2147450943)); ((4 * q + 2147450948), (4 * q + 2147450951))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (4 * q + 2147450950) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147450949) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147450948) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147450942) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147450941) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147450940) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147450934) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147450933) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147450932) 1 18446744073709551608
      /\ getr R' 1 = wz (E + 5252)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz ((32 * q) + 1760)
      /\ getr R' 11 = wz 147936
      /\ getr R' 12 = wz 29
      /\ getr R' 18 = wz ((32 * q) + 1760)
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ getr R' 25 = wz ((32 * q) + 480)
      /\ getr R' 26 = wz ((32 * q) + 544)
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 21; 22; 23; 24; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_ts_bp : bmR_ts (0xea7c4).
Proof.
  intros R F fc m q sp P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.ts_E R q sp) LbB_PmBMR.ts_sr R) by (unfold LbB_PmBMR.ts_E, LbB_PmBMR.ts_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.ts_E R q sp) m LbB_PmBMR.ts_A_knF) by (unfold LbB_PmBMR.ts_E; knowB).
  destruct (LbB_PmBMR.ts_A_run fx R m (seg_rom asegs) q sp ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.ts_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.ts_E R q sp) in *. unfold LbB_PmBMR.ts_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [2; 2; 2; 1; 1; 1; 0; 0; 0]%nat|].
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
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  split; [rrwB HR' (26%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 21; 22; 23; 24; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_ha_pre (R : bvmap 5 word) (m : mem) (q sp vt words x : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 18 = wz ((32 * q) + 1760)
  /\ getr R 19 = wz ((4 * q) + ASHADOW_BASE)
  /\ getr R 20 = wz (32 * q)
  /\ getr R 22 = wz ((32 * q) + 3504)
  /\ getr R 27 = wz ASHADOW_BASE
  /\ fldA m (32 * q + 1760) 8 vt
  /\ fldA m (vt - 24) 8 112
  /\ fldA m (32 * q + 1880) 4 4098
  /\ wr_at asegs m (32 * q + 1880) 4
  /\ fldA m (32 * q + 3504) 8 words
  /\ fldA m words 4 x
  /\ fldA m (4 * q + 2147451115) 1 0
  /\ 227200 <= q <= 2 ^ 42
  /\ 2 ^ 45 + 16 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ 24 <= vt <= 2 ^ 47 + 16
  /\ 16 <= words <= 2 ^ 47
  /\ words mod 16 = 0
  /\ 0 <= x <= 2 ^ 32 - 1
  /\ (words + 4 <= (32 * q) \/ (32 * q) + 4096 <= words)
  /\ sh0 m (vt - 24)
  /\ sh0 m words
  /\ 2 ^ 45 + 16 <= sp
  /\ sp <= 2 ^ 47
  /\ 0x6e6000 + 0x9000 <= 32 * q
  /\ 32 * q + 4096 <= 2 ^ 47
  /\ (32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)
  /\ 0 <= x < 2 ^ 32.

Definition bmR_ha (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp vt words x : Z),
    bmR_ha_pre R m q sp vt words x ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 5252)) fc None m (seg_rom asegs)) (MS R' F (wz 1200700) fc None M' (seg_rom asegs))
      /\ munch [((32 * q + 1880), (32 * q + 1884))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (32 * q + 1880) 4 4104
      /\ getr R' 1 = wz (E + 5372)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz ((32 * q) + 1760)
      /\ getr R' 11 = wz (ext_Z true 0 4 x)
      /\ getr R' 12 = wz 4104
      /\ getr R' 18 = wz ((32 * q) + 1760)
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ getr R' 22 = wz ((32 * q) + 3504)
      /\ getr R' 27 = wz ASHADOW_BASE
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 21; 23; 24; 25; 26; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_ha_bp : bmR_ha (0xea7c4).
Proof.
  intros R F fc m q sp vt words x P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.ha_E R q sp vt words x) LbB_PmBMR.ha_sr R) by (unfold LbB_PmBMR.ha_E, LbB_PmBMR.ha_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.ha_E R q sp vt words x) m LbB_PmBMR.ha_A_knF) by (unfold LbB_PmBMR.ha_E; knowB).
  destruct (LbB_PmBMR.ha_A_run fx R m (seg_rom asegs) q sp vt words x ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.ha_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.ha_E R q sp vt words x) in *. unfold LbB_PmBMR.ha_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); unfold ext_val, wz; rewrite ?u64_of_Z by dlia; reflexivity|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (27%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 21; 23; 24; 25; 26; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_hb_pre (R : bvmap 5 word) (m : mem) (q sp vt words x : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 18 = wz ((32 * q) + 1760)
  /\ getr R 19 = wz ((4 * q) + ASHADOW_BASE)
  /\ getr R 20 = wz (32 * q)
  /\ getr R 22 = wz ((32 * q) + 3504)
  /\ getr R 27 = wz ASHADOW_BASE
  /\ fldA m (32 * q + 1760) 8 vt
  /\ fldA m (vt - 24) 8 112
  /\ fldA m (32 * q + 1880) 4 4104
  /\ wr_at asegs m (32 * q + 1880) 4
  /\ fldA m (32 * q + 3504) 8 words
  /\ fldA m words 4 x
  /\ fldA m (4 * q + 2147451115) 1 0
  /\ 227200 <= q <= 2 ^ 42
  /\ 2 ^ 45 + 16 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ 24 <= vt <= 2 ^ 47 + 16
  /\ 16 <= words <= 2 ^ 47
  /\ words mod 16 = 0
  /\ 0 <= x <= 2 ^ 32 - 1
  /\ (words + 4 <= (32 * q) \/ (32 * q) + 4096 <= words)
  /\ sh0 m (vt - 24)
  /\ sh0 m words
  /\ 2 ^ 45 + 16 <= sp
  /\ sp <= 2 ^ 47
  /\ 0x6e6000 + 0x9000 <= 32 * q
  /\ 32 * q + 4096 <= 2 ^ 47
  /\ (32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)
  /\ 0 <= x < 2 ^ 32.

Definition bmR_hb (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp vt words x : Z),
    bmR_hb_pre R m q sp vt words x ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 5252)) fc None m (seg_rom asegs)) (MS R' F (wz 1200700) fc None M' (seg_rom asegs))
      /\ munch [((32 * q + 1880), (32 * q + 1884))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (32 * q + 1880) 4 4104
      /\ getr R' 1 = wz (E + 5372)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz ((32 * q) + 1760)
      /\ getr R' 11 = wz (ext_Z true 0 4 x)
      /\ getr R' 12 = wz 4104
      /\ getr R' 18 = wz ((32 * q) + 1760)
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ getr R' 22 = wz ((32 * q) + 3504)
      /\ getr R' 27 = wz ASHADOW_BASE
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 21; 23; 24; 25; 26; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_hb_bp : bmR_hb (0xea7c4).
Proof.
  intros R F fc m q sp vt words x P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.hb_E R q sp vt words x) LbB_PmBMR.hb_sr R) by (unfold LbB_PmBMR.hb_E, LbB_PmBMR.hb_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.hb_E R q sp vt words x) m LbB_PmBMR.hb_A_knF) by (unfold LbB_PmBMR.hb_E; knowB).
  destruct (LbB_PmBMR.hb_A_run fx R m (seg_rom asegs) q sp vt words x ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.hb_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.hb_E R q sp vt words x) in *. unfold LbB_PmBMR.hb_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); unfold ext_val, wz; rewrite ?u64_of_Z by dlia; reflexivity|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (27%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 21; 23; 24; 25; 26; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_tq_pre (R : bvmap 5 word) (m : mem) (q sp : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 18 = wz ((32 * q) + 1760)
  /\ getr R 19 = wz ((4 * q) + ASHADOW_BASE)
  /\ getr R 20 = wz (32 * q)
  /\ 227200 <= q <= 2 ^ 42
  /\ 2 ^ 45 + 16 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ 2 ^ 45 + 16 <= sp
  /\ sp <= 2 ^ 47
  /\ 0x6e6000 + 0x9000 <= 32 * q
  /\ 32 * q + 4096 <= 2 ^ 47
  /\ (32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q).

Definition bmR_tq (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp : Z),
    bmR_tq_pre R m q sp ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 5372)) fc None m (seg_rom asegs)) (MS R' F (wz 1008288) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz (E + 5392)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz ((32 * q) + 1760)
      /\ getr R' 11 = wz 148000
      /\ getr R' 12 = wz 2
      /\ getr R' 18 = wz ((32 * q) + 1760)
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_tq_bp : bmR_tq (0xea7c4).
Proof.
  intros R F fc m q sp P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.tq_E R q sp) LbB_PmBMR.tq_sr R) by (unfold LbB_PmBMR.tq_E, LbB_PmBMR.tq_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.tq_E R q sp) m LbB_PmBMR.tq_A_knF) by (unfold LbB_PmBMR.tq_E; knowB).
  destruct (LbB_PmBMR.tq_A_run fx R m (seg_rom asegs) q sp ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.tq_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.tq_E R q sp) in *. unfold LbB_PmBMR.tq_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_td_pre (R : bvmap 5 word) (m : mem) (q sp : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 18 = wz ((32 * q) + 1760)
  /\ getr R 19 = wz ((4 * q) + ASHADOW_BASE)
  /\ getr R 20 = wz (32 * q)
  /\ fldA m (32 * q + 2120) 4 4294967292
  /\ 227200 <= q <= 2 ^ 42
  /\ 2 ^ 45 + 16 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ 2 ^ 45 + 16 <= sp
  /\ sp <= 2 ^ 47
  /\ 0x6e6000 + 0x9000 <= 32 * q
  /\ 32 * q + 4096 <= 2 ^ 47
  /\ (32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q).

Definition bmR_td (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp : Z),
    bmR_td_pre R m q sp ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 5392)) fc None m (seg_rom asegs)) (MS R' F (wz 1034672) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz (E + 5404)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz ((32 * q) + 1760)
      /\ getr R' 18 = wz ((32 * q) + 1760)
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ getr R' 24 = wz 18446744073709551612
      /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_td_bp : bmR_td (0xea7c4).
Proof.
  intros R F fc m q sp P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.td_E R q sp) LbB_PmBMR.td_sr R) by (unfold LbB_PmBMR.td_E, LbB_PmBMR.td_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.td_E R q sp) m LbB_PmBMR.td_A_knF) by (unfold LbB_PmBMR.td_E; knowB).
  destruct (LbB_PmBMR.td_A_run fx R m (seg_rom asegs) q sp ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.td_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.td_E R q sp) in *. unfold LbB_PmBMR.td_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition bmR_te_pre (R : bvmap 5 word) (m : mem) (q sp : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 19 = wz ((4 * q) + ASHADOW_BASE)
  /\ getr R 20 = wz (32 * q)
  /\ wr_at asegs m (4 * q + 2147451100) 50
  /\ 227200 <= q <= 2 ^ 42
  /\ 2 ^ 45 + 16 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ 2 ^ 45 + 16 <= sp
  /\ sp <= 2 ^ 47
  /\ 0x6e6000 + 0x9000 <= 32 * q
  /\ 32 * q + 4096 <= 2 ^ 47
  /\ (32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q).

Definition bmR_te (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp : Z),
    bmR_te_pre R m q sp ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 5404)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 6448)) fc None M' (seg_rom asegs))
      /\ munch [((4 * q + 2147451100), (4 * q + 2147451150))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (4 * q + 2147451149) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451148) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451143) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451142) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451141) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451140) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451147) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451146) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451145) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451144) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451135) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451134) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451133) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451132) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451139) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451138) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451137) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451136) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451127) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451126) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451125) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451124) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451131) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451130) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451129) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451128) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451119) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451118) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451117) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451116) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451123) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451122) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451121) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451120) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451111) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451110) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451109) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451108) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451115) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451114) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451113) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451112) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451103) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451102) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451101) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451100) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451107) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451106) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451105) 1 18446744073709551608
      /\ fldA M' (4 * q + 2147451104) 1 18446744073709551608
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz 18446744073709551608
      /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
      /\ getr R' 20 = wz (32 * q)
      /\ (forall r, In r [1; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma bmR_te_bp : bmR_te (0xea7c4).
Proof.
  intros R F fc m q sp P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmBMR.te_E R q sp) LbB_PmBMR.te_sr R) by (unfold LbB_PmBMR.te_E, LbB_PmBMR.te_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmBMR.te_E R q sp) m LbB_PmBMR.te_A_knF) by (unfold LbB_PmBMR.te_E; knowB).
  destruct (LbB_PmBMR.te_A_run fx R m (seg_rom asegs) q sp ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmBMR.te_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmBMR.te_E R q sp) in *. unfold LbB_PmBMR.te_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%nat|].
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
  split; [fld_postB_at 30%nat|].
  split; [fld_postB_at 31%nat|].
  split; [fld_postB_at 32%nat|].
  split; [fld_postB_at 33%nat|].
  split; [fld_postB_at 34%nat|].
  split; [fld_postB_at 35%nat|].
  split; [fld_postB_at 36%nat|].
  split; [fld_postB_at 37%nat|].
  split; [fld_postB_at 38%nat|].
  split; [fld_postB_at 39%nat|].
  split; [fld_postB_at 40%nat|].
  split; [fld_postB_at 41%nat|].
  split; [fld_postB_at 42%nat|].
  split; [fld_postB_at 43%nat|].
  split; [fld_postB_at 44%nat|].
  split; [fld_postB_at 45%nat|].
  split; [fld_postB_at 46%nat|].
  split; [fld_postB_at 47%nat|].
  split; [fld_postB_at 48%nat|].
  split; [fld_postB_at 49%nat|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  keptB HR HR' ([1; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.
