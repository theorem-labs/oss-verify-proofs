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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_V4W32 LbB_V4W32R.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition v32_B3a_pre (R : bvmap 5 word) (m : mem) (bn sp v src cap b x nc : Z) : Prop :=
  getr R 10 = wz bn
  /\ getr R 2 = wz sp
  /\ getr R 8 = wz (v + 8)
  /\ getr R 23 = wz v
  /\ getr R 9 = wz src
  /\ getr R 19 = wz (sh (v + 8))
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (4 * cap)
  /\ getr R 22 = wz nc
  /\ getr R 18 = wz (4 * nc)
  /\ ACONST m
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (4 * cap))
  /\ fldA m (v + 16) 8 (b + (4 * cap))
  /\ fldA m src 4 x
  /\ sh0 m src
  /\ fldA m (sp + 32) 8 v
  /\ wr_at asegs m sp 32
  /\ wr_at asegs m (bn + (4 * cap)) 4
  /\ bn mod 16 = 0
  /\ 1048576 <= bn <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= src <= 2 ^ 47
  /\ 0 <= x <= 2 ^ 32
  /\ 1 <= cap <= 2 ^ 24
  /\ 2 <= nc <= 2 ^ 25
  /\ 16 <= b <= 2 ^ 47
  /\ 2 ^ 45 + 112 <= sp <= 2 ^ 47
  /\ wr_at asegs m (sp - 112) 112
  /\ (v + 24 <= (sp - 112) \/ (sp - 112) + 224 <= v)
  /\ sh0 m (bn + (4 * cap))
  /\ sh0 m v
  /\ sh0 m (v + 8)
  /\ sh0 m (v + 16)
  /\ 1048576 <= bn
  /\ bn + 4 * nc < 2 ^ 47
  /\ 2 ^ 45 + 112 <= sp
  /\ sp + 112 <= 2 ^ 47
  /\ 0 <= src
  /\ src + 4 <= 2 ^ 47
  /\ (src + 4 <= sp \/ sp + 112 <= src)
  /\ 0 <= x < 2 ^ 32
  /\ cap < nc <= 2 ^ 25
  /\ (v + 24 <= sp - 112 \/ sp + 112 <= v)
  /\ (v + 24 <= 2147446784 \/ 17594333495296 <= v)
  /\ (sp + 112 <= 2147446784 \/ 17594333495296 <= sp - 112)
  /\ 16 <= b
  /\ b + 4 * cap < 2 ^ 47
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 7241728 <= bn
  /\ (bn + 4 * nc <= 2147446784 \/ 17594333495296 <= bn)
  /\ (v + 24 <= bn + 4 * cap \/ bn + 4 * cap + 4 <= v)
  /\ bn + 4 * nc <= sp - 112.

Definition v32_B3a (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (bn sp v src cap b x nc : Z),
    v32_B3a_pre R m bn sp v src cap b x nc ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 200)) fc None m (seg_rom asegs)) (MS R' F (wz AANNOTATE_CC) fc None M' (seg_rom asegs))
      /\ munch [((sp - 104), (sp + 32)); ((bn + (4 * cap)), (bn + (4 * cap) + 4))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sp - 104) 8 954568
      /\ fldA M' (sp - 96) 8 sp
      /\ fldA M' (sp - 88) 8 956276
      /\ fldw asegs M' (sp - 80) 8 (getr R 24)
      /\ fldA M' (sp - 72) 8 v
      /\ fldA M' (sp - 64) 8 nc
      /\ fldA M' (sp - 56) 8 (4 * cap)
      /\ fldA M' (sp - 48) 8 ASHADOW_BASE
      /\ fldA M' (sp - 40) 8 (sh (v + 8))
      /\ fldA M' (sp - 32) 8 (bn + (4 * nc))
      /\ fldA M' (sp - 24) 8 src
      /\ fldA M' (sp - 16) 8 (v + 8)
      /\ fldA M' (sp - 8) 8 (E + 404)
      /\ fldA M' (sp + 16) 8 ((bn + (4 * cap)) + 4)
      /\ fldA M' (bn + (4 * cap)) 4 x
      /\ fldA M' (sp + 24) 8 (bn + (4 * nc))
      /\ fldA M' (sp + 8) 8 (bn + (4 * cap))
      /\ fldA M' sp 8 bn
      /\ getr R' 1 = wz 954568
      /\ getr R' 2 = wz (sp - 96)
      /\ getr R' 8 = wz sp
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz b
      /\ getr R' 11 = wz (b + (4 * cap))
      /\ getr R' 12 = wz ((4 * cap) + b)
      /\ getr R' 13 = wz ((4 * cap) + b)
      /\ getr R' 14 = wz 1
      /\ getr R' 15 = wz 0
      /\ getr R' 16 = wz ((v + 16) / 8)
      /\ getr R' 18 = wz (bn + (4 * nc))
      /\ getr R' 19 = wz (sh (v + 8))
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz ASHADOW_BASE
      /\ getr R' 22 = wz nc
      /\ getr R' 23 = wz v
      /\ (forall r, In r [3; 4; 5; 6; 7; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma v32_B3a_f871c : v32_B3a (v4_entry V32_SLOW_CREF).
Proof.
  intros R F fc m bn sp v src cap b x nc P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32.b3a_E R bn sp v src cap b x nc) LbB_V4W32.b3a_sr R) by (unfold LbB_V4W32.b3a_E, LbB_V4W32.b3a_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32.b3a_E R bn sp v src cap b x nc) m LbB_V4W32.b3a_A_knF) by (unfold LbB_V4W32.b3a_E; knowB).
  destruct (LbB_V4W32.b3a_A_run fx R m (seg_rom asegs) bn sp v src cap b x nc ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32.b3a_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32.b3a_E R bn sp v src cap b x nc) in *. unfold LbB_V4W32.b3a_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
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
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (15%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma v32_B3a_f898c : v32_B3a (v4_entry V32_SLOW_RREF).
Proof.
  intros R F fc m bn sp v src cap b x nc P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32R.b3a_E R bn sp v src cap b x nc) LbB_V4W32R.b3a_sr R) by (unfold LbB_V4W32R.b3a_E, LbB_V4W32R.b3a_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32R.b3a_E R bn sp v src cap b x nc) m LbB_V4W32R.b3a_A_knF) by (unfold LbB_V4W32R.b3a_E; knowB).
  destruct (LbB_V4W32R.b3a_A_run fx R m (seg_rom asegs) bn sp v src cap b x nc ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32R.b3a_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32R.b3a_E R bn sp v src cap b x nc) in *. unfold LbB_V4W32R.b3a_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
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
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (15%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition v32_B3ak_pre (R : bvmap 5 word) (m : mem) (bn sp v src cap b x nc k : Z) : Prop :=
  getr R 10 = wz bn
  /\ getr R 2 = wz sp
  /\ getr R 8 = wz (v + 8)
  /\ getr R 23 = wz v
  /\ getr R 9 = wz src
  /\ getr R 19 = wz (sh (v + 8))
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (4 * cap)
  /\ getr R 22 = wz nc
  /\ getr R 18 = wz (4 * nc)
  /\ ACONST m
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (4 * cap))
  /\ fldA m (v + 16) 8 (b + (4 * cap))
  /\ fldA m src 4 x
  /\ shk m src k
  /\ fldA m (sp + 32) 8 v
  /\ wr_at asegs m sp 32
  /\ wr_at asegs m (bn + (4 * cap)) 4
  /\ bn mod 16 = 0
  /\ 1048576 <= bn <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= src <= 2 ^ 47
  /\ 0 <= x <= 2 ^ 32
  /\ 1 <= cap <= 2 ^ 24
  /\ 2 <= nc <= 2 ^ 25
  /\ 16 <= b <= 2 ^ 47
  /\ 2 ^ 45 + 112 <= sp <= 2 ^ 47
  /\ wr_at asegs m (sp - 112) 112
  /\ (v + 24 <= (sp - 112) \/ (sp - 112) + 224 <= v)
  /\ 4 <= k <= 7
  /\ src mod 8 = 0
  /\ sh0 m (bn + (4 * cap))
  /\ sh0 m v
  /\ sh0 m (v + 8)
  /\ sh0 m (v + 16)
  /\ 1048576 <= bn
  /\ bn + 4 * nc < 2 ^ 47
  /\ 2 ^ 45 + 112 <= sp
  /\ sp + 112 <= 2 ^ 47
  /\ 0 <= src
  /\ src + 4 <= 2 ^ 47
  /\ (src + 4 <= sp \/ sp + 112 <= src)
  /\ 0 <= x < 2 ^ 32
  /\ cap < nc <= 2 ^ 25
  /\ (v + 24 <= sp - 112 \/ sp + 112 <= v)
  /\ (v + 24 <= 2147446784 \/ 17594333495296 <= v)
  /\ (sp + 112 <= 2147446784 \/ 17594333495296 <= sp - 112)
  /\ 16 <= b
  /\ b + 4 * cap < 2 ^ 47
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 7241728 <= bn
  /\ (bn + 4 * nc <= 2147446784 \/ 17594333495296 <= bn)
  /\ (v + 24 <= bn + 4 * cap \/ bn + 4 * cap + 4 <= v)
  /\ bn + 4 * nc <= sp - 112.

Definition v32_B3ak (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (bn sp v src cap b x nc k : Z),
    v32_B3ak_pre R m bn sp v src cap b x nc k ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 200)) fc None m (seg_rom asegs)) (MS R' F (wz AANNOTATE_CC) fc None M' (seg_rom asegs))
      /\ munch [((sp - 104), (sp + 32)); ((bn + (4 * cap)), (bn + (4 * cap) + 4))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sp - 104) 8 954568
      /\ fldA M' (sp - 96) 8 sp
      /\ fldA M' (sp - 88) 8 956276
      /\ fldw asegs M' (sp - 80) 8 (getr R 24)
      /\ fldA M' (sp - 72) 8 v
      /\ fldA M' (sp - 64) 8 nc
      /\ fldA M' (sp - 56) 8 (4 * cap)
      /\ fldA M' (sp - 48) 8 ASHADOW_BASE
      /\ fldA M' (sp - 40) 8 (sh (v + 8))
      /\ fldA M' (sp - 32) 8 (bn + (4 * nc))
      /\ fldA M' (sp - 24) 8 src
      /\ fldA M' (sp - 16) 8 (v + 8)
      /\ fldA M' (sp - 8) 8 (E + 404)
      /\ fldA M' (sp + 16) 8 ((bn + (4 * cap)) + 4)
      /\ fldA M' (bn + (4 * cap)) 4 x
      /\ fldA M' (sp + 24) 8 (bn + (4 * nc))
      /\ fldA M' (sp + 8) 8 (bn + (4 * cap))
      /\ fldA M' sp 8 bn
      /\ getr R' 1 = wz 954568
      /\ getr R' 2 = wz (sp - 96)
      /\ getr R' 8 = wz sp
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz b
      /\ getr R' 11 = wz (b + (4 * cap))
      /\ getr R' 12 = wz ((4 * cap) + b)
      /\ getr R' 13 = wz ((4 * cap) + b)
      /\ getr R' 14 = wz 1
      /\ getr R' 15 = wz 0
      /\ getr R' 16 = wz ((v + 16) / 8)
      /\ getr R' 18 = wz (bn + (4 * nc))
      /\ getr R' 19 = wz (sh (v + 8))
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz ASHADOW_BASE
      /\ getr R' 22 = wz nc
      /\ getr R' 23 = wz v
      /\ (forall r, In r [3; 4; 5; 6; 7; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma v32_B3ak_f871c : v32_B3ak (v4_entry V32_SLOW_CREF).
Proof.
  intros R F fc m bn sp v src cap b x nc k P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54 & P55). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32.b3ak_E R bn sp v src cap b x nc k) LbB_V4W32.b3ak_sr R) by (unfold LbB_V4W32.b3ak_E, LbB_V4W32.b3ak_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32.b3ak_E R bn sp v src cap b x nc k) m LbB_V4W32.b3ak_A_knF) by (unfold LbB_V4W32.b3ak_E; knowB).
  destruct (LbB_V4W32.b3ak_A_run fx R m (seg_rom asegs) bn sp v src cap b x nc k ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32.b3ak_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32.b3ak_E R bn sp v src cap b x nc k) in *. unfold LbB_V4W32.b3ak_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
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
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (15%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma v32_B3ak_f898c : v32_B3ak (v4_entry V32_SLOW_RREF).
Proof.
  intros R F fc m bn sp v src cap b x nc k P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54 & P55). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32R.b3ak_E R bn sp v src cap b x nc k) LbB_V4W32R.b3ak_sr R) by (unfold LbB_V4W32R.b3ak_E, LbB_V4W32R.b3ak_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32R.b3ak_E R bn sp v src cap b x nc k) m LbB_V4W32R.b3ak_A_knF) by (unfold LbB_V4W32R.b3ak_E; knowB).
  destruct (LbB_V4W32R.b3ak_A_run fx R m (seg_rom asegs) bn sp v src cap b x nc k ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32R.b3ak_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32R.b3ak_E R bn sp v src cap b x nc k) in *. unfold LbB_V4W32R.b3ak_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
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
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (15%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition v32_B3b_pre (R : bvmap 5 word) (m : mem) (bn sp v src cap b x nc : Z) : Prop :=
  getr R 10 = wz bn
  /\ getr R 2 = wz sp
  /\ getr R 8 = wz (v + 8)
  /\ getr R 23 = wz v
  /\ getr R 9 = wz src
  /\ getr R 19 = wz (sh (v + 8))
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (4 * cap)
  /\ getr R 22 = wz nc
  /\ getr R 18 = wz (4 * nc)
  /\ ACONST m
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (4 * cap))
  /\ fldA m (v + 16) 8 (b + (4 * cap))
  /\ fldA m src 4 x
  /\ sh0 m src
  /\ fldA m (sp + 32) 8 v
  /\ wr_at asegs m sp 32
  /\ wr_at asegs m (bn + (4 * cap)) 4
  /\ bn mod 16 = 0
  /\ 1048576 <= bn <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= src <= 2 ^ 47
  /\ 0 <= x <= 2 ^ 32
  /\ 1 <= nc <= 2 ^ 25
  /\ 2 ^ 45 + 112 <= sp <= 2 ^ 47
  /\ wr_at asegs m (sp - 112) 112
  /\ (v + 24 <= (sp - 112) \/ (sp - 112) + 224 <= v)
  /\ 0 <= b <= 1
  /\ 0 <= cap <= 1
  /\ shk m (bn + (4 * cap)) 4
  /\ sh0 m v
  /\ sh0 m (v + 8)
  /\ sh0 m (v + 16)
  /\ sh0 m (sp + 8)
  /\ 1048576 <= bn
  /\ bn + 4 * nc < 2 ^ 47
  /\ 2 ^ 45 + 112 <= sp
  /\ sp + 112 <= 2 ^ 47
  /\ 0 <= src
  /\ src + 4 <= 2 ^ 47
  /\ (src + 4 <= sp \/ sp + 112 <= src)
  /\ 0 <= x < 2 ^ 32
  /\ (v + 24 <= sp - 112 \/ sp + 112 <= v)
  /\ (v + 24 <= 2147446784 \/ 17594333495296 <= v)
  /\ (sp + 112 <= 2147446784 \/ 17594333495296 <= sp - 112)
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 7241728 <= bn
  /\ (bn + 4 * nc <= 2147446784 \/ 17594333495296 <= bn)
  /\ (v + 24 <= bn + 4 * cap \/ bn + 4 * cap + 4 <= v)
  /\ b = 0
  /\ cap = 0
  /\ b mod 4 = 0
  /\ bn + 4 * nc <= sp - 112.

Definition v32_B3b (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (bn sp v src cap b x nc : Z),
    v32_B3b_pre R m bn sp v src cap b x nc ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 200)) fc None m (seg_rom asegs)) (MS R' F (wz AASAN_MEMCPY) fc None M' (seg_rom asegs))
      /\ munch [((sp - 104), (sp + 32)); ((bn + (4 * cap)), (bn + (4 * cap) + 4))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sp - 104) 8 954568
      /\ fldA M' (sp - 96) 8 sp
      /\ fldA M' (sp - 88) 8 956276
      /\ fldw asegs M' (sp - 80) 8 (getr R 24)
      /\ fldA M' (sp - 72) 8 v
      /\ fldA M' (sp - 64) 8 nc
      /\ fldA M' (sp - 56) 8 (4 * cap)
      /\ fldA M' (sp - 48) 8 ASHADOW_BASE
      /\ fldA M' (sp - 40) 8 (sh (v + 8))
      /\ fldA M' (sp - 32) 8 (bn + (4 * nc))
      /\ fldA M' (sp - 24) 8 src
      /\ fldA M' (sp - 16) 8 (v + 8)
      /\ fldA M' (sp - 8) 8 (E + 404)
      /\ fldA M' (sp + 16) 8 ((bn + (4 * cap)) + 4)
      /\ fldA M' (bn + (4 * cap)) 4 x
      /\ fldA M' (sp + 24) 8 (bn + (4 * nc))
      /\ fldA M' (sp + 8) 8 (bn + (4 * cap))
      /\ fldA M' sp 8 bn
      /\ getr R' 1 = wz 956436
      /\ getr R' 2 = wz (sp - 80)
      /\ getr R' 8 = wz sp
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz (bn + ((4 * cap) + ((-4) * ((4 * cap) / 4))))
      /\ getr R' 11 = wz b
      /\ getr R' 12 = wz (4 * cap)
      /\ getr R' 13 = wz ((-4) * ((4 * cap) / 4))
      /\ getr R' 16 = wz ((v + 16) / 8)
      /\ getr R' 18 = wz (v + 8)
      /\ getr R' 19 = wz (sp + 8)
      /\ getr R' 20 = wz (bn + ((4 * cap) + ((-4) * ((4 * cap) / 4))))
      /\ getr R' 21 = wz ASHADOW_BASE
      /\ getr R' 22 = wz (sh (v + 8))
      /\ getr R' 23 = wz (sh (sp + 8))
      /\ getr R' 24 = wz (sh v)
      /\ (forall r, In r [3; 4; 5; 6; 7; 17; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma v32_B3b_f871c : v32_B3b (v4_entry V32_SLOW_CREF).
Proof.
  intros R F fc m bn sp v src cap b x nc P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32.b3b_E R bn sp v src cap b x nc) LbB_V4W32.b3b_sr R) by (unfold LbB_V4W32.b3b_E, LbB_V4W32.b3b_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32.b3b_E R bn sp v src cap b x nc) m LbB_V4W32.b3b_A_knF) by (unfold LbB_V4W32.b3b_E; knowB).
  destruct (LbB_V4W32.b3b_A_run fx R m (seg_rom asegs) bn sp v src cap b x nc ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32.b3b_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32.b3b_E R bn sp v src cap b x nc) in *. unfold LbB_V4W32.b3b_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
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
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 17; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma v32_B3b_f898c : v32_B3b (v4_entry V32_SLOW_RREF).
Proof.
  intros R F fc m bn sp v src cap b x nc P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32R.b3b_E R bn sp v src cap b x nc) LbB_V4W32R.b3b_sr R) by (unfold LbB_V4W32R.b3b_E, LbB_V4W32R.b3b_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32R.b3b_E R bn sp v src cap b x nc) m LbB_V4W32R.b3b_A_knF) by (unfold LbB_V4W32R.b3b_E; knowB).
  destruct (LbB_V4W32R.b3b_A_run fx R m (seg_rom asegs) bn sp v src cap b x nc ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32R.b3b_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32R.b3b_E R bn sp v src cap b x nc) in *. unfold LbB_V4W32R.b3b_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
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
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 17; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition v32_B3bk_pre (R : bvmap 5 word) (m : mem) (bn sp v src cap b x nc k : Z) : Prop :=
  getr R 10 = wz bn
  /\ getr R 2 = wz sp
  /\ getr R 8 = wz (v + 8)
  /\ getr R 23 = wz v
  /\ getr R 9 = wz src
  /\ getr R 19 = wz (sh (v + 8))
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (4 * cap)
  /\ getr R 22 = wz nc
  /\ getr R 18 = wz (4 * nc)
  /\ ACONST m
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (4 * cap))
  /\ fldA m (v + 16) 8 (b + (4 * cap))
  /\ fldA m src 4 x
  /\ shk m src k
  /\ fldA m (sp + 32) 8 v
  /\ wr_at asegs m sp 32
  /\ wr_at asegs m (bn + (4 * cap)) 4
  /\ bn mod 16 = 0
  /\ 1048576 <= bn <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= src <= 2 ^ 47
  /\ 0 <= x <= 2 ^ 32
  /\ 1 <= nc <= 2 ^ 25
  /\ 2 ^ 45 + 112 <= sp <= 2 ^ 47
  /\ wr_at asegs m (sp - 112) 112
  /\ (v + 24 <= (sp - 112) \/ (sp - 112) + 224 <= v)
  /\ 0 <= b <= 1
  /\ 0 <= cap <= 1
  /\ 4 <= k <= 7
  /\ src mod 8 = 0
  /\ shk m (bn + (4 * cap)) 4
  /\ sh0 m v
  /\ sh0 m (v + 8)
  /\ sh0 m (v + 16)
  /\ sh0 m (sp + 8)
  /\ 1048576 <= bn
  /\ bn + 4 * nc < 2 ^ 47
  /\ 2 ^ 45 + 112 <= sp
  /\ sp + 112 <= 2 ^ 47
  /\ 0 <= src
  /\ src + 4 <= 2 ^ 47
  /\ (src + 4 <= sp \/ sp + 112 <= src)
  /\ 0 <= x < 2 ^ 32
  /\ (v + 24 <= sp - 112 \/ sp + 112 <= v)
  /\ (v + 24 <= 2147446784 \/ 17594333495296 <= v)
  /\ (sp + 112 <= 2147446784 \/ 17594333495296 <= sp - 112)
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 7241728 <= bn
  /\ (bn + 4 * nc <= 2147446784 \/ 17594333495296 <= bn)
  /\ (v + 24 <= bn + 4 * cap \/ bn + 4 * cap + 4 <= v)
  /\ b = 0
  /\ cap = 0
  /\ b mod 4 = 0
  /\ bn + 4 * nc <= sp - 112.

Definition v32_B3bk (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (bn sp v src cap b x nc k : Z),
    v32_B3bk_pre R m bn sp v src cap b x nc k ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 200)) fc None m (seg_rom asegs)) (MS R' F (wz AASAN_MEMCPY) fc None M' (seg_rom asegs))
      /\ munch [((sp - 104), (sp + 32)); ((bn + (4 * cap)), (bn + (4 * cap) + 4))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sp - 104) 8 954568
      /\ fldA M' (sp - 96) 8 sp
      /\ fldA M' (sp - 88) 8 956276
      /\ fldw asegs M' (sp - 80) 8 (getr R 24)
      /\ fldA M' (sp - 72) 8 v
      /\ fldA M' (sp - 64) 8 nc
      /\ fldA M' (sp - 56) 8 (4 * cap)
      /\ fldA M' (sp - 48) 8 ASHADOW_BASE
      /\ fldA M' (sp - 40) 8 (sh (v + 8))
      /\ fldA M' (sp - 32) 8 (bn + (4 * nc))
      /\ fldA M' (sp - 24) 8 src
      /\ fldA M' (sp - 16) 8 (v + 8)
      /\ fldA M' (sp - 8) 8 (E + 404)
      /\ fldA M' (sp + 16) 8 ((bn + (4 * cap)) + 4)
      /\ fldA M' (bn + (4 * cap)) 4 x
      /\ fldA M' (sp + 24) 8 (bn + (4 * nc))
      /\ fldA M' (sp + 8) 8 (bn + (4 * cap))
      /\ fldA M' sp 8 bn
      /\ getr R' 1 = wz 956436
      /\ getr R' 2 = wz (sp - 80)
      /\ getr R' 8 = wz sp
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz (bn + ((4 * cap) + ((-4) * ((4 * cap) / 4))))
      /\ getr R' 11 = wz b
      /\ getr R' 12 = wz (4 * cap)
      /\ getr R' 13 = wz ((-4) * ((4 * cap) / 4))
      /\ getr R' 16 = wz ((v + 16) / 8)
      /\ getr R' 18 = wz (v + 8)
      /\ getr R' 19 = wz (sp + 8)
      /\ getr R' 20 = wz (bn + ((4 * cap) + ((-4) * ((4 * cap) / 4))))
      /\ getr R' 21 = wz ASHADOW_BASE
      /\ getr R' 22 = wz (sh (v + 8))
      /\ getr R' 23 = wz (sh (sp + 8))
      /\ getr R' 24 = wz (sh v)
      /\ (forall r, In r [3; 4; 5; 6; 7; 17; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma v32_B3bk_f871c : v32_B3bk (v4_entry V32_SLOW_CREF).
Proof.
  intros R F fc m bn sp v src cap b x nc k P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54 & P55 & P56). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32.b3bk_E R bn sp v src cap b x nc k) LbB_V4W32.b3bk_sr R) by (unfold LbB_V4W32.b3bk_E, LbB_V4W32.b3bk_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32.b3bk_E R bn sp v src cap b x nc k) m LbB_V4W32.b3bk_A_knF) by (unfold LbB_V4W32.b3bk_E; knowB).
  destruct (LbB_V4W32.b3bk_A_run fx R m (seg_rom asegs) bn sp v src cap b x nc k ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32.b3bk_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32.b3bk_E R bn sp v src cap b x nc k) in *. unfold LbB_V4W32.b3bk_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
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
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 17; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma v32_B3bk_f898c : v32_B3bk (v4_entry V32_SLOW_RREF).
Proof.
  intros R F fc m bn sp v src cap b x nc k P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54 & P55 & P56). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32R.b3bk_E R bn sp v src cap b x nc k) LbB_V4W32R.b3bk_sr R) by (unfold LbB_V4W32R.b3bk_E, LbB_V4W32R.b3bk_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32R.b3bk_E R bn sp v src cap b x nc k) m LbB_V4W32R.b3bk_A_knF) by (unfold LbB_V4W32R.b3bk_E; knowB).
  destruct (LbB_V4W32R.b3bk_A_run fx R m (seg_rom asegs) bn sp v src cap b x nc k ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32R.b3bk_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32R.b3bk_E R bn sp v src cap b x nc k) in *. unfold LbB_V4W32R.b3bk_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
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
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 17; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition v32_B5_pre (R : bvmap 5 word) (m : mem) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z) : Prop :=
  getr R 2 = wz (sb - 96)
  /\ getr R 8 = wz sb
  /\ getr R 9 = wz v
  /\ getr R 21 = wz ASHADOW_BASE
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (4 * cap))
  /\ fldA m (v + 16) 8 (b + (4 * cap))
  /\ fldA m sb 8 bn
  /\ fldA m (sb + 8) 8 (bn + (4 * cap))
  /\ fldA m (sb + 16) 8 ((bn + (4 * cap)) + 4)
  /\ fldA m (sb + 24) 8 (bn + (4 * nc))
  /\ 2 ^ 45 + 96 <= sb <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= b <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 24
  /\ 1048576 <= bn <= 2 ^ 47
  /\ 1 <= nc <= 2 ^ 25
  /\ bn mod 16 = 0
  /\ b mod 4 = 0
  /\ wr_at asegs m (sb - 96) 96
  /\ (v + 24 <= (sb - 96) \/ (sb - 96) + 136 <= v)
  /\ wr_at asegs m v 24
  /\ wr_at asegs m sb 32
  /\ fldA m (sb - 96) 8 sb
  /\ fldA m (sb - 88) 8 956276
  /\ fldA m (sb - 80) 8 hs0
  /\ fldA m (sb - 72) 8 hs1
  /\ fldA m (sb - 64) 8 hs2
  /\ fldA m (sb - 56) 8 hs3
  /\ fldA m (sb - 48) 8 hs4
  /\ fldA m (sb - 40) 8 hs5
  /\ fldA m (sb - 32) 8 hs6
  /\ fldA m (sb - 24) 8 hs7
  /\ fldA m (sb - 16) 8 hs8
  /\ fldA m (sb - 8) 8 hs9
  /\ sh0 m (sb + 8)
  /\ sh0 m (v + 8)
  /\ sh0 m v
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 2 ^ 45 + 96 <= sb
  /\ sb + 40 <= 2 ^ 47
  /\ (v + 24 <= sb - 96 \/ sb + 40 <= v)
  /\ 0 <= b
  /\ b + 4 * cap < 2 ^ 47
  /\ 1048576 <= bn
  /\ bn + 4 * nc < 2 ^ 47
  /\ cap < nc <= 2 ^ 25
  /\ (v + 24 <= 2147446784 \/ 17594333495296 <= v)
  /\ (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96).

Definition v32_B5 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z),
    v32_B5_pre R m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz 954568) fc None m (seg_rom asegs)) (MS R' F (wz AASAN_MEMCPY) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz 956436
      /\ getr R' 2 = wz (sb - 80)
      /\ getr R' 8 = wz sb
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz ((4 * cap) + (bn + ((-4) * ((4 * cap) / 4))))
      /\ getr R' 11 = wz b
      /\ getr R' 12 = wz (4 * cap)
      /\ getr R' 13 = wz ((-4) * ((4 * cap) / 4))
      /\ getr R' 18 = wz (v + 8)
      /\ getr R' 19 = wz (sb + 8)
      /\ getr R' 20 = wz ((4 * cap) + (bn + ((-4) * ((4 * cap) / 4))))
      /\ getr R' 21 = wz ASHADOW_BASE
      /\ getr R' 22 = wz (sh (v + 8))
      /\ getr R' 23 = wz (sh (sb + 8))
      /\ getr R' 24 = wz (sh v)
      /\ (forall r, In r [3; 4; 5; 6; 7; 15; 16; 17; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma v32_B5_f871c : v32_B5 (v4_entry V32_SLOW_CREF).
Proof.
  intros R F fc m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32.b5_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) LbB_V4W32.b5_sr R) by (unfold LbB_V4W32.b5_E, LbB_V4W32.b5_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32.b5_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m LbB_V4W32.b5_A_knF) by (unfold LbB_V4W32.b5_E; knowB).
  destruct (LbB_V4W32.b5_A_run fx R m (seg_rom asegs) v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32.b5_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32.b5_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) in *. unfold LbB_V4W32.b5_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 15; 16; 17; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma v32_B5_f898c : v32_B5 (v4_entry V32_SLOW_RREF).
Proof.
  intros R F fc m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32R.b5_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) LbB_V4W32R.b5_sr R) by (unfold LbB_V4W32R.b5_E, LbB_V4W32R.b5_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32R.b5_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m LbB_V4W32R.b5_A_knF) by (unfold LbB_V4W32R.b5_E; knowB).
  destruct (LbB_V4W32R.b5_A_run fx R m (seg_rom asegs) v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32R.b5_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32R.b5_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) in *. unfold LbB_V4W32R.b5_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 15; 16; 17; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition v32_B7_pre (R : bvmap 5 word) (m : mem) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z) : Prop :=
  getr R 2 = wz (sb - 80)
  /\ getr R 8 = wz sb
  /\ getr R 9 = wz v
  /\ getr R 18 = wz (v + 8)
  /\ getr R 19 = wz (sb + 8)
  /\ getr R 20 = wz bn
  /\ getr R 21 = wz ASHADOW_BASE
  /\ getr R 22 = wz (sh (v + 8))
  /\ getr R 23 = wz (sh (sb + 8))
  /\ getr R 24 = wz (sh v)
  /\ ACONST m
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (4 * cap))
  /\ fldA m (v + 16) 8 (b + (4 * cap))
  /\ fldA m sb 8 bn
  /\ fldA m (sb + 8) 8 (bn + (4 * cap))
  /\ fldA m (sb + 16) 8 ((bn + (4 * cap)) + 4)
  /\ fldA m (sb + 24) 8 (bn + (4 * nc))
  /\ 2 ^ 45 + 80 <= sb <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= b <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 24
  /\ 1048576 <= bn <= 2 ^ 47
  /\ 1 <= nc <= 2 ^ 25
  /\ bn mod 16 = 0
  /\ b mod 4 = 0
  /\ wr_at asegs m (sb - 80) 80
  /\ (v + 24 <= (sb - 80) \/ (sb - 80) + 120 <= v)
  /\ wr_at asegs m v 24
  /\ wr_at asegs m sb 32
  /\ fldA m (sb - 80) 8 hs0
  /\ fldA m (sb - 72) 8 hs1
  /\ fldA m (sb - 64) 8 hs2
  /\ fldA m (sb - 56) 8 hs3
  /\ fldA m (sb - 48) 8 hs4
  /\ fldA m (sb - 40) 8 hs5
  /\ fldA m (sb - 32) 8 hs6
  /\ fldA m (sb - 24) 8 hs7
  /\ fldA m (sb - 16) 8 hs8
  /\ fldA m (sb - 8) 8 hs9
  /\ sh0 m (sb + 8)
  /\ sh0 m v
  /\ sh0 m (v + 8)
  /\ sh0 m (sb + 16)
  /\ sh0 m (v + 16)
  /\ sh0 m (sb + 24)
  /\ sh0 m sb
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 2 ^ 45 + 80 <= sb
  /\ sb + 40 <= 2 ^ 47
  /\ (v + 24 <= sb - 80 \/ sb + 40 <= v)
  /\ 0 <= b
  /\ b + 4 * cap < 2 ^ 47
  /\ 1048576 <= bn
  /\ bn + 4 * nc < 2 ^ 47
  /\ cap < nc <= 2 ^ 25
  /\ (v + 24 <= 2147446784 \/ 17594333495296 <= v)
  /\ (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 80)
  /\ 7241728 <= v.

Definition v32_B7 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z),
    v32_B7_pre R m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz 956436) fc None m (seg_rom asegs)) (MS R' F (wz AANNOTATE_CC) fc None M' (seg_rom asegs))
      /\ munch [((sb - 24), (sb + 32)); (v, (v + 24))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sb - 24) 8 958128
      /\ fldA M' (sb - 16) 8 hs8
      /\ fldA M' (sb - 8) 8 hs9
      /\ fldA M' sb 8 b
      /\ fldA M' (sb + 24) 8 (b + (4 * cap))
      /\ fldA M' (v + 16) 8 (bn + (4 * nc))
      /\ fldA M' (sb + 16) 8 b
      /\ fldA M' (v + 8) 8 ((bn + (4 * cap)) + 4)
      /\ fldA M' (sb + 8) 8 b
      /\ fldA M' v 8 bn
      /\ getr R' 1 = wz 958128
      /\ getr R' 2 = wz (sb - 16)
      /\ getr R' 8 = wz hs8
      /\ getr R' 9 = wz hs7
      /\ getr R' 10 = wz bn
      /\ getr R' 11 = wz (bn + (4 * nc))
      /\ getr R' 12 = wz (bn + (4 * nc))
      /\ getr R' 13 = wz (bn + (4 * (((4 * cap) + 4) / 4)))
      /\ getr R' 14 = wz 1
      /\ getr R' 15 = wz 0
      /\ getr R' 16 = wz 0
      /\ getr R' 18 = wz hs6
      /\ getr R' 19 = wz hs5
      /\ getr R' 20 = wz hs4
      /\ getr R' 21 = wz hs3
      /\ getr R' 22 = wz hs2
      /\ getr R' 23 = wz hs1
      /\ getr R' 24 = wz hs0
      /\ (forall r, In r [3; 4; 5; 6; 7; 17; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma v32_B7_f871c : v32_B7 (v4_entry V32_SLOW_CREF).
Proof.
  intros R F fc m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54 & P55 & P56 & P57 & P58 & P59). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32.b7_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) LbB_V4W32.b7_sr R) by (unfold LbB_V4W32.b7_E, LbB_V4W32.b7_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32.b7_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m LbB_V4W32.b7_A_knF) by (unfold LbB_V4W32.b7_E; knowB).
  destruct (LbB_V4W32.b7_A_run fx R m (seg_rom asegs) v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32.b7_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32.b7_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) in *. unfold LbB_V4W32.b7_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 1; 0; 1; 0; 1; 1; 0]%nat|].
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
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (15%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 17; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma v32_B7_f898c : v32_B7 (v4_entry V32_SLOW_RREF).
Proof.
  intros R F fc m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54 & P55 & P56 & P57 & P58 & P59). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32R.b7_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) LbB_V4W32R.b7_sr R) by (unfold LbB_V4W32R.b7_E, LbB_V4W32R.b7_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32R.b7_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m LbB_V4W32R.b7_A_knF) by (unfold LbB_V4W32R.b7_E; knowB).
  destruct (LbB_V4W32R.b7_A_run fx R m (seg_rom asegs) v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32R.b7_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32R.b7_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) in *. unfold LbB_V4W32R.b7_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 1; 0; 1; 0; 1; 1; 0]%nat|].
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
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (15%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 17; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition v32_B9_pre (E : Z) (R : bvmap 5 word) (m : mem) (bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 : Z) : Prop :=
  getr R 2 = wz (sp - 16)
  /\ getr R 8 = wz (v + 8)
  /\ getr R 9 = wz src
  /\ getr R 18 = wz (bn + (4 * nc))
  /\ getr R 19 = wz (sh (v + 8))
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (4 * cap)
  /\ getr R 22 = wz nc
  /\ getr R 23 = wz v
  /\ fldA m v 8 bn
  /\ fldA m (v + 8) 8 ((bn + (4 * cap)) + 4)
  /\ fldA m (v + 16) 8 (bn + (4 * nc))
  /\ fldA m sp 8 b
  /\ fldA m (sp + 8) 8 b
  /\ fldA m (sp + 16) 8 b
  /\ fldA m (sp + 24) 8 (b + (4 * cap))
  /\ fldA m (sp + 32) 8 v
  /\ fldA m (sp + 104) 8 sv1
  /\ fldA m (sp + 96) 8 sv8
  /\ fldA m (sp + 88) 8 sv9
  /\ fldA m (sp + 80) 8 sv18
  /\ fldA m (sp + 72) 8 sv19
  /\ fldA m (sp + 64) 8 sv20
  /\ fldA m (sp + 56) 8 sv21
  /\ fldA m (sp + 48) 8 sv22
  /\ fldA m (sp + 40) 8 sv23
  /\ 2 ^ 45 <= sp <= 2 ^ 47
  /\ 1048576 <= bn <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 24
  /\ 1 <= nc <= 2 ^ 25
  /\ 0 <= b <= 2 ^ 47
  /\ wr_at asegs m sp 112
  /\ fldA m (sp - 8) 8 (E + 404)
  /\ fldA m (sp - 16) 8 (v + 8)
  /\ sh0 m (v + 8)
  /\ 1048576 <= bn
  /\ bn + 4 * nc < 2 ^ 47
  /\ 2 ^ 45 <= sp
  /\ sp + 112 <= 2 ^ 47
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ cap < nc <= 2 ^ 25
  /\ 0 <= b
  /\ b + 4 * cap < 2 ^ 47.

Definition v32_B9D (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 : Z),
    v32_B9_pre E R m bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 -> (b <> 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz 958128) fc None m (seg_rom asegs)) (MS R' F (wz AOPDEL2) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz (E + 484)
      /\ getr R' 2 = wz sp
      /\ getr R' 8 = wz ((bn + (4 * cap)) + 4)
      /\ getr R' 9 = wz src
      /\ getr R' 10 = wz b
      /\ getr R' 11 = wz (4 * cap)
      /\ getr R' 18 = wz (bn + (4 * nc))
      /\ getr R' 19 = wz (sh (v + 8))
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (4 * cap)
      /\ getr R' 22 = wz nc
      /\ getr R' 23 = wz v
      /\ (forall r, In r [3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma v32_B9D_f871c : v32_B9D (v4_entry V32_SLOW_CREF).
Proof.
  intros R F fc m bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32.b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) LbB_V4W32.b9_sr R) by (unfold LbB_V4W32.b9_E, LbB_V4W32.b9_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32.b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) m LbB_V4W32.b9_D_knF) by (unfold LbB_V4W32.b9_E; knowB).
  destruct (LbB_V4W32.b9_D_run fx R m (seg_rom asegs) bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32.b9_D_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32.b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) in *. unfold LbB_V4W32.b9_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma v32_B9D_f898c : v32_B9D (v4_entry V32_SLOW_RREF).
Proof.
  intros R F fc m bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32R.b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) LbB_V4W32R.b9_sr R) by (unfold LbB_V4W32R.b9_E, LbB_V4W32R.b9_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32R.b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) m LbB_V4W32R.b9_D_knF) by (unfold LbB_V4W32R.b9_E; knowB).
  destruct (LbB_V4W32R.b9_D_run fx R m (seg_rom asegs) bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32R.b9_D_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32R.b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) in *. unfold LbB_V4W32R.b9_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition v32_B9N (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 : Z),
    v32_B9_pre E R m bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 -> (b = 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz 958128) fc None m (seg_rom asegs)) (MS R' F (wz (E + 484)) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz (E + 404)
      /\ getr R' 2 = wz sp
      /\ getr R' 8 = wz ((bn + (4 * cap)) + 4)
      /\ getr R' 9 = wz src
      /\ getr R' 10 = wz b
      /\ getr R' 11 = wz b
      /\ getr R' 18 = wz (bn + (4 * nc))
      /\ getr R' 19 = wz (sh (v + 8))
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (4 * cap)
      /\ getr R' 22 = wz nc
      /\ getr R' 23 = wz v
      /\ (forall r, In r [3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma v32_B9N_f871c : v32_B9N (v4_entry V32_SLOW_CREF).
Proof.
  intros R F fc m bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32.b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) LbB_V4W32.b9_sr R) by (unfold LbB_V4W32.b9_E, LbB_V4W32.b9_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32.b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) m LbB_V4W32.b9_N_knF) by (unfold LbB_V4W32.b9_E; knowB).
  destruct (LbB_V4W32.b9_N_run fx R m (seg_rom asegs) bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32.b9_N_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32.b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) in *. unfold LbB_V4W32.b9_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma v32_B9N_f898c : v32_B9N (v4_entry V32_SLOW_RREF).
Proof.
  intros R F fc m bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32R.b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) LbB_V4W32R.b9_sr R) by (unfold LbB_V4W32R.b9_E, LbB_V4W32R.b9_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32R.b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) m LbB_V4W32R.b9_N_knF) by (unfold LbB_V4W32R.b9_E; knowB).
  destruct (LbB_V4W32R.b9_N_run fx R m (seg_rom asegs) bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32R.b9_N_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32R.b9_E R bn sp v src cap b nc sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) in *. unfold LbB_V4W32R.b9_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition v32_B11_pre (R : bvmap 5 word) (m : mem) (bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 8 = wz ((bn + (4 * cap)) + 4)
  /\ fldA m (sp + 104) 8 sv1
  /\ fldA m (sp + 96) 8 sv8
  /\ fldA m (sp + 88) 8 sv9
  /\ fldA m (sp + 80) 8 sv18
  /\ fldA m (sp + 72) 8 sv19
  /\ fldA m (sp + 64) 8 sv20
  /\ fldA m (sp + 56) 8 sv21
  /\ fldA m (sp + 48) 8 sv22
  /\ fldA m (sp + 40) 8 sv23
  /\ 2 ^ 45 <= sp <= 2 ^ 47
  /\ 1048576 <= bn <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 24
  /\ 1048576 <= bn
  /\ bn + 4 * cap + 4 < 2 ^ 47
  /\ 2 ^ 45 <= sp
  /\ sp + 112 <= 2 ^ 47.

Definition v32_B11 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 : Z),
    v32_B11_pre R m bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 484)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 528)) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz sv1
      /\ getr R' 2 = wz (sp + 112)
      /\ getr R' 8 = wz sv8
      /\ getr R' 9 = wz sv9
      /\ getr R' 10 = wz ((bn + (4 * cap)) + 4)
      /\ getr R' 18 = wz sv18
      /\ getr R' 19 = wz sv19
      /\ getr R' 20 = wz sv20
      /\ getr R' 21 = wz sv21
      /\ getr R' 22 = wz sv22
      /\ getr R' 23 = wz sv23
      /\ (forall r, In r [3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma v32_B11_f871c : v32_B11 (v4_entry V32_SLOW_CREF).
Proof.
  intros R F fc m bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32.b11_E R bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) LbB_V4W32.b11_sr R) by (unfold LbB_V4W32.b11_E, LbB_V4W32.b11_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32.b11_E R bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) m LbB_V4W32.b11_A_knF) by (unfold LbB_V4W32.b11_E; knowB).
  destruct (LbB_V4W32.b11_A_run fx R m (seg_rom asegs) bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32.b11_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32.b11_E R bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) in *. unfold LbB_V4W32.b11_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma v32_B11_f898c : v32_B11 (v4_entry V32_SLOW_RREF).
Proof.
  intros R F fc m bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_V4W32R.b11_E R bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) LbB_V4W32R.b11_sr R) by (unfold LbB_V4W32R.b11_E, LbB_V4W32R.b11_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_V4W32R.b11_E R bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) m LbB_V4W32R.b11_A_knF) by (unfold LbB_V4W32R.b11_E; knowB).
  destruct (LbB_V4W32R.b11_A_run fx R m (seg_rom asegs) bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_V4W32R.b11_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_V4W32R.b11_E R bn sp v cap sv1 sv8 sv9 sv18 sv19 sv20 sv21 sv22 sv23) in *. unfold LbB_V4W32R.b11_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.
