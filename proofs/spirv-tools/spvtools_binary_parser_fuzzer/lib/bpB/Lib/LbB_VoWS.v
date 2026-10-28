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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_VoW.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition vop_B1_pre (R : bvmap 5 word) (m : mem) (v src spz b cap : Z) : Prop :=
  getr R 10 = wz v
  /\ getr R 11 = wz src
  /\ getr R 2 = wz spz
  /\ ACONST m
  /\ mem_inv asegs m
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (20 * cap))
  /\ fldA m (v + 16) 8 (b + (20 * cap))
  /\ wr_at asegs m (spz - 96) 96
  /\ 2 ^ 45 + 96 <= spz <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= b <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 24
  /\ (v + 24 <= (spz - 96) \/ (spz - 96) + 96 <= v)
  /\ sh0 m (v + 8)
  /\ sh0 m v
  /\ sh0 m (v + 16)
  /\ 0 <= b
  /\ b + 20 * cap < 2 ^ 47
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47.

Definition vop_B1T (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v src spz b cap : Z),
    vop_B1_pre R m v src spz b cap -> (2 <= cap) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz E) fc None m (seg_rom asegs)) (MS R' F (wz AOPNEW) fc None M' (seg_rom asegs))
      /\ munch [((spz - 64), spz)] m M'
      /\ wmono asegs m M'
      /\ fldA M' (spz - 64) 8 v
      /\ fldw asegs M' (spz - 56) 8 (getr R 21)
      /\ fldw asegs M' (spz - 48) 8 (getr R 20)
      /\ fldw asegs M' (spz - 40) 8 (getr R 19)
      /\ fldw asegs M' (spz - 32) 8 (getr R 18)
      /\ fldw asegs M' (spz - 24) 8 (getr R 9)
      /\ fldw asegs M' (spz - 16) 8 (getr R 8)
      /\ fldw asegs M' (spz - 8) 8 (getr R 1)
      /\ getr R' 1 = wz (E + 248)
      /\ getr R' 2 = wz (spz - 96)
      /\ getr R' 8 = wz (v + 8)
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz (8 * ((20 * cap) / 4))
      /\ getr R' 11 = wz src
      /\ getr R' 12 = wz 922337203685477581
      /\ getr R' 13 = wz 461168601842738790
      /\ getr R' 14 = wz 14757395259826634752
      /\ getr R' 15 = wz ((1 * ((20 * cap) / 20)) + 1)
      /\ getr R' 16 = wz ((v + 16) / 8)
      /\ getr R' 18 = wz (sh (v + 8))
      /\ getr R' 19 = wz (2 * ((20 * cap) / 20))
      /\ getr R' 20 = wz (20 * cap)
      /\ getr R' 21 = wz src
      /\ (forall r, In r [3; 4; 5; 6; 7; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma vop_B1T_fc400 : vop_B1T (VOPND_SLOW_ENTRY).
Proof.
  intros R F fc m v src spz b cap P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_VoW.vp1_E R v src spz b cap) LbB_VoW.vp1_sr R) by (unfold LbB_VoW.vp1_E, LbB_VoW.vp1_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_VoW.vp1_E R v src spz b cap) m LbB_VoW.vp1_T_knF) by (unfold LbB_VoW.vp1_E; knowB).
  destruct (LbB_VoW.vp1_T_run fx R m (seg_rom asegs) v src spz b cap ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_VoW.vp1_T_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_VoW.vp1_E R v src spz b cap) in *. unfold LbB_VoW.vp1_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fldw_postB_at 1%nat|].
  split; [fldw_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
  split; [fldw_postB_at 4%nat|].
  split; [fldw_postB_at 5%nat|].
  split; [fldw_postB_at 6%nat|].
  split; [fldw_postB_at 7%nat|].
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
  keptB HR HR' ([3; 4; 5; 6; 7; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition vop_B1F (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v src spz b cap : Z),
    vop_B1_pre R m v src spz b cap -> (cap <= 1) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz E) fc None m (seg_rom asegs)) (MS R' F (wz AOPNEW) fc None M' (seg_rom asegs))
      /\ munch [((spz - 64), spz)] m M'
      /\ wmono asegs m M'
      /\ fldA M' (spz - 64) 8 v
      /\ fldw asegs M' (spz - 56) 8 (getr R 21)
      /\ fldw asegs M' (spz - 48) 8 (getr R 20)
      /\ fldw asegs M' (spz - 40) 8 (getr R 19)
      /\ fldw asegs M' (spz - 32) 8 (getr R 18)
      /\ fldw asegs M' (spz - 24) 8 (getr R 9)
      /\ fldw asegs M' (spz - 16) 8 (getr R 8)
      /\ fldw asegs M' (spz - 8) 8 (getr R 1)
      /\ getr R' 1 = wz (E + 248)
      /\ getr R' 2 = wz (spz - 96)
      /\ getr R' 8 = wz (v + 8)
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz ((4 * ((20 * cap) / 4)) + 20)
      /\ getr R' 11 = wz src
      /\ getr R' 12 = wz 922337203685477581
      /\ getr R' 13 = wz 461168601842738790
      /\ getr R' 14 = wz 14757395259826634752
      /\ getr R' 15 = wz ((1 * ((20 * cap) / 20)) + 1)
      /\ getr R' 16 = wz ((v + 16) / 8)
      /\ getr R' 18 = wz (sh (v + 8))
      /\ getr R' 19 = wz ((1 * ((20 * cap) / 20)) + 1)
      /\ getr R' 20 = wz (20 * cap)
      /\ getr R' 21 = wz src
      /\ (forall r, In r [3; 4; 5; 6; 7; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma vop_B1F_fc400 : vop_B1F (VOPND_SLOW_ENTRY).
Proof.
  intros R F fc m v src spz b cap P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_VoW.vp1_E R v src spz b cap) LbB_VoW.vp1_sr R) by (unfold LbB_VoW.vp1_E, LbB_VoW.vp1_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_VoW.vp1_E R v src spz b cap) m LbB_VoW.vp1_F_knF) by (unfold LbB_VoW.vp1_E; knowB).
  destruct (LbB_VoW.vp1_F_run fx R m (seg_rom asegs) v src spz b cap ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_VoW.vp1_F_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_VoW.vp1_E R v src spz b cap) in *. unfold LbB_VoW.vp1_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fldw_postB_at 1%nat|].
  split; [fldw_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
  split; [fldw_postB_at 4%nat|].
  split; [fldw_postB_at 5%nat|].
  split; [fldw_postB_at 6%nat|].
  split; [fldw_postB_at 7%nat|].
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
  keptB HR HR' ([3; 4; 5; 6; 7; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition vop_B3_pre (R : bvmap 5 word) (m : mem) (bn sp v src cap b nc : Z) : Prop :=
  getr R 10 = wz bn
  /\ getr R 21 = wz src
  /\ getr R 2 = wz sp
  /\ getr R 8 = wz (v + 8)
  /\ getr R 9 = wz v
  /\ getr R 18 = wz (sh (v + 8))
  /\ getr R 19 = wz nc
  /\ getr R 20 = wz (20 * cap)
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (20 * cap))
  /\ fldA m (v + 16) 8 (b + (20 * cap))
  /\ fldA m (sp + 32) 8 v
  /\ 2 ^ 45 <= sp <= 2 ^ 47
  /\ 1048576 <= bn <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= src <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 24
  /\ 1 <= nc <= 2 ^ 25
  /\ 0 <= b <= 2 ^ 47
  /\ bn mod 16 = 0
  /\ wr_at asegs m sp 96
  /\ 1048576 <= bn
  /\ bn + 20 * nc < 2 ^ 47
  /\ 2 ^ 45 <= sp
  /\ sp + 96 <= 2 ^ 47
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 0 <= src
  /\ src + 20 <= 2 ^ 47
  /\ (src + 20 <= sp \/ sp + 96 <= src)
  /\ cap < nc <= 2 ^ 25
  /\ 0 <= b
  /\ b + 20 * cap < 2 ^ 47.

Definition vop_B3 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (bn sp v src cap b nc : Z),
    vop_B3_pre R m bn sp v src cap b nc ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 248)) fc None m (seg_rom asegs)) (MS R' F (wz AASAN_MEMCPY) fc None M' (seg_rom asegs))
      /\ munch [(sp, (sp + 32))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sp + 24) 8 (bn + (20 * nc))
      /\ fldA M' (sp + 16) 8 (bn + (20 * cap))
      /\ fldA M' (sp + 8) 8 (bn + (20 * cap))
      /\ fldA M' sp 8 bn
      /\ getr R' 1 = wz (E + 392)
      /\ getr R' 2 = wz sp
      /\ getr R' 8 = wz (v + 8)
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz (bn + (20 * cap))
      /\ getr R' 11 = wz src
      /\ getr R' 12 = wz 20
      /\ getr R' 13 = wz (bn + (20 * cap))
      /\ getr R' 14 = wz 0
      /\ getr R' 15 = wz 0
      /\ getr R' 16 = wz (bn + (20 * nc))
      /\ getr R' 17 = wz 0
      /\ getr R' 18 = wz (sh (v + 8))
      /\ getr R' 19 = wz nc
      /\ getr R' 20 = wz (20 * cap)
      /\ getr R' 21 = wz src
      /\ (forall r, In r [3; 4; 5; 6; 7; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma vop_B3_fc400 : vop_B3 (VOPND_SLOW_ENTRY).
Proof.
  intros R F fc m bn sp v src cap b nc P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_VoW.vp3_E R bn sp v src cap b nc) LbB_VoW.vp3_sr R) by (unfold LbB_VoW.vp3_E, LbB_VoW.vp3_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_VoW.vp3_E R bn sp v src cap b nc) m LbB_VoW.vp3_A_knF) by (unfold LbB_VoW.vp3_E; knowB).
  destruct (LbB_VoW.vp3_A_run fx R m (seg_rom asegs) bn sp v src cap b nc ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_VoW.vp3_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_VoW.vp3_E R bn sp v src cap b nc) in *. unfold LbB_VoW.vp3_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fld_postB_at 3%nat|].
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
  split; [rrwB HR' (17%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition vop_B4_pre (R : bvmap 5 word) (m : mem) (bn sp v src cap b nc : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 8 = wz (v + 8)
  /\ getr R 9 = wz v
  /\ getr R 18 = wz (sh (v + 8))
  /\ getr R 19 = wz nc
  /\ getr R 20 = wz (20 * cap)
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (20 * cap))
  /\ fldA m (v + 16) 8 (b + (20 * cap))
  /\ fldA m sp 8 bn
  /\ fldA m (sp + 8) 8 (bn + (20 * cap))
  /\ fldA m (sp + 16) 8 (bn + (20 * cap))
  /\ fldA m (sp + 24) 8 (bn + (20 * nc))
  /\ fldA m (sp + 32) 8 v
  /\ 2 ^ 45 <= sp <= 2 ^ 47
  /\ 1048576 <= bn <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= src <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 24
  /\ 1 <= nc <= 2 ^ 25
  /\ 0 <= b <= 2 ^ 47
  /\ bn mod 16 = 0
  /\ wr_at asegs m sp 96
  /\ 1048576 <= bn
  /\ bn + 20 * nc < 2 ^ 47
  /\ 2 ^ 45 <= sp
  /\ sp + 96 <= 2 ^ 47
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 0 <= src
  /\ src + 20 <= 2 ^ 47
  /\ (src + 20 <= sp \/ sp + 96 <= src)
  /\ cap < nc <= 2 ^ 25
  /\ 0 <= b
  /\ b + 20 * cap < 2 ^ 47.

Definition vop_B4 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (bn sp v src cap b nc : Z),
    vop_B4_pre R m bn sp v src cap b nc ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 392)) fc None m (seg_rom asegs)) (MS R' F (wz 968952) fc None M' (seg_rom asegs))
      /\ munch [((sp + 16), (sp + 24))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sp + 16) 8 ((bn + (20 * cap)) + 20)
      /\ getr R' 1 = wz (E + 428)
      /\ getr R' 2 = wz sp
      /\ getr R' 8 = wz (v + 8)
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz v
      /\ getr R' 11 = wz sp
      /\ getr R' 18 = wz (sh (v + 8))
      /\ getr R' 19 = wz nc
      /\ getr R' 20 = wz (20 * cap)
      /\ (forall r, In r [3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma vop_B4_fc400 : vop_B4 (VOPND_SLOW_ENTRY).
Proof.
  intros R F fc m bn sp v src cap b nc P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_VoW.vp4_E R bn sp v src cap b nc) LbB_VoW.vp4_sr R) by (unfold LbB_VoW.vp4_E, LbB_VoW.vp4_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_VoW.vp4_E R bn sp v src cap b nc) m LbB_VoW.vp4_A_knF) by (unfold LbB_VoW.vp4_E; knowB).
  destruct (LbB_VoW.vp4_A_run fx R m (seg_rom asegs) bn sp v src cap b nc ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_VoW.vp4_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_VoW.vp4_E R bn sp v src cap b nc) in *. unfold LbB_VoW.vp4_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition vop_B5_pre (R : bvmap 5 word) (m : mem) (bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 8 = wz (v + 8)
  /\ getr R 9 = wz v
  /\ getr R 18 = wz (sh (v + 8))
  /\ getr R 19 = wz nc
  /\ getr R 20 = wz (20 * cap)
  /\ fldA m v 8 bn
  /\ fldA m (v + 8) 8 ((bn + (20 * cap)) + 20)
  /\ fldA m (v + 16) 8 (bn + (20 * nc))
  /\ fldA m sp 8 b
  /\ fldA m (sp + 8) 8 b
  /\ fldA m (sp + 16) 8 b
  /\ fldA m (sp + 24) 8 (b + (20 * cap))
  /\ fldA m (sp + 32) 8 v
  /\ fldA m (sp + 88) 8 pv1
  /\ fldA m (sp + 80) 8 pv8
  /\ fldA m (sp + 72) 8 pv9
  /\ fldA m (sp + 64) 8 pv18
  /\ fldA m (sp + 56) 8 pv19
  /\ fldA m (sp + 48) 8 pv20
  /\ fldA m (sp + 40) 8 pv21
  /\ 2 ^ 45 <= sp <= 2 ^ 47
  /\ 1048576 <= bn <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= src <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 24
  /\ 1 <= nc <= 2 ^ 25
  /\ 0 <= b <= 2 ^ 47
  /\ bn mod 16 = 0
  /\ wr_at asegs m sp 96
  /\ sh0 m (v + 8)
  /\ 1048576 <= bn
  /\ bn + 20 * nc < 2 ^ 47
  /\ 2 ^ 45 <= sp
  /\ sp + 96 <= 2 ^ 47
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 0 <= src
  /\ src + 20 <= 2 ^ 47
  /\ (src + 20 <= sp \/ sp + 96 <= src)
  /\ cap < nc <= 2 ^ 25
  /\ 0 <= b
  /\ b + 20 * cap < 2 ^ 47.

Definition vop_B5D (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 : Z),
    vop_B5_pre R m bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 -> (b <> 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 428)) fc None m (seg_rom asegs)) (MS R' F (wz AOPDEL2) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz (E + 512)
      /\ getr R' 2 = wz sp
      /\ getr R' 8 = wz ((bn + (20 * cap)) + 20)
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz b
      /\ getr R' 11 = wz (20 * cap)
      /\ getr R' 18 = wz (sh (v + 8))
      /\ getr R' 19 = wz nc
      /\ getr R' 20 = wz (20 * cap)
      /\ (forall r, In r [3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma vop_B5D_fc400 : vop_B5D (VOPND_SLOW_ENTRY).
Proof.
  intros R F fc m bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_VoW.vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) LbB_VoW.vp5_sr R) by (unfold LbB_VoW.vp5_E, LbB_VoW.vp5_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_VoW.vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) m LbB_VoW.vp5_D_knF) by (unfold LbB_VoW.vp5_E; knowB).
  destruct (LbB_VoW.vp5_D_run fx R m (seg_rom asegs) bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_VoW.vp5_D_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_VoW.vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) in *. unfold LbB_VoW.vp5_E in Ev.
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
  keptB HR HR' ([3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition vop_B5N (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 : Z),
    vop_B5_pre R m bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 -> (b = 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 428)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 548)) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz pv1
      /\ getr R' 2 = wz (sp + 96)
      /\ getr R' 8 = wz pv8
      /\ getr R' 9 = wz pv9
      /\ getr R' 10 = wz ((bn + (20 * cap)) + 20)
      /\ getr R' 11 = wz b
      /\ getr R' 18 = wz pv18
      /\ getr R' 19 = wz pv19
      /\ getr R' 20 = wz pv20
      /\ getr R' 21 = wz pv21
      /\ (forall r, In r [3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma vop_B5N_fc400 : vop_B5N (VOPND_SLOW_ENTRY).
Proof.
  intros R F fc m bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_VoW.vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) LbB_VoW.vp5_sr R) by (unfold LbB_VoW.vp5_E, LbB_VoW.vp5_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_VoW.vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) m LbB_VoW.vp5_N_knF) by (unfold LbB_VoW.vp5_E; knowB).
  destruct (LbB_VoW.vp5_N_run fx R m (seg_rom asegs) bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_VoW.vp5_N_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_VoW.vp5_E R bn sp v src cap b nc pv1 pv8 pv9 pv18 pv19 pv20 pv21) in *. unfold LbB_VoW.vp5_E in Ev.
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
  keptB HR HR' ([3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition vop_B9_pre (R : bvmap 5 word) (m : mem) (bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21 : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 8 = wz ((bn + (20 * cap)) + 20)
  /\ fldA m (sp + 88) 8 pv1
  /\ fldA m (sp + 80) 8 pv8
  /\ fldA m (sp + 72) 8 pv9
  /\ fldA m (sp + 64) 8 pv18
  /\ fldA m (sp + 56) 8 pv19
  /\ fldA m (sp + 48) 8 pv20
  /\ fldA m (sp + 40) 8 pv21
  /\ 2 ^ 45 <= sp <= 2 ^ 47
  /\ 1048576 <= bn <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 24
  /\ 1048576 <= bn
  /\ bn + 20 * cap + 20 < 2 ^ 47
  /\ 2 ^ 45 <= sp
  /\ sp + 96 <= 2 ^ 47.

Definition vop_B9 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21 : Z),
    vop_B9_pre R m bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 512)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 548)) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz pv1
      /\ getr R' 2 = wz (sp + 96)
      /\ getr R' 8 = wz pv8
      /\ getr R' 9 = wz pv9
      /\ getr R' 10 = wz ((bn + (20 * cap)) + 20)
      /\ getr R' 18 = wz pv18
      /\ getr R' 19 = wz pv19
      /\ getr R' 20 = wz pv20
      /\ getr R' 21 = wz pv21
      /\ (forall r, In r [3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma vop_B9_fc400 : vop_B9 (VOPND_SLOW_ENTRY).
Proof.
  intros R F fc m bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21 P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_VoW.vp9_E R bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21) LbB_VoW.vp9_sr R) by (unfold LbB_VoW.vp9_E, LbB_VoW.vp9_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_VoW.vp9_E R bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21) m LbB_VoW.vp9_A_knF) by (unfold LbB_VoW.vp9_E; knowB).
  destruct (LbB_VoW.vp9_A_run fx R m (seg_rom asegs) bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_VoW.vp9_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_VoW.vp9_E R bn sp cap pv1 pv8 pv9 pv18 pv19 pv20 pv21) in *. unfold LbB_VoW.vp9_E in Ev.
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
  keptB HR HR' ([3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.
