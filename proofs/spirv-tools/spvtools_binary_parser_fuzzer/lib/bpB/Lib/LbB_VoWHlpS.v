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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_VoWHlp.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition voh_Q1_pre (R : bvmap 5 word) (m : mem) (v sb b cap bn nc : Z) : Prop :=
  getr R 10 = wz v
  /\ getr R 11 = wz sb
  /\ getr R 2 = wz sb
  /\ ACONST m
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (20 * cap))
  /\ fldA m (v + 16) 8 (b + (20 * cap))
  /\ fldA m sb 8 bn
  /\ fldA m (sb + 8) 8 (bn + (20 * cap))
  /\ fldA m (sb + 16) 8 ((bn + (20 * cap)) + 20)
  /\ fldA m (sb + 24) 8 (bn + (20 * nc))
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
  /\ sh0 m v
  /\ sh0 m (v + 8)
  /\ sh0 m (v + 16)
  /\ sh0 m (sb + 8)
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 2 ^ 45 + 96 <= sb
  /\ sb + 40 <= 2 ^ 47
  /\ (v + 24 <= sb - 96 \/ sb + 40 <= v)
  /\ 0 <= b
  /\ b + 20 * cap < 2 ^ 47
  /\ 1048576 <= bn
  /\ bn + 20 * nc < 2 ^ 47
  /\ cap < nc <= 2 ^ 25
  /\ (v + 24 <= 2147446784 \/ 17594333495296 <= v)
  /\ (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96).

Definition voh_Q1A (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sb b cap bn nc : Z),
    voh_Q1_pre R m v sb b cap bn nc -> (b <> 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz E) fc None m (seg_rom asegs)) (MS R' F (wz AANNOTATE_CC) fc None M' (seg_rom asegs))
      /\ munch [((sb - 96), sb)] m M'
      /\ wmono asegs m M'
      /\ fldw asegs M' (sb - 96) 8 (getr R 26)
      /\ fldw asegs M' (sb - 88) 8 (getr R 25)
      /\ fldw asegs M' (sb - 80) 8 (getr R 24)
      /\ fldw asegs M' (sb - 72) 8 (getr R 23)
      /\ fldw asegs M' (sb - 64) 8 (getr R 22)
      /\ fldw asegs M' (sb - 56) 8 (getr R 21)
      /\ fldw asegs M' (sb - 48) 8 (getr R 20)
      /\ fldw asegs M' (sb - 40) 8 (getr R 19)
      /\ fldw asegs M' (sb - 32) 8 (getr R 18)
      /\ fldw asegs M' (sb - 24) 8 (getr R 9)
      /\ fldw asegs M' (sb - 16) 8 (getr R 8)
      /\ fldw asegs M' (sb - 8) 8 (getr R 1)
      /\ getr R' 1 = wz (E + 196)
      /\ getr R' 2 = wz (sb - 96)
      /\ getr R' 8 = wz v
      /\ getr R' 9 = wz sb
      /\ getr R' 10 = wz b
      /\ getr R' 11 = wz (b + (20 * cap))
      /\ getr R' 12 = wz (b + (20 * cap))
      /\ getr R' 13 = wz (b + (20 * cap))
      /\ getr R' 18 = wz (v + 8)
      /\ getr R' 19 = wz (v + 16)
      /\ getr R' 22 = wz ASHADOW_BASE
      /\ getr R' 23 = wz (sh v)
      /\ getr R' 24 = wz (sh (v + 16))
      /\ getr R' 25 = wz (sh (v + 8))
      /\ (forall r, In r [3; 4; 5; 6; 7; 15; 16; 17; 20; 21; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma voh_Q1A_ec8f8 : voh_Q1A (0xec8f8).
Proof.
  intros R F fc m v sb b cap bn nc P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_VoWHlp.q1_E R v sb b cap bn nc) LbB_VoWHlp.q1_sr R) by (unfold LbB_VoWHlp.q1_E, LbB_VoWHlp.q1_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_VoWHlp.q1_E R v sb b cap bn nc) m LbB_VoWHlp.q1_A_knF) by (unfold LbB_VoWHlp.q1_E; knowB).
  destruct (LbB_VoWHlp.q1_A_run fx R m (seg_rom asegs) v sb b cap bn nc ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_VoWHlp.q1_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_VoWHlp.q1_E R v sb b cap bn nc) in *. unfold LbB_VoWHlp.q1_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fldw_postB_at 0%nat|].
  split; [fldw_postB_at 1%nat|].
  split; [fldw_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
  split; [fldw_postB_at 4%nat|].
  split; [fldw_postB_at 5%nat|].
  split; [fldw_postB_at 6%nat|].
  split; [fldw_postB_at 7%nat|].
  split; [fldw_postB_at 8%nat|].
  split; [fldw_postB_at 9%nat|].
  split; [fldw_postB_at 10%nat|].
  split; [fldw_postB_at 11%nat|].
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
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 15; 16; 17; 20; 21; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition voh_Q1Z (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sb b cap bn nc : Z),
    voh_Q1_pre R m v sb b cap bn nc -> (b = 0) -> (cap = 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz E) fc None m (seg_rom asegs)) (MS R' F (wz AASAN_MEMCPY) fc None M' (seg_rom asegs))
      /\ munch [((sb - 96), sb)] m M'
      /\ wmono asegs m M'
      /\ fldw asegs M' (sb - 96) 8 (getr R 26)
      /\ fldw asegs M' (sb - 88) 8 (getr R 25)
      /\ fldw asegs M' (sb - 80) 8 (getr R 24)
      /\ fldw asegs M' (sb - 72) 8 (getr R 23)
      /\ fldw asegs M' (sb - 64) 8 (getr R 22)
      /\ fldw asegs M' (sb - 56) 8 (getr R 21)
      /\ fldw asegs M' (sb - 48) 8 (getr R 20)
      /\ fldw asegs M' (sb - 40) 8 (getr R 19)
      /\ fldw asegs M' (sb - 32) 8 (getr R 18)
      /\ fldw asegs M' (sb - 24) 8 (getr R 9)
      /\ fldw asegs M' (sb - 16) 8 (getr R 8)
      /\ fldw asegs M' (sb - 8) 8 (getr R 1)
      /\ getr R' 1 = wz (E + 300)
      /\ getr R' 2 = wz (sb - 96)
      /\ getr R' 8 = wz v
      /\ getr R' 9 = wz sb
      /\ getr R' 10 = wz bn
      /\ getr R' 11 = wz b
      /\ getr R' 12 = wz (20 * cap)
      /\ getr R' 14 = wz 0
      /\ getr R' 18 = wz (v + 8)
      /\ getr R' 19 = wz (v + 16)
      /\ getr R' 20 = wz (sb + 8)
      /\ getr R' 21 = wz bn
      /\ getr R' 22 = wz ASHADOW_BASE
      /\ getr R' 23 = wz (sh v)
      /\ getr R' 24 = wz (sh (v + 16))
      /\ getr R' 25 = wz (sh (v + 8))
      /\ getr R' 26 = wz (sh (sb + 8))
      /\ (forall r, In r [3; 4; 5; 6; 7; 15; 16; 17; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma voh_Q1Z_ec8f8 : voh_Q1Z (0xec8f8).
Proof.
  intros R F fc m v sb b cap bn nc P Q0 Q1.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_VoWHlp.q1_E R v sb b cap bn nc) LbB_VoWHlp.q1_sr R) by (unfold LbB_VoWHlp.q1_E, LbB_VoWHlp.q1_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_VoWHlp.q1_E R v sb b cap bn nc) m LbB_VoWHlp.q1_Z_knF) by (unfold LbB_VoWHlp.q1_E; knowB).
  destruct (LbB_VoWHlp.q1_Z_run fx R m (seg_rom asegs) v sb b cap bn nc ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_VoWHlp.q1_Z_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_VoWHlp.q1_E R v sb b cap bn nc) in *. unfold LbB_VoWHlp.q1_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fldw_postB_at 0%nat|].
  split; [fldw_postB_at 1%nat|].
  split; [fldw_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
  split; [fldw_postB_at 4%nat|].
  split; [fldw_postB_at 5%nat|].
  split; [fldw_postB_at 6%nat|].
  split; [fldw_postB_at 7%nat|].
  split; [fldw_postB_at 8%nat|].
  split; [fldw_postB_at 9%nat|].
  split; [fldw_postB_at 10%nat|].
  split; [fldw_postB_at 11%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  split; [rrwB HR' (26%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 15; 16; 17; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition voh_Q2_pre (R : bvmap 5 word) (m : mem) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z) : Prop :=
  getr R 2 = wz (sb - 96)
  /\ getr R 8 = wz v
  /\ getr R 9 = wz sb
  /\ getr R 18 = wz (v + 8)
  /\ getr R 19 = wz (v + 16)
  /\ getr R 22 = wz ASHADOW_BASE
  /\ getr R 23 = wz (sh v)
  /\ getr R 24 = wz (sh (v + 16))
  /\ getr R 25 = wz (sh (v + 8))
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (20 * cap))
  /\ fldA m (v + 16) 8 (b + (20 * cap))
  /\ fldA m sb 8 bn
  /\ fldA m (sb + 8) 8 (bn + (20 * cap))
  /\ fldA m (sb + 16) 8 ((bn + (20 * cap)) + 20)
  /\ fldA m (sb + 24) 8 (bn + (20 * nc))
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
  /\ fldA m (sb - 96) 8 hs0
  /\ fldA m (sb - 88) 8 hs1
  /\ fldA m (sb - 80) 8 hs2
  /\ fldA m (sb - 72) 8 hs3
  /\ fldA m (sb - 64) 8 hs4
  /\ fldA m (sb - 56) 8 hs5
  /\ fldA m (sb - 48) 8 hs6
  /\ fldA m (sb - 40) 8 hs7
  /\ fldA m (sb - 32) 8 hs8
  /\ fldA m (sb - 24) 8 hs9
  /\ fldA m (sb - 16) 8 hs10
  /\ fldA m (sb - 8) 8 hs11
  /\ sh0 m (sb + 8)
  /\ sh0 m (v + 8)
  /\ sh0 m v
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 2 ^ 45 + 96 <= sb
  /\ sb + 40 <= 2 ^ 47
  /\ (v + 24 <= sb - 96 \/ sb + 40 <= v)
  /\ 0 <= b
  /\ b + 20 * cap < 2 ^ 47
  /\ 1048576 <= bn
  /\ bn + 20 * nc < 2 ^ 47
  /\ cap < nc <= 2 ^ 25
  /\ (v + 24 <= 2147446784 \/ 17594333495296 <= v)
  /\ (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96).

Definition voh_Q2 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
    voh_Q2_pre R m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 196)) fc None m (seg_rom asegs)) (MS R' F (wz AASAN_MEMCPY) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz (E + 300)
      /\ getr R' 2 = wz (sb - 96)
      /\ getr R' 8 = wz v
      /\ getr R' 9 = wz sb
      /\ getr R' 10 = wz bn
      /\ getr R' 11 = wz b
      /\ getr R' 12 = wz (20 * cap)
      /\ getr R' 14 = wz 0
      /\ getr R' 18 = wz (v + 8)
      /\ getr R' 19 = wz (v + 16)
      /\ getr R' 20 = wz (sb + 8)
      /\ getr R' 21 = wz bn
      /\ getr R' 22 = wz ASHADOW_BASE
      /\ getr R' 23 = wz (sh v)
      /\ getr R' 24 = wz (sh (v + 16))
      /\ getr R' 25 = wz (sh (v + 8))
      /\ getr R' 26 = wz (sh (sb + 8))
      /\ (forall r, In r [3; 4; 5; 6; 7; 15; 16; 17; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma voh_Q2_ec8f8 : voh_Q2 (0xec8f8).
Proof.
  intros R F fc m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_VoWHlp.q2_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) LbB_VoWHlp.q2_sr R) by (unfold LbB_VoWHlp.q2_E, LbB_VoWHlp.q2_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_VoWHlp.q2_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m LbB_VoWHlp.q2_A_knF) by (unfold LbB_VoWHlp.q2_E; knowB).
  destruct (LbB_VoWHlp.q2_A_run fx R m (seg_rom asegs) v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_VoWHlp.q2_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_VoWHlp.q2_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) in *. unfold LbB_VoWHlp.q2_E in Ev.
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
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  split; [rrwB HR' (26%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 15; 16; 17; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition voh_Q3_pre (R : bvmap 5 word) (m : mem) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z) : Prop :=
  getr R 2 = wz (sb - 96)
  /\ getr R 8 = wz v
  /\ getr R 9 = wz sb
  /\ getr R 18 = wz (v + 8)
  /\ getr R 19 = wz (v + 16)
  /\ getr R 22 = wz ASHADOW_BASE
  /\ getr R 23 = wz (sh v)
  /\ getr R 24 = wz (sh (v + 16))
  /\ getr R 25 = wz (sh (v + 8))
  /\ getr R 20 = wz (sb + 8)
  /\ getr R 21 = wz bn
  /\ getr R 26 = wz (sh (sb + 8))
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (20 * cap))
  /\ fldA m (v + 16) 8 (b + (20 * cap))
  /\ fldA m sb 8 bn
  /\ fldA m (sb + 8) 8 (bn + (20 * cap))
  /\ fldA m (sb + 16) 8 ((bn + (20 * cap)) + 20)
  /\ fldA m (sb + 24) 8 (bn + (20 * nc))
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
  /\ fldA m (sb - 96) 8 hs0
  /\ fldA m (sb - 88) 8 hs1
  /\ fldA m (sb - 80) 8 hs2
  /\ fldA m (sb - 72) 8 hs3
  /\ fldA m (sb - 64) 8 hs4
  /\ fldA m (sb - 56) 8 hs5
  /\ fldA m (sb - 48) 8 hs6
  /\ fldA m (sb - 40) 8 hs7
  /\ fldA m (sb - 32) 8 hs8
  /\ fldA m (sb - 24) 8 hs9
  /\ fldA m (sb - 16) 8 hs10
  /\ fldA m (sb - 8) 8 hs11
  /\ sh0 m (sb + 8)
  /\ sh0 m v
  /\ sh0 m (v + 8)
  /\ sh0 m (sb + 16)
  /\ sh0 m (v + 16)
  /\ sh0 m (sb + 24)
  /\ sh0 m sb
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 2 ^ 45 + 96 <= sb
  /\ sb + 40 <= 2 ^ 47
  /\ (v + 24 <= sb - 96 \/ sb + 40 <= v)
  /\ 0 <= b
  /\ b + 20 * cap < 2 ^ 47
  /\ 1048576 <= bn
  /\ bn + 20 * nc < 2 ^ 47
  /\ cap < nc <= 2 ^ 25
  /\ (v + 24 <= 2147446784 \/ 17594333495296 <= v)
  /\ (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96).

Definition voh_Q3 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 : Z),
    voh_Q3_pre R m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 300)) fc None m (seg_rom asegs)) (MS R' F (wz AANNOTATE_CC) fc None M' (seg_rom asegs))
      /\ munch [(sb, (sb + 32)); (v, (v + 24))] m M'
      /\ wmono asegs m M'
      /\ fldA M' sb 8 b
      /\ fldA M' (sb + 24) 8 (b + (20 * cap))
      /\ fldA M' (v + 16) 8 (bn + (20 * nc))
      /\ fldA M' (sb + 16) 8 b
      /\ fldA M' (v + 8) 8 ((bn + (20 * cap)) + 20)
      /\ fldA M' (sb + 8) 8 b
      /\ fldA M' v 8 bn
      /\ getr R' 1 = wz hs11
      /\ getr R' 2 = wz sb
      /\ getr R' 8 = wz hs10
      /\ getr R' 9 = wz hs9
      /\ getr R' 10 = wz bn
      /\ getr R' 11 = wz (bn + (20 * nc))
      /\ getr R' 12 = wz (bn + (20 * nc))
      /\ getr R' 13 = wz (((20 * cap) + bn) + 20)
      /\ getr R' 14 = wz 0
      /\ getr R' 18 = wz hs8
      /\ getr R' 19 = wz hs7
      /\ getr R' 20 = wz hs6
      /\ getr R' 21 = wz hs5
      /\ getr R' 22 = wz hs4
      /\ getr R' 23 = wz hs3
      /\ getr R' 24 = wz hs2
      /\ getr R' 25 = wz hs1
      /\ getr R' 26 = wz hs0
      /\ (forall r, In r [3; 4; 5; 6; 7; 15; 16; 17; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma voh_Q3_ec8f8 : voh_Q3 (0xec8f8).
Proof.
  intros R F fc m v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54 & P55 & P56 & P57 & P58 & P59 & P60 & P61). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_VoWHlp.q3_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) LbB_VoWHlp.q3_sr R) by (unfold LbB_VoWHlp.q3_E, LbB_VoWHlp.q3_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_VoWHlp.q3_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) m LbB_VoWHlp.q3_A_knF) by (unfold LbB_VoWHlp.q3_E; knowB).
  destruct (LbB_VoWHlp.q3_A_run fx R m (seg_rom asegs) v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_VoWHlp.q3_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_VoWHlp.q3_E R v sb b cap bn nc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11) in *. unfold LbB_VoWHlp.q3_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 1; 0; 1; 0; 1; 1; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fld_postB_at 3%nat|].
  split; [fld_postB_at 4%nat|].
  split; [fld_postB_at 5%nat|].
  split; [fld_postB_at 6%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (23%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  split; [rrwB HR' (26%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 15; 16; 17; 27; 28; 29; 30; 31]%bv : list reg).
Qed.
