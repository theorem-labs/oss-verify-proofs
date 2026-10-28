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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_RvW.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition rvw_R1_pre (R : bvmap 5 word) (m : mem) (v k spz b cap n : Z) : Prop :=
  getr R 10 = wz v
  /\ getr R 11 = wz k
  /\ getr R 2 = wz spz
  /\ ACONST m
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (4 * n))
  /\ fldA m (v + 16) 8 (b + (4 * cap))
  /\ wr_at asegs m (spz - 80) 80
  /\ 2 ^ 45 + 192 <= spz <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= b <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 45
  /\ 0 <= n <= 2 ^ 45
  /\ 0 <= k <= 2 ^ 24
  /\ (v + 24 <= (spz - 80) \/ (spz - 80) + 80 <= v)
  /\ sh0 m (v + 16)
  /\ sh0 m v
  /\ sh0 m (v + 8)
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 0 <= b
  /\ b + 4 * cap < 2 ^ 47
  /\ 0 <= n <= cap
  /\ cap <= 2 ^ 45
  /\ (v + 24 <= spz - 80 \/ spz <= v).

Definition rvw_R1R (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v k spz b cap n : Z),
    rvw_R1_pre R m v k spz b cap n -> (k <= cap) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz E) fc None m (seg_rom asegs)) (MS R' F (wz (E + 300)) fc None M' (seg_rom asegs))
      /\ munch [((spz - 40), spz)] m M'
      /\ wmono asegs m M'
      /\ fldw asegs M' (spz - 40) 8 (getr R 19)
      /\ fldw asegs M' (spz - 32) 8 (getr R 18)
      /\ fldw asegs M' (spz - 24) 8 (getr R 9)
      /\ fldw asegs M' (spz - 16) 8 (getr R 8)
      /\ fldw asegs M' (spz - 8) 8 (getr R 1)
      /\ getr R' 2 = wz spz
      /\ getr R' 10 = wz v
      /\ getr R' 11 = wz ((4 * cap) / 4)
      /\ getr R' 12 = wz b
      /\ getr R' 13 = wz ASHADOW_BASE
      /\ getr R' 14 = wz 0
      /\ (forall r, In r [1; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma rvw_R1R_ec634 : rvw_R1R (0xec634).
Proof.
  intros R F fc m v k spz b cap n P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_RvW.r1_E R v k spz b cap n) LbB_RvW.r1_sr R) by (unfold LbB_RvW.r1_E, LbB_RvW.r1_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_RvW.r1_E R v k spz b cap n) m LbB_RvW.r1_R_knF) by (unfold LbB_RvW.r1_E; knowB).
  destruct (LbB_RvW.r1_R_run fx R m (seg_rom asegs) v k spz b cap n ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_RvW.r1_R_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_RvW.r1_E R v k spz b cap n) in *. unfold LbB_RvW.r1_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fldw_postB_at 0%nat|].
  split; [fldw_postB_at 1%nat|].
  split; [fldw_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
  split; [fldw_postB_at 4%nat|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (14%bv : reg); regB|].
  keptB HR HR' ([1; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition rvw_R1N (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v k spz b cap n : Z),
    rvw_R1_pre R m v k spz b cap n -> (cap < k) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz E) fc None m (seg_rom asegs)) (MS R' F (wz AOPNEW) fc None M' (seg_rom asegs))
      /\ munch [((spz - 48), spz)] m M'
      /\ wmono asegs m M'
      /\ fldA M' (spz - 48) 8 v
      /\ fldw asegs M' (spz - 40) 8 (getr R 19)
      /\ fldw asegs M' (spz - 32) 8 (getr R 18)
      /\ fldw asegs M' (spz - 24) 8 (getr R 9)
      /\ fldw asegs M' (spz - 16) 8 (getr R 8)
      /\ fldw asegs M' (spz - 8) 8 (getr R 1)
      /\ getr R' 1 = wz (E + 152)
      /\ getr R' 2 = wz (spz - 80)
      /\ getr R' 8 = wz k
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz (4 * k)
      /\ getr R' 11 = wz (b + (4 * n))
      /\ getr R' 12 = wz b
      /\ getr R' 13 = wz 0
      /\ getr R' 14 = wz ((v + 8) / 8)
      /\ getr R' 18 = wz (4 * k)
      /\ getr R' 19 = wz (4 * n)
      /\ (forall r, In r [3; 4; 5; 6; 7; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma rvw_R1N_ec634 : rvw_R1N (0xec634).
Proof.
  intros R F fc m v k spz b cap n P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_RvW.r1_E R v k spz b cap n) LbB_RvW.r1_sr R) by (unfold LbB_RvW.r1_E, LbB_RvW.r1_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_RvW.r1_E R v k spz b cap n) m LbB_RvW.r1_N_knF) by (unfold LbB_RvW.r1_E; knowB).
  destruct (LbB_RvW.r1_N_run fx R m (seg_rom asegs) v k spz b cap n ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_RvW.r1_N_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_RvW.r1_E R v k spz b cap n) in *. unfold LbB_RvW.r1_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fldw_postB_at 1%nat|].
  split; [fldw_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
  split; [fldw_postB_at 4%nat|].
  split; [fldw_postB_at 5%nat|].
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
  keptB HR HR' ([3; 4; 5; 6; 7; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition rvw_R2_pre (R : bvmap 5 word) (m : mem) (v k sb n A : Z) : Prop :=
  getr R 10 = wz A
  /\ getr R 2 = wz sb
  /\ getr R 8 = wz k
  /\ getr R 9 = wz v
  /\ getr R 18 = wz (4 * k)
  /\ getr R 19 = wz (4 * n)
  /\ wr_at asegs m sb 32
  /\ 2 ^ 45 + 112 <= sb <= 2 ^ 47
  /\ 0 <= n <= 2 ^ 24
  /\ 1048576 <= A <= 2 ^ 47
  /\ 1 <= k <= 2 ^ 24
  /\ A mod 16 = 0
  /\ 1048576 <= A
  /\ A + 4 * k < 2 ^ 47
  /\ 0 <= n <= k
  /\ 2 ^ 45 + 112 <= sb
  /\ sb + 80 <= 2 ^ 47.

Definition rvw_R2 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v k sb n A : Z),
    rvw_R2_pre R m v k sb n A ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 152)) fc None m (seg_rom asegs)) (MS R' F (wz 956208) fc None M' (seg_rom asegs))
      /\ munch [(sb, (sb + 32))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sb + 24) 8 ((4 * k) + A)
      /\ fldA M' (sb + 16) 8 ((4 * n) + A)
      /\ fldA M' (sb + 8) 8 ((4 * n) + A)
      /\ fldA M' sb 8 A
      /\ getr R' 1 = wz (E + 208)
      /\ getr R' 2 = wz sb
      /\ getr R' 8 = wz 0
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz v
      /\ getr R' 11 = wz sb
      /\ getr R' 18 = wz (4 * k)
      /\ getr R' 19 = wz ((4 * n) + A)
      /\ (forall r, In r [3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma rvw_R2_ec634 : rvw_R2 (0xec634).
Proof.
  intros R F fc m v k sb n A P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_RvW.r2_E R v k sb n A) LbB_RvW.r2_sr R) by (unfold LbB_RvW.r2_E, LbB_RvW.r2_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_RvW.r2_E R v k sb n A) m LbB_RvW.r2_A_knF) by (unfold LbB_RvW.r2_E; knowB).
  destruct (LbB_RvW.r2_A_run fx R m (seg_rom asegs) v k sb n A ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_RvW.r2_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_RvW.r2_E R v k sb n A) in *. unfold LbB_RvW.r2_E in Ev.
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
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition rvw_H1_pre (R : bvmap 5 word) (m : mem) (v sb b cap n A k : Z) : Prop :=
  getr R 10 = wz v
  /\ getr R 11 = wz sb
  /\ getr R 2 = wz sb
  /\ ACONST m
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (4 * n))
  /\ fldA m (v + 16) 8 (b + (4 * cap))
  /\ fldA m sb 8 A
  /\ fldA m (sb + 8) 8 (A + (4 * n))
  /\ fldA m (sb + 16) 8 (A + (4 * n))
  /\ fldA m (sb + 24) 8 (A + (4 * k))
  /\ 2 ^ 45 + 112 <= sb <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= b <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 24
  /\ 0 <= n <= 2 ^ 24
  /\ 1048576 <= A <= 2 ^ 47
  /\ 1 <= k <= 2 ^ 24
  /\ A mod 16 = 0
  /\ b mod 4 = 0
  /\ wr_at asegs m (sb - 112) 112
  /\ (v + 24 <= (sb - 112) \/ (sb - 112) + 152 <= v)
  /\ sh0 m v
  /\ sh0 m (v + 8)
  /\ sh0 m (v + 16)
  /\ sh0 m (sb + 8)
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 0 <= b
  /\ b + 4 * cap < 2 ^ 47
  /\ 0 <= n <= cap
  /\ cap <= 2 ^ 24
  /\ 1048576 <= A
  /\ A + 4 * k < 2 ^ 47
  /\ cap < k <= 2 ^ 24
  /\ 2 ^ 45 + 112 <= sb
  /\ sb + 40 <= 2 ^ 47
  /\ (v + 24 <= sb - 112 \/ sb + 40 <= v)
  /\ (v + 24 <= 2147446784 \/ 17594333495296 <= v)
  /\ (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 112).

Definition rvw_H1A (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sb b cap n A k : Z),
    rvw_H1_pre R m v sb b cap n A k -> (b <> 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz 956208) fc None m (seg_rom asegs)) (MS R' F (wz AANNOTATE_CC) fc None M' (seg_rom asegs))
      /\ munch [((sb - 104), sb)] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sb - 104) 8 954568
      /\ fldA M' (sb - 96) 8 sb
      /\ fldA M' (sb - 88) 8 956276
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
      /\ getr R' 1 = wz 954568
      /\ getr R' 2 = wz (sb - 96)
      /\ getr R' 8 = wz sb
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz b
      /\ getr R' 11 = wz (b + (4 * cap))
      /\ getr R' 12 = wz (b + (4 * n))
      /\ getr R' 13 = wz (b + (4 * cap))
      /\ getr R' 16 = wz ((v + 16) / 8)
      /\ getr R' 21 = wz ASHADOW_BASE
      /\ (forall r, In r [3; 4; 5; 6; 7; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma rvw_H1A_ec634 : rvw_H1A (0xec634).
Proof.
  intros R F fc m v sb b cap n A k P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_RvW.h1_E R v sb b cap n A k) LbB_RvW.h1_sr R) by (unfold LbB_RvW.h1_E, LbB_RvW.h1_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_RvW.h1_E R v sb b cap n A k) m LbB_RvW.h1_A_knF) by (unfold LbB_RvW.h1_E; knowB).
  destruct (LbB_RvW.h1_A_run fx R m (seg_rom asegs) v sb b cap n A k ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_RvW.h1_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_RvW.h1_E R v sb b cap n A k) in *. unfold LbB_RvW.h1_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
  split; [fldw_postB_at 4%nat|].
  split; [fldw_postB_at 5%nat|].
  split; [fldw_postB_at 6%nat|].
  split; [fldw_postB_at 7%nat|].
  split; [fldw_postB_at 8%nat|].
  split; [fldw_postB_at 9%nat|].
  split; [fldw_postB_at 10%nat|].
  split; [fldw_postB_at 11%nat|].
  split; [fldw_postB_at 12%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|].
  split; [rrwB HR' (16%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition rvw_H1Z (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sb b cap n A k : Z),
    rvw_H1_pre R m v sb b cap n A k -> (b = 0) -> (cap = 0) -> (n = 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz 956208) fc None m (seg_rom asegs)) (MS R' F (wz AASAN_MEMCPY) fc None M' (seg_rom asegs))
      /\ munch [((sb - 104), sb)] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sb - 104) 8 954568
      /\ fldA M' (sb - 96) 8 sb
      /\ fldA M' (sb - 88) 8 956276
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
      /\ getr R' 1 = wz 956436
      /\ getr R' 2 = wz (sb - 80)
      /\ getr R' 8 = wz sb
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz ((4 * n) + (A + ((-4) * ((4 * n) / 4))))
      /\ getr R' 11 = wz b
      /\ getr R' 12 = wz (4 * n)
      /\ getr R' 13 = wz ((-4) * ((4 * n) / 4))
      /\ getr R' 16 = wz ((v + 16) / 8)
      /\ getr R' 18 = wz (v + 8)
      /\ getr R' 19 = wz (sb + 8)
      /\ getr R' 20 = wz ((4 * n) + (A + ((-4) * ((4 * n) / 4))))
      /\ getr R' 21 = wz ASHADOW_BASE
      /\ getr R' 22 = wz (sh (v + 8))
      /\ getr R' 23 = wz (sh (sb + 8))
      /\ getr R' 24 = wz (sh v)
      /\ (forall r, In r [3; 4; 5; 6; 7; 17; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma rvw_H1Z_ec634 : rvw_H1Z (0xec634).
Proof.
  intros R F fc m v sb b cap n A k P Q0 Q1 Q2.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_RvW.h1_E R v sb b cap n A k) LbB_RvW.h1_sr R) by (unfold LbB_RvW.h1_E, LbB_RvW.h1_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_RvW.h1_E R v sb b cap n A k) m LbB_RvW.h1_Z_knF) by (unfold LbB_RvW.h1_E; knowB).
  destruct (LbB_RvW.h1_Z_run fx R m (seg_rom asegs) v sb b cap n A k ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_RvW.h1_Z_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_RvW.h1_E R v sb b cap n A k) in *. unfold LbB_RvW.h1_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
  split; [fldw_postB_at 4%nat|].
  split; [fldw_postB_at 5%nat|].
  split; [fldw_postB_at 6%nat|].
  split; [fldw_postB_at 7%nat|].
  split; [fldw_postB_at 8%nat|].
  split; [fldw_postB_at 9%nat|].
  split; [fldw_postB_at 10%nat|].
  split; [fldw_postB_at 11%nat|].
  split; [fldw_postB_at 12%nat|].
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

Definition rvw_H2_pre (R : bvmap 5 word) (m : mem) (v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z) : Prop :=
  getr R 2 = wz (sb - 96)
  /\ getr R 8 = wz sb
  /\ getr R 9 = wz v
  /\ getr R 21 = wz ASHADOW_BASE
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (4 * n))
  /\ fldA m (v + 16) 8 (b + (4 * cap))
  /\ fldA m sb 8 A
  /\ fldA m (sb + 8) 8 (A + (4 * n))
  /\ fldA m (sb + 16) 8 (A + (4 * n))
  /\ fldA m (sb + 24) 8 (A + (4 * k))
  /\ fldA m (sb - 96) 8 sb
  /\ fldA m (sb - 88) 8 956276
  /\ 2 ^ 45 + 96 <= sb <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= b <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 24
  /\ 0 <= n <= 2 ^ 24
  /\ 1048576 <= A <= 2 ^ 47
  /\ 1 <= k <= 2 ^ 24
  /\ A mod 16 = 0
  /\ b mod 4 = 0
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
  /\ 0 <= b
  /\ b + 4 * cap < 2 ^ 47
  /\ 0 <= n <= cap
  /\ cap <= 2 ^ 24
  /\ 1048576 <= A
  /\ A + 4 * k < 2 ^ 47
  /\ cap < k <= 2 ^ 24
  /\ 2 ^ 45 + 96 <= sb
  /\ sb + 40 <= 2 ^ 47
  /\ (v + 24 <= sb - 96 \/ sb + 40 <= v)
  /\ (v + 24 <= 2147446784 \/ 17594333495296 <= v)
  /\ (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 96).

Definition rvw_H2 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z),
    rvw_H2_pre R m v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz 954568) fc None m (seg_rom asegs)) (MS R' F (wz AASAN_MEMCPY) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz 956436
      /\ getr R' 2 = wz (sb - 80)
      /\ getr R' 8 = wz sb
      /\ getr R' 9 = wz v
      /\ getr R' 10 = wz ((4 * n) + (A + ((-4) * ((4 * n) / 4))))
      /\ getr R' 11 = wz b
      /\ getr R' 12 = wz (4 * n)
      /\ getr R' 13 = wz ((-4) * ((4 * n) / 4))
      /\ getr R' 18 = wz (v + 8)
      /\ getr R' 19 = wz (sb + 8)
      /\ getr R' 20 = wz ((4 * n) + (A + ((-4) * ((4 * n) / 4))))
      /\ getr R' 21 = wz ASHADOW_BASE
      /\ getr R' 22 = wz (sh (v + 8))
      /\ getr R' 23 = wz (sh (sb + 8))
      /\ getr R' 24 = wz (sh v)
      /\ (forall r, In r [3; 4; 5; 6; 7; 15; 16; 17; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma rvw_H2_ec634 : rvw_H2 (0xec634).
Proof.
  intros R F fc m v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_RvW.h2_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) LbB_RvW.h2_sr R) by (unfold LbB_RvW.h2_E, LbB_RvW.h2_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_RvW.h2_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m LbB_RvW.h2_A_knF) by (unfold LbB_RvW.h2_E; knowB).
  destruct (LbB_RvW.h2_A_run fx R m (seg_rom asegs) v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_RvW.h2_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_RvW.h2_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) in *. unfold LbB_RvW.h2_E in Ev.
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

Definition rvw_H3_pre (R : bvmap 5 word) (m : mem) (v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z) : Prop :=
  getr R 2 = wz (sb - 80)
  /\ getr R 8 = wz sb
  /\ getr R 9 = wz v
  /\ getr R 18 = wz (v + 8)
  /\ getr R 19 = wz (sb + 8)
  /\ getr R 20 = wz A
  /\ getr R 21 = wz ASHADOW_BASE
  /\ getr R 22 = wz (sh (v + 8))
  /\ getr R 23 = wz (sh (sb + 8))
  /\ getr R 24 = wz (sh v)
  /\ ACONST m
  /\ fldA m v 8 b
  /\ fldA m (v + 8) 8 (b + (4 * n))
  /\ fldA m (v + 16) 8 (b + (4 * cap))
  /\ fldA m sb 8 A
  /\ fldA m (sb + 8) 8 (A + (4 * n))
  /\ fldA m (sb + 16) 8 (A + (4 * n))
  /\ fldA m (sb + 24) 8 (A + (4 * k))
  /\ 2 ^ 45 + 80 <= sb <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= b <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 24
  /\ 0 <= n <= 2 ^ 24
  /\ 1048576 <= A <= 2 ^ 47
  /\ 1 <= k <= 2 ^ 24
  /\ A mod 16 = 0
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
  /\ 0 <= b
  /\ b + 4 * cap < 2 ^ 47
  /\ 0 <= n <= cap
  /\ cap <= 2 ^ 24
  /\ 1048576 <= A
  /\ A + 4 * k < 2 ^ 47
  /\ cap < k <= 2 ^ 24
  /\ 2 ^ 45 + 80 <= sb
  /\ sb + 40 <= 2 ^ 47
  /\ (v + 24 <= sb - 80 \/ sb + 40 <= v)
  /\ (v + 24 <= 2147446784 \/ 17594333495296 <= v)
  /\ (sb + 40 <= 2147446784 \/ 17594333495296 <= sb - 80)
  /\ 7241728 <= v.

Definition rvw_H3 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 : Z),
    rvw_H3_pre R m v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz 956436) fc None m (seg_rom asegs)) (MS R' F (wz AANNOTATE_CC) fc None M' (seg_rom asegs))
      /\ munch [((sb - 24), (sb + 32)); (v, (v + 24))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sb - 24) 8 958128
      /\ fldA M' (sb - 16) 8 hs8
      /\ fldA M' (sb - 8) 8 hs9
      /\ fldA M' sb 8 b
      /\ fldA M' (sb + 24) 8 (b + (4 * cap))
      /\ fldA M' (v + 16) 8 (A + (4 * k))
      /\ fldA M' (sb + 16) 8 b
      /\ fldA M' (v + 8) 8 (A + (4 * n))
      /\ fldA M' (sb + 8) 8 b
      /\ fldA M' v 8 A
      /\ getr R' 1 = wz 958128
      /\ getr R' 2 = wz (sb - 16)
      /\ getr R' 8 = wz hs8
      /\ getr R' 9 = wz hs7
      /\ getr R' 10 = wz A
      /\ getr R' 11 = wz (A + (4 * k))
      /\ getr R' 12 = wz ((4 * k) + A)
      /\ getr R' 13 = wz (A + (4 * ((4 * n) / 4)))
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

Lemma rvw_H3_ec634 : rvw_H3 (0xec634).
Proof.
  intros R F fc m v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39 & P40 & P41 & P42 & P43 & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54 & P55 & P56 & P57 & P58 & P59 & P60 & P61). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_RvW.h3_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) LbB_RvW.h3_sr R) by (unfold LbB_RvW.h3_E, LbB_RvW.h3_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_RvW.h3_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) m LbB_RvW.h3_A_knF) by (unfold LbB_RvW.h3_E; knowB).
  destruct (LbB_RvW.h3_A_run fx R m (seg_rom asegs) v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_RvW.h3_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_RvW.h3_E R v sb b cap n A k hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9) in *. unfold LbB_RvW.h3_E in Ev.
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

Definition rvw_H4_pre (E : Z) (R : bvmap 5 word) (m : mem) (v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 : Z) : Prop :=
  getr R 2 = wz (sb - 16)
  /\ fldA m (sb - 8) 8 (E + 208)
  /\ fldA m (sb - 16) 8 hs8
  /\ fldA m sb 8 b
  /\ fldA m (sb + 8) 8 b
  /\ fldA m (sb + 16) 8 b
  /\ fldA m (sb + 24) 8 (b + (4 * cap))
  /\ fldA m (sb + 32) 8 v
  /\ fldA m (sb + 72) 8 sv1
  /\ fldA m (sb + 64) 8 sv8
  /\ fldA m (sb + 56) 8 sv9
  /\ fldA m (sb + 48) 8 sv18
  /\ fldA m (sb + 40) 8 sv19
  /\ 2 ^ 45 + 16 <= sb <= 2 ^ 47
  /\ 1048576 <= v <= 2 ^ 47
  /\ 0 <= b <= 2 ^ 47
  /\ 0 <= cap <= 2 ^ 24
  /\ 1048576 <= v
  /\ v + 24 <= 2 ^ 47
  /\ 0 <= b
  /\ b + 4 * cap < 2 ^ 47
  /\ 2 ^ 45 + 16 <= sb
  /\ sb + 80 <= 2 ^ 47.

Definition rvw_H4D (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 : Z),
    rvw_H4_pre E R m v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 -> (b <> 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz 958128) fc None m (seg_rom asegs)) (MS R' F (wz AOPDEL2) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz (E + 276)
      /\ getr R' 2 = wz sb
      /\ getr R' 8 = wz hs8
      /\ getr R' 10 = wz b
      /\ getr R' 11 = wz (4 * cap)
      /\ (forall r, In r [3; 4; 5; 6; 7; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma rvw_H4D_ec634 : rvw_H4D (0xec634).
Proof.
  intros R F fc m v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_RvW.h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) LbB_RvW.h4_sr R) by (unfold LbB_RvW.h4_E, LbB_RvW.h4_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_RvW.h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) m LbB_RvW.h4_D_knF) by (unfold LbB_RvW.h4_E; knowB).
  destruct (LbB_RvW.h4_D_run fx R m (seg_rom asegs) v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_RvW.h4_D_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_RvW.h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) in *. unfold LbB_RvW.h4_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition rvw_H4N (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 : Z),
    rvw_H4_pre E R m v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 -> (b = 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz 958128) fc None m (seg_rom asegs)) (MS R' F (wz (E + 300)) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz sv1
      /\ getr R' 2 = wz (sb + 80)
      /\ getr R' 8 = wz sv8
      /\ getr R' 9 = wz sv9
      /\ getr R' 10 = wz b
      /\ getr R' 11 = wz b
      /\ getr R' 18 = wz sv18
      /\ getr R' 19 = wz sv19
      /\ (forall r, In r [3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma rvw_H4N_ec634 : rvw_H4N (0xec634).
Proof.
  intros R F fc m v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_RvW.h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) LbB_RvW.h4_sr R) by (unfold LbB_RvW.h4_E, LbB_RvW.h4_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_RvW.h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) m LbB_RvW.h4_N_knF) by (unfold LbB_RvW.h4_E; knowB).
  destruct (LbB_RvW.h4_N_run fx R m (seg_rom asegs) v sb b cap hs8 sv1 sv8 sv9 sv18 sv19 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_RvW.h4_N_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_RvW.h4_E R v sb b cap hs8 sv1 sv8 sv9 sv18 sv19) in *. unfold LbB_RvW.h4_E in Ev.
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
  keptB HR HR' ([3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition rvw_R4_pre (R : bvmap 5 word) (m : mem) (sb sv1 sv8 sv9 sv18 sv19 : Z) : Prop :=
  getr R 2 = wz sb
  /\ fldA m (sb + 72) 8 sv1
  /\ fldA m (sb + 64) 8 sv8
  /\ fldA m (sb + 56) 8 sv9
  /\ fldA m (sb + 48) 8 sv18
  /\ fldA m (sb + 40) 8 sv19
  /\ 2 ^ 45 <= sb <= 2 ^ 47
  /\ 2 ^ 45 <= sb
  /\ sb + 80 <= 2 ^ 47.

Definition rvw_R4 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (sb sv1 sv8 sv9 sv18 sv19 : Z),
    rvw_R4_pre R m sb sv1 sv8 sv9 sv18 sv19 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 276)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 300)) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz sv1
      /\ getr R' 2 = wz (sb + 80)
      /\ getr R' 8 = wz sv8
      /\ getr R' 9 = wz sv9
      /\ getr R' 18 = wz sv18
      /\ getr R' 19 = wz sv19
      /\ (forall r, In r [3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma rvw_R4_ec634 : rvw_R4 (0xec634).
Proof.
  intros R F fc m sb sv1 sv8 sv9 sv18 sv19 P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_RvW.r4_E R sb sv1 sv8 sv9 sv18 sv19) LbB_RvW.r4_sr R) by (unfold LbB_RvW.r4_E, LbB_RvW.r4_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_RvW.r4_E R sb sv1 sv8 sv9 sv18 sv19) m LbB_RvW.r4_A_knF) by (unfold LbB_RvW.r4_E; knowB).
  destruct (LbB_RvW.r4_A_run fx R m (seg_rom asegs) sb sv1 sv8 sv9 sv18 sv19 ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_RvW.r4_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_RvW.r4_E R sb sv1 sv8 sv9 sv18 sv19) in *. unfold LbB_RvW.r4_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.
