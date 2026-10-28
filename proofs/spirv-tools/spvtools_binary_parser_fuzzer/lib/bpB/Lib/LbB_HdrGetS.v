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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HdrGetR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition hg_h1_pre (R : bvmap 5 word) (m : mem) (b code nn e h sp w0 : Z) : Prop :=
  getr R 10 = wz b
  /\ getr R 11 = wz e
  /\ getr R 12 = wz h
  /\ getr R 2 = wz sp
  /\ ACONST m
  /\ fldA m b 8 code
  /\ fldA m (b + 8) 8 nn
  /\ fldA m code 4 w0
  /\ 7241728 <= b <= 2 ^ 47 - 16
  /\ b mod 8 = 0
  /\ 7241728 <= code <= 2 ^ 47 - 20
  /\ code mod 8 = 0
  /\ 5 <= nn <= 2 ^ 64 - 1
  /\ 0 <= e <= 1
  /\ 7241728 <= h <= 2 ^ 47 - 32
  /\ h mod 8 = 0
  /\ 140735332483136 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ wr_at asegs m (sp - 64) 64
  /\ 0 <= w0 <= 2 ^ 32 - 1
  /\ sh0 m b
  /\ sh0 m (b + 8)
  /\ sh0 m code
  /\ (b + 16 <= sp - 64 \/ sp <= b)
  /\ (code + 20 <= sp - 64 \/ sp <= code)
  /\ (h + 32 <= sp - 64 \/ sp <= h)
  /\ (h + 32 <= b \/ b + 16 <= h)
  /\ (h + 32 <= code \/ code + 20 <= h).

Definition hg_h1 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code nn e h sp w0 : Z),
    hg_h1_pre R m b code nn e h sp w0 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz E) fc None m (seg_rom asegs)) (MS R' F (wz 1034240) fc None M' (seg_rom asegs))
      /\ munch [((sp - 56), sp)] m M'
      /\ wmono asegs m M'
      /\ fldw asegs M' (sp - 56) 8 (getr R 21)
      /\ fldw asegs M' (sp - 48) 8 (getr R 20)
      /\ fldw asegs M' (sp - 40) 8 (getr R 19)
      /\ fldw asegs M' (sp - 32) 8 (getr R 18)
      /\ fldw asegs M' (sp - 24) 8 (getr R 9)
      /\ fldw asegs M' (sp - 16) 8 (getr R 8)
      /\ fldw asegs M' (sp - 8) 8 (getr R 1)
      /\ getr R' 1 = wz (E + 172)
      /\ getr R' 2 = wz (sp - 64)
      /\ getr R' 8 = wz b
      /\ getr R' 9 = wz h
      /\ getr R' 11 = wz e
      /\ getr R' 12 = wz 5
      /\ getr R' 18 = wz e
      /\ getr R' 19 = wz 18446744073709551612
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (sh b)
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma hg_h1_ea2b4 : hg_h1 (959156).
Proof.
  intros R F fc m b code nn e h sp w0 P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_HdrGetR.h1_E R b code nn e h sp w0) LbB_HdrGetR.h1_sr R) by (unfold LbB_HdrGetR.h1_E, LbB_HdrGetR.h1_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_HdrGetR.h1_E R b code nn e h sp w0) m LbB_HdrGetR.h1_N_knF) by (unfold LbB_HdrGetR.h1_E; knowB).
  destruct (LbB_HdrGetR.h1_N_run fx R m (seg_rom asegs) b code nn e h sp w0 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_HdrGetR.h1_N_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_HdrGetR.h1_E R b code nn e h sp w0) in *. unfold LbB_HdrGetR.h1_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fldw_postB_at 0%nat|].
  split; [fldw_postB_at 1%nat|].
  split; [fldw_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
  split; [fldw_postB_at 4%nat|].
  split; [fldw_postB_at 5%nat|].
  split; [fldw_postB_at 6%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition hg_h1s_pre (R : bvmap 5 word) (m : mem) (b code nn e h sp : Z) : Prop :=
  getr R 10 = wz b
  /\ getr R 11 = wz e
  /\ getr R 12 = wz h
  /\ getr R 2 = wz sp
  /\ ACONST m
  /\ fldA m b 8 code
  /\ fldA m (b + 8) 8 nn
  /\ 7241728 <= b <= 2 ^ 47 - 16
  /\ b mod 8 = 0
  /\ 7241728 <= code <= 2 ^ 47 - 20
  /\ code mod 8 = 0
  /\ 0 <= e <= 1
  /\ 7241728 <= h <= 2 ^ 47 - 32
  /\ h mod 8 = 0
  /\ 140735332483136 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ wr_at asegs m (sp - 64) 64
  /\ 0 <= nn <= 4
  /\ sh0 m b
  /\ sh0 m (b + 8)
  /\ (b + 16 <= sp - 64 \/ sp <= b)
  /\ (code + 20 <= sp - 64 \/ sp <= code)
  /\ (h + 32 <= sp - 64 \/ sp <= h)
  /\ (h + 32 <= b \/ b + 16 <= h)
  /\ (h + 32 <= code \/ code + 20 <= h).

Definition hg_h1s (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code nn e h sp : Z),
    hg_h1s_pre R m b code nn e h sp ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz E) fc None m (seg_rom asegs)) (MS R' F (wz (E + 680)) fc None M' (seg_rom asegs))
      /\ munch [((sp - 56), sp)] m M'
      /\ wmono asegs m M'
      /\ fldw asegs M' (sp - 56) 8 (getr R 21)
      /\ fldw asegs M' (sp - 48) 8 (getr R 20)
      /\ fldw asegs M' (sp - 40) 8 (getr R 19)
      /\ fldw asegs M' (sp - 32) 8 (getr R 18)
      /\ fldw asegs M' (sp - 24) 8 (getr R 9)
      /\ fldw asegs M' (sp - 16) 8 (getr R 8)
      /\ fldw asegs M' (sp - 8) 8 (getr R 1)
      /\ getr R' 2 = wz sp
      /\ getr R' 10 = wz 18446744073709551612
      /\ getr R' 11 = wz nn
      /\ getr R' 12 = wz 5
      /\ (forall r, In r [1; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma hg_h1s_ea2b4 : hg_h1s (959156).
Proof.
  intros R F fc m b code nn e h sp P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_HdrGetR.h1s_E R b code nn e h sp) LbB_HdrGetR.h1s_sr R) by (unfold LbB_HdrGetR.h1s_E, LbB_HdrGetR.h1s_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_HdrGetR.h1s_E R b code nn e h sp) m LbB_HdrGetR.h1s_S_knF) by (unfold LbB_HdrGetR.h1s_E; knowB).
  destruct (LbB_HdrGetR.h1s_S_run fx R m (seg_rom asegs) b code nn e h sp ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_HdrGetR.h1s_S_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_HdrGetR.h1s_E R b code nn e h sp) in *. unfold LbB_HdrGetR.h1s_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fldw_postB_at 0%nat|].
  split; [fldw_postB_at 1%nat|].
  split; [fldw_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|].
  split; [fldw_postB_at 4%nat|].
  split; [fldw_postB_at 5%nat|].
  split; [fldw_postB_at 6%nat|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  keptB HR HR' ([1; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition hg_h2_pre (R : bvmap 5 word) (m : mem) (b code e h sp r1 w : Z) : Prop :=
  getr R 2 = wz (sp - 64)
  /\ getr R 8 = wz b
  /\ getr R 9 = wz h
  /\ getr R 18 = wz e
  /\ getr R 19 = wz (-4)
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (sh b)
  /\ getr R 10 = wz r1
  /\ fldA m b 8 code
  /\ 7241728 <= b <= 2 ^ 47 - 16
  /\ b mod 8 = 0
  /\ 7241728 <= code <= 2 ^ 47 - 20
  /\ code mod 8 = 0
  /\ 0 <= e <= 1
  /\ 7241728 <= h <= 2 ^ 47 - 32
  /\ h mod 8 = 0
  /\ 140735332483136 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ wr_at asegs m h 32
  /\ fldA m (code + 4) 4 w
  /\ 0 <= w <= 2 ^ 32 - 1
  /\ sh0 m h
  /\ sh0 m b
  /\ sh0 m (code + 4)
  /\ (b + 16 <= sp - 64 \/ sp <= b)
  /\ (code + 20 <= sp - 64 \/ sp <= code)
  /\ (h + 32 <= sp - 64 \/ sp <= h)
  /\ (h + 32 <= b \/ b + 16 <= h)
  /\ (h + 32 <= code \/ code + 20 <= h)
  /\ (h + 32 <= 2147446784 \/ 17594333495296 <= h).

Definition hg_h2 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 w : Z),
    hg_h2_pre R m b code e h sp r1 w ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 172)) fc None m (seg_rom asegs)) (MS R' F (wz 1034240) fc None M' (seg_rom asegs))
      /\ munch [(h, (h + 4))] m M'
      /\ wmono asegs m M'
      /\ fldA M' h 4 r1
      /\ getr R' 1 = wz (E + 260)
      /\ getr R' 2 = wz (sp - 64)
      /\ getr R' 8 = wz b
      /\ getr R' 9 = wz h
      /\ getr R' 11 = wz e
      /\ getr R' 12 = wz 0
      /\ getr R' 18 = wz e
      /\ getr R' 19 = wz (-4)
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (sh b)
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma hg_h2_ea2b4 : hg_h2 (959156).
Proof.
  intros R F fc m b code e h sp r1 w P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_HdrGetR.h2_E R b code e h sp r1 w) LbB_HdrGetR.h2_sr R) by (unfold LbB_HdrGetR.h2_E, LbB_HdrGetR.h2_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_HdrGetR.h2_E R b code e h sp r1 w) m LbB_HdrGetR.h2_A_knF) by (unfold LbB_HdrGetR.h2_E; knowB).
  destruct (LbB_HdrGetR.h2_A_run fx R m (seg_rom asegs) b code e h sp r1 w ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_HdrGetR.h2_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_HdrGetR.h2_E R b code e h sp r1 w) in *. unfold LbB_HdrGetR.h2_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition hg_h3x_pre (R : bvmap 5 word) (m : mem) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z) : Prop :=
  getr R 2 = wz (sp - 64)
  /\ getr R 8 = wz b
  /\ getr R 9 = wz h
  /\ getr R 18 = wz e
  /\ getr R 19 = wz (-4)
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (sh b)
  /\ getr R 10 = wz r1
  /\ fldA m b 8 code
  /\ 7241728 <= b <= 2 ^ 47 - 16
  /\ b mod 8 = 0
  /\ 7241728 <= code <= 2 ^ 47 - 20
  /\ code mod 8 = 0
  /\ 0 <= e <= 1
  /\ 7241728 <= h <= 2 ^ 47 - 32
  /\ h mod 8 = 0
  /\ 140735332483136 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ wr_at asegs m h 32
  /\ fldA m (code + 8) 4 w
  /\ 0 <= w <= 2 ^ 32 - 1
  /\ fldA m (sp - 56) 8 fs5
  /\ fldA m (sp - 48) 8 fs4
  /\ fldA m (sp - 40) 8 fs3
  /\ fldA m (sp - 32) 8 fs2
  /\ fldA m (sp - 24) 8 fs1
  /\ fldA m (sp - 16) 8 fs0
  /\ fldA m (sp - 8) 8 fra
  /\ sh0 m (h + 4)
  /\ (b + 16 <= sp - 64 \/ sp <= b)
  /\ (code + 20 <= sp - 64 \/ sp <= code)
  /\ (h + 32 <= sp - 64 \/ sp <= h)
  /\ (h + 32 <= b \/ b + 16 <= h)
  /\ (h + 32 <= code \/ code + 20 <= h)
  /\ 0 <= r1 <= 2 ^ 64 - 1
  /\ 0 <= Z.land r1 18446744073692774655 <= 2 ^ 64 - 1
  /\ (h + 32 <= 2147446784 \/ 17594333495296 <= h).

Definition hg_h3x (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z),
    hg_h3x_pre R m b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra -> (Z.land r1 18446744073692774655 <> 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 260)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 680)) fc None M' (seg_rom asegs))
      /\ munch [((h + 4), (h + 8))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (h + 4) 4 r1
      /\ getr R' 1 = wz fra
      /\ getr R' 2 = wz sp
      /\ getr R' 8 = wz fs0
      /\ getr R' 9 = wz fs1
      /\ getr R' 10 = wz 18446744073709551612
      /\ getr R' 11 = wz (h + 4)
      /\ getr R' 18 = wz fs2
      /\ getr R' 19 = wz fs3
      /\ getr R' 20 = wz fs4
      /\ getr R' 21 = wz fs5
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma hg_h3x_ea2b4 : hg_h3x (959156).
Proof.
  intros R F fc m b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_HdrGetR.h3x_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) LbB_HdrGetR.h3x_sr R) by (unfold LbB_HdrGetR.h3x_E, LbB_HdrGetR.h3x_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_HdrGetR.h3x_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) m LbB_HdrGetR.h3x_A_knF) by (unfold LbB_HdrGetR.h3x_E; knowB).
  destruct (LbB_HdrGetR.h3x_A_run fx R m (seg_rom asegs) b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_HdrGetR.h3x_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_HdrGetR.h3x_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) in *. unfold LbB_HdrGetR.h3x_E in Ev.
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
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition hg_h3v_pre (R : bvmap 5 word) (m : mem) (b code e h sp r1 w : Z) : Prop :=
  getr R 2 = wz (sp - 64)
  /\ getr R 8 = wz b
  /\ getr R 9 = wz h
  /\ getr R 18 = wz e
  /\ getr R 19 = wz (-4)
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (sh b)
  /\ getr R 10 = wz r1
  /\ fldA m b 8 code
  /\ 7241728 <= b <= 2 ^ 47 - 16
  /\ b mod 8 = 0
  /\ 7241728 <= code <= 2 ^ 47 - 20
  /\ code mod 8 = 0
  /\ 0 <= e <= 1
  /\ 7241728 <= h <= 2 ^ 47 - 32
  /\ h mod 8 = 0
  /\ 140735332483136 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ wr_at asegs m h 32
  /\ fldA m (code + 8) 4 w
  /\ 0 <= w <= 2 ^ 32 - 1
  /\ 65536 <= r1 <= 67072
  /\ sh0 m (h + 4)
  /\ sh0 m b
  /\ sh0 m (code + 8)
  /\ (b + 16 <= sp - 64 \/ sp <= b)
  /\ (code + 20 <= sp - 64 \/ sp <= code)
  /\ (h + 32 <= sp - 64 \/ sp <= h)
  /\ (h + 32 <= b \/ b + 16 <= h)
  /\ (h + 32 <= code \/ code + 20 <= h)
  /\ 0 <= Z.land r1 18446744073692774655 <= 2 ^ 64 - 1
  /\ (h + 32 <= 2147446784 \/ 17594333495296 <= h).

Definition hg_h3v (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 w : Z),
    hg_h3v_pre R m b code e h sp r1 w -> (Z.land r1 18446744073692774655 = 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 260)) fc None m (seg_rom asegs)) (MS R' F (wz 1034240) fc None M' (seg_rom asegs))
      /\ munch [((h + 4), (h + 8))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (h + 4) 4 r1
      /\ getr R' 1 = wz (E + 380)
      /\ getr R' 2 = wz (sp - 64)
      /\ getr R' 8 = wz b
      /\ getr R' 9 = wz h
      /\ getr R' 11 = wz e
      /\ getr R' 18 = wz e
      /\ getr R' 19 = wz (-4)
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (sh b)
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma hg_h3v_ea2b4 : hg_h3v (959156).
Proof.
  intros R F fc m b code e h sp r1 w P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_HdrGetR.h3v_E R b code e h sp r1 w) LbB_HdrGetR.h3v_sr R) by (unfold LbB_HdrGetR.h3v_E, LbB_HdrGetR.h3v_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_HdrGetR.h3v_E R b code e h sp r1 w) m LbB_HdrGetR.h3v_A_knF) by (unfold LbB_HdrGetR.h3v_E; knowB).
  destruct (LbB_HdrGetR.h3v_A_run fx R m (seg_rom asegs) b code e h sp r1 w ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_HdrGetR.h3v_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_HdrGetR.h3v_E R b code e h sp r1 w) in *. unfold LbB_HdrGetR.h3v_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition hg_h3a_pre (R : bvmap 5 word) (m : mem) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z) : Prop :=
  getr R 2 = wz (sp - 64)
  /\ getr R 8 = wz b
  /\ getr R 9 = wz h
  /\ getr R 18 = wz e
  /\ getr R 19 = wz (-4)
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (sh b)
  /\ getr R 10 = wz r1
  /\ fldA m b 8 code
  /\ 7241728 <= b <= 2 ^ 47 - 16
  /\ b mod 8 = 0
  /\ 7241728 <= code <= 2 ^ 47 - 20
  /\ code mod 8 = 0
  /\ 0 <= e <= 1
  /\ 7241728 <= h <= 2 ^ 47 - 32
  /\ h mod 8 = 0
  /\ 140735332483136 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ wr_at asegs m h 32
  /\ fldA m (code + 8) 4 w
  /\ 0 <= w <= 2 ^ 32 - 1
  /\ fldA m (sp - 56) 8 fs5
  /\ fldA m (sp - 48) 8 fs4
  /\ fldA m (sp - 40) 8 fs3
  /\ fldA m (sp - 32) 8 fs2
  /\ fldA m (sp - 24) 8 fs1
  /\ fldA m (sp - 16) 8 fs0
  /\ fldA m (sp - 8) 8 fra
  /\ 0 <= r1 <= 65535
  /\ sh0 m (h + 4)
  /\ (b + 16 <= sp - 64 \/ sp <= b)
  /\ (code + 20 <= sp - 64 \/ sp <= code)
  /\ (h + 32 <= sp - 64 \/ sp <= h)
  /\ (h + 32 <= b \/ b + 16 <= h)
  /\ (h + 32 <= code \/ code + 20 <= h)
  /\ 0 <= Z.land r1 18446744073692774655 <= 2 ^ 64 - 1
  /\ (h + 32 <= 2147446784 \/ 17594333495296 <= h).

Definition hg_h3a (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z),
    hg_h3a_pre R m b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra -> (Z.land r1 18446744073692774655 = 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 260)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 680)) fc None M' (seg_rom asegs))
      /\ munch [((h + 4), (h + 8))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (h + 4) 4 r1
      /\ getr R' 1 = wz fra
      /\ getr R' 2 = wz sp
      /\ getr R' 8 = wz fs0
      /\ getr R' 9 = wz fs1
      /\ getr R' 10 = wz 18446744073709551612
      /\ getr R' 11 = wz 18446744073709550079
      /\ getr R' 18 = wz fs2
      /\ getr R' 19 = wz fs3
      /\ getr R' 20 = wz fs4
      /\ getr R' 21 = wz fs5
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma hg_h3a_ea2b4 : hg_h3a (959156).
Proof.
  intros R F fc m b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_HdrGetR.h3a_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) LbB_HdrGetR.h3a_sr R) by (unfold LbB_HdrGetR.h3a_E, LbB_HdrGetR.h3a_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_HdrGetR.h3a_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) m LbB_HdrGetR.h3a_A_knF) by (unfold LbB_HdrGetR.h3a_E; knowB).
  destruct (LbB_HdrGetR.h3a_A_run fx R m (seg_rom asegs) b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_HdrGetR.h3a_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_HdrGetR.h3a_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) in *. unfold LbB_HdrGetR.h3a_E in Ev.
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
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition hg_h3b_pre (R : bvmap 5 word) (m : mem) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z) : Prop :=
  getr R 2 = wz (sp - 64)
  /\ getr R 8 = wz b
  /\ getr R 9 = wz h
  /\ getr R 18 = wz e
  /\ getr R 19 = wz (-4)
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (sh b)
  /\ getr R 10 = wz r1
  /\ fldA m b 8 code
  /\ 7241728 <= b <= 2 ^ 47 - 16
  /\ b mod 8 = 0
  /\ 7241728 <= code <= 2 ^ 47 - 20
  /\ code mod 8 = 0
  /\ 0 <= e <= 1
  /\ 7241728 <= h <= 2 ^ 47 - 32
  /\ h mod 8 = 0
  /\ 140735332483136 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ wr_at asegs m h 32
  /\ fldA m (code + 8) 4 w
  /\ 0 <= w <= 2 ^ 32 - 1
  /\ fldA m (sp - 56) 8 fs5
  /\ fldA m (sp - 48) 8 fs4
  /\ fldA m (sp - 40) 8 fs3
  /\ fldA m (sp - 32) 8 fs2
  /\ fldA m (sp - 24) 8 fs1
  /\ fldA m (sp - 16) 8 fs0
  /\ fldA m (sp - 8) 8 fra
  /\ 67073 <= r1 <= 2 ^ 24 - 1
  /\ sh0 m (h + 4)
  /\ (b + 16 <= sp - 64 \/ sp <= b)
  /\ (code + 20 <= sp - 64 \/ sp <= code)
  /\ (h + 32 <= sp - 64 \/ sp <= h)
  /\ (h + 32 <= b \/ b + 16 <= h)
  /\ (h + 32 <= code \/ code + 20 <= h)
  /\ 0 <= Z.land r1 18446744073692774655 <= 2 ^ 64 - 1
  /\ (h + 32 <= 2147446784 \/ 17594333495296 <= h).

Definition hg_h3b (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra : Z),
    hg_h3b_pre R m b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra -> (Z.land r1 18446744073692774655 = 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 260)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 680)) fc None M' (seg_rom asegs))
      /\ munch [((h + 4), (h + 8))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (h + 4) 4 r1
      /\ getr R' 1 = wz fra
      /\ getr R' 2 = wz sp
      /\ getr R' 8 = wz fs0
      /\ getr R' 9 = wz fs1
      /\ getr R' 10 = wz 18446744073709551612
      /\ getr R' 11 = wz 18446744073709550079
      /\ getr R' 18 = wz fs2
      /\ getr R' 19 = wz fs3
      /\ getr R' 20 = wz fs4
      /\ getr R' 21 = wz fs5
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma hg_h3b_ea2b4 : hg_h3b (959156).
Proof.
  intros R F fc m b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_HdrGetR.h3b_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) LbB_HdrGetR.h3b_sr R) by (unfold LbB_HdrGetR.h3b_E, LbB_HdrGetR.h3b_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_HdrGetR.h3b_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) m LbB_HdrGetR.h3b_A_knF) by (unfold LbB_HdrGetR.h3b_E; knowB).
  destruct (LbB_HdrGetR.h3b_A_run fx R m (seg_rom asegs) b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_HdrGetR.h3b_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_HdrGetR.h3b_E R b code e h sp r1 w fs5 fs4 fs3 fs2 fs1 fs0 fra) in *. unfold LbB_HdrGetR.h3b_E in Ev.
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
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition hg_h4_pre (R : bvmap 5 word) (m : mem) (b code e h sp r1 w : Z) : Prop :=
  getr R 2 = wz (sp - 64)
  /\ getr R 8 = wz b
  /\ getr R 9 = wz h
  /\ getr R 18 = wz e
  /\ getr R 19 = wz (-4)
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (sh b)
  /\ getr R 10 = wz r1
  /\ fldA m b 8 code
  /\ 7241728 <= b <= 2 ^ 47 - 16
  /\ b mod 8 = 0
  /\ 7241728 <= code <= 2 ^ 47 - 20
  /\ code mod 8 = 0
  /\ 0 <= e <= 1
  /\ 7241728 <= h <= 2 ^ 47 - 32
  /\ h mod 8 = 0
  /\ 140735332483136 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ wr_at asegs m h 32
  /\ fldA m (code + 12) 4 w
  /\ 0 <= w <= 2 ^ 32 - 1
  /\ sh0 m (h + 8)
  /\ sh0 m b
  /\ sh0 m (code + 12)
  /\ (b + 16 <= sp - 64 \/ sp <= b)
  /\ (code + 20 <= sp - 64 \/ sp <= code)
  /\ (h + 32 <= sp - 64 \/ sp <= h)
  /\ (h + 32 <= b \/ b + 16 <= h)
  /\ (h + 32 <= code \/ code + 20 <= h)
  /\ (h + 32 <= 2147446784 \/ 17594333495296 <= h).

Definition hg_h4 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 w : Z),
    hg_h4_pre R m b code e h sp r1 w ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 380)) fc None m (seg_rom asegs)) (MS R' F (wz 1034240) fc None M' (seg_rom asegs))
      /\ munch [((h + 8), (h + 12))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (h + 8) 4 r1
      /\ getr R' 1 = wz (E + 468)
      /\ getr R' 2 = wz (sp - 64)
      /\ getr R' 8 = wz b
      /\ getr R' 9 = wz h
      /\ getr R' 11 = wz e
      /\ getr R' 12 = wz 0
      /\ getr R' 18 = wz e
      /\ getr R' 19 = wz (-4)
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (sh b)
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma hg_h4_ea2b4 : hg_h4 (959156).
Proof.
  intros R F fc m b code e h sp r1 w P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_HdrGetR.h4_E R b code e h sp r1 w) LbB_HdrGetR.h4_sr R) by (unfold LbB_HdrGetR.h4_E, LbB_HdrGetR.h4_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_HdrGetR.h4_E R b code e h sp r1 w) m LbB_HdrGetR.h4_A_knF) by (unfold LbB_HdrGetR.h4_E; knowB).
  destruct (LbB_HdrGetR.h4_A_run fx R m (seg_rom asegs) b code e h sp r1 w ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_HdrGetR.h4_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_HdrGetR.h4_E R b code e h sp r1 w) in *. unfold LbB_HdrGetR.h4_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition hg_h5_pre (R : bvmap 5 word) (m : mem) (b code e h sp r1 w : Z) : Prop :=
  getr R 2 = wz (sp - 64)
  /\ getr R 8 = wz b
  /\ getr R 9 = wz h
  /\ getr R 18 = wz e
  /\ getr R 19 = wz (-4)
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (sh b)
  /\ getr R 10 = wz r1
  /\ fldA m b 8 code
  /\ 7241728 <= b <= 2 ^ 47 - 16
  /\ b mod 8 = 0
  /\ 7241728 <= code <= 2 ^ 47 - 20
  /\ code mod 8 = 0
  /\ 0 <= e <= 1
  /\ 7241728 <= h <= 2 ^ 47 - 32
  /\ h mod 8 = 0
  /\ 140735332483136 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ wr_at asegs m h 32
  /\ fldA m (code + 16) 4 w
  /\ 0 <= w <= 2 ^ 32 - 1
  /\ shk m (code + 16) 4
  /\ sh0 m (h + 12)
  /\ sh0 m b
  /\ (b + 16 <= sp - 64 \/ sp <= b)
  /\ (code + 20 <= sp - 64 \/ sp <= code)
  /\ (h + 32 <= sp - 64 \/ sp <= h)
  /\ (h + 32 <= b \/ b + 16 <= h)
  /\ (h + 32 <= code \/ code + 20 <= h)
  /\ (h + 32 <= 2147446784 \/ 17594333495296 <= h).

Definition hg_h5 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 w : Z),
    hg_h5_pre R m b code e h sp r1 w ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 468)) fc None m (seg_rom asegs)) (MS R' F (wz 1034240) fc None M' (seg_rom asegs))
      /\ munch [((h + 12), (h + 16))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (h + 12) 4 r1
      /\ getr R' 1 = wz (E + 556)
      /\ getr R' 2 = wz (sp - 64)
      /\ getr R' 8 = wz b
      /\ getr R' 9 = wz h
      /\ getr R' 11 = wz e
      /\ getr R' 12 = wz 3
      /\ getr R' 18 = wz e
      /\ getr R' 19 = wz (-4)
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (sh b)
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma hg_h5_ea2b4 : hg_h5 (959156).
Proof.
  intros R F fc m b code e h sp r1 w P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_HdrGetR.h5_E R b code e h sp r1 w) LbB_HdrGetR.h5_sr R) by (unfold LbB_HdrGetR.h5_E, LbB_HdrGetR.h5_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_HdrGetR.h5_E R b code e h sp r1 w) m LbB_HdrGetR.h5_A_knF) by (unfold LbB_HdrGetR.h5_E; knowB).
  destruct (LbB_HdrGetR.h5_A_run fx R m (seg_rom asegs) b code e h sp r1 w ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_HdrGetR.h5_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_HdrGetR.h5_E R b code e h sp r1 w) in *. unfold LbB_HdrGetR.h5_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition hg_h5z_pre (R : bvmap 5 word) (m : mem) (b code e h sp r1 w : Z) : Prop :=
  getr R 2 = wz (sp - 64)
  /\ getr R 8 = wz b
  /\ getr R 9 = wz h
  /\ getr R 18 = wz e
  /\ getr R 19 = wz (-4)
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (sh b)
  /\ getr R 10 = wz r1
  /\ fldA m b 8 code
  /\ 7241728 <= b <= 2 ^ 47 - 16
  /\ b mod 8 = 0
  /\ 7241728 <= code <= 2 ^ 47 - 20
  /\ code mod 8 = 0
  /\ 0 <= e <= 1
  /\ 7241728 <= h <= 2 ^ 47 - 32
  /\ h mod 8 = 0
  /\ 140735332483136 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ wr_at asegs m h 32
  /\ fldA m (code + 16) 4 w
  /\ 0 <= w <= 2 ^ 32 - 1
  /\ sh0 m (h + 12)
  /\ sh0 m b
  /\ sh0 m (code + 16)
  /\ (b + 16 <= sp - 64 \/ sp <= b)
  /\ (code + 20 <= sp - 64 \/ sp <= code)
  /\ (h + 32 <= sp - 64 \/ sp <= h)
  /\ (h + 32 <= b \/ b + 16 <= h)
  /\ (h + 32 <= code \/ code + 20 <= h)
  /\ (h + 32 <= 2147446784 \/ 17594333495296 <= h).

Definition hg_h5z (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 w : Z),
    hg_h5z_pre R m b code e h sp r1 w ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 468)) fc None m (seg_rom asegs)) (MS R' F (wz 1034240) fc None M' (seg_rom asegs))
      /\ munch [((h + 12), (h + 16))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (h + 12) 4 r1
      /\ getr R' 1 = wz (E + 556)
      /\ getr R' 2 = wz (sp - 64)
      /\ getr R' 8 = wz b
      /\ getr R' 9 = wz h
      /\ getr R' 11 = wz e
      /\ getr R' 12 = wz 0
      /\ getr R' 18 = wz e
      /\ getr R' 19 = wz (-4)
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (sh b)
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma hg_h5z_ea2b4 : hg_h5z (959156).
Proof.
  intros R F fc m b code e h sp r1 w P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_HdrGetR.h5z_E R b code e h sp r1 w) LbB_HdrGetR.h5z_sr R) by (unfold LbB_HdrGetR.h5z_E, LbB_HdrGetR.h5z_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_HdrGetR.h5z_E R b code e h sp r1 w) m LbB_HdrGetR.h5z_A_knF) by (unfold LbB_HdrGetR.h5z_E; knowB).
  destruct (LbB_HdrGetR.h5z_A_run fx R m (seg_rom asegs) b code e h sp r1 w ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_HdrGetR.h5z_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_HdrGetR.h5z_E R b code e h sp r1 w) in *. unfold LbB_HdrGetR.h5z_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition hg_h6_pre (R : bvmap 5 word) (m : mem) (b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra : Z) : Prop :=
  getr R 2 = wz (sp - 64)
  /\ getr R 8 = wz b
  /\ getr R 9 = wz h
  /\ getr R 18 = wz e
  /\ getr R 19 = wz (-4)
  /\ getr R 20 = wz ASHADOW_BASE
  /\ getr R 21 = wz (sh b)
  /\ getr R 10 = wz r1
  /\ fldA m b 8 code
  /\ 7241728 <= b <= 2 ^ 47 - 16
  /\ b mod 8 = 0
  /\ 7241728 <= code <= 2 ^ 47 - 20
  /\ code mod 8 = 0
  /\ 0 <= e <= 1
  /\ 7241728 <= h <= 2 ^ 47 - 32
  /\ h mod 8 = 0
  /\ 140735332483136 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ wr_at asegs m h 32
  /\ fldA m (sp - 56) 8 fs5
  /\ fldA m (sp - 48) 8 fs4
  /\ fldA m (sp - 40) 8 fs3
  /\ fldA m (sp - 32) 8 fs2
  /\ fldA m (sp - 24) 8 fs1
  /\ fldA m (sp - 16) 8 fs0
  /\ fldA m (sp - 8) 8 fra
  /\ sh0 m (h + 16)
  /\ sh0 m b
  /\ sh0 m (h + 24)
  /\ (b + 16 <= sp - 64 \/ sp <= b)
  /\ (code + 20 <= sp - 64 \/ sp <= code)
  /\ (h + 32 <= sp - 64 \/ sp <= h)
  /\ (h + 32 <= b \/ b + 16 <= h)
  /\ (h + 32 <= code \/ code + 20 <= h)
  /\ (h + 32 <= 2147446784 \/ 17594333495296 <= h).

Definition hg_h6 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra : Z),
    hg_h6_pre R m b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 556)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 680)) fc None M' (seg_rom asegs))
      /\ munch [((h + 16), (h + 32))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (h + 24) 8 (code + 20)
      /\ fldA M' (h + 16) 4 r1
      /\ getr R' 1 = wz fra
      /\ getr R' 2 = wz sp
      /\ getr R' 8 = wz fs0
      /\ getr R' 9 = wz fs1
      /\ getr R' 10 = wz 0
      /\ getr R' 11 = wz (code + 20)
      /\ getr R' 12 = wz 0
      /\ getr R' 18 = wz fs2
      /\ getr R' 19 = wz fs3
      /\ getr R' 20 = wz fs4
      /\ getr R' 21 = wz fs5
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma hg_h6_ea2b4 : hg_h6 (959156).
Proof.
  intros R F fc m b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_HdrGetR.h6_E R b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra) LbB_HdrGetR.h6_sr R) by (unfold LbB_HdrGetR.h6_E, LbB_HdrGetR.h6_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_HdrGetR.h6_E R b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra) m LbB_HdrGetR.h6_A_knF) by (unfold LbB_HdrGetR.h6_E; knowB).
  destruct (LbB_HdrGetR.h6_A_run fx R m (seg_rom asegs) b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_HdrGetR.h6_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_HdrGetR.h6_E R b code e h sp r1 fs5 fs4 fs3 fs2 fs1 fs0 fra) in *. unfold LbB_HdrGetR.h6_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.
