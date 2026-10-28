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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmHTR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition ht_a_pre (R : bvmap 5 word) (m : mem) (p sh fb b e h : Z) : Prop :=
  getr R 9 = wz fb
  /\ getr R 18 = wz p
  /\ getr R 19 = wz sh
  /\ getr R 25 = wz b
  /\ fldA m (p + 88) 4 e
  /\ fldA m (fb + 48) 8 h
  /\ ((sh + 278) + 4 <= (p + 88) \/ (p + 88) + 4 <= (sh + 278))
  /\ ((sh + 278) + 4 <= (fb + 48) \/ (fb + 48) + 8 <= (sh + 278))
  /\ wr_at asegs m (sh + 278) 4
  /\ 0 <= p
  /\ p + 96 <= 2 ^ 47
  /\ 0 <= sh
  /\ sh + 288 <= 2 ^ 47
  /\ 0 <= fb
  /\ fb + 64 <= 2 ^ 47
  /\ 0 <= b < 2 ^ 64
  /\ 0 <= e <= 1
  /\ 0 <= h < 2 ^ 64.

Definition ht_a (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (p sh fb b e h : Z),
    ht_a_pre R m p sh fb b e h ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 5632)) fc None m (seg_rom asegs)) (MS R' F (wz 959156) fc None M' (seg_rom asegs))
      /\ munch [((sh + 278), (sh + 282))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (sh + 281) 1 0
      /\ fldA M' (sh + 280) 1 0
      /\ fldA M' (sh + 279) 1 0
      /\ fldA M' (sh + 278) 1 0
      /\ getr R' 1 = wz (E + 5668)
      /\ getr R' 9 = wz fb
      /\ getr R' 10 = wz b
      /\ getr R' 11 = wz e
      /\ getr R' 12 = wz h
      /\ getr R' 18 = wz p
      /\ getr R' 19 = wz sh
      /\ getr R' 25 = wz b
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma ht_a_bp : ht_a (0xea7c4).
Proof.
  intros R F fc m p sh fb b e h P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmHTR.hta_E R p sh fb b e h) LbB_PmHTR.hta_sr R) by (unfold LbB_PmHTR.hta_E, LbB_PmHTR.hta_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmHTR.hta_E R p sh fb b e h) m LbB_PmHTR.hta_A_knF) by (unfold LbB_PmHTR.hta_E; knowB).
  destruct (LbB_PmHTR.hta_A_run fx R m (seg_rom asegs) p sh fb b e h ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmHTR.hta_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmHTR.hta_E R p sh fb b e h) in *. unfold LbB_PmHTR.hta_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fld_postB_at 3%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); evs; apply ext_sx4_small; lia|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition ht_z_pre (R : bvmap 5 word) (m : mem) (p : Z) : Prop :=
  getr R 10 = wz 0
  /\ getr R 18 = wz p
  /\ fldA m (p + 24) 8 0
  /\ 0 <= p
  /\ p + 96 <= 2 ^ 47.

Definition ht_z (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (p : Z),
    ht_z_pre R m p ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 5668)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 6384)) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 10 = wz 0
      /\ getr R' 17 = wz 0
      /\ getr R' 18 = wz p
      /\ (forall r, In r [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma ht_z_bp : ht_z (0xea7c4).
Proof.
  intros R F fc m p P.
  destruct P as (P0 & P1 & P2 & P3 & P4). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmHTR.htz_E R p) LbB_PmHTR.htz_sr R) by (unfold LbB_PmHTR.htz_E, LbB_PmHTR.htz_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmHTR.htz_E R p) m LbB_PmHTR.htz_Z_knF) by (unfold LbB_PmHTR.htz_E; knowB).
  destruct (LbB_PmHTR.htz_Z_run fx R m (seg_rom asegs) p ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmHTR.htz_Z_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmHTR.htz_E R p) in *. unfold LbB_PmHTR.htz_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (17%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  keptB HR HR' ([1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition ht_n_pre (R : bvmap 5 word) (m : mem) (p : Z) : Prop :=
  getr R 10 = wz (-4)
  /\ getr R 18 = wz p
  /\ 0 <= p
  /\ p + 96 <= 2 ^ 47.

Definition ht_n (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (p : Z),
    ht_n_pre R m p ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 5668)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 5672)) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 10 = wz (-4)
      /\ getr R' 18 = wz p
      /\ (forall r, In r [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma ht_n_bp : ht_n (0xea7c4).
Proof.
  intros R F fc m p P.
  destruct P as (P0 & P1 & P2 & P3). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmHTR.htn_E R p) LbB_PmHTR.htn_sr R) by (unfold LbB_PmHTR.htn_E, LbB_PmHTR.htn_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmHTR.htn_E R p) m LbB_PmHTR.htn_N_knF) by (unfold LbB_PmHTR.htn_E; knowB).
  destruct (LbB_PmHTR.htn_N_run fx R m (seg_rom asegs) p ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmHTR.htn_N_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmHTR.htn_E R p) in *. unfold LbB_PmHTR.htn_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  keptB HR HR' ([1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.
