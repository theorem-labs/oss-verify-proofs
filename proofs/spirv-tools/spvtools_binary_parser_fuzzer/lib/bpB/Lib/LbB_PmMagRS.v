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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmMagR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition hdrR_a2_pre (R : bvmap 5 word) (m : mem) (q sp words n fp : Z) : Prop :=
  getr R 2 = wz sp
  /\ getr R 9 = wz fp
  /\ getr R 18 = wz ((32 * q) + 3456)
  /\ getr R 19 = wz ((4 * q) + ASHADOW_BASE)
  /\ getr R 20 = wz (32 * q)
  /\ getr R 22 = wz ((32 * q) + 3504)
  /\ fldA m (32 * q + 3504) 8 words
  /\ fldA m (32 * q + 3512) 8 n
  /\ fldA m (fp + 40) 8 ASHADOW_BASE
  /\ wr_at asegs m (4 * q + 2147451096) 2
  /\ 2 ^ 45 + 16 <= sp <= 2 ^ 47
  /\ 2 ^ 45 <= fp <= 2 ^ 47
  /\ 227200 <= q <= 2 ^ 42
  /\ 16 <= words <= 2 ^ 47
  /\ 5 <= n <= 2 ^ 24
  /\ 2 ^ 45 + 16 <= sp
  /\ sp <= 2 ^ 47
  /\ 0x6e6000 + 0x9000 <= 32 * q
  /\ 32 * q + 4096 <= 2 ^ 47
  /\ (32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q).

Definition hdrR_a2_post (E : Z) (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp words n fp : Z) (R' : bvmap 5 word) (M' : mem) : Prop :=
  CatSim.msteps asegs (MS R F (wz (E + 3384)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 4784)) fc None M' (seg_rom asegs))
  /\ munch [((4 * q + 2147451096), (4 * q + 2147451098))] m M'
  /\ wmono asegs m M'
  /\ fldA M' (4 * q + 2147451097) 1 0
  /\ fldA M' (4 * q + 2147451096) 1 0
  /\ getr R' 2 = wz sp
  /\ getr R' 9 = wz fp
  /\ getr R' 10 = wz words
  /\ getr R' 11 = wz n
  /\ getr R' 12 = wz 5
  /\ getr R' 18 = wz ((32 * q) + 3456)
  /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE)
  /\ getr R' 20 = wz (32 * q)
  /\ getr R' 22 = wz ((32 * q) + 3504)
  /\ getr R' 25 = wz ((32 * q) + 1728)
  /\ getr R' 27 = wz ASHADOW_BASE
  /\ (forall r, In r [1; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 21; 23; 24; 26; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Definition hdrR_a2 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp words n fp : Z),
    hdrR_a2_pre R m q sp words n fp ->
    exists R' M', hdrR_a2_post E R F fc m q sp words n fp R' M'.

Lemma hdrR_a2_bp : hdrR_a2 (0xea7c4).
Proof.
  intros R F fc m q sp words n fp P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmMagR.ha_E R q sp words n fp) LbB_PmMagR.ha_sr R) by (unfold LbB_PmMagR.ha_E, LbB_PmMagR.ha_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmMagR.ha_E R q sp words n fp) m LbB_PmMagR.ha_G_knF) by (unfold LbB_PmMagR.ha_E; knowB).
  destruct (LbB_PmMagR.ha_G_run fx R m (seg_rom asegs) q sp words n fp ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmMagR.ha_G_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmMagR.ha_E R q sp words n fp) in *. unfold LbB_PmMagR.ha_E in Ev.
  rw_exB Hms. unfold hdrR_a2_post.
  split; [exact Hms|].
  split; [munchB_at [0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [rrwB HR' (2%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  split; [rrwB HR' (27%bv : reg); regB|].
  keptB HR HR' ([1; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 21; 23; 24; 26; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition hdrR_mg_pre (R : bvmap 5 word) (m : mem) (q sp words n x : Z) : Prop :=
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
  /\ wr_at asegs m (32 * q + 3544) 4
  /\ wr_at asegs m (32 * q + 3548) 1
  /\ fldA m (4 * q + 2147451096) 1 0
  /\ fldA m (4 * q + 2147451097) 1 0
  /\ fldA m (4 * q + 2147451323) 1 0
  /\ wr_at asegs m (sp - 16) 16
  /\ 2 ^ 45 + 16 <= sp <= 2 ^ 47
  /\ sp mod 16 = 0
  /\ 227200 <= q <= 2 ^ 42
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

Definition hdrR_mgL_post (E : Z) (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp words n x : Z) (R' : bvmap 5 word) (M' : mem) : Prop :=
  CatSim.msteps asegs (MS R F (wz (E + 4784)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 5632)) fc None M' (seg_rom asegs))
  /\ munch [((32 * q + 1728), (32 * q + 1744)); ((32 * q + 3544), (32 * q + 3549)); ((sp - 8), sp)] m M'
  /\ wmono asegs m M'
  /\ fldA M' (32 * q + 3548) 1 0
  /\ fldA M' (32 * q + 3544) 4 0
  /\ fldA M' (sp - 8) 8 (E + 4808)
  /\ fldA M' (32 * q + 1736) 8 n
  /\ fldA M' (32 * q + 1728) 8 words
  /\ getr R' 1 = wz (E + 5624)
  /\ getr R' 2 = wz sp
  /\ getr R' 10 = wz 0
  /\ getr R' 11 = wz ((32 * q) + 3544)
  /\ getr R' 12 = wz 0
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

Definition hdrR_mgL (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp words n x : Z),
    hdrR_mg_pre R m q sp words n x -> (x mod 256 = 3) -> ((x / 256) mod 256 = 2) -> ((x / 65536) mod 256 = 35) -> (x / 16777216 = 7) ->
    exists R' M', hdrR_mgL_post E R F fc m q sp words n x R' M'.

Lemma hdrR_mgL_bp : hdrR_mgL (0xea7c4).
Proof.
  intros R F fc m q sp words n x P Q0 Q1 Q2 Q3.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmMagR.mg_E R q sp words n x) LbB_PmMagR.mg_sr R) by (unfold LbB_PmMagR.mg_E, LbB_PmMagR.mg_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmMagR.mg_E R q sp words n x) m LbB_PmMagR.mg_L_knF) by (unfold LbB_PmMagR.mg_E; knowB).
  destruct (LbB_PmMagR.mg_L_run fx R m (seg_rom asegs) q sp words n x ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmMagR.mg_L_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmMagR.mg_E R q sp words n x) in *. unfold LbB_PmMagR.mg_E in Ev.
  rw_exB Hms. unfold hdrR_mgL_post.
  split; [exact Hms|].
  split; [munchB_at [1; 1; 2; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fld_postB_at 3%nat|].
  split; [fld_postB_at 4%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
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
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition hdrR_mgB_post (E : Z) (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp words n x : Z) (R' : bvmap 5 word) (M' : mem) : Prop :=
  CatSim.msteps asegs (MS R F (wz (E + 4784)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 5632)) fc None M' (seg_rom asegs))
  /\ munch [((32 * q + 1728), (32 * q + 1744)); ((32 * q + 3544), (32 * q + 3549)); ((sp - 8), sp)] m M'
  /\ wmono asegs m M'
  /\ fldA M' (32 * q + 3548) 1 1
  /\ fldA M' (32 * q + 3544) 4 1
  /\ fldA M' (sp - 8) 8 (E + 4808)
  /\ fldA M' (32 * q + 1736) 8 n
  /\ fldA M' (32 * q + 1728) 8 words
  /\ getr R' 1 = wz (E + 5624)
  /\ getr R' 2 = wz sp
  /\ getr R' 10 = wz 1
  /\ getr R' 11 = wz ((32 * q) + 3544)
  /\ getr R' 12 = wz 1
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

Definition hdrR_mgB (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (q sp words n x : Z),
    hdrR_mg_pre R m q sp words n x -> (x mod 256 = 7) -> ((x / 256) mod 256 = 35) -> ((x / 65536) mod 256 = 2) -> (x / 16777216 = 3) ->
    exists R' M', hdrR_mgB_post E R F fc m q sp words n x R' M'.

Lemma hdrR_mgB_bp : hdrR_mgB (0xea7c4).
Proof.
  intros R F fc m q sp words n x P Q0 Q1 Q2 Q3.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31 & P32 & P33 & P34). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmMagR.mg_E R q sp words n x) LbB_PmMagR.mg_sr R) by (unfold LbB_PmMagR.mg_E, LbB_PmMagR.mg_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmMagR.mg_E R q sp words n x) m LbB_PmMagR.mg_B_knF) by (unfold LbB_PmMagR.mg_E; knowB).
  destruct (LbB_PmMagR.mg_B_run fx R m (seg_rom asegs) q sp words n x ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmMagR.mg_B_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmMagR.mg_E R q sp words n x) in *. unfold LbB_PmMagR.mg_E in Ev.
  rw_exB Hms. unfold hdrR_mgB_post.
  split; [exact Hms|].
  split; [munchB_at [1; 1; 2; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  split; [fld_postB_at 1%nat|].
  split; [fld_postB_at 2%nat|].
  split; [fld_postB_at 3%nat|].
  split; [fld_postB_at 4%nat|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (2%bv : reg); regB|].
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
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.
