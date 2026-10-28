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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_WdMMR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition wd_mm0_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 22 = wz (ff + 3504)
  /\ getr R 18 = wz (ff + 3456)
  /\ fldA m (ff + 3504) 8 0
  /\ 1048576 <= ff
  /\ ff + 4096 <= 2 ^ 47.

Definition wd_mm0 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_mm0_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 3384)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 4112)) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 10 = wz 0
      /\ getr R' 18 = wz (ff + 3456)
      /\ getr R' 22 = wz (ff + 3504)
      /\ (forall r, In r [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_mm0_ea7c4 : wd_mm0 (0xea7c4).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1 & P2 & P3 & P4). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdMMR.mm0_E R ff) LbB_WdMMR.mm0_sr R) by (unfold LbB_WdMMR.mm0_E, LbB_WdMMR.mm0_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdMMR.mm0_E R ff) m LbB_WdMMR.mm0_A_knF) by (unfold LbB_WdMMR.mm0_E; knowB).
  destruct (LbB_WdMMR.mm0_A_run fx R m (seg_rom asegs) ff ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdMMR.mm0_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdMMR.mm0_E R ff) in *. unfold LbB_WdMMR.mm0_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  keptB HR HR' ([1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_mm1_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 20 = wz ff
  /\ getr R 19 = wz (sh ff)
  /\ wr_at asegs m (ff / 8 + 2147450880) 512
  /\ 1048576 <= ff
  /\ ff + 4096 <= 2 ^ 47.

Definition wd_mm1 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_mm1_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 4112)) fc None m (seg_rom asegs)) (MS R' F (wz AASAN_MEMSET) fc None M' (seg_rom asegs))
      /\ munch [((ff / 8 + 2147450884), (ff / 8 + 2147450887)); ((ff / 8 + 2147450900), (ff / 8 + 2147450903)); ((ff / 8 + 2147450980), (ff / 8 + 2147451030))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (ff / 8 + 2147450902) 1 0
      /\ fldA M' (ff / 8 + 2147450901) 1 0
      /\ fldA M' (ff / 8 + 2147450900) 1 0
      /\ fldA M' (ff / 8 + 2147450886) 1 0
      /\ fldA M' (ff / 8 + 2147450885) 1 0
      /\ fldA M' (ff / 8 + 2147450884) 1 0
      /\ fldA M' (ff / 8 + 2147451029) 1 0
      /\ fldA M' (ff / 8 + 2147451028) 1 0
      /\ fldA M' (ff / 8 + 2147451023) 1 0
      /\ fldA M' (ff / 8 + 2147451022) 1 0
      /\ fldA M' (ff / 8 + 2147451021) 1 0
      /\ fldA M' (ff / 8 + 2147451020) 1 0
      /\ fldA M' (ff / 8 + 2147451027) 1 0
      /\ fldA M' (ff / 8 + 2147451026) 1 0
      /\ fldA M' (ff / 8 + 2147451025) 1 0
      /\ fldA M' (ff / 8 + 2147451024) 1 0
      /\ fldA M' (ff / 8 + 2147451015) 1 0
      /\ fldA M' (ff / 8 + 2147451014) 1 0
      /\ fldA M' (ff / 8 + 2147451013) 1 0
      /\ fldA M' (ff / 8 + 2147451012) 1 0
      /\ fldA M' (ff / 8 + 2147451019) 1 0
      /\ fldA M' (ff / 8 + 2147451018) 1 0
      /\ fldA M' (ff / 8 + 2147451017) 1 0
      /\ fldA M' (ff / 8 + 2147451016) 1 0
      /\ fldA M' (ff / 8 + 2147451007) 1 0
      /\ fldA M' (ff / 8 + 2147451006) 1 0
      /\ fldA M' (ff / 8 + 2147451005) 1 0
      /\ fldA M' (ff / 8 + 2147451004) 1 0
      /\ fldA M' (ff / 8 + 2147451011) 1 0
      /\ fldA M' (ff / 8 + 2147451010) 1 0
      /\ fldA M' (ff / 8 + 2147451009) 1 0
      /\ fldA M' (ff / 8 + 2147451008) 1 0
      /\ fldA M' (ff / 8 + 2147450999) 1 0
      /\ fldA M' (ff / 8 + 2147450998) 1 0
      /\ fldA M' (ff / 8 + 2147450997) 1 0
      /\ fldA M' (ff / 8 + 2147450996) 1 0
      /\ fldA M' (ff / 8 + 2147451003) 1 0
      /\ fldA M' (ff / 8 + 2147451002) 1 0
      /\ fldA M' (ff / 8 + 2147451001) 1 0
      /\ fldA M' (ff / 8 + 2147451000) 1 0
      /\ fldA M' (ff / 8 + 2147450991) 1 0
      /\ fldA M' (ff / 8 + 2147450990) 1 0
      /\ fldA M' (ff / 8 + 2147450989) 1 0
      /\ fldA M' (ff / 8 + 2147450988) 1 0
      /\ fldA M' (ff / 8 + 2147450995) 1 0
      /\ fldA M' (ff / 8 + 2147450994) 1 0
      /\ fldA M' (ff / 8 + 2147450993) 1 0
      /\ fldA M' (ff / 8 + 2147450992) 1 0
      /\ fldA M' (ff / 8 + 2147450983) 1 0
      /\ fldA M' (ff / 8 + 2147450982) 1 0
      /\ fldA M' (ff / 8 + 2147450981) 1 0
      /\ fldA M' (ff / 8 + 2147450980) 1 0
      /\ fldA M' (ff / 8 + 2147450987) 1 0
      /\ fldA M' (ff / 8 + 2147450986) 1 0
      /\ fldA M' (ff / 8 + 2147450985) 1 0
      /\ fldA M' (ff / 8 + 2147450984) 1 0
      /\ getr R' 1 = wz (E + 4356)
      /\ getr R' 10 = wz (ff + 32)
      /\ getr R' 11 = wz 0
      /\ getr R' 12 = wz 16
      /\ getr R' 19 = wz (sh ff)
      /\ getr R' 20 = wz ff
      /\ getr R' 24 = wz (ff + 32)
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_mm1_ea7c4 : wd_mm1 (0xea7c4).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1 & P2 & P3 & P4). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdMMR.mm1_E R ff) LbB_WdMMR.mm1_sr R) by (unfold LbB_WdMMR.mm1_E, LbB_WdMMR.mm1_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdMMR.mm1_E R ff) m LbB_WdMMR.mm1_A_knF) by (unfold LbB_WdMMR.mm1_E; knowB).
  destruct (LbB_WdMMR.mm1_A_run fx R m (seg_rom asegs) ff ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdMMR.mm1_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdMMR.mm1_E R ff) in *. unfold LbB_WdMMR.mm1_E in Ev.
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
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (20%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  keptB HR HR' ([2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_mm2_pre (R : bvmap 5 word) (m : mem) (ff S1 cons pos mb : Z) : Prop :=
  getr R 18 = wz (ff + 3456)
  /\ getr R 24 = wz (ff + 32)
  /\ getr R 9 = wz S1
  /\ getr R 20 = wz ff
  /\ getr R 19 = wz (sh ff)
  /\ fldA m (ff + 3536) 8 pos
  /\ fldA m (ff + 3464) 8 cons
  /\ fldA m (S1 + 40) 8 mb
  /\ cons mod 16 = 0
  /\ 1 <= cons <= 2 ^ 47
  /\ wr_at asegs m ff 4096
  /\ wr_at asegs m (ff / 8 + 2147450880) 512
  /\ (ff + 4096 <= S1 \/ S1 + 192 <= ff)
  /\ ((ff / 8 + 2147450880) + 512 <= ff \/ ff + 4096 <= (ff / 8 + 2147450880))
  /\ 1048576 <= ff
  /\ ff + 4096 <= 2 ^ 47
  /\ 2 ^ 45 <= S1
  /\ S1 + 192 <= 2 ^ 47.

Definition wd_mm2 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff S1 cons pos mb : Z),
    wd_mm2_pre R m ff S1 cons pos mb ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 4356)) fc None m (seg_rom asegs)) (MS R' F (wz 1010964) fc None M' (seg_rom asegs))
      /\ munch [((ff + 48), (ff + 56)); ((ff + 96), (ff + 98)); ((ff + 160), (ff + 162)); ((ff / 8 + 2147450892), (ff / 8 + 2147450895))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (ff + 160) 2 0
      /\ fldA M' (ff + 96) 2 0
      /\ fldA M' (ff / 8 + 2147450894) 1 0
      /\ fldA M' (ff / 8 + 2147450893) 1 0
      /\ fldA M' (ff / 8 + 2147450892) 1 0
      /\ fldA M' (ff + 48) 8 pos
      /\ getr R' 1 = wz (E + 4440)
      /\ getr R' 9 = wz S1
      /\ getr R' 10 = wz (ff + 800)
      /\ getr R' 11 = wz (ff + 32)
      /\ getr R' 12 = wz cons
      /\ getr R' 13 = wz (ff + 96)
      /\ getr R' 14 = wz 18446744073709551612
      /\ getr R' 15 = wz (ff + 160)
      /\ getr R' 18 = wz (ff + 800)
      /\ getr R' 19 = wz (sh ff)
      /\ getr R' 20 = wz ff
      /\ getr R' 24 = wz (ff + 32)
      /\ getr R' 25 = wz (ff + 96)
      /\ getr R' 26 = wz (ff + 160)
      /\ getr R' 27 = wz mb
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 16; 17; 21; 22; 23; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_mm2_ea7c4 : wd_mm2 (0xea7c4).
Proof.
  intros R F fc m ff S1 cons pos mb P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdMMR.mm2_E R ff S1 cons pos mb) LbB_WdMMR.mm2_sr R) by (unfold LbB_WdMMR.mm2_E, LbB_WdMMR.mm2_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdMMR.mm2_E R ff S1 cons pos mb) m LbB_WdMMR.mm2_A_knF) by (unfold LbB_WdMMR.mm2_E; knowB).
  destruct (LbB_WdMMR.mm2_A_run fx R m (seg_rom asegs) ff S1 cons pos mb ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdMMR.mm2_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdMMR.mm2_E R ff S1 cons pos mb) in *. unfold LbB_WdMMR.mm2_E in Ev.
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
  split; [rrwB HR' (9%bv : reg); regB|].
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
  split; [rrwB HR' (27%bv : reg); regB|].
  keptB HR HR' ([2; 3; 4; 5; 6; 7; 8; 16; 17; 21; 22; 23; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_mm3_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 26 = wz (ff + 160)
  /\ getr R 25 = wz (ff + 96)
  /\ getr R 19 = wz (sh ff)
  /\ getr R 18 = wz (ff + 800)
  /\ fldA m (ff + 160) 1 0
  /\ fldA m (ff + 96) 1 0
  /\ wr_at asegs m (ff / 8 + 2147450880) 512
  /\ 1048576 <= ff
  /\ ff + 4096 <= 2 ^ 47.

Definition wd_mm3 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_mm3_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 4440)) fc None m (seg_rom asegs)) (MS R' F (wz 1008288) fc None M' (seg_rom asegs))
      /\ munch [((ff / 8 + 2147450884), (ff / 8 + 2147450887)); ((ff / 8 + 2147450892), (ff / 8 + 2147450895)); ((ff / 8 + 2147450900), (ff / 8 + 2147450903))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (ff / 8 + 2147450902) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450901) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450900) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450894) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450893) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450892) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450886) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450885) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450884) 1 18446744073709551608
      /\ getr R' 1 = wz (E + 4556)
      /\ getr R' 10 = wz (ff + 800)
      /\ getr R' 11 = wz 147744
      /\ getr R' 12 = wz 15
      /\ getr R' 18 = wz (ff + 800)
      /\ getr R' 19 = wz (sh ff)
      /\ getr R' 21 = wz 18446744073709551608
      /\ getr R' 25 = wz (ff + 96)
      /\ getr R' 26 = wz (ff + 160)
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 20; 22; 23; 24; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_mm3_ea7c4 : wd_mm3 (0xea7c4).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdMMR.mm3_E R ff) LbB_WdMMR.mm3_sr R) by (unfold LbB_WdMMR.mm3_E, LbB_WdMMR.mm3_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdMMR.mm3_E R ff) m LbB_WdMMR.mm3_A_knF) by (unfold LbB_WdMMR.mm3_E; knowB).
  destruct (LbB_WdMMR.mm3_A_run fx R m (seg_rom asegs) ff ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdMMR.mm3_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdMMR.mm3_E R ff) in *. unfold LbB_WdMMR.mm3_E in Ev.
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
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  split; [rrwB HR' (26%bv : reg); regB|].
  keptB HR HR' ([2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 20; 22; 23; 24; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_mm4_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 18 = wz (ff + 800)
  /\ fldA m (ff + 1160) 4 4294967292
  /\ 1048576 <= ff
  /\ ff + 4096 <= 2 ^ 47.

Definition wd_mm4 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_mm4_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 4556)) fc None m (seg_rom asegs)) (MS R' F (wz 1034672) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz (E + 4568)
      /\ getr R' 10 = wz (ff + 800)
      /\ getr R' 18 = wz (ff + 800)
      /\ getr R' 24 = wz 18446744073709551612
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_mm4_ea7c4 : wd_mm4 (0xea7c4).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1 & P2 & P3). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdMMR.mm4_E R ff) LbB_WdMMR.mm4_sr R) by (unfold LbB_WdMMR.mm4_E, LbB_WdMMR.mm4_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdMMR.mm4_E R ff) m LbB_WdMMR.mm4_A_knF) by (unfold LbB_WdMMR.mm4_E; knowB).
  destruct (LbB_WdMMR.mm4_A_run fx R m (seg_rom asegs) ff ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdMMR.mm4_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdMMR.mm4_E R ff) in *. unfold LbB_WdMMR.mm4_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  keptB HR HR' ([2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_mm5_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 21 = wz 18446744073709551608
  /\ getr R 19 = wz (sh ff)
  /\ wr_at asegs m (ff / 8 + 2147450880) 512
  /\ 1048576 <= ff
  /\ ff + 4096 <= 2 ^ 47.

Definition wd_mm5 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_mm5_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 4568)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 6460)) fc None M' (seg_rom asegs))
      /\ munch [((ff / 8 + 2147450980), (ff / 8 + 2147451030))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (ff / 8 + 2147451029) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451028) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451023) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451022) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451021) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451020) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451027) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451026) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451025) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451024) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451015) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451014) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451013) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451012) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451019) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451018) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451017) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451016) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451007) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451006) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451005) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451004) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451011) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451010) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451009) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451008) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450999) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450998) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450997) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450996) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451003) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451002) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451001) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451000) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450991) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450990) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450989) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450988) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450995) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450994) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450993) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450992) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450983) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450982) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450981) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450980) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450987) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450986) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450985) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450984) 1 18446744073709551608
      /\ getr R' 19 = wz (sh ff)
      /\ getr R' 21 = wz 18446744073709551608
      /\ (forall r, In r [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_mm5_ea7c4 : wd_mm5 (0xea7c4).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1 & P2 & P3 & P4). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdMMR.mm5_E R ff) LbB_WdMMR.mm5_sr R) by (unfold LbB_WdMMR.mm5_E, LbB_WdMMR.mm5_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdMMR.mm5_E R ff) m LbB_WdMMR.mm5_A_knF) by (unfold LbB_WdMMR.mm5_E; knowB).
  destruct (LbB_WdMMR.mm5_A_run fx R m (seg_rom asegs) ff ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdMMR.mm5_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdMMR.mm5_E R ff) in *. unfold LbB_WdMMR.mm5_E in Ev.
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
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  keptB HR HR' ([1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.
