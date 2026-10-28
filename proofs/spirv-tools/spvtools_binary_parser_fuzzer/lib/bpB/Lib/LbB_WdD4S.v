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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_WdD4R.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition wd_d1_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 20 = wz ff
  /\ getr R 19 = wz (sh ff)
  /\ wr_at asegs m (ff / 8 + 2147450880) 512
  /\ 1048576 <= ff
  /\ ff + 4096 <= 2 ^ 47.

Definition wd_d1 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_d1_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 5672)) fc None m (seg_rom asegs)) (MS R' F (wz AASAN_MEMSET) fc None M' (seg_rom asegs))
      /\ munch [((ff / 8 + 2147450956), (ff / 8 + 2147450959)); ((ff / 8 + 2147450972), (ff / 8 + 2147450975)); ((ff / 8 + 2147451166), (ff / 8 + 2147451216))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (ff / 8 + 2147450974) 1 0
      /\ fldA M' (ff / 8 + 2147450973) 1 0
      /\ fldA M' (ff / 8 + 2147450972) 1 0
      /\ fldA M' (ff / 8 + 2147450958) 1 0
      /\ fldA M' (ff / 8 + 2147450957) 1 0
      /\ fldA M' (ff / 8 + 2147450956) 1 0
      /\ fldA M' (ff / 8 + 2147451215) 1 0
      /\ fldA M' (ff / 8 + 2147451214) 1 0
      /\ fldA M' (ff / 8 + 2147451209) 1 0
      /\ fldA M' (ff / 8 + 2147451208) 1 0
      /\ fldA M' (ff / 8 + 2147451207) 1 0
      /\ fldA M' (ff / 8 + 2147451206) 1 0
      /\ fldA M' (ff / 8 + 2147451213) 1 0
      /\ fldA M' (ff / 8 + 2147451212) 1 0
      /\ fldA M' (ff / 8 + 2147451211) 1 0
      /\ fldA M' (ff / 8 + 2147451210) 1 0
      /\ fldA M' (ff / 8 + 2147451201) 1 0
      /\ fldA M' (ff / 8 + 2147451200) 1 0
      /\ fldA M' (ff / 8 + 2147451199) 1 0
      /\ fldA M' (ff / 8 + 2147451198) 1 0
      /\ fldA M' (ff / 8 + 2147451205) 1 0
      /\ fldA M' (ff / 8 + 2147451204) 1 0
      /\ fldA M' (ff / 8 + 2147451203) 1 0
      /\ fldA M' (ff / 8 + 2147451202) 1 0
      /\ fldA M' (ff / 8 + 2147451193) 1 0
      /\ fldA M' (ff / 8 + 2147451192) 1 0
      /\ fldA M' (ff / 8 + 2147451191) 1 0
      /\ fldA M' (ff / 8 + 2147451190) 1 0
      /\ fldA M' (ff / 8 + 2147451197) 1 0
      /\ fldA M' (ff / 8 + 2147451196) 1 0
      /\ fldA M' (ff / 8 + 2147451195) 1 0
      /\ fldA M' (ff / 8 + 2147451194) 1 0
      /\ fldA M' (ff / 8 + 2147451185) 1 0
      /\ fldA M' (ff / 8 + 2147451184) 1 0
      /\ fldA M' (ff / 8 + 2147451183) 1 0
      /\ fldA M' (ff / 8 + 2147451182) 1 0
      /\ fldA M' (ff / 8 + 2147451189) 1 0
      /\ fldA M' (ff / 8 + 2147451188) 1 0
      /\ fldA M' (ff / 8 + 2147451187) 1 0
      /\ fldA M' (ff / 8 + 2147451186) 1 0
      /\ fldA M' (ff / 8 + 2147451177) 1 0
      /\ fldA M' (ff / 8 + 2147451176) 1 0
      /\ fldA M' (ff / 8 + 2147451175) 1 0
      /\ fldA M' (ff / 8 + 2147451174) 1 0
      /\ fldA M' (ff / 8 + 2147451181) 1 0
      /\ fldA M' (ff / 8 + 2147451180) 1 0
      /\ fldA M' (ff / 8 + 2147451179) 1 0
      /\ fldA M' (ff / 8 + 2147451178) 1 0
      /\ fldA M' (ff / 8 + 2147451169) 1 0
      /\ fldA M' (ff / 8 + 2147451168) 1 0
      /\ fldA M' (ff / 8 + 2147451167) 1 0
      /\ fldA M' (ff / 8 + 2147451166) 1 0
      /\ fldA M' (ff / 8 + 2147451173) 1 0
      /\ fldA M' (ff / 8 + 2147451172) 1 0
      /\ fldA M' (ff / 8 + 2147451171) 1 0
      /\ fldA M' (ff / 8 + 2147451170) 1 0
      /\ getr R' 1 = wz (E + 5916)
      /\ getr R' 10 = wz (ff + 608)
      /\ getr R' 11 = wz 0
      /\ getr R' 12 = wz 16
      /\ getr R' 19 = wz (sh ff)
      /\ getr R' 20 = wz ff
      /\ getr R' 24 = wz (ff + 608)
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_d1_ea7c4 : wd_d1 (0xea7c4).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1 & P2 & P3 & P4). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdD4R.d1_E R ff) LbB_WdD4R.d1_sr R) by (unfold LbB_WdD4R.d1_E, LbB_WdD4R.d1_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdD4R.d1_E R ff) m LbB_WdD4R.d1_A_knF) by (unfold LbB_WdD4R.d1_E; knowB).
  destruct (LbB_WdD4R.d1_A_run fx R m (seg_rom asegs) ff ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdD4R.d1_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdD4R.d1_E R ff) in *. unfold LbB_WdD4R.d1_E in Ev.
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

Definition wd_d2_pre (R : bvmap 5 word) (m : mem) (ff S1 cons pos : Z) : Prop :=
  getr R 18 = wz (ff + 3456)
  /\ getr R 24 = wz (ff + 608)
  /\ getr R 9 = wz S1
  /\ getr R 20 = wz ff
  /\ getr R 19 = wz (sh ff)
  /\ fldA m (ff + 3536) 8 pos
  /\ fldA m (ff + 3464) 8 cons
  /\ fldA m (S1 + 48) 8 (ff + 2224)
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

Definition wd_d2 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff S1 cons pos : Z),
    wd_d2_pre R m ff S1 cons pos ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 5916)) fc None m (seg_rom asegs)) (MS R' F (wz 1010964) fc None M' (seg_rom asegs))
      /\ munch [((ff + 624), (ff + 632)); ((ff + 672), (ff + 674)); ((ff + 736), (ff + 738)); ((ff / 8 + 2147450964), (ff / 8 + 2147450967))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (ff + 736) 2 0
      /\ fldA M' (ff + 672) 2 0
      /\ fldA M' (ff / 8 + 2147450966) 1 0
      /\ fldA M' (ff / 8 + 2147450965) 1 0
      /\ fldA M' (ff / 8 + 2147450964) 1 0
      /\ fldA M' (ff + 624) 8 pos
      /\ getr R' 1 = wz (E + 6000)
      /\ getr R' 9 = wz S1
      /\ getr R' 10 = wz (ff + 2288)
      /\ getr R' 11 = wz (ff + 608)
      /\ getr R' 12 = wz cons
      /\ getr R' 13 = wz (ff + 672)
      /\ getr R' 14 = wz 18446744073709551615
      /\ getr R' 15 = wz (ff + 736)
      /\ getr R' 18 = wz (ff + 2288)
      /\ getr R' 19 = wz (sh ff)
      /\ getr R' 20 = wz ff
      /\ getr R' 24 = wz (ff + 608)
      /\ getr R' 25 = wz (ff + 672)
      /\ getr R' 26 = wz (ff + 736)
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 16; 17; 21; 22; 23; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_d2_ea7c4 : wd_d2 (0xea7c4).
Proof.
  intros R F fc m ff S1 cons pos P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdD4R.d2_E R ff S1 cons pos) LbB_WdD4R.d2_sr R) by (unfold LbB_WdD4R.d2_E, LbB_WdD4R.d2_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdD4R.d2_E R ff S1 cons pos) m LbB_WdD4R.d2_A_knF) by (unfold LbB_WdD4R.d2_E; knowB).
  destruct (LbB_WdD4R.d2_A_run fx R m (seg_rom asegs) ff S1 cons pos ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdD4R.d2_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdD4R.d2_E R ff S1 cons pos) in *. unfold LbB_WdD4R.d2_E in Ev.
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
  keptB HR HR' ([2; 3; 4; 5; 6; 7; 8; 16; 17; 21; 22; 23; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_d3_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 26 = wz (ff + 736)
  /\ getr R 25 = wz (ff + 672)
  /\ getr R 19 = wz (sh ff)
  /\ getr R 18 = wz (ff + 2288)
  /\ fldA m (ff + 736) 1 0
  /\ fldA m (ff + 672) 1 0
  /\ wr_at asegs m (ff / 8 + 2147450880) 512
  /\ 1048576 <= ff
  /\ ff + 4096 <= 2 ^ 47.

Definition wd_d3 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_d3_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 6000)) fc None m (seg_rom asegs)) (MS R' F (wz 1008288) fc None M' (seg_rom asegs))
      /\ munch [((ff / 8 + 2147450956), (ff / 8 + 2147450959)); ((ff / 8 + 2147450964), (ff / 8 + 2147450967)); ((ff / 8 + 2147450972), (ff / 8 + 2147450975))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (ff / 8 + 2147450974) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450973) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450972) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450966) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450965) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450964) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450958) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450957) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450956) 1 18446744073709551608
      /\ getr R' 1 = wz (E + 6116)
      /\ getr R' 10 = wz (ff + 2288)
      /\ getr R' 11 = wz 148032
      /\ getr R' 12 = wz 46
      /\ getr R' 18 = wz (ff + 2288)
      /\ getr R' 19 = wz (sh ff)
      /\ getr R' 21 = wz 18446744073709551608
      /\ getr R' 25 = wz (ff + 672)
      /\ getr R' 26 = wz (ff + 736)
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 20; 22; 23; 24; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_d3_ea7c4 : wd_d3 (0xea7c4).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdD4R.d3_E R ff) LbB_WdD4R.d3_sr R) by (unfold LbB_WdD4R.d3_E, LbB_WdD4R.d3_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdD4R.d3_E R ff) m LbB_WdD4R.d3_A_knF) by (unfold LbB_WdD4R.d3_E; knowB).
  destruct (LbB_WdD4R.d3_A_run fx R m (seg_rom asegs) ff ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdD4R.d3_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdD4R.d3_E R ff) in *. unfold LbB_WdD4R.d3_E in Ev.
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

Definition wd_d4_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 18 = wz (ff + 2288)
  /\ fldA m (ff + 2648) 4 4294967295
  /\ 1048576 <= ff
  /\ ff + 4096 <= 2 ^ 47.

Definition wd_d4 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_d4_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 6116)) fc None m (seg_rom asegs)) (MS R' F (wz 1034672) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz (E + 6128)
      /\ getr R' 10 = wz (ff + 2288)
      /\ getr R' 18 = wz (ff + 2288)
      /\ getr R' 24 = wz 18446744073709551615
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_d4_ea7c4 : wd_d4 (0xea7c4).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1 & P2 & P3). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdD4R.d4_E R ff) LbB_WdD4R.d4_sr R) by (unfold LbB_WdD4R.d4_E, LbB_WdD4R.d4_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdD4R.d4_E R ff) m LbB_WdD4R.d4_A_knF) by (unfold LbB_WdD4R.d4_E; knowB).
  destruct (LbB_WdD4R.d4_A_run fx R m (seg_rom asegs) ff ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdD4R.d4_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdD4R.d4_E R ff) in *. unfold LbB_WdD4R.d4_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  keptB HR HR' ([2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_d5_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 21 = wz 18446744073709551608
  /\ getr R 19 = wz (sh ff)
  /\ wr_at asegs m (ff / 8 + 2147450880) 512
  /\ 1048576 <= ff
  /\ ff + 4096 <= 2 ^ 47.

Definition wd_d5 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_d5_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 6128)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 6428)) fc None M' (seg_rom asegs))
      /\ munch [((ff / 8 + 2147451166), (ff / 8 + 2147451216))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (ff / 8 + 2147451215) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451214) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451209) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451208) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451207) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451206) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451213) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451212) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451211) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451210) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451201) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451200) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451199) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451198) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451205) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451204) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451203) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451202) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451193) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451192) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451191) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451190) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451197) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451196) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451195) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451194) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451185) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451184) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451183) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451182) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451189) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451188) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451187) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451186) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451177) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451176) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451175) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451174) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451181) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451180) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451179) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451178) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451169) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451168) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451167) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451166) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451173) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451172) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451171) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147451170) 1 18446744073709551608
      /\ getr R' 19 = wz (sh ff)
      /\ getr R' 21 = wz 18446744073709551608
      /\ (forall r, In r [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_d5_ea7c4 : wd_d5 (0xea7c4).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1 & P2 & P3 & P4). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdD4R.d5_E R ff) LbB_WdD4R.d5_sr R) by (unfold LbB_WdD4R.d5_E, LbB_WdD4R.d5_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdD4R.d5_E R ff) m LbB_WdD4R.d5_A_knF) by (unfold LbB_WdD4R.d5_E; knowB).
  destruct (LbB_WdD4R.d5_A_run fx R m (seg_rom asegs) ff ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdD4R.d5_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdD4R.d5_E R ff) in *. unfold LbB_WdD4R.d5_E in Ev.
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
