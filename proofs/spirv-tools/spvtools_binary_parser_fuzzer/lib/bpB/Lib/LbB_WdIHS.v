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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_WdIHR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition wd_ih0_pre (R : bvmap 5 word) (m : mem) (ff sp mb words n : Z) : Prop :=
  getr R 18 = wz (ff + 3456)
  /\ getr R 22 = wz (ff + 3504)
  /\ getr R 9 = wz sp
  /\ fldA m (ff + 3504) 8 words
  /\ fldA m (ff + 3512) 8 n
  /\ fldA m (sp + 40) 8 mb
  /\ 7241728 <= ff <= 2 ^ 47 - 4096
  /\ 140735332483136 <= sp <= 2 ^ 47
  /\ 0 <= n <= 4
  /\ 0 <= mb <= 2 ^ 64 - 1
  /\ 0 <= words <= 2 ^ 64 - 1.

Definition wd_ih0 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff sp mb words n : Z),
    wd_ih0_pre R m ff sp mb words n -> (words <> 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 3384)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 3408)) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 9 = wz sp
      /\ getr R' 10 = wz words
      /\ getr R' 11 = wz n
      /\ getr R' 12 = wz 5
      /\ getr R' 18 = wz (ff + 3456)
      /\ getr R' 22 = wz (ff + 3504)
      /\ getr R' 27 = wz mb
      /\ (forall r, In r [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 19; 20; 21; 23; 24; 25; 26; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_ih0_ea7c4 : wd_ih0 (960452).
Proof.
  intros R F fc m ff sp mb words n P Q0.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdIHR.ih0_E R ff sp mb words n) LbB_WdIHR.ih0_sr R) by (unfold LbB_WdIHR.ih0_E, LbB_WdIHR.ih0_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdIHR.ih0_E R ff sp mb words n) m LbB_WdIHR.ih0_A_knF) by (unfold LbB_WdIHR.ih0_E; knowB).
  destruct (LbB_WdIHR.ih0_A_run fx R m (seg_rom asegs) ff sp mb words n ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdIHR.ih0_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdIHR.ih0_E R ff sp mb words n) in *. unfold LbB_WdIHR.ih0_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (22%bv : reg); regB|].
  split; [rrwB HR' (27%bv : reg); regB|].
  keptB HR HR' ([1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 19; 20; 21; 23; 24; 25; 26; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_ih1_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 20 = wz ff
  /\ getr R 19 = wz (sh ff)
  /\ wr_at asegs m (ff / 8 + 2147450880) 512
  /\ 7241728 <= ff <= 2 ^ 47 - 4096.

Definition wd_ih1 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_ih1_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 3408)) fc None m (seg_rom asegs)) (MS R' F (wz AASAN_MEMSET) fc None M' (seg_rom asegs))
      /\ munch [((ff / 8 + 2147450908), (ff / 8 + 2147450911)); ((ff / 8 + 2147450924), (ff / 8 + 2147450927)); ((ff / 8 + 2147451038), (ff / 8 + 2147451088))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (ff / 8 + 2147450926) 1 0
      /\ fldA M' (ff / 8 + 2147450925) 1 0
      /\ fldA M' (ff / 8 + 2147450924) 1 0
      /\ fldA M' (ff / 8 + 2147450910) 1 0
      /\ fldA M' (ff / 8 + 2147450909) 1 0
      /\ fldA M' (ff / 8 + 2147450908) 1 0
      /\ fldA M' (ff / 8 + 2147451087) 1 0
      /\ fldA M' (ff / 8 + 2147451086) 1 0
      /\ fldA M' (ff / 8 + 2147451081) 1 0
      /\ fldA M' (ff / 8 + 2147451080) 1 0
      /\ fldA M' (ff / 8 + 2147451079) 1 0
      /\ fldA M' (ff / 8 + 2147451078) 1 0
      /\ fldA M' (ff / 8 + 2147451085) 1 0
      /\ fldA M' (ff / 8 + 2147451084) 1 0
      /\ fldA M' (ff / 8 + 2147451083) 1 0
      /\ fldA M' (ff / 8 + 2147451082) 1 0
      /\ fldA M' (ff / 8 + 2147451073) 1 0
      /\ fldA M' (ff / 8 + 2147451072) 1 0
      /\ fldA M' (ff / 8 + 2147451071) 1 0
      /\ fldA M' (ff / 8 + 2147451070) 1 0
      /\ fldA M' (ff / 8 + 2147451077) 1 0
      /\ fldA M' (ff / 8 + 2147451076) 1 0
      /\ fldA M' (ff / 8 + 2147451075) 1 0
      /\ fldA M' (ff / 8 + 2147451074) 1 0
      /\ fldA M' (ff / 8 + 2147451065) 1 0
      /\ fldA M' (ff / 8 + 2147451064) 1 0
      /\ fldA M' (ff / 8 + 2147451063) 1 0
      /\ fldA M' (ff / 8 + 2147451062) 1 0
      /\ fldA M' (ff / 8 + 2147451069) 1 0
      /\ fldA M' (ff / 8 + 2147451068) 1 0
      /\ fldA M' (ff / 8 + 2147451067) 1 0
      /\ fldA M' (ff / 8 + 2147451066) 1 0
      /\ fldA M' (ff / 8 + 2147451057) 1 0
      /\ fldA M' (ff / 8 + 2147451056) 1 0
      /\ fldA M' (ff / 8 + 2147451055) 1 0
      /\ fldA M' (ff / 8 + 2147451054) 1 0
      /\ fldA M' (ff / 8 + 2147451061) 1 0
      /\ fldA M' (ff / 8 + 2147451060) 1 0
      /\ fldA M' (ff / 8 + 2147451059) 1 0
      /\ fldA M' (ff / 8 + 2147451058) 1 0
      /\ fldA M' (ff / 8 + 2147451049) 1 0
      /\ fldA M' (ff / 8 + 2147451048) 1 0
      /\ fldA M' (ff / 8 + 2147451047) 1 0
      /\ fldA M' (ff / 8 + 2147451046) 1 0
      /\ fldA M' (ff / 8 + 2147451053) 1 0
      /\ fldA M' (ff / 8 + 2147451052) 1 0
      /\ fldA M' (ff / 8 + 2147451051) 1 0
      /\ fldA M' (ff / 8 + 2147451050) 1 0
      /\ fldA M' (ff / 8 + 2147451041) 1 0
      /\ fldA M' (ff / 8 + 2147451040) 1 0
      /\ fldA M' (ff / 8 + 2147451039) 1 0
      /\ fldA M' (ff / 8 + 2147451038) 1 0
      /\ fldA M' (ff / 8 + 2147451045) 1 0
      /\ fldA M' (ff / 8 + 2147451044) 1 0
      /\ fldA M' (ff / 8 + 2147451043) 1 0
      /\ fldA M' (ff / 8 + 2147451042) 1 0
      /\ getr R' 1 = wz (E + 3652)
      /\ getr R' 10 = wz (ff + 224)
      /\ getr R' 11 = wz 0
      /\ getr R' 12 = wz 16
      /\ getr R' 19 = wz (sh ff)
      /\ getr R' 20 = wz ff
      /\ getr R' 24 = wz (ff + 224)
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_ih1_ea7c4 : wd_ih1 (960452).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1 & P2 & P3). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdIHR.ih1_E R ff) LbB_WdIHR.ih1_sr R) by (unfold LbB_WdIHR.ih1_E, LbB_WdIHR.ih1_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdIHR.ih1_E R ff) m LbB_WdIHR.ih1_A_knF) by (unfold LbB_WdIHR.ih1_E; knowB).
  destruct (LbB_WdIHR.ih1_A_run fx R m (seg_rom asegs) ff ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdIHR.ih1_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdIHR.ih1_E R ff) in *. unfold LbB_WdIHR.ih1_E in Ev.
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

Definition wd_ih2_pre (R : bvmap 5 word) (m : mem) (ff cons pos : Z) : Prop :=
  getr R 18 = wz (ff + 3456)
  /\ getr R 24 = wz (ff + 224)
  /\ getr R 20 = wz ff
  /\ getr R 19 = wz (sh ff)
  /\ fldA m (ff + 3536) 8 pos
  /\ fldA m (ff + 3464) 8 cons
  /\ wr_at asegs m ff 4096
  /\ wr_at asegs m (ff / 8 + 2147450880) 512
  /\ 7241728 <= ff <= 2 ^ 47 - 4096
  /\ 1 <= cons <= 2 ^ 47
  /\ cons mod 16 = 0
  /\ 0 <= pos <= 2 ^ 64 - 1
  /\ (ff + 4096 <= 2147446784 \/ 17594333495296 <= ff).

Definition wd_ih2 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff cons pos : Z),
    wd_ih2_pre R m ff cons pos ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 3652)) fc None m (seg_rom asegs)) (MS R' F (wz 1010964) fc None M' (seg_rom asegs))
      /\ munch [((ff + 240), (ff + 248)); ((ff + 288), (ff + 290)); ((ff + 352), (ff + 354)); ((ff / 8 + 2147450916), (ff / 8 + 2147450919))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (ff + 352) 2 0
      /\ fldA M' (ff + 288) 2 0
      /\ fldA M' (ff / 8 + 2147450918) 1 0
      /\ fldA M' (ff / 8 + 2147450917) 1 0
      /\ fldA M' (ff / 8 + 2147450916) 1 0
      /\ fldA M' (ff + 240) 8 pos
      /\ getr R' 1 = wz (E + 3732)
      /\ getr R' 10 = wz (ff + 1264)
      /\ getr R' 11 = wz (ff + 224)
      /\ getr R' 12 = wz cons
      /\ getr R' 13 = wz (ff + 288)
      /\ getr R' 14 = wz 18446744073709551612
      /\ getr R' 15 = wz (ff + 352)
      /\ getr R' 18 = wz (ff + 3456)
      /\ getr R' 19 = wz (sh ff)
      /\ getr R' 20 = wz ff
      /\ getr R' 24 = wz (ff + 224)
      /\ getr R' 25 = wz (ff + 1264)
      /\ getr R' 26 = wz (ff + 288)
      /\ getr R' 27 = wz (ff + 352)
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 9; 16; 17; 21; 22; 23; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_ih2_ea7c4 : wd_ih2 (960452).
Proof.
  intros R F fc m ff cons pos P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdIHR.ih2_E R ff cons pos) LbB_WdIHR.ih2_sr R) by (unfold LbB_WdIHR.ih2_E, LbB_WdIHR.ih2_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdIHR.ih2_E R ff cons pos) m LbB_WdIHR.ih2_A_knF) by (unfold LbB_WdIHR.ih2_E; knowB).
  destruct (LbB_WdIHR.ih2_A_run fx R m (seg_rom asegs) ff cons pos ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdIHR.ih2_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdIHR.ih2_E R ff cons pos) in *. unfold LbB_WdIHR.ih2_E in Ev.
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
  keptB HR HR' ([2; 3; 4; 5; 6; 7; 8; 9; 16; 17; 21; 22; 23; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_ih3_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 27 = wz (ff + 352)
  /\ getr R 26 = wz (ff + 288)
  /\ getr R 19 = wz (sh ff)
  /\ getr R 25 = wz (ff + 1264)
  /\ fldA m (ff + 352) 1 0
  /\ fldA m (ff + 288) 1 0
  /\ wr_at asegs m (ff / 8 + 2147450880) 512
  /\ 7241728 <= ff <= 2 ^ 47 - 4096.

Definition wd_ih3 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_ih3_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 3732)) fc None m (seg_rom asegs)) (MS R' F (wz 1008288) fc None M' (seg_rom asegs))
      /\ munch [((ff / 8 + 2147450908), (ff / 8 + 2147450911)); ((ff / 8 + 2147450916), (ff / 8 + 2147450919)); ((ff / 8 + 2147450924), (ff / 8 + 2147450927))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (ff / 8 + 2147450926) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450925) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450924) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450918) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450917) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450916) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450910) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450909) 1 18446744073709551608
      /\ fldA M' (ff / 8 + 2147450908) 1 18446744073709551608
      /\ getr R' 1 = wz (E + 3848)
      /\ getr R' 10 = wz (ff + 1264)
      /\ getr R' 11 = wz 147776
      /\ getr R' 12 = wz 35
      /\ getr R' 19 = wz (sh ff)
      /\ getr R' 21 = wz 18446744073709551608
      /\ getr R' 25 = wz (ff + 1264)
      /\ getr R' 26 = wz (ff + 288)
      /\ getr R' 27 = wz (ff + 352)
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 20; 22; 23; 24; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_ih3_ea7c4 : wd_ih3 (960452).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdIHR.ih3_E R ff) LbB_WdIHR.ih3_sr R) by (unfold LbB_WdIHR.ih3_E, LbB_WdIHR.ih3_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdIHR.ih3_E R ff) m LbB_WdIHR.ih3_A_knF) by (unfold LbB_WdIHR.ih3_E; knowB).
  destruct (LbB_WdIHR.ih3_A_run fx R m (seg_rom asegs) ff ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdIHR.ih3_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdIHR.ih3_E R ff) in *. unfold LbB_WdIHR.ih3_E in Ev.
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
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  split; [rrwB HR' (26%bv : reg); regB|].
  split; [rrwB HR' (27%bv : reg); regB|].
  keptB HR HR' ([2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 20; 22; 23; 24; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_ih4_pre (R : bvmap 5 word) (m : mem) (ff nw : Z) : Prop :=
  getr R 18 = wz (ff + 3456)
  /\ getr R 25 = wz (ff + 1264)
  /\ fldA m (ff + 3512) 8 nw
  /\ 7241728 <= ff <= 2 ^ 47 - 4096
  /\ 0 <= nw <= 2 ^ 64 - 1.

Definition wd_ih4 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff nw : Z),
    wd_ih4_pre R m ff nw ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 3848)) fc None m (seg_rom asegs)) (MS R' F (wz 1201164) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz (E + 3860)
      /\ getr R' 10 = wz (ff + 1264)
      /\ getr R' 11 = wz nw
      /\ getr R' 18 = wz (ff + 3456)
      /\ getr R' 25 = wz (ff + 1264)
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_ih4_ea7c4 : wd_ih4 (960452).
Proof.
  intros R F fc m ff nw P.
  destruct P as (P0 & P1 & P2 & P3 & P4). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdIHR.ih4_E R ff nw) LbB_WdIHR.ih4_sr R) by (unfold LbB_WdIHR.ih4_E, LbB_WdIHR.ih4_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdIHR.ih4_E R ff nw) m LbB_WdIHR.ih4_A_knF) by (unfold LbB_WdIHR.ih4_E; knowB).
  destruct (LbB_WdIHR.ih4_A_run fx R m (seg_rom asegs) ff nw ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdIHR.ih4_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdIHR.ih4_E R ff nw) in *. unfold LbB_WdIHR.ih4_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_ih5_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 25 = wz (ff + 1264)
  /\ 7241728 <= ff <= 2 ^ 47 - 4096.

Definition wd_ih5 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_ih5_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 3860)) fc None m (seg_rom asegs)) (MS R' F (wz 1008288) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz (E + 3880)
      /\ getr R' 10 = wz (ff + 1264)
      /\ getr R' 11 = wz 147872
      /\ getr R' 12 = wz 18
      /\ getr R' 25 = wz (ff + 1264)
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_ih5_ea7c4 : wd_ih5 (960452).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdIHR.ih5_E R ff) LbB_WdIHR.ih5_sr R) by (unfold LbB_WdIHR.ih5_E, LbB_WdIHR.ih5_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdIHR.ih5_E R ff) m LbB_WdIHR.ih5_A_knF) by (unfold LbB_WdIHR.ih5_E; knowB).
  destruct (LbB_WdIHR.ih5_A_run fx R m (seg_rom asegs) ff ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdIHR.ih5_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdIHR.ih5_E R ff) in *. unfold LbB_WdIHR.ih5_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (12%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_ih6_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 25 = wz (ff + 1264)
  /\ 7241728 <= ff <= 2 ^ 47 - 4096.

Definition wd_ih6 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_ih6_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 3880)) fc None m (seg_rom asegs)) (MS R' F (wz 1200700) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz (E + 3892)
      /\ getr R' 10 = wz (ff + 1264)
      /\ getr R' 11 = wz 5
      /\ getr R' 25 = wz (ff + 1264)
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_ih6_ea7c4 : wd_ih6 (960452).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdIHR.ih6_E R ff) LbB_WdIHR.ih6_sr R) by (unfold LbB_WdIHR.ih6_E, LbB_WdIHR.ih6_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdIHR.ih6_E R ff) m LbB_WdIHR.ih6_A_knF) by (unfold LbB_WdIHR.ih6_E; knowB).
  destruct (LbB_WdIHR.ih6_A_run fx R m (seg_rom asegs) ff ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdIHR.ih6_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdIHR.ih6_E R ff) in *. unfold LbB_WdIHR.ih6_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_ih7_pre (R : bvmap 5 word) (m : mem) (ff : Z) : Prop :=
  getr R 25 = wz (ff + 1264)
  /\ fldA m (ff + 1624) 4 4294967292
  /\ 7241728 <= ff <= 2 ^ 47 - 4096.

Definition wd_ih7 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff : Z),
    wd_ih7_pre R m ff ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 3892)) fc None m (seg_rom asegs)) (MS R' F (wz 1034672) fc None M' (seg_rom asegs))
      /\ M' = m
      /\ getr R' 1 = wz (E + 3904)
      /\ getr R' 10 = wz (ff + 1264)
      /\ getr R' 24 = wz 18446744073709551612
      /\ getr R' 25 = wz (ff + 1264)
      /\ (forall r, In r [2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_ih7_ea7c4 : wd_ih7 (960452).
Proof.
  intros R F fc m ff P.
  destruct P as (P0 & P1 & P2). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdIHR.ih7_E R ff) LbB_WdIHR.ih7_sr R) by (unfold LbB_WdIHR.ih7_E, LbB_WdIHR.ih7_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdIHR.ih7_E R ff) m LbB_WdIHR.ih7_A_knF) by (unfold LbB_WdIHR.ih7_E; knowB).
  destruct (LbB_WdIHR.ih7_A_run fx R m (seg_rom asegs) ff ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdIHR.ih7_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdIHR.ih7_E R ff) in *. unfold LbB_WdIHR.ih7_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [reflexivity|].
  split; [rrwB HR' (1%bv : reg); regB|].
  split; [rrwB HR' (10%bv : reg); regB|].
  split; [rrwB HR' (24%bv : reg); regB|].
  split; [rrwB HR' (25%bv : reg); regB|].
  keptB HR HR' ([2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Definition wd_ih8_pre (R : bvmap 5 word) (m : mem) (ff sp mb : Z) : Prop :=
  getr R 21 = wz (-8)
  /\ getr R 19 = wz (sh ff)
  /\ getr R 9 = wz sp
  /\ wr_at asegs m (ff / 8 + 2147450880) 512
  /\ fldA m (sp + 40) 8 mb
  /\ 7241728 <= ff <= 2 ^ 47 - 4096
  /\ 140735332483136 <= sp <= 2 ^ 47
  /\ 0 <= mb <= 2 ^ 64 - 1.

Definition wd_ih8 (E : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff sp mb : Z),
    wd_ih8_pre R m ff sp mb ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (E + 3904)) fc None m (seg_rom asegs)) (MS R' F (wz (E + 6460)) fc None M' (seg_rom asegs))
      /\ munch [((ff / 8 + 2147451038), (ff / 8 + 2147451088))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (ff / 8 + 2147451087) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451086) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451081) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451080) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451079) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451078) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451085) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451084) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451083) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451082) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451073) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451072) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451071) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451070) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451077) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451076) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451075) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451074) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451065) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451064) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451063) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451062) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451069) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451068) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451067) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451066) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451057) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451056) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451055) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451054) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451061) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451060) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451059) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451058) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451049) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451048) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451047) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451046) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451053) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451052) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451051) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451050) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451041) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451040) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451039) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451038) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451045) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451044) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451043) 1 (-8)
      /\ fldA M' (ff / 8 + 2147451042) 1 (-8)
      /\ getr R' 9 = wz sp
      /\ getr R' 19 = wz (sh ff)
      /\ getr R' 21 = wz (-8)
      /\ getr R' 27 = wz mb
      /\ (forall r, In r [1; 2; 3; 4; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 22; 23; 24; 25; 26; 28; 29; 30; 31]%bv -> getr R' r = getr R r).

Lemma wd_ih8_ea7c4 : wd_ih8 (960452).
Proof.
  intros R F fc m ff sp mb P.
  destruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7). stash_disjB.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_WdIHR.ih8_E R ff sp mb) LbB_WdIHR.ih8_sr R) by (unfold LbB_WdIHR.ih8_E, LbB_WdIHR.ih8_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_WdIHR.ih8_E R ff sp mb) m LbB_WdIHR.ih8_A_knF) by (unfold LbB_WdIHR.ih8_E; knowB).
  destruct (LbB_WdIHR.ih8_A_run fx R m (seg_rom asegs) ff sp mb ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_WdIHR.ih8_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_WdIHR.ih8_E R ff sp mb) in *. unfold LbB_WdIHR.ih8_E in Ev.
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
  split; [rrwB HR' (9%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|].
  split; [rrwB HR' (21%bv : reg); regB|].
  split; [rrwB HR' (27%bv : reg); regB|].
  keptB HR HR' ([1; 2; 3; 4; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 22; 23; 24; 25; 26; 28; 29; 30; 31]%bv : list reg).
Qed.
