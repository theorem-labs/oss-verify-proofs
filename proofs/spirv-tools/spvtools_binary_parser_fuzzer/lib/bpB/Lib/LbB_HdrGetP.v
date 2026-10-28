From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_Own LbB_TablStmt LbB_TablImg.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HCommon.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Call LbB_Conv LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwStm.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_HdrGet LbB_HdrGetS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HdrGetR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition HG_K1 : Z := 18446744073692774655.
Definition HG_KV : Z := 4278190335.
Definition HG_LB : Z := 2147446784.
Definition HG_HB : Z := 17594333495296.

Lemma hg_ext_sx32 : forall w, 0 <= w <= 2 ^ 32 - 1 -> ext_val true 0 4 (Z_to_bv 64 w) = wz (sx32A w).
Proof.
  intros w Hw. unfold ext_val, ext_Z, wz. rewrite u64_of_Z by lia.
  change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 4) with 32. change (8 * N.of_nat 4)%N with 32%N.
  rewrite Z.pow_0_r, Z.div_1_r, Z.mod_small by lia.
  unfold sx32A, PrsGrammar.sx32. destruct (Z.ltb_spec w (2 ^ 31)) as [L|L]; apply bv_eq; rewrite !Z_to_bv_unsigned;
    unfold bv_swrap, bv_wrap; change (bv_modulus 32) with (2 ^ 32); change (bv_half_modulus 32) with (2 ^ 31);
    change (bv_modulus 64) with (2 ^ 64).
  - rewrite (Z.mod_small (w + 2 ^ 31) (2 ^ 32)) by lia. replace (w + 2 ^ 31 - 2 ^ 31) with w by lia. reflexivity.
  - replace (w + 2 ^ 31) with ((w - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z_mod_plus_full. rewrite (Z.mod_small (w - 2 ^ 31)) by lia.
    rewrite <- (Z_mod_plus_full (w - 2 ^ 31 - 2 ^ 31) 1 (2 ^ 64)). f_equal. lia.
Qed.

Lemma hg_h1w :
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code nn e h sp w0 : Z),
    hg_h1_pre R m b code nn e h sp w0 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz 959156) fc None m (seg_rom asegs)) (MS R' F (wz 1034240) fc None M' (seg_rom asegs))
      /\ munch [((sp - 56), sp)] m M'
      /\ wmono asegs m M'
      /\ fldw asegs M' (sp - 56) 8 (getr R 21)
      /\ fldw asegs M' (sp - 48) 8 (getr R 20)
      /\ fldw asegs M' (sp - 40) 8 (getr R 19)
      /\ fldw asegs M' (sp - 32) 8 (getr R 18)
      /\ fldw asegs M' (sp - 24) 8 (getr R 9)
      /\ fldw asegs M' (sp - 16) 8 (getr R 8)
      /\ fldw asegs M' (sp - 8) 8 (getr R 1)
      /\ getr R' 1 = wz (959156 + 172)
      /\ getr R' 2 = wz (sp - 64)
      /\ getr R' 8 = wz b
      /\ getr R' 9 = wz h
      /\ getr R' 11 = wz e
      /\ getr R' 12 = wz 5
      /\ getr R' 18 = wz e
      /\ getr R' 19 = wz 18446744073709551612
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (sh b)
      /\ getr R' 10 = wz (sx32A w0)
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).
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
  split; [rrwB HR' (10%bv : reg); evs; apply hg_ext_sx32; lia|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma hg_h2w :
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 w : Z),
    hg_h2_pre R m b code e h sp r1 w ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (959156 + 172)) fc None m (seg_rom asegs)) (MS R' F (wz 1034240) fc None M' (seg_rom asegs))
      /\ munch [(h, (h + 4))] m M'
      /\ wmono asegs m M'
      /\ fldA M' h 4 r1
      /\ getr R' 1 = wz (959156 + 260)
      /\ getr R' 2 = wz (sp - 64)
      /\ getr R' 8 = wz b
      /\ getr R' 9 = wz h
      /\ getr R' 11 = wz e
      /\ getr R' 12 = wz 0
      /\ getr R' 18 = wz e
      /\ getr R' 19 = wz (-4)
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (sh b)
      /\ getr R' 10 = wz (sx32A w)
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).
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
  split; [rrwB HR' (10%bv : reg); evs; apply hg_ext_sx32; lia|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma hg_h3vw :
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 w : Z),
    hg_h3v_pre R m b code e h sp r1 w -> (Z.land r1 18446744073692774655 = 0) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (959156 + 260)) fc None m (seg_rom asegs)) (MS R' F (wz 1034240) fc None M' (seg_rom asegs))
      /\ munch [((h + 4), (h + 8))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (h + 4) 4 r1
      /\ getr R' 1 = wz (959156 + 380)
      /\ getr R' 2 = wz (sp - 64)
      /\ getr R' 8 = wz b
      /\ getr R' 9 = wz h
      /\ getr R' 11 = wz e
      /\ getr R' 18 = wz e
      /\ getr R' 19 = wz (-4)
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (sh b)
      /\ getr R' 10 = wz (sx32A w)
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).
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
  split; [rrwB HR' (10%bv : reg); evs; apply hg_ext_sx32; lia|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma hg_h4w :
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 w : Z),
    hg_h4_pre R m b code e h sp r1 w ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (959156 + 380)) fc None m (seg_rom asegs)) (MS R' F (wz 1034240) fc None M' (seg_rom asegs))
      /\ munch [((h + 8), (h + 12))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (h + 8) 4 r1
      /\ getr R' 1 = wz (959156 + 468)
      /\ getr R' 2 = wz (sp - 64)
      /\ getr R' 8 = wz b
      /\ getr R' 9 = wz h
      /\ getr R' 11 = wz e
      /\ getr R' 12 = wz 0
      /\ getr R' 18 = wz e
      /\ getr R' 19 = wz (-4)
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (sh b)
      /\ getr R' 10 = wz (sx32A w)
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).
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
  split; [rrwB HR' (10%bv : reg); evs; apply hg_ext_sx32; lia|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma hg_h5w :
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 w : Z),
    hg_h5_pre R m b code e h sp r1 w ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (959156 + 468)) fc None m (seg_rom asegs)) (MS R' F (wz 1034240) fc None M' (seg_rom asegs))
      /\ munch [((h + 12), (h + 16))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (h + 12) 4 r1
      /\ getr R' 1 = wz (959156 + 556)
      /\ getr R' 2 = wz (sp - 64)
      /\ getr R' 8 = wz b
      /\ getr R' 9 = wz h
      /\ getr R' 11 = wz e
      /\ getr R' 12 = wz 3
      /\ getr R' 18 = wz e
      /\ getr R' 19 = wz (-4)
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (sh b)
      /\ getr R' 10 = wz (sx32A w)
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).
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
  split; [rrwB HR' (10%bv : reg); evs; apply hg_ext_sx32; lia|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma hg_h5zw :
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (b code e h sp r1 w : Z),
    hg_h5z_pre R m b code e h sp r1 w ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (959156 + 468)) fc None m (seg_rom asegs)) (MS R' F (wz 1034240) fc None M' (seg_rom asegs))
      /\ munch [((h + 12), (h + 16))] m M'
      /\ wmono asegs m M'
      /\ fldA M' (h + 12) 4 r1
      /\ getr R' 1 = wz (959156 + 556)
      /\ getr R' 2 = wz (sp - 64)
      /\ getr R' 8 = wz b
      /\ getr R' 9 = wz h
      /\ getr R' 11 = wz e
      /\ getr R' 12 = wz 0
      /\ getr R' 18 = wz e
      /\ getr R' 19 = wz (-4)
      /\ getr R' 20 = wz ASHADOW_BASE
      /\ getr R' 21 = wz (sh b)
      /\ getr R' 10 = wz (sx32A w)
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r).
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
  split; [rrwB HR' (10%bv : reg); evs; apply hg_ext_sx32; lia|].
  keptB HR HR' ([3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Qed.

Lemma hg_land_small : forall x, 0 <= x < 2 ^ 64 -> Z.land x HG_K1 = 0 -> x < 2 ^ 24.
Proof.
  intros x Hx H.
  assert (S : Z.shiftr (Z.land x HG_K1) 24 = 0) by (rewrite H; reflexivity).
  rewrite Z.shiftr_land in S.
  replace (Z.shiftr HG_K1 24) with (Z.ones 40) in S by (vm_compute; reflexivity).
  rewrite Z.land_ones in S by lia. rewrite Z.shiftr_div_pow2 in S by lia.
  assert (D : x / 2 ^ 24 < 2 ^ 40) by (apply Z.div_lt_upper_bound; lia).
  rewrite Z.mod_small in S by (split; [apply Z.div_pos; lia | exact D]).
  Z.div_mod_to_equations. lia.
Qed.

Lemma hg_ver_of : forall x, Z.land x HG_K1 = 0 -> 65536 <= x <= 67072 -> hg_ver_ok x.
Proof.
  intros x H R. unfold hg_ver_ok. split; [|lia].
  change (Z.land x HG_KV = 0).
  replace HG_KV with (Z.land HG_K1 HG_KV) by (vm_compute; reflexivity).
  rewrite Z.land_assoc, H. reflexivity.
Qed.

Lemma hg_ret : forall (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
          x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (ret_pc x1) fc None m (seg_rom asegs)) ->
    evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 (AHDR_GET + 680)) fc None m (seg_rom asegs)).
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
  unfold AHDR_GET. step. apply evt_done. exact HQ.
Qed.

Lemma hg_rdn_tr : forall W (m m' : mem) a k, munch W m m' -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
  disjoint_from W a (Z.of_nat k) -> PropExec.rdn ASEGS m' (Z_to_bv 64 a) k = PropExec.rdn ASEGS m (Z_to_bv 64 a) k.
Proof.
  intros W m m' a k MU Ha Hk D. apply CRep.rdn_agree_win; [exact Ha | exact Hk |].
  intros x Hx. unfold LibIface.zwin in Hx. apply MU. rewrite u64_of_Z by lia.
  eapply disjoint_outside; [exact D | lia].
Qed.

Lemma hg_fld_tr : forall W m m' a k v, munch W m m' -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
  disjoint_from W a (Z.of_nat k) -> fldA m a k v -> fldA m' a k v.
Proof.
  intros W m m' a k v MU Ha Hk D HF. unfold fldA, fld in *. rewrite (hg_rdn_tr W m m' a k MU Ha Hk D). exact HF.
Qed.

Lemma hg_fld_tr4 : forall W m m' a v, munch W m m' -> 0 <= a -> a + 4 < 2 ^ 64 -> disjoint_from W a 4 -> fldA m a 4 v -> fldA m' a 4 v.
Proof. intros W m m' a v MU Ha Hk D HF. exact (hg_fld_tr W m m' a 4 v MU Ha Hk D HF). Qed.

Lemma hg_fld_tr8 : forall W m m' a v, munch W m m' -> 0 <= a -> a + 8 < 2 ^ 64 -> disjoint_from W a 8 -> fldA m a 8 v -> fldA m' a 8 v.
Proof. intros W m m' a v MU Ha Hk D HF. exact (hg_fld_tr W m m' a 8 v MU Ha Hk D HF). Qed.

Lemma hg_out_dj : forall W a, outside W a -> disjoint_from W a 1.
Proof. induction W as [|[l r] W IH]; cbn; intros a H; [exact I|]. destruct H as [H1 H2]. split; [lia | exact (IH a H2)]. Qed.

Lemma hg_dj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[l r] W IH]; cbn; intros a n a' n' D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia | exact (IH a n a' n' D2 H1 H2)].
Qed.

Lemma hg_shk_tr : forall W m m' x k, munch W m m' -> 0 <= x < 2 ^ 47 -> outside W (x / 8 + SHBASE) -> shk m x k -> shk m' x k.
Proof.
  intros W m m' x k MU Hx O K. unfold shk in *.
  assert (D : 0 <= x / 8 < 2 ^ 44) by (Z.div_mod_to_equations; lia).
  rewrite (hg_rdn_tr W m m' (x / 8 + SHBASE) 1 MU); [exact K | unfold SHBASE; lia | cbn [Z.of_nat Pos.of_succ_nat]; unfold SHBASE; lia
    | exact (hg_out_dj W _ O)].
Qed.

Lemma hg_wr_tr : forall m m' a k, wmono asegs m m' -> wr_at asegs m a k -> wr_at asegs m' a k.
Proof. intros m m' a k WM (W0 & W1 & W). split; [exact W0|]. split; [exact W1|]. intros i Hi. apply WM, W, Hi. Qed.

Lemma hg_fldw_A : forall m a w, fldw asegs m a 8 w -> fldA m a 8 (bv_unsigned w).
Proof. intros m a w H. unfold fldw, fldA, fld in *. rewrite Z_to_bv_bv_unsigned. exact H. Qed.

Lemma hg_fld4_mod : forall m a v, fldA m a 4 v -> fldA m a 4 (v mod 2 ^ 32).
Proof. intros m a v H. unfold fldA, fld in *. rewrite <- HCommon.w2lb4_low. exact H. Qed.

Lemma hg_fld8_mod : forall m a v, fldA m a 8 v -> fldA m a 8 (v mod 2 ^ 64).
Proof.
  intros m a v H. unfold fldA, fld in *. replace (Z_to_bv 64 (v mod 2 ^ 64)) with (Z_to_bv 64 v); [exact H|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity.
Qed.

Lemma hg_sx32_rng : forall r, 0 <= r < 2 ^ 32 -> 0 <= sx32A r < 2 ^ 64 /\ sx32A r mod 2 ^ 32 = r.
Proof.
  intros r Hr. unfold sx32A, PrsGrammar.sx32. destruct (Z.ltb_spec r (2 ^ 31)) as [L|L].
  - split; [lia | apply Z.mod_small; lia].
  - split; [lia|]. replace (r + 2 ^ 64 - 2 ^ 32) with (r + (2 ^ 32 - 1) * 2 ^ 32) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma hg_rw4 : forall m a v, fldA m a 4 v -> wr_at asegs m a 4 -> rw_cells asegs m a [C4 (Z_to_bv 64 v)].
Proof.
  intros m a v HF HW. pose proof HW as (HW0 & HW1 & _). split; [|exact HW].
  split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply bytes_at_of_rdn; [lia | rewrite length_le4; lia | rewrite length_le4; exact HF].
Qed.

Lemma hg_rw8 : forall m a v, fldA m a 8 v -> wr_at asegs m a 8 -> rw_cells asegs m a [C8 (Z_to_bv 64 v)].
Proof.
  intros m a v HF HW. pose proof HW as (HW0 & HW1 & _). split; [|exact HW].
  split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply bytes_at_of_rdn; [lia | rewrite length_le8; lia | rewrite length_le8; exact HF].
Qed.

Lemma hg_rw_cons4 : forall m a v cs, fldA m a 4 v -> wr_at asegs m a 4 -> rw_cells asegs m (a + 4) cs ->
  rw_cells asegs m a (C4 (Z_to_bv 64 v) :: cs).
Proof.
  intros m a v cs HF HW HR. apply (proj2 (rw_cells_app asegs m a [C4 (Z_to_bv 64 v)] cs)).
  split; [exact (hg_rw4 m a v HF HW) | exact HR].
Qed.

Lemma hg_rw5 : forall m a v0 v1 v2 v3 v4, wr_at asegs m a 20 -> fldA m a 4 v0 -> fldA m (a + 4) 4 v1 -> fldA m (a + 8) 4 v2 ->
  fldA m (a + 12) 4 v3 -> fldA m (a + 16) 4 v4 ->
  rw_cells asegs m a [C4 (Z_to_bv 64 v0); C4 (Z_to_bv 64 v1); C4 (Z_to_bv 64 v2); C4 (Z_to_bv 64 v3); C4 (Z_to_bv 64 v4)].
Proof.
  intros m a v0 v1 v2 v3 v4 W F0 F1 F2 F3 F4. pose proof W as (W0 & W1 & _).
  apply hg_rw_cons4; [exact F0 | eapply rw_wr_at_sub; [exact W | lia | lia] |].
  apply hg_rw_cons4; [exact F1 | eapply rw_wr_at_sub; [exact W | lia | lia] |].
  replace (a + 4 + 4) with (a + 8) by lia.
  apply hg_rw_cons4; [exact F2 | eapply rw_wr_at_sub; [exact W | lia | lia] |].
  replace (a + 8 + 4) with (a + 12) by lia.
  apply hg_rw_cons4; [exact F3 | eapply rw_wr_at_sub; [exact W | lia | lia] |].
  replace (a + 12 + 4) with (a + 16) by lia.
  apply hg_rw4; [exact F4 | eapply rw_wr_at_sub; [exact W | lia | lia]].
Qed.

Lemma hg_sh_at : forall m A n o x k, addressable m A n -> x = A + o -> 0 <= o < n ->
  nth_error (shadow_of n) (Z.to_nat (o / 8)) = Some (b8 k) -> 0 <= k < 256 -> shk m x k.
Proof.
  intros m A n o x k (Hn & SH) -> Ho E Hk. pose proof SH as (HA & HA8 & _).
  destruct (LbB_Conv.shk_of_SHAD m A _ (A + o) SH) as (bt & Hb & K).
  { rewrite shadow_of_length by lia. unfold nsh. Z.div_mod_to_equations. nia. }
  replace (A + o - A) with o in Hb by lia. rewrite E in Hb. injection Hb as <-.
  unfold b8 in K. rewrite Z_to_bv_unsigned, bv_wrap_small in K by (change (bv_modulus 8) with 256; lia). exact K.
Qed.

Ltac hg_conj := repeat match goal with |- _ /\ _ => split end.
Ltac hg_in := simpl In; repeat first [left; reflexivity | right].

Section HGP.
  Context {HCEIL : HeapCeil}.
  Hypothesis HFW : fixword_stmtA.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : mem) (lo b code n e h : Z) (ws : list Z).
  Hypothesis ST : stk asegs m0 lo (bv_unsigned sp).
  Hypothesis CE : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - HG_STACK.
  Hypothesis S16 : bv_unsigned sp mod 16 = 0.
  Hypothesis S47 : bv_unsigned sp <= 2 ^ 47.
  Hypothesis MIm : mem_inv asegs m0.
  Hypothesis ACm : ACONST m0.
  Hypothesis HP : hg_pre (b, code, n, e, h, ws) m0 (bv_unsigned sp) a0 a1 a2 a3.

  Local Abbreviation SP := (bv_unsigned sp).

  Definition hgW : list (Z * Z) := [(SP - 64, SP); (h, h + 32)].
  Definition hgM (m : mem) : Prop := munch hgW m0 m /\ wmono asegs m0 m /\ mem_inv asegs m.
  Definition hgFR (m : mem) : Prop :=
    fldA m (SP - 56) 8 (bv_unsigned s5) /\ fldA m (SP - 48) 8 (bv_unsigned s4) /\ fldA m (SP - 40) 8 (bv_unsigned s3)
    /\ fldA m (SP - 32) 8 (bv_unsigned s2) /\ fldA m (SP - 24) 8 (bv_unsigned s1) /\ fldA m (SP - 16) 8 (bv_unsigned s0)
    /\ fldA m (SP - 8) 8 (bv_unsigned ra).
  Definition hgKR (R : bvmap 5 word) : Prop :=
    getr R 3 = gp /\ getr R 4 = tp /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9
    /\ getr R 26 = s10 /\ getr R 27 = s11.
  Definition hgRG (R : bvmap 5 word) : Prop :=
    getr R 2 = wz (SP - 64) /\ getr R 8 = wz b /\ getr R 9 = wz h /\ getr R 18 = wz e /\ getr R 19 = wz (-4)
    /\ getr R 20 = wz ASHADOW_BASE /\ getr R 21 = wz (sh b).
  Definition hgQ : machine_state -> Prop :=
    tl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HG_STACK [(h, h + 32)] lo m0
      (hg_post (b, code, n, e, h, ws) m0).
  Definition hgw (i : Z) : Z := Znth i ws mod 2 ^ 32.

  Lemma hg_wb : forall i, 0 <= hgw i < 2 ^ 32.
  Proof. intros i. unfold hgw. apply Z.mod_pos_bound. lia. Qed.

  Lemma hg_geo : 0x7fff7f800040 <= SP <= 2 ^ 47 /\ SP mod 16 = 0 /\ 0x7fff7f800000 <= lo <= SP - 64
    /\ 0x6e8000 <= b <= 2 ^ 47 - 16 /\ b mod 8 = 0 /\ 0x6e8000 <= code <= 2 ^ 47 - 20 /\ code mod 8 = 0
    /\ 0 <= e <= 1 /\ 0x6e8000 <= h <= 2 ^ 47 - 32 /\ h mod 8 = 0.
  Proof.
    pose proof HP as (_ & _ & _ & _ & _ & Pb8 & _ & Pb1 & Pb2 & _ & Pe & Ph8 & Pht & _ & _ & Pc1 & _ & Pc2 & _ & _ & _ & _ & Pca & _).
    pose proof aceil_facts as ((A1 & A2) & _). destruct Pht as (_ & _ & _ & _ & T). destruct Pca as (_ & Pca'). destruct Pca' as (_ & C8 & _).
    unfold HG_STACK, AIMG_TOP in *. lia.
  Qed.

  Lemma hg_dj : rw_keep (b + 16 <= SP - 64 \/ SP <= b) /\ rw_keep (code + 20 <= SP - 64 \/ SP <= code)
    /\ rw_keep (h + 32 <= SP - 64 \/ SP <= h) /\ rw_keep (h + 32 <= b \/ b + 16 <= h) /\ rw_keep (h + 32 <= code \/ code + 20 <= h)
    /\ rw_keep (h + 32 <= HG_LB \/ HG_HB <= h).
  Proof.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Pbs & _ & _ & Pht & _ & Phb & _ & _ & _ & Pcs & _ & _ & _ & _ & Phc).
    destruct Pht as (_ & _ & _ & T1 & T2). unfold rw_keep, HG_STACK, TL_STACK, HG_LB, HG_HB in *. lia.
  Qed.

  Lemma hg_stk : forall m, hgM m -> stk asegs m lo SP.
  Proof.
    intros m (_ & WM & _). apply (BakeStackRep.stk_high_transport m0 m lo SP ST WM).
    pose proof aceil_facts as ((A1 & _) & _). unfold AIMG_TOP. lia.
  Qed.

  Lemma hg_ac : forall m, hgM m -> ACONST m.
  Proof.
    intros m (MU & WM & _). apply (ACONST_frame hgW m0 m ACm MU WM). unfold hgW.
    pose proof hg_geo as (G & _). pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pht & _).
    destruct Pht as (_ & _ & AO & _).
    apply Forall_cons; [|apply Forall_cons; [exact AO | apply Forall_nil]].
    apply aconst_ok_high; [replace (sh AIMG_TOP) with 2148356096 by reflexivity; lia | right; left; lia].
  Qed.

  Lemma hg_mstep : forall Wc m m', hgM m -> sub_fp Wc hgW -> munch Wc m m' -> wmono asegs m m' -> mem_inv asegs m' -> hgM m'.
  Proof.
    intros Wc m m' (MU & WM & _) SF MU' WM' MI'. split; [|split; [eapply wmono_trans; eassumption | exact MI']].
    eapply munch_trans; [exact MU | eapply munch_weaken; eassumption].
  Qed.

  Lemma hg_fb : forall m, hgM m -> fldA m b 8 code.
  Proof.
    intros m (MU & _ & _). pose proof hg_geo as G. pose proof hg_dj as (D1 & _ & _ & D4 & _). unfold rw_keep in *.
    pose proof HP as (_ & _ & _ & Pc & _).
    eapply hg_fld_tr8; [exact MU | lia | lia | | exact Pc]. unfold hgW; cbn [disjoint_from]. hg_conj; [lia | lia | exact I].
  Qed.

  Lemma hg_fws : forall m, hgM m -> fldA m code 4 (hgw 0) /\ fldA m (code + 4) 4 (hgw 1) /\ fldA m (code + 8) 4 (hgw 2)
    /\ fldA m (code + 12) 4 (hgw 3) /\ fldA m (code + 16) 4 (hgw 4).
  Proof.
    intros m (MU & _ & _). pose proof hg_geo as G. pose proof hg_dj as (_ & D2 & _ & _ & D5 & _). unfold rw_keep in *.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pw & _).
    assert (K : forall i, 0 <= i < 5 -> fldA m (code + 4 * i) 4 (hgw i)).
    { intros i Hi. apply hg_fld4_mod. eapply hg_fld_tr4; [exact MU | lia | lia | | exact (Pw i Hi)].
      unfold hgW; cbn [disjoint_from]. hg_conj; [lia | lia | exact I]. }
    pose proof (K 0 ltac:(lia)) as K0. pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
    pose proof (K 3 ltac:(lia)) as K3. pose proof (K 4 ltac:(lia)) as K4.
    replace (code + 4 * 0) with code in K0 by lia. replace (code + 4 * 1) with (code + 4) in K1 by lia.
    replace (code + 4 * 2) with (code + 8) in K2 by lia. replace (code + 4 * 3) with (code + 12) in K3 by lia.
    replace (code + 4 * 4) with (code + 16) in K4 by lia. tauto.
  Qed.

  Lemma hg_sh_tr : forall m x k, hgM m -> 0 <= x < 2 ^ 47 -> shk m0 x k -> shk m x k.
  Proof.
    intros m x k (MU & _ & _) Hx K. pose proof hg_geo as (G1 & _ & _ & _ & _ & _ & _ & _ & Gh & _).
    pose proof hg_dj as (_ & _ & _ & _ & _ & D6). unfold rw_keep, HG_LB, HG_HB in D6.
    eapply hg_shk_tr; [exact MU | exact Hx | | exact K].
    unfold hgW, SHBASE. cbn [outside]. clear - G1 Gh D6 Hx. Z.div_mod_to_equations. lia.
  Qed.

  Ltac hg_sh1 Hm AD A n o := apply (hg_sh_tr _ _ _ Hm); [lia | apply (hg_sh_at _ A n o); [exact AD | lia | lia | reflexivity | lia]].

  Ltac hg_shf Hm AD A n o := apply (hg_sh_tr _ _ _ Hm); [lia | apply (hg_sh_at _ A n o); [exact AD | lia | lia
    | apply shadow_of_nth_full; [lia | rewrite Z2Nat.id by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia] | lia]].

  Lemma hg_shs : forall m, hgM m ->
    sh0 m b /\ sh0 m (b + 8) /\ sh0 m code /\ sh0 m (code + 4) /\ sh0 m (code + 8) /\ sh0 m (code + 12)
    /\ sh0 m h /\ sh0 m (h + 4) /\ sh0 m (h + 8) /\ sh0 m (h + 12) /\ sh0 m (h + 16) /\ sh0 m (h + 24).
  Proof.
    intros m Hm. pose proof hg_geo as (_ & _ & _ & Gb & _ & Gc & _ & _ & Gh & _).
    pose proof HP as (_ & _ & _ & _ & _ & _ & Pba & _ & _ & _ & _ & _ & _ & Pha & _ & _ & _ & _ & _ & Pn & _ & _ & Pca & _).
    unfold sh0.
    split; [hg_sh1 Hm Pba b 16 0|]. split; [hg_sh1 Hm Pba b 16 8|].
    split; [hg_shf Hm Pca code (4 * n) 0|]. split; [hg_shf Hm Pca code (4 * n) 4|].
    split; [hg_shf Hm Pca code (4 * n) 8|]. split; [hg_shf Hm Pca code (4 * n) 12|].
    split; [hg_sh1 Hm Pha h 32 0|]. split; [hg_sh1 Hm Pha h 32 4|]. split; [hg_sh1 Hm Pha h 32 8|].
    split; [hg_sh1 Hm Pha h 32 12|]. split; [hg_sh1 Hm Pha h 32 16|]. hg_sh1 Hm Pha h 32 24.
  Qed.

  Lemma hg_sh16a : forall m, hgM m -> n = 5 -> shk m (code + 16) 4.
  Proof.
    intros m Hm N. pose proof hg_geo as (_ & _ & _ & _ & _ & Gc & _).
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pca & _).
    replace (4 * n) with 20 in Pca by lia. hg_sh1 Hm Pca code 20 16.
  Qed.

  Lemma hg_sh16z : forall m, hgM m -> 6 <= n -> sh0 m (code + 16).
  Proof.
    intros m Hm N. pose proof hg_geo as (_ & _ & _ & _ & _ & Gc & _).
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pca & _).
    unfold sh0. hg_shf Hm Pca code (4 * n) 16.
  Qed.

  Lemma hg_wrh : forall m, hgM m -> wr_at asegs m h 32.
  Proof.
    intros m (_ & WM & _). pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pht & _).
    destruct Pht as (W & _). exact (hg_wr_tr m0 m h 32 WM W).
  Qed.

  Lemma hg_fr_tr : forall Wc m m', munch Wc m m' -> disjoint_from Wc (SP - 56) 56 -> hgFR m -> hgFR m'.
  Proof.
    intros Wc m m' MU D (F1 & F2 & F3 & F4 & F5 & F6 & F7). pose proof hg_geo as (G & _).
    unfold hgFR. hg_conj; (eapply hg_fld_tr8; [exact MU | lia | lia | eapply hg_dj_sub; [exact D | lia | lia] | eassumption]).
  Qed.

  Lemma hg_kr_keep : forall R R', hgKR R ->
    (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r) -> hgKR R'.
  Proof.
    intros R R' (K3 & K4 & K22 & K23 & K24 & K25 & K26 & K27) QK. unfold hgKR.
    rewrite !QK by hg_in. tauto.
  Qed.

  Lemma hg_call : forall (Q : machine_state -> Prop) R m w e' rp,
    rfull R -> hgKR R -> hgRG R -> getr R 1 = wz rp -> 0 <= rp < 2 ^ 64 -> rp mod 2 = 0 ->
    getr R 10 = wz (sx32A w) -> getr R 11 = wz e' -> 0 <= w < 2 ^ 32 -> 0 <= e' < 2 ^ 32 -> hgM m ->
    (forall R' m' r, rfull R' -> hgKR R' -> hgRG R' -> munch [] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
       0 <= r < 2 ^ 32 -> getr R' 10 = wz (sx32A r) -> evt asegs Q (MS R' F (wz rp) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS R F (wz AT_FIXWORD) fc None m (seg_rom asegs)).
  Proof.
    intros Q R m w e' rp RF KR RG G1 Hrp Hev G10 G11 Hw He Hm K.
    pose proof hg_geo as (G & GS & GL & _).
    pose proof RG as (G2 & _).
    assert (U2 : bv_unsigned (getr R 2) = SP - 64) by (rewrite G2; unfold wz; rewrite u64_of_Z by lia; reflexivity).
    rewrite (rfull_eq R RF).
    eapply evt_cut.
    { apply (HFW (w, e') (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31) F fc m lo);
        rewrite ?U2.
      - exact (proj1 (stk_split asegs m lo (SP - 64) SP (hg_stk m Hm) ltac:(lia))).
      - exact CE.
      - lia.
      - clear - GS. Z.div_mod_to_equations. lia.
      - lia.
      - exact (proj2 (proj2 Hm)).
      - exact (hg_ac m Hm).
      - split; [lia|]. split; [exact G10|]. split; [lia | exact G11]. }
    intros ms1 P1.
    destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & AC1
                    & (r & Hr & Hb0)).
    subst ms1.
    replace (ret_pc (getr R 1)) with (wz rp) by (rewrite G1; symmetry; exact (ret_pc_even rp Hrp Hev)).
    apply (K _ m1 r); [apply rfull_mkR | exact KR | exact RG | | exact WM1 | exact MI1 | exact Hr | exact Hb0].
    intros y _. apply MU1. split; [lia | exact I].
  Qed.

  Lemma hg_exit : forall R m, rfull R -> getr R 1 = ra -> getr R 2 = sp -> hgKR R ->
    getr R 8 = s0 -> getr R 9 = s1 -> getr R 18 = s2 -> getr R 19 = s3 -> getr R 20 = s4 -> getr R 21 = s5 -> hgM m ->
    hg_post (b, code, n, e, h, ws) m0 (getr R 10) (getr R 11) m ->
    evt asegs hgQ (MS R F (wz (AHDR_GET + 680)) fc None m (seg_rom asegs)).
  Proof.
    intros R m RF G1 G2 (K3 & K4 & K22 & K23 & K24 & K25 & K26 & K27) G8 G9 G18 G19 G20 G21 Hm HQ.
    rewrite (rfull_eq R RF). apply hg_ret.
    rewrite G1, G2, K3, K4, G8, G9, G18, G19, G20, G21, K22, K23, K24, K25, K26, K27.
    unfold hgQ, tl_post.
    exists (getr R 5), (getr R 6), (getr R 7), (getr R 10), (getr R 11), (getr R 12), (getr R 13), (getr R 14), (getr R 15),
      (getr R 16), (getr R 17), (getr R 28), (getr R 29), (getr R 30), (getr R 31), m.
    split; [reflexivity|]. split; [exact (proj1 Hm)|]. split; [exact (proj1 (proj2 Hm))|].
    split; [exact (proj2 (proj2 Hm))|]. split; [exact (hg_stk m Hm)|]. split; [exact (hg_ac m Hm)|]. exact HQ.
  Qed.

  Ltac hg_ctx m Hm :=
    pose proof hg_geo as (Gs & Gs16 & Glo & Gb & Gb8 & Gc & Gc8 & Ge & Gh & Gh8);
    pose proof hg_dj as (D1 & D2 & D3 & D4 & D5 & D6);
    pose proof (hg_fb m Hm) as Fb; pose proof (hg_wrh m Hm) as Wh;
    pose proof (hg_shs m Hm) as (Sb & Sb8 & Sc0 & Sc4 & Sc8 & Sc12 & Sh0 & Sh4 & Sh8 & Sh12 & Sh16 & Sh24).

  Ltac hg_mi Hm MU WM MI := eapply hg_mstep; [exact Hm | | exact MU | exact WM | exact MI];
    unfold sub_fp, hgW; intros xx Hxx; cbn [outside] in Hxx |- *; hg_conj; first [exact I | lia].

  Ltac hg_djfr := cbn [disjoint_from]; hg_conj; first [exact I | unfold rw_keep in *; lia].

  Ltac hg_tr4s MU := eapply hg_fld_tr4; [exact MU | lia | lia | cbn [disjoint_from]; hg_conj; first [exact I | lia] | eassumption].

  Ltac hg_tr4c MU2 MU := eapply hg_fld_tr4; [exact MU2 | lia | lia | exact I | hg_tr4s MU].

  Ltac hg_bvu Q := rewrite Q; apply Z_to_bv_bv_unsigned.

  Lemma hg_s6 : forall R m rm rv rg rb rs, rfull R -> hgM m -> hgFR m -> hgKR R -> hgRG R ->
    getr R 10 = wz (sx32A rs) -> 0 <= rs < 2 ^ 32 ->
    fldA m h 4 rm -> fldA m (h + 4) 4 rv -> fldA m (h + 8) 4 rg -> fldA m (h + 12) 4 rb ->
    0 <= rm < 2 ^ 32 -> 0 <= rv < 2 ^ 32 -> 0 <= rg < 2 ^ 32 -> 0 <= rb < 2 ^ 32 -> hg_ver_ok rv ->
    evt asegs hgQ (MS R F (wz (AHDR_GET + 556)) fc None m (seg_rom asegs)).
  Proof.
    intros R m rm rv rg rb rs RF Hm FR KR RG G10 Hrs H0 H4 H8 H12 Rm Rv Rg Rb VOK.
    hg_ctx m Hm. pose proof FR as (F1 & F2 & F3 & F4 & F5 & F6 & F7). pose proof RG as (G2 & G8 & G9 & G18 & G19 & G20 & G21).
    pose proof (hg_sx32_rng rs Hrs) as (Ss & Sm).
    destruct (hg_h6_ea2b4 R F fc m b code e h SP (sx32A rs) (bv_unsigned s5) (bv_unsigned s4) (bv_unsigned s3)
                (bv_unsigned s2) (bv_unsigned s1) (bv_unsigned s0) (bv_unsigned ra))
      as (R' & M' & MS & MU & WM & C24 & C16 & Q1 & Q2 & Q8 & Q9 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q21 & QK).
    { unfold hg_h6_pre. hg_conj; first [assumption | lia]. }
    eapply evt_of_msteps; [exact MS|].
    assert (Hm' : hgM M') by hg_mi Hm MU WM (msteps_mem_inv _ _ _ MS (proj2 (proj2 Hm))).
    apply hg_exit; [exact (msteps_full _ _ _ MS RF) | hg_bvu Q1 | hg_bvu Q2 | exact (hg_kr_keep R R' KR QK) | hg_bvu Q8 | hg_bvu Q9
      | hg_bvu Q18 | hg_bvu Q19 | hg_bvu Q20 | hg_bvu Q21 | exact Hm' |].
    left. split; [rewrite Q10; reflexivity|].
    exists rm, rv, rg, rb, rs. hg_conj; try lia; [exact VOK | |].
    - apply hg_rw5; [eapply rw_wr_at_sub; [exact (hg_wrh M' Hm') | lia | lia] | hg_tr4s MU | hg_tr4s MU | hg_tr4s MU | hg_tr4s MU |].
      rewrite <- Sm. exact (hg_fld4_mod _ _ _ C16).
    - apply hg_rw8; [exact C24 | eapply rw_wr_at_sub; [exact (hg_wrh M' Hm') | lia | lia]].
  Qed.

  Lemma hg_s5 : forall R m rm rv rg rb, rfull R -> hgM m -> hgFR m -> hgKR R -> hgRG R ->
    getr R 10 = wz (sx32A rb) -> 0 <= rb < 2 ^ 32 ->
    fldA m h 4 rm -> fldA m (h + 4) 4 rv -> fldA m (h + 8) 4 rg ->
    0 <= rm < 2 ^ 32 -> 0 <= rv < 2 ^ 32 -> 0 <= rg < 2 ^ 32 -> hg_ver_ok rv ->
    evt asegs hgQ (MS R F (wz (AHDR_GET + 468)) fc None m (seg_rom asegs)).
  Proof.
    intros R m rm rv rg rb RF Hm FR KR RG G10 Hrb H0 H4 H8 Rm Rv Rg VOK.
    hg_ctx m Hm. pose proof RG as (G2 & G8 & G9 & G18 & G19 & G20 & G21).
    pose proof (hg_sx32_rng rb Hrb) as (Ss & Sm).
    pose proof (hg_fws m Hm) as (_ & _ & _ & _ & W4). pose proof (hg_wb 4) as B4.
    assert (X : exists R' M',
      CatSim.msteps asegs (MS R F (wz (AHDR_GET + 468)) fc None m (seg_rom asegs)) (MS R' F (wz AT_FIXWORD) fc None M' (seg_rom asegs))
      /\ munch [((h + 12), (h + 16))] m M' /\ wmono asegs m M' /\ fldA M' (h + 12) 4 (sx32A rb)
      /\ getr R' 1 = wz (AHDR_GET + 556) /\ hgRG R' /\ getr R' 11 = wz e /\ getr R' 10 = wz (sx32A (hgw 4))
      /\ (forall r, In r [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r)).
    { pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pn & _).
      assert (N : n = 5 \/ 6 <= n) by lia. destruct N as [N5 | N6].
      - pose proof (hg_sh16a m Hm N5) as Sc16.
        destruct (hg_h5w R F fc m b code e h SP (sx32A rb) (hgw 4))
          as (R' & M' & MS & MU & WM & C & Q1 & Q2 & Q8 & Q9 & Q11 & _ & Q18 & Q19 & Q20 & Q21 & Q10 & QK).
        { unfold hg_h5_pre. hg_conj; first [assumption | lia]. }
        exists R', M'. hg_conj; [exact MS | exact MU | exact WM | exact C | exact Q1
          | exact (conj Q2 (conj Q8 (conj Q9 (conj Q18 (conj Q19 (conj Q20 Q21)))))) | exact Q11 | exact Q10 | exact QK].
      - pose proof (hg_sh16z m Hm N6) as Sc16.
        destruct (hg_h5zw R F fc m b code e h SP (sx32A rb) (hgw 4))
          as (R' & M' & MS & MU & WM & C & Q1 & Q2 & Q8 & Q9 & Q11 & _ & Q18 & Q19 & Q20 & Q21 & Q10 & QK).
        { unfold hg_h5z_pre. hg_conj; first [assumption | lia]. }
        exists R', M'. hg_conj; [exact MS | exact MU | exact WM | exact C | exact Q1
          | exact (conj Q2 (conj Q8 (conj Q9 (conj Q18 (conj Q19 (conj Q20 Q21)))))) | exact Q11 | exact Q10 | exact QK]. }
    destruct X as (R' & M' & MS & MU & WM & C & Q1 & RG' & Q11 & Q10 & QK).
    eapply evt_of_msteps; [exact MS|].
    assert (Hm' : hgM M') by hg_mi Hm MU WM (msteps_mem_inv _ _ _ MS (proj2 (proj2 Hm))).
    assert (FR' : hgFR M') by (eapply hg_fr_tr; [exact MU | hg_djfr | exact FR]).
    pose proof (hg_fld4_mod _ _ _ C) as C'. rewrite Sm in C'.
    apply (hg_call _ R' M' (hgw 4) e (AHDR_GET + 556)); [exact (msteps_full _ _ _ MS RF) | exact (hg_kr_keep R R' KR QK)
      | exact RG' | exact Q1 | unfold AHDR_GET; lia | reflexivity
      | exact Q10 | exact Q11 | exact B4 | lia | exact Hm' |].
    intros R2 m2 r RF2 KR2 RG2 MU2 WM2 MI2 Hr G10'.
    apply (hg_s6 R2 m2 rm rv rg rb r RF2); [hg_mi Hm' MU2 WM2 MI2 | eapply hg_fr_tr; [exact MU2 | exact I | exact FR'] | exact KR2
      | exact RG2 | exact G10' | exact Hr | hg_tr4c MU2 MU | hg_tr4c MU2 MU | hg_tr4c MU2 MU | hg_tr4s MU2 | exact Rm | exact Rv
      | exact Rg | exact Hrb | exact VOK].
  Qed.

  Lemma hg_s4 : forall R m rm rv rg, rfull R -> hgM m -> hgFR m -> hgKR R -> hgRG R ->
    getr R 10 = wz (sx32A rg) -> 0 <= rg < 2 ^ 32 -> fldA m h 4 rm -> fldA m (h + 4) 4 rv ->
    0 <= rm < 2 ^ 32 -> 0 <= rv < 2 ^ 32 -> hg_ver_ok rv ->
    evt asegs hgQ (MS R F (wz (AHDR_GET + 380)) fc None m (seg_rom asegs)).
  Proof.
    intros R m rm rv rg RF Hm FR KR RG G10 Hrg H0 H4 Rm Rv VOK.
    hg_ctx m Hm. pose proof RG as (G2 & G8 & G9 & G18 & G19 & G20 & G21).
    pose proof (hg_sx32_rng rg Hrg) as (Ss & Sm).
    pose proof (hg_fws m Hm) as (_ & _ & _ & W3 & _). pose proof (hg_wb 3) as B3.
    destruct (hg_h4w R F fc m b code e h SP (sx32A rg) (hgw 3))
      as (R' & M' & MS & MU & WM & C & Q1 & Q2 & Q8 & Q9 & Q11 & Q12 & Q18 & Q19 & Q20 & Q21 & Q10 & QK).
    { unfold hg_h4_pre. hg_conj; first [assumption | lia]. }
    eapply evt_of_msteps; [exact MS|].
    assert (Hm' : hgM M') by hg_mi Hm MU WM (msteps_mem_inv _ _ _ MS (proj2 (proj2 Hm))).
    assert (FR' : hgFR M') by (eapply hg_fr_tr; [exact MU | hg_djfr | exact FR]).
    pose proof (hg_fld4_mod _ _ _ C) as C'. rewrite Sm in C'.
    apply (hg_call _ R' M' (hgw 3) e (AHDR_GET + 468)); [exact (msteps_full _ _ _ MS RF) | exact (hg_kr_keep R R' KR QK)
      | exact (conj Q2 (conj Q8 (conj Q9 (conj Q18 (conj Q19 (conj Q20 Q21)))))) | exact Q1 | unfold AHDR_GET; lia | reflexivity
      | exact Q10 | exact Q11 | exact B3 | lia | exact Hm' |].
    intros R2 m2 r RF2 KR2 RG2 MU2 WM2 MI2 Hr G10'.
    apply (hg_s5 R2 m2 rm rv rg r RF2); [hg_mi Hm' MU2 WM2 MI2 | eapply hg_fr_tr; [exact MU2 | exact I | exact FR'] | exact KR2
      | exact RG2 | exact G10' | exact Hr | hg_tr4c MU2 MU | hg_tr4c MU2 MU | hg_tr4s MU2 | exact Rm | exact Rv | exact Hrg
      | exact VOK].
  Qed.

  Lemma hg_s3 : forall R m rm rv, rfull R -> hgM m -> hgFR m -> hgKR R -> hgRG R ->
    getr R 10 = wz (sx32A rv) -> 0 <= rv < 2 ^ 32 -> fldA m h 4 rm -> 0 <= rm < 2 ^ 32 ->
    evt asegs hgQ (MS R F (wz (AHDR_GET + 260)) fc None m (seg_rom asegs)).
  Proof.
    intros R m rm rv RF Hm FR KR RG G10 Hrv H0 Rm.
    hg_ctx m Hm. pose proof FR as (F1 & F2 & F3 & F4 & F5 & F6 & F7). pose proof RG as (G2 & G8 & G9 & G18 & G19 & G20 & G21).
    pose proof (hg_sx32_rng rv Hrv) as (Ss & Sm).
    pose proof (hg_fws m Hm) as (_ & _ & W2 & _ & _). pose proof (hg_wb 2) as B2.
    assert (LB1 : 0 <= Z.land (sx32A rv) HG_K1) by (apply Z.land_nonneg; lia).
    assert (LB2 : Z.land (sx32A rv) HG_K1 <= 2 ^ 64 - 1)
      by (pose proof (land_le_l (sx32A rv) HG_K1 ltac:(lia) ltac:(unfold HG_K1; lia)); lia).
    assert (Hm1 : forall M', munch [(h + 4, h + 8)] m M' -> wmono asegs m M' -> mem_inv asegs M' -> hgM M')
      by (intros M' MU WM MI; hg_mi Hm MU WM MI).
    destruct (Z.eq_dec (Z.land (sx32A rv) HG_K1) 0) as [L0 | LN].
    2: {
      destruct (hg_h3x_ea2b4 R F fc m b code e h SP (sx32A rv) (hgw 2) (bv_unsigned s5) (bv_unsigned s4) (bv_unsigned s3)
                  (bv_unsigned s2) (bv_unsigned s1) (bv_unsigned s0) (bv_unsigned ra))
        as (R' & M' & MS & MU & WM & C & Q1 & Q2 & Q8 & Q9 & Q10 & Q11 & Q18 & Q19 & Q20 & Q21 & QK);
        [unfold hg_h3x_pre; hg_conj; first [assumption | lia] | exact LN |].
      eapply evt_of_msteps; [exact MS|].
      apply hg_exit; [exact (msteps_full _ _ _ MS RF) | hg_bvu Q1 | hg_bvu Q2 | exact (hg_kr_keep R R' KR QK) | hg_bvu Q8 | hg_bvu Q9
        | hg_bvu Q18 | hg_bvu Q19 | hg_bvu Q20 | hg_bvu Q21 | exact (Hm1 M' MU WM (msteps_mem_inv _ _ _ MS (proj2 (proj2 Hm))))
        | right; rewrite Q10; apply bv_eq; reflexivity]. }
    pose proof (hg_land_small (sx32A rv) Ss L0) as L24.
    destruct (Z_le_gt_dec (sx32A rv) 65535) as [Ra | Ra].
    {
      destruct (hg_h3a_ea2b4 R F fc m b code e h SP (sx32A rv) (hgw 2) (bv_unsigned s5) (bv_unsigned s4) (bv_unsigned s3)
                  (bv_unsigned s2) (bv_unsigned s1) (bv_unsigned s0) (bv_unsigned ra))
        as (R' & M' & MS & MU & WM & C & Q1 & Q2 & Q8 & Q9 & Q10 & Q11 & Q18 & Q19 & Q20 & Q21 & QK);
        [unfold hg_h3a_pre; hg_conj; first [assumption | lia] | exact L0 |].
      eapply evt_of_msteps; [exact MS|].
      apply hg_exit; [exact (msteps_full _ _ _ MS RF) | hg_bvu Q1 | hg_bvu Q2 | exact (hg_kr_keep R R' KR QK) | hg_bvu Q8 | hg_bvu Q9
        | hg_bvu Q18 | hg_bvu Q19 | hg_bvu Q20 | hg_bvu Q21 | exact (Hm1 M' MU WM (msteps_mem_inv _ _ _ MS (proj2 (proj2 Hm))))
        | right; rewrite Q10; apply bv_eq; reflexivity]. }
    destruct (Z_le_gt_dec (sx32A rv) 67072) as [Rv | Rv].
    2: {
      destruct (hg_h3b_ea2b4 R F fc m b code e h SP (sx32A rv) (hgw 2) (bv_unsigned s5) (bv_unsigned s4) (bv_unsigned s3)
                  (bv_unsigned s2) (bv_unsigned s1) (bv_unsigned s0) (bv_unsigned ra))
        as (R' & M' & MS & MU & WM & C & Q1 & Q2 & Q8 & Q9 & Q10 & Q11 & Q18 & Q19 & Q20 & Q21 & QK);
        [unfold hg_h3b_pre; hg_conj; first [assumption | lia] | exact L0 |].
      eapply evt_of_msteps; [exact MS|].
      apply hg_exit; [exact (msteps_full _ _ _ MS RF) | hg_bvu Q1 | hg_bvu Q2 | exact (hg_kr_keep R R' KR QK) | hg_bvu Q8 | hg_bvu Q9
        | hg_bvu Q18 | hg_bvu Q19 | hg_bvu Q20 | hg_bvu Q21 | exact (Hm1 M' MU WM (msteps_mem_inv _ _ _ MS (proj2 (proj2 Hm))))
        | right; rewrite Q10; apply bv_eq; reflexivity]. }
    destruct (hg_h3vw R F fc m b code e h SP (sx32A rv) (hgw 2))
      as (R' & M' & MS & MU & WM & C & Q1 & Q2 & Q8 & Q9 & Q11 & Q18 & Q19 & Q20 & Q21 & Q10 & QK);
      [unfold hg_h3v_pre; hg_conj; first [assumption | lia] | exact L0 |].
    eapply evt_of_msteps; [exact MS|].
    assert (E1 : sx32A rv = rv) by (rewrite Z.mod_small in Sm by lia; exact Sm).
    assert (Hm' : hgM M') by exact (Hm1 M' MU WM (msteps_mem_inv _ _ _ MS (proj2 (proj2 Hm)))).
    assert (FR' : hgFR M') by (eapply hg_fr_tr; [exact MU | hg_djfr | exact FR]).
    rewrite E1 in C.
    apply (hg_call _ R' M' (hgw 2) e (AHDR_GET + 380)); [exact (msteps_full _ _ _ MS RF) | exact (hg_kr_keep R R' KR QK)
      | exact (conj Q2 (conj Q8 (conj Q9 (conj Q18 (conj Q19 (conj Q20 Q21)))))) | exact Q1 | unfold AHDR_GET; lia | reflexivity
      | exact Q10 | exact Q11 | exact B2 | lia | exact Hm' |].
    intros R2 m2 r RF2 KR2 RG2 MU2 WM2 MI2 Hr G10'.
    apply (hg_s4 R2 m2 rm rv r RF2); [hg_mi Hm' MU2 WM2 MI2 | eapply hg_fr_tr; [exact MU2 | exact I | exact FR'] | exact KR2
      | exact RG2 | exact G10' | exact Hr | hg_tr4c MU2 MU | hg_tr4s MU2 | exact Rm | exact Hrv
      | rewrite <- E1; apply hg_ver_of; [exact L0 | lia]].
  Qed.

  Lemma hg_s2 : forall R m rm, rfull R -> hgM m -> hgFR m -> hgKR R -> hgRG R -> getr R 10 = wz (sx32A rm) -> 0 <= rm < 2 ^ 32 ->
    evt asegs hgQ (MS R F (wz (AHDR_GET + 172)) fc None m (seg_rom asegs)).
  Proof.
    intros R m rm RF Hm FR KR RG G10 Hrm.
    hg_ctx m Hm. pose proof RG as (G2 & G8 & G9 & G18 & G19 & G20 & G21).
    pose proof (hg_sx32_rng rm Hrm) as (Ss & Sm).
    pose proof (hg_fws m Hm) as (_ & W1 & _). pose proof (hg_wb 1) as B1.
    destruct (hg_h2w R F fc m b code e h SP (sx32A rm) (hgw 1))
      as (R' & M' & MS & MU & WM & C & Q1 & Q2 & Q8 & Q9 & Q11 & Q12 & Q18 & Q19 & Q20 & Q21 & Q10 & QK).
    { unfold hg_h2_pre. hg_conj; first [assumption | lia]. }
    eapply evt_of_msteps; [exact MS|].
    assert (Hm' : hgM M') by hg_mi Hm MU WM (msteps_mem_inv _ _ _ MS (proj2 (proj2 Hm))).
    assert (FR' : hgFR M') by (eapply hg_fr_tr; [exact MU | hg_djfr | exact FR]).
    pose proof (hg_fld4_mod _ _ _ C) as C'. rewrite Sm in C'.
    apply (hg_call _ R' M' (hgw 1) e (AHDR_GET + 260)); [exact (msteps_full _ _ _ MS RF) | exact (hg_kr_keep R R' KR QK)
      | exact (conj Q2 (conj Q8 (conj Q9 (conj Q18 (conj Q19 (conj Q20 Q21)))))) | exact Q1 | unfold AHDR_GET; lia | reflexivity
      | exact Q10 | exact Q11 | exact B1 | lia | exact Hm' |].
    intros R2 m2 r RF2 KR2 RG2 MU2 WM2 MI2 Hr G10'.
    apply (hg_s3 R2 m2 rm r RF2); [hg_mi Hm' MU2 WM2 MI2 | eapply hg_fr_tr; [exact MU2 | exact I | exact FR'] | exact KR2
      | exact RG2 | exact G10' | exact Hr | hg_tr4s MU2 | exact Hrm].
  Qed.

  Lemma hg_s1 : forall R, rfull R -> getr R 1 = ra -> getr R 2 = sp -> hgKR R -> getr R 8 = s0 -> getr R 9 = s1 ->
    getr R 18 = s2 -> getr R 19 = s3 -> getr R 20 = s4 -> getr R 21 = s5 -> getr R 10 = wz b -> getr R 11 = wz e ->
    getr R 12 = wz h -> evt asegs hgQ (MS R F (wz AHDR_GET) fc None m0 (seg_rom asegs)).
  Proof.
    intros R RF G1 G2 KR G8 G9 G18 G19 G20 G21 G10 G11 G12.
    assert (Hm : hgM m0) by (split; [apply munch_refl | split; [apply wmono_refl | exact MIm]]).
    hg_ctx m0 Hm.
    assert (G2' : getr R 2 = wz SP) by (rewrite G2; unfold wz; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Ws : wr_at asegs m0 (SP - 64) 64).
    { pose proof (rw_wr_at_of_stk asegs m0 (SP - 64) SP (proj2 (stk_split asegs m0 lo (SP - 64) SP ST ltac:(lia)))) as W.
      replace (SP - (SP - 64)) with 64 in W by lia. exact W. }
    pose proof HP as (_ & _ & _ & _ & Pn & _).
    pose proof (hg_fld8_mod m0 (b + 8) n Pn) as Fn.
    pose proof (Z.mod_pos_bound n (2 ^ 64) ltac:(lia)) as Bn.
    pose proof (hg_fws m0 Hm) as (W0 & _). pose proof (hg_wb 0) as B0.
    destruct (Z_le_gt_dec (n mod 2 ^ 64) 4) as [NS | NB].
    - destruct (hg_h1s_ea2b4 R F fc m0 b code (n mod 2 ^ 64) e h SP)
        as (R' & M' & MS & MU & WM & F1 & F2 & F3 & F4 & F5 & F6 & F7 & Q2 & Q10 & Q11 & Q12 & QK).
      { unfold hg_h1s_pre. hg_conj; first [assumption | lia]. }
      eapply evt_of_msteps; [exact MS|].
      pose proof KR as (K3 & K4 & K22 & K23 & K24 & K25 & K26 & K27).
      apply hg_exit; [exact (msteps_full _ _ _ MS RF) | rewrite QK by hg_in; exact G1 | hg_bvu Q2
        | unfold hgKR; rewrite !QK by hg_in; tauto | rewrite QK by hg_in; exact G8 | rewrite QK by hg_in; exact G9
        | rewrite QK by hg_in; exact G18 | rewrite QK by hg_in; exact G19 | rewrite QK by hg_in; exact G20
        | rewrite QK by hg_in; exact G21 | hg_mi Hm MU WM (msteps_mem_inv _ _ _ MS MIm)
        | right; rewrite Q10; apply bv_eq; reflexivity].
    - destruct (hg_h1w R F fc m0 b code (n mod 2 ^ 64) e h SP (hgw 0))
        as (R' & M' & MS & MU & WM & F1 & F2 & F3 & F4 & F5 & F6 & F7 & Q1 & Q2 & Q8 & Q9 & Q11 & Q12 & Q18 & Q19 & Q20 & Q21 & Q10
            & QK).
      { unfold hg_h1_pre. hg_conj; first [assumption | lia]. }
      eapply evt_of_msteps; [exact MS|].
      assert (Hm' : hgM M') by hg_mi Hm MU WM (msteps_mem_inv _ _ _ MS MIm).
      rewrite G21 in F1. rewrite G20 in F2. rewrite G19 in F3. rewrite G18 in F4. rewrite G9 in F5. rewrite G8 in F6.
      rewrite G1 in F7.
      assert (FR' : hgFR M') by (unfold hgFR; hg_conj; apply hg_fldw_A; assumption).
      assert (RG' : hgRG R').
      { unfold hgRG. hg_conj; try assumption. rewrite Q19. apply bv_eq. reflexivity. }
      apply (hg_call _ R' M' (hgw 0) e (AHDR_GET + 172)); [exact (msteps_full _ _ _ MS RF) | exact (hg_kr_keep R R' KR QK)
        | exact RG' | exact Q1 | unfold AHDR_GET; lia | reflexivity | exact Q10 | exact Q11 | exact B0 | lia | exact Hm' |].
      intros R2 m2 r RF2 KR2 RG2 MU2 WM2 MI2 Hr G10'.
      apply (hg_s2 R2 m2 r RF2); [hg_mi Hm' MU2 WM2 MI2 | eapply hg_fr_tr; [exact MU2 | exact I | exact FR'] | exact KR2
        | exact RG2 | exact G10' | exact Hr].
  Qed.
End HGP.

Section HGT.
  Context {HCEIL : HeapCeil}.

Theorem hdr_get_okA : fixword_stmtA -> hdr_get_stmt.
Proof.
  intros HFW. unfold hdr_get_stmt, tleaf.
  intros [[[[[b code] n] e] h] ws] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST CE LO S16 S47 MI AC HP.
  pose proof HP as (H10 & H11 & H12 & _).
  eapply hg_s1; try eassumption; try apply rfull_mkR; try reflexivity; try (unfold hgKR; hg_conj; reflexivity).
Qed.
End HGT.
