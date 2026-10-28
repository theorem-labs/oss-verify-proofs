(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem LbB_RwStm.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_Own LbB_HEmpStmt LbB_DStat.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmEmhW.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Record emh_inst : Type := EMHI { emh_entry : Z; emh_emp : emp_inst; emh_voff : Z }.
Definition EMH_EXT : emh_inst := EMHI 0xf9e90 EMP_EXT 20.
Definition EMH_U32 : emh_inst := EMHI 0xf9064 EMP_U32 20.

Definition AEMH_STACK : Z := 80 + AEMP_STACK.

Definition emh_sq (spz : Z) : Z := 32 * ((spz - 64) / 32).
Definition EMH_KEPT : list reg := [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition emh_A (I : emh_inst) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (obj spz keyp : Z),
    getr R 2 = wz spz -> getr R 10 = wz obj -> getr R 11 = wz keyp ->
    ACONST m -> fldA m AUAR_CELL 4 1 -> wr_at asegs m (spz - 64) 64 ->
    2 ^ 46 <= spz <= 2 ^ 47 -> spz mod 16 = 0 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (emh_entry I)) fc None m (seg_rom asegs)) (MS R' F (wz AFS_MALLOC_1) fc None M' (seg_rom asegs))
      /\ munch [(spz - 64, spz)] m M' /\ wmono asegs m M'
      /\ fldw asegs M' (spz - 48) 8 (getr R 20) /\ fldw asegs M' (spz - 40) 8 (getr R 19)
      /\ fldw asegs M' (spz - 32) 8 (getr R 18) /\ fldw asegs M' (spz - 24) 8 (getr R 9)
      /\ fldw asegs M' (spz - 16) 8 (getr R 8) /\ fldw asegs M' (spz - 8) 8 (getr R 1)
      /\ getr R' 1 = wz (emh_entry I + 88) /\ getr R' 2 = wz (emh_sq spz) /\ getr R' 8 = wz spz
      /\ getr R' 9 = wz (emh_sq spz) /\ getr R' 10 = wz 96 /\ getr R' 18 = wz keyp /\ getr R' 19 = wz SHBASE
      /\ getr R' 20 = wz obj /\ (forall r, In r EMH_KEPT -> getr R' r = getr R r).

Definition emh_B (I : emh_inst) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ff sq keyp obj spz : Z),
    getr R 10 = wz ff -> getr R 2 = wz sq -> getr R 9 = wz sq -> getr R 18 = wz keyp -> getr R 20 = wz obj ->
    getr R 8 = wz spz -> getr R 19 = wz SHBASE -> getr R 1 = wz (emh_entry I + 88) ->
    relro0 m -> wr_at asegs m (sq + 8) 8 -> wr_at asegs m ff 128 -> wr_at asegs m (sh ff) 16 ->
    AIMG_TOP <= ff -> ff + 128 <= sq -> ff mod 64 = 0 -> (ff + 128 <= 2147446784 \/ 17594333495296 <= ff) ->
    2 ^ 46 <= sq -> sq + 16 <= 2 ^ 47 -> sq mod 32 = 0 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (emh_entry I + 88)) fc None m (seg_rom asegs))
                          (MS R' F (wz (emp_entry (emh_emp I))) fc None M' (seg_rom asegs))
      /\ munch [(sq + 8, sq + 16); (ff, ff + 40); (sh ff, sh ff + 16)] m M' /\ wmono asegs m M'
      /\ fldA M' (ff + 32) 8 keyp /\ fldA M' (sh ff + 4) 1 0
      /\ getr R' 1 = wz (emh_entry I + 296) /\ getr R' 2 = wz sq /\ getr R' 8 = wz spz /\ getr R' 9 = wz sq
      /\ getr R' 10 = wz obj /\ getr R' 11 = wz keyp /\ getr R' 13 = wz (ff + 32)
      /\ getr R' 18 = wz ff /\ getr R' 19 = wz (sh ff) /\ getr R' 20 = wz ff
      /\ (forall r, In r EMH_KEPT -> getr R' r = getr R r).

Definition emh_C (I : emh_inst) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (p sq spz ff fp ra0 sv8 sv9 sv18 sv19 sv20 : Z),
    getr R 10 = wz p -> getr R 2 = wz sq -> getr R 9 = wz sq -> getr R 8 = wz spz -> getr R 18 = wz ff ->
    getr R 20 = wz ff -> getr R 19 = wz (sh ff) -> getr R 1 = wz (emh_entry I + 296) ->
    wr_at asegs m (sh ff) 16 -> wr_at asegs m ff 8 -> fldA m (ff + 120) 8 fp -> wr_at asegs m fp 1 ->
    fldA m (spz - 8) 8 ra0 -> fldA m (spz - 16) 8 sv8 -> fldA m (spz - 24) 8 sv9 ->
    fldA m (spz - 32) 8 sv18 -> fldA m (spz - 40) 8 sv19 -> fldA m (spz - 48) 8 sv20 ->
    1 <= p -> p + 24 <= 2 ^ 47 -> p mod 8 = 0 ->
    AIMG_TOP <= ff -> ff + 128 <= sq -> ff mod 64 = 0 -> (ff + 128 <= 2147446784 \/ 17594333495296 <= ff) ->
    AIMG_TOP <= fp -> fp + 1 <= ff -> (fp + 1 <= 2147446784 \/ 17594333495296 <= fp) ->
    2 ^ 46 + 64 <= spz -> spz <= 2 ^ 47 -> spz mod 16 = 0 -> 2 ^ 46 <= sq -> sq + 16 <= spz ->
    exists R' M',
      CatSim.msteps asegs (MS R F (wz (emh_entry I + 296)) fc None m (seg_rom asegs))
                          (MS R' F (wz (emh_entry I + 500)) fc None M' (seg_rom asegs))
      /\ munch [(sh ff, sh ff + 16); (ff, ff + 8); (fp, fp + 1)] m M' /\ wmono asegs m M'
      /\ fldA M' fp 1 0
      /\ getr R' 1 = wz ra0 /\ getr R' 2 = wz spz /\ getr R' 8 = wz sv8 /\ getr R' 9 = wz sv9
      /\ getr R' 10 = wz (p + emh_voff I) /\ getr R' 18 = wz sv18 /\ getr R' 19 = wz sv19 /\ getr R' 20 = wz sv20
      /\ (forall r, In r EMH_KEPT -> getr R' r = getr R r).

Definition emh_ret (I : emh_inst) : Prop :=
  forall (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
          x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (ret_pc x1) fc None m (seg_rom asegs)) ->
    evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 (emh_entry I + 500)) fc None m (seg_rom asegs)).

Ltac emh_ret_tac := intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
  x28 x29 x30 x31 F fc m HQ; cbn [emh_entry EMH_EXT EMH_U32]; step; apply evt_done; exact HQ.

Lemma emh_ret_ext : emh_ret EMH_EXT. Proof. emh_ret_tac. Qed.
Lemma emh_ret_u32 : emh_ret EMH_U32. Proof. emh_ret_tac. Qed.

Ltac emh_shu := unfold sh, AIMG_TOP in *; rewrite ?ASHADOW_BASE_val in *.

Lemma emh_A_ext : emh_A EMH_EXT.
Proof.
  intros R F fc m obj spz keyp G2 G10 G11 AC UAR WR SPR SP16. unfold AUAR_CELL in UAR.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmEmhW.xa_E R obj spz keyp) LbB_PmEmhW.xa_sr R) by (unfold LbB_PmEmhW.xa_E, LbB_PmEmhW.xa_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmEmhW.xa_E R obj spz keyp) m LbB_PmEmhW.xa_A_knF) by (unfold LbB_PmEmhW.xa_E; knowB).
  destruct (LbB_PmEmhW.xa_A_run fx R m (seg_rom asegs) obj spz keyp ltac:(lia) ltac:(lia) ltac:(lia) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmEmhW.xa_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmEmhW.xa_E R obj spz keyp) in *. unfold LbB_PmEmhW.xa_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fldw_postB_at 0%nat|]. split; [fldw_postB_at 1%nat|]. split; [fldw_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|]. split; [fldw_postB_at 4%nat|]. split; [fldw_postB_at 5%nat|].
  unfold emh_sq.
  split; [rrwB HR' (1%bv : reg); regB|]. split; [rrwB HR' (2%bv : reg); regB|]. split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|]. split; [rrwB HR' (10%bv : reg); regB|]. split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|]. split; [rrwB HR' (20%bv : reg); regB|].
  keptB HR HR' EMH_KEPT.
Qed.

Lemma emh_A_u32 : emh_A EMH_U32.
Proof.
  intros R F fc m obj spz keyp G2 G10 G11 AC UAR WR SPR SP16. unfold AUAR_CELL in UAR.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmEmhW.ua_E R obj spz keyp) LbB_PmEmhW.ua_sr R) by (unfold LbB_PmEmhW.ua_E, LbB_PmEmhW.ua_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmEmhW.ua_E R obj spz keyp) m LbB_PmEmhW.ua_A_knF) by (unfold LbB_PmEmhW.ua_E; knowB).
  destruct (LbB_PmEmhW.ua_A_run fx R m (seg_rom asegs) obj spz keyp ltac:(lia) ltac:(lia) ltac:(lia) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmEmhW.ua_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmEmhW.ua_E R obj spz keyp) in *. unfold LbB_PmEmhW.ua_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [0; 0; 0; 0; 0; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fldw_postB_at 0%nat|]. split; [fldw_postB_at 1%nat|]. split; [fldw_postB_at 2%nat|].
  split; [fldw_postB_at 3%nat|]. split; [fldw_postB_at 4%nat|]. split; [fldw_postB_at 5%nat|].
  unfold emh_sq.
  split; [rrwB HR' (1%bv : reg); regB|]. split; [rrwB HR' (2%bv : reg); regB|]. split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|]. split; [rrwB HR' (10%bv : reg); regB|]. split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|]. split; [rrwB HR' (20%bv : reg); regB|].
  keptB HR HR' EMH_KEPT.
Qed.

Ltac emh_knB RL := change bsegs with asegs; kn_eval; unfold know_ok;
  repeat (apply Forall_cons; [first [exact (kimg_relro _ _ RL) | kentryB] |]); apply Forall_nil.

Lemma emh_B_ext : emh_B EMH_EXT.
Proof.
  intros R F fc m ff sq keyp obj spz G10 G2 G9 G18 G20 G8 G19 G1 RL W1 W2 W3 B1 B2 B3 B4 B5 B6 B7.
  stash_disjB. emh_shu.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmEmhW.xb_E R ff sq keyp obj spz) LbB_PmEmhW.xb_sr R)
    by (unfold LbB_PmEmhW.xb_E, LbB_PmEmhW.xb_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmEmhW.xb_E R ff sq keyp obj spz) m LbB_PmEmhW.xb_A_knF)
    by (unfold LbB_PmEmhW.xb_E; emh_knB RL).
  destruct (LbB_PmEmhW.xb_A_run fx R m (seg_rom asegs) ff sq keyp obj spz ltac:(assumption) ltac:(assumption)
              ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmEmhW.xb_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmEmhW.xb_E R ff sq keyp obj spz) in *. unfold LbB_PmEmhW.xb_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [2; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 1; 1; 1; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 1%nat|]. split; [fld_postB_at 13%nat|].
  split; [rrwB HR' (1%bv : reg); regB|]. split; [rrwB HR' (2%bv : reg); regB|]. split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|]. split; [rrwB HR' (10%bv : reg); regB|]. split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|]. split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|]. split; [rrwB HR' (20%bv : reg); regB|].
  keptB HR HR' EMH_KEPT.
Qed.

Lemma emh_B_u32 : emh_B EMH_U32.
Proof.
  intros R F fc m ff sq keyp obj spz G10 G2 G9 G18 G20 G8 G19 G1 RL W1 W2 W3 B1 B2 B3 B4 B5 B6 B7.
  stash_disjB. emh_shu.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmEmhW.ub_E R ff sq keyp obj spz) LbB_PmEmhW.ub_sr R)
    by (unfold LbB_PmEmhW.ub_E, LbB_PmEmhW.ub_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmEmhW.ub_E R ff sq keyp obj spz) m LbB_PmEmhW.ub_A_knF)
    by (unfold LbB_PmEmhW.ub_E; emh_knB RL).
  destruct (LbB_PmEmhW.ub_A_run fx R m (seg_rom asegs) ff sq keyp obj spz ltac:(assumption) ltac:(assumption)
              ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmEmhW.ub_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmEmhW.ub_E R ff sq keyp obj spz) in *. unfold LbB_PmEmhW.ub_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [2; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 1; 1; 1; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 1%nat|]. split; [fld_postB_at 13%nat|].
  split; [rrwB HR' (1%bv : reg); regB|]. split; [rrwB HR' (2%bv : reg); regB|]. split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|]. split; [rrwB HR' (10%bv : reg); regB|]. split; [rrwB HR' (11%bv : reg); regB|].
  split; [rrwB HR' (13%bv : reg); regB|]. split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|]. split; [rrwB HR' (20%bv : reg); regB|].
  keptB HR HR' EMH_KEPT.
Qed.

Lemma emh_C_ext : emh_C EMH_EXT.
Proof.
  intros R F fc m p sq spz ff fp ra0 sv8 sv9 sv18 sv19 sv20 G10 G2 G9 G8 G18 G20 G19 G1 W1 W2 K1 W3 S1 S2 S3 S4 S5 S6
         P1 P2 P3 B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12.
  stash_disjB. emh_shu.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmEmhW.xc_E R p sq spz ff fp ra0 sv8 sv9 sv18 sv19 sv20) LbB_PmEmhW.xc_sr R)
    by (unfold LbB_PmEmhW.xc_E, LbB_PmEmhW.xc_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmEmhW.xc_E R p sq spz ff fp ra0 sv8 sv9 sv18 sv19 sv20) m LbB_PmEmhW.xc_A_knF)
    by (unfold LbB_PmEmhW.xc_E; knowB).
  destruct (LbB_PmEmhW.xc_A_run fx R m (seg_rom asegs) p sq spz ff fp ra0 sv8 sv9 sv18 sv19 sv20
              ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
              ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
              ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmEmhW.xc_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmEmhW.xc_E R p sq spz ff fp ra0 sv8 sv9 sv18 sv19 sv20) in *. unfold LbB_PmEmhW.xc_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  cbn [emh_voff EMH_EXT].
  split; [rrwB HR' (1%bv : reg); regB|]. split; [rrwB HR' (2%bv : reg); regB|]. split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|]. split; [rrwB HR' (10%bv : reg); regB|]. split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|]. split; [rrwB HR' (20%bv : reg); regB|].
  keptB HR HR' EMH_KEPT.
Qed.

Lemma emh_C_u32 : emh_C EMH_U32.
Proof.
  intros R F fc m p sq spz ff fp ra0 sv8 sv9 sv18 sv19 sv20 G10 G2 G9 G8 G18 G20 G19 G1 W1 W2 K1 W3 S1 S2 S3 S4 S5 S6
         P1 P2 P3 B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12.
  stash_disjB. emh_shu.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (LbB_PmEmhW.uc_E R p sq spz ff fp ra0 sv8 sv9 sv18 sv19 sv20) LbB_PmEmhW.uc_sr R)
    by (unfold LbB_PmEmhW.uc_E, LbB_PmEmhW.uc_sr; rw_seedB).
  assert (HK : know_ok bsegs (LbB_PmEmhW.uc_E R p sq spz ff fp ra0 sv8 sv9 sv18 sv19 sv20) m LbB_PmEmhW.uc_A_knF)
    by (unfold LbB_PmEmhW.uc_E; knowB).
  destruct (LbB_PmEmhW.uc_A_run fx R m (seg_rom asegs) p sq spz ff fp ra0 sv8 sv9 sv18 sv19 sv20
              ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
              ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
              ltac:(assumption) ltac:(assumption) ltac:(assumption) HR HK) as (R' & HR' & Hlf & Hms).
  change bsegs with asegs in Hms. unfold LbB_PmEmhW.uc_A_ss in HR', Hlf, Hms. cbn [s_regs s_log s_pc] in HR', Hlf, Hms.
  set (Ev := LbB_PmEmhW.uc_E R p sq spz ff fp ra0 sv8 sv9 sv18 sv19 sv20) in *. unfold LbB_PmEmhW.uc_E in Ev.
  rw_exB Hms.
  split; [exact Hms|].
  split; [munchB_at [2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0]%nat|].
  split; [apply rw_wmono|].
  split; [fld_postB_at 0%nat|].
  cbn [emh_voff EMH_U32].
  split; [rrwB HR' (1%bv : reg); regB|]. split; [rrwB HR' (2%bv : reg); regB|]. split; [rrwB HR' (8%bv : reg); regB|].
  split; [rrwB HR' (9%bv : reg); regB|]. split; [rrwB HR' (10%bv : reg); regB|]. split; [rrwB HR' (18%bv : reg); regB|].
  split; [rrwB HR' (19%bv : reg); regB|]. split; [rrwB HR' (20%bv : reg); regB|].
  keptB HR HR' EMH_KEPT.
Qed.

Section EmhStmts.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition emh_post (I : emh_inst) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc key : Z) (ents : list (Z * (Z * Z)))
      (lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' LBm' : list block)
                     (F' : bvmap 5 word) (fc' : bv 32) (p v bl' bc' : Z) (ents' : list (Z * (Z * Z))) (inserted rehashed : bool) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + emh_voff I)) a1 a2 a3 a4 a5 a6 a7
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ frm_zero fc'
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B

      /\ umapx MI_A 24 (nval24 ASEGS) (lbl LB') m' obj bl' bc' ents' /\ umap_sh m' 24 (bl', bc', ents')
      /\ addressable m' obj 40 /\ wr_at asegs m' obj 40
      /\ In (p, (key, v)) ents'
      /\ (inserted = false -> ents' = ents /\ rehashed = false)
      /\ (inserted = true -> v = 0 /\ Permutation ents' ((p, (key, 0)) :: ents))
      /\ (rehashed = false -> bl' = bl /\ bc' = bc)
      /\ (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc)

      /\ as_RHEAP H s' LB' m' /\ Permutation LB' (LB0 ++ LBm') /\ Permutation (lbl LBm') (umap_blocks 24 bl' bc' ents')
      /\ lb_own LBm' m'
      /\ Forall (fs_scratch H LF) XS /\ xpres H LB0 (bv_unsigned sp) ((obj, obj + 40) :: XS) m m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - (if rehashed then ICM (8 * bc') else 0).

  Definition emh_stmt (I : emh_inst) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LB0 LBm : list block) (LF : list fframe)
           (obj bl bc keyp key : Z) (ents : list (Z * (Z * Z))) (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 (emh_entry I)) fc None m (seg_rom asegs) ->
      frm_zero fc ->
      a0 = Z_to_bv 64 obj -> a1 = Z_to_bv 64 keyp ->

      umapx MI_A 24 (nval24 ASEGS) (lbl LB) m obj bl bc ents -> umap_sh m 24 (bl, bc, ents) ->
      Permutation LB (LB0 ++ LBm) -> Permutation (lbl LBm) (umap_blocks 24 bl bc ents) ->
      addressable m obj 40 -> wr_at asegs m obj 40 -> map_live_frame LF obj -> obj + 40 <= aceil ->
      (forall b, In b LB -> obj + 40 <= blk_addr b \/ blk_addr b + blk_size b <= obj) ->

      fldA m keyp 4 key -> accessible m keyp 4 -> emp_src H LB0 (bv_unsigned sp) obj keyp 4 ->
      (exists f, In f LF /\ ff_addr f <= keyp /\ keyp + 4 <= ff_addr f + fsz (ff_class f)) ->
      keyp mod 4 = 0 -> 0 <= key < 2 ^ 32 ->

      Zlength ents + 1 < 2 ^ 24 -> bc <> BSEQ_LAST ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
      lb_small LB + 24 + nsmall (8 * bseq_next bc) <= RT_SMALL_MAX -> Z.of_nat (length LB) + 2 <= RT_CNT_MAX ->
      nlarge LB + nlg (8 * bseq_next bc) <= RT_LARGE_MAX ->
      ((bc = 0 \/ Zlength ents = bc) -> ICM (8 * bseq_next bc) <= as_AL H s) ->
      trace_ok (as_TR H) APC0_FREE [emp_del_ra (emh_emp I)] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->

      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AEMH_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE_BP)%nat -> relro0 m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
      lb_own LBm m ->
      as_SR H (emh_post I ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB0 LF obj bl bc key ents lo B shi m mo) (mkCfg msF mo).
End EmhStmts.
