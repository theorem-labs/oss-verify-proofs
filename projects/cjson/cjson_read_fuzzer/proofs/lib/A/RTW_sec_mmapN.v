(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_sec_mmap.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_MMAP_ONFATAL : Z := 0x678fc.

(* [comment removed for export] *)
Lemma getnamedfd_any_ok :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (nm lo : Z),
  mem_inv asegs m -> 0 <= nm < 2^64 ->
  ro_cells asegs m 0xa1f70 [C8 (Z_to_bv 64 0x13bda8)] -> ro_cells asegs m 0x13beac [C1 (Z_to_bv 8 0)] ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 272 <= bv_unsigned sp ->
  evt asegs (fun ms' => exists (a2' : word) (m' : word -> option byte),
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom asegs)
               /\ munch [(bv_unsigned sp - 272, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
               /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 nm) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x683dc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI NM GOTC CF260 ST CEIL SPB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 56%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 10 lstep. (* [comment removed for export] *)
  lstep. if_cases KN; zify_cond KN.
  2: lstep; lstep; lstep; fl; lstep; fl; lstep; fl; lstep; try if_lia. (* [comment removed for export] *)
  all: do 10 lstep.
  all: release_frame FR ST (bv_unsigned sp).
  all: finish.
Qed.

Section MMAPONFATAL.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (sz nm lo : Z).
  Hypothesis HC : mmap_consts mv.
  Hypothesis MI0 : mem_inv asegs mv.
  Hypothesis ST0 : stk asegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 320 <= bv_unsigned sp.
  Hypothesis SZ : 0x10000 <= sz /\ sz mod 4096 = 0 /\ sz + 4096 <= 2^63.
  Hypothesis NM : 0 <= nm < 2^64.

  (* [comment removed for export] *)
  Lemma mmap_onfatal_spec : forall (P : machine_state -> Model -> lghost -> Prop),
    sz <= R ->
    (forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte),
       mem_inv asegs m' -> munch [(lo, bv_unsigned sp)] mv m' -> wmono asegs mv m' ->
       stk asegs m' lo (bv_unsigned sp) ->
       LSCPS asegs P (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (ret_pc ra) fc None m' (seg_rom asegs)) mo (mkG G R)) ->
    (forall (a : word) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte),
       mmap_grant mo a sz ->
       mem_inv asegs m' -> munch [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + sz)] mv m' -> wmono asegs mv m' ->
       stk asegs m' lo (bv_unsigned sp) ->
       rw_cells asegs m' (bv_unsigned a) [CB (Z.to_nat sz) (repeat (Z_to_bv 8 0) (Z.to_nat sz))] ->
       LSCPS asegs P (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (ret_pc ra) fc None m' (seg_rom asegs)) (mm_add_map a (Z_to_bv 64 sz) mo) (mkG G (R - sz))) ->
    LSCPS asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sz) (Z_to_bv 64 nm) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 A_MMAP_ONFATAL) fc None mv (seg_rom asegs)) mo (mkG G R).
  Proof.
    intros P HRsz K0 K.
    destruct HC as (GOTP & PSC & GOTC & CF260 & CF144 & GOTS & DY). hide GOTC. hide GOTS. hide CF260. hide CF144. hide DY.
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0.
    pose proof (munch_refl [(lo, bv_unsigned sp)] mv) as MU. pose proof (wmono_refl asegs mv) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    unfold A_MMAP_ONFATAL.
    apply lscps_assume. intros NWX HOK HBINV.
    apply lscps_step_evt.
    carve_frame 48%nat ST.
    do 5 lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. fl. clear GOTP. (* [comment removed for export] *)
    lstep. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. fl. lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    setreg 9 (Z_to_bv 64 sz) ltac:(f_equal; symmetry; apply roundup_aligned; lia).
    lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    pose proof GOTC as GOTC1. recell GOTC1 MU. pose proof CF260 as CF1. recell CF1 MU.
    call_sp getnamedfd_any_ok; [exact MI| exact NM| exact GOTC1| exact CF1| exact ST| idtac; lia| lia|].
    clear GOTC1 CF1. restk. fixMI.
    lstep. fl. lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    step_ecall. cbv beta.
    eapply lscps_mmap_rw2.
    { at_node_red. split_spine; reflexivity. }
    { lia. } { lia. } { rewrite pru_id by lia. lia. }
    { (* [comment removed for export] *)
      intros e He. cbn in He. destruct He as [<-|[]].
      unfold efferr, eff0. apply lscps_step_evt. sys_nret. unfold errno_ret, ENOMEM.
      lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. if_lia. lstep. fl. lstep. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      lstep. fl. lstep. lstep. if_lia. (* [comment removed for export] *)
      lstep. lstep. (* [comment removed for export] *)
      lstep. do 4 lstep. lstep. lstep. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. eapply K0; [exact MI| exact MU| exact WM| exact ST]. }
    { intros a GR. rewrite pru_id in GR |- * by lia.
      pose proof GR as (GA & GP & GC & GF). idtac.
      pose proof (grant_above_image mo a sz HOK GR ltac:(lia)) as GI. unfold AIMG_HI in GI.
      pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. cbn in RA.
      apply (munch_weaken _ [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + sz)]) in MU. 2:{ unfold sub_fp; cbn; intros; lia. }
      apply lscps_step_evt. rewrite <- (Z_to_bv_bv_unsigned a). sys_nret. fixMI.
      Unshelve.
      2:{ apply ro_addr_noseg. eapply (region_free_reserved_noseg asegs (Z_to_bv 64 (bv_unsigned a)) (Z_to_bv 64 sz) _ mo NWX HOK).
          - rewrite region_free_app in GF. apply andb_true_iff in GF as [GF _]. rewrite Z_to_bv_bv_unsigned. exact GF.
          - rewrite !unsigned_lit by lia. lia. }
      lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      lstep. lstep. (* [comment removed for export] *)
      pose proof GOTC as GOTC1. recell GOTC1 MU. lstep. lstep. fl. clear GOTC1. (* [comment removed for export] *)
      pose proof CF144 as CF1. recell CF1 MU. lstep. fl. clear CF1. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep. do 4 lstep. lstep. lstep. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. eapply K; [exact GR| exact MI| exact MU| exact WM| exact ST| exact ZNEW]. }
  Qed.
End MMAPONFATAL.


End CeilWrap.
End RTW_sec_mmap.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap.
Import RTW_sec_mmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section MMAPONFATALN.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (sz nm lo : Z).
  Hypothesis HC : mmap_consts mv.
  Hypothesis MI0 : mem_inv asegs mv.
  Hypothesis ST0 : stk asegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 320 <= bv_unsigned sp.
  Hypothesis SZ : 0x10000 <= sz /\ sz mod 4096 = 0 /\ sz + 4096 <= 2^63.
  Hypothesis NM : 0 <= nm < 2^64.

  (* [comment removed for export] *)
  Lemma mmap_onfatal_nn_spec : forall (P : machine_state -> Model -> lghost -> Prop),
    sz <= R -> mmap_placeable mo sz ->
    (forall (a : word) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte),
       mmap_grant mo a sz ->
       mem_inv asegs m' -> munch [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + sz)] mv m' -> wmono asegs mv m' ->
       stk asegs m' lo (bv_unsigned sp) ->
       rw_cells asegs m' (bv_unsigned a) [CB (Z.to_nat sz) (repeat (Z_to_bv 8 0) (Z.to_nat sz))] ->
       LSCPS asegs P (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (ret_pc ra) fc None m' (seg_rom asegs)) (mm_add_map a (Z_to_bv 64 sz) mo) (mkG G (R - sz))) ->
    LSCPS asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sz) (Z_to_bv 64 nm) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 A_MMAP_ONFATAL) fc None mv (seg_rom asegs)) mo (mkG G R).
  Proof.
    intros P HRsz HPL K.
    destruct HC as (GOTP & PSC & GOTC & CF260 & CF144 & GOTS & DY). hide GOTC. hide GOTS. hide CF260. hide CF144. hide DY.
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0.
    pose proof (munch_refl [(lo, bv_unsigned sp)] mv) as MU. pose proof (wmono_refl asegs mv) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    unfold A_MMAP_ONFATAL.
    apply lscps_assume. intros NWX HOK HBINV.
    apply lscps_step_evt.
    carve_frame 48%nat ST.
    do 5 lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. fl. clear GOTP. (* [comment removed for export] *)
    lstep. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. fl. lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    setreg 9 (Z_to_bv 64 sz) ltac:(f_equal; symmetry; apply roundup_aligned; lia).
    lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    pose proof GOTC as GOTC1. recell GOTC1 MU. pose proof CF260 as CF1. recell CF1 MU.
    call_sp getnamedfd_any_ok; [exact MI| exact NM| exact GOTC1| exact CF1| exact ST| idtac; lia| lia|].
    clear GOTC1 CF1. restk. fixMI.
    lstep. fl. lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    step_ecall. cbv beta.
    eapply lscps_mmap_rw_grant.
    { at_node_red. split_spine; reflexivity. }
    { lia. } { lia. } { rewrite pru_id by lia. lia. }
    { rewrite pru_id by lia. exact HPL. }
    { intros a GR. rewrite pru_id in GR |- * by lia.
      pose proof GR as (GA & GP & GC & GF). idtac.
      pose proof (grant_above_image mo a sz HOK GR ltac:(lia)) as GI. unfold AIMG_HI in GI.
      pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. cbn in RA.
      apply (munch_weaken _ [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + sz)]) in MU. 2:{ unfold sub_fp; cbn; intros; lia. }
      apply lscps_step_evt. rewrite <- (Z_to_bv_bv_unsigned a). sys_nret. fixMI.
      Unshelve.
      2:{ apply ro_addr_noseg. eapply (region_free_reserved_noseg asegs (Z_to_bv 64 (bv_unsigned a)) (Z_to_bv 64 sz) _ mo NWX HOK).
          - rewrite region_free_app in GF. apply andb_true_iff in GF as [GF _]. rewrite Z_to_bv_bv_unsigned. exact GF.
          - rewrite !unsigned_lit by lia. lia. }
      lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      lstep. lstep. (* [comment removed for export] *)
      pose proof GOTC as GOTC1. recell GOTC1 MU. lstep. lstep. fl. clear GOTC1. (* [comment removed for export] *)
      pose proof CF144 as CF1. recell CF1 MU. lstep. fl. clear CF1. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep. do 4 lstep. lstep. lstep. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. eapply K; [exact GR| exact MI| exact MU| exact WM| exact ST| exact ZNEW]. }
  Qed.
End MMAPONFATALN.

End CeilWrap.
