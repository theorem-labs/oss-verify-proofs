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
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_heap_inst0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_heap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_hdr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_usage.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
Module Drv_open_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_syscalls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_heap_inst0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_heap.KB_drv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_heap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_hdr.Drv_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_usage.Drv_exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_usage.Drv_die.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
  Hypothesis SO_EXIT : so_exit_stmt.
  Hypothesis SO_OOM : so_diag_oom_stmt.
  Hypothesis SO_READERR : so_diag_read_error_stmt.
  Hypothesis SO_CANTOPEN : so_diag_cannot_open_stmt.

  (* [comment removed for export] *)
  Lemma after_open_ok :
    forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (fs : Fs) (e3 : FdEntry) (lo P1 : Z) (tid : word) (path slack : list byte) (errv : word) (fj : list byte)
           (v0 v1 v2 v3 v4 v5 v6 v7 ra0 : word) (KH : TSet),
      DMOD fs (FDS3 e3) mo -> DHEAP0 (bv_unsigned sp + 128) m mo -> tp = wz PTP ->
      stk psegs m lo (bv_unsigned sp) -> lo + 2^22 <= bv_unsigned sp + 80 -> alloc_ceiling <= lo -> bv_unsigned sp + 128 <= 0x800000000000 ->
      mem_inv psegs m -> frm0 fc -> DSTAT false tid m -> 0 < bv_unsigned tid < 2^22 ->
      rw_cells psegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0) ->
      CJST m -> rw_cells psegs m PERRNO [C4 errv] -> rw_cells psegs m PINITFLAG [C1 (Z_to_bv 8 0)] ->
      stdout_file m stdout_init -> stderr_wfile0 m -> (exists stj, rw_cells psegs m PRS [CB RSN stj]) ->
      bytes_at psegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
      (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 131071 -> bv_unsigned sp + 128 <= P1 ->
      KH [] ->
      (forall (m' : word -> option byte) (mo' : Model) (cs : mstate) (c : cptr) (off A : Z) (junk stj : list byte) (e' : word) ms',
          stk psegs m' lo (bv_unsigned sp) -> mem_inv psegs m' -> DSTAT false tid m' ->
          rw_cells psegs m' (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0) ->
          CJST m' -> rw_cells psegs m' PERRNO [C4 e'] -> rw_cells psegs m' PINITFLAG [C1 (Z_to_bv 8 0)] ->
          stdout_file m' stdout_init -> stderr_wfile0 m' -> bytes_at psegs m' P1 (path ++ Z_to_bv 8 0 :: slack) ->
          rw_cells psegs m' PRS [CB RSN stj] ->
          DHEAP cs [((c, off), A, 65536)] (bv_unsigned sp + 128) m' mo' -> MLEAF (cs0 (reservedZ psegs)) 65536 cs (Some c) ->
          DMOD fs (FDS3 e3) mo' -> rblock_range A 65536 -> rw_cells psegs m' A [CB (Z.to_nat 65536) junk] ->
          loop_regs sp gp tp F fc P1 s8 s9 s10 s11 0 65536 A m' 0x12218 ms' ->
          realizes psegs (mkCfg ms' mo') KH) ->
      realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) s1 (wz 3) a1 a2 a3 a4 a5 a6 a7 (wz P1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x1218c) fc None m (seg_rom psegs)) mo)
               KH.
  Proof using SO_EXIT SO_OOM.   (* [comment removed for export] *)
    intros until KH. intros DM DH TP ST LO GT SPH MI FRM DS TID FR CJ ER IFL SOF SEF [stj RSC] BY NONUL SLK LEN PUS KH0 HK.
    pose proof RSN_Z as HRSN. pose proof PRS_eq as HPRS.
    pose proof DM as [MOK' MFDS HFS].
    unfold wz in *. unfold PERRNO in ER. unfold PINITFLAG in IFL.
    eapply rz_step_evt; [exact MOK'|].
    step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    do 4 step. apply evt_done.
    eapply drv_malloc_first with (lo := lo);
      first [exact DH| exact ST| exact ER| exact MI| exact TP| reflexivity| unfold CJ_iface.RMALLOC_STACK; lia| idtac].
    - (* [comment removed for export] *)
      intros ms2 mo2 m2 errv2 cs' c off A junk RP VO MI2 ST2 ER2 PR BR BLK DH2 LEAF.
      destruct RP as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & ->).
      replace (ret_pc (Z_to_bv 64 0x121a0)) with (Z_to_bv 64 0x121a0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (dheap_mok _ _ _ _ _ DH2) as MOK2. pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4.
      eapply rz_step_evt; [exact MOK2|]. unfold wz. step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
      do 4 step. step. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia]. clear K.
      do 2 step. apply evt_done.
      (* [comment removed for export] *)
      eapply (HK m2 mo2 cs' c off A junk stj errv2).
      + exact ST2.
      + exact MI2.
      + eapply DSTAT_cj_pres; [exact DS| exact PR].
      + eapply cj_pres_rw_cells; [exact PR| exact FR| left; unfold mframe; cbn; lia].
      + eapply CJST_pres; [exact PR| exact CJ].
      + exact ER2.
      + unfold PINITFLAG; eapply cj_pres_rw_cells; [exact PR| exact IFL| right; left; unfold PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; cbn; lia].
      + eapply stdout_file_cj_pres; [exact SOF| exact PR].
      + eapply stderr_wfile0_cj_pres; [exact SEF| exact PR].
      + eapply cj_pres_bytes_at; [exact PR| exact BY| left; lia].
      + eapply cj_pres_rw_cells; [exact PR| exact RSC| right; left; unfold PRS, PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; pose proof RSN_Z; cbn; lia].
      + exact DH2.
      + exact LEAF.
      + eapply DMOD_vm_only; [exact DM| exact VO| exact MOK2].
      + exact BR.
      + exact BLK.
      + unfold loop_regs, PRS. repeat eexists.
  Qed.

  (* [comment removed for export] *)
  Lemma dir_read :
    forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (fs : Fs) (lo P1 A : Z) (tid : word) (path slack : list byte) (errv q8 q9 q10 q11 : word)
           (cs : mstate) (p : bptr) (junk stj : list byte) ms,
      DMOD fs (FDS3 FdDir) mo -> DHEAP cs [(p, A, 65536)] (bv_unsigned sp + 128) m mo -> tp = wz PTP ->
      stk psegs m lo (bv_unsigned sp) -> lo + 2^22 <= bv_unsigned sp + 80 -> alloc_ceiling <= lo -> bv_unsigned sp + 128 <= 0x800000000000 ->
      mem_inv psegs m -> frm0 fc -> DSTAT false tid m -> 0 < bv_unsigned tid < 2^22 ->
      rw_cells psegs m PERRNO [C4 errv] ->
      stdout_file m stdout_init -> stderr_wfile0 m ->
      bytes_at psegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
      (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 131071 -> bv_unsigned sp + 128 <= P1 ->
      rw_cells psegs m PRS [CB RSN stj] -> rblock_range A 65536 ->
      loop_regs sp gp tp F fc P1 q8 q9 q10 q11 0 65536 A m 0x12218 ms ->
      realizes psegs (mkCfg ms mo) (t_die (msg_read_error path) fs).
  Proof.
    intros until ms. intros DM DH TP ST LO GT SPH MI FRM DS TID ER SOF SEF BY NONUL SLK LEN PUS RSC BR (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s7 & t3 & t4 & t5 & t6 & ->).
    pose proof RSN_Z as HRSN. pose proof PRS_eq as HPRS.
    pose proof DM as [MOK' MFDS HFS]. pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4.
    unfold wz in *. unfold PERRNO in ER.
    eapply rz_step_evt; [exact MOK'|].
    do 3 step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
    do 4 step. apply evt_done.
    eapply (rz_impl_read_dir psegs _ _ mo 3 (bv_unsigned (Z_to_bv 64 PRS)) 65536);
      [exact MOK'| | rewrite MFDS; reflexivity| rewrite rw_bytes_max_val; lia| rewrite unsigned_lit by lia; rewrite TASK_SIZE_val; unfold PRS; lia|].
    { eapply read_spec with (lo := lo) (junk := stj) (errv := errv);
      first [ exact ST | exact MI
            | lazymatch goal with |- _ = _ => reflexivity end
            | rewrite ?(errno_addr_tp tp TP); rewrite ?TP; unfold PERRNO, PTP, PRS; rewrite ?unsigned_lit by lia; first [exact RSC| exact ER| lia] ]. }
    intros ms2 PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & RSC2 & ER2 & He).
    cbn [read_ret] in *. rewrite (errno_addr_tp tp TP) in MU2, ER2. rewrite ?unsigned_lit in MU2 by lia.
    replace (ret_pc (Z_to_bv 64 0x12234)) with (Z_to_bv 64 0x12234) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply rz_step_evt; [exact MOK'|]. step. if_cases K; zify_cond K; [| exfalso; lia]. clear K. apply evt_done.
    destruct (dheap_libc_cells _ _ _ _ _ DH) as (cdt & thr & sec & tm1 & LC).
    xport DS MU2 WM2 DS2. xport LC MU2 WM2 LC2. xport SOF MU2 WM2 SOF2. xport SEF MU2 WM2 SEF2. xport BY MU2 WM2 BY2.
    pose proof (dheap_ssp0 _ _ _ _ _ DH) as SSP. xport SSP MU2 WM2 SSP2.
    eapply die_readerr with (lo := lo) (cdt := cdt) (thr := thr) (sec := sec) (tm1 := tm1) (guard := ssp_guard_val) (P1 := P1) (slack := slack);
      first [exact SO_EXIT| exact SO_READERR| exact DM| right; eexists; reflexivity| exact TP| exact TID| exact FRM| exact BY2| exact NONUL| exact SLK| reflexivity
            | split; [exact ST2| split; [exact MI2| split; [exact DS2| split; [exact LC2| split; [exact SSP2| split; [exact SOF2| exact SEF2]]]]]]
            | unfold GLOBALS_TOP, zlength in *; lia ].
  Qed.

End S.


End CeilWrap.
End Drv_open_A.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS ITree Nodes Decode SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio Malloc Prog MEX_defs MEX_iface MEX_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree F_pad Exit Printf_model F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_heap_inst0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_heap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_heap.KB_drv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Drv_base Drv_heap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_hdr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_hdr.Drv_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_usage.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_usage.Drv_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_usage.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_usage.Drv_die.
Import Drv_open_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
  Hypothesis SO_EXIT : so_exit_stmt.
  Hypothesis SO_OOM : so_diag_oom_stmt.
  Hypothesis SO_READERR : so_diag_read_error_stmt.
  Hypothesis SO_CANTOPEN : so_diag_cannot_open_stmt.

  Hypothesis LOOP : forall sp gp tp F fc fs lo SPB P1 tid path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11,
    loop_side sp tp fc lo SPB P1 tid path slack ->
    loop_stmt sp gp tp F fc fs lo SPB P1 tid (wz PSTAGE2_RET) path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.

  Theorem main_two_proof : main_two_stmt.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo fs lo P1 tid path slack errv.
    intros DM DH RA TP -> -> ST LO CEIL SPH SPAL MI FRM DS TID CJ ER IFL SOF SEF [stj RSC] AV BY NONUL HSL HDD SLK LEN PUS.
    pose proof RSN_Z as HRSN. pose proof PRS_eq as HPRS.   (* [comment removed for export] *)
    pose proof DM as [MOK' MFDS HFS].
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof CEIL as GT.
    unfold wz, PMAIN in *. unfold PERRNO in ER. unfold PINITFLAG in IFL.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    eapply rz_step_evt; [exact MOK'|].
    carve_frame 80%nat ST.
    do 12 step.
    if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    do 4 step.
    apply evt_done.
    name_sp sp (-80).
    rewrite <- Hsp in FR, ST. replace (bv_unsigned sp + 64) with (bv_unsigned sp0 + 144) in AV by lia.
    assert (LO' : lo + 2^22 <= bv_unsigned sp0 + 80) by lia. assert (PUS' : bv_unsigned sp0 + 128 <= P1) by lia.
    assert (SPH' : bv_unsigned sp0 + 128 <= 0x800000000000) by lia.
    assert (SPAL' : bv_unsigned sp0 mod 16 = 0) by (rewrite Hsp, Z.add_mod, SPAL by lia; reflexivity).
    rewrite <- Hsp in MU. replace (bv_unsigned sp) with (bv_unsigned sp0 + 80) in MU by lia.
    replace (bv_unsigned sp + 48) with (bv_unsigned sp0 + 128) in DH by lia.
    clear Hsp Esp LO PUS SPH SPAL. clear sp. rename sp0 into sp.
    lazymatch type of MU with munch _ _ ?mm => rename mm into m1 end.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (DS1 : DSTAT false tid m1).
    { eapply DSTAT_munch; [exact DS| exact MU| exact WM| constructor; [unfold dstat_safe; cbn [fst snd]; lia| constructor]]. }
    assert (DH1 : DHEAP0 (bv_unsigned sp + 128) m1 mo).
    { eapply dheap0_frame_ext; [exact DH| exact MU| exact WM| solve_Forall ltac:(drv_write_ok_tac)]. }
    assert (SOF1 : stdout_file m1 stdout_init).
    { eapply stdout_file_munch; [exact SOF| exact MU| exact WM| constructor; [cbn [fst snd]; lia| constructor]]. }
    assert (SEF1 : stderr_wfile0 m1).
    { eapply stderr_wfile0_munch; [exact SEF| exact MU| exact WM| constructor; [cbn [fst snd]; lia| constructor]]. }
    assert (CJ1 : CJST m1).
    { destruct CJ as (C1 & (e1 & e2 & C2) & C3). split; [| split; [exists e1, e2|]];
      [ (eapply rw_cells_transport; [exact C1| exact MU| exact WM| cbn; unfold PHOOKS, PGERROR, PLCONV; lia])
      | (eapply rw_cells_transport; [exact C2| exact MU| exact WM| cbn; unfold PHOOKS, PGERROR, PLCONV; lia])
      | (eapply rw_cells_transport; [exact C3| exact MU| exact WM| cbn; unfold PHOOKS, PGERROR, PLCONV; lia]) ]. }   (* [comment removed for export] *)
    assert (RSC1 : rw_cells psegs m1 PRS [CB RSN stj]).
    { first [ exact RSC   (* [comment removed for export] *)
            | eapply rw_cells_transport; [exact RSC| exact MU| exact WM| pose proof RSN_Z; cbn; unfold PRS; lia] ]. }
    clear DS SOF SEF CJ DH RSC MU WM.
    pose proof (dheap0_ssp0 _ _ _ DH1) as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (BYP : bytes_at psegs m1 P1 (path ++ [Z_to_bv 8 0])).
    { rewrite (app_assoc_cons path) in BY || idtac.
      replace (path ++ Z_to_bv 8 0 :: slack) with ((path ++ [Z_to_bv 8 0]) ++ slack) in BY by (rewrite <- app_assoc; reflexivity).
      exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) BY)). }
    (* [comment removed for export] *)
    assert (KERR : forall (e : Z) ms2,
      open_post (Z_to_bv 64 0x1218c) sp gp tp (Z_to_bv 64 2) s1 (Z_to_bv 64 P1) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned (Z_to_bv 64 P1)) path errv ssp_guard_val lo m1 (SErr e) ms2 ->
      realizes psegs (mkCfg ms2 mo) (t_die (msg_cannot_open path) fs)).
    { intros e ms2 PO. rewrite (unsigned_lit P1) in PO by lia. (nelim PO 25%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 ST2 ER2 BY2 G1 G2 He).
      cbn [open_ret open_errno] in *. rewrite (errno_addr_tp tp TP) in MU2, ER2.
      replace (ret_pc (Z_to_bv 64 0x1218c)) with (Z_to_bv 64 0x1218c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply rz_step_evt; [exact MOK'|]. step. if_cases K; zify_cond K; [| exfalso; lia]. clear K. apply evt_done.
      (nelim (dheap0_libc_cells _ _ _ DH1) 5%nat; intros cdt thr sec tm1 LC1).
      xport DS1 MU2 WM2 DS2. xport LC1 MU2 WM2 LC2. xport SOF1 MU2 WM2 SOF2. xport SEF1 MU2 WM2 SEF2. xport BY MU2 WM2 BY2'.
      eapply die_cantopen with (lo := lo) (cdt := cdt) (thr := thr) (sec := sec) (tm1 := tm1) (guard := ssp_guard_val) (P1 := P1) (slack := slack);
        first [exact SO_EXIT| exact SO_CANTOPEN| exact DM| left; reflexivity| exact TP| exact TID| exact FRM| exact BY2'| exact NONUL| exact SLK| reflexivity
              | split; [exact ST2| split; [exact MI2| split; [exact DS2| split; [exact LC2| split; [split; [exact G1| exact G2]| split; [exact SOF2| exact SEF2]]]]]]
              | unfold GLOBALS_TOP, zlength in *; lia ]. }
    (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (mkCfg ?ms _) _ =>
      eassert (OPEN : impl psegs (at_node psegs) (enode (NOpen path) dec_open) _ ms) end.
    { eapply open_spec with (lo := lo) (errv := errv) (canary := ssp_guard_val);
      first [ exact ST | exact MI | exact NONUL | exact SSP1 | exact SSP2
            | lazymatch goal with |- _ = _ => reflexivity end
            | rewrite ?(errno_addr_tp tp TP); rewrite ?TP; unfold PERRNO, PTP, F_syscalls.got_ssp, F_syscalls.ssp_guard;
              rewrite ?unsigned_lit by lia; first [exact BYP| exact ER| lia] ]. }
    (* [comment removed for export] *)
    unfold spec_path.
    destruct (Nat.leb_spec0 4096 (length path)) as [TL|NTL].
    { eapply (rz_impl_openat_toolong psegs); [exact MOK'| exact OPEN| exact TL| intros ms2 PO; exact (KERR _ _ PO)]. }
    destruct (list_byte_eqb path []) eqn:E0.
    { apply list_byte_eqb_eq in E0. subst path. eapply (rz_impl_openat_empty psegs); [exact MOK'| exact OPEN| intros ms2 PO; exact (KERR _ _ PO)]. }
    apply list_byte_eqb_neq in E0.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?fj :: _) => set (fj0 := fj) in FR end.
    (* [comment removed for export] *)
    assert (KOK : forall (e3 : FdEntry) (KH : TSet) ms2,
      open_post (Z_to_bv 64 0x1218c) sp gp tp (Z_to_bv 64 2) s1 (Z_to_bv 64 P1) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned (Z_to_bv 64 P1)) path errv ssp_guard_val lo m1
                (SVal (bv_unsigned (alloc_fd (m_fds mo)))) ms2 ->
      KH [] ->
      (forall (m' : word -> option byte) (mo' : Model) (cs : mstate) (c : cptr) (off A : Z) (junk stj' : list byte) (e' : word) ms',
          stk psegs m' lo (bv_unsigned sp) -> mem_inv psegs m' -> DSTAT false tid m' ->
          rw_cells psegs m' (bv_unsigned sp) (mframe fj0 s0 s1 s2 s3 s4 s5 s6 s7 (wz PSTAGE2_RET)) ->
          CJST m' -> rw_cells psegs m' PERRNO [C4 e'] -> rw_cells psegs m' PINITFLAG [C1 (Z_to_bv 8 0)] ->
          stdout_file m' stdout_init -> stderr_wfile0 m' -> bytes_at psegs m' P1 (path ++ Z_to_bv 8 0 :: slack) ->
          rw_cells psegs m' PRS [CB RSN stj'] ->
          DHEAP cs [((c, off), A, 65536)] (bv_unsigned sp + 128) m' mo' -> MLEAF (cs0 (reservedZ psegs)) 65536 cs (Some c) ->
          DMOD fs (FDS3 e3) mo' -> rblock_range A 65536 -> rw_cells psegs m' A [CB (Z.to_nat 65536) junk] ->
          loop_regs sp gp tp F fc P1 s8 s9 s10 s11 0 65536 A m' 0x12218 ms' ->
          realizes psegs (mkCfg ms' mo') KH) ->
      realizes psegs (mkCfg ms2 (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) e3) mo)) KH).
    { intros e3 KH ms2 PO KH0 HK. rewrite MFDS, FDS0_insert. rewrite MFDS, FDS0_alloc in PO. unfold wz in PO. rewrite (unsigned_lit 3) in PO by lia. rewrite (unsigned_lit P1) in PO by lia.
      (nelim PO 25%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 ST2 ER2 BY2 G1 G2 Hfd).
      cbn [open_ret open_errno] in *. rewrite (errno_addr_tp tp TP) in MU2, ER2.
      replace (ret_pc (Z_to_bv 64 0x1218c)) with (Z_to_bv 64 0x1218c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      xport DS1 MU2 WM2 DS2. xport FR MU2 WM2 FR2. xport CJ1 MU2 WM2 CJ2. xport IFL MU2 WM2 IFL2. xport SOF1 MU2 WM2 SOF2. xport SEF1 MU2 WM2 SEF2. xport BY MU2 WM2 BY3.
      xport RSC1 MU2 WM2 RSC2.
      rewrite RA in FR2.
      eapply (after_open_ok SO_EXIT SO_OOM _ sp gp tp _ _ _ s1 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 _ fs e3 lo P1 tid path slack _ fj0 s0 s1 s2 s3 s4 s5 s6 s7 _ KH);
        first [ eapply DMOD_with_fds; exact DM
              | eapply dheap0_model; [eapply dheap0_frame_ext; [exact DH1| exact MU2| exact WM2| solve_Forall ltac:(drv_write_ok_tac)]| reflexivity| destruct MOK' as [Hh _]; exact Hh]
              | exact TP| exact ST2| exact MI2| exact FRM| exact DS2| exact TID| unfold mframe; exact FR2| exact CJ2| exact ER2| exact IFL2| exact SOF2| exact SEF2| exists stj; exact RSC2| exact BY3| exact NONUL| exact SLK| exact LEN| exact KH0| exact HK
              | unfold zlength in *; lia ]. }
    destruct (list_byte_eqb path dot_path) eqn:E1.
    { (* [comment removed for export] *)
      apply list_byte_eqb_eq in E1. subst path. unfold t_opened_dir.
      eapply (rz_impl_openat_dot psegs); [exact MOK'| exact OPEN| rewrite MFDS; reflexivity| rewrite MFDS, FDS0_alloc; unfold wz; rewrite unsigned_lit by lia; lia
        | intros e ms2 He PO; exact (KERR _ _ PO) |].
      intros ms2 PO. apply (KOK FdDir _ ms2 PO); [apply t_emit_has_nil'|].
      intros m' mo' cs c off A junk' stj' e' ms' ST' MI' DS' FR' CJ' ER' IFL' SOF' SEF' BY' RSC' DH' LEAF DM' BR BLK LR.
      eapply (dir_read SO_EXIT SO_READERR) with (junk := junk'); first [exact DM'| exact DH'| exact TP| exact ST'| exact MI'| exact FRM| exact DS'| exact TID| exact ER'| exact SOF'| exact SEF'| exact BY'| exact NONUL| exact SLK| exact LEN| exact RSC'| exact BR| exact LR| lia]. }
    apply list_byte_eqb_neq in E1.
    rewrite <- HFS in KERR, KOK |- *. destruct (fs_lookup (m_fs mo) path) as [data|] eqn:FL.
    - (* [comment removed for export] *)
      unfold t_opened.
      eapply (rz_impl_openat_file psegs); [exact MOK'| exact OPEN| lia| exact E0| exact E1| exact HDD| exact HSL| exact FL| rewrite MFDS; reflexivity| rewrite MFDS, FDS0_alloc; unfold wz; rewrite unsigned_lit by lia; lia
        | intros e ms2 He PO; exact (KERR _ _ PO) |].
      intros ms2 PO. eapply rz_conseq; [apply (KOK (FdFile path (Z_to_bv 64 0)) (Kloop data (m_fs mo) 65536) ms2 PO)|].
      + apply Kloop_nil.
      + intros m' mo' cs c off A junk' stj' e' ms' ST' MI' DS' FR' CJ' ER' IFL' SOF' SEF' BY' RSC' DH' LEAF DM' BR BLK LR.
        destruct LEAF as [ans LEAF]. (nelim (MEX_main.m0_intro _ _ _ _ LEAF) 6%nat; intros v r Ecs Ec Hr RP).
        assert (SIDE : loop_side sp tp fc lo (bv_unsigned sp + 128) P1 tid path slack).
        { split; [exact TP|]. split; [exact LO'|]. split; [exact GT|]. split; [exact SPH'|]. split; [reflexivity|]. split; [exact TID|].
          split; [exact FRM|]. split; [exact NONUL|]. split; [exact SLK|]. split; [exact LEN|]. split; [exact PUS'| exact SPAL']. }
        eapply (LOOP sp gp tp F fc (m_fs mo) lo (bv_unsigned sp + 128) P1 tid path slack data fj0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SIDE 0 65536 A cs (c, off) (d0 r) (firstn (Z.to_nat 65536) (skipn 0 junk')) m' mo' ms'); [| lia| exact LR].
        split; [exact ST'|]. split; [exact MI'|]. split; [exact FR'|]. split; [exact DS'|]. split; [exact CJ'|]. split; [exists e'; exact ER'|]. split; [exact IFL'|].
        split; [exact SOF'|]. split; [exact SEF'|]. split; [exact BY'|]. split; [exact DH'|]. split; [exact RP|]. split; [cbn [fst]; rewrite Ec; reflexivity|].
        split; [exact DM'|]. split; [exact FL|]. split.
        { cbn [Z.to_nat firstn Z.sub]. replace (Z.to_nat (65536 - 0)) with (Z.to_nat 65536) by reflexivity.
          eapply (rw_cells_split_CB psegs m' A [] (Z.to_nat 65536) junk' [] [0%nat; Z.to_nat 65536]) in BLK; [| reflexivity].
          cbn [mk_CB_cells firstn skipn app] in BLK. exact BLK. }
        split; [exists stj'; exact RSC'|].
        pose proof (bytes_at_bound _ _ _ _ BY) as BBd.
        split; [exists 0%nat; reflexivity|]. unfold zlength. lia.
      + apply Kloop_top.
    - (* [comment removed for export] *)
      eapply (rz_impl_openat_absent psegs); [exact MOK'| exact OPEN| lia| exact E0| exact E1| exact HDD| exact HSL| exact FL| intros ms2 PO; exact (KERR _ _ PO)].
  Qed.
End S.


End CeilWrap.
