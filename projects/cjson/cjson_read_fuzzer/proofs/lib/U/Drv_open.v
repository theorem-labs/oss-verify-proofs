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
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_heap_instR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_heap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
Module Drv_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei.   (* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_heap_instR.CJ_heap_inst0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_heap.KB_drv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_base.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


Definition main_two_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
         (fs : Fs) (lo P1 : Z) (tid : word) (path slack : list byte) (errv : word),
    DMOD fs FDS0 mo -> DHEAP0 (bv_unsigned sp + 48) m mo ->
    ra = wz PSTAGE2_RET -> tp = wz PTP -> a0 = wz 2 -> a1 = wz (bv_unsigned sp + 56) ->
    stk usegs m lo (bv_unsigned sp) -> lo + 2^22 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp + 48 <= 0x800000000000 ->
    bv_unsigned sp mod 16 = 0 ->
    mem_inv usegs m -> frm0 fc ->
    DSTAT false tid m -> 0 < bv_unsigned tid < 2^22 ->
    CJST m -> rw_cells usegs m PERRNO [C4 errv] -> rw_cells usegs m PINITFLAG [C1 (Z_to_bv 8 0)] ->
    stdout_file m stdout_init -> stderr_wfile0 m -> (exists stj, rw_cells usegs m PRS [CB RSN stj]) ->
    rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz P1)] ->
    bytes_at usegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
    path_has_slash path = false -> path <> dotdot_path ->   (* [comment removed for export] *)
    (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 131071 -> bv_unsigned sp + 48 <= P1 ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (wz PMAIN) fc None m (seg_rom usegs)) mo)
             (spec_path path fs).


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition Kloop (data : list byte) (fs : Fs) (cap : Z) : TSet := t_body data fs.

Section LoopStmts.
  (* [comment removed for export] *)
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (fs : Fs) (lo SPB P1 : Z) (tid ra0 : word)
            (path slack data : list byte) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 : word) (q8 q9 q10 q11 : word).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition loop_inv (len cap A : Z) (cs : mstate) (p : bptr) (d : dblk) (junk : list byte) (m : word -> option byte) (mo : Model) : Prop :=
    stk usegs m lo (bv_unsigned sp) /\ mem_inv usegs m
    /\ rw_cells usegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)
    /\ DSTAT false tid m /\ CJST m /\ (exists e, rw_cells usegs m PERRNO [C4 e]) /\ rw_cells usegs m PINITFLAG [C1 (Z_to_bv 8 0)]
    /\ stdout_file m stdout_init /\ stderr_wfile0 m
    /\ bytes_at usegs m P1 (path ++ Z_to_bv 8 0 :: slack)
    /\ DHEAP cs [(p, A, cap)] SPB m mo /\ RP1 cs d /\ fst p = db_slot d
    /\ DMOD fs (FDS3 (FdFile path (wz len))) mo /\ fs_lookup fs path = Some data
    /\ rw_cells usegs m A [CB (Z.to_nat len) (firstn (Z.to_nat len) data); CB (Z.to_nat (cap - len)) junk]
    /\ (exists stj, rw_cells usegs m PRS [CB RSN stj])
    /\ (exists k : nat, cap = 65536 * 2 ^ (Z.of_nat k)) /\ 0 <= len <= cap /\ len <= zlength data /\ cap <= 2^26.

  (* [comment removed for export] *)
  Definition loop_regs (len cap A : Z) (m : word -> option byte) (pc : Z) : machine_state -> Prop :=
    fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      ms = MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz P1) (wz len) (wz 3) (wz cap) (wz PRS) s7 q8 q9 q10 q11 t3 t4 t5 t6)
              F (wz pc) fc None m (seg_rom usegs).

  (* [comment removed for export] *)
  Definition loop_stmt : Prop :=
    forall len cap A cs p d junk m mo ms,
      loop_inv len cap A cs p d junk m mo -> len < cap -> loop_regs len cap A m 0x13238 ms ->
      realizes usegs (mkCfg ms mo) (Kloop data fs cap).

  (* [comment removed for export] *)
  Definition post_stmt : Prop :=
    forall cap A cs p d junk m mo (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      loop_inv (zlength data) cap A cs p d junk m mo -> zlength data < cap ->
      realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz P1) (wz (zlength data)) (wz 3) (wz cap) (wz PRS) (wz 0) q8 q9 q10 q11 t3 t4 t5 t6)
                              F (wz 0x13260) fc None m (seg_rom usegs)) mo)
               (t_body data fs).
End LoopStmts.

Lemma Kloop_top : forall data fs cap, t_eq (Kloop data fs cap) (t_body data fs).
Proof. intros data fs cap. apply t_eq_refl. Qed.

Lemma Kloop_nil : forall data fs cap, Kloop data fs cap [].
Proof. intros data fs cap. unfold Kloop. apply t_body_nil. Qed.

(* [comment removed for export] *)
Definition loop_side (sp tp : word) (fc : bv 32) (lo SPB P1 : Z) (tid : word) (path slack : list byte) : Prop :=
  tp = wz PTP /\ lo + 2^22 <= bv_unsigned sp + 80 /\ alloc_ceiling <= lo /\ bv_unsigned sp + 128 <= 0x800000000000 /\ SPB = bv_unsigned sp + 128
  /\ 0 < bv_unsigned tid < 2^22 /\ frm0 fc /\ ~ In (Z_to_bv 8 0) path /\ (- (P1 + zlength path + 1)) mod 8 <= zlength slack
  /\ zlength path <= 131071 /\ bv_unsigned sp + 128 <= P1 /\ bv_unsigned sp mod 16 = 0.

(* [comment removed for export] *)
Definition trun_side (sp tp : word) (lo SPB : Z) : Prop :=
  tp = wz PTP /\ lo + 2^22 <= bv_unsigned sp + 80 /\ alloc_ceiling <= lo /\ bv_unsigned sp + 128 <= 0x800000000000 /\ SPB = bv_unsigned sp + 128
  /\ bv_unsigned sp mod 16 = 0.

Lemma loop_side_trun : forall sp tp fc lo SPB P1 tid path slack,
  loop_side sp tp fc lo SPB P1 tid path slack -> trun_side sp tp lo SPB.
Proof.
  intros until slack. intros (TP & LO & GT & SPH & SPBE & _ & _ & _ & _ & _ & _ & SPAL).
  split; [exact TP|]. split; [exact LO|]. split; [exact GT|]. split; [exact SPH|]. split; [exact SPBE| exact SPAL].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tcalls (cl : Z) (data : list byte) : nat :=
  match Z.to_nat cl with O => 1%nat | _ => S (Z.to_nat (bv_unsigned (nth 2 data (Z_to_bv 8 0)) mod 4)) end.

(* [comment removed for export] *)
Definition lines (j : nat) : list Z := concat (repeat [48; 10] j).
Definition so_after (j : nat) : stdout_st := mkStdout true (lines j) false false.

Section TrunStmt.
  (* [comment removed for export] *)
  Variables (sp gp tp : word) (fs : Fs) (lo SPB : Z) (tid : word) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 ra0 : word)
            (ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 : word) (A cap : Z).

  (* [comment removed for export] *)
  Definition trun_ret (st : Z) (so : stdout_st) : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (e' : word) (LB' : list cblock),
      ms' = MS (mkR (wz 0x132e0) sp gp tp t0 t1 t2 ms0 ms1 (wz st) a1 a2 a3 a4 a5 a6 a7 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (wz 0x132e0) fc' None m' (seg_rom usegs)
      /\ frm0 fc' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' PERRNO [C4 e'] /\ LHEAPd SPB LB' m' mo' /\ In (A, cap) LB'
      /\ rw_cells usegs m' (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)
      /\ DSTAT true tid m' /\ stderr_wfile0 m' /\ stdout_file m' so /\ DMOD fs FDS0 mo'.

  Definition trun_stmt : Prop :=
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (cs : mstate) (d : dblk) (p : bptr) (junk data : list byte) (cl : Z) (e : word) (KT : TSet),
      let len := zlength data in
      let plen := len - 6 - cl in
      DHEAP cs [(p, A, cap)] SPB m mo -> RP1 cs d ->
      rw_cells usegs m A [CB (Z.to_nat len) data; CB (Z.to_nat (cap - len)) junk] ->
      0 <= cl -> 6 + cl <= len -> len < 2^26 -> len <= cap ->
      DMOD fs FDS0 mo -> frm0 fc ->
      stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m -> CJST m -> rw_cells usegs m PERRNO [C4 e] ->
      rw_cells usegs m PINITFLAG [C1 (Z_to_bv 8 0)] -> DSTAT false tid m -> stdout_file m stdout_init -> stderr_wfile0 m ->
      rw_cells usegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0) ->
      KT [] ->
      (forall ms' mo', trun_ret 0 (so_after (tcalls cl data - 1)) ms' mo' -> realizes usegs (mkCfg ms' mo') KT) ->
      realizes usegs (mkCfg (MS (mkR (wz 0x132e0) sp gp tp t0 t1 t2 ms0 ms1 (wz (A + 2)) (wz cl) (wz (A + 6 + cl)) (wz plen) a4 a5 a6 a7
                                     ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz PTRUN) fc None m (seg_rom usegs)) mo)
               (t_emit (W 1 emit_line) KT).
End TrunStmt.


End CeilWrap.
End Drv_stmt.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_ifaceP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_usage.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module Drv_hdr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_ifaceP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_syscalls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_heap_instR.CJ_heap_inst0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_heap.KB_drv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_heap Drv_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_usage.Drv_exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_emit_app' : forall o1 o2 K, t_eq (t_emit (o1 ++ o2) K) (t_emit o1 (t_emit o2 K)).
Proof.
  intros o1 o2 K tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HK)].
    + destruct (is_prefix_app_split o1 o2 tr Hp) as [Hp1 | (b' & -> & Hp2)]; [left; exact Hp1|].
      right. exists b'. split; [reflexivity|]. left. exact Hp2.
    + right. exists (o2 ++ tr'). split; [rewrite app_assoc; reflexivity|]. right. exists tr'. auto.
  - intros [Hp | (tr' & -> & [Hp2 | (tr'' & -> & HK)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. clear K. revert o2 tr' Hp2. induction o1 as [|x o1 IH]; intros o2 tr' Hp2; cbn; [exact Hp2|]. split; [reflexivity| apply IH; exact Hp2].
    + right. exists tr''. split; [rewrite app_assoc; reflexivity| exact HK].
Qed.

Lemma t_eq_alt2 : forall A A' B B' : TSet, t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof. intros A A' B B' HA HB tr. unfold t_alt2. rewrite (HA tr), (HB tr). reflexivity. Qed.

Lemma lines_length : forall j, zlength (lines j) = 2 * Z.of_nat j.
Proof. intros j. unfold lines, zlength. induction j as [|j IH]; [reflexivity|]. cbn [repeat concat app length]. lia. Qed.

Lemma zero_lines_S : forall j, zero_lines (S j) = emit_line ++ to_bytes (lines j).
Proof. intros j. unfold lines. rewrite zero_lines_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cfg_decode : forall b0 b1 : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (sxb b1)) 57))) 49))) (bv_unsigned (zxb b0))
  = (bv_unsigned b0 + 256 * bv_unsigned b1) mod 32768.
Proof.
  intros b0 b1.
  pose proof (bv_unsigned_in_range 8 b0) as R0. change (bv_modulus 8) with 256 in R0.
  pose proof (bv_unsigned_in_range 8 b1) as R1. change (bv_modulus 8) with 256 in R1.
  unfold sxb, zxb. rewrite !Z_to_bv_unsigned.
  set (r := bv_unsigned b1 mod 128).
  assert (Hr : 0 <= r < 128) by (subst r; apply Z.mod_pos_bound; lia).
  assert (U : exists q, bv_wrap 64 (bv_signed b1) = 128 * q + r /\ 0 <= q).
  { unfold bv_wrap, bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 8) with 256. change (256 `div` 2) with 128. change (2 ^ Z.of_N 64) with 18446744073709551616.
    destruct (Z_lt_dec (bv_unsigned b1) 128).
    - exists (bv_unsigned b1 / 128). rewrite (Z.mod_small (bv_unsigned b1 + 128)) by lia.
      rewrite Z.mod_small by lia. subst r. split; [| apply Z.div_pos; lia]. rewrite <- Z.div_mod by lia. lia.
    - exists ((18446744073709551616 - 256) / 128 + bv_unsigned b1 / 128).
      replace (bv_unsigned b1 + 128) with ((bv_unsigned b1 - 128) + 1 * 256) by lia. rewrite Z.mod_add, (Z.mod_small (bv_unsigned b1 - 128)) by lia.
      replace (bv_unsigned b1 - 128 - 128) with ((18446744073709551616 - 256 + bv_unsigned b1) + (-1) * 18446744073709551616) by lia.
      rewrite Z.mod_add, Z.mod_small by lia. subst r.
      pose proof (Z.div_mod (bv_unsigned b1) 128 ltac:(lia)). split; [| lia].
      change ((18446744073709551616 - 256) `div` 128) with 144115188075855870. lia. }
  (nelim U 3%nat; intros q -> Hq).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace ((128 * q + r) * 2 ^ 57) with (r * 2 ^ 57 + q * 2 ^ 64) by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_add by lia. rewrite (Z.mod_small (r * 2 ^ 57)) by lia.
  replace (r * 2 ^ 57) with (r * 2 ^ 8 * 2 ^ 49) by lia. rewrite Z.div_mul by lia.
  rewrite (Z.mod_small (r * 2 ^ 8)) by lia. rewrite (Z.mod_small (bv_unsigned b0)) by lia.
  replace (r * 2 ^ 8) with (Z.shiftl r 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  rewrite Z.lor_comm, lor_shiftl8_add by lia.
  subst r. rewrite <- (Z.mod_small (bv_unsigned b0 + 256 * (bv_unsigned b1 mod 128)) 32768).
  2:{ pose proof (Z.mod_pos_bound (bv_unsigned b1) 128). lia. }
  replace 32768 with (256 * 128) by reflexivity.
  rewrite <- (Z.mod_add _ (bv_unsigned b1 / 128)) by lia. f_equal.
  pose proof (Z.div_mod (bv_unsigned b1) 128 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma t_body_run : forall data fs (b0 b1 : byte) (cl len : Z),
  nth_error data 0 = Some b0 -> nth_error data 1 = Some b1 ->
  len = zlength data -> cl = (bv_unsigned b0 + 256 * bv_unsigned b1) mod 32768 ->
  len < MAX_INPUT -> 6 + cl <= len ->
  t_body data fs = t_emit (W 1 (zero_lines (tcalls cl data))) (t_exit (exit_code 0) fs).
Proof.
  intros data fs b0 b1 cl len H0 H1 HL HC MX OV.
  pose proof (bv_unsigned_in_range 8 b0) as R0. change (bv_modulus 8) with 256 in R0.
  pose proof (bv_unsigned_in_range 8 b1) as R1. change (bv_modulus 8) with 256 in R1.
  assert (Hcl : 0 <= cl < 32768) by (subst cl; apply Z.mod_pos_bound; lia).
  unfold t_body. subst len. unfold zlength in *.
  replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; lia).
  replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  rewrite (nth_error_nth _ _ _ H0), (nth_error_nth _ _ _ H1). cbv zeta. rewrite <- HC.
  replace (length data <? 6 + Z.to_nat cl)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  unfold tcalls. reflexivity.
Qed.

Lemma tcalls_S : forall cl data, exists j : nat, tcalls cl data = S j /\ (j <= 3)%nat.
Proof.
  intros cl data. unfold tcalls. destruct (Z.to_nat cl).
  - exists 0%nat. split; [reflexivity| lia].
  - eexists. split; [reflexivity|]. pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 data (Z_to_bv 8 0))) 4 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Definition trun_all : Prop :=
  forall sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap,
    trun_side sp tp lo SPB -> trun_stmt sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap.

Section S.
  Hypothesis SO_EXIT : so_exit_stmt.
  Hypothesis SO_SHORT : so_diag_short_stmt.
  Hypothesis SO_OVERRUN : so_diag_overrun_stmt.
  Hypothesis TRUN : trun_all.

  Variables (sp gp tp : word) (fs : Fs) (lo SPB P1 : Z) (tid : word)
            (path slack data : list byte) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 : word) (q8 q9 q10 q11 : word).
  Hypothesis TP : tp = wz PTP.
  Hypothesis LO : lo + 2^22 <= bv_unsigned sp + 80.
  Hypothesis GT : alloc_ceiling <= lo.
  Hypothesis SPH : bv_unsigned sp + 128 <= 0x800000000000.
  Hypothesis SPBE : SPB = bv_unsigned sp + 128.
  Hypothesis TID : 0 < bv_unsigned tid < 2^22.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.

  Notation FRAME m := (rw_cells usegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 (wz PSTAGE2_RET))).

  (* [comment removed for export] *)
  Lemma main_free_exit : forall (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (LB : list cblock) (A cap code : Z)
      (so : stdout_st) (e : word) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word) (ph : bool),
    LHEAPd SPB LB m mo -> In (A, cap) LB -> DMOD fs FDS0 mo -> 0 <= code < 256 ->
    rw_cells usegs m PERRNO [C4 e] -> mem_inv usegs m -> stk usegs m lo (bv_unsigned sp) -> FRAME m ->
    DSTAT ph tid m -> stdout_file m so -> zlength (so_buf so) <= 8 -> stderr_wfile0 m ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz code) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 q8 q9 q10 q11 t3 t4 t5 t6)
                              F (wz 0x13360) fc None m (seg_rom usegs)) mo)
             (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (wz code) fs)).
  Proof.
    intros until ph. intros HL INA DM CODE ER MI ST FR DS SOF SOB SEF.
    pose proof DM as [MOK' MFDS HFS]. pose proof GT as GT'.
    unfold wz.
    eapply rz_step_evt; [exact MOK'|]. do 2 step. apply evt_done.
    eapply (scps_realizes usegs).
    { eapply lhd_free with (lo := lo) (SPB := SPB) (LB := LB);
        first [exact HL| exact INA| exact ST| exact MI| exact ER| exact TP| reflexivity
              | unfold CJ_iface.RMALLOC_STACK; lia]. }
    intros ms' mo' PO VO.
    (nelim PO 22%nat; intros y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m' -> MI' ST' ER' PR HL').
    replace (ret_pc (Z_to_bv 64 0x13368)) with (Z_to_bv 64 0x13368) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (lhd_mok _ _ _ _ HL') as MOK2.
    (nelim (lhd_libc_cells _ _ _ _ HL') 5%nat; intros cdt thr sec tm1 LC').
    eapply (main_epilogue_exit SO_EXIT) with (lo := lo) (tid := tid) (cdt := cdt) (thr := thr) (sec := sec) (tm1 := tm1) (guard := ssp_guard_val)
                                            (fj := fj) (v0 := v0) (v1 := v1) (v2 := v2) (v3 := v3) (v4 := v4) (v5 := v5) (v6 := v6) (v7 := v7).
    all: first [ eapply DMOD_vm_only; [exact DM| exact VO| exact MOK2]
            | left; reflexivity
            | reflexivity
            | exact CODE | exact TP | exact ST' | exact TID | exact LC' | exact MI'
            | eapply cj_pres_rw_cells; [exact PR| exact FR| left; cbn; lia]
            | eapply DSTAT_cj_pres; [exact DS| exact PR]
            | eapply stdout_file_cj_pres; [exact SOF| exact PR]
            | apply stderr_wfile0_file; eapply stderr_wfile0_cj_pres; [exact SEF| exact PR]
            | eapply lhd_ssp0; exact HL'
            | unfold GLOBALS_TOP; lia
            ].
  Qed.
  (* [comment removed for export] *)
  Lemma sxb_cases : forall b : byte,
    (bv_unsigned b < 128 /\ Z.land (bv_signed b) 18446744073709551615 = bv_unsigned b)
    \/ (128 <= bv_unsigned b /\ Z.land (bv_signed b) 18446744073709551615 = 2^64 - 256 + bv_unsigned b).
  Proof.
    intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
    change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
    unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 8) with 256. change (256 `div` 2) with 128.
    destruct (Z_lt_dec (bv_unsigned b) 128).
    - left. split; [lia|]. rewrite (Z.mod_small (bv_unsigned b + 128)) by lia. rewrite Z.mod_small by lia. lia.
    - right. split; [lia|]. replace (bv_unsigned b + 128) with ((bv_unsigned b - 128) + 1 * 256) by lia. rewrite Z.mod_add, (Z.mod_small (bv_unsigned b - 128)) by lia.
      replace (bv_unsigned b - 128 - 128) with ((2 ^ 64 - 256 + bv_unsigned b) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma main_tail : forall (A cap st : Z) (so : stdout_st) (b1 : byte) (ms0 ms2 ms3 ms4 : word) ms mo,
    trun_ret sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 (wz PSTAGE2_RET) ms0 (wz A) ms2 ms3 ms4 (Z_to_bv 64 (bv_signed b1)) (wz PRS) (wz 0) q8 q9 q10 q11 A cap st so ms mo ->
    0 <= st < 256 -> zlength (so_buf so) <= 8 ->
    realizes usegs (mkCfg ms mo) (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (wz (if 128 <=? bv_unsigned b1 then 0 else st)) fs)).
  Proof.
    intros until mo. intros RET ST8 SOB.
    (nelim RET 31%nat; intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' e' LB' -> FRM' MI' ST' ER' HL' INA FR DS SEF SOF DM).
    pose proof DM as [MOK' MFDS HFS].
    pose proof (bv_unsigned_in_range 8 b1) as R1. change (bv_modulus 8) with 256 in R1.
    unfold wz. eapply rz_step_evt; [exact MOK'|].
    step. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      destruct (sxb_cases b1) as [[B1 E]|[B1 E]]; rewrite E in K; [exfalso; lia|].
      replace (128 <=? bv_unsigned b1) with true by (symmetry; apply Z.leb_le; lia).
      do 6 step. if_true. apply evt_done.
      eapply main_free_exit; [exact HL'| exact INA| exact DM| lia| exact ER'| exact MI'| exact ST'| exact FR| exact DS| exact SOF| exact SOB| exact SEF].
    - destruct (sxb_cases b1) as [[B1 E]|[B1 E]]; rewrite E in K; [| exfalso; lia].
      replace (128 <=? bv_unsigned b1) with false by (symmetry; apply Z.leb_gt; lia).
      do 2 step. apply evt_done.
      eapply main_free_exit; [exact HL'| exact INA| exact DM| lia| exact ER'| exact MI'| exact ST'| exact FR| exact DS| exact SOF| exact SOB| exact SEF].
  Qed.
  (* [comment removed for export] *)
  Lemma main_fwrite_die : forall (msgA : Z) (msg : list byte) (SO : so_diag_lit_stmt msgA 31 msg)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (LB : list cblock) (A cap : Z) (e : word)
      (ra t0 t1 t2 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word),
    LHEAPd SPB LB m mo -> In (A, cap) LB -> DMOD fs FDS0 mo ->
    rw_cells usegs m PERRNO [C4 e] -> mem_inv usegs m -> stk usegs m lo (bv_unsigned sp) -> FRAME m ->
    DSTAT false tid m -> stdout_file m stdout_init -> stderr_wfile0 m ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) (wz msgA) (wz 31) a2 (wz 0x24688) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 q8 q9 q10 q11 t3 t4 t5 t6)
                              F (wz 0x13358) fc None m (seg_rom usegs)) mo)
             (t_die msg fs).
  Proof.
    intros until t6. intros HL INA DM ER MI ST FR DS SOF SEF.
    pose proof DM as [MOK' MFDS HFS]. destruct (DMOD_chan _ _ _ DM ltac:(left; reflexivity)) as [CH1 CH2].
    pose proof (lhd_ssp0 _ _ _ _ HL) as SSP.
    unfold wz. unfold PERRNO in ER.
    apply rz_die. eapply rz_step_evt; [exact MOK'|]. do 2 step. apply evt_done.
    eapply (SO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo lo ssp_guard_val);
      first [exact MOK'| exact CH2| exact SEF| exact ST| exact SSP| exact MI| reflexivity| apply t_emit_has_nil'| unfold FWRITE_DEPTH, GLOBALS_TOP; lia| idtac].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 SEF2 SSP2.
    replace (ret_pc (Z_to_bv 64 0x13360)) with (Z_to_bv 64 0x13360) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof GT as GT'.
    assert (HL2 : LHEAPd SPB LB m2 mo).
    { eapply lhd_frame_ext; [exact HL| exact MU2| exact WM2| solve_Forall ltac:(drv_write_ok_tac)]. }
    xport ER MU2 WM2 ER2. xport FR MU2 WM2 FR2. xport DS MU2 WM2 DS2. xport SOF MU2 WM2 SOF2.
    change (W 1 []) with (W 1 (to_bytes (so_buf stdout_init))).
    eapply main_free_exit; [exact HL2| exact INA| exact DM| lia| exact ER2| exact MI2| exact ST2| exact FR2| exact DS2| exact SOF2| unfold zlength; cbn [length so_buf stdout_init Z.of_nat]; lia| exact SEF2].
  Qed.

  (* [comment removed for export] *)
  Lemma main_short : forall (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (LB : list cblock) (A cap : Z) (e : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word),
    LHEAPd SPB LB m mo -> In (A, cap) LB -> DMOD fs FDS0 mo ->
    rw_cells usegs m PERRNO [C4 e] -> mem_inv usegs m -> stk usegs m lo (bv_unsigned sp) -> FRAME m ->
    DSTAT false tid m -> stdout_file m stdout_init -> stderr_wfile0 m ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 q8 q9 q10 q11 t3 t4 t5 t6)
                              F (wz 0x13324) fc None m (seg_rom usegs)) mo)
             (t_die msg_short fs).
  Proof.
    intros until t6. intros HL INA DM ER MI ST FR DS SOF SEF.
    pose proof DM as [MOK' _ _]. (nelimp DS 13%nat; intros _ _ _ _ _ _ _ _ _ _ G1 G2 _). unfold wz in G1, G2.
    unfold wz. eapply rz_step_evt; [exact MOK'|]. do 7 step. apply evt_done.
    apply (main_fwrite_die A_MSG_short msg_short SO_SHORT F fc m mo LB A cap e); assumption.
  Qed.

  Lemma main_overrun : forall (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (LB : list cblock) (A cap : Z) (e : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word),
    LHEAPd SPB LB m mo -> In (A, cap) LB -> DMOD fs FDS0 mo ->
    rw_cells usegs m PERRNO [C4 e] -> mem_inv usegs m -> stk usegs m lo (bv_unsigned sp) -> FRAME m ->
    DSTAT false tid m -> stdout_file m stdout_init -> stderr_wfile0 m ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 q8 q9 q10 q11 t3 t4 t5 t6)
                              F (wz 0x13340) fc None m (seg_rom usegs)) mo)
             (t_die msg_overrun fs).
  Proof.
    intros until t6. intros HL INA DM ER MI ST FR DS SOF SEF.
    pose proof DM as [MOK' _ _]. (nelimp DS 13%nat; intros _ _ _ _ _ _ _ _ _ _ G1 G2 _). unfold wz in G1, G2.
    unfold wz. eapply rz_step_evt; [exact MOK'|]. do 6 step. apply evt_done.
    apply (main_fwrite_die A_MSG_overrun msg_overrun SO_OVERRUN F fc m mo LB A cap e); assumption.
  Qed.
  (* [comment removed for export] *)
  Theorem post_ok : forall (F : bvmap 5 word) (fc : bv 32),
    frm0 fc -> post_stmt sp gp tp F fc fs lo SPB P1 tid (wz PSTAGE2_RET) path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.
  Proof.
    intros F fc FRM. unfold post_stmt. intros cap A cs p d junk m mo ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 IV LT.
    (nelim IV 21%nat; intros ST MI FR DS CJ [e ER] IFL SOF SEF BY DH RP PD DM FL BLK [stj RSC] [k CAP] LEN1 LEN2 CAP2).
    pose proof DM as [MOK' MFDS HFS].
    pose proof (dheap_block_range _ _ _ _ _ (p, A, cap) DH ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    (nelimp BR 5%nat; intros BR1 BR2 BR3 BR4 BR5). unfold alloc_ceiling in BR4.
    set (len := zlength data) in *.
    unfold wz in *. unfold PERRNO in ER. unfold PINITFLAG in IFL.
    (* [comment removed for export] *)
    eapply rz_step_evt; [exact MOK'|]. do 2 step. apply evt_done.
    eapply (rz_impl_close usegs _ _ mo 3 (FdFile path (Z_to_bv 64 len))); [exact MOK'| | rewrite MFDS; reflexivity|].
    { eapply close_spec with (lo := lo) (errv := e);
        first [ exact ST | exact MI
              | lazymatch goal with |- _ = _ => reflexivity end
              | rewrite ?(errno_addr_tp tp TP); rewrite ?TP; unfold PERRNO, PTP; rewrite ?unsigned_lit by lia; first [exact ER| lia] ]. }
    cbv zeta. intros ms2 PO.
    (nelim PO 21%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 ST2 ER2).
    cbn [close_ret close_errno] in *. rewrite (errno_addr_tp tp TP) in MU2, ER2.
    replace (ret_pc (Z_to_bv 64 0x13268)) with (Z_to_bv 64 0x13268) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite MFDS, FDS3_remove.
    xport FR MU2 WM2 FR2. xport DS MU2 WM2 DS2. xport CJ MU2 WM2 CJ2. xport IFL MU2 WM2 IFL2. xport SOF MU2 WM2 SOF2. xport SEF MU2 WM2 SEF2.
    xport BLK MU2 WM2 BLK2.
    assert (DH2 : DHEAP cs [(p, A, cap)] SPB m2 (with_fds FDS0 mo)).
    { apply (dheap_model cs _ SPB m2 mo); [| reflexivity| destruct MOK' as [Hh _]; exact Hh].
      eapply dheap_frame_ext; [exact DH| exact MU2| exact WM2| solve_Forall ltac:(drv_write_ok_tac)]. }
    assert (DM2 : DMOD fs FDS0 (with_fds FDS0 mo)) by (eapply DMOD_with_fds; exact DM).
    pose proof (dheap_mok _ _ _ _ _ DH2) as MOK2.
    clear FR DS IFL SOF SEF BLK DH MU2 WM2 ST MI ER.
    (* [comment removed for export] *)
    eapply rz_step_evt; [exact MOK2|]. do 2 step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    { apply evt_done.
      replace (t_body data fs) with (t_die msg_short fs).
      2:{ unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; subst len; unfold zlength in *; lia).
          replace (length data <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; subst len; unfold zlength in *; lia). reflexivity. }
      eapply main_short; [eapply dheap_lheap; exact DH2| left; reflexivity| exact DM2| exact ER2| exact MI2| exact ST2| exact FR2| exact DS2| exact SOF2| exact SEF2]. }
    (* [comment removed for export] *)
    rewrite firstn_all2 in BLK2 by (subst len; unfold zlength in *; lia).
    pose proof (proj1 (rw_cells_CB_bytes _ _ _ _ (proj1 (proj1 (rw_cells_app usegs m2 A [CB (Z.to_nat len) data] _) BLK2)))) as BYA.
    destruct (nth_error data 0) as [b0|] eqn:Hb0. 2:{ exfalso. apply nth_error_None in Hb0. subst len; unfold zlength in *; lia. }
    destruct (nth_error data 1) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. subst len; unfold zlength in *; lia. }
    pose proof (u8ro_read usegs m2 A data 0 b0 _ BYA Hb0 ltac:(lia) eq_refl) as RD0.
    pose proof (u8ro_read usegs m2 A data 1 b1 _ BYA Hb1 ltac:(lia) eq_refl) as RD1.
    replace (wa (A + 0)) with (wa A) in RD0 by (f_equal; lia).
    pose proof (bv_unsigned_in_range 8 b0) as Rb0. change (bv_modulus 8) with 256 in Rb0.
    pose proof (bv_unsigned_in_range 8 b1) as Rb1. change (bv_modulus 8) with 256 in Rb1.
    do 5 step. rewrite cfg_decode.
    set (cl := (bv_unsigned b0 + 256 * bv_unsigned b1) mod 32768) in *.
    assert (Hcl : 0 <= cl < 32768) by (subst cl; apply Z.mod_pos_bound; lia).
    (* [comment removed for export] *)
    do 2 step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    { apply evt_done.
      replace (t_body data fs) with (t_die msg_overrun fs).
      2:{ unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; subst len; unfold zlength in *; lia).
          replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; subst len; unfold zlength in *; lia).
          rewrite (nth_error_nth _ _ _ Hb0), (nth_error_nth _ _ _ Hb1). cbv zeta.
          replace (length data <? 6 + Z.to_nat ((bv_unsigned b0 + 256 * bv_unsigned b1) mod 32768))%nat with true
            by (symmetry; apply Nat.ltb_lt; subst len cl; unfold zlength in *; lia). reflexivity. }
      eapply main_overrun; [eapply dheap_lheap; exact DH2| left; reflexivity| exact DM2| exact ER2| exact MI2| exact ST2| exact FR2| exact DS2| exact SOF2| exact SEF2]. }
    (* [comment removed for export] *)
    destruct (nth_error data (Z.to_nat (2 + cl + 0))) as [p0|] eqn:Hp0. 2:{ exfalso. apply nth_error_None in Hp0. subst len; unfold zlength in *; lia. }
    destruct (nth_error data (Z.to_nat (2 + cl + 1))) as [p1|] eqn:Hp1. 2:{ exfalso. apply nth_error_None in Hp1. subst len; unfold zlength in *; lia. }
    destruct (nth_error data (Z.to_nat (2 + cl + 2))) as [p2|] eqn:Hp2. 2:{ exfalso. apply nth_error_None in Hp2. subst len; unfold zlength in *; lia. }
    destruct (nth_error data (Z.to_nat (2 + cl + 3))) as [p3|] eqn:Hp3. 2:{ exfalso. apply nth_error_None in Hp3. subst len; unfold zlength in *; lia. }
    pose proof (u8ro_read usegs m2 A data (2 + cl + 0) p0 _ BYA Hp0 ltac:(lia) eq_refl) as RP0.
    pose proof (u8ro_read usegs m2 A data (2 + cl + 1) p1 _ BYA Hp1 ltac:(lia) eq_refl) as RP1.
    pose proof (u8ro_read usegs m2 A data (2 + cl + 2) p2 _ BYA Hp2 ltac:(lia) eq_refl) as RP2.
    pose proof (u8ro_read usegs m2 A data (2 + cl + 3) p3 _ BYA Hp3 ltac:(lia) eq_refl) as RP3.
    replace (wa (A + (2 + cl + 0))) with (wa (A + 2 + cl)) in RP0 by (f_equal; lia).
    replace (wa (A + (2 + cl + 1))) with (wa (A + 2 + cl + 1)) in RP1 by (f_equal; lia).
    replace (wa (A + (2 + cl + 2))) with (wa (A + 2 + cl + 2)) in RP2 by (f_equal; lia).
    replace (wa (A + (2 + cl + 3))) with (wa (A + 2 + cl + 3)) in RP3 by (f_equal; lia).
    do 6 step.
    do 16 step. apply evt_done.
    rewrite (unsigned_lit cl) by lia.
    replace (Z_to_bv 64 (A + 2 + cl + 4)) with (Z_to_bv 64 (A + 6 + cl)) by (f_equal; lia).
    replace (Z_to_bv 64 (len + - cl + -6)) with (Z_to_bv 64 (len - 6 - cl)) by (f_equal; lia).
    unfold sxb.
    clear RD0 RD1 RP0 RP1 RP2 RP3 Hp0 Hp1 Hp2 Hp3 BYA.
    (* [comment removed for export] *)
    rewrite (t_body_run data fs b0 b1 cl len Hb0 Hb1 eq_refl eq_refl ltac:(unfold MAX_INPUT; lia) ltac:(lia)).
    (nelim (tcalls_S cl data) 3%nat; intros j TC J3). rewrite TC.
    assert (SIDE : trun_side sp tp lo SPB).
    { split; [exact TP|]. split; [exact LO|]. split; [exact GT|]. split; [exact SPH|]. split; [exact SPBE| exact SPAL]. }
    eapply rz_conseq.
    { eapply (TRUN sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 PSTAGE2_RET) _ _ _ _ _ _ _ _ q8 q9 q10 q11 A cap SIDE
                    _ _ _ _ _ _ _ _ _ _ _ F fc m2 (with_fds FDS0 mo) cs d p junk data cl e
                    (t_emit (W 1 (to_bytes (lines j))) (t_exit (Z_to_bv 64 0) fs)));
        first [ exact DH2 | exact RP | exact BLK2 | exact DM2 | exact FRM | exact ST2 | exact MI2 | exact CJ2 | exact ER2 | exact IFL2 | exact DS2 | exact SOF2 | exact SEF2 | exact FR2
              | apply t_emit_has_nil'
              | lia
              | idtac ].
      - (* [comment removed for export] *)
        intros ms' mo' RET. rewrite TC in RET. replace (S j - 1)%nat with j in RET by lia.
        replace (t_exit (Z_to_bv 64 0) fs) with (t_exit (wz (if 128 <=? bv_unsigned b1 then 0 else 0)) fs) by (destruct (128 <=? bv_unsigned b1); reflexivity).
        change (lines j) with (so_buf (so_after j)).
        eapply main_tail; [exact RET| lia| cbn [so_buf so_after]; rewrite lines_length; lia]. }
    (* [comment removed for export] *)
    cbv zeta. unfold exit_code. rewrite zero_lines_S. subst len. unfold W. rewrite map_app.
    apply t_eq_sym. apply t_emit_app'.
  Qed.
End S.

(* [comment removed for export] *)
Theorem post_proof :
  so_exit_stmt -> so_diag_short_stmt -> so_diag_overrun_stmt -> trun_all ->
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (fs : Fs) (lo SPB P1 : Z) (tid : word)
         (path slack data : list byte) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11 : word),
    loop_side sp tp fc lo SPB P1 tid path slack ->
    post_stmt sp gp tp F fc fs lo SPB P1 tid (wz PSTAGE2_RET) path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.
Proof.
  intros SE SS SV TR. intros until q11. intros nelH_; (nelim nelH_ 12%nat; intros TP LO GT SPH SPBE TID FRM NONUL SLK LEN PUS SPAL).
  eapply post_ok; eassumption.
Qed.

End CeilWrap.
End Drv_hdr.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_SiteM0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module Drv_loop.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_SiteM0.KB_Sites.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_ifaceP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_heap_instR.CJ_heap_inst0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_heap.KB_drv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_heap Drv_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_usage.Drv_exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_usage.Drv_die.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.

(* [comment removed for export] *)
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
Local Ltac lia ::= first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma firstn_add_skipn : forall {X} (l : list X) n k, firstn (n + k) l = firstn n l ++ firstn k (skipn n l).
Proof.
  intros X l n. revert l. induction n as [|n IH]; intros l k; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma firstn_app_read : forall {X} (data : list X) (len n want : nat),
  n = length (firstn want (skipn len data)) ->
  firstn len data ++ firstn want (skipn len data) = firstn (len + n) data.
Proof.
  intros X data len n want ->. rewrite firstn_add_skipn. f_equal.
  rewrite length_firstn. rewrite Nat.min_comm. symmetry.
  destruct (Nat.le_gt_cases want (length (skipn len data))).
  - rewrite Nat.min_r by lia. reflexivity.
  - rewrite Nat.min_l by lia. rewrite !firstn_all2 by lia. reflexivity.
Qed.

Lemma pow2_ge1 : forall k : nat, 1 <= 2 ^ Z.of_nat k.
Proof. intros k. pose proof (Z.pow_le_mono_r 2 0 (Z.of_nat k) ltac:(lia) ltac:(lia)) as H. change (2 ^ 0) with 1 in H. exact H. Qed.

Section S.
  Hypothesis SO_EXIT : so_exit_stmt.
  Hypothesis SO_OOM : so_diag_oom_stmt.
  Hypothesis SO_REFUSED : so_diag_refused_stmt.
  Hypothesis SO_READERR : so_diag_read_error_stmt.

  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (fs : Fs) (lo SPB P1 : Z) (tid ra0 : word)
            (path slack data : list byte) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 : word) (q8 q9 q10 q11 : word).
  Hypothesis TP : tp = wz PTP.
  Hypothesis LO : lo + 2^22 <= bv_unsigned sp + 80.
  Hypothesis GT : alloc_ceiling <= lo.
  Hypothesis SPH : bv_unsigned sp + 128 <= 0x800000000000.
  Hypothesis SPBE : SPB = bv_unsigned sp + 128.
  Hypothesis TID : 0 < bv_unsigned tid < 2^22.
  Hypothesis FRM : frm0 fc.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) path.
  Hypothesis SLK : (- (P1 + zlength path + 1)) mod 8 <= zlength slack.
  Hypothesis LEN : zlength path <= 131071.
  Hypothesis PUS : bv_unsigned sp + 128 <= P1.

  Notation INV := (loop_inv sp fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7).
  Notation REGS := (loop_regs sp gp tp F fc P1 q8 q9 q10 q11).

  (* [comment removed for export] *)
  Definition HEAD_OK (bound : Z) : Prop :=
    forall len cap A cs p d junk m mo ms,
      INV len cap A cs p d junk m mo -> len < cap -> REGS len cap A m 0x13238 ms -> zlength data - len < bound ->
      realizes usegs (mkCfg ms mo) (Kloop data fs cap).

  Hypothesis POST : post_stmt sp gp tp F fc fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.

  Lemma head_ok_mono : forall b b', HEAD_OK b -> b' <= b -> HEAD_OK b'.
  Proof. intros b b' H LE len cap A cs p d junk m mo ms IV LT RG LT'. apply (H len cap A cs p d junk m mo ms IV LT RG). lia. Qed.

  Lemma cap_next : forall (cap : Z) (k : nat), cap = 65536 * 2 ^ Z.of_nat k -> cap < 2 ^ 26 -> cap * 2 <= 2 ^ 26 /\ cap * 2 = 65536 * 2 ^ Z.of_nat (S k).
  Proof.
    intros cap k -> LT. split.
    - destruct (Z_lt_dec (Z.of_nat k) 10).
      + pose proof (Z.pow_le_mono_r 2 (Z.of_nat k) 9 ltac:(lia) ltac:(lia)). cbn in *. lia.
      + pose proof (Z.pow_le_mono_r 2 10 (Z.of_nat k) ltac:(lia) ltac:(lia)). cbn in *. lia.
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_grow : forall (cap A : Z) cs p d junk m mo (b : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      INV cap cap A cs p d junk m mo -> HEAD_OK b -> zlength data - cap < b ->
      realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz P1) (wz cap) (wz 3) (wz cap) (wz PRS) (wz A) q8 q9 q10 q11 t3 t4 t5 t6)
                                F (wz 0x13200) fc None m (seg_rom usegs)) mo)
               (Kloop data fs cap).
  Proof.
    intros until t6. intros IV IH IHb.
    (nelim IV 21%nat; intros ST MI FR DS CJ [e ER] IFL SOF SEF BY DH RP PD DM FL BLK [stj RSC] [k CAP] LEN1 LEN2 CAP2).
    pose proof RSN_Z as HRSN. pose proof PRS_eq as HPRS.
    pose proof DM as [MOK' MFDS HFS].
    pose proof (dheap_block_range _ _ _ _ _ (p, A, cap) DH ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    (nelimp BR 5%nat; intros BR1 BR2 BR3 BR4 BR5). unfold alloc_ceiling in BR4.
    pose proof (pow2_ge1 k) as K2.   (* [comment removed for export] *)
    assert (BR6 : 0x56000 <= A) by (destruct BR5; lia). clear BR5.   (* [comment removed for export] *)
    unfold wz in *. unfold PERRNO in ER. unfold PINITFLAG in IFL.
    eapply rz_step_evt; [exact MOK'|].
    do 2 step. if_cases K; zify_cond K; rewrite Z.shiftr_div_pow2 in K by lia.
    - (* [comment removed for export] *)
      assert (CAPB : 2 ^ 26 <= cap) by (apply Z.nlt_ge; intros Hlt; apply K; apply Z.div_small; lia).
      apply evt_done.
      replace (Kloop data fs cap) with (t_die msg_refused fs).
      2:{ unfold Kloop.
          unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT, zlength in *; lia). reflexivity. }
      (nelim (dheap_libc_cells _ _ _ _ _ DH) 5%nat; intros cdt thr sec tm1 LC).
      eapply die_refused with (lo := lo) (tid := tid) (cdt := cdt) (thr := thr) (sec := sec) (tm1 := tm1) (guard := ssp_guard_val);
        first [exact SO_EXIT| exact SO_REFUSED| exact DM| right; eexists; reflexivity| exact TP| exact TID| exact FRM
              | split; [exact ST| split; [exact MI| split; [exact DS| split; [exact LC| split; [eapply dheap_ssp0; exact DH| split; [exact SOF| exact SEF]]]]]]
              | unfold GLOBALS_TOP; lia ].
    - (* [comment removed for export] *)
      assert (CAPB : cap < 2 ^ 26) by (destruct (Z_lt_dec cap (2 ^ 26)) as [Hl|Hl]; [exact Hl|]; exfalso; pose proof (Z.div_str_pos cap (2 ^ 26) ltac:(lia)); lia).
      destruct (cap_next cap k CAP CAPB) as [CAP2' CAPS].
      do 3 step. apply evt_done.
      rewrite (unsigned_lit cap) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      (nelim (rp1_RP _ _ RP) 3%nat; intros fl lo1 HRP).
      pose proof (big_site _ _ _ _ (cap * 2) HRP ltac:(unfold MMAP_THRESHOLD; lia)) as SITE. unfold MEX_iface.big_site in SITE.
      pose proof (rp_bounds_small rp_bounds _ _ _ _ HRP) as SMALL.
      (* [comment removed for export] *)
      change (Kloop data fs cap) with (Kloop data fs (cap * 2)).
      eapply (drv_malloc_site _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo cs [(p, A, cap)] SPB (cap * 2) lo (cap * 2 + 20) (cap * 2 + 20) e);
        first [exact DH| exact SITE| exact SMALL| exact ST| exact ER| exact MI| exact TP| reflexivity
              | unfold CJ_iface.RMALLOC_STACK; lia | idtac].
      + (* [comment removed for export] *)
        intros ms2 mo2 m2 errv2 cs' c' off' A' junk' RPO VO MI2 ST2 ER2 PR BR' NIN BLK' DH2 LEAF.
        (nelim RPO 15%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 ->).
        replace (ret_pc (Z_to_bv 64 0x13214)) with (Z_to_bv 64 0x13214) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (dheap_mok _ _ _ _ _ DH2) as MOK2. (nelimp BR' 5%nat; intros BQ1 BQ2 BQ3 BQ4 BQ5). unfold alloc_ceiling in BQ4.
        assert (BQ6 : 0x56000 <= A') by (destruct BQ5; lia). clear BQ5.   (* [comment removed for export] *)
        cbn [map bview blk_addr blk_size fst snd] in PR. cbn [map blk_addr fst snd] in NIN.
        assert (NE : A' <> A) by (intros E; apply NIN; left; symmetry; exact E). clear NIN.
        destruct LEAF as [ans LEAF].
        pose proof (big_follow cs d (cap * 2) ans cs' (Some c') RP ltac:(unfold MMAP_THRESHOLD; lia) LEAF) as BF.
        cbv beta iota in BF. (nelim BF 4%nat; intros dnew RP2' Ec' _). clear LEAF ans.
        (* [comment removed for export] *)
        assert (BLKo : rw_cells usegs m2 A [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data)]).
        { pose proof (proj1 (proj1 (rw_cells_app usegs m A [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data)] _) BLK)) as B1.
          eapply cj_pres_rw_cells; [exact PR| exact B1| right; right; exists A, cap; split; [left; reflexivity| cbn; lia]]. }
        pose proof BLK' as BLKn.
        eapply (rw_cells_split_CB usegs m2 A' [] (Z.to_nat (cap * 2)) junk' [] [Z.to_nat cap; Z.to_nat cap]) in BLKn; [| cbn; lia]. cbn [mk_CB_cells app] in BLKn.
        pose proof (proj1 (rw_cells_app usegs m2 A' [CB (Z.to_nat cap) (firstn (Z.to_nat cap) junk')] _) BLKn) as [BLKn1 BLKn2].
        replace (A' + Z.of_nat (cells_size [CB (Z.to_nat cap) (firstn (Z.to_nat cap) junk')])) with (A' + cap) in BLKn2 by (cbn; lia). clear BLKn.
        pose proof (dheap_blocks_disjoint _ _ _ _ _ A' (cap * 2) A cap DH2 ltac:(left; reflexivity) ltac:(right; left; reflexivity) NE) as DISJ.
        (* [comment removed for export] *)
        eapply rz_step_evt; [exact MOK2|]. unfold wz.
        step. if_cases K'; zify_cond K'; [exfalso; lia|]. clear K'.
        step. step. if_cases K'; zify_cond K'; [exfalso; lia|]. clear K'.
        do 4 step.
        assert (LSRC : length (firstn (Z.to_nat cap) data) = Z.to_nat cap) by (rewrite length_firstn; unfold zlength in *; lia).
        eapply evt_cut.
        { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (firstn (Z.to_nat cap) data) (firstn (Z.to_nat cap) junk'));
            rewrite ?unsigned_lit by lia; [| exact LSRC| exact BLKn1| lia| exact MI2].
          exact (proj1 (rw_cells_CB_bytes _ _ _ _ BLKo)). }
        intros ms3 nelH_; (nelim nelH_ 21%nat; intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m3 -> MU3 WM3 MI3 DST3 SRC3).
        rewrite ?unsigned_lit in MU3 by lia. rewrite ?unsigned_lit in DST3 by lia. rewrite ?unsigned_lit in SRC3 by lia.
        replace (ret_pc (Z_to_bv 64 0x13230)) with (Z_to_bv 64 0x13230) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold zlength in *. rewrite ?unsigned_lit in MU3 by lia. rewrite ?unsigned_lit in DST3 by lia.
        (* [comment removed for export] *)
        pose proof (stk_transport_disjoint usegs _ _ _ _ _ ST2 MU3 WM3 ltac:(cbn; lia)) as ST3.
        xport ER2 MU3 WM3 ER3. xport BLKn2 MU3 WM3 BLKn3.
        assert (DH3 : DHEAP cs' [(c', off', A', cap * 2); (p, A, cap)] SPB m3 mo2).
        { eapply dheap_frame_ext; [exact DH2| exact MU3| exact WM3|].
          solve_Forall ltac:(right; right; right; right; exists A', (cap * 2); split; [left; reflexivity| cbn [fst snd]; lia]). }
        (* [comment removed for export] *)
        do 2 step. apply evt_done.
        eapply (drv_free _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 mo2 cs' [(c', off', A', cap * 2); (p, A, cap)] SPB p A cap lo errv2);
          first [exact DH3| right; left; reflexivity| exact ST3| exact ER3| exact MI3| exact TP| reflexivity
                | unfold CJ_iface.RMALLOC_STACK; lia | idtac].
        intros ms4 mo4 m4 cs4 a04 RPO4 VO4 MI4 ST4 ER4 PR4 DH4 FL4.
        rewrite (dheap_remove_old _ _ _ _ _ _ _ _ _ _ DH3) in PR4, DH4.
        (nelim RPO4 15%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 ->).
        replace (ret_pc (Z_to_bv 64 0x13238)) with (Z_to_bv 64 0x13238) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (dheap_mok _ _ _ _ _ DH4) as MOK4.
        cbn [map bview blk_addr blk_size fst snd] in PR4.
        (* [comment removed for export] *)
        destruct FL4 as [ans4 FL4]. rewrite PD in FL4.
        pose proof (free_follow cs' d dnew ans4 cs4 RP2' FL4) as RP4.
        (* [comment removed for export] *)
        assert (FR4 : rw_cells usegs m4 (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)).
        { assert (FR2 : rw_cells usegs m2 (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0))
            by (eapply cj_pres_rw_cells; [exact PR| exact FR| left; unfold mframe; cbn; lia]).
          xport FR2 MU3 WM3 FR3. eapply cj_pres_rw_cells; [exact PR4| exact FR3| left; unfold mframe; cbn; lia]. }
        assert (RSC4 : rw_cells usegs m4 PRS [CB RSN stj]).
        { assert (RSC2 : rw_cells usegs m2 PRS [CB RSN stj])
            by (eapply cj_pres_rw_cells; [exact PR| exact RSC| right; left; unfold PRS, PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; pose proof RSN_Z; cbn; lia]).
          xport RSC2 MU3 WM3 RSC3.
          eapply cj_pres_rw_cells; [exact PR4| exact RSC3| right; left; unfold PRS, PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; pose proof RSN_Z; cbn; lia]. }
        assert (DS4 : DSTAT false tid m4).
        { pose proof (DSTAT_cj_pres _ _ _ _ _ _ DS PR) as DS2. xport DS2 MU3 WM3 DS3. eapply DSTAT_cj_pres; [exact DS3| exact PR4]. }
        assert (CJ4 : CJST m4).
        { pose proof (CJST_pres _ _ _ _ PR CJ) as CJ2. xport CJ2 MU3 WM3 CJ3. eapply CJST_pres; [exact PR4| exact CJ3]. }
        assert (IFL4 : rw_cells usegs m4 PINITFLAG [C1 (Z_to_bv 8 0)]).
        { assert (IFL2 : rw_cells usegs m2 PINITFLAG [C1 (Z_to_bv 8 0)])
            by (unfold PINITFLAG; eapply cj_pres_rw_cells; [exact PR| exact IFL| right; left; unfold PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; cbn; lia]).
          xport IFL2 MU3 WM3 IFL3. unfold PINITFLAG in *.
          eapply cj_pres_rw_cells; [exact PR4| exact IFL3| right; left; unfold PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; cbn; lia]. }
        assert (SOF4 : stdout_file m4 stdout_init).
        { pose proof (stdout_file_cj_pres _ _ _ _ _ SOF PR) as SOF2. xport SOF2 MU3 WM3 SOF3. eapply stdout_file_cj_pres; [exact SOF3| exact PR4]. }
        assert (SEF4 : stderr_wfile0 m4).
        { pose proof (stderr_wfile0_cj_pres _ _ _ _ SEF PR) as SEF2. xport SEF2 MU3 WM3 SEF3. eapply stderr_wfile0_cj_pres; [exact SEF3| exact PR4]. }
        assert (BY4 : bytes_at usegs m4 P1 (path ++ Z_to_bv 8 0 :: slack)).
        { pose proof (cj_pres_bytes_at _ _ _ _ _ _ PR BY ltac:(left; lia)) as BY2. xport BY2 MU3 WM3 BY3.
          eapply cj_pres_bytes_at; [exact PR4| exact BY3| left; lia]. }
        assert (BLK4 : rw_cells usegs m4 A' [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data); CB (Z.to_nat (cap * 2 - cap)) (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk'))]).
        { eapply cj_pres_rw_cells; [exact PR4| | right; right; exists A', (cap * 2); split; [left; reflexivity| cbn; lia]].
          apply (proj2 (rw_cells_app usegs m3 A' [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data)] _)). split; [exact DST3|].
          cbn [cells_size csize Nat.add]. replace (A' + Z.of_nat (Z.to_nat cap + 0)) with (A' + cap) by lia.
          replace (Z.to_nat (cap * 2 - cap)) with (Z.to_nat cap) by lia. exact BLKn3. }
        assert (DM4 : DMOD fs (FDS3 (FdFile path (Z_to_bv 64 cap))) mo4).
        { eapply DMOD_vm_only; [| exact VO4| exact MOK4]. eapply DMOD_vm_only; [exact DM| exact VO| exact MOK2]. }
        assert (IV4 : INV cap (cap * 2) A' cs4 (c', off') dnew (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk')) m4 mo4).
        { split; [exact ST4|]. split; [exact MI4|]. split; [exact FR4|]. split; [exact DS4|]. split; [exact CJ4|]. split; [exists errv2; exact ER4|]. split; [exact IFL4|].
          split; [exact SOF4|]. split; [exact SEF4|]. split; [exact BY4|]. split; [exact DH4|]. split; [exact RP4|]. split; [cbn [fst]; exact Ec'|]. split; [exact DM4|]. split; [exact FL|].
          split; [exact BLK4|]. split; [exists stj; exact RSC4|]. split; [exists (S k); exact CAPS|]. unfold zlength in *. lia. }
        clear FR4 DS4 CJ4 IFL4 SOF4 SEF4 BY4 BLK4 RSC4 DH3 PR4 PR.
        (* [comment removed for export] *)
        eapply (IH cap (cap * 2) A' cs4 (c', off') dnew _ m4 mo4 _ IV4); [lia| | unfold zlength in *; lia].
        unfold loop_regs. unfold wz. nexists 17%nat. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_read : forall (len cap A : Z) cs p d junk m mo (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (want : Z),
      INV len cap A cs p d junk m mo -> HEAD_OK (zlength data - len) ->
      len < cap -> want = Z.min (cap - len) 65536 ->
      realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 (wz want) a3 a4 a5 a6 a7 (wz P1) (wz len) (wz 3) (wz cap) (wz PRS) s7 q8 q9 q10 q11 t3 t4 t5 t6)
                                F (wz 0x13248) fc None m (seg_rom usegs)) mo)
               (Kloop data fs cap).
  Proof.
    intros until want. intros IV IH LT WANT.
    (nelim IV 21%nat; intros ST MI FR DS CJ [e ER] IFL SOF SEF BY DH RP PD DM FL BLK [stj RSC] [k CAP] LEN1 LEN2 CAP2).
    pose proof RSN_Z as HRSN. pose proof PRS_eq as HPRS.
    pose proof DM as [MOK' MFDS HFS].
    pose proof (dheap_block_range _ _ _ _ _ (p, A, cap) DH ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    (nelimp BR 5%nat; intros BR1 BR2 BR3 BR4 BR5). unfold alloc_ceiling in BR4.
    pose proof (pow2_ge1 k) as K2.   (* [comment removed for export] *)
    assert (BR6 : 0x56000 <= A) by (destruct BR5; lia). clear BR5.   (* [comment removed for export] *)
    unfold wz in *. unfold PERRNO in ER. unfold PINITFLAG in IFL.
    (* [comment removed for export] *)
    assert (RSCs : rw_cells usegs m PRS [CB (Z.to_nat want) (firstn (Z.to_nat want) stj); CB (Z.to_nat (65536 - want)) (firstn (Z.to_nat (65536 - want)) (skipn (Z.to_nat want) stj))]).
    { eapply (rw_cells_split_CB usegs m PRS [] RSN stj [] [Z.to_nat want; Z.to_nat (65536 - want)]) in RSC; [| pose proof RSN_Z; cbn [sum_nat]; lia].
      cbn [mk_CB_cells app] in RSC. exact RSC. }
    pose proof (proj1 (rw_cells_app usegs m PRS [CB (Z.to_nat want) (firstn (Z.to_nat want) stj)] _) RSCs) as [RSCa RSCb].
    replace (PRS + Z.of_nat (cells_size [CB (Z.to_nat want) (firstn (Z.to_nat want) stj)])) with (PRS + want) in RSCb by (pose proof RSN_Z; cbn; lia).
    clear RSCs.
    eapply rz_step_evt; [exact MOK'|].
    do 3 step. apply evt_done.
    eapply (rz_impl_read_file usegs _ _ mo 3 (bv_unsigned (Z_to_bv 64 PRS)) want path (Z_to_bv 64 len) data);
      [exact MOK'| | rewrite MFDS; reflexivity| rewrite HFS; exact FL| rewrite rw_bytes_max_val; lia| rewrite unsigned_lit by lia; rewrite TASK_SIZE_val; unfold PRS; lia|].
    { eapply read_spec with (lo := lo) (junk := firstn (Z.to_nat want) stj) (errv := e);
      first [ exact ST | exact MI
            | lazymatch goal with |- _ = _ => reflexivity end
            | rewrite ?(errno_addr_tp tp TP); rewrite ?TP; unfold PERRNO, PTP, PRS; rewrite ?unsigned_lit by lia; first [exact RSCa| exact ER| lia] ]. }
    cbv zeta. intros ms2 PO.
    (nelim PO 23%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 ST2 RSC2 ER2 Hn).
    cbn [read_ret] in *. rewrite (errno_addr_tp tp TP) in MU2, ER2. rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in RSC2 by lia.
    set (bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 want)) in *.
    replace (ret_pc (Z_to_bv 64 0x13254)) with (Z_to_bv 64 0x13254) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite MFDS, FDS3_insert.
    assert (LBS : Z.of_nat (length bs) = Z.min want (zlength data - len)).
    { subst bs. rewrite length_file_read. unfold word_to_nat. unfold zlength in *. rewrite !unsigned_lit by lia. lia. }
    set (n := Z.of_nat (length bs)) in *.
    assert (Hn' : 0 <= n <= want) by lia.
    assert (BS : firstn (Z.to_nat len) data ++ bs = firstn (Z.to_nat (len + n)) data).
    { subst bs. rewrite file_read_unguarded. unfold word_to_nat. rewrite !unsigned_lit by lia.
      replace (Z.to_nat (len + n)) with (Z.to_nat len + Z.to_nat n)%nat by lia. apply firstn_app_read.
      subst n. rewrite Nat2Z.id. rewrite file_read_unguarded. unfold word_to_nat. rewrite !unsigned_lit by lia. reflexivity. }
    (* [comment removed for export] *)
    xport FR MU2 WM2 FR2. xport DS MU2 WM2 DS2. xport CJ MU2 WM2 CJ2. xport IFL MU2 WM2 IFL2. xport SOF MU2 WM2 SOF2. xport SEF MU2 WM2 SEF2. xport BY MU2 WM2 BY2.
    xport BLK MU2 WM2 BLK2. xport RSCb MU2 WM2 RSCb2.
    assert (DH2 : DHEAP cs [(p, A, cap)] SPB m2 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo)).
    { apply (dheap_model cs _ SPB m2 mo); [| reflexivity| destruct MOK' as [Hh _]; exact Hh].
      eapply dheap_frame_ext; [exact DH| exact MU2| exact WM2|].
      solve_Forall ltac:(first [drv_write_ok_tac| unfold PRS; drv_write_ok_tac]). }
    assert (DM2 : DMOD fs (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo)).
    { eapply DMOD_with_fds. exact DM. }
    pose proof (dheap_mok _ _ _ _ _ DH2) as MOK2.
    (* [comment removed for export] *)
    eapply rz_step_evt; [exact MOK2|].
    step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
    do 2 step.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (NPOS : 0 < n) by (rewrite ?unsigned_lit in K by lia; lia). clear K.
      (* [comment removed for export] *)
      pose proof BLK2 as BLK0.
      eapply (rw_cells_split_CB usegs m2 A [CB (Z.to_nat len) (firstn (Z.to_nat len) data)] (Z.to_nat (cap - len)) junk [] [Z.to_nat n; Z.to_nat (cap - len - n)]) in BLK2; [| cbn; lia].
      cbn [mk_CB_cells app] in BLK2.
      pose proof (proj1 (rw_cells_app usegs m2 A [CB (Z.to_nat len) (firstn (Z.to_nat len) data)] _) BLK2) as [BLKa BLKbc].
      pose proof (proj1 (rw_cells_app usegs m2 _ [CB (Z.to_nat n) (firstn (Z.to_nat n) junk)] _) BLKbc) as [BLKb BLKc].
      replace (A + Z.of_nat (cells_size [CB (Z.to_nat len) (firstn (Z.to_nat len) data)])) with (A + len) in BLKb, BLKc by (cbn; lia).
      replace (A + len + Z.of_nat (cells_size [CB (Z.to_nat n) (firstn (Z.to_nat n) junk)])) with (A + len + n) in BLKc by (cbn; lia).
      clear BLK2 BLKbc.
      (* [comment removed for export] *)
      pose proof (proj1 (rw_cells_app usegs m2 PRS [CB (length bs) bs] _) RSC2) as [RSC2a RSC2b].
      replace (PRS + Z.of_nat (cells_size [CB (length bs) bs])) with (PRS + n) in RSC2b by (pose proof RSN_Z; cbn; lia).
      do 4 step.   (* [comment removed for export] *)
      eapply evt_cut.
      { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 bs (firstn (Z.to_nat n) junk));
          rewrite ?unsigned_lit by lia; [| lia| exact BLKb| lia| exact MI2].
        exact (proj1 (rw_cells_CB_bytes _ _ _ _ RSC2a)). }
      intros ms3 nelH_; (nelim nelH_ 21%nat; intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m3 -> MU3 WM3 MI3 DST3 SRC3).
      rewrite ?unsigned_lit in MU3 by lia. rewrite ?unsigned_lit in DST3 by lia. rewrite ?unsigned_lit in SRC3 by lia.
      replace (ret_pc (Z_to_bv 64 0x131ec)) with (Z_to_bv 64 0x131ec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (* [comment removed for export] *)
      pose proof (stk_transport_disjoint usegs _ _ _ _ _ ST2 MU3 WM3 ltac:(cbn; lia)) as ST3.
      xport FR2 MU3 WM3 FR3. xport DS2 MU3 WM3 DS3. xport CJ2 MU3 WM3 CJ3. xport IFL2 MU3 WM3 IFL3. xport SOF2 MU3 WM3 SOF3. xport SEF2 MU3 WM3 SEF3.
      xport BY2 MU3 WM3 BY3. xport ER2 MU3 WM3 ER3. xport BLKa MU3 WM3 BLKa3. xport BLKc MU3 WM3 BLKc3.
      xport RSC2b MU3 WM3 RSC2b3. xport RSCb2 MU3 WM3 RSCb3.
      pose proof (rw_cells_transport _ _ _ _ _ _ RSC2a MU3 WM3 ltac:(cbn; lia)) as RSC2a3.
      assert (DH3 : DHEAP cs [(p, A, cap)] SPB m3 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo)).
      { eapply dheap_frame_ext; [exact DH2| exact MU3| exact WM3|].
        solve_Forall ltac:(right; right; right; right; exists A, cap; split; [left; reflexivity| cbn [fst snd]; lia]). }
      (* [comment removed for export] *)
      assert (BLK3 : rw_cells usegs m3 A [CB (Z.to_nat (len + n)) (firstn (Z.to_nat (len + n)) data); CB (Z.to_nat (cap - (len + n))) (firstn (Z.to_nat (cap - len - n)) (skipn (Z.to_nat n) junk))]).
      { assert (J1 : rw_cells usegs m3 A ([CB (Z.to_nat len) (firstn (Z.to_nat len) data)] ++ ([CB (length bs) bs] ++ [CB (Z.to_nat (cap - len - n)) (firstn (Z.to_nat (cap - len - n)) (skipn (Z.to_nat n) junk))]))).
        { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact BLKa3|]. cbn [cells_size csize Nat.add].
          replace (A + Z.of_nat (Z.to_nat len + 0)) with (A + len) by lia.
          apply (proj2 (rw_cells_app _ _ _ _ _)). split.
          - replace (length bs) with (Z.to_nat n) by lia. exact DST3.
          - cbn [cells_size csize Nat.add]. replace (A + len + Z.of_nat (length bs + 0)) with (A + len + n) by lia. exact BLKc3. }
        cbn [app] in J1.
        pose proof (rw_cells_merge usegs m3 A [] [CB (Z.to_nat len) (firstn (Z.to_nat len) data); CB (length bs) bs] _ J1) as J2.
        cbn [app cells_size cells_bytes csize cbytes] in J2. rewrite app_nil_r, BS in J2.
        replace (Z.to_nat len + (length bs + 0))%nat with (Z.to_nat (len + n)) in J2 by lia.
        replace (Z.to_nat (cap - (len + n))) with (Z.to_nat (cap - len - n)) by lia. exact J2. }
      (* [comment removed for export] *)
      assert (RSC3 : exists stj', rw_cells usegs m3 PRS [CB RSN stj']).
      { assert (J1 : rw_cells usegs m3 PRS ([CB (length bs) bs] ++ ([CB (Z.to_nat want - length bs) (skipn (length bs) (firstn (Z.to_nat want) stj))] ++ [CB (Z.to_nat (65536 - want)) (firstn (Z.to_nat (65536 - want)) (skipn (Z.to_nat want) stj))]))).
        { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact RSC2a3|]. cbn [cells_size csize Nat.add].
          replace (PRS + Z.of_nat (length bs + 0)) with (PRS + n) by lia.
          apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact RSC2b3|].
          cbn [cells_size csize Nat.add]. replace (PRS + n + Z.of_nat (Z.to_nat want - length bs + 0)) with (PRS + want) by lia. exact RSCb3. }
        cbn [app] in J1.
        pose proof (rw_cells_merge usegs m3 PRS [] [_; _; _] [] J1) as J2. cbn [app cells_size cells_bytes csize cbytes] in J2. rewrite ?app_nil_r in J2.
        eexists. replace RSN with (length bs + (Z.to_nat want - length bs + (Z.to_nat (65536 - want) + 0)))%nat by (pose proof RSN_Z; lia). exact J2. }
      assert (IV3 : INV (len + n) cap A cs p d (firstn (Z.to_nat (cap - len - n)) (skipn (Z.to_nat n) junk)) m3 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo)).
      { split; [exact ST3|]. split; [exact MI3|]. split; [exact FR3|]. split; [exact DS3|]. split; [exact CJ3|]. split; [exists e; exact ER3|]. split; [exact IFL3|].
        split; [exact SOF3|]. split; [exact SEF3|]. split; [exact BY3|]. split; [exact DH3|]. split; [exact RP|]. split; [exact PD|]. split; [exact DM2|]. split; [exact FL|].
        split; [exact BLK3|]. split; [exact RSC3|]. split; [exists k; exact CAP|]. unfold zlength in *. lia. }
      clear FR3 DS3 CJ3 IFL3 SOF3 SEF3 BY3 BLK3 RSC3 DH3.
      (* [comment removed for export] *)
      unfold wz.
      do 3 step. if_cases K; zify_cond K.
      + (* [comment removed for export] *)
        apply evt_done. assert (E : len + n = cap) by (rewrite ?unsigned_lit in K by lia; lia).
        rewrite E in IV3 |- *. replace (n + len) with cap by lia.
        eapply (loop_grow cap A cs p d _ m3 _ (zlength data - len) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IV3 IH); unfold zlength in *; lia.
      + (* [comment removed for export] *)
        do 2 step. apply evt_done.
        eapply (IH (len + n) cap A cs p d _ m3 _ _ IV3); [rewrite ?unsigned_lit in K by lia; lia| | lia].
        unfold loop_regs. unfold wz. nexists 17%nat. replace (n + len) with (len + n) by lia. reflexivity.
    - (* [comment removed for export] *)
      apply evt_done.
      assert (EOFL : len = zlength data) by (rewrite ?unsigned_lit in K by lia; unfold zlength in *; lia).
      assert (N0 : n = 0) by (rewrite ?unsigned_lit in K by lia; lia).
      assert (RSC3 : exists stj', rw_cells usegs m2 PRS [CB RSN stj']).
      { assert (BS0 : length bs = 0%nat) by (clear - N0; subst n; lia).
        apply length_zero_iff_nil in BS0. rewrite BS0 in RSC2.
        cbn [length cells_size] in RSC2.
        assert (J1 : rw_cells usegs m2 PRS ([CB (Z.to_nat want - 0) (skipn 0 (firstn (Z.to_nat want) stj))] ++ [CB (Z.to_nat (65536 - want)) (firstn (Z.to_nat (65536 - want)) (skipn (Z.to_nat want) stj))])).
        { apply (proj2 (rw_cells_app _ _ _ _ _)). split.
          - pose proof (proj2 (proj1 (rw_cells_app usegs m2 PRS [CB 0 []] _) RSC2)) as R. cbn [cells_size csize Nat.add] in R. rewrite Z.add_0_r in R. exact R.
          - cbn [cells_size csize Nat.add]. replace (PRS + Z.of_nat (Z.to_nat want - 0 + 0)) with (PRS + want) by lia. exact RSCb2. }
        pose proof (rw_cells_merge usegs m2 PRS [] [_; _] [] J1) as J2. cbn [app cells_size cells_bytes csize cbytes] in J2. rewrite ?app_nil_r in J2.
        eexists. replace RSN with (Z.to_nat want - 0 + (Z.to_nat (65536 - want) + 0))%nat by (pose proof RSN_Z; lia). exact J2. }
      assert (IV2 : INV len cap A cs p d junk m2 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo)).
      { split; [exact ST2|]. split; [exact MI2|]. split; [exact FR2|]. split; [exact DS2|]. split; [exact CJ2|]. split; [exists e; exact ER2|]. split; [exact IFL2|].
        split; [exact SOF2|]. split; [exact SEF2|]. split; [exact BY2|]. split; [rewrite N0, Z.add_0_r in DH2; rewrite N0, Z.add_0_r; exact DH2|]. split; [exact RP|]. split; [exact PD|].
        split; [rewrite N0, Z.add_0_r in DM2 |- *; exact DM2|]. split; [exact FL|].
        split; [exact BLK2|]. split; [exact RSC3|]. split; [exists k; exact CAP|]. unfold zlength in *. lia. }
      rewrite N0, Z.add_0_r in IV2 |- *. subst len.
      unfold Kloop.
      rewrite ?unsigned_lit by lia.
      eapply POST; [exact IV2| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma loop_want : forall (len cap A : Z) cs p d junk m mo (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      INV len cap A cs p d junk m mo -> HEAD_OK (zlength data - len) -> len < cap ->
      realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz P1) (wz len) (wz 3) (wz cap) (wz PRS) s7 q8 q9 q10 q11 t3 t4 t5 t6)
                                F (wz 0x13238) fc None m (seg_rom usegs)) mo)
               (Kloop data fs cap).
  Proof.
    intros until t6. intros IV IH LT.
    (nelimp IV 21%nat; intros _ _ _ _ _ _ _ _ _ _ DH _ _ DM _ _ _ [k CAP] LEN1 LEN2 CAP2).
    pose proof DM as [MOK' _ _].
    unfold wz.
    eapply rz_step_evt; [exact MOK'|].
    step. rewrite (unsigned_lit len) by lia. do 2 step. if_cases K; zify_cond K.
    - apply evt_done. apply (loop_read len cap A cs p d junk m mo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cap - len) IV IH LT); lia.
    - step. apply evt_done. apply (loop_read len cap A cs p d junk m mo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 65536 IV IH LT); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma head_ok : forall n : nat, HEAD_OK (Z.of_nat n).
  Proof.
    induction n as [|n IHn]; intros len cap A cs p d junk m mo ms IV LT RG LT'.
    - exfalso. (nelim IV 21%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LEN1 LEN2 _). unfold zlength in *. lia.
    - pose proof (head_ok_mono _ (zlength data - len) IHn ltac:(lia)) as IH.
      (nelim RG 18%nat; intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 ->).
      apply (loop_want len cap A cs p d junk m mo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IV IH LT).
  Qed.

  Theorem loop_ok : loop_stmt sp gp tp F fc fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.
  Proof.
    intros len cap A cs p d junk m mo ms IV LT RG.
    (nelimp IV 21%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LEN1 LEN2 _).
    apply (head_ok (S (Z.to_nat (zlength data))) len cap A cs p d junk m mo ms IV LT RG). unfold zlength in *. lia.
  Qed.
End S.

(* [comment removed for export] *)
Theorem loop_proof :
  so_exit_stmt -> so_diag_oom_stmt -> so_diag_refused_stmt -> so_diag_read_error_stmt ->
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (fs : Fs) (lo SPB P1 : Z) (tid ra0 : word)
         (path slack data : list byte) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11 : word),
    loop_side sp tp fc lo SPB P1 tid path slack ->
    post_stmt sp gp tp F fc fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11 ->
    loop_stmt sp gp tp F fc fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.
Proof.
  intros SE SO SR SRD. intros until q11. intros (TP & LO & GT & SPH & SPBE & TID & FRM & NONUL & SLK & LEN & PUS & SPAL) POST.
  eapply loop_ok; eassumption.
Qed.


End CeilWrap.
End Drv_loop.

(* [comment removed for export] *)
Module Drv_open_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_syscalls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_heap_instR.CJ_heap_inst0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_heap.KB_drv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_heap Drv_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_usage.Drv_exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_usage.Drv_die.
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
      stk usegs m lo (bv_unsigned sp) -> lo + 2^22 <= bv_unsigned sp + 80 -> alloc_ceiling <= lo -> bv_unsigned sp + 128 <= 0x800000000000 ->
      mem_inv usegs m -> frm0 fc -> DSTAT false tid m -> 0 < bv_unsigned tid < 2^22 ->
      rw_cells usegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0) ->
      CJST m -> rw_cells usegs m PERRNO [C4 errv] -> rw_cells usegs m PINITFLAG [C1 (Z_to_bv 8 0)] ->
      stdout_file m stdout_init -> stderr_wfile0 m -> (exists stj, rw_cells usegs m PRS [CB RSN stj]) ->
      bytes_at usegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
      (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 131071 -> bv_unsigned sp + 128 <= P1 ->
      KH [] ->
      (forall (m' : word -> option byte) (mo' : Model) (cs : mstate) (c : cptr) (off A : Z) (junk stj : list byte) (e' : word) ms',
          stk usegs m' lo (bv_unsigned sp) -> mem_inv usegs m' -> DSTAT false tid m' ->
          rw_cells usegs m' (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0) ->
          CJST m' -> rw_cells usegs m' PERRNO [C4 e'] -> rw_cells usegs m' PINITFLAG [C1 (Z_to_bv 8 0)] ->
          stdout_file m' stdout_init -> stderr_wfile0 m' -> bytes_at usegs m' P1 (path ++ Z_to_bv 8 0 :: slack) ->
          rw_cells usegs m' PRS [CB RSN stj] ->
          DHEAP cs [((c, off), A, 65536)] (bv_unsigned sp + 128) m' mo' -> MLEAF (cs0 (reservedZ usegs)) 65536 cs (Some c) ->
          DMOD fs (FDS3 e3) mo' -> rblock_range A 65536 -> rw_cells usegs m' A [CB (Z.to_nat 65536) junk] ->
          loop_regs sp gp tp F fc P1 s8 s9 s10 s11 0 65536 A m' 0x13238 ms' ->
          realizes usegs (mkCfg ms' mo') KH) ->
      realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) s1 (wz 3) a1 a2 a3 a4 a5 a6 a7 (wz P1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x131ac) fc None m (seg_rom usegs)) mo)
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
      replace (ret_pc (Z_to_bv 64 0x131c0)) with (Z_to_bv 64 0x131c0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
      stk usegs m lo (bv_unsigned sp) -> lo + 2^22 <= bv_unsigned sp + 80 -> alloc_ceiling <= lo -> bv_unsigned sp + 128 <= 0x800000000000 ->
      mem_inv usegs m -> frm0 fc -> DSTAT false tid m -> 0 < bv_unsigned tid < 2^22 ->
      rw_cells usegs m PERRNO [C4 errv] ->
      stdout_file m stdout_init -> stderr_wfile0 m ->
      bytes_at usegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
      (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 131071 -> bv_unsigned sp + 128 <= P1 ->
      rw_cells usegs m PRS [CB RSN stj] -> rblock_range A 65536 ->
      loop_regs sp gp tp F fc P1 q8 q9 q10 q11 0 65536 A m 0x13238 ms ->
      realizes usegs (mkCfg ms mo) (t_die (msg_read_error path) fs).
  Proof.
    intros until ms. intros DM DH TP ST LO GT SPH MI FRM DS TID ER SOF SEF BY NONUL SLK LEN PUS RSC BR (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s7 & t3 & t4 & t5 & t6 & ->).
    pose proof RSN_Z as HRSN. pose proof PRS_eq as HPRS.
    pose proof DM as [MOK' MFDS HFS]. pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4.
    unfold wz in *. unfold PERRNO in ER.
    eapply rz_step_evt; [exact MOK'|].
    do 3 step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
    do 4 step. apply evt_done.
    eapply (rz_impl_read_dir usegs _ _ mo 3 (bv_unsigned (Z_to_bv 64 PRS)) 65536);
      [exact MOK'| | rewrite MFDS; reflexivity| rewrite rw_bytes_max_val; lia| rewrite unsigned_lit by lia; rewrite TASK_SIZE_val; unfold PRS; lia|].
    { eapply read_spec with (lo := lo) (junk := stj) (errv := errv);
      first [ exact ST | exact MI
            | lazymatch goal with |- _ = _ => reflexivity end
            | rewrite ?(errno_addr_tp tp TP); rewrite ?TP; unfold PERRNO, PTP, PRS; rewrite ?unsigned_lit by lia; first [exact RSC| exact ER| lia] ]. }
    intros ms2 PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & RSC2 & ER2 & He).
    cbn [read_ret] in *. rewrite (errno_addr_tp tp TP) in MU2, ER2. rewrite ?unsigned_lit in MU2 by lia.
    replace (ret_pc (Z_to_bv 64 0x13254)) with (Z_to_bv 64 0x13254) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree F_pad Exit F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_heap_instR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_heap_instR.CJ_heap_inst0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_heap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_heap.KB_drv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Drv_base Drv_heap.
Import Drv_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_usage.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_usage.Drv_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_usage.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_usage.Drv_die.
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
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
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
    assert (RSC1 : rw_cells usegs m1 PRS [CB RSN stj]).
    { first [ exact RSC   (* [comment removed for export] *)
            | eapply rw_cells_transport; [exact RSC| exact MU| exact WM| pose proof RSN_Z; cbn; unfold PRS; lia] ]. }
    clear DS SOF SEF CJ DH RSC MU WM.
    pose proof (dheap0_ssp0 _ _ _ DH1) as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (BYP : bytes_at usegs m1 P1 (path ++ [Z_to_bv 8 0])).
    { rewrite (app_assoc_cons path) in BY || idtac.
      replace (path ++ Z_to_bv 8 0 :: slack) with ((path ++ [Z_to_bv 8 0]) ++ slack) in BY by (rewrite <- app_assoc; reflexivity).
      exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) BY)). }
    (* [comment removed for export] *)
    assert (KERR : forall (e : Z) ms2,
      open_post (Z_to_bv 64 0x131ac) sp gp tp (Z_to_bv 64 2) s1 (Z_to_bv 64 P1) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned (Z_to_bv 64 P1)) path errv ssp_guard_val lo m1 (SErr e) ms2 ->
      realizes usegs (mkCfg ms2 mo) (t_die (msg_cannot_open path) fs)).
    { intros e ms2 PO. rewrite (unsigned_lit P1) in PO by lia. (nelim PO 25%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 ST2 ER2 BY2 G1 G2 He).
      cbn [open_ret open_errno] in *. rewrite (errno_addr_tp tp TP) in MU2, ER2.
      replace (ret_pc (Z_to_bv 64 0x131ac)) with (Z_to_bv 64 0x131ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply rz_step_evt; [exact MOK'|]. step. if_cases K; zify_cond K; [| exfalso; lia]. clear K. apply evt_done.
      (nelim (dheap0_libc_cells _ _ _ DH1) 5%nat; intros cdt thr sec tm1 LC1).
      xport DS1 MU2 WM2 DS2. xport LC1 MU2 WM2 LC2. xport SOF1 MU2 WM2 SOF2. xport SEF1 MU2 WM2 SEF2. xport BY MU2 WM2 BY2'.
      eapply die_cantopen with (lo := lo) (cdt := cdt) (thr := thr) (sec := sec) (tm1 := tm1) (guard := ssp_guard_val) (P1 := P1) (slack := slack);
        first [exact SO_EXIT| exact SO_CANTOPEN| exact DM| left; reflexivity| exact TP| exact TID| exact FRM| exact BY2'| exact NONUL| exact SLK| reflexivity
              | split; [exact ST2| split; [exact MI2| split; [exact DS2| split; [exact LC2| split; [split; [exact G1| exact G2]| split; [exact SOF2| exact SEF2]]]]]]
              | unfold GLOBALS_TOP, zlength in *; lia ]. }
    (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (mkCfg ?ms _) _ =>
      eassert (OPEN : impl usegs (at_node usegs) (enode (NOpen path) dec_open) _ ms) end.
    { eapply open_spec with (lo := lo) (errv := errv) (canary := ssp_guard_val);
      first [ exact ST | exact MI | exact NONUL | exact SSP1 | exact SSP2
            | lazymatch goal with |- _ = _ => reflexivity end
            | rewrite ?(errno_addr_tp tp TP); rewrite ?TP; unfold PERRNO, PTP, F_syscalls.got_ssp, F_syscalls.ssp_guard;
              rewrite ?unsigned_lit by lia; first [exact BYP| exact ER| lia] ]. }
    (* [comment removed for export] *)
    unfold spec_path.
    destruct (Nat.leb_spec0 4096 (length path)) as [TL|NTL].
    { eapply (rz_impl_openat_toolong usegs); [exact MOK'| exact OPEN| exact TL| intros ms2 PO; exact (KERR _ _ PO)]. }
    destruct (list_byte_eqb path []) eqn:E0.
    { apply list_byte_eqb_eq in E0. subst path. eapply (rz_impl_openat_empty usegs); [exact MOK'| exact OPEN| intros ms2 PO; exact (KERR _ _ PO)]. }
    apply list_byte_eqb_neq in E0.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?fj :: _) => set (fj0 := fj) in FR end.
    (* [comment removed for export] *)
    assert (KOK : forall (e3 : FdEntry) (KH : TSet) ms2,
      open_post (Z_to_bv 64 0x131ac) sp gp tp (Z_to_bv 64 2) s1 (Z_to_bv 64 P1) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned (Z_to_bv 64 P1)) path errv ssp_guard_val lo m1
                (SVal (bv_unsigned (alloc_fd (m_fds mo)))) ms2 ->
      KH [] ->
      (forall (m' : word -> option byte) (mo' : Model) (cs : mstate) (c : cptr) (off A : Z) (junk stj' : list byte) (e' : word) ms',
          stk usegs m' lo (bv_unsigned sp) -> mem_inv usegs m' -> DSTAT false tid m' ->
          rw_cells usegs m' (bv_unsigned sp) (mframe fj0 s0 s1 s2 s3 s4 s5 s6 s7 (wz PSTAGE2_RET)) ->
          CJST m' -> rw_cells usegs m' PERRNO [C4 e'] -> rw_cells usegs m' PINITFLAG [C1 (Z_to_bv 8 0)] ->
          stdout_file m' stdout_init -> stderr_wfile0 m' -> bytes_at usegs m' P1 (path ++ Z_to_bv 8 0 :: slack) ->
          rw_cells usegs m' PRS [CB RSN stj'] ->
          DHEAP cs [((c, off), A, 65536)] (bv_unsigned sp + 128) m' mo' -> MLEAF (cs0 (reservedZ usegs)) 65536 cs (Some c) ->
          DMOD fs (FDS3 e3) mo' -> rblock_range A 65536 -> rw_cells usegs m' A [CB (Z.to_nat 65536) junk] ->
          loop_regs sp gp tp F fc P1 s8 s9 s10 s11 0 65536 A m' 0x13238 ms' ->
          realizes usegs (mkCfg ms' mo') KH) ->
      realizes usegs (mkCfg ms2 (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) e3) mo)) KH).
    { intros e3 KH ms2 PO KH0 HK. rewrite MFDS, FDS0_insert. rewrite MFDS, FDS0_alloc in PO. unfold wz in PO. rewrite (unsigned_lit 3) in PO by lia. rewrite (unsigned_lit P1) in PO by lia.
      (nelim PO 25%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 ST2 ER2 BY2 G1 G2 Hfd).
      cbn [open_ret open_errno] in *. rewrite (errno_addr_tp tp TP) in MU2, ER2.
      replace (ret_pc (Z_to_bv 64 0x131ac)) with (Z_to_bv 64 0x131ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
      eapply (rz_impl_openat_dot usegs); [exact MOK'| exact OPEN| rewrite MFDS; reflexivity| rewrite MFDS, FDS0_alloc; unfold wz; rewrite unsigned_lit by lia; lia
        | intros e ms2 He PO; exact (KERR _ _ PO) |].
      intros ms2 PO. apply (KOK FdDir _ ms2 PO); [apply t_emit_has_nil'|].
      intros m' mo' cs c off A junk' stj' e' ms' ST' MI' DS' FR' CJ' ER' IFL' SOF' SEF' BY' RSC' DH' LEAF DM' BR BLK LR.
      eapply (dir_read SO_EXIT SO_READERR) with (junk := junk'); first [exact DM'| exact DH'| exact TP| exact ST'| exact MI'| exact FRM| exact DS'| exact TID| exact ER'| exact SOF'| exact SEF'| exact BY'| exact NONUL| exact SLK| exact LEN| exact RSC'| exact BR| exact LR| lia]. }
    apply list_byte_eqb_neq in E1.
    rewrite <- HFS in KERR, KOK |- *. destruct (fs_lookup (m_fs mo) path) as [data|] eqn:FL.
    - (* [comment removed for export] *)
      unfold t_opened.
      eapply (rz_impl_openat_file usegs); [exact MOK'| exact OPEN| lia| exact E0| exact E1| exact HDD| exact HSL| exact FL| rewrite MFDS; reflexivity| rewrite MFDS, FDS0_alloc; unfold wz; rewrite unsigned_lit by lia; lia
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
          eapply (rw_cells_split_CB usegs m' A [] (Z.to_nat 65536) junk' [] [0%nat; Z.to_nat 65536]) in BLK; [| reflexivity].
          cbn [mk_CB_cells firstn skipn app] in BLK. exact BLK. }
        split; [exists stj'; exact RSC'|].
        pose proof (bytes_at_bound _ _ _ _ BY) as BBd.
        split; [exists 0%nat; reflexivity|]. unfold zlength. lia.
      + apply Kloop_top.
    - (* [comment removed for export] *)
      eapply (rz_impl_openat_absent usegs); [exact MOK'| exact OPEN| lia| exact E0| exact E1| exact HDD| exact HSL| exact FL| intros ms2 PO; exact (KERR _ _ PO)].
  Qed.
End S.


End CeilWrap.
