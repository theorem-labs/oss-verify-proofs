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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_heap_inst0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_heap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
Module Drv_stmt.
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
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_heap_inst0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_heap.KB_drv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_base.
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
    stk psegs m lo (bv_unsigned sp) -> lo + 2^22 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp + 48 <= 0x800000000000 ->
    bv_unsigned sp mod 16 = 0 ->
    mem_inv psegs m -> frm0 fc ->
    DSTAT false tid m -> 0 < bv_unsigned tid < 2^22 ->
    CJST m -> rw_cells psegs m PERRNO [C4 errv] -> rw_cells psegs m PINITFLAG [C1 (Z_to_bv 8 0)] ->
    stdout_file m stdout_init -> stderr_wfile0 m -> (exists stj, rw_cells psegs m PRS [CB RSN stj]) ->
    rw_cells psegs m (bv_unsigned sp + 64) [C8 (wz P1)] ->
    bytes_at psegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
    path_has_slash path = false -> path <> dotdot_path ->   (* [comment removed for export] *)
    (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 131071 -> bv_unsigned sp + 48 <= P1 ->
    realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (wz PMAIN) fc None m (seg_rom psegs)) mo)
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
    stk psegs m lo (bv_unsigned sp) /\ mem_inv psegs m
    /\ rw_cells psegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)
    /\ DSTAT false tid m /\ CJST m /\ (exists e, rw_cells psegs m PERRNO [C4 e]) /\ rw_cells psegs m PINITFLAG [C1 (Z_to_bv 8 0)]
    /\ stdout_file m stdout_init /\ stderr_wfile0 m
    /\ bytes_at psegs m P1 (path ++ Z_to_bv 8 0 :: slack)
    /\ DHEAP cs [(p, A, cap)] SPB m mo /\ RP1 cs d /\ fst p = db_slot d
    /\ DMOD fs (FDS3 (FdFile path (wz len))) mo /\ fs_lookup fs path = Some data
    /\ rw_cells psegs m A [CB (Z.to_nat len) (firstn (Z.to_nat len) data); CB (Z.to_nat (cap - len)) junk]
    /\ (exists stj, rw_cells psegs m PRS [CB RSN stj])
    /\ (exists k : nat, cap = 65536 * 2 ^ (Z.of_nat k)) /\ 0 <= len <= cap /\ len <= zlength data /\ cap <= 2^26.

  (* [comment removed for export] *)
  Definition loop_regs (len cap A : Z) (m : word -> option byte) (pc : Z) : machine_state -> Prop :=
    fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      ms = MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz P1) (wz len) (wz 3) (wz cap) (wz PRS) s7 q8 q9 q10 q11 t3 t4 t5 t6)
              F (wz pc) fc None m (seg_rom psegs).

  (* [comment removed for export] *)
  Definition loop_stmt : Prop :=
    forall len cap A cs p d junk m mo ms,
      loop_inv len cap A cs p d junk m mo -> len < cap -> loop_regs len cap A m 0x12218 ms ->
      realizes psegs (mkCfg ms mo) (Kloop data fs cap).

  (* [comment removed for export] *)
  Definition post_stmt : Prop :=
    forall cap A cs p d junk m mo (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      loop_inv (zlength data) cap A cs p d junk m mo -> zlength data < cap ->
      realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz P1) (wz (zlength data)) (wz 3) (wz cap) (wz PRS) (wz 0) q8 q9 q10 q11 t3 t4 t5 t6)
                              F (wz 0x12240) fc None m (seg_rom psegs)) mo)
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
      ms' = MS (mkR (wz 0x122c0) sp gp tp t0 t1 t2 ms0 ms1 (wz st) a1 a2 a3 a4 a5 a6 a7 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (wz 0x122c0) fc' None m' (seg_rom psegs)
      /\ frm0 fc' /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
      /\ rw_cells psegs m' PERRNO [C4 e'] /\ LHEAPd SPB LB' m' mo' /\ In (A, cap) LB'
      /\ rw_cells psegs m' (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)
      /\ DSTAT true tid m' /\ stderr_wfile0 m' /\ stdout_file m' so /\ DMOD fs FDS0 mo'.

  Definition trun_stmt : Prop :=
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (cs : mstate) (d : dblk) (p : bptr) (junk data : list byte) (cl : Z) (e : word) (KT : TSet),
      let len := zlength data in
      let plen := len - 6 - cl in
      DHEAP cs [(p, A, cap)] SPB m mo -> RP1 cs d ->
      rw_cells psegs m A [CB (Z.to_nat len) data; CB (Z.to_nat (cap - len)) junk] ->
      0 <= cl -> 6 + cl <= len -> len < 2^26 -> len <= cap ->
      DMOD fs FDS0 mo -> frm0 fc ->
      stk psegs m lo (bv_unsigned sp) -> mem_inv psegs m -> CJST m -> rw_cells psegs m PERRNO [C4 e] ->
      rw_cells psegs m PINITFLAG [C1 (Z_to_bv 8 0)] -> DSTAT false tid m -> stdout_file m stdout_init -> stderr_wfile0 m ->
      rw_cells psegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0) ->
      KT [] ->
      (forall ms' mo', trun_ret 0 (so_after (tcalls cl data - 1)) ms' mo' -> realizes psegs (mkCfg ms' mo') KT) ->
      realizes psegs (mkCfg (MS (mkR (wz 0x122c0) sp gp tp t0 t1 t2 ms0 ms1 (wz (A + 2)) (wz cl) (wz (A + 6 + cl)) (wz plen) a4 a5 a6 a7
                                     ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz PTRUN) fc None m (seg_rom psegs)) mo)
               (t_emit (W 1 emit_line) KT).
End TrunStmt.


End CeilWrap.
End Drv_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS ITree Nodes Decode SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio Malloc Prog MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocBlocks Malloc_ifaceP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_pad Exit Printf_model F_printf_iface.
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
Import Drv_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_usage.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_usage.Drv_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
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

  Notation FRAME m := (rw_cells psegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 (wz PSTAGE2_RET))).

  (* [comment removed for export] *)
  Lemma main_free_exit : forall (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (LB : list cblock) (A cap code : Z)
      (so : stdout_st) (e : word) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word) (ph : bool),
    LHEAPd SPB LB m mo -> In (A, cap) LB -> DMOD fs FDS0 mo -> 0 <= code < 256 ->
    rw_cells psegs m PERRNO [C4 e] -> mem_inv psegs m -> stk psegs m lo (bv_unsigned sp) -> FRAME m ->
    DSTAT ph tid m -> stdout_file m so -> zlength (so_buf so) <= 8 -> stderr_wfile0 m ->
    realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz code) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 q8 q9 q10 q11 t3 t4 t5 t6)
                              F (wz 0x12340) fc None m (seg_rom psegs)) mo)
             (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (wz code) fs)).
  Proof.
    intros until ph. intros HL INA DM CODE ER MI ST FR DS SOF SOB SEF.
    pose proof DM as [MOK' MFDS HFS]. pose proof GT as GT'.
    unfold wz.
    eapply rz_step_evt; [exact MOK'|]. do 2 step. apply evt_done.
    eapply (scps_realizes psegs).
    { eapply lhd_free with (lo := lo) (SPB := SPB) (LB := LB);
        first [exact HL| exact INA| exact ST| exact MI| exact ER| exact TP| reflexivity
              | unfold CJ_iface.RMALLOC_STACK; lia]. }
    intros ms' mo' PO VO.
    (nelim PO 22%nat; intros y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m' -> MI' ST' ER' PR HL').
    replace (ret_pc (Z_to_bv 64 0x12348)) with (Z_to_bv 64 0x12348) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
    realizes psegs (mkCfg ms mo) (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (wz (if 128 <=? bv_unsigned b1 then 0 else st)) fs)).
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
    rw_cells psegs m PERRNO [C4 e] -> mem_inv psegs m -> stk psegs m lo (bv_unsigned sp) -> FRAME m ->
    DSTAT false tid m -> stdout_file m stdout_init -> stderr_wfile0 m ->
    realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) (wz msgA) (wz 31) a2 (wz 0x23540) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 q8 q9 q10 q11 t3 t4 t5 t6)
                              F (wz 0x12338) fc None m (seg_rom psegs)) mo)
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
    replace (ret_pc (Z_to_bv 64 0x12340)) with (Z_to_bv 64 0x12340) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
    rw_cells psegs m PERRNO [C4 e] -> mem_inv psegs m -> stk psegs m lo (bv_unsigned sp) -> FRAME m ->
    DSTAT false tid m -> stdout_file m stdout_init -> stderr_wfile0 m ->
    realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 q8 q9 q10 q11 t3 t4 t5 t6)
                              F (wz 0x12304) fc None m (seg_rom psegs)) mo)
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
    rw_cells psegs m PERRNO [C4 e] -> mem_inv psegs m -> stk psegs m lo (bv_unsigned sp) -> FRAME m ->
    DSTAT false tid m -> stdout_file m stdout_init -> stderr_wfile0 m ->
    realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 q8 q9 q10 q11 t3 t4 t5 t6)
                              F (wz 0x12320) fc None m (seg_rom psegs)) mo)
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
    eapply (rz_impl_close psegs _ _ mo 3 (FdFile path (Z_to_bv 64 len))); [exact MOK'| | rewrite MFDS; reflexivity|].
    { eapply close_spec with (lo := lo) (errv := e);
        first [ exact ST | exact MI
              | lazymatch goal with |- _ = _ => reflexivity end
              | rewrite ?(errno_addr_tp tp TP); rewrite ?TP; unfold PERRNO, PTP; rewrite ?unsigned_lit by lia; first [exact ER| lia] ]. }
    cbv zeta. intros ms2 PO.
    (nelim PO 21%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 ST2 ER2).
    cbn [close_ret close_errno] in *. rewrite (errno_addr_tp tp TP) in MU2, ER2.
    replace (ret_pc (Z_to_bv 64 0x12248)) with (Z_to_bv 64 0x12248) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
    pose proof (proj1 (rw_cells_CB_bytes _ _ _ _ (proj1 (proj1 (rw_cells_app psegs m2 A [CB (Z.to_nat len) data] _) BLK2)))) as BYA.
    destruct (nth_error data 0) as [b0|] eqn:Hb0. 2:{ exfalso. apply nth_error_None in Hb0. subst len; unfold zlength in *; lia. }
    destruct (nth_error data 1) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. subst len; unfold zlength in *; lia. }
    pose proof (u8ro_read psegs m2 A data 0 b0 _ BYA Hb0 ltac:(lia) eq_refl) as RD0.
    pose proof (u8ro_read psegs m2 A data 1 b1 _ BYA Hb1 ltac:(lia) eq_refl) as RD1.
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
    pose proof (u8ro_read psegs m2 A data (2 + cl + 0) p0 _ BYA Hp0 ltac:(lia) eq_refl) as RP0.
    pose proof (u8ro_read psegs m2 A data (2 + cl + 1) p1 _ BYA Hp1 ltac:(lia) eq_refl) as RP1.
    pose proof (u8ro_read psegs m2 A data (2 + cl + 2) p2 _ BYA Hp2 ltac:(lia) eq_refl) as RP2.
    pose proof (u8ro_read psegs m2 A data (2 + cl + 3) p3 _ BYA Hp3 ltac:(lia) eq_refl) as RP3.
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
