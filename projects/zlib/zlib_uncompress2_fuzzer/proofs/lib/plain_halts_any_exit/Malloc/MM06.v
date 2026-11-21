(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MM15.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require F_malloc_entry.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MM11.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MM14.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MM07.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MM08.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MM13.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MM12.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ASlot_W18.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import F_malloc_entry. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocKit_A.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import Malloc_fp. Import MM14. Import MM14.MallocKit_A2. Import MM07. Import MM07.F_malloc_big.
Import MM08. Import MM08.MallocKit_A3.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition as_fm_link (st0 : mstate) (g head : aptr) : mstate :=
  let hprev := m_prev (get_meta_rec st0 head) in
  let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
  let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
  upd_meta head (m_set_prev (Some g)) st2.

Definition as_fm_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
  set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).

Definition as_queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
  match get_head st0 h with
  | Some head => as_fm_link st0 g head
  | None => as_fm_single st0 h g
  end.

Lemma as_queue_eq : forall R h g st0 (k : mstate -> Malloc.M R) (bail : Malloc.M R),
  m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
  queue h g st0 k bail = k (as_queue_st h g st0).
Proof.
  intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
  unfold as_queue_st, as_fm_link, as_fm_single. destruct (get_head st0 h); reflexivity.
Qed.

Definition as_fm_st (st : mstate) (g : aptr) : mstate := as_queue_st LFree g (put_meta g meta0 st).

Lemma as_free_meta_eq : forall R st g (k : mstate -> Malloc.M R) (bail : Malloc.M R), free_meta g st k bail = k (as_fm_st st g).
Proof.
  intros. unfold free_meta, as_fm_st. apply as_queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.

Lemma outside_In W x lo hi : outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof.
  induction W as [|[a b] W IH]; cbn; intros HO HI; [destruct HI|].
  destruct HI as [E|HI]; [inversion E; subst; tauto|]. apply IH; tauto.
Qed.

Lemma sub_fp_single W lo hi : In (lo, hi) W -> sub_fp [(lo, hi)] W.
Proof. intros HI x HO. cbn. split; [exact (outside_In W x lo hi HO HI)| exact I]. Qed.

Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.
Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
  meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.

Definition failW : list (Z * Z) :=
  (G, G + 40) :: (CTX + 16, CTX + 24)
  :: match c_free_meta_head (ctx st) with
     | Some h => (conc st h, conc st h + 40)
                 :: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
     | None => []
     end.
End FAILM.


End CANSEC1.
End ASlot_W18.

Module ASlot_W6.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocKit_A.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import Malloc_fp. Import MM14. Import MM14.MallocKit_A2.
Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section M.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis FRR : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.

Definition m_regs (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 CTX) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (sc + 10)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition full_skip : bool := (f =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0).
End M.


End CANSEC1.
End ASlot_W6.

Module ASlot_W8.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocKit_A.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import Malloc_fp. Import MM14. Import MM14.MallocKit_A2.
Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section ENTRY.
Variables (st : mstate) (m : mem) (sc lo : Z).
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : ATOP <= lo.
Hypothesis AMS : forall g, active st sc = Some g -> meta_slot st g.
End ENTRY.


End CANSEC1.
End ASlot_W8.

Module F_ntf_A.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree.
Import MM13. Import MM13.MallocKit_B. Import MM12. Import MM12.MallocModel_B.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
End F_ntf_A.

Module F_ntf_C.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import MM13. Import MM13.MallocKit_B. Import F_ntf_A. Import MM07. Import MM07.F_ntf_B.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition qa_facts (st : mstate) (sc : Z) (g : aptr) : Prop :=
  forall head, active st sc = Some head -> head <> g ->
    meta_slot st head /\
    exists pv, m_prev (get_meta_rec st head) = Some pv /\ pv <> g /\ meta_slot st pv.

Definition qpath_st (st : mstate) (sc : Z) (g : aptr) : mstate :=
  if optr_eqb (active st sc) (Some g) then st else queue_st (LActive sc) g st.

End CANSEC1.
End F_ntf_C.
