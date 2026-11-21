(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require MM_syscalls.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require RunDraw.
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_B.
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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module F_mm_syscalls.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Export SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Export MM_syscalls.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
End F_mm_syscalls.

Module MallocFacts_B_reach.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import MM15. Import MM15.ProgDeps.
Import MM15. Import MM15.MallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_B.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.


End MallocFacts_B_reach.

Module MallocHINV.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import MM15. Import MM15.ProgDeps.
Import MM15. Import MM15.MallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree.
Import MM13. Export MM13.MallocBlocks.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition HINV_from (resv : list (Z * Z)) (st : mstate) (pbrk : Z) (LB : list block) : Prop :=
  brk_link st pbrk /\ AREACH_from resv st LB.
End CANSEC1.
Notation HINV := (HINV_from agent_reserved).

Section CANSEC2. Context {rc : runConstT}.
Lemma HINV_from_init : forall resv pbrk, HINV_from resv (minit 0 resv ATOP) pbrk [].
Proof. intros. split; [exact I | apply areach_init]. Qed.

Lemma HINV_init : forall pbrk, HINV (minit 0 agent_reserved ATOP) pbrk [].
Proof. intros. apply HINV_from_init. Qed.

Lemma brk_link_ps_iff : forall st s, brk_link_ps st s <-> brk_link st (ps_brk s).
Proof. intros st s. unfold brk_link_ps, brk_link. destruct (c_brk (ctx st)); tauto. Qed.


End CANSEC2.
End MallocHINV.

Module MallocModel_B.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import MM15. Import MM15.MallocRep. Import MM13. Import MM13.MallocKit_B.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition aor_st (st : mstate) (g : aptr) (i : Z) : mstate :=
  upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st.

Definition act_st (st : mstate) (a : aptr) (act : Z) : mstate :=
  upd_meta a (fun r => m_set_avail (Z.land (m_freed r) act) (m_set_freed (Z.ldiff (m_freed r) act) r)) st.
Definition act_of (st : mstate) (a : aptr) : Z :=
  match m_mem (get_meta_rec st a) with
  | Some _ => mask_upto (group_active_idx st (default (0%N, -1) (m_mem (get_meta_rec st a))))
  | None => 0 end.

Lemma activate_group_eq {R} a st (k : mstate -> Z -> M R) bail :
  m_avail (get_meta_rec st a) = 0 ->
  activate_group a st k bail = k (act_st st a (act_of st a)) (Z.land (m_freed (get_meta_rec st a)) (act_of st a)).
Proof. intros H. unfold activate_group, guard, act_of, act_st. rewrite H. reflexivity. Qed.

Definition deq_mid (h : lhead) (g : aptr) (st : mstate) : mstate :=
  let mr := get_meta_rec st g in
  if negb (optr_eqb (m_next mr) (Some g)) then
    let st1 := match m_prev mr with Some pv => upd_meta pv (m_set_next (m_next mr)) st | None => st end in
    let st2 := match m_next mr with Some nx => upd_meta nx (m_set_prev (m_prev mr)) st1 | None => st1 end in
    if optr_eqb (get_head st2 h) (Some g) then set_head h (m_next mr) st2 else st2
  else set_head h None st.
Definition clr_links (r : meta) : meta := m_set_prev None (m_set_next None r).
Lemma dequeue_mid : forall h g st, dequeue h g st = upd_meta g clr_links (deq_mid h g st).
Proof. reflexivity. Qed.

Definition pd_st (an : bool) (st1 : mstate) (sc : Z) : mstate :=
  if an then match active st1 sc with Some a => act_st st1 a (act_of st1 a) | None => st1 end else st1.

Definition grp_del (st : mstate) (g p : aptr) : mstate :=
  del_slots p (get_stride (get_meta_rec st g)) (m_last_idx (get_meta_rec st g) + 1) (del_group p st).
Definition fg_usage_st (st : mstate) (g : aptr) : mstate :=
  let mr := get_meta_rec st g in
  if m_sizeclass mr <? 48 then set_usage (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) st else st.


End CANSEC1.
End MallocModel_B.

Module Malloc_iface.

From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MallocHINV. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.


Section CANSEC1. Context {rc : runConstT}.
Definition AGP : Z := 0x1a800.
Definition ATP : Z := 0x1a620.
Definition ERRNO : Z := ATP - 164.
Definition MALLOC_SYM : Z := 0x1596c.
Definition FREE_SYM : Z := 0x156e0.
Definition MALLOC_STACK : Z := 8192.
Definition FREE_STACK : Z := 8192.

Definition MEDTAB : Z := 0x1a060.
Definition alloc_static (a : Z) : Prop :=
  (MLOCK <= a < MLOCK + 4) \/ (LIBC <= a < CTX + 928) \/ (ERRNO <= a < ERRNO + 4) \/ (MEDTAB <= a < MEDTAB + 4).
Definition medtab_cells : list cell := [C1 (Z_to_bv 8 28); C1 (Z_to_bv 8 24); C1 (Z_to_bv 8 20); C1 (Z_to_bv 8 32)].


Definition in_block (LB : list block) (a : Z) : Prop :=
  exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.

Definition client_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (0x19000 <= a < 0x1b000 /\ ~ alloc_static a) \/ in_block LB a.

Definition client_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
  SP <= A
  \/ (0x19000 <= A /\ A + n <= 0x1b000 /\ (A + n <= MLOCK \/ MLOCK + 4 <= A) /\ (A + n <= LIBC \/ CTX + 928 <= A)
      /\ (A + n <= ERRNO \/ ERRNO + 4 <= A) /\ (A + n <= MEDTAB \/ MEDTAB + 4 <= A))
  \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

Lemma client_range_addr : forall LB SP A n a,
  client_range LB SP A n -> A <= a < A + n -> client_addr LB SP a.
Proof.
  intros LB SP A n a HR Ha. unfold client_range, client_addr, alloc_static, MLOCK, LIBC, CTX, ERRNO, ATP, MEDTAB in *.
  destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists b; split; [exact Hb|lia]].
Qed.


Definition block_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= ATOP /\ (A + n <= 0x10000 \/ 0x1b000 <= A).




Definition client_write_ok (LB : list block) (iv : Z * Z) : Prop :=
  ATOP <= fst iv
  \/ (0x19000 <= fst iv /\ snd iv <= 0x1b000 /\ (snd iv <= MLOCK \/ MLOCK + 4 <= fst iv) /\ (snd iv <= LIBC \/ CTX + 928 <= fst iv)
      /\ (snd iv <= ERRNO \/ ERRNO + 4 <= fst iv) /\ (snd iv <= MEDTAB \/ MEDTAB + 4 <= fst iv))
  \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).


Definition bptr_eqb (p q : bptr) : bool :=
  aptr_eqb (fst p) (fst q) && Z.eqb (snd p) (snd q).
Definition lb_remove (p : bptr) (LB : list block) : list block :=
  filter (fun b => negb (bptr_eqb (blk_id b) p)) LB.






End CANSEC1.
End Malloc_iface.
