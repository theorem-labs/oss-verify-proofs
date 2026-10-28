(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg Nodes MmapSim.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require FileSim AgentLib ShapeLaws Spec LibWritev RefNodes U.S0ExitBase.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SimInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim.ExitSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim.AllocSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.FileSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeLaws OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.LibWritev OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefNodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ExitBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymExec3 SymExec3Sound SymPlan.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require MallocDefs U.S0EnframeBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymExec3 SymExec3Sound.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymPlan.
Module S0SymSlots.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MallocDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0EnframeBase.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec3Sound. (* [comment removed for export] *)       
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymPlan.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

Module SSL.
Import SX2. Import SX2S. Import SP.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition slot_ok (E : env) (M : word -> option byte) (s : sslot) : Prop :=
  let st := uE E (sl_start s) in let sd := uE E (sl_stride s) in let nn := uE E (sl_n s) in
  let o := uE E (sl_off s) in let W := uE E (sl_W s) in
  enframe_post M (sl_idx s) nn sd st o
  /\ uE E (sl_p s) = st + 16 * o
  /\ (let (hb, hk) := split_lit (sl_start s) in uE E hb + hk = st)
  /\ (let (pb, pk) := split_lit (sl_p s) in uE E pb + pk = st + 16 * o)
  /\ sd = slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W)
  /\ ((w_maplen W = 0 \/ w_lastidx W <> 0) -> w_sizeclass W < 48)
  /\ 16 <= sd < 2 ^ 31 /\ sd mod 16 = 0 /\ st mod 16 = 0
  /\ 16 + sd * sl_idx s <= st /\ st + sd < 2 ^ 64
  /\ 0 <= sl_idx s < 32 /\ sd * sl_idx s + 4096 <= 16 * 65536.

Definition slots_ok (E : env) (M : word -> option byte) (ss : list sslot) : Prop :=
  Forall (slot_ok E M) ss.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End SSL.
End S0SymSlots.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec3Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymPlan OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0SymPlanSoundA.S0SymSlots. (* [comment removed for export] *) From Stdlib Require Lia. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk SymExec. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymExec3 SymExec3Sound. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen. (* [comment removed for export] *) From Stdlib Require Lia. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg SymExec Frame RefMemcpyLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymExec3 SymExec3Sound. (* [comment removed for export] *) From Stdlib Require Lia. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk SymExec. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymExec3 SymExec3Sound. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Module SPSA.
Import SX2. Import SX2S. Import SP. Import SSL.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section NX0.
Variable nx0 : nat.
(* [comment removed for export] *)
Variable IT : itab.
Hypothesis IT_ok : itab_sound RSEGS IT.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fds_std : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
   (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

(* [comment removed for export] *)
Definition iv_disjoint (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
  \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).

Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (iv_disjoint p) l -> seps l -> seps (p :: l).

Definition smap_ok (E : env) (maps : list (word * word)) (m : smap) : Prop :=
  let a := bv_unsigned (edenot E (sm_base m)) in
  let L := bv_unsigned (edenot E (sm_len m)) in
  0 < L < 2 ^ 64 /\ a + L <= 2 ^ 64 /\
  if sm_exact m then In (edenot E (sm_base m), edenot E (sm_len m)) maps
  else exists lo sz, In (lo, sz) maps /\ bv_unsigned lo <= a /\ a + L <= bv_unsigned lo + bv_unsigned sz.

Record vm_ok (E : env) (ms : list smap) (nmaps live : Z) (VM : VmMaps) : Prop := VM_OK {
  vo_res   : vm_reserved VM = segments_reserved RSEGS;
  vo_maps  : Forall (smap_ok E (vm_maps VM)) ms;
  vo_len   : Z.of_nat (length (vm_maps VM)) <= nmaps;
  vo_live  : vm_live_bytes VM <= live;
  vo_small : Forall (fun p => 0 < bv_unsigned (snd p) <= 2 ^ 30) (vm_maps VM);
  vo_nw    : Forall (fun p => bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64) (vm_maps VM);
  vo_seps  : seps (vm_maps VM);
  vo_limit : 2 ^ 34 <= vm_limit VM
}.

Record cs_ok (E : env) (cs : cstate) (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop := CS_OK {
  co_regs : regs_ok E (s_regs (c_ss cs)) R;
  co_know : know_ok RSEGS E M (s_know (c_ss cs));
  co_log  : s_log (c_ss cs) = [];
  co_halt : m_halted model = None;
  co_lazy : m_vm_lazy model = [];
  co_mat  : m_vm_materialized model = [];
  co_fds  : m_fds model = fds_std;
  co_vm   : vm_ok E (c_maps cs) (c_nmaps cs) (c_live cs) (m_vmmaps model);
  co_slots : slots_ok E M (c_slots cs)                       (* [comment removed for export] *)
}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Record std_model (VM : VmMaps) (model : Model) : Prop := STD_MODEL {
  stdm_fds  : m_fds model = fds_std;
  stdm_vm   : m_vmmaps model = VM;
  stdm_halt : m_halted model = None;
  stdm_lazy : m_vm_lazy model = [];
  stdm_mat  : m_vm_materialized model = []
}.

Lemma std_model_mk : forall VM stdin0 fs0 tid rlim,
  std_model VM (mkModelA fds_std VM stdin0 fs0 None tid rlim).
Proof. intros. constructor; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


End NX0.
End SPSA.
