(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import Malloc_fp.
Import ListNotations.
Open Scope Z_scope.

Definition enf_off0 (o : mem) (st1 : mstate) (b : aptr) (stride idx : Z) : Z :=
  let q := snd b + (16 + stride * idx) in
  if rdv pans_mem o st1 (fst b, q + -3) =? 0 then Z.land (c_mmap_counter (ctx st1)) 255
  else Z.land (rdv pans_mem o st1 (fst b, q + -2) + 256 * rdv pans_mem o st1 (fst b, q + -2 + 1) + 1) 255.

Definition enf_leaf (o : mem) (st1 : mstate) (g b : aptr) (idx n : Z) (st' : mstate) (p : aptr) : Prop :=
  exists off, 0 <= off /\ 16 * off + n + 4 <= get_stride (get_meta_rec st1 g)
    /\ p = (fst b, snd b + 16 + get_stride (get_meta_rec st1 g) * idx + 16 * off)
    /\ st' = havoc p n (fst (enframe_at st1 g idx n off))
    /\ p = snd (enframe_at st1 g idx n off)
    /\ off = fold_off (enf_off0 o st1 b (get_stride (get_meta_rec st1 g)) idx) ((get_stride (get_meta_rec st1 g) - 4 - n) / 16).

Lemma surj_pair_let {A B C'} (e : A * B) (f : A -> B -> C') : (let '(x, y) := e in f x y) = f (fst e) (snd e).
Proof. destruct e; reflexivity. Qed.