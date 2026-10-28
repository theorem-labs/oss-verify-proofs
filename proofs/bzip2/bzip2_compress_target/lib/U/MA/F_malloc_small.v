(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_malloc_join.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require AllocSlot_iface Malloc_iface F_malloc_join.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join.F_malloc_enf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.AllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.

(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition coarse_sc (st : mstate) (sc : Z) : Z :=
  match active st sc with
  | Some _ => sc
  | None =>
    if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) then
      let usage1 := usage st (Z.lor sc 1) in
      let usage1 := match active st (Z.lor sc 1) with
                    | None => usage1 + 3
                    | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
                                if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                    end in
      if usage1 <=? 12 then Z.lor sc 1 else sc
    else sc
  end.

Lemma malloc_small_ctrl_eq {R} lay st n (k : mstate -> option (aptr * Z) -> Malloc.M R) bail :
  malloc_small_ctrl lay st n k bail =
  let sc := coarse_sc st (size_to_class n) in
  let g := active st sc in
  let mask := match g with Some gp => m_avail (get_meta_rec st gp) | None => 0 end in
  let first := lowbit mask in
  match g, negb (first =? 0) with
  | Some gp, true => k (upd_meta gp (m_set_avail (mask - first)) st) (Some (gp, ctz32 first))
  | _, _ =>
    alloc_slot lay FUEL st sc n (fun st1 idx =>
      if idx <? 0 then k st1 None
      else match active st1 sc with
           | Some gp => k st1 (Some (gp, idx))
           | None => SVis (EUndef UBadPtr) (fun _ => bail)
           end) bail
  end.
Proof. reflexivity. Qed.

Lemma usages_length : forall st, length (usages st) = 48%nat.
Proof. intros. unfold usages. rewrite length_map, length_seq. reflexivity. Qed.
Lemma usages_nth : forall st sc, 0 <= sc < 48 -> nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
  intros st sc Hsc. unfold usages. rewrite nth_error_map, nth_error_seq.
  replace (Z.to_nat sc <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma land_ones64 y : Z.land y 18446744073709551615 = y mod 2^64.
Proof. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones. lia. Qed.

Lemma land_1_even x : (Z.land x 1 = 0) <-> Z.even x = true.
Proof.
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2^1) with 2.
  rewrite Z.even_spec. split.
  - intros H. exists (x / 2). lia.
  - intros [k ->]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

Section COARSE.
Variables (st : mstate) (LB : list block) (m1 : mem) (t : N).
Let st1 := set_tick t st.
Hypothesis MF : MFACTS st LB.
Hypothesis MR : mrep st1 m1.
Hypothesis MI : mem_inv asegs m1.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End COARSE.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lor1_check : bool :=
  forallb (fun sc => negb ((4 <=? sc) && (sc <? 32) && Z.even sc) || (size_class sc <=? size_class (Z.lor sc 1))) (zseq 0 48).
Lemma lor1_check_true : lor1_check = true.
Proof. vm_compute. reflexivity. Qed.

Lemma size_class_lor1 sc : 4 <= sc < 32 -> Z.even sc = true -> size_class sc <= size_class (Z.lor sc 1).
Proof.
  intros H E. pose proof (forallb_zseq _ 0 48 sc lor1_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  replace (4 <=? sc) with true in X by (symmetry; apply Z.leb_le; lia).
  replace (sc <? 32) with true in X by (symmetry; apply Z.ltb_lt; lia). rewrite E in X. cbn [andb negb orb] in X.
  apply Z.leb_le. exact X.
Qed.

Definition lor1_range_check : bool := forallb (fun sc => (0 <=? Z.lor sc 1) && (Z.lor sc 1 <? 48)) (zseq 0 48).
Lemma lor1_range_check_true : lor1_range_check = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lor1_range sc : 0 <= sc < 48 -> 0 <= Z.lor sc 1 < 48.
Proof.
  intros H. pose proof (forallb_zseq _ 0 48 sc lor1_range_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  apply andb_prop in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
Qed.

Lemma coarse_sc_cases st sc : 0 <= sc < 48 ->
  coarse_sc st sc = sc \/ (coarse_sc st sc = Z.lor sc 1 /\ 4 <= sc < 32 /\ Z.even sc = true).
Proof.
  intros H. unfold coarse_sc. destruct (active st sc); [left; reflexivity|].
  destruct ((4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0)) eqn:E; [|left; reflexivity].
  apply andb_prop in E. destruct E as [E E5]. apply andb_prop in E. destruct E as [E E4].
  apply andb_prop in E. destruct E as [E E3]. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  cbv zeta. destruct (_ <=? 12); [right|left]; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section SMALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis AS : alloc_slot_stmt as_pre as_inv.
Hypothesis HENF : enf_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc n lo.
Hypothesis HFAIL : fail_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc lo.
Hypothesis MF : MFACTS st LB.
Hypothesis MR0 : mrep st m0.
Hypothesis MED0 : rw_cells asegs m0 MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64 - AS_STACK FUEL.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

(* [comment removed for export] *)
End SMALL.

End ACeilS1.
