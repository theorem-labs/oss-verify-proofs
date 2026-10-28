(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
Module F_malloc_enf.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)

Lemma surj_pair_let {A B C'} (e : A * B) (f : A -> B -> C') : (let '(x, y) := e in f x y) = f (fst e) (snd e).
Proof. destruct e; reflexivity. Qed.

(* [comment removed for export] *)

End ACeilS1.
End F_malloc_enf.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require AllocSlot_iface Malloc_iface.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join.F_malloc_enf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.AllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_iface.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma unk_agree_ext st st' o m :
  unk_agree st o m -> s_regions st' = s_regions st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
  s_groups st' = s_groups st -> unk_agree st' o m.
Proof.
  intros UA ER ES EG rid r off h Hr Hk Ho Hc NG. rewrite ER in Hr. rewrite ES in Hc.
  apply (UA rid r off h Hr Hk Ho Hc). cps_intros (b & gh & Hb & Hf & Hx). apply NG. exists b, gh. rewrite EG. auto.
Qed.

Lemma unk_agree_munch st o m m' W :
  unk_agree st o m -> munch W m m' ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> disjoint_from W (r_base r) (round_up_pg (r_len r))) ->
  (forall rid r, (s_regions st) !! rid = Some r -> 0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= 2^64) ->
  unk_agree st o m'.
Proof.
  intros UA MU HD HB rid r off h Hr Hk Ho Hc NG.
  rewrite <- (UA rid r off h Hr Hk Ho Hc NG). apply MU.
  destruct (HB rid r Hr) as [B0 B1]. rewrite wa_unsigned by lia.
  eapply disjoint_outside; [apply (HD rid r Hr Hk)| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition enf_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
  forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (junk : list byte) (s' : PState) (errv : word)
         (t0 t1 t2 a0 a1 a3 a5 a7 t3 t4 t5 t6 : word),
    mrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv asegs m1 ->
    stk asegs m1 lo (bv_unsigned sp + -64) ->
    rw_cells asegs m1 (bv_unsigned sp + -64)
       [C8 (wz idx); C8 (pw st2 (Some g)); C8 (wz (sxv (c_mmap_counter (ctx st2)))); C8 (wz idx); CB 16 junk; C8 s0v; C8 ra] ->
    rw_cells asegs m1 (errno_addr tp) [C4 errv] -> auxv_ok m1 (bv_unsigned sp) ->
    pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                 < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
       malloc_fp st st2 lo (bv_unsigned sp) a) ->
    0 <= c_mmap_counter (ctx st2) < 2^32 ->
    slot_ok st2 g b r idx n ->
    (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    implT o (K st2 (Some (g, idx))) s' Q
          (MS (mkR (Z_to_bv 64 0x17008) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz n) s1
                   a0 a1 (wz idx) a3 (wz (sxv (c_mmap_counter (ctx st2)))) a5 (pw st2 (Some g)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17014) fc None m1 (seg_rom asegs)).

Lemma mrel_same st st' :
  s_regions st' = s_regions st -> s_next_rid st' = s_next_rid st -> s_reserved st' = s_reserved st -> mrel st st'.
Proof.
  intros ER EN ES. split; [| rewrite EN; lia | exact ES].
  intros rid r H. exists r. rewrite ER. repeat split; auto. lia.
Qed.

Section FASTCORE.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Hypothesis HENF : enf_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc n lo.
Hypothesis MF : MFACTS st LB.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64.
Hypothesis N0 : 0 <= n.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

(* [comment removed for export] *)
End FASTCORE.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fail_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
  forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mrep st2 m1 -> ticks_ok st2 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp) ->
    rw_cells asegs m1 (errno_addr tp) [C4 errv] -> auxv_ok m1 (bv_unsigned sp) ->
    pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    implT o (K st2 None) s' Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0v s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section ASCALL.
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
End ASCALL.

End ACeilS1.
