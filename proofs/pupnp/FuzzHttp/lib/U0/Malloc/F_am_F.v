(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_syscalls F_mm_syscalls MallocRep F_malloc_free MallocTree.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_am_A F_am_K F_am_C.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.

Lemma carve_st_regions st p : s_regions (carve_st st p) = s_regions st.
Proof.
  unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
  destruct (c_meta_area_tail (s_ctx st)); reflexivity.
Qed.

Definition mp_strict (a : range_ans) : Prop := match a with RgErr e => e <> 38 | RgDone b => b = true end.
Lemma dec_mprotect_rw_weaken A L rsp a : dec_mprotect_rw A L rsp = Some a -> dec_mprotect A L rsp = Some a /\ mp_strict a.
Proof.
  unfold dec_mprotect_rw. destruct (dec_mprotect A L rsp) as [[e|b]|]; [| | discriminate].
  - destruct (Z.eqb_spec e ENOSYS); [discriminate|]. intros H; inversion H; subst. split; [reflexivity|]. cbn. unfold ENOSYS in *. exact n.
  - destruct b; [| discriminate]. intros H; inversion H; subst. split; reflexivity.
Qed.