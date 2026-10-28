(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Export U0Traps.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.

Definition frdW (segs : list Segment) (W : list ivl) (m0 : word -> option byte) (A : Z) (cs : list cell) : Prop :=
  forall m : word -> option byte, munch W m0 m -> ro_cells segs m A cs.

Lemma frdW_intro : forall segs W (m0 : word -> option byte) A cs,
  rw_cells segs m0 A cs -> disjoint_from W A (Z.of_nat (cells_size cs)) -> frdW segs W m0 A cs.
Proof. intros segs W m0 A cs [H _] D m MU. exact (ro_cells_transport segs W m0 m A cs H MU D). Qed.

Lemma frdW_sub : forall segs W W' (m0 m1 : word -> option byte) A cs,
  frdW segs W m0 A cs -> munch W m0 m1 -> sub_fp W' W -> frdW segs W' m1 A cs.
Proof.
  intros segs W W' m0 m1 A cs H MU SF m MU'. apply H.
  apply (munch_trans W m0 m1 m MU). exact (munch_weaken W' W m1 m SF MU').
Qed.

Lemma frdW_cell : forall segs W (m0 : word -> option byte) A cs k c,
  frdW segs W m0 A cs -> cell_at cs k = Some c -> frdW segs W m0 (A + Z.of_nat k) [c].
Proof.
  intros segs W m0 A cs k c H Hc m MU. specialize (H m MU). destruct H as [Hwf Hb].
  destruct (cell_at_split _ _ _ c Hc) as (pre & post & Ecs & Hsz & _).
  rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre [Hwc Hwpost]].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by assumption. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. destruct Hb as [Hb _].
  split; [cbn; tauto|]. cbn [cells_bytes]. rewrite app_nil_r. exact Hb.
Qed.

Lemma frdW_cell_at : forall segs W (m0 : word -> option byte) A cs k c A',
  frdW segs W m0 A cs -> cell_at cs k = Some c -> A' = A + Z.of_nat k -> frdW segs W m0 A' [c].
Proof. intros segs W m0 A cs k c A' H Hc ->. exact (frdW_cell segs W m0 A cs k c H Hc). Qed.

Ltac u_sub_fp :=
  unfold sub_fp; cbn [outside]; let x := fresh "x" in let Ho := fresh "Ho" in intros x Ho; repeat split; lia.

Ltac u_lit_branch :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      let c' := eval vm_compute in c in
      lazymatch c' with
      | true => change c with true; cbv iota
      | false => change c with false; cbv iota
      end
  end.

Ltac u_closed_cond c :=
  lazymatch c with
  | negb ?c1 => u_closed_cond c1
  | bv_eqb (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  | bv_ltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  | bv_lts (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  end.
Ltac u_try_lit_branch :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => first [ u_closed_cond c; u_lit_branch | idtac ]
  | _ => idtac
  end.

Ltac u_at_pc p :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq p q
  end.
Ltac u_pc_is_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => is_Zlit q
  end.

Ltac u_norm := idtac.
Ltac u_zstep_nofb := ltac2:(Control.enter (fun () => Control.once (fun () => StepFast.sf_step true))).

Ltac u_astep := wstep; u_norm; u_try_lit_branch.
Ltac u_arun_to p :=
  first [ u_at_pc p
        | u_pc_is_lit; u_astep; u_arun_to p
        | fail 1 "u_arun_to: stopped at an open branch / non-literal pc before reaching" p ].
Ltac u_astep_nf := u_zstep_nofb; bz32; u_norm; u_try_lit_branch.
Ltac u_arun :=
  first [ u_pc_is_lit; u_astep_nf; u_arun
        | lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "u_arun: stopped at" pc end ].

Ltac u_trapb p := let b := eval vm_compute in (u0_trapb p) in b.

Ltac u_guard :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
      let ta := u_trapb a in
      lazymatch ta with
      | true => if_false_z
      | false =>
          let tb := u_trapb b in
          lazymatch tb with
          | true => if_true_z
          | false => fail "u_guard: neither arm is a trap pc"
          end
      end
  end.
Ltac u_is_guard :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
      let ta := u_trapb a in
      lazymatch ta with
      | true => idtac
      | false => let tb := u_trapb b in lazymatch tb with true => idtac end
      end
  end.
Ltac u_try_guard := tryif u_is_guard then first [ u_guard | idtac "urun: unproved check branch (missing bound?)" ] else idtac.

Ltac u_new_flag R :=
  lazymatch goal with
  | |- evt _ _ (MS ?R' _ _ _ _ _ _) =>
      match R' with
      | context [Z.b2z ?t] => lazymatch R with context [Z.b2z t] => fail | _ => idtac end
      end
  end.
Ltac u_has_flag :=
  lazymatch goal with |- evt _ _ (MS ?R' _ _ _ _ _ _) => lazymatch R' with context [Z.b2z (_ _ _)] => idtac end end.
Ltac u_flags R := tryif u_new_flag R then (flags; tryif u_has_flag then try flagsb else idtac) else idtac.

Ltac u_regs := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => R end.
Ltac ustep := let R := u_regs in wstep; u_norm; u_flags R; u_try_lit_branch; u_try_guard.
Ltac ustep_nf := let R := u_regs in u_zstep_nofb; bz32; u_norm; u_flags R; u_try_lit_branch; u_try_guard.
Ltac urun_to p :=
  first [ u_at_pc p
        | u_pc_is_lit; ustep; urun_to p
        | fail 1 "urun_to: stopped at an open branch / unproved check branch / non-literal pc before reaching" p ].
Ltac urun :=
  first [ u_pc_is_lit; ustep_nf; urun
        | lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "urun: stopped at" pc end ].
