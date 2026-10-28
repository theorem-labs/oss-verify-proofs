(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_loc_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma rw_cells_retype : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[W B] WR] W' EB ES. unfold rw_cells, cells_at. rewrite EB, ES. auto.
Qed.

Lemma rw_cells_split_n : forall segs m A cs n A',
  rw_cells segs m A cs -> A' = (A + Z.of_nat (cells_size (firstn n cs)))%Z ->
  rw_cells segs m A (firstn n cs) /\ rw_cells segs m A' (skipn n cs).
Proof. intros segs m A cs n A' H ->. apply rw_cells_app. rewrite firstn_skipn. exact H. Qed.

Lemma rw_cells_glue : forall segs m A cs1 cs2 A',
  rw_cells segs m A cs1 -> rw_cells segs m A' cs2 -> A' = (A + Z.of_nat (cells_size cs1))%Z ->
  rw_cells segs m A (cs1 ++ cs2).
Proof. intros segs m A cs1 cs2 A' H1 H2 ->. apply rw_cells_app. split; assumption. Qed.

Lemma rw_cells_merge_n : forall segs m A cs n1 n2,
  rw_cells segs m A cs ->
  rw_cells segs m A (firstn n1 cs ++ CB (cells_size (firstn n2 (skipn n1 cs))) (cells_bytes (firstn n2 (skipn n1 cs))) :: skipn n2 (skipn n1 cs)).
Proof.
  intros segs m A cs n1 n2 H. apply rw_cells_merge.
  rewrite (firstn_skipn n2 (skipn n1 cs)), (firstn_skipn n1 cs). exact H.
Qed.

Ltac take H n A' nm :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let T := fresh "T" in
      pose proof (rw_cells_split_n segs m A cs n A' H eq_refl) as T;
      cbv [firstn skipn] in T; destruct T as [nm T]; clear H; rename T into H
  end.

Ltac glue H1 H2 :=
  lazymatch type of H1 with
  | rw_cells ?segs ?m ?A ?cs1 =>
      lazymatch type of H2 with
      | rw_cells _ _ ?A' ?cs2 =>
          let T := fresh "T" in
          pose proof (rw_cells_glue segs m A cs1 cs2 A' H1 H2 eq_refl) as T;
          cbv [app] in T; clear H1 H2; rename T into H1
      end
  end.

Ltac merge_at H n1 n2 :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let T := fresh "T" in
      pose proof (rw_cells_merge_n segs m A cs n1 n2 H) as T;
      cbv [firstn skipn app cells_size csize Nat.add] in T; clear H; rename T into H
  end.

Ltac retype H cs' :=
  apply (fun X => rw_cells_retype _ _ _ _ cs' X) in H;
  [ | cbn [cells_wf cell_wf]; repeat split; try apply repeat_length; reflexivity
    | vm_compute; reflexivity
    | reflexivity ].

Definition pj_keep (P : Prop) : Prop := P.
Ltac pj_hide H := lazymatch type of H with ?T => change (pj_keep T) in H end.
Ltac pj_unhide H := unfold pj_keep in H.
Ltac pj_carry H MUF WMF :=
  pj_unhide H;
  lazymatch type of MUF with
  | munch ?W ?m1 ?m2 =>
      lazymatch type of H with
      | rw_cells ?segs _ ?A ?cs =>
          let T := fresh "T" in
          assert (T : rw_cells segs m2 A cs)
            by (apply (rw_cells_transport segs W m1 m2 A cs H MUF WMF); cbv [disjoint_from fst snd cells_size csize Nat.add]; repeat split; lia);
          clear H; rename T into H
      end
  end.

Tactic Notation "callc" uconstr(SPEC) "clearing" tactic3(clr) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | clr; post_call segs m ]
  end.

Lemma pj_loc_kit_test : forall m, LOC0 m ->
  rw_cells usegs m 0xed228 [C8 (Z_to_bv 64 0); CB 8 (cells_bytes [C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]); CB 3744 (repeat (Z_to_bv 8 0) 3744)].
Proof.
  intros m H. unfold LOC0, loc0_cells in H.
  retype H [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); CB 3744 (repeat (Z_to_bv 8 0) 3744)].
  take H 1%nat 0xed230%Z H0.
  take H 2%nat 0xed238%Z H1.
  glue H1 H. glue H0 H1.
  merge_at H0 1%nat 2%nat.
  exact H0.
Qed.
