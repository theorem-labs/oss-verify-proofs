(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_loc_defs Pj_loc_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac takeZ H n A' nm :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let T := fresh "T" in
      assert (T : rw_cells segs m A (firstn n cs) /\ rw_cells segs m A' (skipn n cs))
        by (apply (rw_cells_split_n segs m A cs n A' H); cbv [firstn cells_size csize Nat.add]; lia);
      cbv [firstn skipn] in T; destruct T as [nm T]; clear H; rename T into H
  end.
Ltac glueZ H1 H2 :=
  lazymatch type of H1 with
  | rw_cells ?segs ?m ?A ?cs1 =>
      lazymatch type of H2 with
      | rw_cells _ _ ?A' ?cs2 =>
          let T := fresh "T" in
          assert (T : rw_cells segs m A (cs1 ++ cs2))
            by (apply (rw_cells_glue segs m A cs1 cs2 A' H1 H2); cbv [cells_size csize Nat.add]; lia);
          cbv [app] in T; clear H1 H2; rename T into H1
      end
  end.

Lemma bytes_eq_unsigned : forall l1 l2 : list byte, map (@bv_unsigned 8) l1 = map (@bv_unsigned 8) l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma rw_cells_retype_at : forall segs m A cs n1 n2 cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes (firstn n2 (skipn n1 cs)) ->
  cells_size cs' = cells_size (firstn n2 (skipn n1 cs)) ->
  rw_cells segs m A (firstn n1 cs ++ cs' ++ skipn n2 (skipn n1 cs)).
Proof.
  intros segs m A cs n1 n2 cs' H W EB ES.
  rewrite <- (firstn_skipn n1 cs) in H. rewrite <- (firstn_skipn n2 (skipn n1 cs)) in H.
  apply rw_cells_app in H. destruct H as [H1 H2]. apply rw_cells_app in H2. destruct H2 as [H2 H3].
  apply rw_cells_app. split; [exact H1|]. apply rw_cells_app. split.
  - eapply rw_cells_retype; eassumption.
  - rewrite ES. exact H3.
Qed.
Ltac retype_at H n1 n2 cs' :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let T := fresh "T" in
      assert (T : rw_cells segs m A (firstn n1 cs ++ cs' ++ skipn n2 (skipn n1 cs)))
        by (apply (rw_cells_retype_at segs m A cs n1 n2 cs' H);
            [ cbn [cells_wf cell_wf]; repeat split; try apply repeat_length; reflexivity
            | cbv [firstn skipn]; apply bytes_eq_unsigned; vm_compute; reflexivity
            | reflexivity ]);
      cbv [firstn skipn app] in T; clear H; rename T into H
  end.

Ltac forget_junk H :=
  repeat match type of H with
  | context [CB ?n ?x] => lazymatch x with firstn _ _ => idtac | skipn _ _ => idtac end;
      let j := fresh "jk" in set (j := x) in H; clearbody j
  end.

Lemma pj_locale_transport : forall W m m', pj_locale m -> munch W m m' -> wmono usegs m m' -> disjoint_from W 0xed228 3760 -> pj_locale m'.
Proof.
  intros W m m' [L0|(j1 & j2 & j3 & j4 & j5 & j6 & H)] MU WM D.
  - left. unfold LOC0 in *. apply (rw_cells_transport usegs W m m' _ _ L0 MU WM). rewrite loc0_cells_size. exact D.
  - right. exists j1, j2, j3, j4, j5, j6. apply (rw_cells_transport usegs W m m' _ _ H MU WM). rewrite locb_cells_size. exact D.
Qed.
