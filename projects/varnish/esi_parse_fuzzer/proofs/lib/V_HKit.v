(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_peel : forall segs m A c cs,
  rw_cells segs m A (c :: cs) -> rw_cells segs m A [c] /\ rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros segs m A c cs H. change (c :: cs) with ([c] ++ cs) in H.
  apply (proj1 (rw_cells_app segs m A [c] cs)) in H. cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma rw_cells_head_split : forall segs m A n junk post sizes,
  rw_cells segs m A (CB n junk :: post) -> sum_nat sizes = n ->
  rw_cells segs m A (mk_CB_cells sizes junk ++ post).
Proof. intros. apply (rw_cells_split_CB segs m A [] n junk post sizes); assumption. Qed.

(* [comment removed for export] *)
Ltac is_natlit n := lazymatch n with O => idtac | S ?k => is_natlit k end.
Ltac fold_of_nat_in H :=
  repeat match type of H with
  | context [Z.of_nat ?n] => is_natlit n; let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in H
  end.

Ltac is_zlit z := lazymatch z with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
(* [comment removed for export] *)
Ltac fold_to_nat_in H :=
  repeat match type of H with
  | context [Z.to_nat ?z] => is_zlit z; let v := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with v in H
  | context [Z.modulo ?a ?b] => is_zlit a; is_zlit b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v in H
  end.

(* [comment removed for export] *)
Ltac norm_base H :=
  repeat match type of H with
  | rw_cells _ _ (?b + ?x + ?y) _ =>
      lazymatch x with Zpos _ => idtac | Zneg _ => idtac | Z0 => idtac end;
      lazymatch y with Zpos _ => idtac | Zneg _ => idtac | Z0 => idtac end;
      let s := eval vm_compute in (x + y)%Z in
      replace (b + x + y)%Z with (b + s)%Z in H by lia
  end.

(* [comment removed for export] *)
Ltac peel FR N :=
  lazymatch type of FR with
  | rw_cells ?segs ?m ?A (?c :: ?cs) =>
      let X := fresh in
      pose proof (rw_cells_peel segs m A c cs FR) as X; clear FR;
      destruct X as [N FR]; cbn [csize] in FR; fold_of_nat_in FR; norm_base FR;
      (* [comment removed for export] *)
      try (lazymatch type of N with rw_cells _ _ _ [CB _ ?bs] =>
             lazymatch bs with
             | firstn _ _ => let j := fresh "junk" in set (j := bs) in N; clearbody j
             | skipn _ _ => let j := fresh "junk" in set (j := bs) in N; clearbody j
             end end)
  end.

(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_World.

(* [comment removed for export] *)
Ltac hnorm_consts_in H := idtac.

Ltac hnorm_in H :=
  unfold h_ws, h_wsbuf, h_hd, h_vsbloc, h_wrk, h_vc, h_resp, h_req, h_cp, h_vsc in H; cbn [h_sp h_bss] in H;
  hnorm_consts_in H;
  repeat (rewrite unsigned_lit in H by lia).

Ltac post_call_h segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  hnorm_in MUc;
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Tactic Notation "callh" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_call_h segs m ]
  end.

(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_AKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec.
Lemma cframe_absorb_window : forall L (o o' : Z -> Prop) sp win (V V' N : Z -> Prop) m m',
  cframe L o o' sp win V N m m' -> (forall a, V a -> V' a \/ (sp - win <= a < sp)%Z) ->
  cframe L o o' sp win V' N m m'.
Proof.
  intros L o o' sp win V V' N m m' (C1 & C2 & C3) HV. split; [|split; [exact C2|]].
  - intros a Ha NO VIS NW NE NV. apply C1; try assumption. intros X. destruct (HV a X); tauto.
  - intros a Ha NW NE NB. destruct (C3 a Ha NW NE NB) as [X|[X|X]]; [left; exact X| |right; right; exact X].
    destruct (HV a X) as [Y|Y]; [right; left; exact Y| exfalso; exact (NW Y)].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_C8_CB : forall segs m a (w : word), rw_cells segs m a [C8 w] -> rw_cells segs m a [CB 8 (le8 w)].
Proof.
  intros segs m a w H. eapply rw_cells_recast; [exact H| cbn [cells_wf cell_wf]; split; [apply length_le8| exact I] | reflexivity].
Qed.
