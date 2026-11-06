(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition same_except (ks : list nat) (l l' : regfile) : Prop :=
  forall k, ~ In k ks -> rget l' k = rget l k.

Lemma same_except_refl : forall ks l, same_except ks l l.
Proof. intros ks l k _. reflexivity. Qed.

Lemma same_except_trans : forall ks l1 l2 l3,
  same_except ks l1 l2 -> same_except ks l2 l3 -> same_except ks l1 l3.
Proof. intros ks l1 l2 l3 H1 H2 k Hk. rewrite (H2 k Hk). apply H1, Hk. Qed.

Lemma same_except_weaken : forall ks ks' l l',
  same_except ks l l' -> (forall k, In k ks -> In k ks') -> same_except ks' l l'.
Proof. intros ks ks' l l' H Hs k Hk. apply H. intros Hin. apply Hk, Hs, Hin. Qed.

Lemma rget_beyond : forall l k, (length l <= k)%nat -> rget l k = Z_to_bv 64 0.
Proof.
  intros l k H. destruct k as [|k]; [reflexivity|]. cbn [rget].
  revert k H. induction l as [|x l IH]; intros k H; [destruct k; reflexivity|].
  cbn [length] in H. cbn [lget]. destruct l as [|y l'].
  - destruct k; reflexivity.
  - destruct k as [|k]; [cbn [length] in H; lia|]. apply IH. cbn [length] in *. lia.
Qed.

Lemma length32_inv : forall l : regfile, length l = 32%nat ->
  exists x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    l = [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20; x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31].
Proof.
  intros l H.
  do 32 (destruct l as [|? l]; [discriminate H|]). destruct l; [|discriminate H].
  repeat eexists.
Qed.

(* [comment removed for export] *)
Ltac regs_open l H :=
  let x0 := fresh "x0" in let x1 := fresh "ra" in let x2 := fresh "sp" in let x3 := fresh "gp" in
  let x4 := fresh "tp" in let x5 := fresh "t0" in let x6 := fresh "t1" in let x7 := fresh "t2" in
  let x8 := fresh "s0" in let x9 := fresh "s1" in let x10 := fresh "a0" in let x11 := fresh "a1" in
  let x12 := fresh "a2" in let x13 := fresh "a3" in let x14 := fresh "a4" in let x15 := fresh "a5" in
  let x16 := fresh "a6" in let x17 := fresh "a7" in let x18 := fresh "s2" in let x19 := fresh "s3" in
  let x20 := fresh "s4" in let x21 := fresh "s5" in let x22 := fresh "s6" in let x23 := fresh "s7" in
  let x24 := fresh "s8" in let x25 := fresh "s9" in let x26 := fresh "s10" in let x27 := fresh "s11" in
  let x28 := fresh "t3" in let x29 := fresh "t4" in let x30 := fresh "t5" in let x31 := fresh "t6" in
  let E := fresh "El" in
  destruct (length32_inv l H) as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15
    & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & E);
  subst l; clear H; cbn [rget lget] in *.

(* [comment removed for export] *)
Ltac same_ex :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk;
  do 32 (destruct k as [|k]; [first [reflexivity | exfalso; apply Hk; cbv; repeat (first [left; reflexivity | right]); fail]|]);
  rewrite !rget_beyond by (cbn [length]; lia); reflexivity.

Ltac wp_simpl_goal :=
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hide_gets :=
  repeat match goal with
         | |- context [lget ?l ?k] => is_var l; let v := fresh "rv" in set (v := lget l k) in *
         | |- context [rget ?l ?k] => is_var l; let v := fresh "rv" in set (v := rget l k) in *
         end.
Ltac unhide_gets :=
  repeat match goal with
         | v := lget _ _ |- _ => subst v
         | v := rget _ _ |- _ => subst v
         end.

Ltac wp_go base n Ceq C stops :=
  hide_gets;
  lazymatch goal with
  | |- reach ?S ?rom (Z_to_bv 64 ?pc) ?l ?M ?Post =>
      let idx := eval vm_compute in (Z.to_nat ((pc - base) / 4)) in
      change (Z_to_bv 64 pc) with (Z_to_bv 64 (base + 4 * Z.of_nat idx)) at 1;
      apply (wp_sound S rom base n stops Post 400 true);
      rewrite Ceq;
      cbv beta iota zeta delta [wp cnth C in_stops pc_eqb rget lget rset lset vaddr val_imm val_sh val_op
                                val_shw val_opw val_mul val_mulw br_yes br_no szn ext_load];
      wp_simpl_goal
  end;
  unhide_gets.

(* [comment removed for export] *)
Lemma same_except_getr : forall ks regs regs' l',
  rrel regs' l' -> same_except ks (lof regs) l' ->
  forall r : reg, ~ In (ridx r) ks -> getr regs' r = getr regs r.
Proof.
  intros ks regs regs' l' HR Hse r Hr.
  rewrite (proj2 HR r), (Hse _ Hr). symmetry. apply (proj2 (rrel_lof regs) r).
Qed.

(* [comment removed for export] *)
Lemma same_except_fix : forall ks ks' l0 old new,
  same_except ks' l0 old ->
  (forall k, ~ In k ks' -> rget new k = rget old k) ->
  (forall k, ~ In k ks -> In k ks' -> rget new k = rget l0 k) ->
  same_except ks l0 new.
Proof.
  intros ks ks' l0 old new H1 H2 H3 k Hk.
  destruct (in_dec Nat.eq_dec k ks') as [Hin|Hnin]; [apply H3; assumption|].
  rewrite (H2 k Hnin). apply H1, Hnin.
Qed.

(* [comment removed for export] *)
Ltac same_fix Hse :=
  eapply same_except_fix; [exact Hse | same_ex |];
  let k := fresh "k" in let Hk := fresh "Hk" in let Hin := fresh "Hin" in
  intros k Hk Hin; cbv in Hin;
  repeat (destruct Hin as [Hin|Hin];
          [ subst k; first [ exfalso; apply Hk; cbv; repeat (first [left; reflexivity | right]); fail
                           | cbn [rget lget]; try reflexivity ] | ]);
  try contradiction.

(* [comment removed for export] *)
Lemma same_except_call : forall ks ks' l_orig l_call l',
  same_except ks' l_orig l_call -> same_except ks l_call l' -> (forall j, In j ks -> In j ks') ->
  same_except ks' l_orig l'.
Proof.
  intros ks ks' lo lc l' H1 H2 Hs. eapply same_except_trans; [exact H1|].
  eapply same_except_weaken; [exact H2 | exact Hs].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac solve_grows :=
  first [ eassumption | apply mem_grows_refl
        | eapply mem_grows_trans; [|apply wbytes_grows]; solve_grows ].

(* [comment removed for export] *)
Ltac solve_unch tac :=
  first [ eassumption | apply unch_refl
        | apply unch_store; [ solve_unch tac | tac | rewrite ?length_N_to_le_bytes; tac
                            | let x := fresh "x" in let Hx := fresh "Hx" in
                              intros x Hx; rewrite ?length_N_to_le_bytes in Hx; unfold inr in *; tac ] ].

