(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Spec Require Import StrFun.

Module AIcpmc7.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Tac Bytes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition frozen (P : Prop) : Prop := P.

Ltac freeze H := lazymatch type of H with ?T => change T with (frozen T) in H end.

Ltac thaw H MU WM :=
  unfold frozen in H;
  lazymatch type of MU with munch ?W ?m ?m' =>
  lazymatch type of H with
  | rw_cells ?segs m ?A ?cs =>
      apply (rw_cells_transport segs W m m' A cs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia ]
  | ro_cells ?segs m ?A ?cs =>
      apply (ro_cells_transport segs W m m' A cs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; lia ]
  | bytes_at ?segs m ?A ?bs =>
      apply (bytes_at_transport segs W m m' A bs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; lia ]
  | u8arr ?segs m ?A ?xs =>
      apply (u8arr_transport segs W m m' A xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; lia ]
  end end.
End AIcpmc7.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.

Ltac post_call_lit segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  (let T := type of PO in let h := head_of T in try unfold h in PO);
  rewrite ?unsigned_lit in PO by lia;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
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

Tactic Notation "call_lit" uconstr(SPEC) "by" tactic3(side) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC; side | post_call_lit segs m ]
  end.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

Lemma le1_lit : forall z, (0 <= z < 256)%Z -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z Hz. rewrite le1_byte. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma cl_le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma cl_le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
(* [comment removed for export] *)
Ltac fix_bstore :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (cl_le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (cl_le4_lit z) by lia
  | _ => idtac
  end.
Ltac zs := zstep; try (fix_bstore; mem_after_store_opt).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma evt_if_true : forall segs Q R F (c : bool) a b fc rv m ro,
  c = true -> evt segs Q (MS R F a fc rv m ro) -> evt segs Q (MS R F (if c then a else b) fc rv m ro).
Proof. intros segs Q R F c a b fc rv m ro -> H. exact H. Qed.
Lemma evt_if_false : forall segs Q R F (c : bool) a b fc rv m ro,
  c = false -> evt segs Q (MS R F b fc rv m ro) -> evt segs Q (MS R F (if c then a else b) fc rv m ro).
Proof. intros segs Q R F c a b fc rv m ro -> H. exact H. Qed.
Ltac if_dir lem tac :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => apply (lem segs Q R F c a b fc rv m ro); [ tac | ]
  end.
Ltac solve_cond_closed := unfold_cond; fold_lit_ux; reflexivity.
Ltac if_lit_try :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      (* [comment removed for export] *)
      first [ if_dir evt_if_false ltac:(solve_cond_closed) | if_dir evt_if_true ltac:(solve_cond_closed)
            | if_false | if_true ]
  end.
(* [comment removed for export] *)
Ltac sub_norm :=
  repeat match goal with
  | |- context [(?x + ?a - (?x + ?b))%Z] => let v := eval vm_compute in (a - b)%Z in replace (x + a - (x + b))%Z with v in * by lia
  | |- context [(?x + ?a - ?x)%Z] => replace (x + a - x)%Z with a in * by lia
  | |- context [(?x - (?x + ?b))%Z] => let v := eval vm_compute in (- b)%Z in replace (x - (x + b))%Z with v in * by lia
  | |- context [(?x - ?x)%Z] => replace (x - x)%Z with 0%Z in * by lia
  end.
Ltac zgo_step := first [ if_lit_try
                       | progress sub_norm; if_lit_try
                       | lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end ].
Ltac zgo n := lazymatch n with O => idtac | S ?k => tryif zgo_step then zgo k else idtac end.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac zto p := repeat (tryif at_pc p then fail else zgo_step).
