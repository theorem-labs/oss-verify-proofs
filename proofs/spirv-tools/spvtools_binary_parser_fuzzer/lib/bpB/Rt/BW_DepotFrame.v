(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BZBridge BellsX BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsDepotInv.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition avoids (W : list ivl) (a b : Z) : Prop := Forall (fun iv => snd iv <= a \/ b <= fst iv) W.

Lemma avoids_disjoint : forall W a b A n, avoids W a b -> a <= A -> A + n <= b -> disjoint_from W A n.
Proof.
  intros W a b A n AV HA HB. induction W as [|[l h] W IH]; [exact I|].
  apply Forall_cons_iff in AV. destruct AV as [H1 H2]. cbn in H1. split; [lia| apply IH; exact H2].
Qed.

Definition depot_avoid (W : list ivl) (d : depot) : Prop :=
  avoids W 2567960 (6762280 + 8) /\ avoids W 2502408 (2502408 + 28)
  /\ avoids W (d_nb d) (d_nb d + 16 * 65536) /\ avoids W (d_sb d) (d_sb d + 8 * 32768).

Lemma depot_mem_transport : forall segs d m m' W,
  d_wf d -> depot_mem segs d m -> munch W m m' -> wmono segs m m' -> depot_avoid W d -> depot_mem segs d m'.
Proof.
  intros segs d m m' W WF DM MU WM (A1 & A2 & A3 & A4).
  pose proof (wf_ids d WF) as I1. pose proof (wf_frames d WF) as I2. pose proof (wf_nb d WF) as I3. pose proof (wf_sb d WF) as I4.
  destruct DM as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10].
  constructor.
  - intros b Hb. eapply rw_cells_transport; [apply T1; exact Hb|exact MU|exact WM|]. eapply avoids_disjoint; [exact A1| cbn; lia| cbn; lia].
  - eapply rw_cells_transport; [exact T2|exact MU|exact WM|]. eapply avoids_disjoint; [exact A1| cbn; lia| cbn; lia].
  - eapply rw_cells_transport; [exact T3|exact MU|exact WM|]. eapply avoids_disjoint; [exact A1| cbn; lia| cbn; lia].
  - intros id Hid. eapply rw_cells_transport; [apply T4; exact Hid|exact MU|exact WM|]. eapply avoids_disjoint; [exact A3| cbn; lia| cbn; lia].
  - intros id Hid. destruct (T5 id Hid) as [sid H]. exists sid. eapply rw_cells_transport; [exact H|exact MU|exact WM|].
    eapply avoids_disjoint; [exact A3| cbn; lia| cbn; lia].
  - intros id Hid. destruct (T6 id Hid) as (j1 & j2 & j3 & H). exists j1, j2, j3. eapply rw_cells_transport; [exact H|exact MU|exact WM|].
    eapply avoids_disjoint; [exact A3| cbn; lia| cbn; lia].
  - eapply rw_cells_transport; [exact T7|exact MU|exact WM|]. eapply avoids_disjoint; [exact A2| cbn; lia| cbn; lia].
  - eapply rw_cells_transport; [exact T8|exact MU|exact WM|]. eapply avoids_disjoint; [exact A2| cbn; lia| cbn; lia].
  - eapply rw_cells_transport; [exact T9|exact MU|exact WM|]. eapply avoids_disjoint; [exact A2| cbn; lia| cbn; lia].
  - destruct T10 as (junk & U & L). exists junk. split; [|exact L]. eapply u8arr_transport; [exact U|exact MU|exact WM|].
    eapply avoids_disjoint; [exact A4| lia| lia].
Qed.

Lemma DEPOT_transport : forall segs d m m' W,
  DEPOT segs d m -> munch W m m' -> wmono segs m m' -> depot_avoid W d -> DEPOT segs d m'.
Proof. intros segs d m m' W [WF DM] MU WM AV. split; [exact WF|]. eapply depot_mem_transport; eauto. Qed.

Ltac solve_depot_avoid :=
  unfold depot_avoid, avoids; cbn [d_nb d_sb d_put d_insert fst snd];
  repeat split; repeat (first [apply Forall_nil | apply Forall_cons; [cbn beta iota delta [fst snd]; lia|]]).

Ltac post_callD segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  (let h := head_of ltac:(type of PO) in try unfold h in PO);
  rewrite ?unsigned_lit in PO by lia; rewrite ?Z.add_0_r in PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      try match goal with
          | H : DEPOT segs ?d m |- _ =>
              first [ eapply (DEPOT_transport segs d m m') in H; [| exact MUc | exact WMc | solve_depot_avoid]
                    | idtac "note: could not carry DEPOT across the call"; clear H ]
          end;
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
Ltac head_of t := lazymatch t with ?h _ => head_of h | _ => t end.
Tactic Notation "callD" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callD segs m ]
  end.

Lemma d_nb_put : forall d h n, d_nb (d_put d h n) = d_nb d.
Proof. intros. unfold d_put, d_insert. destruct (d_find d h =? 0); reflexivity. Qed.
Lemma d_sb_put : forall d h n, d_sb (d_put d h n) = d_sb d.
Proof. intros. unfold d_put, d_insert. destruct (d_find d h =? 0); reflexivity. Qed.
Ltac solve_depot_avoid ::=
  unfold depot_avoid, avoids; rewrite ?d_nb_put, ?d_sb_put; cbn [fst snd];
  repeat split; repeat (first [apply Forall_nil | apply Forall_cons; [cbn beta iota delta [fst snd]; lia|]]).

Tactic Notation "callD" uconstr(SPEC) "by" tactic3(TAC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC; TAC | post_callD segs m ]
  end.
