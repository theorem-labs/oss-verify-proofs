(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Atp_objl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Atp_defs Atp_h_defs Pj_loc_defs Pj_os_defs El_os_defs El_ins_iface El_esc_iface El_defs El_dump_iface El_dump_kit El_dump_body1 El_dump_body2.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Loop.
  Variable D : denv.
  Variable j0 : list byte.
  Hypothesis DOK : denv_ok D.
  Hypothesis PUT : os_putX_stmt.
  Hypothesis IUL : ins_ul_stmt.
  Hypothesis IU : ins_u_stmt.
  Hypothesis IL : ins_l_stmt.
  Hypothesis INSD : ins_d_stmt.
  Hypothesis ESC : esc_stmt.

  Notation n := (Z.of_nat (length (de_tws D))).
  Notation T := (Tf (de_tws D)).
  Notation S := (Tf (de_sbs D)).
  Notation sn := (Z.of_nat (length (de_sbs D))).

  Let WF : tape_wf T S sn ck_any n. Proof. exact (proj1 DOK). Qed.
  Let HSN : sn < 2^56. Proof. destruct WF as (_ & H & _). lia. Qed.

  Lemma dump_scalar : forall (i j : Z) (K : machine_state -> Prop) (gp : word),
    scalar T S sn i j -> 1 <= i -> j <= n - 1 -> KLOOP D j0 K gp j -> KLOOP D j0 K gp i.
  Proof.
    intros i j K gp SC I1 JN HK. unfold KLOOP. intros m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 F fc DI FRM.
    destruct SC as [[-> TY]|[[-> TY]|[-> STR]]].
    - assert (TR : 0 <= T i < 2^64) by (destruct TY as [E|[E|E]]; rewrite E; apply tword_range; unfold t_true, t_false, t_null; lia).
      eapply (dump_head D j0 DOK PUT IUL); [exact DI| exact FRM| lia| exact TR|].
      intros. eapply (dump_atom D j0 DOK PUT); [eassumption| eassumption| lia| lia| exact TY| exact HK].
    - assert (TR : 0 <= T i < 2^64) by (destruct TY as [E|[E|E]]; rewrite E; apply tword_range; unfold t_i64, t_u64, t_dbl; lia).
      eapply (dump_head D j0 DOK PUT IUL); [exact DI| exact FRM| lia| exact TR|].
      intros. destruct TY as [E|[E|E]].
      + eapply (dump_num_ul D j0 DOK PUT IUL IL); [eassumption| eassumption| lia| lia| right; exact E| exact HK].
      + eapply (dump_num_ul D j0 DOK PUT IUL IL); [eassumption| eassumption| lia| lia| left; exact E| exact HK].
      + eapply (dump_num_d D j0 DOK PUT INSD); [eassumption| eassumption| lia| lia| exact E| exact HK].
    - pose proof (key_word_range _ _ _ _ STR HSN) as (TR & _ & _).
      eapply (dump_head D j0 DOK PUT IUL); [exact DI| exact FRM| lia| exact TR|].
      intros. eapply (dump_str D j0 DOK PUT ESC); [eassumption| eassumption| lia| lia| exact STR| exact HK].
  Qed.

  Lemma tiles_kloop : forall (P : Z -> Z -> Prop) (K : machine_state -> Prop) (gp : word) (it e c : Z),
    (forall a b, P a b -> a < b) ->
    (forall a b, P a b -> 1 <= a -> b <= n - 1 -> KLOOP D j0 K gp b -> KLOOP D j0 K gp a) ->
    tiles P it e c -> 1 <= it -> e <= n - 1 -> KLOOP D j0 K gp e -> KLOOP D j0 K gp it.
  Proof.
    intros P K gp it e c Plt STEP TI. induction TI as [it|it j0_ e0 c0 Pij Tt IHt]; intros LO HI KE; [exact KE|].
    pose proof (Plt _ _ Pij). pose proof (tiles_le _ Plt _ _ _ Tt) as [JE _].
    eapply STEP; [exact Pij| lia| lia| apply IHt; [lia| lia| exact KE]].
  Qed.

  Lemma dump_elem : forall (d : nat) (i j : Z) (K : machine_state -> Prop) (gp : word),
    elem T S sn ck_any d i j -> 1 <= i -> j <= n - 1 -> KLOOP D j0 K gp j -> KLOOP D j0 K gp i.
  Proof.
    induction d as [|d IH]; intros i j K gp EL I1 JN HK.
    all: assert (NR : 2 < n < 2^32) by (clear - WF; destruct WF as (H & _); exact H).
    { cbn [elem] in EL. destruct EL as [SC|[]]. eapply dump_scalar; eassumption. }
    cbn [elem] in EL. destruct EL as [SC|CO]; [eapply dump_scalar; eassumption|].
    destruct CO as (e & c & cv & -> & CK & CO). unfold ck_any in CK.

    assert (OPEN : forall t tend (P : Z -> Z -> Prop), T i = cword t (e + 1) cv -> T e = tword tend i -> tiles P (i + 1) e c ->
              (t = t_arr /\ tend = t_arr_end \/ t = t_obj /\ tend = t_obj_end) -> (forall a b, P a b -> a < b) ->
              (KLOOP D j0 K gp e -> KLOOP D j0 K gp (i + 1)) -> KLOOP D j0 K gp i).
    { intros t tend P Ti Te TI Ht Plt ITEMS.
      pose proof (tiles_le _ Plt _ _ _ TI) as [IE _].
      assert (TR : 0 <= T i < 2^64) by (rewrite Ti; apply cword_range; [destruct Ht as [[-> _]|[-> _]]; unfold t_arr, t_obj; lia| lia| lia]).
      assert (TRE : 0 <= T e < 2^64) by (rewrite Te; apply close_word_range; [destruct Ht as [[_ ->]|[_ ->]]; unfold t_arr_end, t_obj_end; lia| lia]).

      assert (CLOSE : KLOOP D j0 K gp e).
      { unfold KLOOP. intros m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 F fc DI FRM.
        eapply (dump_head D j0 DOK PUT IUL); [exact DI| exact FRM| lia| exact TRE|].
        intros. eapply (dump_close D j0 DOK PUT IU); [eassumption| eassumption| lia| lia| exact TRE| | exact HK].
        rewrite Te, ttype_tword by lia. destruct Ht as [[_ ->]|[_ ->]]; [right| left]; reflexivity. }
      unfold KLOOP. intros m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 F fc DI FRM.
      eapply (dump_head D j0 DOK PUT IUL); [exact DI| exact FRM| lia| exact TR|].
      intros. eapply (dump_open D j0 DOK PUT IUL IU); [eassumption| eassumption| lia| lia| exact TR| | apply ITEMS; exact CLOSE].
      rewrite Ti, ttype_cword by lia. destruct Ht as [[-> _]|[-> _]]; [right| left]; reflexivity. }
    destruct CO as [(Ti & Te & TI)|(Ti & Te & TI)].
    -
      eapply (OPEN t_arr t_arr_end); [exact Ti| exact Te| exact TI| left; split; reflexivity| apply elem_lt|].
      intros KE. eapply (tiles_kloop (elem T S sn ck_any d)); [apply elem_lt| | exact TI| lia| lia| exact KE].
      intros a b Pab A1 Bn Kb. eapply IH; [exact Pab| exact A1| exact Bn| exact Kb].
    -
      eapply (OPEN t_obj t_obj_end); [exact Ti| exact Te| exact TI| right; split; reflexivity| apply field_lt; apply elem_lt|].
      intros KE. eapply (tiles_kloop (field T S sn (elem T S sn ck_any d))); [apply field_lt; apply elem_lt| | exact TI| lia| lia| exact KE].
      intros a b [STR Pab] A1 Bn Kb. pose proof (elem_lt _ _ _ _ _ _ _ Pab).

      eapply dump_scalar; [right; right; split; [reflexivity| exact STR]| lia| lia|].
      eapply IH; [exact Pab| lia| exact Bn| exact Kb].
  Qed.

  Lemma dump_root : forall (K : machine_state -> Prop) (gp : word), KLOOP D j0 K gp (n - 1) -> KLOOP D j0 K gp 1.
  Proof.
    intros K gp HK. destruct (tape_wf_root _ _ _ _ _ WF) as [EL NR].
    eapply (dump_elem TAPE_MAX_DEPTH); [exact EL| lia| lia| exact HK].
  Qed.
End Loop.
End WithCeiling0.
