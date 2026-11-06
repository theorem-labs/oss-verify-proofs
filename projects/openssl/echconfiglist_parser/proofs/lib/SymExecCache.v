(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FMapPositive.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymExec2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import SX2.

Section Cache.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition fdec (pc : Z) : option instr :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | None => None
  | Some w =>
      if is_ecall w then None else
      match decode_any w with
      | None => None
      | Some (i, sz) => if negb (Z.eqb sz 4) then None else Some i
      end
  end.

Fixpoint sym_exec_f (f : Z -> option instr) (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                    (ss : sym_state) (acc : list sidecond) : sym_state * list sidecond * scripts :=
  match fuel with
  | O => (ss, acc, scr)
  | S fu =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (ss, acc, scr) else
      match f (s_pc ss) with
      | None => (ss, acc, scr)
      | Some i =>
          match sym_step segs i ss scr with
          | SOk ss' scs scr' => sym_exec_f f fu false stops scr' ss' (sc_add scs acc)
          | SStop => (ss, acc, scr)
          end
      end
  end.

Lemma sym_exec_f_fdec : forall fuel first stops scr ss acc,
  sym_exec segs fuel first stops scr ss acc = sym_exec_f fdec fuel first stops scr ss acc.
Proof.
  induction fuel as [|fu IH]; intros first stops scr ss acc; cbn [sym_exec sym_exec_f]; [reflexivity|].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  unfold fdec. destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|reflexivity].
  destruct (is_ecall w); [reflexivity|].
  destruct (decode_any w) as [[i sz]|]; [|reflexivity].
  destruct (negb (Z.eqb sz 4)); [reflexivity|].
  destruct (sym_step segs i ss scr) as [ss' scs scr'|]; [apply IH | reflexivity].
Qed.

Lemma sym_exec_f_ext : forall f g, (forall pc, f pc = g pc) ->
  forall fuel first stops scr ss acc,
  sym_exec_f f fuel first stops scr ss acc = sym_exec_f g fuel first stops scr ss acc.
Proof.
  intros f g Hfg. induction fuel as [|fu IH]; intros first stops scr ss acc; cbn [sym_exec_f]; [reflexivity|].
  rewrite Hfg. destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (g (s_pc ss)) as [i|]; [|reflexivity].
  destruct (sym_step segs i ss scr) as [ss' scs scr'|]; [apply IH | reflexivity].
Qed.

(* [comment removed for export] *)
Definition dtab : Type := PositiveMap.t (option instr).

Definition mk_tab (pcs : list positive) : dtab :=
  fold_left (fun t p => PositiveMap.add p (fdec (Zpos p)) t) pcs (PositiveMap.empty (option instr)).

Definition tab_fun (t : dtab) (pc : Z) : option instr :=
  match pc with
  | Zpos p => match PositiveMap.find p t with Some r => r | None => fdec pc end
  | _ => fdec pc
  end.

Definition tab_sound (t : dtab) : Prop := forall p r, PositiveMap.find p t = Some r -> r = fdec (Zpos p).

Lemma mk_tab_sound : forall pcs, tab_sound (mk_tab pcs).
Proof.
  intro pcs. unfold mk_tab.
  assert (G : forall t, tab_sound t -> tab_sound (fold_left (fun t p => PositiveMap.add p (fdec (Zpos p)) t) pcs t)).
  { induction pcs as [|q pcs IH]; intros t Ht; cbn [fold_left]; [exact Ht|].
    apply IH. intros p r Hf. destruct (Pos.eq_dec p q) as [->|Hne].
    - rewrite PositiveMap.gss in Hf. injection Hf as <-. reflexivity.
    - rewrite PositiveMap.gso in Hf by exact Hne. exact (Ht p r Hf). }
  apply G. intros p r Hf. rewrite PositiveMap.gempty in Hf. discriminate.
Qed.

Lemma tab_fun_fdec : forall pcs pc, tab_fun (mk_tab pcs) pc = fdec pc.
Proof.
  intros pcs pc. unfold tab_fun. destruct pc as [|p|p]; [reflexivity| |reflexivity].
  destruct (PositiveMap.find p (mk_tab pcs)) as [r|] eqn:Hf; [|reflexivity].
  exact (mk_tab_sound pcs p r Hf).
Qed.

Theorem sym_exec_cached : forall pcs fuel first stops scr ss acc,
  sym_exec segs fuel first stops scr ss acc = sym_exec_f (tab_fun (mk_tab pcs)) fuel first stops scr ss acc.
Proof.
  intros pcs fuel first stops scr ss acc. rewrite sym_exec_f_fdec.
  apply sym_exec_f_ext. intro pc. symmetry. apply tab_fun_fdec.
Qed.

(* [comment removed for export] *)
Fixpoint sym_pcs_aux (fuel : nat) (first : bool) (stops : list Z) (scr : scripts) (ss : sym_state) (t : dtab) : dtab :=
  match fuel with
  | O => t
  | S fu =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then t else
      match s_pc ss with
      | Zpos p =>
          let '(r, t') := match PositiveMap.find p t with
                          | Some r => (r, t)
                          | None => let r := fdec (Zpos p) in (r, PositiveMap.add p r t)
                          end in
          match r with
          | None => t'
          | Some i =>
              match sym_step segs i ss scr with
              | SOk ss' _ scr' => sym_pcs_aux fu false stops scr' ss' t'
              | SStop => t'
              end
          end
      | _ => t
      end
  end.

Definition sym_pcs (fuel : nat) (stops : list Z) (scr : scripts) (ss : sym_state) : list positive :=
  map fst (PositiveMap.elements (sym_pcs_aux fuel true stops scr ss (PositiveMap.empty (option instr)))).

End Cache.

(* [comment removed for export] *)
Definition pcs_union (ls : list (list positive)) : list positive :=
  map fst (PositiveMap.elements
             (fold_left (fun t p => PositiveMap.add p tt t) (concat ls) (PositiveMap.empty unit))).
