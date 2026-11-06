(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import MState Mem Exec Frame.
From OSSVerify.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxLearn HxSym.
From OSSVerify.Proofs.openssl.bndiv.lib.HXS Require Import HxsStep HxsStepSound HxsHookSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section SymS.
Variable shb : w64.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xtry (S : sstate) : option sstate :=
  let npc := w_add (s_pc S) w_four in
  match hx_fetch segs IEmpty (s_pc S) with
  | Some (DOpImm op rd rs1 imm, _) =>
      match xalu shb (s_mem S) op (rget S rs1) (VC imm) with Some v => Some (with_reg_pc S rd v npc) | None => None end
  | Some (DShiftImm op rd rs1 sh, _) =>
      match xalu shb (s_mem S) op (rget S rs1) (VC sh) with Some v => Some (with_reg_pc S rd v npc) | None => None end
  | Some (DOp op rd rs1 rs2, _) =>
      match xalu shb (s_mem S) op (rget S rs1) (rget S rs2) with Some v => Some (with_reg_pc S rd v npc) | None => None end
  | _ => None
  end.

Definition sxs_step (log : list snode) (S : sstate) : option (list snode * sstate) :=
  match xtry S with
  | Some S' => Some (log, S')
  | None => sx_step segs log S
  end.

(* [comment removed for export] *)
Lemma xtry_hxs_step (S S' : sstate) : xtry S = Some S' -> exists ic', hxs_step shb segs IEmpty S = (ic', SNext S').
Proof.
  unfold xtry, hxs_step. intros H. destruct (hx_fetch segs IEmpty (s_pc S)) as [[d ic1]|]; [|discriminate H].
  exists ic1. unfold hxs_exec. destruct d; try discriminate H.
  - destruct (xalu shb (s_mem S) op (rget S rs1) (VC imm)); [|discriminate H]. injection H as <-. reflexivity.
  - destruct (xalu shb (s_mem S) op (rget S rs1) (VC sh)); [|discriminate H]. injection H as <-. reflexivity.
  - destruct (xalu shb (s_mem S) op (rget S rs1) (rget S rs2)); [|discriminate H]. injection H as <-. reflexivity.
Qed.

(* [comment removed for export] *)
Definition sxs_post (rho : valuation) (log : list snode) (S : sstate) (ms : machine_state) (log' : list snode) (S' : sstate) : Prop :=
  exists rho' ms', agree_below (s_next S) rho rho' /\ mstep segs ms ms' /\ RSn segs shb rho' S' ms'
    /\ log_ok rho' log' /\ log_below (s_next S') log' /\ to_Z (s_next S) <= to_Z (s_next S')
    /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_rom ms' = ms_rom ms
    /\ same_dirs (s_mem S) (s_mem S') /\ mem_step rho' (s_mem S) (ms_mem ms) (ms_mem ms') /\ regs_step (ms_regs ms) (ms_regs ms')
    /\ s_abs S' = s_abs S.

Theorem sxs_step_sound (rho : valuation) (log log' : list snode) (S S' : sstate) (ms : machine_state) :
  RSn segs shb rho S ms -> log_ok rho log -> log_below (s_next S) log -> sxs_step log S = Some (log', S') ->
  sxs_post rho log S ms log' S'.
Proof.
  intros HRS Hlog Hbel H. unfold sxs_step in H. destruct (xtry S) as [S1|] eqn:Ex.
  - (* [comment removed for export] *)
    injection H as <- <-. destruct (xtry_hxs_step S S1 Ex) as [ic' Hs].
    destruct (hxs_step_RSn segs shb rho IEmpty ic' S S1 ms (ic_ok_empty segs) HRS Hs) as (_ & ms' & Hst & HRS' & Hf & Hc & Ho & Hm & Hrs).
    destruct (hxs_step_next segs shb IEmpty ic' S S1 Hs) as [Hnx Habs].
    exists rho, ms'. split; [apply agree_below_refl|]. split; [exact Hst|]. split; [exact HRS'|]. split; [exact Hlog|].
    split; [rewrite Hnx; exact Hbel|]. split; [rewrite Hnx; lia|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Ho|].
    split; [exact (hxs_step_dirs segs shb IEmpty ic' S S1 Hs)|]. split; [exact Hm|]. split; [exact Hrs | exact Habs].
  - (* [comment removed for export] *)
    destruct HRS as [HRn Hlaw].
    destruct (sx_step_sound segs rho log log' S S' ms HRn Hlog Hbel H)
      as (rho1 & ms1 & Hag & Hst & HRn1 & Hlog1 & Hbel1 & Hnx & Hf & Hc & Ho & Hd & Hm & Hrs & Habs).
    exists rho1, ms1. split; [exact Hag|]. split; [exact Hst|]. split.
    { split; [exact HRn1|]. intros rho2 Ha2. apply (sh_law_dirs (wZ shb) rho2 _ _ Hd). apply Hlaw.
      intros t Ht. rewrite (Ha2 t) by lia. apply Hag. exact Ht. }
    repeat (split; [assumption|]). exact Habs.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Run.
Variable stop : w64 -> bool.

Fixpoint sxs_run (n : nat) (log : list snode) (S : sstate) : option (list snode * sstate) :=
  match n with
  | O => Some (log, S)
  | Datatypes.S n' =>
      if stop (s_pc S) then Some (log, S) else
      match sxs_step log S with
      | Some (log', S') => sxs_run n' log' S'
      | None => None
      end
  end.

Theorem sxs_run_sound (P : sstate -> machine_state -> Prop) (n0 : int) (rho0 : valuation) :
  (forall rho, agree_below n0 rho0 rho -> sx_pres segs rho P) ->
  forall (n : nat) (rho : valuation) (log log' : list snode) (S S' : sstate) (ms : machine_state),
    agree_below n0 rho0 rho -> to_Z n0 <= to_Z (s_next S) ->
    RSn segs shb rho S ms -> P S ms -> log_ok rho log -> log_below (s_next S) log -> sxs_run n log S = Some (log', S') ->
    exists rho' ms', agree_below (s_next S) rho rho' /\ msteps segs ms ms' /\ RSn segs shb rho' S' ms' /\ P S' ms'
                     /\ log_ok rho' log' /\ log_below (s_next S') log'.
Proof.
  intros HP. induction n as [|n IH]; intros rho log log' S S' ms Hag0 Hn0 HRS HPS Hlog Hbel H; cbn [sxs_run] in H.
  - injection H as <- <-. exists rho, ms. split; [apply agree_below_refl|]. split; [apply msteps_refl|]. auto.
  - destruct (stop (s_pc S)).
    + injection H as <- <-. exists rho, ms. split; [apply agree_below_refl|]. split; [apply msteps_refl|]. auto.
    + destruct (sxs_step log S) as [[log1 S1]|] eqn:Es; [|discriminate].
      destruct (sxs_step_sound rho log log1 S S1 ms HRS Hlog Hbel Es)
        as (rho1 & ms1 & Hag1 & Hst & HRS1 & Hlog1 & Hbel1 & Hnx & Hf & Hc & Ho & Hd & Hm & Hrs & _).
      assert (Hag01 : agree_below n0 rho0 rho1).
      { intros t Ht. rewrite (Hag1 t) by lia. apply Hag0. exact Ht. }
      assert (HP1 : P S1 ms1).
      { apply (HP rho1 Hag01 S S1 ms ms1 HPS); try assumption; [|exact (proj1 HRS1)]. exact (Rn_agree segs rho rho1 S ms Hag1 (proj1 HRS)). }
      destruct (IH rho1 log1 log' S1 S' ms1 Hag01 ltac:(lia) HRS1 HP1 Hlog1 Hbel1 H) as (rho2 & ms2 & Hag2 & Hms & HRS2 & HP2 & Hlog2 & Hbel2).
      exists rho2, ms2. split.
      { intros t Ht. rewrite (Hag2 t) by lia. apply Hag1. exact Ht. }
      split; [exact (msteps_cons segs _ _ _ Hst Hms)|]. auto.
Qed.

End Run.
End SymS.
