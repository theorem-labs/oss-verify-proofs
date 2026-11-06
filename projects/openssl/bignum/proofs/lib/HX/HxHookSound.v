(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import MState Mem Exec.
From OSSVerify.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section HookSound.
Variable segs : list Segment.

Definition Rn (rho : valuation) (S : sstate) (ms : machine_state) : Prop :=
  forall rho', agree_below (s_next S) rho rho' -> R segs rho' S ms.

Lemma Rn_R (rho : valuation) (S : sstate) (ms : machine_state) : Rn rho S ms -> R segs rho S ms.
Proof. intros H. apply H. apply agree_below_refl. Qed.

Lemma Rn_agree (rho rho' : valuation) (S : sstate) (ms : machine_state) :
  agree_below (s_next S) rho rho' -> Rn rho S ms -> Rn rho' S ms.
Proof. intros Ha H rho'' Ha'. apply H. eapply agree_below_trans; [apply Z.le_refl | exact Ha | exact Ha']. Qed.

Lemma hx_step_next (ic ic' : icache) (S S' : sstate) : hx_step segs ic S = (ic', SNext S') -> s_next S' = s_next S /\ s_abs S' = s_abs S.
Proof.
  intros H. unfold hx_step in H. destruct (hx_fetch segs ic (s_pc S)) as [[d ic1]|]; [|discriminate]. injection H as _ H.
  destruct d; cbn [hx_exec] in H; try discriminate;
    repeat match type of H with
           | (match ?x with _ => _ end) = _ => destruct x; try discriminate
           | (if ?x then _ else _) = _ => destruct x; try discriminate
           end; injection H as <-; split; reflexivity.
Qed.

Section Run.
Variable stop : w64 -> bool.

Lemma hx_run_next (n : nat) : forall (ic ic' : icache) (S : sstate) (r : rres),
  hx_run segs stop n ic S = (ic', r) -> s_next (res_state r) = s_next S /\ s_abs (res_state r) = s_abs S.
Proof.
  induction n as [|n IH]; intros ic ic' S r H; cbn [hx_run] in H.
  - unfold hx_step1 in H. destruct (stop (s_pc S)); [injection H as _ <-; split; reflexivity|].
    destruct (hx_step segs ic S) as [ic1 [S1|c S1]] eqn:Es; injection H as _ <-; cbn [res_state].
    + exact (hx_step_next ic ic1 S S1 Es).
    + unfold hx_step in Es. destruct (hx_fetch segs ic (s_pc S)) as [[d ic2]|]; [|injection Es as _ _ <-; split; reflexivity].
      injection Es as _ Es. destruct d; cbn [hx_exec] in Es; try discriminate;
        repeat match type of Es with
               | (match ?x with _ => _ end) = _ => destruct x; try discriminate
               | (if ?x then _ else _) = _ => destruct x; try discriminate
               end; try discriminate; injection Es as _ <-; split; reflexivity.
  - destruct (hx_run segs stop n ic S) as [ic1 r1] eqn:E1. destruct (IH ic ic1 S r1 E1) as [N1 A1].
    destruct r1 as [S1|S1|c S1]; try (injection H as _ <-; split; assumption).
    destruct (IH ic1 ic' S1 r H) as [N2 A2]. cbn [res_state] in N1, A1. split; congruence.
Qed.

Lemma hx_step_Rn (rho : valuation) (ic ic' : icache) (S S' : sstate) (ms : machine_state) :
  ic_ok segs ic -> Rn rho S ms -> hx_step segs ic S = (ic', SNext S') ->
  ic_ok segs ic' /\ exists ms', mstep segs ms ms' /\ Rn rho S' ms'
                               /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_rom ms' = ms_rom ms
                               /\ mem_step rho (s_mem S) (ms_mem ms) (ms_mem ms') /\ regs_step (ms_regs ms) (ms_regs ms').
Proof.
  intros Hic HRn H. destruct (hx_step_sound segs rho ic ic' S S' ms Hic (Rn_R rho S ms HRn) H) as (Hic' & ms' & Hst & HR' & Hf & Hc & Ho & Hm & Hrs).
  split; [exact Hic'|]. exists ms'. split; [exact Hst|]. split; [|auto].
  intros rho' Ha. rewrite (proj1 (hx_step_next ic ic' S S' H)) in Ha.
  destruct (hx_step_sound segs rho' ic ic' S S' ms Hic (HRn rho' Ha) H) as (_ & ms'' & Hst' & HR'' & _).
  rewrite (mstep_det segs ms ms' ms'' Hst Hst'). exact HR''.
Qed.

Definition run_postn (rho : valuation) (S : sstate) (ms : machine_state) (S' : sstate) : Prop :=
  exists ms', msteps segs ms ms' /\ Rn rho S' ms'
              /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_rom ms' = ms_rom ms
              /\ same_dirs (s_mem S) (s_mem S') /\ mem_frame segs rho (s_mem S) (ms_mem ms) (ms_mem ms').

Definition step_pres (rho : valuation) (P : sstate -> machine_state -> Prop) : Prop :=
  forall S S' ms ms', P S ms -> Rn rho S ms -> Rn rho S' ms' -> mstep segs ms ms' ->
    ms_fregs ms' = ms_fregs ms -> ms_fcsr ms' = ms_fcsr ms -> ms_rom ms' = ms_rom ms ->
    same_dirs (s_mem S) (s_mem S') -> mem_step rho (s_mem S) (ms_mem ms) (ms_mem ms') -> regs_step (ms_regs ms) (ms_regs ms') ->
    s_next S' = s_next S -> s_abs S' = s_abs S -> P S' ms'.

Theorem hx_run_Rn_inv (rho : valuation) (P : sstate -> machine_state -> Prop) (HP : step_pres rho P) (n : nat) :
  forall (ic ic' : icache) (S : sstate) (r : rres) (ms : machine_state),
  ic_ok segs ic -> Rn rho S ms -> P S ms -> hx_run segs stop n ic S = (ic', r) ->
  ic_ok segs ic' /\ exists ms', msteps segs ms ms' /\ Rn rho (res_state r) ms' /\ P (res_state r) ms'.
Proof.
  induction n as [|n IH]; intros ic ic' S r ms Hic HR HPS H; cbn [hx_run] in H.
  - unfold hx_step1 in H. destruct (stop (s_pc S)).
    + injection H as <- <-. split; [exact Hic|]. exists ms. split; [apply msteps_refl | split; assumption].
    + destruct (hx_step segs ic S) as [ic1 [S1|c S1]] eqn:Es; injection H as <- <-.
      * destruct (hx_step_Rn rho ic ic1 S S1 ms Hic HR Es) as (Hic1 & ms' & Hst & HR' & Hf & Hc & Ho & Hm & Hrs).
        destruct (hx_step_next ic ic1 S S1 Es) as [Hnx Habs].
        split; [exact Hic1|]. exists ms'. split; [apply msteps_one; exact Hst|]. split; [exact HR'|].
        exact (HP S S1 ms ms' HPS HR HR' Hst Hf Hc Ho (mem_step_dirs segs S S1 ic ic1 Es) Hm Hrs Hnx Habs).
      * assert (S1 = S).
        { unfold hx_step in Es. destruct (hx_fetch segs ic (s_pc S)) as [[d ic2]|]; [|injection Es as _ _ <-; reflexivity].
          injection Es as _ Es. destruct d; cbn [hx_exec] in Es; try discriminate;
            repeat match type of Es with
                   | (match ?x with _ => _ end) = _ => destruct x; try discriminate
                   | (if ?x then _ else _) = _ => destruct x; try discriminate
                   end; try discriminate; injection Es as _ <-; reflexivity. }
        subst S1. split.
        { unfold hx_step in Es. destruct (hx_fetch segs ic (s_pc S)) as [[d ic2]|] eqn:Ef; [|injection Es as <- _; exact Hic].
          injection Es as <- _. exact (proj1 (hx_fetch_sound segs ic ic2 (s_pc S) d Hic Ef)). }
        exists ms. split; [apply msteps_refl | split; assumption].
  - destruct (hx_run segs stop n ic S) as [ic1 r1] eqn:E1. destruct (IH ic ic1 S r1 ms Hic HR HPS E1) as (Hic1 & ms1 & M1 & R1 & P1).
    destruct r1 as [S1|S1|c S1]; try (injection H as <- <-; split; [exact Hic1 | exists ms1; auto]).
    cbn [res_state] in *. destruct (IH ic1 ic' S1 r ms1 Hic1 R1 P1 H) as (Hic2 & ms2 & M2 & R2 & P2).
    split; [exact Hic2|]. exists ms2. split; [eapply msteps_trans; eassumption | split; assumption].
Qed.

End Run.

Section Drive.
Context {CD : Type}.
Variable hooks : list (w64 * (CD -> sstate -> option (CD * sstate))).
Variable final : w64 -> bool.
Variable G : Type.
Variable J : G -> machine_state -> Prop.
Variable FInv : G -> valuation -> CD -> sstate -> machine_state -> Prop.

Definition Inv (g : G) (rho : valuation) (cd : CD) (S : sstate) (ms : machine_state) : Prop :=
  Rn rho S ms /\ FInv g rho cd S ms.

Hypothesis J_evt : forall g ms, evt segs (J g) ms -> J g ms.

Hypothesis FInv_run : forall g rho cd S S' ms ms',
  FInv g rho cd S ms -> Rn rho S ms -> Rn rho S' ms' -> msteps segs ms ms' ->
  ms_fregs ms' = ms_fregs ms -> ms_fcsr ms' = ms_fcsr ms -> ms_rom ms' = ms_rom ms ->
  same_dirs (s_mem S) (s_mem S') -> mem_frame segs rho (s_mem S) (ms_mem ms) (ms_mem ms') ->
  s_next S' = s_next S -> s_abs S' = s_abs S -> FInv g rho cd S' ms'.

Definition hook_ok (h : CD -> sstate -> option (CD * sstate)) : Prop :=
  forall g rho cd S cd' S' ms, Inv g rho cd S ms -> h cd S = Some (cd', S') ->
    (forall g' rho' ms', agree_below (s_next S) rho rho' -> Inv g' rho' cd' S' ms' -> J g' ms') -> J g ms.

Hypothesis hooks_ok : forall pc h, find_hook hooks pc = Some h -> hook_ok h.

End Drive.

Section DriveStep.
Context {CD : Type}.
Variable hooks : list (w64 * (CD -> sstate -> option (CD * sstate))).
Variable final : w64 -> bool.
Variable G : Type.
Variable J : G -> machine_state -> Prop.
Variable FInv : G -> valuation -> CD -> sstate -> machine_state -> Prop.

Hypothesis J_evt : forall g ms, evt segs (J g) ms -> J g ms.
Hypothesis FInv_step : forall g rho cd, step_pres rho (FInv g rho cd).

Definition hook_ok' (h : CD -> sstate -> option (CD * sstate)) : Prop :=
  forall g rho cd S cd' S' ms, Inv G FInv g rho cd S ms -> h cd S = Some (cd', S') ->
    (forall g' rho' ms', agree_below (s_next S) rho rho' -> Inv G FInv g' rho' cd' S' ms' -> J g' ms') -> J g ms.

Hypothesis hooks_ok : forall pc h, find_hook hooks pc = Some h -> hook_ok' h.

Theorem hx_drive_sound_step (n : nat) : forall (k : nat) (ic ic' : icache) (cd cd_end : CD) (S S_end : sstate) (g : G) (rho : valuation) (ms : machine_state),
  ic_ok segs ic -> Inv G FInv g rho cd S ms -> hx_drive segs hooks final k n ic cd S = (ic', DDone cd_end S_end) ->
  (forall g' rho' ms', agree_below (s_next S) rho rho' -> Inv G FInv g' rho' cd_end S_end ms' -> J g' ms') -> J g ms.
Proof.
  assert (Round : forall (k : nat) (ic ic' : icache) (cd cd_end : CD) (S S_end : sstate) (g : G) (rho : valuation) (ms : machine_state),
            (forall ic1 cd' S2 g' rho' ms', ic_ok segs ic1 -> Inv G FInv g' rho' cd' S2 ms' ->
                match k with O => (ic1, DFuel cd' S2) | Datatypes.S k' => hx_drive segs hooks final k' n ic1 cd' S2 end = (ic', DDone cd_end S_end) ->
                (forall g'' rho'' ms'', agree_below (s_next S2) rho' rho'' -> Inv G FInv g'' rho'' cd_end S_end ms'' -> J g'' ms'') -> J g' ms') ->
            ic_ok segs ic -> Inv G FInv g rho cd S ms -> hx_drive segs hooks final k n ic cd S = (ic', DDone cd_end S_end) ->
            (forall g' rho' ms', agree_below (s_next S) rho rho' -> Inv G FInv g' rho' cd_end S_end ms' -> J g' ms') -> J g ms).
  { intros k ic ic' cd cd_end S S_end g rho ms Next Hic [HRn HF] H K.
    assert (H' : match hx_run segs (stop_pc hooks final) n ic S with
                 | (ic1, RStop S1) =>
                     if final (s_pc S1) then (ic1, DDone cd S1) else
                     match find_hook hooks (s_pc S1) with
                     | Some h => match h cd S1 with
                                 | Some (cd', S2) => if (s_next S1 <=? s_next S2)%uint63
                                                     then match k with O => (ic1, DFuel cd' S2) | Datatypes.S k' => hx_drive segs hooks final k' n ic1 cd' S2 end
                                                     else (ic1, DStuck 102 cd S1)
                                 | None => (ic1, DStuck 100 cd S1)
                                 end
                     | None => (ic1, DStuck 101 cd S1)
                     end
                 | (ic1, RStuck c S1) => (ic1, DStuck c cd S1)
                 | (ic1, RRun S1) => (ic1, DFuel cd S1)
                 end = (ic', DDone cd_end S_end)) by (destruct k; exact H).
    clear H. destruct (hx_run segs (stop_pc hooks final) n ic S) as [ic1 r] eqn:Er.
    destruct (hx_run_Rn_inv (stop_pc hooks final) rho (FInv g rho cd) (FInv_step g rho cd) n ic ic1 S r ms Hic HRn HF Er) as (Hic1 & ms1 & Hms & HRn1 & HF1).
    destruct (hx_run_next (stop_pc hooks final) n ic ic1 S r Er) as [Hnx Habs].
    destruct r as [S1|S1|c S1]; [discriminate H' | | discriminate H']. cbn [res_state] in *.
    apply J_evt. exists ms1. split; [exact Hms|].
    destruct (final (s_pc S1)).
    - assert (E1 : cd_end = cd) by congruence. assert (E2 : S_end = S1) by congruence. subst cd_end S_end.
      apply (K g rho ms1); [apply agree_below_refl | split; assumption].
    - destruct (find_hook hooks (s_pc S1)) as [h|] eqn:Eh; [|discriminate H'].
      destruct (h cd S1) as [[cd' S2]|] eqn:Ehk; [|discriminate H'].
      destruct (s_next S1 <=? s_next S2)%uint63 eqn:Enx; [|discriminate H']. apply leb_spec in Enx.
      apply (hooks_ok (s_pc S1) h Eh g rho cd S1 cd' S2 ms1 (conj HRn1 HF1) Ehk).
      intros g' rho' ms' Ha HI. apply (Next ic1 cd' S2 g' rho' ms' Hic1 HI H').
      intros g'' rho'' ms'' Ha' HI'. apply (K g'' rho'' ms''); [|exact HI'].
      rewrite <- Hnx. exact (agree_below_trans (s_next S1) (s_next S2) rho rho' rho'' Enx Ha Ha'). }
  induction k as [|k IH]; intros ic ic' cd cd_end S S_end g rho ms Hic HI H K.
  - apply (Round 0%nat ic ic' cd cd_end S S_end g rho ms); try assumption. intros; discriminate.
  - apply (Round (Datatypes.S k) ic ic' cd cd_end S S_end g rho ms); try assumption.
    intros ic1 cd' S2 g' rho' ms' Hic1 HI' H2 K2. exact (IH ic1 ic' cd' cd_end S2 S_end g' rho' ms' Hic1 HI' H2 K2).
Qed.

End DriveStep.

End HookSound.
