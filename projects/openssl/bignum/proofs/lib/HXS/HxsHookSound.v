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
From OSSVerify.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound.
From OSSVerify.Proofs.openssl.bignum.lib.HXS Require Import HxsStep HxsStepSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section HookSound.
Variable segs : list Segment.
Variable shb : w64.

Definition RSn (rho : valuation) (S : sstate) (ms : machine_state) : Prop :=
  Rn segs rho S ms /\ forall rho', agree_below (s_next S) rho rho' -> sh_law (wZ shb) rho' (s_mem S).

Lemma hxs_step_cases (ic ic' : icache) (S : sstate) (r : sres) :
  hxs_step shb segs ic S = (ic', r) ->
  hx_step segs ic S = (ic', r)
  \/ exists d rd v, hx_fetch segs ic (s_pc S) = Some (d, ic') /\ r = SNext (with_reg_pc S rd v (w_add (s_pc S) w_four)).
Proof.
  intros H. unfold hxs_step in H. unfold hx_step. destruct (hx_fetch segs ic (s_pc S)) as [[d ic1]|] eqn:Ef; [|left; exact H].
  injection H as <- H. unfold hxs_exec in H.
  destruct d; try (left; f_equal; exact H).
  - destruct (xalu shb (s_mem S) op (rget S rs1) (VC imm)) as [v|]; [|left; f_equal; exact H]. right. exists (DOpImm op rd rs1 imm), rd, v. auto.
  - destruct (xalu shb (s_mem S) op (rget S rs1) (VC sh)) as [v|]; [|left; f_equal; exact H]. right. exists (DShiftImm op rd rs1 sh), rd, v. auto.
  - destruct (xalu shb (s_mem S) op (rget S rs1) (rget S rs2)) as [v|]; [|left; f_equal; exact H]. right. exists (DOp op rd rs1 rs2), rd, v. auto.
Qed.

Lemma hxs_step_next (ic ic' : icache) (S S' : sstate) : hxs_step shb segs ic S = (ic', SNext S') -> s_next S' = s_next S /\ s_abs S' = s_abs S.
Proof.
  intros H. destruct (hxs_step_cases ic ic' S _ H) as [Hc|(d & rd & v & _ & E)]; [exact (hx_step_next segs ic ic' S S' Hc)|].
  injection E as ->. split; reflexivity.
Qed.

Lemma hxs_step_dirs (ic ic' : icache) (S S' : sstate) : hxs_step shb segs ic S = (ic', SNext S') -> same_dirs (s_mem S) (s_mem S').
Proof.
  intros H. destruct (hxs_step_cases ic ic' S _ H) as [Hc|(d & rd & v & _ & E)]; [exact (mem_step_dirs segs S S' ic ic' Hc)|].
  injection E as ->. apply same_dirs_refl.
Qed.

Definition ro_same (M M' : mem) : Prop := forall t rg, mget M t = Some rg -> rg_wr rg = false -> mget M' t = Some rg.

Lemma ro_same_refl (M : mem) : ro_same M M.
Proof. intros t rg H _. exact H. Qed.

Lemma ro_same_trans (M1 M2 M3 : mem) : ro_same M1 M2 -> ro_same M2 M3 -> ro_same M1 M3.
Proof. intros H1 H2 t rg G W. exact (H2 t rg (H1 t rg G W) W). Qed.

Lemma hx_step_ro (ic ic' : icache) (S S' : sstate) : hx_step segs ic S = (ic', SNext S') -> ro_same (s_mem S) (s_mem S').
Proof.
  intros H. unfold hx_step in H. destruct (hx_fetch segs ic (s_pc S)) as [[d ic1]|]; [|discriminate]. injection H as _ H.
  assert (Hst : forall a sz v M', hx_store segs (s_mem S) (s_abs S) a sz v = Some M' -> ro_same (s_mem S) M').
  { intros a sz v M' Hs. unfold hx_store in Hs. destruct (resolve (s_mem S) (s_abs S) a (nbytes sz)) as [[[t rg] off]|] eqn:Er; [|discriminate].
    destruct (rg_wr rg) eqn:Ew; [|discriminate]. destruct (_ <=? 8)%uint63; [|discriminate]. injection Hs as <-.
    assert (Eg : mget (s_mem S) t = Some rg).
    { unfold resolve in Er. destruct a as [w|t' o| |]; [| |discriminate|discriminate].
      - destruct (wh w); [discriminate|]. destruct (abs_find _ _ _) as [[t' off']|]; [|discriminate].
        destruct (mget (s_mem S) t') as [rg'|] eqn:E; [|discriminate]. destruct (rg_abs rg'); [|discriminate].
        destruct (_ && _); [|discriminate]. injection Er as <- <- <-. exact E.
      - destruct (wh o); [discriminate|]. destruct (mget (s_mem S) t') as [rg'|] eqn:E; [|discriminate].
        destruct (rg_abs rg'); [discriminate|]. destruct (in_rg _ _ _); [|discriminate]. injection Er as <- <- <-. exact E. }
    intros t2 rg2 G2 W2. rewrite (mget_mset (s_mem S) t t2 _ (mget_lt _ _ _ Eg)).
    destruct (Z.eqb_spec (to_Z t) (to_Z t2)) as [E|E]; [|exact G2].
    apply to_Z_inj in E. subst t2. rewrite Eg in G2. injection G2 as <-. congruence. }
  destruct d; cbn [hx_exec] in H; try discriminate;
    repeat match type of H with
           | (match ?x with _ => _ end) = _ => destruct x eqn:?; try discriminate
           | (if ?x then _ else _) = _ => destruct x eqn:?; try discriminate
           end;
    try (injection H as <-; cbn [s_mem with_reg_pc with_pc with_mem_pc with_all]; try apply ro_same_refl; eapply Hst; eassumption).
Qed.

Lemma hxs_step_ro (ic ic' : icache) (S S' : sstate) : hxs_step shb segs ic S = (ic', SNext S') -> ro_same (s_mem S) (s_mem S').
Proof.
  intros H. destruct (hxs_step_cases ic ic' S _ H) as [Hc|(d & rd & v & _ & E)]; [exact (hx_step_ro ic ic' S S' Hc)|].
  injection E as ->. apply ro_same_refl.
Qed.

Lemma hx_step_stuck (ic ic' : icache) (S S1 : sstate) (c : int) :
  ic_ok segs ic -> hx_step segs ic S = (ic', SStuck c S1) -> S1 = S /\ ic_ok segs ic'.
Proof.
  intros Hic Es. split.
  - unfold hx_step in Es. destruct (hx_fetch segs ic (s_pc S)) as [[d ic2]|]; [|injection Es as _ _ <-; reflexivity].
    injection Es as _ Es. destruct d; cbn [hx_exec] in Es; try discriminate;
      repeat match type of Es with
             | (match ?x with _ => _ end) = _ => destruct x; try discriminate
             | (if ?x then _ else _) = _ => destruct x; try discriminate
             end; try discriminate; injection Es as _ <-; reflexivity.
  - unfold hx_step in Es. destruct (hx_fetch segs ic (s_pc S)) as [[d ic2]|] eqn:Ef; [|injection Es as <- _; exact Hic].
    injection Es as <- _. exact (proj1 (hx_fetch_sound segs ic ic2 (s_pc S) d Hic Ef)).
Qed.

Lemma hxs_step_stuck (ic ic' : icache) (S S1 : sstate) (c : int) :
  ic_ok segs ic -> hxs_step shb segs ic S = (ic', SStuck c S1) -> S1 = S /\ ic_ok segs ic'.
Proof.
  intros Hic H. destruct (hxs_step_cases ic ic' S _ H) as [Hc|(d & rd & v & _ & E)]; [exact (hx_step_stuck ic ic' S S1 c Hic Hc) | discriminate E].
Qed.

Lemma hxs_step_RSn (rho : valuation) (ic ic' : icache) (S S' : sstate) (ms : machine_state) :
  ic_ok segs ic -> RSn rho S ms -> hxs_step shb segs ic S = (ic', SNext S') ->
  ic_ok segs ic' /\ exists ms', mstep segs ms ms' /\ RSn rho S' ms'
                               /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_rom ms' = ms_rom ms
                               /\ mem_step rho (s_mem S) (ms_mem ms) (ms_mem ms') /\ regs_step (ms_regs ms) (ms_regs ms').
Proof.
  intros Hic [HRn Hlaw] H.
  destruct (hxs_step_sound segs shb rho ic ic' S S' ms Hic (Rn_R segs rho S ms HRn) (Hlaw rho (agree_below_refl _ _)) H)
    as (Hic' & ms' & Hst & HR' & Hf & Hc & Ho & Hm & Hrs).
  split; [exact Hic'|]. exists ms'. split; [exact Hst|]. split; [|auto].
  destruct (hxs_step_next ic ic' S S' H) as [Enx _]. split.
  - intros rho' Ha. rewrite Enx in Ha.
    destruct (hxs_step_sound segs shb rho' ic ic' S S' ms Hic (HRn rho' Ha) (Hlaw rho' Ha) H) as (_ & ms'' & Hst' & HR'' & _).
    rewrite (mstep_det segs ms ms' ms'' Hst Hst'). exact HR''.
  - intros rho' Ha. rewrite Enx in Ha. exact (sh_law_dirs (wZ shb) rho' _ _ (hxs_step_dirs ic ic' S S' H) (Hlaw rho' Ha)).
Qed.

Section Run.
Variable stop : w64 -> bool.

Lemma hxs_run_next (n : nat) : forall (ic ic' : icache) (S : sstate) (r : rres),
  hxs_run shb segs stop n ic S = (ic', r) -> s_next (res_state r) = s_next S /\ s_abs (res_state r) = s_abs S.
Proof.
  induction n as [|n IH]; intros ic ic' S r H; cbn [hxs_run] in H.
  - unfold hxs_step1 in H. destruct (stop (s_pc S)); [injection H as _ <-; split; reflexivity|].
    destruct (hxs_step shb segs ic S) as [ic1 [S1|c S1]] eqn:Es; injection H as _ <-; cbn [res_state].
    + exact (hxs_step_next ic ic1 S S1 Es).
    + destruct (hxs_step_cases ic ic1 S _ Es) as [Hc|(d & rd & v & _ & E)]; [|discriminate E].
      unfold hx_step in Hc. destruct (hx_fetch segs ic (s_pc S)) as [[d ic2]|]; [|injection Hc as _ _ <-; split; reflexivity].
      injection Hc as _ Hc. destruct d; cbn [hx_exec] in Hc; try discriminate;
        repeat match type of Hc with
               | (match ?x with _ => _ end) = _ => destruct x; try discriminate
               | (if ?x then _ else _) = _ => destruct x; try discriminate
               end; try discriminate; injection Hc as _ <-; split; reflexivity.
  - destruct (hxs_run shb segs stop n ic S) as [ic1 r1] eqn:E1. destruct (IH ic ic1 S r1 E1) as [N1 A1].
    destruct r1 as [S1|S1|c S1]; try (injection H as _ <-; split; assumption).
    destruct (IH ic1 ic' S1 r H) as [N2 A2]. cbn [res_state] in N1, A1. split; congruence.
Qed.

Definition xstep_pres (rho : valuation) (P : sstate -> machine_state -> Prop) : Prop :=
  forall S S' ms ms', P S ms -> Rn segs rho S ms -> Rn segs rho S' ms' -> mstep segs ms ms' ->
    ms_fregs ms' = ms_fregs ms -> ms_fcsr ms' = ms_fcsr ms -> ms_rom ms' = ms_rom ms ->
    same_dirs (s_mem S) (s_mem S') -> ro_same (s_mem S) (s_mem S') ->
    mem_step rho (s_mem S) (ms_mem ms) (ms_mem ms') -> regs_step (ms_regs ms) (ms_regs ms') ->
    s_next S' = s_next S -> s_abs S' = s_abs S -> P S' ms'.

Theorem hxs_run_RSn_inv (rho : valuation) (P : sstate -> machine_state -> Prop) (HP : xstep_pres rho P) (n : nat) :
  forall (ic ic' : icache) (S : sstate) (r : rres) (ms : machine_state),
  ic_ok segs ic -> RSn rho S ms -> P S ms -> hxs_run shb segs stop n ic S = (ic', r) ->
  ic_ok segs ic' /\ exists ms', msteps segs ms ms' /\ RSn rho (res_state r) ms' /\ P (res_state r) ms'.
Proof.
  induction n as [|n IH]; intros ic ic' S r ms Hic HR HPS H; cbn [hxs_run] in H.
  - unfold hxs_step1 in H. destruct (stop (s_pc S)).
    + injection H as <- <-. split; [exact Hic|]. exists ms. split; [apply msteps_refl | split; assumption].
    + destruct (hxs_step shb segs ic S) as [ic1 [S1|c S1]] eqn:Es; injection H as <- <-.
      * destruct (hxs_step_RSn rho ic ic1 S S1 ms Hic HR Es) as (Hic1 & ms' & Hst & HR' & Hf & Hc & Ho & Hm & Hrs).
        destruct (hxs_step_next ic ic1 S S1 Es) as [Hnx Habs].
        split; [exact Hic1|]. exists ms'. split; [apply msteps_one; exact Hst|]. split; [exact HR'|].
        exact (HP S S1 ms ms' HPS (proj1 HR) (proj1 HR') Hst Hf Hc Ho (hxs_step_dirs ic ic1 S S1 Es) (hxs_step_ro ic ic1 S S1 Es) Hm Hrs Hnx Habs).
      * destruct (hxs_step_stuck ic ic1 S S1 c Hic Es) as [-> Hic1]. split; [exact Hic1|].
        exists ms. split; [apply msteps_refl | split; assumption].
  - destruct (hxs_run shb segs stop n ic S) as [ic1 r1] eqn:E1. destruct (IH ic ic1 S r1 ms Hic HR HPS E1) as (Hic1 & ms1 & M1 & R1 & P1).
    destruct r1 as [S1|S1|c S1]; try (injection H as <- <-; split; [exact Hic1 | exists ms1; auto]).
    cbn [res_state] in *. destruct (IH ic1 ic' S1 r ms1 Hic1 R1 P1 H) as (Hic2 & ms2 & M2 & R2 & P2).
    split; [exact Hic2|]. exists ms2. split; [eapply msteps_trans; eassumption | split; assumption].
Qed.

End Run.

Section DriveStep.
Context {CD : Type}.
Variable hookix : itrie nat.
Variable hooks : list (@hook CD).
Variable final : w64 -> bool.
Variable G : Type.
Variable J : G -> machine_state -> Prop.
Variable FInv : G -> valuation -> CD -> sstate -> machine_state -> Prop.

Definition XInv (g : G) (rho : valuation) (cd : CD) (S : sstate) (ms : machine_state) : Prop :=
  RSn rho S ms /\ FInv g rho cd S ms.

Hypothesis J_evt : forall g ms, evt segs (J g) ms -> J g ms.
Hypothesis FInv_step : forall g rho cd, xstep_pres rho (FInv g rho cd).

Definition xhook_ok (h : @hook CD) : Prop :=
  forall g rho cd S cd' S' ms, XInv g rho cd S ms -> h cd S = Some (cd', S') ->
    (forall g' rho' ms', agree_below (s_next S) rho rho' -> XInv g' rho' cd' S' ms' -> J g' ms') -> J g ms.

Hypothesis hooks_ok : forall h, In h hooks -> xhook_ok h.

Theorem hxs_drive_sound_step (n : nat) : forall (k : nat) (ic ic' : icache) (cd cd_end : CD) (S S_end : sstate) (g : G) (rho : valuation) (ms : machine_state),
  ic_ok segs ic -> XInv g rho cd S ms -> hxs_drive shb segs hookix hooks final k n ic cd S = (ic', XDone cd_end S_end) ->
  (forall g' rho' ms', agree_below (s_next S) rho rho' -> XInv g' rho' cd_end S_end ms' -> J g' ms') -> J g ms.
Proof.
  assert (Round : forall (k : nat) (ic ic' : icache) (cd cd_end : CD) (S S_end : sstate) (g : G) (rho : valuation) (ms : machine_state),
            (forall ic1 cd' S2 g' rho' ms', ic_ok segs ic1 -> XInv g' rho' cd' S2 ms' ->
                match k with O => (ic1, XFuel cd' S2) | Datatypes.S k' => hxs_drive shb segs hookix hooks final k' n ic1 cd' S2 end = (ic', XDone cd_end S_end) ->
                (forall g'' rho'' ms'', agree_below (s_next S2) rho' rho'' -> XInv g'' rho'' cd_end S_end ms'' -> J g'' ms'') -> J g' ms') ->
            ic_ok segs ic -> XInv g rho cd S ms -> hxs_drive shb segs hookix hooks final k n ic cd S = (ic', XDone cd_end S_end) ->
            (forall g' rho' ms', agree_below (s_next S) rho rho' -> XInv g' rho' cd_end S_end ms' -> J g' ms') -> J g ms).
  { intros k ic ic' cd cd_end S S_end g rho ms Next Hic [HRn HF] H K.
    assert (H' : match hxs_run shb segs (xstop_pc hookix hooks final) n ic S with
                 | (ic1, RStop S1) =>
                     if final (s_pc S1) then (ic1, XDone cd S1) else
                     match hook_at hookix hooks (s_pc S1) with
                     | Some h => match h cd S1 with
                                 | Some (cd', S2) => if (s_next S1 <=? s_next S2)%uint63
                                                     then match k with O => (ic1, XFuel cd' S2) | Datatypes.S k' => hxs_drive shb segs hookix hooks final k' n ic1 cd' S2 end
                                                     else (ic1, XStuck 102 cd S1)
                                 | None => (ic1, XStuck 100 cd S1)
                                 end
                     | None => (ic1, XStuck 101 cd S1)
                     end
                 | (ic1, RStuck c S1) => (ic1, XStuck c cd S1)
                 | (ic1, RRun S1) => (ic1, XFuel cd S1)
                 end = (ic', XDone cd_end S_end)) by (destruct k; exact H).
    clear H. destruct (hxs_run shb segs (xstop_pc hookix hooks final) n ic S) as [ic1 r] eqn:Er.
    destruct (hxs_run_RSn_inv (xstop_pc hookix hooks final) rho (FInv g rho cd) (FInv_step g rho cd) n ic ic1 S r ms Hic HRn HF Er) as (Hic1 & ms1 & Hms & HRn1 & HF1).
    destruct (hxs_run_next (xstop_pc hookix hooks final) n ic ic1 S r Er) as [Hnx Habs].
    destruct r as [S1|S1|c S1]; [discriminate H' | | discriminate H']. cbn [res_state] in *.
    apply J_evt. exists ms1. split; [exact Hms|].
    destruct (final (s_pc S1)).
    - assert (E1 : cd_end = cd) by congruence. assert (E2 : S_end = S1) by congruence. subst cd_end S_end.
      apply (K g rho ms1); [apply agree_below_refl | split; assumption].
    - destruct (hook_at hookix hooks (s_pc S1)) as [h|] eqn:Eh; [|discriminate H'].
      destruct (h cd S1) as [[cd' S2]|] eqn:Ehk; [|discriminate H'].
      destruct (s_next S1 <=? s_next S2)%uint63 eqn:Enx; [|discriminate H']. apply leb_spec in Enx.
      assert (Hin : In h hooks).
      { unfold hook_at in Eh. destruct (pc_ok (s_pc S1)); [|discriminate]. destruct (iget ICD hookix (ic_key (s_pc S1))) as [i|]; [|discriminate].
        exact (nth_error_In hooks i Eh). }
      apply (hooks_ok h Hin g rho cd S1 cd' S2 ms1 (conj HRn1 HF1) Ehk).
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
