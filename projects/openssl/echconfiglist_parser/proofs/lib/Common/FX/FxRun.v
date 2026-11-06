(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import NodesCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxMemSound FxValSound FxStepSound FxStepMain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Run.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.

Local Abbreviation Rr := (R segs IM rho).

Definition nat_of_int (i : int) : nat := Z.to_nat (to_Z i).

Theorem fx_run_sound : forall bp k F F' r cnt,
  (k <= 61)%nat ->
  fx_run IM code bp k F = (F', r, cnt) ->
  to_Z cnt <= 2 ^ Z.of_nat k /\
  forall ms, Rr F ms ->
  exists ms', rsteps segs (nat_of_int cnt) ms = MachineOk ms' /\ Rr F' ms'
              /\ (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms')).
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt Hk H.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63.
    { injection H as <- <- <-. split; [cbn; lia|]. intros ms HR. exists ms. split; [reflexivity | split; [exact HR | discriminate]]. }
    destruct (fx_step IM code F) as [s'| |c] eqn:Es.
    + injection H as <- <- <-. split; [cbn; lia|]. intros ms HR.
      destruct (fx_step_sound segs IM rho Hrho0 code Hcode F ms s' HR Es) as (ms' & Hs & HR').
      exists ms'. split; [|split; [exact HR' | discriminate]].
      change (nat_of_int 1) with 1%nat. cbn [rsteps]. rewrite (R_svc _ _ _ _ _ HR), Hs. reflexivity.
    + injection H as <- <- <-. split; [cbn; lia|]. intros ms HR. exists ms. split; [reflexivity|]. split; [exact HR|].
      intros _. exact (fx_step_ecall segs IM rho code Hcode F ms HR Es).
    + injection H as <- <- <-. split; [cbn; lia|]. intros ms HR. exists ms. split; [reflexivity|]. split; [exact HR | discriminate].
  - cbn [fx_run] in H. destruct (fx_run IM code bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (IH _ _ _ _ ltac:(lia) E1) as (Hb1 & IH1).
    assert (Hpow : 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
    assert (Hlt : 2 ^ Z.of_nat (S k) <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia).
    destruct (stop_is_fuel r1) eqn:Er.
    + destruct (fx_run IM code bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      destruct (IH _ _ _ _ ltac:(lia) E2) as (Hb2 & IH2).
      pose proof (Uint63.to_Z_bounded n1). pose proof (Uint63.to_Z_bounded n2).
      assert (Hadd : to_Z (n1 + n2)%uint63 = to_Z n1 + to_Z n2).
      { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2^63). lia. }
      split; [rewrite Hadd; lia|]. intros ms HR.
      destruct (IH1 ms HR) as (ms1 & Hn1 & HR1 & _).
      destruct (IH2 ms1 HR1) as (ms2 & Hn2 & HR2 & Hec2).
      exists ms2. split; [|split; assumption].
      unfold nat_of_int. rewrite Hadd, Z2Nat.inj_add by lia.
      exact (rsteps_trans segs _ _ _ _ _ Hn1 Hn2).
    + injection H as <- <- <-. split; [lia|]. intros ms HR.
      destruct (IH1 ms HR) as (ms1 & Hn1 & HR1 & Hec1). exists ms1. split; [exact Hn1 | split; assumption].
Qed.

(* [comment removed for export] *)
Theorem fx_run_sound_frame : forall bp k F F' r cnt,
  (k <= 61)%nat ->
  fx_run IM code bp k F = (F', r, cnt) ->
  to_Z cnt <= 2 ^ Z.of_nat k /\
  (forall x, claimed_wr IM rho (f_mem F') x -> claimed_wr IM rho (f_mem F) x) /\
  forall ms, Rr F ms ->
  exists ms', rsteps segs (nat_of_int cnt) ms = MachineOk ms' /\ Rr F' ms'
              /\ (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms'))
              /\ (forall x, ~ claimed_wr IM rho (f_mem F) x -> ms_mem ms' x = ms_mem ms x)
              /\ ms_rom ms' = ms_rom ms.
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt Hk H.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63.
    { injection H as <- <- <-. split; [cbn; lia|]. split; [intros x Hx; exact Hx|].
      intros ms HR. exists ms. split; [reflexivity|]. split; [exact HR|]. split; [discriminate|].
      split; [intros; reflexivity | reflexivity]. }
    destruct (fx_step IM code F) as [s'| |c] eqn:Es.
    + injection H as <- <- <-. split; [cbn; lia|].
      split.
      { (* [comment removed for export] *)
        intros x Hx. exact (fx_step_wr_mono IM rho code F s' Es x Hx). }
      intros ms HR.
      destruct (fx_step_sound_frame segs IM rho Hrho0 code Hcode F ms s' HR Es)
        as (ms' & Hs & HR' & Hfr & _ & Hrom).
      exists ms'. split; [|split; [exact HR' | split; [discriminate | split; assumption]]].
      change (nat_of_int 1) with 1%nat. cbn [rsteps]. rewrite (R_svc _ _ _ _ _ HR), Hs. reflexivity.
    + injection H as <- <- <-. split; [cbn; lia|]. split; [intros x Hx; exact Hx|].
      intros ms HR. exists ms. split; [reflexivity|]. split; [exact HR|].
      split; [intros _; exact (fx_step_ecall segs IM rho code Hcode F ms HR Es)|].
      split; [intros; reflexivity | reflexivity].
    + injection H as <- <- <-. split; [cbn; lia|]. split; [intros x Hx; exact Hx|].
      intros ms HR. exists ms. split; [reflexivity|]. split; [exact HR|]. split; [discriminate|].
      split; [intros; reflexivity | reflexivity].
  - cbn [fx_run] in H. destruct (fx_run IM code bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (IH _ _ _ _ ltac:(lia) E1) as (Hb1 & Hmono1 & IH1).
    assert (Hpow : 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
    assert (Hlt : 2 ^ Z.of_nat (S k) <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia).
    destruct (stop_is_fuel r1) eqn:Er.
    + destruct (fx_run IM code bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      destruct (IH _ _ _ _ ltac:(lia) E2) as (Hb2 & Hmono2 & IH2).
      pose proof (Uint63.to_Z_bounded n1). pose proof (Uint63.to_Z_bounded n2).
      assert (Hadd : to_Z (n1 + n2)%uint63 = to_Z n1 + to_Z n2).
      { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2^63). lia. }
      split; [rewrite Hadd; lia|].
      split; [intros x Hx; apply Hmono1, Hmono2, Hx|].
      intros ms HR.
      destruct (IH1 ms HR) as (ms1 & Hn1 & HR1 & _ & Hfr1 & Hrom1).
      destruct (IH2 ms1 HR1) as (ms2 & Hn2 & HR2 & Hec2 & Hfr2 & Hrom2).
      exists ms2. split; [|split; [exact HR2 | split; [exact Hec2 | split]]].
      * unfold nat_of_int. rewrite Hadd, Z2Nat.inj_add by lia.
        exact (rsteps_trans segs _ _ _ _ _ Hn1 Hn2).
      * intros x Hx. rewrite Hfr2; [apply Hfr1; exact Hx|].
        intros Hc. apply Hx, Hmono1, Hc.
      * rewrite Hrom2. exact Hrom1.
    + injection H as <- <- <-. split; [lia|]. split; [exact Hmono1|]. intros ms HR.
      destruct (IH1 ms HR) as (ms1 & Hn1 & HR1 & Hec1 & Hfr1 & Hrom1).
      exists ms1. split; [exact Hn1 | split; [exact HR1 | split; [exact Hec1 | split; assumption]]].
Qed.

(* [comment removed for export] *)
Theorem fx_run_sound_shape : forall bp k F F' r cnt,
  (k <= 61)%nat ->
  fx_run IM code bp k F = (F', r, cnt) ->
  forall ms, Rr F ms ->
  exists ms', rsteps segs (nat_of_int cnt) ms = MachineOk ms' /\ Rr F' ms'
              /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms.
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt Hk H.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63.
    { injection H as <- <- <-. intros ms HR. exists ms. split; [reflexivity|]. split; [exact HR|].
      split; reflexivity. }
    destruct (fx_step IM code F) as [s'| |c] eqn:Es.
    + injection H as <- <- <-. intros ms HR.
      destruct (fx_step_sound_full segs IM rho Hrho0 code Hcode F ms s' HR Es)
        as (ms' & Hs & HR' & _ & _ & _ & Hfr & Hfc).
      exists ms'. split; [|split; [exact HR' | split; assumption]].
      change (nat_of_int 1) with 1%nat. cbn [rsteps]. rewrite (R_svc _ _ _ _ _ HR), Hs. reflexivity.
    + injection H as <- <- <-. intros ms HR. exists ms. split; [reflexivity|]. split; [exact HR|].
      split; reflexivity.
    + injection H as <- <- <-. intros ms HR. exists ms. split; [reflexivity|]. split; [exact HR|].
      split; reflexivity.
  - cbn [fx_run] in H. destruct (fx_run IM code bp k F) as [[s1 r1] n1] eqn:E1.
    pose proof (IH _ _ _ _ ltac:(lia) E1) as IH1.
    destruct (fx_run_sound_frame bp k F s1 r1 n1 ltac:(lia) E1) as (Hb1 & _ & _).
    assert (Hpow : 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
    assert (Hlt : 2 ^ Z.of_nat (S k) <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia).
    destruct (stop_is_fuel r1) eqn:Er.
    + destruct (fx_run IM code bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      pose proof (IH _ _ _ _ ltac:(lia) E2) as IH2.
      destruct (fx_run_sound_frame bp k s1 s2 r2 n2 ltac:(lia) E2) as (Hb2 & _ & _).
      pose proof (Uint63.to_Z_bounded n1). pose proof (Uint63.to_Z_bounded n2).
      assert (Hadd : to_Z (n1 + n2)%uint63 = to_Z n1 + to_Z n2).
      { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2^63). lia. }
      intros ms HR.
      destruct (IH1 ms HR) as (ms1 & Hn1 & HR1 & Hfr1 & Hfc1).
      destruct (IH2 ms1 HR1) as (ms2 & Hn2 & HR2 & Hfr2 & Hfc2).
      exists ms2. split; [|split; [exact HR2 | split; congruence]].
      unfold nat_of_int. rewrite Hadd, Z2Nat.inj_add by lia.
      exact (rsteps_trans segs _ _ _ _ _ Hn1 Hn2).
    + injection H as <- <- <-. exact IH1.
Qed.
End Run.
