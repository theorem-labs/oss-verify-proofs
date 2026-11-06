(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Frame Exec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxCellFrame FxRoFrame I2Canon.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mrel (m m' : word -> option byte) : Prop :=
  wmono segs m m'
  /\ (mem_inv segs m -> mem_inv segs m')
  /\ (forall x b, mrd segs m x = Some b -> exists b', mrd segs m' x = Some b').

Lemma mrel_refl : forall m, mrel m m.
Proof. intros m. split; [apply wmono_refl|]. split; [intros H; exact H|]. intros x b H. exists b. exact H. Qed.

Lemma mrel_trans : forall m1 m2 m3, mrel m1 m2 -> mrel m2 m3 -> mrel m1 m3.
Proof.
  intros m1 m2 m3 (W1 & I1 & R1) (W2 & I2 & R2). split; [eapply wmono_trans; eassumption|].
  split; [intros H; apply I2, I1, H|].
  intros x b H. destruct (R1 x b H) as [b' H']. exact (R2 x b' H').
Qed.

Lemma write_to_mem_none : forall bs m a x, write_to_mem m a bs x = None -> m x = None.
Proof.
  induction bs as [|b bs IH]; intros m a x H; cbn [write_to_mem] in H; [exact H|].
  apply IH in H. unfold bv_eqb in H. destruct (Z.eqb (bv_unsigned x) (bv_unsigned a)); [discriminate | exact H].
Qed.

Lemma mrel_write : forall m a bs,
  store_ok segs m a (length bs) = true -> mrel m (write_to_mem m a bs).
Proof.
  intros m a bs Hok. split; [apply wmono_write; apply wmono_refl|].
  split; [intros Hinv; apply mem_inv_store; assumption|].
  intros x b H. unfold mrd in *.
  destruct (write_to_mem m a bs x) as [b'|] eqn:E; [exists b'; reflexivity|].
  rewrite (write_to_mem_none _ _ _ _ E) in H. exists b. exact H.
Qed.

Lemma interp_mrel : forall t m report,
  interp_eff_accesses segs t m = MachineOk report -> mrel m (snd (@access_value _ report)).
Proof.
  induction t as [c | c | c | c | c | c | n a k IH | n a v k IH]; intros m report H;
    cbn [interp_eff_accesses] in H; try discriminate H.
  - inversion H; subst. cbn. apply mrel_refl.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs |]; [| discriminate H].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r0 | |] eqn:E; try discriminate H.
    inversion H; subst. cbn [access_value]. exact (IH _ m r0 E).
  - destruct (store_ok segs m a (width_bytes n)) eqn:Hok; [| discriminate H].
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      as [r0 | |] eqn:E; try discriminate H.
    inversion H; subst. cbn [access_value].
    eapply mrel_trans; [| exact (IH _ r0 E)].
    apply mrel_write. rewrite length_Z_to_le_bytes. exact Hok.
Qed.

Lemma decode_exec_mrel : forall st w rep,
  decode_exec_accesses segs st w = MachineOk rep ->
  mrel (ms_mem st) (ms_mem (@access_value _ rep)) /\ ms_rom (@access_value _ rep) = ms_rom st.
Proof.
  intros st w rep H. unfold decode_exec_accesses in H.
  destruct (is_ecall w).
  - inversion H; subst. cbn. split; [apply mrel_refl | reflexivity].
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate H].
    match type of H with
    | context [interp_eff_accesses segs ?t ?m0] =>
        destruct (interp_eff_accesses segs t m0) as [r0 | |] eqn:E; try discriminate H;
        pose proof (interp_mrel _ _ _ E) as HM
    end.
    destruct r0 as [[c m'] acc]. cbn [access_value snd] in HM, H.
    inversion H; subst. cbn. split; [exact HM | reflexivity].
Qed.

Lemma step_mrel : forall ms ms',
  RiscvSemantics.step segs ms = MachineOk ms' -> mrel (ms_mem ms) (ms_mem ms') /\ ms_rom ms' = ms_rom ms.
Proof.
  intros ms ms' H. unfold RiscvSemantics.step, step_accesses in H.
  assert (Hdx : forall w, drop_access_report (decode_exec_accesses segs ms w) = MachineOk ms' ->
                         mrel (ms_mem ms) (ms_mem ms') /\ ms_rom ms' = ms_rom ms).
  { intros w Hw. destruct (decode_exec_accesses segs ms w) as [rep| |] eqn:E; try discriminate Hw.
    cbn [drop_access_report] in Hw. injection Hw as <-.
    exact (decode_exec_mrel ms w rep E). }
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (Hdx w H)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdx w H)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdx w H)|].
  unfold fetch_failure in H.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate H|].
  cbv zeta in H.
  match type of H with context [if ?b then MachineFault else MachineUnmodeled] => destruct b; discriminate H end.
Qed.

Lemma rsteps_mrel : forall n ms ms',
  rsteps segs n ms = MachineOk ms' -> mrel (ms_mem ms) (ms_mem ms') /\ ms_rom ms' = ms_rom ms.
Proof.
  induction n as [|n IH]; intros ms ms' H; cbn [rsteps] in H.
  - injection H as <-. split; [apply mrel_refl | reflexivity].
  - destruct (ms_svc_pending ms); [injection H as <-; split; [apply mrel_refl | reflexivity]|].
    destruct (RiscvSemantics.step segs ms) as [ms1| |] eqn:Hs; try discriminate H.
    destruct (step_mrel ms ms1 Hs) as [M1 R1]. destruct (IH ms1 ms' H) as [M2 R2].
    split; [eapply mrel_trans; eassumption | congruence].
Qed.

Lemma rsteps_msteps : forall n ms ms',
  rsteps segs n ms = MachineOk ms' -> msteps segs ms ms'.
Proof.
  induction n as [|n IH]; intros ms ms' H; cbn [rsteps] in H.
  - injection H as <-. apply msteps_refl.
  - destruct (ms_svc_pending ms) eqn:Hsvc; [injection H as <-; apply msteps_refl|].
    destruct (RiscvSemantics.step segs ms) as [ms1| |] eqn:Hs; try discriminate H.
    eapply msteps_cons; [split; [exact Hsvc | exact Hs] | exact (IH ms1 ms' H)].
Qed.

Lemma mrel_stk : forall m m' lo hi, mrel m m' -> stk segs m lo hi -> stk segs m' lo hi.
Proof.
  intros m m' lo hi (W & _ & Rd) (H1 & H2 & H). split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply W; exact Hw | exact (Rd _ _ Hb)].
Qed.

Lemma mrel_mrd : forall m m' x b, mrel m m' -> mrd segs m x = Some b -> exists b', mrd segs m' x = Some b'.
Proof. intros m m' x b (_ & _ & Rd) H. exact (Rd x b H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable IM : fimage.
Variable code : itrie finstr.
Variable RO : itrie unit.
Hypothesis Hcode : code_ok segs code.

Theorem fx_run_pkg : forall n rho bp k F F' r cnt ms,
  (k <= 61)%nat ->
  fx_run IM code RO bp k F = (F', r, cnt) ->
  rho 0%uint63 = Z_to_bv 64 0 ->
  Rn segs IM n rho F ms ->
  ro_in_r0 RO (f_mem F) ->
  canonR (ms_regs ms) ->
  exists ms',
       rsteps segs (nat_of_int cnt) ms = MachineOk ms'
    /\ msteps segs ms ms'
    /\ Rn segs IM n rho F' ms'
    /\ (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms'))
    /\ ms_rom ms' = ms_rom ms /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms
    /\ mrel (ms_mem ms) (ms_mem ms')
    /\ (forall x, ~ cell_expl rho (f_mem F') x -> ms_mem ms' x = ms_mem ms x)
    /\ (forall x, ro_byte RO x -> ms_mem ms' x = ms_mem ms x)
    /\ ro_in_r0 RO (f_mem F')
    /\ canonR (ms_regs ms').
Proof.
  intros n rho bp k F F' r cnt ms Hk Hrun Hrho0 HRn Hro HC.
  assert (Hag : agree n rho rho) by (split; [exact Hrho0 | intros; reflexivity]).
  pose proof (HRn rho Hag) as HR.
  destruct (fx_run_Rn segs IM code RO Hcode n rho bp k F F' r cnt ms Hk Hrun Hrho0 HRn)
    as (ms' & Hsteps & HRn' & Hec & _ & _ & Hrom).
  destruct (fx_run_Rn_shape segs IM code RO Hcode n rho bp k F F' r cnt ms ms' Hk Hrun Hrho0 HRn Hsteps) as [Hfr Hfc].
  exists ms'. split; [exact Hsteps|]. split; [exact (rsteps_msteps _ _ _ Hsteps)|].
  split; [exact HRn'|]. split; [exact Hec|]. split; [exact Hrom|]. split; [exact Hfr|]. split; [exact Hfc|].
  split; [exact (proj1 (rsteps_mrel _ _ _ Hsteps))|].
  split; [exact (fx_run_cellframe segs IM rho Hrho0 code RO Hcode bp k F F' r cnt Hk Hrun ms ms' HR Hsteps)|].
  split; [exact (fx_run_roframe segs IM rho Hrho0 code RO Hcode bp k F F' r cnt Hk Hrun ms ms' HR Hro Hsteps)|].
  split; [exact (fx_run_ro_in_r0 IM code RO bp k F F' r cnt Hrun Hro)|].
  exact (fx_run_canon segs IM rho Hrho0 code RO Hcode bp k F F' r cnt Hk Hrun ms ms' HR Hsteps HC).
Qed.
End WithSegs.
