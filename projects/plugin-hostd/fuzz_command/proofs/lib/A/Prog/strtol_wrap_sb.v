From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Spec Require Import CType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import __intscan_c asan_memcpy_bz.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.strtol_c.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.strtol.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.__shlim.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.__intscan.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.__errno_location.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.I_strtolw.
Import ListNotations.
Open Scope Z_scope.

Module AMC := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.asan_memcpy_bz.
Module SCc := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.strtol_c.
Module SCp := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.strtol.
Module SHL := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.__shlim.
Module ISp := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.__intscan.
Module ERL := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.__errno_location.
Module BzS := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.I_strtolw.

(* Cross-module cell conversions for the user endptr (C8) and the errno cell (C4), mirroring
   AMC.rw_cb_to_bz / AMC.rw_cb_of_bz / AMC.rw_cb_normalize / AMC.rw_cb_of_normalized. *)

Lemma rw_c8_to_bz : forall m a v, rw_cells rsegs m a [C8 v] -> BzSt.rw_cells BzI.asegs m a [BzCl.C8 v].
Proof. intros m a v ((Hwf & HB) & HW). split; [split|]; [exact Hwf | exact HB | exact HW]. Qed.
Lemma rw_c4_to_bz : forall m a v, rw_cells rsegs m a [C4 v] -> BzSt.rw_cells BzI.asegs m a [BzCl.C4 v].
Proof. intros m a v ((Hwf & HB) & HW). split; [split|]; [exact Hwf | exact HB | exact HW]. Qed.
Lemma rw_c8_of_bz : forall m a v, BzSt.rw_cells BzI.asegs m a [BzCl.C8 v] -> rw_cells rsegs m a [C8 v].
Proof. intros m a v ((Hwf & HB) & HW). split; [split|]; [exact Hwf | exact HB | exact HW]. Qed.
Lemma rw_c4_of_bz : forall m a v, BzSt.rw_cells BzI.asegs m a [BzCl.C4 v] -> rw_cells rsegs m a [C4 v].
Proof. intros m a v ((Hwf & HB) & HW). split; [split|]; [exact Hwf | exact HB | exact HW]. Qed.

Definition strtol_contract_proof : SCc.strtol_contract :=
  SCp.strtol_holds SHL.__shlim_holds (ISp.__intscan_holds ERL.__errno_location_holds SHL.__shlim_holds).

Lemma sb_proof : BzS.strtol_body_stmt (fun s => Z_to_bv 64 (s10_val s)) s10_end (fun s e => s10_errno s e).
Proof.
  unfold BzS.strtol_body_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A Ep str ev can e0 lo
    STR HP EP0 ECELL ERR GOT CAN ST HLO SEPS SEPE SEPT SEPET SEPGO SEPGU SEPGT SEPGE MI HEEND.
  assert (SPUB : bv_unsigned sp <= BzM.UTOP).
  { pose proof ST as (L0 & HH & SA). destruct (SA (bv_unsigned sp - 1) ltac:(lia)) as (W & _).
    pose proof (BzM.wview_below BzI.asegs m _ MI W) as H. rewrite BzM.wa_unsigned in H by lia. lia. }
  assert (EB : (Ep + 8 <= 2 ^ 64)%Z).
  { pose proof (BzSt.rw_cells_bound _ _ _ _ ECELL) as (_ & B).
    change (Z.of_nat (cells_size [C8 e0])) with 8%Z in B. exact B. }
  assert (TB : (bv_unsigned tp + -164 + 4 <= 2 ^ 64)%Z).
  { pose proof (BzSt.rw_cells_bound _ _ _ _ ERR) as (_ & B).
    change (Z.of_nat (cells_size [C4 ev])) with 4%Z in B. exact B. }
  assert (TLB : (0 <= bv_unsigned tp + -164)%Z).
  { pose proof (BzSt.rw_cells_bound _ _ _ _ ERR) as (L & _). exact L. }
  assert (EPUB : Ep + 8 <= BzM.UTOP).
  { destruct ECELL as (_ & (_ & _ & HW)).
    pose proof (HW 7 ltac:(cbn; lia)) as W.
    pose proof (BzM.wview_below BzI.asegs m _ MI W) as H.
    rewrite wa_unsigned in H by lia. lia. }
  assert (TPUB : bv_unsigned tp + -164 + 4 <= BzM.UTOP).
  { destruct ERR as (_ & (_ & _ & HW)).
    pose proof (HW 3 ltac:(cbn; lia)) as W.
    pose proof (BzM.wview_below BzI.asegs m _ MI W) as H.
    rewrite wa_unsigned in H by lia. lia. }
  apply AMC.evt_to_bz.
  apply (evt_mono rsegs (SCc.strtol_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A Ep str ev lo m)).
  - exact (strtol_contract_proof ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m A Ep str ev can e0 lo STR HP EP0 (rw_c8_of_bz _ _ _ ECELL) (rw_c4_of_bz _ _ _ ERR) GOT CAN ST HLO
             SEPS SEPE SEPT SEPET SEPGO SEPGU SEPGT SEPGE (AMC.mem_inv_of_bz m MI)).
  - intros st (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & ST' & RWEp & RWerr).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|].
    split; [exact MU|].
    split; [exact WM|].
    split.
    + apply BzM.mem_inv_intro; [intros x; exact (BzM.mem_inv_seg_below _ _ _ MI)|].
      intros x b Hx. split; [exact (MI' x b Hx)|].
      destruct (Z_lt_le_dec (bv_unsigned x) BzM.UTOP) as [L|L]; [exact L|].
      rewrite (MU x) in Hx by (cbn [outside]; repeat split; lia).
      exact (BzM.mem_inv_ov_below _ _ _ _ MI Hx).
    + split; [exact ST'|].
      split; [exact (rw_c8_to_bz _ _ _ RWEp) | exact (rw_c4_to_bz _ _ _ RWerr)].
Qed.
