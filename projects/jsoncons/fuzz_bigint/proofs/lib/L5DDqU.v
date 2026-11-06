(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3Sound AsanPlanCore Ub0_code_221b0_23098 BigContractUb0 BigLinkGlueUb0 BigLinkDqU BigLinkDivBaseU L5Defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5DDQU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition DDQ : Z := 0x22e6c.          (* [comment removed for export] *)
Definition DDQ_RET : Z := 0x22f64.
End SCFG_1.
      (* [comment removed for export] *)
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Section SCFG_2.
Context {SCFG_P : ScfgP}.


Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.

(* [comment removed for export] *)
Definition ddq_kept : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Definition ddq_post (M M' : word -> option byte) (R R' : bvmap 5 word) : Prop :=
  (forall i, In i ddq_kept -> getr R' (reg i) = getr R (reg i)) /\ regs_preserved R R' /\ M' = M.

Definition ddq_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (d r : Z),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr R 13%bv = Z_to_bv 64 d -> 2 ^ 63 <= d < 2 ^ 64 ->          (* [comment removed for export] *)
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    (forall (fx' : FPState) R' M', ddq_post M M' R R' -> srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model) K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx) R DDQ M model) K.

Lemma rl13 : (13%bv : bv 5) = reg 13. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl1 : (1%bv : bv 5) = reg 1. Proof. apply bv_eq. reflexivity. Qed.
Lemma ret_22e2c fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 0x22f64) M (seg_rom RSEGS)) (@mkst fx R (Z_to_bv 64 r) M (seg_rom RSEGS)).
Proof. intros H1 Hr He. apply (BDU.ret_to fx R M 0x22f64 W_22f64 r F_22f64 eq_refl D_22f64 H1 Hr He). Qed.

Lemma kept_regs_preserved R R' : (forall i, In i ddq_kept -> getr R' (reg i) = getr R (reg i)) -> regs_preserved R R'.
Proof.
  intros K x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply K.
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.

Theorem ddq_run (fx : FPState) R M (d r : Z) :
  getr R (reg 13) = Z_to_bv 64 d -> 2 ^ 63 <= d < 2 ^ 64 -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  exists (fx' : FPState) R' M', msteps RSEGS (@mkst fx R (Z_to_bv 64 DDQ) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 r) M' (seg_rom RSEGS))
    /\ ddq_post M M' R R'.
Proof.
  intros H13 Hd H1 [Hr He]. unfold DDQ.
  destruct (BDQU.ddq_run fx R M d ltac:(unfold BDQU.U; rewrite H13; apply BGU.unsigned_lit; lia) Hd) as (fx' & R' & M' & MS & K & MM & Hg).
  assert (EM: M' = M). { apply FunctionalExtensionality.functional_extensionality. exact MM. } subst M'.
  assert (K1: getr R' (reg 1) = Z_to_bv 64 r). { rewrite (K 1%nat) by (cbn; tauto). exact H1. }
  exists fx', R', M. split.
  - eapply msteps_trans. exact MS. apply (ret_22e2c fx' R' M r K1 Hr He).
  - split. { intros i Hi. apply K. exact Hi. } split. { apply kept_regs_preserved. intros i Hi; apply K; exact Hi. } reflexivity.
Qed.

Theorem ddq_ok : ddq_spec.
Proof.
  intros fx R M model K d r Hh Hl H13 Hd H1 Hra HK. unfold cfg.
  eapply (L5.run_cps RSEGS (fun _ R' M' => ddq_post M M' R R')). exact Hh. exact Hl.
  - rewrite rl13 in H13. rewrite rl1 in H1. exact (ddq_run fx R M d r H13 Hd H1 Hra).
  - intros fx' R' M' HP. apply HK. exact HP.
Qed.
End SCFG_2.

End L5DDQU.
