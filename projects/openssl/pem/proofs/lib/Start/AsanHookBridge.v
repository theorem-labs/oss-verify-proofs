(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec CatSim StoreOk AsanAcct RegEqv.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Exec MState Frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module HBR.

(* [comment removed for export] *)
Definition canon (R : bvmap 5 word) : bvmap 5 word :=
  Frame.mkR (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4)) (getr R (Z_to_bv 5 5))
      (getr R (Z_to_bv 5 6)) (getr R (Z_to_bv 5 7)) (getr R (Z_to_bv 5 8)) (getr R (Z_to_bv 5 9)) (getr R (Z_to_bv 5 10))
      (getr R (Z_to_bv 5 11)) (getr R (Z_to_bv 5 12)) (getr R (Z_to_bv 5 13)) (getr R (Z_to_bv 5 14)) (getr R (Z_to_bv 5 15))
      (getr R (Z_to_bv 5 16)) (getr R (Z_to_bv 5 17)) (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19)) (getr R (Z_to_bv 5 20))
      (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22)) (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24)) (getr R (Z_to_bv 5 25))
      (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27)) (getr R (Z_to_bv 5 28)) (getr R (Z_to_bv 5 29)) (getr R (Z_to_bv 5 30))
      (getr R (Z_to_bv 5 31)).

Lemma reg_cases : forall r : bv 5, r <> 0%bv -> exists k, 1 <= k <= 31 /\ r = Z_to_bv 5 k.
Proof.
  intros r Hr. exists (bv_unsigned r). split.
  - pose proof (bv_unsigned_in_range 5 r) as Hb. unfold bv_modulus in Hb. cbn in Hb.
    destruct (Z.eq_dec (bv_unsigned r) 0) as [E0|E0]; [|lia]. exfalso. apply Hr. apply bv_eq. rewrite E0. reflexivity.
  - symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma canon_eqv : forall R, regs_eqv (canon R) R.
Proof.
  intros R r Hr. destruct (reg_cases r Hr) as (k & Hk & ->).
  assert (Hk' : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12
                \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23
                \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
  unfold canon, getr.
  repeat (destruct Hk' as [-> | Hk']); try (subst k); reflexivity.
Qed.

Section Bridge.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma interp_grows : forall t m r, interp_eff_accesses segs t m = MachineOk r -> mem_grows m (snd (access_value _ r)).
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r H; cbn [interp_eff_accesses] in H; try discriminate.
  - injection H as <-. cbn. apply mem_grows_refl.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep| |] eqn:E; try discriminate.
    injection H as <-. cbn [access_value]. exact (IH _ m rep E).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [rep| |] eqn:E; try discriminate.
    injection H as <-. cbn [access_value].
    eapply mem_grows_trans; [apply write_to_mem_grows | exact (IH _ rep E)].
Qed.

Lemma dea_grows : forall ms w r, decode_exec_accesses segs ms w = MachineOk r -> mem_grows (ms_mem ms) (ms_mem (access_value _ r)).
Proof.
  intros ms w r H. unfold decode_exec_accesses in H. destruct (is_ecall w).
  - injection H as <-. cbn. apply mem_grows_refl.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    destruct (interp_eff_accesses segs _ _) as [rep| |] eqn:E; try discriminate.
    pose proof (interp_grows _ _ _ E) as G. destruct rep as [[c1 m1] rs1]. cbn [access_value accessed_ranges snd] in *.
    injection H as <-. cbn. exact G.
Qed.

Lemma step_grows : forall ms ms', RiscvSemantics.step segs ms = MachineOk ms' -> mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' H. unfold RiscvSemantics.step, drop_access_report in H.
  destruct (step_accesses segs ms) as [rep| |] eqn:Hs; try discriminate. injection H as <-.
  unfold step_accesses in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (dea_grows ms w rep Hs)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (dea_grows ms w rep Hs)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (dea_grows ms w rep Hs)|].
  exfalso. destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) eqn:Hf; try discriminate.
  unfold fetch_failure in Hf.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  match type of Hf with (if ?c then _ else _) = _ => destruct c; discriminate end.
Qed.

Lemma msteps_grows : forall ms ms', CatSim.msteps segs ms ms' -> mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hstep Hrest IH]; [apply mem_grows_refl|].
  eapply mem_grows_trans; [exact (step_grows _ _ Hstep) | exact IH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exec_msteps : forall a b, Exec.msteps segs a b -> CatSim.msteps segs a b.
Proof.
  intros a b H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] Hrest IH]; [apply CatSim.mst_refl|].
  eapply CatSim.mst_step; [exact Hsvc | exact Hstep | exact IH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma step_eqv : forall ms1 ms2 ms1', ms_eqv ms1 ms2 -> RiscvSemantics.step segs ms1 = MachineOk ms1' ->
  exists ms2', RiscvSemantics.step segs ms2 = MachineOk ms2' /\ ms_eqv ms1' ms2'.
Proof.
  intros ms1 ms2 ms1' He H. pose proof (step_accesses_eqv segs ms1 ms2 He) as X.
  unfold RiscvSemantics.step, drop_access_report in *.
  destruct (step_accesses segs ms1) as [r1| |]; try discriminate. injection H as <-.
  destruct (step_accesses segs ms2) as [r2| |]; cbn [mres_eqv] in X; try contradiction.
  destruct X as [_ X]. exists (access_value _ r2). split; [reflexivity | exact X].
Qed.

Lemma msteps_eqv : forall ms1 ms1', CatSim.msteps segs ms1 ms1' -> forall ms2, ms_eqv ms1 ms2 ->
  exists ms2', CatSim.msteps segs ms2 ms2' /\ ms_eqv ms1' ms2'.
Proof.
  intros ms1 ms1' H. induction H as [ms | ms msa msb Hsvc Hstep Hrest IH]; intros ms2 He.
  - exists ms2. split; [apply CatSim.mst_refl | exact He].
  - destruct (step_eqv ms ms2 msa He Hstep) as (ms2a & Hs2 & He2).
    destruct (IH ms2a He2) as (ms2' & Hr & He').
    exists ms2'. split; [|exact He'].
    eapply CatSim.mst_step; [| exact Hs2 | exact Hr].
    destruct He as (_ & _ & _ & Hsv & _). rewrite <- Hsv. exact Hsvc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Lift.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Lemma munrestrict_idem : forall full x y, munrestrict H (munrestrict H full x) y = munrestrict H full y.
Proof. intros full x y. apply functional_extensionality. intro a. unfold munrestrict. destruct (H a); reflexivity. Qed.

Lemma msteps_unrestrict : forall msr msr', CatSim.msteps segs msr msr' -> forall ms, msr = restrict H ms ->
  CatSim.msteps segs ms (unrestrict H (ms_mem ms) msr').
Proof.
  intros msr msr' Hm. induction Hm as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH]; intros ms ->.
  - rewrite unrestrict_restrict. apply CatSim.mst_refl.
  - destruct (step_restrict_sound segs H HH Hwx ms msr1 Hstep) as (rep & Hsa & Hv & _ & _ & Hre).
    assert (Hst : RiscvSemantics.step segs ms = MachineOk (unrestrict H (ms_mem ms) msr1)).
    { unfold RiscvSemantics.step, drop_access_report. rewrite Hsa, Hv. reflexivity. }
    pose proof (IH (unrestrict H (ms_mem ms) msr1) (eq_sym Hre)) as X.
    replace (unrestrict H (ms_mem (unrestrict H (ms_mem ms) msr1)) msr2) with (unrestrict H (ms_mem ms) msr2) in X.
    2:{ unfold unrestrict. cbn [ms_mem]. rewrite munrestrict_idem. reflexivity. }
    eapply CatSim.mst_step; [| exact Hst | exact X]. rewrite restrict_svc_pending in Hsvc. exact Hsvc.
Qed.

(* [comment removed for export] *)
Theorem evt_bridge : forall (Q : machine_state -> Prop) regs pc M rom,
  Exec.evt segs Q (MState.MS (canon regs) bvmap_empty pc (Z_to_bv 32 0) None (mrestrict H M) rom) ->
  exists ms1 ms2,
    Q ms1
    /\ CatSim.msteps segs (mkst regs pc M rom) ms2
    /\ regs_eqv (ms_regs ms1) (ms_regs ms2)
    /\ ms_fregs ms2 = ms_fregs ms1 /\ ms_pc_val ms2 = ms_pc_val ms1 /\ ms_svc_pending ms2 = ms_svc_pending ms1
    /\ ms_resv ms2 = ms_resv ms1 /\ ms_fcsr ms2 = ms_fcsr ms1 /\ ms_rom ms2 = ms_rom ms1
    /\ ms_mem ms2 = munrestrict H M (ms_mem ms1)
    /\ mem_grows (mrestrict H M) (ms_mem ms1).
Proof.
  intros Q regs pc M rom (ms1 & Hrun & HQ).
  apply exec_msteps in Hrun.
  pose proof (msteps_grows _ _ Hrun) as HG. cbn [MState.MS ms_mem] in HG.
  assert (He : ms_eqv (MState.MS (canon regs) bvmap_empty pc (Z_to_bv 32 0) None (mrestrict H M) rom) (restrict H (mkst regs pc M rom))).
  { unfold MState.MS, restrict, mkst. cbn. repeat split; try reflexivity. apply canon_eqv. }
  destruct (msteps_eqv _ _ Hrun _ He) as (ms2 & Hrun2 & He2).
  pose proof (msteps_unrestrict _ _ Hrun2 (mkst regs pc M rom) eq_refl) as Hrun3. cbn [mkst ms_mem] in Hrun3.
  destruct He2 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  exists ms1, (unrestrict H M ms2).
  split; [exact HQ|]. split; [exact Hrun3|]. unfold unrestrict. cbn.
  repeat split; try (symmetry; assumption); try assumption.
  rewrite E7. reflexivity.
Qed.

Lemma mkst_eta : forall ms, ms_fregs ms = bvmap_empty -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = Z_to_bv 32 0 ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4. cbn in *. subst. reflexivity. Qed.

End Lift.
End Bridge.
End HBR.
