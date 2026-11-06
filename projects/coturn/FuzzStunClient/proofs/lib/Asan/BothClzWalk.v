(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefEnframeArith AgentLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import Both_code_clz BothRegionPoisoned AsanClzArith.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefReadLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.BothRegionPoisoned.gr ::= gr_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Definition CLZ_ENTRY : Z := 0x38288.
Definition CLZ_EXIT : Z := 0x38330.

Lemma urd : forall t, bv_unsigned (Z_to_bv 64 t) = rd t.
Proof. intros. rewrite Z_to_bv_unsigned. rewrite bv_wrap64_mod. reflexivity. Qed.

(* [comment removed for export] *)
Lemma k55a : v_addiw (v_lui (349525 ≪ 12)) 1365 = Z_to_bv 64 0x55555555.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma k33a : v_addiw (v_lui (209715 ≪ 12)) 819 = Z_to_bv 64 0x33333333.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma k0fa : v_addiw (v_lui (61681 ≪ 12)) (-241) = Z_to_bv 64 0x0f0f0f0f.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma k01a : v_addiw (v_lui (4112 ≪ 12)) 257 = Z_to_bv 64 0x01010101.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma k55b : v_add (Z_to_bv 64 0x55555555) (v_slli (Z_to_bv 64 0x55555555) 32) = Z_to_bv 64 M55.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma k33b : v_add (Z_to_bv 64 0x33333333) (v_slli (Z_to_bv 64 0x33333333) 32) = Z_to_bv 64 M33.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma k0fb : v_add (Z_to_bv 64 0x0f0f0f0f) (v_slli (Z_to_bv 64 0x0f0f0f0f) 32) = Z_to_bv 64 M0F.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma k01b : v_add (Z_to_bv 64 0x01010101) (v_slli (Z_to_bv 64 0x01010101) 32) = Z_to_bv 64 M01.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma kff : bv_wrap 64 (-1) = MFF.
Proof. vm_compute. reflexivity. Qed.

Section CLZ.
  Variables (mem rom : word -> option byte) (x L : Z) (v : word).
  Hypothesis Hx : (1 <= x < 2 ^ 64)%Z.
  Hypothesis HL : (0 <= L)%Z /\ (L + 56 <= 2 ^ 64)%Z.
  Hypothesis Hrd : rdn SEGS mem (Z_to_bv 64 (L + 48)) 8 = Some (word_to_le_bytes 8 v).

  (* [comment removed for export] *)
  Ltac ushift := unfold v_srli at 1; rewrite urd.
  Ltac uor t := unfold v_or at 1; rewrite !urd;
              match goal with |- context [Z_to_bv 64 (Z.lor (rd ?a) (rd (Z.shiftr (rd ?a) ?n)))] =>
                change (Z.lor (rd a) (rd (Z.shiftr (rd a) n))) with (stepw a n) end.

  #[using="Hx HL Hrd"] Theorem clz_walk_S : forall regs,
    getr regs 18 = Z_to_bv 64 x -> getr regs 9 = Z_to_bv 64 L ->
    exists regs',
      msteps SEGS (mkst regs (0x38288 : word) mem rom) (mkst regs' (0x38330 : word) mem rom)
      /\ getr regs' 19 = Z_to_bv 64 (63 - Z.log2 x)
      /\ getr regs' 14 = v
      /\ (forall r, r <> 11 -> r <> 12 -> r <> 14 -> r <> 15 -> r <> 16 -> r <> 19 -> getr regs' r = getr regs r).
  Proof.
    intros regs H18 H9.
    eexists. split; [|split; [|split]].
    - (* [comment removed for export] *)
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_38288 eq_refl D_38288)). gr. rewrite H18. ushift.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_3828c eq_refl D_3828c)). gr.
      mstep ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_38290 eq_refl D_38290)). gr.
      mstep ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_38294 eq_refl D_38294)). gr.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_38298 eq_refl D_38298)). gr. rewrite H18. uor x.
      set (s1v := stepw x 1).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_3829c eq_refl D_3829c)). gr. rewrite k55a.
      mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_382a0 eq_refl D_382a0)). gr. rewrite k33a.
      mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_382a4 eq_refl D_382a4)). gr. rewrite k0fa.
      (* [comment removed for export] *)
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_382a8 eq_refl D_382a8)). gr. ushift.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_382ac eq_refl D_382ac)). gr. uor s1v.
      set (s2v := stepw s1v 2).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_382b0 eq_refl D_382b0)). gr.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_382b4 eq_refl D_382b4)). gr. rewrite k55b.
      mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_382b8 eq_refl D_382b8)). gr.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_382bc eq_refl D_382bc)). gr. rewrite k33b.
      mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_382c0 eq_refl D_382c0)). gr.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_382c4 eq_refl D_382c4)). gr. rewrite k0fb.
      (* [comment removed for export] *)
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_382c8 eq_refl D_382c8)). gr. ushift.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_382cc eq_refl D_382cc)). gr. uor s2v.
      set (s3v := stepw s2v 4).
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_382d0 eq_refl D_382d0)). gr. ushift.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_382d4 eq_refl D_382d4)). gr. uor s3v.
      set (s4v := stepw s3v 8).
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_382d8 eq_refl D_382d8)). gr. ushift.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_382dc eq_refl D_382dc)). gr. uor s4v.
      set (s5v := stepw s4v 16).
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_382e0 eq_refl D_382e0)). gr. ushift.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_382e4 eq_refl D_382e4)). gr. uor s5v.
      set (sm := stepw s5v 32).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_382e8 eq_refl D_382e8)). gr.
      unfold v_xori at 1. rewrite urd, kff. set (nv := Z.lxor (rd sm) MFF).
      (* [comment removed for export] *)
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_382ec eq_refl D_382ec)). gr. ushift.
      mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_382f0 eq_refl D_382f0)). gr. unfold v_and at 1. rewrite !urd.
      set (a2v := Z.land (rd (Z.shiftr (rd nv) 1)) (rd M55)).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_382f4 eq_refl D_382f4)). gr.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_sub _ _ _ _ _ _ _ _ _ F_382f8 eq_refl D_382f8)). gr. unfold v_sub at 1. rewrite !urd.
      set (dv := (rd nv - rd a2v)%Z).
      (* [comment removed for export] *)
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_382fc eq_refl D_382fc)). gr. ushift.
      mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_38300 eq_refl D_38300)). gr. unfold v_and at 1. rewrite !urd.
      set (e1 := Z.land (rd dv) (rd M33)).
      mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_38304 eq_refl D_38304)). gr. unfold v_and at 1. rewrite !urd.
      set (e2 := Z.land (rd (Z.shiftr (rd dv) 2)) (rd M33)).
      (* [comment removed for export] *)
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ v F_38308 eq_refl D_38308);
                   [ gr; rewrite H9; zn; exact Hrd | apply bytes_le_to_Z_8 ]).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_3830c eq_refl D_3830c)). gr. rewrite k01a.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_38310 eq_refl D_38310)). gr. unfold v_add at 1. rewrite !urd.
      set (fv := (rd e1 + rd e2)%Z).
      (* [comment removed for export] *)
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_38314 eq_refl D_38314)). gr. ushift.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_38318 eq_refl D_38318)). gr. unfold v_add at 1. rewrite !urd.
      set (gv := (rd fv + rd (Z.shiftr (rd fv) 4))%Z).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_3831c eq_refl D_3831c)). gr.
      mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_38320 eq_refl D_38320)). gr. unfold v_and at 1. rewrite !urd.
      set (hv := Z.land (rd gv) (rd M0F)).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_38324 eq_refl D_38324)). gr. rewrite k01b.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_mul _ _ _ _ _ _ _ _ _ F_38328 eq_refl D_38328)). gr. unfold v_mul at 1. rewrite !urd.
      set (pv := (rd hv * rd M01)%Z).
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_3832c eq_refl D_3832c)). gr. ushift.
      apply mst_refl.
    - (* [comment removed for export] *)
      gr. f_equal. etransitivity; [|apply clz_log2; unfold two64; lia].
      cbv delta [clz tailw smearw]. cbv zeta. reflexivity.
    - (* [comment removed for export] *) gr. reflexivity.
    - gr. intros r N11 N12 N14 N15 N16 N19.
      repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
  Qed.
End CLZ.

(* [comment removed for export] *)
Theorem clz_walk :
  forall (mem rom : word -> option byte) (x L : Z) (v : word),
  (1 <= x < 2 ^ 64)%Z -> (0 <= L)%Z /\ (L + 56 <= 2 ^ 64)%Z ->
  rdn SEGS mem (Z_to_bv 64 (L + 48)) 8 = Some (word_to_le_bytes 8 v) ->
  forall regs, getr regs 18 = Z_to_bv 64 x -> getr regs 9 = Z_to_bv 64 L ->
  exists regs',
    msteps SEGS (mkst regs (0x38288 : word) mem rom) (mkst regs' (0x38330 : word) mem rom)
    /\ getr regs' 19 = Z_to_bv 64 (63 - Z.log2 x)
    /\ getr regs' 14 = v
    /\ (forall r, r <> 11 -> r <> 12 -> r <> 14 -> r <> 15 -> r <> 16 -> r <> 19 -> getr regs' r = getr regs r).
Proof.
  intros mem rom x L v Hx HL Hrd regs H18 H9. exact (clz_walk_S mem rom x L v Hx HL Hrd regs H18 H9).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BSL_ENTRY : Z := 0x3837c.
Definition BSL_EXIT : Z := 0x38394.

Section BSL.
  Variables (mem rom : word -> option byte) (L idx : Z) (a2w : word) (bs : list byte).
  Hypothesis HL : (0 <= L)%Z /\ (L + 624 <= 2 ^ 64)%Z.        (* [comment removed for export] *)
  Hypothesis Hidx : (0 <= idx <= 63)%Z.
  Definition W : Z := (L + 104 + 8 * idx)%Z.
  Hypothesis Hrd : rdn SEGS mem (Z_to_bv 64 W) 8 = Some bs.
  Hypothesis Hlen : length bs = 8%nat.
  Hypothesis Hok96 : forall j, (0 <= j < 8)%Z -> store_ok SEGS mem (Z_to_bv 64 (L + 96 + j)) 1 = true.
  Hypothesis HokW : forall j, (0 <= j < 8)%Z -> store_ok SEGS mem (Z_to_bv 64 (W + j)) 1 = true.

  Definition oldv : word := Z_to_bv 64 (bytes_le_to_Z bs).
  Definition newv : word := Z_to_bv 64 (bytes_le_to_Z bs + 1).
  Definition mem1 : word -> option byte := wbytes mem (Z_to_bv 64 (L + 96)) (word_to_le_bytes 8 a2w).
  Definition bsl_mem : word -> option byte := wbytes mem1 (Z_to_bv 64 W) (word_to_le_bytes 8 newv).

  #[using="rom a2w Hlen"] Lemma bs_range : (0 <= bytes_le_to_Z bs < 2 ^ 64)%Z.
  Proof. pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs). rewrite Hlen in B. change (8 * Z.of_nat 8)%Z with 64%Z in B. lia. Qed.

  #[using="HL Hidx Hrd Hlen Hok96 HokW"] Theorem bsl_walk_S : forall regs,
    getr regs 9 = Z_to_bv 64 L -> getr regs 11 = Z_to_bv 64 idx -> getr regs 12 = a2w ->
    exists regs',
      msteps SEGS (mkst regs (0x3837c : word) mem rom) (mkst regs' (0x38394 : word) bsl_mem rom)
      /\ (forall r, r <> 11 -> r <> 13 -> getr regs' r = getr regs r).
  Proof.
    intros regs H9 H11 H12. pose proof bs_range as BR. unfold W in *.
    eexists. split.
    - (* [comment removed for export] *)
      mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_3837c eq_refl D_3837c)). gr. rewrite H11.
      rewrite (v_slli_lit idx 3) by (try lia; change (2 ^ 3)%Z with 8%Z; lia). change (2 ^ 3)%Z with 8%Z.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_38380 eq_refl D_38380)). gr. rewrite H9. rewrite v_add_zbv by lia.
      (* [comment removed for export] *)
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ oldv F_38384 eq_refl D_38384);
                   [ gr; imm_norm; zn; replace (L + idx * 8 + 104)%Z with (L + 104 + 8 * idx)%Z by lia; exact Hrd
                   | unfold oldv; rewrite u64_lit by lia; reflexivity ]).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_38388 eq_refl D_38388)). gr. unfold oldv. zn.
      change (Z_to_bv 64 (bytes_le_to_Z bs + 1)) with newv.
      (* [comment removed for export] *)
      mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (L + 96)) a2w F_3838c eq_refl D_3838c);
                   [ gr; rewrite H9; zn; reflexivity
                   | gr; exact H12
                   | apply store_ok8_bytes; [lia | lia | exact Hok96] ]).
      change (wbytes mem (Z_to_bv 64 (L + 96)) (word_to_le_bytes 8 a2w)) with mem1.
      (* [comment removed for export] *)
      mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (L + 104 + 8 * idx)) newv F_38390 eq_refl D_38390);
                   [ gr; imm_norm; zn; apply (f_equal (Z_to_bv 64)); lia
                   | gr; reflexivity
                   | apply store_ok8_bytes; [lia | lia | intros j Hj; unfold mem1; apply store_ok1_wbytes; apply HokW; exact Hj] ]).
      apply mst_refl.
    - gr. intros r N11 N13.
      repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
  Qed.
End BSL.

Theorem bsl_walk :
  forall (mem rom : word -> option byte) (L idx : Z) (a2w : word) (bs : list byte),
  (0 <= L)%Z /\ (L + 624 <= 2 ^ 64)%Z -> (0 <= idx <= 63)%Z ->
  rdn SEGS mem (Z_to_bv 64 (L + 104 + 8 * idx)) 8 = Some bs -> length bs = 8%nat ->
  (forall j, (0 <= j < 8)%Z -> store_ok SEGS mem (Z_to_bv 64 (L + 96 + j)) 1 = true) ->
  (forall j, (0 <= j < 8)%Z -> store_ok SEGS mem (Z_to_bv 64 (L + 104 + 8 * idx + j)) 1 = true) ->
  forall regs, getr regs 9 = Z_to_bv 64 L -> getr regs 11 = Z_to_bv 64 idx -> getr regs 12 = a2w ->
  exists regs',
    msteps SEGS (mkst regs (0x3837c : word) mem rom)
                (mkst regs' (0x38394 : word)
                      (wbytes (wbytes mem (Z_to_bv 64 (L + 96)) (word_to_le_bytes 8 a2w))
                              (Z_to_bv 64 (L + 104 + 8 * idx)) (word_to_le_bytes 8 (Z_to_bv 64 (bytes_le_to_Z bs + 1)))) rom)
    /\ (forall r, r <> 11 -> r <> 13 -> getr regs' r = getr regs r).
Proof.
  intros mem rom L idx a2w bs HL Hidx Hrd Hlen Hok96 HokW regs H9 H11 H12.
  exact (bsl_walk_S mem rom L idx a2w bs HL Hidx Hrd Hlen Hok96 HokW regs H9 H11 H12).
Qed.
