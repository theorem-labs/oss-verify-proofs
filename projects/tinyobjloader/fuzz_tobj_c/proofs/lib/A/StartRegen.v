(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from the start-up checks of A/e8.v, A/Start2.v and A/Start3.v: each check over the states of A/StartRegenS.v, for both values of CONFIG_RSEQ, with the facts of those states that the first start-up segments read and the restatements of L_hm as S_hm and of T_hm2 as S_hm2, proved per value as A/e8.v and A/Start2.v proved them of the recorded states; the relaunch rule's leaf-keyed form shown to give each recorded exit and hand-off state back from the recorded sources. *)
(* The checks that A/e8.v (Start1), A/Start2.v and A/Start3.v make of the recorded start-up
   states, made of the states A/StartRegenS.v computes, each for both values of CONFIG_RSEQ
   ([intros [|]]): every run reaches the state the next step starts from, and every recorded CFG
   check holds of the relaunched cut and exit states.  With them, the facts of those states the
   segments' proofs read (next variables, lenient flags, stack-pointer facts) and the two
   restatements ([restate_hm]: [L_hm r] as [S_hm r]; [restate_hm2]: [T_hm2 r] as [S_hm2 r]), by
   the proofs A/e8.v and A/Start2.v gave them over the recorded states, each computation on a
   state destructing [r] first. *)
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymSoundR SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA GlueA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform Relaunch.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartHm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartStates e2 StartRegenS.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS.Start1R.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS.Start2R.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS.Start3R.
Close Scope bv_scope.
Open Scope Z_scope.
(* The leaf-keyed instantiation of the relaunch rule (Lib/Relaunch.v [relaunch_src]) gives each
   recorded exit and hand-off state back when the recorded sources stand for the computed ones
   (the rule with N = R). *)
Lemma relaunch_id_E_s2 :
  relaunch_src segsA FUEL1 cutpcs1 G1 srcs1_rec srcs1_rec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start1States.E_s2
  = OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start1States.E_s2.
Proof. vm_compute. reflexivity. Qed.
Lemma relaunch_id_T_hm2 :
  relaunch_src segsA FUEL2 [HMCUT; ECALL_MMAP] G2 [S_s2x_rec] [S_s2x_rec] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start2States.T_hm2
  = OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start2States.T_hm2.
Proof. vm_compute. reflexivity. Qed.
Lemma relaunch_id_E_s3 :
  relaunch_src segsA FUEL2 [HMCUT; ECALL_MMAP] G2 [S_hm2_rec] [S_hm2_rec] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start2States.E_s3
  = OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start2States.E_s3.
Proof. vm_compute. reflexivity. Qed.
Lemma relaunch_id_E_k7 :
  relaunch_src segsA FUEL3 [HMCUT; ECALL_MMAP] G3 [S_s3x_rec] [S_s3x_rec] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start3States.E_k7
  = OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start3States.E_k7.
Proof. vm_compute. reflexivity. Qed.


Lemma xf1_ok : forall r, apply_xforms (add_facts F1x (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartStates.S_ctor r)) xf1 = Some (S_ctor_x r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F1x_below : forall r, forallb (sprop_below (ss_next (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartStates.S_ctor r))) F1x = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma next_S_ctor_x : forall r, ss_next (S_ctor_x r) = 25%positive.
Proof. intros [|]; reflexivity. Qed.
Lemma lenient_S_ctor_x : forall r, ss_lenient (S_ctor_x r) = false.
Proof. intros [|]; reflexivity. Qed.

Lemma run_hm : forall r, sym_run segsA 4000%nat [HMCUT] (S_ctor_x r) true = Some [mkLeaf (L_hm r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run_b2 : forall r, sym_run segsA 4000%nat [ECALL_MMAP] (S_hm r) true = Some [mkLeaf (E_b2_S r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

(* [L_hm r] restated as [S_hm r] (reg 10 := 2^47 - 1, the smeared stack pointer; reg 15 := the
   next fresh variable): a valuation change, by A/e8.v's proof of the recorded pair. *)
Definition Xhm : sv := SAlu ALU_ADD (SVar 1%positive) (SLit (-160)).
Lemma L_hm_a0 : forall r, reg_sv (L_hm r) 10 = smear_sv Xhm [1; 2; 4; 8; 16; 32].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma next_L_hm : forall r, ss_next (L_hm r) = 25%positive.
Proof. intros [|]; reflexivity. Qed.
Lemma below_a5_L_hm : forall r, sv_below 25%positive (reg_sv (L_hm r) 15) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L_hm_sp : forall r,
  In (SPUle (SLit 140735340871680) (SVar 1%positive)) (ss_facts (L_hm r)) /\
  In (SPUle (SVar 1%positive) (SLit 140737488355104)) (ss_facts (L_hm r)).
Proof. intros [|]; split; vm_compute; tauto. Qed.
Definition sd_hm (r : bool) : list (sv * sv) * list sprop :=
  match state_diff (L_hm r) (S_hm r) with Some p => p | None => ([], []) end.
Lemma sd_hm_eq : forall r, state_diff (L_hm r) (S_hm r) = Some (sd_hm r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd_hm_shape : forall r,
  sd_hm r = ([(reg_sv (L_hm r) 10, SLit (2 ^ 47 - 1)); (reg_sv (L_hm r) 15, SVar 25%positive)], []).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma swf_S_hm : forall r, swf (S_hm r) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition rho_hm (r : bool) (rho : valuation) : valuation :=
  rho_set_rw rho 25%positive (eval rho (reg_sv (L_hm r) 15)).

Lemma restate_hm : forall (r : bool) (K : list event -> Model -> Prop) (rho : valuation) (w : world),
  SP segsA K (L_hm r) rho w -> agree_below 25%positive rho (rho_hm r rho) /\ SP segsA K (S_hm r) (rho_hm r rho) w.
Proof.
  intros r K rho w Hsp.
  assert (Hag : agree_below 25%positive rho (rho_hm r rho)) by (unfold rho_hm; apply agree_below_set_rw; lia).
  split; [exact Hag|].
  pose proof (SP_facts_hold segsA K rho (L_hm r) w Hsp) as HF.
  assert (Hv1 : 0x7fff80000000 <= bv_unsigned (rw rho 1%positive) <= 0x7fffffffff20).
  { destruct (L_hm_sp r) as [X1 X2].
    pose proof (proj1 (Forall_forall _ _) HF _ X1) as Y1. pose proof (proj1 (Forall_forall _ _) HF _ X2) as Y2.
    cbn [holds eval] in Y1, Y2. rewrite Z_to_bv_unsigned in Y1, Y2.
    change (bv_wrap 64 140735340871680) with 140735340871680 in Y1. change (bv_wrap 64 140737488355104) with 140737488355104 in Y2. lia. }
  destruct Hsp as [Hsm Hk]. split; [|exact Hk].
  apply (smatch_restate segsA (rho_hm r rho) (L_hm r) (S_hm r) w (fst (sd_hm r)) (snd (sd_hm r))).
  - eapply smatch_agree; [rewrite (next_L_hm r); exact Hag | exact Hsm].
  - exact (swf_S_hm r).
  - rewrite (sd_hm_eq r). destruct (sd_hm r); reflexivity.
  - rewrite (sd_hm_shape r). cbn [fst]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + rewrite (L_hm_a0 r). rewrite <- (eval_agree 25%positive rho (rho_hm r rho) (smear_sv Xhm [1; 2; 4; 8; 16; 32]) Hag ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)).
      cbn [eval]. apply eval_smear_sv_47. unfold Xhm. cbn [eval]. rewrite add_val, Z_to_bv_unsigned.
      change (bv_wrap 64 (-160)) with (2 ^ 64 - 160).
      replace (bv_unsigned (rw rho 1%positive) + (2 ^ 64 - 160)) with ((bv_unsigned (rw rho 1%positive) - 160) + 1 * 2 ^ 64) by lia.
      rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
    + unfold rho_hm at 2. cbn [eval]. rewrite rho_set_rw_at. symmetry. exact (eval_agree 25%positive rho (rho_hm r rho) _ Hag (below_a5_L_hm r)).
  - rewrite (sd_hm_shape r). cbn [snd]. apply Forall_nil.
Qed.

Lemma next_S_hm : forall r, ss_next (S_hm r) = 26%positive.
Proof. intros [|]; reflexivity. Qed.
Lemma lenient_S_hm : forall r, ss_lenient (S_hm r) = false.
Proof. intros [|]; reflexivity. Qed.

Lemma runF_b2 : forall r, sym_runA segsA 400%nat [418488] (S_b2fail r) true = Some [mkLeafA (SPINb2 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin_b2 : forall r, sym_runA segsA 2%nat [418488] (SPINb2 r) true = Some [mkLeafA (SPINb2 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma runO_b2 : forall r, sym_runA segsA 3000%nat [ECALL_MMAP] (S_b2ok r) true = Some [mkLeafA (E_b3 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma runF_b3 : forall r, sym_runA segsA 400%nat [418508] (S_b3fail r) true = Some [mkLeafA (SPINb3 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin_b3 : forall r, sym_runA segsA 2%nat [418508] (SPINb3 r) true = Some [mkLeafA (SPINb3 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma runO_b3 : forall r, sym_runA segsA 3000%nat [ECALL_MMAP] (S_b3ok r) true = Some [mkLeafA (E_b4 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma runF_b4 : forall r, sym_runA segsA 400%nat [418528] (S_b4fail r) true = Some [mkLeafA (SPINb4 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin_b4 : forall r, sym_runA segsA 2%nat [418528] (SPINb4 r) true = Some [mkLeafA (SPINb4 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma check1 : forall r, check_cfgA segsA FUEL1 cutpcs1 G1 (cuts1 r) (exits1 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

(* The measured cuts and exit of check1 for its completeness check (A/e8.v's [vcuts1] and
   [vexits1] over the cut and exit states of this value of the flag). *)
Definition vcuts1 (r : bool) : list vnodeA :=
  [mkVNA (S_b4ok r) 100 (SLit 0);
   mkVNA (Z1 r) 50 (SAlu ALU_SUB (SLit 1584831) (SVar 26%positive));
   mkVNA (Z2 r) 40 (SAlu ALU_SUB (SLit 1580735) (SVar 26%positive))].
Definition vexits1 (r : bool) : list vnodeA := [mkVNA (E_s2 r) 10 (SLit 0)].
Lemma echeck1 : forall r, check_ecfgA segsA FUEL1 cutpcs1 G1 (vcuts1 r) (vexits1 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma next_E_s2 : forall r, ss_next (ax_S (E_s2 r)) = 27%positive.
Proof. intros [|]; reflexivity. Qed.

Lemma runF_s2 : forall r, sym_runA segsA 400%nat [SPIN_MMAPORDIE] (S_s2fail r) true = Some [mkLeafA (SPIN5 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin5 : forall r, sym_runA segsA 2%nat [SPIN_MMAPORDIE] (SPIN5 r) true = Some [mkLeafA (SPIN5 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check2a : forall r,
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib.cfg1_okA FUEL2 [HMCUT; ECALL_MMAP] G2 (S_s2x r) (T_hm2 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma check2b : forall r,
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib.cfg1_okA FUEL2 [HMCUT; ECALL_MMAP] G2 (S_hm2 r) (E_s3 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

(* [T_hm2 r] restated as [S_hm2 r] (reg 10 := 2^47 - 1), by A/Start2.v's proof of the recorded pair. *)
Lemma T_hm2_sp : forall r,
  In (SPUle (SLit 140735340871680) (SVar 1%positive)) (ss_facts (ax_S (T_hm2 r))) /\
  In (SPUle (SVar 1%positive) (SLit 140737488355104)) (ss_facts (ax_S (T_hm2 r))).
Proof. intros [|]; split; vm_compute; tauto. Qed.
Definition sd_hm2 (r : bool) : list (sv * sv) * list sprop :=
  match state_diff (ax_S (T_hm2 r)) (ax_S (S_hm2 r)) with Some p => p | None => ([], []) end.
Lemma sd_hm2_eq : forall r, state_diff (ax_S (T_hm2 r)) (ax_S (S_hm2 r)) = Some (sd_hm2 r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd_hm2_shape : forall r, sd_hm2 r = ([(smear_sv Xhm [1; 2; 4; 8; 16; 32], SLit (2 ^ 47 - 1))], []).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma swf_S_hm2 : forall r, swf (ax_S (S_hm2 r)) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma restate_hm2 : forall (r : bool) (J : jpredA) (rho : valuation) (w : world),
  SPA segsA J (T_hm2 r) rho [] w -> SPA segsA J (S_hm2 r) rho [] w.
Proof.
  intros r J rho w Hsp.
  pose proof (SPA_facts_hold segsA J rho (T_hm2 r) [] w Hsp) as HF.
  assert (Hv1 : 0x7fff80000000 <= bv_unsigned (rw rho 1%positive) <= 0x7fffffffff20).
  { destruct (T_hm2_sp r) as [X1 X2].
    pose proof (proj1 (Forall_forall _ _) HF _ X1) as Y1. pose proof (proj1 (Forall_forall _ _) HF _ X2) as Y2.
    cbn [holds eval] in Y1, Y2. rewrite Z_to_bv_unsigned in Y1, Y2.
    change (bv_wrap 64 140735340871680) with 140735340871680 in Y1. change (bv_wrap 64 140737488355104) with 140737488355104 in Y2. lia. }
  change (S_hm2 r) with (ax_setS (T_hm2 r) (ax_S (S_hm2 r))).
  apply (SPA_restate segsA J rho (T_hm2 r) (ax_S (S_hm2 r)) [] w (fst (sd_hm2 r)) (snd (sd_hm2 r)));
    [exact (swf_S_hm2 r) | rewrite (sd_hm2_eq r); destruct (sd_hm2 r); reflexivity | clear Hsp HF; destruct r; reflexivity | | | exact Hsp].
  - rewrite (sd_hm2_shape r). cbn [fst]. unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    cbn [eval]. apply eval_smear_sv_47. unfold Xhm. cbn [eval]. rewrite add_val, Z_to_bv_unsigned.
    change (bv_wrap 64 (-160)) with (2 ^ 64 - 160).
    replace (bv_unsigned (rw rho 1%positive) + (2 ^ 64 - 160)) with ((bv_unsigned (rw rho 1%positive) - 160) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
  - rewrite (sd_hm2_shape r). cbn [snd]. apply Forall_nil.
Qed.

Lemma next_E_s3 : forall r, ss_next (ax_S (E_s3 r)) = 28%positive.
Proof. intros [|]; reflexivity. Qed.

Lemma runF_s3 : forall r, sym_runA segsA 400%nat [SPIN_MMAPORDIE] (S_s3fail r) true = Some [mkLeafA (SPIN6 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin6 : forall r, sym_runA segsA 2%nat [SPIN_MMAPORDIE] (SPIN6 r) true = Some [mkLeafA (SPIN6 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check3 : forall r,
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib.cfg1_okA FUEL3 [HMCUT; ECALL_MMAP] G3 (S_s3x r) (E_k7 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
