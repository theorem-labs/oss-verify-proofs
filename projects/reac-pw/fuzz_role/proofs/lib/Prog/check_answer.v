From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import
  strcmp_c reac_role_cfg_changes_c reac_role_cfg_apply_state_c check_answer_c reac_role_cfg_changes.
Import ListNotations.
Open Scope Z_scope.

(** check_answer of the plain image (0x14218, 19 instructions), from strcmp_contract, walked with Lib/Tac.v and
    Lib/Step.v. The prologue saves ra in the 16-byte frame; `xor a4, a2, a3; snez a4, a4` is changes_res a2 a3
    ([snez_xor_changes]), so `bne a0, a4` is not taken. The walk then splits on bv_eqb a2 a3: `bne a2, a3` picks the
    literal STATE_APPLIED or STATE_PENDING, which is the same address as a1, so strcmp compares one image string with
    itself, returns 0, and `bnez a0` is not taken; the epilogue reloads ra and frees the frame. *)

(** The text of the two state strings (read-only image bytes, checked by [ro_bytes_b]). *)
Definition TXT_APPLIED : list byte := map (Z_to_bv 8) [97; 112; 112; 108; 105; 101; 100].
Definition TXT_PENDING : list byte :=
  map (Z_to_bv 8) [114; 111; 108; 101; 95; 114; 101; 101; 115; 116; 97; 98; 108; 105; 115; 104; 95; 112; 101; 110;
                   100; 105; 110; 103].

Lemma no_nul : forall l : list byte,
  forallb (fun b => negb (bv_eqb b (Z_to_bv 8 0))) l = true -> ~ In (Z_to_bv 8 0) l.
Proof.
  intros l H Hin. rewrite forallb_forall in H. specialize (H _ Hin). cbv beta in H.
  rewrite bv_eqb_refl in H. discriminate H.
Qed.

Lemma str_at : forall m A txt, mem_inv rsegs m -> 0 <= A -> A + Z.of_nat (length txt) + 1 <= 2^64 ->
  ro_bytes_b rsegs A (txt ++ [Z_to_bv 8 0]) = true -> bytes_at rsegs m A (txt ++ [Z_to_bv 8 0]).
Proof.
  intros m A txt MI H0 H1 H. apply ro_bytes_at; [exact MI | exact H0 | rewrite length_app; cbn [length]; lia |].
  apply ro_bytes_b_sound. exact H.
Qed.

Lemma applied_at : forall m, mem_inv rsegs m ->
  bytes_at rsegs m (bv_unsigned (Z_to_bv 64 STATE_APPLIED)) (TXT_APPLIED ++ [Z_to_bv 8 0]).
Proof.
  intros m MI. unfold STATE_APPLIED. rewrite unsigned_lit by lia.
  apply str_at; [exact MI | lia | change (length TXT_APPLIED) with 7%nat; lia | vm_compute; reflexivity].
Qed.

Lemma pending_at : forall m, mem_inv rsegs m ->
  bytes_at rsegs m (bv_unsigned (Z_to_bv 64 STATE_PENDING)) (TXT_PENDING ++ [Z_to_bv 8 0]).
Proof.
  intros m MI. unfold STATE_PENDING. rewrite unsigned_lit by lia.
  apply str_at; [exact MI | lia | change (length TXT_PENDING) with 24%nat; lia | vm_compute; reflexivity].
Qed.

Lemma applied_nonul : ~ In (Z_to_bv 8 0) TXT_APPLIED.
Proof. apply no_nul. vm_compute. reflexivity. Qed.

Lemma pending_nonul : ~ In (Z_to_bv 8 0) TXT_PENDING.
Proof. apply no_nul. vm_compute. reflexivity. Qed.

(** A branch whose condition the context decides. *)
Ltac br := first [ if_false | if_true | idtac ].

Theorem check_answer_holds : strcmp_contract -> check_answer_contract.
Proof.
  intros HSC. unfold check_answer_contract, CHECK_ANSWER, CHECK_ANSWER_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo HA0 HA1 ST HK HW MI.
  subst a0 a1. clear HW.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (proj1 ST) as Hlo.
  pose proof (Z_to_bv_lit_self sp) as Esp.
  set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
  pose proof (munch_refl [(Sp - 16, Sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* addi sp, sp, -16; sd ra, 8(sp) *)
  step. step.
  (* xor a4, a2, a3; snez a4, a4 *)
  step. step.
  match goal with |- context [v_sltu ?x ?y] =>
    replace (v_sltu x y) with (Z_to_bv 64 (changes_res a2 a3)) by (symmetry; apply snez_xor_changes)
  end.
  (* bne a0, a4: a0 = a4 *)
  step. br.
  destruct (bv_eqb a2 a3) eqn:EQ.
  - (* cur = req: the literal is STATE_APPLIED *)
    pose proof EQ as EQz. unfold bv_eqb in EQz. apply Z.eqb_eq in EQz.
    replace (apply_state_res a2 a3) with STATE_APPLIED by (unfold apply_state_res; rewrite EQ; reflexivity).
    (* bne a2, a3: not taken; auipc a0; addi a2, a0, 0x25b; j 0x14244 *)
    step. br. step. step. step.
    (* mv a0, a1; mv a1, a2; jal strcmp *)
    step. step. step.
    eapply evt_cut.
    { eapply HSC with (sx := TXT_APPLIED) (sy := TXT_APPLIED);
        first [ apply applied_at; assumption | exact applied_nonul ]. }
    intros ms' (r & x11 & x12 & x13 & -> & HR).
    assert (Er : r = Z_to_bv 64 0) by (apply HR; reflexivity). subst r. clear HR.
    rewrite ret_pc_even by (try lia; reflexivity).
    (* bnez a0: not taken; ld ra, 8(sp); addi sp, sp, 16; ret *)
    step. br. step. step. step.
    release_frame FR ST Sp.
    finish.
  - (* cur <> req: the literal is STATE_PENDING *)
    pose proof EQ as EQz. unfold bv_eqb in EQz. apply Z.eqb_neq in EQz.
    replace (apply_state_res a2 a3) with STATE_PENDING by (unfold apply_state_res; rewrite EQ; reflexivity).
    (* bne a2, a3: taken to 0x1423c; auipc a0; addi a2, a0, 0xc1 *)
    step. br. step. step.
    (* mv a0, a1; mv a1, a2; jal strcmp *)
    step. step. step.
    eapply evt_cut.
    { eapply HSC with (sx := TXT_PENDING) (sy := TXT_PENDING);
        first [ apply pending_at; assumption | exact pending_nonul ]. }
    intros ms' (r & x11 & x12 & x13 & -> & HR).
    assert (Er : r = Z_to_bv 64 0) by (apply HR; reflexivity). subst r. clear HR.
    rewrite ret_pc_even by (try lia; reflexivity).
    (* bnez a0: not taken; ld ra, 8(sp); addi sp, sp, 16; ret *)
    step. br. step. step. step.
    release_frame FR ST Sp.
    finish.
Qed.
