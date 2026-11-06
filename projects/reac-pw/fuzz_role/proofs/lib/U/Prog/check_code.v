From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import strcmp_c reac_role_refuse_code_c check_code_c.
Import ListNotations.
Open Scope Z_scope.

(** check_code of the UBSan image (0x142d8, 19 instructions), from strcmp_contract, walked with Lib/Tac.v and
    Lib/Step.v. The prologue saves ra and s0 in the 16-byte frame and moves a1 (CODE_MALFORMED) to s0. strcmp is
    called with a0 = CODE_NONE and the literal 0x103e0 = CODE_NONE, then with a0 = s0 = CODE_MALFORMED and the
    literal 0x103d6 = CODE_MALFORMED: each compares one image string with itself and returns 0, so neither `bnez a0`
    is taken; the epilogue reloads ra and s0 and frees the frame. *)

(** The text of the two code strings (read-only image bytes, checked by [ro_bytes_b]). *)
Definition TXT_NONE : list byte := map (Z_to_bv 8) [110; 111; 110; 101].
Definition TXT_MALFORMED : list byte := map (Z_to_bv 8) [109; 97; 108; 102; 111; 114; 109; 101; 100].

Lemma code_no_nul : forall l : list byte,
  forallb (fun b => negb (bv_eqb b (Z_to_bv 8 0))) l = true -> ~ In (Z_to_bv 8 0) l.
Proof.
  intros l H Hin. rewrite forallb_forall in H. specialize (H _ Hin). cbv beta in H.
  rewrite bv_eqb_refl in H. discriminate H.
Qed.

Lemma code_str_at : forall m A txt, mem_inv rsegs m -> 0 <= A -> A + Z.of_nat (length txt) + 1 <= 2^64 ->
  ro_bytes_b rsegs A (txt ++ [Z_to_bv 8 0]) = true -> bytes_at rsegs m A (txt ++ [Z_to_bv 8 0]).
Proof.
  intros m A txt MI H0 H1 H. apply ro_bytes_at; [exact MI | exact H0 | rewrite length_app; cbn [length]; lia |].
  apply ro_bytes_b_sound. exact H.
Qed.

Lemma none_at : forall m, mem_inv rsegs m ->
  bytes_at rsegs m (bv_unsigned (Z_to_bv 64 CODE_NONE)) (TXT_NONE ++ [Z_to_bv 8 0]).
Proof.
  intros m MI. unfold CODE_NONE. rewrite unsigned_lit by lia.
  apply code_str_at; [exact MI | lia | change (length TXT_NONE) with 4%nat; lia | vm_compute; reflexivity].
Qed.

Lemma malformed_at : forall m, mem_inv rsegs m ->
  bytes_at rsegs m (bv_unsigned (Z_to_bv 64 CODE_MALFORMED)) (TXT_MALFORMED ++ [Z_to_bv 8 0]).
Proof.
  intros m MI. unfold CODE_MALFORMED. rewrite unsigned_lit by lia.
  apply code_str_at; [exact MI | lia | change (length TXT_MALFORMED) with 9%nat; lia | vm_compute; reflexivity].
Qed.

Lemma none_nonul : ~ In (Z_to_bv 8 0) TXT_NONE.
Proof. apply code_no_nul. vm_compute. reflexivity. Qed.

Lemma malformed_nonul : ~ In (Z_to_bv 8 0) TXT_MALFORMED.
Proof. apply code_no_nul. vm_compute. reflexivity. Qed.

(** A branch whose condition the context decides. *)
Ltac br := first [ if_false | if_true | idtac ].

Theorem check_code_holds : strcmp_contract -> check_code_contract.
Proof.
  intros HSC. unfold check_code_contract, CHECK_CODE, CHECK_CODE_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo HA0 HA1 ST HK HW MI.
  subst a0 a1. clear HW.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (proj1 ST) as Hlo.
  pose proof (Z_to_bv_lit_self sp) as Esp.
  set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
  pose proof (munch_refl [(Sp - 16, Sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* addi sp, sp, -16; sd ra, 8(sp); sd s0, 0(sp); mv s0, a1 *)
  step. step. step. step.
  (* auipc a1; addi a1, a1, 0xf8; jal strcmp *)
  step. step. step.
  eapply evt_cut.
  { eapply HSC with (sx := TXT_NONE) (sy := TXT_NONE);
      first [ apply none_at; assumption | exact none_nonul ]. }
  intros ms' (r & x11 & x12 & x13 & -> & HR).
  assert (Er : r = Z_to_bv 64 0) by (apply HR; reflexivity). subst r. clear HR.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* bnez a0: not taken; auipc a0; addi a1, a0, 0xde; mv a0, s0; jal strcmp *)
  step. br. step. step. step. step.
  eapply evt_cut.
  { eapply HSC with (sx := TXT_MALFORMED) (sy := TXT_MALFORMED);
      first [ apply malformed_at; assumption | exact malformed_nonul ]. }
  intros ms' (r & x11' & x12' & x13' & -> & HR).
  assert (Er : r = Z_to_bv 64 0) by (apply HR; reflexivity). subst r. clear HR.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* bnez a0: not taken; ld ra, 8(sp); ld s0, 0(sp); addi sp, sp, 16; ret *)
  step. br. step. step. step. step.
  release_frame FR ST Sp.
  finish.
Qed.
