From Stdlib Require Import ZArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import check_plain_c.
Import ListNotations.
Open Scope Z_scope.

(** check_plain of the plain image (0x14818, 23 instructions), walked with Lib/Tac.v and Lib/Step.v. The prologue
    carves the 16-byte frame and saves ra at sp - 8; both byte blocks end at or below lo, so the store meets neither.
    `bne a0, a1` is not taken (a0 = a1); `blez a0` goes to the epilogue for rc <= 0. For rc > 0 the loop at 0x14830
    ([loop]) walks the rc cells with a0 counting down and a2, a3 two bytes into cell i of out and first; each of the
    three `lbu` pairs reads the same byte of w at both blocks, so no `bne` to the abort frame is taken. The epilogue
    reloads ra and frees the frame. *)

(** A branch whose taken side the context refutes. *)
Ltac refute K :=
  exfalso; zify_cond K;
  first [ lia | mlia | apply andb_false_iff in K; destruct K as [K|K]; zify_bool K; mlia ].
Ltac br := let K := fresh "K" in if_cases K; [ first [ refute K | cbv iota ] .. ].
(** A register value [Z_to_bv 64 e] with [e] in range. *)
Ltac uns := rewrite ?unsigned_lit by lia; lia.

Section Loop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (w : list byte) (X Y rc : Z).
  Hypothesis HX : bytes_at rsegs m X w.
  Hypothesis HY : bytes_at rsegs m Y w.
  Hypothesis HL : Z.of_nat (length w) = 3 * rc.

  Notation ST pc x10 x11 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Notation OUT := (fun ms' : machine_state =>
    exists x10 x11 x12 x13 x14 : word, ms' = ST 0x14864 x10 x11 x12 x13 x14).

  Lemma byte_of : forall k, (k < length w)%nat -> exists b, nth_error w k = Some b.
  Proof. intros k Hk. destruct (nth_error w k) as [b|] eqn:E; [eauto|]. apply nth_error_None in E. lia. Qed.

  (** Byte k of w, read at A + k (as [wa e], the form a load at a nonzero offset addresses). *)
  Lemma rd : forall A k b e, bytes_at rsegs m A w -> nth_error w k = Some b -> e = A + Z.of_nat k ->
    ov_read_bytes rsegs m (wa e) 1 = Some [b].
  Proof.
    intros A k b e H E ->. apply (u8ro_read rsegs m A w (Z.of_nat k) b _ H); [rewrite Nat2Z.id; exact E | lia | reflexivity].
  Qed.

  (** The same read at a register itself (the form a load at offset 0 addresses). *)
  Lemma rd0 : forall A k b (a : word), bytes_at rsegs m A w -> nth_error w k = Some b ->
    bv_unsigned a = A + Z.of_nat k -> ov_read_bytes rsegs m a 1 = Some [b].
  Proof.
    intros A k b a H E Ha. rewrite <- (wa_of_var a (A + Z.of_nat k) Ha). exact (rd A k b _ H E eq_refl).
  Qed.

  (** The loop at 0x14830. Invariant: cells 0 .. i-1 are compared (out and first both hold firstn (3 i) w there, so
      every compare so far was equal); a0 = rc - i cells are left; a2 = out + 3 i + 2 and a3 = first + 3 i + 2. *)
  Lemma loop : forall n i (c p q x11 x14 : word),
    (Z.to_nat rc - i = n)%nat -> (i < Z.to_nat rc)%nat ->
    bv_unsigned c = rc - Z.of_nat i ->
    bv_unsigned p = X + 3 * Z.of_nat i + 2 -> bv_unsigned q = Y + 3 * Z.of_nat i + 2 ->
    evt rsegs OUT (ST 0x14830 c x11 p q x14).
  Proof.
    induction n as [n IH] using lt_wf_ind. intros i c p q x11 x14 Hn Hi Hc Hp Hq.
    pose proof (bytes_at_bound rsegs m X w HX) as BX. pose proof (bytes_at_bound rsegs m Y w HY) as BY.
    destruct (byte_of (3 * i) ltac:(lia)) as [b0 E0].
    destruct (byte_of (3 * i + 1) ltac:(lia)) as [b1 E1].
    destruct (byte_of (3 * i + 2) ltac:(lia)) as [b2 E2].
    (* lbu a1, -2(a2); lbu a4, -2(a3); bne a1, a4: byte 3i of w at both blocks, not taken *)
    pose proof (rd X (3 * i) b0 (bv_unsigned p + -2) HX E0 ltac:(lia)) as R1.
    pose proof (rd Y (3 * i) b0 (bv_unsigned q + -2) HY E0 ltac:(lia)) as R2.
    step. step. step. br. clear R1 R2.
    (* lbu a1, -1(a2); lbu a4, -1(a3); bne a1, a4: byte 3i + 1 *)
    pose proof (rd X (3 * i + 1) b1 (bv_unsigned p + -1) HX E1 ltac:(lia)) as R1.
    pose proof (rd Y (3 * i + 1) b1 (bv_unsigned q + -1) HY E1 ltac:(lia)) as R2.
    step. step. step. br. clear R1 R2.
    (* lbu a1, 0(a2); lbu a4, 0(a3); bne a1, a4: byte 3i + 2, at the cursors themselves *)
    pose proof (rd0 X (3 * i + 2) b2 p HX E2 ltac:(lia)) as R1.
    pose proof (rd0 Y (3 * i + 2) b2 q HY E2 ltac:(lia)) as R2.
    step. step. step. br. clear R1 R2.
    (* addi a0, a0, -1; addi a3, a3, 3; addi a2, a2, 3; bnez a0 *)
    step. step. step. step.
    let K := fresh "K" in
    if_cases K; zify_cond K; cbv iota;
      [ first [ apply evt_done; eexists _, _, _, _, _; reflexivity
              | apply (IH (Z.to_nat rc - S i)%nat ltac:(lia) (S i)); [lia | first [lia | mlia] | uns | uns | uns] ] .. ].
  Qed.
End Loop.

Theorem check_plain_holds : check_plain_contract.
Proof.
  unfold check_plain_contract, CHECK_PLAIN, CHECK_PLAIN_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo rc w HA0 HA1 Hrc HB ST HK HROM MI.
  rewrite HA1 in HA0. subst a0 a1. clear HROM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (proj1 ST) as Hlo.
  pose proof (Z_to_bv_lit_self sp) as Esp.
  set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
  pose proof (munch_refl [(Sp - 16, Sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct (Z_lt_le_dec 0 rc) as [Hpos | Hneg].
  - (* rc > 0: the loop *)
    destruct (HB Hpos) as (HL & HX & HXlo & HY & HYlo). clear HB.
    pose proof (bytes_at_bound rsegs m _ w HX) as BX. pose proof (bytes_at_bound rsegs m _ w HY) as BY.
    carve_frame 16%nat ST.
    (* addi sp, sp, -16; sd ra, 8(sp) *)
    step. step.
    (* bne a0, a1: not taken; blez a0: not taken *)
    step. br. step. br.
    (* addi a3, a3, 2; addi a2, a2, 2 *)
    step. step.
    eapply evt_cut.
    { eapply loop with (w := w) (X := bv_unsigned a2) (Y := bv_unsigned a3) (rc := rc) (n := Z.to_nat rc) (i := 0%nat);
        first [ eassumption | lia | uns ]. }
    intros ms' (x10 & x11 & x12 & x13 & x14 & ->).
    (* ld ra, 8(sp); addi sp, sp, 16; ret *)
    step. step. step.
    release_frame FR ST Sp.
    finish.
  - (* rc <= 0: blez goes to the epilogue *)
    clear HB.
    carve_frame 16%nat ST.
    (* addi sp, sp, -16; sd ra, 8(sp); bne a0, a1: not taken; blez a0: taken *)
    step. step. step. br. step. br.
    (* ld ra, 8(sp); addi sp, sp, 16; ret *)
    step. step. step.
    release_frame FR ST Sp.
    finish.
Qed.
