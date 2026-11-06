From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import reac_role_refuse_code_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_role_refuse_code of the UBSan image (0x145e4, 15 instructions), walked with Lib/Tac.v and Lib/Step.v.
    `addi a1, zero, 1; bgeu a1, a0` splits on a0 <= 1 (unsigned). For a0 > 1 it forms codes[0] with auipc/addi and
    returns. For a0 = 0 or 1 (the walk substitutes the literal) the pointer-overflow test `not a3, a1;
    bltu a3, a2` on REFUSE_TBL and 8 a0 is closed and not taken, and `ld a0, 0(a0)` reads the 8-byte entry a0 of the
    absolute table at REFUSE_TBL. That table is in a writable segment: the contract's table premise gives its bytes
    as the image's ([tbl_read]). *)

Lemma img_nth : forall n A bs, image_bytes rsegs A n = Some bs ->
  forall i, (i < n)%nat -> seg_rom rsegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A bs H i Hi; [lia|]. cbn in H.
  destruct (seg_rom rsegs (wa A)) as [b|] eqn:E; [|discriminate].
  destruct (image_bytes rsegs (A + 1) n) as [bs'|] eqn:E'; [|discriminate].
  inversion H; subst bs. destruct i as [|i].
  - rewrite Z.add_0_r. exact E.
  - cbn [nth_error]. rewrite <- (IH (A + 1) bs' E' i ltac:(lia)). f_equal. unfold wa. f_equal. lia.
Qed.

(** n bytes at A whose memory reads are the image's read as the image bytes. *)
Lemma tbl_read : forall m A n bs, image_bytes rsegs A n = Some bs -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  (forall a, A <= a < A + Z.of_nat n -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
  ov_read_bytes rsegs m (wa A) n = Some bs.
Proof.
  intros m A n bs E H0 H1 H. pose proof (image_bytes_length rsegs n A bs E) as L.
  assert (B : bytes_at rsegs m A bs).
  { split; [lia|]. split; [lia|]. intros i Hi. rewrite H by lia. apply (img_nth n A bs E). lia. }
  subst n.
  pose proof (bytes_at_ov_read rsegs m A bs 0 (length bs) B ltac:(lia)) as R.
  cbn [skipn Z.of_nat] in R. rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

Ltac kill K :=
  exfalso;
  first [ zify_cond K; lia
        | revert K; vm_compute; let H := fresh in intro H; discriminate H ].

(** Entry k (0 or 1) of the table, from the table premise. *)
Ltac entry HT m k :=
  let A := eval vm_compute in (REFUSE_TBL + 8 * k) in
  let obs := eval vm_compute in (image_bytes rsegs A 8) in
  lazymatch obs with
  | Some ?bs =>
      let HR := fresh "HR" in
      assert (HR : ov_read_bytes rsegs m (Z_to_bv 64 A) 8 = Some bs)
        by (apply tbl_read; [vm_compute; reflexivity | lia | lia |];
            intros a Ha; apply HT; unfold REFUSE_TBL, REFUSE_TBL_SIZE; lia)
  end.

Theorem reac_role_refuse_code_holds : reac_role_refuse_code_contract.
Proof.
  unfold reac_role_refuse_code_contract, REAC_ROLE_REFUSE_CODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m HT.
  pose proof (zr_word a0) as R0. unfold inr64 in R0.
  destruct (Z_le_gt_dec (bv_unsigned a0) 1) as [LE|GT].
  - (* the table path: a0 is 0 or 1 *)
    assert (E : a0 = Z_to_bv 64 0 \/ a0 = Z_to_bv 64 1).
    { destruct (Z.eq_dec (bv_unsigned a0) 0) as [E0|E0]; [left|right];
        apply bv_eq; rewrite unsigned_lit by lia; lia. }
    clear LE R0.
    destruct E as [-> | ->]; [entry HT m 0 | entry HT m 1].
    all: (* addi a1, zero, 1; bgeu a1, a0: taken *)
      zstep; zstep;
      let K := fresh "K" in
      if_cases K; [ first [ kill K | idtac ] .. ];
      (* slli a2, a0, 3; auipc a1; addi a1; not a3, a1; bltu a3, a2: not taken *)
      do 5 zstep;
      let K := fresh "K" in
      if_cases K; [ first [ kill K | idtac ] .. ];
      (* slli a0, a0, 3; add a0, a1, a0; ld a0, 0(a0); ret *)
      do 4 zstep; finish.
  - (* a0 > 1: codes[0] *)
    assert (RC : refuse_code_res (bv_unsigned a0) = CODE_NONE).
    { unfold refuse_code_res. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    rewrite RC. unfold CODE_NONE.
    (* addi a1, zero, 1; bgeu a1, a0: not taken *)
    zstep. zstep.
    let K := fresh "K" in
    if_cases K; [ first [ kill K | idtac ] .. ].
    (* auipc a0; addi a0; ret *)
    zstep. zstep. zstep. finish.
Qed.
