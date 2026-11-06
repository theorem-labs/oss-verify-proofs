(** Steps the UBSan builder walks share: block and frame stores that keep [Facts.MBr] and the frame cells, the
    block's len field read from an image, and the list algebra of a 32-bit put (four byte stores). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import Facts Cut.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** Two literal words are the same when their values agree modulo 2^64. *)
Lemma lit_mod : forall a b, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

(** `not x` as the code computes it (18446744073709551615 - x) is the cells' [Z.lnot x]. *)
Lemma lnot_lit : forall x, Z_to_bv 64 (18446744073709551615 - x) = Z_to_bv 64 (Z.lnot x).
Proof. intros x. apply lit_mod. unfold Z.lnot. rewrite <- (Z.mod_add (Z.pred (- x)) 1 (2^64)) by lia. f_equal. lia. Qed.

(** pod_put's capacity test `len + (-0x3ffd) <u -0x4001` (pod.h:177) for any len in [0, 16380]. *)
Lemma cap_lit : forall x, -16381 <= x <= -1 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 (-16385)) = false.
Proof.
  intros x Hx. replace x with ((x + 16381) + -16381) by lia. apply put_cap_dead. lia.
Qed.

(** The value of a complement cell or register. *)
Lemma lnot_mod : forall x, 0 <= x < 2^64 -> Z.lnot x mod 2^64 = 2^64 - 1 - x.
Proof.
  intros x Hx. unfold Z.lnot. rewrite <- (Z.mod_add (Z.pred (- x)) 1 (2^64)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma pred_opp_mod : forall x, 0 <= x < 18446744073709551616 ->
  Z.pred (- x) mod 18446744073709551616 = 18446744073709551615 - x.
Proof.
  intros x Hx. rewrite <- (Z.mod_add (Z.pred (- x)) 1 18446744073709551616) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

(** The block's len field, read from an image. *)
Lemma MBr_img_len : forall sp m rest src pp lo b isp hasp pst es corr m1,
  MBr sp m rest src pp lo (pp_image b isp hasp pst es corr) m1 -> Z.of_nat (length b) <= POD_BUF_MAX ->
  ov_read_bytes rsegs m1 (wa (pp + POD_LEN_OFF)) 8 = Some (le8 (Z_to_bv 64 (Z.of_nat (length b)))).
Proof.
  intros sp m rest src pp lo b isp hasp pst es corr m1 MB Hb.
  pose proof MB as (_ & HL & _).
  erewrite MBr_read; [ | exact MB | unfold POD_LEN_OFF; lia | unfold POD_LEN_OFF, POD_PROPS in *; lia ].
  unfold POD_LEN_OFF. change (Z.to_nat 16384) with (Z.to_nat OFF_LEN).
  rewrite pp_image_slice_len by exact Hb. rewrite le8_lit64. reflexivity.
Qed.

(** Four adjacent one-byte overwrites are one four-byte overwrite. *)
Lemma overwrite4 : forall (I : list byte) (o : Z) x0 x1 x2 x3, 0 <= o -> (Z.to_nat o + 4 <= length I)%nat ->
  overwrite (overwrite (overwrite (overwrite I (Z.to_nat o) [x0]) (Z.to_nat (o + 1)) [x1])
               (Z.to_nat (o + 2)) [x2]) (Z.to_nat (o + 3)) [x3]
  = overwrite I (Z.to_nat o) [x0; x1; x2; x3].
Proof.
  intros I o x0 x1 x2 x3 Ho H.
  replace (Z.to_nat (o + 1)) with (Z.to_nat o + length [x0])%nat by (cbn [length]; lia).
  rewrite overwrite_adj by (cbn [length]; lia). cbn [app].
  replace (Z.to_nat (o + 2)) with (Z.to_nat o + length [x0; x1])%nat by (cbn [length]; lia).
  rewrite overwrite_adj by (cbn [length]; lia). cbn [app].
  replace (Z.to_nat (o + 3)) with (Z.to_nat o + length [x0; x1; x2])%nat by (cbn [length]; lia).
  rewrite overwrite_adj by (cbn [length]; lia). cbn [app]. reflexivity.
Qed.

(** The same with one-byte lists of any form (the le1 of a byte store). *)
Lemma overwrite4' : forall (I : list byte) (o : Z) x0 x1 x2 x3, 0 <= o -> (Z.to_nat o + 4 <= length I)%nat ->
  length x0 = 1%nat -> length x1 = 1%nat -> length x2 = 1%nat -> length x3 = 1%nat ->
  overwrite (overwrite (overwrite (overwrite I (Z.to_nat o) x0) (Z.to_nat (o + 1)) x1)
               (Z.to_nat (o + 2)) x2) (Z.to_nat (o + 3)) x3
  = overwrite I (Z.to_nat o) (x0 ++ x1 ++ x2 ++ x3).
Proof.
  intros I o x0 x1 x2 x3 Ho H L0 L1 L2 L3.
  replace (Z.to_nat (o + 1)) with (Z.to_nat o + length x0)%nat by lia.
  rewrite overwrite_adj by lia.
  replace (Z.to_nat (o + 2)) with (Z.to_nat o + length (x0 ++ x1))%nat by (rewrite length_app; lia).
  rewrite overwrite_adj by (rewrite !length_app; lia).
  replace (Z.to_nat (o + 3)) with (Z.to_nat o + length ((x0 ++ x1) ++ x2))%nat by (rewrite !length_app; lia).
  rewrite overwrite_adj by (rewrite !length_app; lia). rewrite <- !app_assoc. reflexivity.
Qed.

(** A 32-bit put at len = o = |b|: four byte stores, then the len field. *)
Lemma img_put32 : forall b isp hasp pst es corr o x0 x1 x2 x3 v,
  o = Z.of_nat (length b) -> o + 4 <= POD_BUF_MAX -> x0 ++ x1 ++ x2 ++ x3 = le32 v ->
  length x0 = 1%nat -> length x1 = 1%nat -> length x2 = 1%nat -> length x3 = 1%nat ->
  overwrite (overwrite (overwrite (overwrite (overwrite (pp_image b isp hasp pst es corr) (Z.to_nat o) x0)
                                     (Z.to_nat (o + 1)) x1) (Z.to_nat (o + 2)) x2) (Z.to_nat (o + 3)) x3)
    (Z.to_nat POD_LEN_OFF) (le8 (Z_to_bv 64 (o + 4)))
  = pp_image (b ++ le32 v) isp hasp pst es corr.
Proof.
  intros b isp hasp pst es corr o x0 x1 x2 x3 v Ho Hb Hx L0 L1 L2 L3.
  assert (Hlen : (Z.to_nat o + 4 <= length (pp_image b isp hasp pst es corr))%nat).
  { rewrite pp_image_tail, !length_app, length_zeros. unfold POD_BUF_MAX in *. lia. }
  rewrite overwrite4' by (try exact Hlen; lia). rewrite Hx.
  rewrite pp_image_put by (rewrite length_le32; unfold POD_BUF_MAX in *; lia).
  rewrite Ho, Nat2Z.id, le8_lit64, length_le32. f_equal. f_equal. lia.
Qed.

(** A put of x at len = |b| (bytes first, then the len field) is the image of b ++ x. *)
Lemma img_put : forall b x isp hasp pst es corr, Z.of_nat (length b + length x) <= POD_BUF_MAX ->
  overwrite (overwrite (pp_image b isp hasp pst es corr) (Z.to_nat (Z.of_nat (length b))) x)
    (Z.to_nat POD_LEN_OFF) (le8 (Z_to_bv 64 (Z.of_nat (length b) + Z.of_nat (length x))))
  = pp_image (b ++ x) isp hasp pst es corr.
Proof.
  intros b x isp hasp pst es corr H. rewrite pp_image_put by exact H. rewrite Nat2Z.id.
  rewrite le8_lit64. replace (Z.of_nat (length b) + Z.of_nat (length x)) with (Z.of_nat (length b + length x))
    by lia. reflexivity.
Qed.

(** Carry the bytes_at facts across a store that does not touch them. *)
Ltac keep_side := rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; cbn [length]; unfold FRAME_LOCALS, MID_STACK, POD_PROPS, POD_LEN_OFF; lia.
Ltac keep_cells :=
  repeat match goal with
  | H : bytes_at rsegs ?mm ?A ?bs |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?a) ?x) _) =>
      apply (bytes_at_write_other rsegs mm a x A bs) in H; [ | keep_side | keep_side | keep_side ]
  | H : bytes_at rsegs ?mm ?A ?bs |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (wa ?a) ?x) _) =>
      apply (bytes_at_write_other rsegs mm a x A bs) in H; [ | keep_side | keep_side | keep_side ]
  end.

(** A store of width n into the block at pp + o: store_ok from [MBr], the step, the other bytes_at facts carried,
    [MBr] of the overwritten image, and the stored bytes as a fact ST. *)
Ltac ppst HOK o n :=
  lazymatch goal with
  | MB : MBr ?A1 ?A2 ?A3 ?A4 ?A5 ?A6 ?Ib ?mm |- _ =>
      let SK := fresh "SK" in
      let HLI := fresh "HLI" in
      pose proof (MBr_bounds _ _ _ _ _ _ _ _ MB) as (_ & _ & HLI);
      assert (SK : store_ok rsegs mm (wa (A5 + o)) n = true)
        by (eapply MBr_pp_ok; [exact MB | unfold POD_LEN_OFF; lia | unfold POD_PROPS, POD_LEN_OFF in *; lia]);
      zstep; keep_cells;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?w ?bs) _) =>
          let MB2 := fresh "MB" in
          let ST := fresh "ST" in
          replace (write_to_mem mm w bs) with (write_to_mem mm (wa (A5 + o)) bs) by reflexivity;
          assert (MB2 : MBr A1 A2 A3 A4 A5 A6 (overwrite Ib (Z.to_nat o) bs) (write_to_mem mm (wa (A5 + o)) bs))
            by (eapply MBr_pp_store; [exact HOK | exact MB | unfold POD_LEN_OFF; lia |
                                     rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; cbn [length]; unfold POD_PROPS, POD_LEN_OFF in *; lia]);
          assert (ST : bytes_at rsegs (write_to_mem mm (wa (A5 + o)) bs) (A5 + o) bs)
            by (apply bytes_at_write_same; rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; cbn [length]; unfold POD_PROPS, POD_LEN_OFF in *; lia);
          clear MB SK HLI; try rename MB2 into MB;
          let mn := fresh "mm" in
          set (mn := write_to_mem mm (wa (A5 + o)) bs) in *; clearbody mn
      end
  end.

(** One cell read before a load (only the one the load needs, so the load's search stays short). *)
Ltac rd H :=
  lazymatch type of H with
  | bytes_at rsegs ?mm ?a (le8 (Z_to_bv 64 ?v)) => let R := fresh "R" in pose proof (cell8_read mm a v H) as R
  end.

(** The le8 cells of the current memory as loads. *)
Ltac reads :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      repeat match goal with
      | H : bytes_at rsegs mm ?a (le8 (Z_to_bv 64 ?v)) |- _ =>
          lazymatch goal with
          | _ : ov_read_bytes rsegs mm (wa a) 8 = _ |- _ => fail
          | _ => let R := fresh "R" in pose proof (cell8_read mm a v H) as R
          end
      end
  end.

(** A store of width n into the frame at sp + off (the twin of ppst). *)
Ltac stst HOK off n :=
  lazymatch goal with
  | MB : MBr ?A1 ?A2 ?A3 ?A4 ?A5 ?A6 ?Ib ?mm |- _ =>
      let SK := fresh "SK" in
      assert (SK : store_ok rsegs mm (wa (bv_unsigned A1 + off)) n = true)
        by (eapply MBr_stk_ok; [exact HOK | exact MB | unfold MID_STACK, FRAME_LOCALS in *; lia
                               | unfold MID_STACK, FRAME_LOCALS in *; lia]);
      zstep; keep_cells;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?w ?bs) _) =>
          let MB2 := fresh "MB" in
          let ST := fresh "ST" in
          replace (write_to_mem mm w bs) with (write_to_mem mm (wa (bv_unsigned A1 + off)) bs) by reflexivity;
          assert (MB2 : MBr A1 A2 A3 A4 A5 A6 Ib (write_to_mem mm (wa (bv_unsigned A1 + off)) bs))
            by (eapply MBr_stk_store; [exact HOK | exact MB | unfold MID_STACK, FRAME_LOCALS in *; lia
                                      | unfold MID_STACK, FRAME_LOCALS in *; lia
                                      | rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; cbn [length];
                                        unfold MID_STACK, FRAME_LOCALS in *; lia]);
          assert (ST : bytes_at rsegs (write_to_mem mm (wa (bv_unsigned A1 + off)) bs) (bv_unsigned A1 + off) bs)
            by (apply bytes_at_write_same; rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; cbn [length];
                unfold MID_STACK, FRAME_LOCALS in *; lia);
          clear MB SK; try rename MB2 into MB;
          let mn := fresh "mm" in
          set (mn := write_to_mem mm (wa (bv_unsigned A1 + off)) bs) in *; clearbody mn
      end
  end.
