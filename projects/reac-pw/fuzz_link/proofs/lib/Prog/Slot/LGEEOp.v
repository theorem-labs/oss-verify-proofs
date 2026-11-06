(* LGlue's LH_OP: at the loop head the frame cell sp + 0x40 (FO_P) holds the cursor P, and the cursor is a
   proper suffix of the payload (N >= 1), so the byte at P exists; that byte mod 6 is the arm the dispatch at
   0x13a1c-0x13a64 takes. Pure: no allocator, no SR. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LGlue.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ee_skip : forall m A (l1 l2 : list byte),
  bytes_at rsegs m A (l1 ++ l2) -> bytes_at rsegs m (A + Z.of_nat (length l1)) l2.
Proof. intros m A l1 l2 H. apply bytes_at_app in H. exact (proj2 H). Qed.

Lemma ee_take : forall m A (l1 l2 : list byte), bytes_at rsegs m A (l1 ++ l2) -> bytes_at rsegs m A l1.
Proof. intros m A l1 l2 H. apply bytes_at_app in H. exact (proj1 H). Qed.

(* the cursor cell of the loop-head frame: the ninth cell, 64 bytes above sp *)
Lemma ee_lh_cell_P : forall m S md mk P nc j0 j1 j2,
  rw_cells rsegs m (S - SLOT_FRAME) (lh_cells md mk P nc j0 j1 j2) ->
  bytes_at rsegs m (S - SLOT_FRAME + FO_P) (le8 (wz P)).
Proof.
  intros m S md mk P nc j0 j1 j2 [[Hwf Hb] _].
  cbn [lh_cells cells_wf cell_wf] in Hwf. destruct Hwf as [Hj0 _].
  cbn [lh_cells cells_bytes cbytes] in Hb.
  apply ee_skip in Hb. rewrite Hj0 in Hb.
  do 7 (apply ee_skip in Hb; rewrite length_le8 in Hb).
  apply ee_take in Hb.
  match type of Hb with bytes_at _ _ ?a _ =>
    replace (S - SLOT_FRAME + FO_P) with a by (unfold FO_P; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) end.
  exact Hb.
Qed.

Theorem glue_lh_op : LH_OP.
Proof.
  intros E i gp ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6
                    & F & fc & m & P & N & kbs & mbs & gbs & EQ & FC & Hi & HN & HM & _).
  subst ms.
  destruct HM as ((j0 & j1 & j2 & nc & FR) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                  & _ & _ & _ & (Hpl & k & Hk & HP & HNk) & _).
  pose proof (ee_lh_cell_P m (e_S E) (e_md E) (e_mk E) P nc j0 j1 j2 FR) as HC.
  assert (Ekn : Z.of_nat (Z.to_nat k) = k) by (apply Z2Nat.id; lia).
  assert (Hkn : (Z.to_nat k < length (e_pl E))%nat) by lia.
  rewrite <- (firstn_skipn (Z.to_nat k) (e_pl E)) in Hpl.
  apply ee_skip in Hpl.
  rewrite firstn_length_le in Hpl by lia.
  destruct (skipn (Z.to_nat k) (e_pl E)) as [|b rest] eqn:Es.
  { exfalso. pose proof (f_equal (@length byte) Es) as L. rewrite length_skipn in L. cbn [length] in L. lia. }
  change (b :: rest) with ([b] ++ rest) in Hpl. apply ee_take in Hpl.
  exists (bz b mod 6). split; [pose proof (Z.mod_pos_bound (bz b) 6 ltac:(lia)); lia|].
  unfold lh_op. cbn [ms_mem MS].
  exists P, b. split; [exact HC|]. split; [|reflexivity].
  rewrite Ekn, <- HP in Hpl. exact Hpl.
Qed.

Print Assumptions glue_lh_op.
About glue_lh_op.
