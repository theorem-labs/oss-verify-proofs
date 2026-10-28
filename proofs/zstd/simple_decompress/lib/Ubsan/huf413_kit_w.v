From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdWalkKit ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_fkit.
Import ListNotations.
Open Scope Z_scope.

Ltac w_pc_is p :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) =>
      let b := eval vm_compute in (Z.eqb q p) in lazymatch b with true => idtac end
  end.

Lemma w_cb136_as_c8s : forall m A bs, rw_cells usegs m A [CB 136 bs] ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word,
    rw_cells usegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                        C8 w14; C8 w15; C8 w16].
Proof.
  intros m A bs H. pose proof (cb_as_c8s m A 17 bs H) as H2. cbn [c8s_of] in H2.
  do 17 eexists. exact H2.
Qed.

Lemma w_cb120_as_loc : forall m A bs, rw_cells usegs m A [CB 120 bs] ->
  exists u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 : word,
    rw_cells usegs m A [C8 u0; C8 u1; C8 u2; C8 u3; C8 u4; C8 u5; C8 u6; C8 u7; C8 u8; C8 u9; C8 u10; C8 u11; C8 u12; C8 u13]
    /\ rw_cells usegs m (A + 112) [C8 u14].
Proof.
  intros m A bs H. pose proof (cb_as_c8s m A 15 bs H) as H2. cbn [c8s_of] in H2.
  do 15 eexists.
  match type of H2 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: nil) =>
    change (rw_cells usegs m A ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13] ++ [c14])) in H2 end.
  apply (proj1 (rw_cells_app usegs m A _ _)) in H2. destruct H2 as [L T].
  cbn [cells_size csize Nat.add] in T. change (Z.of_nat 112) with 112 in T.
  split; [exact L | exact T].
Qed.
