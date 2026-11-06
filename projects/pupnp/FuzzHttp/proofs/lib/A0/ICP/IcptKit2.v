(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge Image Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit.
Import ListNotations.
Open Scope Z_scope.

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.
Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_pick : forall segs m A pre c post B, rw_cells segs m A (pre ++ c :: post) -> B = A + Z.of_nat (cells_size pre) ->
  rw_cells segs m B [c].
Proof.
  intros segs m A pre c post B H ->. apply rw_cells_app in H. destruct H as [_ H].
  change (c :: post) with ([c] ++ post) in H. apply rw_cells_app in H. exact (proj1 H).
Qed.

Lemma rw_cells_C8_CB : forall segs m A (v : word), rw_cells segs m A [C8 v] -> exists bs, rw_cells segs m A [CB 8 bs].
Proof. intros segs m A v H. destruct (rw_cells_forget _ _ _ _ H) as [bs Hb]. exists bs. exact Hb. Qed.

Lemma align8_walk0 : forall z, 0 <= z < 2^47 -> Z.land (2147450880 + Z.shiftr z 3) 18446744073709551608 = sh z - sh z mod 8.
Proof. intros z Hz. rewrite <- (align8_walk z Hz). rewrite shiftr3_div. rewrite Z.mod_small; [reflexivity|]. Z.div_mod_to_equations. lia. Qed.
Lemma align8_walk2 : forall z, 0 <= z < 2^47 ->
  Z.land (Z.land (2147450880 + Z.shiftr z 3) 18446744073709551615) 18446744073709551608 = sh z - sh z mod 8.
Proof.
  intros z Hz. rewrite <- (align8_walk0 z Hz). f_equal.
  change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite shiftr3_div. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.
Tactic Notation "probe8_regx" constr(r) constr(RD) constr(x) ident(w) ident(Pw) :=
  let a := reg_val r in
  lazymatch a with Z_to_bv 64 ?e =>
    lazymatch type of RD with sh_readable ?mm ?A ?nn =>
      destruct (probe8_at mm A nn x e RD ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(first [ apply align8_walk; lia | apply align8_walk'; lia | apply align8_walk0; lia | apply align8_walk2; lia ])) as [w Pw]
    end end.
