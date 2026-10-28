(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import AsStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma acc_rd1 : forall W m m1 a n X ad,
  acc segs m a n -> munch W m m1 -> offshW W ->
  a <= X < a + n -> 0 <= X < 140737488355328 ->
  ad = wa (shad X) ->
  exists b, ov_read_bytes segs m1 ad 1 = Some [b] /\ sh_ok b X.
Proof.
  intros W m m1 a n X ad ACC MU OFF HX R ->.
  destruct (ACC (X - a) ltac:(lia)) as (b & Hb & Hok). replace (a + (X - a)) with X in * by lia.
  exists b. split; [| exact Hok].
  assert (B1 : bytes_at segs m1 (shad X) [b]).
  { eapply bytes_at_transport; [exact Hb | exact MU |]. cbn [length].
    pose proof (shad_range X R) as RS.
    assert (O : forall x, shad X <= x < shad X + Z.of_nat 1 -> outside W x)
      by (intros x Hx; apply offshW_outside; [exact OFF | lia]).
    clear - O. revert O. generalize (shad X) as A. induction W as [|[lo hi] W IH]; cbn; intros A O; [exact I|].
    split.
    - destruct (O A ltac:(lia)) as [O1 _]. lia.
    - apply IH. intros x Hx. exact (proj2 (O x Hx)). }
  pose proof (bytes_at_read segs m1 (shad X) [b] 0 1 B1 ltac:(lia) ltac:(cbn; lia)) as RD.
  rewrite Z.add_0_r in RD. exact RD.
Qed.

End WithSegs.

Lemma sxb_small : forall b : byte, 0 <= bv_unsigned b < 128 -> sxb b = Z_to_bv 64 (bv_unsigned b).
Proof.
  intros b Hb. unfold sxb. f_equal. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (256 `div` 2) with 128. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma sh_ok_cases : forall (b : byte) X, sh_ok b X ->
  b = z8 \/ (exists k, 0 < k < 8 /\ X mod 8 < k /\ sxb b = Z_to_bv 64 k /\ zxb b = Z_to_bv 64 k).
Proof.
  intros b X [H0|[H1 H2]]; [left; apply z8_of_unsigned0; exact H0 | right].
  exists (bv_unsigned b). split; [exact H1|]. split; [exact H2|]. split; [apply sxb_small; lia|].
  unfold zxb. reflexivity.
Qed.

Lemma land7_mod8 : forall X, 0 <= X -> Z.land X 7 = X mod 8.
Proof. intros X HX. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Ltac shl1 b OK :=
  let ad := cur_mem_addr in
  let X := sh_X ad in
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
    first [
      match goal with
      | ACC : acc segs ?mb ?a ?n, MU : munch ?W ?mb mc |- _ =>
          let RD := fresh "RDsh" in
          destruct (acc_rd1 segs W mb mc a n X ad ACC MU ltac:(shl_off) ltac:(lia) ltac:(lia) ltac:(sh_addr_s)) as (b & RD & OK);
          step; clear RD
      end
    | fail 1 "shl1: no (acc, munch) pair in the context covers the byte at" X ]
  end.
