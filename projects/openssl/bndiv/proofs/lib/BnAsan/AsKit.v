(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SHLO : Z := 2147450880.          (* [comment removed for export] *)
Definition SHHI : Z := 17594333495296.      (* [comment removed for export] *)

Lemma shad_range : forall a, 0 <= a < 140737488355328 -> SHLO <= shad a < SHHI.
Proof. intros a Ha. unfold shad, SHB, SHLO, SHHI. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Fixpoint offshW (W : list ivl) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => (hi <= SHLO \/ SHHI <= lo) /\ offshW W'
  end.

Lemma offshW_outside : forall W x, offshW W -> SHLO <= x < SHHI -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x H Hx; [exact I|].
  destruct H as [H1 H2]. split; [lia| exact (IH x H2 Hx)].
Qed.

Lemma z8_of_unsigned0 : forall b : byte, bv_unsigned b = 0 -> b = z8.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma acc_gran0 : forall m a n g,
  acc segs m a n -> g mod 8 = 0 -> a <= g -> g + 8 <= a + n -> bytes_at segs m (shad g) [z8].
Proof.
  intros m a n g H Hg H1 H2.
  destruct (H (g + 7 - a) ltac:(lia)) as (b & Hb & Hok).
  replace (a + (g + 7 - a)) with (g + 7) in * by lia.
  assert (Es : shad (g + 7) = shad g) by (unfold shad; f_equal; Z.div_mod_to_equations; lia).
  rewrite Es in Hb.
  assert (E7 : (g + 7) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  destruct Hok as [H0|[H3 H4]]; [| rewrite E7 in H4; lia].
  rewrite (z8_of_unsigned0 b H0) in Hb. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma acc_munch : forall W m m1 a n,
  acc segs m a n -> munch W m m1 -> offshW W -> 0 <= a -> a + n <= 140737488355328 -> acc segs m1 a n.
Proof.
  intros W m m1 a n H MU OFF Ha Hn i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
  eapply bytes_at_transport; [exact Hb | exact MU |].
  pose proof (shad_range (a + i) ltac:(lia)) as R. cbn [length].
  assert (O : forall x, shad (a + i) <= x < shad (a + i) + Z.of_nat 1 -> outside W x)
    by (intros x Hx; apply offshW_outside; [exact OFF | lia]).
  clear - O. revert O. generalize (shad (a + i)) as A. induction W as [|[lo hi] W IH]; cbn; intros A O; [exact I|].
  split.
  - destruct (O A ltac:(lia)) as [O1 _]. lia.
  - apply IH. intros x Hx. exact (proj2 (O x Hx)).
Qed.

(* [comment removed for export] *)
Lemma acc_rd0 : forall W m m1 a n g ad,
  acc segs m a n -> munch W m m1 -> offshW W ->
  g mod 8 = 0 -> a <= g -> g + 8 <= a + n -> 0 <= g < 140737488355328 ->
  ad = wa (shad g) ->
  ov_read_bytes segs m1 ad 1 = Some [z8].
Proof.
  intros W m m1 a n g ad H MU OFF Hg H1 H2 R ->.
  pose proof (acc_gran0 m a n g H Hg H1 H2) as B.
  assert (B1 : bytes_at segs m1 (shad g) [z8]).
  { eapply bytes_at_transport; [exact B | exact MU |]. cbn [length].
    pose proof (shad_range g R) as RS.
    assert (O : forall x, shad g <= x < shad g + Z.of_nat 1 -> outside W x)
      by (intros x Hx; apply offshW_outside; [exact OFF | lia]).
    clear - O. revert O. generalize (shad g) as A. induction W as [|[lo hi] W IH]; cbn; intros A O; [exact I|].
    split.
    - destruct (O A ltac:(lia)) as [O1 _]. lia.
    - apply IH. intros x Hx. exact (proj2 (O x Hx)). }
  pose proof (bytes_at_read segs m1 (shad g) [z8] 0 1 B1 ltac:(lia) ltac:(cbn; lia)) as RD.
  rewrite Z.add_0_r in RD. exact RD.
Qed.

(* [comment removed for export] *)
Lemma acc_rd0_same : forall m a n g ad,
  acc segs m a n -> g mod 8 = 0 -> a <= g -> g + 8 <= a + n -> 0 <= g ->
  ad = wa (shad g) ->
  ov_read_bytes segs m ad 1 = Some [z8].
Proof.
  intros m a n g ad H Hg H1 H2 R ->.
  pose proof (acc_gran0 m a n g H Hg H1 H2) as B1.
  pose proof (bytes_at_read segs m (shad g) [z8] 0 1 B1 ltac:(lia) ltac:(cbn; lia)) as RD.
  rewrite Z.add_0_r in RD. exact RD.
Qed.

End WithSegs.

(* [comment removed for export] *)
Lemma zxb_z8 : zxb z8 = Z_to_bv 64 0.
Proof. reflexivity. Qed.
Lemma sxb_z8 : sxb z8 = Z_to_bv 64 0.
Proof. reflexivity. Qed.
