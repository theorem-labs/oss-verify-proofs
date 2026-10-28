(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition shz (m : mem) (a n : Z) : Prop :=
  forall x, a <= x < a + n -> ov_read_bytes bsegs m (wa (x / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0].

Lemma shz_sub : forall m a n a' n', shz m a n -> a <= a' -> a' + n' <= a + n -> shz m a' n'.
Proof. intros m a n a' n' H H1 H2 x Hx. apply H. lia. Qed.

Lemma shz_of_acc : forall m a n, acc bsegs m a n -> a mod 8 = 0 -> 0 <= a -> shz m a (8 * (n / 8)).
Proof.
  intros m a n AC A8 A0 x Hx.
  assert (N0 : 0 <= n / 8) by (destruct (Z_lt_dec n 0) as [L|L]; [|apply Z.div_pos; lia];
                                 assert (n / 8 < 0) by (apply Z.div_lt_upper_bound; lia); lia).
  pose proof (Z.div_mod x 8 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as MX.
  pose proof (Z.div_mod a 8 ltac:(lia)) as DA. pose proof (Z.div_mod n 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as MN.
  set (g := 8 * (x / 8)) in *.
  assert (G : a <= g /\ g + 8 <= a + 8 * (n / 8)).
  { rewrite A8 in DA.
    assert (a / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    assert (x / 8 < a / 8 + n / 8).
    { apply Z.div_lt_upper_bound; [lia|]. lia. }
    subst g. lia. }
  destruct (AC (g + 7 - a) ltac:(lia)) as (b & HB & OK).
  replace (a + (g + 7 - a)) with (g + 7) in HB, OK by lia.
  assert (SH : shad (g + 7) = x / 8 + 2147450880).
  { unfold shad, SHB. f_equal. subst g. symmetry. apply Z.div_unique with (r := 7); lia. }
  rewrite SH in HB.
  assert (M7 : (g + 7) mod 8 = 7).
  { subst g. replace (8 * (x / 8) + 7) with (7 + (x / 8) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  assert (B0 : b = Z_to_bv 8 0).
  { destruct OK as [Z0 | (R1 & R2)]; [| rewrite M7 in R2; lia].
    apply bv_eq. rewrite Z0. reflexivity. }
  subst b.
  pose proof (bytes_at_read bsegs m _ _ 0 1 HB ltac:(lia)) as R.
  rewrite Z.add_0_r in R. apply R. cbn. lia.
Qed.

Lemma sxb_z8 : sxb (Z_to_bv 8 0) = Z_to_bv 64 0.
Proof. reflexivity. Qed.
Lemma zxb_z8 : zxb (Z_to_bv 8 0) = Z_to_bv 64 0.
Proof. reflexivity. Qed.

Lemma lbu_z8 : Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0)) = Z_to_bv 64 0.
Proof. reflexivity. Qed.

Ltac shz_norm := cbv beta; rewrite ?sxb_z8, ?lbu_z8.

Lemma shr3_div : forall x, Z.shiftr x 3 = x / 8.
Proof. intros x. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Ltac shz_pose_with H x name :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      first [ pose proof (H x ltac:(lia)) as name
            | lazymatch goal with
              | MU : munch _ ?m0 m, WM : wmono _ ?m0 m |- _ => pose proof (H m MU WM x ltac:(lia)) as name
              end ]
  end.
Tactic Notation "shz_pose" constr(H) constr(x) := let name := fresh "SHRD" in shz_pose_with H x name.
