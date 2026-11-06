(* Ported by RtStr from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Spec/StrBytes.v, unchanged. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_manifest/lib/A/Spec/StrBytes.v for reac-pw/fuzz_segconf.asan-ubsan (image B), with its module paths changed. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Arr.
Import ListNotations.
Open Scope Z_scope.

Lemma sb_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R. Qed.

Lemma sb_u_byte : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intros b. apply unsigned_lit. pose proof (sb_byte_range b). lia. Qed.

Lemma sb_u_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. exact sb_u_byte. Qed.

Lemma sb_nth_full : forall (s : list byte) i, (i <= length s)%nat -> exists b, nth_error (s ++ [Z_to_bv 8 0]) i = Some b.
Proof.
  intros s i H. destruct (nth_error (s ++ [Z_to_bv 8 0]) i) as [b|] eqn:E; [eauto|].
  apply nth_error_None in E. rewrite length_app in E. cbn in E. lia.
Qed.

Lemma sb_nth_full_zero : forall (s : list byte) i b, ~ In (Z_to_bv 8 0) s ->
  nth_error (s ++ [Z_to_bv 8 0]) i = Some b -> (bv_unsigned b = 0 <-> i = length s).
Proof.
  intros s i b NZ E. pose proof (nth_error_lt _ _ _ E) as Hl. rewrite length_app in Hl. cbn in Hl.
  destruct (Nat.eq_dec i (length s)) as [->|NE].
  - rewrite nth_error_app2, Nat.sub_diag in E by lia. cbn in E. inversion E; subst. split; reflexivity.
  - rewrite nth_error_app1 in E by lia. split; [|intros; lia]. intros Hb. exfalso. apply NZ.
    replace (Z_to_bv 8 0) with b; [eapply nth_error_In; eauto|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma sb_rd1 : forall segs m (A : Z) (bs : list byte) (i : nat) (b : byte) (a : word),
  bytes_at segs m A bs -> nth_error bs i = Some b -> bv_unsigned a = A + Z.of_nat i ->
  ov_read_bytes segs m a 1 = Some [b].
Proof.
  intros segs m A bs i b a H E Ha.
  apply (u8ro_read segs m A bs (Z.of_nat i) b a H); [rewrite Nat2Z.id; exact E | lia |].
  unfold wa. rewrite <- Ha. symmetry. apply Z_to_bv_lit_self.
Qed.

Ltac sb_fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
