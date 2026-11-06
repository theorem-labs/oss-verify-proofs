From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ls_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ls_signed : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in *.
  destruct (Z.ltb_spec (z mod 18446744073709551616) 9223372036854775808); cbv iota;
    Z.div_mod_to_equations; lia.
Qed.

Lemma ls_slliw1 : forall z, 0 <= z < 2 ^ 30 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 1)) = Z_to_bv 64 (2 * z).
Proof.
  intros z Hz. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2 ^ 1) with 2. change (2 ^ 30) with 1073741824 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ls_slli4 : forall z, 0 <= z < 2 ^ 59 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 4) = Z_to_bv 64 (16 * z).
Proof. intros z Hz. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

Lemma ls_idx : forall V N, 0 <= N < 2 ^ 59 ->
  Z_to_bv 64 (V + Z.shiftl (bv_unsigned (Z_to_bv 64 N)) 4) = Z_to_bv 64 (V + 16 * N).
Proof. intros V N H. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

Ltac ls_cond0 :=
  first [ reflexivity
        | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
        | apply Z.leb_le; lia | apply Z.leb_gt; lia ].

Ltac ls_cond :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?unsigned_lit by lia; rewrite ?ls_signed by lia;
  cbn [negb];
  first [ ls_cond0
        | apply (proj2 (Bool.negb_true_iff _)); ls_cond0
        | apply (proj2 (Bool.negb_false_iff _)); ls_cond0 ].

Ltac br c :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?x then _ else _) ?fc ?rv ?m ?ro) =>
      replace x with c; [cbv iota | symmetry; ls_cond]
  end.

Lemma ls_cut : forall segs m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[W B] (H0 & H1 & H)].
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in H1, H.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
Qed.

Lemma ls_join : forall segs m A B cs1 cs2, rw_cells segs m A cs1 -> rw_cells segs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A B cs1 cs2 [[W1 B1] (H0 & H1 & H)] [[W2 B2] (G0 & G1 & G)] ->.
  split; split.
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - lia.
  - rewrite cells_size_app. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hlt|Hge]; [apply H; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G. lia.
Qed.

Lemma ls_rw_nil : forall segs m A, 0 <= A <= 2 ^ 64 -> rw_cells segs m A [CB 0 []].
Proof.
  intros segs m A H. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes app]. apply bytes_at_nil. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.
