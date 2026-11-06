(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Cells Exec Frame Step Tac ZBridge Arr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F9 Require Import F_memcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma lor40' : forall x, Z.land (Z.lor 40 x) 15 = 0 -> False.
Proof.
  intros x E. assert (T : Z.testbit (Z.land (Z.lor 40 x) 15) 3 = true).
  { rewrite Z.land_spec, Z.lor_spec. replace (Z.testbit 40 3) with true by reflexivity. reflexivity. }
  rewrite E in T. discriminate.
Qed.
Lemma le1_lit0 : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].  Proof. reflexivity. Qed.

Section MS40.
Variables ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variables (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (S : Z).
Hypothesis HS : 0 <= S /\ S + 40 <= 2 ^ 64 - 64.

Definition ms40_post : machine_state -> Prop :=
  fun ms' => exists a2' a3' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 0) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(S, S + 40)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ rw_cells rsegs m' S [CB 40 (repeat (Z_to_bv 8 0) 40)].

Lemma ms40_loop : forall (n : nat) (i : Z) (m : word -> option byte) (bs : list byte) (a3v : word),
  a3v = Z_to_bv 64 (S + i) ->
  Z.to_nat (40 - i) = n -> 0 <= i < 40 -> u8arr rsegs m S bs -> length bs = 40%nat ->
  (forall k, (k < Z.to_nat i)%nat -> nth_error bs k = Some (Z_to_bv 8 0)) ->
  munch [(S, S + 40)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs ms40_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (S + 40)) a3v a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x92a18) fc None m (seg_rom rsegs)).
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros i m bs a3v -> Hn Hi BU BL HZ MU WM MI.
  pose proof (u8arr_store_ok rsegs m S bs i (Z_to_bv 64 (S + i)) BU ltac:(rewrite BL; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zstep. rewrite le1_lit0.
  replace (Z_to_bv 64 (S + i)) with (wa (S + i)) by (unfold wa; reflexivity).
  pose proof (u8arr_write rsegs m S bs i (Z_to_bv 8 0) BU ltac:(rewrite BL; lia)) as BU'.
  clear BU. store_done.
  set (bs' := upd bs (Z.to_nat i) (Z_to_bv 8 0)) in *.
  assert (BL' : length bs' = 40%nat) by (unfold bs'; rewrite upd_length; exact BL).
  assert (HZ' : forall k, (k < Z.to_nat (i + 1))%nat -> nth_error bs' k = Some (Z_to_bv 8 0)).
  { intros k Hk. unfold bs'. destruct (Nat.eq_dec k (Z.to_nat i)) as [->|Hne].
    - apply nth_error_upd_same. lia.
    - rewrite nth_error_upd_other by lia. apply HZ. lia. }
  zstep. zstep. if_cases K1; zify_cond K1.
  -
    eapply (IH (Z.to_nat (40 - (i + 1))) ltac:(lia) (i + 1)); [f_equal; lia | reflexivity | lia | exact BU' | exact BL' | exact HZ' | assumption | assumption | assumption].
  -
    assert (Hi39 : i = 39) by lia. subst i.
    zstep. zstep.
    apply evt_done. unfold ms40_post. do 3 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|].
    assert (E : bs' = repeat (Z_to_bv 8 0) 40).
    { apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k 40) as [Hk|Hk].
      - rewrite HZ' by (cbn; lia). rewrite nth_error_repeat by exact Hk. reflexivity.
      - rewrite (proj2 (nth_error_None bs' k)) by lia. rewrite (proj2 (nth_error_None (repeat (Z_to_bv 8 0) 40) k)) by (rewrite repeat_length; lia). reflexivity. }
    pose proof (rw_cells_of_u8arr rsegs _ _ _ BU') as X. rewrite BL', E in X. exact X.
Qed.

Theorem ms40_call : forall (j : list byte) (a3 : word), rw_cells rsegs m0 S [CB 40 j] -> mem_inv rsegs m0 ->
  evt rsegs ms40_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 40) a3 a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x92a00) fc None m0 (seg_rom rsegs)).
Proof.
  intros j a3 FR MI. pose proof (u8arr_of_rw_cells rsegs _ _ _ _ FR) as BU.
  assert (BL : length j = 40%nat) by (destruct FR as [[[H _] _] _]; exact H). clear FR.
  zstep. zstep. zstep. if_cases K1; zify_cond K1; [exfalso; exact (lor40' _ K1) |].
  zstep. if_cases K2; zify_cond K2; [exfalso; lia |].
  zstep. zstep.
  eapply (ms40_loop (Z.to_nat 40) 0 m0 j); [f_equal; lia | reflexivity | lia | exact BU | exact BL | intros k Hk; cbn in Hk; lia | apply munch_refl | apply wmono_refl | exact MI].
Qed.
End MS40.
