(* Relocated from libreac/fuzz_decode lib/B/Prog/reac_frame_clean_len_F.v (origin/ossv/recipes 98c99a85e4) to reac-repacer/fuzz_wire
   image B: entry 0x8158c -> 0x818e8, constants 0x10310 -> 0x10300 and 0x103c8 -> 0x103b0, module paths changed. A byte compare
   gives the two functions equal modulo pc-relative offsets and both 8-byte constants byte-equal. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import reac_frame_clean_len_c reac_frame_clean_len.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import reac_frame_clean_len_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The proof of reac_frame_clean_len_holds (reac_frame_clean_len.v) step for step, with StepF's step: the two 8-byte
   loads at A_M and A_T are closed from the rng premises of reac_frame_clean_len_contract_F; no other step reads or
   writes memory. The arithmetic lemmas rot_wrap and c2 come from reac_frame_clean_len.v. *)
Theorem reac_frame_clean_len_holds_F : reac_frame_clean_len_contract_F.
Proof.
  unfold reac_frame_clean_len_contract_F, REAC_FRAME_CLEAN_LEN, A_M, A_T.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HM HT
    RRM RRT.
  assert (RM : ov_read_bytes rsegs m (wa 0x10300) 8 = Some (le8 (Z_to_bv 64 KM))).
  { replace (wa 0x10300) with (wa (0x10300 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 0x10300 _ 0 8 HM ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  assert (RT : ov_read_bytes rsegs m (wa 0x103b0) 8 = Some (le8 (Z_to_bv 64 KT))).
  { replace (wa 0x103b0) with (wa (0x103b0 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 0x103b0 _ 0 8 HT ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  step. step.
  if_cases HC.
  - step.
    replace (Z_to_bv 64 (reac_frame_clean_len_model (bv_unsigned a0))) with a0.
    + apply evtF_done. do 3 eexists. reflexivity.
    + unfold bv_ltu in HC. rewrite (unsigned_lit 54) in HC by lia. apply Z.ltb_lt in HC.
      unfold reac_frame_clean_len_model. rewrite (proj2 (Z.leb_gt 54 (bv_unsigned a0)) HC). cbn [andb].
      symmetry. apply Z_to_bv_lit_self.
  - assert (Hn : 54 <= bv_unsigned a0 < 2^64).
    { unfold bv_ltu in HC. rewrite (unsigned_lit 54) in HC by lia. apply Z.ltb_ge in HC.
      pose proof (bv_unsigned_in_range 64 a0) as Hr. unfold bv_modulus in Hr. lia. }
    step. step. step. step. step. step. step. step. step. step. step. step. step. step.
    match goal with |- context [Z_to_bv 64 (bv_unsigned a0 + ?E)] =>
      replace (Z_to_bv 64 (bv_unsigned a0 + E)) with (Z_to_bv 64 (reac_frame_clean_len_model (bv_unsigned a0))) end.
    + apply evtF_done. do 3 eexists. reflexivity.
    + rewrite v_sltu_b2z. rewrite (unsigned_lit KM) by (unfold KM; lia).
      rewrite !unsigned_lit_wrap. rewrite rot_wrap. rewrite (Z.mod_small KT) by (unfold KT; lia).
      set (n := bv_unsigned a0) in *. clearbody n.
      destruct (c2 n Hn) as [C1 C2].
      unfold reac_frame_clean_len_model. rewrite (proj2 (Z.leb_le 54 n)) by lia. cbn [andb].
      match goal with |- context [Z.ltb ?A ?B] => destruct (Z.ltb_spec A B) as [L | L] end;
        cbn [Z.b2z];
        match goal with |- context [Z.land ?X 18446744073709551614] =>
          let v := eval vm_compute in (Z.land X 18446744073709551614) in change (Z.land X 18446744073709551614) with v end.
      * rewrite (proj2 (Z.eqb_eq _ 2) (C1 L)). cbv iota.
        apply bv_eq. rewrite !unsigned_lit_wrap.
        replace (n + 18446744073709551614) with ((n - 2) + 1 * 2^64) by lia.
        rewrite Z.mod_add by lia. reflexivity.
      * assert (N : (n - 52) mod 36 <> 2) by (intro E; specialize (C2 E); lia).
        rewrite (proj2 (Z.eqb_neq _ 2) N). cbv iota. f_equal. lia.
Qed.

(* The old contract from the footprint twin, with the footprint ExecF.RNG_all that holds every access. *)
Theorem reac_frame_clean_len_holds_of_F : reac_frame_clean_len_contract.
Proof.
  unfold reac_frame_clean_len_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HM HT.
  pose proof reac_frame_clean_len_holds_F as HF. unfold reac_frame_clean_len_contract_F in HF.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply HF; try assumption.
  - apply ExecF.rng_all; unfold A_M; lia.
  - apply ExecF.rng_all; unfold A_T; lia.
Qed.
