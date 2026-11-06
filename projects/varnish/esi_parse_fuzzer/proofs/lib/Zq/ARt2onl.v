(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AIcpm9j AIcp2qw AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma imemset_byte_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (n : nat) (junk : list byte),
  rw_cells rsegs m (bv_unsigned a0) [CB n junk] -> (bv_unsigned a0 + Z.of_nat n < 2^64)%Z ->
  bv_unsigned a2 = Z.of_nat n -> (1 <= n)%nat ->
  (Z.land (Z.lor (Z.of_nat n) (bv_unsigned a0)) 15 <> 0)%Z ->
  mem_inv rsegs m ->
  evt rsegs (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 (bv_unsigned a1 mod 256) n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6a170) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros DST A64 N EN1 NB MI.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + Z.of_nat n)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (rw_CB_length _ _ _ _ _ DST) as LJ.
  pose proof (zr_word a0) as R0; unfold inr64 in R0. pose proof (zr_word a2) as R2; unfold inr64 in R2.
  zstep. zstep.
  zstep. if_cases K0; zify_cond K0.
  { exfalso. rewrite N in K0. apply NB. rewrite <- K0. reflexivity. }
  zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
  zstep. zstep. rewrite N.
  eapply (ims_loop ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m _ n junk eq_refl LJ ltac:(lia) (n - 0)%nat 0%Z);
    try eassumption; try lia.
  - rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
  - cbn [Z.to_nat repeat skipn app]. exact (u8arr_of_rw_cells _ _ _ _ _ DST).
Qed.

(* [comment removed for export] *)
Lemma upd_repeat_skipn_w : forall (w : word) (ws : list word) (j : nat),
  (j < length ws)%nat -> upd (repeat w j ++ skipn j ws) j w = repeat w (S j) ++ skipn (S j) ws.
Proof.
  intros w ws j Hj.
  rewrite upd_firstn_skipn by (rewrite length_app, repeat_length, length_skipn; lia).
  rewrite firstn_app, repeat_length, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by (rewrite repeat_length; lia).
  rewrite skipn_app, repeat_length. replace (S j - j)%nat with 1%nat by lia.
  rewrite skipn_all2 by (rewrite repeat_length; lia). cbn [app].
  rewrite skipn_skipn. replace (1 + j)%nat with (S j) by lia.
  replace (repeat w (S j)) with (repeat w j ++ [w]) by (replace (S j) with (j + 1)%nat by lia; rewrite repeat_app; reflexivity).
  rewrite <- app_assoc. reflexivity.
Qed.

Definition imemset16_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (k : nat) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(A, A + 8 * Z.of_nat k)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ u64arr rsegs m' A (repeat (Z_to_bv 64 0) k).

Section IMS16.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z) (k : nat) (ws : list word).
  Hypothesis LW : length ws = k.
  Hypothesis KE : Nat.Even k.
  Hypothesis AB : 0 <= A /\ A + 8 * Z.of_nat k < 2^64.
  Notation W := [(A, A + 8 * Z.of_nat k)].
  Notation POST := (imemset16_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A k m).

  #[using="AB KE LW"] Lemma ims16_loop : forall (r : nat) (j : nat) (m1 : word -> option byte),
    (k - j <= 2 * r)%nat -> (j + 2 <= k)%nat -> Nat.Even j ->
    u64arr rsegs m1 A (repeat (Z_to_bv 64 0) j ++ skipn j ws) ->
    mem_inv rsegs m1 -> munch W m m1 -> wmono rsegs m m1 ->
    evt rsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 (A + 8 * Z.of_nat k)) (Z_to_bv 64 (A + 8 * Z.of_nat j)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6a1bc) fc None m1 (seg_rom rsegs)).
  Proof.
    induction r as [|r IH]; intros j m1 Hr Hj HE ARR MI MU WM; [lia|].
    destruct (proj1 (Nat.Even_double _) HE) as [hj Hhj] || pose proof HE as Hhj.
    assert (LA : length (repeat (Z_to_bv 64 0) j ++ skipn j ws) = k).
    { rewrite length_app, repeat_length, length_skipn. lia. }
    (* [comment removed for export] *)
    pose proof (u64arr_store_ok rsegs _ _ _ (Z.of_nat j) (Z_to_bv 64 (A + 8 * Z.of_nat j)) ARR ltac:(rewrite LA; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mq ?a ?bs) _) =>
      change (write_to_mem mq a bs) with (write_to_mem mq (wa (A + 8 * Z.of_nat j)) bs) end.
    pose proof (u64arr_write rsegs _ _ _ (Z.of_nat j) (Z_to_bv 64 0) ARR ltac:(rewrite LA; lia)) as ARR2. clear ARR.
    store_done. try clear SOK.
    rewrite Nat2Z.id, upd_repeat_skipn_w in ARR2 by lia.
    assert (LA2 : length (repeat (Z_to_bv 64 0) (S j) ++ skipn (S j) ws) = k).
    { rewrite length_app, repeat_length, length_skipn. lia. }
    (* [comment removed for export] *)
    pose proof (u64arr_store_ok rsegs _ _ _ (Z.of_nat (S j)) (Z_to_bv 64 (A + 8 * Z.of_nat j + 8)) ARR2 ltac:(rewrite LA2; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mq ?a ?bs) _) =>
      replace (write_to_mem mq a bs) with (write_to_mem mq (wa (A + 8 * Z.of_nat (S j))) bs) by (unfold wa; f_equal; f_equal; lia) end.
    pose proof (u64arr_write rsegs _ _ _ (Z.of_nat (S j)) (Z_to_bv 64 0) ARR2 ltac:(rewrite LA2; lia)) as ARR3. clear ARR2.
    store_done. try clear SOK.
    rewrite Nat2Z.id, upd_repeat_skipn_w in ARR3 by lia.
    zstep. (* [comment removed for export] *)
    pose proof KE as KE'. apply Nat.Even_double in KE'. unfold Nat.double in KE'.
    pose proof HE as HE'. apply Nat.Even_double in HE'. unfold Nat.double in HE'.
    zstep. if_cases K; zify_cond K; rewrite ?Z.mod_small in K by lia.
    - (* [comment removed for export] *)
      replace (A + 8 * Z.of_nat j + 16) with (A + 8 * Z.of_nat (S (S j))) by lia.
      apply (IH (S (S j))); try assumption; try lia.
      apply (proj2 (Nat.Even_succ_succ j)). exact HE.
    - (* [comment removed for export] *)
      assert (E : (S (S j) = k)%nat) by lia.
      zstep.
      rewrite E, <- LW, skipn_all, app_nil_r, LW in ARR3.
      finish.
  Qed.
End IMS16.

Lemma land15_zero : forall x, 0 <= x -> x mod 16 = 0 -> Z.land x 15 = 0.
Proof. intros x Hx H. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. exact H. Qed.

Lemma imemset16_zero_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (k : nat) (ws : list word),
  u64arr rsegs m A ws -> length ws = k -> Nat.Even k -> (2 <= k)%nat -> A mod 16 = 0 -> 0 <= A -> A + 8 * Z.of_nat k < 2^64 ->
  mem_inv rsegs m ->
  evt rsegs (imemset16_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A k m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 (8 * Z.of_nat k)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6a170) fc None m (seg_rom rsegs)).
Proof.
  intros until ws. intros ARR LW KE K2 A16 A0 AB MI.
  pose proof (munch_refl [(A, A + 8 * Z.of_nat k)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof KE as KE'. apply Nat.Even_double in KE'. unfold Nat.double in KE'.
  assert (K16 : (8 * Z.of_nat k) mod 16 = 0).
  { replace (8 * Z.of_nat k) with (Z.of_nat (Nat.div2 k) * 16) by lia. apply Z_mod_mult. }
  amz. amz. rewrite Z.land_lor_distr_l, (land15_zero A), (land15_zero (8 * Z.of_nat k)) by lia. cbn [Z.lor].
  amz. if_true. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  do 7 amz. cbn [Z.shiftl Z.lor].
  amz. (* [comment removed for export] *)
  replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 8 * Z.of_nat 0)) at 1 by (f_equal; lia).
  eapply (ims16_loop ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A k ws LW KE ltac:(lia) k 0%nat);
    try eassumption; try lia.
  all: try (exists 0%nat; reflexivity).
  all: try (cbn [repeat skipn app]; exact ARR).
Qed.
