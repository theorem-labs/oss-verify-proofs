(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec SymStepR StepTac StoreOk AgentLib StartupTac StartupAux RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import BothRPLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import Both_code_depot2 BothDepotMem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.BothRPLib.gr ::= gr_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac nz := gr; rewrite ?getr_zero; pin; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_zbv by lia; rewrite ?v_add_zbv by lia; rewrite ?Z.add_0_r.
(* [comment removed for export] *)
Ltac ai F D := stepi F D; vals_lit; nz; vals_lit.
(* [comment removed for export] *)
Ltac ast F D aa vv okt := stw F D aa vv okt.
(* [comment removed for export] *)
Ltac peelz := repeat (rewrite rdn_wbytes_out by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)).
Ltac hit8 :=
  lazymatch goal with |- rdn _ (wbytes _ ?a' (word_to_le_bytes 8 ?v')) ?a 8 = Some (word_to_le_bytes 8 ?v) =>
    (tryif constr_eq a a' then idtac else replace a with a' by (f_equal; lia));
    (tryif constr_eq v v' then idtac else replace v with v' by (first [congruence | f_equal; lia])) end;
  apply rdn_wbytes_hit8; unorm; lia.
(* [comment removed for export] *)
Ltac ald F D vv pre := ld_step F D (word_to_le_bytes 8 vv) vv ltac:(pre; peelz; hit8) ltac:(apply bytes_le_to_Z_8).
(* [comment removed for export] *)
Ltac okw H := apply okr_store_ok; [lia | cbn; lia | repeat apply okr_wbytes; eapply okr_sub; [exact H | lia | lia] ].

Lemma ret_ok_lit : forall z, (0 <= z < 2 ^ 64)%Z -> (z mod 2 = 0)%Z -> ret_ok (Z_to_bv 64 z).
Proof. intros. apply ret_ok_zbv; assumption. Qed.

(* [comment removed for export] *)
Lemma lock_bytes : forall t, (0 <= t < 2 ^ 31)%Z ->
  word_to_le_bytes 4 (v_or (Z_to_bv 64 t) (Z_to_bv 64 18446744071562067968)) = word_to_le_bytes 4 (Z_to_bv 64 (t + 2 ^ 31)).
Proof.
  intros t Ht. unfold word_to_le_bytes, v_or. rewrite (u64_lit t), (u64_lit 18446744071562067968) by lia.
  assert (HL : Z.lor t 18446744071562067968 = (t + 18446744071562067968)%Z).
  { rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor; try reflexivity;
    change 18446744071562067968%Z with ((2 ^ 33 - 1) * 2 ^ 31)%Z; apply land_low_high; lia. }
  rewrite HL. rewrite (u64_lit (t + 18446744071562067968)), (u64_lit (t + 2 ^ 31)) by lia.
  rewrite (Z_to_le_bytes_mod 4 (t + _)), (Z_to_le_bytes_mod 4 (t + 2 ^ 31)). f_equal.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z.
  replace (t + 18446744071562067968)%Z with (t + 2 ^ 31 + (2 ^ 32 - 1) * 2 ^ 32)%Z by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Section LOCK.
  Variables (mem rom : word -> option byte) (usp p t : Z) (ret : word).
  Hypothesis Husp : (48 <= usp)%Z /\ (usp < 2 ^ 64)%Z.
  Hypothesis Hstk : okr mem (usp - 40) 40.
  Hypothesis Hp : (0 <= p)%Z /\ (p + 4 < 2 ^ 64)%Z /\ (p mod 4 = 0)%Z.
  Hypothesis Hcell : cell32 mem p t.
  Hypothesis Ht : (t < 2 ^ 31)%Z.
  Hypothesis Hokp : okr mem p 4.
  Hypothesis Hdisj : (p + 4 <= usp - 40 \/ usp <= p)%Z.
  Hypothesis Hret : ret_ok ret.

  Definition lock_frame (vra v8 v9 v18 v19 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes mem
      (Z_to_bv 64 (usp - 8)) (word_to_le_bytes 8 vra))
      (Z_to_bv 64 (usp - 16)) (word_to_le_bytes 8 v8))
      (Z_to_bv 64 (usp - 24)) (word_to_le_bytes 8 v9))
      (Z_to_bv 64 (usp - 32)) (word_to_le_bytes 8 v18))
      (Z_to_bv 64 (usp - 40)) (word_to_le_bytes 8 v19).
  Definition lock_mem (vra v8 v9 v18 v19 : word) : word -> option byte :=
    wbytes (lock_frame vra v8 v9 v18 v19) (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 (t + 2 ^ 31))).
  #[local] Abbreviation LM regs := (lock_mem (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).

  #[using="Husp Hstk Hp Hcell Ht Hokp Hdisj Hret"] Theorem lock_walk : forall regs,
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 p ->
    exists regs',
      msteps SEGS (mkst regs (0x75488 : word) mem rom) (mkst regs' ret (LM regs) rom)
      /\ getr regs' 10 = Z_to_bv 64 t /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ret
      /\ (forall r, r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> getr regs' r = getr regs r).
  Proof.
    intros regs H1 H2 H10. destruct Hcell as [Hc Htn]. cbn in Htn.
    eexists. split.
    - (* [comment removed for export] *)
      ai F_75488 D_75488.
      (* [comment removed for export] *)
      ast F_7548c D_7548c (Z_to_bv 64 (usp - 8)) (getr regs 1) ltac:(okw Hstk).
      ast F_75490 D_75490 (Z_to_bv 64 (usp - 16)) (getr regs 8) ltac:(okw Hstk).
      ast F_75494 D_75494 (Z_to_bv 64 (usp - 24)) (getr regs 9) ltac:(okw Hstk).
      ast F_75498 D_75498 (Z_to_bv 64 (usp - 32)) (getr regs 18) ltac:(okw Hstk).
      ast F_7549c D_7549c (Z_to_bv 64 (usp - 40)) (getr regs 19) ltac:(okw Hstk).
      match goal with |- context [wbytes (wbytes (wbytes (wbytes (wbytes mem _ (word_to_le_bytes 8 ?a)) _ (word_to_le_bytes 8 ?b)) _ (word_to_le_bytes 8 ?c)) _ (word_to_le_bytes 8 ?d)) _ (word_to_le_bytes 8 ?e)] =>
        change (wbytes (wbytes (wbytes (wbytes (wbytes mem _ (word_to_le_bytes 8 a)) _ (word_to_le_bytes 8 b)) _ (word_to_le_bytes 8 c)) _ (word_to_le_bytes 8 d)) _ (word_to_le_bytes 8 e))
        with (lock_frame a b c d e) end.
      (* [comment removed for export] *)
      ai F_754a0 D_754a0.
      ai F_754a4 D_754a4.
      ai F_754a8 D_754a8.
      ai F_754ac D_754ac.
      (* [comment removed for export] *)
      ld_step F_754b0 D_754b0 (word_to_le_bytes 4 (Z_to_bv 64 t)) (Z_to_bv 64 t)
        ltac:(unfold lock_frame; peelz; rewrite ?Z.add_0_r; exact Hc)
        ltac:(rewrite bytes_le_cell by (first [cbn; lia | lia]); symmetry; apply u64_lit; lia).
      rewrite v_lw_lit by lia.
      (* [comment removed for export] *)
      stepb_tk F_754b4 D_754b4 ltac:(pin; unfold c_lts; rewrite c_lts_zbv by lia; apply Z.ltb_ge; lia).
      (* [comment removed for export] *)
      ai F_754c8 D_754c8.
      (* [comment removed for export] *)
      eapply (steps_lr_bne_sc _ _ _ rom _ _ _ _ _ _ _ 13 8 10 14 12 _ p t);
        [ exact F_754cc | reflexivity | exact D_754cc
        | exact F_754d0 | reflexivity | exact D_754d0
        | exact F_754d4 | reflexivity | exact D_754d4
        | intros E; discriminate E | intros E; discriminate E | intros E; discriminate E | intros E; discriminate E | intros E; discriminate E
        | gr; pin; reflexivity | lia | lia | lia
        | split; [unfold lock_frame; peelz; exact Hc | cbn; lia] | lia | gr; reflexivity
        | unfold lock_frame; okw Hokp | ].
      step_simpl. gr. rewrite lock_bytes by lia.
      match goal with |- context [wbytes (lock_frame ?a ?b ?c ?d ?e) ?pp ?vv] => change (wbytes (lock_frame a b c d e) pp vv) with (lock_mem a b c d e) end.
      (* [comment removed for export] *)
      stepb_ft F_754d8 D_754d8 ltac:(pin; reflexivity).
      (* [comment removed for export] *)
      stepb_tk F_754dc D_754dc ltac:(pin; unfold c_eq; rewrite bv_eqb_refl; reflexivity).
      (* [comment removed for export] *)
      ald F_754fc D_754fc ret ltac:(unfold lock_mem, lock_frame).
      ald F_75500 D_75500 (getr regs 8) ltac:(unfold lock_mem, lock_frame).
      ald F_75504 D_75504 (getr regs 9) ltac:(unfold lock_mem, lock_frame).
      ald F_75508 D_75508 (getr regs 18) ltac:(unfold lock_mem, lock_frame).
      ald F_7550c D_7550c (getr regs 19) ltac:(unfold lock_mem, lock_frame).
      (* [comment removed for export] *)
      ai F_75510 D_75510. replace (usp + -48 + 48)%Z with usp by lia.
      (* [comment removed for export] *)
      stepjr F_75514 D_75514 ret ltac:(gr; pin; first [reflexivity | assumption]). imm_norm. rewrite (Hret : v_jalr ret 0 = ret).
      apply mst_refl.
    - split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
      intros r N10 N11 N12 N13 N14.
      destruct (bv_eq_dec 5 r 1) as [->|N1]; [gr; symmetry; exact H1|].
      destruct (bv_eq_dec 5 r 2) as [->|N2]; [gr; symmetry; exact H2|].
      destruct (bv_eq_dec 5 r 8) as [->|N8]; [gr; reflexivity|].
      destruct (bv_eq_dec 5 r 9) as [->|N9]; [gr; reflexivity|].
      destruct (bv_eq_dec 5 r 18) as [->|N18]; [gr; reflexivity|].
      destruct (bv_eq_dec 5 r 19) as [->|N19]; [gr; reflexivity|].
      repeat (rewrite getr_other by (first [exact N1|exact N2|exact N8|exact N9|exact N10|exact N11|exact N12|exact N13|exact N14|exact N18|exact N19])).
      reflexivity.
  Qed.
End LOCK.
