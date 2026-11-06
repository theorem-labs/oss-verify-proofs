(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/R_memchr.v, with its module paths and addresses changed; 99 of its 159 lines of code are new or changed and 417 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.zstep ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.StepFast.sf_zstep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Destzna.dk_ands PO.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.TacDiet2.diet_word_eq_tac ].
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Stor0fe.sb_mem_after_store.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Dieta54.dlia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.

From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import strncmp_c.
Open Scope bv_scope.

Lemma walk_stop : forall (a b : byte) l r k,
  (bv_unsigned a = 0 \/ bv_unsigned b = 0 \/ k = 0%nat \/ bv_unsigned a <> bv_unsigned b)%Z ->
  strncmp_walk (a :: l) (b :: r) k = Some (bv_unsigned a - bv_unsigned b)%Z.
Proof.
  intros a b l r k H. cbn [strncmp_walk].
  destruct (bv_unsigned a =? 0)%Z eqn:E1; [reflexivity|].
  destruct (bv_unsigned b =? 0)%Z eqn:E2; [reflexivity|].
  destruct (Nat.eqb k 0) eqn:E3; [reflexivity|].
  destruct (bv_unsigned a =? bv_unsigned b)%Z eqn:E4; [|reflexivity].
  apply Z.eqb_neq in E1. apply Z.eqb_neq in E2. apply Nat.eqb_neq in E3. apply Z.eqb_eq in E4.
  exfalso. lia.
Qed.

Lemma walk_go : forall (a b : byte) l r k,
  (bv_unsigned a <> 0)%Z -> bv_unsigned a = bv_unsigned b ->
  strncmp_walk (a :: l) (b :: r) (S k) = strncmp_walk l r k.
Proof.
  intros a b l r k Ha Hab. cbn [strncmp_walk].
  rewrite (proj2 (Z.eqb_neq _ _) Ha), <- Hab, (proj2 (Z.eqb_neq _ _) Ha), Z.eqb_refl. reflexivity.
Qed.

Lemma land_byte : forall (a : byte), Z.land (bv_unsigned a) 255 = bv_unsigned a.
Proof.
  intros a. pose proof (byte_range a) as H. change 255%Z with (Z.ones 8).
  rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (v : Z).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis LS : bytes_at rsegs m (bv_unsigned a0) ls.
  Hypothesis RS : bytes_at rsegs m (bv_unsigned a1) rs.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono rsegs m m := wmono_refl rsegs m.

  Notation A := (bv_unsigned a0).
  Notation B := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Notation POST := (strncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m).
  Notation ST pc x10 x11 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  #[using="RS LS m"] Lemma bounds : (0 <= A /\ A + Z.of_nat (length ls) <= 2^64 /\ 0 <= B /\ B + Z.of_nat (length rs) <= 2^64)%Z.
  Proof. pose proof (bytes_at_bound _ _ _ _ LS). pose proof (bytes_at_bound _ _ _ _ RS). lia. Qed.

  #[using="WM MU RS LS MI"] Lemma strncmp_loop : forall (k : nat) (j : Z) x13 x14,
    (1 <= j)%Z -> (n - j = Z.of_nat k + 1)%Z ->
    strncmp_walk (skipn (Z.to_nat j) ls) (skipn (Z.to_nat j) rs) k = Some v ->
    evt rsegs POST (ST 0x1f364 (Z_to_bv 64 (A + j)) (Z_to_bv 64 (B + j - 1)) (Z_to_bv 64 (n - j)) x13 x14).
  Proof.
    induction k as [|k IH]; intros j x13 x14 Hj Hk HW; pose proof bounds as BD;
      pose proof (bv_unsigned_in_range 64 a2) as R2; unfold bv_modulus in R2; cbn in R2;
      (destruct (skipn (Z.to_nat j) ls) as [|a l'] eqn:EL; [cbn in HW; discriminate|]);
      (destruct (skipn (Z.to_nat j) rs) as [|b r'] eqn:ER; [cbn in HW; discriminate|]);
      apply skipn_cons_nth in EL; apply skipn_cons_nth in ER; destruct EL as [Hna ->]; destruct ER as [Hnb ->];
      pose proof (nth_error_lt _ _ _ Hna); pose proof (nth_error_lt _ _ _ Hnb); pose proof (byte_range a); pose proof (byte_range b);
      pose proof (u8ro_read rsegs m A ls j a _ LS Hna ltac:(lia) eq_refl) as RD1;
      pose proof (u8ro_read rsegs m B rs j b _ RS Hnb ltac:(lia) eq_refl) as RD2.
    - zstep. zstep. zstep. zstep. zstep. if_cases Ka; zify_cond Ka.
      + zstep. zstep. if_cases Ke; zify_cond Ke.
        * rewrite walk_stop in HW by lia. injection HW as <-.
          zstep. zstep. zstep. zstep. rewrite ?land_byte. finish.
        * zstep. if_cases Kz; zify_cond Kz.
          { exfalso. lia. }
          zstep. zstep. if_cases Kk; zify_cond Kk.
          -- rewrite walk_stop in HW by lia. injection HW as <-.
             zstep. zstep. zstep. zstep. rewrite ?land_byte. finish.
          -- exfalso. lia.
      + rewrite walk_stop in HW by lia. injection HW as <-.
        zstep. zstep. zstep. zstep. rewrite ?land_byte. finish.
    - zstep. zstep. zstep. zstep. zstep. if_cases Ka; zify_cond Ka.
      + zstep. zstep. if_cases Ke; zify_cond Ke.
        * rewrite walk_stop in HW by lia. injection HW as <-.
          zstep. zstep. zstep. zstep. rewrite ?land_byte. finish.
        * zstep. if_cases Kz; zify_cond Kz.
          { exfalso. lia. }
          zstep. zstep. if_cases Kk; zify_cond Kk.
          -- exfalso. lia.
          -- rewrite walk_go in HW by lia.
             replace (A + j + 1)%Z with (A + (j + 1))%Z by lia.
             replace (B + j - 1 + 1)%Z with (B + (j + 1) - 1)%Z by lia.
             replace (n - j + -1)%Z with (n - (j + 1))%Z by lia.
             apply (IH (j + 1)%Z); try lia.
             replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. exact HW.
      + rewrite walk_stop in HW by lia. injection HW as <-.
        zstep. zstep. zstep. zstep. rewrite ?land_byte. finish.
  Qed.

  #[using="WM MU RS LS MI"] Lemma strncmp_body :
    strncmp_model ls rs n = Some v ->
    evt rsegs POST (ST 0x1f33c a0 a1 a2 a3 a4).
  Proof.
    intros HM; pose proof bounds as BD.
    pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
    unfold strncmp_model in HM.
    zstep. if_cases K0; zify_cond K0.
    - rewrite (proj2 (Z.eqb_eq _ _) K0) in HM. injection HM as <-. zstep. zstep. finish.
    - rewrite (proj2 (Z.eqb_neq _ _) K0) in HM.
      change ls with (skipn (Z.to_nat 0) ls) in HM. change rs with (skipn (Z.to_nat 0) rs) in HM.
      (destruct (skipn (Z.to_nat 0) ls) as [|a l'] eqn:EL; [cbn in HM; discriminate|]).
      (destruct (skipn (Z.to_nat 0) rs) as [|b r'] eqn:ER; [cbn in HM; discriminate|]).
      apply skipn_cons_nth in EL; apply skipn_cons_nth in ER; destruct EL as [Hna ->]; destruct ER as [Hnb ->].
      pose proof (nth_error_lt _ _ _ Hna); pose proof (nth_error_lt _ _ _ Hnb); pose proof (byte_range a); pose proof (byte_range b).
      pose proof (u8ro_read rsegs m A ls 0 a a0 LS Hna ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD1.
      pose proof (u8ro_read rsegs m B rs 0 b a1 RS Hnb ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD2.
      zstep. zstep. if_cases Ka; zify_cond Ka.
      + rewrite walk_stop in HM by lia. injection HM as <-.
        zstep. zstep. zstep. rewrite Ka. finish.
      + zstep. zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
        * rewrite walk_stop in HM by lia. injection HM as <-.
          zstep. zstep. zstep. zstep. rewrite ?land_byte. finish.
        * zstep. if_cases Kz; zify_cond Kz.
          { exfalso. lia. }
          zstep. zstep. if_cases Kk; zify_cond Kk.
          -- rewrite walk_stop in HM by lia. injection HM as <-.
             zstep. zstep. zstep. zstep. rewrite ?land_byte. finish.
          -- replace (Z.to_nat (n - 1)) with (S (Z.to_nat (n - 2))) in HM by lia.
             rewrite walk_go in HM by lia.
             eapply evt_eq.
             2:{ apply (strncmp_loop (Z.to_nat (n - 2)) 1); try lia. exact HM. }
             unfold mkR. replace (B + 1 - 1)%Z with B by lia. rewrite Z_to_bv_bv_unsigned.
             replace (n - 1)%Z with (n + -1)%Z by lia. reflexivity.
  Qed.
End Proofs.

Theorem strncmp_holds : strncmp_contract.
Proof.
  unfold strncmp_contract, STRNCMP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v LS RS HM MI.
  exact (strncmp_body ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v MI LS RS HM).
Qed.
