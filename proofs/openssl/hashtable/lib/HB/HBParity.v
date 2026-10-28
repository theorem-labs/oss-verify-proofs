(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBChain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition par_even : kentry := KAlign (EVar 6) 2.
Definition par_odd : kentry := KAlign (EAlu ALU_ADD (EVar 6) (ELit 1)) 2.
Definition with_facts (cs : acs) (F : list kentry) : acs := set_kn cs (F ++ kn cs).

Lemma odd_succ_even : forall V, 0 <= V < 2 ^ 64 -> V mod 2 = 1 -> ((V + 1 mod 2 ^ 64) mod 2 ^ 64) mod 2 = 0.
Proof.
  intros V HV Hodd. rewrite (Z.mod_small 1 (2 ^ 64)) by lia.
  pose proof (Z.div_mod V 2 ltac:(lia)) as DV. rewrite Hodd in DV.
  set (q := V / 2) in *. clearbody q.
  destruct (Z.eq_dec (V + 1) (2 ^ 64)) as [He|Hne].
  - rewrite He, Z.mod_same by lia. reflexivity.
  - rewrite (Z.mod_small (V + 1) (2 ^ 64)) by lia. replace (V + 1) with ((q + 1) * 2) by lia. apply Z.mod_mul. lia.
Qed.

Section Parity.
  Variable SV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable ISP : Z.
  Variable fs : Fs.Fs.
  #[local] Notation PIECE := (piece SV argH ISP fs).
  #[local] Notation CSOK := (cs_ok HASEGS HAT AsanInit.LIMIT SV argH ISP fs).

  Lemma csok_with_facts : forall cs F E R FULL m, CSOK E cs R FULL m -> (forall M, know_ok HASEGS E M F) -> CSOK E (with_facts cs F) R FULL m.
  Proof.
    intros cs F E R FULL m HC HF. unfold with_facts. apply cs_ok_set_kn; [exact HC|].
    apply Forall_app. split; [exact (HF _) | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)].
  Qed.

  Lemma piece_parity : forall cs T, PIECE (with_facts cs [par_even]) T -> PIECE (with_facts cs [par_odd]) T -> PIECE cs T.
  Proof.
    intros cs T PE PO E R FULL m HC.
    set (V := bv_unsigned (edenot E (EVar 6))).
    assert (HV : 0 <= V < 2 ^ 64) by (pose proof (u64_range (edenot E (EVar 6))) as X; unfold two64 in X; exact X).
    pose proof (Z.mod_pos_bound V 2 ltac:(lia)) as HB.
    destruct (Z.eq_dec (V mod 2) 0) as [He|Ho].
    - apply (PE E R FULL m). apply csok_with_facts; [exact HC|]. intros M. constructor; [|constructor]. unfold par_even. cbn [kentry_ok]. split; [reflexivity | exact He].
    - apply (PO E R FULL m). apply csok_with_facts; [exact HC|]. intros M. constructor; [|constructor]. unfold par_odd. cbn [kentry_ok]. split; [reflexivity|].
      change (edenot E (EAlu ALU_ADD (EVar 6) (ELit 1))) with (alu64 ALU_ADD (edenot E (EVar 6)) (Z_to_bv 64 1)).
      rewrite u_add64, u_lit64. unfold two64. fold V. apply odd_succ_even; [exact HV | lia].
  Qed.
End Parity.
