(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the main-entry states reached through stage 2B, per CONFIG_RSEQ value, computed in the build by the collecting runs of Cert/S2AsanB.v in place of the recorded encoded states). *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY73.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cert Require Import PlanRegen S2AsanB.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* the main-entry states: [HS2sB_<h>] at CONFIG_RSEQ value 0, [HS2sB_<h>R] at 1 *)
Definition HS2sB_3 : acs := Eval vm_compute in hs_or (fst (fst jo6_s2b_coll_0)) (jo6_s2b_cs 0).
Definition HS2sB_4 : acs := Eval vm_compute in hs_or (snd (fst jo6_s2b_coll_0)) (jo6_s2b_cs 0).
Definition HS2sB_3R : acs := Eval vm_compute in hs_or (fst (fst jo6_s2b_coll_1)) (jo6_s2b_cs 1).
Definition HS2sB_4R : acs := Eval vm_compute in hs_or (snd (fst jo6_s2b_coll_1)) (jo6_s2b_cs 1).
(* the run's shape at CONFIG_RSEQ value 0; the certificate at 1 is proved against the same shape *)
Definition jo6_s2b_shape : shape := Eval vm_compute in snd jo6_s2b_coll_0.

Definition HS2sB (r : Z) (h : nat) : option acs :=
  match h with
  | 3%nat => Some (if Z.eqb r 1 then HS2sB_3R else HS2sB_3)
  | 4%nat => Some (if Z.eqb r 1 then HS2sB_4R else HS2sB_4)
  | _ => None
  end.

Lemma HS2s_disj : forall r h ch, HS2sB r h = Some ch -> HS2sA r h = None.
Proof.
  intros r h ch H. destruct h as [|[|[|[|[|h]]]]]; cbv beta iota delta [HS2sB] in H; try discriminate H; reflexivity.
Qed.
