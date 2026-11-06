(* The op_read lanes' call kit: the shared lib/Prog/mk_call.v (q_ext, evt_canon, leaf_q_ext,
   canon_of_preserved, leaf_call), re-exported, and the one fact every C0 segment adds to it: the post
   `eqv_cl P ms' /\ seg_fp S hp m0 (ms_mem ms')` is closed under ms_eqv, so `leaf_call` applies. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Export mk_leaf mk_call.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs.
Local Open Scope Z_scope.

Lemma c0_ms_eqv_trans : forall a b c, ms_eqv a b -> ms_eqv b c -> ms_eqv a c.
Proof.
  intros a b c (R1 & F1 & P1 & S1 & V1 & C1 & M1 & O1) (R2 & F2 & P2 & S2 & V2 & C2 & M2 & O2).
  repeat split; try congruence.
  intros r Hr. rewrite (R1 r Hr). exact (R2 r Hr).
Qed.

Lemma c0_q_ext : forall (P : machine_state -> Prop) (S : Z) (hp : list (Z * Z)) (m0 : word -> option byte),
  q_ext (fun ms' => eqv_cl P ms' /\ seg_fp S hp m0 (ms_mem ms')).
Proof.
  intros P S hp m0 c a ((d & Pd & Edc) & FP) Eca. split.
  - exists d. split; [exact Pd|]. exact (c0_ms_eqv_trans d c a Edc Eca).
  - destruct Eca as (_ & _ & _ & _ & _ & _ & EM & _). rewrite <- EM. exact FP.
Qed.
