(* The footprint twin of kind_of_link1.v kind_of_link1_holds (RECIPE.md steps 1-2 (a working note, not in this delivery)): the same run as an
   ExecF.evtF. The function reads and writes no memory, so the twin needs no rng premise and holds for every
   footprint RNG. kind_of_link1.v and its theorem are unchanged (the halts proofs use them). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import kind_of_link1_c kind_of_link1.
(* Last: StepF's step / if_cases work on evtF goals and shadow Step's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Theorem kind_of_link1_F_holds : kind_of_link1_contract_F.
Proof.
  unfold kind_of_link1_contract_F, KIND_OF_LINK1.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  pose proof (rc_signed_cases a0) as HS.
  repeat (first [ step | let E := fresh "E" in if_cases E; zify_cond E ]).
  all: apply evtF_done; destruct (KL1_spec (bv_signed a0)) as [[Hx EK]|[[Hx EK]|[[Hx EK]|[[Hx EK]|[[Hx EK]|Hx]]]]];
    [ .. | destruct Hx as (Hx0 & Hx1 & Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & EK) ];
    first [ exfalso; lia | rewrite EK; eexists; reflexivity ].
Qed.

Theorem kind_of_link1_holds_of_F : kind_of_link1_contract.
Proof. exact (kind_of_link1_contract_of_F kind_of_link1_F_holds). Qed.
