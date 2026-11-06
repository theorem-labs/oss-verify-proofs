From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import kind_of_link1_c.
Import ListNotations.
Open Scope Z_scope.

Theorem kind_of_link1_holds : kind_of_link1_contract.
Proof.
  unfold kind_of_link1_contract, KIND_OF_LINK1.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  pose proof (rc_signed_cases a0) as HS.
  repeat (first [ step | let E := fresh "E" in if_cases E; zify_cond E ]).
  all: apply evt_done; destruct (KL1_spec (bv_signed a0)) as [[Hx EK]|[[Hx EK]|[[Hx EK]|[[Hx EK]|[[Hx EK]|Hx]]]]];
    [ .. | destruct Hx as (Hx0 & Hx1 & Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & EK) ];
    first [ exfalso; lia | rewrite EK; eexists; reflexivity ].
Qed.
