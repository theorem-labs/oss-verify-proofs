From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img codec_chk
  check_refusal_c.
Import ListNotations.
Open Scope Z_scope.

(** check_refusal loads kind (lw at k+0); kind <> 11 returns. Else it loads b (lw at k+0x1c, a u32, so the
    register holds sx32 of it); b <> 0x70 returns. Else it loads rc (lw at k+0x48) and returns when rc <> 0.
    The only other path, rc = 0, is the abort call at 0x15188; the premise excludes kind = 11, b = 0x70,
    rc = 0 together, so that path is never reached. No store, no frame on the returning paths. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Theorem check_refusal_holds : check_refusal_contract.
Proof.
  unfold check_refusal_contract, check_refusal_pre, CHECK_REFUSAL.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m k [HC [HW HN]].
  change (cells_at rsegs m (bv_unsigned a0) (kcall_cells k))
    with (ro_cells rsegs m (bv_unsigned a0) (kcall_cells k)) in HC.
  pose proof (cells_at_bound rsegs m _ _ HC) as HB.
  cbn [kcall_cells cells_size csize Nat.add] in HB.
  unfold kcall_cells in HC.
  unfold kcall_wf in HW.
  destruct HW as (Wk & _ & _ & _ & Wb & _ & _ & _ & Wrc & _).
  (* lw a1, 0(a0); addi a2, zero, 11; bne a1, a2 *)
  step. rewrite (sx32_small (k_kind k)) by lia.
  step. step.
  if_cases K1; rewrite chk_s64_eqb in K1 by lia; zify_bool K1.
  all: try solve [ step; finish ].
  (* kind = 11: lw a1, 0x1c(a0); addi a2, zero, 0x70; bne a1, a2 *)
  all: step; step; step.
  all: if_cases K2; rewrite chk_sx32_eqb in K2 by lia; zify_bool K2.
  all: try solve [ step; finish ].
  (* b = 0x70: lw a0, 0x48(a0); beqz a0 -> abort (rc = 0, excluded) or ret *)
  all: step; rewrite (sx32_small (k_rc k)) by lia.
  all: step.
  all: if_cases K3; rewrite ?chk_s64_eqb in K3 by lia; zify_bool K3.
  all: try solve [ exfalso; apply HN; repeat split; lia ].
  all: step; finish.
Qed.
