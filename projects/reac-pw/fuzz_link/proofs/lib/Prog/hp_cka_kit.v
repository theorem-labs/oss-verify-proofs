(* reac-pw/fuzz_link, PLAIN build: the last step of the check_* walks check_refused.v,
   check_verdict.v, check_write.v and check_socket.v. Each is a K = 0 `leaf_walk` with
   Wr = writes_nothing and Post = unchanged whose returning path writes caller-saved registers only
   and no memory. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

(* regs_preserved regs regs', when regs' is regs with only caller-saved registers written: each
   callee-saved register reads the same in both maps, by evaluation *)
Ltac preserved_by_eval :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hs := fresh "Hs" in let Ht := fresh "Ht" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hs]]]]]; [reflexivity..|];
  assert (Ht : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    by lia;
  destruct Ht as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.

(* the postcondition of such a walk at the state its `ret` reached: memory as it was at the start,
   where MI : mem_inv rsegs m and ST : stk rsegs m lo sp held *)
Ltac ret_unchanged MI ST :=
  apply evt_done; eexists; eexists;
  split; [reflexivity|];
  split; [preserved_by_eval|];
  split; [apply munch_refl|];
  split; [apply wmono_refl|];
  split; [exact MI|];
  split; [exact ST|];
  exact eq_refl.
