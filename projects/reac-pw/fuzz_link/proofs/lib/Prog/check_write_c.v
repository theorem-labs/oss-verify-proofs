(* check_write (fuzz_link.c:568-577) and check_mark (:595-606): the code the call answered is the
   code the model owes, under the harness own comparison same_rc (:471-475).

   The two functions are byte-identical in both builds (link/donors/REPORT.md section 5), so there is
   ONE contract here and it is instantiated at each entry. The body is
   `if (!same_rc(rc, want)) abort();`, compiled as: `want == 1000000` ? `rc == 0` : `rc != want`,
   on the whole registers. The contract says the abort is NOT taken. Claims (f) and (h) of
   plain_halts; the caller gets the premise from link_spec write_agree / mark_agree.
   The returning path uses no stack.
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_WRITE : Z := 0x15d58.
Lemma CHECK_WRITE_is_entry : CHECK_WRITE = P_check_write. Proof. reflexivity. Qed.

Definition CHECK_MARK : Z := 0x15e04.
Lemma CHECK_MARK_is_entry : CHECK_MARK = P_check_mark. Proof. reflexivity. Qed.

(* the register-level reading of same_rc(got, want) = 1 *)
Definition same_rc_regs (regs : bvmap 5 word) : Prop :=
  (getr regs 11 = wz RC_FAILS -> getr regs 10 <> wz 0)
  /\ (getr regs 11 <> wz RC_FAILS -> getr regs 10 = getr regs 11).

Definition check_rc_contract (pc : Z) : Prop :=
  leaf pc 0 (fun regs m => same_rc_regs regs) writes_nothing unchanged.

Definition check_write_contract : Prop := check_rc_contract CHECK_WRITE.
Definition check_mark_contract : Prop := check_rc_contract CHECK_MARK.
