(* check_verdict (fuzz_link.c:589-593): the verdict the library gave is the verdict the model owes.

   It is `if (got != want) abort();`, compiled to one `bne a0, a1` and a return. The contract
   says the abort is NOT taken: that is claim (g) of plain_halts, and the caller (op_decide,
   fuzz_link.c:744-752) must bring `reac_served_decide` and `model_decide` to the same answer.
   The branch compares the whole registers, so the premise does too. The returning path uses no
   stack at all (the 16-byte frame is pushed only on the abort path, +0x08).
   Entry and frame read from the plain image (the unstripped twin of the pin ebe34b259b9f);
   the stack bound K is the function's own frame plus the deepest frame of every callee it can
   reach on the path this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_VERDICT : Z := 0x15f18.
Lemma CHECK_VERDICT_is_entry : CHECK_VERDICT = P_check_verdict. Proof. reflexivity. Qed.

Definition check_verdict_contract : Prop :=
  leaf CHECK_VERDICT 0
    (fun regs m => getr regs 10 = getr regs 11)
    writes_nothing
    unchanged.
