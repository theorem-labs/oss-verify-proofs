(* check_verdict (fuzz_link.c:589-593), UBSAN build: the verdict the library gave is the verdict
   the model owes.

   The twin of lib/Prog/check_verdict_c.v, with the same premise and the same Post. The ubsan body
   is the plain one: `bne a0, a1` to the abort path, else `ret`. The contract says the abort is
   NOT taken (claim (g) of the halting theorem): the caller, op_decide (fuzz_link.c:744-752), must
   bring `reac_served_decide` and `model_decide` to the same answer. The branch compares the whole
   registers, so the premise does too. The returning path uses no stack (the 16-byte frame is
   pushed only on the abort path, +0x08), so K = 0.
   UBSan guards: link/donors/ubsan-checks.tsv gives check_verdict no guard branch. Its one `unimp`
   (0x165e8) follows the call to abort and is reached only through it, so no premise is added.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_VERDICT : Z := 0x165d4.
Lemma CHECK_VERDICT_is_entry : CHECK_VERDICT = P_check_verdict. Proof. reflexivity. Qed.

Definition check_verdict_contract : Prop :=
  leaf CHECK_VERDICT 0
    (fun regs m => getr regs 10 = getr regs 11)
    writes_nothing
    unchanged.
