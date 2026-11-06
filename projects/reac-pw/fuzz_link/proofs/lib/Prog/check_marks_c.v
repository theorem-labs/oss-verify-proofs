(* check_marks (fuzz_link.c:608-623): the marks kept are the interfaces this daemon marked, each
   once, in the model order.

   a0 = got, a pointer to struct reac_served_marks; a1 = m, a pointer to struct model. The body is
   `if (got->n != m->n_mark) abort(); for i < n: if (strcmp(got->name[i], m->mark[i])) abort();`.
   Claims (h) and (i) of plain_halts. Each strcmp needs a NUL inside its 16-byte slot, which
   `marks_wf` and `model_marks_wf` give (calloc zeroed both blocks and snprintf always
   terminates). K = 32 (own frame; strcmp uses no stack).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_MARKS : Z := 0x15e34.
Lemma CHECK_MARKS_is_entry : CHECK_MARKS = P_check_marks. Proof. reflexivity. Qed.

Definition check_marks_contract : Prop :=
  leaf CHECK_MARKS 32
    (fun regs m => exists gbs mbs,
       marks_at m (arg regs 0) gbs /\ model_at m (arg regs 1) mbs
       /\ marks_wf gbs /\ model_marks_wf mbs /\ marks_are gbs mbs
       /\ apart_frame regs 32 (arg regs 0) MK_SIZE
       /\ apart_frame regs 32 (arg regs 1) MD_SIZE)
    writes_nothing
    only_frame.
