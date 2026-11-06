(* reac_served_say_to (reac_served_mark.c:16-19): point the policy`s stream at `out`.

   The whole function is `sd a0, g_say(a1)` and a return: one 8-byte store into the .bss word
   g_say, no stack, no other effect. The harness calls it once, with the FILE fmemopen made
   (fuzz_link.c:160).
   Entry and frame read from the plain image (the unstripped twin of the pin ebe34b259b9f);
   the stack bound K is the function's own frame plus the deepest frame of every callee it can
   reach on the path this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition REAC_SERVED_SAY_TO : Z := 0x163f8.
Lemma REAC_SERVED_SAY_TO_is_entry : REAC_SERVED_SAY_TO = P_reac_served_say_to. Proof. reflexivity. Qed.

Definition reac_served_say_to_contract : Prop :=
  leaf REAC_SERVED_SAY_TO 0
    (fun regs m => wr_at rsegs m A_G_SAY 8)
    (fun regs m => [(A_G_SAY, A_G_SAY + 8)])
    (fun regs m regs' m' => u64_at m' A_G_SAY (arg regs 0)).
