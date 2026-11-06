(* reac_served_say_to (reac_served_mark.c:16-19), UBSAN build: point the policy`s stream at `out`.

   The twin of lib/Prog/reac_served_say_to_c.v, with the same premise and the same Post. The whole
   function is `auipc a1; sd a0, 0x1ec(a1)` (the .bss word g_say at 0x75d70) and a return: one
   8-byte store, no stack, no other effect, so K = 0. The harness calls it once, with the FILE
   fmemopen made (fuzz_link.c:160).
   UBSan guards: link/donors/ubsan-checks.tsv gives reac_served_say_to no trap and no guard branch,
   so no premise is added.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition REAC_SERVED_SAY_TO : Z := 0x16b84.
Lemma REAC_SERVED_SAY_TO_is_entry : REAC_SERVED_SAY_TO = P_reac_served_say_to. Proof. reflexivity. Qed.

Definition reac_served_say_to_contract : Prop :=
  leaf REAC_SERVED_SAY_TO 0
    (fun regs m => wr_at rsegs m A_G_SAY 8)
    (fun regs m => [(A_G_SAY, A_G_SAY + 8)])
    (fun regs m regs' m' => u64_at m' A_G_SAY (arg regs 0)).
