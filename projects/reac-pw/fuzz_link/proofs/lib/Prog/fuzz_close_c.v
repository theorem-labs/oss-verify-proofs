(* fuzz_close (netlink.h:139-146): the fake close(). It marks the socket shut and counts the close.

   a0 = fd. A call on anything but the open NL_FD is misuse. The answer is always 0, and the
   function uses no stack at all.
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition FUZZ_CLOSE : Z := 0x13778.
Lemma FUZZ_CLOSE_is_entry : FUZZ_CLOSE = P_fuzz_close. Proof. reflexivity. Qed.

Definition fuzz_close_contract : Prop :=
  leaf FUZZ_CLOSE 0
    (fun regs m => exists bs, nlk_at m bs /\ nlk_wf bs /\ nk_closed bs + 1 < 2 ^ 31)
    (fun regs m => [(A_G_NL + NK_OPEN, A_G_NL + NK_MISUSE + 4)])
    (fun regs m regs' m' => forall bs, nlk_at m bs -> exists bs', nlk_at m' bs'
       /\ nlk_wf bs' /\ getr regs' 10 = wz 0
       /\ nk_open bs' = 0 /\ nk_opened bs' = nk_opened bs
       /\ nk_closed bs' = nk_closed bs + 1
       /\ nk_misuse bs' =
            (if (arg regs 0 =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1)).
