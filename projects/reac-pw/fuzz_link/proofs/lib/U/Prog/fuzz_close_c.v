(* fuzz_close (netlink.h:139-146), UBSAN build: the fake close(). It marks the socket shut and counts
   the close.

   The twin of lib/Prog/fuzz_close_c.v, with the same premises and the same Post. a0 = fd. A call
   on anything but the open NL_FD is misuse. The answer is always 0, and the function uses no stack
   at all, so K = 0.
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/fuzz_close.s):
   - branch 0x13950 (netlink.h:144, `addiw a0, a2, 1; blt a0, a2` to the `unimp` at 0x13960):
     traps when g_nl.closed++ overflows int. Answered by `nk_closed bs + 1 < 2 ^ 31`, which the
     plain twin now also has.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition FUZZ_CLOSE : Z := 0x13914.
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
