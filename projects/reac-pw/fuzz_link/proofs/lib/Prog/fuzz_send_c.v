(* fuzz_send (netlink.h:89-105): the fake send(). It keeps the request for the harness to read, or
   fails once with the errno the input chose.

   a0 = fd, a1 = buf, a2 = len; the flags argument is dead. A call on anything but the open NL_FD
   is misuse. A pending send_errno is used once and cleared, and then NOTHING is recorded: that is
   why `owe` runs after both failure tests in the model (fuzz_link.c:344-351). Otherwise the first
   min(len, 512) bytes go into g_nl.sent[n_sent] with sent_len = len, while n_sent < 16, and the
   answer is len. K = 48 (own frame; memcpy and ___errno_location use no stack).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition FUZZ_SEND : Z := 0x13528.
Lemma FUZZ_SEND_is_entry : FUZZ_SEND = P_fuzz_send. Proof. reflexivity. Qed.

Definition fuzz_send_contract : Prop :=
  leaf FUZZ_SEND 48
    (fun regs m => exists bs req, nlk_at m bs /\ frame_apart_gnl regs 48 /\ nlk_wf bs
       /\ wr_at rsegs m (errno_at regs) 4
       /\ apart_frame regs 48 (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
       /\ bytes_at rsegs m (arg regs 1) req /\ Z.of_nat (length req) = arg regs 2
       /\ 0 <= arg regs 2 <= NL_SENT_LEN
       /\ apart_gnl (arg regs 1) (arg regs 2)
       /\ apart_frame regs 48 (arg regs 1) (arg regs 2))
    (fun regs m => [(A_G_NL + NK_SEND_ERRNO, A_G_NL + NK_N_SENT + 4);
                    (errno_at regs, errno_at regs + 4)])
    (fun regs m regs' m' => forall bs req, nlk_at m bs ->
       bytes_at rsegs m (arg regs 1) req -> Z.of_nat (length req) = arg regs 2 ->
       exists bs', nlk_at m' bs'
       /\ nlk_wf bs'
       /\ nk_socket_errno bs' = nk_socket_errno bs /\ nk_end_errno bs' = nk_end_errno bs
       /\ nk_open bs' = nk_open bs /\ nk_opened bs' = nk_opened bs
       /\ nk_closed bs' = nk_closed bs
       /\ nk_misuse bs' =
            (if (arg regs 0 =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1)
       /\ (nk_send_errno bs <> 0 ->
             getr regs' 10 = wz (-1) /\ nk_send_errno bs' = 0
             /\ u32_at m' (errno_at regs) (nk_send_errno bs)
             /\ nk_n_sent bs' = nk_n_sent bs /\ nk_sent bs' = nk_sent bs)
       /\ (nk_send_errno bs = 0 ->
             getr regs' 10 = getr regs 12 /\ nk_send_errno bs' = 0
             /\ nk_sent bs' = owe (nk_sent bs) req
             /\ nk_n_sent bs' = Z.of_nat (length (owe (nk_sent bs) req)))).
