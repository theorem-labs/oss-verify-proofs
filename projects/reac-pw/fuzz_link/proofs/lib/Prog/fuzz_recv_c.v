(* fuzz_recv (netlink.h:107-137): the fake recv(). It hands out the next queued chunk whole, or
   fails with the errno the input chose once the queue is empty.

   a0 = fd, a1 = buf, a2 = len; the flags argument is dead. A call on anything but the open NL_FD
   is misuse. Past the chunk it writes zeros to the next 4-byte boundary and then whole
   NLMSG_ERROR messages of -ENOTRECOVERABLE (+0xe0 to +0x120: length 0x24, type 2, code
   0xffffff7d), so a reader that walks past the reply answers that error every time. THE WEAKEST
   FORM THE CALLER NEEDS: nl_talk bounds its walk by the answer, so it never reads those bytes;
   the contract therefore says only that the chunk is at the front of the buffer and the rest of
   the buffer holds some bytes. The trailing messages matter to a mutant, not to a proof of the
   real code; a later strengthening can add them without changing this statement`s premises.
   K = 80 (own frame; memcpy, memset and ___errno_location use no stack).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). 
   THE BUFFER STAYS READABLE ON EVERY PATH (LinkLib's L8, 2026-10-30): the Post says the whole
   buffer is still `rw_cells`, on the failure path too. The write set names the buffer on every
   path, but the failure arm (n_chunks <= next) said nothing of it, and nl_talk's buffer is its own
   frame (sp+24, 16384 bytes; calls at 0x160c4 and 0x16120): after a failing recv nl_talk could
   not show its frame readable, so it could not release it (stk_release needs rw_cells). True of
   the binary: the failure arm returns -1 before touching the buffer. The same class as L6.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition FUZZ_RECV : Z := 0x13610.
Lemma FUZZ_RECV_is_entry : FUZZ_RECV = P_fuzz_recv. Proof. reflexivity. Qed.

Definition fuzz_recv_contract : Prop :=
  leaf FUZZ_RECV 80
    (fun regs m => exists bs junk, nlk_at m bs /\ frame_apart_gnl regs 80 /\ nlk_wf bs
       /\ wr_at rsegs m (errno_at regs) 4
       /\ apart_frame regs 80 (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
       /\ NL_CHUNK_MAX <= arg regs 2
       /\ rw_cells rsegs m (arg regs 1) [CB (Z.to_nat (arg regs 2)) junk]
       /\ apart_gnl (arg regs 1) (arg regs 2)
       /\ apart_frame regs 80 (arg regs 1) (arg regs 2))
    (fun regs m => [(A_G_NL + NK_NEXT, A_G_NL + NK_MISUSE + 4);
                    (errno_at regs, errno_at regs + 4);
                    (arg regs 1, arg regs 1 + arg regs 2)])
    (fun regs m regs' m' => forall bs, nlk_at m bs -> exists bs', nlk_at m' bs'
       /\ nlk_wf bs'
       /\ nk_n_chunks bs' = nk_n_chunks bs /\ nk_end_errno bs' = nk_end_errno bs
       /\ nk_socket_errno bs' = nk_socket_errno bs /\ nk_send_errno bs' = nk_send_errno bs
       /\ nk_chunks bs' = nk_chunks bs
       /\ nk_open bs' = nk_open bs /\ nk_opened bs' = nk_opened bs
       /\ nk_closed bs' = nk_closed bs /\ nk_n_sent bs' = nk_n_sent bs
       /\ nk_misuse bs' =
            (if (arg regs 0 =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1)
       /\ (nk_n_chunks bs <= nk_next bs ->
             getr regs' 10 = wz (-1) /\ nk_next bs' = nk_next bs
             /\ u32_at m' (errno_at regs) (nk_end_errno bs))
       /\ (nk_next bs < nk_n_chunks bs ->
             let c := nk_chunk bs (nk_next bs) in
             getr regs' 10 = wz (Z.of_nat (length c)) /\ nk_next bs' = nk_next bs + 1
             /\ exists rest, bytes_at rsegs m' (arg regs 1) (c ++ rest)
                /\ Z.of_nat (length rest) = arg regs 2 - Z.of_nat (length c))
       /\ exists junk, rw_cells rsegs m' (arg regs 1) [CB (Z.to_nat (arg regs 2)) junk]).
