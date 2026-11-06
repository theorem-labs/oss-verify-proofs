(* nl_talk (reac_link_alias.c:37-93): the library sends one request and reads the answer until its
   ACK or its RTM_NEWLINK.

   a0 = req, a1 = len, a2 = kind, a3 = kind_n, a4 = alias, a5 = alias_n. It opens the socket,
   sends, receives into a 16384-byte buffer of its own frame, walks each answer, and closes the
   socket on every path that opened it. Its walk is link_spec`s `talk_core`, the SAME spec the
   harness`s talk computes, and it answers the code RAW (talk normalises a positive NLMSG_ERROR
   code to RC_FAILS; that is the only difference, and link_spec read_agree is where it is used).
   The reply buffer is 16384 bytes and no chunk is longer than 4096, so recv always hands out a
   whole chunk and the walk is bounded by what recv answered: the fake kernel`s trailing
   -ENOTRECOVERABLE messages are never read.
   CLAIM (a) of plain_halts is in the Post: the socket is shut, the open and close counts move
   together, and no other descriptor is touched. K = 16592 (16512 of its own, including the three
   stack probes of the receive buffer, then copy_attr`s 80).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). 
   THE BUFFER STAYS READABLE (LinkLib's L6, 2026-10-30): the Post must say the whole buffer is
   still `rw_cells`, not only the C string in front of it. `wmono` gives writability and not
   readability (`mrd` of a writable byte may be None), and the write set names the whole buffer, so
   a caller that uses it again has nothing to stand on: nl_talk calls copy_attr on the SAME buffer
   for a second IFLA_IFALIAS (0x161c4) or IFLA_INFO_KIND (0x161fc), and op_read hands the buffer to
   check_bounds, whose Pre is `tbuf_at`. It is provable: memcpy's Post covers the bytes it wrote,
   the rest of the buffer is untouched, and then one NUL store.
   
   A NULL BUFFER OWNS NO BYTES (LinkLib's L7, 2026-10-30): the write set must shrink to nothing
   when the buffer pointer is NULL. `buf_arg` is trivially true of NULL with ANY cap, so a write
   set of [0, cap) let this function's munch cover the caller's own frame and the interface names;
   the contract stayed true of the binary, but no caller could use it. The function writes nothing
   through a NULL buffer (copy_attr returns at once, and the NUL stores are guarded).
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition NL_TALK : Z := 0x16008.
Lemma NL_TALK_is_entry : NL_TALK = P_nl_talk. Proof. reflexivity. Qed.

Definition nl_talk_contract : Prop :=
  leaf NL_TALK 16592
    (fun regs m => exists kbs req,
       nlk_at m kbs /\ frame_apart_gnl regs 16592 /\ nlk_wf kbs /\ nk_open kbs = 0
       /\ wr_at rsegs m (errno_at regs) 4
       /\ apart_frame regs 16592 (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
       /\ bytes_at rsegs m (arg regs 0) req /\ Z.of_nat (length req) = arg regs 1
       /\ 0 <= arg regs 1 <= NL_SENT_LEN
       /\ buf_arg m (arg regs 2) (arg regs 3) /\ buf_arg m (arg regs 4) (arg regs 5)
       /\ apart (errno_at regs) 4 (arg regs 0) (arg regs 1)
       /\ (arg regs 2 <> 0 -> apart (errno_at regs) 4 (arg regs 2) (arg regs 3))
       /\ (arg regs 4 <> 0 -> apart (errno_at regs) 4 (arg regs 4) (arg regs 5))
       /\ (arg regs 2 <> 0 -> 1 <= arg regs 3 -> arg regs 4 <> 0 -> 1 <= arg regs 5 ->
             apart (arg regs 2) (arg regs 3) (arg regs 4) (arg regs 5))
       /\ nk_opened kbs + 1 < 2 ^ 31 /\ nk_closed kbs + 1 < 2 ^ 31
       /\ apart_gnl (arg regs 0) (arg regs 1)
       /\ apart_frame regs 16592 (arg regs 0) (arg regs 1)
       /\ (arg regs 2 <> 0 -> apart_frame regs 16592 (arg regs 2) (arg regs 3)
             /\ apart_gnl (arg regs 2) (arg regs 3))
       /\ (arg regs 4 <> 0 -> apart_frame regs 16592 (arg regs 4) (arg regs 5)
             /\ apart_gnl (arg regs 4) (arg regs 5)))
    (fun regs m => [(A_G_NL, A_G_NL + NK_N_SENT + 4);
                    (errno_at regs, errno_at regs + 4);
                    (arg regs 2, arg regs 2 + (if arg regs 2 =? 0 then 0 else arg regs 3));
                    (arg regs 4, arg regs 4 + (if arg regs 4 =? 0 then 0 else arg regs 5))])
    (fun regs m regs' m' => forall kbs req,
       nlk_at m kbs -> bytes_at rsegs m (arg regs 0) req ->
       Z.of_nat (length req) = arg regs 1 ->
       let K0 := nk_kstate kbs in
       getr regs' 10 = wz (talk_rc_lib K0)
       /\ (exists kbs', nlk_at m' kbs' /\ nlk_wf kbs'
             /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
             /\ nk_n_if kbs' = nk_n_if kbs
             /\ nk_socket_errno kbs' = 0
             /\ nk_send_errno kbs' = k_send (talk_after K0)
             /\ nk_next kbs' = Z.of_nat (k_next (talk_after K0))
             /\ nk_sent kbs' = (if talk_owes K0 then owe (nk_sent kbs) req else nk_sent kbs)
             /\ nk_n_sent kbs' = Z.of_nat (length (nk_sent kbs'))
       /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
       /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
             /\ (nk_socket_errno kbs <> 0 -> nk_opened kbs' = nk_opened kbs)
             /\ (nk_socket_errno kbs = 0 -> nk_opened kbs' = nk_opened kbs + 1))
       /\ (forall pay, a_kind (talk_attrs K0) = Some pay -> arg regs 2 <> 0 -> 1 <= arg regs 3 ->
             cstr_at m' (arg regs 2) (cut_text pay (arg regs 3)))
       /\ (forall pay, a_alias (talk_attrs K0) = Some pay -> arg regs 4 <> 0 -> 1 <= arg regs 5 ->
             cstr_at m' (arg regs 4) (cut_text pay (arg regs 5)))
       /\ (a_kind (talk_attrs K0) = None -> arg regs 2 <> 0 -> forall s,
             Z.of_nat (length s) < arg regs 3 -> cstr_at m (arg regs 2) s ->
             cstr_at m' (arg regs 2) s)
       /\ (a_alias (talk_attrs K0) = None -> arg regs 4 <> 0 -> forall s,
             Z.of_nat (length s) < arg regs 5 -> cstr_at m (arg regs 4) s ->
             cstr_at m' (arg regs 4) s)
       /\ (arg regs 2 <> 0 -> 1 <= arg regs 3 ->
             exists junk, rw_cells rsegs m' (arg regs 2) [CB (Z.to_nat (arg regs 3)) junk])
       /\ (arg regs 4 <> 0 -> 1 <= arg regs 5 ->
             exists junk, rw_cells rsegs m' (arg regs 4) [CB (Z.to_nat (arg regs 5)) junk])).
