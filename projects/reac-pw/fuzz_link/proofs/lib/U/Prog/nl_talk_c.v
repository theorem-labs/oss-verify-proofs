(* nl_talk (reac_link_alias.c:37-93), UBSAN build: the library sends one request and reads the
   answer until its ACK or its RTM_NEWLINK.

   The twin of lib/Prog/nl_talk_c.v, with its premises, its Post, and the premises the UBSan
   guards below need. a0 = req, a1 = len, a2 = kind, a3 = kind_n, a4 = alias, a5 = alias_n. It
   opens the socket, sends, receives into a 16384-byte buffer of its own frame at sp + 0x18,
   walks each answer, and closes the socket on every path that opened it. Its walk is
   link_spec`s `talk_core`, and it answers the code RAW. CLAIM (a) of the halting theorem is in
   the Post, as in the plain twin.
   K = 16624: 16512 of its own (0x7f0, three stack probes of 0x1000, then 0x800 and 0x90), then
   fuzz_recv`s 112, the deepest callee (copy_attr 48 + strnlen 32 = 80, fuzz_socket 32,
   fuzz_send 32, fuzz_close 0, ___errno_location 0).
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/nl_talk.s); every guard
   branches to the `unimp` at 0x169ec:
   - branch 0x167a8 (reac_link_alias.c:61, NLMSG_OK, `andi a2, a1, 3`): traps unless the message
     header nh is 4-aligned. nh starts at sp - 16512 + 0x18 and moves by NL_ALIGN(len), a
     multiple of 4, so it is 4-aligned exactly when sp is; the `leaf` shape does not say that.
     ADDED: `spZ regs mod 4 = 0`.
   - branch 0x168a4 (reac_link_alias.c:74, IFLA_RTA, `andi a0, s5, 1`) and branch 0x168fc
     (reac_link_alias.c:80, RTA_DATA, `andi a0, s6, 1`): trap unless the attribute is 2-aligned.
     Each attribute is nh + 32, or the one before it + 4, plus RTA_ALIGN steps: ANSWERED BY the
     same `spZ regs mod 4 = 0`.
   - branch 0x16800 / 0x16824 / 0x16848 (reac_link_alias.c:55, :44, :46, `beqz a0` after
     ___errno_location): trap when the errno address is NULL. ADDED: `errno_at regs <> 0`.
   - branch 0x16808 / 0x1682c / 0x16850 (the same lines, `andi a1, a0, 3`): trap unless the
     errno address is 4-aligned. ADDED: `errno_at regs mod 4 = 0`. fuzz_socket, fuzz_send and
     fuzz_recv take the same two premises in their own U contracts.
   - branch 0x1681c / 0x16840 / 0x1686c (reac_link_alias.c:55, :44, :48, `neg; negw; beq`, then
     `j` to the trap): trap when `-errno` overflows int, that is when errno = INT_MIN. errno is
     what fuzz_recv, fuzz_socket or fuzz_send just stored: nk_end_errno, nk_socket_errno or
     nk_send_errno. ANSWERED BY nlk_wf, which puts all three in [0, 2^31).
   - branch 0x167d4 (reac_link_alias.c:61, NLMSG_NEXT), 0x16874 and 0x1687c
     (reac_link_alias.c:72, NLMSG_DATA), 0x168e4 (reac_link_alias.c:80, RTA_DATA), 0x16934
     (reac_link_alias.c:81, RTA_NEXT), 0x1695c (reac_link_alias.c:75, RTA_NEXT) and 0x16980
     (the NLMSG_DATA of an NLMSG_ERROR): pointer-sum guards on addresses inside the receive
     buffer, each below sp - 16512 + 0x18 + 16384 + 3 < sp. ANSWERED BY the shape:
     spZ regs < 2^63.
   The callee U contracts need nothing more: fuzz_recv`s `arg regs 1 <> 0` and no-wrap premise
   hold of the stack buffer by the shape, and copy_attr`s `a mod 2 = 0` and `a + 4 < 2^64` are
   the alignment and the shape above.
   ADDED SO THE Post IS TRUE, missing in the plain twin as well (noted for the plain lane; it
   answers no UBSan guard): the kind and alias buffers do not overlap. copy_attr writes one and
   then the other in the same walk, and the Post states both C strings.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. 
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition NL_TALK : Z := 0x166c8.
Lemma NL_TALK_is_entry : NL_TALK = P_nl_talk. Proof. reflexivity. Qed.

Definition nl_talk_contract : Prop :=
  leaf NL_TALK 16624
    (fun regs m => exists kbs req,
       nlk_at m kbs /\ frame_apart_gnl regs 16624 /\ nlk_wf kbs /\ nk_open kbs = 0
       /\ wr_at rsegs m (errno_at regs) 4
       /\ apart_frame regs 16624 (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
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
       /\ apart_frame regs 16624 (arg regs 0) (arg regs 1)
       /\ (arg regs 2 <> 0 -> apart_frame regs 16624 (arg regs 2) (arg regs 3)
             /\ apart_gnl (arg regs 2) (arg regs 3))
       /\ (arg regs 4 <> 0 -> apart_frame regs 16624 (arg regs 4) (arg regs 5)
             /\ apart_gnl (arg regs 4) (arg regs 5))
       /\ errno_at regs <> 0 /\ errno_at regs mod 4 = 0 /\ spZ regs mod 4 = 0
       /\ (arg regs 2 <> 0 -> arg regs 4 <> 0 ->
             arg regs 2 + arg regs 3 <= arg regs 4 \/ arg regs 4 + arg regs 5 <= arg regs 2))
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
             /\ nk_socket_errno kbs' = 0 /\ nk_send_errno kbs' = 0
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
