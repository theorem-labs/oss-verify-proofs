(* model_read (fuzz_link.c:386-401), UBSAN build: what the harness says a read of an interface alias
   owes.

   The twin of lib/Prog/model_read_c.v, with its premises, its Wr set and its Post, the premises
   its callees need in the ubsan build, and the separation premises the Post needs to be true.
   a0 = m, a1 = name, a2 = kind, a3 = kind_n, a4 = alias, a5 = alias_n. It empties both buffers,
   refuses a NULL or empty name with -EINVAL and an unknown name with -ENODEV, and otherwise sends
   the 32-byte RTM_GETLINK of link_spec`s `req_read` and answers `talk`. link_spec`s `read_model`
   is the whole of it. The request is built in the own frame at sp + 8 (memset at 0x15434, then
   the stores of req_head); index_of is called at 0x1541c and talk at 0x154a8.
   K = 240: the own frame of 96 (link/donors/premises-ubsan.txt, `addi sp, sp, -0x60` at +0x00),
   then talk`s 144 (its own 112 plus take_text`s 32, lib/U/Prog/talk_c.v); index_of`s 64 and
   memset`s 0 fit inside that. The brief gave 208 = 96 + 112: link/ct/stack.py takes its call edges
   from link/functions.tsv, whose callee column is the PLAIN build`s, and so misses the two ubsan
   calls from talk to take_text. The prologue is at +0x00, before the buffers are emptied, so every
   returning path writes the frame; the plain Post claims nothing of the memory outside Wr and the
   frame, so it stands as it is.
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/model_read.s); every guard
   branches to the `unimp` at 0x154d8. All five are on the request r = sp + 8 of the own frame, that
   is, entry sp - 88:
   - branch 0x15448 (fuzz_link.c:311, `bgeu a0, a2` with a0 = r, a2 = -4): r + 4 passes 2^64 - 1.
   - branch 0x15458 (fuzz_link.c:312, `bltu a2, a0` with a2 = -7): r + 6 passes 2^64 - 1.
   - branch 0x1546c (fuzz_link.c:313, `bltu a2, a1` with a2 = -9): r + 8 passes 2^64 - 1.
   - branch 0x15478 (fuzz_link.c:314, `bltu a2, a1` with a2 = -17): r + 16 passes 2^64 - 1.
   - branch 0x15484 (fuzz_link.c:314, `bltu a1, a0` with a0 = r + 16, a1 = -5): r + 20 passes
     2^64 - 1.
   ANSWERED BY THE SHAPE: `leaf` gives spZ regs < 2^63 and lo + 240 <= spZ regs with 0 <= lo
   (`stk`), so r = spZ regs - 88 is the real address and r + 20 < 2^64.
   So no premise is added for a guard of this function.
   Premises for the callees, not guards:
   - for callee talk`s U contract (its guard 0x15b88): `arg regs 0 mod 8 = 0`.
   - for callee talk`s U contract (take_text`s payload and buffer must not overlap): each non-NULL
     text buffer is outside g_nl, `apart_gnl`. It also keeps index_of`s view of g_nl unchanged by
     the two stores that empty the buffers.
   - for callee talk`s U contract (the separation its Post needs): each non-NULL text buffer is
     outside the model block, and the two do not overlap.
   - for callee index_of`s U contract (lib/U/Prog/index_of_c.v: strcmp reads every table name after
     index_of pushes its frame [sp-160, sp-96)): every table name is outside this contract`s
     frame, `apart_frame regs 240`, which covers index_of`s frame.
   talk`s other premises follow: the request lies in the own frame, so it is outside talk`s frame
   [sp-240, sp-96) and outside the model block (`apart_frame regs 240` of the block), and its
   length 32 is at most NL_SENT_LEN.
   Premises the Post needs to be TRUE, missing in the plain twin as well: the buffers are emptied
   (+0x34 to +0x48) BEFORE the name is read and before index_of reads the table, so each non-NULL
   text buffer is outside the name string and outside every table name. Without them a store could
   empty the name or a table name, and the answer would not be `read_model` of the first memory.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function`s own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. 
   THE POST FIXES THE MODEL'S TWO ERRNOS (a Theorem Labs lane, AMEND-slot item 7, 2026-10-30): `talk` clears
   the socket errno and leaves the send errno as its own spec says, and a caller that runs a read
   and then a write (model_mark 0x13d98 -> 0x140a8, and model_unmark's loop) cannot show the second
   call runs on the state `mark_lib` and `unmark` run on unless this Post pins both.
   
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

Definition MODEL_READ : Z := 0x153bc.
Lemma MODEL_READ_is_entry : MODEL_READ = P_model_read. Proof. reflexivity. Qed.

Definition model_read_contract : Prop :=
  leaf MODEL_READ 240
    (fun regs m => exists mbs kbs tab nm,
       model_at m (arg regs 0) mbs /\ model_wf mbs
       /\ nlk_at m kbs /\ frame_apart_gnl regs 240 /\ nlk_wf kbs /\ iftab_at m kbs tab
       /\ str_arg m (arg regs 1) nm
       /\ buf_arg m (arg regs 2) (arg regs 3) /\ buf_arg m (arg regs 4) (arg regs 5)
       /\ apart_gnl (arg regs 0) MD_SIZE /\ apart_frame regs 240 (arg regs 0) MD_SIZE
       /\ (arg regs 1 <> 0 -> forall s, nm = Some s ->
             apart_frame regs 240 (arg regs 1) (Z.of_nat (length s) + 1))
       /\ (arg regs 2 <> 0 -> apart_frame regs 240 (arg regs 2) (arg regs 3))
       /\ (arg regs 4 <> 0 -> apart_frame regs 240 (arg regs 4) (arg regs 5))
       /\ arg regs 0 mod 8 = 0
       /\ (arg regs 2 <> 0 -> apart_gnl (arg regs 2) (arg regs 3))
       /\ (arg regs 4 <> 0 -> apart_gnl (arg regs 4) (arg regs 5))
       /\ (arg regs 2 <> 0 ->
             arg regs 2 + arg regs 3 <= arg regs 0 \/ arg regs 0 + MD_SIZE <= arg regs 2)
       /\ (arg regs 4 <> 0 ->
             arg regs 4 + arg regs 5 <= arg regs 0 \/ arg regs 0 + MD_SIZE <= arg regs 4)
       /\ (arg regs 2 <> 0 -> arg regs 4 <> 0 ->
             arg regs 2 + arg regs 3 <= arg regs 4 \/ arg regs 4 + arg regs 5 <= arg regs 2)
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_frame regs 240 p (Z.of_nat (length n2) + 1))
       /\ (forall s, nm = Some s ->
             (arg regs 2 <> 0 -> arg regs 2 + arg regs 3 <= arg regs 1
                                 \/ arg regs 1 + Z.of_nat (length s) + 1 <= arg regs 2)
             /\ (arg regs 4 <> 0 -> arg regs 4 + arg regs 5 <= arg regs 1
                                    \/ arg regs 1 + Z.of_nat (length s) + 1 <= arg regs 4))
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             (arg regs 2 <> 0 -> arg regs 2 + arg regs 3 <= p
                                 \/ p + Z.of_nat (length n2) + 1 <= arg regs 2)
             /\ (arg regs 4 <> 0 -> arg regs 4 + arg regs 5 <= p
                                    \/ p + Z.of_nat (length n2) + 1 <= arg regs 4)))
    (fun regs m => [(arg regs 0, arg regs 0 + MD_SIZE);
                    (arg regs 2, arg regs 2 + (if arg regs 2 =? 0 then 0 else arg regs 3));
                    (arg regs 4, arg regs 4 + (if arg regs 4 =? 0 then 0 else arg regs 5))])
    (fun regs m regs' m' => forall mbs kbs tab nm,
       model_at m (arg regs 0) mbs -> nlk_at m kbs -> iftab_at m kbs tab ->
       str_arg m (arg regs 1) nm ->
       let R := read_model tab nm (arg regs 3) (arg regs 5) (md_reqs mbs) (md_kstate mbs kbs) in
       getr regs' 10 = wz (r_rc R)
       /\ (exists mbs', model_at m' (arg regs 0) mbs' /\ model_wf mbs'
             /\ md_next mbs' = Z.of_nat (k_next (r_state R))
             /\ md_socket_errno mbs' = k_sock (r_state R)
             /\ md_send_errno mbs' = k_send (r_state R)
             /\ md_reqs mbs' = r_reqs R /\ md_n_req mbs' = Z.of_nat (length (r_reqs R))
             /\ md_n_mark mbs' = md_n_mark mbs /\ md_marks mbs' = md_marks mbs)
       /\ (arg regs 2 <> 0 -> 1 <= arg regs 3 -> cstr_at m' (arg regs 2) (r_kind R))
       /\ (arg regs 4 <> 0 -> 1 <= arg regs 5 -> cstr_at m' (arg regs 4) (r_alias R))
       /\ (arg regs 2 <> 0 -> 1 <= arg regs 3 ->
             exists junk, rw_cells rsegs m' (arg regs 2) [CB (Z.to_nat (arg regs 3)) junk])
       /\ (arg regs 4 <> 0 -> 1 <= arg regs 5 ->
             exists junk, rw_cells rsegs m' (arg regs 4) [CB (Z.to_nat (arg regs 5)) junk])).
