(* reac_link_alias_read (reac_link_alias.c:95-119), UBSAN build: the library reads one netdev`s link
   kind and interface alias over rtnetlink.

   The twin of lib/Prog/reac_link_alias_read_c.v, with its premises, its Post, and the premises
   its callee nl_talk`s U contract needs. a0 = name, a1 = kind, a2 = kind_n, a3 = alias,
   a4 = alias_n. It empties both buffers, refuses a NULL or empty name with -EINVAL and an unknown
   name with -ENODEV, and otherwise sends the 32-byte RTM_GETLINK of link_spec`s `req_read` (built
   at sp, inside its own frame) and answers nl_talk. link_spec`s `read_lib` is the whole of it.
   CLAIM (c) of the halting theorem is the refusal clause, as in the plain twin.
   K = 16704 (80 of its own, then nl_talk`s 16624; fuzz_if_nametoindex`s 64 fits inside that).
   UBSan guards: link/donors/ubsan-checks.tsv gives this function no trap and no guard branch
   (link/ct/dis/ubsan/reac_link_alias_read.s has no `unimp`), so no premise answers a guard of
   its own.
   ADDED FOR CALLEE nl_talk`s U CONTRACT (lib/U/Prog/nl_talk_c.v), which answers nl_talk`s
   guards and those of fuzz_socket, fuzz_send and fuzz_recv:
   - `errno_at regs <> 0 /\ errno_at regs mod 4 = 0`: the errno address is not NULL and is
     4-aligned (nl_talk branches 0x16800 to 0x16850). errno is fixed by tp, which the call keeps.
   - `spZ regs mod 4 = 0`: nl_talk`s receive buffer is 4-aligned (nl_talk branch 0x167a8).
     nl_talk runs at sp - 80, and 80 is a multiple of 4.
   ADDED FOR CALLEE fuzz_if_nametoindex`s U CONTRACT (lib/U/Prog/index_of_c.v, the same text in
   both builds): its strcmp reads every table name after the callee pushes its frame at sp - 80,
   so every table name is outside this contract`s frame: `apart_frame regs 16704 p ...` for each
   if_name pointer p. The plain twin lacks it too; that is noted for the plain lane.
   ADDED SO THE Post IS TRUE, missing in the plain twin as well (noted for the plain lane; none
   answers a UBSan guard): the function empties both buffers (+0x34 and +0x40) BEFORE it reads
   the name and before fuzz_if_nametoindex reads the table, and nl_talk may then write errno and
   fill the buffers. So each non-NULL buffer is outside the name string, outside every table
   name and outside errno, and the two buffers do not overlap (nl_talk`s U contract asks for
   that last one too). Without them a store could change the name, a table name or an emptied
   buffer, and the answer would not be `read_lib` of the first memory.
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
   
   GAP 10 (a Theorem Labs lane's sub-lane a Theorem Labs lane, 2026-10-30): the Post must fix the fake kernel's two
   errno fields as well, so that `nk_kstate kbs'` IS the state the spec continued from. A chained
   caller (reac_served_unmark_all's read at 0x167c8 then write at 0x167ec, then the next round;
   reac_served_mark's 0x164b4 then 0x16530) states its own Post over `r_state R` / `w_state W`,
   which `talk_after` has cleared, while the next callee's Post speaks of `nk_kstate kbs'`; with
   the two fields free the request list after the second call is not `fst U` or `m_reqs M`.
   nl_talk's Post already gives the same of its own kstate.
   
   A NULL BUFFER OWNS NO BYTES (LinkLib's L7, 2026-10-30): the write set must shrink to nothing
   when the buffer pointer is NULL. `buf_arg` is trivially true of NULL with ANY cap, so a write
   set of [0, cap) let this function's munch cover the caller's own frame and the interface names;
   the contract stayed true of the binary, but no caller could use it. The function writes nothing
   through a NULL buffer (copy_attr returns at once, and the NUL stores are guarded).
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition REAC_LINK_ALIAS_READ : Z := 0x165ec.
Lemma REAC_LINK_ALIAS_READ_is_entry : REAC_LINK_ALIAS_READ = P_reac_link_alias_read. Proof. reflexivity. Qed.

Definition reac_link_alias_read_contract : Prop :=
  leaf REAC_LINK_ALIAS_READ 16704
    (fun regs m => exists kbs tab nm,
       nlk_at m kbs /\ frame_apart_gnl regs 16704 /\ nlk_wf kbs /\ nk_open kbs = 0
       /\ nk_opened kbs + 1 < 2 ^ 31 /\ nk_closed kbs + 1 < 2 ^ 31 /\ iftab_at m kbs tab
       /\ wr_at rsegs m (errno_at regs) 4
       /\ apart_frame regs 16704 (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
       /\ str_arg m (arg regs 0) nm
       /\ buf_arg m (arg regs 1) (arg regs 2) /\ buf_arg m (arg regs 3) (arg regs 4)
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_frame regs 16704 p (Z.of_nat (length n2) + 1)
             /\ apart_gnl p (Z.of_nat (length n2) + 1)
             /\ apart (errno_at regs) 4 p (Z.of_nat (length n2) + 1)
             /\ (arg regs 1 <> 0 -> 1 <= arg regs 2 ->
                   apart p (Z.of_nat (length n2) + 1) (arg regs 1) (arg regs 2))
             /\ (arg regs 3 <> 0 -> 1 <= arg regs 4 ->
                   apart p (Z.of_nat (length n2) + 1) (arg regs 3) (arg regs 4)))
       /\ (forall s, nm = Some s ->
             (arg regs 1 <> 0 -> 1 <= arg regs 2 ->
                apart (arg regs 0) (Z.of_nat (length s) + 1) (arg regs 1) (arg regs 2))
             /\ (arg regs 3 <> 0 -> 1 <= arg regs 4 ->
                apart (arg regs 0) (Z.of_nat (length s) + 1) (arg regs 3) (arg regs 4)))
       /\ (arg regs 1 <> 0 -> 1 <= arg regs 2 -> arg regs 3 <> 0 -> 1 <= arg regs 4 ->
             apart (arg regs 1) (arg regs 2) (arg regs 3) (arg regs 4))
       /\ (arg regs 1 <> 0 -> apart (errno_at regs) 4 (arg regs 1) (arg regs 2))
       /\ (arg regs 3 <> 0 -> apart (errno_at regs) 4 (arg regs 3) (arg regs 4))
       /\ (forall s, nm = Some s ->
             apart_frame regs 16704 (arg regs 0) (Z.of_nat (length s) + 1)
             /\ apart_gnl (arg regs 0) (Z.of_nat (length s) + 1))
       /\ (arg regs 1 <> 0 -> apart_frame regs 16704 (arg regs 1) (arg regs 2)
             /\ apart_gnl (arg regs 1) (arg regs 2))
       /\ (arg regs 3 <> 0 -> apart_frame regs 16704 (arg regs 3) (arg regs 4)
             /\ apart_gnl (arg regs 3) (arg regs 4))
       /\ errno_at regs <> 0 /\ errno_at regs mod 4 = 0 /\ spZ regs mod 4 = 0
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_frame regs 16704 p (Z.of_nat (length n2) + 1))
       /\ (arg regs 1 <> 0 -> arg regs 3 <> 0 ->
             arg regs 1 + arg regs 2 <= arg regs 3 \/ arg regs 3 + arg regs 4 <= arg regs 1)
       /\ (arg regs 1 <> 0 ->
             arg regs 1 + arg regs 2 <= errno_at regs \/ errno_at regs + 4 <= arg regs 1)
       /\ (arg regs 3 <> 0 ->
             arg regs 3 + arg regs 4 <= errno_at regs \/ errno_at regs + 4 <= arg regs 3)
       /\ (forall s, nm = Some s ->
             (arg regs 1 <> 0 -> arg regs 1 + arg regs 2 <= arg regs 0
                                 \/ arg regs 0 + Z.of_nat (length s) + 1 <= arg regs 1)
             /\ (arg regs 3 <> 0 -> arg regs 3 + arg regs 4 <= arg regs 0
                                    \/ arg regs 0 + Z.of_nat (length s) + 1 <= arg regs 3))
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             (arg regs 1 <> 0 -> arg regs 1 + arg regs 2 <= p
                                 \/ p + Z.of_nat (length n2) + 1 <= arg regs 1)
             /\ (arg regs 3 <> 0 -> arg regs 3 + arg regs 4 <= p
                                    \/ p + Z.of_nat (length n2) + 1 <= arg regs 3)))
    (fun regs m => [(A_G_NL, A_G_NL + NK_N_SENT + 4);
                    (errno_at regs, errno_at regs + 4);
                    (arg regs 1, arg regs 1 + (if arg regs 1 =? 0 then 0 else arg regs 2));
                    (arg regs 3, arg regs 3 + (if arg regs 3 =? 0 then 0 else arg regs 4))])
    (fun regs m regs' m' => forall kbs tab nm,
       nlk_at m kbs -> iftab_at m kbs tab -> str_arg m (arg regs 0) nm ->
       let R := read_lib tab nm (arg regs 2) (arg regs 4) (nk_sent kbs) (nk_kstate kbs) in
       getr regs' 10 = wz (r_rc R)
       /\ (exists kbs', nlk_at m' kbs' /\ nlk_wf kbs'
             /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
             /\ nk_n_if kbs' = nk_n_if kbs /\ iftab_at m' kbs' tab
             /\ nk_next kbs' = Z.of_nat (k_next (r_state R))
             /\ nk_socket_errno kbs' = k_sock (r_state R)
             /\ nk_send_errno kbs' = k_send (r_state R)
             /\ nk_sent kbs' = r_reqs R /\ nk_n_sent kbs' = Z.of_nat (length (r_reqs R))
       /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
       /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
       /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 1
             /\ ((nm = None \/ nm = Some [] \/ (forall s, nm = Some s -> index_of tab s = 0)) ->
                   nk_opened kbs' = nk_opened kbs))
       /\ (arg regs 1 <> 0 -> 1 <= arg regs 2 -> cstr_at m' (arg regs 1) (r_kind R))
       /\ (arg regs 3 <> 0 -> 1 <= arg regs 4 -> cstr_at m' (arg regs 3) (r_alias R))
       /\ (arg regs 1 <> 0 -> 1 <= arg regs 2 ->
             exists junk, rw_cells rsegs m' (arg regs 1) [CB (Z.to_nat (arg regs 2)) junk])
       /\ (arg regs 3 <> 0 -> 1 <= arg regs 4 ->
             exists junk, rw_cells rsegs m' (arg regs 3) [CB (Z.to_nat (arg regs 4)) junk])).
