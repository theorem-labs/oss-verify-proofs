(* reac_link_alias_read (reac_link_alias.c:95-119): the library reads one netdev`s link kind and
   interface alias over rtnetlink.

   a0 = name, a1 = kind, a2 = kind_n, a3 = alias, a4 = alias_n. It empties both buffers, refuses a
   NULL or empty name with -EINVAL and an unknown name with -ENODEV, and otherwise sends the
   32-byte RTM_GETLINK of link_spec`s `req_read` and answers nl_talk. link_spec`s `read_lib` is
   the whole of it, and `read_model` is the same function for model_read: the two differ only by
   `norm_rc`, which is link_spec read_agree and is what makes check_read never fire.
   CLAIM (c) of plain_halts is the refusal clause: a read the arguments already refuse opens no
   socket. K = 16672 (80 of its own, then nl_talk`s 16592).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition REAC_LINK_ALIAS_READ : Z := 0x15f2c.
Lemma REAC_LINK_ALIAS_READ_is_entry : REAC_LINK_ALIAS_READ = P_reac_link_alias_read. Proof. reflexivity. Qed.

Definition reac_link_alias_read_contract : Prop :=
  leaf REAC_LINK_ALIAS_READ 16672
    (fun regs m => exists kbs tab nm,
       nlk_at m kbs /\ frame_apart_gnl regs 16672 /\ nlk_wf kbs /\ nk_open kbs = 0
       /\ nk_opened kbs + 1 < 2 ^ 31 /\ nk_closed kbs + 1 < 2 ^ 31 /\ iftab_at m kbs tab
       /\ wr_at rsegs m (errno_at regs) 4
       /\ apart_frame regs 16672 (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
       /\ str_arg m (arg regs 0) nm
       /\ buf_arg m (arg regs 1) (arg regs 2) /\ buf_arg m (arg regs 3) (arg regs 4)
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_frame regs 16672 p (Z.of_nat (length n2) + 1)
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
             apart_frame regs 16672 (arg regs 0) (Z.of_nat (length s) + 1)
             /\ apart_gnl (arg regs 0) (Z.of_nat (length s) + 1))
       /\ (arg regs 1 <> 0 -> apart_frame regs 16672 (arg regs 1) (arg regs 2)
             /\ apart_gnl (arg regs 1) (arg regs 2))
       /\ (arg regs 3 <> 0 -> apart_frame regs 16672 (arg regs 3) (arg regs 4)
             /\ apart_gnl (arg regs 3) (arg regs 4)))
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
