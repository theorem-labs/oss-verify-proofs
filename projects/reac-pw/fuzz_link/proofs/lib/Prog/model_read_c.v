(* model_read (fuzz_link.c:386-401): what the harness says a read of an interface alias owes.

   a0 = m, a1 = name, a2 = kind, a3 = kind_n, a4 = alias, a5 = alias_n. It empties both buffers,
   refuses a NULL or empty name with -EINVAL and an unknown name with -ENODEV, and otherwise sends
   the 32-byte RTM_GETLINK of link_spec`s `req_read` and answers `talk`. link_spec`s `read_model`
   is the whole of it, and `read_lib` is the same function for reac_link_alias_read, which is why
   check_read never fires (link_spec read_agree). K = 240 (96 of its own, then talk`s 144;
   index_of`s 48 and memset fit inside that).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). 
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition MODEL_READ : Z := 0x14ffc.
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
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_frame regs 240 p (Z.of_nat (length n2) + 1))
       /\ (forall s, nm = Some s ->
             (arg regs 2 <> 0 -> 1 <= arg regs 3 ->
                apart (arg regs 2) (arg regs 3) (arg regs 1) (Z.of_nat (length s) + 1))
             /\ (arg regs 4 <> 0 -> 1 <= arg regs 5 ->
                apart (arg regs 4) (arg regs 5) (arg regs 1) (Z.of_nat (length s) + 1)))
       /\ (arg regs 2 <> 0 -> 1 <= arg regs 3 ->
             apart_gnl (arg regs 2) (arg regs 3)
             /\ apart (arg regs 2) (arg regs 3) (arg regs 0) MD_SIZE
             /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
                   u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
                   apart (arg regs 2) (arg regs 3) p (Z.of_nat (length n2) + 1)))
       /\ (arg regs 4 <> 0 -> 1 <= arg regs 5 ->
             apart_gnl (arg regs 4) (arg regs 5)
             /\ apart (arg regs 4) (arg regs 5) (arg regs 0) MD_SIZE
             /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
                   u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
                   apart (arg regs 4) (arg regs 5) p (Z.of_nat (length n2) + 1)))
       /\ (arg regs 2 <> 0 -> arg regs 4 <> 0 -> 1 <= arg regs 3 -> 1 <= arg regs 5 ->
             apart (arg regs 2) (arg regs 3) (arg regs 4) (arg regs 5)))
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
