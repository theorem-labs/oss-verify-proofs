(* talk (fuzz_link.c:333-384): the harness model of one request and its reply.

   a0 = m, a1 = r, a2 = len, a3 = kind, a4 = kind_n, a5 = alias, a6 = alias_n.
   It answers the code the reply spells, and fills the kind and the alias from the first
   RTM_NEWLINK. link_spec`s `talk_core` is ONE spec for this function and for the library`s
   nl_talk: the two walk the same chunk bytes with the same tests, and differ only in the
   normalisation of a positive NLMSG_ERROR code, which `norm_rc` applies here and not there.
   talk reads the chunk queue and the end errno from g_nl and keeps its OWN socket errno, send
   errno and cursor in the model block; it writes NO byte of g_nl.
   The two text buffers are touched only when the reply really carries that attribute: when it
   does not, talk leaves them as the caller set them (model_read puts a NUL at index 0 first).
   K = 144 (own frame; memcpy uses no stack).
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

Definition TALK : Z := 0x156e4.
Lemma TALK_is_entry : TALK = P_talk. Proof. reflexivity. Qed.

Definition talk_contract : Prop :=
  leaf TALK 144
    (fun regs m => exists mbs kbs req,
       model_at m (arg regs 0) mbs /\ model_wf mbs
       /\ nlk_at m kbs /\ frame_apart_gnl regs 144 /\ nlk_wf kbs
       /\ bytes_at rsegs m (arg regs 1) req /\ Z.of_nat (length req) = arg regs 2
       /\ 0 <= arg regs 2 <= NL_SENT_LEN
       /\ buf_arg m (arg regs 3) (arg regs 4) /\ buf_arg m (arg regs 5) (arg regs 6)
       /\ apart (arg regs 1) (arg regs 2) (arg regs 0) MD_SIZE
       /\ (arg regs 3 <> 0 -> 1 <= arg regs 4 ->
             apart_gnl (arg regs 3) (arg regs 4)
             /\ apart (arg regs 3) (arg regs 4) (arg regs 0) MD_SIZE)
       /\ (arg regs 5 <> 0 -> 1 <= arg regs 6 ->
             apart_gnl (arg regs 5) (arg regs 6)
             /\ apart (arg regs 5) (arg regs 6) (arg regs 0) MD_SIZE)
       /\ (arg regs 3 <> 0 -> 1 <= arg regs 4 -> arg regs 5 <> 0 -> 1 <= arg regs 6 ->
             apart (arg regs 3) (arg regs 4) (arg regs 5) (arg regs 6))
       /\ apart_gnl (arg regs 0) MD_SIZE /\ apart_frame regs 144 (arg regs 0) MD_SIZE
       /\ apart_frame regs 144 (arg regs 1) (arg regs 2)
       /\ (arg regs 3 <> 0 -> apart_frame regs 144 (arg regs 3) (arg regs 4))
       /\ (arg regs 5 <> 0 -> apart_frame regs 144 (arg regs 5) (arg regs 6)))
    (fun regs m => [(arg regs 0, arg regs 0 + MD_SIZE);
                    (arg regs 3, arg regs 3 + (if arg regs 3 =? 0 then 0 else arg regs 4));
                    (arg regs 5, arg regs 5 + (if arg regs 5 =? 0 then 0 else arg regs 6))])
    (fun regs m regs' m' => forall mbs kbs req,
       model_at m (arg regs 0) mbs -> nlk_at m kbs ->
       bytes_at rsegs m (arg regs 1) req -> Z.of_nat (length req) = arg regs 2 ->
       let K0 := md_kstate mbs kbs in
       getr regs' 10 = wz (talk_rc_model K0)
       /\ (exists mbs', model_at m' (arg regs 0) mbs' /\ model_wf mbs'
             /\ md_next mbs' = Z.of_nat (k_next (talk_after K0))
             /\ md_socket_errno mbs' = 0
             /\ md_send_errno mbs' = k_send (talk_after K0)
             /\ md_n_mark mbs' = md_n_mark mbs /\ md_marks mbs' = md_marks mbs
             /\ md_reqs mbs' = (if talk_owes K0 then owe (md_reqs mbs) req else md_reqs mbs)
             /\ md_n_req mbs' = Z.of_nat (length (md_reqs mbs')))
       /\ (forall pay, a_kind (talk_attrs K0) = Some pay -> arg regs 3 <> 0 -> 1 <= arg regs 4 ->
             cstr_at m' (arg regs 3) (cut_text pay (arg regs 4)))
       /\ (forall pay, a_alias (talk_attrs K0) = Some pay -> arg regs 5 <> 0 -> 1 <= arg regs 6 ->
             cstr_at m' (arg regs 5) (cut_text pay (arg regs 6)))
       /\ (a_kind (talk_attrs K0) = None ->
             munch [(arg regs 0, arg regs 0 + MD_SIZE);
                    (arg regs 5, arg regs 5 + (if arg regs 5 =? 0 then 0 else arg regs 6));
                    (spZ regs - 144, spZ regs)] m m')
       /\ (a_alias (talk_attrs K0) = None ->
             munch [(arg regs 0, arg regs 0 + MD_SIZE);
                    (arg regs 3, arg regs 3 + (if arg regs 3 =? 0 then 0 else arg regs 4));
                    (spZ regs - 144, spZ regs)] m m')
       /\ (arg regs 3 <> 0 -> 1 <= arg regs 4 ->
             exists junk, rw_cells rsegs m' (arg regs 3) [CB (Z.to_nat (arg regs 4)) junk])
       /\ (arg regs 5 <> 0 -> 1 <= arg regs 6 ->
             exists junk, rw_cells rsegs m' (arg regs 5) [CB (Z.to_nat (arg regs 6)) junk])).
