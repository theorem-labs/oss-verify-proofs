(* model_write (fuzz_link.c:403-421): what the harness says a write of an interface alias owes.

   a0 = m, a1 = name, a2 = alias. It refuses a NULL or empty name and a NULL alias with -EINVAL,
   an alias of IFALIASZ bytes or more with -ENAMETOOLONG, and an unknown name with -ENODEV;
   otherwise it sends the RTM_NEWLINK of link_spec`s `req_write` and answers `talk`.
   link_spec`s `write_model` is the whole of it, and `write_lib` is the same function for
   reac_link_alias_write, which is why check_write never fires (link_spec write_agree).
   K = 704 (560 of its own, then talk`s 144).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images).
   STRLEN`S SLACK (LinkHelpers, 2026-10-30): the call to strlen on the alias needs the bytes
   after its NUL up to the next multiple of 8 readable (lib/Prog/strlen_c.v); the UBSan twin
   already stated it, the plain twin did not. 
   THE POST FIXES THE MODEL'S TWO ERRNOS (a Theorem Labs lane, AMEND-slot item 7, 2026-10-30): `talk` clears
   the socket errno and leaves the send errno as its own spec says, and a caller that runs a read
   and then a write (model_mark 0x13d98 -> 0x140a8, and model_unmark's loop) cannot show the second
   call runs on the state `mark_lib` and `unmark` run on unless this Post pins both.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition MODEL_WRITE : Z := 0x15c50.
Lemma MODEL_WRITE_is_entry : MODEL_WRITE = P_model_write. Proof. reflexivity. Qed.

Definition model_write_contract : Prop :=
  leaf MODEL_WRITE 704
    (fun regs m => exists mbs kbs tab nm al,
       model_at m (arg regs 0) mbs /\ model_wf mbs
       /\ nlk_at m kbs /\ frame_apart_gnl regs 704 /\ nlk_wf kbs /\ iftab_at m kbs tab
       /\ str_arg m (arg regs 1) nm /\ str_arg m (arg regs 2) al
       /\ apart_gnl (arg regs 0) MD_SIZE /\ apart_frame regs 704 (arg regs 0) MD_SIZE
       /\ (forall s, nm = Some s ->
             apart_frame regs 704 (arg regs 1) (Z.of_nat (length s) + 1))
       /\ (forall s, al = Some s ->
             apart_frame regs 704 (arg regs 2) (Z.of_nat (length s) + 1))
       /\ (forall s, al = Some s -> exists slack,
             bytes_at rsegs m (arg regs 2 + Z.of_nat (length s) + 1) slack
             /\ (- (arg regs 2 + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack))
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_frame regs 704 p (Z.of_nat (length n2) + 1)))
    (fun regs m => [(arg regs 0, arg regs 0 + MD_SIZE)])
    (fun regs m regs' m' => forall mbs kbs tab nm al,
       model_at m (arg regs 0) mbs -> nlk_at m kbs -> iftab_at m kbs tab ->
       str_arg m (arg regs 1) nm -> str_arg m (arg regs 2) al ->
       let W := write_model tab nm al (md_reqs mbs) (md_kstate mbs kbs) in
       getr regs' 10 = wz (w_rc W)
       /\ (exists mbs', model_at m' (arg regs 0) mbs' /\ model_wf mbs'
             /\ md_next mbs' = Z.of_nat (k_next (w_state W))
             /\ md_socket_errno mbs' = k_sock (w_state W)
             /\ md_send_errno mbs' = k_send (w_state W)
             /\ md_reqs mbs' = w_reqs W /\ md_n_req mbs' = Z.of_nat (length (w_reqs W))
             /\ md_n_mark mbs' = md_n_mark mbs /\ md_marks mbs' = md_marks mbs)).
