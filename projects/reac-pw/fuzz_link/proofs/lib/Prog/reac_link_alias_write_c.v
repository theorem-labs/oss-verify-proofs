(* reac_link_alias_write (reac_link_alias.c:121-149): the library sets one netdev`s interface alias
   over rtnetlink; an empty alias removes it.

   a0 = name, a1 = alias. It refuses a NULL or empty name and a NULL alias with -EINVAL, an alias
   of IFALIASZ = 256 bytes or more with -ENAMETOOLONG, and an unknown name with -ENODEV;
   otherwise it sends the RTM_NEWLINK of link_spec`s `req_write` and answers nl_talk.
   link_spec`s `write_lib` is the whole of it, and `write_model` is the same function for
   model_write (link_spec write_agree), which is what makes check_write never fire.
   CLAIM (c) of plain_halts is the refusal clause. K = 16928 (336 of its own, then nl_talk`s
   16592).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images).
   STRLEN`S SLACK (LinkHelpers, 2026-10-30): the call to strlen on the alias needs the bytes
   after its NUL up to the next multiple of 8 readable (lib/Prog/strlen_c.v); the UBSan twin
   already stated it, the plain twin did not. 
   GAP 10 (a Theorem Labs lane's sub-lane a Theorem Labs lane, 2026-10-30): the Post must fix the fake kernel's two
   errno fields as well, so that `nk_kstate kbs'` IS the state the spec continued from. A chained
   caller (reac_served_unmark_all's read at 0x167c8 then write at 0x167ec, then the next round;
   reac_served_mark's 0x164b4 then 0x16530) states its own Post over `r_state R` / `w_state W`,
   which `talk_after` has cleared, while the next callee's Post speaks of `nk_kstate kbs'`; with
   the two fields free the request list after the second call is not `fst U` or `m_reqs M`.
   nl_talk's Post already gives the same of its own kstate.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition REAC_LINK_ALIAS_WRITE : Z := 0x16290.
Lemma REAC_LINK_ALIAS_WRITE_is_entry : REAC_LINK_ALIAS_WRITE = P_reac_link_alias_write. Proof. reflexivity. Qed.

Definition reac_link_alias_write_contract : Prop :=
  leaf REAC_LINK_ALIAS_WRITE 16928
    (fun regs m => exists kbs tab nm al,
       nlk_at m kbs /\ frame_apart_gnl regs 16928 /\ nlk_wf kbs /\ nk_open kbs = 0
       /\ nk_opened kbs + 1 < 2 ^ 31 /\ nk_closed kbs + 1 < 2 ^ 31 /\ iftab_at m kbs tab
       /\ wr_at rsegs m (errno_at regs) 4
       /\ apart_frame regs 16928 (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
       /\ str_arg m (arg regs 0) nm /\ str_arg m (arg regs 1) al
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_frame regs 16928 p (Z.of_nat (length n2) + 1)
             /\ apart_gnl p (Z.of_nat (length n2) + 1)
             /\ apart (errno_at regs) 4 p (Z.of_nat (length n2) + 1))
       /\ (forall s, nm = Some s ->
             apart_frame regs 16928 (arg regs 0) (Z.of_nat (length s) + 1)
             /\ apart_gnl (arg regs 0) (Z.of_nat (length s) + 1))
       /\ (forall s, al = Some s ->
             apart_frame regs 16928 (arg regs 1) (Z.of_nat (length s) + 1)
             /\ apart_gnl (arg regs 1) (Z.of_nat (length s) + 1))
       /\ (forall s, al = Some s -> exists slack,
             bytes_at rsegs m (arg regs 1 + Z.of_nat (length s) + 1) slack
             /\ (- (arg regs 1 + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)))
    (fun regs m => [(A_G_NL, A_G_NL + NK_N_SENT + 4);
                    (errno_at regs, errno_at regs + 4)])
    (fun regs m regs' m' => forall kbs tab nm al,
       nlk_at m kbs -> iftab_at m kbs tab ->
       str_arg m (arg regs 0) nm -> str_arg m (arg regs 1) al ->
       let W := write_lib tab nm al (nk_sent kbs) (nk_kstate kbs) in
       getr regs' 10 = wz (w_rc W)
       /\ (exists kbs', nlk_at m' kbs' /\ nlk_wf kbs'
             /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
             /\ nk_n_if kbs' = nk_n_if kbs /\ iftab_at m' kbs' tab
             /\ nk_next kbs' = Z.of_nat (k_next (w_state W))
             /\ nk_socket_errno kbs' = k_sock (w_state W)
             /\ nk_send_errno kbs' = k_send (w_state W)
             /\ nk_sent kbs' = w_reqs W /\ nk_n_sent kbs' = Z.of_nat (length (w_reqs W))
       /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
       /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
       /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 1
             /\ ((nm = None \/ al = None \/ nm = Some []
                  \/ (forall s, al = Some s -> ALIAS_MAX <= Z.of_nat (length s))
                  \/ (forall s, nm = Some s -> index_of tab s = 0)) ->
                   nk_opened kbs' = nk_opened kbs))).
