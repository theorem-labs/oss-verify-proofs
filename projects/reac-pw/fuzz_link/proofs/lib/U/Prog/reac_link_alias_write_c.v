(* reac_link_alias_write (reac_link_alias.c:121-149), UBSAN build: the library sets one netdev`s
   interface alias over rtnetlink; an empty alias removes it.

   The twin of lib/Prog/reac_link_alias_write_c.v, with its premises, its Post, and the premises
   its callee nl_talk`s U contract needs. a0 = name, a1 = alias. It refuses a NULL or empty name
   and a NULL alias with -EINVAL, an alias of IFALIASZ = 256 bytes or more with -ENAMETOOLONG, and
   an unknown name with -ENODEV; otherwise it builds the RTM_NEWLINK of link_spec`s `req_write` in
   its own frame (the request at sp + 0xc, its IFLA_IFALIAS attribute at sp + 0x2c) and answers
   nl_talk. link_spec`s `write_lib` is the whole of it. CLAIM (c) of the halting theorem is the
   refusal clause, as in the plain twin.
   K = 16960 (336 of its own, then nl_talk`s 16624; strlen and memcpy use no stack and
   fuzz_if_nametoindex`s 64 fits inside that).
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/reac_link_alias_write.s):
   - branch 0x16a8c (reac_link_alias.c:146, RTA_DATA(a) in the memcpy, `beq a2, a3` with
     a2 = sp + 0x2c after the push and a3 = -4, to the `unimp` at 0x16ae8): traps when
     a + 4 wraps to 0, that is when sp - 336 + 0x2c = 2^64 - 4. ANSWERED BY the shape:
     spZ regs < 2^63.
   ADDED FOR CALLEE nl_talk`s U CONTRACT (lib/U/Prog/nl_talk_c.v), which answers nl_talk`s
   guards and those of fuzz_socket, fuzz_send and fuzz_recv:
   - `errno_at regs <> 0 /\ errno_at regs mod 4 = 0`: the errno address is not NULL and is
     4-aligned (nl_talk branches 0x16800 to 0x16850). errno is fixed by tp, which the call keeps.
   - `spZ regs mod 4 = 0`: nl_talk`s receive buffer is 4-aligned (nl_talk branch 0x167a8).
     nl_talk runs at sp - 336, and 336 is a multiple of 4.
   ADDED FOR CALLEES` CONTRACTS THAT THE PLAIN TWIN DOES NOT CARRY EITHER (noted for the plain
   lane; neither answers a UBSan guard):
   - for fuzz_if_nametoindex`s U contract (lib/U/Prog/index_of_c.v): its strcmp reads every table
     name after the callee pushes its frame at sp - 336, so every table name is outside this
     contract`s frame: `apart_frame regs 16960 p ...` for each if_name pointer p.
   - for strlen`s contract (lib/U/Prog/strlen_c.v, the same in both builds; called at +0x34 on
     the alias): the bytes after the alias`s NUL up to the next multiple of 8 are readable, as a
     list `slack` of at least `(- (alias + alen + 1)) mod 8` bytes.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. 
   GAP 10 (a Theorem Labs lane's sub-lane a Theorem Labs lane, 2026-10-30): the Post must fix the fake kernel's two
   errno fields as well, so that `nk_kstate kbs'` IS the state the spec continued from. A chained
   caller (reac_served_unmark_all's read at 0x167c8 then write at 0x167ec, then the next round;
   reac_served_mark's 0x164b4 then 0x16530) states its own Post over `r_state R` / `w_state W`,
   which `talk_after` has cleared, while the next callee's Post speaks of `nk_kstate kbs'`; with
   the two fields free the request list after the second call is not `fst U` or `m_reqs M`.
   nl_talk's Post already gives the same of its own kstate.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition REAC_LINK_ALIAS_WRITE : Z := 0x169f0.
Lemma REAC_LINK_ALIAS_WRITE_is_entry : REAC_LINK_ALIAS_WRITE = P_reac_link_alias_write. Proof. reflexivity. Qed.

Definition reac_link_alias_write_contract : Prop :=
  leaf REAC_LINK_ALIAS_WRITE 16960
    (fun regs m => exists kbs tab nm al,
       nlk_at m kbs /\ frame_apart_gnl regs 16960 /\ nlk_wf kbs /\ nk_open kbs = 0
       /\ nk_opened kbs + 1 < 2 ^ 31 /\ nk_closed kbs + 1 < 2 ^ 31 /\ iftab_at m kbs tab
       /\ wr_at rsegs m (errno_at regs) 4
       /\ apart_frame regs 16960 (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
       /\ str_arg m (arg regs 0) nm /\ str_arg m (arg regs 1) al
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_gnl p (Z.of_nat (length n2) + 1)
             /\ apart (errno_at regs) 4 p (Z.of_nat (length n2) + 1))
       /\ (forall s, nm = Some s ->
             apart_frame regs 16960 (arg regs 0) (Z.of_nat (length s) + 1)
             /\ apart_gnl (arg regs 0) (Z.of_nat (length s) + 1))
       /\ (forall s, al = Some s ->
             apart_frame regs 16960 (arg regs 1) (Z.of_nat (length s) + 1)
             /\ apart_gnl (arg regs 1) (Z.of_nat (length s) + 1))
       /\ errno_at regs <> 0 /\ errno_at regs mod 4 = 0 /\ spZ regs mod 4 = 0
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_frame regs 16960 p (Z.of_nat (length n2) + 1))
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
