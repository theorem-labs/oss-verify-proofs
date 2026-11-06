(* model_write (fuzz_link.c:403-421), UBSAN build: what the harness says a write of an interface
   alias owes.

   The twin of lib/Prog/model_write_c.v, with its premises, its Wr set and its Post, and the
   premises its callees need in the ubsan build.
   a0 = m, a1 = name, a2 = alias. It refuses a NULL or empty name and a NULL alias with -EINVAL,
   an alias of IFALIASZ bytes or more with -ENAMETOOLONG (`bgeu` with 255 at 0x16294), and an
   unknown name with -ENODEV; otherwise it sends the RTM_NEWLINK of link_spec`s `req_write` and
   answers `talk`. link_spec`s `write_model` is the whole of it. strlen is called at 0x1628c,
   index_of at 0x162a8, then the request is built in the own frame at sp + 8 (memset at 0x162d0,
   the stores of req_head and of the attribute header, memcpy of the alias at 0x16364), and talk
   is called at 0x16384 with both text buffers NULL.
   K = 720: the own frame of 576 (link/donors/premises-ubsan.txt, `addi sp, sp, -0x240` at
   +0x00), then talk`s 144 (its own 112 plus take_text`s 32, lib/U/Prog/talk_c.v); strlen, memset
   and memcpy use no stack and index_of`s 64 fits inside that. The brief gave 688 = 576 + 112:
   link/ct/stack.py takes its call edges from link/functions.tsv, whose callee column is the PLAIN
   build`s, and so misses the two ubsan calls from talk to take_text. The prologue is at +0x00, so
   every returning path writes the frame; the plain Post claims nothing of the memory outside Wr
   and the frame, so it stands as it is.
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/model_write.s); every guard
   branches to the `unimp` at 0x163b4. All nine are on the request r = sp + 8 of the own frame,
   that is, entry sp - 568:
   - branch 0x162dc (fuzz_link.c:311, `bgeu s5, a0` with s5 = r, a0 = -4): r + 4 passes 2^64 - 1.
   - branch 0x162ec (fuzz_link.c:312, `bltu a1, s5` with a1 = -7): r + 6 passes 2^64 - 1.
   - branch 0x16300 (fuzz_link.c:313, `bltu a2, a0` with a2 = -9): r + 8 passes 2^64 - 1.
   - branch 0x16310 (fuzz_link.c:314, `bltu a2, a0` with a2 = -17): r + 16 passes 2^64 - 1.
   - branch 0x1631c (fuzz_link.c:314, `bltu a1, a0` with a0 = r + 16, a1 = -5): r + 20 passes
     2^64 - 1.
   - branch 0x16328 (fuzz_link.c:417, `bltu a1, a0` with a0 = r + 16, a1 = -17): r + 32 passes
     2^64 - 1.
   - branch 0x1633c and branch 0x16340 (fuzz_link.c:418, `beq a3, a1` with a3 = r and `beq a0, a1`
     with a0 = r + 16, a1 = -16): r or r + 16 is 2^64 - 16, so that r + 32 wraps to NULL.
   - branch 0x16354 (fuzz_link.c:419, `bltu a2, a0` with a0 = r + 32, a2 = -5): r + 36 passes
     2^64 - 1.
   ANSWERED BY THE SHAPE: `leaf` gives spZ regs < 2^63 and lo + 720 <= spZ regs with 0 <= lo
   (`stk`), so r = spZ regs - 568 is the real address and r + 36 < 2^64.
   So no premise is added for a guard of this function.
   Premises for the callees, not guards:
   - for callee talk`s U contract (its guard 0x15b88): `arg regs 0 mod 8 = 0`. talk`s other
     premises follow: its text buffers are NULL, the request lies in the own frame (outside talk`s
     frame [sp-720, sp-576) and outside the model block by `apart_frame regs 720`), and its length
     32 + NL_ALIGN(4 + alen) is at most 292 <= NL_SENT_LEN because alen <= 255 on that path.
   - for callee index_of`s U contract (lib/U/Prog/index_of_c.v: strcmp reads every table name after
     index_of pushes its frame [sp-640, sp-576)): every table name is outside this contract`s
     frame, `apart_frame regs 720`, which covers index_of`s frame.
   - for callee strlen`s contract (lib/U/Prog/strlen_c.v, the same in both builds): the bytes after
     the alias string`s NUL up to the next multiple of 8 are readable, as a list `slack` of at least
     `(- (alias + alen + 1)) mod 8` bytes. The plain twin lacks it too. With `apart_frame regs 720`
     of the string those bytes are outside the own frame, which is the only memory written before
     strlen runs.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function`s own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. 
   THE POST FIXES THE MODEL'S TWO ERRNOS (a Theorem Labs lane, AMEND-slot item 7, 2026-10-30): `talk` clears
   the socket errno and leaves the send errno as its own spec says, and a caller that runs a read
   and then a write (model_mark 0x13d98 -> 0x140a8, and model_unmark's loop) cannot show the second
   call runs on the state `mark_lib` and `unmark` run on unless this Post pins both.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition MODEL_WRITE : Z := 0x16248.
Lemma MODEL_WRITE_is_entry : MODEL_WRITE = P_model_write. Proof. reflexivity. Qed.

Definition model_write_contract : Prop :=
  leaf MODEL_WRITE 720
    (fun regs m => exists mbs kbs tab nm al,
       model_at m (arg regs 0) mbs /\ model_wf mbs
       /\ nlk_at m kbs /\ frame_apart_gnl regs 720 /\ nlk_wf kbs /\ iftab_at m kbs tab
       /\ str_arg m (arg regs 1) nm /\ str_arg m (arg regs 2) al
       /\ apart_gnl (arg regs 0) MD_SIZE /\ apart_frame regs 720 (arg regs 0) MD_SIZE
       /\ (forall s, nm = Some s ->
             apart_frame regs 720 (arg regs 1) (Z.of_nat (length s) + 1))
       /\ (forall s, al = Some s ->
             apart_frame regs 720 (arg regs 2) (Z.of_nat (length s) + 1))
       /\ arg regs 0 mod 8 = 0
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_frame regs 720 p (Z.of_nat (length n2) + 1))
       /\ (forall s, al = Some s -> exists slack,
             bytes_at rsegs m (arg regs 2 + Z.of_nat (length s) + 1) slack
             /\ (- (arg regs 2 + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)))
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
