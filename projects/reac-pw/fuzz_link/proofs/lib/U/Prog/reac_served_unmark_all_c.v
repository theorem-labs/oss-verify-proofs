(* reac_served_unmark_all (reac_served_mark.c:94-107), UBSAN build: at exit, take away exactly the
   marks this run wrote that are still its own, and clear the list.

   The twin of lib/Prog/reac_served_unmark_all_c.v, with its premises, the premises the UBSan
   guards below need, one counter premise made stronger, and ONE Post clause weaker than the plain
   twin (see the end). a0 = m, which may be NULL. For each kept name it reads the alias into
   char alias[256] at sp; an interface that is gone, or whose alias somebody changed since, is
   left alone, and the rest get an empty alias written. Then it zeroes the whole 516-byte
   structure. link_spec`s `unmark` is the walk.
   K = 17280 (320 of its own, then reac_link_alias_write`s 16960; reac_link_alias_read`s 16704,
   bcmp and memset fit inside that).
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/reac_served_unmark_all.s); every
   guard branches to the `unimp` at 0x17060, and both run only when m <> 0, so the added premise
   sits in that arm:
   - branch 0x16fa8 (reac_served_mark.c:98, `andi a0, a0, 3` before the read of m->n): traps
     unless m is 4-aligned. ADDED: `arg regs 0 mod 4 = 0`.
   - branch 0x16fd4 (reac_served_mark.c:100, `not s6, s1; bltu s6, s4` with s1 = m + 4 and
     s4 = 16 i): traps when m->name[i] = m + 4 + 16 i passes 2^64 - 1. ANSWERED BY THE PLAIN
     PREMISES: marks_wf gives i < m->n <= 32, so the sum is below m + MK_SIZE, and marks_at`s
     u8arr gives m + MK_SIZE <= 2^64. reac_link_alias_read and reac_link_alias_write do not write
     the marks block, so m->n, read again each round, keeps that bound.
   ADDED FOR THE CALLEES` GUARDS, reached through reac_link_alias_read and reac_link_alias_write
   (lib/U/Prog/reac_link_alias_read_c.v, reac_link_alias_write_c.v, nl_talk_c.v):
   - `errno_at regs <> 0 /\ errno_at regs mod 4 = 0` and `spZ regs mod 4 = 0` (nl_talk branches
     0x16800 to 0x16850 and 0x167a8). Both callees run at sp - 320, a multiple of 4.
   - THE COUNTER PREMISE IS STRONGER THAN THE PLAIN TWIN`S `nk_opened kbs + 1 < 2 ^ 31` and
     `nk_closed kbs + 1 < 2 ^ 31`: fuzz_socket traps when g_nl.opened++ overflows int (branch
     0x135c0) and fuzz_close when g_nl.closed++ does (branch 0x13950). This function makes up to
     two exchanges per kept name (a read, then a write) and keeps at most MARKS_MAX names, so the
     counters move by up to 2 MARKS_MAX = 64. HERE: `nk_opened kbs + 2 * MARKS_MAX < 2 ^ 31` and
     `nk_closed kbs + 2 * MARKS_MAX < 2 ^ 31`. The plain twin needs the same bound for its own
     nlk_wf Post; that is noted for the plain lane, not changed here.
   ADDED FOR CALLEES` CONTRACTS THAT THE PLAIN TWIN DOES NOT CARRY EITHER (noted for the plain
   lane; none answers a UBSan guard):
   - `policy_ro m`: the walk compares the alias with the .rodata `reac-pw:served` (bcmp, 15 bytes,
     +0x88) and hands the .rodata empty string to reac_link_alias_write, whose `str_arg` needs it
     as a C string.
   - every table name outside this contract`s frame (`apart_frame regs 17280 p ...`): both
     callees pass it to fuzz_if_nametoindex (lib/U/Prog/index_of_c.v), whose strcmp reads it.
   - the slack strlen reads after the empty string (lib/U/Prog/strlen_c.v, through
     reac_link_alias_write): the bytes from A_EMPTY + 1 up to the next multiple of 8 are readable.
   WEAKER POST THAN THE PLAIN TWIN: the ubsan build pushes its 320-byte frame (ra, s0-s6) BEFORE
   it tests m (+0x24); the plain build tests m before its prologue. So a NULL m leaves memory
   unchanged only outside that frame here: `munch [(spZ regs - 320, spZ regs)] m m'` where the
   plain twin says `m' = m`.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. 
   GAP 13 (a Theorem Labs lane's sub-lane a Theorem Labs lane, 2026-10-30): the interface-table name strings. Both
   callees ask for them (alias_read at 0x167c8, alias_write at 0x167ec), and the memset at 0x1680c
   writes the whole marks block before this function's own Post asserts `iftab_at`.
   
   A NULL MARKS BLOCK OWNS NO BYTES (a Theorem Labs lane's gap 18, 2026-10-30): the write set's marks-block
   interval shrinks to nothing when a0 is NULL, the same rule as L7 for the reader buffers. The
   refusal returns at 0x16488 / 0x16490 / 0x1649c before any store outside the frame, and
   mark_quietly's mq_post_k needs every allocator-owned byte unchanged on that path, which an
   unguarded [0, 516) would not give.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition REAC_SERVED_UNMARK_ALL : Z := 0x16f78.
Lemma REAC_SERVED_UNMARK_ALL_is_entry : REAC_SERVED_UNMARK_ALL = P_reac_served_unmark_all. Proof. reflexivity. Qed.

Definition reac_served_unmark_all_contract : Prop :=
  leaf REAC_SERVED_UNMARK_ALL 17280
    (fun regs m => exists kbs tab,
       nlk_at m kbs /\ frame_apart_gnl regs 17280 /\ nlk_wf kbs /\ nk_open kbs = 0
       /\ nk_opened kbs + 2 * MARKS_MAX < 2 ^ 31 /\ nk_closed kbs + 2 * MARKS_MAX < 2 ^ 31
       /\ iftab_at m kbs tab
       /\ wr_at rsegs m (errno_at regs) 4
       /\ apart_frame regs 17280 (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
       /\ errno_at regs <> 0 /\ errno_at regs mod 4 = 0 /\ spZ regs mod 4 = 0
       /\ policy_ro m
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_frame regs 17280 p (Z.of_nat (length n2) + 1))
       /\ (exists slack, bytes_at rsegs m (A_EMPTY + 1) slack
             /\ (- (A_EMPTY + 1)) mod 8 <= Z.of_nat (length slack))
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             let n := Z.of_nat (length n2) + 1 in
             apart_frame regs 17280 p n /\ apart_gnl p n /\ apart (errno_at regs) 4 p n
             /\ (arg regs 0 <> 0 -> apart (arg regs 0) MK_SIZE p n))
       /\ (arg regs 0 <> 0 -> apart_frame regs 17280 (arg regs 0) MK_SIZE
             /\ apart (errno_at regs) 4 (arg regs 0) MK_SIZE
             /\ apart_gnl (arg regs 0) MK_SIZE
             /\ arg regs 0 mod 4 = 0
             /\ exists gbs, marks_at m (arg regs 0) gbs /\ marks_wf gbs))
    (fun regs m => [(A_G_NL, A_G_NL + NK_N_SENT + 4);
                    (errno_at regs, errno_at regs + 4);
                    (arg regs 0, arg regs 0 + (if arg regs 0 =? 0 then 0 else MK_SIZE))])
    (fun regs m regs' m' =>
       (arg regs 0 = 0 -> munch [(spZ regs - 320, spZ regs)] m m')
       /\ (arg regs 0 <> 0 -> forall kbs tab gbs,
             nlk_at m kbs -> iftab_at m kbs tab -> marks_at m (arg regs 0) gbs ->
             let U := unmark tab (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) in
             (exists gbs', marks_at m' (arg regs 0) gbs' /\ marks_wf gbs' /\ mk_n gbs' = 0)
             /\ (exists kbs', nlk_at m' kbs' /\ nlk_wf kbs'
                   /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
                   /\ nk_n_if kbs' = nk_n_if kbs /\ iftab_at m' kbs' tab
                   /\ nk_next kbs' = Z.of_nat (k_next (snd U))
                   /\ nk_sent kbs' = fst U /\ nk_n_sent kbs' = Z.of_nat (length (fst U))
                   /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
                   /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
                   /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 2 * MARKS_MAX))).
