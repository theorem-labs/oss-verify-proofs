(* reac_served_unmark_all (reac_served_mark.c:94-107): at exit, take away exactly the marks this
   run wrote that are still its own, and clear the list.

   a0 = m, which may be NULL. For each kept name it reads the alias; an interface that is gone, or
   whose alias somebody changed since, is left alone, and the rest get an empty alias written.
   Then it zeroes the whole 516-byte structure, so BOTH the count and every name go, where the
   harness model only sets its count to 0 (fuzz_link.c:472); check_marks compares only the first
   n entries, so the two still agree. link_spec`s `unmark` is the walk.
   K = 17232 (304 of its own, then reac_link_alias_write`s 16928).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). 
   GAP 13 (a Theorem Labs lane's sub-lane a Theorem Labs lane, 2026-10-30): the interface-table name strings. Both
   callees ask for them (alias_read at 0x167c8, alias_write at 0x167ec), and the memset at 0x1680c
   writes the whole marks block before this function's own Post asserts `iftab_at`.
   
   A NULL MARKS BLOCK OWNS NO BYTES (a Theorem Labs lane's gap 18, 2026-10-30): the write set's marks-block
   interval shrinks to nothing when a0 is NULL, the same rule as L7 for the reader buffers. The
   refusal returns at 0x16488 / 0x16490 / 0x1649c before any store outside the frame, and
   mark_quietly's mq_post_k needs every allocator-owned byte unchanged on that path, which an
   unguarded [0, 516) would not give.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition REAC_SERVED_UNMARK_ALL : Z := 0x16770.
Lemma REAC_SERVED_UNMARK_ALL_is_entry : REAC_SERVED_UNMARK_ALL = P_reac_served_unmark_all. Proof. reflexivity. Qed.

Definition reac_served_unmark_all_contract : Prop :=
  leaf REAC_SERVED_UNMARK_ALL 17232
    (fun regs m => exists kbs tab,
       nlk_at m kbs /\ frame_apart_gnl regs 17232 /\ nlk_wf kbs /\ nk_open kbs = 0
       /\ nk_opened kbs + 2 * MARKS_MAX < 2 ^ 31
       /\ nk_closed kbs + 2 * MARKS_MAX < 2 ^ 31 /\ iftab_at m kbs tab
       /\ wr_at rsegs m (errno_at regs) 4
       /\ apart_frame regs 17232 (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             let n := Z.of_nat (length n2) + 1 in
             apart_frame regs 17232 p n /\ apart_gnl p n /\ apart (errno_at regs) 4 p n
             /\ (arg regs 0 <> 0 -> apart (arg regs 0) MK_SIZE p n))
       /\ (arg regs 0 <> 0 -> apart_frame regs 17232 (arg regs 0) MK_SIZE
             /\ apart (errno_at regs) 4 (arg regs 0) MK_SIZE
             /\ apart_gnl (arg regs 0) MK_SIZE
             /\ exists gbs, marks_at m (arg regs 0) gbs /\ marks_wf gbs))
    (fun regs m => [(A_G_NL, A_G_NL + NK_N_SENT + 4);
                    (errno_at regs, errno_at regs + 4);
                    (arg regs 0, arg regs 0 + (if arg regs 0 =? 0 then 0 else MK_SIZE))])
    (fun regs m regs' m' =>
       (arg regs 0 = 0 -> m' = m)
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
