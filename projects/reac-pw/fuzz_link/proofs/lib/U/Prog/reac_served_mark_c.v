(* reac_served_mark (reac_served_mark.c:48-92), UBSAN build: the marking policy for one interface.

   The twin of lib/Prog/reac_served_mark_c.v, with its premises, its Post, the premises the UBSan
   guards below need, the premises its callees` U contracts need, and ONE change to the Wr set
   (see the end). a0 = m, a1 = ifname. It refuses a NULL marks block, a NULL name and an empty
   name with -EINVAL; otherwise it reads the interface`s kind and alias into two buffers of its
   own frame (char kind[32] at sp + 0x100, char alias[256] at sp), takes the verdict of
   reac_served_decide, writes the served alias and remembers the name when the verdict is MARK,
   remembers it when the verdict is OURS and the alias is exactly `reac-pw:served` (a 15-byte
   bcmp), and answers the verdict. On a failed read or write it answers that code instead.
   link_spec`s `mark_lib` is the whole of it. The lines it writes on its stream are not part of
   this contract (see reac_code_emit) beyond how many bytes they leave pending: the stream is
   link`s one memory FILE, stated with lib/U/Prog/memfile_c.v`s `memfile_k`, at most one line of
   MARK_LINE_MAX bytes per call (link/ct/AMEND-mark.md gap 2). This contract uses leaf_fp because
   fprintf and vfprintf run the printf layer.
   K = 17280 (320 of its own, then reac_link_alias_write`s 16960; reac_link_alias_read`s 16704,
   remember`s 6432, reac_code_emit`s 6112 and fprintf`s 6048 fit inside that).
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/reac_served_mark.s); every guard
   branches to the `unimp` at 0x16de4, and both run only when m <> 0 and the name is not empty:
   - branch 0x16c54 (reac_served_mark.c:58, `neg a5, a0; negw a0, a0; bne a0, a5`): traps when
     `-rc` overflows int, rc being reac_link_alias_read`s nonzero answer, that is when
     rc = -2^31.
   - branch 0x16cdc (reac_served_mark.c:69, the same test): traps when `-rc` overflows int, rc
     being reac_link_alias_write`s nonzero answer.
     In link_spec`s `mark_core` a nonzero read code and a nonzero write code are each the answer
     m_rc, and every other answer is -EINVAL or a verdict in 0..3. So both guards are answered by
     one arithmetic premise on the answer. ADDED, in the m <> 0 arm:
     `m_rc (mark_lib tab nm (mk_names gbs) (nk_sent kbs) (nk_kstate kbs)) <> - 2 ^ 31`.
   ADDED FOR THE CALLEES` GUARDS:
   - `arg regs 0 mod 4 = 0`, in the m <> 0 arm: remember`s guard 0x16e8c traps unless m is
     4-aligned (lib/U/Prog/remember_c.v).
   - `errno_at regs <> 0 /\ errno_at regs mod 4 = 0` and `spZ regs mod 4 = 0`: nl_talk`s guards
     0x16800 to 0x16850 and 0x167a8, reached through reac_link_alias_read and
     reac_link_alias_write (lib/U/Prog/nl_talk_c.v). Both callees run at sp - 320, a multiple
     of 4.
   - THE COUNTER PREMISE IS STRONGER THAN THE PLAIN TWIN`S `+ 1`: fuzz_socket traps when
     g_nl.opened++ overflows int (branch 0x135c0) and fuzz_close when g_nl.closed++ does (branch
     0x13950). A MARK verdict makes two exchanges (the read, then the write), so the counters move
     by up to 2. HERE: `nk_opened kbs + 2 < 2 ^ 31` and `nk_closed kbs + 2 < 2 ^ 31`. The plain
     twin needs the same bound for its own nlk_wf Post; that is noted for the plain lane.
   ADDED FOR CALLEES` CONTRACTS THAT THE PLAIN TWIN DOES NOT CARRY EITHER (noted for the plain
   lane; it answers no UBSan guard): every table name outside this contract`s frame
   (`apart_frame regs 17280 p ...`), because reac_link_alias_read and reac_link_alias_write pass
   it to fuzz_if_nametoindex (lib/U/Prog/index_of_c.v), whose strcmp reads it. The strlen slack
   reac_link_alias_write now takes for its alias holds of `reac-pw:served` at 0x10341 with no
   byte: the string and its NUL end at 0x10350, a multiple of 8. Also for remember`s contract
   (lib/U/Prog/remember_c.v), in the m <> 0 arm: the name has at most 15 bytes and lies apart
   from the marks block. remember stores n + 1 into m->n BEFORE snprintf reads the name, so a
   name inside the block would change under it and the Post`s mark list would be false.
   THE Wr SET NAMES THE STREAM`S FILE BLOCK, WHICH THE PLAIN TWIN`S DOES NOT: fprintf and
   reac_code_emit write the FILE structure at g_say (the 1304-byte block fmemopen made), not only
   g_said, and lib/U/Prog/reac_code_emit_c.v`s Wr already says so (`sink_region`). So the stream
   address is bound outside the shape (`forall sink`) and the Wr set holds
   (sink, sink + 1304) beside g_said. The plain twin`s Wr lacks that interval; that is noted for
   the plain lane.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. 
   GAP 9 (a Theorem Labs lane, 2026-10-30): errno must also be apart from g_say and g_said, and inside the
   image. reac_served_mark reads g_say AFTER its callees (ld at 0x164c4 after the alias_read call
   at 0x164b4, and 0x16540 after alias_write at 0x16530), and both callees have errno in their
   write set, so without the first two the `u64_at m A_G_SAY sink` fact is lost across the call and
   the stderr arm at 0x164cc cannot be ruled out. The image range gives rewind's errno_ok its
   separation from the FILE block, including the fresh one fmemopen returns, through mf_place_ok.
   All three hold of the real errno, which is in .bss at 0x75564.
   
   GAPS 11 AND 12 (a Theorem Labs lane's sub-lane a Theorem Labs lane, 2026-10-30). 11: the interface-table name strings.
   Both callees ask each g_nl if_name string to be apart from the callee frame, g_nl and errno, and
   this function's own Post (`iftab_at m' kbs' tab`) must survive its prologue stores
   (0x16474-0x16480), remember's writes to the marks block (0x165c8, 0x1660c) and the printf writes
   to the FILE block (0x16598, 0x165f8). `mark_table_ok` says it once, for both callers. True of
   the binary: the names live in g_names (.bss) and in the `odd` table's .rodata strings.
   12: errno against the name. alias_read writes errno at 0x164b4, and the name is read again by
   alias_write (0x16530), remember (0x165c8, 0x1660c), reac_code_emit (0x164ec, 0x16638) and
   fprintf (0x16598, 0x165f8), while the Post's `str_arg` is over the entry memory.
   
   GAP 14 (a Theorem Labs lane): the refusal arm keeps the fake kernel. A NULL marks block returns before
   any call, but the write set names g_nl unconditionally, and mark_quietly's own
   `a0 = 0 -> nlk_at mem' kbs` has to survive the tail call at 0x15dfc.
   
   A NULL MARKS BLOCK OWNS NO BYTES (a Theorem Labs lane's gap 18, 2026-10-30): the write set's marks-block
   interval shrinks to nothing when a0 is NULL, the same rule as L7 for the reader buffers. The
   refusal returns at 0x16488 / 0x16490 / 0x1649c before any store outside the frame, and
   mark_quietly's mq_post_k needs every allocator-owned byte unchanged on that path, which an
   unguarded [0, 516) would not give.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem memfile_c printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require MemFile.
Local Open Scope Z_scope.

Definition REAC_SERVED_MARK : Z := 0x16bfc.
Lemma REAC_SERVED_MARK_is_entry : REAC_SERVED_MARK = P_reac_served_mark. Proof. reflexivity. Qed.

(* the most bytes one call puts on the stream (the plain twin`s MARK_LINE_MAX) *)
Definition MARK_LINE_MAX : Z := 400.

(* What the call needs of errno, of the name and of the marks block, shared with
   lib/U/Prog/mark_quietly_c.v, which tail-calls this function at the same sp: at `K`, with the
   FILE at `sink`. The same three helpers as the plain twin, plus this build`s alignment guards. *)
Definition mark_errno_ok (m : word -> option byte) (regs : bvmap 5 word) (K sink : Z) : Prop :=
  wr_at rsegs m (errno_at regs) 4
  /\ apart_frame regs K (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
  /\ apart (errno_at regs) 4 sink FILE_BLOCK /\ apart (errno_at regs) 4 A_GOT_GUARD 8
  /\ apart (errno_at regs) 4 A_G_SAY 8 /\ apart (errno_at regs) 4 A_G_SAID SAID_SIZE
  /\ IMG_LO <= errno_at regs /\ errno_at regs + 4 <= IMG_TOP
  /\ errno_at regs <> 0 /\ errno_at regs mod 4 = 0.

Definition mark_name_ok (m : word -> option byte) (regs : bvmap 5 word) (K sink : Z)
    (nm : option (list byte)) : Prop :=
  forall s, nm = Some s ->
    (length s <= 15)%nat
    /\ apart_frame regs K (arg regs 1) (Z.of_nat (length s) + 8)
    /\ apart_gnl (arg regs 1) (Z.of_nat (length s) + 8)
    /\ apart sink FILE_BLOCK (arg regs 1) (Z.of_nat (length s) + 8)
    /\ apart (errno_at regs) 4 (arg regs 1) (Z.of_nat (length s) + 8)
    /\ (exists slack, bytes_at rsegs m (arg regs 1 + Z.of_nat (length s) + 1) slack
          /\ Z.of_nat (length slack) = (- (arg regs 1 + Z.of_nat (length s) + 1)) mod 8)
    /\ (arg regs 0 <> 0 -> apart (arg regs 1) (Z.of_nat (length s) + 8) (arg regs 0) MK_SIZE).

(* GAP 11: every interface-table name string, apart from this frame, g_nl, errno, the FILE
   block and the marks block. Shared with mark_quietly_c.v, which tail-calls this function. *)
Definition mark_table_ok (m : word -> option byte) (regs : bvmap 5 word) (K sink : Z)
    (tab : list (list byte * Z)) : Prop :=
  forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
    u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
    let n := Z.of_nat (length n2) + 1 in
    apart_frame regs K p n /\ apart_gnl p n /\ apart (errno_at regs) 4 p n
    /\ apart sink FILE_BLOCK p n
    /\ (arg regs 0 <> 0 -> apart (arg regs 0) MK_SIZE p n).

Definition mark_block_ok (m : word -> option byte) (regs : bvmap 5 word) (K sink : Z) : Prop :=
  arg regs 0 <> 0 ->
    apart_frame regs K (arg regs 0) MK_SIZE /\ apart_gnl (arg regs 0) MK_SIZE
    /\ apart (errno_at regs) 4 (arg regs 0) MK_SIZE
    /\ apart sink FILE_BLOCK (arg regs 0) MK_SIZE
    /\ pf_img_free (arg regs 0) MK_SIZE
    /\ arg regs 0 mod 4 = 0
    /\ exists gbs, marks_at m (arg regs 0) gbs /\ marks_wf gbs.

(* the UBSan guards at 0x16c54 and 0x16cdc: `-rc` must not overflow int *)
Definition mark_rc_ok (m : word -> option byte) (regs : bvmap 5 word)
    (tab : list (list byte * Z)) (nm : option (list byte)) (kbs : list byte) : Prop :=
  forall gbs, marks_at m (arg regs 0) gbs ->
    m_rc (mark_lib tab nm (mk_names gbs) (nk_sent kbs) (nk_kstate kbs)) <> - 2 ^ 31.

Definition reac_served_mark_contract : Prop :=
  forall sink : Z,
  leaf_fp REAC_SERVED_MARK 17280
    (fun regs m => exists kbs tab nm k,
       nlk_at m kbs /\ frame_apart_gnl regs 17280 /\ nlk_wf kbs /\ nk_open kbs = 0
       /\ nk_opened kbs + 2 < 2 ^ 31 /\ nk_closed kbs + 2 < 2 ^ 31 /\ iftab_at m kbs tab
       /\ mark_errno_ok m regs 17280 sink /\ mark_table_ok m regs 17280 sink tab /\ policy_ro m /\ spZ regs mod 4 = 0
       /\ u64_at m A_G_SAY sink /\ sink <> 0
       /\ memfile_k m sink k /\ k + MARK_LINE_MAX <= MemFile.MF_BUFSIZ
       /\ sink + FILE_BLOCK <= spZ regs - 17280
       /\ str_arg m (arg regs 1) nm
       /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             apart_frame regs 17280 p (Z.of_nat (length n2) + 1))
       /\ mark_name_ok m regs 17280 sink nm
       /\ mark_block_ok m regs 17280 sink
       /\ (arg regs 0 <> 0 -> mark_rc_ok m regs tab nm kbs))
    (fun regs m => [(A_G_NL, A_G_NL + NK_N_SENT + 4);
                    (errno_at regs, errno_at regs + 4);
                    (arg regs 0, arg regs 0 + (if arg regs 0 =? 0 then 0 else MK_SIZE));
                    mf_block sink])
    (fun regs m regs' m' =>
       (forall k, memfile_k m sink k ->
          exists k', k <= k' <= k + MARK_LINE_MAX /\ memfile_k m' sink k')
       /\ (arg regs 0 = 0 -> getr regs' 10 = wz (- E_INVAL)
             /\ forall kbs, nlk_at m kbs -> nlk_at m' kbs)
       /\ (arg regs 0 <> 0 -> forall kbs tab nm gbs,
             nlk_at m kbs -> iftab_at m kbs tab -> str_arg m (arg regs 1) nm ->
             marks_at m (arg regs 0) gbs ->
             let M := mark_lib tab nm (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) in
             getr regs' 10 = wz (m_rc M)
             /\ (exists gbs', marks_at m' (arg regs 0) gbs' /\ marks_wf gbs'
                   /\ mk_names gbs' = m_marks M
                   /\ mk_n gbs' = Z.of_nat (length (m_marks M)))
             /\ (exists kbs', nlk_at m' kbs' /\ nlk_wf kbs'
                   /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
                   /\ nk_n_if kbs' = nk_n_if kbs /\ iftab_at m' kbs' tab
                   /\ nk_next kbs' = Z.of_nat (k_next (m_state M))
                   /\ nk_sent kbs' = m_reqs M /\ nk_n_sent kbs' = Z.of_nat (length (m_reqs M))
                   /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
                   /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
                   /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 2))).
