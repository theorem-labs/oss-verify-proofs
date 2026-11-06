(* reac_served_mark (reac_served_mark.c:48-92): the marking policy for one interface.

   a0 = m, a1 = ifname. It refuses a NULL marks block, a NULL name and an empty name with -EINVAL;
   otherwise it reads the interface`s kind and alias into two buffers of its own frame
   (char kind[32], char alias[256]), takes the verdict of reac_served_decide, writes the served
   alias and remembers the name when the verdict is MARK, remembers it when the verdict is OURS
   and the alias is exactly `reac-pw:served`, and answers the verdict. On a failed read or write
   it answers that code instead. link_spec`s `mark_lib` is the whole of it, and model_mark
   (fuzz_link.c:442-460) is `mark_model`, the same function up to `norm_rc`
   (link_spec mark_agree): that is what makes check_mark and check_marks never fire.
   THE FILE (link/ct/AMEND-mark.md gap 2): the stream is link's one memory FILE, stated with
   lib/Prog/memfile_c.v's `memfile_k m f k`, the predicate fprintf, vfprintf and reac_code_emit
   state. At most one line goes out per call, at most 400 bytes (the longest, 0x1049d with an
   ifname of at most 15 bytes and an alias of at most 255, is 387), so the Pre asks k + 400 <= 1024
   and the Post gives k <= k' <= k + 400. The FILE block lies below every callee window (fprintf's
   and vfprintf's `f + MF_BLOCK <= sp - K`), apart from errno, the marks block and the name.
   Gaps 3a, 6 and 7 of the same file: errno apart from the marks block, the FILE block and the
   GOT slot; the name at most 15 bytes (every caller passes name_of's answer: a g_names entry or an
   `odd` entry, at most 11) with the 7 slack bytes snprintf's `%s` reads, apart from the marks
   block; the marks block outside the image's reserved segments (snprintf's pf_img_free).
   Gap 8: the Post bounds the open counter, at most two exchanges per call.
   This contract uses leaf_fp because fprintf and vfprintf run the printf layer.
   K = 17248 (320 of its own, then reac_link_alias_write`s 16928).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). 
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

Definition REAC_SERVED_MARK : Z := 0x16470.
Lemma REAC_SERVED_MARK_is_entry : REAC_SERVED_MARK = P_reac_served_mark. Proof. reflexivity. Qed.

(* the most bytes one call puts on the stream *)
Definition MARK_LINE_MAX : Z := 400.

(* what the call needs of the name and of the marks block, shared with mark_quietly_c.v, which
   tail-calls this function at the same sp: at `K`, the FILE at `sink` *)
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
    /\ exists gbs, marks_at m (arg regs 0) gbs /\ marks_wf gbs.

Definition mark_errno_ok (m : word -> option byte) (regs : bvmap 5 word) (K sink : Z) : Prop :=
  wr_at rsegs m (errno_at regs) 4
  /\ apart_frame regs K (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
  /\ apart (errno_at regs) 4 sink FILE_BLOCK /\ apart (errno_at regs) 4 A_GOT_GUARD 8
  /\ apart (errno_at regs) 4 A_G_SAY 8 /\ apart (errno_at regs) 4 A_G_SAID SAID_SIZE
  /\ IMG_LO <= errno_at regs /\ errno_at regs + 4 <= IMG_TOP.

Definition reac_served_mark_contract : Prop :=
  forall sink : Z,
  leaf_fp REAC_SERVED_MARK 17248
    (fun regs m => exists kbs tab nm k,
       nlk_at m kbs /\ frame_apart_gnl regs 17248 /\ nlk_wf kbs /\ nk_open kbs = 0
       /\ nk_opened kbs + 2 < 2 ^ 31 /\ nk_closed kbs + 2 < 2 ^ 31 /\ iftab_at m kbs tab
       /\ mark_errno_ok m regs 17248 sink /\ mark_table_ok m regs 17248 sink tab /\ policy_ro m
       /\ u64_at m A_G_SAY sink /\ sink <> 0
       /\ memfile_k m sink k /\ k + MARK_LINE_MAX <= MemFile.MF_BUFSIZ
       /\ sink + FILE_BLOCK <= spZ regs - 17248
       /\ str_arg m (arg regs 1) nm /\ mark_name_ok m regs 17248 sink nm
       /\ mark_block_ok m regs 17248 sink)
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
