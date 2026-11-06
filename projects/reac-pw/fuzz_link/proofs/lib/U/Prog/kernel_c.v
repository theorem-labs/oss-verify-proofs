(* kernel (fuzz_link.c:256-282), UBSAN build: the fake kernel of one operation, as the input spells it.

   The twin of lib/Prog/kernel_c.v: the same leaf shape, the same Wr set, the plain premises and
   the plain Post, with the premises the UBSan guards below need, the premises the callees and a
   provable statement need, and two Post clauses more than the plain twin (see the end). a0 = in,
   the input cursor: p at +0 and n at +8, two 8-byte fields, here wp and wn at entry. kernel takes
   the two failure flags and three errno bytes, empties the chunk queue and fills it with at most
   three chunks. The ubsan build inlines msg_build, attr_text, nl_error, nl_put, nl_set16,
   nl_set32, nl_queue and nl_queue_raw, and CALLS nl_begin (0x1472c, 0x14760, 0x14d38, 0x14e14,
   0x14e8c, 0x15008), nl_attr_put (0x149b4, 0x14c18), memset, memcpy and strlen
   (link/donors/premises-ubsan.txt).
   THE WEAKEST FORM THE CALLER NEEDS, as in the plain twin: the Post does not say WHICH reply bytes
   msg_build makes, only that the queue is replaced by at most three chunks of at most 4096 bytes,
   the cursor of the queue is 0, the three errnos come from nl_errno`s table, and nothing else of
   the fake kernel moves.
   K = 4400: its own frame of 4368 (addi sp, sp, -0x7f0 at +0x0, then -0x800 at +0x38 and -0x120
   at +0x3c), plus the 32 of nl_attr_put, which it calls with jal while that frame is live;
   nl_begin, memset, memcpy and strlen use no stack (link/ct/stack.json, frame column). The 4368
   that link/ct/stack.json gives as the ubsan depth of kernel came from the plain callee table:
   link/ct/stack.py takes its call edges from link/functions.tsv, whose kernel row lists the plain
   callees (attr_text, memcpy, memset, nl_error), so the ubsan-only calls to nl_begin and
   nl_attr_put are not counted there.
   UBSan guards (link/donors/ubsan-checks.tsv lines 128-217, link/ct/dis/ubsan/kernel.s); every
   guard branches to the `unimp` at 0x15368, 90 branches:
   - branch 0x1444c (fuzz.h:39, `andi a0, a0, 7` then bnez, before the first load of in->n):
     traps unless `in` is 8-aligned. ADDED: `arg regs 0 mod 8 = 0`.
   - branches 0x14474, 0x14494, 0x1450c, 0x145ac, 0x14658, 0x1468c, 0x146f4, 0x147c4, 0x14804,
     0x14d64, 0x151f0, 0x15214 (fuzz.h:42, `return *in->p++`, `bgeu 1, p + 1`): trap when the
     cursor p is 0 or p + 1 wraps. Each runs only when in->n is not 0, kernel reads the bytes at
     wp, wp + 1, ... in order, and in->p + in->n = wp + wn holds all the way through, so the read
     at p = wp + j has j < wn. ADDED: `wn <> 0 -> 0 < wp`, `wn <> 0 -> wp + wn < 2 ^ 64`.
   - branch 0x15268 (fuzz.h:63, `in->p += n` of fuzz_take in nl_queue_raw, `not a0, s2` then
     `bltu a0, s3`): traps when p + n wraps, n = min(want, in->n). ANSWERED BY the premise added
     just above: p + n <= wp + wn < 2 ^ 64.
   - branches 0x144d4, 0x14548 (netlink.h:160, `e[b % 6]` of nl_errno, `not` then `bltu`): trap
     when nl_errno.e + 4 * (b mod 6) wraps. ANSWERED BY A CONSTANT ADDRESS: nl_errno.e = 0x106e4,
     offset at most 20.
   - branch 0x14844 (fuzz_link.c:186, `texts[(a >> 3) % 11]`, `not` then `bltu`): traps when
     A_TEXTS + 8 * index wraps. ANSWERED BY A CONSTANT ADDRESS: A_TEXTS = 0x21028, offset at most 80.
   - branch 0x14d88 (fuzz_link.c:227, `codes[c % 4]`, `not` then `bltu`): traps when
     msg_build.codes + 4 * (c mod 4) wraps. ANSWERED BY A CONSTANT ADDRESS: msg_build.codes =
     0x106fc, offset at most 12.
   - 49 branches on the stack writer w, netlink.h:232 `memcpy(w->b + w->n, p, n)` of every inlined
     nl_put and nl_pad (0x14b2c and 0x14b30 carry netlink.h:0): 0x14784, 0x14788, 0x1489c, 0x148a0,
     0x14918, 0x1491c, 0x14944, 0x14948, 0x14970, 0x14974, 0x149cc, 0x149d0, 0x14a20, 0x14a24,
     0x14a58, 0x14a5c, 0x14aac, 0x14ab0, 0x14ad8, 0x14adc, 0x14b2c, 0x14b30, 0x14b54, 0x14b58,
     0x14b80, 0x14b84, 0x14bd4, 0x14bd8, 0x14cd0, 0x14cd4, 0x14ce4, 0x14da8, 0x14dac, 0x14de0,
     0x14de4, 0x14e2c, 0x14e30, 0x14ea8, 0x14eac, 0x14ee0, 0x14ee4, 0x14f54, 0x14f58, 0x14f84,
     0x14f88, 0x15068, 0x1506c, 0x150fc, 0x15100. Each pair is `bgeu n, s6` with s6 = 0x1001
     (traps when w->n >= 4097) and `bltu s8, n` with s8 = ~(sp + 0x80) (traps when w->b + w->n
     wraps); 0x14ce4 is a lone wrap test. ANSWERED BY A PROGRAM FACT AND THE SHAPE: w is the local
     of kernel at sp + 0x80 of its own frame, memset to 0 before each use (0x14678, 0x1513c,
     0x151dc); every inlined nl_put tests the fit before it adds, and the U Posts of nl_begin and
     nl_attr_put keep nlw_wf, so w->n <= 4096; and w->b + 4096 < spZ regs < 2 ^ 63 by `leaf`.
   - 13 branches of nl_set16 and nl_set32, on `w->b + at` of nl_nest_end and nl_end:
     netlink.h:256 0x14c28, 0x14c2c; netlink.h:262 0x14c68, 0x14c6c, 0x14d00, 0x14d04, 0x14edc,
     0x14f0c, 0x14f10, 0x14fb4, 0x14fb8, 0x150a0, 0x150a4. `bgeu at, s6` traps when at >= 4097
     (0x14edc is the `j` that the inverted test `bltu at, s6` at 0x14ed8 falls into), `bltu s8, at`
     traps when w->b + at wraps. ANSWERED BY A PROGRAM FACT AND THE SHAPE: `at` is the w->n that
     the inlined nl_nest read, or the answer of nl_begin, whose U Post says it is nw_n bs with
     nlw_wf bs; so at <= 4096, and the sum is bounded as in the group above.
   - 10 branches on the queue, netlink.h:322 `g_nl.chunk[g_nl.n_chunks]` and netlink.h:323
     `g_nl.chunk_len[g_nl.n_chunks++]`, once for nl_queue (0x15160, 0x1516c, 0x1518c, 0x15198,
     0x151a4) and once for nl_queue_raw (0x152c4, 0x152d0, 0x152f0, 0x152fc, 0x15308): 0x15160 and
     0x152c4 `bgeu n_chunks, 65` after the signed skip of n_chunks > 63 (trap when n_chunks < 0);
     0x1516c and 0x152d0, g_nl + 4096 * n_chunks wraps; 0x1518c and 0x152f0, n_chunks + 1 overflows
     the int; 0x15198 and 0x152fc, n_chunks > 63 (outside chunk_len[64]); 0x151a4 and 0x15308,
     g_nl + 0x40000 + 8 * n_chunks wraps. ANSWERED BY A PROGRAM FACT AND A CONSTANT ADDRESS: kernel
     stores 0 into n_chunks and next (`sd zero, 0x200(a2)` at 0x14580) before the loop, the loop
     runs at most 3 times (fuzz_u8 % 4) and queues at most one chunk per pass, and nothing else
     writes n_chunks (the memcpy into chunk[k], k <= 2, ends below NK_CHUNK_LEN, and the frame is
     apart from g_nl), so n_chunks is 0, 1 or 2 at each of these tests; g_nl = 0x323c0.
   Premises that are not guard premises:
   - FOR THE U CONTRACTS OF CALLEES nl_begin AND nl_attr_put: `spZ regs mod 8 = 0`. Both test
     that w = spZ regs - 4368 + 0x80 is 8-aligned (their guards 0x1580c and 0x159cc), and `leaf`
     says nothing about the alignment of sp.
   - FOR THE U CONTRACT OF CALLEE nl_attr_put AND FOR strlen (lib/U/Prog/strlen_c.v): the eleven
     `texts` entries each point at a C string shorter than 4096 bytes (nl_attr_put asks
     n + 4096 < 2 ^ 64 for n = strlen + 0 or 1), readable together with the slack the word reads
     of strlen need; and long_alias (case 1 of msg_build: memset of 300 bytes, then strlen, then
     nl_attr_put of 301 bytes) is writable, its byte 300 is a NUL (no code writes it), and the 3
     bytes after it, up to g_sink at 0x74d68, are readable: the slack of strlen,
     (-(0x74c38 + 301)) mod 8 = 3. The frame and the cursor are apart from those 304 bytes.
   - FOR A PROVABLE STATEMENT: the wn input bytes at wp are readable (kernel loads them, and
     nl_queue_raw hands them to memcpy); every region kernel only reads (the input, the texts
     table, the texts strings, and the interface names iftab_at points at) lies apart from all it
     writes: its frame, g_nl, long_alias with its 3 slack bytes, and the cursor (`kernel_apart`).
     The clause on the interface names is what makes the plain iftab clause of the Post true; the
     separation of the strings from the frame is also the separation premise of nl_attr_put.
   THE PLAIN TWIN LACKS ALL THREE GROUPS ABOVE (lib/Prog/kernel_c.v has none of them), and its
   iftab clause and its loads of the input have no premise there.
   STRONGER POST THAN THE PLAIN TWIN, two clauses, so that a caller can meet the premises above
   again for its next call (and answer the fuzz.h:42 guards of its own reads after kernel): the
   cursor advanced by some adv, 0 <= adv <= wn, over the same input (the form lib/U/Prog/text_of_c.v
   uses), and long_alias is still writable with a NUL at byte 300.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function`s own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. 
   A TEXTS ENTRY IS NOT NULL (a Theorem Labs lane, 2026-10-30): the texts clause gives each entry `p <> 0`.
   attr_text's Pre asks `arg regs 2 <> 0`, kernel passes texts[(a >> 3) mod 11] there (+0x590,
   +0x790), and the table is in the writable segment, so the image alone does not fix p. Every
   entry the harness has is the address of a .rodata string, so the caller can supply it.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition KERNEL : Z := 0x14404.
Lemma KERNEL_is_entry : KERNEL = P_kernel. Proof. reflexivity. Qed.

(* the n bytes at `a` are apart from all kernel writes: its frame of K = 4400, g_nl, long_alias
   with the 3 slack bytes strlen reads after it, and the cursor at a0 *)
Definition kernel_apart (regs : bvmap 5 word) (a n : Z) : Prop :=
  apart_frame regs 4400 a n /\ apart_gnl a n
  /\ (a + n <= A_LONG_ALIAS \/ A_LONG_ALIAS + LONG_ALIAS_SIZE + 3 <= a)
  /\ (a + n <= arg regs 0 \/ arg regs 0 + 16 <= a).

Definition kernel_contract : Prop :=
  leaf KERNEL 4400
    (fun regs m => exists kbs (wp wn : word),
       nlk_at m kbs /\ frame_apart_gnl regs 4400 /\ nlk_wf kbs
       /\ rw_cells rsegs m (arg regs 0) [C8 wp; C8 wn]
       /\ apart_gnl (arg regs 0) 16 /\ apart_frame regs 4400 (arg regs 0) 16
       /\ arg regs 0 mod 8 = 0
       /\ (bv_unsigned wn <> 0 ->
             0 < bv_unsigned wp /\ bv_unsigned wp + bv_unsigned wn < 2 ^ 64
             /\ (exists ib, bytes_at rsegs m (bv_unsigned wp) ib
                            /\ Z.of_nat (length ib) = bv_unsigned wn)
             /\ kernel_apart regs (bv_unsigned wp) (bv_unsigned wn))
       /\ spZ regs mod 8 = 0
       /\ kernel_apart regs A_TEXTS (8 * TEXTS_N)
       /\ (forall i, 0 <= i < TEXTS_N -> exists p s slack,
             u64_at m (A_TEXTS + 8 * i) p /\ p <> 0
             /\ bytes_at rsegs m p (s ++ zb 0 :: slack) /\ ~ In (zb 0) s
             /\ (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
             /\ Z.of_nat (length s) < NL_CHUNK_MAX
             /\ kernel_apart regs p (Z.of_nat (length s) + 1 + Z.of_nat (length slack)))
       /\ (exists la sl,
             rw_cells rsegs m A_LONG_ALIAS [CB (Z.to_nat 300) la; C1 (zb 0)]
             /\ bytes_at rsegs m (A_LONG_ALIAS + LONG_ALIAS_SIZE) sl /\ length sl = 3%nat)
       /\ apart_frame regs 4400 A_LONG_ALIAS (LONG_ALIAS_SIZE + 3)
       /\ (arg regs 0 + 16 <= A_LONG_ALIAS \/ A_LONG_ALIAS + LONG_ALIAS_SIZE + 3 <= arg regs 0)
       /\ (forall tab i nm ix p, iftab_at m kbs tab -> nth_error tab i = Some (nm, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             kernel_apart regs p (Z.of_nat (length nm) + 1)))
    (fun regs m => [(A_G_NL + NK_CHUNK, A_G_NL + NK_OPEN);
                    (A_LONG_ALIAS, A_LONG_ALIAS + LONG_ALIAS_SIZE);
                    (arg regs 0, arg regs 0 + 16)])
    (fun regs m regs' m' => forall kbs, nlk_at m kbs ->
       exists kbs', nlk_at m' kbs' /\ nlk_wf kbs'
       /\ nk_next kbs' = 0 /\ 0 <= nk_n_chunks kbs' <= 3
       /\ In (nk_end_errno kbs') nl_errno_tab
       /\ (nk_socket_errno kbs' = 0 \/ In (nk_socket_errno kbs') nl_errno_tab)
       /\ (nk_send_errno kbs' = 0 \/ In (nk_send_errno kbs') nl_errno_tab)
       /\ nk_open kbs' = nk_open kbs /\ nk_opened kbs' = nk_opened kbs
       /\ nk_closed kbs' = nk_closed kbs /\ nk_misuse kbs' = nk_misuse kbs
       /\ nk_n_sent kbs' = nk_n_sent kbs /\ nk_sent kbs' = nk_sent kbs
       /\ nk_n_if kbs' = nk_n_if kbs
       /\ (forall tab, iftab_at m kbs tab -> iftab_at m' kbs' tab)
       /\ (forall wp wn : word, rw_cells rsegs m (arg regs 0) [C8 wp; C8 wn] ->
             exists adv, 0 <= adv <= bv_unsigned wn
             /\ rw_cells rsegs m' (arg regs 0)
                  [C8 (Z_to_bv 64 (bv_unsigned wp + adv)); C8 (Z_to_bv 64 (bv_unsigned wn - adv))])
       /\ (exists la, rw_cells rsegs m' A_LONG_ALIAS [CB (Z.to_nat 300) la; C1 (zb 0)])).
