(* talk (fuzz_link.c:333-384), UBSAN build: the harness model of one request and its reply.

   The twin of lib/Prog/talk_c.v, with its premises, its Wr set and its Post, the one premise a
   UBSan guard needs, the premises the calls of the ubsan build need, the separation premises the
   Post needs to be true, and ONE Post clause that differs from the plain twin (see the end).
   a0 = m, a1 = r, a2 = len, a3 = kind, a4 = kind_n, a5 = alias, a6 = alias_n.
   It answers the code the reply spells, and fills the kind and the alias from the first
   RTM_NEWLINK: link_spec`s `talk_core`, with `norm_rc` applied to the code. talk reads the chunk
   queue and the end errno from g_nl and keeps its OWN socket errno, send errno and cursor in the
   model block; it writes NO byte of g_nl. The two text buffers are touched only when the reply
   really carries that attribute: when it does not, talk leaves them as the caller set them.
   In the ubsan build talk CALLS take_text (0x15e18 for the alias, 0x15ea0 for the kind;
   lib/U/Prog/take_text_c.v) where the plain build inlines it, and calls memcpy for `owe` (0x15c10).
   K = 144: the own frame of 112 (link/donors/premises-ubsan.txt, `addi sp, sp, -0x70` at +0x00)
   plus take_text`s 32; memcpy uses no stack (lib/U/Prog/memcpy_c.v keeps sp). The brief gave 112:
   link/ct/stack.py takes its call edges from link/functions.tsv, whose callee column is the PLAIN
   build`s (talk: memcpy only), so it misses the two ubsan calls to take_text. With K = 112 the push
   take_text makes into [sp-144, sp-112) would lie outside the `munch` window, and the contract
   would be false. The prologue is at +0x00, before every test, so every returning path writes the
   frame.
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/talk.s); every guard branches to
   the `unimp` at 0x15f98:
   - branch 0x15b88 (fuzz_link.c:337, `andi a0, a0, 7; bnez`): traps unless `m` is 8-aligned, at
     the first read of m->socket_errno. ADDED: `arg regs 0 mod 8 = 0`.
   - branch 0x15ba8 (fuzz_link.c:340) and branch 0x15bc4 (fuzz_link.c:345), each the `j` after
     `neg; negw; beq`: `-e` overflows int when e = INT_MIN. ANSWERED BY model_wf: 0 <= socket_errno
     < 2^31 and 0 <= send_errno < 2^31.
   - branch 0x15bf4 (fuzz_link.c:300, `bgeu a0, a2` with a2 = 17): index guard on
     m->req[m->n_req]; traps when n_req is negative. ANSWERED BY model_wf (0 <= n_req <= 16); the
     `n_req < NL_SENT_MAX` test (`blt` with 15 at 0x15bec) runs before it.
   - branch 0x15c1c (fuzz_link.c:301, `addiw a1, a0, 1; blt a1, a0`): m->n_req++ overflows int;
     branch 0x15c28 (fuzz_link.c:301, `bltu a2, a0` with a2 = 15): index guard on
     m->req_len[n_req]. ANSWERED BY model_wf and the `n_req < NL_SENT_MAX` test: 0 <= n_req <= 15
     there. The re-read of n_req follows the memcpy, which writes only m->req[n_req] (len <= 512),
     below the offset 8336 of n_req.
   - branch 0x15c04 (fuzz_link.c:300, `not; bltu`): m + 12 + 512 n_req passes 2^64 - 1; branch
     0x15c40 (fuzz_link.c:301, `not; bltu`): m + 8208 + 8 n_req passes 2^64 - 1. ANSWERED BY
     model_at: its bytes_at gives m + MD_SIZE <= 2^64, and both sums stay below m + 8336 for
     n_req <= 15.
   - branch 0x15c94 (fuzz_link.c:0, `bgeu t3, a4` with a4 = 65) and branch 0x15ca0 (fuzz_link.c:0,
     `beq t3, a6` with a6 = 64): index guards on g_nl.chunk[c] and g_nl.chunk_len[c], c = m->next.
     ANSWERED BY model_wf (0 <= next) and nlk_wf (n_chunks <= NL_CHUNKS = 64): the loop body runs
     only while c < n_chunks (the signed `bge` at 0x15c68 and `blt` at 0x15cc0).
   - branch 0x15c9c (fuzz_link.c:352) and branch 0x15ca8 (fuzz_link.c:0), `not; bltu`: g_nl + 4096 c
     and g_nl + 0x40000 + 8 c pass 2^64 - 1. ANSWERED BY THE CONSTANT ADDRESS: g_nl = 0x323c0, far
     below 2^64, and c <= 64; they cannot be taken.
   - the walk over chunk c, b = g_nl + 4096 c. Every offset it forms (off; a = off + 32; i = a + 4;
     and each step by NL_ALIGN) stays in [0, 4096]: off + left, a + al and i + il never grow and
     start at most at chunk_len[c] <= NL_CHUNK_MAX (nlk_wf), every read happens only while
     left >= 16 (a message) or the region left holds at least 4 bytes (an attribute), and every
     length is checked against what is left before it is stepped over. So:
     - branch 0x15cd4, 0x15da8 and 0x15e3c (netlink.h:185 and :204, `beqz`): b + off, b + a, b + i
       is NULL; branch 0x15ce8, 0x15dbc and 0x15e50 (the same lines, `sltu; slti; xor`): the same
       sums wrap; branch 0x15d1c (netlink.h:0, `bltu` with -5): b + off + 4; branch 0x15ddc and
       0x15e6c (netlink.h:207, `bltu` with -3): b + a + 2 and b + i + 2; branch 0x15e04
       (fuzz_link.c:370) and 0x15e8c (fuzz_link.c:375), `bltu` with -5: b + a + 4 and b + i + 4;
       branch 0x15f20 (fuzz_link.c:360, `bltu` with -17): b + off + 16 passes 2^64 - 1.
       ANSWERED BY THE CONSTANT ADDRESS and the bound above: every sum is inside g_nl.
     - branch 0x15d50 (netlink.h:194), branch 0x15ebc and 0x15ee4 (netlink.h:213), `slt; slti;
       bne`: the step `*off += NL_ALIGN(len)` overflows long; branch 0x15ef4 (netlink.h:214, `sgtz;
       slt; bne`): the step `*left -= (long)NL_ALIGN(len)` overflows long; branch 0x15d7c and
       0x15d84 (fuzz_link.c:367, `blt`): off + NL_HDR and then + IFI_LEN overflow long; branch
       0x15e28 (fuzz_link.c:372, `blt`): a + RTA_HDR overflows long. ANSWERED BY nlk_wf: the
       offsets and the lengths left are at most 4096, and each step is NL_ALIGN of a length at
       most 4096.
   - branch 0x15d74 (fuzz_link.c:350, the `j` after `neg; negw; beq`): `-g_nl.end_errno` overflows
     int. ANSWERED BY nlk_wf: 0 <= end_errno < 2^31.
   Premises for the calls of the ubsan build, not guards:
   - for callee take_text`s U contract, whose payload and buffer must not overlap: the payload lies
     in chunk c of g_nl, so `arg regs 3 <> 0 -> apart_gnl (arg regs 3) (arg regs 4)` and the same
     for the alias buffer (args 5 and 6). They also keep the chunk bytes the walk reads unchanged by
     the text writes. take_text`s other premises follow from the plain ones with K = 144: its frame
     [sp-144, sp-112) is inside `frame_apart_gnl regs 144` and below every `apart_frame regs 144`.
   - for callee memcpy`s contract (lib/U/Prog/memcpy_c.v: source and destination do not overlap):
     the request is outside the model block, `arg regs 1 + arg regs 2 <= arg regs 0` or
     `arg regs 0 + MD_SIZE <= arg regs 1`.
   Premises the Post needs to be TRUE, missing in the plain twin as well:
   - each text buffer is outside the model block: the text writes come after the model writes
     (`owe` and the cursor), and an overlap would change the n_req, req and next the Post states.
   - the two text buffers do not overlap: the Post states a C string in each.
   WEAKER POST THAN THE PLAIN TWIN: the plain twin says the send errno of the new model block is 0.
   That is false when both errnos are non-zero, which kernel makes when its flags byte is 3
   (fuzz_link.c:262-263): talk then answers -socket_errno and clears ONLY socket_errno
   (`sw zero, 0(s4)` at 0x15ba0), and the send errno stays for the next call. This twin says it is
   `k_send (talk_after K0)`, link_spec`s own value, which is 0 on every other path. The plain twin
   has the same defect.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function`s own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. 
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition TALK : Z := 0x15b48.
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
       /\ (arg regs 5 <> 0 -> apart_frame regs 144 (arg regs 5) (arg regs 6))
       /\ arg regs 0 mod 8 = 0
       /\ (arg regs 3 <> 0 -> apart_gnl (arg regs 3) (arg regs 4))
       /\ (arg regs 5 <> 0 -> apart_gnl (arg regs 5) (arg regs 6))
       /\ (arg regs 1 + arg regs 2 <= arg regs 0 \/ arg regs 0 + MD_SIZE <= arg regs 1)
       /\ (arg regs 3 <> 0 ->
             arg regs 3 + arg regs 4 <= arg regs 0 \/ arg regs 0 + MD_SIZE <= arg regs 3)
       /\ (arg regs 5 <> 0 ->
             arg regs 5 + arg regs 6 <= arg regs 0 \/ arg regs 0 + MD_SIZE <= arg regs 5)
       /\ (arg regs 3 <> 0 -> arg regs 5 <> 0 ->
             arg regs 3 + arg regs 4 <= arg regs 5 \/ arg regs 5 + arg regs 6 <= arg regs 3))
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
             /\ md_socket_errno mbs' = 0 /\ md_send_errno mbs' = k_send (talk_after K0)
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
