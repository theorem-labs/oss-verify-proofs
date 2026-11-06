(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v at bc49657c087a; module path, this image's values, LLVM_K from check_inject. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths and module names changed; 63 of its 79 lines of code are new or changed and 51 lines of the source are left out. *)
(* text_of (fuzz_link.c:126-136, with fuzz_u8, fuzz_u16, fuzz_take and fuzz_str of fuzz.h inlined),
   UBSAN build: a text from the table `texts`, or a heap copy of the input`s own bytes cut at their
   first NUL.

   The twin of lib/Prog/text_of_c.v, with its premises, the premises the UBSan guards below need,
   the premises a provable statement needs (listed after the guards), and ONE Post clause stronger
   than the plain twin (see the end). a0 = in (the input cursor: p at +0, n at +8), a1 = own (where
   the copy to free is stored); c0 and c1 are the p and n the cursor holds at entry. The selector
   byte decides: without bit 7 it answers one of the eleven `texts` entries and stores NULL in
   `*own`; with bit 7 it takes up to (fuzz_u16 mod 320) bytes of the input, cuts them at their first
   NUL and answers a fresh heap C string, which it also stores in `*own`. An empty cursor (c1 = 0)
   reads no byte and answers texts[0]. The abort at +0x208 (0x16240, reached from the `beqz a0` at
   0x161e0) is the harness`s own allocation failure; `room_slots b 320` rules it out.
   THE WEAKEST FORM THE CALLER NEEDS: the callers (op_write and op_decide, inlined into
   LLVMFuzzerTestOneInput) use the answer only as a C string and free `*own`. So the contract says
   the answer is a C string of at most 319 bytes, that `*own` is either 0 or that same address,
   and, when it allocated, that the block is fresh and accounted. It does NOT say which of the two
   the selector chose.
   K = 48 + ALLOC_STACK = 8240: its own frame of 48 (link/donors/premises-ubsan.txt) and the
   allocator`s ALLOC_STACK = 8192 (lib/Reusable/YO0d.v, re-exported by lib/U/Reusable/YO0d.v);
   memchr and memcpy use no stack (lib/U/Prog/memchr_c.v and memcpy_c.v keep sp and take no stack
   premise). The ubsan body calls exactly what the plain body calls (memchr, malloc, memcpy, abort):
   no call edge of the ubsan build only.
   UBSan guards (link/donors/ubsan-checks.tsv lines 268-277, link/ct/dis/ubsan/text_of.s); every
   guard branches to the `unimp` at 0x1623c (+0x204):
   - branch 0x16054 (fuzz.h:39, `andi a2, a0, 7` at +0x18, then bnez): traps unless the cursor is
     8-aligned for the load of in->n. ADDED: `bv_unsigned (getr regs 10) mod 8 = 0`.
   - branch 0x16078 (fuzz.h:42, the pointer-overflow test of `*in->p++` for the selector byte,
     `addi a2, a1, 1; bgeu a4, a2` with a4 = 1): traps when p + 1 is 0 or 1, that is p = 0 or
     p = 2^64 - 1; it runs only when c1 <> 0. ADDED: `bv_unsigned c0 + bv_unsigned c1 < 2 ^ 64` and
     `bv_unsigned c1 <> 0 -> 0 < bv_unsigned c0`.
   - branches 0x16084 (fuzz_link.c:129, the selector arm, `andi a3, s0, 7` at +0x44) and 0x160e8
     (fuzz_link.c:129, the empty-cursor arm, `andi a0, s0, 7` at +0xac): trap unless own is 8-aligned
     for `*own = NULL`. ADDED: `bv_unsigned (getr regs 11) mod 8 = 0`.
   - branch 0x160d8 (fuzz_link.c:131, `not a2, a0; bltu a2, a1`): traps when
     texts + 8 * (s mod 11) passes 2^64 - 1. ANSWERED BY A CONSTANT ADDRESS: texts is
     A_TEXTS = 0x21028 and the offset is at most 80.
   - branches 0x1611c and 0x1613c (fuzz.h:42, the two fuzz_u8 of fuzz_u16, `bgeu 1, p + 1` with
     p = c0 + 1 and p = c0 + 2): ANSWERED BY THE 0x16078 PREMISES: each runs only when the cursor
     still holds a byte, so p + 1 <= c0 + c1 < 2^64 and p > c0 >= 1. They read p and n back from
     the cursor AFTER the store `*own = NULL` (+0x54), so they also need own apart from the cursor
     (a provability premise below): with own = in that store would zero p and this guard would
     trap.
   - branches 0x1619c (fuzz.h:63, `in->p += n`, `add a2, s2, s1; bltu a2, s1`: p + n wraps) and
     0x161ac (fuzz.h:63, `snez a3, s1; seqz a4, a2; xor; beqz`: traps unless p and p + n are NULL
     together or non-NULL together): ANSWERED BY THE 0x16078 PREMISES: n is at most what the cursor
     holds, so p + n <= c0 + c1 < 2^64, and p >= c0 + 1 > 0.
   - branch 0x16200 (fuzz.h:95, `s[n] = 0`, `not a0, s3; bltu a0, s2`): traps when the fresh block
     s plus n (n <= 319) passes 2^64 - 1. ANSWERED BY THE ALLOCATOR CONTRACT: malloc_ret gives
     fresh_block s (n + 1), so s + n + 1 <= alloc_ceiling < 2^64.
   - the `unimp` at 0x16244 (+0x20c) follows the call to abort and is reached only through it (the
     `fallthrough` row, line 278).
   What a provable statement needs, not guards (the plain twin lacks them too; reported to the
   lane):
   - the input bytes: `exists inp, bytes_at rsegs mem c0 inp` with c1 bytes. The selector, the two
     fuzz_u16 bytes and the taken bytes are read from them, and they are memchr`s and memcpy`s
     bytes_at premise.
   - when c1 <> 0, the input lies inside one live user block. Then malloc keeps those bytes
     (call_post_k), the fresh block cannot overlap them (memcpy`s separation premise), and they lie
     below alloc_ceiling, so outside [sp - K, sp). The slot holds its input in exactly such a block
     (lib_pre_x) and the cursor never leaves it.
   - own apart from the cursor (see 0x1611c).
   - the cursor and own outside [sp - K, sp) (`apart_frame`): the prologue stores five registers at
     +0x04 to +0x14 before either is read, and `*own = NULL` into this frame would overwrite the
     saved ra.
   - the texts table holds the image`s bytes, `G_img_c B [(A_TEXTS, 8 * TEXTS_N)] mem`: texts lies in
     .data.rel.ro, inside the frame`s RELRO list (lib/U/FrameAPI.v frame_RELRO, 0x20fe8 + 296), so
     ro_agree does not give it, and the table arm answers texts[s mod 11], which the Post says is a
     C string. And the cursor and own are not over the table: both are written before the table is
     read.
   STRONGER POST THAN THE PLAIN TWIN: the Post also says the cursor afterwards is (c0 + adv,
   c1 - adv) for some 0 <= adv <= c1. The caller needs it: LLVMFuzzerTestOneInput reads the cursor
   again (the next fuzz_u8, guarded at 0x13c80 and 0x13ff4 in the ubsan build) and must know it
   still lies inside the input; the plain Post says nothing of the cursor although its write set
   names it.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc). This
   contract has the SR shape of the released allocator-facing contracts: the function reaches
   malloc, so it is stated over the frame`s allocator interface (lib/U/Contract.v) and not with the
   `leaf` shape of lib/U/Prog/link_mem.v.
   THE START STATE IS THE FP-AWARE ONE (a Theorem Labs lane, AMEND-slot item 6): `mkst` is written
   `@YK11.mkst fx` here, because this file imports lib/Prog/link_mem.v last and the bare name
   would otherwise resolve to lib/Lib/PropExec.v`s, whose FP file is empty and whose fcsr is 0.
   At every call site the FP file is whatever the printf layer left and the fcsr has only its
   rounding mode at 0, so the contract would not apply.
   
   THE CURSOR AND *own ARE NOT HEAP (LinkHelpers' walker HpTextOf, 2026-10-30): without
   `alloc_ceiling <= a0` and `alloc_ceiling <= a1` the Post is unprovable twice over. `sd a3, 0(a0)`
   at 0x15ad8 writes the advanced cursor on EVERY path with c1 <> 0, including the table arm where
   A' = A, so call_post_k's user-block conjunct is false if the cursor lies in a live block; and a
   cursor or *own in a free slot below alloc_ceiling is kept by no conjunct of malloc's own
   call_post_k, whose frame clause covers only `alloc_ceiling <= a` or `in_img`, so the Post's
   cursor cells need not survive `jal malloc` at 0x15bf4 and the fresh block may cover *own, which
   `sd s3, 0(s0)` at 0x15c1c then overwrites. Both callers pass slots of the slot's own frame
   (a0 = sp+0x40, a1 = sp+0x78 or sp+0x50, at 0x13a9c-0x13ab4 and 0x13fac-0x13fb4).
   *own IS NOT REQUIRED TO BE ZERO, same source: op_decide's `char *ok, *oa` are not initialised
   before the call, so the slot cannot supply it; the function stores 0 there itself before any
   read (`sd zero, 0(s0)`), so any word will do.
   
   AMEND-slot item 8 (a Theorem Labs lane's decide arm, 2026-10-30): the Post must say WHERE the answer
   lies, or a caller cannot show the two strings it then compares are readable and do not move.
   The table arm answers a `texts` entry, inside the read-only image; the copy arm answers the
   fresh block, and the string with its NUL fits inside it. `t` is therefore bound in the outer
   existential, so both arms can speak of it.
   
   THE ALLOCATOR IS ALREADY INITIALISED (LinkHelpers' walker HpTextOf, 2026-10-30): this function
   stores to the cursor (0x15ad8, 0x15adc, 0x15bcc, 0x15bd0) and to *own (0x15ae4) BEFORE its
   `jal malloc` at 0x15bf4, and both callers pass slots of their own frame, which lie above this
   function's sp. malloc's call_pre asks `st_init_done A = false -> auxv_pre ...`, and auxv_pre
   names words above sp (lib/Reusable/YO0d.v:70-77), so with the allocator not yet initialised
   those stores could change the auxv words and nothing would give malloc its premise. The slot
   calls calloc for the model and the marks block before any operation, malloc's Post gives
   `st_init_done A' = true`, and free keeps it. text_buf stores nothing above sp before its malloc
   and needs nothing. The released kb_pre_A (lib/KindBGlue.v:613) has the same side condition.
   
   AMEND-slot item 11 (a Theorem Labs lane, 2026-10-30): the allocating arm keeps every old user block,
   `forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')`, as Contract.malloc_ret
   gives it. call_post_k protects an old block's bytes only when the block is in both A and A', so
   without this the caller loses the model, marks, payload and FILE blocks across the call. True:
   the function allocates once and changes no other allocator state. The same arm also gives
   `st_init_done A' = true`, which malloc_ret states and call_post_k does not carry, and which
   every later call_pre_k and the slot's own post ask for.
   
   AMEND-slot item 12 (a Theorem Labs lane, 2026-10-30): the footprint is the block's real size `k`, not a
   flat 320. With `own + 320` the footprint could reach past the block, above alloc_ceiling or into
   image bytes for a block just below 0x10000, and the slot's step was unprovable. `k` is now bound
   in the outer existential so the footprint can name it; the table arm (own = 0) gives `k = 0`.
   
   AMEND-slot item 13 (a Theorem Labs lane, 2026-10-30): the table arm puts the string AND strlen's slack in
   the read-only segment, `s + |t| + 8 <= A_RO_END`. The first PT_LOAD ends at 0x11eb4 (ubsan
   0x11f54) and the next starts a page later, so a text ending in its last 3 bytes would leave the
   slack to the next 8-boundary in no segment. True with room: the last text ends at 0x10573
   (ubsan 0x10571), so s + |t| + 8 is at most 0x1057b. This is a Post fact, so the flat `+ 8`
   strengthens it for the caller; it is not the containment trap item 10 was, which was a Pre.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import Contract OutForm Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_spec link_mem.
Import ListNotations.
Local Open Scope Z_scope.

Definition TEXT_OF : Z := 0x16038.
Lemma TEXT_OF_is_entry : TEXT_OF = P_text_of. Proof. reflexivity. Qed.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition TEXT_OF_K : Z := 48 + ALLOC_STACK.

Definition text_of_contract : Prop :=
  forall L A regs mem md (b : sbound) (c0 c1 : word),
    segs = rsegs ->
    call_pre_k B MR TEXT_OF_K L A regs mem md -> ro_agree segs mem ->
    rw_cells rsegs mem (bv_unsigned (getr regs 10)) [C8 c0; C8 c1] ->
    (exists w, rw_cells rsegs mem (bv_unsigned (getr regs 11)) [C8 w]) ->
    bv_unsigned (getr regs 10) <> 0 -> bv_unsigned (getr regs 11) <> 0 ->
    @YM05.alloc_ceiling rc <= bv_unsigned (getr regs 10) ->
    @YM05.alloc_ceiling rc <= bv_unsigned (getr regs 11) ->
    res_ok_slots A b -> room_slots b 320 ->
    st_init_done A = true ->
    (* the UBSan guards (header): 0x16054; 0x16084 and 0x160e8; 0x16078 *)
    bv_unsigned (getr regs 10) mod 8 = 0 ->
    bv_unsigned (getr regs 11) mod 8 = 0 ->
    bv_unsigned c0 + bv_unsigned c1 < 2 ^ 64 ->
    (bv_unsigned c1 <> 0 -> 0 < bv_unsigned c0) ->
    (* what a provable statement needs (header) *)
    (exists inp, bytes_at rsegs mem (bv_unsigned c0) inp
                 /\ Z.of_nat (length inp) = bv_unsigned c1
                 /\ (bv_unsigned c0 + bv_unsigned c1 <= bv_unsigned (getr regs 10)
                     \/ bv_unsigned (getr regs 10) + 16 <= bv_unsigned c0)
                 /\ (bv_unsigned c0 + bv_unsigned c1 <= bv_unsigned (getr regs 11)
                     \/ bv_unsigned (getr regs 11) + 8 <= bv_unsigned c0)) ->
    (bv_unsigned c1 <> 0 ->
       exists q k, In (q, k) (user_blocks A) /\ ptr_addr L q <= bv_unsigned c0
                   /\ bv_unsigned c0 + bv_unsigned c1 <= ptr_addr L q + k) ->
    (bv_unsigned (getr regs 11) + 8 <= bv_unsigned (getr regs 10)
       \/ bv_unsigned (getr regs 10) + 16 <= bv_unsigned (getr regs 11)) ->
    apart_frame regs TEXT_OF_K (bv_unsigned (getr regs 10)) 16 ->
    apart_frame regs TEXT_OF_K (bv_unsigned (getr regs 11)) 8 ->
    G_img_c B [(A_TEXTS, 8 * TEXTS_N)] mem ->
    (bv_unsigned (getr regs 10) + 16 <= A_TEXTS
       \/ A_TEXTS + 8 * TEXTS_N <= bv_unsigned (getr regs 10)) ->
    (bv_unsigned (getr regs 11) + 8 <= A_TEXTS
       \/ A_TEXTS + 8 * TEXTS_N <= bv_unsigned (getr regs 11)) ->
    SR segs (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 TEXT_OF) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (own s : Z) (t : list byte) (k : Z),
         c' = mkCfg (@YK11.mkst fx regs' (getr regs 1) mem' (seg_rom segs)) md'
         /\ call_post_k B MR TEXT_OF_K L A regs mem md
              (fun a => (own <= a < own + k)
                        \/ (bv_unsigned (getr regs 10) <= a < bv_unsigned (getr regs 10) + 16)
                        \/ (bv_unsigned (getr regs 11) <= a < bv_unsigned (getr regs 11) + 8))
              L' A' regs' mem' md'
         /\ ro_agree segs mem'
         /\ getr regs' 10 = Z_to_bv 64 s /\ s <> 0
         /\ cstr_at mem' s t /\ Z.of_nat (length t) < 320
         /\ bytes_at rsegs mem' (bv_unsigned (getr regs 11)) (le8 (Z_to_bv 64 own))
         /\ (exists adv, 0 <= adv <= bv_unsigned c1
               /\ rw_cells rsegs mem' (bv_unsigned (getr regs 10))
                    [C8 (Z_to_bv 64 (bv_unsigned c0 + adv)); C8 (Z_to_bv 64 (bv_unsigned c1 - adv))])
         /\ (own = 0 -> k = 0 /\ L' = L /\ A' = A /\ res_ok_slots A' b
               /\ A_RO_LO <= s /\ s + Z.of_nat (length t) + 8 <= A_RO_END)
         /\ (own <> 0 ->
               own = s
               /\ 1 <= k <= 320 /\ fresh_block B own k
               /\ Z.of_nat (length t) + 1 <= k
               /\ (exists b1 b2, blocks L' A' = b1 ++ (own, k) :: b2 /\ blocks L A = b1 ++ b2)
               /\ res_ok_slots A' (sb_malloc b k)
               /\ (forall q n, In (q, n) (user_blocks A) -> In (q, n) (user_blocks A'))
               /\ st_init_done A' = true)).

End K.
