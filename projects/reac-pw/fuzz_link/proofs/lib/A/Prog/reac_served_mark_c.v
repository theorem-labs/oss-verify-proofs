(* reac_served_mark (reac_served_mark.c:48-92) on image A (fuzz_link.asan 0x895a8, 1596 bytes; listing
   (internal path) (internal record, sha256 5943815fc488)): the marking policy for one
   interface. a0 = m (the marks block, which may be NULL), a1 = ifname. The plain contract is
   lib/Prog/reac_served_mark_c.v; this file states the SAME link_spec result (`mark_lib`) in link_amem.v's
   `aleaf_fx` form (the read-set shape for a function that reaches the printf family: rounding mode 0 at entry,
   a Post at SOME fx' related to the entry's by BoxBase.v `fxr`, and a Pre that also sees the call's block list).

   The image-A code, in order:
     +0x00..+0x38  push a 128-byte frame; sd zero, 0(sp); save ra, s0..s10; s0 := sp + 0x80
     +0x3c  andi sp, sp, -0x20                                  (realignment: up to 16 more bytes of window)
     +0x44..+0x5c  s4 := a1 (ifname); s10 := the shadow base (.got 0xa19d0 -> 0xaa438 -> base);
                   a2 := the side-stack switch cell (.got 0xa1a28 -> 0xaa440)
     +0x60..+0x6c  s6 := a0 (the marks block); beqz a2 -> the real-stack arm
     +0x68..+0x70  a0 := 0x1a0; jal frame_alloc_3 (0x3dc18); s3 := a0, s9 := s3   (the 416-byte side frame:
                   kind[32] at s9 + 0x20, alias[256] at s9 + 0x60)
     +0x84..+0x9c  the real-stack arm (not taken under `aside_room`, link-a/form/FORM.md (internal record, sha256 13aeff774164) section 4.2)
     +0xa4..+0x1ac the frame's header words and the shadow bytes of its redzones (meta bytes -0xf, -0xe, -0xd, -8)
     +0x1b0  s5 := -0x16 (- E_INVAL, the refusal answer)
     +0x1b4  beqz s6 -> +0x360  (NULL marks block: refuse)
     +0x1b8  beqz s4 -> +0x360  (NULL name: refuse)
     +0x1bc..+0x1c8, +0x5fc..+0x604  the instrumented check of the 1-byte load of ifname[0]: shadow byte s of s4;
                   s = 0 passes; else (s4 & 7) < s passes; else errpath_load1 (0x5a31c)
     +0x1cc..+0x1d0  lbu a0, 0(s4); beqz -> +0x360   (empty name: refuse)
     +0x1d4..+0x24c s8 := s9 + 0x20 (kind), s7 := s9 + 0x60 (alias); the shadow of the two buffers is set
                   addressable
     +0x27c..+0x280 jal reac_link_alias_read (0x8867c) with a0 = ifname, a1 = kind, a2 = 0x20, a3 = alias,
                   a4 = 0x100; a hit of 0 goes to +0x498
     +0x284..+0x2c8 the read failed: s5 := rc; a0 := g_say (0x6312e0); the `g_say = 0` arm loads the stderr cell
                   through .got+0xcc0 (0xa2630 -> 0xa18c8) under its own instrumented check (+0x2a8, else
                   errpath_load8 0x5a4fc) -- NOT reached when g_say is the fmemopen FILE;
                   jal reac_code_emit (0x89be4) with a3 = 0x21300 (.str.3), a4 = ifname, a5 = -rc
     +0x498..+0x4a0 jal reac_served_decide (0x89510) with a0 = kind, a1 = alias
     +0x4a4..+0x4ac the verdict v: `blt 1, v` -> v in {2, 3}; `bnez v` -> v = 1; else v = 0
     v = 0 (V_MARK): +0x4b0..+0x4bc jal reac_link_alias_write (0x88f54) with a1 = 0x213c0 ("reac-pw:served");
                   on 0 -> +0x5c0 `jal remember` (0x89db4) and s5 := 0; else s5 := rc and
                   +0x5d4..+0x5f4 jal reac_code_emit with a3 = 0x213e0 (.str.5), a4 = ifname, a5 = 0x213c0,
                   a6 = -rc, a7 = 0x21480 (.str.6) when rc = -1 else 0x214e0 (.str.7)
     v = 1 (V_OURS): +0x550..+0x568 jal wrapper_bcmp (0x4305c) with a0 = alias, a1 = 0x213c0, a2 = 15; equal ->
                   +0x56c jal remember; s5 := 1
     v = 2 (V_LEAVE_VLAN): +0x510..+0x544 jal wrapper_fprintf (0x43084) with a1 = 0x21500 (.str.8), a2 = ifname;
                   s5 := 2
     v = 3 (V_LEAVE_HOST): +0x57c..+0x5b4 jal wrapper_fprintf with a1 = 0x215a0 (.str.9), a2 = ifname,
                   a3 = alias; s5 := 3
     +0x360..+0x45c the frame's magic word, meta_fill_f5 (0x55f7c) over the frame's shadow and the inline flag
                   store that releases the class-3 frame (+0x37c `ld a0, 0x1f8(s3); sb zero, 0(a0)`)
     +0x458..+0x494 a0 := s5; restore, pop, ret.
   That is link_spec's `mark_lib` (link_spec.v:446-448 over `mark_core`): a NULL block, a NULL name or an empty
   name answer - E_INVAL; a failed read or write answers that code; otherwise the verdict, with the name
   remembered when the verdict is V_MARK and the write succeeded, or when it is V_OURS and the alias is exactly
   "reac-pw:served" (the 15-byte bcmp is the plain build's strcmp of the same two strings: the literal's 14 bytes
   and its NUL).

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x38 (inside [sp - K, sp)); every callee takes
     ecall_pre-style premises the walk derives from the journal; +0x494 ret.
   - K = 128 + 16 + 9360 = 9504: the 128-byte frame, the realignment slack of `andi sp, sp, -0x20`, then the
     deepest callee window on the covered path: reac_code_emit 9360 (lib/A/Prog/reac_code_emit_c.v), against
     reac_link_alias_read 8592 and reac_link_alias_write 8560 (reac_link_alias_read_c.v, reac_link_alias_write_c.v),
     reac_served_decide 8208, remember 8256, wrapper_bcmp 2 * ESTACK = 8192 (Reusable/YG0d.v:360-379),
     wrapper_fprintf 9216 (lib/A/AE2t.v:36), frame_alloc_3 and meta_fill_f5 ESTACK = 4096. The plain K (17248)
     does not carry over.
   - SIDE = [(3, 2); (1, 1); (9, 1); (0, 1)] (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 4.2): this
     function takes one class-3 frame and keeps it live across reac_link_alias_write, which takes another class-3 frame
     and calls nl_talk (class 9); reac_link_alias_read takes class 1 and also reaches nl_talk; reac_code_emit takes class
     0. With the room premise frame_alloc_3 hands out a frame, so the `bnez s3` fallback arm at +0x80 is not reached.
   - the fake kernel: `anlk_at m LA_G_NL kbs`, `nlk_wf kbs`, `nk_open kbs = 0`, `nk_opened kbs + 2 < 2 ^ 31`,
     `nk_closed kbs + 2 < 2 ^ 31`, `aiftab_at m LA_G_NL kbs tab`, and the shadow of g_nl
     (`range_addressable (ard m) SHADOW_OFF LA_G_NL NK_SIZE`): every byte of g_nl the two alias callees read or
     write, through their own instrumented checks. At most two exchanges run per call (one in the read, one in
     the write), which is where the `+ 2` bounds come from.
   - errno (`amk_errno_ok`): the alias callees reach fuzz_socket / fuzz_send / fuzz_recv, which store errno
     through ___errno_location (`mv a0, tp; addi a0, a0, -0xa4`), under an instrumented check. errno is NOT in
     this contract's write set: it is an image byte outside G, so `ajw` would be false of it, and `akept` excepts
     it in its image clause already (W_journalG.v's `gx_ok` note; the A-side library states errno the same way). The
     separations (from this frame, from g_nl, from the FILE block, from g_say, from g_said, from the marks block
     and from the name) are the plain lane's gaps 3a, 9 and 12: this function reads g_say and the name AFTER
     callees that write errno, so without them those facts do not survive the calls.
   - the name: `astr_arg m (aarg regs 1) nm`, and for a non-NULL name `astr_rt_ok` at this K (the two alias
     callees and remember pass it to the runtime's string wrappers), `(length s <= 15)%nat` (remember's Pre, and
     the line-length bound below), and the separations from g_nl, from the marks block, from the FILE block and
     from errno.
   - the marks block, when a0 <> 0: `amarks_at`, `marks_wf`, `amarks_blk_ok` (remember_c.v: the block
     addressable with its shadow hull, its 8-byte chunk tail visible, outside the callee windows), apart from
     g_nl, from errno and from the FILE block, and `amarks_ledger bl a0` (remember_c.v: a block of the
     allocator's ledger, over the block list `aleaf_fx` hands the Pre, and off the image), which
     remember's Pre asks for snprintf's destination at 0x89b1c / 0x89b70; the block is still in the list there,
     because each callee before them allocates nothing and its Post gives a `Permutation` of the list.
   - the interface table's name strings (`amk_table_ok`, the plain lane's gap 11): each is read by
     reac_link_alias_read, reac_link_alias_write and the index walk inside them, and this function's own Post
     re-states `aiftab_at` over the memory AFTER remember's writes to the marks block and the printf writes to
     the FILE block, so each string must be apart from this frame, from g_nl, from errno, from the FILE block and
     from the marks block, and carry what a string wrapper reads (`astr_rt_ok`).
   - the stream: `au64_at m LA_G_SAY sink`, `sink <> 0` (the `g_say = 0` arms at +0x294, +0x4d0, +0x518, +0x584
     are not taken, so the instrumented load of the stderr cell 0xa18c8 through .got+0xcc0 and its error path are
     not reached), `amemfile_k m sink k` (lib/A/Prog/reac_code_emit_c.v: link's memory FILE on image A),
     `k + MARK_LINE_MAX <= AMF_BUFSIZ`, `amf_blk_ok` (the FILE block addressable and outside the callee
     windows), and `In (sink, AMF_BLOCK) bl` over the block list `aleaf_fx` hands the Pre (the FILE block is a
     block of the allocator's ledger, which the libc fprintf / vfprintf contracts and this function's
     reac_code_emit ask; the slot gives it from the frame's `amf_gi_ledger`, lib/A/AMemFileSink.v).
     MARK_LINE_MAX = 400 bounds one line: the longest format is .str.9 (121 bytes, measured on the pin
     with pyelftools) with a name of at most 15 bytes and an alias of at most 255, and .str.5 through
     reac_code_emit adds EMIT_HEAD = 22; 121 + 15 + 255 = 391 and 22 + 102 + 15 + 14 + 11 + 34 = 198, both under
     400 (the plain lane measured the same bound).
   - the literals this function passes on, each by its exact bytes and with what a string wrapper reads of it
     (`acstr_at` + `astr_rt_ok`, including the shadow of the registered global's granules, in `amk_policy_ok`):
     0x213c0 "reac-pw:served" (the bcmp at +0x560 and the alias_write at +0x4bc), 0x21500 and 0x215a0 (the two
     wrapper_fprintf formats), 0x21300, 0x213e0, 0x21480, 0x214e0 (the reac_code_emit formats and their string
     arguments). `apre`'s `arodata_okP` fixes every .rodata byte to the image's, but only a walk at the concrete
     segments can compute them from it; stating the bytes lets the walk compute each format's parse, length
     and text at the abstract segments. The SHADOW is fixed by neither, which is why `astr_rt_ok` is stated.
   - the two literals reac_served_decide reads (0x212a0 "reac-pw:", 0x212c0 "vlan"): its own Pre asks for them by
     content, so they are stated here with their content (`acstr_at ... S_PREFIX` / `S_VLAN`).
   - the write set and apre's `ajw` on it: g_nl up to its request ring ([LA_G_NL, LA_G_NL + NK_N_SENT + 4), what
     the two alias callees write), the marks block (remember), and the FILE block (the two wrapper_fprintf calls
     and reac_code_emit). g_nl and the FILE block are the plain write set too, minus errno (above). Which clause
     of `ajw` grants each: g_nl by `inG G` (it is one of the eight objects of `LA_G`); the marks block by
     `in_tmp_block` (the calloc(1, 516) of LLVMFuzzerTestOneInput 0x82c84, a block allocated since the journal
     began). The FILE block is granted by `in_tmp_block` only in the target call whose first mark opened it; on
     every later target call it is a block of the journal's start, and the grant is the frame's: the harness
     journal's FP is `amf_harness_fp T` (lib/A/AMemFileSink.v:231, `sink_token` and every kept block), and
     `amf_harness_fp_grants` (lib/A/AMemFile.v:535) gives `awr_byte` of every byte of a kept block that is live
     in the ledger, which `In (sink, AMF_BLOCK) bl` says. The function's own class-3 side frame and its shadow
     are not in the write set: it is taken and released inside the call, and
     `apost`'s `frames S2 = frames Sc` says so (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 2).
   - the read set Rd (`aleaf_fx`'s): the name and its NUL, the interface table and its LIVE name strings with
     their NULs (`amk_tab_rd`: entry i of the table `aiftab_at` reads, the text of the A-side library's
     reac_link_alias_read_ard; the two alias callees read no other entry, and a stale slot, i >= n_if, is
     unconstrained, so naming it would ask `akb` of an arbitrary byte; found by the mark-quietly walk). They are
     read through pointers after frame_alloc_3 has run, so each must be a byte `akept` keeps (`akb`). At the call
     sites they are: mark_quietly's own a1, which the slot takes from name_of (a g_names entry or an `odd`
     entry, both image bytes), and g_nl itself, an image byte.
     THE REST OF EACH NUL'S 8-BYTE GRANULE IS NOT IN Rd. Every runtime string wrapper a later callee reaches
     (remember 0x89b1c / 0x89b70, reac_code_emit 0x89870 / 0x89b9c, wrapper_fprintf 0x89aec / 0x89b5c) asks
     those bytes only VISIBLE (`astr_rt_ok`'s tail clause, RtString.v `atail_vis`), and no value of theirs
     enters a Post. After a name in .rodata they are its registered global's redzone, bytes of
     `as_owned_static` where `akb`'s image clause fails (AF0m.v: (0x20fc1, 0x1f) after .str.1, (0x20fec, 0x14)
     after odd[1], (0x21005, 0x1b), (0x21026, 0x1a), (0x21049, 0x17), (0x21066, 0x1a); open item W6, found by
     the slot's mark-arm walk), so naming them in Rd made the Pre false at op_refused 0x831f8 and op_mark 0x8347c.
     Their visibility is the Pre's own premise at entry (`astr_rt_ok` in `amk_name_ok` and `amk_table_ok`), and
     it holds at every later state without a read set. At tfibsegs: mbyte falls back to seg_rom (YP09.v:18-22),
     seg_rom is Some on all of [0x10000, 0x654000) (AB13.v:148 tfib_rom_all), and image bytes are never hidden
     (YK04.v:38 H_off_segments); the same account as in the kernel contract (kernel_c.v,
     lines 165-167). At the abstract segments: the post-NUL bytes of every registered
     .rodata literal the slice uses are owned redzones that AF0m pins as const cells of value 0 (AF0m.v:652-803,
     e.g. 0x20fc1, 0x20fec, 0x21005, 0x21026, 0x21049, 0x21066, 0x21394, 0x214e1, 0x21683), which AR's
     `am_const` fixes at every state under the instance fact `PcapSyms B` (AD2l.PcapB_syms); the post-NUL bytes
     of a g_names entry lie inside its own 8-byte entry, which is neither owned nor in a write set, so `akept`'s
     image clause keeps them (the comparer's round 13).
   EV = 0: no callee of this function reaches the allocator (the alias callees reach only the fake kernel, and
   the printf layer allocates nothing on the FIT branch).

   What does NOT carry over from the plain text:
   - the `leaf_fp` shape with the printf floor and the stack-protector words (the wrapper contract's on image A).
   - errno in the write set (above), and `frame_apart_gnl regs K` (link-a/form/FORM.md (internal record, sha256 13aeff774164)
     section 1a: on image A the window is on the real stack above `alloc_ceiling` and g_nl is an image byte).
   - `pf_img_free` on the marks block, and `memfile_k` over the plain image (`amemfile_k` here).
   - the plain K (17248) and the plain `sink + FILE_BLOCK <= spZ regs - 17248` (now `amf_blk_ok` at K = 9504).
   Nothing of the plain Post is false of image A; the refusal arm's `nlk_at m' kbs` holds because that path
   leaves g_nl alone (it returns before any callee), even though it does push a frame and take a side frame.
   THE FLOATING-POINT STATE is `aleaf_fx`'s. Entry: the shape takes `YK0o.frm_zero (fp_csr fx)`, which the
   released printf-family contracts ask (boxreg A/Rt/SnprintfDef.v; the printf family's shared contract) and the plain
   mark_quietly states (lib/Prog/mark_quietly_c.v:151); it holds at every call site, because the start-up fcsr
   is 0 (`fp_frm_zero_fx0`, Reusable/YK0o.v:15) and none of link's own functions holds an f* or csr*
   instruction. Exit: `apostF` returns at some fx' with `BoxBase.fxr fx fx'` (every f register but f10 kept,
   the fcsr kept or its rounding mode 0), which is what the two wrapper_fprintf calls, reac_code_emit and
   remember leave.
   Released proofs (rule 24): none of reac_served_mark (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038)).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0o YI04 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem model_decide_c remember_c reac_code_emit_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition REAC_SERVED_MARK_A : Z := 0x895a8.
Lemma REAC_SERVED_MARK_A_is_entry : REAC_SERVED_MARK_A = LA_reac_served_mark. Proof. reflexivity. Qed.

(* the .rodata literals this function forms (twin .symtab; bytes read from the pin with pyelftools) *)
Definition LA_S_READERR : Z := 0x21300.    (* .str.3, 147 bytes, "[%s] could not read the interface alias .." *)
Definition LA_S_SERVED : Z := 0x213c0.     (* .str.4, "reac-pw:served" *)
Definition LA_S_WRITEERR : Z := 0x213e0.   (* .str.5, 102 bytes, "[%s] could not mark it '%s' (errno %d)%s .." *)
Definition LA_S_NOCAP : Z := 0x21480.      (* .str.6, 34 bytes, ": this daemon has no CAP_NET_ADMIN" *)
Definition LA_S_EMPTY : Z := 0x214e0.      (* .str.7, the empty string *)
Definition LA_S_VLANLINE : Z := 0x21500.   (* .str.8, 117 bytes *)
Definition LA_S_OWNALIAS : Z := 0x215a0.   (* .str.9, 121 bytes *)

(* the exact bytes of the four formats this function passes on and of .str.6, which .str.5's last `%s` takes
   (read from the pin's .rodata with pyelftools, without the NUL): stated so that a walk at the abstract
   segments gets each parse, piece list, conversion order, length and text by computation *)
Definition S_STR3 : list byte := map (Z_to_bv 8)
  [91; 37; 115; 93; 32; 99; 111; 117; 108; 100; 32; 110; 111; 116; 32; 114; 101; 97; 100; 32; 116; 104; 101;
   32; 105; 110; 116; 101; 114; 102; 97; 99; 101; 32; 97; 108; 105; 97; 115; 32; 40; 101; 114; 114; 110; 111;
   32; 37; 100; 41; 32; 226; 128; 148; 32; 110; 111; 116; 32; 109; 97; 114; 107; 101; 100; 32; 97; 115; 32; 97;
   32; 82; 69; 65; 67; 32; 105; 110; 116; 101; 114; 102; 97; 99; 101; 44; 32; 115; 111; 32; 116; 104; 101; 32;
   104; 111; 115; 116; 39; 115; 32; 110; 101; 116; 119; 111; 114; 107; 32; 109; 97; 110; 97; 103; 101; 114; 32;
   105; 115; 32; 110; 111; 116; 32; 116; 111; 108; 100; 32; 116; 111; 32; 108; 101; 97; 118; 101; 32; 105; 116;
   32; 97; 108; 111; 110; 101; 10].
Definition S_STR5 : list byte := map (Z_to_bv 8)
  [91; 37; 115; 93; 32; 99; 111; 117; 108; 100; 32; 110; 111; 116; 32; 109; 97; 114; 107; 32; 105; 116; 32; 39;
   37; 115; 39; 32; 40; 101; 114; 114; 110; 111; 32; 37; 100; 41; 37; 115; 32; 226; 128; 148; 32; 116; 104;
   101; 32; 104; 111; 115; 116; 39; 115; 32; 110; 101; 116; 119; 111; 114; 107; 32; 109; 97; 110; 97; 103; 101;
   114; 32; 105; 115; 32; 110; 111; 116; 32; 116; 111; 108; 100; 32; 116; 111; 32; 108; 101; 97; 118; 101; 32;
   105; 116; 32; 97; 108; 111; 110; 101; 10].
Definition S_STR8 : list byte := map (Z_to_bv 8)
  [114; 101; 97; 99; 45; 112; 119; 58; 32; 91; 37; 115; 93; 32; 105; 115; 32; 97; 32; 86; 76; 65; 78; 32; 116;
   104; 101; 32; 104; 111; 115; 116; 32; 109; 97; 100; 101; 32; 226; 128; 148; 32; 110; 111; 116; 32; 109; 97;
   114; 107; 101; 100; 59; 32; 105; 102; 32; 97; 32; 110; 101; 116; 119; 111; 114; 107; 32; 109; 97; 110; 97;
   103; 101; 114; 32; 99; 111; 110; 102; 105; 103; 117; 114; 101; 115; 32; 105; 116; 44; 32; 103; 105; 118;
   101; 32; 105; 116; 32; 110; 111; 32; 97; 100; 100; 114; 101; 115; 115; 101; 115; 32; 116; 104; 101; 114;
   101; 10].
Definition S_STR9 : list byte := map (Z_to_bv 8)
  [114; 101; 97; 99; 45; 112; 119; 58; 32; 91; 37; 115; 93; 32; 99; 97; 114; 114; 105; 101; 115; 32; 116; 104;
   101; 32; 104; 111; 115; 116; 39; 115; 32; 111; 119; 110; 32; 97; 108; 105; 97; 115; 32; 39; 37; 115; 39; 32;
   226; 128; 148; 32; 110; 111; 116; 32; 109; 97; 114; 107; 101; 100; 59; 32; 116; 104; 101; 32; 104; 111; 115;
   116; 39; 115; 32; 110; 101; 116; 119; 111; 114; 107; 32; 109; 97; 110; 97; 103; 101; 114; 32; 105; 115; 32;
   110; 111; 116; 32; 116; 111; 108; 100; 32; 116; 111; 32; 108; 101; 97; 118; 101; 32; 105; 116; 32; 97; 108;
   111; 110; 101; 10].
Definition S_STR6 : list byte := map (Z_to_bv 8)
  [58; 32; 116; 104; 105; 115; 32; 100; 97; 101; 109; 111; 110; 32; 104; 97; 115; 32; 110; 111; 32; 67; 65; 80;
   95; 78; 69; 84; 95; 65; 68; 77; 73; 78].

(* the entries this function calls, beside the four own functions *)
Definition LA_frame_alloc_3 : Z := 0x3dc18.
Definition LA_wrapper_bcmp : Z := 0x4305c.
Definition LA_meta_fill_f5 : Z := 0x55f7c.
(* the stderr arm's two cells, not reached under `sink <> 0` *)
Definition LA_GOT_STDERR : Z := 0xa2630.
Definition LA_STDERR_VAR : Z := 0xa18c8.

(* the most bytes one call puts on the stream *)
Definition MARK_LINE_MAX : Z := 400.

(* the stack bound on image A: the 128-byte frame, the realignment slack, then reac_code_emit's window *)
Definition REAC_SERVED_MARK_AFRAME : Z := 128.
Definition REAC_SERVED_MARK_ASLACK : Z := 16.
Definition REAC_SERVED_MARK_AK : Z :=
  REAC_SERVED_MARK_AFRAME + REAC_SERVED_MARK_ASLACK + REAC_CODE_EMIT_AK.
Lemma REAC_SERVED_MARK_AK_val : REAC_SERVED_MARK_AK = 9504. Proof. reflexivity. Qed.

(* the side-stack room: this frame (class 3) and every frame its call tree holds at once *)
Definition REAC_SERVED_MARK_ASIDE : list (Z * Z) := [(3, 2); (1, 1); (9, 1); (0, 1)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* errno as this call tree writes it: the thread-pointer cell ___errno_location forms, writable and addressable,
   and apart from everything the caller reads after a callee wrote it. `(fb, fn)` is the FILE block of the
   function that takes this premise, or (0, 0) for a function that touches no FILE (reac_served_unmark_all),
   where `apart (as_errno B) 4 0 0` is trivially true. Shared with reac_served_unmark_all_c.v and
   mark_quietly_c.v. *)
Definition amk_errno_ok (regs : bvmap 5 word) (K fb fn : Z) (m : word -> option byte) : Prop :=
  as_errno B = as_tp B - 164
  /\ awrange segs m (as_errno B) 4
  /\ range_addressable (ard segs m) SHADOW_OFF (as_errno B) 4
  /\ apart_frame regs K (as_errno B) 4
  /\ apart_gnl LA_G_NL (as_errno B) 4
  /\ apart (as_errno B) 4 fb fn
  /\ (aarg regs 0 <> 0 -> apart (as_errno B) 4 (aarg regs 0) MK_SIZE).

(* the name, as the two alias callees and remember read it (the plain lane's `mark_name_ok`, at image A's
   addresses, with the shadow facts the wrappers need). Shared with mark_quietly_c.v, which tail-calls this
   function at the same sp. *)
Definition amk_name_ok (regs : bvmap 5 word) (K fb fn : Z) (m : word -> option byte)
    (nm : option (list byte)) : Prop :=
  forall s, nm = Some s ->
    (length s <= 15)%nat
    /\ astr_rt_ok segs regs K m (aarg regs 1) s
    /\ apart_gnl LA_G_NL (aarg regs 1) (Z.of_nat (length s) + 8)
    /\ apart fb fn (aarg regs 1) (Z.of_nat (length s) + 8)
    /\ apart (as_errno B) 4 (aarg regs 1) (Z.of_nat (length s) + 8)
    /\ (aarg regs 0 <> 0 ->
          apart (aarg regs 1) (Z.of_nat (length s) + 8) (aarg regs 0) MK_SIZE).

(* every interface-table name string, apart from this frame, g_nl, errno, the FILE block and the marks block,
   and readable by a string wrapper (the plain lane's `mark_table_ok`, gap 11) *)
Definition amk_table_ok (regs : bvmap 5 word) (K fb fn : Z) (m : word -> option byte)
    (tab : list (list byte * Z)) : Prop :=
  forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
    au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
    astr_rt_ok segs regs K m p n2
    /\ apart_gnl LA_G_NL p (Z.of_nat (length n2) + 1)
    /\ apart (as_errno B) 4 p (Z.of_nat (length n2) + 1)
    /\ apart fb fn p (Z.of_nat (length n2) + 1)
    /\ (aarg regs 0 <> 0 -> apart (aarg regs 0) MK_SIZE p (Z.of_nat (length n2) + 1)).

(* the marks block, as remember and the two Posts see it (the plain lane's `mark_block_ok`). Shared with
   mark_quietly_c.v. *)
Definition amk_block_ok (regs : bvmap 5 word) (K fb fn : Z) (m : word -> option byte) : Prop :=
  aarg regs 0 <> 0 ->
    amarks_blk_ok segs regs K m (aarg regs 0)
    /\ apart_gnl LA_G_NL (aarg regs 0) MK_SIZE
    /\ apart (as_errno B) 4 (aarg regs 0) MK_SIZE
    /\ apart fb fn (aarg regs 0) MK_SIZE
    /\ exists gbs, amarks_at segs m (aarg regs 0) gbs /\ marks_wf gbs.

(* the literals of the marking policy's own lines, the two reac_served_decide reads, and the four its callees
   ask for by content: remember's "%s" (0x21680) and the three of reac_code_emit's first line (0x21640,
   0x212e0, 0x21660). Every literal this function forms is stated by its exact bytes, with what a string
   wrapper reads of it: the four formats it passes on (.str.3 and .str.5 to reac_code_emit, .str.8 and .str.9
   to wrapper_fprintf; on the pin .str.3 holds %s %d, .str.5 %s %s %d %s, .str.8 %s, .str.9 %s %s) and the
   string arguments .str.4, .str.6 and .str.7. So a walk at the abstract segments computes each format's parse,
   conversion order, length and text, which the callees' format family, their bounds and this function's
   MARK_LINE_MAX need, with no segment computation (the comparer's rounds 9 and 10). Shared with
   mark_quietly_c.v. *)
Definition amk_policy_ok (regs : bvmap 5 word) (K : Z) (m : word -> option byte) : Prop :=
  acstr_at segs m LA_RSD_PREFIX S_PREFIX /\ astr_rt_ok segs regs K m LA_RSD_PREFIX S_PREFIX
  /\ acstr_at segs m LA_RSD_VLAN S_VLAN /\ astr_rt_ok segs regs K m LA_RSD_VLAN S_VLAN
  /\ acstr_at segs m LA_S_SERVED S_SERVED /\ astr_rt_ok segs regs K m LA_S_SERVED S_SERVED
  /\ acstr_at segs m LA_FMT_S S_FMT_S /\ astr_rt_ok segs regs K m LA_FMT_S S_FMT_S
  /\ acstr_at segs m LA_FMT_SS S_FMT_SS /\ astr_rt_ok segs regs K m LA_FMT_SS S_FMT_SS
  /\ acstr_at segs m LA_S_REACPW S_REACPW /\ astr_rt_ok segs regs K m LA_S_REACPW S_REACPW
  /\ acstr_at segs m LA_S_E_NOT_MARKED S_E_NOT_MARKED
  /\ astr_rt_ok segs regs K m LA_S_E_NOT_MARKED S_E_NOT_MARKED
  /\ acstr_at segs m LA_S_READERR S_STR3 /\ astr_rt_ok segs regs K m LA_S_READERR S_STR3
  /\ acstr_at segs m LA_S_WRITEERR S_STR5 /\ astr_rt_ok segs regs K m LA_S_WRITEERR S_STR5
  /\ acstr_at segs m LA_S_VLANLINE S_STR8 /\ astr_rt_ok segs regs K m LA_S_VLANLINE S_STR8
  /\ acstr_at segs m LA_S_OWNALIAS S_STR9 /\ astr_rt_ok segs regs K m LA_S_OWNALIAS S_STR9
  /\ acstr_at segs m LA_S_NOCAP S_STR6 /\ astr_rt_ok segs regs K m LA_S_NOCAP S_STR6
  /\ acstr_at segs m LA_S_EMPTY [] /\ astr_rt_ok segs regs K m LA_S_EMPTY [].

(* the fake kernel, as this call tree reads and writes it: its bytes, its shape, and its shadow (addressable,
   with the hull visible: the checked copies of fuzz_send / fuzz_recv into and out of g_nl read the shadow hull,
   Reusable/YG0d.v:330, which the A-side library's two alias contracts state as `shadow_hull_vis` of g_nl). Shared with
   reac_served_unmark_all_c.v and mark_quietly_c.v. *)
Definition amk_nlk_ok (m : word -> option byte) (kbs : list byte) (tab : list (list byte * Z)) (n : Z) : Prop :=
  anlk_at segs m LA_G_NL kbs /\ nlk_wf kbs /\ nk_open kbs = 0
  /\ nk_opened kbs + n < 2 ^ 31 /\ nk_closed kbs + n < 2 ^ 31
  /\ aiftab_at segs m LA_G_NL kbs tab
  /\ range_addressable (ard segs m) SHADOW_OFF LA_G_NL NK_SIZE
  /\ shadow_hull_vis (ard segs m) LA_G_NL NK_SIZE.

(* the bytes of the LIVE interface-table strings with their NULs: entry i of the table `aiftab_at` reads from
   g_nl, whose name pointer is p and whose string is n2 (the text of the A-side library's reac_link_alias_read_ard,
   which is what the two alias callees read; a stale slot, i >= n_if, is unconstrained and is not read). The rest
   of each NUL's granule is not here: see the read-set paragraph of the header. Shared with
   reac_served_unmark_all_c.v and mark_quietly_c.v. *)
Definition amk_tab_rd (m : word -> option byte) (a : Z) : Prop :=
  exists bs tab i n2 ix p, anlk_at segs m LA_G_NL bs /\ aiftab_at segs m LA_G_NL bs tab
    /\ nth_error tab i = Some (n2, ix)
    /\ au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p
    /\ acstr_at segs m p n2 /\ p <= a <= p + Z.of_nat (length n2).

(* the read set of this function and of mark_quietly: the name and its NUL, the interface table and its live
   name strings with their NULs *)
Definition amk_rd (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  astr_rd segs m (aarg regs 1) a
  \/ rd_ivl (LA_G_NL + NK_IF_NAME) (LA_G_NL + NK_SIZE) a
  \/ amk_tab_rd m a.

Definition reac_served_mark_apre (sink : Z) (bl : list (Z * Z)) (regs : bvmap 5 word) (m : word -> option byte)
  : Prop :=
  exists kbs tab nm k,
    In (sink, AMF_BLOCK) bl
    /\ (aarg regs 0 <> 0 -> amarks_ledger bl (aarg regs 0))
    /\ amk_nlk_ok m kbs tab 2
    /\ amk_errno_ok regs REAC_SERVED_MARK_AK sink AMF_BLOCK m
    /\ apart (as_errno B) 4 LA_G_SAY 8 /\ apart (as_errno B) 4 LA_G_SAID SAID_SIZE
    /\ amk_table_ok regs REAC_SERVED_MARK_AK sink AMF_BLOCK m tab
    /\ amk_policy_ok regs REAC_SERVED_MARK_AK m
    /\ au64_at segs m LA_G_SAY sink /\ sink <> 0
    /\ amemfile_k segs m sink k /\ k + MARK_LINE_MAX <= AMF_BUFSIZ
    /\ amf_blk_ok segs regs REAC_SERVED_MARK_AK m sink
    /\ astr_arg segs m (aarg regs 1) nm
    /\ amk_name_ok regs REAC_SERVED_MARK_AK sink AMF_BLOCK m nm
    /\ amk_block_ok regs REAC_SERVED_MARK_AK sink AMF_BLOCK m.

(* the write set: g_nl up to its request ring, the marks block, the FILE block. errno is NOT here (an image
   byte outside G: `ajw` would be false, and `akept` excepts it already). *)
Definition reac_served_mark_awr (sink : Z) (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(LA_G_NL, LA_G_NL + NK_N_SENT + 4);
   aivl (aarg regs 0) MK_SIZE;
   aivl sink AMF_BLOCK].

Definition reac_served_mark_apost (sink : Z) (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  (forall k, amemfile_k segs m sink k ->
     exists k', k <= k' <= k + MARK_LINE_MAX /\ amemfile_k segs m' sink k')
  /\ (aarg regs 0 = 0 -> getr regs' 10 = w64 (- E_INVAL)
        /\ forall kbs, anlk_at segs m LA_G_NL kbs -> anlk_at segs m' LA_G_NL kbs)
  /\ (aarg regs 0 <> 0 -> forall kbs tab nm gbs,
        anlk_at segs m LA_G_NL kbs -> aiftab_at segs m LA_G_NL kbs tab ->
        astr_arg segs m (aarg regs 1) nm -> amarks_at segs m (aarg regs 0) gbs ->
        let M := mark_lib tab nm (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) in
        getr regs' 10 = w64 (m_rc M)
        /\ (exists gbs', amarks_at segs m' (aarg regs 0) gbs' /\ marks_wf gbs'
              /\ mk_names gbs' = m_marks M
              /\ mk_n gbs' = Z.of_nat (length (m_marks M)))
        /\ (exists kbs', anlk_at segs m' LA_G_NL kbs' /\ nlk_wf kbs'
              /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
              /\ nk_n_if kbs' = nk_n_if kbs /\ aiftab_at segs m' LA_G_NL kbs' tab
              /\ nk_next kbs' = Z.of_nat (k_next (m_state M))
              /\ nk_sent kbs' = m_reqs M /\ nk_n_sent kbs' = Z.of_nat (length (m_reqs M))
              /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
              /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
              /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 2)).

Definition reac_served_mark_acontract : Prop :=
  forall sink : Z,
    aleaf_fx SK segs rlo rhi B REAC_SERVED_MARK_A REAC_SERVED_MARK_AK 0 REAC_SERVED_MARK_ASIDE
      (reac_served_mark_apre sink) amk_rd (reac_served_mark_awr sink) (reac_served_mark_apost sink).

End c.
