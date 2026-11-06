(* reac_served_unmark_all (reac_served_mark.c:94-107) on image A (fuzz_link.asan 0x89ed4, 1148 bytes; listing
   (internal path) (internal record, sha256 9bc7ee7c887a)): at exit, take away
   exactly the marks this run wrote that are still its own, and clear the list. a0 = m, which may be NULL. The plain
   contract is lib/Prog/reac_served_unmark_all_c.v; this file states the SAME link_spec result (`unmark`) in
   link_amem.v's `aleaf_rd` form.

   The image-A code, in order:
     +0x00..+0x3c  push a 160-byte frame; sd zero, 0(sp); save ra, s0..s11; s0 := sp + 0xa0
     +0x40  andi sp, sp, -0x20                                  (realignment: up to 16 more bytes of window)
     +0x48..+0x60  s4 := a0; s10 := the shadow base (.got 0xa19d0); a2 := the side-stack switch cell (.got
                   0xa1a28)
     +0x68..+0x70  a0 := 0x160; jal frame_alloc_3 (0x3dc18); s3 := a0, s9 := s3   (the 352-byte side frame, with
                   the alias buffer alias[256] at s9 + 0x20)
     +0x84..+0x9c  the real-stack arm (not taken under `aside_room`, link-a/form/FORM.md (internal record, sha256 13aeff774164) section 4.2)
     +0xa4..+0x188 the frame's header words and the shadow bytes of its redzones
     +0x18c  beqz s4 -> +0x350                                  (NULL marks block: straight to the release)
     +0x190..+0x19c, +0x468..+0x478  the instrumented check of the 4-byte load of m->n: shadow byte s of s4;
                   s = 0 passes; else (s4 & 7) + 3 < s passes; else errpath_load4 (0x5a45c)
     +0x1a0  lw a0, 0(s4) = m->n;  +0x1a4 blez -> +0x340        (no name kept: straight to the memset)
     +0x1a8..+0x1d4 s11 := 0 (the index), s5 := s9 + 0x20 (the alias buffer), s6 := s4 + 4 (the names array),
                   s7 := 0x213c0 (".str.4" = "reac-pw:served"), [s1 + 0x18] := 0x214e0 (".str.7" = "")
     the loop, i = 0 .. m->n - 1:
     +0x25c..+0x26c jal reac_link_alias_read (0x8867c) with a0 = m->name[i], a1 = 0 (no kind buffer), a2 = 0,
                   a3 = alias, a4 = 0x100; a non-zero answer skips this name (+0x270 bnez)
     +0x274..+0x280 jal wrapper_bcmp (0x4305c) with a0 = alias, a1 = 0x213c0, a2 = 15; a non-zero answer skips
     +0x288..+0x290 jal reac_link_alias_write (0x88f54) with a0 = m->name[i], a1 = "" (the empty alias)
     +0x314..+0x334 the shadow check of m->n again, i := i + 1, the slot pointer += 16, loop while i < m->n
     +0x340..+0x34c jal checked_memset (0x53214) with a0 = m, a1 = 0, a2 = 0x204 = MK_SIZE  (the WHOLE block:
                   both the count and every name go, where the harness model only sets its count to 0;
                   check_marks compares only the first n entries, so the two still agree)
     +0x350..+0x424 the frame's magic word, meta_fill_f5 (0x55f7c) over the frame's shadow and the inline flag
                   store that releases the class-3 frame (+0x370 `ld a0, 0x1f8(s3); sb zero, 0(a0)`)
     +0x428..+0x464 restore, pop, ret.
   That is link_spec's `unmark` (link_spec.v:457-472): for each kept name, read its alias; an interface that is
   gone, or whose alias somebody changed since, is left alone; the rest get an empty alias written; then the
   whole 516-byte structure is zeroed.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x3c (inside [sp - K, sp)); every callee takes
     ecall_pre-style premises the walk derives from the journal; +0x464 ret.
   - K = 160 + 16 + 8592 = 8768: the 160-byte frame, the realignment slack of `andi sp, sp, -0x20`, then the
     deepest callee window: reac_link_alias_read 8592 (reac_link_alias_read_c.v), against
     reac_link_alias_write 8560, wrapper_bcmp 2 * ESTACK = 8192 (Reusable/YG0d.v:360-379), checked_memset,
     frame_alloc_3 and meta_fill_f5 ESTACK = 4096. The plain K (17232) does not carry over.
   - SIDE = [(3, 2); (1, 1); (9, 1)] (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 4.2): this function's
     own class-3 frame stays live across reac_link_alias_write, which takes a second class-3 frame and calls nl_talk (class
     9); reac_link_alias_read takes class 1 and also reaches nl_talk. There is no class-0 frame here (no reac_code_emit).
     With the room premise frame_alloc_3 hands out a frame, so the `bnez s3` fallback arm at +0x80 is not reached.
   - the fake kernel (`amk_nlk_ok ... (2 * MARKS_MAX)`): `anlk_at`, `nlk_wf`, `nk_open = 0`, the two counter
     bounds with 2 * MARKS_MAX (at most two exchanges per kept name, at most MARKS_MAX names), `aiftab_at`, and
     the shadow of g_nl, which the two alias callees' checks read.
   - errno (`amk_errno_ok regs K 0 0`, reac_served_mark_c.v): the alias callees store errno through
     ___errno_location under an instrumented check. The FILE range is (0, 0) because this function touches no
     FILE: it makes no printf call. errno is NOT in the write set (an image byte outside G: `ajw` would be
     false, and `akept` excepts it already).
   - the interface table's name strings (`amk_table_ok regs K 0 0`): both callees read them (+0x26c, +0x290),
     and this function's own Post re-states `aiftab_at` over the memory AFTER the memset at +0x34c, so each
     string must be apart from this frame, from g_nl, from errno and from the marks block, and carry what a
     string wrapper reads (the plain lane's gap 13).
   - the marks block, when a0 <> 0 (`amk_block_ok regs K 0 0`): `amarks_at`, `marks_wf`, the block addressable
     with its shadow hull and its 8-byte chunk tail visible, outside the callee windows, apart from g_nl and
     errno. The same facts are what checked_memset asks of its destination (`dest_ok`, `amem_range`,
     `range_addressable`, `shadow_hull_vis`, Reusable/YG0d.v:319-334), and what makes the names it passes to the
     alias callees readable.
   - the two literals: 0x213c0 "reac-pw:served" (the 15-byte bcmp at +0x280, which is the plain build's strcmp
     of the same two strings: the literal's 14 bytes and its NUL) and 0x214e0 "" (the empty alias
     reac_link_alias_write writes). Their BYTES are the image's (`apre`'s `arodata_okP`); their SHADOW is not,
     which is why `astr_rt_ok` is stated of each.
   - the write set and apre's `ajw` on it: g_nl up to its request ring (what the two alias callees write) and
     the marks block (the memset). The function's own class-3 side frame and its shadow are not in the write
     set: it is taken and released inside the call (`apost`'s `frames S2 = frames Sc`).
   - the read set Rd (`aleaf_rd`): the interface table and its name strings. The names this function passes to
     its callees lie INSIDE the marks block, which is in the write set, so they are not in Rd. a1 is not an
     argument of this function and is in neither set.
   EV = 0: no callee reaches the allocator.

   What does NOT carry over from the plain text:
   - `(arg regs 0 = 0 -> m' = m)`. FALSE of image A (link-a/form/FORM.md (internal record, sha256 13aeff774164) section
     1a): the prologue pushes 160 bytes at +0x00..+0x3c and frame_alloc_3 runs BEFORE the `beqz s4` at +0x18c, so memory
     changes on that path too. What is true, and what the Post says instead, is `akept` (everything outside [sp - K, sp)
     and the write set) plus the fake kernel unchanged, which is what the caller needs; the side frame's own bytes and
     shadow are outside `akept`'s four clauses, because the frame is not one of `frames Sc`.
   - errno in the write set (above), and `frame_apart_gnl regs K` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1a).
   - the plain K (17232).
   Released proofs (rule 24): none of reac_served_unmark_all
   (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038)).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI04 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem model_decide_c remember_c reac_code_emit_c reac_served_mark_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition REAC_SERVED_UNMARK_ALL_A : Z := 0x89ed4.
Lemma REAC_SERVED_UNMARK_ALL_A_is_entry :
  REAC_SERVED_UNMARK_ALL_A = LA_reac_served_unmark_all. Proof. reflexivity. Qed.

(* the runtime entry of the final clear (listing +0x34c) *)
Definition LA_checked_memset : Z := 0x53214.

(* the stack bound on image A: the 160-byte frame, the realignment slack, then alias_read's window *)
Definition REAC_SERVED_UNMARK_ALL_AFRAME : Z := 160.
Definition REAC_SERVED_UNMARK_ALL_ASLACK : Z := 16.
Definition AUN_ALIAS_READ_STK : Z := 8592.   (* reac_link_alias_read_c.v REAC_LINK_ALIAS_READ_AK *)
Definition REAC_SERVED_UNMARK_ALL_AK : Z :=
  REAC_SERVED_UNMARK_ALL_AFRAME + REAC_SERVED_UNMARK_ALL_ASLACK + AUN_ALIAS_READ_STK.
Lemma REAC_SERVED_UNMARK_ALL_AK_val : REAC_SERVED_UNMARK_ALL_AK = 8768. Proof. reflexivity. Qed.

(* the side-stack room: this frame (class 3) and every frame its call tree holds at once *)
Definition REAC_SERVED_UNMARK_ALL_ASIDE : list (Z * Z) := [(3, 2); (1, 1); (9, 1)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition reac_served_unmark_all_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists kbs tab,
    amk_nlk_ok segs m kbs tab (2 * MARKS_MAX)
    /\ amk_errno_ok segs B regs REAC_SERVED_UNMARK_ALL_AK 0 0 m
    /\ amk_table_ok segs B regs REAC_SERVED_UNMARK_ALL_AK 0 0 m tab
    /\ amk_block_ok segs B regs REAC_SERVED_UNMARK_ALL_AK 0 0 m
    /\ acstr_at segs m LA_S_SERVED S_SERVED
    /\ astr_rt_ok segs regs REAC_SERVED_UNMARK_ALL_AK m LA_S_SERVED S_SERVED
    /\ acstr_at segs m LA_S_EMPTY []
    /\ astr_rt_ok segs regs REAC_SERVED_UNMARK_ALL_AK m LA_S_EMPTY [].

(* the read set: the interface table and its LIVE name strings (`amk_tab_rd`, reac_served_mark_c.v: the entries
   `aiftab_at` reads, which is all the two alias callees read; a stale slot is unconstrained and not read). The
   names this function passes to its callees lie inside the marks block, which is in the write set. *)
Definition reac_served_unmark_all_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  rd_ivl (LA_G_NL + NK_IF_NAME) (LA_G_NL + NK_SIZE) a
  \/ amk_tab_rd segs m a.

(* the write set: g_nl up to its request ring, and the marks block the memset clears *)
Definition reac_served_unmark_all_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(LA_G_NL, LA_G_NL + NK_N_SENT + 4); aivl (aarg regs 0) MK_SIZE].

Definition reac_served_unmark_all_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  (aarg regs 0 = 0 -> forall kbs, anlk_at segs m LA_G_NL kbs -> anlk_at segs m' LA_G_NL kbs)
  /\ (aarg regs 0 <> 0 -> forall kbs tab gbs,
        anlk_at segs m LA_G_NL kbs -> aiftab_at segs m LA_G_NL kbs tab ->
        amarks_at segs m (aarg regs 0) gbs ->
        let U := unmark tab (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) in
        (exists gbs', amarks_at segs m' (aarg regs 0) gbs' /\ marks_wf gbs' /\ mk_n gbs' = 0)
        /\ (exists kbs', anlk_at segs m' LA_G_NL kbs' /\ nlk_wf kbs'
              /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
              /\ nk_n_if kbs' = nk_n_if kbs /\ aiftab_at segs m' LA_G_NL kbs' tab
              /\ nk_next kbs' = Z.of_nat (k_next (snd U))
              /\ nk_sent kbs' = fst U /\ nk_n_sent kbs' = Z.of_nat (length (fst U))
              /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
              /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
              /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 2 * MARKS_MAX)).

Definition reac_served_unmark_all_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B REAC_SERVED_UNMARK_ALL_A REAC_SERVED_UNMARK_ALL_AK 0
    REAC_SERVED_UNMARK_ALL_ASIDE
    reac_served_unmark_all_apre reac_served_unmark_all_ard reac_served_unmark_all_awr
    reac_served_unmark_all_apost.

End c.
