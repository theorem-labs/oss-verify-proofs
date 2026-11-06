From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_env.
Import ListNotations.
Open Scope Z_scope.

(** m_file(c, text, label) (fuzz_segconf.c:259-293, static void; at 0x13fb4 in the image 3776ca44d75c, size 2004,
    frame 0xd0 = 208 bytes, `sd` of s11, s10, ..., s0, ra at
    sp + 0x68, 0x70, ..., 0xc0, 0xc8 (0x13fb8-0x13fe8), restored by the epilogue 0x1474c-0x14784). It inlines m_header
    (c:159-194), m_key (c:197-257), blank (c:113-116), strip (c:119-125; 5 sites: c:285, 167, 173, 205, 206) and fold
    (c:141-148; 2 sites: c:219, 229).

    As compiled:
    - Entry 0x13fb4-0x14040: s2 = text, s0 = c, s1 = c + 0x2000; snprintf(c->reading, 96, "%s" (0x104e0),
      label ? label : "reac-pw.conf" (seg_spec.STR_BASE)) (`jal snprintf` 0x14028; 0x18(sp) = &c->reading);
      c->gen++ (`lw`/`addi`/`sw` c + 0x23b0, 0x1402c-0x14038; 0x10(sp) = c + 0x2000); *text = 0 (`beqz` 0x14040)
      goes to the epilogue 0x1474c; else the loop set-up 0x14044-0x14078: cur = NULL (0x20(sp)), line = 0 (s3),
      the constants s1 = ';', s7 = '\t', s8 = 511, s9 = the blank mask 2^32 + 2^13 + 2^9 (' ', '\r', '\t': `srl` +
      `andi 1` after `bltu 0x20`), s10 = '#', s11 = ' ', and 8(sp) = &c->kept_knock[0] (c + 0x238c).
    - Line-loop head 0x1407c (H_MF_HEAD below): s5 = p; nl = strchr(p, '\n') (`jal strchr` 0x14088, s4); e = nl or
      p + strlen(p) (`jal strlen` 0x1409c); the next p = nl + 1 or e (s2, 0x140a4-0x140ac); line++ (`addiw` 0x140b4);
      e - p > 511 (`bge s8` 0x140b8) is the long line: the blank skip 0x140bc-0x140dc and, when the first non-blank
      is '[', cur = NULL (0x143b0-0x143c4), then the shared m_refuse 0x143d0; else the comment cut 0x140e0-0x14118
      (q[-1] read only for q > s), strip 0x1411c-0x14170, s = e goes to the tail, '[' (0x14184) to m_header 0x14188,
      else m_key 0x14200. Every line ends at the tail 0x143d4 (H_MF_TAIL): `lbu *p`, `bnez` back to the head, else
      the epilogue 0x1474c (H_MF_EXIT).
    - m_header: memchr(s, ']', e - s) 0x14190; no ']' or close + 1 <> e refuses (0x1463c/0x14644, cur = NULL);
      strip of [s + 1, close) 0x141a4-0x141fc; be - b < 8, ieq(b, 7, "segment") (0x14400) = 0 or b[7] not ' '/'\t'
      refuses (0x144c8); strip of [b + 7, be) 0x14414-0x14474; n = 0 or n >= 16 refuses (0x1463c); g = m_find(c, nm,
      n) (0x14494); found: g->gen = c->gen refuses (0x144b8) and then g->gen = c->gen (0x14720); not found: c->n >= 32
      gives overflow++ (0x14630-0x14638) and a refusal (0x14644); else g = &c->seg[c->n++] (0x146e0-0x146ec),
      memset(g, 0, 256) (0x146fc), memcpy(g->name, nm, n) (0x14710), g->gen = c->gen; cur = g (0x1449c / 0x14700).
    - m_key: eq = memchr(s, '=', e - s) (0x14208); cur = NULL or no '=' refuses (0x143d0); strip of the key and of
      the value 0x14218-0x142b4, the quote pair 0x142b8-0x142ec; ieq(k, kn, "role") (0x14308): the inline fold into
      low = sp + 0x28 (cap 64, 0x14310-0x1435c), the five words (m_key.words, M_KEY_WORDS below: strlen 0x14374,
      bcmp(words[i], low, ln) 0x14388), the hit sets role = m_key.role[i] (.rodata 0x10a10), role_set = 1 and
      snprintf(g->role_file, 96, "%s", c->reading) (0x14590), a miss refuses (0x143a8); "model" (ieq 0x144e4): fold
      cap 24 (0x144ec-0x14534), fuzz_catalogue_row(low, ln) (0x14540): NULL refuses (0x14744), else memcpy(g->model,
      low, ln + 1) (0x14558), model_set = 1; "ignore" (ieq 0x145b0): ieq "yes" 0x145c8, "true" 0x14660, "1",
      "no" 0x14690, "false" 0x146a8, "0", else a refusal (0x14744); a hit sets ignore, ignore_set = 1 and
      snprintf(g->ignore_file, 96, "%s", c->reading) (0x146d8); "knock" (ieq 0x145ec): n_kept <= 7 (`blt` 0x14608)
      stores kept_knock[n_kept] = 1 (0x1461c), then the refusal 0x143d0 (knock = true); any other key refuses
      (0x143a8).
    It reads the text (strchr, strlen, memchr, ieq, m_find, memcpy(g->name, nm) and its own loads, each inside [p,
    the text's NUL + slack)), the label (snprintf's %s), the mconf block, the 40-byte words table in .data.rel.ro
    (not fixed by mem_inv: words_img), the role table and the string literals in .rodata, and the box-model table
    (fuzz_catalogue_row: cat_img).
    It writes its frame and the callees' frames below sp ([sp - M_FILE_STACK, sp): m_refuse is the deepest) and in
    the mconf block at most M_FILE_W: seg[0 .. n') (n' the final n: memset/memcpy of a new entry, gen, role,
    role_set, role_file, model, model_set, ignore, ignore_set, ignore_file of any entry), n, overflow, refused,
    kept[k0 .. k1) and kept_knock[k0 .. k1) (k0, k1 the entry and final n_kept: m_refuse's slot and the knock flag),
    n_kept, gen, reading. The text is never written.

    Post in the spine's terms: the block holds SegModel.m_file mc s lab (seg_spec.mconf_at); void, a printer, so
    seg_env.ret_void_fp. The bounds the UBSan build's traps need come out of the post: mconf_enc gives n <= 32,
    n_kept <= 8, every name NUL-free and at most 15 bytes; the model lemmas at the end of this file give the counters
    (m_file_gen: gen' = gen + 1; m_file_refused / m_file_overflow: at most one more per byte of text), so a caller
    meets the next call's premise; the line bound (line + the bytes left <= 65535) is the loop invariant's.

    Callee contracts its walk takes as premises: snprintf_contract (Prog/snprintf_c.v, SNPRINTF = 0x19078; the "%s" format
    in .rodata, the %s argument NUL-free with its slack and apart from the stack and from the destination, the
    96-byte destination writable, printf_env); strchr_contract (Prog/strchr_c.v, STRCHR = 0x1eadc, 32 bytes
    of stack); strlen_contract (Prog/strlen_c.v, STRLEN = 0x1ec30); memchr_contract (Prog/memchr_c.v, MEMCHR =
    0x1e430); bcmp_contract (Prog/bcmp_c.v, BCMP = 0x1e42c); memcpy_contract (Prog/memcpy_c.v, 0x1e52c);
    memset_contract (Prog/memset_c.v, 0x1e930); fuzz_catalogue_row_contract (Prog/fuzz_catalogue_row_c.v, 0x15d64,
    FCR_STACK 48: cat_img); ieq_contract (IEQ = 0x14c2c, IEQ_STACK 32), m_find_contract (M_FIND = 0x149dc,
    M_FIND_STACK 48) and m_refuse_contract (M_REFUSE = 0x14b8c, M_REFUSE_STACK = 16 + PRINTF_K) of
    commit 66de2e2eba42 (Prog/ieq_c.v, m_find_c.v, m_refuse_c.v). Why each holds at its site:
    the text pointers lie in [p, the text's NUL] of the text block (cstr_at, apart from the stack and from c), the
    stack is the region [lo, sp) with M_FILE_STACK - M_FILE_FRAME = M_REFUSE_STACK bytes below the frame, c is the
    16-aligned writable block above the image (mconf_at, wr_at, blk_slack: c->reading, printf's %s, ends at the
    block's end), the line number is in [1, 65535] and refused + 1 < 2^32 (the loop invariant), knock = true only
    at the knock branch (mconf_atp true after its store). A callee whose post munches (lo, its sp) (snprintf's
    printf_post) is instantiated with lo := its sp - its stack, so its writes lie in [sp0 - M_FILE_STACK, sp0).

    Call sites: LLVMFuzzerTestOneInput 0x13a04 (c:612, a drop-in turn: a0 = s0 = m, a1 = s7 = text, a2 = s9 = NULL,
    main's label[40] buffer or longl) and 0x13a34 (c:615, the last turn: a2 = 0). At each: m = calloc(1, 9236)
    (16-aligned, above the image, writable, slack) holding the model state after the earlier turns (seg_spec.seg_run:
    gen = the number of turns run, at most 3, refused and overflow at most 65535 per turn); the text = fuzz_str's
    malloc block, a C string of at most 65535 bytes; the label a C string of at most 120 bytes or NULL. *)
Definition M_FILE : Z := 0x13fb4.
Definition M_FILE_FRAME : Z := 0xd0.
(** The saved registers: s11 at sp + M_FILE_SAVE, then s10, ..., s0, ra at sp + 0xc8. *)
Definition M_FILE_SAVE : Z := 0x68.
(** Its frame and m_refuse's need below it (m_refuse_c.v's M_REFUSE_STACK = 16 + PRINTF_K, the deepest callee: snprintf
    needs PRINTF_K, m_find 48, ieq 32, strchr 32, fuzz_catalogue_row 48, the others none). *)
Definition M_FILE_STACK : Z := M_FILE_FRAME + (16 + PRINTF_K).
Definition M_FILE_HEAD : Z := 0x1407c.
Definition M_FILE_TAIL : Z := 0x143d4.
Definition M_FILE_EXIT : Z := 0x1474c.
(** m_key's static `words[]` (fuzz_segconf.c:214): five pointers in .data.rel.ro (symbol m_key.words, 40 bytes);
    m_key.role, the five enum values, is in .rodata. *)
Definition M_KEY_WORDS : Z := 0x20aa8.
Definition M_KEY_ROLE : Z := 0x10a10.
(** The blank set as the loop's shift mask: bits 9 ('\t'), 13 ('\r') and 32 (' '). *)
Definition BLANK_MASK : Z := 0x100002200.

(** The words table reads as in the image (.data.rel.ro: FR's relro gives it, as for cat_img). *)
Definition words_img (m : word -> option byte) : Prop :=
  forall a, M_KEY_WORDS <= a < M_KEY_WORDS + 40 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a).

(** The bytes m_file may write: the frames, seg[0 .. n'), n / overflow / refused, kept[k0 .. k1),
    kept_knock[k0 .. k1), n_kept / gen / reading (k0 the entry n_kept; n', k1 of the final state mc'). *)
Definition M_FILE_W (sp c : Z) (k0 : nat) (mc' : mconf) : list ivl :=
  [(sp - M_FILE_STACK, sp);
   (c, mseg_addr c (length (mc_seg mc')));
   (c + MC_N, c + MC_REFUSED + 4);
   (kept_addr c k0, kept_addr c (length (mc_kept mc')));
   (c + MC_KNOCK + 4 * Z.of_nat k0, c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc')));
   (c + MC_NKEPT, c + MC_READING + 96)].

Definition m_file_pre (m : word -> option byte) (fc : bv 32) (sp lo c t lp : Z) (mc : mconf) (s : list Z)
    (lab : option (list Z)) : Prop :=
  c <> 0 /\ c mod 16 = 0 /\ blk_noimg rsegs c SEG_M_SIZE /\
  mconf_at rsegs m c mc /\ wr_at rsegs m c SEG_M_SIZE /\ blk_slack rsegs m c SEG_M_SIZE /\
  apart c (SEG_M_SIZE + 4) lo sp /\
  mc_gen mc + 1 < 2 ^ 31 /\ mc_refused mc + 2 ^ 17 < 2 ^ 32 /\ mc_overflow mc + 2 ^ 17 < 2 ^ 32 /\
  t <> 0 /\ blk_noimg rsegs t (Z.of_nat (length s) + 1) /\ cstr_at rsegs m t s /\ (length s <= 65535)%nat /\
  apart t (Z.of_nat (length s) + 8) lo sp /\ apart t (cstr_span t s) c (c + SEG_M_SIZE) /\
  ocstr_at rsegs m lp lab /\
  (match lab with
   | Some l => Z.of_nat (length l) < 2 ^ 31 - 1 /\
               apart lp (Z.of_nat (length l) + 8) lo sp /\
               apart lp (Z.of_nat (length l) + 8) (c + MC_READING) (c + MC_READING + 96)
   | None => True
   end) /\
  printf_env m fc lo sp /\ cat_img rsegs m (sa_catalogue SA) /\ words_img m /\
  stack_ok rsegs m lo sp M_FILE_STACK /\ mem_inv rsegs m.

Definition m_file_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (mc : mconf) (s : list Z)
         (lab : option (list Z)),
    m_file_pre m fc (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) mc s lab ->
    evt rsegs
      (ret_void_fp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
         m
         (M_FILE_W (bv_unsigned sp) (bv_unsigned a0) (length (mc_kept mc)) (m_file mc s lab))
         lo
         (fun m' => mconf_at rsegs m' (bv_unsigned a0) (m_file mc s lab)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 M_FILE) fc None m (seg_rom rsegs)).

(** ** The cuts (family F3's shape: one Prop per cut, H_<cut>; one per piece, S_<piece> := H_exits -> H_entry)

    The loop state at the head and at the tail: (mc, cur) = SegModel's state after the [line] lines consumed so
    far, [p] = the address of the rest of the text [rest] (a C string), [k0] = n_kept at entry (it fixes M_FILE_W),
    sp0 = the entry sp, ra0 and e0 .. e11 = the entry ra and s0 .. s11, saved in the frame. The post is the function's
    post computed from that state: the final model is fst (m_lines (mc, cur) line (lines rest)). *)

(** The cur cell 0x20(sp): &c->seg[i] for Some i, NULL for None. *)
Definition cur_ptr (c : Z) (cur : option nat) : Z := match cur with Some i => mseg_addr c i | None => 0 end.
Definition cur_ok (mc : mconf) (cur : option nat) : Prop :=
  match cur with Some i => (i < length (mc_seg mc))%nat | None => True end.
(** An 8-byte frame cell holding v. *)
Definition cell8 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le8 (Z_to_bv 64 v)).

(** The facts the head and the tail share. The counters' bounds shrink with the text left: each line refuses at most
    once and adds at most one overflow, and consumes at least one byte. *)
Definition m_file_loop (m : word -> option byte) (fc : bv 32) (sp0 sp lo c p : Z) (mc : mconf)
    (cur : option nat) (line : Z) (k0 : nat) (rest : list Z)
    (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) : Prop :=
  sp + M_FILE_FRAME = sp0 /\
  saved_at rsegs m (sp + M_FILE_SAVE) [e11; e10; e9; e8; e7; e6; e5; e4; e3; e2; e1; e0; ra0] /\
  cell8 m (sp + 0x8) (c + MC_KNOCK) /\ cell8 m (sp + 0x10) (c + MC_N) /\ cell8 m (sp + 0x18) (c + MC_READING) /\
  cell8 m (sp + 0x20) (cur_ptr c cur) /\
  c <> 0 /\ c mod 16 = 0 /\ blk_noimg rsegs c SEG_M_SIZE /\
  mconf_at rsegs m c mc /\ wr_at rsegs m c SEG_M_SIZE /\ blk_slack rsegs m c SEG_M_SIZE /\
  apart c (SEG_M_SIZE + 4) lo sp0 /\
  cur_ok mc cur /\ (k0 <= length (mc_kept mc))%nat /\
  0 <= line /\ line + Z.of_nat (length rest) <= 65535 /\
  mc_refused mc + Z.of_nat (length rest) < 2 ^ 32 /\ mc_overflow mc + Z.of_nat (length rest) < 2 ^ 32 /\
  p <> 0 /\ blk_noimg rsegs p (Z.of_nat (length rest) + 1) /\ cstr_at rsegs m p rest /\
  apart p (Z.of_nat (length rest) + 8) lo sp0 /\ apart p (cstr_span p rest) c (c + SEG_M_SIZE) /\
  printf_env m fc lo sp0 /\ cat_img rsegs m (sa_catalogue SA) /\ words_img m /\
  stack_ok rsegs m lo sp0 M_FILE_STACK /\ mem_inv rsegs m.

(** The registers the loop keeps: s0 = c, s2 = p, s3 = line, and the constants s1 = ';', s7 = '\t', s8 = 511,
    s9 = BLANK_MASK, s10 = '#', s11 = ' ' (s4, s5, s6 and the a/t registers are scratch). *)
Definition m_file_regs (c p line : Z) (s0 s1 s2 s3 s7 s8 s9 s10 s11 : word) : Prop :=
  s0 = Z_to_bv 64 c /\ s1 = Z_to_bv 64 0x3b /\ s2 = Z_to_bv 64 p /\ s3 = Z_to_bv 64 line /\
  s7 = Z_to_bv 64 9 /\ s8 = Z_to_bv 64 0x1ff /\ s9 = Z_to_bv 64 BLANK_MASK /\ s10 = Z_to_bv 64 0x23 /\
  s11 = Z_to_bv 64 0x20.

(** H_MF_HEAD n: the line-loop invariant at the head 0x1407c (both entries: the set-up's fall-through 0x14078 and the
    tail's `bnez` 0x143d8), for the text left shorter than n bytes (the measure of the loop's induction), nonempty (the
    entry test and the tail test read *p <> 0). *)
Definition H_MF_HEAD (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z),
    (length rest < n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    m_file_regs c p line s0 s1 s2 s3 s7 s8 s9 s10 s11 ->
    evt rsegs
      (ret_void_fp ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F
         m
         (M_FILE_W (bv_unsigned sp0) c k0 (fst (m_lines (mc, cur) line (lines rest))))
         lo
         (fun m' => mconf_at rsegs m' c (fst (m_lines (mc, cur) line (lines rest)))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 M_FILE_HEAD) fc None m (seg_rom rsegs)).

(** H_MF_TAIL n: the tail 0x143d4 every line joins (0x14174, 0x143d0, 0x1459c, 0x1464c, 0x14724), after line [line]
    with the state (mc, cur) = SegModel.m_line of it and [rest] the text after it (possibly empty). *)
Definition H_MF_TAIL (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z),
    (length rest < n)%nat ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    m_file_regs c p line s0 s1 s2 s3 s7 s8 s9 s10 s11 ->
    evt rsegs
      (ret_void_fp ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F
         m
         (M_FILE_W (bv_unsigned sp0) c k0 (fst (m_lines (mc, cur) line (lines rest))))
         lo
         (fun m' => mconf_at rsegs m' c (fst (m_lines (mc, cur) line (lines rest)))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 M_FILE_TAIL) fc None m (seg_rom rsegs)).

(** H_MF_EXIT: the epilogue 0x1474c (from the entry's empty-text test 0x14040 and the tail 0x143dc): it restores
    ra0, e0 .. e11 from the frame and sp0 = sp + 0xd0, writes nothing, and returns; any W and any Q of the memory
    it starts from. *)
Definition H_MF_EXIT : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (W : list ivl) (Q : (word -> option byte) -> Prop),
    bv_unsigned sp + M_FILE_FRAME = bv_unsigned sp0 ->
    saved_at rsegs m (bv_unsigned sp + M_FILE_SAVE) [e11; e10; e9; e8; e7; e6; e5; e4; e3; e2; e1; e0; ra0] ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> stk rsegs m lo (bv_unsigned sp0) -> Q m ->
    evt rsegs
      (ret_void_fp ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m W lo Q)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 M_FILE_EXIT) fc None m (seg_rom rsegs)).

(** The pieces.
    - S_MF_ENTRY, 0x13fb4-0x1407c (prologue, the reading snprintf, gen++, the set-up): to the head with
      (MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc) (mc_kept mc) (mc_gen mc + 1) rd, None), line 0, p = text,
      rest = s, k0 = length (mc_kept mc), or (s = []) to the exit with that state.
    - S_MF_LINE, 0x1407c-0x143d4 (one line: split, the long line, the comment cut, strip, m_header, m_key): from the
      head with rest to the tail with (m_line (mc, cur) (line + 1) l), line + 1 and rest' (l, rest' = break_nl rest),
      so the text left shrinks by |l| + 1 or |l| >= 1 bytes. A prover may cut it further at the dispatch 0x14188 (header)
      / 0x14200 (key), where s5 = s, s6 = e and a2 = e - s hold the stripped line.
    - S_MF_TAIL, 0x143d4-0x143dc: *p <> 0 back to the head (same state), else (rest = []) to the exit.
    - S_MF_EXIT, 0x1474c-0x14784: the epilogue. *)
Definition S_MF_ENTRY : Prop := (forall n, H_MF_HEAD n) -> H_MF_EXIT -> m_file_contract.
Definition S_MF_LINE : Prop := forall n, H_MF_TAIL n -> H_MF_HEAD (S n).
Definition S_MF_TAIL : Prop := forall n, H_MF_HEAD n -> H_MF_EXIT -> H_MF_TAIL n.
Definition S_MF_EXIT : Prop := H_MF_EXIT.
(** The whole contract from the pieces (an induction on n; statement only). *)
Definition m_file_pieces_give_contract : Prop := S_MF_EXIT -> S_MF_TAIL -> S_MF_LINE -> S_MF_ENTRY -> m_file_contract.

(** ** The model's counters (build-independent; the UBSan twin lib/U/Prog/m_file_c.v uses these)
    gen goes up by one per call, refused and overflow by at most one per line, hence by at most the text's length:
    with m = calloc's zeros and at most 4 calls, a caller meets m_file_pre's gen, refused and overflow bounds. *)
Lemma m_header_cnt m l n :
  mc_gen (fst (m_header m l n)) = mc_gen m /\
  mc_refused m <= mc_refused (fst (m_header m l n)) <= mc_refused m + 1 /\
  mc_overflow m <= mc_overflow (fst (m_header m l n)) <= mc_overflow m + 1.
Proof.
  unfold m_header. cbv zeta. destruct (memchr l RBR) as [ci|]; [|cbn; lia].
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         | |- context [m_find ?a ?b] => destruct (m_find a b)
         end; cbn; lia.
Qed.

Lemma m_key_cnt m g l n :
  mc_gen (m_key m g l n) = mc_gen m /\
  mc_refused m <= mc_refused (m_key m g l n) <= mc_refused m + 1 /\
  mc_overflow (m_key m g l n) = mc_overflow m.
Proof.
  unfold m_key. cbv zeta. destruct (memchr l EQ); [|cbn; lia]. destruct g; [|cbn; lia].
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         | |- context [h_role_word ?a] => destruct (h_role_word a)
         | |- context [cat_row ?a] => destruct (cat_row a)
         end; cbn; lia.
Qed.

Lemma m_line_cnt st n l :
  mc_gen (fst (m_line st n l)) = mc_gen (fst st) /\
  mc_refused (fst st) <= mc_refused (fst (m_line st n l)) <= mc_refused (fst st) + 1 /\
  mc_overflow (fst st) <= mc_overflow (fst (m_line st n l)) <= mc_overflow (fst st) + 1.
Proof.
  destruct st as [m cur]. unfold m_line. destruct (512 <=? length l)%nat; [cbn; lia|].
  destruct (h_strip (h_cut_comment l)) as [|b s]; [cbn; lia|].
  destruct (b =? LBR); cbn [fst]; [apply m_header_cnt|].
  pose proof (m_key_cnt m cur (b :: s) n) as H. lia.
Qed.

Lemma m_lines_cnt ls : forall st n,
  mc_gen (fst (m_lines st n ls)) = mc_gen (fst st) /\
  mc_refused (fst st) <= mc_refused (fst (m_lines st n ls)) <= mc_refused (fst st) + Z.of_nat (length ls) /\
  mc_overflow (fst st) <= mc_overflow (fst (m_lines st n ls)) <= mc_overflow (fst st) + Z.of_nat (length ls).
Proof.
  induction ls as [|l r IH]; intros st n; cbn [m_lines length]; [lia|].
  pose proof (m_line_cnt st (n + 1) l) as H1. pose proof (IH (m_line st (n + 1) l) (n + 1)) as H2. lia.
Qed.

Lemma m_file_gen mc s lab : mc_gen (m_file mc s lab) = mc_gen mc + 1.
Proof. unfold m_file. cbv zeta. exact (proj1 (m_lines_cnt _ _ _)). Qed.

Lemma m_file_refused mc s lab : nulfree s ->
  mc_refused mc <= mc_refused (m_file mc s lab) <= mc_refused mc + Z.of_nat (length s).
Proof.
  intros Hn. pose proof (lines_props s Hn) as [_ Hl]. unfold m_file. cbv zeta.
  match goal with |- context [m_lines ?st ?n ?ls] => pose proof (m_lines_cnt ls st n) as H end.
  cbn [fst mc_refused] in H. lia.
Qed.

Lemma m_file_overflow mc s lab : nulfree s ->
  mc_overflow mc <= mc_overflow (m_file mc s lab) <= mc_overflow mc + Z.of_nat (length s).
Proof.
  intros Hn. pose proof (lines_props s Hn) as [_ Hl]. unfold m_file. cbv zeta.
  match goal with |- context [m_lines ?st ?n ?ls] => pose proof (m_lines_cnt ls st n) as H end.
  cbn [fst mc_overflow] in H. lia.
Qed.
