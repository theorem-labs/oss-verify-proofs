From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
Import ListNotations.
Open Scope Z_scope.

(** m_file(c, text, label) (fuzz_segconf.c:259-293, static void; at 0x14268 in the UBSan image 1696d6c34ffd, size
    1880; frame 0x110 = 272 bytes, `sd` of s11, s10, ..., s0, ra at
    sp + 0xa8, 0xb0, ..., 0x100, 0x108 (0x1426c-0x1429c), restored by the epilogue 0x14980-0x149b8; the one `unimp`
    0x149bc). It inlines m_header (c:159-194), m_key (c:197-257) and blank; strip (0x15028) and fold (0x151a4) are
    calls in this build (5 and 2 sites). The plain twin is lib/Prog/m_file_c.v;
    the model's counter lemmas (m_file_gen, m_file_refused, m_file_overflow) are there, build-independent.

    As compiled:
    - Entry 0x14268-0x142f8: s0 = c, c & 3 <> 0 traps (0x142a8); s2 = text, s8 = c + 0x2000; snprintf(c->reading,
      96, "%s" (0x104e0), label ? label : "reac-pw.conf") (`jal snprintf` 0x142e0; 0x20(sp) = &c->reading); c->gen++
      (`addiw`, the signed-overflow trap `blt` 0x142ec, `sw` 0x142f0); *text = 0 (`beqz` 0x142f8) goes to the
      epilogue 0x14980; else the set-up 0x142fc-0x14344: line = 0 (s3), cur = NULL (0x30(sp)), the constants s4 = 1,
      s6 = 511, s7 = '#', s9 = the blank mask, s10 = ' ', s11 = ';', and the cells 8(sp) = ~c, 0x10(sp) =
      &c->kept_knock[0] (c + 0x238c), 0x18(sp) = ~(c + 0x238c), 0x28(sp) = c + 0x2000.
    - Line-loop head 0x14348 (H_MF_HEAD below): s5 = p, s1 = line; nl = strchr(p, '\n') (0x14358); nl = -1 traps
      (0x1436c); e = nl or p + strlen(p) (0x1437c; the wrap trap 0x14384), kept at 0x38(sp), s = p at 0x40(sp); the next
      p = nl + 1 or e (s2); line++ (`addiw`, trap 0x14398); e - p > 511 (`bge s6` 0x143a0) is the long line (0x143a4-
      0x143c4 and 0x14690-0x146a4: cur = NULL when the first non-blank is '['), then m_refuse 0x146b0; else the
      comment cut 0x143c8-0x14404 (q = 1 traps at 0x143e0 before the q[-1] read, only for q > s), strip(&s, &e)
      (0x14410, cells sp + 0x40 / 0x38), s = e goes to the tail, s = NULL traps (0x14420), '[' to m_header 0x14434,
      else m_key 0x14528. Every line ends at the tail 0x146b4 (H_MF_TAIL): `lbu *p`, `bnez` back to the head, else
      the epilogue 0x14980 (H_MF_EXIT).
    - m_header: memchr(s, ']', e - s) (0x1443c; close = -1 traps 0x14448); close + 1 <> e or no ']' refuses
      (0x14670, cur = NULL); s = -1 traps (0x14458); strip(&b, &be) (0x14470, cells sp + 0x48 / 0xa0); be - b < 8,
      ieq(b, 7, "segment") (0x14494) = 0, the b + 7 wrap trap (0x144a8), b[7] not ' '/'\t' refuse (0x14670);
      strip(&nm, &ne) (0x144d0, cells sp + 0x98 / 0x90); n = 0 or n >= 16 refuses; g = m_find(c, nm, n) (0x144f4;
      g & 3 traps 0x14504); found: g->gen = c->gen refuses (0x14520); not found: c->n >= 32 gives overflow++
      (0x148e0-0x148e8) and a refusal (0x148f4); else c->n++ (0x14904), the seg[n] bound trap (0x1490c: n >= 33
      unsigned), the m + 256 n wrap trap (0x14918), memset(g, 0, 256) (0x1492c), memcpy(g->name, nm, n) (0x14940);
      g->gen = c->gen (g & 3 trap 0x14950, `sw` 0x14958); cur = g (0x30(sp): 0x14508 / 0x14934).
    - m_key: eq = memchr(s, '=', e - s) (0x14530); cur = NULL or no '=' refuses (0x14684); eq = -1 traps (0x1454c);
      strip(&k, &ke) (0x14564, cells sp + 0xa0 / 0x98) and strip(&v, &ve) (0x14570, cells sp + 0x90 / 0x88); the
      quote pair 0x14574-0x145c4 (v = NULL 0x14588, ve < 2 0x145a4, v = -1 0x145b4 trap); ieq(k, kn, "role")
      (0x145e4): fold(v, vn, low = sp + 0x48, 64) (0x145fc), the five words (m_key.words, M_KEY_WORDS below: strlen
      0x14620, bcmp 0x14634), a miss refuses (0x14658); a hit (0x14730: the m_key.role[i] wrap trap 0x14748, g & 3
      0x14754) sets role and role_set and snprintf(g->role_file, 96, "%s", c->reading) (`jal snprintf` 0x148b8, the
      site role_file and ignore_file share); "model" (ieq 0x146d0): fold cap 24 (0x146e8), fuzz_catalogue_row(low, ln)
      (0x146f8): NULL refuses (0x147c4), else (g & 3 trap 0x1470c) memcpy(g->model, low, ln + 1) (0x14720) and
      model_set = 1; "ignore" (ieq 0x1478c): "yes" 0x147a4, "true" 0x14830, "1" (v NULL trap 0x14844), "no" 0x14864,
      "false" 0x1487c, "0" (trap 0x14968), else a refusal (0x146b0); a hit (g & 3 trap 0x14890) sets ignore,
      ignore_set = 1 and snprintf(g->ignore_file, ...) (0x148b8); "knock" (ieq 0x147dc): n_kept <= 7 (`blt` 0x147f4),
      the kept_knock bound trap (0x147fc: n_kept >= 8 unsigned) and wrap trap (0x14808), kept_knock[n_kept] = 1
      (0x14818), then the refusal 0x146b0 (knock = true); any other key refuses (0x148c8).
    It reads and writes what the plain build does (lib/Prog/m_file_c.v), plus strip's two pointer cells in its frame.

    The 26 trap sites and what makes each fall through: alignment c & 3 (0x142a8: c mod 16 =
    0) and g & 3 (0x14504 0x1470c 0x14754 0x14890 0x14950: g = c + 256 i, m_find's answer or the new entry); signed
    overflow gen++ (0x142ec: mc_gen mc + 1 < 2^31) and line++ (0x14398: line + the text left <= 65535, the loop
    invariant); NULL *s, *v (0x14420 0x14588 0x14844 0x14968: the pointers lie in the text block, above the image);
    bounds kept_knock[n_kept] (0x147fc: n_kept <= 8 by mconf_enc and <= 7 on that path) and seg[c->n] (0x1490c:
    n <= 32 by mconf_enc and < 32 on that path); pointer overflow (a wrap or a NULL result) nl + 1, p + strlen,
    q - 1, close + 1, s + 1, b + 7, eq + 1, ve - 1, v + 1 (0x1436c 0x14384 0x143e0 0x14448 0x14458 0x144a8 0x1454c
    0x145a4 0x145b4: the text's bytes lie in (0, 2^64) by t <> 0 and cstr_at / bytes_at, with its NUL),
    m_key.role + 4 i (0x14748: .rodata),
    &kept_knock[n] (0x14808) and m + 256 n (0x14918: the block [c, c + 9236) by mconf_at).

    Post in the spine's terms: the block holds SegModel.m_file mc s lab; void, a printer: seg_env.ret_void_fp. The
    bounds the traps of the next call and of main need come out of it as in the plain build (mconf_enc; the counter
    lemmas of lib/Prog/m_file_c.v; the line bound is the invariant's).

    Callee contracts its walk takes as premises (this build's entries): snprintf_contract
    (lib/U/Prog/snprintf_c.v, SNPRINTF = 0x19a14);
    strchr_contract (lib/U/Prog/strchr_c.v, STRCHR = 0x1f478); strlen_contract (0x1f5cc), memchr_contract
    (0x1edcc), bcmp_contract (0x1edc8), memcpy_contract (0x1eec8), memset_contract (0x1f2cc),
    fuzz_catalogue_row_contract (0x166f4; cat_img) of lib/U/Prog; ieq_contract (IEQ = 0x150d8, IEQ_STACK 32),
    m_find_contract (M_FIND = 0x14ccc, M_FIND_STACK 64), m_refuse_contract (M_REFUSE = 0x14f30, M_REFUSE_STACK =
    16 + PRINTF_K), strip_contract (lib/U/Prog/strip_c.v, STRIP = 0x15028, no stack; strip_pre's two 8-aligned
    cells in this frame, strip_mid: the bytes between the new pointers are SegModel.h_strip) and fold_contract
    (lib/U/Prog/fold_c.v, FOLD = 0x151a4, no stack; fold_out l cap = h_fold, out = low, cap 64 or 24) of
    commit 66de2e2eba42. Why each holds at its site: as in the plain build.

    Call sites: LLVMFuzzerTestOneInput 0x13b3c (c:612: a0 = 0x50(sp) = m, a1 = s7 = text, a2 = s9 = NULL, main's
    label[40] buffer or longl) and 0x13b7c (c:615: a2 = 0); the premises hold there as in the plain build. *)
Definition M_FILE : Z := 0x14268.
Definition M_FILE_FRAME : Z := 0x110.
(** The saved registers: s11 at sp + M_FILE_SAVE, then s10, ..., s0, ra at sp + 0x108. *)
Definition M_FILE_SAVE : Z := 0xa8.
(** Its frame and m_refuse's need below it (m_refuse_c.v's M_REFUSE_STACK = 16 + PRINTF_K, the deepest callee: snprintf
    needs PRINTF_K, m_find 64, ieq 32, strchr 32, fuzz_catalogue_row 48, strip, fold and the others none). *)
Definition M_FILE_STACK : Z := M_FILE_FRAME + (16 + PRINTF_K).
Definition M_FILE_HEAD : Z := 0x14348.
Definition M_FILE_TAIL : Z := 0x146b4.
Definition M_FILE_EXIT : Z := 0x14980.
(** m_key's static `words[]`: five pointers in .data.rel.ro (symbol m_key.words, 40 bytes); m_key.role in .rodata. *)
Definition M_KEY_WORDS : Z := 0x21440.
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

(** The cur cell 0x30(sp): &c->seg[i] for Some i, NULL for None. *)
Definition cur_ptr (c : Z) (cur : option nat) : Z := match cur with Some i => mseg_addr c i | None => 0 end.
Definition cur_ok (mc : mconf) (cur : option nat) : Prop :=
  match cur with Some i => (i < length (mc_seg mc))%nat | None => True end.
(** An 8-byte frame cell holding v. *)
Definition cell8 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le8 (Z_to_bv 64 v)).

(** The facts the head and the tail share. The counters' bounds shrink with the text left: each line refuses at most
    once and adds at most one overflow, and consumes at least one byte. The cells 8(sp) and 0x18(sp) hold the
    complements the wrap checks compare against (-1 - c = ~c as a 64-bit word). *)
Definition m_file_loop (m : word -> option byte) (fc : bv 32) (sp0 sp lo c p : Z) (mc : mconf)
    (cur : option nat) (line : Z) (k0 : nat) (rest : list Z)
    (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) : Prop :=
  sp + M_FILE_FRAME = sp0 /\
  saved_at rsegs m (sp + M_FILE_SAVE) [e11; e10; e9; e8; e7; e6; e5; e4; e3; e2; e1; e0; ra0] /\
  cell8 m (sp + 0x8) (- 1 - c) /\ cell8 m (sp + 0x10) (c + MC_KNOCK) /\ cell8 m (sp + 0x18) (- 1 - (c + MC_KNOCK)) /\
  cell8 m (sp + 0x20) (c + MC_READING) /\ cell8 m (sp + 0x28) (c + MC_N) /\ cell8 m (sp + 0x30) (cur_ptr c cur) /\
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

(** The registers the loop keeps: s0 = c, s2 = p, s3 = line, s8 = c + 0x2000, and the constants s4 = 1 (the q = 1
    check), s6 = 511, s7 = '#', s9 = BLANK_MASK, s10 = ' ', s11 = ';' (s1, s5 and the a/t registers are scratch). *)
Definition m_file_regs (c p line : Z) (s0 s2 s3 s4 s6 s7 s8 s9 s10 s11 : word) : Prop :=
  s0 = Z_to_bv 64 c /\ s2 = Z_to_bv 64 p /\ s3 = Z_to_bv 64 line /\ s4 = Z_to_bv 64 1 /\
  s6 = Z_to_bv 64 0x1ff /\ s7 = Z_to_bv 64 0x23 /\ s8 = Z_to_bv 64 (c + MC_N) /\ s9 = Z_to_bv 64 BLANK_MASK /\
  s10 = Z_to_bv 64 0x20 /\ s11 = Z_to_bv 64 0x3b.

(** H_MF_HEAD n: the line-loop invariant at the head 0x14348 (both entries: the set-up's fall-through 0x14344 and the
    tail's `bnez` 0x146b8), for the text left shorter than n bytes (the measure of the loop's induction), nonempty (the
    entry test and the tail test read *p <> 0). *)
Definition H_MF_HEAD (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z),
    (length rest < n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    m_file_regs c p line s0 s2 s3 s4 s6 s7 s8 s9 s10 s11 ->
    evt rsegs
      (ret_void_fp ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F
         m
         (M_FILE_W (bv_unsigned sp0) c k0 (fst (m_lines (mc, cur) line (lines rest))))
         lo
         (fun m' => mconf_at rsegs m' c (fst (m_lines (mc, cur) line (lines rest)))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 M_FILE_HEAD) fc None m (seg_rom rsegs)).

(** H_MF_TAIL n: the tail 0x146b4 every line joins (0x1468c, 0x146b0, 0x1472c, 0x148bc, 0x148d0, 0x148fc,
    0x1495c), after line [line] with the state (mc, cur) = SegModel.m_line of it and [rest] the text after it
    (possibly empty). *)
Definition H_MF_TAIL (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z),
    (length rest < n)%nat ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    m_file_regs c p line s0 s2 s3 s4 s6 s7 s8 s9 s10 s11 ->
    evt rsegs
      (ret_void_fp ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F
         m
         (M_FILE_W (bv_unsigned sp0) c k0 (fst (m_lines (mc, cur) line (lines rest))))
         lo
         (fun m' => mconf_at rsegs m' c (fst (m_lines (mc, cur) line (lines rest)))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 M_FILE_TAIL) fc None m (seg_rom rsegs)).

(** H_MF_EXIT: the epilogue 0x14980 (from the entry's empty-text test 0x142f8 and the tail 0x146bc): it restores
    ra0, e0 .. e11 from the frame and sp0 = sp + 0x110, writes nothing, and returns; any W and any Q of the memory
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
    - S_MF_ENTRY, 0x14268-0x14348 (prologue, the reading snprintf, gen++, the set-up): to the head with
      (MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc) (mc_kept mc) (mc_gen mc + 1) rd, None), line 0, p = text,
      rest = s, k0 = length (mc_kept mc), or (s = []) to the exit with that state.
    - S_MF_LINE, 0x14348-0x146b4 (one line: split, the long line, the comment cut, strip, m_header, m_key): from the
      head with rest to the tail with (m_line (mc, cur) (line + 1) l), line + 1 and rest' (l, rest' = break_nl rest).
      A prover may cut it further at the dispatch 0x14434 (header) / 0x14528 (key), where s5 = s, s4 = e (and the
      cells 0x40(sp) = s, 0x38(sp) = e) and a2 = e - s hold the stripped line.
    - S_MF_TAIL, 0x146b4-0x146bc: *p <> 0 back to the head (same state), else (rest = []) to the exit.
    - S_MF_EXIT, 0x14980-0x149b8: the epilogue. *)
Definition S_MF_ENTRY : Prop := (forall n, H_MF_HEAD n) -> H_MF_EXIT -> m_file_contract.
Definition S_MF_LINE : Prop := forall n, H_MF_TAIL n -> H_MF_HEAD (S n).
Definition S_MF_TAIL : Prop := forall n, H_MF_HEAD n -> H_MF_EXIT -> H_MF_TAIL n.
Definition S_MF_EXIT : Prop := H_MF_EXIT.
(** The whole contract from the pieces (an induction on n; statement only). *)
Definition m_file_pieces_give_contract : Prop := S_MF_EXIT -> S_MF_TAIL -> S_MF_LINE -> S_MF_ENTRY -> m_file_contract.
