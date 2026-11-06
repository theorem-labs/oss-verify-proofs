(* m_file (fuzz_segconf.c:259-293, static void; it inlines m_header c:159-194, m_key c:197-257, blank c:113-116,
   strip c:119-125 and fold c:141-148; fuzz_segconf.asan 0x85ebc, 4,496 bytes, 1,124 instructions; frame 288 bytes
   realigned down to 32 (`andi sp,sp,-32` at 0x85efc, frame pointer s0 = the entry sp), a class-1 side-stack frame
   of 128 bytes (`__asan_stack_malloc_1` with a0 = 0x80 at 0x85f30, descriptor "1 32 64 9 low.i:212" at 0x1d8f6:
   the 64-byte buffer low.i at frame + 32), 43 inline checks, 32 calls): the contract of the ASan build's code, in
   plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr of apost_baseF at the return).
   Drafted by the G2 walk lane at commit 66967dd64303; this is the text of
   record, committed by the image-A contracts lane with the corrections its commit lists (the parameter order;
   m_key.words / m_key.role and the image label pinned at every allocator state; STK_m_file's window).

   Functional content: the plain contract lib/Prog/m_file_c.v at 440d61eaa8c8 (m_file_pre :119-135, the
   post `mconf_at m' c (m_file mc s lab)` and the footprint M_FILE_W :111-117, the model's counters :266-331, the
   call sites :93-97), restated over the ASan reader rd = aview segs (w_H W) mem with SegABase's forms. The cut map
   of the ASan code is the G2 walk lane's MF-CUTS-A.md (sha256 8761669a9b3d); its pcs are cited below.

   What the code does (listing m_file.fuzz_segconf.asan.s, 0x85ebc-0x87048): the prologue saves ra, s0 .. s11 at
   sp0 - 8 .. sp0 - 104 and stores 0 at sp0 - 288; s1 = (sp0 - 288) & -32; reads the use-after-return option
   (the GOT word 0xa2aa8 -> 0xac000) and the shadow base (0xa2a50 -> 0xabff8); takes the class-1 side-stack frame
   (FB), writes its header (FB + 0 = 0x41b58ab3, FB + 8 = 0x1d8f6, FB + 16 = 0x85ebc) and poisons its 16 shadow bytes
   (0xf1 x 4, 0xf8 x 8, 0xf3 x 4); snprintf(c->reading, 96, "%s", label ? label : "reac-pw.conf") (0x86014);
   c->gen++ (0x86028-0x86048); *text = 0 goes to the release (0x86060); else the line loop (head 0x860d0, tail
   0x86cf8): strchr / strlen split the line (0x860d8, 0x860ec), a line longer than 511 bytes is refused (m_refuse
   0x861ec, cur = NULL when its first non-blank is '['), else the comment cut, the strip, and '[' to m_header
   (memchr ']' 0x862d4, ieq "segment" 0x864b0, m_find 0x86ac8, the new entry's memset 0x86c2c / memcpy 0x86c44),
   any other first byte to m_key (memchr '=' 0x86344; low.i marked usable 0x86664-0x86680; ieq "role" / "model" /
   "ignore" / "knock"; the role words loop strlen 0x86760 / bcmp 0x86774; fuzz_catalogue_row 0x86878 and memcpy
   0x86890 into g->model; snprintf of c->reading into g->role_file 0x86934 / g->ignore_file 0x86a34; low.i marked
   unusable again 0x86cd4-0x86cf4). Every refusal is a call of m_refuse(c, line) (0x861ec, 0x863ac, 0x8653c,
   0x867a8, 0x86b14, 0x86bd4, 0x86bf4, 0x86ccc). The release 0x86e70-0x86ed0: FB + 0 = 0x45e0360e, the frame's
   shadow 0xf5, the flag byte (its address in the frame's last word) cleared, no `__asan_stack_free_1` call. The
   post is the plain one: the block holds SegModel.m_file mc s lab.
   What it reads: the text [t, t + |s|] and its slack (strchr, strlen, memchr, ieq, m_find, memcpy and its own
   byte loads), the label (snprintf's %s), the mconf block and the 4 bytes after it (snprintf's %s of c->reading
   reads to the next 8-byte boundary; plain blk_slack), the literals M_FILE_LITS, m_key.words (40 bytes, 5 pointers)
   and m_key.role (20 bytes), the box-model table (fuzz_catalogue_row), the shadow, and the GOT and option cells.
   What it writes: its own stack window (the saves, the probe word, the spill slots s1 + 24 .. s1 + 183) and its own
   side-stack frame with that frame's shadow; and in the mconf block at most M_FILE_FP: seg[0 .. n'), n, overflow,
   refused, kept[k0 .. k1), kept_knock[k0 .. k1), n_kept, gen, reading (n', k1 of the final model; k0 the entry
   n_kept). The text and the label are never written.

   ASAN FACTS ADDED over the plain contract:
   - the 43 inline checks (MF-CUTS-A.md section 4 lists each: shadow load pc, kind, address, error arm). The checks
     in the mconf block (load4 c->gen 0x86028, c->n 0x86b98, c->overflow 0x86bb4, store4 c->n 0x86c00, load4 c->gen
     0x86aec / 0x86c58, load4 / store4 g->gen 0x86ae0 / 0x86c70, store4 g->role 0x868e4, role_set 0x8690c,
     model_set 0x868a0, ignore 0x869f4, ignore_set 0x86a0c, load4 c->n_kept 0x86b44, store4 kept_knock[n_kept]
     0x86b78) are killed by sa_addr rd c SEG_M_SIZE, with g = c + 256 i and i < 32 (mconf_encp), n_kept <= 7 at the
     store; the byte checks on the text (0x86054, the FRONT / LONGP / HDRA / KEYA / TAIL load1 sites, v[i] of the
     folds 0x866c8 / 0x86800) by sa_addr rd t (|s| + 1), every cursor lying in [t, t + |s|]; words[i] (load8
     0x86750) by mf_words; role[i] (load4 0x868cc) by mf_roles; low[i] (store1 0x866d8 / 0x86810) by the walk's own
     frame facts (astack_malloc_realizes's zero shadow, then its own poisoning stores). The error path (a call of
     an errpath_* entry) is not reached.
   - the interceptors' range checks: the text ranges by sa_addr rd t; snprintf's %s by sa_addr rd lp (the label) and
     sa_addr rd c (c->reading); every destination (c->reading, g->role_file, g->ignore_file, g, g->name, g->model)
     lies in the block, addressable (sa_addr) and live (sa_heap).
   - where each object lies: c = calloc(1, 0x2414) (LLVMFuzzerTestOneInput 0x84f94) and t = malloc(n + 1)
     (0x850f4) by sa_heap, never by an address bound against the image's end (seg's blk_noimg fix, SegABase's head
     :49-53); the label in a heap block, a live side-stack frame (main's class-3 label[40]) or the image (the .bss
     object longl) - and in the image case PINNED at every allocator state, its shadow by sa_pinned and its tail by
     sa_pinned_tail, because snprintf reads it (0x86014) after this function's own `__asan_stack_malloc_1`
     (0x85f30) and the kit keeps no image shadow across that call (SegABase.v, the comments on sa_pinned and
     sa_romtail); the literals and the box-model table by sa_lit / sa_cat (pinned through the base);
     m_key.words and m_key.role by mf_words / mf_roles, also pinned (read at 0x86750 and 0x868cc, after the same
     stack_malloc_1). The stack window is
     apart from all of them by the kit (reac_segconf_find_c.v's note), so the plain `apart _ _ lo sp` conjuncts are
     not restated. The text's read span is kept apart from the block by seg_spec.cstr_span (seg's fix), not by
     |s| + 8.
   - its own side-stack frame: sa_room S (one frame; no callee takes one). The use-after-return option is AR's
     constant cell 1 (lib/Reusable/YG0f.v:193 aso_const_law), so the real-stack fallback 0x85f4c-0x85f64 is not taken;
     the frame is released inline before the return, so the post's frames are the entry's: sa_noalloc.
   - it reaches snprintf (itself and through m_refuse): sa_frm0 (rounding mode 0, AWALK-FORM.md 1.4,
     fuzz_command lib/A/Prog/check_reply_c.v:119, :155), sa_ssp GOTW GUARD (printf_core's stack-protector cells),
     apost_baseF.
   - the shadow base and the option cell are AR's const cells (as_got_shadow, as_shadow_cell, as_got_uar,
     as_uar_cell), so neither is a premise. No allocator entry: EV_m_file = 0.
   Call sites (provenance/evidence/image-tables/callsites.asan.tsv lines 12, 14): LLVMFuzzerTestOneInput 0x851ac (a drop-in turn:
   a0 = m, a1 = s7 = the text, a2 = s4 = longl (0x85178), main's label[40] or 0 (0x8518c)) and 0x85204 (the last
   turn: a2 = 0). At each: m = calloc(1, 9236) holding the model after the earlier turns (seg_spec.seg_run), the text
   a malloc block of at most 65,536 bytes holding a C string, the label a C string of at most 120 bytes or NULL.
   image A: A_m_file = BASE + AF_m_file = 0x84d34 + 0x1188 = 0x85ebc (lib/A/Prog/SegList.v:12); RLO / RHI =
   SEG_RLO / SEG_RHI = 0xa14a0 / 0xa3748 (lib/A/Prog/SegGlob.v:21-22); WORDS = 0xa1880 (m_key.words, .data.rel.ro:
   0x21140 "auto", 0x21160 "master", 0x21180 "slave", 0x211a0 "tap", 0x211c0 "box"); ROLES = 0x211e0 (m_key.role,
   .rodata, {0, 1, 2, 3, 4}); CAT = 0xa18e0 (fuzz_catalogue); GUARD = __stack_chk_guard 0x5ff078 and GOTW = 0xa36d8,
   its GOT word (measured by the G3 contracts lane: printf_core loads it at 0x96e44 and it holds 0x5ff078); lit F_s =
   0x21080, S_base = 0x210a0,
   S_segment = 0x21100, S_role = 0x21120, S_model = 0x21220, S_ignore = 0x21240, S_yes = 0x21260, S_true = 0x21280,
   S_no = 0x212a0, S_false = 0x212c0, S_knock = 0x212e0 (MF-CUTS-A.md section 1), F_addr_line = 0x210c0 and
   F_addr = 0x210e0 (m_refuse's .str.6 / .str.7 at 0x87854 / 0x87868; which text is which is INFERENCE from
   SegModel.m_refuse's `0 < line` test and the code's `blez` 0x8784c).
   STK_m_file = 288 + 16 + STK_fuzz_catalogue_row = 288 + 16 + (64 + 2 * ESTACK) = 8,560 (corrected at intake;
   the draft said 12,640 by counting snprintf's window as 3 * ESTACK). m_file's frame is 288 bytes and
   s1 = (sp0 - 288) & -32 lies 0 or 16 bytes lower (afn_pre gives sp0 mod 16 = 0, so the realignment is at most
   16, not 31); every callee runs at sp = s1. The windows below s1, each the callee's own STK as its contract file
   gives it: fuzz_catalogue_row 64 + 2 * ESTACK = 8,256 (its 64-byte frame and the kit's abcmp_realizes window,
   lib/Reusable/YG0d.v:364) - the DEEPEST; m_refuse 48 + 2 * ESTACK = 8,240 and m_find 48 + 2 * ESTACK = 8,240;
   m_file's own snprintf 2 * ESTACK = 8,192 (row 4's text is fuzz_command's asnprintf_realizes, whose window is
   CMD_SNP_K = 2 * ESTACK, its lib/A/Rt/RtPFCmd.v:65; fuzz_command's CHECK_REPLY_STK counted 3 * ESTACK, more than
   that text asks); ieq 48 + ESTACK; bcmp 2 * ESTACK; strchr 2 * ESTACK (row 6's accepted text,
   RtSeg.astrchr_realizes at commit 80d098bd1905, lib/A/Rt/RtSeg.v:72); strlen / memchr /
   __asan_memcpy / __asan_memset / __asan_stack_malloc_1 ESTACK. m_file's own deepest write, the
   probe word at sp0 - 288, lies inside 288 + 16. STK is a parameter: this number is image A's instance (SegInstA),
   not contract text.
   IMAGE-INDEPENDENT: no image module is Required; A_m_file, STK_m_file, RLO, RHI, WORDS, ROLES, CAT, GOTW, GUARD and
   lit are parameters (or fields of B).
   The WALK takes these as Section hypotheses (the interceptor lane's interface rows as at a7281bdd8928,
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626); the image-A owner's frame
   texts; the program callees' contracts from the contracts lane), each `forall fx0 : YK11.FPState`:
     the class-1 side-stack frame: astack_malloc_realizes 1, stack_malloc_progressP B, astack_free_law SEGS B,
       frame_flag_lawP SEGS B (the inline release; AWALK-FORM.md 2.6);
     `__asan_memcpy` / `__asan_memset`: aintrin_realizes OCpy / OSet (lib/Reusable/YG0d.v:326) at the listing's
       SS___asan_memcpy / SS___asan_memset;
     row 4 RtPFSeg.seg_asnprintf_realizes (img_lo img_hi cr pc gotw guard; commit 755e9278f8ff,
       RtPFSeg.v:228) at SS___interceptor_trampoline_snprintf, GOTW, GUARD;
     row 6 RtSeg.astrchr_realizes (pc) (accepted at commit 80d098bd1905, RtSeg.v:72; its strchr
       site 0x860d8 takes its premises from m_file_pre's text facts, with amem_range t (|s| + 8) added for it
       after the interceptor lane's review, O3), row 16 RtString.astrlen_realizes, row 19 abcmp_realizes, row 20
       MemchrDef.amemchr_realizes (both memchr sites: c = 0x5d at 0x862d4, c = 0x3d at 0x86344), each at its
       trampoline SS___interceptor_trampoline_<x>;
     m_refuse_contract, m_find_contract, ieq_contract, fuzz_catalogue_row_contract (lib/A/Prog/<F>_c.v on this
       branch) at (BASE + AF_<F>) and their STK.
   They are NOT premises of this contract: the statement does not mention them.
   SATISFIABLE (a start-state shape meeting every premise; no proof here): the harness's first turn at 0x85204 with
   one file: frames S = [(3, p3)] (main's class-3 frame; sa_room holds, 1 <= 8); ablocks B ly S holds c_r = malloc
   (16616), m = calloc(1, 9236) and t = malloc(n + 1) (and the payload); mc = mconf0 (calloc's zeros encode it:
   seg_spec.mconf_enc_zero), so gen = refused = overflow = 0 and the counter bounds hold; s = the turn's text, at
   most 65,535 NUL-free bytes with its NUL at t + n and its slack inside t's chunk (ASan's right redzone, mapped and
   not m's block, since m was allocated before t); lab = None and lp = 0 (a2 = 0); a0 = m, a1 = t, sp = the
   harness's s1, 16-aligned, with STK_m_file present bytes below it inside the stack band; fcsr = 0 (frm 0); RLO /
   RHI / WORDS / ROLES / CAT / GOTW / GUARD / lit the image-A values above, whose bytes are the pin's .rodata /
   .data.rel.ro bytes and whose shadow ASan's global registration leaves usable; st_nev S <= EV_MAX by AR. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the literals m_file hands to an interceptor or a callee: snprintf's format and default label (0x86014), the
   words ieq compares a header or a key with (ieq calls strlen on its word), and m_refuse's two formats, which
   m_refuse_contract asks as SegABase.sa_lit (its M_REFUSE_LITS). All are fuzz_segconf.c's copies of these texts
   (the reac_segconf.c module has its own copies at other addresses), so the harness instantiates lit with its
   fuzz_segconf.c map. *)
Definition M_FILE_LITS : list (list Z) :=
  [F_s; S_base; S_segment; S_role; S_model; S_ignore; S_yes; S_true; S_no; S_false; S_knock; F_addr_line; F_addr].
(* the five role words of m_key.words (H:214-218), in the table's order: SegModel.h_role_word's list *)
Definition MF_ROLE_WORDS : list (list Z) := [S_auto; S_master; S_slave; S_tap; S_box].
(* the bytes of the mconf block m_file may write (plain M_FILE_W without its stack entry, which apost_baseF's
   window carries): seg[0 .. n'), n / overflow / refused, kept[k0 .. k1), kept_knock[k0 .. k1), n_kept / gen /
   reading, with k0 the entry n_kept and n', k1 those of the final model mc' *)
Definition M_FILE_FP (c : Z) (k0 : nat) (mc' : mconf) : list (Z * Z) :=
  [(c, seg_spec.mseg_addr c (length (mc_seg mc')));
   (c + seg_spec.MC_N, c + seg_spec.MC_REFUSED + 4);
   (seg_spec.kept_addr c k0, seg_spec.kept_addr c (length (mc_kept mc')));
   (c + seg_spec.MC_KNOCK + 4 * Z.of_nat k0, c + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc')));
   (c + seg_spec.MC_NKEPT, c + seg_spec.MC_READING + 96)].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* the events this call spends: 0, neither it nor a callee reaches an allocator entry *)
Definition EV_m_file : Z := 0.
(* m_key.words as the code reads it (plain words_img): 40 bytes addressable at every allocator state and an image
   object, and word i a pointer, read from the image's own word, to the literal MF_ROLE_WORDS[i] (strlen 0x86760
   and bcmp 0x86774 read it); the pointer is bound existentially, as SegABase.sa_cat binds a token pointer. The
   addressability is sa_pinned, not an entry-state sa_addr (corrected at intake): words[i] is loaded at 0x86750,
   after this function's own `__asan_stack_malloc_1` (0x85f30), and the kit keeps no image shadow across that
   call (SegABase.v, the comment on sa_pinned). *)
Definition mf_words (rd : reader) (words : Z) : Prop :=
sa_pinned segs B words 40 /\ sa_img segs B words 40 /\
forall i, (i < 5)%nat -> exists wp, rdword rd (words + 8 * Z.of_nat i) = Some wp /\
sa_lit segs B rd wp (nth i MF_ROLE_WORDS []).
(* m_key.role as the code reads it (`lw` 0x868e8): 20 bytes addressable at every allocator state (sa_pinned, for
   the same reason: role[i] is loaded at 0x868cc, after the stack_malloc_1) and an image object, entry i the role
   i (the enum value SegModel.h_role_word answers for word i) *)
Definition mf_roles (rd : reader) (roles : Z) : Prop :=
sa_pinned segs B roles 20 /\ sa_img segs B roles 20 /\
forall i, (i < 5)%nat -> sa_val rd (roles + 4 * Z.of_nat i) 4 (Z.of_nat i).
(* the plain m_file_pre (lib/Prog/m_file_c.v:119-135 at 440d61eaa8c8) over the reader rd = aview segs (w_H W) mem:
   the mconf block c holding mc, a live heap block, addressable, with the 4 bytes after it mapped (snprintf's %s of
   c->reading reads to the next 8-byte boundary, plain blk_slack); the counters' room (plain); the text t, a C string
   s with its slack (sa_str), at most 65,535 bytes, in a live heap block, its bytes and NUL addressable, its read
   span apart from the block (seg_spec.cstr_span); the label lp, NULL or a C string of at most 65,535 bytes (a %s
   argument, SegABase's head :49-51) in a heap block, a live side-stack frame, or the image - pinned there, its
   shadow by sa_pinned and its tail by sa_pinned_tail, because snprintf reads it after the stack_malloc_1 and the
   one image label is the .bss longl, whose tail is a .bss redzone the journal does not keep (corrected at intake,
   the same form as reac_segconf_parse_file's label; the harness gives the tail as sa_romtail, since seg_rom
   reads the rw .bss segment, and SegABase.sa_pinned_tail_of_romtail turns it into this premise) - addressable,
   its read span apart from the destination c->reading. The plain
   stack_ok / apart-from-the-stack / mem_inv / printf_env conjuncts are afn_pre's, the locations' and the
   contract's image premises here.
   amem_range t (|s| + 8), the band room past the text (added 2026-10-30 after the interceptor lane's review, O3): row
   6, RtSeg.astrchr_realizes (commit 80d098bd1905, lib/A/Rt/RtSeg.v:72-79), asks
   amem_range x (astr_len s' + 8) of its string at the strchr site 0x860d8, where x is the line cursor (s11) in
   [t, t + |s|] and x + astr_len s' = t + |s|; one conjunct at t gives it at every cursor, since amem_range's end is
   the same and its high-memory arm only needs kHighMemBeg <= t <= x (lib/Reusable/YG0d.v:325). sa_addr gives only
   amem_range t (|s| + 1), and a heap block's address is not a computation a walk can do, unlike a literal's. Every
   other premise of row 6 at that site follows from the text facts above: 0 < x from t <> 0 and sa_addr's
   0 <= t; the string by SegABase.sa_strz_bytes; aread_ok from sa_addr, the length bound and sa_heap (a heap
   byte is not in the call's scratch window); atail_vis from sa_str's tail; rt_rom_view from arodata_okP. *)
Definition m_file_pre (ly : alayout) (S : astate) (rd : reader) (c t lp : Z) (mc : mconf) (s : list Z)
(lab : option (list Z)) : Prop :=
c <> 0 /\ c mod 16 = 0 /\ sa_mconf rd c mc /\ sa_heap B ly S c seg_spec.SEG_M_SIZE /\
sa_addr rd c seg_spec.SEG_M_SIZE /\ sa_tail rd (c + seg_spec.SEG_M_SIZE - 1) /\
mc_gen mc + 1 < 2 ^ 31 /\ mc_refused mc + 2 ^ 17 < 2 ^ 32 /\ mc_overflow mc + 2 ^ 17 < 2 ^ 32 /\
t <> 0 /\ sa_str rd t s /\ Z.of_nat (length s) <= 65535 /\ sa_heap B ly S t (Z.of_nat (length s) + 1) /\
sa_addr rd t (Z.of_nat (length s) + 1) /\ amem_range t (Z.of_nat (length s) + 8) /\
sa_disj t (seg_spec.cstr_span t s) c seg_spec.SEG_M_SIZE /\
sa_ostr rd lp lab /\
match lab with
| Some l =>
    Z.of_nat (length l) <= 65535 /\
    (sa_heap B ly S lp (Z.of_nat (length l) + 1) \/ sa_fframe ly S lp (Z.of_nat (length l) + 1) \/
     (sa_img segs B lp (Z.of_nat (length l) + 1) /\ sa_pinned segs B lp (Z.of_nat (length l) + 1) /\
      sa_pinned_tail segs B (lp + Z.of_nat (length l)))) /\
    sa_addr rd lp (Z.of_nat (length l) + 1) /\
    sa_disj lp (seg_spec.cstr_span lp l) (c + seg_spec.MC_READING) 96
| None => True
end.
Definition m_file_contract (A_m_file STK_m_file RLO RHI : Z) (lit : list Z -> Z) (WORDS ROLES CAT GOTW GUARD : Z)
: Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c t lp : Z) (mc : mconf) (s : list Z) (lab : option (list Z)),
afn_pre segs B STK_m_file ly S W regs mem md ch ->
(* rounding mode 0, which the snprintf wrapper needs (its own three calls and m_refuse's two) *)
sa_frm0 ->
(* room for its class-1 side-stack frame *)
sa_room S ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
(* the image objects it and its callees read: the literals, m_key.words, m_key.role, the box-model table
   (fuzz_catalogue_row), printf_core's stack-protector cells *)
(forall x, In x M_FILE_LITS -> sa_lit segs B (aview segs (w_H W) mem) (lit x) x) ->
mf_words (aview segs (w_H W) mem) WORDS -> mf_roles (aview segs (w_H W) mem) ROLES ->
sa_cat segs B (aview segs (w_H W) mem) CAT -> sa_ssp (aview segs (w_H W) mem) GOTW GUARD ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 11 = w64 t -> 0 <= t < 2 ^ 64 ->
getr regs 12 = w64 lp -> 0 <= lp < 2 ^ 64 ->
m_file_pre ly S (aview segs (w_H W) mem) c t lp mc s lab ->
st_nev S + EV_m_file <= EV_MAX ->
SRr segs W (cfg_at segs A_m_file regs mem md)
(apost_baseF segs B STK_m_file (M_FILE_FP c (length (mc_kept mc)) (SegModel.m_file mc s lab)) regs ly S W mem md
EV_m_file
(fun ly' S' W' regs' mem' md' =>
 sa_mconf (aview segs (w_H W') mem') c (SegModel.m_file mc s lab) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.

(* ===================================== the model's counters ===================================== *)
(* Restated from the plain / UBSan owner's lib/Prog/m_file_c.v:266-331 at 440d61eaa8c8, statements and proofs unchanged
   (that file Requires the plain image module Img0, so this file cannot Require it). gen goes up by one per call,
   refused and overflow by at most one per line, hence by at most the text's length: with m = calloc's zeros and at
   most 4 calls, a caller meets m_file_pre's gen, refused and overflow bounds at the next call. *)
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
