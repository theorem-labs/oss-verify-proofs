(** * Spec.PngModel.Harness — transcription of the fuzz driver's own logic.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.Base] and Stdlib.  Nothing here mentions RISC-V, the
    memory images, the trusted spec, or the trace-set machinery
    ([Common/ShapeBudget.v], WP-1's package): this file supplies the
    SOURCE-LEVEL functions those trace sets are stated against — the size
    predicates, the message byte strings, and [rt_viol] — and nothing else.

    Sources, transcribed in full and BUG-FOR-BUG (in-container
    [/harness/problem/materials/harness/src/], host copies at
    [data/libpng4--aug14/materials/harness/src/]):

    - [png_harness.c]   (455 lines) — the fuzz target: the six phases, the
      allocator/error hooks, the two I/O sinks, and the round-trip core.
    - [provable_main.c] (121 lines) — the replay driver: [read_all], the
      64 MiB input limit, and the four loud [exit(2)] messages.
    - [grow_buf.h]      ( 31 lines) — malloc/copy/free growth (no realloc).

    Build defines of the delivered binary (from [build.sh]'s
    [build_provable], confirmed against the binary's rodata):
    [-DHARNESS_ROUNDTRIP -DHARNESS_WRITE -DHARNESS_PROGRESSIVE
     -DHARNESS_SIMPLIFIED -DHARNESS_FAIL_EXIT=134 -DHARNESS_QUIET].
    Every [#ifdef] below is resolved at those settings; the disabled
    branches ([abort()] instead of [exit(134)], the non-quiet banners, the
    [selftest OK] line) are NOT transcribed, and their absence is confirmed
    by the binary's string table (no [selftest OK], no
    [provable_main: running], no [Running: ], no [Done:    ]).

    WHY THIS FILE MATTERS.  On a clean run the binary's trace is SILENT:
    file reads emit no events, allocation is trace-silent, and the QUIET
    build suppresses all printing.  The ONE place where a value computed by
    libpng/zlib decides an observable outcome is the round-trip guards
    inside [assert_roundtrip] ([png_harness.c:308-338]).  [rt_viol] below is
    the predicate that says whether those guards fire.

    Two facts established by other lanes and USED here:

    - **E2 is closed**: no NULL-tolerated, output-relevant allocation site
      exists on the encode path.  Consequently [rt_viol] is a function of
      the FILE BYTES ALONE, independent of which allocations the kernel
      refused — which is why [cd_enc]/[cd_dec] below are the ALL-SUCCESS
      codec functions and allocation refusal appears only as [RtSkip].
    - **HFLAG**: [harness_alloc_failed] ([png_harness.c:71]) is consulted at
      exactly ONE place, [:322].  See §3 for the per-site table; several
      harness-side allocation failures deliberately do NOT set it, because
      they return before any comparison is reached.  The model records what
      the C does, not what a tidy design would do.

    Structure (matching [Inftrees.v]'s shape: constants, then per-C-function
    transcriptions with line citations, [nat]-fuelled [Fixpoint]s whose fuel
    is read off the C loop, a record for loop-carried state, and a [_wf]
    predicate collecting caller obligations):

      §0  byte strings and the printf renderings
      §1  constants
      §2  colour types and [channels_of]
      §3  the allocator hooks, the error hooks, and the two sinks
      §4  [provable_main.c]: [read_all], its outcomes and its messages
      §5  the round-trip core: [Shape], [Codec], [assert_rt], [RT_MSG]
      §6  [ReachableShapes] and the synthesised pixel family
      §7  [LLVMFuzzerTestOneInput]: the six phases
      §8  facts: the dead guard arms and the Route-A collapse of [rt_viol]

    VALIDATED AGAINST THE DELIVERED BINARY [/harness/reference_binary]
    (tools in [a working folder], all via the qemu
    GDB-RSP tracer described in that directory's README.md):

    - [rtsweep.py shapes] — EXHAUSTIVE over the whole [RS_ed] family:
      all 32768 [(data[0..3])] combinations driven through
      [LLVMFuzzerTestOneInput], reading the seven argument registers of
      [assert_roundtrip].  32768/32768 shapes reproduced by [ed_shape],
      129,792,000 pixel bytes reproduced by [synth_bytes], 0 mismatches;
      every call carried [corrupt = 0, expect_ok = 1].
    - [rtexhaust.py] — the same 32768 shapes end to end, binary unmodified
      and unstubbed: every run exits 0 with empty stdout and stderr, i.e.
      no round-trip guard fires anywhere in the family.
    - [rtcorpus.py] — 264 real PNGs (pngsuite + 12 generated large/odd
      images) and the 401 injected family inputs: 797 [assert_roundtrip]
      calls, all with [corrupt = 0, expect_ok = 1]; 252 + 401 from the P2
      site and 144 from the P3 site; every P2 shape in [RS_ed], every P3
      shape in [RS_de] (12 of them outside the 64x64 box); every
      [encode_raw] that returned 1 produced at least 67 bytes; every
      [decode_raw] returned 1.
    - [rtmsg.py] — [rt_fail] synthesised on the real binary with 14
      argument tuples: all 18 message byte strings in this file (five
      [rt_what] literals, four [provable_main] messages, nine [RT_MSG]
      renderings) reproduce the binary's output byte for byte, and the
      exit status is 134.
    - the [MAX_INPUT] boundary is confirmed by running the binary on files
      of 2^26 - 1 (silent, exit 0), 2^26 and 2^26 + 1 (exit 2 with
      [MSG_LM]) bytes; [MSG_CO] and [MSG_RD] by running it on a missing
      path, the empty path, ["."] and ["/tmp"]; and [MSG_OOM] by forcing
      [read_all]'s [malloc(1 << 16)] and its [grow_buf] malloc to return
      NULL over RSP — both print the same string and exit 2.
    - [rw_shape] / [rw_interlace] checked against [png_set_IHDR]'s
      arguments inside [run_write] on 8 inputs, 0 mismatches.

    Full record with reproduction commands:
    [wp4-harness-validation.txt].

    Worth knowing when reading those numbers: a real PNG always begins with
    the same four signature bytes, so EVERY valid PNG produces the SAME P2
    shape [(w,h,bd,ct) = (15,8,8,2)] — 236 of the 252 corpus files land
    there.  The corpus alone therefore validates almost nothing about
    [ed_shape]; the exhaustive injected sweep is the evidence. *)

(* [String] is required BEFORE [List] on purpose: both export a [length],
   and every [length] below is the list one. *)
From Stdlib Require Import Bool ZArith String Ascii List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.
(* [&&]/[||] appear in [if] conditions, where no expected type opens
   [bool_scope] for us; neither notation collides with [Z_scope]. *)
Local Open Scope bool_scope.

(** ** §0  Byte strings and the printf renderings *)

(** A C string literal as the byte list a [write]/[writev] would emit.  The
    harness's literals are pure ASCII, so this is unambiguous. *)
Definition bos (s : string) : list Z :=
  map (fun c => Z.of_N (N_of_ascii c)) (list_ascii_of_string s).

Definition LF : Z := 10.   (** ['\n'] *)

(** [%zu] / [%u]: unsigned decimal, no padding, no sign.  The fuel bound 32
    exceeds the 20 digits of [2^64 - 1]. *)
Fixpoint dec_rev (n : nat) (v : Z) : list Z :=
  match n with
  | O => []
  | S k => if v <=? 0 then [] else (48 + v mod 10) :: dec_rev k (v / 10)
  end.

Definition u_dec (v : Z) : list Z :=
  if v <=? 0 then [48] else rev (dec_rev 32%nat v).

(** [%02x]: lowercase hex, zero-padded to two digits.  [rt_fail]'s [a]/[b]
    arguments are [uint8_t] promoted to [unsigned], so they are in [0..255]
    and the field is always exactly two digits. *)
Definition hexdig (v : Z) : Z := if v <? 10 then 48 + v else 87 + v.

Definition hex2 (b : Z) : list Z :=
  [hexdig ((b / 16) mod 16); hexdig (b mod 16)].

(** ** §1  Constants *)

(** [png_harness.c:25] [static const int kHdr = 8;] — the PNG signature
    length, and also the [size < 8] gate of [LLVMFuzzerTestOneInput]. *)
Definition kHdr : Z := 8.

(** [png_harness.c:26] [#define MAX_ALLOC 8000000]. *)
Definition MAX_ALLOC : Z := 8000000.

(** [provable_main.c:51] [#define MAX_INPUT (64u << 20)]. *)
Definition MAX_INPUT : Z := 67108864.

(** [provable_main.c:61] [size_t cap = 1 << 16]. *)
Definition READ_CAP0 : Z := 65536.

(** [png_harness.c:203] [exit(HARNESS_FAIL_EXIT)] with
    [-DHARNESS_FAIL_EXIT=134].  134 mirrors SIGABRT's observable low byte
    without [abort()]'s unmodeled [rt_sigprocmask]/[tgkill]. *)
Definition HARNESS_FAIL_EXIT : Z := 134.

(** [provable_main.c:59,65,74,88] — every loud driver error exits 2. *)
Definition EXIT_IOERR : Z := 2.

(** [png_harness.c:218] [size_t nc = b->cap ? b->cap : 1024]. *)
Definition DYN_CAP0 : Z := 1024.

(** [png_harness.c:316] [if (corrupt && enc.len > 60)]. *)
Definition RT_CORRUPT_MIN : Z := 60.

(** ** §2  Colour types and [channels_of] *)

(** [png.h:667-671]. *)
Definition PNG_CT_GRAY       : Z := 0.
Definition PNG_CT_RGB        : Z := 2.
Definition PNG_CT_PALETTE    : Z := 3.
Definition PNG_CT_GRAY_ALPHA : Z := 4.
Definition PNG_CT_RGB_ALPHA  : Z := 6.

(** Interlace types ([png.h:686-687]) are written as the literals 0 and 1
    below rather than as named constants: [Spec/PngModel/Chunk.v] already
    owns [PNG_INTERLACE_NONE] / [PNG_INTERLACE_ADAM7] (same values), and
    this file must not depend on it — [Harness.v]'s only [PngModel]
    dependency is [Base]. *)

(** [png_harness.c:234-242].  The [default: return 0] arm covers PALETTE
    (3) and every out-of-range value; the harness never builds one, but the
    transcription keeps the arm. *)
Definition channels_of (ct : Z) : Z :=
  if ct =? PNG_CT_GRAY       then 1 else
  if ct =? PNG_CT_GRAY_ALPHA then 2 else
  if ct =? PNG_CT_RGB        then 3 else
  if ct =? PNG_CT_RGB_ALPHA  then 4 else 0.

(** ** §3  Allocator hooks, error hooks, and the two I/O sinks *)

(** [png_harness.c:73-79]:
<<
    static void *limited_malloc(png_structp p, png_alloc_size_t size) {
      if (size > MAX_ALLOC) { harness_alloc_failed = 1; return NULL; }
      void *r = malloc(size);
      if (!r) harness_alloc_failed = 1;
      return r;
    }
>>
    Two distinct refusals share one flag: a DETERMINISTIC threshold refusal
    (a function of [size] alone) and the allocator's own nondeterministic
    NULL.  Only the first is modeled here; the second is the alloc-silence
    layer's business.

    Note the threshold is [>], not [>=]: a request of exactly [MAX_ALLOC]
    bytes is forwarded to [malloc]. *)
Definition lm_refused (size : Z) : bool := MAX_ALLOC <? size.

(** Every libpng allocation on every phase goes through this hook: each of
    the five [png_create_*_struct] sites is followed by [png_set_mem_fn]
    ([:94, :112, :141, :254, :283, :368]).  The two [decode_raw] creations
    at [:276]/[:278] are the exception — they run BEFORE [:283]'s
    [png_set_mem_fn] and therefore use the default allocator; the C
    compensates by setting the flag by hand at [:277]/[:279]. *)

(** [png_harness.c:36-43], enabled by [-DHARNESS_QUIET]:
<<
    static void quiet_error(png_structp p, png_const_charp msg) { png_longjmp(p, 1); }
    static void quiet_warning(png_structp p, png_const_charp msg) { }
>>
    Both are installed as the [error_fn]/[warn_fn] of every [png_struct]
    the harness creates ([PNG_ERR_HOOKS], [:44]).  Neither writes a byte:
    this is the whole of the QUIET property at the libpng boundary.
    [quiet_error] does not return (libpng requires it not to); it unwinds
    to the enclosing [setjmp(png_jmpbuf(p))], which in every case returns
    from the phase or returns 0 from [encode_raw]/[decode_raw]. *)
Definition quiet_error_emits   : bool := false.
Definition quiet_warning_emits : bool := false.

(** [png_harness.c:60-64], the counting write sink used by [run_write]:
<<
    typedef struct { size_t n; } SinkState;
    static void mem_write(png_structp p, png_bytep d, size_t len) { s->n += len; }
>>
    The payload [d] is discarded; [s->n] is never read.  So the whole write
    phase is value-irrelevant, and this is the fact that says so. *)
Definition mem_sink_step (n len : Z) : Z := n + len.

(** [png_harness.c:214-231], the growable encoder sink.  Growth is by
    [grow_buf()] (malloc / memcpy / free — [grow_buf.h:21-29]), NEVER by
    [realloc], because [realloc] on an mmap-served musl block issues
    [mremap], which the trusted syscall model does not cover. *)
Record DynBuf : Type := mkDynBuf {
  db_len : Z;             (** [b->len] *)
  db_cap : Z;             (** [b->cap] *)
  db_bytes : list Z       (** the first [db_len] bytes of [b->buf] *)
}.

Definition db_empty : DynBuf := mkDynBuf 0 0 [].

(** [png_harness.c:219-220] [while (nc < b->len + n) nc *= 2].  Fuel 64
    exceeds the 64 doublings a [size_t] admits. *)
Fixpoint dyn_grow (k : nat) (nc need : Z) : Z :=
  match k with
  | O => nc
  | S k' => if nc <? need then dyn_grow k' (nc * 2) need else nc
  end.

(** The capacity [dyn_write] settles on for a write of [n] bytes.  Equals
    [db_cap b] when no growth is needed ([:217]'s test fails). *)
Definition dyn_newcap (b : DynBuf) (n : Z) : Z :=
  if db_cap b <? db_len b + n
  then dyn_grow 64%nat (if db_cap b =? 0 then DYN_CAP0 else db_cap b) (db_len b + n)
  else db_cap b.

(** One [dyn_write] call, on the all-success path ([grow_buf] returned
    non-NULL; on NULL the C raises [png_error(p, "sink oom")] — SILENT, and
    it makes the enclosing [encode_raw] return 0, i.e. an [RtSkip]).
    [:229]'s [if (n) memcpy(...)] guard against [memcpy(NULL, d, 0)] has no
    effect on the resulting byte list. *)
Definition dyn_step (b : DynBuf) (d : list Z) : DynBuf :=
  let n := Z.of_nat (length d) in
  mkDynBuf (db_len b + n) (dyn_newcap b n) (db_bytes b ++ d).

(** *** The allocation-site table (HFLAG)

    Every allocation the driver's own code performs, with (a) whether its
    failure sets [harness_alloc_failed] and (b) whether its failure is
    OBSERVABLE (a loud [exit(2)]) or a silent skip.  This is the table the
    alloc-silence layer is stated against, and it is deliberately
    IRREGULAR: several harness-side failures do not set the flag because
    they return before any comparison is reached.

    Exhaustive against the source (every [malloc], [grow_buf] and
    [png_malloc] in [png_harness.c] and [provable_main.c]); the only site
    not listed is [png_harness.c:410], inside
    [harness_roundtrip_selftest], which no code path in the delivered
    binary reaches (see the note at [arm_vacuous_dead]). *)
Inductive AllocSite : Set :=
| AS_ra_init      (** [provable_main.c:62]  [malloc(1 << 16)]              *)
| AS_ra_grow      (** [provable_main.c:78]  [grow_buf(buf, len, cap)]      *)
| AS_ed_orig      (** [png_harness.c:350]   [malloc(total)] for the pixels *)
| AS_ar_dec       (** [png_harness.c:317]   [malloc(total)] for [dec]      *)
| AS_enc_struct   (** [png_harness.c:248]   png_create_write_struct        *)
| AS_enc_info     (** [png_harness.c:250]   png_create_info_struct         *)
| AS_enc_rows     (** [png_harness.c:260]   [malloc(8 * h)] in encode_raw  *)
| AS_dec_struct   (** [png_harness.c:276]   png_create_read_struct         *)
| AS_dec_info     (** [png_harness.c:278]   png_create_info_struct         *)
| AS_dec_rows     (** [png_harness.c:293]   [malloc(8 * h)] in decode_raw  *)
| AS_de_struct    (** [png_harness.c:362]   png_create_read_struct  (P3)   *)
| AS_de_info      (** [png_harness.c:364]   png_create_info_struct  (P3)   *)
| AS_de_p1        (** [png_harness.c:388]   [malloc(4 * w * h)]            *)
| AS_de_rows      (** [png_harness.c:390]   [malloc(8 * h)]                *)
| AS_rw_row       (** [png_harness.c:123]   [malloc(rb)] in run_write      *)
| AS_simpl_buf    (** [png_harness.c:447]   [malloc(nbytes)]               *)
| AS_dyn_grow     (** [png_harness.c:220]   [grow_buf] inside dyn_write    *)
| AS_libpng.      (** every [limited_malloc] call ([:73]) and hence every
                      libpng-internal allocation, incl. [png_malloc] at
                      [:163]                                               *)

(** Does a failure at this site set [harness_alloc_failed]?  The writes are
    at [png_harness.c:75, :77] (inside [limited_malloc]) and [:277, :279,
    :294] (by hand in [decode_raw]) — and NOWHERE else.  In particular the
    four harness-side mallocs at [:317], [:350], [:388], [:390] and the two
    P3 struct creations at [:362], [:364] deliberately do NOT set it: each
    returns before any comparison is reached, so the flag would be dead
    information.  Model what the C does, not what a tidy design would do. *)
Definition as_sets_flag (a : AllocSite) : bool :=
  match a with
  | AS_dec_struct | AS_dec_info | AS_dec_rows | AS_libpng => true
  | _ => false
  end.

(** Is a failure at this site OBSERVABLE?  Only the two [read_all] sites
    are: everything else is a silent skip.  [AS_enc_rows] reaches
    [png_error(p, "rows oom")] and [dyn_write]'s [grow_buf] failure reaches
    [png_error(p, "sink oom")]; under the quiet hooks both longjmp
    silently, so [encode_raw] returns 0 and [assert_roundtrip] returns at
    [:314] — a skip, NOT a driver OOM. *)
Definition as_loud (a : AllocSite) : bool :=
  match a with AS_ra_init | AS_ra_grow => true | _ => false end.

(** Sites whose failure can be reached BETWEEN the flag clear at [:319] and
    the flag test at [:322] — i.e. the sites the flag actually has to
    cover.  [AS_ar_dec] is excluded because [:317] precedes the clear;
    [AS_ed_orig], [AS_de_p1], [AS_de_rows], [AS_enc_rows] are excluded
    because they precede any comparison on their path. *)
Definition as_in_flag_window (a : AllocSite) : bool :=
  match a with
  | AS_dec_struct | AS_dec_info | AS_dec_rows | AS_libpng => true
  | _ => false
  end.

(** The discipline is sound in exactly this sense: within the window, the
    flag is set at every site.  [as_flag_covers_window] is the statement,
    checked by computation over the whole site enumeration.  Hence
    [!ok && !harness_alloc_failed] at [:322] implies the decode ran its
    all-success path, which is what makes [rt_viol] a function of the file
    bytes alone. *)
Definition all_alloc_sites : list AllocSite :=
  [AS_ra_init; AS_ra_grow; AS_ed_orig; AS_ar_dec; AS_enc_struct; AS_enc_info;
   AS_enc_rows; AS_dec_struct; AS_dec_info; AS_dec_rows; AS_de_struct;
   AS_de_info; AS_de_p1; AS_de_rows; AS_rw_row; AS_simpl_buf; AS_dyn_grow;
   AS_libpng].

Lemma as_flag_covers_window :
  forallb (fun a => implb (as_in_flag_window a) (as_sets_flag a))
          all_alloc_sites = true.
Proof. reflexivity. Qed.

Lemma as_loud_sites_are_driver_only :
  filter as_loud all_alloc_sites = [AS_ra_init; AS_ra_grow].
Proof. reflexivity. Qed.

(** ** §4  [provable_main.c]: [read_all], its outcomes, and its messages *)

(** The four loud driver messages.  Format strings confirmed byte-for-byte
    against the delivered binary's rodata (file offsets 0x43720, 0x43740,
    0x43760, 0x437a0); the trailing ['\n'] is INSIDE each format string, so
    each is one [fprintf], i.e. one unbuffered [writev] on musl's stderr. *)

(** [provable_main.c:58] ["provable_main: cannot open %s\n"]. *)
Definition MSG_CO (p : list Z) : list Z :=
  bos "provable_main: cannot open " ++ p ++ [LF].

(** [provable_main.c:64] and [:80] ["provable_main: out of memory\n"] — the
    SAME string at both sites, so the two loud allocation failures are
    observationally identical and contribute one trace, not two. *)
Definition MSG_OOM : list Z :=
  bos "provable_main: out of memory" ++ [LF].

(** [provable_main.c:87] ["provable_main: read error on %s\n"]. *)
Definition MSG_RD (p : list Z) : list Z :=
  bos "provable_main: read error on " ++ p ++ [LF].

(** [provable_main.c:73-74].  The C splits the literal across two source
    lines; concatenated it is
    ["provable_main: %s is at or above the %u-byte input limit\n"], and the
    [%u] argument is [MAX_INPUT], rendered "67108864". *)
Definition MSG_LM (p : list Z) : list Z :=
  bos "provable_main: " ++ p ++ bos " is at or above the "
  ++ u_dec MAX_INPUT ++ bos "-byte input limit" ++ [LF].

(** The outcome of one [read_all] call ([provable_main.c:55-97]). *)
Inductive RaOut : Set :=
| RaOpenFail            (** [:56-60]  open() < 0        -> [MSG_CO], exit 2 *)
| RaOom                 (** [:63,:79] malloc/grow NULL  -> [MSG_OOM], exit 2 *)
| RaReadErr             (** [:86-89]  read() < 0        -> [MSG_RD], exit 2 *)
| RaLimit               (** [:72-76]  len == cap >= MAX_INPUT -> [MSG_LM], exit 2 *)
| RaOk (len cap : Z).   (** [:94-96]  full file read; [cap] = final capacity *)

(** The deterministic all-success run of [read_all] on a REGULAR file of
    [n] bytes.

    Reads on a regular file are deterministic and full: [read(fd, buf+len,
    cap-len)] returns [min(cap - len, n - len)].  So one read per capacity
    brings [len] to [min(cap, n)], and the loop only ever revisits the
    growth test when [len == cap], i.e. when [n >= cap].

    Fuel 32 exceeds the ten doublings from [2^16] to [2^26].

    BUG-FOR-BUG detail worth stating explicitly: a file whose size is
    EXACTLY a capacity ([n = cap]) forces one extra doubling and one extra
    [grow_buf] copy before the terminating zero-length read, because
    [:68]'s [len == cap] test cannot distinguish end-of-file from
    more-to-come.  That is also what puts the file of exactly [MAX_INPUT]
    bytes on the refusing side of the limit. *)
Fixpoint ra_run (k : nat) (cap n : Z) : RaOut :=
  match k with
  | O => RaLimit                       (** unreachable at fuel 32 *)
  | S k' =>
      if n <? cap then RaOk n cap
      else if MAX_INPUT <=? cap then RaLimit
      else ra_run k' (cap * 2) n
  end.

Definition read_all_ok (n : Z) : RaOut := ra_run 32%nat READ_CAP0 n.

(** The documented boundary ([provable_main.c:45-49]): strictly below
    [MAX_INPUT] is read in full, [MAX_INPUT] or more is refused. *)
Definition sz_refused (n : Z) : bool := MAX_INPUT <=? n.

(** [png_harness.c:427] [if (size < (size_t)kHdr) return 0;] — the
    [LLVMFuzzerTestOneInput] gate.  NOTE: on a clean run this gate has NO
    observable consequence (both sides exit 0 silently); it matters only
    for the REACHABILITY of the round-trip guards. *)
Definition sz_gated (n : Z) : bool := n <? kHdr.

Lemma read_all_ok_below : read_all_ok (MAX_INPUT - 1) = RaOk (MAX_INPUT - 1) MAX_INPUT.
Proof. reflexivity. Qed.

Lemma read_all_at_limit : read_all_ok MAX_INPUT = RaLimit.
Proof. reflexivity. Qed.

Lemma read_all_small : read_all_ok 0 = RaOk 0 READ_CAP0.
Proof. reflexivity. Qed.

(** The extra-doubling corner, at the first capacity. *)
Lemma read_all_exact_cap : read_all_ok READ_CAP0 = RaOk READ_CAP0 (2 * READ_CAP0).
Proof. reflexivity. Qed.

Lemma read_all_just_under_cap :
  read_all_ok (READ_CAP0 - 1) = RaOk (READ_CAP0 - 1) READ_CAP0.
Proof. reflexivity. Qed.

(** The classification WP-1's [FBig] arm needs: the driver refuses a file
    for the input-limit reason EXACTLY when [sz_refused] says so.  (The
    outcome does not depend on how the kernel chunks the reads: [len] can
    only reach [cap] when the file has at least [cap] bytes, so a partial
    read changes the number of [read] syscalls — all event-free — and
    nothing else.) *)
Lemma read_all_limit_iff : forall n, read_all_ok n = RaLimit <-> MAX_INPUT <= n.
Proof.
  intros n. unfold read_all_ok, READ_CAP0, MAX_INPUT. cbn [ra_run].
  repeat (match goal with
          | |- context [ n <? ?c ] =>
              let E := fresh "E" in
              destruct (n <? c) eqn:E;
              [ apply Z.ltb_lt in E; split; [discriminate | lia]
              | apply Z.ltb_ge in E ]
          end).
  split; [ intros _; lia | reflexivity ].
Qed.

Lemma read_all_refused_iff :
  forall n, read_all_ok n = RaLimit <-> sz_refused n = true.
Proof.
  intros n. unfold sz_refused. rewrite Z.leb_le. apply read_all_limit_iff.
Qed.

(** Below the limit the whole file is read, into a buffer whose capacity is
    the first entry of the doubling sequence [2^16, 2^17, ..., 2^26] that
    is strictly greater than the file size — never more than [MAX_INPUT],
    so live allocation is bounded by a constant, not by the input size,
    which is the property [provable_main.c:26-49] argues the equivalence
    theorem needs. *)
Lemma read_all_below_limit :
  forall n, 0 <= n -> n < MAX_INPUT ->
  exists c, read_all_ok n = RaOk n c /\ n < c <= MAX_INPUT.
Proof.
  intros n H0 H1. unfold read_all_ok, READ_CAP0, MAX_INPUT in *. cbn [ra_run].
  repeat (match goal with
          | |- context [ n <? ?c ] =>
              let E := fresh "E" in
              destruct (n <? c) eqn:E;
              [ apply Z.ltb_lt in E; eexists; split; [reflexivity | lia]
              | apply Z.ltb_ge in E ]
          end).
  lia.
Qed.

(** ** §5  The round-trip core ([png_harness.c:244-355]) *)

(** An image shape: the four IHDR fields [assert_roundtrip] is parametric
    in.  Interlacing is not a field because both round-trip encodes are
    [PNG_INTERLACE_NONE] ([:256]). *)
Record Shape : Set := mkShape {
  sh_w  : Z;
  sh_h  : Z;
  sh_bd : Z;
  sh_ct : Z
}.

(** [png_harness.c:311] [size_t total = (size_t)w * ch * (bd / 8) * h;]
    — left-associated, and [bd / 8] is INTEGER division, so a hypothetical
    [bd < 8] would give [total = 0] and fire the degenerate arm.  The
    driver only ever passes [bd] in [{8, 16}]. *)
Definition sh_total (s : Shape) : Z :=
  sh_w s * channels_of (sh_ct s) * (sh_bd s / 8) * sh_h s.

(** *** The codec interface

    The three functions the round-trip core consumes, on the ALL-SUCCESS
    allocation path (E2: no NULL-tolerated, output-relevant allocation site
    exists on the encode path, so these are functions of their arguments
    alone).  Allocation refusal never turns a skip into a failure, only a
    failure into a skip — so [rt_viol] computed here is an UPPER BOUND on
    what is reachable, which is the direction both routes need.

    Kept as a record (not [Parameter]s, which the axiom gate forbids) so
    that WP-1's shapes and the round-trip theorem quantify over the same
    interface and Route B remains available without an interface change. *)
Record Codec : Type := mkCodec {
  (** [encode_raw] ([:246-268]): [None] is the C's [return 0] (a
      [png_create_*] failure, or a [png_error] caught by [:253]'s setjmp —
      including ["rows oom"] at [:261] and ["sink oom"] from [dyn_write]).
      [Some b] is [return 1] with [b] the bytes [dyn_write] accumulated. *)
  cd_enc : list Z -> Shape -> option (list Z);

  (** [decode_raw] ([:273-304]) at the expected shape, on the all-success
      path: [Some pix] is [return 1] with [out] filled, [None] is the CLEAN
      [return 0] (IHDR/rowbytes mismatch at [:288-292], or a [png_error]
      that is not an allocation failure).  The [!ok && harness_alloc_failed]
      case is NOT here: it is an allocation-pattern skip. *)
  cd_dec : list Z -> Shape -> option (list Z);

  (** [roundtrip_decode_encode]'s front end ([:360-393]): decode the INPUT
      to canonical RGBA8.  [None] whenever the C bails before reaching
      [:395] — [size < 8] or bad signature ([:361]), no IHDR ([:375]),
      [!w || !h || h > 1e8/w] ([:376]), [rb != 4*w] ([:386]), a failed
      [malloc] ([:388], [:390]), or a [png_error]. *)
  cd_front : list Z -> option (Shape * list Z)
}.

(** The five [rt_fail] call sites, as a tag.  Keeping the arm identity out
    of the message bytes makes the dead-arm lemmas one [discriminate]. *)
Inductive RtArm : Set :=
| ArmDegenerate   (** [:312] [total == 0]                                  *)
| ArmNoBody       (** [:315] [enc.len <= kHdr]                             *)
| ArmIhdr         (** [:323] [!ok] with the flag clear                     *)
| ArmNeq          (** [:325] [dec[i] != pix[i]]                            *)
| ArmVacuous.     (** [:334] corrupted stream still reproduced P           *)

(** The [what] argument of [rt_fail] at each site, byte-for-byte.  All five
    literals confirmed in the delivered binary's rodata at VMAs 0x53640,
    0x53670, 0x53690, 0x536c0, 0x536d8 — the five addresses the five [jal
    rt_fail] sites load, in that order. *)
Definition rt_what (a : RtArm) : list Z :=
  match a with
  | ArmDegenerate => bos "degenerate (zero-size) image reached comparison"
  | ArmNoBody     => bos "encoder produced no PNG body"
  | ArmIhdr       => bos "decode(encode(P)) did not reproduce IHDR/size"
  | ArmNeq        => bos "decode(encode(P)) != P"
  | ArmVacuous    => bos "corrupted stream still reproduced P (check is vacuous)"
  end.

(** A fired guard: which arm, and [rt_fail]'s [off]/[a]/[b] arguments.
    [rf_off = None] models the C's [off == (size_t)-1] sentinel, which
    suppresses the middle [fprintf]; a genuine offset can never equal it
    ([i < total <= 2^63]). *)
Record RtFailure : Set := mkRtFailure {
  rf_arm : RtArm;
  rf_off : option Z;
  rf_a   : Z;
  rf_b   : Z
}.

Definition rf_plain (a : RtArm) : RtFailure := mkRtFailure a None 0 0.

(** [png_harness.c:197-209]:
<<
    fprintf(stderr, "ROUNDTRIP VIOLATION: %s", what);
    if (off != (size_t)-1)
      fprintf(stderr, " at byte %zu: got 0x%02x expected 0x%02x", off, a, b);
    fprintf(stderr, "\n");
    exit(HARNESS_FAIL_EXIT);
>>
    Three [fprintf]s (two when [off] is the sentinel), all to musl's
    UNBUFFERED stderr, so the byte stream is their concatenation.  Argument
    order is [off], then [a] = [dec[i]] (the GOT value), then [b] =
    [pix[i]] (the EXPECTED value) — [:325] passes [dec[i]] before [pix[i]].
    Both format strings confirmed in the binary's rodata at 0x435f8 and
    0x43610. *)
Definition RT_MSG (what : list Z) (off : option Z) (a b : Z) : list Z :=
  bos "ROUNDTRIP VIOLATION: " ++ what
  ++ (match off with
      | None => []
      | Some o => bos " at byte " ++ u_dec o
                  ++ bos ": got 0x" ++ hex2 a
                  ++ bos " expected 0x" ++ hex2 b
      end)
  ++ [LF].

Definition rt_msg (f : RtFailure) : list Z :=
  RT_MSG (rt_what (rf_arm f)) (rf_off f) (rf_a f) (rf_b f).

(** The outcome of one [assert_roundtrip] call. *)
Inductive RtOutcome : Set :=
| RtSkip                  (** a silent [return]: [:314] ([encode_raw]
                              returned 0), or one of the allocation-pattern
                              skips at [:318] and [:322]                   *)
| RtOk                    (** ran to [:337] without firing a guard         *)
| RtFail (f : RtFailure). (** [rt_fail] -> [MSG] then [exit 134]           *)

(** [png_harness.c:324-325] and [:333], the byte comparison.  Fuel is
    [total], read off [for (size_t i = 0; i < total; i++)].  Returns the
    FIRST mismatch with its index and the two bytes, in the C's argument
    order (got = [dec], expected = [pix]). *)
Fixpoint rt_cmp (n : nat) (i : Z) (dec pix : list Z) : option (Z * Z * Z) :=
  match n with
  | O => None
  | S k =>
      let a := nth (Z.to_nat i) dec 0 in
      let b := nth (Z.to_nat i) pix 0 in
      if a =? b then rt_cmp k (i + 1) dec pix else Some (i, a, b)
  end.

(** [png_harness.c:316] [if (corrupt && enc.len > 60) enc.buf[enc.len / 2] ^= 0xFF;].
    Test-only; [corrupt] is 0 on every driver path (§8). *)
Fixpoint list_upd (l : list Z) (i : nat) (f : Z -> Z) : list Z :=
  match l, i with
  | [], _ => []
  | x :: tl, O => f x :: tl
  | x :: tl, S k => x :: list_upd tl k f
  end.

Definition rt_corrupt (b : list Z) : list Z :=
  let n := Z.of_nat (length b) in
  if RT_CORRUPT_MIN <? n then list_upd b (Z.to_nat (n / 2)) (fun v => Z.lxor v 255)
  else b.

(** [png_harness.c:308-338], [assert_roundtrip], in full.

    The two [corrupt]/[expect_ok] parameters are kept so the transcription
    is faithful; the driver calls it only as [assert_rt C pix s false true]
    ([:353] and [:395]).  [harness_rt_pixels_compared] ([:326]) is a
    write-only counter — it is never read on this driver, so it is not
    modeled. *)
Definition assert_rt (C : Codec) (pix : list Z) (s : Shape)
                     (corrupt expect_ok : bool) : RtOutcome :=
  if sh_total s =? 0 then RtFail (rf_plain ArmDegenerate)         (* :312 *)
  else match cd_enc C pix s with
  | None => RtSkip                                                (* :314 *)
  | Some enc =>
      if Z.of_nat (length enc) <=? kHdr
      then RtFail (rf_plain ArmNoBody)                            (* :315 *)
      else
        let enc' := if corrupt then rt_corrupt enc else enc in    (* :316 *)
        (* :317-318's [malloc(total)] failure is an allocation-pattern
           skip; :319 clears the flag; :320 decodes. *)
        match cd_dec C enc' s with
        | Some dec =>
            match rt_cmp (Z.to_nat (sh_total s)) 0 dec pix with
            | None =>
                if expect_ok then RtOk                            (* :326 *)
                else RtFail (rf_plain ArmVacuous)                 (* :334 *)
            | Some (i, a, b) =>
                if expect_ok then RtFail (mkRtFailure ArmNeq (Some i) a b)  (* :325 *)
                else RtOk                                         (* :333, differs *)
            end
        | None =>
            if expect_ok then RtFail (rf_plain ArmIhdr)           (* :323 *)
            else RtOk    (* :331's [if (ok)] is false: nothing happens *)
        end
  end.

(** ** §6  [ReachableShapes] and the synthesised pixel family *)

(** [png_harness.c:352] [for (size_t i = 0; i < total; i++) orig[i] = data[i % size];]
    and [:125] (the same idiom in [run_write]).  [size >= 8] on every
    driver path, so the [i % size] never divides by zero; the Gallina
    [Nat.modulo _ 0 = _] convention keeps the function total anyway. *)
Definition synth_bytes (d : list Z) (n : Z) : list Z :=
  map (fun k => nth (Nat.modulo k (length d)) d 0) (seq 0 (Z.to_nat n)).

Lemma synth_bytes_length : forall d n, length (synth_bytes d n) = Z.to_nat n.
Proof. intros d n. unfold synth_bytes. now rewrite length_map, length_seq. Qed.

(** [png_harness.c:343-348]:
<<
    static const int cts[4] = { PNG_COLOR_TYPE_GRAY, PNG_COLOR_TYPE_RGB,
                                PNG_COLOR_TYPE_RGB_ALPHA, PNG_COLOR_TYPE_GRAY_ALPHA };
    int ct = cts[data[0] & 3];
    int bd = (data[1] & 1) ? 16 : 8;
    png_uint_32 w = 1 + (data[2] & 63);
    png_uint_32 h = 1 + (data[3] & 63);
>>
    Note the table order: index 1 is RGB (2) and index 2 is RGBA (6), so
    the tag values are NOT monotone in the index.  Note also that [bd]'s
    polarity here is the OPPOSITE of [run_write]'s ([:117]
    [bd = (data[2] & 1) ? 8 : 16]), and reads a different byte. *)
Definition ed_cts : list Z :=
  [PNG_CT_GRAY; PNG_CT_RGB; PNG_CT_RGB_ALPHA; PNG_CT_GRAY_ALPHA].

Definition ed_shape (d : list Z) : Shape :=
  mkShape (1 + Z.land (nth 2 d 0) 63)
          (1 + Z.land (nth 3 d 0) 63)
          (if Z.land (nth 1 d 0) 1 =? 1 then 16 else 8)
          (nth (Z.to_nat (Z.land (nth 0 d 0) 3)) ed_cts 0).

(** [png_harness.c:106-120], [run_write]'s synthetic image.  Transcribed
    for completeness: the phase is value-irrelevant (its sink only counts),
    but the shape family differs from [ed_shape]'s in three ways — a 32,
    not 64, dimension mask; the inverted depth polarity noted above; and
    interlacing, which the round-trip encodes never use. *)
Definition rw_shape (d : list Z) : Shape :=
  mkShape (1 + Z.land (nth 0 d 0) 31)
          (1 + Z.land (nth 1 d 0) 31)
          (if Z.land (nth 2 d 0) 1 =? 1 then 8 else 16)
          PNG_CT_RGB_ALPHA.

Definition rw_interlace (d : list Z) : Z :=
  if Z.land (nth 3 d 0) 1 =? 1 then 1 (* PNG_INTERLACE_ADAM7 *)
                               else 0 (* PNG_INTERLACE_NONE  *).

(** *** The reachable shape family

    This is precisely the domain the round-trip theorem must quantify over:
    the union of the two [assert_roundtrip] call sites' shapes. *)

(** [P2], [roundtrip_encode_decode] ([:341-355]): 64 x 64 x 2 x 4 = 32768
    shapes, all non-interlaced. *)
Definition RS_ed (s : Shape) : Prop :=
  1 <= sh_w s <= 64 /\ 1 <= sh_h s <= 64
  /\ (sh_bd s = 8 \/ sh_bd s = 16)
  /\ In (sh_ct s) ed_cts.

(** [P3], [roundtrip_decode_encode] ([:395]): canonical RGBA8 at whatever
    shape the input's IHDR gave, under [:376]'s work bound.  Unbounded in
    [w] and [h] separately, so this family is infinite; the round-trip
    theorem is universally quantified over the PIXELS, so only these SHAPE
    facts are consumed. *)
Definition RS_de (s : Shape) : Prop :=
  1 <= sh_w s /\ 1 <= sh_h s /\ sh_h s <= 100000000 / sh_w s
  /\ sh_bd s = 8 /\ sh_ct s = PNG_CT_RGB_ALPHA.

Definition ReachableShape (s : Shape) : Prop := RS_ed s \/ RS_de s.

(** Decision procedures, for [vm_compute] inside proofs and for the
    differential harness. *)
Definition rs_ed_b (s : Shape) : bool :=
  (1 <=? sh_w s) && (sh_w s <=? 64) && (1 <=? sh_h s) && (sh_h s <=? 64)
  && ((sh_bd s =? 8) || (sh_bd s =? 16))
  && ((sh_ct s =? 0) || (sh_ct s =? 2) || (sh_ct s =? 6) || (sh_ct s =? 4)).

Definition rs_de_b (s : Shape) : bool :=
  (1 <=? sh_w s) && (1 <=? sh_h s) && (sh_h s <=? 100000000 / sh_w s)
  && (sh_bd s =? 8) && (sh_ct s =? 6).

Lemma rs_ed_b_spec : forall s, rs_ed_b s = true <-> RS_ed s.
Proof.
  intros s. unfold rs_ed_b, RS_ed, ed_cts, PNG_CT_GRAY, PNG_CT_RGB,
    PNG_CT_RGB_ALPHA, PNG_CT_GRAY_ALPHA.
  rewrite !andb_true_iff, !orb_true_iff, !Z.leb_le, !Z.eqb_eq.
  cbn [In]. intuition lia.
Qed.

Lemma rs_de_b_spec : forall s, rs_de_b s = true <-> RS_de s.
Proof.
  intros s. unfold rs_de_b, RS_de, PNG_CT_RGB_ALPHA.
  rewrite !andb_true_iff, !Z.leb_le, !Z.eqb_eq. tauto.
Qed.

(** The [RS_ed] family, enumerated.  32768 shapes; small enough to sweep
    exhaustively on the delivered binary, which is what
    [a working folder] does. *)
Definition z_range (n : nat) : list Z := map (fun k => Z.of_nat (S k)) (seq 0 n).

Definition rs_ed_enum : list Shape :=
  flat_map (fun ct =>
    flat_map (fun bd =>
      flat_map (fun w => map (fun h => mkShape w h bd ct) (z_range 64))
               (z_range 64))
             [8; 16])
    ed_cts.

(* Stated over [Z]: the [nat] literal 32768 is unary and overflows the
   parser's stack. *)
Lemma rs_ed_enum_length : Z.of_nat (length rs_ed_enum) = 32768.
Proof. vm_compute. reflexivity. Qed.

Lemma rs_ed_enum_sound : forallb rs_ed_b rs_ed_enum = true.
Proof. vm_compute. reflexivity. Qed.

Lemma in_z_range : forall n v, 1 <= v <= Z.of_nat n -> In v (z_range n).
Proof.
  intros n v Hv. unfold z_range.
  apply in_map_iff. exists (Z.to_nat (v - 1)). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma rs_ed_enum_complete : forall s, RS_ed s -> In s rs_ed_enum.
Proof.
  (* NB: no [cbn in *] here — it would unfold [rs_ed_enum] in the goal and
     compute all 32768 shapes. *)
  intros [w h bd ct] (Hw & Hh & Hbd & Hct).
  cbn [sh_w sh_h sh_bd sh_ct] in Hw, Hh, Hbd, Hct.
  unfold rs_ed_enum. apply in_flat_map. exists ct. split; [exact Hct|].
  apply in_flat_map. exists bd. split.
  { cbn [In]. destruct Hbd as [-> | ->]; [left | right; left]; reflexivity. }
  apply in_flat_map. exists w. split; [apply in_z_range; cbn; lia|].
  apply in_map_iff. exists h. split; [reflexivity|].
  apply in_z_range; cbn; lia.
Qed.

(** The shape [P2] derives from an input is always in the family — the
    load-bearing fact, and it needs no hypothesis on the input bytes:
    [Z.land _ 63] is [_ mod 64] for every [Z], including negatives. *)
Lemma land_mask_range : forall x m, 0 <= m -> 0 <= Z.land x (Z.ones m) < 2 ^ m.
Proof.
  intros x m Hm. rewrite Z.land_ones by exact Hm.
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma land_63 : forall x, 0 <= Z.land x 63 <= 63.
Proof. intros x. pose proof (land_mask_range x 6 ltac:(lia)). cbn in *. lia. Qed.

Lemma land_3 : forall x, 0 <= Z.land x 3 <= 3.
Proof. intros x. pose proof (land_mask_range x 2 ltac:(lia)). cbn in *. lia. Qed.

Lemma ed_shape_RS : forall d, RS_ed (ed_shape d).
Proof.
  intros d. unfold RS_ed, ed_shape; cbn [sh_w sh_h sh_bd sh_ct].
  pose proof (land_63 (nth 2 d 0)). pose proof (land_63 (nth 3 d 0)).
  pose proof (land_3 (nth 0 d 0)).
  split; [lia|]. split; [lia|].
  split; [destruct (Z.land (nth 1 d 0) 1 =? 1); [right|left]; reflexivity|].
  unfold ed_cts, PNG_CT_GRAY, PNG_CT_RGB, PNG_CT_RGB_ALPHA, PNG_CT_GRAY_ALPHA.
  remember (Z.to_nat (Z.land (nth 0 d 0) 3)) as k eqn:Hkdef.
  assert (Hk : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3)%nat) by (subst k; lia).
  destruct Hk as [-> | [-> | [-> | ->]]]; cbn [nth In];
    [ left | right; left | right; right; left | right; right; right; left ];
    reflexivity.
Qed.

Lemma ed_shape_reachable : forall d, ReachableShape (ed_shape d).
Proof. intros d. left. apply ed_shape_RS. Qed.

(** Both families have a positive pixel count, which kills [:312]'s
    degenerate arm. *)
Lemma RS_ed_total_pos : forall s, RS_ed s -> 0 < sh_total s.
Proof.
  intros [w h bd ct] (Hw & Hh & Hbd & Hct); cbn in *.
  unfold sh_total, channels_of, PNG_CT_GRAY, PNG_CT_GRAY_ALPHA,
         PNG_CT_RGB, PNG_CT_RGB_ALPHA; cbn [sh_w sh_h sh_bd sh_ct].
  unfold ed_cts, PNG_CT_GRAY, PNG_CT_RGB, PNG_CT_RGB_ALPHA,
         PNG_CT_GRAY_ALPHA in Hct; cbn [In] in Hct.
  destruct Hbd as [->| ->];
    (destruct Hct as [<-|[<-|[<-|[<-|[]]]]]; cbn; nia).
Qed.

Lemma RS_de_total_pos : forall s, RS_de s -> 0 < sh_total s.
Proof.
  intros [w h bd ct] (Hw & Hh & _ & Hbd & Hct); cbn in *; subst.
  unfold sh_total, channels_of, PNG_CT_GRAY, PNG_CT_GRAY_ALPHA,
         PNG_CT_RGB, PNG_CT_RGB_ALPHA; cbn. nia.
Qed.

Lemma reachable_total_pos : forall s, ReachableShape s -> 0 < sh_total s.
Proof. intros s [H|H]; [apply RS_ed_total_pos|apply RS_de_total_pos]; exact H. Qed.

(** ** §7  [LLVMFuzzerTestOneInput]: the six phases ([:426-455])

    A data description of the dispatch, not a simulation of libpng.  Every
    phase creates and destroys its own [png_struct]s; no state flows
    between phases through libpng — only through the heap allocator and the
    two harness globals. *)
Inductive Phase : Set :=
| Ph_read          (** [:428] [run_read]                  ([:134-169]) *)
| Ph_rt_ed         (** [:430] [roundtrip_encode_decode]   ([:341-355]) *)
| Ph_rt_de         (** [:431] [roundtrip_decode_encode]   ([:360-400]) *)
| Ph_progressive   (** [:434] [run_progressive]           ([:89-100])  *)
| Ph_write         (** [:437] [run_write]                 ([:106-131]) *)
| Ph_simplified.   (** [:439-453] the inline simplified block          *)

Definition phases : list Phase :=
  [Ph_read; Ph_rt_ed; Ph_rt_de; Ph_progressive; Ph_write; Ph_simplified].

(** Only the two round-trip phases can reach [rt_fail]; every other phase
    is silent on every path. *)
Definition phase_can_rt_fail (p : Phase) : bool :=
  match p with Ph_rt_ed | Ph_rt_de => true | _ => false end.

(** Each phase's own entry gate, over and above [:427]'s [size < 8]. *)
Definition phase_gate (p : Phase) (n : Z) : bool :=
  match p with
  | Ph_read        => true      (** [:135] gates on the SIGNATURE, not the size *)
  | Ph_rt_ed       => 4 <=? n   (** [:342] [if (size < 4) return]              *)
  | Ph_rt_de       => kHdr <=? n(** [:361] [size < kHdr] or bad signature      *)
  | Ph_progressive => true
  | Ph_write       => 4 <=? n   (** [:107] [if (size < 4) return]              *)
  | Ph_simplified  => true
  end.

(** [:427]'s gate subsumes both [size < 4] gates, so neither ever fires on
    a driver path. *)
Lemma phase_gates_subsumed :
  forall n, sz_gated n = false -> forallb (fun p => phase_gate p n) phases = true.
Proof.
  intros n H. unfold sz_gated, kHdr in H. apply Z.ltb_ge in H.
  unfold phases. cbn [forallb phase_gate]. unfold kHdr.
  assert (H4 : (4 <=? n) = true) by (apply Z.leb_le; lia).
  assert (H8 : (8 <=? n) = true) by (apply Z.leb_le; lia).
  rewrite H4, H8. reflexivity.
Qed.

(** ** §8  Facts

    The three guard arms the campaign notes classify as statically excluded
    on this driver, then the top-level predicate and its Route-A collapse. *)

(** *** Arm 1 ([:312], degenerate image): dead on both call sites, because
    [w, h >= 1] by construction and [ch >= 1] for every colour type the
    driver builds. *)
Lemma arm_degenerate_dead :
  forall C pix s corrupt expect_ok,
    ReachableShape s -> assert_rt C pix s corrupt expect_ok <> RtFail (rf_plain ArmDegenerate).
Proof.
  intros C pix s corrupt expect_ok Hs.
  pose proof (reachable_total_pos s Hs) as Hpos.
  unfold assert_rt. rewrite (proj2 (Z.eqb_neq _ _)) by lia.
  destruct (cd_enc C pix s) as [enc|]; [|discriminate].
  destruct (Z.of_nat (length enc) <=? kHdr); [discriminate|].
  destruct (cd_dec C _ s) as [dec|];
    [destruct (rt_cmp _ 0 dec pix) as [[[i a] b]|]|];
    destruct expect_ok; discriminate.
Qed.

(** *** Arm 2 ([:315], no PNG body): dead once the encoder completes.  The
    obligation is on the codec — a completed [encode_raw] emits at least
    the 8-byte signature, a 25-byte IHDR chunk and a 12-byte IEND, i.e.
    [>= 45] bytes, comfortably past [kHdr]. *)
Definition codec_body (C : Codec) : Prop :=
  forall pix s enc, cd_enc C pix s = Some enc -> kHdr < Z.of_nat (length enc).

Lemma arm_nobody_dead :
  forall C pix s corrupt expect_ok,
    codec_body C -> assert_rt C pix s corrupt expect_ok <> RtFail (rf_plain ArmNoBody).
Proof.
  intros C pix s corrupt expect_ok Hb. unfold assert_rt.
  destruct (sh_total s =? 0); [discriminate|].
  destruct (cd_enc C pix s) as [enc|] eqn:He; [|discriminate].
  rewrite (proj2 (Z.leb_gt _ _)) by (apply Hb with (pix := pix) (s := s); exact He).
  destruct (cd_dec C _ s) as [dec|];
    [destruct (rt_cmp _ 0 dec pix) as [[[i a] b]|]|];
    destruct expect_ok; discriminate.
Qed.

(** *** Arm 5 ([:334], the vacuity check): dead because [corrupt = 0] and
    [expect_ok = 1] on every driver path, and the arm lives in the
    [expect_ok = 0] branch.

    Source: [assert_roundtrip] has four call sites in the C ([:353], [:395],
    [:414], [:416]); only [:416] passes [corrupt = 1], and it is inside
    [harness_roundtrip_selftest], which nothing calls.  Confirmed in the
    delivered binary: [objdump] finds exactly four [jal 10ad8
    <assert_roundtrip>] — at 0x11740 (P2, inlined into
    LLVMFuzzerTestOneInput), 0x11184 (P3, in roundtrip_decode_encode) and
    0x115bc / 0x115e8 (in harness_roundtrip_selftest) — and ZERO callers of
    [harness_roundtrip_selftest] (0x11564), with no 8-byte occurrence of
    that address anywhere inside a PT_LOAD segment, so it is not reached
    indirectly either.  797 traced calls on real inputs all carried
    [corrupt = 0, expect_ok = 1].

    The same [objdump] pass finds exactly five [jal 10a64 <rt_fail>], all
    inside [assert_roundtrip], loading the five [rt_what] literals in the
    order 0x53640 / 0x536d8 / 0x53690 / 0x536c0 / 0x53670 — i.e. exactly
    the five [RtArm]s, with [(off, a, b) = (-1, 0, 0)] materialised as
    immediates at the four plain arms and left in live registers at
    [ArmNeq]. *)
Lemma arm_vacuous_dead :
  forall C pix s corrupt, assert_rt C pix s corrupt true <> RtFail (rf_plain ArmVacuous).
Proof.
  intros C pix s corrupt. unfold assert_rt.
  destruct (sh_total s =? 0); [discriminate|].
  destruct (cd_enc C pix s) as [enc|]; [|discriminate].
  destruct (Z.of_nat (length enc) <=? kHdr); [discriminate|].
  destruct (cd_dec C _ s) as [dec|];
    [destruct (rt_cmp _ 0 dec pix) as [[[i a] b]|]|]; discriminate.
Qed.

(** With those three gone, only [ArmIhdr] and [ArmNeq] can fire, and both
    are decided by the codec. *)
Lemma live_arms :
  forall C pix s corrupt f,
    ReachableShape s -> codec_body C ->
    assert_rt C pix s corrupt true = RtFail f ->
    rf_arm f = ArmIhdr \/ rf_arm f = ArmNeq.
Proof.
  intros C pix s corrupt f Hs Hb H.
  pose proof (reachable_total_pos s Hs) as Hpos.
  unfold assert_rt in H. rewrite (proj2 (Z.eqb_neq _ _)) in H by lia.
  destruct (cd_enc C pix s) as [enc|] eqn:He; [|discriminate].
  rewrite (proj2 (Z.leb_gt _ _)) in H
    by (apply Hb with (pix := pix) (s := s); exact He).
  destruct (cd_dec C _ s) as [dec|];
    [destruct (rt_cmp _ 0 dec pix) as [[[i a] b]|]|];
    inversion H; subst; cbn; tauto.
Qed.

(** *** [rt_viol]: does any round-trip guard fire on the input bytes?

    A function of the FILE BYTES ALONE (E2), which is what makes the
    per-file classification independent of the allocation pattern.  The two
    round-trip phases run in source order ([:430] then [:431]); [P2] exits
    the process if it fires, so [P3] is only reached when [P2] is clean. *)
Definition rt_ed (C : Codec) (d : list Z) : RtOutcome :=
  if Z.of_nat (length d) <? 4 then RtSkip                       (* :342 *)
  else let s := ed_shape d in
       assert_rt C (synth_bytes d (sh_total s)) s false true.   (* :353 *)

Definition rt_de (C : Codec) (d : list Z) : RtOutcome :=
  match cd_front C d with
  | None => RtSkip
  | Some (s, pix) => assert_rt C pix s false true               (* :395 *)
  end.

Definition rt_outcome (C : Codec) (d : list Z) : RtOutcome :=
  match rt_ed C d with
  | RtFail f => RtFail f
  | _        => rt_de C d
  end.

Definition rt_viol (C : Codec) (d : list Z) : bool :=
  match rt_outcome C d with RtFail _ => true | _ => false end.

(** Route B's message: the exact bytes the binary would write.  Defined
    here so that keeping the arm costs no interface change. *)
Definition rt_viol_msg (C : Codec) (d : list Z) : option (list Z) :=
  match rt_outcome C d with
  | RtFail f => Some (rt_msg f)
  | _        => None
  end.

Lemma rt_viol_msg_iff :
  forall C d, rt_viol C d = true <-> exists m, rt_viol_msg C d = Some m.
Proof.
  intros C d. unfold rt_viol, rt_viol_msg.
  destruct (rt_outcome C d); split; try discriminate;
    intros H; try (destruct H; discriminate); eauto.
Qed.

(** *** The caller obligations on the codec — the [_wf] predicate *)
Definition codec_front_wf (C : Codec) : Prop :=
  forall d s pix, cd_front C d = Some (s, pix) ->
                  RS_de s /\ Z.of_nat (length pix) = sh_total s.

Definition codec_wf (C : Codec) : Prop := codec_body C /\ codec_front_wf C.

(** *** Route A: the round-trip theorem, and the collapse it buys

    [codec_ed_id] is exactly the pixel-domain identity
    [decode(encode(P)) = P] on the reachable shapes.  It is the ONE
    obligation the round-trip mathematics owes; everything else about the
    rt arm is discharged here, once. *)
Definition codec_ed_id (C : Codec) : Prop :=
  forall s pix enc,
    ReachableShape s ->
    Z.of_nat (length pix) = sh_total s ->
    cd_enc C pix s = Some enc ->
    cd_dec C enc s = Some pix.

Lemma rt_cmp_refl : forall n i l, rt_cmp n i l l = None.
Proof.
  induction n as [|n IH]; intros i l; cbn; [reflexivity|].
  now rewrite Z.eqb_refl.
Qed.

Lemma assert_rt_clean :
  forall C pix s,
    ReachableShape s -> codec_body C -> codec_ed_id C ->
    Z.of_nat (length pix) = sh_total s ->
    assert_rt C pix s false true = RtSkip \/ assert_rt C pix s false true = RtOk.
Proof.
  intros C pix s Hs Hb Hid Hlen.
  pose proof (reachable_total_pos s Hs) as Hpos.
  unfold assert_rt. rewrite (proj2 (Z.eqb_neq _ _)) by lia.
  destruct (cd_enc C pix s) as [enc|] eqn:He; [|now left].
  rewrite (proj2 (Z.leb_gt _ _)) by (apply Hb with (pix := pix) (s := s); exact He).
  cbn match. rewrite (Hid s pix enc Hs Hlen He).
  rewrite rt_cmp_refl. now right.
Qed.

Theorem rt_viol_false :
  forall C, codec_wf C -> codec_ed_id C -> forall d, rt_viol C d = false.
Proof.
  intros C [Hb Hf] Hid d. unfold rt_viol, rt_outcome.
  assert (Hed : rt_ed C d = RtSkip \/ rt_ed C d = RtOk).
  { unfold rt_ed. destruct (Z.of_nat (length d) <? 4); [now left|].
    apply assert_rt_clean; auto using ed_shape_reachable.
    - now rewrite synth_bytes_length, Z2Nat.id
        by (apply Z.lt_le_incl, reachable_total_pos, ed_shape_reachable). }
  assert (Hde : rt_de C d = RtSkip \/ rt_de C d = RtOk).
  { unfold rt_de. destruct (cd_front C d) as [[s pix]|] eqn:Hfr; [|now left].
    destruct (Hf d s pix Hfr) as [Hrs Hlen].
    apply assert_rt_clean; auto. now right. }
  destruct Hed as [-> | ->]; destruct Hde as [-> | ->]; reflexivity.
Qed.

(** The Route-A payoff, stated the way WP-1's [rt_arm] consumes it: under
    the round-trip theorem the arm is definitionally the continuation, so
    the 134 printing walk is never written.  Route B keeps [rt_viol] and
    [rt_viol_msg] as they stand and needs no change here. *)
Corollary rt_arm_collapses :
  forall (A : Type) (fail cont : A) C,
    codec_wf C -> codec_ed_id C ->
    forall d, (if rt_viol C d then fail else cont) = cont.
Proof. intros A fail cont C Hwf Hid d. now rewrite rt_viol_false. Qed.
