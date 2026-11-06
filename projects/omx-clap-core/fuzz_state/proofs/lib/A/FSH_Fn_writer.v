(* fs program part, WRITER group: the ASan contract of each writer function of fuzz_state.asan, in S0's form
   (lib/A/FSH_Gen.v fpreU / fpostU / wkeep, lib/A/FSH_Base.v's fs.asan numerals and STK_f).
   Functions: put, indent, put_string, write_value (level-indexed), pj_write, preset_base64_encode,
   preset_base64_decode. STATEMENTS ONLY.

   What each function computes comes from fs's released pure models, not from this file: lib/Prog/WriterSpec.v
   (esc / spieces / wstr / newcap / b64_enc / b64_dec), lib/Prog/WriterApp.v (the writer state wst and put1 /
   putN), lib/Prog/WriterValue.v (wind / wvpieces / wdoc), lib/Spec/PjTree.v. fs's released PLAIN contracts
   lib/Prog/<f>_c.v are the template for every functional premise and post.

   Two shapes are worth reading before the specs:
   (a) THE CALLER'S OBJECT. pj_write keeps its `struct pj_out` on its own REAL stack (no fake frame; 32 bytes at
       its entry sp - 56 .. sp - 24), and passes its address down to put, indent, put_string and write_value.
       That object is ABOVE those callees' stack pointers, so the donor's journal window [sp - STK, sp) forbids
       the writes `put` must make. `ajournal` takes the window top sp0 as a parameter, and the donor itself uses
       that freedom (lib/A/ACes.v:164 rd_entry), so S0's `fpostU` exposes sp0: each such post runs the window to
       `ot` (the end of the object) and gives the slack straight back with FSH_Gen's `wkeep`, which keeps every
       byte of [sp, ot) outside the object. preset_base64_decode's `*lenp` is the same shape, 8 bytes one call
       level up. The READER lane states parse_string / parse_items / literal the same way, over `struct pj_in`.
   (b) THE NARROW FORM ON THE HARNESS DOCUMENT (a Theorem Labs lane 20:36Z, a Theorem Labs lane confirmed). put_string carries
       `plain_bytes`, and write_value / pj_write the tree form `jv_plain`: no string byte below 0x20, no 0x22 and no 0x5c. READER's named hypothesis FS_DOC_STRS (owner a Theorem Labs lane) discharges it for the document
       fs.c:237-248 builds. With it put_string takes only its plain-byte path: its two-char escape arm and its
       \u%04x arm (the escape dispatch PS_ESC 0x85c84, whose snprintf call is at 0x85d04 (callee
       PS_FMT 0x42694, returning to PS_FMT_RET 0x85d08; S0 FSH_Fn_FORM section 4 names the call site); the generation-N image-A proof, commit 211ff3e9df0 lib/A/Prog/put_string_blocks.v:447-451, not in this tree) are unreachable, so snprintf leaves this
       group. The premise is stated, never assumed silently, and the posts keep the general `spieces` / `wdoc`
       text, under which it makes `esc` the identity.

   Form: S0's FSH_Fn_FORM.md sections 1-3 (no CTX: dropped 2026-10-29 once RELOC's C5 landed; the frames premise, the
   16-aligned window top `ot` with `wkeep` covering the slack, and the level-indexed recursion
   write_value_spec_at k with STK_write_value (2 - k)).
   Ported from: a Theorem Labs lane's lib/A/FMH_Fn.v (form), S0 a working branch 0433af44ccd (names and numerals).
   Rule 24 (proof-index v5 built 2026-10-28T21:58:24Z, exit 0, read from a file, not a pipe): put, indent,
   put_string, write_value, pj_write, preset_base64_encode and preset_base64_decode have RELEASED proofs for fs's
   PLAIN and UBSAN builds only (lib/Prog, lib/U/Prog, ossv/recipes@566eb6ffa5, release/pau-projects-recipes@b6a0088adc),
   none for an ASan build. Those plain contracts / proofs are the templates used here, not drop-ins. *)

From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
(* READER's one placement predicate for a `struct pj` (FSH_Fn_reader.pobj; Required, used qualified, so no image-A
   name enters the image-B file) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable segs : list Segment.   (* FSH_Base's choice: the image is a Section variable here, and the
                                   harness fixes it (lib/A/FSH_Harness.v segs := tfibsegs, lib/B's := fsbsegs) *)
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- model numerals, copied from fs's released plain contracts so that no frozen statement file is imported ---- *)
(* WMAX: the plain contract's 2^28 (lib/Prog/put_c.v:17) halved. On the ASan side the buffer is a fuzz_realloc
   block of cap + HEAD bytes and the core caps a request at MALLOC_MAX = 2^28 (Reusable/YG00.v:39), so a buffer of
   2^28 would be a request the allocator refuses. With the text below 2^27 the buffer's class is at most 2^27. *)
Definition WMAX : Z := 2 ^ 27.
Definition enc_size (len : Z) : Z := (len + 2) / 3 * 4 + 1.          (* lib/Prog/preset_base64_encode_c.v:17 *)
Definition dec_size (tb : list Z) : Z :=
  Z.of_nat (length tb) / 4 * 3 + 3.                                  (* lib/Prog/preset_base64_decode_c.v:16 *)

(* ---- budgets that CHAIN across several put calls (a Theorem Labs lane 22:43Z: per-call constants cannot be re-established
   between puts). The writer's buffer is the only block a writer call allocates, and its size class bounds what is
   left to spend:
   - grows: the buffer is 0 or 4096 * 2^j with 4096 * 2^j <= WMAX, so `wgrows cap` grows already done is at most
     WGROWS_MAX = 16 (0 -> 4096 -> ... -> 2^27), and each grow is one fuzz_realloc: EV_fuzz_realloc = 3 ticks
     (FSH_Gen.v:49) and one count; the one refused allocation also costs at most 3 ticks and one count, after which
     `failed` is set and no put allocates again. `wbud failed cap` is what is left: (WGROWS_MAX + 1 - wgrows cap)
     while not failed, 0 once failed. Every multi-put spec takes `st_nev S + 3 * wbud <= EV_MAX` and
     `cnt + wbud < 2^64`, and its post gives the same two facts back for the new state, so a caller chains them.
   - live bytes: everything but the buffer is untouched, so `live - cap` (g_live) and `blocks_bytes S - bsz cap`
     (the core's allocated request sizes, YG01.v:222) are invariants; during a grow the old and the new buffer are
     both allocated, hence the 2 * WMAX and 2 * (WMAX + HEAD) slack. ---- *)
Definition WGROWS_MAX : Z := 16.
Definition wgrows (cap : Z) : Z := if cap =? 0 then 0 else Z.log2 (cap / 4096) + 1.
Definition wbud (failed cap : Z) : Z := if failed =? 0 then WGROWS_MAX + 1 - wgrows cap else 0.
Definition bsz (cap : Z) : Z := if cap =? 0 then 0 else cap + HEAD.
(* room for the one block encode / decode allocate: enc_size len + HEAD <= 178956989 for len <= 2^27 and
   dec_size tb + HEAD <= 201326611 for length tb <= 2^28, both below 2^28 (a Theorem Labs lane 23:37Z: 2^23 could
   not meet fuzz_malloc_spec's room premise above ~6 MiB). Callers meet it: LIVE_MAX = 2^34. *)


(* BUDGETS BY THE CALL'S OWN TRACE (a Theorem Labs lane 00:18Z and 00:45Z, a Theorem Labs lane's crt budget audit): a premise that pins
   a fixed worst case forces every caller to carry a budget it never spends. The writer model records each
   fuzz_realloc request in w_calls (WriterApp.put1), so a call's ticks are at most 3 per request (EV_fuzz_realloc;
   the first grow, from NULL, costs 1), its count rises by one per request, and the most it holds at once is the
   old and the new buffer (< 2 * (final cap + HEAD)). *)
Definition wcalls (st : WriterApp.wst) : Z := Z.of_nat (length (WriterApp.w_calls st)).
(* A writer call's EVENTS by its own trace. Each request in w_calls is one fuzz_realloc call, which costs
   EV_fuzz_realloc = 3 - EXCEPT a request made while the buffer is still NULL: fuzz_realloc serves p = 0 by
   tail-calling fuzz_malloc, one event (FSH_Gen.v:76). A call that starts from w0 (cap = 0, calls = []) makes
   exactly one such request, its first, because put1 only grows a buffer it has just allocated. pj_write is
   that case and uses wev0; put / indent / put_string / write_value start from a caller's buffer whose cap may
   be anything, so they keep the uniform 3 per request. Found by a Theorem Labs lane on S0 7c46ddd1720 (reloc-check
   item 3, D2): with 3 charged for the first request too, check_round_trip's two-realloc path summed to 80
   against its reserved 78. *)
Definition wev0 (st : WriterApp.wst) : Z :=
  match WriterApp.w_calls st with
  | [] => 0
  | _ :: r => EV_fuzz_malloc + EV_fuzz_realloc * Z.of_nat (length r)
  end.

(* The journal count a multi-put call hands back, BY ITS OWN TRACE AND ITS STARTING CAPACITY. At cap <> 0 every
   request is a real fuzz_realloc, 3 events each. At cap = 0 the FIRST request is served by fuzz_realloc's p = 0
   arm, which tail-calls fuzz_malloc and journals 1 (FSH_Fn_alloc.v:219), and after it either the buffer exists
   (cap <> 0 from then on) or `failed` is sticky and no further request is made - so at most one request in the
   whole call is the cheap one, which is exactly wev0. Found by a Theorem Labs lane, 2026-10-29: pj_write's own count is
   wev0, and it is BUILT from its callees' counts, so a callee that reports the uniform 3 per request makes
   pj_write's post underivable (ajournal's k is an upper bound and only ever rises). *)
Definition wevk (cap : Z) (st : WriterApp.wst) : Z :=
  if cap =? 0 then wev0 st else EV_fuzz_realloc * wcalls st.

Definition wbudget_pre (S : astate) (cap cnt live : Z) (st' : WriterApp.wst) : Prop :=
  st_nev S + wevk cap st' <= EV_MAX /\
  blocks_bytes S - bsz cap + 2 * (WriterApp.w_cap st' + HEAD) <= LIVE_MAX /\
  live - cap + 2 * WriterApp.w_cap st' < 2 ^ 64 /\ cnt + wcalls st' < 2 ^ 64.

(* decode's ticks on its own arm: one malloc on success, malloc + free on a bad text *)
Definition dec_ev (tb : list Z) : Z :=
  match WriterSpec.b64_dec tb with Some _ => EV_fuzz_malloc | None => EV_preset_base64_decode end.

(* JOURNAL COUNTS BY THE CALL'S OWN TRACE (a Theorem Labs lane 00:18Z rule: a fixed constant that overshoots on some path
   makes the caller unprovable there, since ajournal's k only adds up). A multi-put call journals
   3 * (wbud failed cap - wbud failed' cap'): what it took out of the size-class budget, 3 per grow and 3 for the one
   refusal, 0 when nothing grew; these telescope across a caller's calls. pj_write journals what its write took
   out of a fresh budget, plus EV_fuzz_free on the failure path. *)
(* the budget facts a multi-put post hands back (premise forms: st_nev S + 3 * wbud failed cap <= EV_MAX,
   blocks_bytes S - bsz cap + 2 * (WMAX + HEAD) <= LIVE_MAX, live - cap + 2 * WMAX < 2^64,
   cnt + wbud failed cap < 2^64, cap <= WMAX) *)
Definition wbudget_kept (S S' : astate) (failed cap cnt failed' cap' cnt' : Z) : Prop :=
  cap' <= WMAX /\ blocks_bytes S' - bsz cap' <= blocks_bytes S - bsz cap /\ cnt <= cnt'.

(* ================= the writer's out-object ================= *)
(* `struct pj_out` (preset_file.c:446-452) as the ASan walk sees it: fs's plain put_c.v:52-63 pj_out_ok, with
   the buffer a live reader block (FSH_Gen's fs_rblock, whose 16-byte head is user-poisoned while live). *)
Definition wout_ok (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
    (o buf cap failed : Z) (text : list Z) : Prop :=
  o mod 8 = 0 /\ 0 <= o /\ o + 32 <= ly_top ly /\
  (forall i, 0 <= i < 32 -> writable_at segs (rdW W mem) (o + i) /\ apresent (w_H W) mem (o + i)) /\
  0 <= buf < 2 ^ 64 /\ 0 <= cap < 2 ^ 64 /\
  val_mem segs (rdW W mem) o 8 buf /\
  val_mem segs (rdW W mem) (o + 8) 8 (Z.of_nat (length text)) /\
  val_mem segs (rdW W mem) (o + 16) 8 cap /\
  val_mem segs (rdW W mem) (o + 24) 4 failed /\ (failed = 0 \/ failed = 1) /\
  WriterSpec.bytes_ok text /\
  ((cap = 0 /\ buf = 0 /\ text = []) \/
   ((exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) /\
    fs_rblock segs B ly S W mem buf cap /\
    Z.of_nat (length text) < cap /\
    zbytes_at segs W mem buf (text ++ [0]))).

(* How the live user-poisoned heads move when the writer's buffer grows: the head either stays, or leaves U and
   a new one joins, or - at the first allocation, when cap = 0 - only joins. Intermediate buffers of a
   multi-put call are freed inside it, so only the last one is live at the return. *)
Definition uswap (U U' : list (Z * Z)) (buf buf' cap : Z) : Prop :=
  (U' = U /\ buf' = buf) \/
  (exists U1 U2, U = U1 ++ (buf - HEAD, HEAD) :: U2 /\ U' = U1 ++ U2 ++ [(buf' - HEAD, HEAD)]) \/
  (cap = 0 /\ U' = U ++ [(buf' - HEAD, HEAD)]).

(* the footprint a writer call may change outside its window: the old buffer, freed when it grows (the
   whole block, head included, as a (lo, hi) range, which is how inFP reads FP; YI04.v:390). fs's alloc.c
   statics are S0's FS_PSTAT_FP (owner 21:23Z): every writer call reaches fuzz_malloc / _realloc / _free. *)
Definition wbuf_fp (buf cap : Z) : list (Z * Z) := if cap =? 0 then [] else [(buf - HEAD, buf + cap)].

(* the ablocks twin of uswap (a Theorem Labs lane 22:47Z): the writer's buffer block either stays, or is removed and its
   successor appended (fuzz_realloc's post shape, lib/A/FSH_Fn_alloc.v), or - at the first allocation, when
   cap = 0 - is only appended; every other block is untouched. A caller (pj_write) reads its own post's
   ablocks clause off this. *)
Definition bswap (A A' : list (Z * Z)) (buf buf' cap cap' : Z) : Prop :=
  (buf' = buf /\ cap' = cap /\ A' = A) \/
  (cap = 0 /\ exists C1 C2, A' = C1 ++ (buf' - HEAD, cap' + HEAD) :: C2 /\ C1 ++ C2 = A) \/
  (exists A1 A2 C1 C2, A = A1 ++ (buf - HEAD, cap + HEAD) :: A2 /\
     A' = C1 ++ (buf' - HEAD, cap' + HEAD) :: C2 /\ C1 ++ C2 = A1 ++ A2).
(* arm 2 is NOT an append either, for the same reason one level up: a call that starts at cap = 0 and grows
   TWICE does fuzz_malloc and then fuzz_realloc, and the second block may land anywhere, so the composite is
   `A' = C1 ++ new :: C2` with C1 ++ C2 = A. The append is the case C1 = A, C2 = [], so put's single-malloc
   arm still derives it. Measured by a Theorem Labs lane, 2026-10-29. *)
(* arm 3 is the REALLOC form, not an append: fuzz_realloc_spec's granted p <> 0 post places the new block
   anywhere in the list (FSH_Fn_alloc.v:199-237), so `A' = A1 ++ A2 ++ [new]` was not derivable - measured by
   a Theorem Labs lane on put's grow arm, 2026-10-29. blocks_bytes still follows, through AD1r.blocks_bytes_ablocks
   and bsum_perm, since C1 ++ C2 is a permutation of the old list minus the old block. *)

(* where a byte range the writer READS lives, in a form that survives allocator calls (a Theorem Labs lane 22:49Z: an entry
   `zbytes_at` says nothing about the SHADOW, and ajournal keeps no shadow byte across fuzz_realloc / fuzz_malloc,
   so a bare entry fact cannot stand for the reads after a call; a range inside the USER bytes of a live reader
   block, never its user-poisoned head, can, from AR and block membership). Either nothing is read, or the range is
   inside the user bytes [p, p + k) of a live reader block other than the writer's own buffer, or it is a prefix of
   one of fs's read-only strings (S0's FS_RO_STRS, lib/A/FSH_Rt.v:35-, which holds every literal the writer puts). *)
Definition wsrc_kept (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (mem : word -> option byte)
    (buf s : Z) (bs : list Z) : Prop :=
  (* nothing is read, but the interceptor still range-checks the pointer (a Theorem Labs lane 00:01Z: put's
     memcpy(buf + len, s, 0) needs amem_range s 0, false in the shadow gap) *)
  (bs = [] /\ amem_range s 0) \/
  (exists p k, p <> buf /\ fs_rblock segs B ly S W mem p k /\ p <= s /\ s + Z.of_nat (length bs) <= p + k) \/
  (* any live block, a plain interceptor malloc block included (a Theorem Labs lane 23:09Z: the entry's base64 text is
     one, with no fuzz head), other than the buffer's, the range avoiding every user-poisoned range: S0's
     cstr_kept shape (FSH_Rt.v), as a Theorem Labs lane asked 23:13Z *)
  (exists p k, p <> buf - HEAD /\ In (p, k) (ablocks B ly S) /\
     p <= s /\ s + Z.of_nat (length bs) <= p + k /\
     (forall r, In r U -> fst r + snd r <= s \/ s + Z.of_nat (length bs) <= fst r)) \/
  (* a prefix of an fs read-only literal, its terminating 0 included *)
  (exists l, In (s, l) FS_RO_STRS /\ (length bs <= Nat.succ (length l))%nat).

(* the post of a callee that writes the caller's object: S0's fpostU with the window top raised to `ot` *)
Definition wpost (STK ot : Z) (FP : list (Z * Z)) (regs : bvmap 5 word)
    (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (mem : word -> option byte) (md : Model)
    (k : Z) (U' : list (Z * Z))
    (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fpostU segs B (STK + (ot - spZ regs)) ot FP regs ly S U W mem md k U' Q.

(* ---- the narrow form's premise (plain_byte / plain_bytes / jv_plain) is S0's, FSH_Gen.v:144-: one definition
   shared with the walks and with READER's FS_DOC_STRS (see (b) in the header) ---- *)

(* the tree the writer reads: every node byte is in a live reader block *)
Definition ublocks_ok (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
    (UL : list (Z * Z)) : Prop :=
  forall a k, In (a, k) UL -> fs_rblock segs B ly S W mem a k.

(* ================= put ================= *)
(* preset_file.c:454-476: appends n bytes at s to o's buffer, growing it with fuzz_realloc when it does not fit.
   Model: WriterApp.put1 over (failed, text, cap, cnt, fail). Four arms, as plain put_c.v:86-116. *)
(* NO CTX PREMISE (owner a Theorem Labs lane 05:00Z, with ALLOC's matching drop in FSH_Fn_alloc.v): the writer specs
   used to require `In (raZ regs :: spine ch) CTX`. A Theorem Labs lane PROVED it unsatisfiable for any finite CTX in a
   reachable state - write_value's top-level arm reads word[o-8] = pj_write's frame slot 0, which pj_write never
   writes - so a theorem over it could be vacuously green. It is no longer needed: RELOC's C5 lets an
   allocator call rest on `In (call_trace ...) (as_universe B) \/ st_nev S < EV_MAX` (FSupoisonU.v:194 / :217),
   and each spec's own budget premise gives the second disjunct. The CTX PARAMETER is dropped with it (owner
   ruling 05:05Z: an unused binder is dead weight and keeps every caller passing a meaningless list). *)
Definition put_spec : Prop :=
  forall ly S U W regs mem md ch ot o s n buf cap failed (text bs : list Z) live peak cnt fail,
  fpreU segs B STK_put ly S U W regs mem md ch -> fs_heads B ly S U ->
  (* + 1: put_string calls put while its own class-0 fake frame is live (a Theorem Labs lane 22:44Z) *)
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE + 1 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s -> getr regs 12 = w64 n ->
  wout_ok ly S W mem o buf cap failed text -> fs_glob segs W mem live peak cnt fail ->
  (* the live buffer's head is user-poisoned: fuzz_realloc's p <> 0 arm asks `exists U1 U2, U = U1 ++ (p - HEAD,
     HEAD) :: U2`, and nothing else in this spec puts the head in U (wout_ok takes no U, fs_rblock has no
     poison clause, fs_heads runs U -> blocks). Every caller holds it: pj_write starts at cap = 0, and each
     post's uswap keeps U (arm 1) or puts (buf' - HEAD, HEAD) in U' (arms 2 / 3). A Theorem Labs lane, 2026-10-29. *)
  (cap <> 0 -> In (buf - HEAD, HEAD) U) ->
  (* the out-object lies in the caller's frame, above this one *)
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (* the frame chain an allocator call reads at s0 = o (approved a Theorem Labs lane 00:01Z; refined by a Theorem Labs lane 01:3xZ): either o is
     right above this frame (called from pj_write: o - 16 is this function's own saved-ra slot, written by the prologue
     with raZ regs, a code address), or the chain from o ENDS AFTER ONE NODE whose two words lie below o. A general
     achain from o could run through o's own 32 bytes, which a put rewrites, so it would not survive to the next call;
     [o - 8] and [o - 16] lie in [sp + 0, o) of the CALLER's frame (spZ regs + 16 <= o; a Theorem Labs lane: at o = sp or sp + 8
     they would be this function's own prologue slots), so no callee writes them and every callee's wkeep keeps them. *)
  (o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
   spZ regs + 16 <= o /\ exists ra nfp, rdword (aview segs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
     rdword (aview segs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling)) ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  zbytes_at segs W mem s bs -> wsrc_kept ly S U W mem buf s bs -> Z.of_nat (length bs) = n -> WriterSpec.bytes_ok bs ->
  0 <= s /\ s + n <= alloc_ceiling -> (s + n <= o \/ ot <= s) ->
  Z.of_nat (length text) + n + 1 <= WMAX ->
  cap <= WMAX -> cap <= live ->
  (* cap <= live: fuzz_realloc_spec asks `k <= live` at the grow call and fs_glob ties live to nothing
     (FSH_Gen.v:310-313 gives only 0 <= live <= peak), so the fact must come from the caller. Every caller
     holds it: the post returns live' = live + cap' - cap, and pj_write starts from cap = 0. Measured by
     a Theorem Labs lane, 2026-10-29. *)
  wbudget_pre S cap cnt live (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs) ->
  SRr segs W (cfg_at segs A_put regs mem md)
    (fun W' c' => exists (st' : WriterApp.wst) buf' U',
       st' = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs /\
       uswap U U' buf buf' cap /\
       wpost STK_put ot (FS_PSTAT_FP ++ wbuf_fp buf cap)
         regs ly S U W mem md (wevk cap st') U'
         (fun ly' S' W' regs' mem' md' =>
            wout_ok ly' S' W' mem' o buf' (WriterApp.w_cap st') (WriterApp.w_failed st') (WriterApp.w_text st') /\
            wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st') (WriterApp.w_cnt st') /\
            bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
            wkeep segs W W' mem mem' (spZ regs) ot o 32 /\
            (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
               fs_glob segs W' mem' (live + WriterApp.w_cap st' - cap) peak'
                 (WriterApp.w_cnt st') (WriterApp.w_fail st')) /\
            (forall i, 0 <= i < n -> mbyte segs (rdW W' mem') (s + i) = mbyte segs (rdW W mem) (s + i)))
         W' c').

(* ================= indent ================= *)
(* preset_file.c:514-523: one put of a newline, then depth puts of two spaces, when pretty. Model: WriterValue.wind. *)
Definition indent_spec : Prop :=
  forall ly S U W regs mem md ch ot o pretty depth buf cap failed text live peak cnt fail,
  fpreU segs B STK_indent ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  getr regs 10 = w64 o -> getr regs 11 = w64 pretty -> getr regs 12 = w64 depth ->
  0 <= pretty < alloc_ceiling -> - 2 ^ 31 <= depth < 2 ^ 31 ->
  wout_ok ly S W mem o buf cap failed text -> fs_glob segs W mem live peak cnt fail ->
  (cap <> 0 -> In (buf - HEAD, HEAD) U) ->   (* the buffer's head is in U: see put_spec *)
  (* indent states no separate room premise: at its own put calls (0x85e7c / 0x85e98 in A) s0 = depth (`mv s0, a2` at
     0x85e64), so no frame-chain push needs room there (a Theorem Labs lane). The window bounds below are put's own premises at
     those calls (put writes o's 32 bytes), and the chain clause after them is what put's chain premise at o is
     discharged from; both are needed. *)
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (* the frame chain an allocator call reads at s0 = o (approved a Theorem Labs lane 00:01Z; refined by a Theorem Labs lane 01:3xZ): either o is
     right above this frame (called from pj_write: o - 16 is this function's own saved-ra slot, written by the prologue
     with raZ regs, a code address), or the chain from o ENDS AFTER ONE NODE whose two words lie below o. A general
     achain from o could run through o's own 32 bytes, which a put rewrites, so it would not survive to the next call;
     [o - 8] and [o - 16] lie in [sp + 0, o) of the CALLER's frame (spZ regs + 16 <= o; a Theorem Labs lane: at o = sp or sp + 8
     they would be this function's own prologue slots), so no callee writes them and every callee's wkeep keeps them. *)
  (o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
   spZ regs + 16 <= o /\ exists ra nfp, rdword (aview segs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
     rdword (aview segs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling)) ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  Z.of_nat (length text) + Z.of_nat (length (concat (WriterValue.wind (negb (pretty =? 0)) depth))) + 1
    <= WMAX ->
  cap <= WMAX -> cap <= live ->   (* cap <= live: see the note at put_spec *)
  wbudget_pre S cap cnt live (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterValue.wind (negb (pretty =? 0)) depth)) ->
  SRr segs W (cfg_at segs A_indent regs mem md)
    (fun W' c' => exists (st' : WriterApp.wst) buf' U',
       st' = WriterApp.putN (WriterApp.mkW failed text cap cnt fail [])
               (WriterValue.wind (negb (pretty =? 0)) depth) /\
       uswap U U' buf buf' cap /\
       wpost STK_indent ot (FS_PSTAT_FP ++ wbuf_fp buf cap) regs ly S U W mem md
         (wevk cap st') U'
         (fun ly' S' W' regs' mem' md' =>
            wout_ok ly' S' W' mem' o buf' (WriterApp.w_cap st') (WriterApp.w_failed st') (WriterApp.w_text st') /\
            wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st') (WriterApp.w_cnt st') /\
            bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
            wkeep segs W W' mem mem' (spZ regs) ot o 32 /\
            (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
               fs_glob segs W' mem' (live + WriterApp.w_cap st' - cap) peak'
                 (WriterApp.w_cnt st') (WriterApp.w_fail st')))
         W' c').

(* ================= put_string ================= *)
(* preset_file.c:478-512: writes the quoted (0x22), escaped form of the C string at s. Model: WriterSpec.spieces.
   Plain template: lib/Prog/put_string_c.v. It takes a class-0 fake frame (FSH_Base FRAME_put_string, the
   __asan_stack_malloc_0 call at 0x85b48), so its STK is S0's, with the probe page. *)
Definition put_string_spec : Prop :=
  forall ly S U W regs mem md ch ot o s buf cap failed (text bs : list Z) live peak cnt fail,
  fpreU segs B STK_put_string ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s ->
  wout_ok ly S W mem o buf cap failed text -> fs_glob segs W mem live peak cnt fail ->
  (cap <> 0 -> In (buf - HEAD, HEAD) U) ->   (* the buffer's head is in U: see put_spec *)
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (* the frame chain an allocator call reads at s0 = o (approved a Theorem Labs lane 00:01Z; refined by a Theorem Labs lane 01:3xZ): either o is
     right above this frame (called from pj_write: o - 16 is this function's own saved-ra slot, written by the prologue
     with raZ regs, a code address), or the chain from o ENDS AFTER ONE NODE whose two words lie below o. A general
     achain from o could run through o's own 32 bytes, which a put rewrites, so it would not survive to the next call;
     [o - 8] and [o - 16] lie in [sp + 0, o) of the CALLER's frame (spZ regs + 16 <= o; a Theorem Labs lane: at o = sp or sp + 8
     they would be this function's own prologue slots), so no callee writes them and every callee's wkeep keeps them. *)
  (o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
   spZ regs + 16 <= o /\ exists ra nfp, rdword (aview segs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
     rdword (aview segs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling)) ->
  (* the ENTRY chain avoids o's 32 bytes (a Theorem Labs lane, 2026-10-29): put_string keeps s0 = its own entry sp across
     its THREE put calls, so put #2 / #3 read put_string's own record followed by the caller's whole chain from
     here, and put #1 rewrites [o, o + 32), which lies in caller frames. fpchain (YG00.v:368-373) is deterministic
     and reads every frame it VISITS on the current memory: each record's two words [fp - 16, fp), and, when it
     stops at [], one more word [bp - 8, bp) at a bp that is no record's fp (the last record's nfp, or s0 itself
     when ch = []). So the clause ranges over the VISITED frame pointers - s0 and the nfp of every record that
     CONTINUES (a record that stops by bad_next reads nothing at its nfp, so its nfp is not constrained;
     a Theorem Labs lane, 2026-10-29: otherwise a stopping record's nfp in (o, o + 48) would meet every caller premise and
     break the clause; same shape as FSH_Fn_reader.v:346) - not just the records; it implies the record form (the first fp is s0, each later fp the previous nfp). fp <= o puts
     both reads below o, o + 48 <= fp puts them above o + 32. Its one caller, write_value, calls with s0 = o,
     whose one-node chain has nfp < alloc_ceiling <= o (bad_next) or no record at all (the [] read at o - 8), so
     every visited fp is <= o. Only put_string needs it: write_value calls put with s0 = o (read from
     [o - 16, o)) and indent with s0 = depth < alloc_ceiling (chain []). *)
  (forall fp, fp = s0Z regs \/
     (exists r, In r ch /\ snd r = fp /\ bad_next (fst (fst r)) (ly_top ly) fp = false) ->
     fp <= o \/ o + 48 <= fp) ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  cstr_ok segs W mem s bs -> wsrc_kept ly S U W mem buf s (bs ++ [0]) ->
  WriterSpec.bytes_ok bs -> WriterSpec.no_zero bs -> plain_bytes bs ->
  (s + Z.of_nat (length bs) + 1 <= o \/ ot <= s) ->
  Z.of_nat (length text) + Z.of_nat (length (WriterSpec.wstr bs)) + 1 <= WMAX ->
  cap <= WMAX -> cap <= live ->   (* cap <= live: see the note at put_spec *)
  wbudget_pre S cap cnt live (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs)) ->
  SRr segs W (cfg_at segs A_put_string regs mem md)
    (fun W' c' => exists (st' : WriterApp.wst) buf' U',
       st' = WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs) /\
       uswap U U' buf buf' cap /\
       wpost STK_put_string ot (FS_PSTAT_FP ++ wbuf_fp buf cap) regs ly S U W mem md
         (wevk cap st') U'
         (fun ly' S' W' regs' mem' md' =>
            wout_ok ly' S' W' mem' o buf' (WriterApp.w_cap st') (WriterApp.w_failed st') (WriterApp.w_text st') /\
            wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st') (WriterApp.w_cnt st') /\
            bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
            wkeep segs W W' mem mem' (spZ regs) ot o 32 /\
            cstr_ok segs W' mem' s bs /\
            (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
               fs_glob segs W' mem' (live + WriterApp.w_cap st' - cap) peak'
                 (WriterApp.w_cnt st') (WriterApp.w_fail st')))
         W' c').

(* ================= write_value ================= *)
(* preset_file.c:525-575: the recursive value writer. Model: WriterValue.wvpieces t p d. Level-indexed by the
   tree, as the plain contract is (write_value_c.v, WV_K t) and as S0's STK_write_value m asks. *)
Definition write_value_spec_at (k : nat) : Prop :=
  forall ly S U W regs mem md ch ot o v pretty d (t : PjTree.jv) D UL buf cap failed text live peak cnt fail,
  (PjTree.depth t <= 2 - k)%nat ->
  fpreU segs B (STK_write_value (2 - k)) ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 d ->
  0 <= pretty < alloc_ceiling -> 0 <= d < 2 ^ 31 -> d + Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1 ->
  (* write_value's OWN entry chain must carry to its closing tail put after earlier puts rewrote [o, o + 32)
     (a Theorem Labs lane gap 3): s0 at entry is data, or o itself (the recursive call), or far above the object *)
  (s0Z regs < alloc_ceiling \/ s0Z regs = o \/ o + 48 <= s0Z regs) ->
  wout_ok ly S W mem o buf cap failed text -> fs_glob segs W mem live peak cnt fail ->
  (cap <> 0 -> In (buf - HEAD, HEAD) U) ->   (* the buffer's head is in U: see put_spec *)
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (* the frame chain an allocator call reads at s0 = o (approved a Theorem Labs lane 00:01Z; refined by a Theorem Labs lane 01:3xZ): either o is
     right above this frame (called from pj_write: o - 16 is this function's own saved-ra slot, written by the prologue
     with raZ regs, a code address), or the chain from o ENDS AFTER ONE NODE whose two words lie below o. A general
     achain from o could run through o's own 32 bytes, which a put rewrites, so it would not survive to the next call;
     [o - 8] and [o - 16] lie in [sp + 0, o) of the CALLER's frame (spZ regs + 16 <= o; a Theorem Labs lane: at o = sp or sp + 8
     they would be this function's own prologue slots), so no callee writes them and every callee's wkeep keeps them. *)
  (o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
   spZ regs + 16 <= o /\ exists ra nfp, rdword (aview segs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
     rdword (aview segs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling)) ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  PjStruct.pj_node segs (rdW W mem) (fun a k => In (a, k) UL) v t D ->
  FSH_Fn_reader.pobj segs B ly S W mem v ->   (* the root node itself: 8-aligned, addressable, in a live frame or block *)
  ublocks_ok ly S W mem UL -> (forall a k, In (a, k) D -> In (a, k) UL /\ a <> buf) ->
  (* the root node is not inside the writer's own buffer block, which a put may overwrite or free (a Theorem Labs lane 23:03Z) *)
  (cap <> 0 -> v + 56 <= buf - HEAD \/ buf + cap <= v) ->
  jv_plain t ->
  (forall x, o <= x < ot -> ~ PjStruct.pj_foot v D x) ->
  Z.of_nat (length text)
    + Z.of_nat (length (concat (WriterValue.wvpieces t (negb (pretty =? 0)) d))) + 1 <= WMAX ->
  cap <= WMAX -> cap <= live ->   (* cap <= live: see the note at put_spec *)
  wbudget_pre S cap cnt live (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterValue.wvpieces t (negb (pretty =? 0)) d)) ->
  SRr segs W (cfg_at segs A_write_value regs mem md)
    (fun W' c' => exists (st' : WriterApp.wst) buf' U',
       st' = WriterApp.putN (WriterApp.mkW failed text cap cnt fail [])
               (WriterValue.wvpieces t (negb (pretty =? 0)) d) /\
       uswap U U' buf buf' cap /\
       wpost (STK_write_value (2 - k)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) regs ly S U W mem md
         (wevk cap st') U'
         (fun ly' S' W' regs' mem' md' =>
            wout_ok ly' S' W' mem' o buf' (WriterApp.w_cap st') (WriterApp.w_failed st') (WriterApp.w_text st') /\
            wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st') (WriterApp.w_cnt st') /\
            bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
            wkeep segs W W' mem mem' (spZ regs) ot o 32 /\
            PjStruct.pj_node segs (rdW W' mem') (fun a k => In (a, k) UL) v t D /\
            (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
               fs_glob segs W' mem' (live + WriterApp.w_cap st' - cap) peak'
                 (WriterApp.w_cnt st') (WriterApp.w_fail st')))
         W' c').

(* ================= pj_write ================= *)
(* preset_file.c:654-668: builds a pj_out on its own real stack, calls write_value, returns the buffer or frees
   it. The success arm is named: it is what pj_parse's caller discharges (agreed with a Theorem Labs lane 20:34Z), and
   it gives the EXACT bytes, which is what READER's character-set lemma reads off. *)
Definition pjw_succ (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
    (q : Z) (t : PjTree.jv) (p : bool) (cap : Z) : Prop :=
  q <> 0 /\ 4096 + HEAD <= q /\
  (exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) /\
  Z.of_nat (length (WriterValue.wdoc t p)) < cap /\
  fs_rblock segs B ly S W mem q cap /\
  zbytes_at segs W mem q (WriterValue.wdoc t p ++ [0]).

Definition pj_write_spec : Prop :=
  forall ly S U W regs mem md ch v pretty (t : PjTree.jv) D UL live peak cnt fail,
  fpreU segs B STK_pj_write ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  getr regs 10 = w64 v -> getr regs 11 = w64 pretty -> 0 <= pretty < alloc_ceiling ->
  PjStruct.pj_node segs (rdW W mem) (fun a k => In (a, k) UL) v t D ->
  FSH_Fn_reader.pobj segs B ly S W mem v ->   (* the root node itself: 8-aligned, addressable, in a live frame or block *)
  ublocks_ok ly S W mem UL -> (forall a k, In (a, k) D -> In (a, k) UL) ->
  fs_glob segs W mem live peak cnt fail ->   (* the allocator statics at entry: without it live / peak / cnt /
     fail are tied to nothing in memory, so the post's fs_glob over st' (built from cnt / fail) was false for
     any cnt but g_count's value, and write_value_spec_at, which pj_write calls, demands it - a Theorem Labs lane,
     2026-10-29. Same form as encode_spec / decode_spec. *)
  jv_plain t -> (PjTree.depth t <= 2)%nat ->   (* crt_doc_ok; pj_write calls write_value at level 0 *)
  Z.of_nat (length (WriterValue.wdoc t (negb (pretty =? 0)))) + 1 <= WMAX ->
  (let st' := WriterApp.putN (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0))) in
   st_nev S + wev0 st' + EV_fuzz_free <= EV_MAX /\ blocks_bytes S + 2 * (WriterApp.w_cap st' + HEAD) <= LIVE_MAX /\
   live + 2 * WriterApp.w_cap st' < 2 ^ 64 /\ cnt + wcalls st' < 2 ^ 64) ->
  SRr segs W (cfg_at segs A_pj_write regs mem md)
    (fun W' c' =>
       let st' := WriterApp.putN (WriterApp.w0 cnt fail)
                    (WriterValue.wdpieces t (negb (pretty =? 0))) in
       (* success: the document's buffer is returned, its head user-poisoned *)
       (exists q, WriterApp.w_failed st' = 0 /\
        fpostU segs B STK_pj_write (spZ regs) FS_PSTAT_FP regs ly S U W mem md (wev0 st')
          (U ++ [(q - HEAD, HEAD)])
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 q /\
             pjw_succ ly' S' W' mem' q t (negb (pretty =? 0)) (WriterApp.w_cap st') /\
             (* not an append: the document buffer may be grown twice, and fuzz_realloc places the new block
                anywhere in the list (a Theorem Labs lane, 2026-10-29). blocks_bytes follows by permutation. *)
             (exists C1 C2, ablocks B ly' S' = C1 ++ (q - HEAD, WriterApp.w_cap st' + HEAD) :: C2 /\
                C1 ++ C2 = ablocks B ly S) /\
             PjStruct.pj_node segs (rdW W' mem') (fun a k => In (a, k) UL) v t D /\
             (exists peak', peak <= peak' <= Z.max peak (live + 2 * WriterApp.w_cap st') /\
                fs_glob segs W' mem' (live + WriterApp.w_cap st') peak'
                  (WriterApp.w_cnt st') (WriterApp.w_fail st'))) W' c')
       \/
       (* a refused allocation anywhere in the run: the null return, and any buffer already taken is freed *)
       (WriterApp.w_failed st' <> 0 /\
        fpostU segs B STK_pj_write (spZ regs) FS_PSTAT_FP regs ly S U W mem md (wev0 st' + EV_fuzz_free) U
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 0 /\
             Permutation (ablocks B ly' S') (ablocks B ly S) /\
             PjStruct.pj_node segs (rdW W' mem') (fun a k => In (a, k) UL) v t D /\
             (exists peak', peak <= peak' <= Z.max peak (live + 2 * WriterApp.w_cap st') /\
                fs_glob segs W' mem' live peak' (WriterApp.w_cnt st') (WriterApp.w_fail st'))) W' c')).

(* ================= preset_base64_encode ================= *)
(* preset_file.c:577-608: one fuzz_malloc of enc_size len, then the base64 loop. Model: WriterSpec.b64_enc.
   Plain template: lib/Prog/preset_base64_encode_c.v:35. *)
Definition encode_spec : Prop :=
  forall ly S U W regs mem md ch data len (bs : list Z) live peak cnt fail,
  fpreU segs B STK_preset_base64_encode ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  getr regs 10 = w64 data -> getr regs 11 = w64 len ->
  WriterSpec.bytes_ok bs -> Z.of_nat (length bs) = len -> 0 <= len <= 2 ^ 27 ->
  zbytes_at segs W mem data bs -> 4096 <= data /\ data + len <= alloc_ceiling ->
  (* the bytes are a live reader block's user bytes, so their shadow survives the fuzz_malloc call (a Theorem Labs lane 22:49Z) *)
  (0 < len -> exists kd, fs_rblock segs B ly S W mem data kd /\ len <= kd) ->
  fs_glob segs W mem live peak cnt fail ->
  st_nev S + EV_preset_base64_encode <= EV_MAX -> blocks_bytes S + (enc_size len + HEAD) <= LIVE_MAX ->
  live + enc_size len < 2 ^ 64 -> cnt + 1 < 2 ^ 64 ->
  SRr segs W (cfg_at segs A_preset_base64_encode regs mem md)
    (fun W' c' =>
       (* the one allocation refused: the null return, the counter ticks, fail latches to SIZE_MAX *)
       (cnt = fail /\
        fpostU segs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP regs ly S U W mem md 0 U
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 0 /\
             ablocks B ly' S' = ablocks B ly S /\
             fs_glob segs W' mem' live peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ) W' c')
       \/
       (exists q, cnt <> fail /\ q <> 0 /\
        fpostU segs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP regs ly S U W mem md
          EV_preset_base64_encode (U ++ [(q - HEAD, HEAD)])
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 q /\ 4096 + HEAD <= q /\
             ablocks B ly' S' = ablocks B ly S ++ [(q - HEAD, enc_size len + HEAD)] /\
             fs_rblock segs B ly' S' W' mem' q (enc_size len) /\
             zbytes_at segs W' mem' q (WriterSpec.b64_enc bs ++ [0]) /\
             (forall i, 0 <= i < len -> mbyte segs (rdW W' mem') (data + i) = mbyte segs (rdW W mem) (data + i)) /\
             fs_glob segs W' mem' (live + enc_size len)
               (Z.max peak (live + enc_size len)) ((cnt + 1) mod 2 ^ 64) fail) W' c')).

(* ================= preset_base64_decode ================= *)
(* preset_file.c:610-650: strlen, fuzz_malloc of dec_size tb, the scan (memchr over g_b64), fuzz_free on a bad
   text; writes the byte count into *lenp. `lenp` is a `size_t *`, so the store is 8 bytes, and on the entry's
   real-stack path it is a CALLER real-stack object (ENTRY slice section 8: LLVMFuzzerTestOneInput's frame
   offset 32), which is why this spec uses the raised window with o = lenp and n = 8. Three arms, as plain
   preset_base64_decode_c.v:35. *)
Definition decode_spec : Prop :=
  forall ly S U W regs mem md ch ot text lenp (tb : list Z) live peak cnt fail v,
  fpreU segs B STK_preset_base64_decode ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  getr regs 10 = w64 text -> getr regs 11 = w64 lenp ->
  cstr_ok segs W mem text tb -> wsrc_kept ly S U W mem 0 text (tb ++ [0]) ->
  WriterSpec.bytes_ok tb -> Z.of_nat (length tb) <= 2 ^ 28 ->
  lenp mod 8 = 0 -> spZ regs <= lenp -> lenp + 8 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (* the frame chain fuzz_malloc reads at s0 = lenp (approved a Theorem Labs lane 00:01Z; ENTRY discharges it) *)
  (exists chl, achain ly (aview segs (w_H W) (unpoison U mem)) (spZ regs) lenp chl) ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  val_mem segs (rdW W mem) lenp 8 v -> 0 <= v < 2 ^ 64 ->
  (lenp + 8 <= text \/ text + Z.of_nat (length tb) + 1 <= lenp) ->
  fs_glob segs W mem live peak cnt fail ->
  st_nev S + dec_ev tb <= EV_MAX -> blocks_bytes S + (dec_size tb + HEAD) <= LIVE_MAX ->
  live + dec_size tb < 2 ^ 64 -> cnt + 1 < 2 ^ 64 ->
  SRr segs W (cfg_at segs A_preset_base64_decode regs mem md)
    (fun W' c' =>
       (* the one allocation refused *)
       (cnt = fail /\
        wpost STK_preset_base64_decode ot FS_PSTAT_FP regs ly S U W mem md 0 U
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
             wkeep segs W W' mem mem' (spZ regs) ot lenp 8 /\
             val_mem segs (rdW W' mem') lenp 8 v /\
             fs_glob segs W' mem' live peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ) W' c')
       \/
       (* a bad text: the block is allocated and freed again *)
       (cnt <> fail /\ WriterSpec.b64_dec tb = None /\
        wpost STK_preset_base64_decode ot FS_PSTAT_FP regs ly S U W mem md EV_preset_base64_decode U
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\   (* malloc then free of the
             SAME fresh block: malloc's post is an exact append and free's an exact one-occurrence removal
             (FSH_Fn_alloc.v:128, :159), so the list comes back EQUAL, not merely permuted (CNO's request,
             a Theorem Labs lane 2026-10-29: check_no_overread's post needs the equality) *)
             wkeep segs W W' mem mem' (spZ regs) ot lenp 8 /\
             val_mem segs (rdW W' mem') lenp 8 v /\
             fs_glob segs W' mem' live (Z.max peak (live + dec_size tb))
               ((cnt + 1) mod 2 ^ 64) fail) W' c')
       \/
       (* success: the block holds b64_dec tb and *lenp its length *)
       (exists q out, cnt <> fail /\ WriterSpec.b64_dec tb = Some out /\ q <> 0 /\
        wpost STK_preset_base64_decode ot FS_PSTAT_FP regs ly S U W mem md 1 (U ++ [(q - HEAD, HEAD)])
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 q /\ 4096 + HEAD <= q /\
             ablocks B ly' S' = ablocks B ly S ++ [(q - HEAD, dec_size tb + HEAD)] /\
             fs_rblock segs B ly' S' W' mem' q (dec_size tb) /\
             zbytes_at segs W' mem' q out /\
             wkeep segs W W' mem mem' (spZ regs) ot lenp 8 /\
             val_mem segs (rdW W' mem') lenp 8 (Z.of_nat (length out)) /\
             cstr_ok segs W' mem' text tb /\
             fs_glob segs W' mem' (live + dec_size tb)
               (Z.max peak (live + dec_size tb)) ((cnt + 1) mod 2 ^ 64) fail) W' c')).

(* the same function when *lenp lies in a live caller FAKE frame, which is where both measured callers keep it
   when __asan_stack_malloc_0 grants the frame (a Theorem Labs lane 21:29Z, measured: check_reject_clean_starved a1 =
   s9 + 0x20, s9 the fake frame, a1 set at 0x8262c, call 0x82630; LLVMFuzzerTestOneInput s4 = s8 + 0x20, call 0x810a0). The fake
   stack is disjoint from the real one, so the window form above cannot hold there: the slot is in FP and the
   window top stays at sp. decode_spec above is the real-stack fallback form. *)
Definition decode_spec_ff : Prop :=
  forall ly S U W regs mem md ch text lenp (tb : list Z) live peak cnt fail v,
  fpreU segs B STK_preset_base64_decode ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  getr regs 10 = w64 text -> getr regs 11 = w64 lenp ->
  cstr_ok segs W mem text tb -> wsrc_kept ly S U W mem 0 text (tb ++ [0]) ->
  WriterSpec.bytes_ok tb -> Z.of_nat (length tb) <= 2 ^ 28 ->
  (* *lenp is 8 bytes of a live CALLER FAKE FRAME (ajournal's frame clause, YCbq.v:362-364) *)
  lenp mod 8 = 0 -> (exists cid pos, In (cid, pos) (frames S) /\
     forall a, lenp <= a < lenp + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
  (forall a, lenp <= a < lenp + 8 -> apresent (w_H W) mem a) ->
  (* *lenp's 8 bytes are ADDRESSABLE in the shadow (a Theorem Labs lane, 2026-10-29): decode's inline ASan check of the
     *lenp store reads them, and nothing above gives their VALUES - AR_frames_law (YG0d.v:454-462) gives only
     presence and non-ownership of a live frame's bytes. Every caller meets it: both callers keep *lenp as a
     variable of their own fake frame, whose prologue writes that granule's shadow 00 (check_reject_clean_starved
     s9 + 0x20, LLVMFuzzerTestOneInput s8 + 0x20, after the f1 left redzone). *)
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF lenp 8 ->
  val_mem segs (rdW W mem) lenp 8 v -> 0 <= v < 2 ^ 64 ->
  (lenp + 8 <= text \/ text + Z.of_nat (length tb) + 1 <= lenp) ->
  fs_glob segs W mem live peak cnt fail ->
  st_nev S + dec_ev tb <= EV_MAX -> blocks_bytes S + (dec_size tb + HEAD) <= LIVE_MAX ->
  live + dec_size tb < 2 ^ 64 -> cnt + 1 < 2 ^ 64 ->
  SRr segs W (cfg_at segs A_preset_base64_decode regs mem md)
    (fun W' c' =>
       (* the one allocation refused *)
       (cnt = fail /\
        fpostU segs B STK_preset_base64_decode (spZ regs) (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) regs ly S U W mem md 0 U
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
             val_mem segs (rdW W' mem') lenp 8 v /\
             fs_glob segs W' mem' live peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ) W' c')
       \/
       (* a bad text: the block is allocated and freed again *)
       (cnt <> fail /\ WriterSpec.b64_dec tb = None /\
        fpostU segs B STK_preset_base64_decode (spZ regs) (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) regs ly S U W mem md EV_preset_base64_decode U
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\   (* malloc then free of the
             SAME fresh block: malloc's post is an exact append and free's an exact one-occurrence removal
             (FSH_Fn_alloc.v:128, :159), so the list comes back EQUAL, not merely permuted (CNO's request,
             a Theorem Labs lane 2026-10-29: check_no_overread's post needs the equality) *)
             val_mem segs (rdW W' mem') lenp 8 v /\
             fs_glob segs W' mem' live (Z.max peak (live + dec_size tb))
               ((cnt + 1) mod 2 ^ 64) fail) W' c')
       \/
       (* success: the block holds b64_dec tb and *lenp its length *)
       (exists q out, cnt <> fail /\ WriterSpec.b64_dec tb = Some out /\ q <> 0 /\
        fpostU segs B STK_preset_base64_decode (spZ regs) (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) regs ly S U W mem md 1 (U ++ [(q - HEAD, HEAD)])
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 q /\ 4096 + HEAD <= q /\
             ablocks B ly' S' = ablocks B ly S ++ [(q - HEAD, dec_size tb + HEAD)] /\
             fs_rblock segs B ly' S' W' mem' q (dec_size tb) /\
             zbytes_at segs W' mem' q out /\
             val_mem segs (rdW W' mem') lenp 8 (Z.of_nat (length out)) /\
             cstr_ok segs W' mem' text tb /\
             fs_glob segs W' mem' (live + dec_size tb)
               (Z.max peak (live + dec_size tb)) ((cnt + 1) mod 2 ^ 64) fail) W' c')).

End c.
