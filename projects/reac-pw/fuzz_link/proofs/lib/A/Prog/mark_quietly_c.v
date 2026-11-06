(* mark_quietly (fuzz_link.c:153-164) on image A (fuzz_link.asan 0x883d4, 124 bytes; listing
   (internal path) (internal record, sha256 83bb83545bf3)): open the harness's own stream
   once, rewind it, and run the marking policy. a0 = m (the marks block), a1 = ifname. The plain contract is
   lib/Prog/mark_quietly_c.v; this file states the SAME link_spec result (`mark_lib`, through the tail call)
   over the A-state, in link_amem.v's `aleaf_alloc_fx_sk` form on the first call and `aleaf_fx` on every later
   one (the shapes for a function that reaches the printf family: rounding mode 0 at entry, a Post at SOME fx'
   related to the entry's by BoxBase.v `fxr`, and a Pre that also sees the call's block list). The first-call
   shape `aleaf_alloc_fx_sk` is `aleaf_alloc_fx` with the premise `YI16.sink_open_fp FP` right after `apre`
   (form e47ff041e8b3): fmemopen's tail call to __ofl_add writes musl's open-file-list head, and a journal
   spares that head only when its footprint is sink-open (Reusable/YCbq.v `fp_spares`; found by
   the mark-quietly walk). The harness discharges it by this unit's AMemFile.v `amf_harness_fp_sink_open`.

   TWO CONTRACTS, ONE FUNCTION. The first call of the process opens the FILE (one malloc inside fmemopen); every
   later call does not. `aleaf_alloc_fx`'s Post raises the journal's event index by exactly EV and bounds the
   allocator's move by MO, so the two arms cannot share one EV: the opening arm has EV = 1 and
   LIVE = AMF_BLOCK, the later arm has no allocator event at all and is the `aleaf_fx` shape, whose Post
   keeps the block list (`Permutation`) and the whole allocator state but the side stack. A caller decides which
   it holds by reading g_sink, which both Pres fix (`au64_at m LA_G_SINK sink`). The plain contract puts the two
   arms inside one SR statement because its frame carries the allocator interface in every case.

   The image-A code, in order:
     +0x00..+0x10  push a 32-byte frame; save ra, s0, s1, s2       (no realignment: no `andi sp, sp, -0x20`)
     +0x14..+0x20  s0 := a1 (ifname); a1 := g_sink (0x62fec0, a constant offset into a global, so the
                   instrumentation leaves the load unchecked); s1 := a0 (the marks block)
     +0x24  bnez a1 -> +0x4c                                        (a FILE is already open: the later arm)
     +0x28..+0x3c  a0 := g_said (0x62fee0), a1 := 0x1000, a2 := 0x21260 (".str.22" = "w");
                   jal wrapper_fmemopen (0x430a8)
     +0x40  sd a0, g_sink                                           (g_sink := the new FILE)
     +0x44  beqz a0 -> +0x74 before_abort (0x5b318), abort (0x90ac4) (the harness's own fmemopen failure; the
                   allocator room premises of `aleaf_alloc_fx` rule it out)
     +0x48  jal reac_served_say_to (0x89504)                        (g_say := the new FILE)
     +0x4c  ld a0, g_sink;  +0x50 jal wrapper_rewind (0x430d4)      (the window is emptied; any pending bytes of
                   the previous call go to g_said through mwrite)
     +0x54..+0x6c  a0 := the marks block, a1 := ifname; restore, pop (sp back to the entry sp)
     +0x70  j reac_served_mark (0x895a8)                            (TAIL call, on this function's own sp)

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x10; wrapper_fmemopen, wrapper_rewind and the
     two own callees take premises the walk derives from the journal; the tail jump at +0x70 returns to this
     function's own ra.
   - K = 32 + (ASTACK + 2 * ESTACK) = 24608. The 32-byte frame, then the deepest callee window. fmemopen reaches
     the allocator, whose contract window is ASTACK = 16384 (`acall_pre`, Reusable/YG0d.v:226-234) below the
     frames of the fmemopen interceptor and of musl's fmemopen; the libc slice owns the exact number
     (link-a/libc/table.tsv (internal record, sha256 52efb25e5b91): wrapper_fmemopen has no row yet), so this contract
     takes ASTACK + 2 * ESTACK as an upper bound and names it. `MARK_QUIETLY_AK_covers_tail` records that the window
     also covers the tail call to reac_served_mark (9504) at the restored sp; the rewind's released window is
     ARW_STK = 160 + ESTACK = 4256 (lib/A/Rt/LinkMfDefs.v), inside it too. The plain K (17280) does not carry
     over.
   - SIDE: the same list as reac_served_mark's, because of the tail call (link-a/form/FORM.md
     (internal record, sha256 13aeff774164) section 4.2). fmemopen, rewind and reac_served_say_to take no side frame.
   - EVERY PREMISE reac_served_mark ASKS OF ITS CALLER, at THIS K (the plain lane's gap 3c): the tail call at
     +0x70 happens with sp already restored (+0x6c), so reac_served_mark runs on this function's own sp, and
     K = 24608 >= 9504, so its window is inside this one. They are stated with reac_served_mark_c.v's own
     `amk_nlk_ok`, `amk_errno_ok`, `amk_table_ok`, `amk_block_ok`, `amk_name_ok` and `amk_policy_ok`, so there
     is ONE form for both callers.
   - the name and every interface-table string apart from the four globals this function writes BEFORE the
     tail jump hands them to reac_served_mark (`amq_globals`): g_sink (+0x40 `sd a0, g_sink`, opening arm),
     g_say (reac_served_say_to at +0x48, opening arm), the open-file list head (fmemopen's tail call to
     __ofl_add, opening arm) and g_said (the rewind at +0x50: `arewind_mf_realizes`' Post excepts
     [g_said, +4096) from its kept clause, on both arms). reac_served_mark's own helpers separate the strings
     only from g_nl, errno, the FILE block and the marks block, which is all reac_served_mark itself writes
     (its fprintf / vfprintf callees keep g_said: lib/A/Rt/LinkVfDefs.v
     avfprintf_mf_realizes / afprintf_mf_realizes). Without this conjunct a name inside g_said, or the empty name at g_sink, would be a
     different string at 0x88444 than at entry (found by the mark-quietly walk, 2026-10-30). True at every call
     site: the slot passes a g_names entry or an `odd` entry, and the table strings are the same two kinds,
     all below g_sink 0x62fec0 or in .rodata.
   - the later arm (`sink <> 0`): `amemfile_k m sink k` for some k (rewind empties the window, so any k will
     do), `au64_at m LA_G_SAY sink` and `au64_at m LA_OFL_HEAD sink` (the plain lane's AMEND-slot item 9: nothing
     writes the open-file list head on a later call, and `amemfile_k` does not mention it, so without the Pre
     fact the later-call arm's Post could not say it), `amf_blk_ok` (the FILE block addressable and outside
     the callee windows), and g_said's place for the flush: `amem_range`, `range_addressable` and
     `shadow_hull_vis` over [g_said, g_said + 4096). The rewind at +0x50 flushes the line the previous call
     left (up to MARK_LINE_MAX bytes, that call's Post) into g_said through mwrite, whose copy goes through the
     memcpy wrapper (link-a/libc/strmem.md (internal record, sha256 b0efa271b731) section 4: mwrite 0x96cc0 -> 0x52d74);
     a checked copy asks those three facts of its destination (Reusable/YG0d.v:329-330).
   - the REAL(rewind) cell is NOT a premise: the rewind wrapper (0x430d4 `j 0x48ce8`) jumps through
     0xa37d8, which holds 0x97210 (musl rewind) in the pin's .data, and the frame's const table now has that
     row (lib/A/AF0m.v, `z8 (ANum 0xa37d8) 0x97210`), so AR's const law gives it at
     every state; the rewind contract (lib/A/Rt/LinkMfDefs.v arewind_mf_realizes) does not take it either.
   - the opening arm (`sink = 0`): what fmemopen asks, in the shape the plain lane's fmemopen contract states
     it: the three stdio words 0 (`amf_env segs link_amf m`, lib/A/AMemFileSink.v: `__libc.threaded` 0x651ea1,
     which fmemopen reads at 0x96ba8 and which must be 0 for the store `lock = -1` at 0x96bc4 that
     `amemfile_at` asks; `__libc.need_locks` 0x651ea3 and `ofl_lock` 0x652300, which `__ofl_add`'s `__lock`
     reads and, when not 0, writes, outside the write set; the plain contract's `stdio_ok`), `au64_at m
     LA_OFL_HEAD 0` (the open-file list is empty, so fmemopen's tail call to __ofl_add stores the new FILE
     there), `awrange m LA_G_SINK 8` and `awrange m LA_G_SAY 8` (the two stores at +0x40 and inside
     reac_served_say_to), g_said writable, in memory, addressable and with its shadow hull visible (the
     rewind contract asks `amf_buf_ok` on every call, although no flush runs on a fresh FILE), and the mode
     string at 0x21260 with what a string wrapper reads of it. The errno, table and marks separations are
     stated against the FILE range (0, 0) on this arm, because the block does not exist yet; AR separates the
     fresh block from the image, from the live blocks and from the side stack, so nothing else is needed
     (`AR_blocks_law`, Reusable/YG0d.v:430-434). The three stdio words hold at the call site: the frame's
     `amf_sink` gives `amf_env` at every return of LLVMFuzzerTestOneInput, and nothing in the slot writes them.
     Also `aarg regs 1 < alloc_ceiling`: the fmemopen contract asks, at 0x88410, the allocator's frame chain
     `achain lyc rd sp s0 ch` with its spine in its context list `[[]]`, so ch = []; s0 there is this function's
     a1 (+0x14 `mv s0, a1`), and Reusable/YCbq.v `achain_low` gives ch = [] from s0 < alloc_ceiling (the other
     arms of `achain`, a value at the stack's top or not 8-aligned, are not facts of a name). True at the real
     calls: a1 is a g_names or `odd` entry (image bytes) or NULL (found by the mark-quietly walk, 2026-10-30).
   - the write set and apre's `ajw` on it: g_nl up to its request ring, the marks block, g_said (rewind flushes
     the previous call's line into it through mwrite), and on the opening arm g_sink, g_say and the open-file
     list head; on the later arm the FILE block, which is a block of the call's state and which `akept` would
     otherwise keep. Which clause of `ajw` grants each: the five globals by `inG G` (each is one of the eight
     objects of `LA_G`, link_aaddr.v); the marks block by `in_tmp_block` (the calloc(1, 516) of
     LLVMFuzzerTestOneInput 0x82c84). The FILE block of the later arm is granted by `in_tmp_block` only in the
     target call whose first mark opened it; on every later target call it is a block of the journal's start,
     and the grant is the frame's: the harness journal's FP is `amf_harness_fp T` (lib/A/AMemFileSink.v:231,
     `sink_token` and every kept block), and `amf_harness_fp_grants` (lib/A/AMemFile.v:535) gives `awr_byte` of
     every byte of a kept block that is live in the ledger, which this arm's `In (sink, AMF_BLOCK) bl` says.
     The FRESH FILE block is not in the write set on the opening arm: it is not in `ablocks B lyc Sc`, so no
     clause of `akept` speaks of it.
   - the read set Rd (`aleaf_fx` / `aleaf_alloc_fx`): the name and its NUL, the interface table and its name
     strings (reac_served_mark_c.v's `amk_rd`). They are read after a malloc may have run, which is exactly the
     case the read set is for: `akb` is what keeps them.
   EV = 1 on the opening arm (fmemopen's one malloc; __ofl_add allocates nothing), 0 on the later arm.
   LIVE = AMF_BLOCK = 1304 on the opening arm.

   THE PARAMETERS of the opening arm (`MT`, `MO`, `CTX`, `LedPre`, `LedPost`) are the ones `aleaf_alloc_fx` carries
   until the frame and the cf layer land (link-a/form/FORM.md (internal record, sha256 13aeff774164) sections 1, 4.3):
   MT and MO are the frame's meter and the move of one `malloc(1304)`; CTX is the list of contexts whose allocator
   traces the start-up universe lists; and the intended instance of the wild-trace pair is link-a/form/FORM.md
   (internal record, sha256 13aeff774164) section 1's for mark_quietly, `LedPre := fun _ => True` and
   `LedPost := fun Sc S2 => (length (wild_part (as_universe B) (st_depot S2)) <= length (wild_part (as_universe B) (st_depot Sc)))%nat`
   (no wild trace at this allocator site, link-a/design/ACEJ-WILD.md (internal record, sha256 6ee1df95f779) section 3).

   What does NOT carry over from the plain text:
   - the SR shape over the frame's allocator interface (`call_pre_k`, `mq_post_k`, `room_slots`,
     `res_ok_slots`): on image A the allocator room is `blocks_bytes Sc + LIVE <= LIVE_MAX` and `mo_ok MT Sc MO`, and
     the caller's frame clause is the journal (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 4.3).
   - `spZ regs <= TASK_SIZE` and `task_mem` (the plain gap 15, which turned SR memory into what `leaf_fp` needs):
     the journal carries the stack on image A.
   - `kept_str` on the name and on every table string (the plain gap 17 and AMEND-slot item 10): on image A it is
     the read set Rd with `akb` (no allocator call can hand the bytes out) plus the separation from the four
     globals this function writes (`amq_globals`, above).
   - `guard_words` and `A_IMG_TOP <= spZ regs - K`: the wrapper contracts' on image A.
   - `(bv_unsigned (getr regs 10) <> 0 -> exists q n, In (q, n) (blocks L A) /\ ...)`, the plain gap 16: on image
     A it is stated over the block list the fx shapes hand the Pre. The marks block, when a0 <> 0:
     `amarks_ledger bl a0` (remember_c.v: `In (a0, MK_SIZE) bl` and `YCbq.off_img a0 MK_SIZE`), which remember's
     snprintf destination needs through the tail call (`link_snp_place`, LinkSnpDef.v:166); on the
     opening arm fmemopen's Post appends the FILE block to the list, so the marks block stays in it. The FILE
     block, on the later arm: `In (sink, AMF_BLOCK) bl`, which the libc rewind / fprintf / vfprintf contracts
     need (the slot gives both from the frame's `amf_gi_ledger`, lib/A/AMemFileSink.v, and its own calloc
     block). On the opening arm the FILE block does not exist yet; the fmemopen contract's Post adds it.
   Nothing of the plain Post is false of image A.
   THE FLOATING-POINT STATE is the shapes'. Entry: `aleaf_fx` / `aleaf_alloc_fx` take
   `YK0o.frm_zero (fp_csr fx)`, as the plain contract does (lib/Prog/mark_quietly_c.v:151), because the tail
   call reaches the printf family, whose released contracts ask for rounding mode 0 at entry; it holds at every
   call site, because the start-up fcsr is 0 (`fp_frm_zero_fx0`, Reusable/YK0o.v:15) and none of the 36
   listings of link's own functions holds an f* or csr* instruction. Exit: `apostF` returns at some fx' with
   `BoxBase.fxr fx fx'` (every f register but f10 kept, the fcsr kept or its rounding mode 0), the image-A
   form of the plain contract's fresh `fx'` with `frm_zero`.
   Released proofs (rule 24): none of mark_quietly (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038)); the fmemopen and rewind wrappers
   are NEW (link-a/libc/strmem.md (internal record, sha256 b0efa271b731) section 4, link-a/libc/table.tsv (internal record, sha256 52efb25e5b91)).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0o YI04 YI16 YM05 YC5d YG00 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem model_decide_c remember_c reac_code_emit_c reac_served_mark_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition MARK_QUIETLY_A : Z := 0x883d4.
Lemma MARK_QUIETLY_A_is_entry : MARK_QUIETLY_A = LA_mark_quietly. Proof. reflexivity. Qed.

(* the mode string fmemopen reads (listing +0x34; .str.22, a registered 32-byte global) *)
Definition LA_MODE_STR : Z := 0x21260.
Definition S_MODE_W : list byte := map (Z_to_bv 8) [119].

(* the runtime entries this function calls *)
Definition LA_wrapper_fmemopen : Z := 0x430a8.
Definition LA_wrapper_rewind : Z := 0x430d4.
Definition LA_before_abort : Z := 0x5b318.

(* the stack bound on image A: the 32-byte frame, then the fmemopen path, which reaches the allocator. The exact
   window of the fmemopen wrapper is the libc slice's; ASTACK + 2 * ESTACK is an upper bound for it (the
   allocator's own window below the interceptor's and musl's fmemopen frames). *)
Definition MARK_QUIETLY_AFRAME : Z := 32.
Definition AMQ_FMEMOPEN_STK : Z := ASTACK + 2 * ESTACK.
Definition MARK_QUIETLY_AK : Z := MARK_QUIETLY_AFRAME + AMQ_FMEMOPEN_STK.
Lemma MARK_QUIETLY_AK_val : MARK_QUIETLY_AK = 24608. Proof. reflexivity. Qed.
(* the tail call runs on this function's own sp, so its window must be inside this one *)
Lemma MARK_QUIETLY_AK_covers_tail : REAC_SERVED_MARK_AK <= MARK_QUIETLY_AK.
Proof. unfold REAC_SERVED_MARK_AK, MARK_QUIETLY_AK. vm_compute. discriminate. Qed.

(* the side-stack room: the tail call's *)
Definition MARK_QUIETLY_ASIDE : list (Z * Z) := REAC_SERVED_MARK_ASIDE.

(* the four program globals this function writes before its tail jump: g_sink, g_said (the rewind's flush),
   g_say and the open-file list head, as (base, length) *)
Definition amq_globals : list (Z * Z) :=
  [(LA_G_SINK, 8); (LA_G_SAID, SAID_SIZE); (LA_G_SAY, 8); (LA_OFL_HEAD, 8)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* what both arms ask of the fake kernel, errno, the table, the marks block, the name and the policy strings,
   against the FILE range (fb, fn) of the arm: reac_served_mark's own premises at this K *)
Definition amq_common (fb fn : Z) (bl : list (Z * Z)) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists kbs tab nm,
    (aarg regs 0 <> 0 -> amarks_ledger bl (aarg regs 0))
    /\ (forall g n, In (g, n) amq_globals ->
          (forall s, nm = Some s -> apart g n (aarg regs 1) (Z.of_nat (length s) + 8))
          /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
                au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
                apart g n p (Z.of_nat (length n2) + 1)))
    /\ amk_nlk_ok segs m kbs tab 2
    /\ amk_errno_ok segs B regs MARK_QUIETLY_AK fb fn m
    /\ apart (as_errno B) 4 LA_G_SAY 8 /\ apart (as_errno B) 4 LA_G_SAID SAID_SIZE
    /\ apart (as_errno B) 4 LA_G_SINK 8 /\ apart (as_errno B) 4 LA_OFL_HEAD 8
    /\ amk_table_ok segs B regs MARK_QUIETLY_AK fb fn m tab
    /\ amk_policy_ok segs regs MARK_QUIETLY_AK m
    /\ astr_arg segs m (aarg regs 1) nm
    /\ amk_name_ok segs B regs MARK_QUIETLY_AK fb fn m nm
    /\ amk_block_ok segs B regs MARK_QUIETLY_AK fb fn m.

(* the answer of the tail call, as reac_served_mark gives it (reac_served_mark_c.v's Post, without its FILE
   clause, which each arm states for its own stream) *)
Definition amq_rc (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  (aarg regs 0 = 0 -> getr regs' 10 = w64 (- E_INVAL)
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

(* the read set of both arms: the name, the interface table and its name strings *)
Definition mark_quietly_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  amk_rd segs regs m a.

(* ==========================================================================
   The later call: g_sink already holds the FILE, no allocator event
   ========================================================================== *)

Definition mark_quietly_apre_again (sink : Z) (bl : list (Z * Z)) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  In (sink, AMF_BLOCK) bl
  /\ au64_at segs m LA_G_SINK sink /\ sink <> 0
  /\ amq_common sink AMF_BLOCK bl regs m
  /\ (exists k, amemfile_k segs m sink k)
  /\ au64_at segs m LA_G_SAY sink /\ au64_at segs m LA_OFL_HEAD sink
  /\ amf_blk_ok segs regs MARK_QUIETLY_AK m sink
  /\ awrange segs m LA_G_SAID SAID_SIZE
  (* the rewind's flush into g_said goes through the checked copy (mwrite -> the memcpy wrapper) *)
  /\ amem_range LA_G_SAID SAID_SIZE
  /\ range_addressable (ard segs m) SHADOW_OFF LA_G_SAID SAID_SIZE
  /\ shadow_hull_vis (ard segs m) LA_G_SAID SAID_SIZE.

Definition mark_quietly_awr_again (sink : Z) (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(LA_G_NL, LA_G_NL + NK_N_SENT + 4);
   aivl (aarg regs 0) MK_SIZE;
   (LA_G_SAID, LA_G_SAID + SAID_SIZE);
   aivl sink AMF_BLOCK].

Definition mark_quietly_apost_again (sink : Z) (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  au64_at segs m' LA_G_SINK sink /\ au64_at segs m' LA_G_SAY sink /\ au64_at segs m' LA_OFL_HEAD sink
  /\ (exists k', k' <= MARK_LINE_MAX /\ amemfile_k segs m' sink k')
  /\ amq_rc regs m regs' m'.

Definition mark_quietly_acontract_again : Prop :=
  forall sink : Z,
    aleaf_fx SK segs rlo rhi B MARK_QUIETLY_A MARK_QUIETLY_AK 0 MARK_QUIETLY_ASIDE
      (mark_quietly_apre_again sink) mark_quietly_ard (mark_quietly_awr_again sink)
      (mark_quietly_apost_again sink).

(* ==========================================================================
   The first call: fmemopen makes the FILE (one allocator event)
   ========================================================================== *)

Definition mark_quietly_apre_open (bl : list (Z * Z)) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  au64_at segs m LA_G_SINK 0
  /\ amq_common 0 0 bl regs m
  /\ amf_env segs link_amf m
  /\ aarg regs 1 < alloc_ceiling
  /\ au64_at segs m LA_OFL_HEAD 0
  /\ awrange segs m LA_G_SINK 8 /\ awrange segs m LA_G_SAY 8
  /\ awrange segs m LA_G_SAID SAID_SIZE
  (* the rewind contract asks g_said's place (amf_buf_ok) on every call, also on a fresh FILE *)
  /\ amem_range LA_G_SAID SAID_SIZE
  /\ range_addressable (ard segs m) SHADOW_OFF LA_G_SAID SAID_SIZE
  /\ shadow_hull_vis (ard segs m) LA_G_SAID SAID_SIZE
  /\ acstr_at segs m LA_MODE_STR S_MODE_W
  /\ astr_rt_ok segs regs MARK_QUIETLY_AK m LA_MODE_STR S_MODE_W.

Definition mark_quietly_awr_open (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(LA_G_NL, LA_G_NL + NK_N_SENT + 4);
   aivl (aarg regs 0) MK_SIZE;
   (LA_G_SINK, LA_G_SINK + 8);
   (LA_G_SAID, LA_G_SAID + SAID_SIZE);
   (LA_G_SAY, LA_G_SAY + 8);
   (LA_OFL_HEAD, LA_OFL_HEAD + 8)].

(* PostA also sees the block lists before and after, so it names the fresh FILE block (pcap's
   tpcap_source_open_specX shape, A/Prog/PcapSourceOpenDefs.v:139-166). The list after is the list before with
   the FILE block added, up to `Permutation`: after fmemopen the function calls reac_served_say_to and
   tail-jumps into reac_served_mark, whose `aleaf` / `aleaf_fx` Posts give the block list only up to
   `Permutation` (found by the mark-quietly walk; the slot's own block-list fact is a Permutation too). *)
Definition mark_quietly_aposta_open (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte)
    (bl0 bl2 : list (Z * Z)) : Prop :=
  exists sink', sink' <> 0
    /\ au64_at segs m' LA_G_SINK sink' /\ au64_at segs m' LA_G_SAY sink'
    /\ au64_at segs m' LA_OFL_HEAD sink'
    /\ Permutation bl2 (bl0 ++ [(sink', AMF_BLOCK)])
    /\ (exists k', k' <= MARK_LINE_MAX /\ amemfile_k segs m' sink' k')
    /\ amq_rc regs m regs' m'.

Definition mark_quietly_acontract_open (MT : ameter_ops) (MO : Z) (CTX : list (list Z))
    (LedPre : astate -> Prop) (LedPost : astate -> astate -> Prop) : Prop :=
  aleaf_alloc_fx_sk SK segs rlo rhi B MT MARK_QUIETLY_A MARK_QUIETLY_AK 1 AMF_BLOCK MO
    MARK_QUIETLY_ASIDE CTX LedPre LedPost
    mark_quietly_apre_open mark_quietly_ard mark_quietly_awr_open mark_quietly_aposta_open.

End c.
