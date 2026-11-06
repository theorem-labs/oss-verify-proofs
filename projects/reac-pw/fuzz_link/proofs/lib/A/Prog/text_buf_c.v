(* text_buf (fuzz_link.c:654-665) on image A (fuzz_link.asan 0x863d0, 92 bytes; listing
   (internal path) (internal record, sha256 e2ba9446e8c9)): a buffer of `cap` bytes a reader
   may write, with a guard byte after it; NULL for cap = 0. a0 = cap. The plain contract is lib/Prog/text_buf_c.v (an
   SR-shape contract over the plain allocator interface); this file states the same result in link_amem.v's
   `aleaf_alloc` form (link-a/form/FORM.md (internal record, sha256 13aeff774164) sections 1, 3, 4.3).

   The image-A code, in order:
     +0x00..+0x0c  push a 32-byte frame; save ra, s0, s1
     +0x10  beqz a0 -> +0x38                                            (cap = 0: s0 := 0, answer NULL)
     +0x14..+0x1c  s1 := cap + 1; wrapper_malloc(cap + 1) (0x540cc), return address 0x863f0
     +0x20  beqz a0 -> +0x54 (abort path: the harness's own allocation failure)
     +0x24..+0x30  s0 := the block; checked_memset(block, 0x5a, cap + 1) (0x53214)
     +0x34  j +0x3c;  +0x3c  a0 := s0;  +0x40..+0x50  restore, pop, ret
     +0x54  jal before_abort (0x5b318); +0x58 jal abort (0x90ac4).
   No instrumented check: the stores into the block are inside checked_memset.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x0c (inside [sp - K, sp)); the malloc call takes
     the premises of the journal-level malloc rule (Reusable/YC5d.v:56-74 `amalloc04_rule`: the journal, gp/tp,
     ret_ok of 0x863f0, the event room, the live room, the meter, the frame chain and its trace in the universe) at
     sp' = sp - 32 with its ASTACK window; checked_memset takes `aintrin_realizes` (YG0d.v:325-343) on the fresh
     block, whose dest facts come from malloc's Post and AR (a fresh block is writable, not allocator-owned, and its
     shadow is AR's block shadow, AR_shadow_law YG0d.v:437-441); +0x50 ret.
   - K = 32 + ASTACK = 16416: the 32-byte frame, then malloc's window [sp' - ASTACK, sp') (checked_memset's ESTACK
     window is inside it). No realignment. The plain K (16 + ALLOC_STACK) does not carry over.
   - `aarg regs 0 < 40` (the plain `0 <= cap < 40`; cap = kc or ac, `fuzz_u8(in) % 40`, fuzz_link.c:680, both call
     sites LLVMFuzzerTestOneInput 0x835f4 / 0x83600): malloc's request cap + 1 is at most LIVE = 40 (its
     `0 <= n < MALLOC_MAX` and `blocks_bytes Sc + n <= LIVE_MAX`, from aleaf_alloc's `blocks_bytes Sc + LIVE <=
     LIVE_MAX`), its meter `mo_ok MT Sc (mo_malloc MT (cap + 1))` from aleaf_alloc's `mo_ok MT Sc MO` with
     MO = mo_malloc MT 40 (ameter_laws mo_malloc_mono and mo_ok_le), and checked_memset's `n < 2 ^ 32`. With these
     premises malloc does not answer 0, so +0x20 falls through: THE ABORT PATH IS UNREACHABLE (the plain
     `room_slots b (cap + 1)` did this on the plain allocator).
   - `text_buf_traces`: the call trace of the malloc at +0x1c is in the start-up universe's FIXED traces, for every
     context CTX allows (amalloc04_rule's `In (call_trace0 (pc_malloc_ra0 code) regsT ch) (as_universe B)`, whose
     coercion is u_fix). text_buf keeps s0 as a callee-saved register and builds no frame record, so the wrapper's
     record links to the caller's s0: the trace is `unwind_of_chain` (YG00.v:375) of the wrapper's return 0x863f0
     followed by the spine of the caller's chain, i.e. `tl c` for the context c = raZ regs :: spine ch that aleaf_alloc
     puts in CTX (the return address of text_buf itself is not on it). The start-up universe ACej.v lists text_buf's
     traces among its fixed ones (link-a/design/ACEJ-WILD.md (internal record, sha256 6ee1df95f779) section 3: no wild
     trace at this site); that membership is an obligation of the image instance and of CTX, not checked here.
   - LedPre := True: text_buf needs no wild-trace room. LedPost: the wild part of the depot does not grow (its trace
     is fixed), so a caller can state text_of's LedPre after a text_buf call (the form audit's finding 2).
   The write set is empty: the only bytes written outside the frame and the callees' windows are the fresh block's,
   which `akept` does not keep (it is no block of Sc), and the allocator's own state, which the journal's AR covers.
   The function reads through no pointer argument, so plain `aleaf_alloc` (no read set).
   EV = 1 (one malloc), LIVE = 40, MO = mo_malloc MT 40, SIDE = [] (no frame_alloc).

   PostA: cap = 0: a0 = 0 and the block list is the call's (up to order); cap <> 0: a0 = p, 4096 <= p, the block list
   is the call's with (p, cap + 1) appended (amalloc04_rule's `ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)]`),
   and the cap bytes and the guard byte at p all hold 0x5a and are writable (`atbuf_at m' p cap (repeat 0x5a cap)`).

   What does NOT carry over from the plain text (an SR-shape contract over the plain allocator interface):
   - `call_pre_k` / `call_post_k`, `res_ok_slots`, `room_slots`, `fresh_block`, `L' = L /\ A' = A /\ md' = md`:
     replaced by the journal premise and Post (link-a/form/FORM.md (internal record, sha256 13aeff774164) 4.3: the
     allocator room is `blocks_bytes` / `mo_ok`, the block list is `ablocks`, the descriptors and file system are
     apost's), and the plain `segs = rsegs`, `ro_agree` by `arodata_okP` (apre).
   - the plain `@YK11.mkst fx` start state is aleaf_alloc's `cfg_at segs pc regs memc mdc` under the same fx.
   - the plain AMEND-slot item 11 (the allocating arm keeps every old user block and
     gives `st_init_done A' = true`): here `bl2 = bl ++ [(p, cap + 1)]` keeps every block of the call, and the
     allocator's state is the journal's AR (no `st_init_done` on image A).
   Released proofs (rule 24): none of text_buf (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038)).

   Satisfiability witness (op_read, LLVMFuzzerTestOneInput 0x835f4): a0 = 16 (kc = 16); CTX = the contexts of the two
   call sites, each [ra; spine of LLVMFuzzerTestOneInput's chain] with ra = 0x835f8 or 0x83604; the journal's start
   state's allocator after the two callocs (blocks_bytes = 8856 + 516, far below LIVE_MAX = 2 ^ 34); MT the slot's
   meter with room for mo_malloc MT 40. The closed lemma of the register part of `text_buf_apre` is in
   lib/A/Prog/help_witness.v; `text_buf_traces` waits for the instance (ACej.v and B).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG00 YG01 YG0f YG0d YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition TEXT_BUF_A : Z := 0x863d0.
Lemma TEXT_BUF_A_is_entry : TEXT_BUF_A = LA_text_buf. Proof. reflexivity. Qed.

(* the return address of the malloc call (+0x1c jal wrapper_malloc) *)
Definition TEXT_BUF_MALLOC_RA : Z := 0x863f0.

(* the stack bound on image A: the 32-byte frame and malloc's window *)
Definition TEXT_BUF_AFRAME : Z := 32.
Definition TEXT_BUF_AK : Z := TEXT_BUF_AFRAME + ASTACK.
Lemma TEXT_BUF_AK_val : TEXT_BUF_AK = 16416. Proof. reflexivity. Qed.

(* the largest request: cap + 1 with cap < 40 *)
Definition TEXT_BUF_LIVE : Z := 40.

(* the write set: nothing that akept keeps (the fresh block is no block of the call's state) *)
Definition text_buf_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) := [].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).

(* the malloc trace of every context CTX allows is a fixed trace of the universe *)
Definition text_buf_traces : Prop :=
  forall c, In c CTX ->
    In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
          flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (TEXT_BUF_MALLOC_RA :: tl c)))
       (u_fix (as_universe B)).

Definition text_buf_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  aarg regs 0 < 40 /\ text_buf_traces.

Definition text_buf_ledpre (Sc : astate) : Prop := True.
Definition text_buf_ledpost (Sc S2 : astate) : Prop :=
  (length (wild_part (as_universe B) (st_depot S2)) <= length (wild_part (as_universe B) (st_depot Sc)))%nat.

Definition text_buf_apostA (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) (bl bl2 : list (Z * Z)) : Prop :=
  (aarg regs 0 = 0 -> getr regs' 10 = w64 0 /\ Permutation bl2 bl)
  /\ (aarg regs 0 <> 0 -> exists p,
        getr regs' 10 = w64 p /\ 4096 <= p
        /\ bl2 = bl ++ [(p, aarg regs 0 + 1)]
        /\ atbuf_at segs m' p (aarg regs 0) (repeat (zb GUARD_BYTE) (Z.to_nat (aarg regs 0)))).

Definition text_buf_acontract : Prop :=
  aleaf_alloc SK segs rlo rhi B MT TEXT_BUF_A TEXT_BUF_AK 1 TEXT_BUF_LIVE (mo_malloc MT TEXT_BUF_LIVE) [] CTX
    text_buf_ledpre text_buf_ledpost text_buf_apre text_buf_awr text_buf_apostA.

End c.
