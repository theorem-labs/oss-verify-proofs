(* fs program part, group ALLOC (fuzz/alloc.c): one ASan contract per function of the group, over fs.asan-ubsan
   (build B), in the donor's per-function form. STATEMENTS ONLY (rule 24: no function proved here).

   This is the asan-ubsan twin of lib/A/FSH_Fn_alloc.v: the SAME eight definition names carrying the SAME text,
   read over B's numerals. Only the import lines differ, so that FSH_Base (B's addresses, frames and stack
   budgets), FSH_Rt (B's cstr_kept / FS_RO_STRS) and FSPstat (B's four static slots) come from lib/B, while
   FSupoison, FSupoisonU, FSH_YC20 and FSH_Gen, which carry no image numeral, stay in lib/A exactly as
   lib/B/FSH_Base.v and lib/B/FSH_Rt.v themselves import them.

   The one structural difference between the two builds inside this group: B's compiler OUTLINES alloc.c's own()
   (B has a real function at 0x82acc, which A inlines into its callers). So B's own frames for fuzz_malloc and
   fuzz_realloc are smaller than A's, and B's STK_fuzz_malloc / STK_fuzz_realloc instead include STK_own. Those
   numbers live in lib/B/FSH_Base.v and are not restated here; this file names only STK_fuzz_malloc,
   STK_fuzz_realloc and the rest, so it reads B's values with no change of text. disown() is inline in both.

   Stated in the U FORM from the start (a Theorem Labs lane, 20:42Z): every spec threads the poisoned-head set U and gives
   its own U', because fuzz_malloc user-poisons a 16-byte head per block, so every program function runs with live
   heads. The U = [] forms are corollaries elsewhere, never the primary text.

   port-from:
   - lib/A/FSH_Fn_alloc.v (same text, B imports)
   - fuzz_alloc_live / _peak / _peak_reset / _fail, fuzz_malloc, fuzz_free: a Theorem Labs lane's lib/A/FMH_Fn.v:75-157
     (a working branch e48bf3cce32). fs's code for these is byte-identical to fm's modulo addresses
     (a Theorem Labs lane FsBinMatch.md section 3), and the specs are fm's generalised from U = [] to any U.
   - fuzz_strdup, fuzz_realloc: NEW (fm links neither). Functional content from fs's own released plain contracts
     lib/Prog/fuzz_strdup_c.v:29-60 and lib/Prog/fuzz_realloc_c.v:29-66 @ c8557374ad2e, restated in ASan form.

   All numerals, frames, stack budgets and the fpreU / fs_glob / fs_rblock instances come from S0
   (lib/B/FSH_Base.v, lib/A/FSH_Gen.v); this file defines no numeral of its own. fs_heads is FSupoisonU's
   (FSupoisonU.v:119), so ARU_free_outside discharges the free / realloc disjointness with no extra premise
   (a Theorem Labs lane, 20:41Z). The realloc arm itself is NOT stated here: a Theorem Labs lane owns the one shared primary-size realloc
   contract (lead, 20:53Z), and this group's fuzz_realloc walk consumes it.

   RESTATED 2026-10-28T21:3xZ on S0 7dd4849273a, following lib/A's restatement of the same date (three changes,
   all found by the ALLOC walk lanes; this twin takes them unchanged, over B's numbers):
   (1) FP. The ajournal image clause used to freeze every non-owned in-image byte when FP = [], which made any
       post that changes fuzz/alloc.c's statics contradictory (a Theorem Labs lane / owner 21:23Z, a Theorem Labs lane's text). The
       clause now exempts `inFP FP a`, and fs's four statics are FS_PSTAT_FP (lib/B/FSPstat.v, B's addresses). So
       every arm that WRITES g_live / g_peak / g_count / g_fail_at states FP = FS_PSTAT_FP (++ its block
       footprint, if any). The two read-only counters and fuzz_free's p = 0 arm write nothing and keep FP = [].
   (2) fs_heads is now a PREMISE of the four counter specs too (it was only in their posts, and fpreU cannot
       supply it: upoison_ok admits U entries that are not 16-byte heads at a block start).
   (3) fuzz_strdup takes `cstr_kept B ly S U s cs` (lib/B/FSH_Rt.v, a Theorem Labs lane's table-arm shape: a live block, an
       FS_RO_STRS literal, or a format), so the source string survives the inner fuzz_malloc call. The released
       plain proof carries the same premise (lib/Prog/fuzz_strdup_c.v:36-38).
   (4) fuzz_malloc_spec and fuzz_realloc_spec take `1 <= n`, not `0 <= n` (ruled 2026-10-28T21:53Z, case (i)).
       The poison contract (FSpoisonW.tfib_poison16, a Theorem Labs lane's apoison16_realizes) needs the strict
       `h + 16 < p + req_size n`, which fails at n = 0 since the block is (res - 16, n + 16). No fs call site passes 0:
       all 9 sites in each image build a size >= 1 by construction (strlen + 1, len + 1, count + 1, len/4*3 + 3,
       (len+2)/3*4 + 1, 8 * cap and 56 * cap with cap >= 8, and a capacity >= 4096), and the released
       `n + 16 <= 2 ^ 30` premise (lib/Prog/fuzz_malloc_c.v:34) rules out a wrap to 0. Measured list, disassembly-based
       (src/preset_file.c is not in git at c8557374ad2e): (internal path).
       This matches the donor a Theorem Labs lane, whose fuzz_malloc_spec takes `1 <= n`. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Base FSH_Rt FSPstat.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.

(* ---- the four counters (alloc.c:118-141): no allocation, no event, U passed through ---- *)

(* fuzz_alloc_live 0x82eec: returns g_live *)
Definition fuzz_alloc_live_spec : Prop :=
  forall ly S U W regs mem md ch live peak cnt fail,
  fpreU segs B STK_fuzz_alloc ly S U W regs mem md ch -> fs_heads B ly S U ->
  fs_glob segs W mem live peak cnt fail ->
  SRr segs W (cfg_at segs A_fuzz_alloc_live regs mem md)
    (apost_baseU segs B STK_fuzz_alloc [] regs ly S W mem md 0 U U
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 live /\ ablocks B ly' S' = ablocks B ly S /\
          fs_glob segs W' mem' live peak cnt fail /\ fs_heads B ly' S' U)).

(* fuzz_alloc_peak 0x82ef8: returns g_peak *)
Definition fuzz_alloc_peak_spec : Prop :=
  forall ly S U W regs mem md ch live peak cnt fail,
  fpreU segs B STK_fuzz_alloc ly S U W regs mem md ch -> fs_heads B ly S U ->
  fs_glob segs W mem live peak cnt fail ->
  SRr segs W (cfg_at segs A_fuzz_alloc_peak regs mem md)
    (apost_baseU segs B STK_fuzz_alloc [] regs ly S W mem md 0 U U
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 peak /\ ablocks B ly' S' = ablocks B ly S /\
          fs_glob segs W' mem' live peak cnt fail /\ fs_heads B ly' S' U)).

(* fuzz_alloc_peak_reset 0x82f04: g_peak = g_live *)
Definition fuzz_alloc_peak_reset_spec : Prop :=
  forall ly S U W regs mem md ch live peak cnt fail,
  fpreU segs B STK_fuzz_alloc ly S U W regs mem md ch -> fs_heads B ly S U ->
  fs_glob segs W mem live peak cnt fail ->
  SRr segs W (cfg_at segs A_fuzz_alloc_peak_reset regs mem md)
    (apost_baseU segs B STK_fuzz_alloc FS_PSTAT_FP regs ly S W mem md 0 U U
       (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\
          fs_glob segs W' mem' live live cnt fail /\ fs_heads B ly' S' U)).

(* fuzz_alloc_fail 0x82f18 (alloc.c:138-141): g_fail_at = g_count + k, saturating at SIZE_MAX *)
Definition fuzz_alloc_fail_spec : Prop :=
  forall ly S U W regs mem md ch live peak cnt fail k,
  fpreU segs B STK_fuzz_alloc ly S U W regs mem md ch -> fs_heads B ly S U ->
  fs_glob segs W mem live peak cnt fail ->
  getr regs 10 = w64 k -> 0 <= k < 2 ^ 64 ->
  SRr segs W (cfg_at segs A_fuzz_alloc_fail regs mem md)
    (apost_baseU segs B STK_fuzz_alloc FS_PSTAT_FP regs ly S W mem md 0 U U
       (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\ fs_heads B ly' S' U /\
          fs_glob segs W' mem' live peak cnt (if cnt + k <? 2 ^ 64 then cnt + k else SIZE_MAXZ))).

(* ---- fuzz_malloc 0x82a58 (alloc.c:61-66, own :41-49, outlined at 0x82acc) ----
   failing() ? NULL : malloc (n + HEAD), the head keeps n and is poisoned, so U gains it at the end. One event. *)
(* CTX premise DROPPED from fuzz_malloc / free / strdup / realloc (owner a Theorem Labs lane 2026-10-29T05:00Z, via a Theorem Labs lane):
   `In (raZ regs :: spine ch) CTX` was unsatisfiable in a reachable state (pj_write's never-written frame slot);
   the allocator call now takes C5's `In (call_trace ..) (as_universe B) \/ st_nev S < EV_MAX` (FSupoisonU.v:194 / :217),
   closed by the room premise. Stage 1 of the fold (a Theorem Labs lane 05:11Z) drops the now-unused CTX binder as well.
   own_spec drops its CTX premise and binder too (a Theorem Labs lane 05:27Z, measured by a Theorem Labs lane: own's proof has no use
   for it and its callers no longer have a CTX to build it from). *)
Definition fuzz_malloc_spec : Prop :=
  forall ly S U W regs mem md ch n live peak cnt fail,
  fpreU segs B STK_fuzz_malloc ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 10 = w64 n -> 1 <= n -> n + HEAD < MALLOC_MAX ->
  fs_glob segs W mem live peak cnt fail -> (cnt <> fail -> live + n < 2 ^ 64) -> cnt + 1 < 2 ^ 64 ->
  st_nev S + 1 <= EV_MAX -> (cnt <> fail -> blocks_bytes S + (n + HEAD) <= LIVE_MAX) ->
  SRr segs W (cfg_at segs A_fuzz_malloc regs mem md)
    (fun W' c' =>
       (cnt = fail /\ apost_baseU segs B STK_fuzz_malloc FS_PSTAT_FP regs ly S W mem md 0 U U
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
             fs_heads B ly' S' U /\
             fs_glob segs W' mem' live peak (cnt + 1) SIZE_MAXZ) W' c')
       \/
       (cnt <> fail /\ exists res,
          apost_baseU segs B STK_fuzz_malloc FS_PSTAT_FP regs ly S W mem md 1 U (U ++ [(res - HEAD, HEAD)])
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
             ablocks B ly' S' = ablocks B ly S ++ [(res - HEAD, n + HEAD)] /\
             fs_heads B ly' S' (U ++ [(res - HEAD, HEAD)]) /\
             (0 < n -> fs_rblock segs B ly' S' W' mem' res n) /\
             range_addressable (aview segs (w_H W') mem') SHADOW_OFF res n /\
             fs_glob segs W' mem' (live + n) (Z.max peak (live + n)) (cnt + 1) fail) W' c')).

(* ---- fuzz_free 0x82dbc (alloc.c:107-116, disown :51-59) ----
   p = 0 returns; else unpoison the head, g_live -= n, tail-call free (p - HEAD). The block's own head is removed
   from U wherever it sits, which is what FSupoisonU.ARU_unpoison_any gives. One event when p <> 0; p = 0 returns at
   the first `beqz` with no event, so its room premise is only on p <> 0 (a Theorem Labs lane, 2026-10-29T04:54Z: pj_free
   frees NULL fields and was unprovable under an unconditional + 1). *)
Definition fuzz_free_spec : Prop :=
  forall ly S U W regs mem md ch p n live peak cnt fail,
  getr regs 10 = w64 p ->
  fs_glob segs W mem live peak cnt fail -> fs_heads B ly S U ->
  ((p = 0 /\ fpreU segs B STK_fuzz_free ly S U W regs mem md ch) \/
   (p <> 0 /\ exists U1 U2, U = U1 ++ (p - HEAD, HEAD) :: U2 /\
      fpreU segs B STK_fuzz_free ly S U W regs mem md ch /\
      fs_rblock segs B ly S W mem p n /\ n <= live)) ->
  (p <> 0 -> st_nev S + 1 <= EV_MAX) ->
  SRr segs W (cfg_at segs A_fuzz_free regs mem md)
    (fun W' c' =>
       (p = 0 /\ apost_baseU segs B STK_fuzz_free [] regs ly S W mem md 0 U U
          (fun ly' S' W' regs' mem' md' =>
             ablocks B ly' S' = ablocks B ly S /\ fs_heads B ly' S' U /\
             fs_glob segs W' mem' live peak cnt fail) W' c')
       \/
       (p <> 0 /\ exists U1 U2, U = U1 ++ (p - HEAD, HEAD) :: U2 /\
          apost_baseU segs B STK_fuzz_free (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, n + HEAD)]) regs ly S W mem md 1 U
            (U1 ++ U2)
          (fun ly' S' W' regs' mem' md' =>
             (exists l1 l2, ablocks B ly S = l1 ++ (p - HEAD, n + HEAD) :: l2 /\ ablocks B ly' S' = l1 ++ l2) /\
             fs_heads B ly' S' (U1 ++ U2) /\
             fs_glob segs W' mem' (live - n) peak cnt fail) W' c')).

(* ---- fuzz_strdup 0x82d60 (alloc.c:96-104) ----
   n = strlen (s) + 1; d = fuzz_malloc (n); memcpy (d, s, n) when d. One allocation, through fuzz_malloc, so one
   event and one new head. cstr_ok gives the strlen / memcpy interceptors their addressable range. *)
Definition fuzz_strdup_spec : Prop :=
  forall ly S U W regs mem md ch s cs live peak cnt fail,
  fpreU segs B STK_fuzz_strdup ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 10 = w64 s -> cstr_ok segs W mem s cs -> cstr_kept B ly S U s cs ->
  (forall a, s <= a < s + Z.of_nat (length cs) + 1 -> ~ (spZ regs - STK_fuzz_strdup <= a < spZ regs)) ->
  fs_glob segs W mem live peak cnt fail ->
  (cnt <> fail -> live + (Z.of_nat (length cs) + 1) < 2 ^ 64) -> cnt + 1 < 2 ^ 64 ->
  Z.of_nat (length cs) + 1 + HEAD < MALLOC_MAX ->
  st_nev S + 1 <= EV_MAX -> (cnt <> fail -> blocks_bytes S + (Z.of_nat (length cs) + 1 + HEAD) <= LIVE_MAX) ->
  SRr segs W (cfg_at segs A_fuzz_strdup regs mem md)
    (fun W' c' =>
       (cnt = fail /\ apost_baseU segs B STK_fuzz_strdup FS_PSTAT_FP regs ly S W mem md 0 U U
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
             fs_heads B ly' S' U /\
             fs_glob segs W' mem' live peak (cnt + 1) SIZE_MAXZ) W' c')
       \/
       (cnt <> fail /\ exists res,
          apost_baseU segs B STK_fuzz_strdup FS_PSTAT_FP regs ly S W mem md 1 U (U ++ [(res - HEAD, HEAD)])
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
             ablocks B ly' S' = ablocks B ly S ++ [(res - HEAD, Z.of_nat (length cs) + 1 + HEAD)] /\
             fs_heads B ly' S' (U ++ [(res - HEAD, HEAD)]) /\
             fs_rblock segs B ly' S' W' mem' res (Z.of_nat (length cs) + 1) /\
             zbytes_at segs W' mem' res (cs ++ [0]) /\
             fs_glob segs W' mem' (live + (Z.of_nat (length cs) + 1))
               (Z.max peak (live + (Z.of_nat (length cs) + 1))) (cnt + 1) fail) W' c')).

(* ---- fuzz_realloc 0x82bc4 (alloc.c:75-94) ----
   p = 0 behaves as fuzz_malloc n. Otherwise failing() / overflow answer NULL without calling realloc; else
   disown (unpoison the old head), realloc (b, HEAD + n), own (poison the new head, B's outlined own() at
   0x82acc), so U loses the old head anywhere it sits and gains the new one at the end. The first min (k, n)
   bytes are kept (fs plain lib/Prog/fuzz_realloc_c.v:29-66). realloc's own NULL answer is absent from the post:
   it is dead under the granted-allocation rule, a LEMMA the walk proves (fuzz_realloc always asks HEAD + n >=
   HEAD, never 0, and a NULL p never reaches realloc), not a citation - fo_dead is cgif_rgb's vocabulary, not
   this donor's.
   realloc TICKS THREE TIMES (free PNull, malloc, free of the old block), so arm (c)'s journal counts 3 (it bounds the
   ticks: ajournal's st_nev S' <= st_nev S + k, YCbq.v:357; was 2, unprovable - a Theorem Labs lane 05:2xZ, realloc_ticks3)
   and the room premise is + 3 when p <> 0; p = 0 is a tail call to fuzz_malloc and ticks once, so its room
   premise is + 1 (a Theorem Labs lane, 2026-10-29T00:52Z: a uniform + 3 made the reader's event charge unprovable at a
   second grow from capacity 0). The ASan realloc contract itself is a Theorem Labs lane's shared
   primary-size arm, which this group's walk consumes; it is not stated here. *)
Definition fuzz_realloc_spec : Prop :=
  forall ly S U W regs mem md ch p k n old live peak cnt fail,
  fpreU segs B STK_fuzz_realloc ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 10 = w64 p -> getr regs 11 = w64 n -> 1 <= n -> n + HEAD < MALLOC_MAX ->
  fs_glob segs W mem live peak cnt fail -> (cnt <> fail -> live + n < 2 ^ 64) -> cnt + 1 < 2 ^ 64 ->
  ((p = 0 /\ k = 0 /\ old = []) \/
   (p <> 0 /\ (exists U1 U2, U = U1 ++ (p - HEAD, HEAD) :: U2) /\
    fs_rblock segs B ly S W mem p k /\ Z.of_nat (length old) = k /\ zbytes_at segs W mem p old /\ k <= live)) ->
  (p = 0 -> st_nev S + EV_fuzz_malloc <= EV_MAX) /\ (p <> 0 -> st_nev S + 3 <= EV_MAX) ->
  (cnt <> fail -> blocks_bytes S + (n + HEAD) <= LIVE_MAX) ->
  SRr segs W (cfg_at segs A_fuzz_realloc regs mem md)
    (fun W' c' =>
       (cnt = fail /\ apost_baseU segs B STK_fuzz_realloc FS_PSTAT_FP regs ly S W mem md 0 U U
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
             fs_heads B ly' S' U /\
             fs_glob segs W' mem' live peak (cnt + 1) SIZE_MAXZ) W' c')
       \/
       (cnt <> fail /\ p = 0 /\ exists res,
          apost_baseU segs B STK_fuzz_realloc FS_PSTAT_FP regs ly S W mem md 1 U (U ++ [(res - HEAD, HEAD)])
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
             ablocks B ly' S' = ablocks B ly S ++ [(res - HEAD, n + HEAD)] /\
             fs_heads B ly' S' (U ++ [(res - HEAD, HEAD)]) /\
             (0 < n -> fs_rblock segs B ly' S' W' mem' res n) /\
             fs_glob segs W' mem' (live + n) (Z.max peak (live + n)) (cnt + 1) fail) W' c')
       \/
       (cnt <> fail /\ p <> 0 /\ exists U1 U2 res, U = U1 ++ (p - HEAD, HEAD) :: U2 /\
          apost_baseU segs B STK_fuzz_realloc (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, k + HEAD)]) regs ly S W mem md 3 U
            (U1 ++ U2 ++ [(res - HEAD, HEAD)])
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
             (exists b1 b2 c1 c2, ablocks B ly S = b1 ++ (p - HEAD, k + HEAD) :: b2 /\
                ablocks B ly' S' = c1 ++ (res - HEAD, n + HEAD) :: c2 /\ c1 ++ c2 = b1 ++ b2) /\
             fs_heads B ly' S' (U1 ++ U2 ++ [(res - HEAD, HEAD)]) /\
             (0 < n -> fs_rblock segs B ly' S' W' mem' res n) /\
             zbytes_at segs W' mem' res (firstn (Z.to_nat (Z.min k n)) old) /\
             fs_glob segs W' mem' (live - k + n) (Z.max peak (live - k + n)) (cnt + 1) fail) W' c')).

(* ---- own 0x82acc (alloc.c:41-49; B only, A inlines it into fuzz_malloc / fuzz_realloc) ----
   head := n (the memcpy, inlined as 8 checked byte stores into [b, b + 8)), poison the 16-byte head
   (__asan_poison_memory_region 0x54904 at 0x82b58), so U gains it; g_live += n, g_peak := max (G_LIVE / G_PEAK);
   a0 = b + HEAD. No allocation and no event: the block was made by the caller's runtime call, so ablocks is unchanged
   and the head is not yet in U. UBSan pointer-overflow check 0x82b7c-0x82b80 traps (unimp 0x82bc0) iff b >= 2^64 - 16,
   hence `b < 2 ^ 64 - HEAD`. g_count / g_fail_at are not touched (failing() is in the callers).
   FP = FS_PSTAT_FP ++ [(b, b + 8)]: it writes g_live / g_peak AND exactly the 8 head bytes [b, b + 8) of a block that
   is already in ablocks at entry (made by the caller's runtime call), which ajournal's block clause only allows inside
   FP (YCbq.v:361-362; awr_byte0 :461-465). Was FS_PSTAT_FP alone: unprovable (a Theorem Labs lane 2026-10-29T07:3xZ); then
   the whole block ablocks_fp [(b, n + HEAD)], which let own overwrite the user bytes realloc had just copied, so
   fuzz_realloc B's arm (c) could not be composed (a Theorem Labs lane, 08:5xZ). The 8-byte range keeps [b + 8, b + n + HEAD).
   Callers absorb it: on the success paths the block is the caller's temp block (ajournal_sub's in_tmp_block arm); the
   dead realloc own(b, old) is inside arm (c)'s ablocks_fp [(p - HEAD, k + HEAD)], the same block.
   Callers: fuzz_malloc 0x82ab4 (tail `j`), fuzz_realloc 0x82d0c (tail `j`, success) and 0x82d18 (`jal`, own (b, old)
   after realloc returns NULL; n := old). The two tail calls restore ra / sp first, so at own's entry raZ is the
   GRANDPARENT's return address (a Theorem Labs lane's check, reloc-check/b-reader-stmts.md); own_spec takes no CTX premise
   (dropped 2026-10-29, see the note above fuzz_malloc_spec). Measured (capstone, the pinned unstripped fs.asan-ubsan) by a Theorem Labs lane,
   (internal path); the bound re-measured by a Theorem Labs lane. *)
Definition own_spec : Prop :=
  forall ly S U W regs mem md ch b n live peak cnt fail,
  fpreU segs B STK_own ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 10 = w64 b -> getr regs 11 = w64 n ->
  In (b, n + HEAD) (ablocks B ly S) -> ~ In (b, HEAD) U ->
  b mod 16 = 0 -> 4096 <= b -> b < 2 ^ 64 - HEAD ->
  1 <= n -> n + HEAD < MALLOC_MAX ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF b (n + HEAD) ->
  fs_glob segs W mem live peak cnt fail -> live + n < 2 ^ 64 ->
  SRr segs W (cfg_at segs A_own regs mem md)
    (apost_baseU segs B STK_own (FS_PSTAT_FP ++ [(b, b + 8)]) regs ly S W mem md 0 U (U ++ [(b, HEAD)])
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 (b + HEAD) /\
          ablocks B ly' S' = ablocks B ly S /\
          fs_heads B ly' S' (U ++ [(b, HEAD)]) /\
          fs_rblock segs B ly' S' W' mem' (b + HEAD) n /\
          range_addressable (aview segs (w_H W') mem') SHADOW_OFF (b + HEAD) n /\
          fs_glob segs W' mem' (live + n) (Z.max peak (live + n)) cnt fail)).

End c.
